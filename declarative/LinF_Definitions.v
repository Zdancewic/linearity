(** 
    Lightweight Linear F
    Steve Zdancewic and Karl Mazurak
*)

Require Export Metatheory.

(* ********************************************************************** *)
(** * #<a name="syntax"></a># Syntax (pre-terms) *)

Inductive kn : Set :=
  | kn_lin
  | kn_nonlin
.

Inductive typ : Set :=
  | typ_bvar : nat -> typ
  | typ_fvar : atom -> typ
  | typ_arrow : kn -> typ -> typ -> typ
  | typ_all : kn -> typ -> typ
.

Inductive exp : Set :=
  | exp_bvar : nat -> exp
  | exp_fvar : atom -> exp
  | exp_abs : kn -> typ -> exp -> exp
  | exp_app : exp -> exp -> exp
  | exp_tabs : kn -> exp -> exp
  | exp_tapp : exp -> typ -> exp
.

Coercion typ_bvar : nat >-> typ.
Coercion typ_fvar : atom >-> typ.
Coercion exp_bvar : nat >-> exp.
Coercion exp_fvar : atom >-> exp.


(* ********************************************************************** *)
(** * #<a name="open"></a># Opening terms *)

Fixpoint open_tt_rec (K : nat) (U : typ) (T : typ)  {struct T} : typ :=
  match T with
  | typ_bvar J => if K === J then U else (typ_bvar J)
  | typ_fvar X => typ_fvar X
  | typ_arrow k T1 T2 => typ_arrow k (open_tt_rec K U T1) (open_tt_rec K U T2)
  | typ_all k T2 => typ_all k (open_tt_rec (S K) U T2)
  end.

Fixpoint open_te_rec (K : nat) (U : typ) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_abs k V e1 => exp_abs  k (open_tt_rec K U V)  (open_te_rec K U e1)
  | exp_app e1 e2 => exp_app  (open_te_rec K U e1) (open_te_rec K U e2)
  | exp_tabs k e1 => exp_tabs k  (open_te_rec (S K) U e1)
  | exp_tapp e1 V => exp_tapp (open_te_rec K U e1) (open_tt_rec K U V)
  end.

Fixpoint open_ee_rec (k : nat) (f : exp) (e : exp)  {struct e} : exp :=
  match e with
  | exp_bvar i => if k === i then f else (exp_bvar i)
  | exp_fvar x => exp_fvar x
  | exp_abs K V e1 => exp_abs K V (open_ee_rec (S k) f e1)
  | exp_app e1 e2 => exp_app (open_ee_rec k f e1) (open_ee_rec k f e2)
  | exp_tabs K e1 => exp_tabs K (open_ee_rec k f e1)
  | exp_tapp e1 V => exp_tapp (open_ee_rec k f e1) V
  end.

Definition open_tt T U := open_tt_rec 0 U T.
Definition open_te e U := open_te_rec 0 U e.
Definition open_ee e1 e2 := open_ee_rec 0 e2 e1.


(* ********************************************************************** *)
(** * #<a name="lc"></a># Local closure *)

Inductive type : typ -> Prop :=
  | type_var : forall X,
      type (typ_fvar X)
  | type_arrow : forall K T1 T2,
      type T1 ->
      type T2 ->
      type (typ_arrow K T1 T2)
  | type_all : forall L K T2,
      (forall X : atom, X `notin` L -> type (open_tt T2 X)) ->
      type (typ_all K T2)
.

Inductive expr : exp -> Prop :=
  | expr_var : forall x,
      expr (exp_fvar x)
  | expr_abs : forall L K T e1,
      type T ->
      (forall x : atom, x `notin` L -> expr (open_ee e1 x)) ->
      expr (exp_abs K T e1)
  | expr_app : forall e1 e2,
      expr e1 ->
      expr e2 ->
      expr (exp_app e1 e2)
  | expr_tabs : forall L K e1,
      (forall X : atom, X `notin` L -> expr (open_te e1 X)) ->
      expr (exp_tabs K e1)
  | expr_tapp : forall e1 V,
      expr e1 ->
      type V ->
      expr (exp_tapp e1 V)
.


(* ********************************************************************** *)
(** * #<a name="env"></a># Environments *)

Inductive binding : Set :=
  | bind_kn :  kn -> binding
  | bind_typ : typ -> binding.

Notation env := (list (atom * binding)).
Notation empty := (@nil (atom * binding)).

Inductive lbinding : Set :=
  | lbind_typ : typ -> lbinding.

Notation lenv := (list (atom * lbinding)).
Notation lempty := (@nil (atom * lbinding)).

Notation "[ x ]" := (x :: nil).


(* ********************************************************************** *)
(** * #<a name="wf"></a># Well-formedness *)

Inductive wf_typ : env -> typ -> kn -> Prop :=
  | wf_typ_var : forall K E (X : atom),
      ok E ->
      binds X (bind_kn K) E ->
      wf_typ E (typ_fvar X) K
  | wf_typ_arrow : forall E K1 K2 K T1 T2,
      wf_typ E T1 K1 ->
      wf_typ E T2 K2 ->
      wf_typ E (typ_arrow K T1 T2) K
  | wf_typ_all : forall L E K1 K2 T2,
      (forall X : atom, X `notin` L ->
        wf_typ ([(X, bind_kn K1)] ++ E) (open_tt T2 X) K2) ->
      wf_typ E (typ_all K1 T2) K2
  | wf_typ_sub : forall E T,
      wf_typ E T kn_nonlin ->
      wf_typ E T kn_lin
.

Inductive wf_env : env -> Prop :=
  | wf_env_empty :
      wf_env empty
  | wf_env_kn : forall (E : env) (X : atom) (K : kn),
      wf_env E ->
      X `notin` dom E ->
      wf_env ([(X, bind_kn K)] ++ E)
  | wf_env_typ : forall (E : env) (x : atom) (T : typ),
      wf_env E ->
      wf_typ E T kn_nonlin ->
      x `notin` dom E ->
      wf_env ([(x, bind_typ T)] ++ E).

Inductive wf_lenv : env -> lenv -> Prop :=
  | wf_lenv_empty :  forall (E:env),
      wf_env E ->
      wf_lenv E lempty
  | wf_lenv_typ : forall (E:env) (D:lenv) (x:atom) (T:typ),
      wf_lenv E D ->
      x `notin` dom E ->
      x `notin` dom D -> 
      wf_typ E T kn_lin ->
      wf_lenv E ([(x, lbind_typ T)] ++ D).

(* ********************************************************************** *)
(** * #<a name="split"></a># Linear Context Splitting *)

Inductive lenv_split : env -> lenv -> lenv -> lenv -> Prop :=
  | lenv_split_empty: forall E, 
       wf_env E -> 
       lenv_split E lempty lempty lempty
  | lenv_split_left: forall E D1 D2 D3 x T,
       lenv_split E D1 D2 D3 ->
       x `notin` dom E ->
       x `notin` dom D3 ->
       wf_typ E T kn_lin ->
       lenv_split E ([(x, lbind_typ T)]++D1) D2 ([(x, lbind_typ T)]++D3)
  | lenv_split_right: forall E D1 D2 D3 x T,
       lenv_split E D1 D2 D3 ->
       x `notin` dom E ->
       x `notin` dom D3 ->
       wf_typ E T kn_lin ->
       lenv_split E D1 ([(x, lbind_typ T)]++D2) ([(x, lbind_typ T)]++D3).

(* ********************************************************************** *)
(** * #<a name="values"></a># Values *)

Inductive value : exp -> Prop :=
  | value_abs : forall K T e1,
      expr (exp_abs K T e1) ->
      value (exp_abs K T e1)
  | value_tabs : forall K e1,
      expr (exp_tabs K e1) ->
      value (exp_tabs K e1)
.

(* ********************************************************************** *)
(** * #<a name="typing_doc"></a># Typing *)

Inductive typing : env -> lenv -> exp -> typ -> Prop :=
  | typing_var : forall E x T,
      wf_env E ->
      binds x (bind_typ T) E ->
      typing E lempty (exp_fvar x) T
  | typing_lvar : forall E x T,
      wf_lenv E [(x, lbind_typ T)] ->
      typing E [(x, lbind_typ T)] (exp_fvar x) T
  | typing_abs : forall L K E D T1 e1 T2,
      wf_typ E T1 kn_nonlin -> 
      (forall x : atom, x `notin` L ->
        typing ([(x, bind_typ T1)] ++ E) D (open_ee e1 x) T2) ->
      (K = kn_nonlin -> D = lempty) ->
      typing E D (exp_abs K T1 e1) (typ_arrow K T1 T2)
  | typing_labs : forall L K E D T1 e1 T2,
      wf_typ E T1 kn_lin -> 
      (forall x : atom, x `notin` L ->
        typing E ([(x, lbind_typ T1)] ++ D) (open_ee e1 x) T2) ->
      (K = kn_nonlin -> D = lempty) ->
      typing E D (exp_abs K T1 e1) (typ_arrow K T1 T2)
  | typing_app : forall T1 K E D1 D2 D3 e1 e2 T2,
      typing E D1 e1 (typ_arrow K T1 T2) ->
      typing E D2 e2 T1 ->
      lenv_split E D1 D2 D3 ->
      typing E D3 (exp_app e1 e2) T2
  | typing_tabs : forall L E D K e1 T1,
      value e1 ->
      (forall X : atom, X `notin` L ->
        typing ([(X, bind_kn K)] ++ E) D (open_te e1 X) (open_tt T1 X)) ->
      typing E D (exp_tabs K e1) (typ_all K T1)
  | typing_tapp : forall K E D e1 T T2,
      typing E D e1 (typ_all K T2) ->
      wf_typ E T K ->
      typing E D (exp_tapp e1 T) (open_tt T2 T)
.


(* ********************************************************************** *)
(** * #<a name="reduction"></a># Reduction *)

Inductive red : exp -> exp -> Prop :=
  | red_app_1 : forall e1 e1' e2,
      expr e2 ->
      red e1 e1' ->
      red (exp_app e1 e2) (exp_app e1' e2)
  | red_app_2 : forall e1 e2 e2',
      value e1 ->
      red e2 e2' ->
      red (exp_app e1 e2) (exp_app e1 e2')
  | red_tapp : forall e1 e1' V,
      type V ->
      red e1 e1' ->
      red (exp_tapp e1 V) (exp_tapp e1' V)
  | red_abs : forall K T e1 v2,
      expr (exp_abs K T e1) ->
      value v2 ->
      red (exp_app (exp_abs K T e1) v2) (open_ee e1 v2)
  | red_tabs : forall K e1 T,
      expr (exp_tabs K e1) ->
      type T ->
      red (exp_tapp (exp_tabs K e1) T) (open_te e1 T)
.


(* ********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

(** We declare most constructors as [Hint]s to be used by the [auto]
    and [eauto] tactics.  We exclude constructors from the subtyping
    and typing relations that use cofinite quantification.  It is
    unlikely that [eauto] will find an instantiation for the finite
    set [L], and in those cases, [eauto] can take some time to fail.
    (A priori, this is not obvious.  In practice, one adds as hints
    all constructors and then later removes some constructors when
    they cause proof search to take too long.) *)

Hint Constructors type expr wf_typ wf_env wf_lenv value red.
Hint Resolve typing_var typing_lvar typing_app typing_tapp.
