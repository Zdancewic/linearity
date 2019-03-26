(**
    Authors: Steve Zdancewic and Karl Mazurak and Jianzhou Zhao.
*) 

Require Export Metatheory.

(* ********************************************************************** *)
(** * #<a name="syntax"></a># Syntax (pre-terms) *)

Inductive typ : Set :=
  | typ_bvar : nat -> typ
  | typ_fvar : atom -> typ
  | typ_arrow : typ -> typ -> typ
  | typ_all : typ -> typ
  | typ_bang : typ -> typ
  | typ_with : typ -> typ -> typ
.

Inductive exp : Set :=
  | exp_bvar : nat -> exp
  | exp_fvar : atom -> exp
  | exp_abs : typ -> exp -> exp
  | exp_app : exp -> exp -> exp
  | exp_tabs : exp -> exp
  | exp_tapp : exp -> typ -> exp
  | exp_bang : exp -> exp
  | exp_let : exp -> exp -> exp
  | exp_apair : exp -> exp -> exp
  | exp_fst : exp -> exp
  | exp_snd : exp -> exp
.

Coercion typ_bvar : nat >-> typ.
Coercion typ_fvar : atom >-> typ.
Coercion exp_bvar : nat >-> exp.
Coercion exp_fvar : atom >-> exp.


(* ********************************************************************** *)
(** * #<a name="open"></a># Opening terms *)

Fixpoint open_tt_rec (K : nat) (U : typ) (T : typ)  {struct T} : typ :=
  match T with
  | typ_bvar J => if K == J then U else (typ_bvar J)
  | typ_fvar X => typ_fvar X
  | typ_arrow T1 T2 => typ_arrow (open_tt_rec K U T1) (open_tt_rec K U T2)
  | typ_all T1 => typ_all (open_tt_rec (S K) U T1)
  | typ_bang T1 => typ_bang (open_tt_rec K U T1)
  | typ_with T1 T2 => typ_with (open_tt_rec K U T1) (open_tt_rec K U T2)
  end.

Fixpoint open_te_rec (K : nat) (U : typ) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_abs V e1 => exp_abs (open_tt_rec K U V)  (open_te_rec K U e1)
  | exp_app e1 e2 => exp_app (open_te_rec K U e1) (open_te_rec K U e2)
  | exp_tabs e1 => exp_tabs (open_te_rec (S K) U e1)
  | exp_tapp e1 V => exp_tapp (open_te_rec K U e1) (open_tt_rec K U V)
  | exp_bang e1 => exp_bang  (open_te_rec K U e1)
  | exp_let e1 e2 => exp_let  (open_te_rec K U e1) (open_te_rec K U e2)
  | exp_apair e1 e2 => exp_apair  (open_te_rec K U e1) (open_te_rec K U e2)
  | exp_fst e1 => exp_fst  (open_te_rec K U e1)
  | exp_snd e1 => exp_snd  (open_te_rec K U e1)
  end.

Fixpoint open_ee_rec (k : nat) (f : exp) (e : exp)  {struct e} : exp :=
  match e with
  | exp_bvar i => if k == i then f else (exp_bvar i)
  | exp_fvar x => exp_fvar x
  | exp_abs V e1 => exp_abs V (open_ee_rec (S k) f e1)
  | exp_app e1 e2 => exp_app (open_ee_rec k f e1) (open_ee_rec k f e2)
  | exp_tabs e1 => exp_tabs (open_ee_rec k f e1)
  | exp_tapp e1 V => exp_tapp (open_ee_rec k f e1) V
  | exp_bang e1 => exp_bang  (open_ee_rec k f e1)
  | exp_let e1 e2 => exp_let  (open_ee_rec k f e1) (open_ee_rec (S k) f e2)
  | exp_apair e1 e2 => exp_apair  (open_ee_rec k f e1) (open_ee_rec k f e2)
  | exp_fst e1 => exp_fst  (open_ee_rec k f e1)
  | exp_snd e1 => exp_snd  (open_ee_rec k f e1)
  end.

Definition open_tt T U := open_tt_rec 0 U T.
Definition open_te e U := open_te_rec 0 U e.
Definition open_ee e1 e2 := open_ee_rec 0 e2 e1.

(* ********************************************************************** *)
(** * #<a name="lc"></a># Local closure *)

Inductive type : typ -> Prop :=
  | type_var : forall X,
      type (typ_fvar X)
  | type_arrow : forall T1 T2,
      type T1 ->
      type T2 ->
      type (typ_arrow T1 T2)
  | type_all : forall L T1,
      (forall X : atom, X `notin` L -> type (open_tt T1 X)) ->
      type (typ_all T1)
  | type_bang : forall T1,
      type T1 ->
      type (typ_bang T1)
  | type_with : forall T1 T2,
      type T1 ->
      type T2 ->
      type (typ_with T1 T2)
.

Inductive expr : exp -> Prop :=
  | expr_var : forall x,
      expr (exp_fvar x)
  | expr_abs : forall L T e1,
      type T ->
      (forall x : atom, x `notin` L -> expr (open_ee e1 x)) ->
      expr (exp_abs T e1)
  | expr_app : forall e1 e2,
      expr e1 ->
      expr e2 ->
      expr (exp_app e1 e2)
  | expr_tabs : forall L e1,
      (forall X : atom, X `notin` L -> expr (open_te e1 X)) ->
      expr (exp_tabs e1)
  | expr_tapp : forall e1 V,
      expr e1 ->
      type V ->
      expr (exp_tapp e1 V)
  | expr_bang : forall e1,
      expr e1 ->
      expr (exp_bang e1)
  | expr_let : forall L e1 e2,
      expr e1 ->
      (forall x : atom, x `notin` L -> expr (open_ee e2 x)) ->
      expr (exp_let e1 e2)
  | expr_apair : forall e1 e2,
      expr e1 ->
      expr e2 ->
      expr (exp_apair e1 e2)
  | expr_fst : forall e1,
      expr e1 ->
      expr (exp_fst e1)
  | expr_snd : forall e1,
      expr e1 ->
      expr (exp_snd e1)
.

(* ********************************************************************** *)
(** * #<a name="env"></a># Environments *)

Inductive binding : Set :=
  | bind_kn :  binding
  | bind_typ : typ -> binding.

Notation env := (list (atom * binding)).
Notation empty := (@nil (atom * binding)).

Inductive lbinding : Set :=
  | lbind_typ : typ -> lbinding.

Notation lenv := (list (atom * lbinding)).
Notation lempty := (@nil (atom * lbinding)).

(* ********************************************************************** *)
(** * #<a name="wf"></a># Well-formedness *)

Inductive wf_typ : env -> typ -> Prop :=
  | wf_typ_var : forall E (X : atom),
      uniq E ->
      binds X bind_kn E ->
      wf_typ E (typ_fvar X)
  | wf_typ_arrow : forall E T1 T2,
      wf_typ E T1 ->
      wf_typ E T2 ->
      wf_typ E (typ_arrow T1 T2)
  | wf_typ_all : forall L E T1,
      (forall X : atom, X `notin` L ->
        wf_typ ([(X, bind_kn)] ++ E) (open_tt T1 X)) ->
      wf_typ E (typ_all T1)
  | wf_typ_bang : forall E T1,
      wf_typ E T1 ->
      wf_typ E (typ_bang T1)
  | wf_typ_with : forall E T1 T2,
      wf_typ E T1 ->
      wf_typ E T2 ->
      wf_typ E (typ_with T1 T2)
  .

Inductive wf_env : env -> Prop :=
  | wf_env_empty :
      wf_env empty
  | wf_env_kn : forall (E : env) (X : atom),
      wf_env E ->
      X `notin` dom E ->
      wf_env ([(X, bind_kn)] ++ E)
  | wf_env_typ : forall (E : env) (x : atom) (T : typ),
      wf_env E ->
      wf_typ E T ->
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
      wf_typ E T ->
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
       wf_typ E T ->
       lenv_split E ([(x, lbind_typ T)]++D1) D2 ([(x, lbind_typ T)]++D3)
  | lenv_split_right: forall E D1 D2 D3 x T,
       lenv_split E D1 D2 D3 ->
       x `notin` dom E ->
       x `notin` dom D3 ->
       wf_typ E T ->
       lenv_split E D1 ([(x, lbind_typ T)]++D2) ([(x, lbind_typ T)]++D3).

(* ********************************************************************** *)
(** * #<a name="values"></a># Values *)

Inductive value : exp -> Prop :=
  | value_abs : forall T e1,
      expr (exp_abs T e1) ->
      value (exp_abs T e1)
  | value_tabs : forall e1,
      expr (exp_tabs e1) ->
      value (exp_tabs e1)
  | value_bang : forall e1,
      expr e1 ->
      value (exp_bang e1)
  | value_apair : forall e1 e2,
      expr e1 ->
      expr e2 ->
      value (exp_apair e1 e2)
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
  | typing_abs : forall L E D T1 e1 T2,
      wf_typ E T1-> 
      (forall x : atom, x `notin` L ->
        typing E ([(x, lbind_typ T1)] ++ D) (open_ee e1 x) T2) ->
      typing E D (exp_abs T1 e1) (typ_arrow T1 T2)
  | typing_app : forall T1 E D1 D2 D3 e1 e2 T2,
      typing E D1 e1 (typ_arrow T1 T2) ->
      typing E D2 e2 T1 ->
      lenv_split E D1 D2 D3 ->
      typing E D3 (exp_app e1 e2) T2
  | typing_tabs : forall L E D e1 T1,
      (forall X : atom, X `notin` L ->
        typing ([(X, bind_kn)] ++ E) D (open_te e1 X) (open_tt T1 X)) ->
      typing E D (exp_tabs e1) (typ_all T1)
  | typing_tapp : forall E D e1 T T1,
      typing E D e1 (typ_all T1) ->
      wf_typ E T ->
      typing E D (exp_tapp e1 T) (open_tt T1 T)
  | typing_bang : forall E e T,
      typing E lempty e T ->
      typing E lempty (exp_bang e) (typ_bang T)
  | typing_let : forall L E D1 D2 D3 T1 e1 e2 T2,
      typing E D1 e1 (typ_bang T1) ->
      (forall x : atom, x `notin` L ->
        typing ([(x, bind_typ T1)] ++ E) D2 (open_ee e2 x) T2) ->
      lenv_split E D1 D2 D3 ->
      typing E D3 (exp_let e1 e2) T2
  | typing_apair : forall E D e1 e2 T1 T2,
      typing E D e1 T1 ->
      typing E D e2 T2 ->
      typing E D (exp_apair e1 e2) (typ_with T1 T2)
  | typing_fst : forall E D e T1 T2,
      typing E D e (typ_with T1 T2) ->
      typing E D (exp_fst e) T1
  | typing_snd : forall E D e T1 T2,
      typing E D e (typ_with T1 T2) ->
      typing E D (exp_snd e) T2
.

(* ********************************************************************** *)
(** * #<a name="reduction"></a># Reduction *)

Inductive red : exp -> exp -> Prop :=
  | red_app : forall e1 e1' e2,
      expr e2 ->
      red e1 e1' ->
      red (exp_app e1 e2) (exp_app e1' e2)
  | red_tapp : forall e1 e1' V,
      type V ->
      red e1 e1' ->
      red (exp_tapp e1 V) (exp_tapp e1' V)
  | red_abs : forall T e1 e2,
      expr (exp_abs T e1) ->
      expr e2 ->
      red (exp_app (exp_abs T e1) e2) (open_ee e1 e2)
  | red_tabs : forall e1 T,
      expr (exp_tabs e1) ->
      type T ->
      red (exp_tapp (exp_tabs e1) T) (open_te e1 T)
  | red_let_cong : forall e1 e1' e2,
      expr (exp_let e1 e2) ->
      red e1 e1' ->
      red (exp_let e1 e2) (exp_let e1' e2)
  | red_let_beta : forall e1 e2,
      expr (exp_let (exp_bang e1) e2) ->
      red (exp_let (exp_bang e1) e2) (open_ee e2 e1)
  | red_fst_cong : forall e e',
      red e e' ->
      red (exp_fst e) (exp_fst e')
  | red_fst_beta : forall e1 e2,
      expr e1 ->
      expr e2 ->
      red (exp_fst (exp_apair e1 e2)) e1
  | red_snd_cong : forall e e',
      red e e' ->
      red (exp_snd e) (exp_snd e')
  | red_snd_beta : forall e1 e2,
      expr e1 ->
      expr e2 ->
      red (exp_snd (exp_apair e1 e2)) e2
.


(* ********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

(** We declare most constructors as [Hint]s to be used by the [auto]
    and [eauto] tactics.  We exclude constructors from the typing 
    relations that use cofinite quantification.  It is unlikely that 
    [eauto] will find an instantiation for the finite set [L], and in 
    those cases, [eauto] can take some time to fail. (A priori, this 
    is not obvious.  In practice, one adds as hints all constructors 
    and then later removes some constructors when they cause proof 
    search to take too long.) *)

Hint Constructors type expr wf_typ wf_env wf_lenv value red lenv_split.
Hint Resolve typing_var typing_lvar typing_app typing_tapp typing_bang typing_apair typing_fst typing_snd.

(* ********************************************************************** *)
(** * #<a name="cases"></a># Cases Tactic *)

Tactic Notation "typ_cases" tactic(first) tactic(c) :=
  first;
  [ c "typ_bvar" |  c "typ_fvar" | 
    c "typ_arrow" | c "typ_all" | c "typ_bang" | c "typ_with" ].

Tactic Notation "exp_cases" tactic(first) tactic(c) :=
  first;
  [ c "exp_bvar" |  c "exp_fvar" | 
    c "exp_abs" | c "exp_app" |
    c "exp_tabs" | c "exp_tapp" | 
    c "exp_bang" | c "exp_let" | 
    c "exp_apair" | c "exp_fst" | c "exp_snd" ].

Tactic Notation "type_cases" tactic(first) tactic(c) :=
  first;
  [ c "type_var" | c "type_arrow" | c "type_all" | c "type_bang" | c "type_with" ].

Tactic Notation "expr_cases" tactic(first) tactic(c) :=
  first;
  [ c "expr_var" | 
    c "expr_abs" | c "expr_app" |
    c "expr_tabs" | c "expr_tapp" |
    c "expr_bang" | c "expr_let" |
    c "expr_apair" | c "expr_fst" | c "expr_snd" ].

Tactic Notation "wf_typ_cases" tactic(first) tactic(c) :=
  first;
  [ c "wf_typ_var" | c "wf_typ_arrow" | c "wf_typ_all" | c "wf_typ_bang" | c "wf_typ_with" ].

Tactic Notation "wf_env_cases" tactic(first) tactic(c) :=
  first;
  [ c "wf_env_empty" | c "wf_env_kn" | c "wf_env_typ" ].

Tactic Notation "wf_lenv_cases" tactic(first) tactic(c) :=
  first;
  [ c "wf_lenv_empty" | c "wf_lenv_typ" ].

Tactic Notation "lenv_split_cases" tactic(first) tactic(c) :=
  first;
  [ c "lenv_split_empty" | c "lenv_split_left" | c "lenv_split_right" ].

Tactic Notation "value_cases" tactic(first) tactic(c) :=
  first;
  [ c "value_abs" | c "value_tabs" | c "value_bang"| c "value_apair" ].

Tactic Notation "red_cases" tactic(first) tactic(c) :=
  first;
  [ c "red_app" |
    c "red_tapp" | c "red_abs" | c "red_tabs" | 
    c "red_let_cong" | c "red_let_beta" | 
    c "red_fst_cong" | c "red_fst_beta" | 
    c "red_snd_cong" | c "red_snd_beta" ].

Tactic Notation "typing_cases" tactic(first) tactic(c) :=
  first;
  [ c "typing_var" | c "typing_lvar" |
    c "typing_abs" | c "typing_app" | 
    c "typing_tabs" | c "typing_tapp" | 
    c "typing_bang" | c "typing_let" | 
    c "typing_apair" | c "typing_fst" | c "typing_snd" ].

