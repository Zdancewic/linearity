(** 
    A simple concurrent Linear language
*)

Require Export Metatheory.

(* ********************************************************************** *)
(** * #<a name="syntax"></a># Syntax (pre-terms) *)

Inductive typ : Set :=
  | typ_unit : typ
  | typ_answer : typ
  | typ_arrow : typ -> typ -> typ
  | typ_with : typ -> typ -> typ
  | typ_tensor : typ -> typ -> typ
  | typ_plus : typ -> typ -> typ
.

Inductive chan : Set :=
  | bchan : nat -> chan
  | fchan : atom -> chan
.

Inductive exp : Set :=
  | exp_bvar : nat -> exp
  | exp_fvar : atom -> exp
  | exp_unit : exp
  | exp_seq : exp -> exp -> exp
  | exp_abs : typ -> exp -> exp
  | exp_app : exp -> exp -> exp
  | exp_apair : exp -> exp -> exp
  | exp_fst : exp -> exp
  | exp_snd : exp -> exp
  | exp_mpair : exp -> exp -> exp
  | exp_let : exp -> exp -> exp
  | exp_inl : typ -> exp -> exp
  | exp_inr : typ -> exp -> exp
  | exp_case : exp -> exp -> exp -> exp
  | exp_go : typ -> exp -> exp
  | exp_yield : exp -> exp
  | exp_snk : chan -> typ -> exp
  | exp_src : chan -> typ -> exp
  | exp_done : chan -> exp
.

Inductive proc : Set :=
  | proc_exp : exp -> proc
  | proc_par : proc -> proc -> proc
  | proc_new : typ -> proc -> proc
.

Coercion bchan : nat >-> chan.
Coercion fchan : atom >-> chan.
Coercion exp_bvar : nat >-> exp.
Coercion exp_fvar : atom >-> exp.
Coercion proc_exp : exp >-> proc.


(* ********************************************************************** *)
(** * #<a name="open"></a># Opening terms *)

Definition open_cc_rec (K : nat) (C : chan) (A : chan) : chan :=
  match A with
  | bchan J => if K == J then C else (bchan J)
  | fchan X => fchan X
  end.

Fixpoint open_ce_rec (K : nat) (C : chan) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_unit => exp_unit
  | exp_seq e1 e2 => exp_seq (open_ce_rec K C e1) (open_ce_rec K C e2)
  | exp_abs V e1 => exp_abs V (open_ce_rec K C e1)
  | exp_app e1 e2 => exp_app (open_ce_rec K C e1) (open_ce_rec K C e2)
  | exp_apair e1 e2 => exp_apair (open_ce_rec K C e1) (open_ce_rec K C e2)
  | exp_fst e1 => exp_fst (open_ce_rec K C e1)
  | exp_snd e1 => exp_snd (open_ce_rec K C e1)
  | exp_mpair e1 e2 => exp_mpair (open_ce_rec K C e1) (open_ce_rec K C e2)
  | exp_let e1 e2 => exp_let (open_ce_rec K C e1) (open_ce_rec K C e2)
  | exp_inl T e1 => exp_inl T (open_ce_rec K C e1)
  | exp_inr T e1 => exp_inr T (open_ce_rec K C e1)
  | exp_case e1 e2 e3 =>
      exp_case (open_ce_rec K C e1) (open_ce_rec K C e2) (open_ce_rec K C e3)
  | exp_go T e1 => exp_go T (open_ce_rec K C e1)
  | exp_yield e1 => exp_yield (open_ce_rec K C e1)
  | exp_snk A T => exp_snk (open_cc_rec K C A) T
  | exp_src A T => exp_src (open_cc_rec K C A) T
  | exp_done A => exp_done (open_cc_rec K C A)
  end.

Fixpoint open_cp_rec (K : nat) (C : chan) (P : proc) {struct P} : proc :=
  match P with
  | proc_exp e => proc_exp (open_ce_rec K C e)
  | proc_par P1 P2 => proc_par (open_cp_rec K C P1) (open_cp_rec K C P2)
  | proc_new T P1 => proc_new T (open_cp_rec (S K) C P1)
  end.

Fixpoint open_ee_rec (k : nat) (f : exp) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => if k == i then f else (exp_bvar i)
  | exp_fvar x => exp_fvar x
  | exp_unit => exp_unit
  | exp_seq e1 e2 => exp_seq (open_ee_rec k f e1) (open_ee_rec k f e2)
  | exp_abs V e1 => exp_abs V (open_ee_rec (S k) f e1)
  | exp_app e1 e2 => exp_app (open_ee_rec k f e1) (open_ee_rec k f e2)
  | exp_apair e1 e2 => exp_apair  (open_ee_rec k f e1) (open_ee_rec k f e2)
  | exp_fst e1 => exp_fst  (open_ee_rec k f e1)
  | exp_snd e1 => exp_snd  (open_ee_rec k f e1)
  | exp_mpair e1 e2 => exp_mpair (open_ee_rec k f e1) (open_ee_rec k f e2)
  | exp_let e1 e2 => exp_let (open_ee_rec k f e1) (open_ee_rec k f e2)
  | exp_inl T e1 => exp_inl T (open_ee_rec k f e1)
  | exp_inr T e1 => exp_inr T (open_ee_rec k f e1)
  | exp_case e1 e2 e3 =>
      exp_case (open_ee_rec k f e1) (open_ee_rec k f e2) (open_ee_rec k f e3)
  | exp_go T e1 => exp_go T (open_ee_rec k f e1)
  | exp_yield e1 => exp_yield (open_ee_rec k f e1)
  | exp_snk A T => exp_snk A T
  | exp_src A T => exp_src A T
  | exp_done A => exp_done A
  end.

Definition open_cc A C := open_cc_rec 0 C A.
Definition open_ce e C := open_ce_rec 0 C e.
Definition open_cp P C := open_cp_rec 0 C P.
Definition open_ee e1 e2 := open_ee_rec 0 e2 e1.

(* ********************************************************************** *)
(** * #<a name="close"></a># Closing terms *)

Definition close_cc_rec (K:nat) (X:atom) (A:chan) : chan :=
  match A with
  | bchan J => bchan J
  | fchan Y => if (X === Y) then (bchan K) else fchan Y
  end.

Fixpoint close_ce_rec (K : nat) (X : atom) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_unit => exp_unit
  | exp_seq e1 e2 => exp_seq (close_ce_rec K X e1) (close_ce_rec K X e2)
  | exp_abs V e1 => exp_abs V (close_ce_rec K X e1)
  | exp_app e1 e2 => exp_app (close_ce_rec K X e1) (close_ce_rec K X e2)
  | exp_apair e1 e2 => exp_apair (close_ce_rec K X e1) (close_ce_rec K X e2)
  | exp_fst e1 => exp_fst (close_ce_rec K X e1)
  | exp_snd e1 => exp_snd (close_ce_rec K X e1)
  | exp_mpair e1 e2 => exp_mpair (close_ce_rec K X e1) (close_ce_rec K X e2)
  | exp_let e1 e2 => exp_let (close_ce_rec K X e1) (close_ce_rec K X e2)
  | exp_inl T e1 => exp_inl T (close_ce_rec K X e1)
  | exp_inr T e1 => exp_inr T (close_ce_rec K X e1)
  | exp_case e1 e2 e3 =>
      exp_case (close_ce_rec K X e1) (close_ce_rec K X e2) (close_ce_rec K X e3)
  | exp_go T e1 => exp_go T (close_ce_rec K X e1)
  | exp_yield e1 => exp_yield (close_ce_rec K X e1)
  | exp_snk A T => exp_snk (close_cc_rec K X A) T
  | exp_src A T => exp_src (close_cc_rec K X A) T
  | exp_done A => exp_done (close_cc_rec K X A)
  end.

Fixpoint close_cp_rec (K : nat) (X : atom) (P : proc) {struct P} : proc :=
  match P with
  | proc_exp e => proc_exp (close_ce_rec K X e)
  | proc_par P1 P2 => proc_par (close_cp_rec K X P1) (close_cp_rec K X P2)
  | proc_new T P1 => proc_new T (close_cp_rec (S K) X P1)
  end.

Definition close_cc A X := close_cc_rec 0 X A.
Definition close_ce e X := close_ce_rec 0 X e.
Definition close_cp P X := close_cp_rec 0 X P.


Fixpoint close_ee_rec (K : nat) (X : atom) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar Y => if (X === Y) then exp_bvar K else exp_fvar Y
  | exp_unit => exp_unit
  | exp_seq e1 e2 => exp_seq (close_ee_rec K X e1) (close_ee_rec K X e2)
  | exp_abs V e1 => exp_abs V (close_ee_rec (S K) X e1)
  | exp_app e1 e2 => exp_app (close_ee_rec K X e1) (close_ee_rec K X e2)
  | exp_apair e1 e2 => exp_apair (close_ee_rec K X e1) (close_ee_rec K X e2)
  | exp_fst e1 => exp_fst (close_ee_rec K X e1)
  | exp_snd e1 => exp_snd (close_ee_rec K X e1)
  | exp_mpair e1 e2 => exp_mpair (close_ee_rec K X e1) (close_ee_rec K X e2)
  | exp_let e1 e2 => exp_let (close_ee_rec K X e1) (close_ee_rec K X e2)
  | exp_inl T e1 => exp_inl T (close_ee_rec K X e1)
  | exp_inr T e1 => exp_inr T (close_ee_rec K X e1)
  | exp_case e1 e2 e3 =>
      exp_case (close_ee_rec K X e1) (close_ee_rec K X e2) (close_ee_rec K X e3)
  | exp_go T e1 => exp_go T (close_ee_rec K X e1)
  | exp_yield e1 => exp_yield (close_ee_rec K X e1)
  | exp_snk A T => exp_snk A T
  | exp_src A T => exp_src A T
  | exp_done A => exp_done A
  end.


(* ********************************************************************** *)
(** * #<a name="swap"></a># Swapping *)

Definition swap_cc (X : atom) (Y : atom) (A : chan) : chan :=
  match A with
  | bchan J => bchan J
  | fchan Z => if (Z == Y) then (fchan X) else
                if (Z == X) then (fchan Y) else fchan Z
  end.

Fixpoint swap_ce (X : atom) (Y : atom) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_unit => exp_unit
  | exp_seq e1 e2 => exp_seq (swap_ce X Y e1) (swap_ce X Y e2)
  | exp_abs V e1 => exp_abs V (swap_ce X Y e1)
  | exp_app e1 e2 => exp_app (swap_ce X Y e1) (swap_ce X Y e2)
  | exp_apair e1 e2 => exp_apair (swap_ce X Y e1) (swap_ce X Y e2)
  | exp_fst e1 => exp_fst (swap_ce X Y e1)
  | exp_snd e1 => exp_snd (swap_ce X Y e1)
  | exp_mpair e1 e2 => exp_mpair (swap_ce X Y e1) (swap_ce X Y e2)
  | exp_let e1 e2 => exp_let (swap_ce X Y e1) (swap_ce X Y e2)
  | exp_inl T e1 => exp_inl T (swap_ce X Y e1)
  | exp_inr T e1 => exp_inr T (swap_ce X Y e1)
  | exp_case e1 e2 e3 =>
      exp_case (swap_ce X Y e1) (swap_ce X Y e2) (swap_ce X Y e3)
  | exp_go T e1 => exp_go T (swap_ce X Y e1)
  | exp_yield e1 => exp_yield (swap_ce X Y e1)
  | exp_snk A T => exp_snk (swap_cc X Y A) T
  | exp_src A T => exp_src (swap_cc X Y A) T
  | exp_done A => exp_done (swap_cc X Y A)
  end.

Fixpoint swap_cp (X : atom) (Y : atom) (P : proc) {struct P} : proc :=
  match P with
  | proc_exp e => proc_exp (swap_ce X Y e)
  | proc_par P1 P2 => proc_par (swap_cp X Y P1) (swap_cp X Y P2)
  | proc_new T P1 => proc_new T (swap_cp X Y P1)
  end.


(* ********************************************************************** *)
(** * #<a name="lc"></a># Local closure *)

Inductive type : typ -> Prop :=
  | type_triv : forall T, type T
.

Inductive channel : chan -> Prop :=
  | fchannel : forall x,
      channel (fchan x)
.

Inductive expr : exp -> Prop :=
  | expr_var : forall x,
      expr (exp_fvar x)
  | expr_unit :  expr exp_unit
  | expr_seq : forall e1 e2,
      expr e1 ->
      expr e2 ->
      expr (exp_seq e1 e2)
  | expr_abs : forall L T e1,
      type T ->
      (forall x : atom, x `notin` L -> expr (open_ee e1 x)) ->
      expr (exp_abs T e1)
  | expr_app : forall e1 e2,
      expr e1 ->
      expr e2 ->
      expr (exp_app e1 e2)
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
  | expr_mpair : forall e1 e2,
      expr e1 ->
      expr e2 ->
      expr (exp_mpair e1 e2)
  | expr_let : forall e1 e2,
      expr e1 ->
      expr e2 ->
      expr (exp_let e1 e2)
  | expr_inl : forall T e1,
      type T ->
      expr e1 ->
      expr (exp_inl T e1)
  | expr_inr : forall T e1,
      type T ->
      expr e1 ->
      expr (exp_inr T e1)
  | expr_case : forall e1 e2 e3,
      expr e1 ->
      expr e2 ->
      expr e3 ->
      expr (exp_case e1 e2 e3)
  | expr_go : forall T e1,
      type T ->
      expr e1 ->
      expr (exp_go T e1)
  | expr_yield : forall e1,
      expr e1 ->
      expr (exp_yield e1)
  | expr_snk : forall C T,
      channel C ->
      type T ->
      expr (exp_snk C T)
  | expr_src : forall C T,
      channel C ->
      type T ->
      expr (exp_src C T)
  | expr_done : forall C,
      channel C ->
      expr (exp_done C)
.

Inductive process : proc -> Prop :=
  | process_exp : forall e,
      expr e ->
      process (proc_exp e)
  | process_par : forall P1 P2,
      process P1 ->
      process P2 ->
      process (proc_par P1 P2)
  | process_new : forall L T P1,
      type T ->
      (forall X : atom, X `notin` L -> process (open_cp P1 X)) ->
      process (proc_new T P1)
.


(* ********************************************************************** *)
(** * #<a name="env"></a># Environments *)

Inductive binding : Set :=
  | bind_kn : binding.

Notation env := (list (atom * binding)).
Notation empty := (@nil (atom * binding)).

Inductive lbinding : Set :=
  | lbind_typ : typ -> lbinding
.

Notation lenv := (list (atom * lbinding)).
Notation lempty := (@nil (atom * lbinding)).

Inductive cdir : Set :=
  | cdir_snk
  | cdir_src
  | cdir_both
.

Inductive cbinding : Set :=
  | cbind_proto : cdir -> typ -> cbinding
.

Notation cenv := (list (atom * cbinding)).
Notation cempty := (@nil (atom * cbinding)).

Notation cenvs := (list cenv).
Notation lcempty := (@nil cenv).

(* ********************************************************************** *)
(** * #<a name="wf"></a># Well-formedness *)

Inductive wf_typ : env -> typ -> Prop :=
  | wf_typ_triv : forall E T, wf_typ E T
.     

(* As opposed to kinds in the simple setting *)
Inductive wf_proto : env -> typ -> Prop :=
  | wf_proto_answer : forall E, wf_proto E typ_answer
  | wf_proto_arrow : forall E T1 T2,
      wf_typ E T1 ->
      wf_proto E T2 -> 
      wf_proto E (typ_arrow T1 T2)
  | wf_proto_with : forall E T1 T2,
      wf_proto E T1  ->
      wf_proto E T2 ->
      wf_proto E (typ_with T1 T2)
.

Inductive wf_env : env -> Prop :=
  | wf_env_empty :
      wf_env empty
  | wf_env_kn : forall (E : env) (X : atom),
      wf_env E ->
      X `notin` dom E ->
      wf_env ([(X, bind_kn)] ++ E)
.

Inductive wf_lenv : env -> lenv -> Prop :=
  | wf_lenv_empty : forall (E:env),
      wf_env E ->
      wf_lenv E lempty
  | wf_lenv_typ : forall (E:env) (D:lenv) (x:atom) (T:typ),
      wf_lenv E D ->
      x `notin` dom E ->
      x `notin` dom D ->
      wf_typ E T ->
      wf_lenv E ([(x, lbind_typ T)] ++ D)
.

Inductive wf_cenv : env -> cenv -> Prop :=
  | wf_cenv_empty :  forall (E:env),
      wf_env E ->
      wf_cenv E cempty
  | wf_cenv_proto : forall (E:env) (Q:cenv) (X:atom) (d:cdir) (T:typ),
      wf_cenv E Q ->
      X `notin` dom E ->
      X `notin` dom Q -> 
      wf_proto E T ->
      wf_cenv E ([(X, cbind_proto d T)] ++ Q)
.

(*Inductive wf_cenv_acc : env -> cenv -> cenv -> cenv-> Prop :=
  | wf_cenv_acc_empty : forall (E:env) (Q:cenv),
      wf_cenv E Q ->
      wf_cenv_acc E cempty Q Q
  | wf_cenv_acc_fresh : forall (E:env) (Q:cenv) (X:atom) (d:cdir) (T:typ) (Q' Q'' : cenv),
      wf_cenv_acc E Q Q' Q'' ->
      X `notin` dom E ->
      X `notin` dom Q'' ->
      wf_proto E T ->
      wf_cenv_acc E ([(X, cbind_proto d T)] ++ Q) Q' ([(X, cbind_proto d T)] ++ Q'')
  | wf_cenv_acc_snksrc : forall (E:env) (Q:cenv) (X:atom) (T:typ) (Q' QL QR : cenv),
      wf_cenv_acc E Q Q' (QL ++ [(X, cbind_proto cdir_src T)] ++ QR) ->
      X `notin` dom E ->
      X `notin` dom Q ->
      wf_proto E T ->
      wf_cenv_acc E ([(X, cbind_proto cdir_snk T)] ++ Q) Q'
                              (QL ++ [(X, cbind_proto cdir_both T)] ++ QR)
  | wf_cenv_acc_srcsnk : forall (E:env) (Q:cenv) (X:atom) (T:typ) (Q' QL QR : cenv),
      wf_cenv_acc E Q Q' (QL ++ [(X, cbind_proto cdir_snk T)] ++ QR) ->
      X `notin` dom E ->
      X `notin` dom Q ->
      wf_proto E T ->
      wf_cenv_acc E ([(X, cbind_proto cdir_src T)] ++ Q) Q'
                              (QL ++ [(X, cbind_proto cdir_both T)] ++ QR)
.

Inductive wf_cenvs_aux : env -> cenvs -> cenv -> Prop :=
  | wf_cenvs_aux_nil : forall (E:env),
      wf_env E ->
      wf_cenvs_aux E nil cempty
  | wf_cenvs_aux_cons : forall (E:env) (Qs:cenvs) (Q:cenv) (Q':cenv) (Q'':cenv),
      wf_cenvs_aux E Qs Q' ->
      wf_cenv_acc E Q Q' Q'' ->
      wf_cenvs_aux E (Q::Qs) Q''
.*)

Inductive vwf_envs : env -> cenv -> lenv -> Prop :=
  | vwf_envs_empty : forall (E:env) (Q:cenv),
      wf_cenv E Q ->
      vwf_envs E Q lempty
  | vwf_envs_typ : forall (E:env) (Q:cenv) (D:lenv) (x:atom) (T:typ),
      vwf_envs E Q D ->
      x `notin` dom E ->
      x `notin` dom D ->
      x `notin` dom Q -> 
      wf_typ E T ->
      vwf_envs E Q ([(x, lbind_typ T)] ++ D)
.

Inductive wf_chan : env -> chan -> Prop :=
  | wf_fchan : forall E X,
    wf_env E ->
    X `notin` dom E ->
    wf_chan E (fchan X)
.

(* ********************************************************************** *)
(** * #<a name="split"></a># Linear Context Splitting and Agreement *)

Inductive cenv_split_exp : env -> cenv -> cenv -> cenv -> Prop :=
  | cenv_split_exp_empty: forall E, 
      wf_env E -> 
      cenv_split_exp E cempty cempty cempty
  | cenv_split_exp_left: forall E Q1 Q2 Q3 X d T,
      cenv_split_exp E Q1 Q2 Q3 ->
      X `notin` dom E ->
      X `notin` dom Q3 ->
      wf_proto E T ->
      cenv_split_exp E ([(X, cbind_proto d T)]++Q1) Q2 ([(X, cbind_proto d T)]++Q3)
  | cenv_split_exp_right: forall E Q1 Q2 Q3 X d T,
      cenv_split_exp E Q1 Q2 Q3 ->
      X `notin` dom E ->
      X `notin` dom Q3 ->
      wf_proto E T ->
      cenv_split_exp E Q1 ([(X, cbind_proto d T)]++Q2) ([(X, cbind_proto d T)]++Q3)
.

Inductive cenv_split_proc : env -> cenv -> cenv -> cenv -> option atom -> Prop :=
  | cenv_split_proc_empty: forall E, 
      wf_env E -> 
      cenv_split_proc E cempty cempty cempty None
  | cenv_split_proc_left: forall E Q1 Q2 Q3 X d T Z,
      cenv_split_proc E Q1 Q2 Q3 Z ->
      X `notin` dom E ->
      X `notin` dom Q3 ->
      wf_proto E T ->
      cenv_split_proc E ([(X, cbind_proto d T)]++Q1) Q2 ([(X, cbind_proto d T)]++Q3) Z
  | cenv_split_proc_right: forall E Q1 Q2 Q3 X d T Z ,
      cenv_split_proc E Q1 Q2 Q3 Z ->
      X `notin` dom E ->
      X `notin` dom Q3 ->
      wf_proto E T ->
      cenv_split_proc E Q1 ([(X, cbind_proto d T)]++Q2) ([(X, cbind_proto d T)]++Q3) Z
  | cenv_split_proc_snksrc: forall E Q1 Q2 Q3 X T,
      cenv_split_exp E Q1 Q2 Q3 ->
      X `notin` dom E ->
      X `notin` dom Q3 ->
      wf_proto E T ->
      cenv_split_proc E ([(X, cbind_proto cdir_snk T)]++Q1)
        ([(X, cbind_proto cdir_src T)]++Q2)
        ([(X, cbind_proto cdir_both T)]++Q3) (Some X)
  | cenv_split_proc_srcsnk: forall E Q1 Q2 Q3 X T,
      cenv_split_exp E Q1 Q2 Q3 ->
      X `notin` dom E ->
      X `notin` dom Q3 ->
      wf_proto E T ->
      cenv_split_proc E ([(X, cbind_proto cdir_src T)]++Q1)
        ([(X, cbind_proto cdir_snk T)]++Q2)
        ([(X, cbind_proto cdir_both T)]++Q3) (Some X)
.

Inductive cenv_split_multi : env -> cenvs -> cenv -> option atom -> Prop :=
  | cenv_split_multi_empty: forall E,
      wf_env E ->
      cenv_split_multi E lcempty cempty None
  | cenv_split_multi_leaf: forall E Q,
      wf_cenv E Q ->
      cenv_split_multi E [Q] Q None
  | cenv_split_multi_branch : forall E Qs1 Qs2 Q1 Q2 Q3 X Y Z,
      cenv_split_multi E Qs1 Q1 X ->
      cenv_split_multi E Qs2 Q2 Y ->
      cenv_split_proc E Q1 Q2 Q3 Z ->
      cenv_split_multi E (Qs1++Qs2) Q3 Z
.

Inductive wf_cenvs : env -> cenvs -> Prop :=
  | wf_cenvs_nil : forall E,
      wf_env E ->
      wf_cenvs E lcempty
  | wf_cenvs_csm : forall E Qs Q Z,
      cenv_split_multi E Qs Q Z ->
      wf_cenvs E Qs
.

Inductive cenvs_split_multi : env -> cenvs -> cenvs -> Prop :=
  | cenvs_split_multi_nil: forall E,
      wf_env E ->
      cenvs_split_multi E nil nil
  | cenvs_split_multi_cons: forall E Qs1 Qs2 Qs Q Z,
      cenvs_split_multi E Qs1 Qs2 ->
      cenv_split_multi E Qs Q Z ->
      wf_cenvs E (Q::Qs2) ->
      cenvs_split_multi E (Qs++Qs1) (Q::Qs2)
.

Inductive cenvs_split_simple : env -> cenvs -> cenvs -> cenvs -> Prop :=
  | cenvs_split_simple_nil: forall E,
      cenvs_split_simple E nil nil nil
  | cenvs_split_simple_left: forall E Qs1 Qs2 Qs3 Q,
      cenvs_split_simple E Qs1 Qs2 Qs3 ->
      cenvs_split_simple E (Q::Qs1) Qs2 (Q::Qs3)
  | cenvs_split_simple_right: forall E Qs1 Qs2 Qs3 Q,
      cenvs_split_simple E Qs1 Qs2 Qs3 ->
      cenvs_split_simple E Qs1 (Q::Qs2) (Q::Qs3)
.

Inductive cenvs_split : env -> cenvs -> cenvs -> cenvs -> Prop :=
  | cenvs_split_ms: forall E Qs1 Qs2 Qs3 Qs',
      cenvs_split_multi E Qs' Qs3 ->
      cenvs_split_simple E Qs1 Qs2 Qs' ->
      cenvs_split E Qs1 Qs2 Qs3
(*  | cenvs_split_nil: forall E,
      wf_env E ->
      cenvs_split E nil nil nil
  | cenvs_split_cons: forall E Qs1 Qs2 Qs3 Q3 Qs1' Qs2' Qs3',
      cenvs_split E Qs1 Qs2 Qs3 ->
      cenv_split_multi E Qs3' Q3 ->
      cenvs_split_simple E Qs1' Qs2' Qs3' ->
      wf_cenvs E (Q3::Qs3) ->
      cenvs_split E (Qs1'++Qs1) (Qs2'++Qs2) (Q3::Qs3)*)
.

Inductive cenv_agree : env -> cenv -> cenv -> Prop :=
  | cenv_agree_empty: forall E,
      wf_env E ->
      cenv_agree E cempty cempty
  | cenv_agree_both:  forall E Q1 Q2 X d T,
      cenv_agree E Q1 Q2 ->
      X `notin` dom E ->
      X `notin` dom Q1 ->
      X `notin` dom Q2 ->
      wf_proto E T ->
      cenv_agree E ([(X, cbind_proto d T )]++Q1) ([(X, cbind_proto d T )]++Q2)
  | cenv_agree_left: forall E Q1 Q2 X d T,
      cenv_agree E Q1 Q2 ->
      X `notin` dom E ->
      X `notin` dom Q1 ->
      X `notin` dom Q2 ->
      wf_proto E T ->
      cenv_agree E ([(X, cbind_proto d T )]++Q1) Q2
  | cenv_agree_right: forall E Q1 Q2 X d T,
      cenv_agree E Q1 Q2 ->
      X `notin` dom E ->
      X `notin` dom Q1 ->
      X `notin` dom Q2 ->
      wf_proto E T ->
      cenv_agree E Q1 ([(X, cbind_proto d T )]++Q2)
.

Inductive lenv_split : env -> cenv -> lenv -> lenv -> lenv -> Prop :=
  | lenv_split_empty: forall E Q, 
      wf_cenv E Q -> 
      lenv_split E Q lempty lempty lempty
  | lenv_split_left: forall E Q D1 D2 D3 x T,
      lenv_split E Q D1 D2 D3 ->
      x `notin` dom E ->
      x `notin` dom Q ->
      x `notin` dom D3 ->
      wf_typ E T ->
      lenv_split E Q ([(x, lbind_typ T)]++D1) D2 ([(x, lbind_typ T)]++D3)
  | lenv_split_right: forall E Q D1 D2 D3 x T,
      lenv_split E Q D1 D2 D3 ->
      x `notin` dom E ->
      x `notin` dom Q ->
      x `notin` dom D3 ->
      wf_typ E T ->
      lenv_split E Q D1 ([(x, lbind_typ T)]++D2) ([(x, lbind_typ T)]++D3)
.

Inductive lenv_agree : env -> cenv -> lenv -> lenv -> Prop :=
  | lenv_agree_empty: forall E Q,
      wf_cenv E Q ->
      lenv_agree E Q lempty lempty
  | lenv_agree_both:  forall E Q D1 D2 X T,
      lenv_agree E Q D1 D2 ->
      X `notin` dom E ->
      X `notin` dom Q ->
      X `notin` dom D1 ->
      X `notin` dom D2 ->
      wf_typ E T ->
      lenv_agree E Q ([(X, lbind_typ T )]++D1) ([(X, lbind_typ T )]++D2)
  | lenv_agree_left: forall E Q D1 D2 X T,
      lenv_agree E Q D1 D2 ->
      X `notin` dom E ->
      X `notin` dom Q ->
      X `notin` dom D1 ->
      X `notin` dom D2 ->
      wf_typ E T ->
      lenv_agree E Q ([(X, lbind_typ T )]++D1) D2
  | lenv_agree_right: forall E Q D1 D2 X T,
      lenv_agree E Q D1 D2 ->
      X `notin` dom E ->
      X `notin` dom Q ->
      X `notin` dom D1 ->
      X `notin` dom D2 ->
      wf_typ E T ->
      lenv_agree E Q D1 ([(X, lbind_typ T )]++D2)
.

(* ********************************************************************** *)
(** * #<a name="values"></a># Values and Evaluation Contexts *)

Inductive value : exp -> Prop :=
  | value_unit :  value exp_unit
  | value_abs : forall T e1,
      expr (exp_abs T e1) ->
      value (exp_abs T e1)
  | value_apair : forall e1 e2,
      expr (exp_apair e1 e2) ->
      value (exp_apair e1 e2)
  | value_mpair : forall e1 e2,
      value e1 ->
      value e2 ->
      value (exp_mpair e1 e2)
  | value_inl : forall T e1,
      value e1 ->
      value (exp_inl T e1)
  | value_inr : forall T e1,
      value e1 ->
      value (exp_inr T e1)
  | value_snk : forall C T,
      expr (exp_snk C T) ->
      value (exp_snk C T)
  | value_src : forall C T,
      expr (exp_src C T) ->
      value (exp_src C T)
  | value_done : forall C,
      expr (exp_done C) ->
      value (exp_done C)
.

Inductive ectx : Set := 
  | ectx_hole : ectx
  | ectx_seq : forall e, ectx -> expr e -> ectx
  | ectx_appl : forall e, ectx -> expr e -> ectx
  | ectx_appr : forall v, value v -> ectx -> ectx
  | ectx_fst : ectx -> ectx
  | ectx_snd : ectx -> ectx
  | ectx_mpairl : forall e, ectx -> expr e -> ectx
  | ectx_mpairr : forall v, value v -> ectx -> ectx
  | ectx_let : forall e, ectx -> expr e -> ectx
  | ectx_inl : forall T, type T -> ectx -> ectx
  | ectx_inr : forall T, type T -> ectx -> ectx
  | ectx_case : forall e2 e3, ectx -> expr e2 -> expr e3 -> ectx
  | ectx_go : forall T, type T -> ectx -> ectx
  | ectx_yield : ectx -> ectx
.

Inductive plug : ectx -> exp -> exp -> Prop :=
  | plug_hole : forall e,
      plug ectx_hole e e
  | plug_seq : forall e2 M1 He2 e e1,
      plug M1 e e1 ->
      plug (ectx_seq e2 M1 He2) e (exp_seq e1 e2)
  | plug_appl : forall e2 M1 He2 e e1,
      plug M1 e e1 ->
      plug (ectx_appl e2 M1 He2) e (exp_app e1 e2)
  | plug_appr : forall v1 M2 Hv1 e e2,
      plug M2 e e2 ->
      plug (ectx_appr v1 Hv1 M2) e (exp_app v1 e2)
  | plug_fst : forall M1 e e1,
      plug M1 e e1 ->
      plug (ectx_fst M1) e (exp_fst e1)
  | plug_snd : forall M1 e e1,
      plug M1 e e1 ->
      plug (ectx_snd M1) e (exp_snd e1)
  | plug_mpairl : forall e2 M1 He2 e e1,
      plug M1 e e1 ->
      plug (ectx_mpairl e2 M1 He2) e (exp_mpair e1 e2)
  | plug_mpairr : forall v1 M2 Hv1 e e2,
      plug M2 e e2 ->
      plug (ectx_mpairr v1 Hv1 M2) e (exp_mpair v1 e2)
  | plug_let : forall e2 M1 He2 e e1,
      plug M1 e e1 ->
      plug (ectx_let e2 M1 He2) e (exp_let e1 e2)
  | plug_inl : forall T HT M1 e e1,
      plug M1 e e1 ->
      plug (ectx_inl T HT M1) e (exp_inl T e1)
  | plug_inr : forall T HT M1 e e1,
      plug M1 e e1 ->
      plug (ectx_inr T HT M1) e (exp_inr T e1)
  | plug_case : forall e2 e3 M1 He2 He3 e e1,
      plug M1 e e1 ->
      plug (ectx_case e2 e3 M1 He2 He3) e (exp_case e1 e2 e3)
  | plug_go : forall T HT M1 e e1,
      plug M1 e e1 ->
      plug (ectx_go T HT M1) e (exp_go T e1)
  | plug_yield : forall M1 e e1,
      plug M1 e e1 ->
      plug (ectx_yield M1) e (exp_yield e1)
.

(* Fixpoint plug (M : ectx) (e : exp) {struct M} : exp :=
  match M with
  | ectx_hole => e
  | ectx_seq e2 M1 _ => exp_seq (plug M1 e) e2
  | ectx_appl e2 M1 _ => exp_app (plug M1 e) e2
  | ectx_appr v1 _ M2 => exp_app v1 (plug M2 e)
  | ectx_fst M1 => exp_fst (plug M1 e)
  | ectx_snd M1 => exp_snd (plug M1 e)
  | ectx_mpairl e2 M1 _ => exp_mpair (plug M1 e) e2
  | ectx_mpairr v1 _ M2 => exp_mpair v1 (plug M2 e)
  | ectx_let e2 M1 _ => exp_let (plug M1 e) e2
  | ectx_inl T _ M1 => exp_inl T (plug M1 e)
  | ectx_inr T _ M1 => exp_inr T (plug M1 e)
  | ectx_case e2 e3 M1 _ _ => exp_case (plug M1 e) e2 e3
  | ectx_go T _ M1 => exp_go T (plug M1 e)
  | ectx_yield M1 => exp_yield (plug M1 e)
  end. *)

(* ********************************************************************** *)
(** * #<a name="typing_doc"></a># Typing *)

Definition typ_src T := typ_arrow (typ_arrow T typ_answer) typ_answer.

Inductive dual : env -> typ -> typ -> Prop :=
  | dual_answer : forall E,
      wf_env E ->
      dual E typ_answer typ_unit
  | dual_arrow : forall E T1 T2 T2',
      dual E T2 T2' ->
      dual E (typ_arrow T1 T2) (typ_src (typ_tensor T1 T2'))
  | dual_with : forall E T1 T2 T1' T2',
      dual E T1 T1' ->
      dual E T2 T2' ->
      dual E (typ_with T1 T2) (typ_src (typ_plus T1' T2'))
.

(*Inductive covers : cdir -> cdir -> Prop :=
  | covers_refl : forall d,
      covers d d
  | covers_both : forall d,
      covers cdir_both d
.

Inductive snk : env -> typ -> chan -> exp -> Prop :=
  | snk_answer : forall E C,
      wf_chan E C ->
      snk E typ_answer C (rt_endsnk C)
  | snk_arrow : forall E T1 T2 C e2,
      snk E T2 C e2 ->
      snk E (typ_arrow T1 T2) C (rt_abs C T1 e2)
  | snk_with : forall E T1 T2 C e1 e2,
      snk E T1 C e1 ->
      snk E T2 C e2 ->
      snk E (typ_with T1 T2) C (rt_apair C e1 e2)
.

Inductive src : env -> typ -> chan -> exp -> Prop :=
  | src_answer : forall E C,
      wf_chan E C ->
      src E typ_answer C (rt_endsrc C)
  | src_arrow : forall L E T1 T2 C e2,
      src E T2 C e2 ->
      (forall x, x `notin` L ->
        open_ee (exp_mpair (exp_bvar 0) e2) x =
        exp_mpair (open_ee (exp_bvar 0) x) e2) ->
      src E (typ_arrow T1 T2) C
        (rt_app C T1 (exp_abs T1 (exp_mpair (exp_bvar 0) e2)))
  | src_with : forall E T1 T2 C e1 e2 T1' T2',
      src E T1 C e1 ->
      src E T2 C e2 ->
      dual E T1 T1' ->
      dual E T2 T2' ->
      src E (typ_with T1 T2) C
        (rt_select C (exp_inl (typ_plus T1' T2') e1) (exp_inr (typ_plus T1' T2') e2))
.*)

Inductive typing : env -> lenv -> cenv -> exp -> typ -> Prop :=
  | typing_var : forall E x T,
      wf_lenv E [(x, lbind_typ T)] ->
      typing E [(x, lbind_typ T)] cempty (exp_fvar x) T
  | typing_unit : forall E,
      wf_env E ->
      typing E lempty cempty exp_unit typ_unit
  | typing_seq : forall E D1 D2 D3 Q1 Q2 Q3 e1 e2 T2,
      typing E D1 Q1 e1 typ_unit ->
      typing E D2 Q2 e2 T2 ->
      lenv_split E Q3 D1 D2 D3 ->
      cenv_split_exp E Q1 Q2 Q3 ->
      typing E D3 Q3 (exp_seq e1 e2) T2
  | typing_abs : forall L E D Q T1 e1 T2,
      wf_typ E T1 -> 
      (forall x : atom, x `notin` L ->
        typing E ([(x, lbind_typ T1)] ++ D) Q (open_ee e1 x) T2) ->
      typing E D Q (exp_abs T1 e1) (typ_arrow T1 T2)
  | typing_app : forall T1 E D1 D2 D3 Q1 Q2 Q3 e1 e2 T2,
      typing E D1 Q1 e1 (typ_arrow T1 T2) ->
      typing E D2 Q2 e2 T1 ->
      lenv_split E Q3 D1 D2 D3 ->
      cenv_split_exp E Q1 Q2 Q3 ->
      typing E D3 Q3 (exp_app e1 e2) T2
  | typing_apair : forall E D Q e1 e2 T1 T2,
      typing E D Q e1 T1 ->
      typing E D Q e2 T2 ->
      typing E D Q (exp_apair e1 e2) (typ_with T1 T2)
  | typing_fst : forall E D Q e T1 T2,
      typing E D Q e (typ_with T1 T2) ->
      typing E D Q (exp_fst e) T1
  | typing_snd : forall E D Q e T1 T2,
      typing E D Q e (typ_with T1 T2) ->
      typing E D Q (exp_snd e) T2
  | typing_mpair : forall E D1 D2 D3 Q1 Q2 Q3 e1 e2 T1 T2,
      typing E D1 Q1 e1 T1 ->
      typing E D2 Q2 e2 T2 ->
      lenv_split E Q3 D1 D2 D3 ->
      cenv_split_exp E Q1 Q2 Q3 ->
      typing E D3 Q3 (exp_mpair e1 e2) (typ_tensor T1 T2)
  | typing_let : forall E D1 D2 D3 Q1 Q2 Q3 e1 e2 T1 T2 T3,
      typing E D1 Q1 e1 (typ_tensor T1 T2) ->
      typing E D2 Q2 e2 (typ_arrow T1 (typ_arrow T2 T3)) ->
      lenv_split E Q3 D1 D2 D3 ->
      cenv_split_exp E Q1 Q2 Q3 ->
      typing E D3 Q3 (exp_let e1 e2) T3
  | typing_inl : forall E D Q e1 T1 T2,
      typing E D Q e1 T1 ->
      typing E D Q (exp_inl (typ_plus T1 T2) e1) (typ_plus T1 T2)
  | typing_inr : forall E D Q e2 T1 T2,
      typing E D Q e2 T2 ->
      typing E D Q (exp_inr (typ_plus T1 T2) e2) (typ_plus T1 T2)
  | typing_case : forall E D1 D2 D3 Q1 Q2 Q3 e1 e2 e3 T1 T2 T3,
      typing E D1 Q1 e1 (typ_plus T1 T2) ->
      typing E D2 Q2 e2 (typ_arrow T1 T3) ->
      typing E D2 Q2 e3 (typ_arrow T2 T3) ->
      lenv_split E Q3 D1 D2 D3 ->
      cenv_split_exp E Q1 Q2 Q3 ->
      typing E D3 Q3 (exp_case e1 e2 e3) T3
  | typing_go : forall E D Q T1 e1 T2,
      typing E D Q e1 (typ_arrow T1 typ_answer) ->
      dual E T1 T2 ->
      typing E D Q (exp_go T1 e1) T2
  | typing_yield : forall E D Q e1 T1,
      typing E D Q e1 (typ_src T1) ->
      typing E D Q (exp_yield e1) T1
  | typing_snk : forall E X T,
      wf_cenv E [(X, cbind_proto cdir_snk T)] ->
      typing E lempty [(X, cbind_proto cdir_snk T)]
        (exp_snk (fchan X) T) T
  | typing_src : forall E X T T',
      wf_cenv E [(X, cbind_proto cdir_src T)] ->
      dual E T T' ->
      typing E lempty [(X, cbind_proto cdir_src T)]
        (exp_src (fchan X) T) T'
  | typing_done : forall E X,
      wf_cenv E [(X, cbind_proto cdir_both typ_answer)] ->
      typing E lempty [(X, cbind_proto cdir_both typ_answer)]
        (exp_done (fchan X)) typ_answer
.

Fixpoint doms (C : Type) (E : list (list (atom*C))) : atoms :=
  match E with 
  | nil => Metatheory.empty
  | H :: T => dom H `union` doms C T
  end.

Inductive disjoints : forall (A B : Type), list (atom*A) -> list (list (atom*B)) -> Prop :=
  | disjoints_nil : forall A B E,
      disjoints A B E nil
  | disjoints_cons : forall A B E H T,
      disjoint E H ->
      disjoints A B E T ->
      disjoints A B E (H::T)
.

Inductive nd_cons_cenvs : cenvs -> (atom -> typ -> cenvs) -> Prop :=
  | nd_cons_cenvs_fresh : forall QsL QsR,
      nd_cons_cenvs (QsL ++ QsR)
        (fun (X:atom) (T:typ) =>
           QsL ++ [[(X, cbind_proto cdir_both T)]] ++ QsR)
  | nd_cons_cenvs_cons : forall Q QsL QsR,
      nd_cons_cenvs (QsL ++ [Q] ++ QsR)
        (fun (X:atom) (T:typ) =>
           QsL ++ [[(X, cbind_proto cdir_both T)] ++ Q] ++ QsR)
.
      
(* The old definition
  | nd_cons_cenvs_nil : forall E X T,
      wf_proto E T ->
      X `notin` dom E ->
      nd_cons_cenvs E X T nil [[(X, cbind_proto cdir_both T)]]
  | nd_cons_cenvs_head : forall E X T Q Qs,
      wf_proto E T ->
      X `notin` dom E ->
      X `notin` dom Q ->
      X `notin` doms cbinding Qs ->
      nd_cons_cenvs E X T (Q::Qs) (([(X, cbind_proto cdir_both T)]++Q)::Qs)
  | nd_cons_cenvs_tail : forall E X T Q Qs Qs',
      nd_cons_cenvs E X T Qs Qs' ->
      X `notin` dom Q ->
      nd_cons_cenvs E X T (Q::Qs) (Q::Qs')
.*)

Inductive proc_typing : cenvs -> proc -> typ -> Prop :=
  | typing_exp : forall Q e T Qs,
      typing empty lempty Q e T ->
      cenvs_split_multi empty [Q] Qs ->
      proc_typing Qs (proc_exp e) T
  | typing_parl : forall Qs1 Qs2 Qs3 P1 P2 T1,
      proc_typing Qs1 P1 T1 ->
      proc_typing Qs2 P2 typ_answer ->
      cenvs_split empty Qs1 Qs2 Qs3 ->
      proc_typing Qs3 (proc_par P1 P2) T1
  | typing_parr : forall Qs1 Qs2 Qs3 P1 P2 T2,
      proc_typing Qs1 P1 typ_answer ->
      proc_typing Qs2 P2 T2 ->
      cenvs_split empty Qs1 Qs2 Qs3 ->
      proc_typing Qs3 (proc_par P1 P2) T2
  | typing_new : forall L Qs FQs T1 P1 T2,
      wf_proto empty T1 ->
      nd_cons_cenvs Qs FQs ->
      (forall (X : atom), X `notin` L ->
        proc_typing (FQs X T1) (open_cp P1 X) T2) ->
      proc_typing Qs (proc_new T1 P1) T2
.

(* Altnerate typing_new, requires swapping lemmas... 
  | typing_new : forall Qs Qs' T1 P1 T2 X,
      X `notin` .... ->
      wf_proto empty T1 ->
      nd_prepend_list [(X, cbind_proto cdir_both T1)] Qs Qs' ->
      proc_typing' Qs' (open_cp P1 X) T2 ->
      proc_typing' Qs (proc_new T1 P1) T2
*)

Inductive ectx_typing : env -> lenv -> cenv -> ectx -> typ -> typ -> Prop :=
  | ectx_typing_hole : forall E T,
      wf_env E ->
      wf_typ E T ->
      ectx_typing E lempty cempty ectx_hole T T
  | ectx_typing_seq : forall E D1 D2 D3 Q1 Q2 Q3 M e T T' He,
      ectx_typing E D1 Q1 M T typ_unit ->
      typing E D2 Q2 e T' ->
      lenv_split E Q3 D1 D2 D3 ->
      cenv_split_exp E Q1 Q2 Q3 ->
      ectx_typing E D3 Q3 (ectx_seq e M He) T T'
  | ectx_typing_appl : forall E D1 D2 D3 Q1 Q2 Q3 M e T T1 T2 He,
      ectx_typing E D1 Q1 M T (typ_arrow T1 T2) ->
      typing E D2 Q2 e T1 ->
      lenv_split E Q3 D1 D2 D3 ->
      cenv_split_exp E Q1 Q2 Q3 ->
      ectx_typing E D3 Q3 (ectx_appl e M He) T T2
  | ectx_typing_appr : forall E D1 D2 D3 Q1 Q2 Q3 v M T T1 T2 Hv,
      typing E D1 Q1 v (typ_arrow T1 T2) ->
      ectx_typing E D2 Q2 M T T1 ->
      lenv_split E Q3 D1 D2 D3 ->
      cenv_split_exp E Q1 Q2 Q3 ->
      ectx_typing E D3 Q3 (ectx_appr v Hv M) T T2
  | ectx_typing_fst : forall E D Q M T T1 T2,
      ectx_typing E D Q M T (typ_with T1 T2) ->
      ectx_typing E D Q (ectx_fst M) T T1
  | ectx_typing_snd : forall E D Q M T T1 T2,
      ectx_typing E D Q M T (typ_with T1 T2) ->
      ectx_typing E D Q (ectx_snd M) T T2
  | ectx_typing_mpairl : forall E D1 D2 D3 Q1 Q2 Q3 M e T T1 T2 He,
      ectx_typing E D1 Q1 M T T1 ->
      typing E D2 Q2 e T2 ->
      lenv_split E Q3 D1 D2 D3 ->
      cenv_split_exp E Q1 Q2 Q3 ->
      ectx_typing E D3 Q3 (ectx_mpairl e M He) T (typ_tensor T1 T2)
  | ectx_typing_mpairr : forall E D1 D2 D3 Q1 Q2 Q3 v M T T1 T2 Hv,
      typing E D1 Q1 v T1 ->
      ectx_typing E D2 Q2 M T T2 ->
      lenv_split E Q3 D1 D2 D3 ->
      cenv_split_exp E Q1 Q2 Q3 ->
      ectx_typing E D3 Q3 (ectx_mpairr v Hv M) T (typ_tensor T1 T2)
  | ectx_typing_let : forall E D1 D2 D3 Q1 Q2 Q3 M e T T1 T2 T3 He,
      ectx_typing E D1 Q1 M T (typ_tensor T1 T2) ->
      typing E D2 Q2 e (typ_arrow T1 (typ_arrow T2 T3)) ->
      lenv_split E Q3 D1 D2 D3 ->
      cenv_split_exp E Q1 Q2 Q3 ->
      ectx_typing E D3 Q3 (ectx_let e M He) T T3
  | ectx_typing_inl : forall E D Q M T T1 T2 Ht,
      ectx_typing E D Q M T T1 ->
      ectx_typing E D Q (ectx_inl (typ_plus T1 T2) Ht M) T (typ_plus T1 T2)
  | ectx_typing_inr : forall E D Q M T T1 T2 Ht,
      ectx_typing E D Q M T T2 ->
      ectx_typing E D Q (ectx_inr (typ_plus T1 T2) Ht M) T (typ_plus T1 T2)
  | ectx_typing_case : forall E D1 D2 D3 Q1 Q2 Q3 M e1 e2 T T1 T2 T3 He1 He2,
      ectx_typing E D1 Q1 M T (typ_plus T1 T2) ->
      typing E D2 Q2 e1 (typ_arrow T1 T3) ->
      typing E D2 Q2 e2 (typ_arrow T2 T3) ->
      lenv_split E Q3 D1 D2 D3 ->
      cenv_split_exp E Q1 Q2 Q3 ->
      ectx_typing E D3 Q3 (ectx_case e1 e2 M He1 He2) T T3
  | ectx_typing_go : forall E D Q M T T1 T2 Ht,
      ectx_typing E D Q M T (typ_arrow T1 typ_answer) ->
      dual E T1 T2 ->
      ectx_typing E D Q (ectx_go T1 Ht M) T T2
  | ectx_typing_yield : forall E D Q M T T',
      ectx_typing E D Q M T (typ_src T') ->
      ectx_typing E D Q (ectx_yield M) T T'
.


(* ********************************************************************** *)
(** * #<a name="reduction"></a># Reduction *)

Inductive red : exp -> exp -> Prop :=
  | red_seq : forall e2,
      expr (exp_seq exp_unit e2) ->
      red (exp_seq exp_unit e2) e2
  | red_app : forall T e1 v2,
      value (exp_abs T e1) ->
      value v2 ->
      red (exp_app (exp_abs T e1) v2) (open_ee e1 v2)
  | red_fst : forall e1 e2,
      value (exp_apair e1 e2) ->
      red (exp_fst (exp_apair e1 e2)) e1
  | red_snd : forall e1 e2,
      value (exp_apair e1 e2) ->
      red (exp_snd (exp_apair e1 e2)) e2
  | red_let : forall v1 v2 e3,
      value (exp_mpair v1 v2) ->
      expr e3 ->
      red (exp_let (exp_mpair v1 v2) e3) (exp_app (exp_app e3 v1) v2)
  | red_inl : forall v1 T e2 e3,
      value (exp_inl T v1) ->
      expr e2 ->
      expr e3 ->
      red (exp_case (exp_inl T v1) e2 e3) (exp_app e2 v1)
  | red_inr : forall v1 T e2 e3,
      value (exp_inr T v1) ->
      expr e2 ->
      expr e3 ->
      red (exp_case (exp_inr T v1) e2 e3) (exp_app e3 v1)
  | red_yield_abs : forall T e1,
      value (exp_abs (typ_arrow T typ_answer) e1) ->
      red (exp_yield (exp_abs (typ_arrow T typ_answer) e1))
        (exp_app
           (exp_abs (typ_tensor T typ_unit) (exp_let (exp_bvar 0)
              (exp_abs T (exp_abs typ_unit (exp_seq (exp_bvar 0) (exp_bvar 1))))))
           (exp_yield (exp_go (typ_arrow T typ_answer)
              (exp_abs (typ_arrow T typ_answer) e1))))
  | red_yield_snk : forall C T,
      value (exp_snk C T) ->
      red (exp_yield (exp_snk C (typ_src T)))
        (exp_app
           (exp_abs (typ_tensor T typ_unit) (exp_let (exp_bvar 0)
              (exp_abs T (exp_abs typ_unit (exp_seq (exp_bvar 0) (exp_bvar 1))))))
           (exp_yield (exp_go (typ_arrow T typ_answer)
              (exp_snk C (typ_src T)))))
  | red_app_src : forall C T v2,
      value (exp_src C T) ->
      value v2 ->
      red (exp_app (exp_src C T) v2) (exp_app v2 (exp_yield (exp_src C T)))
.

(*Inductive exp_gadgets : env -> cenv -> exp -> Prop :=
  | exp_gadgets_var : forall E x, 
      exp_gadgets E cempty (exp_fvar x)
  | exp_gadgets_unit : forall E,
      exp_gadgets E cempty (exp_unit)
  | exp_gadgets_seq : forall E Q Q1 Q2 e1 e2,
      cenv_split_exp E Q1 Q2 Q ->
      exp_gadgets E Q1 e1 ->
      exp_gadgets E Q2 e2 ->
      exp_gadgets E Q (exp_seq e1 e2)
  | exp_gadgets_abs : forall L E Q T e,
      (forall x, x `notin` L -> exp_gadgets E Q (open_ee e x)) ->
       exp_gadgets E Q (exp_abs T e)
  | exp_gadgets_app : forall E Q Q1 Q2 e1 e2,
      cenv_split_exp E Q1 Q2 Q ->
      exp_gadgets E Q1 e1 ->
      exp_gadgets E Q2 e2 ->
      exp_gadgets E Q (exp_app e1 e2)
  | exp_gadgets_apair : forall E Q e1 e2,
      exp_gadgets E Q e1 ->
      exp_gadgets E Q e2 ->
      exp_gadgets E Q (exp_apair e1 e2)
  | exp_gadgets_fst : forall E Q e,
      exp_gadgets E Q e ->
      exp_gadgets E Q (exp_fst e)
  | exp_gadgets_snd : forall E Q e,
      exp_gadgets E Q e ->
      exp_gadgets E Q (exp_snd e)
  | exp_gadgets_mpair : forall E Q Q1 Q2 e1 e2,
      cenv_split_exp E Q1 Q2 Q ->
      exp_gadgets E Q1 e1 ->
      exp_gadgets E Q2 e2 ->
      exp_gadgets E Q (exp_mpair e1 e2)
  | exp_gadgets_let : forall E Q Q1 Q2 e1 e2,
      cenv_split_exp E Q1 Q2 Q ->
      exp_gadgets E Q1 e1 ->
      exp_gadgets E Q2 e2 ->
      exp_gadgets E Q (exp_let e1 e2)
  | exp_gadgets_inl : forall E Q e T,
      exp_gadgets E Q e ->
      exp_gadgets E Q (exp_inl T e)
  | exp_gadgets_inr : forall E Q e T,
      exp_gadgets E Q e ->
      exp_gadgets E Q (exp_inr T e)
  | exp_gadgets_case : forall E Q Q1 Q2 e1 e2 e3,
      cenv_split_exp E Q1 Q2 Q ->
      exp_gadgets E Q1 e1 ->
      exp_gadgets E Q2 e2 ->
      exp_gadgets E Q2 e3 ->
      exp_gadgets E Q (exp_case e1 e2 e3)
  | exp_gadgets_go : forall E Q e T,
      exp_gadgets E Q e ->
      exp_gadgets E Q (exp_go T e)
  | exp_gadgets_yield : forall E Q e,
      exp_gadgets E Q e ->
      exp_gadgets E Q (exp_yield e)
  | exp_gadgets_done : forall E X,
      exp_gadgets E [(X, cbind_proto cdir_both typ_answer)] (rt_done X)
  | exp_gadgets_endsnk : forall E X,
      exp_gadgets E [(X, cbind_proto cdir_snk typ_answer)] (rt_endsnk X)
  | exp_gadgets_endsrc : forall E X,
      exp_gadgets E [(X, cbind_proto cdir_src typ_unit)] (rt_endsrc X)
  | exp_gadgets_rt_abs : forall E X T1 T2 e,
      snk E (typ_arrow T1 T2) (fchan X) (rt_abs (fchan X) T1 e) ->
      exp_gadgets E [(X, cbind_proto cdir_snk (typ_arrow T1 T2))] (rt_abs (fchan X) T1 e)
  | exp_gadgets_rt_app : forall E X T1 T2 e,
      src E (typ_arrow T1 T2) (fchan X) (rt_app (fchan X) T1 e) ->
      exp_gadgets E [(X, cbind_proto cdir_src (typ_arrow T1 T2))] (rt_app (fchan X) T1 e)
  | exp_gadgets_rt_apair : forall E X T1 T2 e1 e2,
      snk E (typ_with T1 T2) (fchan X) (rt_apair (fchan X) e1 e2) ->
      exp_gadgets E [(X, cbind_proto cdir_snk (typ_with T1 T2))] (rt_apair (fchan X) e1 e2)
  | exp_gadgets_rt_select : forall E X T1 T2 e1 e2,
      src E (typ_with T1 T2) (fchan X) (rt_select (fchan X) e1 e2) ->
      exp_gadgets E [(X, cbind_proto cdir_src (typ_with T1 T2))] (rt_select (fchan X) e1 e2)
.

Inductive proc_gadgets : cenv -> proc -> Prop :=
  | proc_gadgets_exp : forall Q e,
      exp_gadgets empty Q e ->
      proc_gadgets Q (proc_exp e)
  | proc_gadgets_par : forall Q Q1 Q2 P1 P2,
      cenv_split_proc empty Q1 Q2 Q ->
      proc_gadgets Q1 P1 ->
      proc_gadgets Q2 P2 ->
      proc_gadgets Q (proc_par P1 P2)
  | proc_gadgets_new : forall L Q T P,
      (forall X, X `notin` L -> proc_gadgets ([(X, cbind_proto cdir_both T)] ++ Q)
         (open_cp P X)) ->
      proc_gadgets Q (proc_new T P)
.*)

Inductive canon_inner : proc -> Prop :=
  | canon_inner_exp : forall e,
      expr e ->
      canon_inner (proc_exp e)
  | canon_inner_par : forall e P,
      expr e ->
      canon_inner P ->
      canon_inner (proc_par (proc_exp e) P)
.

Inductive canon_outer : proc -> Prop :=
  | canon_outer_par :forall P,
      canon_inner P ->
      canon_outer P
  | canon_outer_new : forall L T P,
      (forall X, X `notin` L -> canon_outer (open_cp P X)) ->
      canon_outer (proc_new T P)
.

Inductive proc_eq : proc -> proc -> Prop :=
  | eq_refl : forall P1,
      process P1 ->
      proc_eq P1 P1
  | eq_sym : forall P1 P2,
      proc_eq P1 P2 ->
      proc_eq P2 P1
  | eq_trans : forall P1 P2 P3,
      proc_eq P1 P2 ->
      proc_eq P2 P3 ->
      proc_eq P1 P3
  | eq_par : forall P1 P2 P1' P2',
      proc_eq P1 P1' ->
      proc_eq P2 P2' ->
      proc_eq (proc_par P1 P2) (proc_par P1' P2')
  | eq_new : forall L T P1 P1',
      (forall X, X `notin` L -> proc_eq (open_cp P1 X) (open_cp P1' X)) ->
      proc_eq (proc_new T P1) (proc_new T P1')
  | eq_comm : forall P1 P2 P1' P2',
      proc_eq P1 P1' ->
      proc_eq P2 P2' ->
      proc_eq (proc_par P1 P2) (proc_par P2' P1')
  | eq_assoc : forall P1 P2 P3 P1' P2' P3',
      proc_eq P1 P1' ->
      proc_eq P2 P2' ->
      proc_eq P3 P3' ->
      proc_eq (proc_par (proc_par P1 P2) P3) (proc_par P1' (proc_par P2' P3'))
  | eq_swap : forall L T1 T2 P1 P1',
      process (proc_new T1 (proc_new T2 P1)) ->
      process (proc_new T2 (proc_new T1 P1')) ->
      (forall X Y, X `notin` L -> Y `notin` (singleton X `union` L) ->
         (open_cp (open_cp_rec 1 Y P1) X) = (open_cp (open_cp_rec 1 X P1') Y)) ->
      proc_eq (proc_new T1 (proc_new T2 P1)) (proc_new T2 (proc_new T1 P1'))
  | eq_extrude : forall T P1 P2,
      process P2 ->
      process (proc_new T (proc_par P1 P2)) ->
      proc_eq (proc_new T (proc_par P1 P2))
                    (proc_par (proc_new T P1) P2)
.

Inductive proc_eq1 : proc -> proc -> Prop :=
  | proc_eq1_parl : forall P1 P1' P2,
      proc_eq1 P1 P1' ->
      proc_eq1 (proc_par P1 P2) (proc_par P1' P2)
  | proc_eq1_new : forall L P1 P1' T,
      (forall X, X `notin` L ->
         proc_eq1 (open_cp P1 X) (open_cp P1' X)) ->
      proc_eq1 (proc_new T P1) (proc_new T P1')
  | proc_eq1_comm : forall P1 P2,
      proc_eq1 (proc_par P1 P2) (proc_par P2 P1)
  | proc_eq1_assoc : forall P1 P2 P3,
      proc_eq1 (proc_par (proc_par P1 P2) P3) (proc_par P1 (proc_par P2 P3))
  | proc_eq1_swap : forall L T1 T2 P1 P1',
      (forall X Y, X `notin` L -> Y `notin` (singleton X `union` L) ->
        (open_cp (open_cp_rec 1 Y P1) X) = (open_cp (open_cp_rec 1 X P1') Y)) ->
      proc_eq1 (proc_new T1 (proc_new T2 P1)) (proc_new T2 (proc_new T1 P1'))
  | proc_eq1_extrude :  forall T P1 P2,
      process P2 ->
      proc_eq1 (proc_new T (proc_par P1 P2)) (proc_par (proc_new T P1) P2)
.

Inductive proc_eqm : proc -> proc -> Prop :=
  | proc_eqm_refl : forall P,
      proc_eqm P P
  | proc_eqm_left : forall P1 P2 P3,
      proc_eq1 P1 P2 ->
      proc_eqm P2 P3 ->
      proc_eqm P1 P3
  | proc_eqm_right : forall P1 P2 P3,
      proc_eq1 P2 P1 ->
      proc_eqm P2 P3 ->
      proc_eqm P1 P3
.

Inductive proc_red : proc -> proc -> Prop :=
  | red_ectx : forall e1 e2 M f1 f2,
      red e1 e2 ->
      plug M e1 f1 ->
      plug M e2 f2 ->
      proc_red (proc_exp f1) (proc_exp f2)
  | red_done : forall P1,
      process (proc_par P1 (proc_new typ_answer (exp_done (bchan 0)))) ->
      proc_red (proc_par P1 (proc_new typ_answer (exp_done (bchan 0)))) P1
  | red_par : forall P1 P2 P2',
      process (proc_par P1 P2) ->
      proc_red P2 P2' ->
      proc_red (proc_par P1 P2) (proc_par P1 P2')
  | red_new : forall L T P1 P1',
      process (proc_new T P1) ->
      (forall X, X `notin` L -> proc_red (open_cp P1 X) (open_cp P1' X)) ->
      proc_red (proc_new T P1) (proc_new T P1')
  | red_go : forall M T v f f1,
      value v ->
      type T ->
      plug M (exp_go T v) f ->
      plug M (exp_src (bchan 0) T) f1 ->
      proc_red f (proc_new T (proc_par f1 (exp_app v (exp_snk (bchan 0) T))))
  | red_pass : forall T1 T2 M1 M2 v f1 f2 f1' f2',
      value v ->
      type (typ_arrow T1 T2) ->
      plug M1 (exp_yield (exp_src (bchan 0) (typ_arrow T1 T2))) f1 ->
      plug M2 (exp_app (exp_snk (bchan 0) (typ_arrow T1 T2)) v) f2 ->
      plug M1 (exp_mpair v (exp_src (bchan 0) T2)) f1' ->
      plug M2 (exp_snk (bchan 0) T2) f2' ->
      proc_red
        (proc_new (typ_arrow T1 T2) (proc_par f1 f2))
        (proc_new T2 (proc_par f1' f2'))
  | red_left : forall T1 T2 T' M1 M2 f1 f2 f1' f2', (* Change *)
      type (typ_with T1 T2) ->
      dual empty (typ_with T1 T2) (typ_src T') ->
      plug M1 (exp_yield (exp_src (bchan 0) (typ_with T1 T2))) f1 ->
      plug M2 (exp_fst (exp_snk (bchan 0) (typ_with T1 T2))) f2 ->
      plug M1 (exp_inl T' (exp_src (bchan 0) T1)) f1' ->
      plug M2 (exp_snk (bchan 0) T1) f2' ->
      proc_red
        (proc_new (typ_with T1 T2) (proc_par f1 f2))
        (proc_new T1 (proc_par f1' f2'))
  | red_right : forall T1 T2 T' M1 M2 f1 f2 f1' f2', (* Change also *)
      type (typ_with T1 T2) ->
      dual empty (typ_with T1 T2) (typ_src T') ->
      plug M1 (exp_yield (exp_src (bchan 0) (typ_with T1 T2))) f1 ->
      plug M2 (exp_snd (exp_snk (bchan 0) (typ_with T1 T2))) f2 ->
      plug M1 (exp_inr T' (exp_src (bchan 0) T2)) f1' ->
      plug M2 (exp_snk (bchan 0) T2) f2' ->
      proc_red
        (proc_new (typ_with T1 T2) (proc_par f1 f2))
        (proc_new T2 (proc_par f1' f2'))
  | red_close : forall M1 M2 f1 f2 f1' f2',
      plug M1 (exp_src (bchan 0) typ_answer) f1 ->
      plug M2 (exp_snk (bchan 0) typ_answer) f2 ->
      plug M1 exp_unit f1' ->
      plug M2 (exp_done (bchan 0)) f2' ->
      proc_red
        (proc_new typ_answer (proc_par f1 f2))
        (proc_new typ_answer (proc_par f1' f2'))
(*  | red_eq : forall P1 P2 P1' P2',
      process P1 ->
      proc_eq P1 P1' ->
      proc_red P1' P2' ->
      proc_eq P2' P2 ->
      proc_red P1 P2*)
.

(* ********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

(** We declare most constructors as [Hint]s to be used by the [auto]
      and [eauto] tactics.  We exclude constructors from the typing and
      process typing relations that use cofinite quantification.  It is
      unlikely that [eauto] will find an instantiation for the finite
      set [L], and in those cases, [eauto] can take some time to fail.
      (A priori, this is not obvious.  In practice, one adds as hints
      all constructors and then later removes some constructors when
      they cause proof search to take too long.) *)

Hint Constructors type channel expr value process plug red proc_red.
Hint Constructors wf_typ wf_proto wf_env wf_lenv wf_cenv vwf_envs wf_chan.
(*Hint Constructors (*wf_cenv_acc wf_cenvs_aux wf_cenvs*) nd_cons_cenvs.*)
Hint Constructors cenv_split_multi cenvs_split_multi cenvs_split_simple cenvs_split.
Hint Constructors lenv_split lenv_agree cenv_split_exp cenv_split_proc cenv_agree.
Hint Constructors canon_inner cdir (*covers src snk*) dual disjoints.
Hint Resolve typing_var typing_unit typing_seq typing_app.
Hint Resolve typing_apair typing_fst typing_snd typing_mpair typing_let.
Hint Resolve typing_inl typing_inr typing_case typing_go.
Hint Resolve typing_snk typing_src typing_done.
Hint Resolve typing_exp typing_parl typing_parr.
(*Hint Resolve exp_gadgets_var exp_gadgets_seq exp_gadgets_app.
Hint Resolve exp_gadgets_apair exp_gadgets_fst exp_gadgets_snd.
Hint Resolve exp_gadgets_mpair exp_gadgets_let exp_gadgets_go.
Hint Resolve exp_gadgets_inl exp_gadgets_inr exp_gadgets_case.
Hint Resolve exp_gadgets_done exp_gadgets_endsnk exp_gadgets_endsrc.
Hint Resolve exp_gadgets_rt_abs exp_gadgets_rt_app.
Hint Resolve exp_gadgets_rt_apair exp_gadgets_rt_select.*)
Hint Resolve (*proc_gadgets_exp proc_gadgets_par*) canon_outer_par.
Hint Resolve eq_refl eq_sym eq_trans eq_par eq_comm eq_assoc.
Hint Resolve proc_eq1_parl proc_eq1_comm proc_eq1_assoc proc_eq1_extrude.
Hint Resolve proc_eqm_refl proc_eqm_left proc_eqm_right.

(* ********************************************************************** *)
(** * #<a name="cases"></a># Cases Tactic *)

Tactic Notation "typ_cases" tactic(first) tactic(c) :=
  first;
  [ c "typ_unit" |  c "typ_answer" | c "typ_arrow" 
    c "typ_with" | c "typ_tensor" | c "typ_plus" ].

Tactic Notation "chan_cases" tactic(first) tactic(c) :=
  first;
  [ c "bchan" | c "fchan" ].

Tactic Notation "exp_cases" tactic(first) tactic(c) :=
  first;
  [ c "exp_bvar" |  c "exp_fvar" | 
    c "exp_unit" | c "exp_seq" |
    c "exp_abs" | c "exp_app" |
    c "exp_apair" | c "exp_fst" | c "exp_snd" |
    c "exp_mpair" | c "exp_let" |
    c "exp_inl" | c "exp_inr" | c "exp_case" |
    c "exp_go" | c "exp_yield" |
    c "exp_snk" | c "exp_src" | c "exp_done" ].

Tactic Notation "proc_cases" tactic(first) tactic(c) :=
  first;
  [ c "proc_exp" | c "proc_par" | c "proc_new" ].

Tactic Notation "type_cases" tactic(first) tactic(c) :=
  first;
  [ c "type_triv" ].

Tactic Notation "expr_cases" tactic(first) tactic(c) :=
  first;
  [ c "expr_var" | c "expr_unit" | c "expr_seq" |
    c "expr_abs" | c "expr_app" |
    c "expr_apair" | c "expr_fst" | c "expr_snd" |
    c "expr_mpair" | c "expr_let" |
    c "expr_inl" | c "expr_inr" | c "expr_case" |
    c "expr_go" | c "expr_yield" |
    c "expr_snk" | c "expr_src" | c "expr_done" ].

Tactic Notation "process_cases" tactic(first) tactic(c) :=
  first;
  [ c "process_exp" | c "process_par" | c "process_new" ].

Tactic Notation "wf_typ_cases" tactic(first) tactic(c) :=
  first;
  [ c "wf_typ_triv" ].

Tactic Notation "wf_proto_cases" tactic(first) tactic(c) :=
  first;
  [ c "wf_proto_answer" | c "wf_proto_arrow" | c "wf_proto_with" ].

Tactic Notation "wf_env_cases" tactic(first) tactic(c) :=
  first;
  [ c "wf_env_empty" | c "wf_env_kn" ].

Tactic Notation "wf_lenv_cases" tactic(first) tactic(c) :=
  first;
  [ c "wf_lenv_empty" | c "wf_lenv_typ" ].

Tactic Notation "wf_cenv_cases" tactic(first) tactic(c) :=
  first;
  [ c "wf_cenv_empty" | c "wf_cenv_proto" ].

(*Tactic Notation "wf_cenv_acc_cases" tactic(first) tactic(c) :=
  first;
  [ c "wf_cenv_acc_empty" | c "wf_cenv_acc_fresh"
  | c "wf_cenv_acc_snksrc" | c "wf_cenv_acc_srcsnk" ].

Tactic Notation "wf_cenvs_aux_cases" tactic(first) tactic(c) :=
  first;
  [ c "wf_cenvs_aux_nil" | c "wf_cenvs_aux_cons" ].*)

Tactic Notation "vwf_envs_cases" tactic(first) tactic(c) :=
  first;
  [ c "vwf_envs_empty" | c "vwf_envs_typ" ].

Tactic Notation "lenv_split_cases" tactic(first) tactic(c) :=
  first;
  [ c "lenv_split_empty" | c "lenv_split_left" | c "lenv_split_right" ].

Tactic Notation "lenv_agree_cases" tactic(first) tactic(c) :=
  first;
  [ c "lenv_agree_empty" | c "lenv_agree_both" |
    c "lenv_agree_left" | c "lenv_agree_right"  ].

Tactic Notation "cenv_split_exp_cases" tactic(first) tactic(c) :=
  first;
  [ c "cenv_split_exp_empty" | c "cenv_split_exp_left" | c "cenv_split_exp_right" ].

Tactic Notation "cenv_split_proc_cases" tactic(first) tactic(c) :=
  first;
  [ c "cenv_split_proc_empty" | c "cenv_split_proc_left" | c "cenv_split_proc_right" |
    c "cenv_split_proc_snksrc" | c "cenv_split_proc_srcsnk" ].

Tactic Notation "cenv_split_multi_cases" tactic(first) tactic(c) :=
  first;
  [ c "cenv_split_multi_empty" | c "cenv_split_multi_leaf" | c "cenv_split_multi_branch" ].

Tactic Notation "cenvs_split_simple_cases" tactic(first) tactic(c) :=
  first;
  [ c "cenvs_split_simple_nil" | c "cenvs_split_simple_left" | c "cenvs_split_simple_right" ].

Tactic Notation "cenvs_split_multi_cases" tactic(first) tactic(c) :=
  first;
  [ c "cenvs_split_multi_nil" | c "cenvs_split_multi_cons" ].

Tactic Notation "cenv_agree_cases" tactic(first) tactic(c) :=
  first;
  [ c "cenv_agree_empty" | c "cenv_agree_both" |
    c "cenv_agree_left" | c "cenv_agree_right"  ].

Tactic Notation "value_cases" tactic(first) tactic(c) :=
  first;
  [ c "value_unit" | c "value_abs" | c "value_apair" |
    c "value_mpair" | c "value_inl" | c "value_inr" |
    c "value_snk" | c "value_src" | c "value_done" ].

Tactic Notation "ectx_cases" tactic(first) tactic(c) :=
  first;
  [ c "ectx_hole" | c "ectx_seq" | c "ectx_appl" | c "ectx_appr" |
    c "ectx_fst" | c "ectx_snd" | c "ectx_mpairl" | c "ectx_mpairr" | c "ectx_let" |
    c "ectx_inl" | c "ectx_inr" | c "ectx_case" | c "ectx_go" | c "ectx_yield" ].

Tactic Notation "plug_cases" tactic(first) tactic(c) :=
  first;
  [ c "plug_hole" | c "plug_seq" | c "plug_appl" | c "plug_appr" |
    c "plug_fst" | c "plug_snd" | c "plug_mpairl" | c "plug_mpairr" | c "plug_let" |
    c "plug_inl" | c "plug_inr" | c "plug_case" | c "plug_go" | c "plug_yield" ].

Tactic Notation "dual_cases" tactic(first) tactic(c) :=
  first;
  [ c "dual_answer" | c "dual_arrow" | c "dual_with" ].

(*Tactic Notation "covers_cases" tactic(first) tactic(c) :=
  first;
  [ c "covers_refl" | c "covers_both" ].*)

Tactic Notation "typing_cases" tactic(first) tactic(c) :=
  first;
  [ c "typing_var" | c "typing_unit" | c "typing_seq" |
    c "typing_abs" | c "typing_app" |
    c "typing_apair" | c "typing_fst" | c "typing_snd" |
    c "typing_mpair" | c "typing_let" |
    c "typing_inl" | c "typing_inr" | c "typing_case" |
    c "typing_go" | c "typing_yield" |
    c "typing_snk" | c "typing_src" | c "typing_done" ].

Tactic Notation "disjoints_cases" tactic(first) tactic(c) :=
  first;
  [ c "disjoints_nil" | c "disjoints_cons" ].

Tactic Notation "nd_cons_cenvs_cases" tactic(first) tactic(c) :=
  first;
  [ c "nd_cons_cenvs_fresh" | c "nd_cons_cenvs_cons" ].

Tactic Notation "proc_typing_cases" tactic(first) tactic(c) :=
  first;
  [ c "typing_exp" | c "typing_parl" | c "typing_parr" | c "typing_new" ].

Tactic Notation "ectx_typing_cases" tactic(first) tactic(c) :=
  first;
  [ c "ectx_typing_hole" | c "ectx_typing_seq" |
    c "ectx_typing_appl" | c "ectx_typing_appr" |
    c "ectx_typing_fst" | c "ectx_typing_snd" |
    c "ectx_typing_mpairl" | c "ectx_typing_mpairr" | c "ectx_typing_let" |
    c "ectx_typing_inl" | c "ectx_typing_inr" | c "ectx_typing_case" |
    c "ectx_typing_go" | c "ectx_typing_yield" ].

(*Tactic Notation "exp_gadgets_cases" tactic(first) tactic(c) :=
  first;
  [ c "exp_gadgets_var" | c "exp_gadgets_unit" | c "exp_gadgets_seq" |
    c "exp_gadgets_abs" | c "exp_gadgets_app" |
    c "exp_gadgets_apair" | c "exp_gadgets_fst" | c "exp_gadgets_snd" |
    c "exp_gadgets_mpair" | c "exp_gadgets_let" |
    c "exp_gadgets_inl" | c "exp_gadgets_inr" | c "exp_gadgets_case" |
    c "exp_gadgets_go" | c "exp_gadgets_yield" |
    c "exp_gadgets_rt_done" | c "exp_gadgets_rt_endsnk" | c "exp_gadgets_rt_endsrc" |
    c "exp_gadgets_rt_abs" | c "exp_gadgets_rt_app" |
    c "exp_gadgets_rt_apair" | c "exp_gadgets_rt_select" ].

Tactic Notation "proc_gadgets_cases" tactic(first) tactic(c) :=
  first;
  [ c "proc_gadgets_exp" | c "proc_gadgets_par" | c "proc_gadgets_new" ].*)

Tactic Notation "red_cases" tactic(first) tactic(c) :=
  first;
  [ c "red_seq" | c "red_app" | c "red_fst" | c "red_fst" | 
    c "red_let" | c "red_inl" | c "red_inr" |
    c "red_yield_abs" | c "red_yield_snk" | c "red_app_src" ].

(*Tactic Notation "snk_cases" tactic(first) tactic(c) :=
  first;
  [ c "snk_answer" | c "snk_arrow" | c "snk_with" ].

Tactic Notation "src_cases" tactic(first) tactic(c) :=
  first;
  [ c "src_answer" | c "src_arrow" | c "src_with" ].*)

Tactic Notation "canon_inner_cases" tactic(first) tactic(c) :=
  first;
  [ c "canon_inner_exp" | c "canon_inner_par" ].

Tactic Notation "canon_outer_cases" tactic(first) tactic(c) :=
  first;
  [ c "canon_outer_par" | c "canon_outer_new" ].

Tactic Notation "proc_eq_cases" tactic(first) tactic(c) :=
  first;
  [ c "eq_refl" | c "eq_sym" | c "eq_trans" | c "eq_par" | c "eq_new" |
    c "eq_comm" | c "eq_assoc" | c "eq_swap" | c "eq_extrude" ].

Tactic Notation "proc_eq1_cases" tactic(first) tactic(c) :=
  first;
  [ c "proc_eq1_parl" | c "proc_eq1_new" | c "proc_eq1_comm" |
    c "proc_eq1_assoc" | c "proc_eq1_swap" | c "proc_eq1_extrude" ].

Tactic Notation "proc_eqm_cases" tactic(first) tactic(c) :=
  first;
  [ c "proc_eqm_refl" | c "proc_eqm_left" | c "proc_eqm_right" ].

Tactic Notation "proc_red_cases" tactic(first) tactic(c) :=
  first;
  [ c "red_ectx" | c "red_done" | c "red_par" | c "red_new" | c "red_go" |
    c "red_pass" | c "red_left" | c "red_right" | c "red_close" ].
