(** Authors: Jianzhou Zhao. *)

Require Export Bang_OParametricity_Pre.
Require Import Bang_Renaming.
Require Import Program.

Module Type IOParametricity.

(* ********************************************************************** *)
(** * Axioms for atoms *)

Axiom typvars_neq_termvars : forall X x E (lE:lenv),
  X `in` ddom_env E ->
  x `in` dom lE ->
  X <> x.

Axiom disjoint_termvars : forall (lEnv:lenv) (gsubst:gamma_subst),
  disjoint lEnv gsubst.

(* ********************************************************************** *)
(** * Wf Relations *)

Definition wfor (E:env) (r : rel) (T T' : typ) : Prop :=
  (wf_typ E T) /\
  (wf_typ E T')
  .

Axiom wfor_inv : forall E r T T',
  wfor E r T T'->
  (wf_typ E T) /\
  (wf_typ E T')
  .

Axiom wfor_left_inv : forall E t t' R,
  wfor E R t t' -> wf_typ E t.

Axiom wfor_right_inv : forall E t t' R,
  wfor E R t t' -> wf_typ E t'.

(* ********************************************************************** *)
(** * Value Relations *)
Program Fixpoint F_Related_ovalues
    (t:typ) (rsubst:rho_subst)
    (dsubst dsubst':delta_subst) (v:exp) (v':exp) (Env:env) (lEnv:lenv) {measure typ_size t} : Prop :=
  match t with
  | typ_fvar X =>
    exists R,
    (binds X R rsubst) /\ (value v) /\ (value v') /\ (R v v')
  | typ_arrow t1 t2 =>
    (value v) /\ (value v') /\
    (forall lEnv1 x x',
       typing Env lEnv1 x (apply_delta_subst_typ dsubst t1) ->
       typing Env lEnv1 x' (apply_delta_subst_typ dsubst' t1) ->
       wf_lenv Env (lEnv1++lEnv) ->
       (exists w, exists w',
        normalize x w /\ normalize x' w' /\
       F_Related_ovalues t1 rsubst dsubst dsubst' w w' Env lEnv1) ->
       (exists u, exists u', 
        normalize (exp_app v x) u /\
        normalize (exp_app v' x') u' /\
        F_Related_ovalues t2 rsubst dsubst dsubst' u u' Env (lEnv1++lEnv))
    )
  | typ_all t1 =>
      (
      (value v) /\ (value v') /\
      (exists L,
         (forall (X:atom) t2 t2' R (Fr:X `notin` L),
          wfor Env R t2 t2' ->
          X `notin` ((dom rsubst) `union` (fv_tt t1)) ->
          (exists w, exists w',
          normalize (exp_tapp v t2) w /\
          normalize (exp_tapp v' t2') w' /\
          F_Related_ovalues (open_tt t1 X)
                           ([(X,R)]++rsubst)
                           ([(X,t2)]++dsubst)
                           ([(X,t2')]++dsubst')
                            w w' Env lEnv)
        ))
      )
  | typ_bang t1 =>
    (value v) /\ (value v') /\
    (exists e1, exists e1', 
      v = exp_bang e1 /\
      v' = exp_bang e1' /\
      (exists u1, exists u1',
       normalize e1 u1 /\
       normalize e1' u1' /\
       F_Related_ovalues t1 rsubst dsubst dsubst' u1 u1' Env lEnv)
    )
  | typ_with t1 t2 =>
    (value v) /\ (value v') /\
    (exists e1, exists e2, exists e1', exists e2',
      v = exp_apair e1 e2 /\
      v' = exp_apair e1' e2' /\
      (exists u1, exists u1',
       normalize e1 u1 /\
       normalize e1' u1' /\
       F_Related_ovalues t1 rsubst dsubst dsubst' u1 u1' Env lEnv) /\
      (exists u2, exists u2',
       normalize e2 u2 /\
       normalize e2' u2' /\
       F_Related_ovalues t2 rsubst dsubst dsubst' u2 u2' Env lEnv)
    )
  | _ => False
  end
  .
Obligation 1.
  simpl. omega.
Qed.
Next Obligation.
  rewrite <- Heq_t. simpl. omega.
Qed.
Next Obligation.
  simpl. 
  assert (typ_size (open_tt t1 X) = typ_size t1). apply open_tt_typ_size_eq.
  omega.
Qed.
Next Obligation.
  simpl.  omega.
Qed.
Next Obligation.
  simpl.  omega.
Qed.
Next Obligation.
  split.
    intros t1 t2. unfold not. intro C. inversion C.
  split.
    intros t1. unfold not. intro C. inversion C.
  split.
    intros t1. unfold not. intro C. inversion C.
  split.
    intros t1 t2. unfold not. intro C. inversion C.
    intros X. unfold not. intro C. inversion C.
Qed.

(** * Term Relations *)
Definition F_Related_oterms t rsubst (dsubst dsubst':delta_subst) e e' Env lEnv: Prop:=
    exists v, exists v',
    typing Env lEnv e (apply_delta_subst_typ dsubst t) /\
    typing Env lEnv e' (apply_delta_subst_typ dsubst' t) /\
    normalize e v /\
    normalize e' v' /\
    F_Related_ovalues t rsubst dsubst dsubst' v v' Env lEnv
  .

(** * Subst Relations *)
Inductive F_Related_osubst : env -> lenv -> gamma_subst -> gamma_subst -> gamma_subst -> gamma_subst -> rho_subst -> delta_subst -> delta_subst -> env -> lenv -> Prop:=
  | F_Related_osubst_empty :
    forall Env, 
      wf_env Env ->
      F_Related_osubst nil nil gamma_nil gamma_nil gamma_nil gamma_nil rho_nil delta_nil delta_nil Env nil
  | F_Related_osubst_kind :
    forall (E:env) (lE:lenv) (gsubst gsubst' lgsubst lgsubst':gamma_subst) (rsubst:rho_subst) (dsubst dsubst':delta_subst) Env lEnv X R t t',
      F_Related_osubst E lE gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
      X `notin` (fv_env E) `union` (fv_lenv lE) `union`  (fv_env Env) `union` (fv_lenv lEnv) ->
      wfor Env R t t' ->
      F_Related_osubst ([(X, bind_kn)]++E) lE gsubst gsubst' lgsubst lgsubst'
                                   ([(X,R)]++rsubst) ([(X,t)]++dsubst) ([(X,t')]++dsubst') Env lEnv
  | F_Related_osubst_typ :
    forall (E:env)(lE:lenv)(gsubst gsubst' lgsubst lgsubst':gamma_subst) (e e':exp) (t:typ) (rsubst:rho_subst) (dsubst dsubst':delta_subst) Env lEnv (x:atom),
      F_Related_osubst E lE gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
      typing Env lempty e (apply_delta_subst_typ dsubst t) ->
      typing Env lempty e' (apply_delta_subst_typ dsubst' t) ->
      F_Related_oterms t rsubst dsubst dsubst' e e' Env lempty ->
      x `notin` ((fv_env E) `union` (fv_lenv lE) `union` (fv_tt t)) `union`  (fv_env Env) `union` (fv_lenv lEnv) ->
      wf_typ E t ->
      F_Related_osubst ([(x, bind_typ t)]++E) lE
                   ([(x, e)]++gsubst) ([(x, e')]++gsubst') lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv 
  | F_Related_osubst_ltyp :
    forall (E:env)(lE:lenv)(gsubst gsubst' lgsubst lgsubst':gamma_subst) (e e':exp) (t:typ) (rsubst:rho_subst) (dsubst dsubst':delta_subst) Env lEnv1 lEnv2 (x:atom),
      F_Related_osubst E lE gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv1 ->
      typing Env lEnv2 e (apply_delta_subst_typ dsubst t) ->
      typing Env lEnv2 e' (apply_delta_subst_typ dsubst' t) ->
      disjoint E lEnv2 /\ disjoint lE lEnv2 ->      
      wf_lenv Env (lEnv2++lEnv1) ->
      F_Related_oterms t rsubst dsubst dsubst' e e' Env lEnv2 ->
      x `notin` ((fv_env E) `union` (fv_lenv lE) `union` (fv_tt t)) `union`  (fv_env Env) `union` (fv_lenv lEnv1) `union` (fv_lenv lEnv2) ->
      wf_typ E t ->
      F_Related_osubst E ([(x, lbind_typ t)]++lE)
                   gsubst gsubst' ([(x, e)]++lgsubst) ([(x, e')]++lgsubst') rsubst dsubst dsubst' Env (lEnv2++lEnv1)
      .

Tactic Notation "F_Related_osubst_cases" tactic(first) tactic(c) :=
  first;
  [ c "F_Related_osubst_empty" |
    c "F_Related_osubst_kind" |
    c "F_Related_osubst_typ" | 
    c "F_Related_osubst_ltyp" ].

(** * Relations Subst *)
Inductive F_Rosubst : env-> rho_subst-> delta_subst -> delta_subst -> env -> Prop:=
  | F_Rosubst_empty :
    forall Env, 
      wf_env Env ->
      F_Rosubst nil rho_nil delta_nil delta_nil Env
  | F_Rosubst_rel :
    forall (E:env) (rsubst:rho_subst) (dsubst:delta_subst) (dsubst':delta_subst) Env R t t' X,
      F_Rosubst E rsubst dsubst dsubst' Env ->
      wfor Env R t t' ->
      X `notin` (fv_env E) `union` (fv_env Env)->
      F_Rosubst ([(X, bind_kn)]++E) ([(X, R)]++rsubst) ([(X, t)]++dsubst) ([(X, t')]++dsubst') Env
  | F_Rosubst_typ :
    forall (E:env) (rsubst:rho_subst) (dsubst:delta_subst) (dsubst':delta_subst) Env x T,
      F_Rosubst E rsubst dsubst dsubst' Env ->
      wf_typ E T ->
      x `notin` (fv_env E) `union` (fv_env Env)->
      F_Rosubst ([(x, bind_typ T)]++E) rsubst dsubst dsubst' Env
      .

Tactic Notation "F_Rosubst_cases" tactic(first) tactic(c) :=
  first;
  [ c "F_Rosubst_empty" |
    c "F_Rosubst_rel" |
    c "F_Rosubst_typ" ].

(** * SystemF Relations *)
Definition F_ORel t rsubst (dsubst dsubst':delta_subst) Env lEnv v v' :=
   typing Env lEnv v (apply_delta_subst_typ dsubst t) /\
   typing Env lEnv v' (apply_delta_subst_typ dsubst' t) /\
   F_Related_ovalues t rsubst dsubst dsubst' v v' Env lEnv
  .

(** * A Family of SystemF Relations *)
Definition F_FORel t rsubst (dsubst dsubst':delta_subst) Env v v' :=
   exists lEnv, F_ORel t rsubst dsubst dsubst' Env lEnv v v'
  .

Hint Constructors F_Related_osubst F_Rosubst.

(* ********************************************************************** *)
(* Fvalue simplification *)
Axiom F_Related_ovalues_bvar_eq: forall i (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) Env lEnv,
  F_Related_ovalues (typ_bvar i) rsubst dsubst dsubst' v v' Env lEnv <-> False.

Axiom F_Related_ovalues_bvar_leq: forall i (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) Env lEnv,
  F_Related_ovalues (typ_bvar i) rsubst dsubst dsubst' v v' Env lEnv -> False.

Axiom F_Related_ovalues_bvar_req: forall i (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) Env lEnv,
  False -> 
  F_Related_ovalues (typ_bvar i) rsubst dsubst dsubst' v v' Env lEnv.

Axiom F_Related_ovalues_fvar_eq: forall X (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) Env lEnv,
  F_Related_ovalues (typ_fvar X) rsubst dsubst dsubst' v v' Env lEnv <->
    exists R,
      (binds X R rsubst) /\ (value v) /\ (value v') /\ (R v v')
  .

Axiom F_Related_ovalues_fvar_leq: forall X  (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) Env lEnv,
  F_Related_ovalues (typ_fvar X) rsubst dsubst dsubst' v v' Env lEnv ->
    exists R,
      (binds X R rsubst) /\ (value v) /\ (value v') /\ (R v v')
  .

Axiom F_Related_ovalues_fvar_req: forall X  (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) Env lEnv,
  (exists R,
    (binds X R rsubst) /\ (value v) /\ (value v') /\ (R v v')) ->
  F_Related_ovalues (typ_fvar X) rsubst dsubst dsubst' v v' Env lEnv.

Axiom F_Related_ovalues_arrow_eq: forall (t1 t2:typ)  (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) Env lEnv,
  F_Related_ovalues (typ_arrow t1 t2) rsubst dsubst dsubst' v v' Env lEnv
  <->
  (
    (value v) /\ (value v') /\
    (forall lEnv1 x x',
       typing Env lEnv1 x (apply_delta_subst_typ dsubst t1) ->
       typing Env lEnv1 x' (apply_delta_subst_typ dsubst' t1) ->
       wf_lenv Env (lEnv1++lEnv) ->
       (exists w, exists w',
        normalize x w /\ normalize x' w' /\
       F_Related_ovalues t1 rsubst dsubst dsubst' w w' Env lEnv1) ->
       (exists u, exists u', 
        normalize (exp_app v x) u /\
        normalize (exp_app v' x') u' /\
        F_Related_ovalues t2 rsubst dsubst dsubst' u u' Env (lEnv1++lEnv))
    )
  )
   .

Axiom F_Related_ovalues_arrow_leq: forall (t1 t2:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) Env lEnv,
  F_Related_ovalues (typ_arrow t1 t2) rsubst dsubst dsubst' v v' Env lEnv
  ->
  (
    (value v) /\ (value v') /\
    (forall lEnv1 x x',
       typing Env lEnv1 x (apply_delta_subst_typ dsubst t1) ->
       typing Env lEnv1 x' (apply_delta_subst_typ dsubst' t1) ->
       wf_lenv Env (lEnv1++lEnv) ->
       (exists w, exists w',
        normalize x w /\ normalize x' w' /\
       F_Related_ovalues t1 rsubst dsubst dsubst' w w' Env lEnv1) ->
       (exists u, exists u', 
        normalize (exp_app v x) u /\
        normalize (exp_app v' x') u' /\
        F_Related_ovalues t2 rsubst dsubst dsubst' u u' Env (lEnv1++lEnv))
    )
  )
   .

Axiom F_Related_ovalues_arrow_req: forall (t1 t2:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) Env lEnv,
  (
    (value v) /\ (value v') /\
    (forall lEnv1 x x',
       typing Env lEnv1 x (apply_delta_subst_typ dsubst t1) ->
       typing Env lEnv1 x' (apply_delta_subst_typ dsubst' t1) ->
       wf_lenv Env (lEnv1++lEnv) ->
       (exists w, exists w',
        normalize x w /\ normalize x' w' /\
       F_Related_ovalues t1 rsubst dsubst dsubst' w w' Env lEnv1) ->
       (exists u, exists u', 
        normalize (exp_app v x) u /\
        normalize (exp_app v' x') u' /\
        F_Related_ovalues t2 rsubst dsubst dsubst' u u' Env (lEnv1++lEnv))
    )
  ) ->
  F_Related_ovalues (typ_arrow t1 t2) rsubst dsubst dsubst' v v' Env lEnv
   .

Axiom F_Related_ovalues_all_eq: forall (t1:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) Env lEnv,
  F_Related_ovalues (typ_all t1) rsubst dsubst dsubst' v v' Env lEnv
  <->
      (
      (value v) /\ (value v') /\
      (exists L,
         (forall (X:atom) t2 t2' R (Fr:X `notin` L),
         wfor Env R t2 t2' ->
          X `notin` ((dom rsubst) `union` (fv_tt t1)) ->
          (exists w, exists w',
          normalize (exp_tapp v t2) w /\
          normalize (exp_tapp v' t2') w' /\
          F_Related_ovalues (open_tt t1 X)
                           ([(X, R)]++rsubst)
                           ([(X, t2)]++dsubst)
                           ([(X, t2')]++dsubst')
                            w w' Env lEnv)
        ))
      )
  .

Axiom F_Related_ovalues_all_leq: forall (t1:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) Env lEnv,
  F_Related_ovalues (typ_all t1) rsubst dsubst dsubst' v v' Env lEnv
  ->
      (
      (value v) /\ (value v') /\
      (exists L,
         (forall (X:atom) t2 t2' R (Fr:X `notin` L),
         wfor Env R t2 t2' ->
          X `notin` ((dom rsubst) `union` (fv_tt t1)) ->
          (exists w, exists w',
          normalize (exp_tapp v t2) w /\
          normalize (exp_tapp v' t2') w' /\
          F_Related_ovalues (open_tt t1 X)
                           ([(X, R)]++rsubst)
                           ([(X, t2)]++dsubst)
                           ([(X, t2')]++dsubst')
                            w w' Env lEnv)
        ))
      )
  .

Axiom F_Related_ovalues_all_req: forall (t1:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) Env lEnv,
      (
      (value v) /\ (value v') /\
      (exists L,
         (forall (X:atom) t2 t2' R (Fr:X `notin` L),
         wfor Env R t2 t2' ->
          X `notin` ((dom rsubst) `union` (fv_tt t1)) ->
          (exists w, exists w',
          normalize (exp_tapp v t2) w /\
          normalize (exp_tapp v' t2') w' /\
          F_Related_ovalues (open_tt t1 X)
                           ([(X, R)]++rsubst)
                           ([(X, t2)]++dsubst)
                           ([(X, t2')]++dsubst')
                            w w' Env lEnv)
        ))
      )
  ->
  F_Related_ovalues (typ_all t1) rsubst dsubst dsubst' v v' Env lEnv
  .

Axiom F_Related_ovalues_bang_eq: forall (t1:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) Env lEnv,
  F_Related_ovalues (typ_bang t1) rsubst dsubst dsubst' v v' Env lEnv
  <->
    (value v) /\ (value v') /\
    (exists e1, exists e1',
      v = exp_bang e1 /\
      v' = exp_bang e1' /\
      (exists u1, exists u1',
       normalize e1 u1 /\
       normalize e1' u1' /\
       F_Related_ovalues t1 rsubst dsubst dsubst' u1 u1' Env lEnv)
    )
   .

Axiom F_Related_ovalues_bang_leq: forall (t1:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) Env lEnv,
  F_Related_ovalues (typ_bang t1) rsubst dsubst dsubst' v v' Env lEnv
  ->
    (value v) /\ (value v') /\
    (exists e1, exists e1', 
      v = exp_bang e1 /\
      v' = exp_bang e1' /\
      (exists u1, exists u1',
       normalize e1 u1 /\
       normalize e1' u1' /\
       F_Related_ovalues t1 rsubst dsubst dsubst' u1 u1' Env lEnv)
    )
   .

Axiom F_Related_ovalues_bang_req: forall (t1:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) Env lEnv,
    (value v) /\ (value v') /\
    (exists e1, exists e1', 
      v = exp_bang e1 /\
      v' = exp_bang e1' /\
      (exists u1, exists u1',
       normalize e1 u1 /\
       normalize e1' u1' /\
       F_Related_ovalues t1 rsubst dsubst dsubst' u1 u1' Env lEnv)
    )
  ->
  F_Related_ovalues (typ_bang t1) rsubst dsubst dsubst' v v' Env lEnv
   .

Axiom F_Related_ovalues_with_eq: forall (t1 t2:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) Env lEnv,
  F_Related_ovalues (typ_with t1 t2) rsubst dsubst dsubst' v v' Env lEnv
  <->
    (value v) /\ (value v') /\
    (exists e1, exists e2, exists e1', exists e2',
      v = exp_apair e1 e2 /\
      v' = exp_apair e1' e2' /\
      (exists u1, exists u1',
       normalize e1 u1 /\
       normalize e1' u1' /\
       F_Related_ovalues t1 rsubst dsubst dsubst' u1 u1' Env lEnv) /\
      (exists u2, exists u2',
       normalize e2 u2 /\
       normalize e2' u2' /\
       F_Related_ovalues t2 rsubst dsubst dsubst' u2 u2' Env lEnv)
    )
   .

Axiom F_Related_ovalues_with_leq: forall (t1 t2:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) Env lEnv,
  F_Related_ovalues (typ_with t1 t2) rsubst dsubst dsubst' v v' Env lEnv
  ->
    (value v) /\ (value v') /\
    (exists e1, exists e2, exists e1', exists e2',
      v = exp_apair e1 e2 /\
      v' = exp_apair e1' e2' /\
      (exists u1, exists u1',
       normalize e1 u1 /\
       normalize e1' u1' /\
       F_Related_ovalues t1 rsubst dsubst dsubst' u1 u1' Env lEnv) /\
      (exists u2, exists u2',
       normalize e2 u2 /\
       normalize e2' u2' /\
       F_Related_ovalues t2 rsubst dsubst dsubst' u2 u2' Env lEnv)
    )
   .

Axiom F_Related_ovalues_with_req: forall (t1 t2:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) Env lEnv,
    (value v) /\ (value v') /\
    (exists e1, exists e2, exists e1', exists e2',
      v = exp_apair e1 e2 /\
      v' = exp_apair e1' e2' /\
      (exists u1, exists u1',
       normalize e1 u1 /\
       normalize e1' u1' /\
       F_Related_ovalues t1 rsubst dsubst dsubst' u1 u1' Env lEnv) /\
      (exists u2, exists u2',
       normalize e2 u2 /\
       normalize e2' u2' /\
       F_Related_ovalues t2 rsubst dsubst dsubst' u2 u2' Env lEnv)
    )
  ->
  F_Related_ovalues (typ_with t1 t2) rsubst dsubst dsubst' v v' Env lEnv
   .

(* ********************************************************************** *)
(** * Inversion *)

Axiom F_Related_ovalues_inversion: forall t v v' rsubst dsubst dsubst' Env lEnv,
  F_Related_ovalues t rsubst dsubst dsubst' v v' Env lEnv ->
  ((value v)* (value v'))%type.

Axiom F_Rosubst__wf_osubst:
  forall (E:env) (rsubst:rho_subst) (dsubst:delta_subst) (dsubst':delta_subst) Env,
  F_Rosubst E rsubst dsubst dsubst' Env ->
  ((wf_delta_osubst E dsubst Env) * (wf_delta_osubst E dsubst' Env) * (wf_rho_subst E rsubst))%type.

Axiom Forel_inversion: forall t rsubst dsubst dsubst' v v' Env lEnv,
  F_ORel t rsubst dsubst dsubst' Env lEnv v v' ->
  ((value v)* (value v'))%type.

Axiom Fforel_inversion: forall t rsubst dsubst dsubst' v v' Env,
  F_FORel t rsubst dsubst dsubst' Env v v' ->
  ((value v)* (value v'))%type.

Axiom F_Related_osubst__inversion:
  forall (E:env) (lE:lenv) (rsubst:rho_subst) (dsubst:delta_subst) (dsubst':delta_subst) gsubst gsubst' lgsubst lgsubst' Env lEnv,
  F_Related_osubst E lE gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
  ((wf_delta_osubst E dsubst Env) * (wf_delta_osubst E dsubst' Env) *
   (wf_lgamma_osubst E lE dsubst gsubst lgsubst Env lEnv)* (wf_lgamma_osubst E lE dsubst' gsubst' lgsubst' Env lEnv) *
   (wf_rho_subst E rsubst) * (wf_env E) * (wf_lenv E lE) * (wf_env Env) * (wf_lenv Env lEnv))%type.

(*******************************************************************************)
(** Dom Equal *)

Axiom Forel_lin_domeq : forall t rsubst dsubst dsubst' e e' Env lEnv lEnv',
  F_Related_ovalues t rsubst dsubst dsubst' e e' Env lEnv ->
  wf_lenv Env lEnv ->
  dom lEnv [=] dom lEnv' ->
  F_Related_ovalues t rsubst dsubst dsubst' e e' Env lEnv'.

(* **************************************** *)
(** * Weaken and Stronger of SystemF Relations *)

Axiom Forel_weaken:  forall t E E' v v' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 Env lEnv X R t2 t2',
  ((F_Related_ovalues t (rsubst'++rsubst) (dsubst0++dsubst) (dsubst'0++dsubst') v v' Env lEnv ->
  ddom_env E [=] dom dsubst ->
  ddom_env E [=] dom dsubst' ->
  ddom_env E' [=] dom dsubst0 ->
  ddom_env E' [=] dom dsubst'0 ->
  ddom_env E [=] dom rsubst ->
  ddom_env E' [=] dom rsubst' ->
  X `notin` (fv_env E `union` fv_env E' `union` (fv_tt t) `union` fv_env Env `union` fv_lenv lEnv)->
  wf_typ Env t2 ->
  wf_typ Env t2' ->
  wf_rho_subst (E'++E) (rsubst'++rsubst) ->
  wf_delta_osubst (E'++E) (dsubst0++dsubst) Env ->
  wf_delta_osubst (E'++E) (dsubst'0++dsubst') Env ->
  F_Related_ovalues t (rsubst'++[(X, R)]++rsubst) (dsubst0++[(X, t2)]++dsubst) (dsubst'0++[(X, t2')]++dsubst') v v' Env lEnv))
  .

Axiom Forel_weaken_head:  forall t E v v' rsubst dsubst dsubst' Env lEnv X R t2 t2',
  ((F_Related_ovalues t rsubst dsubst dsubst' v v' Env lEnv ->
  ddom_env E [=] dom dsubst ->
  ddom_env E [=] dom dsubst' ->
  ddom_env E [=] dom rsubst ->
  X `notin` (fv_env E `union` (fv_tt t) `union` fv_env Env `union` fv_lenv lEnv)->
  wf_typ Env t2 ->
  wf_typ Env t2' ->
  wf_rho_subst E rsubst ->
  wf_delta_osubst E dsubst Env ->
  wf_delta_osubst E dsubst' Env ->
  F_Related_ovalues t ([(X, R)]++rsubst) ([(X, t2)]++dsubst) ([(X, t2')]++dsubst') v v' Env lEnv))
  .

Axiom Forel_stronger:  forall t E E' v v' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 Env lEnv X R t2 t2',
  F_Related_ovalues t (rsubst'++[(X,R)]++rsubst) (dsubst0++[(X,t2)]++dsubst) (dsubst'0++[(X,t2')]++dsubst') v v' Env lEnv ->
  ddom_env E [=] dom dsubst ->
  ddom_env E [=] dom dsubst' ->
  ddom_env E' [=] dom dsubst0 ->
  ddom_env E' [=] dom dsubst'0 ->
  ddom_env E [=] dom rsubst ->
  ddom_env E' [=] dom rsubst' ->
  X `notin` (fv_env E `union` fv_env E' `union` (fv_tt t) `union` fv_env Env `union` fv_lenv lEnv)->
  wf_typ Env t2 ->
  wf_typ Env t2' ->
  wf_rho_subst (E'++[(X,bind_kn)]++E) (rsubst'++[(X,R)]++rsubst) ->
  wf_delta_osubst (E'++[(X,bind_kn)]++E) (dsubst0++[(X,t2)]++dsubst) Env ->
  wf_delta_osubst (E'++[(X,bind_kn)]++E) (dsubst'0++[(X,t2')]++dsubst') Env ->
  F_Related_ovalues t (rsubst'++rsubst) (dsubst0++dsubst) (dsubst'0++dsubst') v v' Env lEnv 
  .

Axiom bindosgE__bindosgsubst: forall E lE gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv x T,
    F_Related_osubst E lE gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
    binds x (bind_typ T) E ->
    wf_typ E T ->
    x `notin` dom lgsubst /\ x `notin` dom lgsubst' /\
    (exists e, exists e',
                ((binds x (e) gsubst)
                *(binds x (e') gsubst')
                *(typing Env lempty e (apply_delta_subst_typ dsubst T))*(typing Env lempty e' (apply_delta_subst_typ dsubst' T))
                *(F_Related_oterms T rsubst dsubst dsubst' e e' Env lempty))%type)
    .

Axiom lbindosgE__lbindosgsubst: forall E gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv x T,
    F_Related_osubst E [(x, lbind_typ T)] gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
    wf_typ E T ->
    x `notin` dom gsubst /\ x `notin` dom gsubst' /\
    (exists e, exists e',
                ((binds x (e) lgsubst)
                *(binds x (e') lgsubst')
                *(typing Env lEnv e (apply_delta_subst_typ dsubst T))*(typing Env lEnv e' (apply_delta_subst_typ dsubst' T))
                *(F_Related_oterms T rsubst dsubst dsubst' e e' Env lEnv))%type)
    .

(*******************************************************************************)
(** subst *)

Definition F_ORel__R (t:typ) (E:env) (rsubst:rho_subst) dsubst dsubst' Env lEnv (R:rel) :=
  wf_delta_osubst E dsubst Env /\  wf_delta_osubst E dsubst' Env /\  wf_rho_subst E rsubst /\
  (forall v v',
    ((F_ORel t rsubst dsubst dsubst' Env lEnv v v' -> R v v') 
   * (R v v'->F_ORel t rsubst dsubst dsubst' Env lEnv v v')) % type)
  .

Definition F_FORel__R (t:typ) (E:env) (rsubst:rho_subst) dsubst dsubst' Env (R:rel) :=
  wf_delta_osubst E dsubst Env /\  wf_delta_osubst E dsubst' Env /\  wf_rho_subst E rsubst /\
  (forall v v',
    ((F_FORel t rsubst dsubst dsubst' Env v v' -> R v v') 
   * (R v v'->F_FORel t rsubst dsubst dsubst' Env v v')) % type)
  .

Axiom F_FORel__R__wfor: forall (E:env) (t:typ) (rsubst:rho_subst) dsubst dsubst' Env (R:rel),
  F_FORel__R t E rsubst dsubst dsubst' Env R -> 
  wf_typ E t ->
  wfor Env R (apply_delta_subst_typ dsubst t) (apply_delta_subst_typ dsubst' t).

Axiom oparametricity_subst_value : forall t E E' e e' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 Env lEnv X R t2 k,
  wf_typ (E'++[(X, bind_kn)]++E) (open_tt_rec k (typ_fvar X) t) ->
  wf_typ (E'++E) (open_tt_rec k t2 t) ->
  wf_typ (E'++E) t2 ->
  F_FORel__R t2 (E'++E) (rsubst'++rsubst) (dsubst0++dsubst) (dsubst'0++dsubst') Env R ->
  X `notin` (fv_env E `union` fv_env E' `union` (fv_tt t) `union` (fv_te e) `union` (fv_te e') `union` fv_env Env `union` fv_lenv lEnv)-> 
  ddom_env E [=] dom dsubst ->
  ddom_env E [=] dom dsubst' ->
  ddom_env E' [=] dom dsubst0 ->
  ddom_env E' [=] dom dsubst'0 ->
  ddom_env E [=] dom rsubst ->
  ddom_env E' [=] dom rsubst' ->
  (F_Related_ovalues (open_tt_rec k (typ_fvar X) t) (rsubst'++[(X, R)]++rsubst ) (dsubst0++[(X, (apply_delta_subst_typ (dsubst0++dsubst) t2))]++dsubst) (dsubst'0++[(X,(apply_delta_subst_typ (dsubst'0++dsubst') t2))]++dsubst') e e' Env lEnv ->
  typing Env lEnv e (apply_delta_subst_typ (dsubst0++[(X,(apply_delta_subst_typ (dsubst0++dsubst) t2))]++dsubst) (open_tt_rec k (typ_fvar X) t)) ->
  typing Env lEnv e' (apply_delta_subst_typ (dsubst'0++[(X,(apply_delta_subst_typ (dsubst'0++dsubst') t2))]++dsubst') (open_tt_rec k (typ_fvar X) t)) ->
  wf_rho_subst (E'++[(X, bind_kn)]++E) (rsubst'++[(X, R)]++rsubst) ->
  wf_delta_osubst (E'++[(X, bind_kn)]++E) (dsubst0++[(X, (apply_delta_subst_typ (dsubst0++dsubst) t2))]++dsubst) Env -> 
  wf_delta_osubst (E'++[(X, bind_kn)]++E) (dsubst'0++[(X, (apply_delta_subst_typ (dsubst'0++dsubst') t2))]++dsubst') Env -> 
  F_Related_ovalues (open_tt_rec k t2 t) (rsubst'++rsubst) (dsubst0++dsubst) (dsubst'0++dsubst') e e' Env lEnv)
  .

(*******************************************************************************)
(** F_Related_osubst_split *)

Axiom F_Related_osubst_split: forall E lE lE1 lE2 dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
   F_Related_osubst E lE gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
   lenv_split E lE1 lE2 lE ->
   exists lgsubst1, exists lgsubst1', exists lgsubst2, exists lgsubst2', exists lEnv1, exists lEnv2,
     lgamma_osubst_split E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst Env lEnv1 lEnv2 lEnv /\
     lgamma_osubst_split E lE dsubst' gsubst' lgsubst1' lgsubst2' lgsubst' Env lEnv1 lEnv2 lEnv  /\
     F_Related_osubst E lE1 gsubst gsubst' lgsubst1 lgsubst1' rsubst dsubst dsubst' Env lEnv1 /\     
     F_Related_osubst E lE2 gsubst gsubst' lgsubst2 lgsubst2' rsubst dsubst dsubst' Env lEnv2.

(*******************************************************************************)
(** parametricity *)

Axiom oparametricity: forall E lE e t dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
   typing E lE e t ->
   F_Related_osubst E lE gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
   F_Rosubst E rsubst dsubst dsubst' Env->
   F_Related_oterms t rsubst dsubst dsubst'
                                 (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
                                 (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e)))
                                 Env lEnv
   .

End IOParametricity.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../../../metatheory" "-I" "../Bang") ***
*** End: ***
 *)
