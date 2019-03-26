(** Authors: Jianzhou Zhao. *)

Require Import Wf_nat.
Require Export Metatheory.
Require Import Bang_Definitions.
Require Import Bang_Infrastructure.
Require Import Bang_Lemmas.
Require Import Bang_Soundness.
Require Import Bang_OParametricity_Pre.
Require Export Bang_OParametricity_Interface.
Require Import Bang_OParametricity_Macro.
Require Import Bang_Renaming.
Require Import Program.
Require Import FunctionalExtensionality.
Require Import Tactics.

Ltac fold_sub f args :=
  match goal with
    | [ |- ?T ] => 
      match T with
        context [ Fix_measure_sub _ _ _ _ ?x ] => fold (f args x)
      end
  end.

Ltac unfold_sub f args := 
  set (call:=f args) ; unfold f in call ; unfold call ; clear call ; 
  rewrite WfExtensionality.fix_sub_measure_eq_ext ; repeat fold_sub f args ; simpl proj1_sig.

Module OParametricity : IOParametricity.

(* ********************************************************************** *)
(** * Wf Relations *)

Axiom ddom_gdom_disjoint : forall X x E,
  X `in` ddom_env E ->
  x `in` gdom_env E ->
  X <> x.

Axiom ddom_ldom_disjoint : forall X x E (lE:lenv),
  X `in` ddom_env E ->
  x `in` dom lE ->
  X <> x.

Lemma ddom_ldoms_disjoint : forall X E (lE:lenv),
  X `in` ddom_env E ->
  X `notin` dom lE.
Proof.
  intros.
  destruct (@in_dec X (dom lE)); auto.
    assert (X <> X) as J.
      apply ddom_ldom_disjoint with (E:=E)(lE:=lE); auto.  
    contradict J; auto.
Qed.

Definition admissible (E:env) (r : rel) : Prop :=
  (forall v v',
    r v v' ->
    (forall x y,
      x `in` (AtomSetImpl.diff (fv_ee v) (gdom_env E)) ->
      x `in` (AtomSetImpl.diff (fv_ee v') (gdom_env E)) ->
      y `notin` (AtomSetImpl.diff (fv_ee v  `union` fv_ee v' `union` dom E) {{x}}) ->
      r (subst_ee x y v) (subst_ee x y v')
    )
  ).

Definition wfor (E:env) (r : rel) (T T' : typ) : Prop :=
  (wf_typ E T) /\
  (wf_typ E T') /\
  admissible E r
  .

Lemma wfor_inv : forall E r T T',
  wfor E r T T'->
  (wf_typ E T) /\
  (wf_typ E T') /\
  admissible E r
  .
Proof. auto. Qed.

Lemma wfor_left_inv : forall E t t' R,
  wfor E R t t' -> wf_typ E t.
Proof.
  intros.
  inversion H. auto.
Qed.

Lemma wfor_right_inv : forall E t t' R,
  wfor E R t t' -> wf_typ E t'.
Proof.
  intros. 
  inversion H. inversion H1. auto.
Qed.

Lemma wfor_renaming_inv : forall E r T T',
  wfor E r T T' ->
  admissible E r
  .
Proof.
  intros. 
  inversion H. inversion H1. auto.
Qed.

(* ********************************************************************** *)
(** * Value Relations *)
Program Fixpoint F_Related_ovalues
    (t:typ) (rsubst:rho_subst)
    (dsubst dsubst':delta_subst) (v:exp) (v':exp) (Env:env) (lEnv:lenv) {measure typ_size t} : Prop :=
  match t with
  | typ_fvar X =>
  (*
       (v, v') \in R
       . |- v : dsubst(X)
       . |- v' : dsubst'(X)
    -------------------
       v ~ v' : X | (\rho, X->R)
  *)
    exists R,
    (binds X R rsubst) /\ (value v) /\ (value v') /\ (admissible Env R) /\ (R v v')
  | typ_arrow t1 t2 =>
  (*
    v and v' are values
    . |- v : dsubst(t1->t2) . |- v' : dsubst'(t1->t2)
    \forall x x', . |- x : dsubst(t1)  . |- x' : dsubst'(t1)  (x ~~ x': t1 | \rho) -> v x ~~ v' x':t2 | \rho
   -----------------------------------------------------------------
          v ~ v': t1->t2 | \rho
  *)
    (value v) /\ (value v') /\
    (exists L,
      (forall lEnv1 x x',
       typing Env lEnv1 x (apply_delta_subst_typ dsubst t1) ->
       typing Env lEnv1 x' (apply_delta_subst_typ dsubst' t1) ->
       wf_lenv Env (lEnv1++lEnv) ->
       disjdom L (dom lEnv1) ->
       (exists w, exists w',
        normalize x w /\ normalize x' w' /\
       F_Related_ovalues t1 rsubst dsubst dsubst' w w' Env lEnv1) ->
       (exists u, exists u', 
        normalize (exp_app v x) u /\
        normalize (exp_app v' x') u' /\
        F_Related_ovalues t2 rsubst dsubst dsubst' u u' Env (lEnv1++lEnv))
      )
    )
  | typ_all t1 =>
  (*
    v and v' are values
    . |- v : dsubst(A t1) . |- v' : dsubst'(A t1')
    \forall R \in t2 <-> t2. v[t2] ~~ v'[t2'] : t1 | \rho, U->R
   -----------------------------------------------------------------
          v ~ v': \/U. t1 | \rho
  *)
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
  (*
     . |-  <m1, m2> : dsubst(t1*t2)
     . |-  <m1', m2'> : dsubst'(t1*t2)
      m1 ~~ m1' : t1 | \rho
      m2 ~~ m2' : t2 | \rho
   -----------------------------------------------------------------
         <m1, m2> ~ <m1', m2'>: t1*t2 | \rho
  *)
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
(*
   .| e : dsubst(t)    .| e' : dsubst'(t)
    e ->* v               e' ->* v'
    (v ~ v': t | \rho)
   -----------------------------------------------------------------
    e ~~ e': t | \rho
*)
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
    (*
      gamma_nil ~ gamma_nil : gempty | rho_nil, delta_nil,  delta_nil
    *)
    forall Env, 
      wf_env Env ->
      F_Related_osubst nil nil gamma_nil gamma_nil gamma_nil gamma_nil rho_nil delta_nil delta_nil Env nil
  | F_Related_osubst_kind :
    (*
      gsubst ~ gsubst' : genv | rsubst, dsubst, dsubst'
      R \in t<->t'
     -----------------------------------------------------------------
      gsubst ~ gsubst' : genv | (rsubst, X->R), (dsubst, X->t), (dsubst', X->t')
    *)
    forall (E:env) (lE:lenv) (gsubst gsubst' lgsubst lgsubst':gamma_subst) (rsubst:rho_subst) (dsubst dsubst':delta_subst) Env lEnv X R t t',
      F_Related_osubst E lE gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
      X `notin` (fv_env E) `union` (fv_lenv lE) `union`  (fv_env Env) `union` (fv_lenv lEnv) ->
      wfor Env R t t' ->
      F_Related_osubst ([(X, bind_kn)]++E) lE gsubst gsubst' lgsubst lgsubst'
                                   ([(X,R)]++rsubst) ([(X,t)]++dsubst) ([(X,t')]++dsubst') Env lEnv
  | F_Related_osubst_typ :
    (*
      gsubst ~ gsubst' : genv | rsubst, dsubst, dsubst'
      e ~ e' : t | rho_subst
     -----------------------------------------------------------------
      (gsubst, x->e) ~ (gsubst',x->e') : (genv, x:t) | rho_subst, dsubst, dsubst'
    *)
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
    (*
      gsubst ~ gsubst' : genv | rsubst, dsubst, dsubst'
      e ~ e' : t | rho_subst
     -----------------------------------------------------------------
      (gsubst, x->e) ~ (gsubst',x->e') : (genv, x:t) | rho_subst, dsubst, dsubst'
    *)
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
    (*
      empty |- rho_nil \in delta_nil <-> delta_nil
    *)
    forall Env, 
      wf_env Env ->
      F_Rosubst nil rho_nil delta_nil delta_nil Env
  | F_Rosubst_rel :
    (*
      env |- rho_subst \in delta_subst <-> delta_subst'
      R \in t <-> t'
     -----------------------------------------------------------------
      env, X |- (rho_subst, X->R) \in (delta_subst, X->t) <-> (delta_subst', X->t')
    *)
    forall (E:env) (rsubst:rho_subst) (dsubst:delta_subst) (dsubst':delta_subst) Env R t t' X,
      F_Rosubst E rsubst dsubst dsubst' Env ->
      wfor Env R t t' ->
      X `notin` (fv_env E) `union` (fv_env Env)->
      F_Rosubst ([(X, bind_kn)]++E) ([(X, R)]++rsubst) ([(X, t)]++dsubst) ([(X, t')]++dsubst') Env
  | F_Rosubst_typ :
    (*
      env |- rho_subst \in delta_subst <-> delta_subst'
     -----------------------------------------------------------------
      env, x~:T |- rho_subst \in delta_subst <-> delta_subst'
    *)
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
Lemma F_Related_ovalues_bvar_eq: forall i (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) Env lEnv,
  F_Related_ovalues (typ_bvar i) rsubst dsubst dsubst' v v' Env lEnv <-> False.
Proof. 
  intros.
  unfold_sub F_Related_ovalues (typ_bvar i).
  split; auto.
Qed.

Lemma F_Related_ovalues_bvar_leq: forall i (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) Env lEnv,
  F_Related_ovalues (typ_bvar i) rsubst dsubst dsubst' v v' Env lEnv -> False.
Proof. 
  intros.
  destruct (@F_Related_ovalues_bvar_eq i rsubst dsubst dsubst' v v' Env lEnv); auto.
Qed.

Lemma F_Related_ovalues_bvar_req: forall i (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) Env lEnv,
  False -> 
  F_Related_ovalues (typ_bvar i) rsubst dsubst dsubst' v v' Env lEnv.
Proof. 
  intros.
  destruct (@F_Related_ovalues_bvar_eq i rsubst dsubst dsubst' v v' Env lEnv); auto.
Qed.

Lemma F_Related_ovalues_fvar_eq: forall X (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) Env lEnv,
  F_Related_ovalues (typ_fvar X) rsubst dsubst dsubst' v v' Env lEnv <->
    exists R,
      (binds X R rsubst) /\ (value v) /\ (value v') /\ (admissible Env R) /\ (R v v')
  .
Proof. 
  intros.
  unfold_sub F_Related_ovalues (typ_fvar X).
  split; auto.
Qed.

Lemma F_Related_ovalues_fvar_leq: forall X (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) Env lEnv,
  F_Related_ovalues (typ_fvar X) rsubst dsubst dsubst' v v' Env lEnv ->
    exists R,
      (binds X R rsubst) /\ (value v) /\ (value v') /\ (admissible Env R) /\ (R v v')
  .
Proof. 
  intros.
  destruct (@F_Related_ovalues_fvar_eq X rsubst dsubst dsubst' v v' Env lEnv); auto.
Qed.

Lemma F_Related_ovalues_fvar_req: forall X (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) Env lEnv,
  (exists R,
    (binds X R rsubst) /\ (value v) /\ (value v') /\ (admissible Env R) /\ (R v v')) ->
  F_Related_ovalues (typ_fvar X) rsubst dsubst dsubst' v v' Env lEnv.
Proof. 
  intros.
  destruct (@F_Related_ovalues_fvar_eq X rsubst dsubst dsubst' v v' Env lEnv); auto.
Qed.

Lemma F_Related_ovalues_arrow_eq: forall (t1 t2:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) Env lEnv,
  F_Related_ovalues (typ_arrow t1 t2) rsubst dsubst dsubst' v v' Env lEnv
  <->
  (
    (value v) /\ (value v') /\
    (exists L,
      (forall lEnv1 x x',
       typing Env lEnv1 x (apply_delta_subst_typ dsubst t1) ->
       typing Env lEnv1 x' (apply_delta_subst_typ dsubst' t1) ->
       wf_lenv Env (lEnv1++lEnv) ->
       disjdom L (dom lEnv1) ->
       (exists w, exists w',
        normalize x w /\ normalize x' w' /\
       F_Related_ovalues t1 rsubst dsubst dsubst' w w' Env lEnv1) ->
       (exists u, exists u', 
        normalize (exp_app v x) u /\
        normalize (exp_app v' x') u' /\
        F_Related_ovalues t2 rsubst dsubst dsubst' u u' Env (lEnv1++lEnv))
      )
    )
  )
   .
Proof. 
  intros.
  unfold_sub F_Related_ovalues (typ_arrow t1 t2).
  split; intros H; decompose [and] H. auto. 
    split; auto.
Qed.

Lemma F_Related_ovalues_arrow_leq: forall (t1 t2:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) Env lEnv,
  F_Related_ovalues (typ_arrow t1 t2) rsubst dsubst dsubst' v v' Env lEnv
  ->
  (
    (value v) /\ (value v') /\
    (exists L,
      (forall lEnv1 x x',
       typing Env lEnv1 x (apply_delta_subst_typ dsubst t1) ->
       typing Env lEnv1 x' (apply_delta_subst_typ dsubst' t1) ->
       wf_lenv Env (lEnv1++lEnv) ->
       disjdom L (dom lEnv1) ->
       (exists w, exists w',
        normalize x w /\ normalize x' w' /\
       F_Related_ovalues t1 rsubst dsubst dsubst' w w' Env lEnv1) ->
       (exists u, exists u', 
        normalize (exp_app v x) u /\
        normalize (exp_app v' x') u' /\
        F_Related_ovalues t2 rsubst dsubst dsubst' u u' Env (lEnv1++lEnv))
      )
    )
  )
   .
Proof. 
  intros.
  destruct (@F_Related_ovalues_arrow_eq t1 t2 rsubst dsubst dsubst' v v' Env lEnv); auto.
Qed.

Lemma F_Related_ovalues_arrow_req: forall (t1 t2:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) Env lEnv,
  (
    (value v) /\ (value v') /\
    (exists L,
      (forall lEnv1 x x',
       typing Env lEnv1 x (apply_delta_subst_typ dsubst t1) ->
       typing Env lEnv1 x' (apply_delta_subst_typ dsubst' t1) ->
       wf_lenv Env (lEnv1++lEnv) ->
       disjdom L (dom lEnv1) ->
       (exists w, exists w',
        normalize x w /\ normalize x' w' /\
       F_Related_ovalues t1 rsubst dsubst dsubst' w w' Env lEnv1) ->
       (exists u, exists u', 
        normalize (exp_app v x) u /\
        normalize (exp_app v' x') u' /\
        F_Related_ovalues t2 rsubst dsubst dsubst' u u' Env (lEnv1++lEnv))
      )
    )
  ) ->
  F_Related_ovalues (typ_arrow t1 t2) rsubst dsubst dsubst' v v' Env lEnv
   .
Proof. 
  intros.
  destruct (@F_Related_ovalues_arrow_eq t1 t2 rsubst dsubst dsubst' v v' Env lEnv); auto.
Qed.

Lemma F_Related_ovalues_all_eq: forall (t1:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) Env lEnv,
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
Proof. 
  intros.
  unfold_sub F_Related_ovalues (typ_all t1).
  split; intros H; decompose [and] H; clear H.
    destruct H3 as [L H3].
    repeat(split; auto).
    exists L.
    intros X t2 t2' R Hfv Hwfor Hfv'.
    assert (J:=@H3 X t2 t2' R Hfv Hwfor Hfv').
    clear H3.
    destruct J as [w [w' [J1 [J2 J]]]]. 
    exists w. exists w'.
    split; auto.

    split; auto.
Qed.

Lemma F_Related_ovalues_all_leq: forall (t1:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) Env lEnv,
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
Proof. 
  intros.
  destruct (@F_Related_ovalues_all_eq t1 rsubst dsubst dsubst' v v' Env lEnv); auto.
Qed.

Lemma F_Related_ovalues_all_req: forall (t1:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) Env lEnv,
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
Proof. 
  intros.
  destruct (@F_Related_ovalues_all_eq t1 rsubst dsubst dsubst' v v' Env lEnv); auto.
Qed.

Lemma F_Related_ovalues_bang_eq: forall (t1:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) Env lEnv,
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
Proof. 
  intros.
  unfold_sub F_Related_ovalues (typ_bang t1).
  split; intros H; decompose [and] H; clear H.
    destruct H3 as [e1 [e1' [J1 [J2 J3]]]].
    repeat(split; auto).
    exists e1. exists e1'.
    repeat(split; auto).

    split; auto.
Qed.

Lemma F_Related_ovalues_bang_leq: forall (t1:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) Env lEnv,
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
Proof. 
  intros.
  destruct (@F_Related_ovalues_bang_eq t1 rsubst dsubst dsubst' v v' Env lEnv); auto.
Qed.

Lemma F_Related_ovalues_bang_req: forall (t1:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) Env lEnv,
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
Proof. 
  intros.
  destruct (@F_Related_ovalues_bang_eq t1 rsubst dsubst dsubst' v v' Env lEnv); auto.
Qed.

Lemma F_Related_ovalues_with_eq: forall (t1 t2:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) Env lEnv,
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
Proof. 
  intros.
  unfold_sub F_Related_ovalues (typ_with t1 t2).
  split; intros H; decompose [and] H; clear H.
    destruct H3 as [e1 [e2 [e1' [e2' [J1 [J2 J3]]]]]].
    repeat(split; auto).
    exists e1. exists e2. exists e1'. exists e2'.
    repeat(split; auto).

    split; auto.
Qed.

Lemma F_Related_ovalues_with_leq: forall (t1 t2:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) Env lEnv,
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
Proof. 
  intros.
  destruct (@F_Related_ovalues_with_eq t1 t2 rsubst dsubst dsubst' v v' Env lEnv); auto.
Qed.

Lemma F_Related_ovalues_with_req: forall (t1 t2:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) Env lEnv,
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
Proof. 
  intros.
  destruct (@F_Related_ovalues_with_eq t1 t2 rsubst dsubst dsubst' v v' Env lEnv); auto.
Qed.

(* ********************************************************************** *)
(** * Inversion *)

Lemma F_Related_ovalues_inversion: forall t v v' rsubst dsubst dsubst' Env lEnv,
  F_Related_ovalues t rsubst dsubst dsubst' v v' Env lEnv ->
  ((value v)* (value v'))%type.
Proof.
  intros t v v' rsubst dsubst dsubst' Env lEnv H.
  (typ_cases (induction t) Case); intros.
  Case "typ_bvar".
  apply F_Related_ovalues_bvar_leq in H; auto. inversion H.
  Case "typ_fvar".
  apply F_Related_ovalues_fvar_leq in H.
  destruct H as [R [Hb [Hv [Hv' Hr]]]].
  split; auto.
  Case "typ_arrow".
  apply F_Related_ovalues_arrow_leq in H.
  decompose [and] H; subst; clear H; auto.
  Case "typ_all".
  apply F_Related_ovalues_all_leq in H.
  decompose [and] H; subst; clear H; auto.
  Case "typ_bang".
  apply F_Related_ovalues_bang_leq in H.
  decompose [and] H; subst; clear H; auto.
  Case "typ_with".
  apply F_Related_ovalues_with_leq in H.
  decompose [and] H; subst; clear H; auto.
Qed.

Lemma F_Rosubst__wf_osubst:
  forall (E:env) (rsubst:rho_subst) (dsubst:delta_subst) (dsubst':delta_subst) Env,
  F_Rosubst E rsubst dsubst dsubst' Env ->
  ((wf_delta_osubst E dsubst Env) * (wf_delta_osubst E dsubst' Env) * (wf_rho_subst E rsubst))%type.
Proof.
  intros E rsubst dsubst dsubst' Env HRsub.
  (F_Rosubst_cases (induction HRsub) Case); try solve [split; auto].
  Case "F_Rosubst_rel".
    decompose [prod] IHHRsub.
    unfold wfor in H. decompose [and] H.
    split. split.
      apply wf_delta_osubst_styp; auto.
      apply wf_delta_osubst_styp; auto.
      apply wf_rho_subst_srel; auto.
  Case "F_Rosubst_typ".
    decompose [prod] IHHRsub. clear IHHRsub.
    split. split.
      apply wf_delta_osubst_skip; auto.
      apply wf_delta_osubst_skip; auto.
      apply wf_rho_subst_skip; auto.
Qed.

Lemma Forel_inversion: forall t rsubst dsubst dsubst' v v' Env lEnv,
  F_ORel t rsubst dsubst dsubst' Env lEnv v v' ->
  ((value v)* (value v'))%type.
Proof.
  intros t rsubst dsubst dsubst' v v' Env lEnv Hrel.
  unfold F_ORel in Hrel. destruct Hrel as [Typing [Typing' Hrel]].
  apply F_Related_ovalues_inversion in Hrel.
  assumption.
Qed.

Lemma Fforel_inversion: forall t rsubst dsubst dsubst' v v' Env,
  F_FORel t rsubst dsubst dsubst' Env v v' ->
  ((value v)* (value v'))%type.
Proof.
  intros t rsubst dsubst dsubst' v v' Env Hrel.
  unfold F_FORel in Hrel.
  destruct Hrel as [lEnv Hrel].
  apply Forel_inversion in Hrel.
  assumption.
Qed.

Lemma F_Related_osubst__inversion:
  forall (E:env) (lE:lenv) (rsubst:rho_subst) (dsubst:delta_subst) (dsubst':delta_subst) gsubst gsubst' lgsubst lgsubst' Env lEnv,
  F_Related_osubst E lE gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
  ((wf_delta_osubst E dsubst Env) * (wf_delta_osubst E dsubst' Env) *
   (wf_lgamma_osubst E lE dsubst gsubst lgsubst Env lEnv)* (wf_lgamma_osubst E lE dsubst' gsubst' lgsubst' Env lEnv) *
   (wf_rho_subst E rsubst) * (wf_env E) * (wf_lenv E lE) * (wf_env Env) * (wf_lenv Env lEnv))%type.
Proof.
  intros E lE rsubst dsubst dsubst' gsubst gsubst' lgsubst lgsubst' Env lEnv HRsub.
  (F_Related_osubst_cases (induction HRsub) Case).
    repeat (split; auto).
  Case "F_Related_osubst_kind".
    decompose [prod] IHHRsub.
    repeat (split; eauto using wfor_left_inv, wfor_right_inv).
      apply wf_delta_osubst_styp; eauto using wfor_left_inv.
      apply wf_delta_osubst_styp; eauto using wfor_right_inv.
      apply wf_lgamma_osubst_skind; eauto using wfor_left_inv.
       auto using free_env__free_dom.
      apply wf_lgamma_osubst_skind; eauto using wfor_right_inv.
       auto using free_env__free_dom.
      apply wf_rho_subst_srel; auto.
      apply wf_env_kn; auto.
      rewrite_env (nil ++ [(X, bind_kn)] ++ E). apply wf_lenv_weakening; auto.
       simpl_env. apply wf_env_kn; auto.
  Case "F_Related_osubst_typ".
    decompose [prod] IHHRsub.
    repeat (split; eauto).
      apply wf_delta_osubst_skip; auto. 
      apply wf_delta_osubst_skip; auto. 
      apply wf_lgamma_osubst_sval; auto. 
      apply wf_lgamma_osubst_sval; auto. 
      apply wf_rho_subst_skip; auto.
      apply wf_env_typ; auto.
      rewrite_env (nil ++ [(x, bind_typ t)] ++ E). apply wf_lenv_weakening; auto.
       simpl_env. apply wf_env_typ; auto.
  Case "F_Related_osubst_ltyp".
    decompose [prod] IHHRsub.
    repeat (split; eauto).
      apply wf_lgamma_osubst_slval with (lEnv1:=lEnv1) (lEnv2:=lEnv2); auto. 
       auto using free_env__free_dom.
      apply wf_lgamma_osubst_slval with (lEnv1:=lEnv1) (lEnv2:=lEnv2); auto. 
      apply wf_lenv_typ; auto.
Qed.

(*******************************************************************************)
(** Renaming *)

Definition P_Forel_lin_renaming_one (n:nat) := 
  forall t rsubst dsubst dsubst' e e' E Env lEnv' lEnv x0 y0 b,
  typ_size t = n ->
  F_Related_ovalues t rsubst dsubst dsubst' e e' Env (lEnv'++[(x0, b)]++lEnv) ->
  wf_rho_subst E rsubst ->
  wf_delta_osubst E dsubst Env ->
  wf_delta_osubst E dsubst' Env ->
  typing Env (lEnv'++[(x0, b)]++lEnv) e (apply_delta_subst_typ dsubst t) ->
  typing Env (lEnv'++[(x0, b)]++lEnv) e' (apply_delta_subst_typ dsubst' t) ->
  y0 `notin` dom Env `union` dom lEnv' `union` dom lEnv ->
  F_Related_ovalues t rsubst dsubst dsubst' (subst_ee x0 y0 e) (subst_ee x0 y0 e') Env (lEnv'++[(y0, b)]++lEnv).

Lemma _Forel_lin_renaming_one :  forall n, P_Forel_lin_renaming_one n.
Proof.
  intro n.
  apply lt_wf_ind. clear n.
  intros n H.
  unfold P_Forel_lin_renaming_one in *.
  intros t rsubst dsubst dsubst' e e' E Env lEnv' lEnv x0 y0 b Htsize Hrel Hwfr Hwfd Hwfd' Typinge Typinge' Fvy0.
  destruct (y0 == x0); subst.
    rewrite subst_ee_id. rewrite subst_ee_id. auto.
 (typ_cases (destruct t) Case).

  Case "typ_bvar". (*bvar*)
  apply F_Related_ovalues_bvar_leq in Hrel; auto.

  Case "typ_fvar". (* fvar *)
  apply F_Related_ovalues_fvar_leq in Hrel.
  apply F_Related_ovalues_fvar_req.
  destruct Hrel as [R0 [Hb [Hv [Hv' [Hadmin Hr]]]]]; subst; simpl.
  exists (R0).
    repeat(split; auto).
      apply value_through_subst_ee; auto.
      apply value_through_subst_ee; auto.
      
      assert (x0 `in` (AtomSetImpl.diff (fv_ee e) (gdom_env Env))) as x0indiffe.
        assert (J:=Typinge).
        apply typing_ldom in J.
        rewrite J. simpl_env. auto.
      assert (x0 `in` (AtomSetImpl.diff (fv_ee e') (gdom_env Env))) as x0indiffe'.
        assert (J:=Typinge').
        apply typing_ldom in J.
        rewrite J. simpl_env. auto.
      assert (y0 `notin` (AtomSetImpl.diff (fv_ee e) {{x0}})) as y0ne.
        apply notin_fv_ee_typing with (y:=y0) in Typinge; auto.
      assert (y0 `notin` (AtomSetImpl.diff (fv_ee e') {{x0}})) as y0ne'.
        apply notin_fv_ee_typing with (y:=y0) in Typinge'; auto.
      apply Hadmin; auto.

  Case "typ_arrow". (* arrow *)
  apply F_Related_ovalues_arrow_leq in Hrel.
  apply F_Related_ovalues_arrow_req.
  destruct Hrel as [Hv [Hv' [L' Harrow]]]; subst.
  simpl_env.
  repeat(split; auto).     
     apply value_through_subst_ee; auto.
     apply value_through_subst_ee; auto.
     SCase "arrow".
     exists (L' `union` {{x0}} `union` {{y0}}).
     intros lEnv1 x x' Htypingx Htypingx' Wfle Disj Harrow'.
     rename Harrow' into Hrel_wft1'.
     simpl_env in *.

     assert (y0 `notin` dom lEnv1) as y0notinlEnv1.
       destruct Disj as [Disj1 Disj2].
       apply Disj1; auto.
     assert (x0 `notin` dom lEnv1) as x0notinlEnv1.
       destruct Disj as [Disj1 Disj2].
       apply Disj1; auto.
     assert (disjdom L' (dom lEnv1)) as Disj'.
       destruct Disj as [Disj1 Disj2].
       split; intros z znotin.
         apply Disj1; auto.
         apply Disj2 in znotin; auto.
     assert (x0 `notin` dom Env) as x0notinlEnv.
       apply typing_regular in Typinge.
       decompose [and] Typinge. clear Typinge.
       apply disjoint_wf_lenv in H2.
       solve_uniq.
     assert (wf_lenv Env (lEnv1++lEnv'++[(x0, b)]++lEnv)) as Wfle'.
       apply wf_lenv_merge; auto.
          apply uniq_from_wf_lenv in Wfle.
          solve_uniq.
     destruct (@Harrow lEnv1 x x') as [u [u' [Hnorm_vxu [Hnorm_v'x'u' Hrel_wft1]]]]; auto.

     exists (subst_ee x0 y0 u). exists (subst_ee x0 y0 u').
     assert (y0 `notin` fv_ee x) as y0nx.
       apply notin_fv_ee_typing with (y:=y0) in Htypingx; auto.
     assert (y0 `notin` fv_ee x') as y0nx'.
       apply notin_fv_ee_typing with (y:=y0) in Htypingx'; auto.
     assert (x0 `notin` fv_ee x) as x0nx.
       apply notin_fv_ee_typing with (y:=x0) in Htypingx; auto.
     assert (x0 `notin` fv_ee x') as x0nx'.
       apply notin_fv_ee_typing with (y:=x0) in Htypingx'; auto.
     assert (y0 `notin` fv_ee e) as y0ne.
       apply notin_fv_ee_typing with (y:=y0) in Typinge; auto.
     assert (y0 `notin` fv_ee u) as y0nu.
       apply notin_fv_ee_mred with (e:=exp_app e x); auto.
         destruct Hnorm_vxu; auto.
     assert (y0 `notin` fv_ee e') as y0ne'.
       apply notin_fv_ee_typing with (y:=y0) in Typinge'; auto.
     assert (y0 `notin` fv_ee u') as y0nu'.
       apply notin_fv_ee_mred with (e:=exp_app e' x'); auto.
         destruct Hnorm_v'x'u'; auto.
     assert (J1:=Hnorm_vxu).
     apply  normalize_renaming_one with (x:=x0)(y:=y0) in Hnorm_vxu; auto.
     simpl in Hnorm_vxu. rewrite <- subst_ee_fresh with (e:=x) in Hnorm_vxu; auto.
     assert (J2:=Hnorm_v'x'u').
     apply  normalize_renaming_one with (x:=x0)(y:=y0) in Hnorm_v'x'u'; auto.
     simpl in Hnorm_v'x'u'. rewrite <- subst_ee_fresh with (e:=x') in Hnorm_v'x'u'; auto.
     repeat(split; auto).
       assert (typ_size t2 < typ_size (typ_arrow t1 t2)) as G2. simpl. omega.
       simpl in Fvy0.
       apply H with (e:=u)(e':=u')(t:=t2)(rsubst:=rsubst)(dsubst:=dsubst)(dsubst':=dsubst')(Env:=Env)(lEnv:=lEnv)(lEnv':=lEnv1++lEnv')(x0:=x0)(y0:=y0)(b:=b) (E:=E)in G2; simpl_env in *; auto.
         apply preservation_normalization with (e:=exp_app e x); auto.
           simpl_commut_subst in Typinge.
           apply typing_app with (D2:=lEnv1) (D1:=lEnv'++[(x0,b)]++lEnv)(T1:=apply_delta_subst_typ dsubst t1); auto.
              apply lenv_split_commute.
              apply disjoint__lenv_split; auto.
                 apply uniq_from_wf_lenv in Wfle. solve_uniq.

         apply preservation_normalization with (e:=exp_app e' x'); auto.
           simpl_commut_subst in Typinge'.
           apply typing_app with (D2:=lEnv1) (D1:=lEnv'++[(x0,b)]++lEnv)(T1:=apply_delta_subst_typ dsubst' t1); auto.
              apply lenv_split_commute.
              apply disjoint__lenv_split; auto.
                 apply uniq_from_wf_lenv in Wfle. solve_uniq.

  Case "typ_all". (* all *)
  apply F_Related_ovalues_all_leq in Hrel.
  apply F_Related_ovalues_all_req.
  destruct Hrel as [Hv [Hv' [L' Hall]]]; subst.
  simpl_env.
  repeat(split; auto).
     apply value_through_subst_ee; auto.
     apply value_through_subst_ee; auto.
     SCase "all".
     exists (L' `union`  dom Env `union` fv_lenv lEnv `union` fv_lenv lEnv' `union` {{x0}} `union` {{y0}} `union` dom E `union` dom dsubst `union` dom dsubst' `union` dom rsubst).
     intros X1 t3 t2'0 R0 Fr Hwfor' Hfv'.
     assert (X1 `notin` L') as Fr''. auto.
     destruct (@Hall X1 t3 t2'0 R0 Fr'') as [w0 [w'0 [Hnorm_vt2w0 [Hnorm_v't2'w'0 Hrel_wft]]]]; auto.
     exists (subst_ee x0 y0 w0). exists (subst_ee x0 y0 w'0). 
     assert (y0 `notin` fv_ee e) as y0ne.
       apply notin_fv_ee_typing with (y:=y0) in Typinge; auto.
     assert (y0 `notin` fv_ee e') as y0ne'.
       apply notin_fv_ee_typing with (y:=y0) in Typinge'; auto.
     assert (y0 `notin` fv_ee w0) as y0nw0.
       apply notin_fv_ee_mred with (e:=exp_tapp e t3); auto.
         destruct Hnorm_vt2w0; auto.
     assert (y0 `notin` fv_ee w'0) as y0nw'0.
       apply notin_fv_ee_mred with (e:=exp_tapp e' t2'0); auto.
         destruct Hnorm_v't2'w'0; auto.
     assert (J1:=Hnorm_vt2w0).
     assert (J2:=Hnorm_v't2'w'0).
     apply  normalize_renaming_one with (x:=x0)(y:=y0) in Hnorm_vt2w0; auto.
     simpl in Hnorm_vt2w0.
     apply  normalize_renaming_one with (x:=x0)(y:=y0) in Hnorm_v't2'w'0; auto.
     simpl in Hnorm_v't2'w'0.
     repeat(split; auto).
     assert (typ_size (open_tt t X1) < typ_size (typ_all t)) as G. 
       simpl. rewrite open_tt_typ_size_eq. omega.
     apply H with (e:=w0)(e':=w'0)(t:=(open_tt t X1))(rsubst:=[(X1,R0)]++rsubst)(dsubst:=[(X1,t3)]++dsubst)(dsubst':=[(X1,t2'0)]++dsubst')(Env:=Env)(lEnv:=lEnv)(lEnv':=lEnv')(x0:=x0)(y0:=y0)(b:=b)(E:=[(X1,bind_kn)]++E) in G; simpl_env; simpl; auto; simpl_env.
       apply rsubst_weaken_head; auto.
         apply dom_rho_subst in Hwfr. decompose [and] Hwfr; auto.
       apply odsubst_weaken_head; try solve [assumption].
         apply wfor_left_inv in Hwfor'; auto.
         apply dom_delta_osubst in Hwfd. decompose [and] Hwfd; auto.
         destruct_notin. auto.
       apply odsubst_weaken_head; try solve [assumption].
         apply wfor_right_inv in Hwfor'; auto.
         apply dom_delta_osubst in Hwfd'. decompose [and] Hwfd'; auto.
         destruct_notin. auto.
       apply preservation_normalization with (e:=exp_tapp e t3); auto.
         simpl_commut_subst in Typinge.
         assert (type t3) as type3.
           apply wfor_left_inv in Hwfor'.
           apply type_from_wf_typ in Hwfor'; auto.
         rewrite subst_tt_open_tt; auto.
         rewrite <- subst_tt_fresh with (T:=t); auto.
         simpl.
         destruct (X1==X1); try solve [contradict n; auto].
         rewrite commut_delta_osubst_open_tt with (dE:=E)(Env:=Env); auto.
         rewrite delta_osubst_closed_typ with (t:=t3); auto.
           apply typing_tapp; eauto using wfor_left_inv.

           apply wfor_left_inv in Hwfor'.
           split; intros x1 x1notin.
             apply in_fv_wf with (X:=x1) in Hwfor'; auto.
               apply disjoint_delta_osubst in Hwfd.
               decompose [and] Hwfd. clear Hwfd.
               clear H0 x1notin e0 y0ne y0ne' y0nw0 y0nw'0 Hfv' Fr'' Fr H n0 Hall.
               solve_uniq.

             apply notin_fv_wf with (X:=x1) in Hwfor'; auto.
               apply disjoint_delta_osubst in Hwfd.
               decompose [and] Hwfd. clear Hwfd.
               clear H0 e0 y0ne y0ne' y0nw0 y0nw'0 Hfv' Fr'' Fr H n0 Hall.
               solve_uniq.
       apply preservation_normalization with (e:=exp_tapp e' t2'0); auto.
         simpl_commut_subst in Typinge'.
         assert (type t2'0) as type2'0.
           apply wfor_right_inv in Hwfor'.
           apply type_from_wf_typ in Hwfor'; auto.
         rewrite subst_tt_open_tt; auto.
         rewrite <- subst_tt_fresh with (T:=t); auto.
         simpl.
         destruct (X1==X1); try solve [contradict n; auto].
         rewrite commut_delta_osubst_open_tt with (dE:=E)(Env:=Env); auto.
         rewrite delta_osubst_closed_typ with (t:=t2'0); auto.
           apply typing_tapp; eauto using wfor_right_inv.

           apply wfor_right_inv in Hwfor'.
           split; intros x1 x1notin.
             apply in_fv_wf with (X:=x1) in Hwfor'; auto.
               apply disjoint_delta_osubst in Hwfd'.
               decompose [and] Hwfd'. clear Hwfd'.
               clear H0 x1notin e0 y0ne y0ne' y0nw0 y0nw'0 Hfv' Fr'' Fr H n0 Hall.
               solve_uniq.

             apply notin_fv_wf with (X:=x1) in Hwfor'; auto.
               apply disjoint_delta_osubst in Hwfd'.
               decompose [and] Hwfd'. clear Hwfd'.
               clear H0 e0 y0ne y0ne' y0nw0 y0nw'0 Hfv' Fr'' Fr H n0 Hall.
               solve_uniq.

  Case "typ_bang". (* bang *)
  apply F_Related_ovalues_bang_leq in Hrel.
  apply F_Related_ovalues_bang_req.
  destruct Hrel as [Hv [Hv' [e1 [e1' [Heq [Heq' 
                                [u1 [u1' [Hnorm_e1u1 [Hnorm_e1'u1' Hrel_wft1]]]
                              ]]]]]]]; subst.
  simpl_commut_subst in Typinge.
  inversion Typinge; subst.
  contradict H0. simpl_env.
  apply nil_neq_one_mid.

  Case "typ_with". (* with *)
  apply F_Related_ovalues_with_leq in Hrel.
  apply F_Related_ovalues_with_req.
  destruct Hrel as [Hv [Hv' [e1 [e2 [e1' [e2' [Heq [Heq' 
                                [[u1 [u1' [Hnorm_e1u1 [Hnorm_e1'u1' Hrel_wft1]]]] 
                                 [u2 [u2' [Hnorm_e2u2 [Hnorm_e2'u2' Hrel_wft2]]]]]
                              ]]]]]]]]; subst.
  repeat(split; auto).
     apply value_through_subst_ee; auto.
     apply value_through_subst_ee; auto.
     SCase "with".
     exists (subst_ee x0 y0 e1). exists (subst_ee x0 y0 e2). 
     exists (subst_ee x0 y0 e1'). exists (subst_ee x0 y0 e2'). 
     repeat(split; auto).
       SSCase "with1".
       exists (subst_ee x0 y0 u1). exists (subst_ee x0 y0 u1'). 
       simpl in Fvy0.
       assert (y0 `notin` fv_ee e1) as y0ne1.
         apply notin_fv_ee_typing with (y:=y0) in Typinge; simpl in Typinge; auto.
       assert (y0 `notin` fv_ee u1) as y0nu1.
         apply notin_fv_ee_mred with (e:=e1); auto.
           destruct Hnorm_e1u1; auto.
       assert (y0 `notin` fv_ee e1') as y0ne1'.
         apply notin_fv_ee_typing with (y:=y0) in Typinge'; simpl in Typinge'; auto.
       assert (y0 `notin` fv_ee u1') as y0nu1'.
         apply notin_fv_ee_mred with (e:=e1'); auto.
           destruct Hnorm_e1'u1'; auto.
       assert (J1:=Hnorm_e1u1). assert (J2:=Hnorm_e1'u1').
       apply  normalize_renaming_one with (x:=x0)(y:=y0) in Hnorm_e1u1; auto.
       apply  normalize_renaming_one with (x:=x0)(y:=y0) in Hnorm_e1'u1'; auto.
       repeat(split;auto).
       assert (typ_size t1 < typ_size (typ_with t1 t2)) as G1. simpl. omega.
       apply H with (e:=u1)(e':=u1')(t:=t1)(rsubst:=rsubst)(dsubst:=dsubst)(dsubst':=dsubst')(Env:=Env)(lEnv:=lEnv)(lEnv':=lEnv')(x0:=x0)(y0:=y0)(b:=b)(E:=E) in G1; auto.
         apply preservation_normalization with (e:=e1); auto.
           simpl_commut_subst in Typinge. inversion Typinge; auto.
         apply preservation_normalization with (e:=e1'); auto.
           simpl_commut_subst in Typinge'. inversion Typinge'; auto.
       SSCase "with2".
       exists (subst_ee x0 y0 u2). exists (subst_ee x0 y0 u2'). 
       simpl in Fvy0.
       assert (y0 `notin` fv_ee e2) as y0ne2.
         apply notin_fv_ee_typing with (y:=y0) in Typinge; simpl in Typinge; auto.
       assert (y0 `notin` fv_ee u2) as y0nu2.
         apply notin_fv_ee_mred with (e:=e2); auto.
           destruct Hnorm_e2u2; auto.
       assert (y0 `notin` fv_ee e2') as y0ne2'.
         apply notin_fv_ee_typing with (y:=y0) in Typinge'; simpl in Typinge'; auto.
       assert (y0 `notin` fv_ee u2') as y0nu2'.
         apply notin_fv_ee_mred with (e:=e2'); auto.
           destruct Hnorm_e2'u2'; auto.
       assert (J1:=Hnorm_e2u2). assert (J2:=Hnorm_e2'u2').
       apply  normalize_renaming_one with (x:=x0)(y:=y0) in Hnorm_e2u2; auto.
       apply  normalize_renaming_one with (x:=x0)(y:=y0) in Hnorm_e2'u2'; auto.
       repeat(split; auto).
       assert (typ_size t2 < typ_size (typ_with t1 t2)) as G2. simpl. omega.
       apply H with (e:=u2)(e':=u2')(t:=t2)(rsubst:=rsubst)(dsubst:=dsubst)(dsubst':=dsubst')(Env:=Env)(lEnv:=lEnv)(lEnv':=lEnv')(x0:=x0)(y0:=y0)(b:=b)(E:=E) in G2; auto.
         apply preservation_normalization with (e:=e2); auto.
           simpl_commut_subst in Typinge. inversion Typinge; auto.
         apply preservation_normalization with (e:=e2'); auto.
           simpl_commut_subst in Typinge'. inversion Typinge'; auto.
Qed.

Lemma Forel_lin_renaming_one : forall t rsubst dsubst dsubst' e e' E Env lEnv' lEnv x0 y0 b,
  F_Related_ovalues t rsubst dsubst dsubst' e e' Env (lEnv'++[(x0, b)]++lEnv) ->
  wf_rho_subst E rsubst ->
  wf_delta_osubst E dsubst Env ->
  wf_delta_osubst E dsubst' Env ->
  typing Env (lEnv'++[(x0, b)]++lEnv) e (apply_delta_subst_typ dsubst t) ->
  typing Env (lEnv'++[(x0, b)]++lEnv) e' (apply_delta_subst_typ dsubst' t) ->
  y0 `notin` dom Env `union` dom lEnv' `union` dom lEnv ->
  F_Related_ovalues t rsubst dsubst dsubst' (subst_ee x0 y0 e) (subst_ee x0 y0 e') Env (lEnv'++[(y0, b)]++lEnv).
Proof.
  intros.
  assert (P_Forel_lin_renaming_one (typ_size t)).
    apply (@_Forel_lin_renaming_one (typ_size t)).
  unfold P_Forel_lin_renaming_one in H2.
  eauto.
Qed.

Lemma Forel_lin_renaming : forall t rsubst dsubst dsubst' e e' E Env lEnv x0 y0,
  F_Related_ovalues t rsubst dsubst dsubst' e e' Env lEnv ->
  wf_rho_subst E rsubst ->
  wf_delta_osubst E dsubst Env ->
  wf_delta_osubst E dsubst' Env ->
  typing Env lEnv e (apply_delta_subst_typ dsubst t) ->
  typing Env lEnv e' (apply_delta_subst_typ dsubst' t) ->
  x0 `notin` dom Env ->
  y0 `notin` dom Env `union` dom lEnv ->
  F_Related_ovalues t rsubst dsubst dsubst' (subst_ee x0 y0 e) (subst_ee x0 y0 e') Env (subst_atom_lenv lEnv x0 y0).
Proof.
  intros t rsubst dsubst dsubst' e e' E Env lEnv x0 y0 Hrel Hwfr Hwfd Hwfd' Typinge Typinge' x0notin y0notin.
  destruct (@in_dec x0 (dom lEnv)) as [x0in | x0notin'].
    apply binds_In_inv in x0in.
    destruct x0in as [b Binds].
    apply subst_atom_lenv_in_inv with (y:=y0) in Binds; eauto.
    destruct Binds as [lE1 [lE2 [EQ1 EQ2]]]; subst.
    rewrite EQ2.
    apply Forel_lin_renaming_one with (y0:=y0)(E:=E) in Hrel; auto.

    assert (J:=Typinge).
    apply notin_fv_ee_typing with (y:=x0) in Typinge; auto.
    apply notin_fv_ee_typing with (y:=x0) in Typinge'; auto.
    rewrite <- subst_ee_fresh; auto.
    rewrite <- subst_ee_fresh; auto.
    rewrite <- subst_atom_lenv_notin_inv; auto.
Qed.

Lemma Forel_lin_renamings : forall t rsubst dsubst dsubst' e e' E Env lEnv asubst,
  F_Related_ovalues t rsubst dsubst dsubst' e e' Env lEnv ->
  wf_rho_subst E rsubst ->
  wf_delta_osubst E dsubst Env ->
  wf_delta_osubst E dsubst' Env ->
  typing Env lEnv e (apply_delta_subst_typ dsubst t) ->
  typing Env lEnv e' (apply_delta_subst_typ dsubst' t) ->
  wf_atom_subst asubst ->
  disjoint asubst Env ->
  disjdom (atom_subst_codom asubst) (dom Env `union` dom lEnv) ->
  F_Related_ovalues t rsubst dsubst dsubst' (subst_atoms_exp asubst e) (subst_atoms_exp asubst e') Env (subst_atoms_lenv asubst lEnv).
Proof.
  intros t rsubst dsubst dsubst' e e' E Env lEnv asubst Hrel Hwfr Hwfd Hwfd' Typing Typing' Wfa Disj1 Disj2.
  generalize dependent E.
  generalize dependent Env.
  generalize dependent lEnv.
  generalize dependent e.
  generalize dependent e'.
  generalize dependent t.
  generalize dependent rsubst.
  generalize dependent dsubst.
  generalize dependent dsubst'.
  induction Wfa; intros; simpl; auto.
    apply IHWfa with (E:=E); auto.
      apply Forel_lin_renaming with (E:=E); auto.
        solve_uniq.

        destruct Disj2 as [J1 J2].
        apply J1.
        simpl. auto.

      apply typing_lin_renaming; auto.
        solve_uniq.

        destruct Disj2 as [J1 J2].
        apply J1.
        simpl. auto.

      apply typing_lin_renaming; auto.
        solve_uniq.

        destruct Disj2 as [J1 J2].
        apply J1.
        simpl. auto.

      solve_uniq.

      simpl in Disj2.
      destruct (in_dec x (dom lEnv)).
         apply binds_In_inv in i.
         destruct i as [a Binds].
         apply subst_atom_lenv_in_inv with (y:=y) in Binds; auto.
           destruct Binds as [lE1 [lE2 [EQ1 EQ2]]]; subst.
           rewrite EQ2.
           destruct Disj2 as [J1 J2].
           split; intros.
             assert (x0 <> y) as x0ny.
               rewrite asubst_atoms__dom_codom in H0.
               clear H IHWfa J1 J2 EQ2. fsetdec.
             assert (x0 `in` union {{y}} (atom_subst_codom AE)) as x0in. fsetdec.
             apply J1 in x0in. simpl_env in x0in. simpl_env. fsetdec.

             assert (x0 `in` {{y}} \/ x0 `in` (dom Env) `union` (dom lE1) `union` (dom lE2)) as x0in. 
               simpl_env in H1. fsetdec.
             clear H1.
             destruct x0in as [x0in | x0in].
               clear H J1 J2 Disj1 EQ2.
               rewrite asubst_atoms__dom_codom in H0.
               fsetdec.
                
               assert (x0 `in` (dom Env) `union` dom (lE1++[(x,a)]++lE2)) as x0in'. 
                 simpl_env. fsetdec.
               apply J2 in x0in'. fsetdec.
           apply typing_regular in Typing.
           decompose [and] Typing. apply uniq_from_wf_lenv in H3; auto.

         rewrite <- subst_atom_lenv_notin_inv with (x:=x) (y:=y)(lE:=lEnv); auto.
           destruct Disj2 as [J1 J2].
           split; intros.
              apply J1; auto.
              apply J2 in H1; auto.
Qed.

(*******************************************************************************)
(** Reverse Renaming *)

Lemma Forel_lin_rev_renamings : forall t rsubst dsubst dsubst' e e' E Env lEnv asubst,
  F_Related_ovalues t rsubst dsubst dsubst' e e' Env lEnv ->
  wf_rho_subst E rsubst ->
  wf_delta_osubst E dsubst Env ->
  wf_delta_osubst E dsubst' Env ->
  typing Env lEnv e (apply_delta_subst_typ dsubst t) ->
  typing Env lEnv e' (apply_delta_subst_typ dsubst' t) ->
  wf_atom_subst asubst ->
  disjdom (atom_subst_codom asubst) (dom Env) ->
  disjdom (dom asubst) (dom Env `union` dom lEnv) ->
  F_Related_ovalues t rsubst dsubst dsubst' (rev_subst_atoms_exp asubst e) (rev_subst_atoms_exp asubst e') Env (rev_subst_atoms_lenv asubst lEnv).
Proof.
  intros t rsubst dsubst dsubst' e e' E Env lEnv asubst Hrel Hwfr Hwfd Hwfd' Typing Typing' Wfa Disj1 Disj2.
  generalize dependent E.
  generalize dependent Env.
  generalize dependent lEnv.
  generalize dependent e.
  generalize dependent e'.
  generalize dependent t.
  generalize dependent rsubst.
  generalize dependent dsubst.
  generalize dependent dsubst'.
  induction Wfa; intros; simpl; auto.
    apply IHWfa with (E:=E); auto.
      apply Forel_lin_renaming with (E:=E); try solve [assumption].
        destruct Disj1 as [J1 J2].
        assert (y `in` atom_subst_codom ([(x,y)]++AE)). simpl. auto.
        apply J1 in H1. auto.

        destruct Disj2 as [J1 J2].
        apply J1.
        simpl. auto.

      apply typing_lin_renaming; try solve [assumption].
        destruct Disj1 as [J1 J2].
        assert (y `in` atom_subst_codom ([(x,y)]++AE)). simpl. auto.
        apply J1 in H1. auto.

        destruct Disj2 as [J1 J2].
        apply J1.
        simpl. auto.

      apply typing_lin_renaming; try solve [assumption].
        destruct Disj1 as [J1 J2].
        assert (y `in` atom_subst_codom ([(x,y)]++AE)). simpl. auto.
        apply J1 in H1. auto.

        destruct Disj2 as [J1 J2].
        apply J1.
        simpl. auto.

      destruct Disj1 as [J1 J2].
      split; intros.
        apply J1. simpl. auto.
        apply J2 in H1. simpl in H1. auto.

      simpl in Disj2.
      destruct (in_dec y (dom lEnv)).
         apply binds_In_inv in i.
         destruct i as [a Binds].
         apply subst_atom_lenv_in_inv with (y:=x) in Binds; auto.
           destruct Binds as [lE1 [lE2 [EQ1 EQ2]]]; subst.
           rewrite EQ2.
           destruct Disj2 as [J1 J2].
           split; intros.
             assert (x0 <> x) as x0ny.
               rewrite asubst_atoms__dom_codom in H.
               clear H0 IHWfa J1 J2 EQ2. fsetdec.
             assert (x0 `in` add x (dom AE)) as x0in. fsetdec.
             apply J1 in x0in. simpl_env in x0in. simpl_env. fsetdec.

             assert (x0 `in` {{x}} \/ x0 `in` (dom Env) `union` (dom lE1) `union` (dom lE2)) as x0in. 
               simpl_env in H1. fsetdec.
             clear H1.
             destruct x0in as [x0in | x0in].
               clear H0 J1 J2 Disj1 EQ2.
               rewrite asubst_atoms__dom_codom in H.
               fsetdec.
                
               assert (x0 `in` (dom Env) `union` dom (lE1++[(y,a)]++lE2)) as x0in'. 
                 simpl_env. fsetdec.
               apply J2 in x0in'. fsetdec.
           apply typing_regular in Typing.
           decompose [and] Typing. apply uniq_from_wf_lenv in H3; auto.

         rewrite <- subst_atom_lenv_notin_inv with (x:=y) (y:=x)(lE:=lEnv); auto.
           destruct Disj2 as [J1 J2].
           split; intros.
              apply J1; auto.
              apply J2 in H1; auto.
Qed.

(*******************************************************************************)
(** Dom Equal *)

Definition P_Forel_lin_domeq (n:nat) := 
  forall t rsubst dsubst dsubst' e e' Env lEnv lEnv',
  typ_size t = n ->
  F_Related_ovalues t rsubst dsubst dsubst' e e' Env lEnv ->
  wf_lenv Env lEnv ->
  dom lEnv [=] dom lEnv' ->
  F_Related_ovalues t rsubst dsubst dsubst' e e' Env lEnv'.

Lemma _Forel_lin_domeq :  forall n, P_Forel_lin_domeq n.
Proof.
  intro n.
  apply lt_wf_ind. clear n.
  intros n H.
  unfold P_Forel_lin_domeq in *.
  intros t rsubst dsubst dsubst' e e' Env lEnv lEnv'
         Htsize Hrel Hwfle Hdomeq.
 (typ_cases (destruct t) Case).

  Case "typ_bvar". (*bvar*)
  apply F_Related_ovalues_bvar_leq in Hrel; auto.

  Case "typ_fvar". (* fvar *)
  apply F_Related_ovalues_fvar_leq in Hrel.
  apply F_Related_ovalues_fvar_req.
  destruct Hrel as [R0 [Hb [Hv [Hv' Hr]]]]; subst; simpl.
  exists (R0).
    repeat(split; auto).

  Case "typ_arrow". (* arrow *)
  apply F_Related_ovalues_arrow_leq in Hrel.
  apply F_Related_ovalues_arrow_req.
  destruct Hrel as [Hv [Hv' [L' Harrow]]]; subst.
  simpl_env.
  repeat(split; auto).
     SCase "arrow".
     exists L'.
     intros lEnv1 x x' Htypingx Htypingx' Wfle Disj Harrow'.
     rename Harrow' into Hrel_wft1'.
     simpl_env in *.

     assert (wf_lenv Env (lEnv1++lEnv)) as Wfle'.
       apply wf_lenv_merge; auto.
          assert (disjoint lEnv1 lEnv') as Disj'.
            apply uniq_from_wf_lenv in Wfle.
            solve_uniq.
          apply disjoint_sym_1.
          apply disjoint_eq with (D1:=lEnv'); auto.
            rewrite Hdomeq. fsetdec.
     destruct (@Harrow lEnv1 x x') as [u [u' [Hnorm_vxu [Hnorm_v'x'u' Hrel_wft1]]]]; auto.

     exists (u). exists (u'). repeat(split; auto).
     assert (typ_size t2 < typ_size (typ_arrow t1 t2)) as G2. simpl. omega.
     apply H with (e:=u)(e':=u')(t:=t2)(rsubst:=rsubst)(dsubst:=dsubst)(dsubst':=dsubst')(Env:=Env)(lEnv:=lEnv1++lEnv)(lEnv':=lEnv1++lEnv') in G2; auto.
       simpl_env. rewrite Hdomeq. fsetdec.

  Case "typ_all". (* all *)
  apply F_Related_ovalues_all_leq in Hrel.
  apply F_Related_ovalues_all_req.
  destruct Hrel as [Hv [Hv' [L' Hall]]]; subst.
  simpl_env.
  repeat(split; auto).
     SCase "all".
     exists (L' `union`  dom Env `union` fv_lenv lEnv `union` fv_lenv lEnv').
      intros X1 t3 t2'0 R0 Fr Hwfor' Hfv'.
      assert (X1 `notin` L') as Fr''. auto.
      destruct (@Hall X1 t3 t2'0 R0 Fr'') as [w0 [w'0 [Hnorm_vt2w0 [Hnorm_v't2'w'0 Hrel_wft]]]]; auto.
      exists (w0). exists (w'0). repeat(split; auto).
      assert (typ_size (open_tt t X1) < typ_size (typ_all t)) as G. 
        simpl. rewrite open_tt_typ_size_eq. omega.
      apply H with (e:=w0)(e':=w'0)(t:=(open_tt t X1))(rsubst:=[(X1,R0)]++rsubst)(dsubst:=[(X1,t3)]++dsubst)(dsubst':=[(X1,t2'0)]++dsubst')(Env:=Env)(lEnv:=lEnv)(lEnv':=lEnv') in G; auto.

  Case "typ_bang". (* bang *)
  apply F_Related_ovalues_bang_leq in Hrel.
  apply F_Related_ovalues_bang_req.
  destruct Hrel as [Hv [Hv' [e1 [e1' [Heq [Heq' 
                                [u1 [u1' [Hnorm_e1u1 [Hnorm_e1'u1' Hrel_wft1]]]
                              ]]]]]]]; subst.
  repeat(split; auto).
     SCase "bang".
     exists (e1). exists (e1'). repeat(split; auto).
       exists (u1). exists (u1').  repeat(split;auto).
       assert (typ_size t < typ_size (typ_bang t)) as G1. simpl. omega.
       apply H with (e:=u1)(e':=u1')(t:=t)(rsubst:=rsubst)(dsubst:=dsubst)(dsubst':=dsubst')(Env:=Env)(lEnv:=lEnv)(lEnv':=lEnv') in G1; auto.

  Case "typ_with". (* with *)
  apply F_Related_ovalues_with_leq in Hrel.
  apply F_Related_ovalues_with_req.
  destruct Hrel as [Hv [Hv' [e1 [e2 [e1' [e2' [Heq [Heq' 
                                [[u1 [u1' [Hnorm_e1u1 [Hnorm_e1'u1' Hrel_wft1]]]] 
                                 [u2 [u2' [Hnorm_e2u2 [Hnorm_e2'u2' Hrel_wft2]]]]]
                              ]]]]]]]]; subst.
  repeat(split; auto).
     SCase "with".
     exists (e1). exists (e2). exists (e1'). exists (e2'). repeat(split; auto).
       SSCase "with1".
       exists (u1). exists (u1').  repeat(split;auto).
       assert (typ_size t1 < typ_size (typ_with t1 t2)) as G1. simpl. omega.
       apply H with (e:=u1)(e':=u1')(t:=t1)(rsubst:=rsubst)(dsubst:=dsubst)(dsubst':=dsubst')(Env:=Env)(lEnv:=lEnv)(lEnv':=lEnv') in G1; auto.
       SSCase "with2".
       exists (u2). exists (u2').  repeat(split; auto).
       assert (typ_size t2 < typ_size (typ_with t1 t2)) as G2. simpl. omega.
       apply H with (e:=u2)(e':=u2')(t:=t2)(rsubst:=rsubst)(dsubst:=dsubst)(dsubst':=dsubst')(Env:=Env)(lEnv:=lEnv)(lEnv':=lEnv') in G2; auto.
Qed.

Lemma Forel_lin_domeq : forall t rsubst dsubst dsubst' e e' Env lEnv lEnv',
  F_Related_ovalues t rsubst dsubst dsubst' e e' Env lEnv ->
  wf_lenv Env lEnv ->
  dom lEnv [=] dom lEnv' ->
  F_Related_ovalues t rsubst dsubst dsubst' e e' Env lEnv'.
Proof.
  intros.
  assert (P_Forel_lin_domeq (typ_size t)).
    apply (@_Forel_lin_domeq (typ_size t)).
  unfold P_Forel_lin_domeq in H2.
  eauto.
Qed.

(* **************************************** *)
(** * Weaken and Stronger of SystemF Relations *)
Definition P_Forel_weaken_stronger (n:nat) := 
  ((forall t E E' v v' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 Env lEnv X R t2 t2',
  typ_size t = n ->
  (F_Related_ovalues t (rsubst'++rsubst) (dsubst0++dsubst) (dsubst'0++dsubst') v v' Env lEnv ->
  ddom_env E [=] dom dsubst ->
  ddom_env E [=] dom dsubst' ->
  ddom_env E' [=] dom dsubst0 ->
  ddom_env E' [=] dom dsubst'0 ->
  ddom_env E [=] dom rsubst ->
  ddom_env E' [=] dom rsubst' ->
  X `notin` (fv_env E `union` fv_env E' `union` (fv_tt t) `union` fv_env Env `union` fv_lenv lEnv)->
  wf_typ Env t2 ->
  wf_typ Env t2' ->
  wf_rho_subst (E'++E) (rsubst' ++ rsubst) ->
  wf_delta_osubst (E'++E) (dsubst0 ++ dsubst) Env ->
  wf_delta_osubst (E'++E) (dsubst'0 ++ dsubst') Env ->
  F_Related_ovalues t (rsubst'++[(X, R)]++rsubst) (dsubst0++[(X,t2)]++dsubst) (dsubst'0++[(X,t2')]++dsubst') v v' Env lEnv))
  *
  (forall t E E' v v' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 Env lEnv X R t2 t2',
  typ_size t = n ->
  (F_Related_ovalues t (rsubst'++[(X, R)]++rsubst) (dsubst0++[(X,t2)]++dsubst) (dsubst'0++[(X,t2')]++dsubst') v v' Env lEnv ->
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
  F_Related_ovalues t (rsubst' ++ rsubst) (dsubst0 ++ dsubst) (dsubst'0 ++ dsubst') v v' Env lEnv )))%type
  .


Lemma _Forel_weaken_stronger:  forall n, P_Forel_weaken_stronger n.
Proof.
  intro n.
  apply lt_wf_ind. clear n.
  intros n H.
  unfold P_Forel_weaken_stronger in *.
  split.
  (* -> *)
  intros t E E' v v' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 Env lEnv X R t2 t2'
     Htsize Hrel H2dsubst H2dsubst' H2dsubst0 H2dsubst'0 H2rsubst H2rsubst' Hfv Hwft2 Hwft2' HwF_Rosubst Hwf_dsubst Hwf_dsubst'.
  (typ_cases (destruct t) Case).

  Case "typ_bvar". (*bvar*)
  apply F_Related_ovalues_bvar_leq in Hrel; auto.

  Case "typ_fvar". (* fvar *)
  apply F_Related_ovalues_fvar_leq in Hrel.
  apply F_Related_ovalues_fvar_req.
  destruct Hrel as [R0 [Hb [Hv [Hv' Hr]]]]; subst; simpl.
  exists (R0).
  simpl_env.
    repeat(split; auto).

  Case "typ_arrow". (* arrow *)
  apply F_Related_ovalues_arrow_leq in Hrel.
  apply F_Related_ovalues_arrow_req.
  destruct Hrel as [Hv [Hv' [L' Harrow]]]; subst.
  repeat(split; auto).
     SCase "arrow".
     exists (L' `union` {{X}}).
     intros lEnv1 x x' Htypingx Htypingx' Hwfle Disj Harrow'.
     destruct Harrow' as [w [w' [Hnorm_xw [Hnorm_x'w' Hrel_wft1']]]].
     simpl_env in *.

     assert (X `notin` fv_lenv lEnv1) as XnotinlEnv1.
       assert (X `notin` dom lEnv1) as J.
         destruct Disj as [J1 J2].
         apply J1; auto.
       apply typing_regular in Htypingx.
       decompose [and] Htypingx. clear Htypingx.
       apply wf_lenv_fv_lenv_sub in H2.
       clear H0 H1 H4 H Harrow H2dsubst H2dsubst' H2dsubst0 H2dsubst'0 H2rsubst H2rsubst'.
       destruct_notin.
       clear NotInTac NotInTac0 NotInTac2.
       assert (X `notin` dom Env) as J'.
         apply free_env__free_dom in NotInTac1; auto.
       fsetdec.

     assert (X `notin` fv_lenv (lEnv1++lEnv)) as XnotinlEnv.
       simpl_env. auto.

     assert (typ_size t1 < typ_size (typ_arrow t1 t3)) as G1. simpl. omega.
     apply H in G1. destruct G1 as [Hrel_wft1_wft1' Hrel_wft1'_wft1].
     simpl in Hfv.
     apply Hrel_wft1'_wft1 with (E:=E) (E':=E') in Hrel_wft1'; auto.
       SSCase "arrow".
       destruct (@Harrow lEnv1 x x') as [u [u' [Hnorm_vxu [Hnorm_v'x'u' Hrel_wft1]]]]; auto.
          apply typing_odsubst_stronger with (E:=E'++[(X,bind_kn)]++E)(X:=X)(t:=t2); eauto.
             apply odsubst_weaken; try solve [assumption].
               destruct_notin. auto.
          apply typing_odsubst_stronger with (E:=E'++[(X,bind_kn)]++E)(X:=X)(t:=t2'); eauto.
             apply odsubst_weaken; try solve [assumption].
               destruct_notin. auto.
          destruct Disj as [J1 J2].
          split; intros x0 x0notin.
             apply J1; auto.
             apply J2 in x0notin; auto.
          exists (w). exists (w'). split; auto.

       exists (u). exists (u'). repeat(split; auto).
       assert (typ_size t3 < typ_size (typ_arrow t1 t3)) as G2. simpl. omega.
       apply H in G2. destruct G2 as [Hrel_wft2_wft2' Hrel_wft2'_wft2].
       simpl in Hfv.
       apply Hrel_wft2_wft2' with (E:=E) (E':=E'); auto.
       SSCase "rsubst". eapply rsubst_weaken; eauto.
       SSCase "dsubst".
             apply odsubst_weaken; try solve [assumption].
               destruct_notin. auto.
       SSCase "dsubst'".
             apply odsubst_weaken; try solve [assumption].
               destruct_notin. auto.

  Case "typ_all". (* all *)
  apply F_Related_ovalues_all_leq in Hrel.
  apply F_Related_ovalues_all_req.
  destruct Hrel as [Hv [Hv' [L' Hall]]]; subst.
  repeat(split; auto).
     SCase "all".
     exists (L' `union` singleton X `union` fv_env E `union` fv_env E' `union` dom Env).
      intros X1 t3 t2'0 R0 Fr Hwfor' Hfv'.
      assert (X1 `notin` L') as Fr''. auto.
      destruct (@Hall X1 t3 t2'0 R0 Fr'') as [w0 [w'0 [Hnorm_vt2w0 [Hnorm_v't2'w'0 Hrel_wft]]]]; auto.
      exists (w0). exists (w'0). repeat(split; auto).
      assert (typ_size (open_tt t X1) < typ_size (typ_all t)) as G. 
        simpl. rewrite open_tt_typ_size_eq. omega.
      apply H in G. destruct G as [Hrel_wft_wft' Hrel_wft'_wft].
      simpl_env in Hrel_wft_wft'. clear H Hrel_wft'_wft.
      apply Hrel_wft_wft' with (t0:=(open_tt t X1)) 
                               (E':=[(X1,bind_kn)]++E')(E:=E)
                               (rsubst':=[(X1,R0)]++rsubst')(rsubst:=rsubst)
                               (dsubst0:=[(X1,t3)]++dsubst0)(dsubst:=dsubst)
                               (dsubst'0:=[(X1,t2'0)]++dsubst'0)(dsubst':=dsubst')
                               (v:=w0) (v':=w'0)
                               (X:=X) (R:=R) 
                               (t2:=t2) (t2':=t2')
                               ; simpl_env; auto; clear Hrel_wft_wft'.
          SSCase "fv".
          destruct_notin.
          simpl in *. auto using notin_fv_tt_open_tt.
          SSCase "dsubst".
          eapply odsubst_weaken_head; simpl_env; eauto using wfor_left_inv.
          SSCase "dsubst'".
          eapply odsubst_weaken_head; simpl_env; eauto using wfor_right_inv.

  Case "typ_bang". (* bang *)
  apply F_Related_ovalues_bang_leq in Hrel.
  apply F_Related_ovalues_bang_req.
  destruct Hrel as [Hv [Hv' [e1 [e1' [Heq [Heq' 
                                [u1 [u1' [Hnorm_e1u1 [Hnorm_e1'u1' Hrel_wft1]]]
                              ]]]]]]]; subst.
  repeat(split; auto).
     SCase "bang".
     simpl in Hfv.
     exists (e1). exists (e1'). repeat(split; auto).
       exists (u1). exists (u1').  repeat(split;auto).
       assert (typ_size t < typ_size (typ_bang t)) as G1. simpl. omega.
       apply H in G1. destruct G1 as [Hrel_wft1_wft1' Hrel_wft1'_wft1].
       simpl in Hfv.
       apply Hrel_wft1_wft1' with (E:=E) (E':=E'); auto.

  Case "typ_with". (* with *)
  apply F_Related_ovalues_with_leq in Hrel.
  apply F_Related_ovalues_with_req.
  destruct Hrel as [Hv [Hv' [e1 [e2 [e1' [e2' [Heq [Heq' 
                                [[u1 [u1' [Hnorm_e1u1 [Hnorm_e1'u1' Hrel_wft1]]]] 
                                 [u2 [u2' [Hnorm_e2u2 [Hnorm_e2'u2' Hrel_wft2]]]]]
                              ]]]]]]]]; subst.
  repeat(split; auto).
     SCase "with".
     simpl in Hfv.
     exists (e1). exists (e2). exists (e1'). exists (e2'). repeat(split; auto).
       SSCase "with1".
       exists (u1). exists (u1').  repeat(split;auto).
       assert (typ_size t1 < typ_size (typ_with t1 t3)) as G1. simpl. omega.
       apply H in G1. destruct G1 as [Hrel_wft1_wft1' Hrel_wft1'_wft1].
       simpl in Hfv.
       apply Hrel_wft1_wft1' with (E:=E) (E':=E'); auto.
       SSCase "with2".
       exists (u2). exists (u2').  repeat(split; auto).
       assert (typ_size t3 < typ_size (typ_with t1 t3)) as G2. simpl. omega.
       apply H in G2. destruct G2 as [Hrel_wft2_wft2' Hrel_wft2'_wft2].
      simpl in Hfv.
      apply Hrel_wft2_wft2' with (E:=E) (E':=E'); auto.

  (* <- *)
  intros t E E' v v' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 Env lEnv X R t2 t2'
     Htsize Hrel H2dsubst H2dsubst' H2dsubst0 H2dsubst'0 H2rsubst H2rsubst' Hfv Hwft2 Hwft2' HwF_Rosubst Hwf_dsubst Hwf_dsubst'.
  (typ_cases (destruct t) Case).

  Case "typ_bvar". (*bvar*)
  apply F_Related_ovalues_bvar_leq in Hrel; auto.

  Case "typ_fvar". (* fvar *)
  apply F_Related_ovalues_fvar_leq in Hrel.
  apply F_Related_ovalues_fvar_req.
  destruct Hrel as [R0 [Hb [Hv [Hv' Hr]]]]; subst; simpl.
  exists (R0).
  repeat(split; auto).
      simpl_env in Hb. simpl in Hfv.
      analyze_binds Hb.

  Case "typ_arrow". (* arrow *)
  apply F_Related_ovalues_arrow_leq in Hrel.
  apply F_Related_ovalues_arrow_req.
  destruct Hrel as [Hv [Hv' [L' Harrow]]]; subst.
  repeat(split; auto).
     SCase "arrow".
     exists (L' `union` {{X}}).
     intros lEnv1 x x' Htypingx Htypingx' Hwfle Disj Harrow'.
     destruct Harrow' as [w [w' [Hnorm_xw [Hnorm_x'w' Hrel_wft1]]]].
 
     assert (X `notin` fv_lenv lEnv1) as XnotinlEnv1.
       assert (X `notin` dom lEnv1) as J.
         destruct Disj as [J1 J2].
         apply J1; auto.
       apply typing_regular in Htypingx.
       decompose [and] Htypingx. clear Htypingx.
       apply wf_lenv_fv_lenv_sub in H2.
       clear H0 H1 H4 H Harrow H2dsubst H2dsubst' H2dsubst0 H2dsubst'0 H2rsubst H2rsubst'.
       destruct_notin.
       clear NotInTac NotInTac0 NotInTac2.
       assert (X `notin` dom Env) as J'.
         apply free_env__free_dom in NotInTac1; auto.
       fsetdec.
     assert (X `notin` fv_lenv (lEnv1++lEnv)) as XnotinlEnv.
       simpl_env. auto.

     assert (typ_size t1 < typ_size (typ_arrow t1 t3)) as G1. simpl. omega.
     apply H in G1. destruct G1 as [Hrel_wft1_wft1' Hrel_wft1'_wft1].
     simpl in Hfv.
     apply Hrel_wft1_wft1' with (X:=X)(R:=R)(t2:=t2)(t2':=t2')(E:=E) (E':=E') in Hrel_wft1; auto.
       SSCase "arrow".
       destruct (@Harrow lEnv1 x x') as [u [u' [Hnorm_vxu [Hnorm_v'x'u' Hrel_wft1']]]]; auto.
          apply typing_odsubst_weaken with (E:=E'++E); eauto using wfor_left_inv.
               apply odsubst_stronger with (t:=t2) (X:=X); eauto using wfor_left_inv.
          apply typing_odsubst_weaken with (E:=E'++E); eauto using wfor_right_inv.
               apply odsubst_stronger with (t:=t2') (X:=X); eauto using wfor_right_inv.
          destruct Disj as [J1 J2].
          split; intros x0 x0notin.
            apply J1; auto.
            apply J2 in x0notin; auto.
          exists (w). exists (w'). split; auto.

       exists (u). exists (u'). repeat(split; auto).
       assert (typ_size t3 < typ_size (typ_arrow t1 t3)) as G2. simpl. omega.
       apply H in G2. destruct G2 as [Hrel_wft2_wft2' Hrel_wft2'_wft2].
       simpl in Hfv.
       apply Hrel_wft2'_wft2 with (X:=X)(R:=R)(t2:=t2)(t2':=t2')(E:=E)(E':=E'); auto.
       SSCase "rsubst". apply rsubst_stronger  in HwF_Rosubst; eauto.
       SSCase "dsubst". apply odsubst_stronger with (t:=t2) in Hwf_dsubst; eauto using wfor_left_inv.
       SSCase "dsubst'". apply odsubst_stronger with (t:=t2') in Hwf_dsubst'; eauto using wfor_right_inv.

  Case "typ_all". (* all *)
  apply F_Related_ovalues_all_leq in Hrel.
  apply F_Related_ovalues_all_req.
  destruct Hrel as [Hv [Hv' [L' Hall]]]; subst.
  repeat(split; auto).
     SCase "all".
      exists (L' `union` singleton X  `union` fv_env E `union` fv_env E' `union` dom Env).
      intros X1 t3 t2'0 R0 Fr Hwfor' Hfv'.
      assert (X1 `notin` L') as Fr''. auto.
      destruct (@Hall X1 t3 t2'0 R0 Fr'') as [w0 [w'0 [Hnorm_vt2w0 [Hnorm_v't2'w'0 Hrel_wft]]]]; auto.
          destruct_notin. simpl_env. simpl. auto.
      exists (w0). exists (w'0). repeat(split; auto).
      assert (typ_size (open_tt t X1) < typ_size (typ_all t)) as G. 
        simpl. rewrite open_tt_typ_size_eq. omega.
      apply H in G. destruct G as [Hrel_wft_wft' Hrel_wft'_wft].
      simpl_env in Hrel_wft'_wft. clear H Hrel_wft_wft'.
      apply Hrel_wft'_wft with (t0:=(open_tt t X1)) 
                               (E':=[(X1,bind_kn)]++E')(E:=E)
                               (rsubst':=[(X1,R0)]++rsubst')(rsubst:=rsubst)
                               (dsubst0:=[(X1,t3)]++dsubst0)(dsubst:=dsubst)
                               (dsubst'0:=[(X1,t2'0)]++dsubst'0)(dsubst':=dsubst')
                               (v:=w0) (v':=w'0)
                               (X:=X) (R:=R) 
                               (t2:=t2) (t2':=t2')
                               ; simpl_env; auto; clear Hrel_wft'_wft.
          SSCase "fv".
          destruct_notin. simpl in NotInTac5. simpl.
          auto using notin_fv_tt_open_tt.
          SSCase "dsubst".
          simpl_env. eapply odsubst_weaken_head; simpl_env; eauto using wfor_left_inv.
          SSCase "dsubst'".
          simpl_env. eapply odsubst_weaken_head; simpl_env; eauto using wfor_right_inv.

  Case "typ_bang". (* bang *)
  apply F_Related_ovalues_bang_leq in Hrel.
  apply F_Related_ovalues_bang_req.
  destruct Hrel as [Hv [Hv' [e1 [e1' [Heq [Heq' 
                                [u1 [u1' [Hnorm_e1u1 [Hnorm_e1'u1' Hrel_wft1]]]
                              ]]]]]]]; subst.
  repeat(split; auto).
     SCase "bang".
     simpl in Hfv.
     exists (e1).  exists (e1'). repeat(split; auto).
       exists (u1). exists (u1'). repeat(split; auto).
       assert (typ_size t < typ_size (typ_bang t)) as G1. simpl. omega.
       apply H in G1. destruct G1 as [Hrel_wft1_wft1' Hrel_wft1'_wft1].
       simpl in Hfv.
       eapply Hrel_wft1'_wft1; eauto.

  Case "typ_with". (* with *)
  apply F_Related_ovalues_with_leq in Hrel.
  apply F_Related_ovalues_with_req.
  destruct Hrel as [Hv [Hv' [e1 [e2 [e1' [e2' [Heq [Heq' 
                                [[u1 [u1' [Hnorm_e1u1 [Hnorm_e1'u1' Hrel_wft1]]]] 
                                 [u2 [u2' [Hnorm_e2u2 [Hnorm_e2'u2' Hrel_wft2]]]]]
                              ]]]]]]]]; subst.
  repeat(split; auto).
     SCase "with".
     simpl in Hfv.
     exists (e1). exists (e2). exists (e1'). exists (e2'). repeat(split; auto).
       SSCase "with1".
       exists (u1). exists (u1'). repeat(split; auto).
       assert (typ_size t1 < typ_size (typ_with t1 t3)) as G1. simpl. omega.
       apply H in G1. destruct G1 as [Hrel_wft1_wft1' Hrel_wft1'_wft1].
       simpl in Hfv.
       eapply Hrel_wft1'_wft1; eauto.
       SSCase "with2".
       exists (u2). exists (u2'). repeat(split; auto).
       assert (typ_size t3 < typ_size (typ_with t1 t3)) as G2. simpl. omega.
       apply H in G2. destruct G2 as [Hrel_wft2_wft2' Hrel_wft2'_wft2].
       simpl in Hfv.
       eapply Hrel_wft2'_wft2; eauto.
Qed.

Lemma Forel_weaken: forall t E E' v v' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 Env lEnv X R t2 t2',
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
Proof.
  intros.
  assert (P_Forel_weaken_stronger (typ_size t)).
    apply (@_Forel_weaken_stronger (typ_size t)).
  unfold P_Forel_weaken_stronger in H12.
  decompose [prod] H12.
  eapply a; eauto.
Qed.

Lemma Forel_weaken_head:  forall t E v v' rsubst dsubst dsubst' Env lEnv X R t2 t2',
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
Proof.
  intros.
  apply Forel_weaken with (E:=E) (E':=@nil (atom*binding)) (X:=X) (R:=R)
                            (t:=t) 
                            (rsubst:=rsubst) (rsubst':=rho_nil)
                            (dsubst:=dsubst) (dsubst0:=delta_nil)
                            (dsubst':=dsubst') (dsubst'0:=delta_nil)
                            (t2:=t2) (t2':=t2') (v:=v) (v':=v'); auto.
Qed.

Lemma Forel_stronger:  forall t E E' v v' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 Env lEnv X R t2 t2',
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
Proof.
  intros.
  assert (P_Forel_weaken_stronger (typ_size t)).
    apply (@_Forel_weaken_stronger (typ_size t)).
  unfold P_Forel_weaken_stronger in H12.
  decompose [prod] H12.
  eapply b; eauto.
Qed.

Lemma bindosgE__bindosgsubst: forall E lE gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv x T,
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
Proof.
  intros E lE gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv x T Hrel_sub Hbinds Hwft.
  generalize dependent x.
  generalize dependent T.
  (F_Related_osubst_cases (induction Hrel_sub) Case); intros.
  Case "F_Related_osubst_empty".
    inversion Hbinds.
  Case "F_Related_osubst_kind".
    analyze_binds Hbinds.
    apply F_Related_osubst__inversion in Hrel_sub. 
    destruct Hrel_sub as [[[[[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe] Hwfe'] HwfEnv] HwflEnv].
    assert (wf_typ E T) as WFT'.
      apply wf_typ_from_binds_typ with (E:=E) (x:=x); auto.
    assert (X `notin` fv_tt T); eauto using notin_fv_wf.
    apply IHHrel_sub in BindsTac; auto.
    destruct BindsTac as [J1 [J2 [e [e' [[[[Hbinds Hbinds'] Ht] Ht'] [v [v' [Htt [Htt' [Hnorm [Hnorm' Hrel]]]]]]]]]]].
    split; auto.
    split; auto.
       exists (e). exists (e').
       split; simpl; auto.
         rewrite <- subst_tt_fresh; auto.
       split; simpl; auto.
         rewrite <- subst_tt_fresh; auto.

       exists (v). exists (v').
       split; simpl; auto.
         rewrite <- subst_tt_fresh; auto.
       split; simpl; auto.
         rewrite <- subst_tt_fresh; auto.
       split; auto.
       split; auto.
         apply Forel_weaken_head with (E:=E) (X:=X) (R:=R)
                            (t:=T) (rsubst:=rsubst) (dsubst:=dsubst) (dsubst':=dsubst') 
                            (t2:=t) (t2':=t') (v:=v) (v':=v'); eauto using dom_delta_osubst, dom_rho_subst, wfor_left_inv, wfor_right_inv.

  Case "F_Related_osubst_typ".
    apply F_Related_osubst__inversion in Hrel_sub. 
    destruct Hrel_sub as [[[[[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe] Hwfe'] HwfEnv] HwflEnv].
    destruct (x0 == x); subst.
    SCase "x0=x".
      rewrite_env (nil ++ [(x, bind_typ t)] ++ E) in Hbinds.
      apply binds_mid_eq in Hbinds. inversion Hbinds. subst.
      split.
       apply wf_lgamma_osubst__nfv with (x:=x) in Hwflg; auto.
         decompose [and] Hwflg; auto.
      split.
       apply wf_lgamma_osubst__nfv with (x:=x) in Hwflg'; auto.
         decompose [and] Hwflg; auto.
      exists (e). exists (e').
      repeat(split; auto).
         SSCase "uniq".
         simpl_env. apply uniq_push; eauto.
    SCase "x0<>x".
      analyze_binds Hbinds.
        assert (wf_typ E T) as WFT0'.
          apply wf_typ_strengthening with (E:=E) (F:=@nil (atom*binding)) (x:=x) (U:=t); auto.

        apply (@IHHrel_sub T WFT0' x0) in BindsTac.
        destruct BindsTac as [J1 [J2 [v0 [v'0 [[[[Hbinds1 Hbinds2] Htt] Htt'] Hrel]]]]].
        split.
         apply wf_lgamma_osubst__nfv with (x:=x) in Hwflg; auto.
           decompose [and] Hwflg; auto.
        split.
         apply wf_lgamma_osubst__nfv with (x:=x) in Hwflg'; auto.
           decompose [and] Hwflg; auto.
         exists (v0). exists (v'0).
         repeat(split; auto).

  Case "F_Related_osubst_ltyp".
    apply F_Related_osubst__inversion in Hrel_sub. 
    destruct Hrel_sub as [[[[[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe] Hwfe'] HwfEnv] HwflEnv].
    assert (J:=Hbinds).
    apply (@IHHrel_sub T Hwft x0) in Hbinds.
    destruct Hbinds as [J1 [J2 Hbinds]].
    split. 
      apply binds_In in J.
      rewrite dom_app.
      destruct (x0 == x); subst; auto.
         contradict J; auto.
    split; auto.
      apply binds_In in J.
      rewrite dom_app.
      destruct (x0 == x); subst; auto.
         contradict J; auto.
Qed.

Lemma lbindosgE__lbindosgsubst: forall E gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv x T,
    F_Related_osubst E [(x, lbind_typ T)] gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
    wf_typ E T ->
    x `notin` dom gsubst /\ x `notin` dom gsubst' /\
    (exists e, exists e',
                ((binds x (e) lgsubst)
                *(binds x (e') lgsubst')
                *(typing Env lEnv e (apply_delta_subst_typ dsubst T))*(typing Env lEnv e' (apply_delta_subst_typ dsubst' T))
                *(F_Related_oterms T rsubst dsubst dsubst' e e' Env lEnv))%type)
    .
Proof.
  intros E gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv x T Hrel_sub Hwft.
  remember [(x, lbind_typ T)] as lE.
  generalize dependent x.
  generalize dependent T.
  (F_Related_osubst_cases (induction Hrel_sub) Case); intros; subst.
  Case "F_Related_osubst_empty".
    inversion HeqlE.
  Case "F_Related_osubst_kind".
    apply F_Related_osubst__inversion in Hrel_sub. 
    destruct Hrel_sub as [[[[[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe] Hwfe'] HwfEnv] HwflEnv].
    assert (wf_typ E T ) as WFT'.
      apply wf_typ_from_lbinds_typ with (E:=E)(lE:=[(x, lbind_typ T)])(x:=x); auto.
    assert (X `notin` fv_tt T); eauto using notin_fv_wf.
    apply IHHrel_sub with (x0:=x) in WFT'; auto.
    destruct WFT' as [J1 [J2 [e [e' [[[[Hbinds Hbinds'] Ht] Ht'] [v [v' [Htt [Htt' [Hnorm [Hnorm' Hrel]]]]]]]]]]].
    split; auto.
    split; auto.
       exists (e). exists (e').
       split; simpl; auto.
         rewrite <- subst_tt_fresh; auto.
       split; simpl; auto.
         rewrite <- subst_tt_fresh; auto.

       exists (v). exists (v').
       split; simpl; auto.
         rewrite <- subst_tt_fresh; auto.
       split; simpl; auto.
         rewrite <- subst_tt_fresh; auto.
       split; auto.
       split; auto.
         apply Forel_weaken_head with (E:=E) (X:=X) (R:=R)
                            (t:=T) (rsubst:=rsubst) (dsubst:=dsubst) (dsubst':=dsubst') 
                            (t2:=t) (t2':=t') (v:=v) (v':=v'); eauto using dom_delta_osubst, dom_rho_subst, wfor_left_inv, wfor_right_inv.

  Case "F_Related_osubst_typ".
    apply F_Related_osubst__inversion in Hrel_sub. 
    destruct Hrel_sub as [[[[[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe] Hwfe'] HwfEnv] HwflEnv].
    assert (wf_typ E T) as WFT0'.
      apply wf_typ_strengthening with (E:=E) (F:=@nil (atom*binding)) (x:=x) (U:=t); auto.
    apply IHHrel_sub with (x:=x0) in WFT0'; auto.
    destruct WFT0' as [J1 [J2 [e0 [e'0 [[[[Hbinds1 Hbinds2] Htt] Htt'] Hrel]]]]].
    split. 
      rewrite dom_app.
      destruct (x0 == x); subst; auto.
         destruct_notin. contradict NotInTac1; simpl; auto.
    split.
      rewrite dom_app.
      destruct (x0 == x); subst; auto.
         destruct_notin. contradict NotInTac1; simpl; auto.

      exists (e0). exists (e'0).
      repeat(split; auto).

  Case "F_Related_osubst_ltyp".
    apply F_Related_osubst__inversion in Hrel_sub. 
    destruct Hrel_sub as [[[[[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe] Hwfe'] HwfEnv] HwflEnv].
    inversion HeqlE; subst.
    assert (dom lEnv1 [=] {}) as lEnv1Nil.
      apply wf_lgamma_osubst_empty_linctx in Hwflg; auto.
    apply empty_dom__empty_ctx in lEnv1Nil. subst.
    split.
     apply wf_lgamma_osubst__nfv with (x:=x0) in Hwflg; auto.
       decompose [and] Hwflg; auto.
    split.
     apply wf_lgamma_osubst__nfv with (x:=x0) in Hwflg'; auto.
       decompose [and] Hwflg; auto.

     exists (e). exists (e').
     simpl_env in *.
     repeat(split; auto).
Qed.

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

Lemma F_FORel__R__wfor: forall (E:env) (t:typ) (rsubst:rho_subst) dsubst dsubst' Env (R:rel),
  F_FORel__R t E rsubst dsubst dsubst' Env R -> 
  wf_typ E t ->
  wfor Env R (apply_delta_subst_typ dsubst t) (apply_delta_subst_typ dsubst' t).
Proof.
  intros E t rsubst dsubst dsubst' Env R Hr_eq Hwft.
  unfold F_ORel__R in Hr_eq. unfold wfor. 
  destruct Hr_eq as [Hwfd [Hwfd' [Hwfor Hr_eq]]].
  split. apply wft_osubst with (E:=E); auto.
  split. apply wft_osubst with (E:=E); auto.
          intros v v' Rvv' x y Fvx Fvx' Fvy.
          destruct (@Hr_eq v v') as [J1 J2].
          destruct (@Hr_eq (subst_ee x y v) (subst_ee x y v')) as [J3 J4].
          apply J3. apply J2 in Rvv'.
          destruct Rvv' as [lEnv [Typingv [Typingv' Rvv']]].
          assert (J:=Typingv). apply typing_ldom in J.
          assert (J':=Typingv'). apply typing_ldom in J'.
          rewrite J in Fvx.
          assert (x `notin` dom Env) as xnotinEnv.
            apply typing_regular in Typingv.
            decompose [and] Typingv.
            apply disjoint_wf_lenv in H1.
            clear H H0 H3 J1 J2 J3 J4 Fvx' Fvy Typingv.
            solve_uniq.
          destruct (x==y); subst.
             rewrite subst_ee_id. rewrite subst_ee_id.
             exists lEnv. split; auto.
          
            assert (y `notin` dom lEnv) as ynotinlEnv.
              rewrite <- J.
              clear J1 J2 J3 J4 J J' Fvx Fvx'.
              fsetdec.
            assert (y `notin` dom Env) as ynotinEnv.
              clear J1 J2 J3 J4 J J' Fvx Fvx'.
              fsetdec.
            exists (subst_atom_lenv lEnv x y).
            split.
              apply typing_lin_renaming; auto.
            split.
              apply typing_lin_renaming; auto.
              apply Forel_lin_renaming with (E:=E); auto.
Qed.

(** * Subst of SystemF Relations *)
Definition P_oparametricity_subst_value (n:nat) := 
  forall t E E' e e' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 Env lEnv X R t2 k,
  typ_size t = n ->
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
  (F_Related_ovalues (open_tt_rec k (typ_fvar X) t) 
               (rsubst'++[(X, R)]++rsubst) 
               (dsubst0++[(X,(apply_delta_subst_typ (dsubst0++dsubst) t2))]++dsubst) 
               (dsubst'0++[(X,(apply_delta_subst_typ (dsubst'0++dsubst') t2))]++dsubst') 
                e e' Env lEnv ->
  typing Env lEnv e (apply_delta_subst_typ (dsubst0++[(X,(apply_delta_subst_typ (dsubst0++dsubst) t2))]++dsubst) (open_tt_rec k (typ_fvar X) t)) ->
  typing Env lEnv e' (apply_delta_subst_typ (dsubst'0++[(X,(apply_delta_subst_typ (dsubst'0++dsubst') t2))]++dsubst') (open_tt_rec k (typ_fvar X) t)) ->
  wf_rho_subst (E'++[(X, bind_kn)]++E) (rsubst'++[(X, R)]++rsubst) ->
  wf_delta_osubst (E'++[(X, bind_kn)]++E) (dsubst0++[(X,(apply_delta_subst_typ (dsubst0++dsubst) t2))]++dsubst) Env -> 
  wf_delta_osubst (E'++[(X, bind_kn)]++E) (dsubst'0++[(X,(apply_delta_subst_typ (dsubst'0++dsubst') t2))]++dsubst') Env -> 
  F_Related_ovalues (open_tt_rec k t2 t) (rsubst'++rsubst) (dsubst0++dsubst) (dsubst'0++dsubst') e e' Env lEnv)
  *
  (F_Related_ovalues (open_tt_rec k  t2 t) (rsubst'++rsubst) (dsubst0++dsubst) (dsubst'0++dsubst') e e' Env lEnv ->
  typing Env lEnv e (apply_delta_subst_typ (dsubst0++dsubst) (open_tt_rec k t2 t)) ->
  typing Env lEnv e' (apply_delta_subst_typ (dsubst'0++dsubst') (open_tt_rec k t2 t)) ->
  wf_rho_subst (E'++E) (rsubst'++rsubst) ->
  wf_delta_osubst (E'++E) (dsubst0++dsubst) Env -> 
  wf_delta_osubst (E'++E) (dsubst'0++dsubst') Env -> 
  F_Related_ovalues (open_tt_rec k (typ_fvar X) t) 
              (rsubst'++[(X, R)]++rsubst) 
              (dsubst0++[(X,(apply_delta_subst_typ (dsubst0++dsubst) t2))]++dsubst) 
              (dsubst'0++[(X,(apply_delta_subst_typ (dsubst'0++dsubst') t2))]++dsubst')
              e e' Env lEnv)
  .

Lemma _oparametricity_subst_value_left : forall n,
  (forall m, m<n -> P_oparametricity_subst_value m) ->
  forall  t E E' e e' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 Env lEnv X R t2 k,
  typ_size t = n ->  
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
  wfor Env R (apply_delta_subst_typ (dsubst0++dsubst) t2) (apply_delta_subst_typ (dsubst'0++dsubst') t2) ->
  (F_Related_ovalues (open_tt_rec k (typ_fvar X) t) 
               (rsubst'++[(X, R)]++rsubst) 
               (dsubst0++[(X,(apply_delta_subst_typ (dsubst0++dsubst) t2))]++dsubst) 
               (dsubst'0++[(X,(apply_delta_subst_typ (dsubst'0++dsubst') t2))]++dsubst') 
                e e' Env lEnv ->
  typing Env lEnv e (apply_delta_subst_typ (dsubst0++[(X,(apply_delta_subst_typ (dsubst0++dsubst) t2))]++dsubst) (open_tt_rec k (typ_fvar X) t)) ->
  typing Env lEnv e' (apply_delta_subst_typ (dsubst'0++[(X,(apply_delta_subst_typ (dsubst'0++dsubst') t2))]++dsubst') (open_tt_rec k (typ_fvar X) t)) ->
  wf_rho_subst (E'++[(X, bind_kn)]++E) (rsubst'++[(X, R)]++rsubst) ->
  wf_delta_osubst (E'++[(X, bind_kn)]++E) (dsubst0++[(X,(apply_delta_subst_typ (dsubst0++dsubst) t2))]++dsubst) Env -> 
  wf_delta_osubst (E'++[(X, bind_kn)]++E) (dsubst'0++[(X,(apply_delta_subst_typ (dsubst'0++dsubst') t2))]++dsubst') Env -> 
  F_Related_ovalues (open_tt_rec k t2 t) (rsubst'++rsubst) (dsubst0++dsubst) (dsubst'0++dsubst') e e' Env lEnv).
Proof.
  intros n H t E E' e e' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 Env lEnv X R t2 k
         Htsize Hwft Hwft' Hwft2 Hr_eq Hfv H1dsubst  H1dsubst'  H1dsubst0  H1dsubst'0  H1rsubst  H1rsubst' HwfoR.  
  unfold P_oparametricity_subst_value in *.
  intros Hrel Typinge Typinge' Hwfor Hwfd Hwfd'.
  (typ_cases (induction t) Case); simpl in Hrel; simpl; 
    simpl in Typinge; simpl in Typinge'; simpl_env in *.

  Case "typ_bvar". (* bvar *)
  destruct (k==n0); subst.
    SCase "fvar".
    apply F_Related_ovalues_fvar_leq in Hrel.
    destruct Hrel as [R0 [Hb [Hv [Hv' [Hadmin Hr]]]]]; subst; simpl.
    assert (R=R0).
      simpl_env in Hb.
      apply binds_mid_eq in Hb; auto.
      simpl_env in Hwfor. apply wf_rho_subst__uniq in Hwfor. decompose [and] Hwfor; auto.
    subst.
    assert (
      (F_FORel t2 (rsubst'++rsubst) (dsubst0++dsubst) (dsubst'0++dsubst') Env e e' -> R0 e e') *
      (R0 e e' -> F_FORel t2 (rsubst'++rsubst) (dsubst0++dsubst) (dsubst'0++dsubst') Env e e')
      ) as HR'.
      unfold F_FORel__R in Hr_eq. decompose [and] Hr_eq. auto.
    destruct HR' as [Hrel_r Hr_rel].
    apply Hr_rel in Hr; auto.
    destruct Hr as [lEnv' [Htypinge [Htypinge' Hr]]].
    apply Forel_lin_domeq with (lEnv:=lEnv'); auto.
      apply typing_ldom in Htypinge.
      apply typing_ldom in Typinge.
      rewrite <- Htypinge. rewrite <- Typinge.
      fsetdec.

    SCase "bvar".
    apply F_Related_ovalues_bvar_leq in Hrel; auto.

  Case "typ_fvar". (* fvar *)
  apply F_Related_ovalues_fvar_leq in Hrel.
  apply F_Related_ovalues_fvar_req.  
  destruct Hrel as [R0 [Hb [Hv [Hv' [Hadmin Hr]]]]]; subst; simpl.
  exists (R0).
  repeat(split; auto).
    simpl in Hfv.  analyze_binds Hb.

  Case "typ_arrow". (* arrow *)
  apply F_Related_ovalues_arrow_leq in Hrel.
  apply F_Related_ovalues_arrow_req.  
  destruct Hrel as [Hv [Hv' [L' Harrow]]]; subst.
  simpl in Hfv.  simpl_env in *.
  repeat(split; auto).
         SCase "arrow". 
         exists (L' `union` {{X}}).
         intros lEnv1 x x' Htypingx Htypingx' Hwfle Disj Harrow'.
         destruct Harrow' as [v [v' [Hnorm_xv [Hnorm_x'v' Hrel_wft1']]]].        
 
         assert (X `notin` fv_lenv lEnv1) as XnotinlEnv1.
           assert (X `notin` dom lEnv1) as J.
             destruct Disj as [J1 J2].
             apply J1; auto.
           apply typing_regular in Htypingx.
           decompose [and] Htypingx. clear Htypingx.
           apply wf_lenv_fv_lenv_sub in H2.
           clear H0 H1 H4 H Harrow H1dsubst H1dsubst' H1dsubst0 H1dsubst'0 H1rsubst H1rsubst'.
           destruct_notin.
           clear NotInTac NotInTac0 NotInTac2.
           assert (X `notin` dom Env) as J'.
             apply free_env__free_dom in NotInTac3; auto.
           fsetdec.
         assert (X `notin` fv_lenv (lEnv1++lEnv)) as XnotinlEnv.
           simpl_env. auto.

         destruct (@Harrow lEnv1 x x') as [u [u' [Hnorm_vxu [Hnorm_v'x'u' Hrel_wft1]]]]; auto.
           SSCase "typing". eapply m_typing_ovar_stronger; eauto using wfor_left_inv.
           SSCase "typing". eapply m_typing_ovar_stronger; eauto using wfor_right_inv.
           SSCase "Disj".
             destruct Disj as [J1 J2].
             split; intros x0 x0notin.
               apply J1; auto.
               apply J2 in x0notin; auto.
           SSCase "arrow_left". 
           assert (typ_size t1 < typ_size (typ_arrow t1 t3)) as G1. simpl. omega.
           apply H with (E:=E) (E':=E') (e:=v) (e':=v') (t:=t1) (Env:=Env) (lEnv:=lEnv1)
                        (rsubst:=rsubst) (dsubst:=dsubst) (dsubst':=dsubst')
                        (X:=X) (R:=R) (t2:=t2) (k:=k)
                        (rsubst':=rsubst') (dsubst0:=dsubst0) (dsubst'0:=dsubst'0) in G1; try solve [assumption].
              SSSCase "arrow_left". 
              destruct G1 as [Hrel_wft1_wft1' Hrel_wft1'_wft1].
              simpl in Hrel_wft1'_wft1. apply Hrel_wft1'_wft1 in Hrel_wft1'; auto.
                exists(v). exists(v'). simpl in Hfv. split; auto.
                SSSSCase  "typing". apply preservation_normalization with (e:=x); auto.
                SSSSCase  "typing". apply preservation_normalization with (e:=x'); auto.
                SSSSCase "rsubst". eapply rsubst_stronger; eauto.
                SSSSCase "dsubst". eapply odsubst_stronger; eauto using wfor_left_inv.
                SSSSCase "dsubst'". eapply odsubst_stronger; eauto using wfor_right_inv.
              SSSCase "sizeeq".  auto.
              SSSCase "wft". 
              simpl in Hwft. apply wft_arrow_inv in Hwft. destruct Hwft; auto.
              simpl in Hwft'. apply wft_arrow_inv in Hwft'. destruct Hwft'; auto.
              SSSCase "fv". 
              assert (X `notin` fv_te v). 
                eapply m_typing_onormalization_fv with (e:=x); eauto.
              assert (X `notin` fv_te v'). 
                eapply m_typing_onormalization_fv with (e:=x'); eauto.
              destruct_notin. auto.
         SSCase "arrow_right". 
         exists (u). exists (u'). 
         repeat(split; auto).
           assert (typ_size t3 < typ_size (typ_arrow t1 t3)) as G2. simpl. omega.
           apply H with (E:=E) (E':=E') (e:=u) (e':=u') (t:=t3) (Env:=Env) (lEnv:=lEnv1++lEnv)
                        (rsubst:=rsubst) (dsubst:=dsubst) (dsubst':=dsubst')
                        (X:=X) (R:=R) (t2:=t2) (k:=k) 
                        (rsubst':=rsubst') (dsubst0:=dsubst0) (dsubst'0:=dsubst'0) in G2; try solve [assumption].
            destruct G2 as [Hrel_wft2_wft2' Hrel_wft2'_wft2]; auto.
            apply Hrel_wft2_wft2'; auto.
              SSSSCase "typing".
              apply preservation_normalization with (e:=exp_app e x); auto.
                apply typing_app with (D1:=lEnv) (D2:=lEnv1) (T1:=apply_delta_subst_typ (dsubst0++[(X, apply_delta_subst_typ (dsubst0++dsubst) t2)]++dsubst) (open_tt_rec k X t1)); auto.
                  simpl_commut_subst in Typinge. auto.
                  eapply m_typing_ovar_stronger; eauto using wfor_left_inv.
                  apply lenv_split_commute.
                    apply disjoint__lenv_split; auto.
                       apply uniq_from_wf_lenv in Hwfle. solve_uniq.
              SSSSCase "typing".
              apply preservation_normalization with (e:=exp_app e' x'); auto.
                apply typing_app with (D1:=lEnv) (D2:=lEnv1) (T1:=apply_delta_subst_typ (dsubst'0++[(X, apply_delta_subst_typ (dsubst'0++dsubst') t2)]++dsubst') (open_tt_rec k X t1)); auto.
                  simpl_commut_subst in Typinge'. auto.
                  eapply m_typing_ovar_stronger; eauto using wfor_right_inv.
                  apply lenv_split_commute.
                    apply disjoint__lenv_split; auto.
                       apply uniq_from_wf_lenv in Hwfle. solve_uniq.
            SSSCase "sizeeq". auto.
            SSSCase "wft". 
            simpl in Hwft. apply wft_arrow_inv in Hwft. destruct Hwft; auto.
            simpl in Hwft'. apply wft_arrow_inv in Hwft'. destruct Hwft'; auto.
            SSSCase "fv". 
            assert (X `notin` fv_te u). eapply m_typing_onormalization_arrow_fv_stronger with (e:=e) (x:=x) (t1:=t1) (Env:=Env) (lEnv:=lEnv1); eauto using wfor_left_inv.
            assert (X `notin` fv_te u'). eapply m_typing_onormalization_arrow_fv_stronger with (e:=e') (x:=x') (t1:=t1) (Env:=Env) (lEnv:=lEnv1); eauto using wfor_right_inv.
            destruct_notin. auto.

  Case "typ_all". (* all *)
  assert (uniq (E'++[(X, bind_kn)]++E)) as Uniq.
    apply wf_delta_osubst__uniq in Hwfd.
    decompose [and] Hwfd; auto.
  apply F_Related_ovalues_all_leq in Hrel.
  apply F_Related_ovalues_all_req.  
  destruct Hrel as [Hv [Hv' [L' Hall]]]; subst.
  simpl_env in *.
  repeat(split; auto).
       SCase "all".  
         assert (forall X,
           X `notin` dom (E'++E) `union` fv_tt (open_tt_rec (S k) t2 t) ->
           wf_typ ([(X, bind_kn)]++E'++E) (open_tt (open_tt_rec (S k) t2 t) X)) as w'.
           simpl in Hwft'. 
           eapply wft_all_inv; eauto.
         assert (forall Y,
           Y `notin` dom (E'++[(X, bind_kn)]++E) `union` fv_tt (open_tt_rec (S k) X t) ->
           wf_typ ([(Y, bind_kn)]++E'++[(X, bind_kn)]++E) (open_tt (open_tt_rec (S k) X t) Y)) as w.
           simpl in Hwft. 
           eapply wft_all_inv; eauto.
         exists (L' `union` fv_env E `union` fv_env E' `union` dom E `union` dom E' `union` (fv_tt (open_tt_rec (S k) (typ_fvar X) t)) `union` singleton X  `union` (fv_tt t2) `union` dom Env `union` fv_env Env).
         intros X4 t3 t2' R0 Fr Hwfor' Hfv'.
         assert (X4 `notin` L') as Fr''. auto.
         destruct (@Hall X4 t3 t2' R0 Fr'') as [v [v' [Hnorm_vt2v [Hnorm_v't2'v' Hrel_wft]]]]; auto.
         exists (v). exists (v'). repeat (split; auto).
         assert (open_tt (open_tt_rec (S k) (typ_fvar X) t) X4 = open_tt_rec (S k) (typ_fvar X) (open_tt t X4)) as  G'. 
           unfold open_tt. unfold open_tt.
           destruct_notin.
           rewrite open_tt_rec_commute; auto.
         assert (open_tt (open_tt_rec (S k) t2 t) X4 = open_tt_rec (S k) t2 (open_tt t X4)) as G''.
           unfold open_tt. unfold open_tt.
           destruct_notin.
           rewrite open_tt_rec_commute; auto.
           eauto using type_from_wf_typ, notin_fv_tt_open_tt.
         assert (wf_typ ([(X4, bind_kn)]++E'++E) (open_tt_rec (S k)  t2 (open_tt t X4))) as WFT'. 
           rewrite <- G''.
           apply w' with (X:=X4); auto.
         assert (wf_typ ([(X4, bind_kn)]++E'++[(X,bind_kn)]++E) (open_tt_rec (S k)  X (open_tt t X4))) as WFT. 
           rewrite <- G'.
           apply w with (Y:=X4); auto.
         assert (wf_typ ([(X4, bind_kn)]++E'++E) t2) as WFT2'. 
           apply wf_rho_subst__uniq in Hwfor. decompose [and] Hwfor.
           eapply wf_typ_weaken_head; eauto.

         assert (typ_size (open_tt t X4) < typ_size (typ_all t)) as G. 
          simpl. rewrite open_tt_typ_size_eq. omega.
         apply H with (E:=E) (E':=[(X4, bind_kn)]++E') (t:=open_tt t X4)
                (rsubst:=rsubst) (dsubst:=dsubst) (dsubst':=dsubst')
                (X:=X) (R:=R) (t2:=t2) (k:=S k) (Env:=Env) (lEnv:=lEnv)
                (rsubst':=[(X4, R0)]++rsubst')
                (dsubst'0:=[(X4, t2')]++dsubst'0) (dsubst0:=[(X4, t3)]++dsubst0)
                (e:=v) (e':=v')
                in G; simpl_env; simpl;  auto.
         SSCase "all".
         destruct G as [Hrel_wft_wft' Hrel_wft'_wft].
         simpl_env. rewrite G''.
         apply Hrel_wft_wft'.
             SSSCase "all". simpl; simpl_env.
             assert (X4 `notin` fv_tt t2) as J. destruct_notin; auto.
             rewrite <- subst_tt_fresh; auto.
             rewrite <- subst_tt_fresh; auto.
             rewrite <- G'. auto.
             SSSCase "typing". simpl; simpl_env.
             apply preservation_normalization with (e:=exp_tapp e t3); auto.
               assert (type t3) as J.
                 apply wfor_left_inv in Hwfor'.
                 apply type_from_wf_typ in Hwfor'; auto.
               rewrite subst_tt_open_tt_rec; auto.
               rewrite <- subst_tt_fresh with (T:=t2); auto.
               unfold open_tt.
               rewrite subst_tt_open_tt_rec; auto.
               simpl. destruct (X4 == X4); subst; try solve [contradict n; auto].
               destruct (X == X4); subst.
                 destruct_notin. contradict NotInTac4; auto.

                 simpl_env.
                 simpl_commut_subst in Typinge.
                 assert (X4 `notin` fv_tt t) as JJ.
                   apply notin_fv_tt_open_tt_rec_inv with (Y:=X) (k:=S k); auto.
                 rewrite <- subst_tt_fresh with (T:=t); auto.
                 rewrite open_tt_rec_commute; auto.
                 rewrite commut_delta_osubst_open_tt_rec with (dE:=E'++[(X, bind_kn )]++E)(Env:=Env); auto.
                 rewrite delta_osubst_closed_typ with (t:=t3); auto.
                   apply typing_tapp with (T:=t3); eauto using wfor_left_inv.

                   clear J e0 n JJ Hrel_wft'_wft Hrel_wft_wft' H  Hall.
                   clear WFT WFT' WFT2' G' G'' Hrel_wft w' IHt Typinge Typinge' Hfv Fr.
                   split; intros x0 x0notin.
                     apply wfor_left_inv in Hwfor'.
                     apply in_fv_wf with (X:=x0) in Hwfor'; auto.
                     apply disjoint_delta_osubst in Hwfd.
                     destruct Hwfd as [J1 J2].
                     clear Hfv' Fr'' w Hwfd' J1 Uniq.
                     destruct_uniq. simpl_env.
                     clear x0notin Hwft Hwft' Hwft2 Hr_eq HwfoR Hwfor H1dsubst H1dsubst'  H1dsubst0  H1dsubst'0  H1rsubst  H1rsubst'.
                     solve_uniq.

                     apply wfor_left_inv in Hwfor'.
                     apply notin_fv_wf with (X:=x0) in Hwfor'; auto.
                     apply disjoint_delta_osubst in Hwfd.
                     destruct Hwfd as [J1 J2].
                     clear Hfv' Fr'' w Hwfd' J1 Uniq.
                     destruct_uniq. simpl_env in x0notin.
                     clear Hwft Hwft' Hwft2 Hr_eq HwfoR Hwfor H1dsubst H1dsubst'  H1dsubst0  H1dsubst'0  H1rsubst  H1rsubst'.
                     solve_uniq.
            SSSSCase "typing". simpl. simpl_env.
             apply preservation_normalization with (e:=exp_tapp e' t2'); auto.
               assert (type t2') as J.
                 apply wfor_right_inv in Hwfor'.
                 apply type_from_wf_typ in Hwfor'; auto.
               rewrite subst_tt_open_tt_rec; auto.
               rewrite <- subst_tt_fresh with (T:=t2); auto.
               unfold open_tt.
               rewrite subst_tt_open_tt_rec; auto.
               simpl. destruct (X4 == X4); subst; try solve [contradict n; auto].
               destruct (X == X4); subst.
                 destruct_notin. contradict NotInTac4; auto.

                 simpl_env.
                 simpl_commut_subst in Typinge'.
                 assert (X4 `notin` fv_tt t) as JJ.
                   apply notin_fv_tt_open_tt_rec_inv with (Y:=X) (k:=S k); auto.
                 rewrite <- subst_tt_fresh with (T:=t); auto.
                 rewrite open_tt_rec_commute; auto.
                 rewrite commut_delta_osubst_open_tt_rec with (dE:=E'++[(X, bind_kn)]++E)(Env:=Env); auto.
                 rewrite delta_osubst_closed_typ with (t:=t2'); auto.
                   apply typing_tapp with (T:=t2'); eauto using wfor_right_inv.

                   clear J e0 n JJ Hrel_wft'_wft Hrel_wft_wft' H  Hall.
                   clear WFT WFT' WFT2' G' G'' Hrel_wft w' IHt Typinge Typinge' Hfv Fr.
                   split; intros x0 x0notin.
                     apply wfor_right_inv in Hwfor'.
                     apply in_fv_wf with (X:=x0) in Hwfor'; auto.
                     apply disjoint_delta_osubst in Hwfd'.
                     destruct Hwfd' as [J1 J2].
                     clear Hfv' Fr'' w Hwfd J1 Uniq.
                     destruct_uniq. simpl_env.
                     clear x0notin Hwft Hwft' Hwft2 Hr_eq HwfoR Hwfor H1dsubst H1dsubst'  H1dsubst0  H1dsubst'0  H1rsubst  H1rsubst'.
                     solve_uniq.

                     apply wfor_right_inv in Hwfor'.
                     apply notin_fv_wf with (X:=x0) in Hwfor'; auto.
                     apply disjoint_delta_osubst in Hwfd'.
                     destruct Hwfd' as [J1 J2].
                     clear Hfv' Fr'' w Hwfd J1 Uniq.
                     destruct_uniq. simpl_env in x0notin.
                     clear Hwft Hwft' Hwft2 Hr_eq HwfoR Hwfor H1dsubst H1dsubst'  H1dsubst0  H1dsubst'0  H1rsubst  H1rsubst'.
                     solve_uniq.
             SSSCase "rsubst". simpl_env.
             apply rsubst_weaken_head; try solve [assumption | simpl_env; auto].
             SSSCase "dsubst". simpl. simpl_env.
             rewrite <- subst_tt_fresh; auto.          
             eapply odsubst_weaken_head; simpl_env; try solve [eauto using wfor_left_inv | fsetdec].
             SSSCase "dsubst'". simpl. simpl_env.
             rewrite <- subst_tt_fresh; auto.          
             eapply odsubst_weaken_head; simpl_env; try solve [eauto using wfor_right_inv | fsetdec].
         SSCase "F_FORel_R".
           unfold F_FORel__R in *. 
           destruct Hr_eq as [ HHwfd [ HHwfd' [ HHwfor Hrel_rel]]].
           repeat(split; simpl_env).
           apply wf_delta_osubst_styp; eauto using wfor_left_inv.
           apply wf_delta_osubst_styp; eauto using wfor_right_inv.
           apply wf_rho_subst_srel; auto.
           SSSCase "Rel -> R".
           intro Hrel.
             destruct (@Hrel_rel v0 v'0) as [Hrel_r Hr_rel].
             apply Hrel_r.
             unfold F_FORel in *.
             destruct Hrel as [lEnv' [Htypingv0 [Htypingv'0 Hrel]]].
             exists lEnv'.
             assert (X4 `notin` fv_lenv lEnv') as X4notinlEnv'.             
               assert (X4 `notin` dom Env `union` dom lEnv') as J.
                 assert (X4 `notin` dom lEnv').
                   apply ddom_ldoms_disjoint with (E:=[(X4, bind_kn)]); simpl; auto.
                 auto.
               apply typing_regular in Htypingv0.
               decompose [and] Htypingv0.
               apply wf_lenv_fv_lenv_sub in H2.
               clear Hfv Hall H IHt Fr Hfv' Fr'' H H1 H4 Htypingv0 Htypingv'0 Hrel Hrel_r Hr_rel Hrel_wft.
               fsetdec.
             unfold F_ORel in *.
             split.
               simpl in Htypingv0.
               rewrite <- subst_tt_fresh in Htypingv0; auto.
             split.
               simpl in Htypingv'0.
               rewrite <- subst_tt_fresh in Htypingv'0; auto.
             apply Forel_stronger with (E:=E'++E) (E':=@nil (atom*binding)) (X:=X4) (R:=R0) 
                            (rsubst:=rsubst'++rsubst) (rsubst':=rho_nil)
                            (dsubst:=dsubst0++dsubst) (dsubst0:=delta_nil)
                            (dsubst':=dsubst'0++dsubst') (dsubst'0:=delta_nil)
                            (t2:=t3) (t2':=t2'); simpl_env; simpl; auto.
                   eapply wfor_left_inv; eauto.
                   eapply wfor_right_inv; eauto.
                   SSSSCase "rsubst". simpl_env. apply rsubst_weaken_head; simpl_env; auto.
                   SSSSCase "dsubst". simpl_env. apply odsubst_weaken_head; simpl_env; eauto using wfor_left_inv.
                   SSSSCase "dsubst". simpl_env. apply odsubst_weaken_head; simpl_env; eauto using wfor_right_inv.
           SSSCase "R -> Rrel".
             intro Hr.
             destruct (@Hrel_rel v0 v'0) as [Hrel_r Hr_rel].
             unfold F_FORel in *.
             apply Hr_rel in Hr.
             destruct Hr as [lEnv' [Htypingv0 [Htypingv'0 Hr]]].
             exists lEnv'.
             assert (X4 `notin` fv_lenv lEnv') as X4notinlEnv'.
               assert (X4 `notin` dom Env `union` dom lEnv') as J.
                 assert (X4 `notin` dom lEnv').
                   apply ddom_ldoms_disjoint with (E:=[(X4, bind_kn)]); simpl; auto.
                 auto.
               apply typing_regular in Htypingv0.
               decompose [and] Htypingv0.
               apply wf_lenv_fv_lenv_sub in H2.
               clear Hfv Hall H IHt Fr Hfv' Fr'' H H1 H4 Htypingv0 Htypingv'0 Hrel_r Hr_rel Hrel_wft.
               fsetdec.
             unfold F_ORel in *.
             split.
               simpl. rewrite <- subst_tt_fresh; auto.
             split.
               simpl. rewrite <- subst_tt_fresh; auto.
             apply Forel_weaken_head with (E:=E'++E) (X:=X4) (R:=R0)
                            (rsubst:=rsubst'++rsubst) (dsubst:=dsubst0++dsubst) (dsubst':=dsubst'0++dsubst')
                            (t2:=t3) (t2':=t2'); simpl; simpl_env; auto.
               eapply wfor_left_inv; eauto.
               eapply wfor_right_inv; eauto.
       SSCase "fv".
        eapply m_all_ofv with (e:=e) (e':=e') (t3:=t3) (t2':=t2'); eauto using wfor_left_inv, wfor_right_inv.

  Case "typ_bang". (* bang *)
  apply F_Related_ovalues_bang_leq in Hrel.
  apply F_Related_ovalues_bang_req.  
  destruct Hrel as [Hv [Hv'[e1 [e1' [Heq [Heq' 
                                [u1 [u1' [Hnorm_e1u1 [Hnorm_e1'u1' Hrel_wft1]]]
                              ]]]]]]]; subst.
       simpl in Hfv.
       simpl_env in *.
       repeat(split; auto).
       SCase "bang".  
       simpl in Hwft. apply wft_bang_inv in Hwft.
       simpl in Hwft'. apply wft_bang_inv in Hwft'.
       exists (e1). exists (e1'). repeat(split; auto).
          exists (u1). exists (u1'). repeat(split; auto).
               assert (typ_size t < typ_size (typ_bang t)) as G1. simpl. omega.
               apply H with (E:=E) (E':=E') (e:=u1) (e':=u1') (t:=t) (Env:=Env) (lEnv:=lEnv)
                        (rsubst:=rsubst) (dsubst:=dsubst) (dsubst':=dsubst')
                        (X:=X) (R:=R) (t2:=t2) (k:=k) 
                        (rsubst':=rsubst') (dsubst0:=dsubst0) (dsubst'0:=dsubst'0) in G1; try solve [assumption].
                 destruct G1 as [Hrel_wft1_wft1' Hrel_wft1'_wft1].
                 simpl in Hrel_wft1_wft1'. apply Hrel_wft1_wft1'; auto.
                 SSSCase "typing". 
                 apply preservation_normalization with (e:=e1); auto.
                   simpl_commut_subst in Typinge.
                   inversion Typinge; subst. auto.
                 SSSCase "typing". 
                 apply preservation_normalization with (e:=e1'); auto.
                   simpl_commut_subst in Typinge'.
                   inversion Typinge'; subst. auto.
                 SSSCase "sizeeq".  auto.
                 SSSCase "fv". 
                 eapply m_with1_fv with (e1:=e1) (e1':=e1'); eauto.

  Case "typ_with". (* with *)
  apply F_Related_ovalues_with_leq in Hrel.
  apply F_Related_ovalues_with_req.  
  destruct Hrel as [Hv [Hv'[e1 [e2 [e1' [e2' [Heq [Heq' 
                                [[u1 [u1' [Hnorm_e1u1 [Hnorm_e1'u1' Hrel_wft1]]]] 
                                 [u2 [u2' [Hnorm_e2u2 [Hnorm_e2'u2' Hrel_wft2]]]]]
                              ]]]]]]]]; subst.
       simpl in Hfv.
       simpl_env in *.
       repeat(split; auto).
       SCase "with".  
       simpl in Hwft. apply wft_with_inv in Hwft. destruct Hwft; subst.
       simpl in Hwft'. apply wft_with_inv in Hwft'. destruct Hwft'; subst.
       exists (e1). exists (e2). exists (e1'). exists (e2'). repeat(split; auto).
          SSCase "with1".
          exists (u1). exists (u1'). repeat(split; auto).
               assert (typ_size t1 < typ_size (typ_with t1 t3)) as G1. simpl. omega.
               apply H with (E:=E) (E':=E') (e:=u1) (e':=u1') (t:=t1) (Env:=Env) (lEnv:=lEnv)
                        (rsubst:=rsubst) (dsubst:=dsubst) (dsubst':=dsubst')
                        (X:=X) (R:=R) (t2:=t2) (k:=k) 
                        (rsubst':=rsubst') (dsubst0:=dsubst0) (dsubst'0:=dsubst'0) in G1; try solve [assumption].
                 destruct G1 as [Hrel_wft1_wft1' Hrel_wft1'_wft1].
                 simpl in Hrel_wft1_wft1'. apply Hrel_wft1_wft1'; auto.
                 SSSCase "typing". 
                 apply preservation_normalization with (e:=e1); auto.
                   simpl_commut_subst in Typinge.
                   inversion Typinge; subst. auto.
                 SSSCase "typing". 
                 apply preservation_normalization with (e:=e1'); auto.
                   simpl_commut_subst in Typinge'.
                   inversion Typinge'; subst. auto.
                 SSSCase "sizeeq".  auto.
                 SSSCase "fv". 
                 eapply m_with1_fv with (e1:=e1) (e1':=e1'); eauto.
          SSCase "with2".
          exists (u2). exists (u2'). repeat(split; auto).
               assert (typ_size t3 < typ_size (typ_with t1 t3)) as G2. simpl. omega.
               assert (X `notin` (fv_env E `union` fv_env E' `union` fv_tt t3 `union` fv_te u2 `union` fv_te u2' `union` fv_env Env `union` fv_lenv lEnv)).
                 eapply m_with2_fv with (e2:=e2) (e2':=e2'); eauto.
               apply H with (E:=E) (E':=E') (e:=u2) (e':=u2') (t:=t3) (Env:=Env) (lEnv:=lEnv)
                        (rsubst:=rsubst) (dsubst:=dsubst) (dsubst':=dsubst')
                        (X:=X) (R:=R) (t2:=t2) (k:=k)  
                        (rsubst':=rsubst') (dsubst0:=dsubst0) (dsubst'0:=dsubst'0) in G2; try solve [assumption].
               destruct G2 as [Hrel_wft3_wft3' Hrel_wft3'_wft3].
               apply Hrel_wft3_wft3'; auto.
                 SSSCase "typing". 
                 apply preservation_normalization with (e:=e2); auto.
                   simpl_commut_subst in Typinge.
                   inversion Typinge; subst. auto.
                 SSSCase "typing". 
                 apply preservation_normalization with (e:=e2'); auto.
                   simpl_commut_subst in Typinge'.
                   inversion Typinge'; subst. auto.
                 SSSCase "sizeeq".  auto.
Qed.

Lemma _oparametricity_subst_value_right : forall n,
  (forall m, m<n -> P_oparametricity_subst_value m) ->
  forall  t E E' e e' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 Env lEnv X R t2 k,
  typ_size t = n ->  
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
  wfor Env R (apply_delta_subst_typ (dsubst0++dsubst) t2) (apply_delta_subst_typ (dsubst'0++dsubst') t2) ->
  (F_Related_ovalues (open_tt_rec k  t2 t) (rsubst'++rsubst) (dsubst0++dsubst) (dsubst'0++dsubst') e e' Env lEnv ->
  typing Env lEnv e (apply_delta_subst_typ (dsubst0++dsubst) (open_tt_rec k t2 t)) ->
  typing Env lEnv e' (apply_delta_subst_typ (dsubst'0++dsubst') (open_tt_rec k t2 t)) ->
  wf_rho_subst (E'++E) (rsubst'++rsubst) ->
  wf_delta_osubst (E'++E) (dsubst0++dsubst) Env -> 
  wf_delta_osubst (E'++E) (dsubst'0++dsubst') Env -> 
  F_Related_ovalues (open_tt_rec k (typ_fvar X) t) 
              (rsubst'++[(X, R)]++rsubst) 
              (dsubst0++[(X,(apply_delta_subst_typ (dsubst0++dsubst) t2))]++dsubst) 
              (dsubst'0++[(X,(apply_delta_subst_typ (dsubst'0++dsubst') t2))]++dsubst')
              e e' Env lEnv)
.
Proof.
  intros n H t E E' e e' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 Env lEnv X R t2 k
         Htsize Hwft Hwft' Hwft2 Hr_eq Hfv H1dsubst  H1dsubst'  H1dsubst0  H1dsubst'0  H1rsubst  H1rsubst' HwfoR.  
  unfold P_oparametricity_subst_value in *.
  intros Hrel Typinge Typinge' Hwfor Hwfd Hwfd'.
  (typ_cases (induction t) Case); simpl in Hrel; simpl; simpl_env in *.

  Case "typ_bvar". (* bvar *)
  simpl in Typinge, Typinge'.
  destruct (k==n0); subst.
    SCase "fvar".
    apply F_Related_ovalues_fvar_req.
    exists (R).
    assert (
      (F_FORel t2 (rsubst'++rsubst) (dsubst0++dsubst) (dsubst'0++dsubst') Env e e' -> R e e') *
      (R e e' -> F_FORel t2 (rsubst'++rsubst)  (dsubst0++dsubst) (dsubst'0++dsubst') Env e e')
      ) as HR'.
      unfold F_FORel__R in Hr_eq. decompose [and] Hr_eq; auto.
    destruct HR' as [Hrel_r Hr_rel].
    assert (F_FORel t2 (rsubst'++rsubst)  (dsubst0++dsubst) (dsubst'0++dsubst') Env e e') as XX.
      unfold F_FORel. exists lEnv. unfold F_ORel. 
      split; auto.
    apply Hrel_r in XX.
    apply F_Related_ovalues_inversion in Hrel.
    destruct Hrel as [Hv Hv'].
    repeat(split; auto).
      apply wfor_renaming_inv in HwfoR; auto.
    SCase "bvar".
    apply F_Related_ovalues_bvar_req; auto.

  Case "typ_fvar". (* fvar *)
  apply F_Related_ovalues_fvar_leq in Hrel; auto.
  apply F_Related_ovalues_fvar_req; auto.
  destruct Hrel as [R0 [Hb [Hv [Hv' Hr]]]]; subst; simpl.
  exists (R0).
  repeat(split; auto; simpl_env; auto).

  Case "typ_arrow". (* arrow *)
  apply F_Related_ovalues_arrow_leq in Hrel; auto.
  apply F_Related_ovalues_arrow_req; auto.
  destruct Hrel as [Hv [Hv' [L' Harrow]]]; subst.
  simpl in Hfv.
  simpl in Hwft. apply wft_arrow_inv in Hwft. destruct Hwft; auto.
  simpl in Hwft'. apply wft_arrow_inv in Hwft'. destruct Hwft'; auto.
  simpl_env in *.
  repeat(split; auto).
         SCase "arrorw".  
         exists (L' `union` {{X}}).
         intros lEnv1 x x' Htypingx Htypingx' Hwfle Disj Harrow'.
         destruct Harrow' as [v [v' [Hnorm_xv [Hnorm_x'v' Hrel_wft1]]]]; auto.
 
         assert (X `notin` fv_lenv lEnv1) as XnotinlEnv1.
           assert (X `notin` dom lEnv1) as J.
             destruct Disj as [J1 J2].
             apply J1; auto.
           apply typing_regular in Htypingx.
           decompose [and] Htypingx. clear Htypingx.
           apply wf_lenv_fv_lenv_sub in H6.
           clear H4 H5 H8 H Harrow H1dsubst H1dsubst' H1dsubst0 H1dsubst'0 H1rsubst H1rsubst'.
           destruct_notin.
           clear NotInTac NotInTac0 NotInTac2 NotInTac4 NotInTac5.
           assert (X `notin` dom Env) as J'.
             apply free_env__free_dom in NotInTac3; auto.
           fsetdec.
         assert (X `notin` fv_lenv (lEnv1++lEnv)) as XnotinlEnv.
           simpl_env. auto.

         destruct (@Harrow lEnv1 x x') as [u [u' [Hnorm_vxu [Hnorm_v'x'u' Hrel_wft1']]]]; auto.
           SSCase "typing". eapply m_typing_ovar_weaken; destruct_notin; eauto using wfor_left_inv.
           SSCase "typing". eapply m_typing_ovar_weaken; destruct_notin; eauto using wfor_right_inv.
           SSCase "Disj".
             destruct Disj as [J1 J2].
             split; intros x0 x0notin.
               apply J1; auto.
               apply J2 in x0notin; auto.           
           SSCase "arrow". 
           assert (typ_size t1 < typ_size (typ_arrow t1 t3)) as G1. simpl. omega.
           apply H with (E:=E) (E':=E') (e:=v) (e':=v') (t:=t1) (Env:=Env) (lEnv:=lEnv1)
                        (rsubst:=rsubst) (dsubst:=dsubst) (dsubst':=dsubst')
                        (X:=X) (R:=R) (t2:=t2) (k:=k) 
                        (rsubst':=rsubst') (dsubst0:=dsubst0) (dsubst'0:=dsubst'0) in G1; try solve [assumption].
              SSSCase "arrow_left". 
              destruct G1 as [Hrel_wft1_wft1' Hrel_wft1'_wft1].
              simpl in Hrel_wft1_wft1'. apply Hrel_wft1_wft1' in Hrel_wft1; auto.
               SSSSCase "arrow_left".
                 exists (v). exists (v'). split; auto.  
                 apply preservation_normalization with (e:=x); auto.
                 apply preservation_normalization with (e:=x'); auto.
                 simpl_env. eapply rsubst_weaken; eauto.
                 simpl_env. apply odsubst_weaken; try solve [assumption].
                                           apply wfor_left_inv in HwfoR; auto.
                                           destruct_notin. auto using free_env__free_dom.
                 simpl_env. apply odsubst_weaken; try solve [assumption].
                                           apply wfor_right_inv in HwfoR; auto.
                                           destruct_notin. auto using free_env__free_dom.
              SSSCase "sizeeq".  auto.
              SSSCase "fv". 
               assert (X `notin` fv_te v). 
                 eapply m_typing_onormalization_fv with (e:=x); eauto.
               assert (X `notin` fv_te v'). 
                 eapply m_typing_onormalization_fv with (e:=x'); eauto.
               destruct_notin. auto.
         SSCase "arrow_right". 
          exists (u). exists (u'). repeat(split; auto).
          assert (open_tt_rec k (typ_fvar X) t3 = open_tt_rec k (typ_fvar X) t3) as G'0. auto.
          assert (E'++[(X,bind_kn)]++E = E'++[(X,bind_kn)]++E) as G'1. auto.
          assert (F_FORel__R t2 (E'++E) (rsubst'++rsubst) (dsubst0++dsubst) (dsubst'0++dsubst') Env R) as HR. auto.
           assert (typ_size t3 < typ_size (typ_arrow t1 t3)) as G2. simpl. omega.
           apply H with (E:=E) (E':=E') (e:=u) (e':=u') (t:=t3) (Env:=Env) (lEnv:=lEnv1++lEnv)
                        (rsubst:=rsubst) (dsubst:=dsubst) (dsubst':=dsubst')
                        (X:=X) (R:=R) (t2:=t2) (k:=k) 
                        (rsubst':=rsubst') (dsubst0:=dsubst0) (dsubst'0:=dsubst'0) in G2; try solve [assumption].
           destruct G2 as [Hrel_wft2_wft2' Hrel_wft2'_wft2]; auto.
             apply Hrel_wft2'_wft2; auto.
              SSSSCase "typing".
              apply preservation_normalization with (e:=exp_app e x); auto.
                apply typing_app with (D1:=lEnv) (D2:=lEnv1) (T1:=apply_delta_subst_typ (dsubst0++[(X, apply_delta_subst_typ (dsubst0++dsubst) t2)]++dsubst) (open_tt_rec k X t1)); auto.
                  simpl in Typinge. simpl_commut_subst in Typinge. 
                  rewrite delta_osubst_opt with (dsubst':=dsubst0)(dsubst:=dsubst)(E:=E) (E':=E')(Env:=Env)(X:=X)(t:=apply_delta_subst_typ (dsubst0++dsubst) t2); try solve [assumption].
                    assert (X `notin` fv_tt t2) as J.
                      destruct_notin.      
                    apply notin_fv_wf with (X:=X) in Hwft2.
                      apply Hwft2.
                      simpl_env. auto using free_env__free_dom. 
                    rewrite swap_subst_tt_odsubst with (E:=E'++E)(Env:=Env); auto using free_env__free_dom.
                    simpl. 
                    destruct (X==X).
                      rewrite subst_tt_open_tt_rec; eauto using type_from_wf_typ.
                      simpl. 
                      destruct (X==X); auto.
                        rewrite <- subst_tt_fresh with (T:=t1); auto.
                        contradict n; auto.         
                      contradict n; auto.   
                   apply odsubst_weaken; try solve [assumption].
                     apply wft_osubst with (E:=E'++E); try solve [assumption].
                       auto using free_env__free_dom. 
                   auto using free_env__free_dom.
                   apply wft_osubst with (E:=E'++E); auto.
                  apply lenv_split_commute.
                    apply disjoint__lenv_split; auto.
                       apply uniq_from_wf_lenv in Hwfle. solve_uniq.
              SSSSCase "typing".
              apply preservation_normalization with (e:=exp_app e' x'); auto.
                apply typing_app with (D1:=lEnv) (D2:=lEnv1) (T1:=apply_delta_subst_typ (dsubst'0++[(X, apply_delta_subst_typ (dsubst'0++dsubst') t2)]++dsubst') (open_tt_rec k X t1)); auto.
                  simpl in Typinge'. simpl_commut_subst in Typinge'. 
                  rewrite delta_osubst_opt with (dsubst':=dsubst'0)(dsubst:=dsubst')(E:=E) (E':=E')(Env:=Env)(X:=X)(t:=apply_delta_subst_typ (dsubst'0++dsubst') t2); try solve [assumption].
                    assert (X `notin` fv_tt t2) as J.
                      destruct_notin.      
                    apply notin_fv_wf with (X:=X) in Hwft2.
                      apply Hwft2.
                      simpl_env. auto using free_env__free_dom. 
                    rewrite swap_subst_tt_odsubst with (E:=E'++E)(Env:=Env); auto using free_env__free_dom.
                    simpl. 
                    destruct (X==X).
                      rewrite subst_tt_open_tt_rec; eauto using type_from_wf_typ.
                      simpl. 
                      destruct (X==X); auto.
                        rewrite <- subst_tt_fresh with (T:=t1); auto.
                        contradict n; auto.         
                      contradict n; auto.   
                   apply odsubst_weaken; try solve [assumption].
                     apply wft_osubst with (E:=E'++E); try solve [assumption].
                       auto using free_env__free_dom. 
                   auto using free_env__free_dom.
                   apply wft_osubst with (E:=E'++E); auto.
                  apply lenv_split_commute.
                    apply disjoint__lenv_split; auto.
                       apply uniq_from_wf_lenv in Hwfle. solve_uniq.
             SSSCase "sizeeq".  auto.
             SSSCase "fv". 
             assert (X `notin` fv_te u). eapply m_typing_onormalization_arrow_fv_weaken with (e:=e) (x:=x) (t1:=t1) (Env:=Env) (lEnv:=lEnv1); eauto using wfor_left_inv.
             assert (X `notin` fv_te u'). eapply m_typing_onormalization_arrow_fv_weaken with (e:=e') (x:=x') (t1:=t1) (Env:=Env) (lEnv:=lEnv1); eauto using wfor_right_inv.
             destruct_notin. auto.

  Case "typ_all". (* all *)
  assert (uniq (E'++[(X, bind_kn)]++E)) as Uniq.
    apply wf_delta_osubst__uniq in Hwfd.
    decompose [and] Hwfd; auto.
    apply uniq_insert_mid; auto.
  apply F_Related_ovalues_all_leq in Hrel.
  apply F_Related_ovalues_all_req.  
  destruct Hrel as [Hv [Hv' [L' Hall]]]; subst.
  simpl_env in *; simpl in Hfv.
  repeat(split; auto).
       SCase "all".
         assert (forall X,
           X `notin` dom (E'++E) `union` fv_tt (open_tt_rec (S k) t2 t) ->
           wf_typ ([(X, bind_kn)]++E'++E) (open_tt (open_tt_rec (S k) t2 t) X)) as w'.
           simpl in Hwft'. 
           eapply wft_all_inv; eauto.
         assert (forall Y,
           Y `notin` dom (E'++[(X, bind_kn)]++E) `union` fv_tt (open_tt_rec (S k) X t) ->
           wf_typ ([(Y, bind_kn)]++E'++[(X, bind_kn)]++E) (open_tt (open_tt_rec (S k) X t) Y)) as w.
           simpl in Hwft. 
           eapply wft_all_inv; eauto.
         exists (L'   `union` fv_env E  `union` fv_env E' `union` dom E  `union` dom E' `union` (fv_tt (open_tt_rec (S k) t2 t)) `union` singleton X `union` (fv_tt t2) `union` dom Env `union` fv_env Env).
         intros X2 t3 t2' R0 Fr Hwfor' Hfv'.
         assert (X2 `notin` L') as Fr''. auto.
         destruct (@Hall X2 t3 t2' R0 Fr'') as [v [v' [Hnorm_vt2v [Hnorm_v't2'v' Hrel_wft]]]]; auto.
         exists (v). exists (v'). repeat(split; auto).
         assert (open_tt (open_tt_rec (S k) (typ_fvar X) t) X2 = open_tt_rec (S k) (typ_fvar X) (open_tt t X2)) as  G'. 
           unfold open_tt. unfold open_tt.
           destruct_notin. rewrite open_tt_rec_commute; auto.
         assert (open_tt (open_tt_rec (S k) t2 t) X2 = open_tt_rec (S k) t2 (open_tt t X2)) as G''.
           unfold open_tt. unfold open_tt.
           destruct_notin. rewrite open_tt_rec_commute; eauto.
             eauto using type_from_wf_typ, notin_fv_tt_open_tt.
         assert (wf_typ ([(X2, bind_kn)]++E'++E) (open_tt_rec (S k)  t2 (open_tt t X2))) as WFT'. 
           rewrite <- G''.
           apply w' with (X:=X2).
           auto.
         assert (wf_typ ([(X2, bind_kn)]++E'++[(X,bind_kn)]++E) (open_tt_rec (S k) X (open_tt t X2))) as WFT. 
           rewrite <- G'.
           apply w with (Y:=X2).
           auto.
         assert (wf_typ ([(X2, bind_kn)]++E'++E) t2) as WFT2'. 
           apply wf_rho_subst__uniq in Hwfor. decompose [and] Hwfor.
           apply wf_typ_weaken_head; try solve [assumption].
             apply uniq_push; try solve [assumption]. 
               destruct_notin. clear NotInTac  NotInTac0  NotInTac1  NotInTac4  NotInTac5  NotInTac6  NotInTac7  NotInTac8  NotInTac9  NotInTac10  NotInTac11  NotInTac12  NotInTac13  NotInTac14  NotInTac15.
               rewrite dom_app. auto.
         assert (typ_size (open_tt t X2) < typ_size (typ_all t)) as G. 
          simpl. rewrite open_tt_typ_size_eq. omega.
         apply H with (E:=E) (E':=[(X2, bind_kn )]++E') (t:=open_tt t X2)
                (rsubst:=rsubst) (dsubst:=dsubst) (dsubst':=dsubst')
                (X:=X) (R:=R) (t2:=t2) (k:=S k)
                (rsubst':=[(X2, R0)]++rsubst') (Env:=Env) (lEnv:=lEnv)
                (dsubst'0:=[(X2, t2')]++dsubst'0) (dsubst0:=[(X2, t3)]++dsubst0)
                (e:=v) (e':=v') 
                in G; simpl_env; simpl; auto.  
         SSCase "all".
           destruct G as [Hrel_wft_wft' Hrel_wft'_wft].
           simpl in Hrel_wft'_wft.
           rewrite <- subst_tt_fresh with (T:=t2) (U:=t3) in Hrel_wft'_wft; auto.
           rewrite <- subst_tt_fresh with (T:=t2) (U:=t2') in Hrel_wft'_wft; auto.
           rewrite G'.
           apply Hrel_wft'_wft; simpl_env.
              SSSCase "all". rewrite <- G''. auto.
              SSSCase "typing".
              apply preservation_normalization with (e:=exp_tapp e t3); auto.
               assert (type t3) as J.
                 apply wfor_left_inv in Hwfor'.
                 apply type_from_wf_typ in Hwfor'; auto.
               rewrite subst_tt_open_tt_rec; auto.
               rewrite <- subst_tt_fresh with (T:=t2); auto.
               unfold open_tt.
               rewrite subst_tt_open_tt_rec; auto.
               simpl. destruct (X2 == X2); subst; try solve [contradict n; auto].
               destruct (X == X2); subst.
                 destruct_notin. contradict NotInTac5; auto.

                 simpl in Typinge.
                 simpl_commut_subst in Typinge.
                 assert (X2 `notin` fv_tt t) as JJ.
                   apply notin_fv_tt_open_tt_rec_inv with (Y:=X) (k:=S k); auto.
                 rewrite <- subst_tt_fresh with (T:=t); auto.
                 assert (type t2) as J'.
                   apply type_from_wf_typ in Hwft2; auto.
                 rewrite open_tt_rec_commute'; auto.
                 rewrite commut_delta_osubst_open_tt_rec with (dE:=E'++E)(Env:=Env); auto.
                  rewrite delta_osubst_closed_typ with (t:=t3); auto.
                   apply typing_tapp with (T:=t3); eauto using wfor_left_inv.

                   clear J e0 n JJ Hrel_wft'_wft Hrel_wft_wft' H  Hall.
                   clear WFT WFT' WFT2' G' G'' Hrel_wft w' IHt Typinge Typinge' Hfv Fr.
                   split; intros x0 x0notin.
                     apply wfor_left_inv in Hwfor'.
                     apply in_fv_wf with (X:=x0) in Hwfor'; auto.
                     apply disjoint_delta_osubst in Hwfd.
                     destruct Hwfd as [J1 J2].
                     clear Hfv' Fr'' w Hwfd' J1 Uniq.
                     destruct_uniq. simpl_env.
                     clear x0notin Hwft Hwft' Hwft2 Hr_eq HwfoR Hwfor H1dsubst H1dsubst'  H1dsubst0  H1dsubst'0  H1rsubst  H1rsubst'.
                     solve_uniq.

                     apply wfor_left_inv in Hwfor'.
                     apply notin_fv_wf with (X:=x0) in Hwfor'; auto.
                     apply disjoint_delta_osubst in Hwfd.
                     destruct Hwfd as [J1 J2].
                     clear Hfv' Fr'' w Hwfd' J1 Uniq.
                     destruct_uniq. simpl_env in x0notin.
                     clear Hwft Hwft' Hwft2 Hr_eq HwfoR Hwfor H1dsubst H1dsubst'  H1dsubst0  H1dsubst'0  H1rsubst  H1rsubst'.
                     solve_uniq.
              SSSCase "typing".
              apply preservation_normalization with (e:=exp_tapp e' t2'); auto.
               assert (type t2') as J.
                 apply wfor_right_inv in Hwfor'.
                 apply type_from_wf_typ in Hwfor'; auto.
               rewrite subst_tt_open_tt_rec; auto.
               rewrite <- subst_tt_fresh with (T:=t2); auto.
               unfold open_tt.
               rewrite subst_tt_open_tt_rec; auto.
               simpl. destruct (X2 == X2); subst; try solve [contradict n; auto].
               destruct (X == X2); subst.
                 destruct_notin. contradict NotInTac5; auto.

                 simpl in Typinge'.
                 simpl_commut_subst in Typinge'.
                 assert (X2 `notin` fv_tt t) as JJ.
                   apply notin_fv_tt_open_tt_rec_inv with (Y:=X) (k:=S k); auto.
                 rewrite <- subst_tt_fresh with (T:=t); auto.
                 assert (type t2) as J'.
                   apply type_from_wf_typ in Hwft2; auto.
                 rewrite open_tt_rec_commute'; auto.
                 rewrite commut_delta_osubst_open_tt_rec with (dE:=E'++E)(Env:=Env); auto.
                  rewrite delta_osubst_closed_typ with (t:=t2'); auto.
                   apply typing_tapp with (T:=t2'); eauto using wfor_right_inv.

                   clear J e0 n JJ Hrel_wft'_wft Hrel_wft_wft' H  Hall.
                   clear WFT WFT' WFT2' G' G'' Hrel_wft w' IHt Typinge Typinge' Hfv Fr.
                   split; intros x0 x0notin.
                     apply wfor_right_inv in Hwfor'.
                     apply in_fv_wf with (X:=x0) in Hwfor'; try solve [assumption]. 
                     apply disjoint_delta_osubst in Hwfd'.
                     destruct Hwfd' as [J1 J2].
                     clear Fr'' w Hwfd J1 Uniq.
                     destruct_uniq. simpl_env.
                     clear x0notin Hwft Hwft' Hwft2 Hr_eq HwfoR Hwfor H1dsubst H1dsubst'  H1dsubst0  H1dsubst'0  H1rsubst  H1rsubst'.
                     solve_uniq.

                     apply wfor_right_inv in Hwfor'.
                     apply notin_fv_wf with (X:=x0) in Hwfor'; try solve [assumption].                     
                     apply disjoint_delta_osubst in Hwfd'.
                     destruct Hwfd' as [J1 J2].
                     clear Hfv' Fr'' w Hwfd J1 Uniq.
                     destruct_uniq. simpl_env in x0notin.
                     clear Hwft Hwft' Hwft2 Hr_eq HwfoR Hwfor H1dsubst H1dsubst'  H1dsubst0  H1dsubst'0  H1rsubst  H1rsubst'.
                     solve_uniq.
              SSSCase "rsubst". apply rsubst_weaken_head; simpl_env; auto.
              SSSCase "dsubst". apply odsubst_weaken_head; simpl_env; eauto using wfor_left_inv.
              SSSCase "dsubst'". apply odsubst_weaken_head; simpl_env; eauto using wfor_right_inv.
         SSCase "F_FORel".
         unfold F_FORel__R in *. destruct Hr_eq as [ HHwfd [ HHwfd' [ HHwfor Hrel_rel]]].
           repeat(split; simpl_env).
           apply wf_delta_osubst_styp; eauto using wfor_left_inv.
           apply wf_delta_osubst_styp; eauto using wfor_right_inv.
           apply wf_rho_subst_srel; auto.
           SSSCase "Rel -> R".
           intro Hrel.
             destruct (@Hrel_rel v0 v'0) as [Hrel_r Hr_rel].
             apply Hrel_r.
             unfold F_FORel in *.
             destruct Hrel as [lEnv' [Htypingv0 [Htypingv'0 Hrel]]].
             exists lEnv'.
             assert (X2 `notin` fv_lenv lEnv') as X2notinlEnv'.
               assert (X2 `notin` dom Env `union` dom lEnv') as J.
                 assert (X2 `notin` dom lEnv').
                   apply ddom_ldoms_disjoint with (E:=[(X2, bind_kn)]); simpl; auto.
                 auto.
               apply typing_regular in Htypingv0.
               decompose [and] Htypingv0.
               apply wf_lenv_fv_lenv_sub in H2.
               clear Hfv Hall H IHt Fr Hfv' Fr'' H H1 H4 Htypingv0 Htypingv'0 Hrel Hrel_r Hr_rel Hrel_wft.
               fsetdec.
             unfold F_ORel in *.
             split.
               simpl in Htypingv0.
               rewrite <- subst_tt_fresh in Htypingv0; auto.
             split.
               simpl in Htypingv'0.
               rewrite <- subst_tt_fresh in Htypingv'0; auto.
             apply Forel_stronger with (E:=E'++E) (E':=@nil (atom*binding)) (X:=X2) (R:=R0) 
                            (rsubst:=rsubst'++rsubst) (rsubst':=rho_nil)
                            (dsubst:=dsubst0++dsubst) (dsubst0:=delta_nil)
                            (dsubst':=dsubst'0++dsubst') (dsubst'0:=delta_nil)
                            (t2:=t3) (t2':=t2'); simpl; simpl_env; auto.
                   eapply wfor_left_inv; eauto.
                   eapply wfor_right_inv; eauto.
                   SSSSCase "dsubst". apply odsubst_weaken_head; simpl_env; eauto using wfor_left_inv.
                   SSSSCase "dsubst'". apply odsubst_weaken_head; simpl_env; eauto using wfor_right_inv.               
           SSSCase "R -> Rrel".
             intro Hr.
             destruct (@Hrel_rel v0 v'0) as [Hrel_r Hr_rel].
             unfold F_FORel in *.
             apply Hr_rel in Hr.
             destruct Hr as [lEnv' [Htypingv0 [Htypingv'0 Hr]]].
             exists lEnv'.
             assert (X2 `notin` fv_lenv lEnv') as X2notinlEnv'.
               assert (X2 `notin` dom Env `union` dom lEnv') as J.
                 assert (X2 `notin` dom lEnv').
                   apply ddom_ldoms_disjoint with (E:=[(X2, bind_kn)]); simpl; auto.
                 auto.
               apply typing_regular in Htypingv0.
               decompose [and] Htypingv0.
               apply wf_lenv_fv_lenv_sub in H2.
               clear Hfv Hall H IHt Fr Hfv' Fr'' H H1 H4 Htypingv0 Htypingv'0 Hrel_r Hr_rel Hrel_wft.
               fsetdec.
             unfold F_ORel in *.
             split.
               simpl. rewrite <- subst_tt_fresh; auto.
             split.
               simpl. rewrite <- subst_tt_fresh; auto.
             apply Forel_weaken_head with (E:=E'++E) (X:=X2) (R:=R0) 
                            (rsubst:=rsubst'++rsubst)
                            (dsubst:=dsubst0++dsubst)
                            (dsubst':=dsubst'0++dsubst')
                            (t2:=t3) (t2':=t2'); simpl_env; auto.
                eapply wfor_left_inv; eauto.
                eapply wfor_right_inv; eauto.
         SSCase "fv".
         eapply m_all_ofv with (e:=e) (e':=e') (t3:=t3) (t2':=t2'); eauto using wfor_left_inv, wfor_right_inv.

  Case "typ_bang". (* bang *)
  apply F_Related_ovalues_bang_leq in Hrel.
  apply F_Related_ovalues_bang_req.  
  destruct Hrel as [Hv [Hv' [e1 [e1' [Heq [Heq' 
                                [u1 [u1' [Hnorm_e1u1 [Hnorm_e1'u1' Hrel_wft1]]]
                              ]]]]]]]; subst.
       simpl in Hfv.
       simpl in Hwft. apply wft_bang_inv in Hwft. 
       simpl in Hwft'. apply wft_bang_inv in Hwft'. 
       simpl_env in *.
       repeat(split; auto).
       SCase "bang".
       exists (e1). exists (e1'). repeat(split; auto).
         SSCase "with1".
         exists (u1). exists (u1'). repeat(split; auto).
         assert (typ_size t < typ_size (typ_bang t)) as G1. simpl. omega.
         apply H with (E:=E) (E':=E') (e:=u1) (e':=u1') (t:=t) (Env:=Env) (lEnv:=lEnv)
                        (rsubst:=rsubst) (dsubst:=dsubst) (dsubst':=dsubst')
                        (X:=X) (R:=R) (t2:=t2) (k:=k) 
                        (rsubst':=rsubst') (dsubst0:=dsubst0) (dsubst'0:=dsubst'0) in G1; try solve [assumption].
                 destruct G1 as [Hrel_wft1_wft1' Hrel_wft1'_wft1].
                 simpl in Hrel_wft1'_wft1. apply Hrel_wft1'_wft1; auto.
                 SSSCase "typing". 
                 apply preservation_normalization with (e:=e1); auto.
                   simpl in Typinge.
                   simpl_commut_subst in Typinge.
                   inversion Typinge; subst. auto.
                 SSSCase "typing". 
                 apply preservation_normalization with (e:=e1'); auto.
                   simpl in Typinge'.
                   simpl_commut_subst in Typinge'.
                   inversion Typinge'; subst. auto.
                 SSSCase "sizeeq".  auto.
                 SSSCase "fv". 
                 eapply m_with1_fv with (e1:=e1) (e1':=e1'); eauto.

  Case "typ_with". (* with *)
  apply F_Related_ovalues_with_leq in Hrel.
  apply F_Related_ovalues_with_req.  
  destruct Hrel as [Hv [Hv' [e1 [e2 [e1' [e2' [Heq [Heq' 
                                [[u1 [u1' [Hnorm_e1u1 [Hnorm_e1'u1' Hrel_wft1]]]] 
                                 [u2 [u2' [Hnorm_e2u2 [Hnorm_e2'u2' Hrel_wft2]]]]]
                              ]]]]]]]]; subst.
       simpl in Hfv.
       simpl in Hwft. apply wft_with_inv in Hwft. destruct Hwft; subst.
       simpl in Hwft'. apply wft_with_inv in Hwft'. destruct Hwft'; subst.
       simpl_env in *.
       repeat(split; auto).
       SCase "with".
       exists (e1). exists (e2). exists (e1'). exists (e2'). repeat(split; auto).
         SSCase "with1".
         exists (u1). exists (u1'). repeat(split; auto).
         assert (typ_size t1 < typ_size (typ_with t1 t3)) as G1. simpl. omega.
         apply H with (E:=E) (E':=E') (e:=u1) (e':=u1') (t:=t1) (Env:=Env) (lEnv:=lEnv)
                        (rsubst:=rsubst) (dsubst:=dsubst) (dsubst':=dsubst')
                        (X:=X) (R:=R) (t2:=t2) (k:=k) 
                        (rsubst':=rsubst') (dsubst0:=dsubst0) (dsubst'0:=dsubst'0) in G1; try solve [assumption].
                 destruct G1 as [Hrel_wft1_wft1' Hrel_wft1'_wft1].
                 simpl in Hrel_wft1'_wft1. apply Hrel_wft1'_wft1; auto.
                 SSSCase "typing". 
                 apply preservation_normalization with (e:=e1); auto.
                   simpl in Typinge.
                   simpl_commut_subst in Typinge.
                   inversion Typinge; subst. auto.
                 SSSCase "typing". 
                 apply preservation_normalization with (e:=e1'); auto.
                   simpl in Typinge'.
                   simpl_commut_subst in Typinge'.
                   inversion Typinge'; subst. auto.
                 SSSCase "sizeeq".  auto.
                 SSSCase "fv". 
                 eapply m_with1_fv with (e1:=e1) (e1':=e1'); eauto.
         SSCase "with2".
         exists (u2). exists (u2'). repeat(split; auto).
         assert (X `notin` (fv_env E `union` fv_env E' `union` fv_tt t3 `union` fv_te u2 `union` fv_te u2' `union` fv_env Env `union` fv_lenv lEnv)).
            eapply m_with2_fv with (e2:=e2) (e2':=e2'); eauto.
         assert (typ_size t3 < typ_size (typ_with t1 t3)) as G2. simpl. omega.
         apply H with (E:=E) (E':=E') (e:=u2) (e':=u2') (t:=t3) (Env:=Env) (lEnv:=lEnv)
                        (rsubst:=rsubst) (dsubst:=dsubst) (dsubst':=dsubst')
                        (X:=X) (R:=R) (t2:=t2) (k:=k)
                        (rsubst':=rsubst') (dsubst0:=dsubst0) (dsubst'0:=dsubst'0) in G2; try solve [assumption].
         destruct G2 as [Hrel_wft3_wft3' Hrel_wft3'_wft3].
         apply Hrel_wft3'_wft3; auto.
           SSSCase "typing". 
             apply preservation_normalization with (e:=e2); auto.
               simpl in Typinge.
               simpl_commut_subst in Typinge.
               inversion Typinge; subst. auto.
           SSSCase "typing". 
             apply preservation_normalization with (e:=e2'); auto.
               simpl in Typinge'.
               simpl_commut_subst in Typinge'.
               inversion Typinge'; subst. auto.
           SSSCase "sizeeq".  auto.
Qed.

Lemma _oparametricity_subst_value :  forall n, P_oparametricity_subst_value n.
Proof.
  intro n.
  apply lt_wf_ind. clear n.
  intros n H.
  unfold P_oparametricity_subst_value.
  intros t E E' e e' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 Env lEnv X R t2 k
         Htsize Hwft Hwft' Hwft2 Hr_eq Hfv H1dsubst  H1dsubst'  H1dsubst0  H1dsubst'0 H1rsubst  H1rsubst'.  
  assert (wfor Env R (apply_delta_subst_typ (dsubst0++dsubst) t2) (apply_delta_subst_typ (dsubst'0++dsubst') t2)) as HwfoR. 
    eapply F_FORel__R__wfor; eauto.
  split.
    apply _oparametricity_subst_value_left with (n:=n); auto.
    apply _oparametricity_subst_value_right with (n:=n); auto.
Qed.

Lemma oparametricity_subst_value : forall t E E' e e' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 Env lEnv X R t2 k,
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
Proof.
  intros t E E' e e' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 Env lEnv X R t2 k
        Hwft' Hwft Hwft2 Hrel_eq Hfv Hdsubst Hdsubst' Hdsubst0 Hdsubst'0 Hrsubst Hrsubst'.
  assert (P_oparametricity_subst_value (typ_size t)).
    apply (@_oparametricity_subst_value (typ_size t)).
  unfold P_oparametricity_subst_value in H.
  assert (typ_size t = typ_size t) as Htsize. auto.
  decompose [prod] (@H t E E' e e' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 Env lEnv X R t2 k
                     Htsize Hwft' Hwft Hwft2 Hrel_eq Hfv Hdsubst Hdsubst' Hdsubst0 Hdsubst'0 Hrsubst Hrsubst').
  eapply a; eauto.
Qed.

(*******************************************************************************)
(** F_Related_osubst_split *)

Lemma F_Related_osubst_split: forall E lE lE1 lE2 dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
   F_Related_osubst E lE gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
   lenv_split E lE1 lE2 lE ->
   exists lgsubst1, exists lgsubst1', exists lgsubst2, exists lgsubst2', exists lEnv1, exists lEnv2,
     lgamma_osubst_split E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst Env lEnv1 lEnv2 lEnv /\
     lgamma_osubst_split E lE dsubst' gsubst' lgsubst1' lgsubst2' lgsubst' Env lEnv1 lEnv2 lEnv  /\
     F_Related_osubst E lE1 gsubst gsubst' lgsubst1 lgsubst1' rsubst dsubst dsubst' Env lEnv1 /\     
     F_Related_osubst E lE2 gsubst gsubst' lgsubst2 lgsubst2' rsubst dsubst dsubst' Env lEnv2.
Proof.
  intros E lE lE1 lE2 dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv Hrel_subst Hsplit.
  generalize dependent lE1. generalize dependent lE2.
  (F_Related_osubst_cases (induction Hrel_subst) Case); intros.
  Case "F_Related_osubst_empty".
    exists gamma_nil. exists gamma_nil. exists gamma_nil. exists gamma_nil. exists lempty. exists lempty.
    inversion Hsplit; subst.
    repeat (split; auto).
  Case "F_Related_osubst_kind".
    assert (J:=Hsplit).
    apply lenv_split_strengthening_typ_tail in Hsplit; auto.
    apply IHHrel_subst in Hsplit. clear IHHrel_subst.
    destruct Hsplit as [lgsubst1 [lgsubst1' [lgsubst2 [lgsubst2'[lEnv1 [lEnv2 [J1 [J2 [J3 J4]]]]]]]]].
    exists lgsubst1. exists lgsubst1'. exists lgsubst2. exists lgsubst2'. exists lEnv1. exists lEnv2.
    split.
      apply lgamma_osubst_split_nonlin_weakening_typ_tail; auto.
        apply wf_lgamma_osubst_skind; eauto using wfor_left_inv.
          apply lgamma_osubst_split__wf_lgamma_osubst in J1; auto.
          auto using free_env__free_dom.
    split.
      apply lgamma_osubst_split_nonlin_weakening_typ_tail; auto.
        apply wf_lgamma_osubst_skind; eauto using wfor_right_inv.
          apply lgamma_osubst_split__wf_lgamma_osubst in J2; auto.
          auto using free_env__free_dom.
    split.
      apply F_Related_osubst_kind; auto.
        apply fv_lenv_split in J. rewrite J in H. 
        apply lgamma_osubst_split__lenv_split in J1.
        apply fv_lenv_split in J1. rewrite J1 in H. 
        auto.
      apply F_Related_osubst_kind; auto.
        apply fv_lenv_split in J. rewrite J in H.
        apply lgamma_osubst_split__lenv_split in J1.
        apply fv_lenv_split in J1. rewrite J1 in H. 
        auto.
  Case "F_Related_osubst_typ".
    assert (J:=Hsplit).
    apply lenv_split_strengthening_tail in Hsplit; auto.
    apply IHHrel_subst in Hsplit. clear IHHrel_subst.
    destruct Hsplit as [lgsubst1 [lgsubst1' [lgsubst2 [lgsubst2' [lEnv1 [lEnv2 [J1 [J2 [J3 J4]]]]]]]]].
    exists lgsubst1. exists lgsubst1'. exists lgsubst2. exists lgsubst2'. exists lEnv1. exists lEnv2.
    split.
      apply lgamma_osubst_split_nonlin_weakening_tail; auto.
        apply wf_lgamma_osubst_sval; auto.
          apply lgamma_osubst_split__wf_lgamma_osubst in J1; auto.
    split.
      apply lgamma_osubst_split_nonlin_weakening_tail; auto.
        apply wf_lgamma_osubst_sval; auto.
          apply lgamma_osubst_split__wf_lgamma_osubst in J2; auto.
    split.
      apply F_Related_osubst_typ; auto.
        apply fv_lenv_split in J. rewrite J in H2.
        apply lgamma_osubst_split__lenv_split in J1.
        apply fv_lenv_split in J1. rewrite J1 in H2. 
        auto.
      apply F_Related_osubst_typ; auto.
        apply fv_lenv_split in J. rewrite J in H2.
        apply lgamma_osubst_split__lenv_split in J1.
        apply fv_lenv_split in J1. rewrite J1 in H2. 
        auto.
  Case "F_Related_osubst_ltyp".
    inversion Hsplit; subst.
    SCase "lenv_split_left".
      destruct H1 as [JJ1 JJ2].
      assert (J:=H9).
      apply IHHrel_subst in H9. clear IHHrel_subst.
      destruct H9 as [lgsubst1 [lgsubst1' [lgsubst2 [lgsubst2' [lEnv1' [lEnv2' [J1 [J2 [J3 J4]]]]]]]]].
      exists ([(x,e)]++lgsubst1). exists ([(x,e')]++lgsubst1'). exists lgsubst2. exists lgsubst2'. 
      exists (lEnv2 ++ lEnv1'). exists lEnv2'.

      assert (JJ:=J1). 
      apply lgamma_osubst_split__lenv_split in JJ.
      apply fv_lenv_split in JJ. 
      rewrite JJ in H4. clear JJ.

      split.
        apply lgamma_osubst_split_left with (lEnv1:=lEnv1') (lEnv1':=lEnv2) (lEnv3:=lEnv1); auto.
          apply lgamma_osubst_split__lenv_split in J1.
          apply dom_lenv_split in J1. rewrite J1.
          auto using free_env__free_dom, free_lenv__free_dom.

          split; auto.
          split; auto.
            assert (disjoint lEnv2 lEnv1) as Disj1.
              apply uniq_from_wf_lenv in H2.
              solve_uniq.
            apply disjoint_sub with (D1:=lEnv1); auto.
              apply lgamma_osubst_split__lenv_split in J1.
              apply dom_lenv_split in J1. 
              rewrite J1. apply dom_sub_right.

          apply wf_lenv_merge; auto.
            apply lgamma_osubst_split__lenv_split in J1.
            apply wf_lenv_split_left in J1; auto.

            assert (disjoint lEnv2 lEnv1) as Disj1.
              apply uniq_from_wf_lenv in H2.
              solve_uniq.
            apply disjoint_sym_1.
            apply disjoint_sub with (D1:=lEnv1); auto.
              apply lgamma_osubst_split__lenv_split in J1.
              apply dom_lenv_split in J1. 
              rewrite J1. apply dom_sub_left.
      split.
        apply lgamma_osubst_split_left with (lEnv1:=lEnv1') (lEnv1':=lEnv2) (lEnv3:=lEnv1); auto.
          apply lgamma_osubst_split__lenv_split in J1.
          apply dom_lenv_split in J1. rewrite J1.
          auto using free_env__free_dom, free_lenv__free_dom.

          split; auto.
          split; auto.
            assert (disjoint lEnv2 lEnv1) as Disj1.
              apply uniq_from_wf_lenv in H2.
              solve_uniq.
            apply disjoint_sub with (D1:=lEnv1); auto.
              apply lgamma_osubst_split__lenv_split in J1.
              apply dom_lenv_split in J1. 
              rewrite J1. apply dom_sub_right.

          apply wf_lenv_merge; auto.
            apply lgamma_osubst_split__lenv_split in J1.
            apply wf_lenv_split_left in J1; auto.

            assert (disjoint lEnv2 lEnv1) as Disj1.
              apply uniq_from_wf_lenv in H2.
              solve_uniq.
            apply disjoint_sym_1.
            apply disjoint_sub with (D1:=lEnv1); auto.
              apply lgamma_osubst_split__lenv_split in J1.
              apply dom_lenv_split in J1. 
              rewrite J1. apply dom_sub_left.
      split; auto.
        apply F_Related_osubst_ltyp with (lEnv1:=lEnv1') (lEnv2:=lEnv2); auto.
          split; auto.
            apply disjoint_sub with (D1:=lE); auto.
              apply dom_lenv_split in J.
              rewrite J. apply dom_sub_left.

          apply wf_lenv_merge; auto.
            apply lgamma_osubst_split__lenv_split in J1.
            apply wf_lenv_split_left in J1; auto.

            assert (disjoint lEnv2 lEnv1) as Disj1.
              apply uniq_from_wf_lenv in H2.
              solve_uniq.
            apply disjoint_sym_1.
            apply disjoint_sub with (D1:=lEnv1); auto.
              apply lgamma_osubst_split__lenv_split in J1.
              apply dom_lenv_split in J1. 
              rewrite J1. apply dom_sub_left.
 
          simpl_env.
          apply fv_lenv_split in J.
          rewrite J in H4.
          auto.
    SCase "lenv_split_right".
      destruct H1 as [JJ1 JJ2].
      assert (J:=H9).
      apply IHHrel_subst in H9. clear IHHrel_subst.
      destruct H9 as [lgsubst1 [lgsubst1' [lgsubst2 [lgsubst2' [lEnv1' [lEnv2' [J1 [J2 [J3 J4]]]]]]]]].
      exists lgsubst1. exists lgsubst1'. exists ([(x,e)]++lgsubst2). exists ([(x,e')]++lgsubst2').
      exists lEnv1'. exists (lEnv2 ++ lEnv2').

      assert (JJ:=J1). 
      apply lgamma_osubst_split__lenv_split in JJ.
      apply fv_lenv_split in JJ. 
      rewrite JJ in H4. clear JJ.

      split.
        apply lgamma_osubst_split_right with (lEnv2:=lEnv2') (lEnv2':=lEnv2) (lEnv3:=lEnv1); auto.
          apply lgamma_osubst_split__lenv_split in J1.
          apply dom_lenv_split in J1. rewrite J1.
          auto using free_env__free_dom, free_lenv__free_dom.

          split; auto.
          split; auto.
            assert (disjoint lEnv2 lEnv1) as Disj1.
              apply uniq_from_wf_lenv in H2.
              solve_uniq.
            apply disjoint_sub with (D1:=lEnv1); auto.
              apply lgamma_osubst_split__lenv_split in J1.
              apply dom_lenv_split in J1. 
              rewrite J1. apply dom_sub_left.

          apply wf_lenv_merge; auto.
            apply lgamma_osubst_split__lenv_split in J1.
            apply wf_lenv_split_right in J1; auto.

            assert (disjoint lEnv2 lEnv1) as Disj1.
              apply uniq_from_wf_lenv in H2.
              solve_uniq.
            apply disjoint_sym_1.
            apply disjoint_sub with (D1:=lEnv1); auto.
              apply lgamma_osubst_split__lenv_split in J1.
              apply dom_lenv_split in J1. 
              rewrite J1. apply dom_sub_right.
      split.
        apply lgamma_osubst_split_right with (lEnv2:=lEnv2') (lEnv2':=lEnv2) (lEnv3:=lEnv1); auto.
          apply lgamma_osubst_split__lenv_split in J1.
          apply dom_lenv_split in J1. rewrite J1.
          auto using free_env__free_dom, free_lenv__free_dom.

          split; auto.
          split; auto.
            assert (disjoint lEnv2 lEnv1) as Disj1.
              apply uniq_from_wf_lenv in H2.
              solve_uniq.
            apply disjoint_sub with (D1:=lEnv1); auto.
              apply lgamma_osubst_split__lenv_split in J1.
              apply dom_lenv_split in J1. 
              rewrite J1. apply dom_sub_left.

          apply wf_lenv_merge; auto.
            apply lgamma_osubst_split__lenv_split in J1.
            apply wf_lenv_split_right in J1; auto.

            assert (disjoint lEnv2 lEnv1) as Disj1.
              apply uniq_from_wf_lenv in H2.
              solve_uniq.
            apply disjoint_sym_1.
            apply disjoint_sub with (D1:=lEnv1); auto.
              apply lgamma_osubst_split__lenv_split in J1.
              apply dom_lenv_split in J1. 
              rewrite J1. apply dom_sub_right.
      split; auto.
        apply F_Related_osubst_ltyp with (lEnv1:=lEnv2') (lEnv2:=lEnv2); auto.
          split; auto.
            apply disjoint_sub with (D1:=lE); auto.
              apply dom_lenv_split in J.
              rewrite J. apply dom_sub_right.

          apply wf_lenv_merge; auto.
            apply lgamma_osubst_split__lenv_split in J1.
            apply wf_lenv_split_right in J1; auto.

            assert (disjoint lEnv2 lEnv1) as Disj1.
              apply uniq_from_wf_lenv in H2.
              solve_uniq.
            apply disjoint_sym_1.
            apply disjoint_sub with (D1:=lEnv1); auto.
              apply lgamma_osubst_split__lenv_split in J1.
              apply dom_lenv_split in J1.
              rewrite J1. apply dom_sub_right.
 
          simpl_env.
          apply fv_lenv_split in J.
          rewrite J in H4.
          auto.
Qed. 

(*******************************************************************************)
(** parametricity *)

Lemma oparametricity: forall E lE e t dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
   typing E lE e t ->
   F_Related_osubst E lE gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
   F_Rosubst E rsubst dsubst dsubst' Env->
   F_Related_oterms t rsubst dsubst dsubst'
                                 (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
                                 (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e)))
                                 Env lEnv
   .
Proof.
  intros E lE e t dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv Htyping Hrel_sub HRsub.
  generalize dependent rsubst.
  generalize dependent gsubst'.
  generalize dependent gsubst.
  generalize dependent lgsubst'.
  generalize dependent lgsubst.
  generalize dependent dsubst'.
  generalize dependent dsubst.
  generalize dependent Env.
  generalize dependent lEnv.
  (typing_cases (induction Htyping) Case); intros.
  Case "typing_var".
    assert (J:=Hrel_sub). apply F_Related_osubst__inversion in J. 
    destruct J as [[[[[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe] Hwfe'] HwfEnv] HwflEnv].
    assert (G:=@bindosgE__bindosgsubst E [] gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv x T Hrel_sub H0); auto.
    destruct G as [J1 [J2 [v [v' [[[[Hb Hb'] Ht] Ht'] Hrel]]]]]; eauto using wf_typ_from_binds_typ.
    assert (dom lEnv [=] {}) as lEnvNil.
      apply wf_lgamma_osubst_empty_linctx in Hwflg; auto.
    apply empty_dom__empty_ctx in lEnvNil. subst.
    rewrite m_delta_gamma_osubst_var with (E:=E) (lE:=[]) (x:=x) (gsubst:=gsubst) (t:=apply_delta_subst_typ dsubst T) (e:=v) (Env:=Env) (lEnv:=[]); auto.
    rewrite m_delta_gamma_osubst_var with (E:=E) (lE:=[]) (x:=x) (gsubst:=gsubst') (t:=apply_delta_subst_typ dsubst' T) (e:=v') (Env:=Env) (lEnv:=[]); auto.

  Case "typing_lvar".
    assert (J:=Hrel_sub). apply F_Related_osubst__inversion in J. 
    destruct J as [[[[[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe] Hwfe'] HwfEnv] HwflEnv].
    assert (G:=@lbindosgE__lbindosgsubst E gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv x T Hrel_sub); auto.
    destruct G as [J1 [J2 [v [v' [[[[Hb Hb'] Ht] Ht'] Hrel]]]]]; eauto using wf_typ_from_lbinds_typ.
    rewrite m_delta_lgamma_osubst_var with (E:=E) (lE:=[(x, lbind_typ T)]) (x:=x) (gsubst:=gsubst) (t:=apply_delta_subst_typ dsubst T) (e:=v) (Env:=Env) (lEnv:=lEnv); auto.
    rewrite m_delta_lgamma_osubst_var with (E:=E) (lE:=[(x, lbind_typ T)]) (x:=x) (gsubst:=gsubst') (t:=apply_delta_subst_typ dsubst' T) (e:=v') (Env:=Env) (lEnv:=lEnv); auto.

  Case "typing_abs".
    assert (J:=Hrel_sub). apply F_Related_osubst__inversion in J. 
    destruct J as [[[[[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe] Hwfe'] HwfEnv] HwflEnv].

    rename H into WFTV.
    
    exists (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_abs T1 e1)))).
    exists (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_abs T1 e1)))).
    split.
      SCase "typing".
      simpl_commut_subst.
      apply typing_abs with (L:=L `union` dom (gsubst) `union` dom (lgsubst) `union` dom E `union` dom Env `union` dom lEnv); auto.
        apply wft_osubst with (E:=E) (dsubst:=dsubst); auto.

        intros x Hfv.
        assert (x `notin` L) as Htyping; auto.
        apply H0 in Htyping. 
        apply m_typing_osubst_ltyp_closed with (E:=E) (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst) (Env:=Env) (lEnv:=lEnv) in Htyping; auto.
    split.
      SCase "typing".
      simpl_commut_subst.
      apply typing_abs with (L:=L `union` dom (gsubst') `union` dom (lgsubst')  `union` dom E `union` dom Env `union` dom lEnv); auto.
        apply wft_osubst with (E:=E) (dsubst:=dsubst'); auto.

        intros x Hfv.
        assert (x `notin` L) as Htyping; auto.
        apply H0 in Htyping. 
        apply m_typing_osubst_ltyp_closed with (E:=E) (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst') (Env:=Env) (lEnv:=lEnv) in Htyping; auto.
    split; try solve [split; try solve [apply delta_gamma_lgamma_osubst_value with (E:=E) (D:=D) (Env:=Env) (lEnv:=lEnv); eauto using FrTyping__labsvalue | auto]].
    split; try solve [split; try solve [apply delta_gamma_lgamma_osubst_value with (E:=E) (D:=D) (Env:=Env) (lEnv:=lEnv); eauto using FrTyping__labsvalue | auto]].
      SCase "Frel".
      apply F_Related_ovalues_arrow_req.
      split; try solve [apply delta_gamma_lgamma_osubst_value with (E:=E) (D:=D) (Env:=Env) (lEnv:=lEnv); eauto using FrTyping__labsvalue].
      split; try solve [apply delta_gamma_lgamma_osubst_value with (E:=E) (D:=D) (Env:=Env) (lEnv:=lEnv); eauto using FrTyping__labsvalue].
      SSCase "arrow".
        exists (dom gsubst `union` dom lgsubst `union` dom gsubst' `union` dom lgsubst' `union` dom E `union` dom D).
        intros lEnv1 x x' Htyping Htyping' Hwfle Disj' Harrow_left.

        assert (disjoint lEnv1 gsubst /\ disjoint lEnv1 lgsubst /\ disjoint lEnv1 gsubst' /\ disjoint lEnv1 lgsubst' /\ disjoint lEnv1 E /\ disjoint lEnv1 D) as Disj.
          apply disjdom_sym_1 in Disj'.
          split.
            apply disjdom__disjoint.
            apply disjdom_sub with (D1:=dom gsubst `union` dom lgsubst `union` dom gsubst' `union` dom lgsubst' `union` dom E `union` dom D); auto.
               fsetdec.
          split.
            apply disjdom__disjoint.
            apply disjdom_sub with (D1:=dom gsubst `union` dom lgsubst `union` dom gsubst' `union` dom lgsubst' `union` dom E `union` dom D); auto.
               fsetdec.
          split.
            apply disjdom__disjoint.
            apply disjdom_sub with (D1:=dom gsubst `union` dom lgsubst `union` dom gsubst' `union` dom lgsubst' `union` dom E `union` dom D); auto.
               fsetdec.
          split.
            apply disjdom__disjoint.
            apply disjdom_sub with (D1:=dom gsubst `union` dom lgsubst `union` dom gsubst' `union` dom lgsubst' `union` dom E `union` dom D); auto.
               fsetdec.
          split.
            apply disjdom__disjoint.
            apply disjdom_sub with (D1:=dom gsubst `union` dom lgsubst `union` dom gsubst' `union` dom lgsubst' `union` dom E `union` dom D); auto.
               fsetdec.
            apply disjdom__disjoint.
            apply disjdom_sub with (D1:=dom gsubst `union` dom lgsubst `union` dom gsubst' `union` dom lgsubst' `union` dom E `union` dom D); auto.
               fsetdec.
        pick fresh y.
        assert (y `notin` L) as Fry. auto.
        assert (wf_typ E T2) as WFT'. 
          apply H0 in Fry.
          apply typing_regular in Fry.
          decompose [and] Fry; auto.
        apply H1 with (dsubst:=dsubst) (dsubst':=dsubst') 
                         (gsubst:=gsubst)(Env:=Env)(lEnv:=lEnv1++lEnv)
                         (gsubst':=gsubst') 
                         (lgsubst:=[(y,x)]++lgsubst)
                         (lgsubst':=[(y,x')]++lgsubst') 
                         (rsubst:=rsubst) in Fry; auto.
        assert (
            apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst ([(y,x)]++lgsubst) (open_ee e1 y))) =
            apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (subst_ee y x (open_ee e1 y))))
                  ) as Heq1. simpl. reflexivity.
         assert (
            apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst ([(y,x')]++lgsubst') (open_ee e1 y))) =
            apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (subst_ee y x' (open_ee e1 y))))
                  ) as Heq2.  simpl. reflexivity.
         rewrite Heq1 in Fry. rewrite Heq2 in Fry. clear Heq1 Heq2.
         destruct Fry as [v [v' [Ht [Ht' [[Hbrc Hv] [[Hbrc' Hv'] Hrel]]]]]].
         exists (v). exists (v').
         split.
           SSSCase "norm".
           split; auto.
           apply bigstep_red_trans with (e':=(apply_delta_subst dsubst (apply_gamma_subst gsubst  (apply_gamma_subst lgsubst (subst_ee y x (open_ee e1 y)))))); auto.
              eapply m_red_labs_osubst with (lEnv':=lEnv1); eauto.
                decompose [and] Disj. split; auto.
         split; auto.
           SSSCase "norm".
           split; auto.
           apply bigstep_red_trans with (e':=(apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (subst_ee y x' (open_ee e1 y)))))); auto.
              eapply m_red_labs_osubst with (lEnv':=lEnv1); eauto.
                decompose [and] Disj. split; auto.
           SSSCase "Frel".
           apply F_Related_osubst_ltyp with (lEnv1:=lEnv) (lEnv2:=lEnv1); auto.
             decompose [and] Disj. split; auto.

             destruct Harrow_left as [w [w' [Hn [Hn' Hrel']]]].
             exists (w). exists (w'). split; auto.

  Case "typing_app".
   assert (J:=Hrel_sub). apply F_Related_osubst__inversion in J. 
    destruct J as [[[[[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe] Hwfe'] HwfEnv] HwflEnv].
   assert (J:=Htyping1).
   apply typing_regular in J.
   destruct J as [_ [Hwfle'' [He WFTarrow]]].
   apply F_Related_osubst_split with (lE1:=D1) (lE2:=D2) in Hrel_sub; auto.
   destruct Hrel_sub as [lgsubst1 [lgsubst1' [lgsubst2 [lgsubst2' [lEnv1 [lEnv2 [J1 [J2 [J3 J4]]]]]]]]].

   assert (
      F_Related_oterms (typ_arrow T1 T2) rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst1 e1)))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst1' e1))) Env lEnv1
     ) as FR_ArrowType.
    apply IHHtyping1; auto.
   destruct FR_ArrowType as [v [v' [Ht [Ht' [Hn [Hn' Hrel]]]]]].

   apply F_Related_ovalues_arrow_leq in Hrel.
   destruct Hrel as [Hv [Hv' [L Harrow]]]; subst.

   assert (
      F_Related_oterms T1 rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst2 e2)))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst'(apply_gamma_subst lgsubst2' e2))) Env lEnv2
     ) as FR_T1.
    apply IHHtyping2; auto.
   destruct FR_T1 as [v0 [v'0 [Ht1 [Ht1' [Hn1 [Hn1' Hrel_wft1]]]]]].

   assert (lenv_split Env lEnv1 lEnv2 lEnv) as Split.
     apply lgamma_osubst_split__lenv_split in J1. auto.

   assert (uniq lEnv2) as Uniq2.
     apply typing_regular in Ht1. destruct Ht1 as [JJ1 [JJ2 [JJ3 JJ4]]].
     apply uniq_from_wf_lenv in JJ2; auto.
   assert (JJ:=@pick_lenv (L `union` dom lEnv2 `union` dom lEnv `union` dom lEnv1 `union` dom Env `union` dom E `union` dom D1 `union` dom D2 `union` dom D3 ) lEnv2 Uniq2).
   destruct JJ as [asubst [Wfa [lEnv2_eq_asubst Disj]]].
   assert (disjoint asubst Env) as Disj1.
     apply disjoint_split_right in Split.
     apply disjoint_eq with (D1:=lEnv2); auto.
   assert (disjdom (atom_subst_codom asubst) (union (dom Env) (dom lEnv2))) as Disj2.
     apply disjdom_sym_1 in Disj.
     apply disjdom_sub with (D2:=union (dom Env) (dom lEnv2)) in Disj; try solve [assumption].
     fsetdec.
   destruct (@Harrow (subst_atoms_lenv asubst lEnv2) 
                                             (subst_atoms_exp asubst (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst2 e2)))) 
                                             (subst_atoms_exp asubst (apply_delta_subst dsubst' (apply_gamma_subst gsubst'(apply_gamma_subst lgsubst2' e2))))) 
       as [u [u' [Hnorm_vxu [Hnorm_v'x'u' Hrel_wft2]]]]; auto.
     apply typing_lin_renamings; auto.
     apply typing_lin_renamings; auto.
     apply wf_lenv_merge; auto.
       apply wf_lenv_renamings; auto.

       assert (disjdom (atom_subst_codom asubst) (dom lEnv2)) as Disj3.
         apply disjdom_app_r in Disj2. destruct Disj2.
         apply disjdom_sym_1; auto.
       assert (J:=@subst_atoms_lenv__dom_upper asubst lEnv2 Wfa Uniq2 Disj3).
       apply disjdom__disjoint.
       apply disjdom_sym_1.
       apply disjdom_sub with (D1:=union (dom lEnv2) (atom_subst_codom asubst)); auto.
       eapply disjdom_app_r.
         split.
           apply disjoint__disjdom.
           apply disjoint_lenv_split' in Split.
           apply disjoint_sym_1; auto.
            
           apply disjdom_sym_1 in Disj.
           apply disjdom_sub with (D2:=(dom lEnv1)) in Disj; auto.
             fsetdec.

     assert (J:=@subst_atoms_lenv__dom_eq asubst lEnv2 Wfa Uniq2 lEnv2_eq_asubst).
     apply disjdom_sym_1 in Disj.
     apply disjdom_sub with (D2:=L) in Disj; auto.
       apply disjdom_sym_1.
       apply disjdom_eq with (D1:=atom_subst_codom asubst); auto.
          rewrite J. fsetdec.       
       fsetdec.

     exists (subst_atoms_exp asubst v0). exists (subst_atoms_exp asubst v'0).
     split.
       apply normalize_renamings; auto.
     split.
       apply normalize_renamings; auto.
       apply Forel_lin_renamings with (E:=E); auto.
         eapply preservation_normalization; eauto.
         eapply preservation_normalization; eauto.

   assert (F_Related_ovalues T2 rsubst dsubst dsubst' (rev_subst_atoms_exp asubst u) (rev_subst_atoms_exp asubst u') Env (lEnv2++lEnv1)) as Hrel_wft2'.
     assert (lEnv2++lEnv1 = rev_subst_atoms_lenv asubst ((subst_atoms_lenv asubst lEnv2)++ lEnv1)) as Eq1.
       rewrite rev_subst_atoms_lenv_app.
       rewrite <- id_rev_subst_atoms_lenv; auto.
         rewrite <- rev_subst_atoms_lenv_notin_inv; auto.
           apply disjdom_sym_1 in Disj.
           apply disjdom_sub with (D2:=dom lEnv1) in Disj; auto.
             fsetdec.
         rewrite lEnv2_eq_asubst. fsetdec.

         apply disjdom_sym_1 in Disj.
         apply disjdom_sub with (D2:=dom lEnv2) in Disj; auto.
           fsetdec.
     rewrite Eq1.
     apply Forel_lin_rev_renamings with (E:=E); auto.
       apply preservation_normalization with (e:=exp_app v (subst_atoms_exp asubst (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst2 e2))))); auto.
         apply typing_app with (T1:=apply_delta_subst_typ dsubst T1) (D1:=lEnv1) (D2:=subst_atoms_lenv asubst lEnv2).
           simpl_commut_subst in Ht.
           apply preservation_normalization with (v:=v) in Ht; auto.

           apply typing_lin_renamings; auto.

           apply lenv_split_commute.
           apply disjoint__lenv_split; auto.
             apply wf_lenv_renamings; auto.

             assert (J:=@subst_atoms_lenv__dom_eq asubst lEnv2 Wfa Uniq2 lEnv2_eq_asubst).
             apply disjdom_sym_1 in Disj.
             apply disjdom_sub with (D2:=dom lEnv1) in Disj; auto.
               apply disjdom__disjoint.
               apply disjdom_eq with (D1:=atom_subst_codom asubst); auto.
                 rewrite J. fsetdec.             
               fsetdec.

       apply preservation_normalization with (e:=exp_app v' (subst_atoms_exp asubst (apply_delta_subst dsubst' (apply_gamma_subst gsubst'(apply_gamma_subst lgsubst2' e2))))); auto.
         apply typing_app with (T1:=apply_delta_subst_typ dsubst' T1) (D1:=lEnv1) (D2:=subst_atoms_lenv asubst lEnv2).
           simpl_commut_subst in Ht'.
           apply preservation_normalization with (v:=v') in Ht'; auto.

           apply typing_lin_renamings; auto.

           apply lenv_split_commute.
           apply disjoint__lenv_split; auto.
             apply wf_lenv_renamings; auto.

             assert (J:=@subst_atoms_lenv__dom_eq asubst lEnv2 Wfa Uniq2 lEnv2_eq_asubst).
             apply disjdom_sym_1 in Disj.
             apply disjdom_sub with (D2:=dom lEnv1) in Disj; auto.
               apply disjdom__disjoint.
               apply disjdom_eq with (D1:=atom_subst_codom asubst); auto.
                 rewrite J. fsetdec.             
               fsetdec.

       apply disjdom_sym_1 in Disj.
       apply disjdom_sub with (D2:=dom Env) in Disj; auto.
         fsetdec.

       apply disjdom_eq with (D1:=dom lEnv2); auto.
       eapply disjdom_app_r.
       split.
         apply disjoint__disjdom.
         apply disjoint_split_right in Split; auto.
       
         apply disjoint__disjdom.
         eapply disjoint_app_l.
         split.
           assert (J:=@subst_atoms_lenv__dom_eq asubst lEnv2 Wfa Uniq2 lEnv2_eq_asubst).
           apply disjdom__disjoint.
           apply disjdom_eq with (D1:=atom_subst_codom asubst); auto.
             apply disjdom_sym_1 in Disj.
             apply disjdom_sub with (D2:=dom lEnv2) in Disj; auto.
               fsetdec.             
             fsetdec.

           apply disjoint_lenv_split' in Split; auto.
   assert (normalize (exp_app v (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst2 e2)))) (rev_subst_atoms_exp asubst u)) as Hnorm'_vxu.
     apply normalize_rev_renamings with (asubst:=asubst) in Hnorm_vxu; auto.
     rewrite rev_subst_atoms_exp__app in Hnorm_vxu.
     rewrite <- id_rev_subst_atoms_exp with (asubst:=asubst) in Hnorm_vxu; auto.
       rewrite <- rev_wf_asubst_id with (asubst:=asubst) (e:=v) in Hnorm_vxu; auto.
       apply disjdom_sub with (D1:=dom Env `union` dom lEnv1).
         eapply disjdom_app_r.
         split.
           apply disjdom_sym_1.
           apply disjdom_sym_1 in Disj.
           apply disjdom_sub with (D2:=dom Env) in Disj; auto.
             fsetdec.             
           apply disjdom_sym_1.
           apply disjdom_sym_1 in Disj.
           apply disjdom_sub with (D2:=dom lEnv1) in Disj; auto.
             fsetdec.             
         apply preservation_normalization with (v:=v) in Ht; auto.
         apply typing_fv_ee_upper in Ht; auto.
      apply typing_fv_ee_lower in Ht1; auto.
      rewrite <- lEnv2_eq_asubst. assumption.

      apply typing_fv_ee_upper in Ht1; auto.
      apply disjdom_sub with (D1:=union (dom Env) (dom lEnv2)); auto.  

   assert (normalize (exp_app v' (apply_delta_subst dsubst' (apply_gamma_subst gsubst'(apply_gamma_subst lgsubst2' e2)))) (rev_subst_atoms_exp asubst u')) as Hnorm'_v'x'u'.
     apply normalize_rev_renamings with (asubst:=asubst) in Hnorm_v'x'u'; auto.
     rewrite rev_subst_atoms_exp__app in Hnorm_v'x'u'.
     rewrite <- id_rev_subst_atoms_exp with (asubst:=asubst) in Hnorm_v'x'u'; auto.
       rewrite <- rev_wf_asubst_id with (asubst:=asubst) (e:=v') in Hnorm_v'x'u'; auto.
       apply disjdom_sub with (D1:=dom Env `union` dom lEnv1).
         eapply disjdom_app_r.
         split.
           apply disjdom_sym_1.
           apply disjdom_sym_1 in Disj.
           apply disjdom_sub with (D2:=dom Env) in Disj; auto.
             fsetdec.             
           apply disjdom_sym_1.
           apply disjdom_sym_1 in Disj.
           apply disjdom_sub with (D2:=dom lEnv1) in Disj; auto.
             fsetdec.             
         apply preservation_normalization with (v:=v') in Ht'; auto.
         apply typing_fv_ee_upper in Ht'; auto.
      apply typing_fv_ee_lower in Ht1'; auto.
      rewrite <- lEnv2_eq_asubst. assumption.

      apply typing_fv_ee_upper in Ht1'; auto.
      apply disjdom_sub with (D1:=union (dom Env) (dom lEnv2)); auto.  

   exists(rev_subst_atoms_exp asubst u). exists(rev_subst_atoms_exp asubst u').
   assert (apply_delta_subst dsubst
            (apply_gamma_subst gsubst
              (apply_gamma_subst lgsubst (exp_app e1 e2)) 
            ) =
            apply_delta_subst dsubst
            (apply_gamma_subst gsubst
              (exp_app 
                (apply_gamma_subst lgsubst1 e1)
                (apply_gamma_subst lgsubst2 e2)
              )               
            )
          ) as EQ.
     simpl_commut_subst in *.
     rewrite lgamma_subst_split_osubst' with (lgsubst1:=lgsubst1) (lgsubst2:=lgsubst2) (E:=E) (lE:=D3) (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst) (Env:=Env) (lEnv1:=lEnv1) (lEnv2:=lEnv2) (lEnv:=lEnv); auto.
     rewrite lgamma_subst_split_osubst with (lgsubst1:=lgsubst1) (lgsubst2:=lgsubst2) (E:=E) (lE:=D3) (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst) (Env:=Env) (lEnv1:=lEnv1) (lEnv2:=lEnv2) (lEnv:=lEnv); auto.
     apply F_Related_osubst__inversion in J3.
     decompose [prod] J3; auto.
     apply F_Related_osubst__inversion in J4.
     decompose [prod] J4; auto.
     rewrite lgamma_osubst_split_shuffle2 with (lgsubst:=lgsubst) (lgsubst1:=lgsubst1) (E:=E) (lE:=D3) (Env:=Env) (lEnv1:=lEnv1) (lEnv2:=lEnv2) (lEnv:=lEnv) ; auto.
     erewrite gamma_osubst_closed_exp; eauto.
       rewrite lgamma_osubst_split_shuffle1 with (lgsubst:=lgsubst) (lgsubst2:=lgsubst2) (E:=E) (lE:=D3) (e:=apply_gamma_subst lgsubst2 e2) (Env:=Env) (lEnv1:=lEnv1) (lEnv2:=lEnv2) (lEnv:=lEnv) ; auto.
       erewrite gamma_osubst_closed_exp with 
         (e:=apply_delta_subst dsubst
            (apply_gamma_subst gsubst
              (apply_gamma_subst lgsubst2 e2))
          ); eauto.
         unfold disjdom.
         rewrite_env (nil ++ E) in Htyping2.
         rewrite_env (nil ++ D2) in Htyping2.
         apply typing_osubst_closed with (dsubst:=dsubst)(gsubst:=gsubst)(lgsubst:=lgsubst2)(Env:=Env)(lEnv:=lEnv2) in Htyping2; auto.
         simpl_env in Htyping2.
         split; intros x xnotin.
           apply in_fv_ee_typing with (x:=x) in Htyping2; auto.
           assert (x `in` dom Env \/ x `in` dom lEnv2) as J. fsetdec.
           destruct J as [J | J].
             apply disjoint_lgamma_osubst in b5.
             decompose [and] b5. clear b5.
             clear H0 H2 H1 H3 H5 H6 H7 H8 H10.
             clear xnotin b b0 b1 b2 b3 b4 b6 b7 a0 b8 b9 b10 b11 b12 b13 b14 a1.
             clear IHHtyping1 IHHtyping2 J2 J3 J4 Ht Ht' Hn Hn' Harrow Ht1 Ht1' Hn1 Hn1' Hrel_wft1 Hrel_wft2.
             solve_uniq.

             assert (x `in` dom lEnv)as J'.
               apply dom_lenv_split in Split.
               rewrite Split. auto.
             assert (dom D1 [=] dom lgsubst1) as DomEq.
               apply dom_lgamma_osubst in b5.
               decompose [and] b5; auto.
             rewrite <- DomEq.
             assert (x `notin` dom D3)as J''.            
               apply lgamma_osubst_split__wf_lgamma_osubst in J1.
               apply disjoint_lgamma_osubst in J1.
               decompose [and] J1. clear J1.             
               clear H0 H2 H1 H3 H5 H4 H7 H8 H10.
               clear xnotin b b0 b1 b2 b3 b4 b6 b7 a0 b8 b9 b10 b11 b12 b13 b14 a1.
               clear IHHtyping1 IHHtyping2 J2 J3 J4 Ht Ht' Hn Hn' Harrow Ht1 Ht1' Hn1 Hn1' Hrel_wft1 Hrel_wft2.
               solve_uniq.
             apply dom_lenv_split in H.
             rewrite H in J''. auto.

           apply notin_fv_ee_typing with (y:=x) in Htyping2; auto.
           assert (x `notin` dom Env) as J'.
             apply disjoint_lgamma_osubst in b5.
             decompose [and] b5. clear b5.
             clear H0 H2 H1 H3 H5 H6 H7 H8 H10.
             clear b b0 b1 b2 b3 b4 b6 b7 a0 b8 b9 b10 b11 b12 b13 b14 a1.
             clear IHHtyping1 IHHtyping2 J2 J3 J4 Ht Ht' Hn Hn' Harrow Ht1 Ht1' Hn1 Hn1' Hrel_wft1 Hrel_wft2.
             solve_uniq.

           assert ( x `notin` dom lEnv2) as J''.
             assert (dom D1 [=] dom lgsubst1) as DomEq.
               apply dom_lgamma_osubst in b5.
               decompose [and] b5; auto.
             rewrite <- DomEq in xnotin.
             assert (x `in` dom D3)as J'''.            
               apply dom_lenv_split in H.
               rewrite H. auto.
             assert (x `notin` dom lEnv)as JJ'.
               apply lgamma_osubst_split__wf_lgamma_osubst in J1.
               apply disjoint_lgamma_osubst in J1.
               decompose [and] J1. clear J1.             
               clear H0 H2 H1 H3 H5 H4 H7 H8 H10.
               clear b b0 b1 b2 b3 b4 b6 b7 a0 b8 b9 b10 b11 b12 b13 b14 a1.
               clear IHHtyping1 IHHtyping2 J2 J3 J4 Ht Ht' Hn Hn' Harrow Ht1 Ht1' Hn1 Hn1' Hrel_wft1 Hrel_wft2.
               solve_uniq.
             apply dom_lenv_split in Split.
             rewrite Split in JJ'. auto.
           auto.

       unfold disjdom.
       rewrite_env (nil ++ E) in Htyping1.
       rewrite_env (nil ++ D1) in Htyping1.
       apply typing_osubst_closed with (dsubst:=dsubst)(gsubst:=gsubst)(lgsubst:=lgsubst1)(Env:=Env)(lEnv:=lEnv1) in Htyping1; auto.
       simpl_env in Htyping1.
       split; intros x xnotin.
         apply in_fv_ee_typing with (x:=x) in Htyping1; auto.
         assert (x `in` dom Env \/ x `in` dom lEnv1) as J. fsetdec.
         destruct J as [J | J].
           apply disjoint_lgamma_osubst in b13.
           decompose [and] b13. clear b13.
           clear H0 H2 H1 H3 H5 H6 H7 H8 H10.
           clear b b0 b1 b2 b3 b4 b6 b7 a0 b8 b9 b10 b11 b12 b5 b14 a1.
           clear IHHtyping1 IHHtyping2 J2 J3 J4 Ht Ht' Hn Hn' Harrow Ht1 Ht1' Hn1 Hn1' Hrel_wft1 Hrel_wft2.
           solve_uniq.

           assert (x `in` dom lEnv)as J'.
             apply dom_lenv_split in Split.
             rewrite Split. auto.
           assert (dom D2 [=] dom lgsubst2) as DomEq.
             apply dom_lgamma_osubst in b13.
             decompose [and] b13; auto.
           rewrite <- DomEq.
           assert (x `notin` dom D3)as J''.            
             apply lgamma_osubst_split__wf_lgamma_osubst in J1.
             apply disjoint_lgamma_osubst in J1.
             decompose [and] J1. clear J1.             
             clear H0 H2 H1 H3 H5 H4 H7 H8 H10.
             clear J DomEq xnotin b b0 b1 b2 b3 b4 b5 b6 b7 a0 b8 b9 b10 b11 b12 b13 b14 a1.
             clear IHHtyping1 IHHtyping2 J2 J3 J4 Ht Ht' Hn Hn' Harrow Ht1 Ht1' Hn1 Hn1' Hrel_wft1 Hrel_wft2.
             solve_uniq.
           apply dom_lenv_split in H.
           rewrite H in J''. auto.
         apply notin_fv_ee_typing with (y:=x) in Htyping1; auto.
         assert (x `notin` dom Env) as J'.
           apply disjoint_lgamma_osubst in b13.
           decompose [and] b13. clear b13.
           clear H0 H2 H1 H3 H5 H6 H7 H8 H10.
           clear b b0 b1 b2 b3 b4 b5 b6 b7 a0 b8 b9 b10 b11 b12 b14 a1.
           clear IHHtyping1 IHHtyping2 J2 J3 J4 Ht Ht' Hn Hn' Harrow Ht1 Ht1' Hn1 Hn1' Hrel_wft1 Hrel_wft2.
           solve_uniq.
         assert ( x `notin` dom lEnv1) as J''.
           assert (dom D2 [=] dom lgsubst2) as DomEq.
             apply dom_lgamma_osubst in b13.
             decompose [and] b13; auto.
           rewrite <- DomEq in xnotin.
           assert (x `in` dom D3)as J'''.            
             apply dom_lenv_split in H.
             rewrite H. auto.
           assert (x `notin` dom lEnv)as JJ'.
             apply lgamma_osubst_split__wf_lgamma_osubst in J1.
             apply disjoint_lgamma_osubst in J1.
             decompose [and] J1. clear J1.             
             clear H0 H2 H1 H3 H5 H4 H7 H8 H10.
             clear b b0 b1 b2 b3 b4 b5 b6 b7 a0 b8 b9 b10 b11 b12 b14 a1.
             clear IHHtyping1 IHHtyping2 J2 J3 J4 Ht Ht' Hn Hn' Harrow Ht1 Ht1' Hn1 Hn1' Hrel_wft1 Hrel_wft2.
             solve_uniq.
           apply dom_lenv_split in Split.
           rewrite Split in JJ'. auto.
         auto.   
   repeat(rewrite EQ). clear EQ.
   assert (apply_delta_subst dsubst'
            (apply_gamma_subst gsubst'
              (apply_gamma_subst lgsubst' (exp_app e1 e2)) 
            ) =
            apply_delta_subst dsubst'
            (apply_gamma_subst gsubst'
              (exp_app 
                (apply_gamma_subst lgsubst1' e1)
                (apply_gamma_subst lgsubst2' e2)
              )               
            )
          ) as EQ.
     simpl_commut_subst in *.
     rewrite lgamma_subst_split_osubst' with (lgsubst1:=lgsubst1') (lgsubst2:=lgsubst2') (E:=E) (lE:=D3) (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst') (Env:=Env) (lEnv1:=lEnv1) (lEnv2:=lEnv2) (lEnv:=lEnv); auto.
     rewrite lgamma_subst_split_osubst with (lgsubst1:=lgsubst1') (lgsubst2:=lgsubst2') (E:=E) (lE:=D3) (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst') (Env:=Env) (lEnv1:=lEnv1) (lEnv2:=lEnv2) (lEnv:=lEnv); auto.
     apply F_Related_osubst__inversion in J3.
     decompose [prod] J3; auto.
     apply F_Related_osubst__inversion in J4.
     decompose [prod] J4; auto.
     rewrite lgamma_osubst_split_shuffle2 with (lgsubst:=lgsubst') (lgsubst1:=lgsubst1') (E:=E) (lE:=D3)  (Env:=Env) (lEnv1:=lEnv1) (lEnv2:=lEnv2) (lEnv:=lEnv); auto.
     erewrite gamma_osubst_closed_exp; eauto.
       rewrite lgamma_osubst_split_shuffle1 with (lgsubst:=lgsubst') (lgsubst2:=lgsubst2') (E:=E) (lE:=D3) (e:=apply_gamma_subst lgsubst2' e2)  (Env:=Env) (lEnv1:=lEnv1) (lEnv2:=lEnv2) (lEnv:=lEnv); auto.
       erewrite gamma_osubst_closed_exp with 
         (e:=apply_delta_subst dsubst'
            (apply_gamma_subst gsubst'
              (apply_gamma_subst lgsubst2' e2))
          ); eauto.
         unfold disjdom.
         rewrite_env (nil ++ E) in Htyping2.
         rewrite_env (nil ++ D2) in Htyping2.
         apply typing_osubst_closed with (dsubst:=dsubst')(gsubst:=gsubst')(lgsubst:=lgsubst2')(Env:=Env)(lEnv:=lEnv2) in Htyping2; auto.
         simpl_env in Htyping2.
         split; intros x xnotin.
           apply in_fv_ee_typing with (x:=x) in Htyping2; auto.
           assert (x `in` dom Env \/ x `in` dom lEnv2) as J. fsetdec.
           destruct J as [J | J].
             apply disjoint_lgamma_osubst in b4.
             decompose [and] b4. clear b4.
             clear H0 H2 H1 H3 H5 H6 H7 H8 H10.
             clear b b0 b1 b2 b3 b5 b6 b7 a0 b8 b9 b10 b11 b12 b13 b14 a1.
             clear IHHtyping1 IHHtyping2 J2 J3 J4 Ht Ht' Hn Hn' Harrow Ht1 Ht1' Hn1 Hn1' Hrel_wft1 Hrel_wft2.
             solve_uniq.

             assert (x `in` dom lEnv)as J'.
               apply dom_lenv_split in Split.
               rewrite Split. auto.
             assert (dom D1 [=] dom lgsubst1') as DomEq.
               apply dom_lgamma_osubst in b4.
               decompose [and] b4; auto.
             rewrite <- DomEq.
             assert (x `notin` dom D3)as J''.            
               apply lgamma_osubst_split__wf_lgamma_osubst in J2.
               apply disjoint_lgamma_osubst in J2.
               decompose [and] J2. clear J2.             
               clear H0 H2 H1 H3 H5 H4 H7 H8 H10.
               clear J DomEq xnotin b b0 b1 b2 b3 b4 b5 b6 b7 a0 b8 b9 b10 b11 b12 b13 b14 a1.
               clear IHHtyping1 IHHtyping2 J3 J4 Ht Ht' Hn Hn' Harrow Ht1 Ht1' Hn1 Hn1' Hrel_wft1 Hrel_wft2.
               solve_uniq.
             apply dom_lenv_split in H.
             rewrite H in J''. auto.

           apply notin_fv_ee_typing with (y:=x) in Htyping2; auto.
           assert (x `notin` dom Env) as J'.
             apply disjoint_lgamma_osubst in b4.
             decompose [and] b4. clear b4.
             clear H0 H2 H1 H3 H5 H6 H7 H8 H10.
             clear b b0 b1 b2 b3 b5 b6 b7 a0 b8 b9 b10 b11 b12 b13 b14 a1.
             clear IHHtyping1 IHHtyping2 J2 J3 J4 Ht Ht' Hn Hn' Harrow Ht1 Ht1' Hn1 Hn1' Hrel_wft1 Hrel_wft2.
             solve_uniq.

           assert ( x `notin` dom lEnv2) as J''.
             assert (dom D1 [=] dom lgsubst1') as DomEq.
               apply dom_lgamma_osubst in b4.
               decompose [and] b4; auto.
             rewrite <- DomEq in xnotin.
             assert (x `in` dom D3)as J'''.            
               apply dom_lenv_split in H.
               rewrite H. auto.
             assert (x `notin` dom lEnv)as JJ'.
               apply lgamma_osubst_split__wf_lgamma_osubst in J2.
               apply disjoint_lgamma_osubst in J2.
               decompose [and] J2. clear J2.             
               clear H0 H2 H1 H3 H5 H4 H7 H8 H10.
               clear DomEq xnotin b b0 b1 b2 b3 b4 b5 b6 b7 a0 b8 b9 b10 b11 b12 b13 b14 a1.
               clear IHHtyping1 IHHtyping2 J3 J4 Ht Ht' Hn Hn' Harrow Ht1 Ht1' Hn1 Hn1' Hrel_wft1 Hrel_wft2.
               solve_uniq.
             apply dom_lenv_split in Split.
             rewrite Split in JJ'. auto.
           auto.

       unfold disjdom.
       rewrite_env (nil ++ E) in Htyping1.
       rewrite_env (nil ++ D1) in Htyping1.
       apply typing_osubst_closed with (dsubst:=dsubst')(gsubst:=gsubst')(lgsubst:=lgsubst1')(Env:=Env)(lEnv:=lEnv1) in Htyping1; auto.
       simpl_env in Htyping1.
       split; intros x xnotin.
         apply in_fv_ee_typing with (x:=x) in Htyping1; auto.
         assert (x `in` dom Env \/ x `in` dom lEnv1) as J. fsetdec.
         destruct J as [J | J].
           apply disjoint_lgamma_osubst in b12.
           decompose [and] b12. clear b12.
           clear H0 H2 H1 H3 H5 H6 H7 H8 H10.
            clear b b0 b1 b2 b3 b4 b6 b7 a0 b8 b9 b10 b11 b5 b13 b14 a1.
            clear IHHtyping1 IHHtyping2 J2 J3 J4 Ht Ht' Hn Hn' Harrow Ht1 Ht1' Hn1 Hn1' Hrel_wft1 Hrel_wft2.
           solve_uniq.

           assert (x `in` dom lEnv)as J'.
             apply dom_lenv_split in Split.
             rewrite Split. auto.
           assert (dom D2 [=] dom lgsubst2') as DomEq.
             apply dom_lgamma_osubst in b12.
             decompose [and] b12; auto.
           rewrite <- DomEq.
           assert (x `notin` dom D3)as J''.            
             apply lgamma_osubst_split__wf_lgamma_osubst in J2.
             apply disjoint_lgamma_osubst in J2.
             decompose [and] J2. clear J2.             
             clear H0 H2 H1 H3 H5 H4 H7 H8 H10.
             clear J DomEq xnotin b b0 b1 b2 b3 b4 b5 b6 b7 a0 b8 b9 b10 b11 b12 b13 b14 a1.
             clear IHHtyping1 IHHtyping2 J1 J3 J4 Ht Ht' Hn Hn' Harrow Ht1 Ht1' Hn1 Hn1' Hrel_wft1 Hrel_wft2.
             solve_uniq.
           apply dom_lenv_split in H.
           rewrite H in J''. auto.
         apply notin_fv_ee_typing with (y:=x) in Htyping1; auto.
         assert (x `notin` dom Env) as J'.
           apply disjoint_lgamma_osubst in b12.
           decompose [and] b12. clear b12.
           clear H0 H2 H1 H3 H5 H6 H7 H8 H10.
           clear b b0 b1 b2 b3 b4 b5 b6 b7 a0 b8 b9 b10 b11 b13 b14 a1.
           clear IHHtyping1 IHHtyping2 J1 J3 J4 Ht Ht' Hn Hn' Harrow Ht1 Ht1' Hn1 Hn1' Hrel_wft1 Hrel_wft2.
           solve_uniq.
         assert ( x `notin` dom lEnv1) as J''.
           assert (dom D2 [=] dom lgsubst2') as DomEq.
             apply dom_lgamma_osubst in b12.
             decompose [and] b12; auto.
           rewrite <- DomEq in xnotin.
           assert (x `in` dom D3)as J'''.            
             apply dom_lenv_split in H.
             rewrite H. auto.
           assert (x `notin` dom lEnv)as JJ'.
             apply lgamma_osubst_split__wf_lgamma_osubst in J2.
             apply disjoint_lgamma_osubst in J2.
             decompose [and] J2. clear J2.             
             clear H0 H2 H1 H3 H5 H4 H7 H8 H10.
             clear b b0 b1 b2 b3 b4 b5 b6 b7 a0 b8 b9 b10 b11 b13 b14 a1.
             clear IHHtyping1 IHHtyping2 J1 J3 J4 Ht Ht' Hn Hn' Harrow Ht1 Ht1' Hn1 Hn1' Hrel_wft1 Hrel_wft2.
             solve_uniq.
           apply dom_lenv_split in Split.
           rewrite Split in JJ'. auto.
         auto.   
   repeat(rewrite EQ). clear EQ.
   repeat(split; try solve [simpl_commut_subst in *; eauto |
                                              simpl_commut_subst; apply congr_app with (v1:=v); auto |
                                              simpl_commut_subst; apply congr_app with (v1:=v'); auto]).
    apply Forel_lin_domeq with (lEnv:=lEnv2++lEnv1); auto.
      apply wf_lenv_merge; auto.
        apply disjoint_lenv_split' in Split; auto.
      apply dom_lenv_split in Split.
        rewrite Split. simpl_env. fsetdec.

  Case "typing_tabs".
  assert (J:=Hrel_sub). apply F_Related_osubst__inversion in J.
  destruct J as [[[[[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe] Hwfe'] HwfEnv] HwflEnv].
  exists (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_tabs e1)))).
  exists (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_tabs e1)))).
      split.
      SCase "typing".
      simpl_commut_subst.
      apply typing_tabs with (L:=L `union` dom (dsubst) `union` dom E `union` dom Env `union` dom lEnv).
        intros X Hfv.
        assert (X `notin` L) as Htyping. auto.
        apply H in Htyping. 
        apply m_typing_osubst_kind_closed with (E:=E) (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst) (Env:=Env) (lEnv:=lEnv) in Htyping; auto.

      split.
      SCase "typing".
      simpl_commut_subst.
      apply typing_tabs with (L:=L `union` dom (dsubst') `union` dom E `union` dom Env `union` dom lEnv).
        intros X Hfv.
        assert (X `notin` L) as Htyping. auto.
        apply H in Htyping. 
        apply m_typing_osubst_kind_closed with (E:=E) (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst') (Env:=Env) (lEnv:=lEnv) in Htyping; auto.

      split; try solve [split; auto; eapply delta_gamma_lgamma_osubst_value with (E:=E) (dsubst:=dsubst) (lgsubst:=lgsubst) (Env:=Env) (lEnv:=lEnv) ; eauto using FrTyping__tabsvalue].
      split; try solve [split; auto; eapply delta_gamma_lgamma_osubst_value with (E:=E) (dsubst:=dsubst') (lgsubst:=lgsubst') (Env:=Env) (lEnv:=lEnv) ; eauto using FrTyping__tabsvalue].
      SCase "Frel".
      apply F_Related_ovalues_all_req.
      repeat(split; try solve [eapply delta_gamma_lgamma_osubst_value with (E:=E) (Env:=Env) (lEnv:=lEnv) ; eauto using FrTyping__tabsvalue |
                                           apply  typing_osubst_closed with (E:=E) (E':=@nil (atom*binding))(dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst) (D:=D) (D':=nil) (Env:=Env) (lEnv:=lEnv) ; 
                                               try solve [auto | apply typing_tabs with (L:=L); auto] |
                                           apply  typing_osubst_closed with (E:=E) (E':=@nil (atom*binding))(dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst') (D:=D) (D':=nil) (Env:=Env) (lEnv:=lEnv) ; 
                                               try solve [auto | apply typing_tabs with (L:=L); auto]]).
        SSCase "Frel".
        exists (L `union` fv_te e1 `union` dom E `union` fv_env E `union` fv_lenv D `union` fv_env Env `union` fv_lenv lEnv).
        intros X t2 t2' R Fr Hwfor Hfv.
        assert (X `notin` L) as FryL. auto.
        assert (wf_typ ([(X,bind_kn)]++E) (open_tt T1 X)) as WFT'.
          apply H in FryL.
          apply typing_regular in FryL.
          decompose [and] FryL; auto.
        apply H0 with (dsubst:=[(X, t2)]++dsubst) 
                         (dsubst':=[(X, t2')]++dsubst') 
                         (gsubst:=gsubst) (Env:=Env) (lEnv:=lEnv)
                         (gsubst':=gsubst') 
                         (lgsubst:=lgsubst)
                         (lgsubst':=lgsubst') 
                         (rsubst:=[(X,R)]++rsubst)in FryL; auto.
        simpl in FryL. simpl_env in FryL.
        erewrite swap_subst_te_ogsubst with (E:=E) (dsubst:=dsubst) (Env:=Env) (lEnv:=lEnv) in FryL; eauto using wfor_left_inv. 
        erewrite swap_subst_te_olgsubst with (E:=E) (dsubst:=dsubst) (Env:=Env) (lEnv:=lEnv) in FryL; eauto using wfor_left_inv. 
        erewrite swap_subst_te_ogsubst with  (E:=E)  (dsubst:=dsubst') (Env:=Env) (lEnv:=lEnv) in FryL; eauto using wfor_right_inv.
        erewrite swap_subst_te_olgsubst with  (E:=E)  (dsubst:=dsubst') (Env:=Env) (lEnv:=lEnv) in FryL; eauto using wfor_right_inv.
        destruct FryL as [v [v' [Ht [Ht' [[Hbrc Hv] [[Hbrc' Hv'] Hrel]]]]]].
        exists (v). exists (v').
        split.
          SSSCase "norm".
          split; auto.
          apply bigstep_red_trans with (e':=(apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (subst_te X t2 (open_te e1 X)))))); auto.
            eapply m_red_tabs_osubst; eauto using wfor_left_inv.

        split; auto.
          SSSCase "norm".
          split; auto.
          apply bigstep_red_trans with (e':=(apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (subst_te X t2' (open_te e1 X)))))); auto.
            eapply m_red_tabs_osubst; eauto using wfor_right_inv.
          SSSCase "Fsubst".
          apply F_Related_osubst_kind; auto.
          SSSCase "FRsubst".
          apply F_Rosubst_rel; auto.

   Case "typing_tapp".
   assert (J:=Hrel_sub). apply F_Related_osubst__inversion in J. 
   destruct J as [[[[[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe] Hwfe'] HwfEnv] HwflEnv].
   apply typing_regular in Htyping.
   destruct Htyping as [_ [_ [He WFTall]]].
   assert (
      F_Related_oterms (typ_all T1) rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e1)))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e1))) Env lEnv
     ) as FR_AllType.
      apply IHHtyping; auto.
   destruct FR_AllType as [v [v' [Ht [Ht' [Hn [Hn' Hrel]]]]]].

   apply F_Related_ovalues_all_leq in Hrel.
   destruct Hrel as [Hv [Hv' [L Hall]]]; subst.
   unfold open_tt in Hall.

   assert (forall X,
     X `notin` dom (E) `union` fv_tt T1 ->
     wf_typ ([(X, bind_kn)]++E) (open_tt T1 X)) as w.
     simpl in WFTall.
     eapply wft_all_inv; eauto.

   pick fresh y.
   assert (y `notin` L) as Fr'. auto.
   destruct (@Hall y (apply_delta_subst_typ dsubst T) (apply_delta_subst_typ dsubst' T) 
                                (F_FORel T (rho_nil++rsubst) (delta_nil++dsubst) (delta_nil++dsubst') Env)
                                Fr'
                   ) as [u [u' [Hn_vt2u [Hn_v't2'u' Hrel_wft]]]]; auto.
          apply F_FORel__R__wfor with (E:=E) (rsubst:=rsubst); auto.
             simpl_env. split; auto. 

          assert (ddom_env E [=] dom rsubst) as EQ.
            apply dom_rho_subst; auto.
          assert (y `notin` ddom_env E) as Fv.
            apply dom__ddom; auto.
          rewrite EQ in Fv. auto.

   exists(u). exists (u').
       split. simpl_commut_subst in *; rewrite commut_delta_osubst_open_tt with (dE:=E) (Env:=Env); auto.
                eapply typing_tapp; eauto using wft_osubst.
       split. simpl_commut_subst in *; rewrite commut_delta_osubst_open_tt with (dE:=E) (Env:=Env); auto.
                eapply typing_tapp; eauto using wft_osubst.
       split.
       SCase "Norm".
       simpl_commut_subst.
       eapply m_ocongr_tapp; eauto.

      split.
      SCase "Norm".
      simpl_commut_subst.
      eapply m_ocongr_tapp; eauto.

      SCase "Frel".
      unfold open_tt.
      assert (F_Related_ovalues (open_tt_rec 0 T T1) (rho_nil++rsubst) (delta_nil++dsubst) (delta_nil++dsubst') u u' Env lEnv =
                  F_Related_ovalues (open_tt_rec 0 T T1) rsubst dsubst dsubst' u u' Env lEnv).
         simpl. reflexivity.
      rewrite <- H0.
      apply oparametricity_subst_value with
                (E:=E) (E':=@nil (atom*binding))
                (rsubst:=rsubst) (rsubst':=rho_nil)
                (k:=0)
                (t:=T1) (t2:=T)
                (X:=y) (R:=(F_FORel T (rho_nil++rsubst) (delta_nil++dsubst) (delta_nil++dsubst') Env))
                ; auto.
        SSCase "wft".
          simpl_env. unfold open_tt in w. apply w; auto.

        SSCase "wft".
          simpl_env. rewrite subst_tt_intro_rec with (X:=y); auto.
          rewrite_env (map (subst_tb y T) nil ++ E).
          eapply wf_typ_subst_tb; auto.
          apply w; auto.

        SSCase "Rel__R".
        unfold F_ORel__R. split; auto.

        SSCase "fv".
        eapply m_tapp_ofv with (dsubst:=dsubst) (dsubst':=dsubst') (v:=v) (v':=v') (Env:=Env) (lEnv:=lEnv); 
           eauto using notin_fv_te_typing.

        SSCase "eq".
        apply dom_delta_osubst with (Env:=Env); auto.
        apply dom_delta_osubst with (Env:=Env); auto.
        apply dom_rho_subst; auto.

        SSCase "typing".
        simpl_env. simpl.
        apply preservation_normalization with (e:=(exp_tapp (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e1)))
                                                            (apply_delta_subst_typ dsubst (apply_gamma_subst_typ gsubst (apply_gamma_subst_typ lgsubst T))))); auto.
          rewrite swap_subst_tt_odsubst with (E:=E)(Env:=Env); auto.
          rewrite subst_tt_open_tt_rec; eauto using type_from_wf_typ.
            rewrite <- subst_tt_fresh with (T:=T1); auto.
            simpl. destruct (y == y); subst; try solve [contradict n; auto].
              rewrite commut_delta_osubst_open_tt_rec with (dE:=E)(Env:=Env); auto.
              apply typing_tapp; eauto using wft_osubst.
                simpl_commut_subst in Ht. auto.

          apply m_ocongr_tapp with(E:=E)(lE:=D)(Env:=Env)(lEnv:=lEnv)(v:=v); auto.

        SSCase "typing".
        simpl_env. simpl.
        apply preservation_normalization with (e:=(exp_tapp (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e1)))
                                                            (apply_delta_subst_typ dsubst' (apply_gamma_subst_typ gsubst' (apply_gamma_subst_typ lgsubst' T))))); auto.
          rewrite swap_subst_tt_odsubst with (E:=E)(Env:=Env); auto.
          rewrite subst_tt_open_tt_rec; eauto using type_from_wf_typ.
            rewrite <- subst_tt_fresh with (T:=T1); auto.
            simpl. destruct (y == y); subst; try solve [contradict n; auto].
              rewrite commut_delta_osubst_open_tt_rec with (dE:=E)(Env:=Env); auto.
              apply typing_tapp; eauto using wft_osubst.
                simpl_commut_subst in Ht'. auto.

          apply m_ocongr_tapp with(E:=E)(lE:=D)(Env:=Env)(lEnv:=lEnv)(v:=v'); auto.

        SSCase "rsubst".
        eapply rsubst_weaken with (X:=y) (rsubst:=rsubst) (rsubst':=rho_nil); eauto.
          apply dom_rho_subst; auto.
        SSCase "dsubst".   
        apply odsubst_weaken with (X:=y) (dsubst:=dsubst) (dsubst':=delta_nil) (t:=(apply_delta_subst_typ dsubst T)); auto.
          apply wft_osubst with (E:=E) (Env:=Env) (dsubst:=dsubst) ; auto.
          apply dom_delta_osubst in Hwfd; auto.
        SSCase "dsubst'".
        apply odsubst_weaken with (X:=y) (dsubst:=dsubst') (dsubst':=delta_nil) (t:=(apply_delta_subst_typ dsubst' T)); auto.
          apply wft_osubst with (E:=E) (Env:=Env) (dsubst:=dsubst') ; auto.
          apply dom_delta_osubst in Hwfd'; auto.

  Case "typing_bang".
    assert (J:=Hrel_sub). apply F_Related_osubst__inversion in J. decompose [prod] J. clear J.

    assert (
      F_Related_oterms T rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e))) Env lEnv
     ) as FR_T.
       apply IHHtyping; auto.
    destruct FR_T as [v [v' [Ht [Ht' [Hn [Hn' Hrel]]]]]].

    exists (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_bang e)))).
    exists (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_bang e)))).
    assert (J:=b4).
    apply wf_lgamma_osubst_empty_linctx in J; auto.
    apply dom_empty_inv in J; subst.
    split; simpl_commut_subst; auto.
    split; simpl_commut_subst; auto.
    split. split; simpl_commut_subst; auto.
    split. split; simpl_commut_subst; auto.
      SCase "Frel".
        SSCase "Frel".
        apply F_Related_ovalues_bang_req.
        repeat (split; simpl_commut_subst; auto).
        exists (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e))).
        exists (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e))).
        repeat(split; auto).
          exists (v). exists (v'). split; auto.

  Case "typing_let".
    assert (J:=Hrel_sub). apply F_Related_osubst__inversion in J. 
    destruct J as [[[[[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe] Hwfe'] HwfEnv] HwflEnv].
    apply F_Related_osubst_split with (lE1:=D1) (lE2:=D2) in Hrel_sub; auto.
    destruct Hrel_sub as [lgsubst1 [lgsubst1' [lgsubst2 [lgsubst2' [lEnv1 [lEnv2 [J1 [J2 [J3 J4]]]]]]]]].

   assert (
      F_Related_oterms (typ_bang T1) rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst1 e1)))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst'(apply_gamma_subst lgsubst1' e1))) Env lEnv1
     ) as FR_T1.
    apply IHHtyping; auto.
   destruct FR_T1 as [v1 [v'1 [Ht1 [Ht1' [Hn1 [Hn1' Hrel1]]]]]].

   apply F_Related_ovalues_bang_leq in Hrel1.
   destruct Hrel1 as [Hv1 [Hv'1 [x1 [x1' [EQ1 [EQ1' Hrel1]]]]]]; subst.

   assert (lenv_split Env lEnv1 lEnv2 lEnv) as Split.
     apply lgamma_osubst_split__lenv_split in J1. auto.

   assert (apply_delta_subst dsubst
            (apply_gamma_subst gsubst
              (apply_gamma_subst lgsubst (exp_let e1 e2)) 
            ) =
            apply_delta_subst dsubst
            (apply_gamma_subst gsubst
              (exp_let 
                (apply_gamma_subst lgsubst1 e1)
                (apply_gamma_subst lgsubst2 e2)
              )               
            )
          ) as EQ.
     simpl_commut_subst in *.
     rewrite lgamma_subst_split_osubst' with (lgsubst1:=lgsubst1) (lgsubst2:=lgsubst2) (E:=E) (lE:=D3) (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst) (Env:=Env) (lEnv1:=lEnv1) (lEnv2:=lEnv2) (lEnv:=lEnv); auto.
     rewrite lgamma_subst_split_osubst with (lgsubst1:=lgsubst1) (lgsubst2:=lgsubst2) (E:=E) (lE:=D3) (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst) (Env:=Env) (lEnv1:=lEnv1) (lEnv2:=lEnv2) (lEnv:=lEnv); auto.
     apply F_Related_osubst__inversion in J3.
     decompose [prod] J3; auto.
     apply F_Related_osubst__inversion in J4.
     decompose [prod] J4; auto.
     rewrite lgamma_osubst_split_shuffle2 with (lgsubst:=lgsubst) (lgsubst1:=lgsubst1) (E:=E) (lE:=D3) (Env:=Env) (lEnv1:=lEnv1) (lEnv2:=lEnv2) (lEnv:=lEnv) ; auto.
     erewrite gamma_osubst_closed_exp; eauto.
     SCase "EQ".
       rewrite lgamma_osubst_split_shuffle1 with (lgsubst:=lgsubst) (lgsubst2:=lgsubst2) (E:=E) (lE:=D3) (e:=apply_gamma_subst lgsubst2 e2) (Env:=Env) (lEnv1:=lEnv1) (lEnv2:=lEnv2) (lEnv:=lEnv) ; auto.
       erewrite gamma_osubst_closed_exp with 
         (e:=apply_delta_subst dsubst
            (apply_gamma_subst gsubst
              (apply_gamma_subst lgsubst2 e2))
          ); eauto.
         unfold disjdom.
         pick fresh y.
         assert (y `notin` L) as Htyping2. auto.
         assert (wf_lenv (apply_delta_subst_env dsubst (y~bind_typ T1)++Env) lEnv2) as Wfle2.
           rewrite_env (nil ++ [(y, bind_typ (apply_delta_subst_typ dsubst T1))] ++ Env).
           apply wf_lenv_weakening; auto.
             simpl_env. apply wf_env_typ; auto.
             apply typing_regular in Ht1. decompose [and] Ht1.
             inversion H6; auto.
         apply H in Htyping2. 
         rewrite_env (nil ++ E) in Htyping2.
         rewrite_env (nil ++ D2) in Htyping2.
         apply typing_osubst_closed with (dsubst:=dsubst)(gsubst:=gsubst)(lgsubst:=lgsubst2)(Env:=Env)(lEnv:=lEnv2) in Htyping2; auto.
         simpl_env in Htyping2.
         split; intros x xin.
         SSCase "left".
           assert (x `in` fv_ee (apply_delta_subst dsubst
                 (apply_gamma_subst gsubst
                   (apply_gamma_subst lgsubst2 (open_ee e2 y))))) as xin'.
             rewrite commut_lgamma_osubst_open_ee with (E:=E)(D:=D2)(gsubst:=gsubst)(dsubst:=dsubst)(Env:=Env)(lEnv:=lEnv2); auto.
             rewrite commut_gamma_osubst_open_ee with (E:=E)(D:=D2)(lgsubst:=lgsubst2)(dsubst:=dsubst)(Env:=Env)(lEnv:=lEnv2); auto.
             rewrite commut_delta_osubst_open_ee with (dE:=E)(dsubst:=dsubst)(Env:=Env); auto.
             assert (J5:=@fv_ee_open_ee_sub_right 
               (apply_delta_subst dsubst
                 (apply_gamma_subst gsubst
                   (apply_gamma_subst lgsubst2 e2)))
               (apply_delta_subst dsubst
                 (apply_gamma_subst gsubst
                   (apply_gamma_subst lgsubst2 y)))).
             clear - J5 xin. fsetdec.             
           apply in_fv_ee_typing with (x:=x) in Htyping2; auto.
           assert (x = y \/ x `in` (dom Env) \/ x `in` dom lEnv2) as J. 
             simpl in Htyping2. clear - Htyping2. fsetdec.
           destruct J as [J | [J | J]]; subst.
               clear - Fr b5.
               apply dom_lgamma_osubst in b5.
               decompose [and] b5. clear b5.
               rewrite <- H2. auto.

               apply disjoint_lgamma_osubst in b5.
               decompose [and] b5. clear b5.
               clear - J H6.
               solve_uniq.

               assert (x `in` dom lEnv)as J'.
                 apply dom_lenv_split in Split.
                 rewrite Split. auto.
               assert (dom D1 [=] dom lgsubst1) as DomEq.
                 apply dom_lgamma_osubst in b5.
                 decompose [and] b5; auto.
               rewrite <- DomEq.
               assert (x `notin` dom D3)as J''.            
                 apply lgamma_osubst_split__wf_lgamma_osubst in J1.
                 apply disjoint_lgamma_osubst in J1.
                 decompose [and] J1. clear J1.
                 clear - H8 J'.             
                 solve_uniq.
               apply dom_lenv_split in H1.
               rewrite H1 in J''. auto.

         SSCase "right".
           assert (x `notin` union (dom (apply_delta_subst_env dsubst (y~bind_typ T1)++Env)) (dom lEnv2)) as xnotin.
             assert (x `notin` dom Env) as J'.
               apply disjoint_lgamma_osubst in b5.
               decompose [and] b5. 
               clear - xin H6.
               solve_uniq.

             assert ( x `notin` dom lEnv2) as J''.
               assert (dom D1 [=] dom lgsubst1) as DomEq.
                 apply dom_lgamma_osubst in b5.
                 decompose [and] b5; auto.
               rewrite <- DomEq in xin.
              assert (x `in` dom D3)as J'''.            
                 apply dom_lenv_split in H1.
                 rewrite H1. auto.
              assert (x `notin` dom lEnv)as JJ'.
                apply lgamma_osubst_split__wf_lgamma_osubst in J1.
                apply disjoint_lgamma_osubst in J1.
                decompose [and] J1.
                clear - J''' H8. 
                solve_uniq.
              apply dom_lenv_split in Split.
              rewrite Split in JJ'. auto.
              assert (x <> y) as xny.
                assert (dom D1 [=] dom lgsubst1) as DomEq.
                  apply dom_lgamma_osubst in b5.
                  decompose [and] b5; auto.
                rewrite <- DomEq in xin.
                destruct_notin.
                clear - NotInTac13 xin.
                destruct (x == y); subst; auto.
             simpl. clear - J' J'' xny. auto.

           apply notin_fv_ee_typing with (y:=x) in Htyping2; auto.
           rewrite commut_lgamma_osubst_open_ee with (E:=E)(D:=D2)(gsubst:=gsubst)(dsubst:=dsubst)(Env:=Env)(lEnv:=lEnv2) in Htyping2; auto.
           rewrite commut_gamma_osubst_open_ee with (E:=E)(D:=D2)(lgsubst:=lgsubst2)(dsubst:=dsubst)(Env:=Env)(lEnv:=lEnv2) in Htyping2; auto.
           rewrite commut_delta_osubst_open_ee with (dE:=E)(dsubst:=dsubst)(Env:=Env) in Htyping2; auto.
           assert (J5:=@fv_ee_open_ee_sub_right 
               (apply_delta_subst dsubst
                 (apply_gamma_subst gsubst
                   (apply_gamma_subst lgsubst2 e2)))
               (apply_delta_subst dsubst
                 (apply_gamma_subst gsubst
                   (apply_gamma_subst lgsubst2 y)))).
           clear - J5 Htyping2. fsetdec.             

     SCase "disjdom".
       unfold disjdom.
       rewrite_env (nil ++ E) in Htyping.
       rewrite_env (nil ++ D1) in Htyping.
       apply typing_osubst_closed with (dsubst:=dsubst)(gsubst:=gsubst)(lgsubst:=lgsubst1)(Env:=Env)(lEnv:=lEnv1) in Htyping; auto.
       simpl_env in Htyping.
       split; intros x xnotin.
         apply in_fv_ee_typing with (x:=x) in Htyping; auto.
         assert (x `in` dom Env \/ x `in` dom lEnv1) as J. fsetdec.
         destruct J as [J | J].
           apply disjoint_lgamma_osubst in b13.
           decompose [and] b13.
           clear - J H6.
           solve_uniq.

           assert (x `in` dom lEnv)as J'.
             apply dom_lenv_split in Split.
             rewrite Split. auto.
           assert (dom D2 [=] dom lgsubst2) as DomEq.
             apply dom_lgamma_osubst in b13.
             decompose [and] b13; auto.
           rewrite <- DomEq.
           assert (x `notin` dom D3)as J''.            
             apply lgamma_osubst_split__wf_lgamma_osubst in J1.
             apply disjoint_lgamma_osubst in J1.
             decompose [and] J1. 
             clear - H8 J'.
             solve_uniq.
           apply dom_lenv_split in H1.
           rewrite H1 in J''. auto.
         apply notin_fv_ee_typing with (y:=x) in Htyping; auto.
         assert (x `notin` dom Env) as J'.
           apply disjoint_lgamma_osubst in b13.
           decompose [and] b13.
           clear - xnotin H6.
           solve_uniq.
         assert ( x `notin` dom lEnv1) as J''.
           assert (dom D2 [=] dom lgsubst2) as DomEq.
             apply dom_lgamma_osubst in b13.
             decompose [and] b13; auto.
           rewrite <- DomEq in xnotin.
           assert (x `in` dom D3)as J'''.            
             apply dom_lenv_split in H1.
             rewrite H1. auto.
           assert (x `notin` dom lEnv)as JJ'.
             apply lgamma_osubst_split__wf_lgamma_osubst in J1.
             apply disjoint_lgamma_osubst in J1.
             decompose [and] J1.
             clear - J''' H8.
             solve_uniq.
           apply dom_lenv_split in Split.
           rewrite Split in JJ'. auto.
         auto.   
   repeat(rewrite EQ).
   assert (apply_delta_subst dsubst'
            (apply_gamma_subst gsubst'
              (apply_gamma_subst lgsubst' (exp_let e1 e2)) 
            ) =
            apply_delta_subst dsubst'
            (apply_gamma_subst gsubst'
              (exp_let 
                (apply_gamma_subst lgsubst1' e1)
                (apply_gamma_subst lgsubst2' e2)
              )               
            )
          ) as EQ'.
     simpl_commut_subst in *.
     rewrite lgamma_subst_split_osubst' with (lgsubst1:=lgsubst1') (lgsubst2:=lgsubst2') (E:=E) (lE:=D3) (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst') (Env:=Env) (lEnv1:=lEnv1) (lEnv2:=lEnv2) (lEnv:=lEnv); auto.
     rewrite lgamma_subst_split_osubst with (lgsubst1:=lgsubst1') (lgsubst2:=lgsubst2') (E:=E) (lE:=D3) (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst') (Env:=Env) (lEnv1:=lEnv1) (lEnv2:=lEnv2) (lEnv:=lEnv); auto.
     apply F_Related_osubst__inversion in J3.
     decompose [prod] J3; auto.
     apply F_Related_osubst__inversion in J4.
     decompose [prod] J4; auto.
     rewrite lgamma_osubst_split_shuffle2 with (lgsubst:=lgsubst') (lgsubst1:=lgsubst1') (E:=E) (lE:=D3)  (Env:=Env) (lEnv1:=lEnv1) (lEnv2:=lEnv2) (lEnv:=lEnv); auto.
     erewrite gamma_osubst_closed_exp; eauto.
     SCase "EQ".
       rewrite lgamma_osubst_split_shuffle1 with (lgsubst:=lgsubst') (lgsubst2:=lgsubst2') (E:=E) (lE:=D3) (e:=apply_gamma_subst lgsubst2' e2)  (Env:=Env) (lEnv1:=lEnv1) (lEnv2:=lEnv2) (lEnv:=lEnv); auto.
       erewrite gamma_osubst_closed_exp with 
         (e:=apply_delta_subst dsubst'
            (apply_gamma_subst gsubst'
              (apply_gamma_subst lgsubst2' e2))
          ); eauto.
         unfold disjdom.
         pick fresh y.
         assert (wf_lenv (apply_delta_subst_env dsubst' (y~bind_typ T1)++Env) lEnv2) as Wfle2.
           rewrite_env (nil ++ [(y, bind_typ (apply_delta_subst_typ dsubst' T1))] ++ Env).
           apply wf_lenv_weakening; auto.
             simpl_env. apply wf_env_typ; auto.
             apply typing_regular in Ht1'. decompose [and] Ht1'.
             inversion H6; auto.
         assert (y `notin` L) as Htyping2. auto.
         apply H in Htyping2.        
         rewrite_env (nil ++ E) in Htyping2.
         rewrite_env (nil ++ D2) in Htyping2.
         apply typing_osubst_closed with (dsubst:=dsubst')(gsubst:=gsubst')(lgsubst:=lgsubst2')(Env:=Env)(lEnv:=lEnv2) in Htyping2; auto.
         simpl_env in Htyping2.
         split; intros x xin.
         SSCase "left".
           assert (x `in` fv_ee (apply_delta_subst dsubst'
                 (apply_gamma_subst gsubst'
                   (apply_gamma_subst lgsubst2' (open_ee e2 y))))) as xin'.
             rewrite commut_lgamma_osubst_open_ee with (E:=E)(D:=D2)(gsubst:=gsubst')(dsubst:=dsubst')(Env:=Env)(lEnv:=lEnv2); auto.
             rewrite commut_gamma_osubst_open_ee with (E:=E)(D:=D2)(lgsubst:=lgsubst2')(dsubst:=dsubst')(Env:=Env)(lEnv:=lEnv2); auto.
             rewrite commut_delta_osubst_open_ee with (dE:=E)(dsubst:=dsubst')(Env:=Env); auto.
             assert (J5:=@fv_ee_open_ee_sub_right 
               (apply_delta_subst dsubst'
                 (apply_gamma_subst gsubst'
                   (apply_gamma_subst lgsubst2' e2)))
               (apply_delta_subst dsubst'
                 (apply_gamma_subst gsubst'
                   (apply_gamma_subst lgsubst2' y)))).
             clear - J5 xin. fsetdec.             
           apply in_fv_ee_typing with (x:=x) in Htyping2; auto.
           assert (x = y \/ x `in` (dom Env) \/ x `in` dom lEnv2) as J. 
             simpl in Htyping2. clear - Htyping2. fsetdec.
           destruct J as [J | [J | J]]; subst.
               clear - Fr b4.
               apply dom_lgamma_osubst in b4.
               decompose [and] b4.
               rewrite <- H2. auto.

             apply disjoint_lgamma_osubst in b4.
             decompose [and] b4. 
             clear - J H6.
             solve_uniq.

             assert (x `in` dom lEnv)as J'.
               apply dom_lenv_split in Split.
               rewrite Split. auto.
             assert (dom D1 [=] dom lgsubst1') as DomEq.
               apply dom_lgamma_osubst in b4.
               decompose [and] b4; auto.
             rewrite <- DomEq.
             assert (x `notin` dom D3)as J''.            
               apply lgamma_osubst_split__wf_lgamma_osubst in J2.
               apply disjoint_lgamma_osubst in J2.
               decompose [and] J2.
               clear - H8 J'.
               solve_uniq.
             apply dom_lenv_split in H1.
             rewrite H1 in J''. auto.

         SSCase "right".
           assert (x `notin` union (dom (apply_delta_subst_env dsubst' (y~bind_typ T1)++Env)) (dom lEnv2)) as xnotin.
             assert (x `notin` dom Env) as J'.
               apply disjoint_lgamma_osubst in b4.
               decompose [and] b4. 
               clear - H6 xin.
               solve_uniq.

             assert ( x `notin` dom lEnv2) as J''.
               assert (dom D1 [=] dom lgsubst1') as DomEq.
                 apply dom_lgamma_osubst in b4.
                 decompose [and] b4; auto.
               rewrite <- DomEq in xin.
               assert (x `in` dom D3)as J'''.            
                 apply dom_lenv_split in H1.
                 rewrite H1. auto.
               assert (x `notin` dom lEnv)as JJ'.
                 apply lgamma_osubst_split__wf_lgamma_osubst in J2.
                 apply disjoint_lgamma_osubst in J2.
                 decompose [and] J2.
                 clear - H8 J'''.
                 solve_uniq.
               apply dom_lenv_split in Split.
               rewrite Split in JJ'. auto.
               assert (x <> y) as xny.
                 assert (dom D1 [=] dom lgsubst1') as DomEq.
                   apply dom_lgamma_osubst in b4.
                   decompose [and] b4; auto.
                 rewrite <- DomEq in xin.
                 destruct_notin.
                 clear - NotInTac13 xin.
                 destruct (x == y); subst; auto.
             clear - J' J'' xny.  simpl. auto.

           apply notin_fv_ee_typing with (y:=x) in Htyping2; auto.
           rewrite commut_lgamma_osubst_open_ee with (E:=E)(D:=D2)(gsubst:=gsubst')(dsubst:=dsubst')(Env:=Env)(lEnv:=lEnv2) in Htyping2; auto.
           rewrite commut_gamma_osubst_open_ee with (E:=E)(D:=D2)(lgsubst:=lgsubst2')(dsubst:=dsubst')(Env:=Env)(lEnv:=lEnv2) in Htyping2; auto.
           rewrite commut_delta_osubst_open_ee with (dE:=E)(dsubst:=dsubst')(Env:=Env) in Htyping2; auto.
           assert (J5:=@fv_ee_open_ee_sub_right 
               (apply_delta_subst dsubst'
                 (apply_gamma_subst gsubst'
                   (apply_gamma_subst lgsubst2' e2)))
               (apply_delta_subst dsubst'
                 (apply_gamma_subst gsubst'
                   (apply_gamma_subst lgsubst2' y)))).
           clear - J5 Htyping2. fsetdec.             

     SCase "disjdom".
       unfold disjdom.
       rewrite_env (nil ++ E) in Htyping.
       rewrite_env (nil ++ D1) in Htyping.
       apply typing_osubst_closed with (dsubst:=dsubst')(gsubst:=gsubst')(lgsubst:=lgsubst1')(Env:=Env)(lEnv:=lEnv1) in Htyping; auto.
       simpl_env in Htyping.
       split; intros x xin.
         apply in_fv_ee_typing with (x:=x) in Htyping; auto.
         assert (x `in` dom Env \/ x `in` dom lEnv1) as J. fsetdec.
         destruct J as [J | J].
           apply disjoint_lgamma_osubst in b12.
           decompose [and] b12. 
           clear - J H6.
           solve_uniq.

           assert (x `in` dom lEnv)as J'.
             apply dom_lenv_split in Split.
             rewrite Split. auto.
           assert (dom D2 [=] dom lgsubst2') as DomEq.
             apply dom_lgamma_osubst in b12.
             decompose [and] b12; auto.
           rewrite <- DomEq.
           assert (x `notin` dom D3)as J''.            
             apply lgamma_osubst_split__wf_lgamma_osubst in J2.
             apply disjoint_lgamma_osubst in J2.
             decompose [and] J2. 
             clear - J' H8.
             solve_uniq.
           apply dom_lenv_split in H1.
           rewrite H1 in J''. auto.
         apply notin_fv_ee_typing with (y:=x) in Htyping; auto.
         assert (x `notin` dom Env) as J'.
           apply disjoint_lgamma_osubst in b12.
           decompose [and] b12. 
           clear - xin H6.
           solve_uniq.
         assert ( x `notin` dom lEnv1) as J''.
           assert (dom D2 [=] dom lgsubst2') as DomEq.
             apply dom_lgamma_osubst in b12.
             decompose [and] b12; auto.
           rewrite <- DomEq in xin.
           assert (x `in` dom D3)as J'''.            
             apply dom_lenv_split in H1.
             rewrite H1. auto.
           assert (x `notin` dom lEnv)as JJ'.
             apply lgamma_osubst_split__wf_lgamma_osubst in J2.
             apply disjoint_lgamma_osubst in J2.
             decompose [and] J2. 
             clear - J''' H8.
             solve_uniq.
           apply dom_lenv_split in Split.
           rewrite Split in JJ'. auto.
         auto.   
   repeat(rewrite EQ'). 

   pick fresh y.
   assert (y `notin` L) as Fry. auto.
   assert (wf_typ ([(y, bind_typ T1)]++E) T2) as WFT2. 
     apply H in Fry.
     apply typing_regular in Fry.
     decompose [and] Fry; auto.
   assert (wf_typ E T1) as WFT1. 
     apply typing_regular in Htyping.
     decompose [and] Htyping.
     inversion H6; auto.
   assert (wf_lgamma_osubst E D2 dsubst gsubst lgsubst2 Env lEnv2) as Wflg2.
     apply F_Related_osubst__inversion in J4. decompose [prod] J4; auto.
     assert (wf_lgamma_osubst E D2 dsubst' gsubst' lgsubst2' Env lEnv2) as Wflg2'.
     apply F_Related_osubst__inversion in J4. decompose [prod] J4; auto.
   assert (typing Env lEnv1 x1 (apply_delta_subst_typ dsubst T1)) as Typing1.
     apply preservation_normalization with (v:=exp_bang x1) in Ht1; auto.
     simpl_commut_subst in Ht1. inversion Ht1; subst; auto.             
   assert (typing Env lEnv1 x1' (apply_delta_subst_typ dsubst' T1)) as Typing1'.
     apply preservation_normalization with (v:=exp_bang x1') in Ht1'; auto.
     simpl_commut_subst in Ht1'. inversion Ht1'; subst; auto.             
   assert (expr (exp_let e1 e2)) as Expr2.
     assert (typing E D3 (exp_let e1 e2) T2) as Typing2.
        apply typing_let with (L:=L)(D1:=D1)(D2:=D2)(T1:=T1); auto.
      apply typing_regular in Typing2.
      decompose [and] Typing2; auto.
   assert (Htv1:=Ht1).
   apply preservation_normalization with (v:=exp_bang x1) in Htv1; auto.
   assert (Htv1':=Ht1').
   apply preservation_normalization with (v:=exp_bang x1') in Htv1'; auto.
   simpl_commut_subst in Htv1. simpl_commut_subst in Htv1'.
   inversion Htv1; subst. inversion Htv1'; subst.
   assert (J:=Split). apply lenv_split_empty_left in J; subst.
   apply H0 with (dsubst:=dsubst) (dsubst':=dsubst') 
                         (gsubst:=[(y,x1)]++gsubst)
                         (gsubst':=[(y,x1')]++gsubst') 
                         (lgsubst:=lgsubst2)
                         (lgsubst':=lgsubst2') 
                         (rsubst:=rsubst)(Env:=Env)(lEnv:=lEnv) in Fry; auto.
          assert (
            apply_delta_subst dsubst (apply_gamma_subst ([(y,x1)]++gsubst) (apply_gamma_subst lgsubst2 (open_ee e2 y))) =
            apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst2 (subst_ee y x1 (open_ee e2 y))))
                  ) as Heq1. simpl. 
           rewrite swap_subst_ee_olgsubst with (E:=E)(D:=D2)(dsubst:=dsubst)(lgsubst:=lgsubst2)(gsubst:=gsubst)(t:=apply_delta_subst_typ dsubst T1)(Env:=Env)(lEnv:=lEnv)(lEnv':=[]); auto.
             apply wf_lgamma_osubst__nfv with (x:=y) in Wflg2; auto.
         assert (
            apply_delta_subst dsubst' (apply_gamma_subst ([(y,x1')]++gsubst') (apply_gamma_subst lgsubst2' (open_ee e2 y))) =
            apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst2' (subst_ee y x1' (open_ee e2 y))))
                  ) as Heq2.  simpl.
           rewrite swap_subst_ee_olgsubst with (E:=E)(D:=D2)(dsubst:=dsubst')(lgsubst:=lgsubst2')(gsubst:=gsubst')(t:=apply_delta_subst_typ dsubst' T1)(Env:=Env)(lEnv:=lEnv)(lEnv':=[]); auto.
             apply wf_lgamma_osubst__nfv with (x:=y) in Wflg2'; auto.
         rewrite Heq1 in Fry. rewrite Heq2 in Fry. clear Heq1 Heq2.
         destruct Fry as [v2 [v2' [Ht2 [Ht2' [[Hbrc2 Hv2] [[Hbrc2' Hv2'] Hrel2]]]]]].

         exists (v2). exists (v2').
         split.
           SCase "typing".
           simpl_commut_subst. simpl_commut_subst in Ht1.
           apply typing_let with (L:=L `union` dom (gsubst) `union` dom (lgsubst2) `union` dom E `union` dom Env `union` dom lEnv)(D1:=[])(D2:=lEnv)(T1:=apply_delta_subst_typ dsubst T1); auto.
             intros x Hfv.
             assert (x `notin` L) as Htyping2; auto.
             apply H in Htyping2. 
             apply m_typing_osubst_typ_closed with (E:=E) (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst2)(Env:=Env)(lEnv:=lEnv) in Htyping2; auto.
         split.
           SCase "typing".
           simpl_commut_subst. simpl_commut_subst in Ht1'.
           apply typing_let with (L:=L `union` dom (gsubst') `union` dom (lgsubst2') `union` dom E `union` dom Env `union` dom lEnv)(D1:=[])(D2:=lEnv)(T1:=apply_delta_subst_typ dsubst' T1); auto.
             intros x Hfv.
             assert (x `notin` L) as Htyping2; auto.
             apply H in Htyping2. 
             apply m_typing_osubst_typ_closed with (E:=E) (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst2') (Env:=Env) (lEnv:=lEnv) in Htyping2; auto.
         split.
           SSSCase "norm".
           split; auto.
           apply bigstep_red__trans with (e':=(apply_delta_subst dsubst (apply_gamma_subst gsubst  (apply_gamma_subst lgsubst2 (subst_ee y x1 (open_ee e2 y)))))); auto.
             simpl_commut_subst.
             apply bigstep_red__trans with (e':=exp_let (exp_bang x1) (apply_delta_subst dsubst (apply_gamma_subst gsubst  (apply_gamma_subst lgsubst2 e2)))); auto.
               destruct Hn1 as [Hbrc1 Hx1].
               apply _congr_let_arg; auto.
                 apply expr_preserved_under_lgamma_osubst with (E:=E)(D:=D3)(dsubst:=dsubst)(gsubst:=gsubst)(lgsubst:=lgsubst)(Env:=Env)(lEnv:=lEnv) in Expr2; auto.
                 apply expr_preserved_under_gamma_osubst with (E:=E)(D:=D3)(dsubst:=dsubst)(gsubst:=gsubst)(lgsubst:=lgsubst)(Env:=Env)(lEnv:=lEnv) in Expr2; auto.
                 apply expr_preserved_under_delta_osubst with (E:=E)(dsubst:=dsubst)(Env:=Env) in Expr2; auto.
                 rewrite EQ in Expr2. simpl_commut_subst in Expr2; auto.

                 apply bigstep_red_trans with (e':=(apply_delta_subst dsubst (apply_gamma_subst gsubst  (apply_gamma_subst lgsubst2 (subst_ee y x1 (open_ee e2 y)))))); auto.
                   apply m_red_bang_osubst with (D2:=D2)(lgsubst2:=lgsubst2)(E:=E)(T1:=T1)(T2:=T2)(L:=L)(Env:=Env)(lEnv2:=lEnv); auto.

         split; auto.
           SSSCase "norm".
           split; auto.
           apply bigstep_red__trans with (e':=(apply_delta_subst dsubst' (apply_gamma_subst gsubst'  (apply_gamma_subst lgsubst2' (subst_ee y x1' (open_ee e2 y)))))); auto.
             simpl_commut_subst.
             apply bigstep_red__trans with (e':=exp_let (exp_bang x1') (apply_delta_subst dsubst' (apply_gamma_subst gsubst'  (apply_gamma_subst lgsubst2' e2)))); auto.
               destruct Hn1' as [Hbrc1' Hx1'].
               apply _congr_let_arg; auto.
                 apply expr_preserved_under_lgamma_osubst with (E:=E)(D:=D3)(dsubst:=dsubst')(gsubst:=gsubst')(lgsubst:=lgsubst')(Env:=Env)(lEnv:=lEnv) in Expr2; auto.
                 apply expr_preserved_under_gamma_osubst with (E:=E)(D:=D3)(dsubst:=dsubst')(gsubst:=gsubst')(lgsubst:=lgsubst')(Env:=Env)(lEnv:=lEnv) in Expr2; auto.
                 apply expr_preserved_under_delta_osubst with (E:=E)(dsubst:=dsubst')(Env:=Env) in Expr2; auto.
                 rewrite EQ' in Expr2. simpl_commut_subst in Expr2; auto.

                 apply bigstep_red_trans with (e':=(apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst2' (subst_ee y x1' (open_ee e2 y)))))); auto.
                   apply m_red_bang_osubst with (D2:=D2)(lgsubst2:=lgsubst2')(E:=E)(T1:=T1)(T2:=T2)(L:=L)(Env:=Env)(lEnv2:=lEnv); auto.
       SCase "Fsubst".
           apply F_Related_osubst_typ; auto.
           destruct Hrel1 as [u1 [u1' [Hx1u1 [Hx1'u1' Hrel1]]]].
           exists (u1). exists (u1'). split; auto.
       SCase "FRsubst".
           apply F_Rosubst_typ; auto.

    Case "typing_apair".
    assert (J:=Hrel_sub). apply F_Related_osubst__inversion in J. decompose [prod] J. clear J.

    assert (
      F_Related_oterms T1 rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e1)))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e1))) Env lEnv
     ) as FR_T1.
       apply IHHtyping1; auto.
    destruct FR_T1 as [v [v' [Ht1 [Ht1' [Hn1 [Hn1' Hrel1]]]]]].

    assert (
      F_Related_oterms T2 rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e2)))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e2))) Env lEnv
     ) as FR_T2.
       apply IHHtyping2; auto.
    destruct FR_T2 as [v0 [v'0 [Ht2 [Ht2' [Hn2 [Hn2' Hrel2]]]]]].

    exists (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_apair e1 e2)))).
    exists (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_apair e1 e2)))).
    split; simpl_commut_subst; auto.
    split; simpl_commut_subst; auto.
    split. split; simpl_commut_subst; auto.
    split. split; simpl_commut_subst; auto.
      SCase "Frel".
        SSCase "Frel".
        apply F_Related_ovalues_with_req.
        repeat (split; simpl_commut_subst; auto).
        exists (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e1))).
        exists (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e2))).
        exists (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e1))).
        exists (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e2))).
        repeat(split; auto).
          exists (v). exists (v'). split; auto.
          exists (v0). exists (v'0). split; auto.

    Case "typing_fst".
    assert (J:=Hrel_sub). apply F_Related_osubst__inversion in J.
    destruct J as [[[[[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe] Hwfe'] HwfEnv] HwflEnv].
    assert (wf_typ E (typ_with T1 T2)) as WFTwith.
      apply typing_regular in Htyping.
      destruct Htyping as [_ [_ [He WFTwith]]]; auto.
    assert (
      F_Related_oterms (typ_with T1 T2) rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e))) Env lEnv
     ) as FR_With.
       apply IHHtyping; auto.
    destruct FR_With as [ee1 [ee1' [Ht [Ht' [Hn [Hn' FR_With]]]]]].

    assert (J1:=Htyping). assert (J2:=Htyping).
    apply typing_osubst_closed with (E:=E) (E':=@nil (atom*binding)) (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst) (D:=D) (D':=nil) (Env:=Env) (lEnv:=lEnv) in J1; auto.
        rewrite commut_delta_subst_with in J1; auto.
    apply typing_osubst_closed with (E:=E) (E':=@nil (atom*binding)) (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst') (D:=D) (D':=nil) (Env:=Env) (lEnv:=lEnv) in J2; auto.
        rewrite commut_delta_subst_with in J2; auto.
    apply congr_fst with (T1:=apply_delta_subst_typ dsubst T1) (T2:=apply_delta_subst_typ dsubst T2) (Env:=Env) (lEnv:=lEnv) in Hn; auto.
    apply congr_fst with (T1:=apply_delta_subst_typ dsubst' T1) (T2:=apply_delta_subst_typ dsubst' T2) (Env:=Env) (lEnv:=lEnv) in Hn'; auto.
    destruct Hn as [e1 [e2 [Hbrc Heq]]].
    destruct Hn' as [e1' [e2' [Hbrc' Heq']]].
    apply F_Related_ovalues_with_leq in FR_With.
    subst.
    destruct FR_With as [Hv [Hv' [ee1 [ee2 [ee1' [ee2' [Heq [Heq' 
                                [[u1 [u1' [[Hbrc_e1u1 Hu1][[Hbrc_e1'u1' Hu1'] Hrel_wft1]]]] 
                                 [u2 [u2' [[Hbrc_e2u2 Hu2][[Hbrc_e2'u2' Hu2'] Hrel_wft2]]]]]
                              ]]]]]]]]; subst.
    inversion Heq. inversion Heq'. subst. clear Heq Heq'.
    exists(u1). exists(u1').
        repeat(split; simpl_commut_subst; auto; try solve [
          apply typing_fst with (T2:=apply_delta_subst_typ dsubst T2);
            apply typing_osubst_closed with (E:=E) (E':=@nil (atom*binding)) (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst) (D:=D) (D':=nil) (Env:=Env) (lEnv:=lEnv) in Htyping; auto |
          apply typing_fst with (T2:=apply_delta_subst_typ dsubst' T2);
            apply typing_osubst_closed with (E:=E) (E':=@nil (atom*binding))  (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst') (D:=D) (D':=nil) (Env:=Env) (lEnv:=lEnv) in Htyping; auto |
          split; auto; apply bigstep_red__trans with (e':=ee1); auto |
          split; auto; apply bigstep_red__trans with (e':=ee1'); auto]).

    Case "typing_snd".
    assert (J:=Hrel_sub). apply F_Related_osubst__inversion in J.
    destruct J as [[[[[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe] Hwfe'] HwfEnv] HwflEnv].
    assert (wf_typ E (typ_with T1 T2)) as WFTwith.
      apply typing_regular in Htyping.
      destruct Htyping as [_ [_ [He WFTwith]]]; auto.
    assert (
      F_Related_oterms (typ_with T1 T2) rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e))) Env lEnv
     ) as FR_With.
       apply IHHtyping; auto.
    destruct FR_With as [ee2 [ee2' [Ht [Ht' [Hn [Hn' FR_With]]]]]].

    assert (J1:=Htyping). assert (J2:=Htyping).
    apply typing_osubst_closed with (E:=E) (E':=@nil (atom*binding)) (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst) (D:=D) (D':=nil) (Env:=Env) (lEnv:=lEnv) in J1; auto.
        rewrite commut_delta_subst_with in J1; auto.
    apply typing_osubst_closed with (E:=E) (E':=@nil (atom*binding)) (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst') (D:=D) (D':=nil) (Env:=Env) (lEnv:=lEnv) in J2; auto.
        rewrite commut_delta_subst_with in J2; auto.
    apply congr_snd with (T1:=apply_delta_subst_typ dsubst T1) (T2:=apply_delta_subst_typ dsubst T2) (Env:=Env) (lEnv:=lEnv) in Hn; auto.
    apply congr_snd with (T1:=apply_delta_subst_typ dsubst' T1) (T2:=apply_delta_subst_typ dsubst' T2) (Env:=Env) (lEnv:=lEnv) in Hn'; auto.
    destruct Hn as [e1 [e2 [Hbrc Heq]]].
    destruct Hn' as [e1' [e2' [Hbrc' Heq']]].
    apply F_Related_ovalues_with_leq in FR_With.
    subst.
    destruct FR_With as [Hv [Hv' [ee1 [ee2 [ee1' [ee2' [Heq [Heq' 
                                [[u1 [u1' [[Hbrc_e1u1 Hu1][[Hbrc_e1'u1' Hu1'] Hrel_wft1]]]] 
                                 [u2 [u2' [[Hbrc_e2u2 Hu2][[Hbrc_e2'u2' Hu2'] Hrel_wft2]]]]]
                              ]]]]]]]]; subst.
    inversion Heq. inversion Heq'. subst. clear Heq Heq'.
    exists (u2). exists (u2').
        repeat(split; simpl_commut_subst; auto; try solve [
          apply typing_snd with (T1:=apply_delta_subst_typ dsubst T1);
            apply  typing_osubst_closed with (E:=E) (E':=@nil (atom*binding)) (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst) (D:=D) (D':=nil) (Env:=Env) (lEnv:=lEnv) in Htyping; auto |
          apply typing_snd with (T1:=apply_delta_subst_typ dsubst' T1);
            apply  typing_osubst_closed with (E:=E) (E':=@nil (atom*binding))  (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst') (D:=D) (D':=nil) (Env:=Env) (lEnv:=lEnv) in Htyping; auto |
          split; auto; apply bigstep_red__trans with (e':=ee2); auto |
          split; auto; apply bigstep_red__trans with (e':=ee2'); auto]).

Qed.

End OParametricity.


(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../../../metatheory" "-I" "../Bang") ***
*** End: ***
 *)
