(** Authors: Jianzhou Zhao. *)

Require Import Wf_nat.
Require Export Metatheory.
Require Import LinF_Definitions.
Require Import LinF_Infrastructure.
Require Import LinF_Lemmas.
Require Import LinF_Soundness.
Require Import LinF_Parametricity_Pre.
Require Export LinF_Parametricity_Interface.
Require Import LinF_Parametricity_Macro.
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

Module Parametricity : IParametricity.

(* ********************************************************************** *)
(** * Wf Relations *)

Definition wfr (r : rel) (T T' : typ) (K:kn) : Prop :=
  (wf_typ nil T K) /\
  (wf_typ nil T' K).

Lemma wfr_inv : forall r T T' K,
  wfr r T T' K->
  (wf_typ nil T K) /\
  (wf_typ nil T' K).
Proof. auto. Qed.

Lemma wfr_left_inv : forall t t' R K,
  wfr R t t' K -> wf_typ nil t K.
Proof.
  intros.
  inversion H. auto.
Qed.

Lemma wfr_right_inv : forall t t' R K,
  wfr R t t' K -> wf_typ nil t' K.
Proof.
  intros. inversion H. auto.
Qed.

(* ********************************************************************** *)
(** * Value Relations *)
Program Fixpoint F_related_values
    (t:typ) (rsubst:rho_subst)
    (dsubst dsubst':delta_subst) (v:exp) (v':exp) {measure typ_size t} : Prop :=
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
    (binds X R rsubst) /\ (value v) /\ (value v') /\ (R v v')
  | typ_arrow K t1 t2 =>
  (*
    v and v' are values
    . |- v : dsubst(t1->t2) . |- v' : dsubst'(t1->t2)
    \forall x x', . |- x : dsubst(t1)  . |- x' : dsubst'(t1)  (x ~~ x': t1 | \rho) -> v x ~~ v' x':t2 | \rho
   -----------------------------------------------------------------
          v ~ v': t1->t2 | \rho
  *)
    (value v) /\ (value v') /\
    (forall x x',
     typing nil nil x (apply_delta_subst_typ dsubst t1) ->
     typing nil nil x' (apply_delta_subst_typ dsubst' t1) ->
     F_related_values t1 rsubst dsubst dsubst' x x'
     ->
     (exists u, exists u',
      normalize (exp_app v x) u /\
      normalize (exp_app v' x') u' /\
      F_related_values t2 rsubst dsubst dsubst' u u')
    )
  | typ_all K t1 =>
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
         wfr R t2 t2' K ->
          X `notin` ((dom rsubst) `union` (fv_tt t1)) ->
          (exists w, exists w',
          normalize (exp_tapp v t2) w /\
          normalize (exp_tapp v' t2') w' /\
          F_related_values (open_tt t1 X)
                           ([(X,R)]++rsubst)
                           ([(X,t2)]++dsubst)
                           ([(X,t2')]++dsubst')
                            w w')
        ))
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
       F_related_values t1 rsubst dsubst dsubst' u1 u1') /\
      (exists u2, exists u2',
       normalize e2 u2 /\
       normalize e2' u2' /\
       F_related_values t2 rsubst dsubst dsubst' u2 u2')
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
    intros K t1 t2. unfold not. intro C. inversion C.
  split.
    intros K t1. unfold not. intro C. inversion C.
  split.
    intros K t1. unfold not. intro C. inversion C.
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
Definition F_related_terms t rsubst (dsubst dsubst':delta_subst) e e': Prop:=
    exists v, exists v',
    typing nil nil e (apply_delta_subst_typ dsubst t) /\
    typing nil nil e' (apply_delta_subst_typ dsubst' t) /\
    normalize e v /\
    normalize e' v' /\
    F_related_values t rsubst dsubst dsubst' v v'
  .

(** * Subst Relations *)
Inductive F_related_subst : env -> lenv -> gamma_subst -> gamma_subst -> gamma_subst -> gamma_subst -> rho_subst -> delta_subst -> delta_subst -> Prop:=
  | F_related_subst_empty :
    (*
      gamma_nil ~ gamma_nil : gempty | rho_nil, delta_nil,  delta_nil
    *)
      F_related_subst nil nil gamma_nil gamma_nil gamma_nil gamma_nil rho_nil delta_nil delta_nil
  | F_related_subst_kind :
    (*
      gsubst ~ gsubst' : genv | rsubst, dsubst, dsubst'
      R \in t<->t'
     -----------------------------------------------------------------
      gsubst ~ gsubst' : genv | (rsubst, X->R), (dsubst, X->t), (dsubst', X->t')
    *)
    forall (E:env) (lE:lenv) (gsubst gsubst' lgsubst lgsubst':gamma_subst) (rsubst:rho_subst) (dsubst dsubst':delta_subst) X R t t' K,
      F_related_subst E lE gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst'->
      X `notin` (fv_env E) `union` (fv_lenv lE) ->
      wfr R t t' K ->
      F_related_subst ([(X, bind_kn K)]++E) lE gsubst gsubst' lgsubst lgsubst'
                                   ([(X,R)]++rsubst) ([(X,t)]++dsubst) ([(X,t')]++dsubst')
  | F_related_subst_typ :
    (*
      gsubst ~ gsubst' : genv | rsubst, dsubst, dsubst'
      e ~ e' : t | rho_subst
     -----------------------------------------------------------------
      (gsubst, x->e) ~ (gsubst',x->e') : (genv, x:t) | rho_subst, dsubst, dsubst'
    *)
    forall (E:env)(lE:lenv)(gsubst gsubst' lgsubst lgsubst':gamma_subst) (v v':exp) (t:typ) (rsubst:rho_subst) (dsubst dsubst':delta_subst) (x:atom),
      F_related_subst E lE gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst'->
      typing nil nil v (apply_delta_subst_typ dsubst t) ->
      typing nil nil v' (apply_delta_subst_typ dsubst' t) ->
      F_related_values t rsubst dsubst dsubst' v v' ->
      x `notin` ((fv_env E) `union` (fv_lenv lE) `union` (fv_tt t)) ->
      wf_typ E t kn_nonlin ->
      F_related_subst ([(x, bind_typ t)]++E) lE
                   ([(x, v)]++gsubst) ([(x, v')]++gsubst') lgsubst lgsubst' rsubst dsubst dsubst'
  | F_related_subst_ltyp :
    (*
      gsubst ~ gsubst' : genv | rsubst, dsubst, dsubst'
      e ~ e' : t | rho_subst
     -----------------------------------------------------------------
      (gsubst, x->e) ~ (gsubst',x->e') : (genv, x:t) | rho_subst, dsubst, dsubst'
    *)
    forall (E:env)(lE:lenv)(gsubst gsubst' lgsubst lgsubst':gamma_subst) (v v':exp) (t:typ) (rsubst:rho_subst) (dsubst dsubst':delta_subst) (x:atom),
      F_related_subst E lE gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst'->
      typing nil nil v (apply_delta_subst_typ dsubst t) ->
      typing nil nil v' (apply_delta_subst_typ dsubst' t) ->
      F_related_values t rsubst dsubst dsubst' v v' ->
      x `notin` ((fv_env E) `union` (fv_lenv lE) `union` (fv_tt t)) ->
      wf_typ E t kn_lin ->
      F_related_subst E ([(x, lbind_typ t)]++lE)
                   gsubst gsubst' ([(x, v)]++lgsubst) ([(x, v')]++lgsubst') rsubst dsubst dsubst'
      .

Tactic Notation "F_related_subst_cases" tactic(first) tactic(c) :=
  first;
  [ c "F_related_subst_empty" |
    c "F_related_subst_kind" |
    c "F_related_subst_typ" | 
    c "F_related_subst_ltyp" ].

(** * Relations Subst *)
Inductive F_Rsubst : env-> rho_subst-> delta_subst -> delta_subst -> Prop:=
  | F_Rsubst_empty :
    (*
      empty |- rho_nil \in delta_nil <-> delta_nil
    *)
      F_Rsubst nil rho_nil delta_nil delta_nil
  | F_Rsubst_rel :
    (*
      env |- rho_subst \in delta_subst <-> delta_subst'
      R \in t <-> t'
     -----------------------------------------------------------------
      env, X |- (rho_subst, X->R) \in (delta_subst, X->t) <-> (delta_subst', X->t')
    *)
    forall (E:env) (rsubst:rho_subst) (dsubst:delta_subst) (dsubst':delta_subst) R t t' X K,
      F_Rsubst E rsubst dsubst dsubst' ->
      wfr R t t' K ->
      X `notin` (fv_env E) ->
      F_Rsubst ([(X, bind_kn K)]++E) ([(X, R)]++rsubst) ([(X, t)]++dsubst) ([(X, t')]++dsubst')
  | F_Rsubst_typ :
    (*
      env |- rho_subst \in delta_subst <-> delta_subst'
     -----------------------------------------------------------------
      env, x~:T |- rho_subst \in delta_subst <-> delta_subst'
    *)
    forall (E:env) (rsubst:rho_subst) (dsubst:delta_subst) (dsubst':delta_subst) x T,
      F_Rsubst E rsubst dsubst dsubst' ->
      wf_typ E T kn_nonlin ->
      x `notin` (fv_env E) ->
      F_Rsubst ([(x, bind_typ T)]++E) rsubst dsubst dsubst'
      .

Tactic Notation "F_Rsubst_cases" tactic(first) tactic(c) :=
  first;
  [ c "F_Rsubst_empty" |
    c "F_Rsubst_rel" |
    c "F_Rsubst_typ" ].

(** * SystemF Relations *)
Definition F_Rel t rsubst (dsubst dsubst':delta_subst) v v' :=
   F_related_values t rsubst dsubst dsubst' v v'
  .

Hint Constructors F_related_subst F_Rsubst.

(* ********************************************************************** *)
(* Fvalue simplification *)
Lemma F_related_values_bvar_eq: forall i (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp),
  F_related_values (typ_bvar i) rsubst dsubst dsubst' v v' <-> False.
Proof. 
  intros.
  unfold_sub F_related_values (typ_bvar i).
  split; auto.
Qed.

Lemma F_related_values_bvar_leq: forall i (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp),
  F_related_values (typ_bvar i) rsubst dsubst dsubst' v v' -> False.
Proof. 
  intros.
  destruct (@F_related_values_bvar_eq i rsubst dsubst dsubst' v v'); auto.
Qed.

Lemma F_related_values_bvar_req: forall i (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp),
  False -> 
  F_related_values (typ_bvar i) rsubst dsubst dsubst' v v'.
Proof. 
  intros.
  destruct (@F_related_values_bvar_eq i rsubst dsubst dsubst' v v'); auto.
Qed.

Lemma F_related_values_fvar_eq: forall X (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp),
  F_related_values (typ_fvar X) rsubst dsubst dsubst' v v' <->
    exists R,
     (binds X R rsubst) /\ (value v) /\ (value v') /\ (R v v')
  .
Proof. 
  intros.
  unfold_sub F_related_values (typ_fvar X).
  split; auto.
Qed.

Lemma F_related_values_fvar_leq: forall X (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp),
  F_related_values (typ_fvar X) rsubst dsubst dsubst' v v' ->
    exists R,
      (binds X R rsubst) /\ (value v) /\ (value v') /\ (R v v')
  .
Proof. 
  intros.
  destruct (@F_related_values_fvar_eq X rsubst dsubst dsubst' v v'); auto.
Qed.

Lemma F_related_values_fvar_req: forall X (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp),
  (exists R,
    (binds X R rsubst) /\ (value v) /\ (value v') /\ (R v v')) ->
  F_related_values (typ_fvar X) rsubst dsubst dsubst' v v'.
Proof. 
  intros.
  destruct (@F_related_values_fvar_eq X rsubst dsubst dsubst' v v'); auto.
Qed.

Lemma F_related_values_arrow_eq: forall (t1 t2:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) K,
  F_related_values (typ_arrow K t1 t2) rsubst dsubst dsubst' v v'
  <->
  (
    (value v) /\ (value v') /\
    (forall x x',
     typing nil nil x (apply_delta_subst_typ dsubst t1) ->
     typing nil nil x' (apply_delta_subst_typ dsubst' t1) ->
     F_related_values t1 rsubst dsubst dsubst' x x'
     ->
     (exists u, exists u',
      normalize (exp_app v x) u /\
      normalize (exp_app v' x') u' /\
      F_related_values t2 rsubst dsubst dsubst' u u')
    )
  )
   .
Proof. 
  intros.
  unfold_sub F_related_values (typ_arrow K t1 t2).
  split; intros H; decompose [and] H. 
    split; auto.
    split; auto.
Qed.

Lemma F_related_values_arrow_leq: forall (t1 t2:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) K,
  F_related_values (typ_arrow K t1 t2) rsubst dsubst dsubst' v v'
  ->
  (
    (value v) /\ (value v') /\
    (forall x x',
     typing nil nil x (apply_delta_subst_typ dsubst t1) ->
     typing nil nil x' (apply_delta_subst_typ dsubst' t1) ->
     F_related_values t1 rsubst dsubst dsubst' x x'
     ->
     (exists u, exists u',
      normalize (exp_app v x) u /\
      normalize (exp_app v' x') u' /\
      F_related_values t2 rsubst dsubst dsubst' u u')
    )
  )
   .
Proof. 
  intros.
  destruct (@F_related_values_arrow_eq t1 t2 rsubst dsubst dsubst' v v' K); auto.
Qed.

Lemma F_related_values_arrow_req: forall (t1 t2:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) K,
  (
    (value v) /\ (value v') /\
    (forall x x',
     typing nil nil x (apply_delta_subst_typ dsubst t1) ->
     typing nil nil x' (apply_delta_subst_typ dsubst' t1) ->
     F_related_values t1 rsubst dsubst dsubst' x x'
     ->
     (exists u, exists u',
      normalize (exp_app v x) u /\
      normalize (exp_app v' x') u' /\
      F_related_values t2 rsubst dsubst dsubst' u u')
    )
  ) ->
  F_related_values (typ_arrow K t1 t2) rsubst dsubst dsubst' v v'
   .
Proof. 
  intros.
  destruct (@F_related_values_arrow_eq t1 t2 rsubst dsubst dsubst' v v' K); auto.
Qed.

Lemma F_related_values_all_eq: forall (t1:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) K,
  F_related_values (typ_all K t1) rsubst dsubst dsubst' v v'
  <->
      (
      (value v) /\ (value v') /\
      (exists L,
         (forall (X:atom) t2 t2' R (Fr:X `notin` L),
         wfr R t2 t2' K ->
          X `notin` ((dom rsubst) `union` (fv_tt t1)) ->
          (exists w, exists w',
          normalize (exp_tapp v t2) w /\
          normalize (exp_tapp v' t2') w' /\
          F_related_values (open_tt t1 X)
                           ([(X, R)]++rsubst)
                           ([(X, t2)]++dsubst)
                           ([(X, t2')]++dsubst')
                            w w')
        ))
      )
  .
Proof. 
  intros.
  unfold_sub F_related_values (typ_all K t1).
  split; intros H; decompose [and] H; clear H.
    destruct H3 as [L H3].
    repeat(split; auto).
    exists L.
    intros X t2 t2' R Hfv Hwfr Hfv'.
    assert (J:=@H3 X t2 t2' R Hfv Hwfr Hfv').
    clear H3.
    destruct J as [w [w' [J1 [J2 J]]]]. 
    exists w. exists w'.
    split; auto.

    split; auto.
Qed.

Lemma F_related_values_all_leq: forall (t1:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) K,
  F_related_values (typ_all K t1) rsubst dsubst dsubst' v v'
  ->
      (
      (value v) /\ (value v') /\
      (exists L,
         (forall (X:atom) t2 t2' R (Fr:X `notin` L),
         wfr R t2 t2' K ->
          X `notin` ((dom rsubst) `union` (fv_tt t1)) ->
          (exists w, exists w',
          normalize (exp_tapp v t2) w /\
          normalize (exp_tapp v' t2') w' /\
          F_related_values (open_tt t1 X)
                           ([(X, R)]++rsubst)
                           ([(X, t2)]++dsubst)
                           ([(X, t2')]++dsubst')
                            w w')
        ))
      )
  .
Proof. 
  intros.
  destruct (@F_related_values_all_eq t1 rsubst dsubst dsubst' v v' K); auto.
Qed.

Lemma F_related_values_all_req: forall (t1:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) K,
      (
      (value v) /\ (value v') /\
      (exists L,
         (forall (X:atom) t2 t2' R (Fr:X `notin` L),
         wfr R t2 t2' K ->
          X `notin` ((dom rsubst) `union` (fv_tt t1)) ->
          (exists w, exists w',
          normalize (exp_tapp v t2) w /\
          normalize (exp_tapp v' t2') w' /\
          F_related_values (open_tt t1 X)
                           ([(X, R)]++rsubst)
                           ([(X, t2)]++dsubst)
                           ([(X, t2')]++dsubst')
                            w w')
        ))
      )
  ->
  F_related_values (typ_all K t1) rsubst dsubst dsubst' v v'
  .
Proof. 
  intros.
  destruct (@F_related_values_all_eq t1 rsubst dsubst dsubst' v v' K); auto.
Qed.

Lemma F_related_values_with_eq: forall (t1 t2:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp),
  F_related_values (typ_with t1 t2) rsubst dsubst dsubst' v v'
  <->
    (value v) /\ (value v') /\
    (exists e1, exists e2, exists e1', exists e2',
      v = exp_apair e1 e2 /\
      v' = exp_apair e1' e2' /\
      (exists u1, exists u1',
       normalize e1 u1 /\
       normalize e1' u1' /\
       F_related_values t1 rsubst dsubst dsubst' u1 u1') /\
      (exists u2, exists u2',
       normalize e2 u2 /\
       normalize e2' u2' /\
       F_related_values t2 rsubst dsubst dsubst' u2 u2')
    )
   .
Proof. 
  intros.
  unfold_sub F_related_values (typ_with t1 t2).
  split; intros H; decompose [and] H; clear H.
    destruct H3 as [e1 [e2 [e1' [e2' [J1 [J2 J3]]]]]].
    repeat(split; auto).
    exists e1. exists e2. exists e1'. exists e2'.
    repeat(split; auto).

    split; auto.
Qed.

Lemma F_related_values_with_leq: forall (t1 t2:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp),
  F_related_values (typ_with t1 t2) rsubst dsubst dsubst' v v'
  ->
    (value v) /\ (value v') /\
    (exists e1, exists e2, exists e1', exists e2',
      v = exp_apair e1 e2 /\
      v' = exp_apair e1' e2' /\
      (exists u1, exists u1',
       normalize e1 u1 /\
       normalize e1' u1' /\
       F_related_values t1 rsubst dsubst dsubst' u1 u1') /\
      (exists u2, exists u2',
       normalize e2 u2 /\
       normalize e2' u2' /\
       F_related_values t2 rsubst dsubst dsubst' u2 u2')
    )
   .
Proof. 
  intros.
  destruct (@F_related_values_with_eq t1 t2 rsubst dsubst dsubst' v v'); auto.
Qed.

Lemma F_related_values_with_req: forall (t1 t2:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp),
    (value v) /\ (value v') /\
    (exists e1, exists e2, exists e1', exists e2',
      v = exp_apair e1 e2 /\
      v' = exp_apair e1' e2' /\
      (exists u1, exists u1',
       normalize e1 u1 /\
       normalize e1' u1' /\
       F_related_values t1 rsubst dsubst dsubst' u1 u1') /\
      (exists u2, exists u2',
       normalize e2 u2 /\
       normalize e2' u2' /\
       F_related_values t2 rsubst dsubst dsubst' u2 u2')
    )
  ->
  F_related_values (typ_with t1 t2) rsubst dsubst dsubst' v v'
   .
Proof. 
  intros.
  destruct (@F_related_values_with_eq t1 t2 rsubst dsubst dsubst' v v'); auto.
Qed.

(* ********************************************************************** *)
(** * Inversion *)

Lemma F_related_values_inversion: forall t v v' rsubst dsubst dsubst',
  F_related_values t rsubst dsubst dsubst' v v' ->
  ((value v)* (value v'))%type.
Proof.
  intros t v v' rsubst dsubst dsubst' H.
  (typ_cases (induction t) Case); intros.
  Case "typ_bvar".
  apply F_related_values_bvar_leq in H; auto. inversion H.
  Case "typ_fvar".
  apply F_related_values_fvar_leq in H.
  unfold In_rel in H.
  destruct H as [R [Hb [Hv [Hv' Hr]]]].
  split; auto.
  Case "typ_arrow".
  apply F_related_values_arrow_leq in H.
  decompose [and] H; subst; clear H; auto.
  Case "typ_all".
  apply F_related_values_all_leq in H.
  decompose [and] H; subst; clear H; auto.
  Case "typ_with".
  apply F_related_values_with_leq in H.
  decompose [and] H; subst; clear H; auto.
Qed.

Lemma F_Rsubst__wf_subst:
  forall (E:env) (rsubst:rho_subst) (dsubst:delta_subst) (dsubst':delta_subst),
  F_Rsubst E rsubst dsubst dsubst'  ->
  ((wf_delta_subst E dsubst) * (wf_delta_subst E dsubst') * (wf_rho_subst E rsubst))%type.
Proof.
  intros E rsubst dsubst dsubst' HRsub.
  (F_Rsubst_cases (induction HRsub) Case); try solve [split; auto].
  Case "F_Rsubst_rel".
    decompose [prod] IHHRsub.
    unfold wfr in H. decompose [and] H.
    split. split.
      apply wf_delta_subst_styp; auto.
      apply wf_delta_subst_styp; auto.
      apply wf_rho_subst_srel; auto.
  Case "F_Rsubst_typ".
    decompose [prod] IHHRsub. clear IHHRsub.
    split. split.
      apply wf_delta_subst_skip; auto.
      apply wf_delta_subst_skip; auto.
      apply wf_rho_subst_skip; auto.
Qed.

Lemma Frel_inversion: forall t rsubst dsubst dsubst' v v',
  F_Rel t rsubst dsubst dsubst' v v' ->
  ((value v)* (value v'))%type.
Proof.
  intros t rsubst dsubst dsubst' v v' Hrel.
  unfold F_Rel in Hrel.
  apply F_related_values_inversion in Hrel.
  assumption.
Qed.

Lemma F_related_subst__inversion:
  forall (E:env) (lE:lenv) (rsubst:rho_subst) (dsubst:delta_subst) (dsubst':delta_subst) gsubst gsubst' lgsubst lgsubst',
  F_related_subst E lE gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
  ((wf_delta_subst E dsubst) * (wf_delta_subst E dsubst') *
   (wf_lgamma_subst E lE dsubst gsubst lgsubst)* (wf_lgamma_subst E lE dsubst' gsubst' lgsubst') *
   (wf_rho_subst E rsubst) * (wf_env E))%type.
Proof.
  intros E lE rsubst dsubst dsubst' gsubst gsubst' lgsubst lgsubst' HRsub.
  (F_related_subst_cases (induction HRsub) Case).
    repeat (split; auto).
  Case "F_related_subst_kind".
    decompose [prod] IHHRsub.
    repeat (split; eauto using wfr_left_inv, wfr_right_inv).
      apply wf_delta_subst_styp; eauto using wfr_left_inv.
      apply wf_delta_subst_styp; eauto using wfr_right_inv.
      apply wf_lgamma_subst_skind; eauto using wfr_left_inv.
      apply wf_lgamma_subst_skind; eauto using wfr_right_inv.
      apply wf_rho_subst_srel; auto.
      apply wf_env_kn; auto.
  Case "F_related_subst_typ".
    decompose [prod] IHHRsub.
    repeat (split; eauto).
      apply wf_delta_subst_skip; auto. 
      apply wf_delta_subst_skip; auto. 
      apply wf_lgamma_subst_sval; auto. 
      apply wf_lgamma_subst_sval; auto. 
      apply wf_rho_subst_skip; auto.
      apply wf_env_typ; auto.
  Case "F_related_subst_ltyp".
    decompose [prod] IHHRsub.
    repeat (split; eauto).
      apply wf_lgamma_subst_slval; auto. 
      apply wf_lgamma_subst_slval; auto. 
Qed.

(* **************************************** *)
(** * Weaken and Stronger of SystemF Relations *)
Definition P_Frel_weaken_stronger (n:nat) := 
  ((forall t E E' v v' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 X R t2 t2' K,
  typ_size t = n ->
  (F_related_values t (rsubst'++rsubst) (dsubst0++dsubst) (dsubst'0++dsubst') v v' ->
  ddom_env E [=] dom dsubst ->
  ddom_env E [=] dom dsubst' ->
  ddom_env E' [=] dom dsubst0 ->
  ddom_env E' [=] dom dsubst'0 ->
  ddom_env E [=] dom rsubst ->
  ddom_env E' [=] dom rsubst' ->
  X `notin` (fv_env E `union` fv_env E' `union` (fv_tt t))->
  wfr R t2 t2' K ->
  wf_rho_subst (E'++E) (rsubst' ++ rsubst) ->
  wf_delta_subst (E'++E) (dsubst0 ++ dsubst) ->
  wf_delta_subst (E'++E) (dsubst'0 ++ dsubst') ->
  F_related_values t (rsubst'++[(X, R)]++rsubst) (dsubst0++[(X,t2)]++dsubst) (dsubst'0++[(X,t2')]++dsubst') v v' ))
  *
  (forall t E E' v v' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 X R t2 t2' K,
  typ_size t = n ->
  (F_related_values t (rsubst'++[(X, R)]++rsubst) (dsubst0++[(X,t2)]++dsubst) (dsubst'0++[(X,t2')]++dsubst') v v' ->
  ddom_env E [=] dom dsubst ->
  ddom_env E [=] dom dsubst' ->
  ddom_env E' [=] dom dsubst0 ->
  ddom_env E' [=] dom dsubst'0 ->
  ddom_env E [=] dom rsubst ->
  ddom_env E' [=] dom rsubst' ->
  X `notin` (fv_env E `union` fv_env E' `union` (fv_tt t))->
  wfr R t2 t2' K ->
  wf_rho_subst (E'++[(X,bind_kn K)]++E) (rsubst'++[(X,R)]++rsubst) ->
  wf_delta_subst (E'++[(X,bind_kn K)]++E) (dsubst0++[(X,t2)]++dsubst) ->
  wf_delta_subst (E'++[(X,bind_kn K)]++E) (dsubst'0++[(X,t2')]++dsubst') ->
  F_related_values t (rsubst' ++ rsubst) (dsubst0 ++ dsubst) (dsubst'0 ++ dsubst') v v')))%type
  .


Lemma _Frel_weaken_stronger:  forall n, P_Frel_weaken_stronger n.
Proof.
  intro n.
  apply lt_wf_ind. clear n.
  intros n H.
  unfold P_Frel_weaken_stronger in *.
  split.
  (* -> *)
  intros t E E' v v' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 X R t2 t2' K
     Htsize Hrel H2dsubst H2dsubst' H2dsubst0 H2dsubst'0 H2rsubst H2rsubst' Hfv Hwfr Hwf_rsubst Hwf_dsubst Hwf_dsubst'.
  (typ_cases (destruct t) Case).

  Case "typ_bvar". (*bvar*)
  apply F_related_values_bvar_leq in Hrel; auto.

  Case "typ_fvar". (* fvar *)
  apply F_related_values_fvar_leq in Hrel.
  apply F_related_values_fvar_req.
  unfold In_rel in Hrel.
  destruct Hrel as [R0 [Hb [Hv [Hv' Hr]]]]; subst; simpl.
  exists (R0).
  simpl_env.
    repeat(split; auto).

  Case "typ_arrow". (* arrow *)
  apply F_related_values_arrow_leq in Hrel.
  apply F_related_values_arrow_req.
  destruct Hrel as [Hv [Hv' Harrow]]; subst.
  repeat(split; simpl_env; auto).
     SCase "arrow".
     intros x x' Htypingx Htypingx' Harrow'.
     rename Harrow' into Hrel_wft1'.
     simpl_env in *.

     assert (typ_size t1 < typ_size (typ_arrow K t1 t3)) as G1. simpl. omega.
     apply H in G1. destruct G1 as [Hrel_wft1_wft1' Hrel_wft1'_wft1].
     simpl in Hfv.
     apply Hrel_wft1'_wft1 with (E:=E) (E':=E') (K:=K) in Hrel_wft1'; auto; simpl_env.
       SSCase "arrow".
       destruct (@Harrow x x') as [u [u' [Hnorm_vxu [Hnorm_v'x'u' Hrel_wft1]]]]; auto.
          apply typing_dsubst_stronger with (E:=E'++[(X,bind_kn K)]++E)(X:=X)(t:=t2); eauto using wfr_left_inv.
             eapply dsubst_weaken; eauto using wfr_left_inv.
          apply typing_dsubst_stronger with (E:=E'++[(X,bind_kn K)]++E)(X:=X)(t:=t2'); eauto using wfr_right_inv.
             eapply dsubst_weaken; eauto using wfr_right_inv.

       exists (u). exists (u'). repeat(split; auto).
       assert (typ_size t3 < typ_size (typ_arrow K t1 t3)) as G2. simpl. omega.
       apply H in G2. destruct G2 as [Hrel_wft2_wft2' Hrel_wft2'_wft2].
       simpl in Hfv.
       apply Hrel_wft2_wft2' with (E:=E) (E':=E') (K:=K) ; auto.
       SSCase "rsubst". eapply rsubst_weaken; eauto.
       SSCase "dsubst". eapply dsubst_weaken; eauto using wfr_left_inv.
       SSCase "dsubst'". eapply dsubst_weaken; eauto using wfr_right_inv.

  Case "typ_all". (* all *)
  apply F_related_values_all_leq in Hrel.
  apply F_related_values_all_req.
  destruct Hrel as [Hv [Hv' [L' Hall]]]; subst.
  repeat(split; simpl_env; auto).
     SCase "all".
     exists (L' `union` singleton X `union` fv_env E `union` fv_env E').
      intros X1 t3 t2'0 R0 Fr Hwfr' Hfv'.
      assert (X1 `notin` L') as Fr''. auto.
      destruct (@Hall X1 t3 t2'0 R0 Fr'') as [w0 [w'0 [Hnorm_vt2w0 [Hnorm_v't2'w'0 Hrel_wft]]]]; auto.
      exists (w0). exists (w'0). repeat(split; auto).
      assert (typ_size (open_tt t X1) < typ_size (typ_all k t)) as G. 
        simpl. rewrite open_tt_typ_size_eq. omega.
      apply H in G. destruct G as [Hrel_wft_wft' Hrel_wft'_wft].
      simpl_env in Hrel_wft_wft'. clear H Hrel_wft'_wft.
      apply Hrel_wft_wft' with (t0:=(open_tt t X1)) 
                               (E':=[(X1,bind_kn k)]++E')(E:=E)
                               (rsubst':=[(X1,R0)]++rsubst')(rsubst:=rsubst)
                               (dsubst0:=[(X1,t3)]++dsubst0)(dsubst:=dsubst)
                               (dsubst'0:=[(X1,t2'0)]++dsubst'0)(dsubst':=dsubst')
                               (v:=w0) (v':=w'0)
                               (X:=X) (R:=R) 
                               (t2:=t2) (t2':=t2') (K:=K)
                               ; simpl_env; auto; clear Hrel_wft_wft'.
          SSCase "fv".
          destruct_notin.
          simpl in *. auto using notin_fv_tt_open_tt.
          SSCase "dsubst".
          eapply dsubst_weaken_head; simpl_env; eauto using wfr_left_inv.
          SSCase "dsubst'".
          eapply dsubst_weaken_head; simpl_env; eauto using wfr_right_inv.

  Case "typ_with". (* with *)
  apply F_related_values_with_leq in Hrel.
  apply F_related_values_with_req.
  destruct Hrel as [Hv [Hv' [e1 [e2 [e1' [e2' [Heq [Heq' 
                                [[u1 [u1' [Hnorm_e1u1 [Hnorm_e1'u1' Hrel_wft1]]]] 
                                 [u2 [u2' [Hnorm_e2u2 [Hnorm_e2'u2' Hrel_wft2]]]]]
                              ]]]]]]]]; subst.
  repeat(split; auto; simpl_env in *).
     SCase "with".
     simpl in Hfv.
     exists (e1). exists (e2). exists (e1'). exists (e2'). repeat(split; auto).
       SSCase "with1".
       exists (u1). exists (u1').  repeat(split;auto).
       simpl_env in *.
       assert (typ_size t1 < typ_size (typ_with t1 t3)) as G1. simpl. omega.
       apply H in G1. destruct G1 as [Hrel_wft1_wft1' Hrel_wft1'_wft1].
       simpl in Hfv.
       apply Hrel_wft1_wft1' with (E:=E) (E':=E') (K:=K) ; auto.
       SSCase "with2".
       exists (u2). exists (u2').  repeat(split; auto).
       assert (typ_size t3 < typ_size (typ_with t1 t3)) as G2. simpl. omega.
       apply H in G2. destruct G2 as [Hrel_wft2_wft2' Hrel_wft2'_wft2].
      simpl in Hfv.
      apply Hrel_wft2_wft2' with (E:=E) (E':=E') (K:=K) ; auto.

  (* <- *)
  intros t E E' v v' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 X R t2 t2' K
     Htsize Hrel H2dsubst H2dsubst' H2dsubst0 H2dsubst'0 H2rsubst H2rsubst' Hfv Hwfr Hwf_rsubst Hwf_dsubst Hwf_dsubst'.
  (typ_cases (destruct t) Case).

  Case "typ_bvar". (*bvar*)
  apply F_related_values_bvar_leq in Hrel; auto.

  Case "typ_fvar". (* fvar *)
  apply F_related_values_fvar_leq in Hrel.
  apply F_related_values_fvar_req.
  unfold In_rel in Hrel.
  destruct Hrel as [R0 [Hb [Hv [Hv' Hr]]]]; subst; simpl.
  exists (R0).
  repeat(split; auto).
      simpl_env in Hb. simpl in Hfv.
      analyze_binds Hb.

  Case "typ_arrow". (* arrow *)
  apply F_related_values_arrow_leq in Hrel.
  apply F_related_values_arrow_req.
  destruct Hrel as [Hv [Hv' Harrow]]; subst.
  repeat(split; simpl_env in *; auto).
     SCase "arrow".
     intros x x' Htypingx Htypingx' Harrow'.
     rename Harrow' into Hrel_wft1.
 
     assert (typ_size t1 < typ_size (typ_arrow K t1 t3)) as G1. simpl. omega.
     apply H in G1. destruct G1 as [Hrel_wft1_wft1' Hrel_wft1'_wft1].
     simpl in Hfv.
     apply Hrel_wft1_wft1' with (X:=X)(R:=R)(t2:=t2)(t2':=t2')(K:=K) (E:=E) (E':=E') in Hrel_wft1; auto; simpl_env.
       SSCase "arrow".
       destruct (@Harrow x x') as [u [u' [Hnorm_vxu [Hnorm_v'x'u' Hrel_wft1']]]]; auto.
          apply typing_dsubst_weaken with (E:=E'++E); eauto using wfr_left_inv.
               apply dsubst_stronger with (t:=t2) (X:=X) (K:=K); eauto using wfr_left_inv.
          apply typing_dsubst_weaken with (E:=E'++E); eauto using wfr_right_inv.
               apply dsubst_stronger with (t:=t2') (X:=X) (K:=K); eauto using wfr_right_inv.

       exists (u). exists (u'). repeat(split; auto).
       assert (typ_size t3 < typ_size (typ_arrow K t1 t3)) as G2. simpl. omega.
       apply H in G2. destruct G2 as [Hrel_wft2_wft2' Hrel_wft2'_wft2].
       simpl in Hfv.
       apply Hrel_wft2'_wft2 with (X:=X)(R:=R)(t2:=t2)(t2':=t2') (K:=K)(E:=E)(E':=E'); auto.
       SSCase "rsubst". apply rsubst_stronger  in Hwf_rsubst; eauto.
       SSCase "dsubst". apply dsubst_stronger with (t:=t2) in Hwf_dsubst; eauto using wfr_left_inv.
       SSCase "dsubst'". apply dsubst_stronger with (t:=t2') in Hwf_dsubst'; eauto using wfr_right_inv.

  Case "typ_all". (* all *)
  apply F_related_values_all_leq in Hrel.
  apply F_related_values_all_req.
  destruct Hrel as [Hv [Hv' [L' Hall]]]; subst.
  repeat(split; auto; simpl_env in *).
     SCase "all".
      exists (L' `union` singleton X  `union` fv_env E `union` fv_env E').
      intros X1 t3 t2'0 R0 Fr Hwfr' Hfv'.
      assert (X1 `notin` L') as Fr''. auto.
      destruct (@Hall X1 t3 t2'0 R0 Fr'') as [w0 [w'0 [Hnorm_vt2w0 [Hnorm_v't2'w'0 Hrel_wft]]]]; auto.
          destruct_notin. simpl_env. simpl. auto.
      exists (w0). exists (w'0). repeat(split; auto).
      assert (typ_size (open_tt t X1) < typ_size (typ_all k t)) as G. 
        simpl. rewrite open_tt_typ_size_eq. omega.
      apply H in G. destruct G as [Hrel_wft_wft' Hrel_wft'_wft].
      simpl_env in Hrel_wft'_wft. clear H Hrel_wft_wft'.
      apply Hrel_wft'_wft with (t0:=(open_tt t X1)) 
                               (E':=[(X1,bind_kn k)]++E')(E:=E)
                               (rsubst':=[(X1,R0)]++rsubst')(rsubst:=rsubst)
                               (dsubst0:=[(X1,t3)]++dsubst0)(dsubst:=dsubst)
                               (dsubst'0:=[(X1,t2'0)]++dsubst'0)(dsubst':=dsubst')
                               (v:=w0) (v':=w'0)
                               (X:=X) (R:=R) 
                               (t2:=t2) (t2':=t2') (K:=K)
                               ; simpl_env; auto; clear Hrel_wft'_wft.
          SSCase "fv".
          destruct_notin. simpl in NotInTac5. simpl.
          auto using notin_fv_tt_open_tt.
          SSCase "dsubst".
          simpl_env. eapply dsubst_weaken_head; simpl_env; eauto using wfr_left_inv.
          SSCase "dsubst'".
          simpl_env. eapply dsubst_weaken_head; simpl_env; eauto using wfr_right_inv.

  Case "typ_with". (* with *)
  apply F_related_values_with_leq in Hrel.
  apply F_related_values_with_req.
  destruct Hrel as [Hv [Hv' [e1 [e2 [e1' [e2' [Heq [Heq' 
                                [[u1 [u1' [Hnorm_e1u1 [Hnorm_e1'u1' Hrel_wft1]]]] 
                                 [u2 [u2' [Hnorm_e2u2 [Hnorm_e2'u2' Hrel_wft2]]]]]
                              ]]]]]]]]; subst.
  repeat(split; auto; simpl_env in *).
     SCase "with".
     simpl in Hfv.
     exists (e1). exists (e2). exists (e1'). exists (e2'). repeat(split; auto).
       SSCase "with1".
       exists (u1). exists (u1'). repeat(split; auto).
       simpl_env in *.
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

Lemma Frel_weaken:  forall t E E' v v' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 X R t2 t2' K,
  ((F_related_values t (rsubst'++rsubst) (dsubst0++dsubst) (dsubst'0++dsubst') v v' ->
  ddom_env E [=] dom dsubst ->
  ddom_env E [=] dom dsubst' ->
  ddom_env E' [=] dom dsubst0 ->
  ddom_env E' [=] dom dsubst'0 ->
  ddom_env E [=] dom rsubst ->
  ddom_env E' [=] dom rsubst' ->
  X `notin` (fv_env E `union` fv_env E' `union` (fv_tt t))->
  wfr R t2 t2' K ->
  wf_rho_subst (E'++E) (rsubst'++rsubst) ->
  wf_delta_subst (E'++E) (dsubst0++dsubst) ->
  wf_delta_subst (E'++E) (dsubst'0++dsubst') ->
  F_related_values t (rsubst'++[(X, R)]++rsubst) (dsubst0++[(X, t2)]++dsubst) (dsubst'0++[(X, t2')]++dsubst') v v' ))
  .
Proof.
  intros.
  assert (P_Frel_weaken_stronger (typ_size t)).
    apply (@_Frel_weaken_stronger (typ_size t)).
  unfold P_Frel_weaken_stronger in H11.
  decompose [prod] H11.
  eapply a; eauto.
Qed.

Lemma Frel_weaken_head:  forall t E v v' rsubst dsubst dsubst' X R t2 t2' K,
  ((F_related_values t rsubst dsubst dsubst' v v' ->
  ddom_env E [=] dom dsubst ->
  ddom_env E [=] dom dsubst' ->
  ddom_env E [=] dom rsubst ->
  X `notin` (fv_env E `union` (fv_tt t))->
  wfr R t2 t2' K ->
  wf_rho_subst E rsubst ->
  wf_delta_subst E dsubst ->
  wf_delta_subst E dsubst' ->
  F_related_values t ([(X, R)]++rsubst) ([(X, t2)]++dsubst) ([(X, t2')]++dsubst') v v' ))
  .
Proof.
  intros.
  apply Frel_weaken with (E:=E) (E':=@nil (atom*binding)) (X:=X) (R:=R)
                            (t:=t) (K:=K)
                            (rsubst:=rsubst) (rsubst':=rho_nil)
                            (dsubst:=dsubst) (dsubst0:=delta_nil)
                            (dsubst':=dsubst') (dsubst'0:=delta_nil)
                            (t2:=t2) (t2':=t2') (v:=v) (v':=v'); auto.
Qed.

Lemma Frel_stronger:  forall t E E' v v' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 X R t2 t2' K,
  F_related_values t (rsubst'++[(X,R)]++rsubst) (dsubst0++[(X,t2)]++dsubst) (dsubst'0++[(X,t2')]++dsubst') v v' ->
  ddom_env E [=] dom dsubst ->
  ddom_env E [=] dom dsubst' ->
  ddom_env E' [=] dom dsubst0 ->
  ddom_env E' [=] dom dsubst'0 ->
  ddom_env E [=] dom rsubst ->
  ddom_env E' [=] dom rsubst' ->
  X `notin` (fv_env E `union` fv_env E' `union` (fv_tt t))->
  wfr R t2 t2' K ->
  wf_rho_subst (E'++[(X,bind_kn K)]++E) (rsubst'++[(X,R)]++rsubst) ->
  wf_delta_subst (E'++[(X,bind_kn K)]++E) (dsubst0++[(X,t2)]++dsubst) ->
  wf_delta_subst (E'++[(X,bind_kn K)]++E) (dsubst'0++[(X,t2')]++dsubst') ->
  F_related_values t (rsubst'++rsubst) (dsubst0++dsubst) (dsubst'0++dsubst') v v'
  .
Proof.
  intros.
  assert (P_Frel_weaken_stronger (typ_size t)).
    apply (@_Frel_weaken_stronger (typ_size t)).
  unfold P_Frel_weaken_stronger in H11.
  decompose [prod] H11.
  eapply b; eauto.
Qed.

Lemma bindsgE__bindsgsubst: forall E lE gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' x T,
    F_related_subst E lE gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
    binds x (bind_typ T) E ->
    wf_typ E T kn_nonlin ->
    x `notin` dom lgsubst /\ x `notin` dom lgsubst' /\
    (exists v, exists v',
                ((binds x (v) gsubst)
                *(binds x (v') gsubst')
                *(typing nil nil v (apply_delta_subst_typ dsubst T))*(typing nil nil v' (apply_delta_subst_typ dsubst' T))
                *(F_related_values T rsubst dsubst dsubst' v v'))%type)
    .
Proof.
  intros E lE gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' x T Hrel_sub Hbinds Hwft.
  generalize dependent x.
  generalize dependent T.
  (F_related_subst_cases (induction Hrel_sub) Case); intros.
  Case "F_related_subst_empty".
    inversion Hbinds.
  Case "F_related_subst_kind".
    analyze_binds Hbinds.
    apply F_related_subst__inversion in Hrel_sub. 
    destruct Hrel_sub as [[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe].
    assert (wf_typ E T kn_nonlin) as WFT'.
      apply wf_typ_from_binds_typ with (E:=E) (x:=x); auto.
    assert (X `notin` fv_tt T); eauto using notin_fv_wf.
    apply IHHrel_sub in BindsTac; auto.
    destruct BindsTac as [J1 [J2 [v [v' [[[[Hbinds Hbinds'] Htt] Htt'] Hrel]]]]].
    split; auto.
    split; auto.
       exists (v). exists (v').
       split; simpl; auto.
         rewrite <- subst_tt_fresh; auto.
       split; simpl; auto.
         rewrite <- subst_tt_fresh; auto.
         apply Frel_weaken_head with (E:=E) (X:=X) (R:=R) (K:=K)
                            (t:=T) (rsubst:=rsubst) (dsubst:=dsubst) (dsubst':=dsubst') 
                            (t2:=t) (t2':=t') (v:=v) (v':=v'); auto using dom_delta_subst, dom_rho_subst.

  Case "F_related_subst_typ".
    apply F_related_subst__inversion in Hrel_sub. 
    destruct Hrel_sub as [[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe].
    destruct (x0 == x); subst.
    SCase "x0=x".
      rewrite_env (nil ++ [(x, bind_typ t)] ++ E) in Hbinds.
      apply binds_mid_eq in Hbinds. inversion Hbinds. subst.
      split.
       apply wf_lgamma_subst__nfv with (x:=x) in Hwflg; auto.
         decompose [and] Hwflg; auto.
      split.
       apply wf_lgamma_subst__nfv with (x:=x) in Hwflg'; auto.
         decompose [and] Hwflg; auto.
      exists (v). exists (v').
      repeat(split; auto).
         SSCase "uniq".
         simpl_env. apply uniq_push; eauto.
    SCase "x0<>x".
      analyze_binds Hbinds.
        assert (wf_typ E T kn_nonlin) as WFT0'.
          apply wf_typ_strengthening with (E:=E) (F:=@nil (atom*binding)) (x:=x) (U:=t); auto.

        apply (@IHHrel_sub T WFT0' x0) in BindsTac.
        destruct BindsTac as [J1 [J2 [v0 [v'0 [[[[Hbinds1 Hbinds2] Htt] Htt'] Hrel]]]]].
        split.
         apply wf_lgamma_subst__nfv with (x:=x) in Hwflg; auto.
           decompose [and] Hwflg; auto.
        split.
         apply wf_lgamma_subst__nfv with (x:=x) in Hwflg'; auto.
           decompose [and] Hwflg; auto.
         exists (v0). exists (v'0).
         repeat(split; auto).

  Case "F_related_subst_ltyp".
    apply F_related_subst__inversion in Hrel_sub. 
    destruct Hrel_sub as [[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe].
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

Lemma lbindsgE__lbindsgsubst: forall E lE gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' x T,
    F_related_subst E lE gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
    binds x (lbind_typ T) lE ->
    wf_typ E T kn_lin ->
    x `notin` dom gsubst /\ x `notin` dom gsubst' /\
    (exists v, exists v',
                ((binds x (v) lgsubst)
                *(binds x (v') lgsubst')
                *(typing nil nil v (apply_delta_subst_typ dsubst T))*(typing nil nil v' (apply_delta_subst_typ dsubst' T))
                *(F_related_values T rsubst dsubst dsubst' v v'))%type)
    .
Proof.
  intros E lE gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' x T Hrel_sub Hbinds Hwft.
  generalize dependent x.
  generalize dependent T.
  (F_related_subst_cases (induction Hrel_sub) Case); intros.
  Case "F_related_subst_empty".
    inversion Hbinds.
  Case "F_related_subst_kind".
    analyze_binds Hbinds.
    apply F_related_subst__inversion in Hrel_sub. 
    destruct Hrel_sub as [[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe].
    assert (wf_typ E T kn_lin) as WFT'.
      apply wf_typ_from_lbinds_typ with (E:=E)(lE:=lE)(x:=x); auto.
        apply wf_lgamma_subst__wf_lenv in Hwflg.
        destruct Hwflg; auto.
    assert (X `notin` fv_tt T); eauto using notin_fv_wf.
    apply IHHrel_sub in Hbinds; auto.
    destruct Hbinds as [J1 [J2 [v [v' [[[[Hbinds Hbinds'] Htt] Htt'] Hrel]]]]].
    split; auto.
    split; auto.
       exists (v). exists (v').
       split; simpl; auto.
         rewrite <- subst_tt_fresh; auto.
       split; simpl; auto.
         rewrite <- subst_tt_fresh; auto.
         apply Frel_weaken_head with (E:=E) (X:=X) (R:=R) (K:=K)
                            (t:=T) (rsubst:=rsubst) (dsubst:=dsubst) (dsubst':=dsubst') 
                            (t2:=t) (t2':=t') (v:=v) (v':=v'); auto using dom_delta_subst, dom_rho_subst.

  Case "F_related_subst_typ".
    apply F_related_subst__inversion in Hrel_sub. 
    destruct Hrel_sub as [[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe].
    assert (J:=Hbinds).
    assert (wf_typ E T kn_lin) as WFT0'.
      apply wf_typ_strengthening with (E:=E) (F:=@nil (atom*binding)) (x:=x) (U:=t); auto.
    apply (@IHHrel_sub T WFT0' x0) in Hbinds.
    destruct Hbinds as [J1 [J2 [v0 [v'0 [[[[Hbinds1 Hbinds2] Htt] Htt'] Hrel]]]]].
    split. 
      apply binds_In in J.
      rewrite dom_app.
      destruct (x0 == x); subst; auto.
         contradict J; auto.
    split.
      apply binds_In in J.
      rewrite dom_app.
      destruct (x0 == x); subst; auto.
         contradict J; auto.

      exists (v0). exists (v'0).
      repeat(split; auto).

  Case "F_related_subst_ltyp".
    apply F_related_subst__inversion in Hrel_sub. 
    destruct Hrel_sub as [[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe].
    destruct (x0 == x); subst.
    SCase "x0=x".
      rewrite_env (nil ++ [(x, lbind_typ t)] ++ lE) in Hbinds.
      apply binds_mid_eq in Hbinds. inversion Hbinds. subst.
      split.
       apply wf_lgamma_subst__nfv with (x:=x) in Hwflg; auto.
         decompose [and] Hwflg; auto.
      split.
       apply wf_lgamma_subst__nfv with (x:=x) in Hwflg'; auto.
         decompose [and] Hwflg; auto.

       exists (v). exists (v').
       repeat(split; auto).
         simpl_env. apply uniq_push; eauto.
           apply wf_lgamma_subst__uniq in Hwflg.
           decompose [and] Hwflg; auto.
    SCase "x0<>x".
      analyze_binds Hbinds.
        apply (@IHHrel_sub T Hwft x0) in BindsTac.
        destruct BindsTac as [J1 [J2 [v0 [v'0 [[[[Hbinds Hbinds'] Htt] Htt'] Hrel]]]]].
        split.
         apply wf_lgamma_subst__nfv with (x:=x) in Hwflg; auto.
           decompose [and] Hwflg; auto.
        split.
         apply wf_lgamma_subst__nfv with (x:=x) in Hwflg'; auto.
           decompose [and] Hwflg; auto.

         exists (v0). exists (v'0).
         repeat(split; auto).
Qed.

Definition F_Rel__R (t:typ) (E:env) (rsubst:rho_subst) dsubst dsubst' (R:rel) :=
  wf_delta_subst E dsubst /\  wf_delta_subst E dsubst' /\  wf_rho_subst E rsubst /\
  (forall v v',
    ((F_Rel t rsubst dsubst dsubst' v v' -> R v v') 
   * (R v v'->F_Rel t rsubst dsubst dsubst' v v')) % type)
  .

Lemma F_Rel__R__wfr: forall (E:env) (t:typ) (rsubst:rho_subst) dsubst dsubst' (R:rel) K,
  F_Rel__R t E rsubst dsubst dsubst' R -> 
  wf_typ E t K ->
  wfr R (apply_delta_subst_typ dsubst t) (apply_delta_subst_typ dsubst' t) K.
Proof.
  intros E t rsubst dsubst dsubst' R K Hr_eq Hwft.
  unfold F_Rel__R in Hr_eq. unfold wfr. 
  destruct Hr_eq as [Hwfd [Hwfd' [Hwfr Hr_eq]]].
  split.  apply wft_subst with (E:=E); auto.
              apply wft_subst with (E:=E); auto.
Qed.

(** * Subst of SystemF Relations *)
Definition P_parametricity_subst_value (n:nat) := 
  forall t E E' e e' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 X R t2 k K Q,
  typ_size t = n ->
  wf_typ (E'++[(X, bind_kn Q)]++E) (open_tt_rec k (typ_fvar X) t) K ->
  wf_typ (E'++E) (open_tt_rec k t2 t) K ->
  wf_typ (E'++E) t2 Q ->
  F_Rel__R t2 (E'++E) (rsubst'++rsubst) (dsubst0++dsubst) (dsubst'0++dsubst') R ->
  X `notin` (fv_env E `union` fv_env E' `union` (fv_tt t) `union` (fv_te e) `union` (fv_te e'))-> 
  ddom_env E [=] dom dsubst ->
  ddom_env E [=] dom dsubst' ->
  ddom_env E' [=] dom dsubst0 ->
  ddom_env E' [=] dom dsubst'0 ->
  ddom_env E [=] dom rsubst ->
  ddom_env E' [=] dom rsubst' ->
  (F_related_values (open_tt_rec k (typ_fvar X) t) 
               (rsubst'++[(X, R)]++rsubst) 
               (dsubst0++[(X,(apply_delta_subst_typ (dsubst0++dsubst) t2))]++dsubst) 
               (dsubst'0++[(X,(apply_delta_subst_typ (dsubst'0++dsubst') t2))]++dsubst') 
                e e' ->
  wf_rho_subst (E'++[(X, bind_kn Q)]++E) (rsubst'++[(X, R)]++rsubst) ->
  wf_delta_subst (E'++[(X, bind_kn Q)]++E) (dsubst0++[(X,(apply_delta_subst_typ (dsubst0++dsubst) t2))]++dsubst) -> 
  wf_delta_subst (E'++[(X, bind_kn Q)]++E) (dsubst'0++[(X,(apply_delta_subst_typ (dsubst'0++dsubst') t2))]++dsubst') -> 
  F_related_values (open_tt_rec k t2 t) (rsubst'++rsubst) (dsubst0++dsubst) (dsubst'0++dsubst') e e')
  *
  (F_related_values (open_tt_rec k  t2 t) (rsubst'++rsubst) (dsubst0++dsubst) (dsubst'0++dsubst') e e'->
  wf_rho_subst (E'++E) (rsubst'++rsubst) ->
  wf_delta_subst (E'++E) (dsubst0++dsubst) -> 
  wf_delta_subst (E'++E) (dsubst'0++dsubst') -> 
  F_related_values (open_tt_rec k (typ_fvar X) t) 
              (rsubst'++[(X, R)]++rsubst) 
              (dsubst0++[(X,(apply_delta_subst_typ (dsubst0++dsubst) t2))]++dsubst) 
              (dsubst'0++[(X,(apply_delta_subst_typ (dsubst'0++dsubst') t2))]++dsubst')
              e e')
  .

Lemma _parametricity_subst_value :  forall n, P_parametricity_subst_value n.
Proof.
  intro n.
  apply lt_wf_ind. clear n.
  intros n H.
  unfold P_parametricity_subst_value in *.
  intros t E E' e e' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 X R t2 k K Q
         Htsize Hwft Hwft' Hwft2 Hr_eq Hfv H1dsubst  H1dsubst'  H1dsubst0  H1dsubst'0 H1rsubst  H1rsubst'.
  assert (wfr R (apply_delta_subst_typ (dsubst0++dsubst) t2) (apply_delta_subst_typ (dsubst'0++dsubst') t2) Q) as WFR. 
    eapply F_Rel__R__wfr; eauto.
  split.
  (* -> *)
  intros Hrel Hwfr Hwfd Hwfd'.
  (typ_cases (induction t) Case); simpl in Hrel; simpl; simpl_env in *.

  Case "typ_bvar". (* bvar *)
  destruct (k==n0); subst.
    SCase "fvar".
    apply F_related_values_fvar_leq in Hrel.
    destruct Hrel as [R0 [Hb [Hv [Hv' Hr]]]]; subst; simpl.
    assert (R=R0).
      simpl_env in Hb.
      apply binds_mid_eq in Hb; auto.
      simpl_env in Hwfr. apply wf_rho_subst__uniq in Hwfr. decompose [and] Hwfr; auto.
    subst.
    assert (
      (F_Rel t2 (rsubst'++rsubst) (dsubst0++dsubst) (dsubst'0++dsubst') e e' -> R0 e e') *
      (R0 e e' -> F_Rel t2 (rsubst'++rsubst) (dsubst0++dsubst) (dsubst'0++dsubst') e e')
      ) as HR'.
      unfold F_Rel__R in Hr_eq. decompose [and] Hr_eq. auto.
    destruct HR' as [Hrel_r Hr_rel].
    apply Hr_rel in Hr; auto.
    SCase "bvar".
    apply F_related_values_bvar_leq in Hrel; auto.

  Case "typ_fvar". (* fvar *)
  apply F_related_values_fvar_leq in Hrel.
  apply F_related_values_fvar_req.  
  destruct Hrel as [R0 [Hb [Hv [Hv' Hr]]]]; subst; simpl.
  exists (R0).
  repeat(split; auto).
    simpl in Hfv.  analyze_binds Hb.

  Case "typ_arrow". (* arrow *)
  apply F_related_values_arrow_leq in Hrel.
  apply F_related_values_arrow_req.  
  destruct Hrel as [Hv [Hv' Harrow]]; subst.
  simpl in Hfv.
  repeat(split; auto; simpl_env in *).
         SCase "arrow". 
         intros x x' Htypingx Htypingx' Harrow'.
         rename Harrow' into Hrel_wft1'.
         destruct (@Harrow x x') as [u [u' [Hnorm_vxu [Hnorm_v'x'u' Hrel_wft1]]]]; auto.
           SSCase "typing". eapply m_typing_var_stronger; eauto using wfr_left_inv.
           SSCase "typing". eapply m_typing_var_stronger; eauto using wfr_right_inv.
           SSCase "arrow_left". 
           assert (typ_size t1 < typ_size (typ_arrow k0 t1 t3)) as G1. simpl. omega.
           apply H with (E:=E) (E':=E') (e:=x) (e':=x') (t:=t1)
                        (rsubst:=rsubst) (dsubst:=dsubst) (dsubst':=dsubst')
                        (X:=X) (R:=R) (t2:=t2) (k:=k) (K:=kn_lin) (Q:=Q)
                        (rsubst':=rsubst') (dsubst0:=dsubst0) (dsubst'0:=dsubst'0) in G1; auto.
              SSSCase "arrow_left". 
              destruct G1 as [Hrel_wft1_wft1' Hrel_wft1'_wft1].
              simpl in Hrel_wft1'_wft1. apply Hrel_wft1'_wft1 in Hrel_wft1'; auto.
                SSSSCase "rsubst". eapply rsubst_stronger; eauto.
                SSSSCase "dsubst". eapply dsubst_stronger; eauto using wfr_left_inv.
                SSSSCase "dsubst'". eapply dsubst_stronger; eauto using wfr_right_inv.
              SSSCase "wft". 
              simpl in Hwft. apply wft_arrow_inv in Hwft. destruct Hwft; auto.
              simpl in Hwft'. apply wft_arrow_inv in Hwft'. destruct Hwft'; auto.
              SSSCase "fv". 
              assert (X `notin` fv_te x). 
                eapply m_typing_normalization_fv with (e:=x); eauto.
                  unfold normalize. 
                  split; auto.
                    apply F_related_values_inversion in Hrel_wft1'.
                    decompose [prod] Hrel_wft1'; auto.
              assert (X `notin` fv_te x'). 
                eapply m_typing_normalization_fv with (e:=x'); eauto.
                  unfold normalize. 
                  split; auto.
                    apply F_related_values_inversion in Hrel_wft1'.
                    decompose [prod] Hrel_wft1'; auto.
              destruct_notin. auto.
         SSCase "arrow_right". 
         exists (u). exists (u'). 
         repeat(split; auto).
           assert (typ_size t3 < typ_size (typ_arrow k0 t1 t3)) as G2. simpl. omega.
           apply H with (E:=E) (E':=E') (e:=u) (e':=u') (t:=t3)
                        (rsubst:=rsubst) (dsubst:=dsubst) (dsubst':=dsubst')
                        (X:=X) (R:=R) (t2:=t2) (k:=k) (K:=kn_lin) (Q:=Q)
                        (rsubst':=rsubst') (dsubst0:=dsubst0) (dsubst'0:=dsubst'0) in G2; auto.
            destruct G2 as [Hrel_wft2_wft2' Hrel_wft2'_wft2]; auto.
            SSSCase "wft". 
            simpl in Hwft. apply wft_arrow_inv in Hwft. destruct Hwft; auto.
            simpl in Hwft'. apply wft_arrow_inv in Hwft'. destruct Hwft'; auto.
            SSSCase "fv". 
            assert (X `notin` fv_te u). eapply m_typing_normalization_arrow_fv_stronger with (e:=e) (x:=x) (t1:=t1); eauto using wfr_left_inv.
            assert (X `notin` fv_te u').  eapply m_typing_normalization_arrow_fv_stronger with (e:=e') (x:=x') (t1:=t1); eauto using wfr_right_inv.
            destruct_notin. auto.

  Case "typ_all". (* all *)
  assert (uniq (E'++[(X, bind_kn Q)]++E)) as Uniq.
    apply wf_delta_subst__uniq in Hwfd.
    decompose [and] Hwfd; auto.
  apply F_related_values_all_leq in Hrel.
  apply F_related_values_all_req.  
  destruct Hrel as [Hv [Hv' [L' Hall]]]; subst.
  repeat(split; auto; simpl_env in *).
       SCase "all".  
         assert (forall X,
           X `notin` dom (E'++E) `union` fv_tt (open_tt_rec (S k) t2 t) ->
           wf_typ ([(X, bind_kn k0)]++E'++E) (open_tt (open_tt_rec (S k) t2 t) X) kn_lin) as w'.
           simpl in Hwft'. 
           eapply wft_all_inv; eauto.
         assert (forall Y,
           Y `notin` dom (E'++[(X, bind_kn Q)]++E) `union` fv_tt (open_tt_rec (S k) X t) ->
           wf_typ ([(Y, bind_kn k0)]++E'++[(X, bind_kn Q)]++E) (open_tt (open_tt_rec (S k) X t) Y) kn_lin) as w.
           simpl in Hwft. 
           eapply wft_all_inv; eauto.
         exists (L' `union` fv_env E `union` fv_env E' `union` dom E `union` dom E' `union` (fv_tt (open_tt_rec (S k) (typ_fvar X) t)) `union` singleton X  `union` (fv_tt t2)).
         intros X4 t3 t2' R0 Fr Hwfr' Hfv'.
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
         assert (wf_typ ([(X4, bind_kn k0)]++E'++E) (open_tt_rec (S k)  t2 (open_tt t X4)) kn_lin) as WFT'. 
           rewrite <- G''.
           apply w' with (X:=X4); auto.
         assert (wf_typ ([(X4, bind_kn k0)]++E'++[(X,bind_kn Q)]++E) (open_tt_rec (S k)  X (open_tt t X4)) kn_lin) as WFT. 
           rewrite <- G'.
           apply w with (Y:=X4); auto.
         assert (wf_typ ([(X4, bind_kn k0)]++E'++E) t2 Q) as WFT2'. 
           apply wf_rho_subst__uniq in Hwfr. decompose [and] Hwfr.
           eapply wf_typ_weaken_head; eauto.

         assert (typ_size (open_tt t X4) < typ_size (typ_all k0 t)) as G. 
          simpl. rewrite open_tt_typ_size_eq. omega.
         apply H with (E:=E) (E':=[(X4, bind_kn k0)]++E') (t:=open_tt t X4)
                (rsubst:=rsubst) (dsubst:=dsubst) (dsubst':=dsubst')
                (X:=X) (R:=R) (t2:=t2) (k:=S k)
                (rsubst':=[(X4, R0)]++rsubst')
                (dsubst'0:=[(X4, t2')]++dsubst'0) (dsubst0:=[(X4, t3)]++dsubst0)
                (e:=v) (e':=v') (K:=kn_lin) (Q:=Q)
                in G; simpl_env in *; simpl;  auto.       
         SSCase "all".
         destruct G as [Hrel_wft_wft' Hrel_wft'_wft].
         simpl_env. rewrite G''.
         apply Hrel_wft_wft'; simpl_env in *; simpl; simpl_env.
             SSSCase "all".
             assert (X4 `notin` fv_tt t2) as J. destruct_notin; auto.
             rewrite <- subst_tt_fresh; auto.
             rewrite <- subst_tt_fresh; auto.
             rewrite <- G'. auto.
             SSSCase "rsubst".
             eapply rsubst_weaken_head; simpl_env in *; try solve [eauto | fsetdec].
             SSSCase "dsubst".
             rewrite <- subst_tt_fresh; auto.          
             eapply dsubst_weaken_head; simpl_env in *; try solve [eauto using wfr_left_inv | fsetdec].
             SSSCase "dsubst'".
             rewrite <- subst_tt_fresh; auto.          
             eapply dsubst_weaken_head; simpl_env in *; try solve [eauto using wfr_right_inv | fsetdec].
         SSCase "F_Rel_R".
           unfold F_Rel__R in *. 
           destruct Hr_eq as [ HHwfd [ HHwfd' [ HHwfr Hrel_rel]]].
           repeat(split; simpl_env).
           apply wf_delta_subst_styp; eauto using wfr_left_inv.
           apply wf_delta_subst_styp; eauto using wfr_right_inv.
           apply wf_rho_subst_srel; auto.
           SSSCase "Rel -> R".
           intro Hrel.
             destruct (@Hrel_rel v0 v'0) as [Hrel_r Hr_rel].
             apply Hrel_r.
             unfold F_Rel in *.
             apply Frel_stronger with (E:=E'++E) (E':=@nil (atom*binding)) (X:=X4) (R:=R0) 
                            (rsubst:=rsubst'++rsubst) (rsubst':=rho_nil)
                            (dsubst:=dsubst0++dsubst) (dsubst0:=delta_nil)
                            (dsubst':=dsubst'0++dsubst') (dsubst'0:=delta_nil)
                            (t2:=t3) (t2':=t2') (K:=k0); simpl_env; simpl; auto.
                   SSSSCase "rsubst". simpl_env. eapply rsubst_weaken_head; simpl_env; eauto.
                   SSSSCase "dsubst". simpl_env. eapply dsubst_weaken_head; simpl_env; eauto using wfr_left_inv.
                   SSSSCase "dsubst". simpl_env. eapply dsubst_weaken_head; simpl_env; eauto using wfr_right_inv.
           SSSCase "R -> Rrel".
             intro Hr.
             destruct (@Hrel_rel v0 v'0) as [Hrel_r Hr_rel].
             unfold F_Rel in *.
             apply Frel_weaken_head with (E:=E'++E) (X:=X4) (R:=R0) (K:=k0)
                            (rsubst:=rsubst'++rsubst) (dsubst:=dsubst0++dsubst) (dsubst':=dsubst'0++dsubst')
                            (t2:=t3) (t2':=t2'); simpl; simpl_env; auto.
        SSCase "fv".
        eapply m_all_left_fv with (e:=e) (e':=e') (t3:=t3) (t2':=t2'); eauto using wfr_left_inv, wfr_right_inv.

  Case "typ_with". (* with *)
  apply F_related_values_with_leq in Hrel.
  apply F_related_values_with_req.  
  destruct Hrel as [Hv [Hv'[e1 [e2 [e1' [e2' [Heq [Heq' 
                                [[u1 [u1' [Hnorm_e1u1 [Hnorm_e1'u1' Hrel_wft1]]]] 
                                 [u2 [u2' [Hnorm_e2u2 [Hnorm_e2'u2' Hrel_wft2]]]]]
                              ]]]]]]]]; subst.
       simpl in Hfv.
       repeat(split; auto; simpl_env in *).
       SCase "with".  
       simpl in Hwft. apply wft_with_inv in Hwft. destruct Hwft; subst.
       simpl in Hwft'. apply wft_with_inv in Hwft'. destruct Hwft'; subst.
       exists (e1). exists (e2). exists (e1'). exists (e2'). repeat(split; auto).
          SSCase "with1".
          exists (u1). exists (u1'). repeat(split; auto).
               assert (typ_size t1 < typ_size (typ_with t1 t3)) as G1. simpl. omega.
               apply H with (E:=E) (E':=E') (e:=u1) (e':=u1') (t:=t1)
                        (rsubst:=rsubst) (dsubst:=dsubst) (dsubst':=dsubst')
                        (X:=X) (R:=R) (t2:=t2) (k:=k)  (K:=kn_lin) (Q:=Q)
                        (rsubst':=rsubst') (dsubst0:=dsubst0) (dsubst'0:=dsubst'0) in G1; auto.
                 destruct G1 as [Hrel_wft1_wft1' Hrel_wft1'_wft1].
                 simpl in Hrel_wft1_wft1'. apply Hrel_wft1_wft1'; auto.
                 SSSCase "fv". 
                 eapply m_with1_fv with (e1:=e1) (e1':=e1'); eauto.
          SSCase "with2".
          exists (u2). exists (u2'). repeat(split; auto).
               assert (typ_size t3 < typ_size (typ_with t1 t3)) as G2. simpl. omega.
               assert (X `notin` (fv_env E `union` fv_env E' `union` fv_tt t3 `union` fv_te u2 `union` fv_te u2')).
                 eapply m_with2_fv with (e2:=e2) (e2':=e2'); eauto.
               apply H with (E:=E) (E':=E') (e:=u2) (e':=u2') (t:=t3)
                        (rsubst:=rsubst) (dsubst:=dsubst) (dsubst':=dsubst')
                        (X:=X) (R:=R) (t2:=t2) (k:=k)  (K:=kn_lin) (Q:=Q)
                        (rsubst':=rsubst') (dsubst0:=dsubst0) (dsubst'0:=dsubst'0) in G2; auto.
               destruct G2; auto.

  (* <- *)
  intros Hrel Hwfr Hwfd Hwfd'.
  (typ_cases (induction t) Case); simpl in Hrel; simpl; simpl_env in *.

  Case "typ_bvar". (* bvar *)
  destruct (k==n0); subst.
    SCase "fvar".
    apply F_related_values_fvar_req.
    exists (R).
    assert (
      (F_Rel t2 (rsubst'++rsubst) (dsubst0++dsubst) (dsubst'0++dsubst') e e' -> R e e') *
      (R e e' -> F_Rel t2 (rsubst'++rsubst)  (dsubst0++dsubst) (dsubst'0++dsubst') e e')
      ) as HR'.
      unfold F_Rel__R in Hr_eq. decompose [and] Hr_eq; auto.
    destruct HR' as [Hrel_r Hr_rel].
    assert (F_Rel t2 (rsubst'++rsubst)  (dsubst0++dsubst) (dsubst'0++dsubst') e e') as XX.
      unfold F_Rel. assumption.
    apply Hrel_r in XX.
    apply F_related_values_inversion in Hrel.
    destruct Hrel as [Hv Hv'].
    repeat(split; auto).
    SCase "bvar".
    apply F_related_values_bvar_req; auto.

  Case "typ_fvar". (* fvar *)
  apply F_related_values_fvar_leq in Hrel; auto.
  apply F_related_values_fvar_req; auto.
  unfold In_rel in Hrel.
  destruct Hrel as [R0 [Hb [Hv [Hv' Hr]]]]; subst; simpl.
  exists (R0).
  repeat(split; auto; simpl_env; auto).

  Case "typ_arrow". (* arrow *)
  apply F_related_values_arrow_leq in Hrel; auto.
  apply F_related_values_arrow_req; auto.
  destruct Hrel as [Hv [Hv' Harrow]]; subst.
  simpl in Hfv.
  simpl in Hwft. apply wft_arrow_inv in Hwft. destruct Hwft; auto.
  simpl in Hwft'. apply wft_arrow_inv in Hwft'. destruct Hwft'; auto.
  repeat(split; auto; simpl_env in *).
        SCase "arrorw".  
         intros x x' Htypingx Htypingx' Harrow'.
         rename Harrow' into Hrel_wft1.
         destruct (@Harrow x x') as [u [u' [Hnorm_vxu [Hnorm_v'x'u' Hrel_wft1']]]]; auto.
           SSCase "typing". eapply m_typing_var_weaken; destruct_notin; eauto using wfr_left_inv.
           SSCase "typing". eapply m_typing_var_weaken; destruct_notin; eauto using wfr_right_inv.
           SSCase "arrow". 
           assert (typ_size t1 < typ_size (typ_arrow k0 t1 t3)) as G1. simpl. omega.
           apply H with (E:=E) (E':=E') (e:=x) (e':=x') (t:=t1)
                        (rsubst:=rsubst) (dsubst:=dsubst) (dsubst':=dsubst')
                        (X:=X) (R:=R) (t2:=t2) (k:=k) (K:=kn_lin) (Q:=Q)
                        (rsubst':=rsubst') (dsubst0:=dsubst0) (dsubst'0:=dsubst'0) in G1; auto.
              SSSCase "arrow_left". 
              destruct G1 as [Hrel_wft1_wft1' Hrel_wft1'_wft1].
              simpl in Hrel_wft1_wft1'. apply Hrel_wft1_wft1' in Hrel_wft1; auto.
               SSSSCase "arrow_left". 
                 simpl_env. eapply rsubst_weaken; eauto.
                 simpl_env. apply dsubst_weaken; eauto using wfr_left_inv.
                 simpl_env. apply dsubst_weaken; eauto using wfr_right_inv.
              SSSCase "fv". 
               assert (X `notin` fv_te x). 
                 eapply m_typing_normalization_fv with (e:=x); eauto.
                  unfold normalize. 
                  split; auto.
                    apply F_related_values_inversion in Hrel_wft1.
                    decompose [prod] Hrel_wft1; auto.
               assert (X `notin` fv_te x'). 
                 eapply m_typing_normalization_fv with (e:=x'); eauto.
                  unfold normalize. 
                  split; auto.
                    apply F_related_values_inversion in Hrel_wft1.
                    decompose [prod] Hrel_wft1; auto.
               destruct_notin. auto.
         SSCase "arrow_right". 
          exists (u). exists (u'). repeat(split; auto).
          assert (open_tt_rec k (typ_fvar X) t3 = open_tt_rec k (typ_fvar X) t3) as G'0. auto.
          assert (E'++[(X,bind_kn Q)]++E = E'++[(X,bind_kn Q)]++E) as G'1. auto.
          assert (F_Rel__R t2 (E'++E) (rsubst'++rsubst) (dsubst0++dsubst) (dsubst'0++dsubst') R) as HR. auto.
           assert (typ_size t3 < typ_size (typ_arrow k0 t1 t3)) as G2. simpl. omega.
           apply H with (E:=E) (E':=E') (e:=u) (e':=u') (t:=t3)
                        (rsubst:=rsubst) (dsubst:=dsubst) (dsubst':=dsubst')
                        (X:=X) (R:=R) (t2:=t2) (k:=k) (K:=kn_lin) (Q:=Q)
                        (rsubst':=rsubst') (dsubst0:=dsubst0) (dsubst'0:=dsubst'0) in G2; auto.
           destruct G2 as [Hrel_wft2_wft2' Hrel_wft2'_wft2]; auto.
             SSSCase "fv". 
             assert (X `notin` fv_te u). eapply m_typing_normalization_arrow_fv_weaken with (e:=e) (x:=x) (t1:=t1) ; eauto using wfr_left_inv.
             assert (X `notin` fv_te u'). eapply m_typing_normalization_arrow_fv_weaken with (e:=e') (x:=x') (t1:=t1) ; eauto using wfr_right_inv.
             destruct_notin. auto.

  Case "typ_all". (* all *)
  assert (uniq (E'++[(X, bind_kn Q)]++E)) as Uniq.
    apply wf_delta_subst__uniq in Hwfd.
    decompose [and] Hwfd; auto.
    apply uniq_insert_mid; auto.
  apply F_related_values_all_leq in Hrel.
  apply F_related_values_all_req.  
  destruct Hrel as [Hv [Hv' [L' Hall]]]; subst.
  repeat(split; auto; simpl_env in *; simpl in Hfv).
       SCase "all".
         assert (forall X,
           X `notin` dom (E'++E) `union` fv_tt (open_tt_rec (S k) t2 t) ->
           wf_typ ([(X, bind_kn k0)]++E'++E) (open_tt (open_tt_rec (S k) t2 t) X) kn_lin) as w'.
           simpl in Hwft'. 
           eapply wft_all_inv; eauto.
         assert (forall Y,
           Y `notin` dom (E'++[(X, bind_kn Q)]++E) `union` fv_tt (open_tt_rec (S k) X t) ->
           wf_typ ([(Y, bind_kn k0)]++E'++[(X, bind_kn Q)]++E) (open_tt (open_tt_rec (S k) X t) Y) kn_lin) as w.
           simpl in Hwft. 
           eapply wft_all_inv; eauto.
         exists (L'   `union` fv_env E  `union` fv_env E' `union` dom E  `union` dom E' `union` (fv_tt (open_tt_rec (S k) t2 t)) `union` singleton X `union` (fv_tt t2)).
         intros X2 t3 t2' R0 Fr Hwfr' Hfv'.
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
         assert (wf_typ ([(X2, bind_kn k0)]++E'++E) (open_tt_rec (S k)  t2 (open_tt t X2)) kn_lin) as WFT'. 
           rewrite <- G''.
           apply w' with (X:=X2).
           auto.
         assert (wf_typ ([(X2, bind_kn k0)]++E'++[(X,bind_kn Q)]++E) (open_tt_rec (S k) X (open_tt t X2)) kn_lin) as WFT. 
           rewrite <- G'.
           apply w with (Y:=X2).
           auto.
         assert (wf_typ ([(X2, bind_kn k0)]++E'++E) t2 Q) as WFT2'. 
           apply wf_rho_subst__uniq in Hwfr. decompose [and] Hwfr.
           eapply wf_typ_weaken_head; eauto.
         assert (typ_size (open_tt t X2) < typ_size (typ_all k0 t)) as G. 
          simpl. rewrite open_tt_typ_size_eq. omega.
         apply H with (E:=E) (E':=[(X2, bind_kn k0)]++E') (t:=open_tt t X2)
                (rsubst:=rsubst) (dsubst:=dsubst) (dsubst':=dsubst')
                (X:=X) (R:=R) (t2:=t2) (k:=S k)
                (rsubst':=[(X2, R0)]++rsubst')
                (dsubst'0:=[(X2, t2')]++dsubst'0) (dsubst0:=[(X2, t3)]++dsubst0)
                (e:=v) (e':=v') (K:=kn_lin) (Q:=Q)
                in G; simpl_env in *; simpl;  auto.       
         SSCase "all".
           destruct G as [Hrel_wft_wft' Hrel_wft'_wft].
           simpl in Hrel_wft'_wft.
           rewrite <- subst_tt_fresh in Hrel_wft'_wft; auto.
           rewrite <- subst_tt_fresh in Hrel_wft'_wft; auto.
           rewrite G'.
           apply Hrel_wft'_wft; simpl_env.
              SSSCase "all". rewrite <- G''. auto.
              SSSCase "rsubst". eapply rsubst_weaken_head; simpl_env; eauto.
              SSSCase "dsubst". eapply dsubst_weaken_head; simpl_env; eauto using wfr_left_inv.
              SSSCase "dsubst'". eapply dsubst_weaken_head; simpl_env; eauto using wfr_right_inv.
         SSCase "F_Rel".
         unfold F_Rel__R in *. destruct Hr_eq as [ HHwfd [ HHwfd' [ HHwfr Hrel_rel]]].
           repeat(split; simpl_env).
           apply wf_delta_subst_styp; eauto using wfr_left_inv.
           apply wf_delta_subst_styp; eauto using wfr_right_inv.
           apply wf_rho_subst_srel; auto.
           SSSCase "Rel -> R".
           intro Hrel.
             destruct (@Hrel_rel v0 v'0) as [Hrel_r Hr_rel].
             apply Hrel_r.
             unfold F_Rel in *.
             apply Frel_stronger with (E:=E'++E) (E':=@nil (atom*binding)) (X:=X2) (R:=R0) 
                            (rsubst:=rsubst'++rsubst) (rsubst':=rho_nil)
                            (dsubst:=dsubst0++dsubst) (dsubst0:=delta_nil)
                            (dsubst':=dsubst'0++dsubst') (dsubst'0:=delta_nil)
                            (t2:=t3) (t2':=t2') (K:=k0); simpl_env in *; simpl; auto; simpl_env .
                   SSSSCase "rsubst". eapply rsubst_weaken_head; simpl_env; eauto.
                   SSSSCase "dsubst". eapply dsubst_weaken_head; simpl_env; eauto using wfr_left_inv.
                   SSSSCase "dsubst'". eapply dsubst_weaken_head; simpl_env; eauto using wfr_right_inv.               
           SSSCase "R -> Rrel".
             intro Hr.
             destruct (@Hrel_rel v0 v'0) as [Hrel_r Hr_rel].
             unfold F_Rel in *.
             apply Frel_weaken_head with (E:=E'++E) (X:=X2) (R:=R0) 
                            (rsubst:=rsubst'++rsubst) (K:=k0)
                            (dsubst:=dsubst0++dsubst)
                            (dsubst':=dsubst'0++dsubst')
                            (t2:=t3) (t2':=t2'); simpl_env in*; auto.
         SSCase "fv".
         eapply m_all_right_fv with (e:=e) (e':=e') (t3:=t3) (t2':=t2'); eauto using wfr_left_inv, wfr_right_inv.

  Case "typ_with". (* with *)
  apply F_related_values_with_leq in Hrel.
  apply F_related_values_with_req.  
  destruct Hrel as [Hv [Hv' [e1 [e2 [e1' [e2' [Heq [Heq' 
                                [[u1 [u1' [Hnorm_e1u1 [Hnorm_e1'u1' Hrel_wft1]]]] 
                                 [u2 [u2' [Hnorm_e2u2 [Hnorm_e2'u2' Hrel_wft2]]]]]
                              ]]]]]]]]; subst.
       simpl in Hfv.
       simpl in Hwft. apply wft_with_inv in Hwft. destruct Hwft; subst.
       simpl in Hwft'. apply wft_with_inv in Hwft'. destruct Hwft'; subst.
       repeat(split; auto;simpl_env in *).
       SCase "with".
       exists (e1). exists (e2). exists (e1'). exists (e2'). repeat(split; auto).
         SSCase "with1".
         exists (u1). exists (u1'). repeat(split; auto).
         assert (typ_size t1 < typ_size (typ_with t1 t3)) as G1. simpl. omega.
         apply H with (E:=E) (E':=E') (e:=u1) (e':=u1') (t:=t1)
                        (rsubst:=rsubst) (dsubst:=dsubst) (dsubst':=dsubst')
                        (X:=X) (R:=R) (t2:=t2) (k:=k) (K:=kn_lin) (Q:=Q)
                        (rsubst':=rsubst') (dsubst0:=dsubst0) (dsubst'0:=dsubst'0) in G1; auto.
                 destruct G1 as [Hrel_wft1_wft1' Hrel_wft1'_wft1].
                 simpl in Hrel_wft1'_wft1. apply Hrel_wft1'_wft1; auto.
                 eapply m_with1_fv with (e1:=e1) (e1':=e1'); eauto.
         SSCase "with2".
         exists (u2). exists (u2'). repeat(split; auto).
         assert (X `notin` (fv_env E `union` fv_env E' `union` fv_tt t3 `union` fv_te u2 `union` fv_te u2')).
            eapply m_with2_fv with (e2:=e2) (e2':=e2'); eauto.
         assert (typ_size t3 < typ_size (typ_with t1 t3)) as G2. simpl. omega.
         apply H with (E:=E) (E':=E') (e:=u2) (e':=u2') (t:=t3)
                        (rsubst:=rsubst) (dsubst:=dsubst) (dsubst':=dsubst')
                        (X:=X) (R:=R) (t2:=t2) (k:=k)(K:=kn_lin) (Q:=Q)
                        (rsubst':=rsubst') (dsubst0:=dsubst0) (dsubst'0:=dsubst'0) in G2; auto.
         destruct G2; auto.
Qed.

Lemma parametricity_subst_value : forall t E E' e e' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 X R t2 k K Q,
  wf_typ (E'++[(X,bind_kn Q)]++E) (open_tt_rec k (typ_fvar X) t) K->
  wf_typ (E'++E) (open_tt_rec k t2 t) K ->
  wf_typ (E'++E) t2 Q ->
  F_Rel__R t2 (E'++E) (rsubst'++rsubst) (dsubst0++dsubst) (dsubst'0++dsubst') R ->
  X `notin` (fv_env E `union` fv_env E' `union` (fv_tt t) `union` (fv_te e) `union` (fv_te e'))-> 
  ddom_env E [=] dom dsubst ->
  ddom_env E [=] dom dsubst' ->
  ddom_env E' [=] dom dsubst0 ->
  ddom_env E' [=] dom dsubst'0 ->
  ddom_env E [=] dom rsubst ->
  ddom_env E' [=] dom rsubst' ->
  (F_related_values (open_tt_rec k (typ_fvar X) t) (rsubst'++[(X, R)]++rsubst ) (dsubst0++[(X, (apply_delta_subst_typ (dsubst0++dsubst) t2))]++dsubst) (dsubst'0++[(X,(apply_delta_subst_typ (dsubst'0++dsubst') t2))]++dsubst') e e' ->
  wf_rho_subst (E'++[(X, bind_kn Q)]++E) (rsubst'++[(X, R)]++rsubst) ->
  wf_delta_subst (E'++[(X, bind_kn Q)]++E) (dsubst0++[(X, (apply_delta_subst_typ (dsubst0++dsubst) t2))]++dsubst) -> 
  wf_delta_subst (E'++[(X, bind_kn Q)]++E) (dsubst'0++[(X, (apply_delta_subst_typ (dsubst'0++dsubst') t2))]++dsubst') -> 
  F_related_values (open_tt_rec k t2 t) (rsubst'++rsubst) (dsubst0++dsubst) (dsubst'0++dsubst') e e')
  .
Proof.
  intros t E E' e e' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 X R t2 k K Q
        Hwft' Hwft Hwft2 Hrel_eq Hfv Hdsubst Hdsubst' Hdsubst0 Hdsubst'0 Hrsubst Hrsubst'.
  assert (P_parametricity_subst_value (typ_size t)).
    apply (@_parametricity_subst_value (typ_size t)).
  unfold P_parametricity_subst_value in H.
  assert (typ_size t = typ_size t) as Htsize. auto.
  decompose [prod] (@H t E E' e e' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 X R t2 k K Q
                     Htsize Hwft' Hwft Hwft2 Hrel_eq Hfv Hdsubst Hdsubst' Hdsubst0 Hdsubst'0 Hrsubst Hrsubst').
  eapply a; eauto.
Qed.

(*******************************************************************************)
(** F_related_subst_split *)

Lemma F_related_subst_split: forall E lE lE1 lE2 dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
   F_related_subst E lE gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
   lenv_split E lE1 lE2 lE ->
   exists lgsubst1, exists lgsubst1', exists lgsubst2, exists lgsubst2',
     lgamma_subst_split E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst /\
     lgamma_subst_split E lE dsubst' gsubst' lgsubst1' lgsubst2' lgsubst' /\
     F_related_subst E lE1 gsubst gsubst' lgsubst1 lgsubst1' rsubst dsubst dsubst' /\     
     F_related_subst E lE2 gsubst gsubst' lgsubst2 lgsubst2' rsubst dsubst dsubst'.
Proof.
  intros E lE lE1 lE2 dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Hrel_subst Hsplit.
  generalize dependent lE1. generalize dependent lE2.
  (F_related_subst_cases (induction Hrel_subst) Case); intros.
  Case "F_related_subst_empty".
    exists gamma_nil. exists gamma_nil. exists gamma_nil. exists gamma_nil.
    inversion Hsplit; subst.
    repeat (split; auto).
  Case "F_related_subst_kind".
    assert (J:=Hsplit).
    apply lenv_split_strengthening_typ_tail in Hsplit; auto.
    apply IHHrel_subst in Hsplit. clear IHHrel_subst.
    destruct Hsplit as [lgsubst1 [lgsubst1' [lgsubst2 [lgsubst2'[J1 [J2 [J3 J4]]]]]]].
    exists lgsubst1. exists lgsubst1'. exists lgsubst2. exists lgsubst2'.
    split.
      apply lgamma_subst_split_nonlin_weakening_typ_tail; auto.
        apply wf_lgamma_subst_skind; eauto using wfr_left_inv.
          apply lgamma_subst_split__wf_lgamma_subst in J1; auto.
    split.
      apply lgamma_subst_split_nonlin_weakening_typ_tail; auto.
        apply wf_lgamma_subst_skind; eauto using wfr_right_inv.
          apply lgamma_subst_split__wf_lgamma_subst in J2; auto.
    split.
      apply F_related_subst_kind; auto.
        apply fv_lenv_split in J.
        rewrite J in H. auto.
      apply F_related_subst_kind; auto.
        apply fv_lenv_split in J.
        rewrite J in H. auto.
  Case "F_related_subst_typ".
    assert (J:=Hsplit).
    apply lenv_split_strengthening_tail in Hsplit; auto.
    apply IHHrel_subst in Hsplit. clear IHHrel_subst.
    destruct Hsplit as [lgsubst1 [lgsubst1' [lgsubst2 [lgsubst2'[J1 [J2 [J3 J4]]]]]]].
    exists lgsubst1. exists lgsubst1'. exists lgsubst2. exists lgsubst2'.
    split.
      apply lgamma_subst_split_nonlin_weakening_tail; auto.
        apply wf_lgamma_subst_sval; auto.
          apply lgamma_subst_split__wf_lgamma_subst in J1; auto.
    split.
      apply lgamma_subst_split_nonlin_weakening_tail; auto.
        apply wf_lgamma_subst_sval; auto.
          apply lgamma_subst_split__wf_lgamma_subst in J2; auto.
    split.
      apply F_related_subst_typ; auto.
        apply fv_lenv_split in J.
        rewrite J in H2. auto.
      apply F_related_subst_typ; auto.
        apply fv_lenv_split in J.
        rewrite J in H2. auto.
  Case "F_related_subst_ltyp".
    inversion Hsplit; subst.
    SCase "lenv_split_left".
      assert (J:=H7).
      apply IHHrel_subst in H7. clear IHHrel_subst.
      destruct H7 as [lgsubst1 [lgsubst1' [lgsubst2 [lgsubst2'[J1 [J2 [J3 J4]]]]]]].
      exists ([(x,v)]++lgsubst1). exists ([(x,v')]++lgsubst1'). exists lgsubst2. exists lgsubst2'.
      split.
        apply lgamma_subst_split_left; auto.
      split.
        apply lgamma_subst_split_left; auto.
      split; auto.
        apply F_related_subst_ltyp; auto.
          apply fv_lenv_split in J.
          rewrite J in H2. auto.
    SCase "lenv_split_right".
      assert (J:=H7).
      apply IHHrel_subst in H7. clear IHHrel_subst.
      destruct H7 as [lgsubst1 [lgsubst1' [lgsubst2 [lgsubst2'[J1 [J2 [J3 J4]]]]]]].
       exists lgsubst1. exists lgsubst1'. exists ([(x,v)]++lgsubst2). exists ([(x,v')]++lgsubst2').
      split.
        apply lgamma_subst_split_right; auto.
      split.
        apply lgamma_subst_split_right; auto.
      split; auto.
        apply F_related_subst_ltyp; auto.
          apply fv_lenv_split in J.
          rewrite J in H2. auto.
Qed. 

(*******************************************************************************)
(** parametricity *)

Lemma parametricity: forall E lE e t dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
   typing E lE e t ->
   F_related_subst E lE gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
   F_Rsubst E rsubst dsubst dsubst'->
   F_related_terms t rsubst dsubst dsubst'
                                 (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
                                 (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e)))
   .
Proof.
  intros E lE e t dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Htyping Hrel_sub HRsub.
  generalize dependent rsubst.
  generalize dependent gsubst'.
  generalize dependent gsubst.
  generalize dependent lgsubst'.
  generalize dependent lgsubst.
  generalize dependent dsubst'.
  generalize dependent dsubst.
  (typing_cases (induction Htyping) Case); intros.
  Case "typing_var".
    assert (J:=Hrel_sub). apply F_related_subst__inversion in J. 
    destruct J as [[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe].
    assert (G:=@bindsgE__bindsgsubst E [] gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' x T Hrel_sub H0); auto.
    destruct G as [J1 [J2 [v [v' [[[[Hb Hb'] Ht] Ht'] Hrel]]]]]; eauto using wf_typ_from_binds_typ.
    rewrite m_delta_gamma_subst_var with (E:=E) (lE:=[]) (x:=x) (gsubst:=gsubst) (t:=apply_delta_subst_typ dsubst T) (e:=v); auto.
    rewrite m_delta_gamma_subst_var with (E:=E) (lE:=[]) (x:=x) (gsubst:=gsubst') (t:=apply_delta_subst_typ dsubst' T) (e:=v'); auto.
    exists v. exists v'.
      assert (J:=Hrel). apply F_related_values_inversion in J. destruct J as [JJ1 JJ2].
      repeat (split; auto).

  Case "typing_lvar".
    assert (J:=Hrel_sub). apply F_related_subst__inversion in J. 
    destruct J as [[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe].
    assert (binds x (lbind_typ T) [(x, lbind_typ T)]) as Binds. apply binds_one_3; auto.
    assert (G:=@lbindsgE__lbindsgsubst E [(x, lbind_typ T)] gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' x T Hrel_sub Binds); auto.
    destruct G as [J1 [J2 [v [v' [[[[Hb Hb'] Ht] Ht'] Hrel]]]]]; eauto using wf_typ_from_lbinds_typ.
    rewrite m_delta_lgamma_subst_var with (E:=E) (lE:=[(x, lbind_typ T)]) (x:=x) (gsubst:=gsubst) (t:=apply_delta_subst_typ dsubst T) (e:=v); auto.
    rewrite m_delta_lgamma_subst_var with (E:=E) (lE:=[(x, lbind_typ T)]) (x:=x) (gsubst:=gsubst') (t:=apply_delta_subst_typ dsubst' T) (e:=v'); auto.
    exists v. exists v'.
      assert (J:=Hrel). apply F_related_values_inversion in J. destruct J as [JJ1 JJ2].
      repeat (split; auto).

  Case "typing_abs".
    assert (J:=Hrel_sub). apply F_related_subst__inversion in J. 
    destruct J as [[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe].

    rename H into WFTV.
    
    exists (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_abs K T1 e1)))).
    exists (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_abs K T1 e1)))).
    split.
      SCase "typing".
      simpl_commut_subst.
      apply typing_abs with (L:=L `union` dom (gsubst) `union` dom (lgsubst) `union` dom E); auto.
        apply wft_subst with (E:=E) (dsubst:=dsubst); auto.

        intros x Hfv.
        assert (x `notin` L) as Htyping; auto.
        apply H0 in Htyping. 
        apply m_typing_subst_typ_closed with (E:=E) (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst) in Htyping; auto.
    split.
      SCase "typing".
      simpl_commut_subst.
      apply typing_abs with (L:=L `union` dom (gsubst') `union` dom (lgsubst')  `union` dom E); auto.
        apply wft_subst with (E:=E) (dsubst:=dsubst'); auto.

        intros x Hfv.
        assert (x `notin` L) as Htyping; auto.
        apply H0 in Htyping. 
        apply m_typing_subst_typ_closed with (E:=E) (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst') in Htyping; auto.

    split; try solve [split; try solve [apply delta_gamma_lgamma_subst_value with (E:=E) (D:=D); eauto using FrTyping__absvalue | auto]].
    split; try solve [split; try solve [apply delta_gamma_lgamma_subst_value with (E:=E) (D:=D); eauto using FrTyping__absvalue | auto]].
      SCase "Frel".
      apply F_related_values_arrow_req.
      split; try solve [apply delta_gamma_lgamma_subst_value with (E:=E) (D:=D); eauto using FrTyping__absvalue].
      split; try solve [apply delta_gamma_lgamma_subst_value with (E:=E) (D:=D); eauto using FrTyping__absvalue].
      SSCase "arrow".
        intros x x' Htyping Htyping' Harrow_left.
        pick fresh y.
        assert (y `notin` L) as Fry. auto.
        assert (wf_typ ([(y, bind_typ T1)]++E) T2 kn_lin) as WFT'. 
          apply H0 in Fry.
          apply typing_regular in Fry.
          decompose [and] Fry; auto.
        apply H1 with (dsubst:=dsubst) (dsubst':=dsubst') 
                         (gsubst:=[(y,x)]++gsubst)
                         (gsubst':=[(y,x')]++gsubst') 
                         (lgsubst:=lgsubst)
                         (lgsubst':=lgsubst') 
                         (rsubst:=rsubst) in Fry; auto.
        assert (
            apply_delta_subst dsubst (apply_gamma_subst ([(y,x)]++gsubst) (apply_gamma_subst lgsubst (open_ee e1 y))) =
            apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (subst_ee y x (open_ee e1 y))))
                  ) as Heq1. simpl. 
           rewrite swap_subst_ee_lgsubst with (E:=E)(D:=D)(dsubst:=dsubst)(lgsubst:=lgsubst)(gsubst:=gsubst)(t:=apply_delta_subst_typ dsubst T1); auto.
             apply wf_lgamma_subst__nfv with (x:=y) in Hwflg; auto.
         assert (
            apply_delta_subst dsubst' (apply_gamma_subst ([(y,x')]++gsubst') (apply_gamma_subst lgsubst' (open_ee e1 y))) =
            apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (subst_ee y x' (open_ee e1 y))))
                  ) as Heq2.  simpl.
           rewrite swap_subst_ee_lgsubst with (E:=E)(D:=D)(dsubst:=dsubst')(lgsubst:=lgsubst')(gsubst:=gsubst')(t:=apply_delta_subst_typ dsubst' T1); auto.
             apply wf_lgamma_subst__nfv with (x:=y) in Hwflg'; auto.
         rewrite Heq1 in Fry. rewrite Heq2 in Fry. clear Heq1 Heq2.
         destruct Fry as [v [v' [Ht [Ht' [[Hbrc Hv] [[Hbrc' Hv'] Hrel]]]]]].
         exists (v). exists (v').
         split.
           SSSCase "norm".
           split; auto.
           apply bigstep_red_trans with (e':=(apply_delta_subst dsubst (apply_gamma_subst gsubst  (apply_gamma_subst lgsubst (subst_ee y x (open_ee e1 y)))))); auto.
              eapply m_red_abs_subst; eauto.
                apply F_related_values_inversion in Harrow_left.
                decompose [prod] Harrow_left; auto.
         split; auto.
           SSSCase "norm".
           split; auto.
           apply bigstep_red_trans with (e':=(apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (subst_ee y x' (open_ee e1 y)))))); auto.
              eapply m_red_abs_subst; eauto.
                apply F_related_values_inversion in Harrow_left.
                decompose [prod] Harrow_left; auto.
           SSSCase "Frel".
           apply F_related_subst_typ; auto.
           SSSCase "FRsubst".
           apply F_Rsubst_typ; auto.

  Case "typing_labs".
    assert (J:=Hrel_sub). apply F_related_subst__inversion in J. 
    destruct J as [[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe].

    rename H into WFTV.
    
    exists (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_abs K T1 e1)))).
    exists (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_abs K T1 e1)))).
    split.
      SCase "typing".
      simpl_commut_subst.
      apply typing_labs with (L:=L `union` dom (gsubst) `union` dom (lgsubst) `union` dom E); auto.
        apply wft_subst with (E:=E) (dsubst:=dsubst); auto.

        intros x Hfv.
        assert (x `notin` L) as Htyping; auto.
        apply H0 in Htyping. 
        apply m_typing_subst_ltyp_closed with (E:=E) (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst) in Htyping; auto.
    split.
      SCase "typing".
      simpl_commut_subst.
      apply typing_labs with (L:=L `union` dom (gsubst') `union` dom (lgsubst')  `union` dom E); auto.
        apply wft_subst with (E:=E) (dsubst:=dsubst'); auto.

        intros x Hfv.
        assert (x `notin` L) as Htyping; auto.
        apply H0 in Htyping. 
        apply m_typing_subst_ltyp_closed with (E:=E) (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst') in Htyping; auto.

    split; try solve [split; try solve [apply delta_gamma_lgamma_subst_value with (E:=E) (D:=D); eauto using FrTyping__labsvalue | auto]].
    split; try solve [split; try solve [apply delta_gamma_lgamma_subst_value with (E:=E) (D:=D); eauto using FrTyping__labsvalue | auto]].
      SCase "Frel".
      apply F_related_values_arrow_req.
      split; try solve [apply delta_gamma_lgamma_subst_value with (E:=E) (D:=D); eauto using FrTyping__labsvalue].
      split; try solve [apply delta_gamma_lgamma_subst_value with (E:=E) (D:=D); eauto using FrTyping__labsvalue].
      SSCase "arrow".
        intros x x' Htyping Htyping' Harrow_left.
        pick fresh y.
        assert (y `notin` L) as Fry. auto.
        assert (wf_typ E T2 kn_lin) as WFT'. 
          apply H0 in Fry.
          apply typing_regular in Fry.
          decompose [and] Fry; auto.
        apply H1 with (dsubst:=dsubst) (dsubst':=dsubst') 
                         (gsubst:=gsubst)
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
              eapply m_red_labs_subst; eauto.
                apply F_related_values_inversion in Harrow_left.
                decompose [prod] Harrow_left; auto.
         split; auto.
           SSSCase "norm".
           split; auto.
           apply bigstep_red_trans with (e':=(apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (subst_ee y x' (open_ee e1 y)))))); auto.
              eapply m_red_labs_subst; eauto.
                apply F_related_values_inversion in Harrow_left.
                decompose [prod] Harrow_left; auto.
           SSSCase "Frel".
           apply F_related_subst_ltyp; auto.

  Case "typing_app".
   assert (J:=Hrel_sub). apply F_related_subst__inversion in J. 
   destruct J as [[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe].
   assert (J:=Htyping1).
   apply typing_regular in J.
   destruct J as [Hwfe' [Hwfle' [He WFTarrow]]].
   apply F_related_subst_split with (lE1:=D1) (lE2:=D2) in Hrel_sub; auto.
   destruct Hrel_sub as [lgsubst1 [lgsubst1' [lgsubst2 [lgsubst2' [J1 [J2 [J3 J4]]]]]]].

   assert (
      F_related_terms (typ_arrow K T1 T2) rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst1 e1)))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst1' e1)))
     ) as FR_ArrowType.
    apply IHHtyping1; auto.
   destruct FR_ArrowType as [v [v' [Ht [Ht' [Hn [Hn' Hrel]]]]]].

   apply F_related_values_arrow_leq in Hrel.
   destruct Hrel as [Hv [Hv' Harrow]]; subst.

   assert (
      F_related_terms T1 rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst2 e2)))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst'(apply_gamma_subst lgsubst2' e2)))
     ) as FR_T1.
    apply IHHtyping2; auto.
   destruct FR_T1 as [v0 [v'0 [Ht1 [Ht1' [Hn1 [Hn1' Hrel_wft1]]]]]].

   destruct (@Harrow v0 v'0) as [u [u' [Hnorm_vxu [Hnorm_v'x'u' Hrel_wft2]]]]; auto.
     eapply preservation_normalization; eauto.
     eapply preservation_normalization; eauto.

   exists(u). exists(u').
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
     rewrite lgamma_subst_split_subst' with (lgsubst1:=lgsubst1) (lgsubst2:=lgsubst2) (E:=E) (lE:=D3) (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst); auto.
     rewrite lgamma_subst_split_subst with (lgsubst1:=lgsubst1) (lgsubst2:=lgsubst2) (E:=E) (lE:=D3) (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst); auto.
     apply F_related_subst__inversion in J3.
     decompose [prod] J3; auto.
     apply F_related_subst__inversion in J4.
     decompose [prod] J4; auto.
     rewrite lgamma_subst_split_shuffle2 with (lgsubst:=lgsubst) (lgsubst1:=lgsubst1) (E:=E) (lE:=D3) ; auto.
     erewrite gamma_subst_closed_exp; eauto.
     rewrite lgamma_subst_split_shuffle1 with (lgsubst:=lgsubst) (lgsubst2:=lgsubst2) (E:=E) (lE:=D3) (e:=apply_gamma_subst lgsubst2 e2) ; auto.
     erewrite gamma_subst_closed_exp with 
         (e:=apply_delta_subst dsubst
            (apply_gamma_subst gsubst
              (apply_gamma_subst lgsubst2 e2))
          ); eauto.
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
     rewrite lgamma_subst_split_subst' with (lgsubst1:=lgsubst1') (lgsubst2:=lgsubst2') (E:=E) (lE:=D3) (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst'); auto.
     rewrite lgamma_subst_split_subst with (lgsubst1:=lgsubst1') (lgsubst2:=lgsubst2') (E:=E) (lE:=D3) (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst'); auto.
     apply F_related_subst__inversion in J3.
     decompose [prod] J3; auto.
     apply F_related_subst__inversion in J4.
     decompose [prod] J4; auto.
     rewrite lgamma_subst_split_shuffle2 with (lgsubst:=lgsubst') (lgsubst1:=lgsubst1') (E:=E) (lE:=D3) ; auto.
     erewrite gamma_subst_closed_exp; eauto.
     rewrite lgamma_subst_split_shuffle1 with (lgsubst:=lgsubst') (lgsubst2:=lgsubst2') (E:=E) (lE:=D3) (e:=apply_gamma_subst lgsubst2' e2) ; auto.
     erewrite gamma_subst_closed_exp with 
         (e:=apply_delta_subst dsubst'
            (apply_gamma_subst gsubst'
              (apply_gamma_subst lgsubst2' e2))
          ); eauto.
   repeat(rewrite EQ). clear EQ.
   repeat(split; try solve [simpl_commut_subst in *; eauto |
                                              simpl_commut_subst; apply congr_app with (v1:=v) (v2:=v0); auto |
                                              simpl_commut_subst; apply congr_app with (v1:=v') (v2:=v'0); auto]).

  Case "typing_tabs".
  assert (J:=Hrel_sub). apply F_related_subst__inversion in J.
  destruct J as [[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe].
  exists (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_tabs K e1)))).
  exists (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_tabs K e1)))).
      split.
      SCase "typing".
      simpl_commut_subst.
      apply typing_tabs with (L:=L `union` dom (dsubst) `union` dom E).
        intros.
        rewrite <- apply_delta_subst_typ_nfv with (dsubst:=dsubst); auto.
        rewrite <- apply_gamma_subst_typ_nfv with (gsubst:=gsubst); auto.
        rewrite <- apply_gamma_subst_typ_nfv with (gsubst:=lgsubst); auto.
        rewrite <- commut_delta_subst_open_te with (dE:=E); auto.
        rewrite <- commut_gamma_subst_open_te with (E:=E) (D:=D) (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst); auto.
        rewrite <- commut_lgamma_subst_open_te with (E:=E) (D:=D) (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst); auto.
        eapply delta_gamma_lgamma_subst_value; eauto.

        intros X Hfv.
        assert (X `notin` L) as Htyping. auto.
        apply H0 in Htyping. 
        apply m_typing_subst_kind_closed with (E:=E) (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst) in Htyping; auto.

      split.
      SCase "typing".
      simpl_commut_subst.
      apply typing_tabs with (L:=L `union` dom (dsubst') `union` dom E).
        intros.
        rewrite <- apply_delta_subst_typ_nfv with (dsubst:=dsubst'); auto.
        rewrite <- apply_gamma_subst_typ_nfv with (gsubst:=gsubst'); auto.
        rewrite <- apply_gamma_subst_typ_nfv with (gsubst:=lgsubst'); auto.
        rewrite <- commut_delta_subst_open_te with (dE:=E); auto.
        rewrite <- commut_gamma_subst_open_te with (E:=E) (D:=D) (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst'); auto.
        rewrite <- commut_lgamma_subst_open_te with (E:=E) (D:=D) (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst'); auto.
        eapply delta_gamma_lgamma_subst_value; eauto.

        intros X Hfv.
        assert (X `notin` L) as Htyping. auto.
        apply H0 in Htyping. 
        apply m_typing_subst_kind_closed with (E:=E) (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst') in Htyping; auto.

      split; try solve [split; auto; eapply delta_gamma_lgamma_subst_value with (E:=E) (dsubst:=dsubst) (lgsubst:=lgsubst); eauto using FrTyping__tabsvalue].
      split; try solve [split; auto; eapply delta_gamma_lgamma_subst_value with (E:=E) (dsubst:=dsubst') (lgsubst:=lgsubst'); eauto using FrTyping__tabsvalue].
      SCase "Frel".
      apply F_related_values_all_req.
      repeat(split; try solve [eapply delta_gamma_lgamma_subst_value with (E:=E); eauto using FrTyping__tabsvalue |
                                           apply  typing_subst_closed with (E:=E) (E':=@nil (atom*binding))(dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst) (D:=D) (D':=nil); 
                                               try solve [auto | apply typing_tabs with (L:=L); auto] |
                                           apply  typing_subst_closed with (E:=E) (E':=@nil (atom*binding))(dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst') (D:=D) (D':=nil); 
                                               try solve [auto | apply typing_tabs with (L:=L); auto]]).
        SSCase "Frel".
        exists (L `union` fv_te e1 `union` dom E `union` fv_env E `union` fv_lenv D).
        intros X t2 t2' R Fr HwfR Hfv.
        assert (X `notin` L) as FryL. auto.
        assert (wf_typ ([(X,bind_kn K)]++E) (open_tt T1 X) kn_lin) as WFT'.
          apply H0 in FryL.
          apply typing_regular in FryL.
          decompose [and] FryL; auto.
        apply H1 with (dsubst:=[(X, t2)]++dsubst) 
                         (dsubst':=[(X, t2')]++dsubst') 
                         (gsubst:=gsubst)
                         (gsubst':=gsubst') 
                         (lgsubst:=lgsubst)
                         (lgsubst':=lgsubst') 
                         (rsubst:=[(X,R)]++rsubst)in FryL; auto.
        simpl in FryL. simpl_env in FryL.
        erewrite swap_subst_te_gsubst with (E:=E) (dsubst:=dsubst) in FryL; eauto using wfr_left_inv. 
        erewrite swap_subst_te_lgsubst with (E:=E) (dsubst:=dsubst) in FryL; eauto using wfr_left_inv. 
        erewrite swap_subst_te_gsubst with  (E:=E)  (dsubst:=dsubst') in FryL; eauto using wfr_right_inv.
        erewrite swap_subst_te_lgsubst with  (E:=E)  (dsubst:=dsubst') in FryL; eauto using wfr_right_inv.
        destruct FryL as [v [v' [Ht [Ht' [[Hbrc Hv] [[Hbrc' Hv'] Hrel]]]]]].
        exists (v). exists (v').
        split.
          SSSCase "norm".
          split; auto.
          apply bigstep_red_trans with (e':=(apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (subst_te X t2 (open_te e1 X)))))); auto.
            eapply m_red_tabs_subst; eauto using wfr_left_inv.

        split; auto.
          SSSCase "norm".
          split; auto.
          apply bigstep_red_trans with (e':=(apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (subst_te X t2' (open_te e1 X)))))); auto.
            eapply m_red_tabs_subst; eauto using wfr_right_inv.
          SSSCase "Fsubst".
          apply F_related_subst_kind; auto.
          SSSCase "FRsubst".
          apply F_Rsubst_rel; auto.

   Case "typing_tapp".
   assert (J:=Hrel_sub). apply F_related_subst__inversion in J. 
   destruct J as [[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe].
   apply typing_regular in Htyping.
   destruct Htyping as [Hwfe' [Hwfle [He WFTall]]].
   assert (
      F_related_terms (typ_all K T2) rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e1)))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e1)))
     ) as FR_AllType.
      apply IHHtyping; auto.
   destruct FR_AllType as [v [v' [Ht [Ht' [Hn [Hn' Hrel]]]]]].

   apply F_related_values_all_leq in Hrel.
   destruct Hrel as [Hv [Hv' [L Hall]]]; subst.
   unfold open_tt in Hall.

   assert (forall X,
     X `notin` dom (E) `union` fv_tt T2 ->
     wf_typ ([(X, bind_kn K)]++E) (open_tt T2 X) kn_lin) as w.
     simpl in WFTall.
     eapply wft_all_inv; eauto.

   pick fresh y.
   assert (y `notin` L) as Fr'. auto.
   destruct (@Hall y (apply_delta_subst_typ dsubst T) (apply_delta_subst_typ dsubst' T) 
                                (F_Rel T (rho_nil++rsubst) (delta_nil++dsubst) (delta_nil++dsubst'))
                                Fr'
                   ) as [u [u' [Hn_vt2u [Hn_v't2'u' Hrel_wft]]]]; auto.
          split; try solve [apply wft_subst with (E:=E); auto].
              assert (ddom_env E [=] dom rsubst) as EQ.
                apply dom_rho_subst; auto.
              assert (y `notin` ddom_env E) as Fv.
                 apply dom__ddom; auto.
              rewrite EQ in Fv. auto.

   exists(u). exists (u').
       split. simpl_commut_subst in *; rewrite commut_delta_subst_open_tt with (dE:=E); auto.
                eapply typing_tapp; eauto using wft_subst.
       split. simpl_commut_subst in *; rewrite commut_delta_subst_open_tt with (dE:=E); auto.
                eapply typing_tapp; eauto using wft_subst.
       split.
       SCase "Norm".
       simpl_commut_subst.
       eapply m_congr_tapp; eauto.

      split.
      SCase "Norm".
      simpl_commut_subst.
      eapply m_congr_tapp; eauto.

      SCase "Frel".
      unfold open_tt.
      assert (F_related_values (open_tt_rec 0 T T2) (rho_nil++rsubst) (delta_nil++dsubst) (delta_nil++dsubst') u u' =
                  F_related_values (open_tt_rec 0 T T2) rsubst dsubst dsubst' u u').
         simpl. reflexivity.
      rewrite <- H0.
      apply parametricity_subst_value with
                (E:=E) (E':=@nil (atom*binding))
                (rsubst:=rsubst) (rsubst':=rho_nil)
                (k:=0)
                (t:=T2) (t2:=T) (K:=kn_lin) (Q:=K)
                (X:=y) (R:=(F_Rel T (rho_nil++rsubst) (delta_nil++dsubst) (delta_nil++dsubst')))
                ; auto.
        SSCase "wft".
          simpl_env. unfold open_tt in w. apply w; auto.

        SSCase "wft".
          simpl_env. rewrite subst_tt_intro_rec with (X:=y); auto.
          rewrite_env (map (subst_tb y T) nil ++ E).
          eapply wf_typ_subst_tb with (Q:=K); auto.
          apply w; auto.

        SSCase "Rel__R".
        unfold F_Rel__R. split; auto.

        SSCase "fv".
        eapply m_tapp_fv with (dsubst:=dsubst) (dsubst':=dsubst') (v:=v) (v':=v'); 
           eauto using notin_fv_te_typing.

        SSCase "eq".
        apply dom_delta_subst; auto.
        apply dom_delta_subst; auto.
        apply dom_rho_subst; auto.
        SSCase "rsubst".
        eapply rsubst_weaken with (X:=y) (rsubst:=rsubst) (rsubst':=rho_nil); eauto.
          apply dom_rho_subst; auto.
        SSCase "dsubst".   
        apply dsubst_weaken with (X:=y) (K:=K) (dsubst:=dsubst) (dsubst':=delta_nil) (t:=(apply_delta_subst_typ dsubst T)); auto.
          apply wft_subst_closed with (E:=E) (E':=@nil (atom*binding)) (dsubst:=dsubst) ; auto.
          apply dom_delta_subst in Hwfd; auto.
        SSCase "dsubst'".
        apply dsubst_weaken with (X:=y) (K:=K) (dsubst:=dsubst') (dsubst':=delta_nil) (t:=(apply_delta_subst_typ dsubst' T)); auto.
          apply wft_subst_closed with (E:=E) (E':=@nil (atom*binding)) (dsubst:=dsubst'); auto.
          apply dom_delta_subst in Hwfd'; auto.

    Case "typing_apair".
    assert (J:=Hrel_sub). apply F_related_subst__inversion in J. decompose [prod] J. clear J.

    assert (
      F_related_terms T1 rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e1)))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e1)))
     ) as FR_T1.
       apply IHHtyping1; auto.
    destruct FR_T1 as [v [v' [Ht1 [Ht1' [Hn1 [Hn1' Hrel1]]]]]].

    assert (
      F_related_terms T2 rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e2)))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e2)))
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
        apply F_related_values_with_req.
        repeat (split; simpl_commut_subst; auto).
        exists (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e1))).
        exists (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e2))).
        exists (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e1))).
        exists (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e2))).
        repeat(split; auto).
          exists (v). exists (v'). split; auto.
          exists (v0). exists (v'0). split; auto.

    Case "typing_fst".
    assert (J:=Hrel_sub). apply F_related_subst__inversion in J.
    destruct J as [[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe].
    assert (wf_typ E (typ_with T1 T2) kn_lin) as WFTwith.
      apply typing_regular in Htyping.
      destruct Htyping as [Hwfe' [Hwfle [He WFTwith]]]; auto.
    assert (
      F_related_terms (typ_with T1 T2) rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e)))
     ) as FR_With.
       apply IHHtyping; auto.
    destruct FR_With as [ee1 [ee1' [Ht [Ht' [Hn [Hn' FR_With]]]]]].

    assert (J1:=Htyping). assert (J2:=Htyping).
    apply  typing_subst_closed with (E:=E) (E':=@nil (atom*binding)) (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst) (D:=D) (D':=nil) in J1; auto.
        rewrite commut_delta_subst_with in J1; auto.
    apply  typing_subst_closed with (E:=E) (E':=@nil (atom*binding)) (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst') (D:=D) (D':=nil) in J2; auto.
        rewrite commut_delta_subst_with in J2; auto.
    apply congr_fst with (T1:=apply_delta_subst_typ dsubst T1) (T2:=apply_delta_subst_typ dsubst T2) in Hn; auto.
    apply congr_fst with (T1:=apply_delta_subst_typ dsubst' T1) (T2:=apply_delta_subst_typ dsubst' T2) in Hn'; auto.
    destruct Hn as [e1 [e2 [Hbrc Heq]]].
    destruct Hn' as [e1' [e2' [Hbrc' Heq']]].
    apply F_related_values_with_leq in FR_With.
    subst.
    destruct FR_With as [Hv [Hv' [ee1 [ee2 [ee1' [ee2' [Heq [Heq' 
                                [[u1 [u1' [[Hbrc_e1u1 Hu1][[Hbrc_e1'u1' Hu1'] Hrel_wft1]]]] 
                                 [u2 [u2' [[Hbrc_e2u2 Hu2][[Hbrc_e2'u2' Hu2'] Hrel_wft2]]]]]
                              ]]]]]]]]; subst.
    inversion Heq. inversion Heq'. subst. clear Heq Heq'.
    exists(u1). exists(u1').
        repeat(split; simpl_commut_subst; auto; try solve [
          apply typing_fst with (T2:=apply_delta_subst_typ dsubst T2);
            apply  typing_subst_closed with (E:=E) (E':=@nil (atom*binding)) (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst) (D:=D) (D':=nil) in Htyping; auto |
          apply typing_fst with (T2:=apply_delta_subst_typ dsubst' T2);
            apply  typing_subst_closed with (E:=E) (E':=@nil (atom*binding))  (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst') (D:=D) (D':=nil) in Htyping; auto |
          split; auto; apply bigstep_red__trans with (e':=ee1); auto |
          split; auto; apply bigstep_red__trans with (e':=ee1'); auto]).
        SCase "Frel".

    Case "typing_snd".
    assert (J:=Hrel_sub). apply F_related_subst__inversion in J.
    destruct J as [[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe].
    assert (wf_typ E (typ_with T1 T2) kn_lin) as WFTwith.
      apply typing_regular in Htyping.
      destruct Htyping as [Hwfe' [Hwfle [He WFTwith]]]; auto.
    assert (
      F_related_terms (typ_with T1 T2) rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e)))
     ) as FR_With.
       apply IHHtyping; auto.
    destruct FR_With as [ee2 [ee2' [Ht [Ht' [Hn [Hn' FR_With]]]]]].

    assert (J1:=Htyping). assert (J2:=Htyping).
    apply  typing_subst_closed with (E:=E) (E':=@nil (atom*binding)) (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst) (D:=D) (D':=nil) in J1; auto.
        rewrite commut_delta_subst_with in J1; auto.
    apply  typing_subst_closed with (E:=E) (E':=@nil (atom*binding)) (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst') (D:=D) (D':=nil) in J2; auto.
        rewrite commut_delta_subst_with in J2; auto.
    apply congr_snd with (T1:=apply_delta_subst_typ dsubst T1) (T2:=apply_delta_subst_typ dsubst T2) in Hn; auto.
    apply congr_snd with (T1:=apply_delta_subst_typ dsubst' T1) (T2:=apply_delta_subst_typ dsubst' T2) in Hn'; auto.
    destruct Hn as [e1 [e2 [Hbrc Heq]]].
    destruct Hn' as [e1' [e2' [Hbrc' Heq']]].
    apply F_related_values_with_leq in FR_With.
    subst.
    destruct FR_With as [Hv [Hv' [ee1 [ee2 [ee1' [ee2' [Heq [Heq' 
                                [[u1 [u1' [[Hbrc_e1u1 Hu1][[Hbrc_e1'u1' Hu1'] Hrel_wft1]]]] 
                                 [u2 [u2' [[Hbrc_e2u2 Hu2][[Hbrc_e2'u2' Hu2'] Hrel_wft2]]]]]
                              ]]]]]]]]; subst.
    inversion Heq. inversion Heq'. subst. clear Heq Heq'.
    exists (u2). exists (u2').
        repeat(split; simpl_commut_subst; auto; try solve [
          apply typing_snd with (T1:=apply_delta_subst_typ dsubst T1);
            apply  typing_subst_closed with (E:=E) (E':=@nil (atom*binding)) (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst) (D:=D) (D':=nil) in Htyping; auto |
          apply typing_snd with (T1:=apply_delta_subst_typ dsubst' T1);
            apply  typing_subst_closed with (E:=E) (E':=@nil (atom*binding))  (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst') (D:=D) (D':=nil) in Htyping; auto |
          split; auto; apply bigstep_red__trans with (e':=ee2); auto |
          split; auto; apply bigstep_red__trans with (e':=ee2'); auto]).

Qed.

End Parametricity.


(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../../../metatheory" "-I" "../linf") ***
*** End: ***
 *)
