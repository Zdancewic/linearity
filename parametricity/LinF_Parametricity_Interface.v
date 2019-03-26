(** Authors: Jianzhou Zhao. *)

Require Export LinF_Parametricity_Pre.
Require Import Program.

Module Type IParametricity.

(* ********************************************************************** *)
(** * Wf Relations *)

Definition wfr (r : rel) (T T' : typ) (K:kn) : Prop :=
  (wf_typ nil T K) /\
  (wf_typ nil T' K).

Axiom wfr_inv : forall r T T' K,
  wfr r T T' K->
  (wf_typ nil T K) /\
  (wf_typ nil T' K).

Axiom wfr_left_inv : forall t t' R K,
  wfr R t t' K -> wf_typ nil t K.

Axiom wfr_right_inv : forall t t' R K,
  wfr R t t' K -> wf_typ nil t' K.


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
Axiom F_related_values_bvar_eq: forall i (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp),
  F_related_values (typ_bvar i) rsubst dsubst dsubst' v v' <-> False.

Axiom F_related_values_bvar_leq: forall i (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp),
  F_related_values (typ_bvar i) rsubst dsubst dsubst' v v' -> False.

Axiom F_related_values_bvar_req: forall i (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp),
  False -> 
  F_related_values (typ_bvar i) rsubst dsubst dsubst' v v'.

Axiom F_related_values_fvar_eq: forall X (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp),
  F_related_values (typ_fvar X) rsubst dsubst dsubst' v v' <->
    exists R,
     (binds X R rsubst) /\ (value v) /\ (value v') /\ (R v v')
  .

Axiom F_related_values_fvar_leq: forall X  (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp),
  F_related_values (typ_fvar X) rsubst dsubst dsubst' v v' ->
    exists R,
      (binds X R rsubst) /\ (value v) /\ (value v') /\ (R v v')
  .

Axiom F_related_values_fvar_req: forall X  (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp),
  (exists R,
    (binds X R rsubst) /\ (value v) /\ (value v') /\ (R v v')) ->
  F_related_values (typ_fvar X) rsubst dsubst dsubst' v v'.

Axiom F_related_values_arrow_eq: forall (t1 t2:typ)  (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) K,
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

Axiom F_related_values_arrow_leq: forall (t1 t2:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) K,
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

Axiom F_related_values_arrow_req: forall (t1 t2:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) K,
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

Axiom F_related_values_all_eq: forall (t1:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) K,
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

Axiom F_related_values_all_leq: forall (t1:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) K,
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

Axiom F_related_values_all_req: forall (t1:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) K,
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

Axiom F_related_values_with_eq: forall (t1 t2:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp),
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

Axiom F_related_values_with_leq: forall (t1 t2:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp),
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

Axiom F_related_values_with_req: forall (t1 t2:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp),
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

(* ********************************************************************** *)
(** * Inversion *)

Axiom F_related_values_inversion: forall t v v' rsubst dsubst dsubst',
  F_related_values t rsubst dsubst dsubst' v v' ->
  ((value v)* (value v'))%type.

Axiom F_Rsubst__wf_subst:
  forall (E:env) (rsubst:rho_subst) (dsubst:delta_subst) (dsubst':delta_subst),
  F_Rsubst E rsubst dsubst dsubst'  ->
  ((wf_delta_subst E dsubst) * (wf_delta_subst E dsubst') * (wf_rho_subst E rsubst))%type.

Axiom Frel_inversion: forall t rsubst dsubst dsubst' v v',
  F_Rel t rsubst dsubst dsubst' v v' ->
  ((value v)* (value v'))%type.

Axiom F_related_subst__inversion:
  forall (E:env) (lE:lenv) (rsubst:rho_subst) (dsubst:delta_subst) (dsubst':delta_subst) gsubst gsubst' lgsubst lgsubst',
  F_related_subst E lE gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
  ((wf_delta_subst E dsubst) * (wf_delta_subst E dsubst') *
   (wf_lgamma_subst E lE dsubst gsubst lgsubst)* (wf_lgamma_subst E lE dsubst' gsubst' lgsubst') *
   (wf_rho_subst E rsubst) * (wf_env E))%type.

(* **************************************** *)
(** * Weaken and Stronger of SystemF Relations *)

Axiom Frel_weaken:  forall t E E' v v' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 X R t2 t2' K,
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

Axiom Frel_weaken_head:  forall t E v v' rsubst dsubst dsubst' X R t2 t2' K,
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

Axiom Frel_stronger:  forall t E E' v v' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 X R t2 t2' K,
  F_related_values t (rsubst'++[(X, R)]++rsubst) (dsubst0++[(X, t2)]++dsubst) (dsubst'0++[(X, t2')]++dsubst') v v' ->
  ddom_env E [=] dom dsubst ->
  ddom_env E [=] dom dsubst' ->
  ddom_env E' [=] dom dsubst0 ->
  ddom_env E' [=] dom dsubst'0 ->
  ddom_env E [=] dom rsubst ->
  ddom_env E' [=] dom rsubst' ->
  X `notin` (fv_env E `union` fv_env E' `union` (fv_tt t))->
  wfr R t2 t2' K ->
  wf_rho_subst (E'++[(X, bind_kn K)]++E) (rsubst'++[(X, R)]++rsubst) ->
  wf_delta_subst (E'++[(X, bind_kn K)]++E) (dsubst0++[(X, t2)]++dsubst) ->
  wf_delta_subst (E'++[(X, bind_kn K)]++E) (dsubst'0++[(X, t2')]++dsubst') ->
  F_related_values t (rsubst'++rsubst) (dsubst0++dsubst) (dsubst'0++dsubst') v v'
  .

Axiom bindsgE__bindsgsubst: forall E lE gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' x T,
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

Axiom lbindsgE__lbindsgsubst: forall E lE gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' x T,
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

(*******************************************************************************)
(** subst *)

Definition F_Rel__R (t:typ) (E:env) (rsubst:rho_subst) dsubst dsubst' (R:rel) :=
  wf_delta_subst E dsubst /\  wf_delta_subst E dsubst' /\  wf_rho_subst E rsubst /\
  (forall v v',
    ((F_Rel t rsubst dsubst dsubst' v v' -> R v v') 
   * (R v v'->F_Rel t rsubst dsubst dsubst' v v')) % type)
  .

Axiom F_Rel__R__wfr: forall (E:env) (t:typ) (rsubst:rho_subst) dsubst dsubst' (R:rel) K,
  F_Rel__R t E rsubst dsubst dsubst' R -> 
  wf_typ E t K ->
  wfr R (apply_delta_subst_typ dsubst t) (apply_delta_subst_typ dsubst' t) K.

Axiom parametricity_subst_value : forall t E E' e e' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 X R t2 k K Q,
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
  (F_related_values (open_tt_rec k (typ_fvar X) t) (rsubst'++[(X, R)]++rsubst ) (dsubst0++[(X, (apply_delta_subst_typ (dsubst0++dsubst) t2))]++dsubst) (dsubst'0++[(X,(apply_delta_subst_typ (dsubst'0++dsubst') t2))]++dsubst') e e' ->
  wf_rho_subst (E'++[(X, bind_kn Q)]++E) (rsubst'++[(X, R)]++rsubst) ->
  wf_delta_subst (E'++[(X, bind_kn Q)]++E) (dsubst0++[(X, (apply_delta_subst_typ (dsubst0++dsubst) t2))]++dsubst) -> 
  wf_delta_subst (E'++[(X, bind_kn Q)]++E) (dsubst'0++[(X, (apply_delta_subst_typ (dsubst'0++dsubst') t2))]++dsubst') -> 
  F_related_values (open_tt_rec k t2 t) (rsubst'++rsubst) (dsubst0++dsubst) (dsubst'0++dsubst') e e')
  .

(*******************************************************************************)
(** F_related_subst_split *)

Axiom F_related_subst_split: forall E lE lE1 lE2 dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
   F_related_subst E lE gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
   lenv_split E lE1 lE2 lE ->
   exists lgsubst1, exists lgsubst1', exists lgsubst2, exists lgsubst2',
     lgamma_subst_split E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst /\
     lgamma_subst_split E lE dsubst' gsubst' lgsubst1' lgsubst2' lgsubst' /\
     F_related_subst E lE1 gsubst gsubst' lgsubst1 lgsubst1' rsubst dsubst dsubst' /\     
     F_related_subst E lE2 gsubst gsubst' lgsubst2 lgsubst2' rsubst dsubst dsubst'.

(*******************************************************************************)
(** parametricity *)

Axiom parametricity: forall E lE e t dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
   typing E lE e t ->
   F_related_subst E lE gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
   F_Rsubst E rsubst dsubst dsubst'->
   F_related_terms t rsubst dsubst dsubst'
                                 (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
                                 (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e)))
   .

End IParametricity.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../../../metatheory" "-I" "../linf") ***
*** End: ***
 *)
