(** Authors: Jianzhou Zhao. *)

Require Export LinF_OParametricity_Pre.
Require Import LinF_Renaming.
Require Import Program.

Module Type IOParametricity.

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

Definition wfor (E:env) (r : rel) (T T' : typ) (K:kn) : Prop :=
  (wf_typ E T K) /\
  (wf_typ E T' K) /\
  admissible E r
  .

Axiom wfor_inv : forall E r T T' K,
  wfor E r T T' K->
  (wf_typ E T K) /\
  (wf_typ E T' K) /\
  admissible E r
  .

Axiom wfor_left_inv : forall E t t' R K,
  wfor E R t t' K -> wf_typ E t K.

Axiom wfor_right_inv : forall E t t' R K,
  wfor E R t t' K -> wf_typ E t' K.

Axiom wfor_renaming_inv : forall E r T T' K,
  wfor E r T T' K->
  admissible E r
  .
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
  | typ_arrow K t1 t2 =>
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
       F_Related_ovalues t1 rsubst dsubst dsubst' x x' Env lEnv1
       ->
       (exists u, exists u', 
        normalize (exp_app v x) u /\
        normalize (exp_app v' x') u' /\
        F_Related_ovalues t2 rsubst dsubst dsubst' u u' Env (lEnv1++lEnv))
      )
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
          wfor Env R t2 t2' K ->
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
    forall (E:env) (lE:lenv) (gsubst gsubst' lgsubst lgsubst':gamma_subst) (rsubst:rho_subst) (dsubst dsubst':delta_subst) Env lEnv X R t t' K,
      F_Related_osubst E lE gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
      X `notin` (fv_env E) `union` (fv_lenv lE) `union`  (fv_env Env) `union` (fv_lenv lEnv) ->
      wfor Env R t t' K ->
      F_Related_osubst ([(X, bind_kn K)]++E) lE gsubst gsubst' lgsubst lgsubst'
                                   ([(X,R)]++rsubst) ([(X,t)]++dsubst) ([(X,t')]++dsubst') Env lEnv
  | F_Related_osubst_typ :
    (*
      gsubst ~ gsubst' : genv | rsubst, dsubst, dsubst'
      e ~ e' : t | rho_subst
     -----------------------------------------------------------------
      (gsubst, x->e) ~ (gsubst',x->e') : (genv, x:t) | rho_subst, dsubst, dsubst'
    *)
    forall (E:env)(lE:lenv)(gsubst gsubst' lgsubst lgsubst':gamma_subst) (v v':exp) (t:typ) (rsubst:rho_subst) (dsubst dsubst':delta_subst) Env lEnv (x:atom),
      F_Related_osubst E lE gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
      typing Env lempty v (apply_delta_subst_typ dsubst t) ->
      typing Env lempty v' (apply_delta_subst_typ dsubst' t) ->
      F_Related_ovalues t rsubst dsubst dsubst' v v' Env lempty ->
      x `notin` ((fv_env E) `union` (fv_lenv lE) `union` (fv_tt t)) `union`  (fv_env Env) `union` (fv_lenv lEnv) ->
      wf_typ E t kn_nonlin ->
      F_Related_osubst ([(x, bind_typ t)]++E) lE
                   ([(x, v)]++gsubst) ([(x, v')]++gsubst') lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv 
  | F_Related_osubst_ltyp :
    (*
      gsubst ~ gsubst' : genv | rsubst, dsubst, dsubst'
      e ~ e' : t | rho_subst
     -----------------------------------------------------------------
      (gsubst, x->e) ~ (gsubst',x->e') : (genv, x:t) | rho_subst, dsubst, dsubst'
    *)
    forall (E:env)(lE:lenv)(gsubst gsubst' lgsubst lgsubst':gamma_subst) (v v':exp) (t:typ) (rsubst:rho_subst) (dsubst dsubst':delta_subst) Env lEnv1 lEnv2 (x:atom),
      F_Related_osubst E lE gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv1 ->
      typing Env lEnv2 v (apply_delta_subst_typ dsubst t) ->
      typing Env lEnv2 v' (apply_delta_subst_typ dsubst' t) ->
      disjoint E lEnv2 /\ disjoint lE lEnv2 ->      
      wf_lenv Env (lEnv2++lEnv1) ->
      F_Related_ovalues t rsubst dsubst dsubst' v v' Env lEnv2 ->
      x `notin` ((fv_env E) `union` (fv_lenv lE) `union` (fv_tt t)) `union`  (fv_env Env) `union` (fv_lenv lEnv1) `union` (fv_lenv lEnv2) ->
      wf_typ E t kn_lin ->
      F_Related_osubst E ([(x, lbind_typ t)]++lE)
                   gsubst gsubst' ([(x, v)]++lgsubst) ([(x, v')]++lgsubst') rsubst dsubst dsubst' Env (lEnv2++lEnv1)
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
    forall (E:env) (rsubst:rho_subst) (dsubst:delta_subst) (dsubst':delta_subst) Env R t t' X K,
      F_Rosubst E rsubst dsubst dsubst' Env ->
      wfor Env R t t' K ->
      X `notin` (fv_env E) `union` (fv_env Env)->
      F_Rosubst ([(X, bind_kn K)]++E) ([(X, R)]++rsubst) ([(X, t)]++dsubst) ([(X, t')]++dsubst') Env
  | F_Rosubst_typ :
    (*
      env |- rho_subst \in delta_subst <-> delta_subst'
     -----------------------------------------------------------------
      env, x~:T |- rho_subst \in delta_subst <-> delta_subst'
    *)
    forall (E:env) (rsubst:rho_subst) (dsubst:delta_subst) (dsubst':delta_subst) Env x T,
      F_Rosubst E rsubst dsubst dsubst' Env ->
      wf_typ E T kn_nonlin ->
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
      (binds X R rsubst) /\ (value v) /\ (value v') /\ (admissible Env R) /\ (R v v')
  .

Axiom F_Related_ovalues_fvar_leq: forall X  (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) Env lEnv,
  F_Related_ovalues (typ_fvar X) rsubst dsubst dsubst' v v' Env lEnv ->
    exists R,
      (binds X R rsubst) /\ (value v) /\ (value v') /\ (admissible Env R) /\ (R v v')
  .

Axiom F_Related_ovalues_fvar_req: forall X  (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) Env lEnv,
  (exists R,
    (binds X R rsubst) /\ (value v) /\ (value v') /\ (admissible Env R) /\ (R v v')) ->
  F_Related_ovalues (typ_fvar X) rsubst dsubst dsubst' v v' Env lEnv.

Axiom F_Related_ovalues_arrow_eq: forall (t1 t2:typ)  (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) K Env lEnv,
  F_Related_ovalues (typ_arrow K t1 t2) rsubst dsubst dsubst' v v' Env lEnv
  <->
  (
    (value v) /\ (value v') /\
    (exists L,
      (forall lEnv1 x x',
       typing Env lEnv1 x (apply_delta_subst_typ dsubst t1) ->
       typing Env lEnv1 x' (apply_delta_subst_typ dsubst' t1) ->
       wf_lenv Env (lEnv1++lEnv) ->
       disjdom L (dom lEnv1) ->
       F_Related_ovalues t1 rsubst dsubst dsubst' x x' Env lEnv1
       ->
       (exists u, exists u', 
        normalize (exp_app v x) u /\
        normalize (exp_app v' x') u' /\
        F_Related_ovalues t2 rsubst dsubst dsubst' u u' Env (lEnv1++lEnv))
      )
    )
  )
   .

Axiom F_Related_ovalues_arrow_leq: forall (t1 t2:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) K Env lEnv,
  F_Related_ovalues (typ_arrow K t1 t2) rsubst dsubst dsubst' v v' Env lEnv
  ->
  (
    (value v) /\ (value v') /\
    (exists L,
      (forall lEnv1 x x',
       typing Env lEnv1 x (apply_delta_subst_typ dsubst t1) ->
       typing Env lEnv1 x' (apply_delta_subst_typ dsubst' t1) ->
       wf_lenv Env (lEnv1++lEnv) ->
       disjdom L (dom lEnv1) ->
       F_Related_ovalues t1 rsubst dsubst dsubst' x x' Env lEnv1
       ->
       (exists u, exists u', 
        normalize (exp_app v x) u /\
        normalize (exp_app v' x') u' /\
        F_Related_ovalues t2 rsubst dsubst dsubst' u u' Env (lEnv1++lEnv))
      )
    )
  )
   .

Axiom F_Related_ovalues_arrow_req: forall (t1 t2:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) K Env lEnv,
  (
    (value v) /\ (value v') /\
    (exists L,
      (forall lEnv1 x x',
       typing Env lEnv1 x (apply_delta_subst_typ dsubst t1) ->
       typing Env lEnv1 x' (apply_delta_subst_typ dsubst' t1) ->
       wf_lenv Env (lEnv1++lEnv) ->
       disjdom L (dom lEnv1) ->
       F_Related_ovalues t1 rsubst dsubst dsubst' x x' Env lEnv1
       ->
       (exists u, exists u', 
        normalize (exp_app v x) u /\
        normalize (exp_app v' x') u' /\
        F_Related_ovalues t2 rsubst dsubst dsubst' u u' Env (lEnv1++lEnv))
      )
    )
  ) ->
  F_Related_ovalues (typ_arrow K t1 t2) rsubst dsubst dsubst' v v' Env lEnv
   .

Axiom F_Related_ovalues_all_eq: forall (t1:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) K Env lEnv,
  F_Related_ovalues (typ_all K t1) rsubst dsubst dsubst' v v' Env lEnv
  <->
      (
      (value v) /\ (value v') /\
      (exists L,
         (forall (X:atom) t2 t2' R (Fr:X `notin` L),
         wfor Env R t2 t2' K ->
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

Axiom F_Related_ovalues_all_leq: forall (t1:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) K Env lEnv,
  F_Related_ovalues (typ_all K t1) rsubst dsubst dsubst' v v' Env lEnv
  ->
      (
      (value v) /\ (value v') /\
      (exists L,
         (forall (X:atom) t2 t2' R (Fr:X `notin` L),
         wfor Env R t2 t2' K ->
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

Axiom F_Related_ovalues_all_req: forall (t1:typ) (rsubst:rho_subst)(dsubst dsubst':delta_subst)(v v':exp) K Env lEnv,
      (
      (value v) /\ (value v') /\
      (exists L,
         (forall (X:atom) t2 t2' R (Fr:X `notin` L),
         wfor Env R t2 t2' K ->
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
  F_Related_ovalues (typ_all K t1) rsubst dsubst dsubst' v v' Env lEnv
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
(** Renaming *)

Axiom Forel_lin_renaming : forall t rsubst dsubst dsubst' e e' E Env lEnv x0 y0,
  F_Related_ovalues t rsubst dsubst dsubst' e e' Env lEnv ->
  wf_rho_subst E rsubst ->
  wf_delta_osubst E dsubst Env ->
  wf_delta_osubst E dsubst' Env ->
  typing Env lEnv e (apply_delta_subst_typ dsubst t) ->
  typing Env lEnv e' (apply_delta_subst_typ dsubst' t) ->
  x0 `notin` dom Env ->
  y0 `notin` dom Env `union` dom lEnv ->
  F_Related_ovalues t rsubst dsubst dsubst' (subst_ee x0 y0 e) (subst_ee x0 y0 e') Env (subst_atom_lenv lEnv x0 y0).

Axiom Forel_lin_renamings : forall t rsubst dsubst dsubst' e e' E Env lEnv asubst,
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

(*******************************************************************************)
(** Reverse Renaming *)

Axiom Forel_lin_rev_renamings : forall t rsubst dsubst dsubst' e e' E Env lEnv asubst,
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

(*******************************************************************************)
(** Dom Equal *)

Axiom Forel_lin_domeq : forall t rsubst dsubst dsubst' e e' Env lEnv lEnv',
  F_Related_ovalues t rsubst dsubst dsubst' e e' Env lEnv ->
  wf_lenv Env lEnv ->
  dom lEnv [=] dom lEnv' ->
  F_Related_ovalues t rsubst dsubst dsubst' e e' Env lEnv'.

(* **************************************** *)
(** * Weaken and Stronger of SystemF Relations *)

Axiom Forel_weaken:  forall t E E' v v' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 Env lEnv X R t2 t2' K,
  ((F_Related_ovalues t (rsubst'++rsubst) (dsubst0++dsubst) (dsubst'0++dsubst') v v' Env lEnv ->
  ddom_env E [=] dom dsubst ->
  ddom_env E [=] dom dsubst' ->
  ddom_env E' [=] dom dsubst0 ->
  ddom_env E' [=] dom dsubst'0 ->
  ddom_env E [=] dom rsubst ->
  ddom_env E' [=] dom rsubst' ->
  X `notin` (fv_env E `union` fv_env E' `union` (fv_tt t) `union` fv_env Env `union` fv_lenv lEnv)->
  wf_typ Env t2 K ->
  wf_typ Env t2' K ->
  wf_rho_subst (E'++E) (rsubst'++rsubst) ->
  wf_delta_osubst (E'++E) (dsubst0++dsubst) Env ->
  wf_delta_osubst (E'++E) (dsubst'0++dsubst') Env ->
  F_Related_ovalues t (rsubst'++[(X, R)]++rsubst) (dsubst0++[(X, t2)]++dsubst) (dsubst'0++[(X, t2')]++dsubst') v v' Env lEnv))
  .

Axiom Forel_weaken_head:  forall t E v v' rsubst dsubst dsubst' Env lEnv X R t2 t2' K,
  ((F_Related_ovalues t rsubst dsubst dsubst' v v' Env lEnv ->
  ddom_env E [=] dom dsubst ->
  ddom_env E [=] dom dsubst' ->
  ddom_env E [=] dom rsubst ->
  X `notin` (fv_env E `union` (fv_tt t) `union` fv_env Env `union` fv_lenv lEnv)->
  wf_typ Env t2 K ->
  wf_typ Env t2' K ->
  wf_rho_subst E rsubst ->
  wf_delta_osubst E dsubst Env ->
  wf_delta_osubst E dsubst' Env ->
  F_Related_ovalues t ([(X, R)]++rsubst) ([(X, t2)]++dsubst) ([(X, t2')]++dsubst') v v' Env lEnv))
  .

Axiom Forel_stronger:  forall t E E' v v' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 Env lEnv X R t2 t2' K,
  F_Related_ovalues t (rsubst'++[(X,R)]++rsubst) (dsubst0++[(X,t2)]++dsubst) (dsubst'0++[(X,t2')]++dsubst') v v' Env lEnv ->
  ddom_env E [=] dom dsubst ->
  ddom_env E [=] dom dsubst' ->
  ddom_env E' [=] dom dsubst0 ->
  ddom_env E' [=] dom dsubst'0 ->
  ddom_env E [=] dom rsubst ->
  ddom_env E' [=] dom rsubst' ->
  X `notin` (fv_env E `union` fv_env E' `union` (fv_tt t) `union` fv_env Env `union` fv_lenv lEnv)->
  wf_typ Env t2 K ->
  wf_typ Env t2' K ->
  wf_rho_subst (E'++[(X,bind_kn K)]++E) (rsubst'++[(X,R)]++rsubst) ->
  wf_delta_osubst (E'++[(X,bind_kn K)]++E) (dsubst0++[(X,t2)]++dsubst) Env ->
  wf_delta_osubst (E'++[(X,bind_kn K)]++E) (dsubst'0++[(X,t2')]++dsubst') Env ->
  F_Related_ovalues t (rsubst'++rsubst) (dsubst0++dsubst) (dsubst'0++dsubst') v v' Env lEnv 
  .

Axiom bindosgE__bindosgsubst: forall E lE gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv x T,
    F_Related_osubst E lE gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
    binds x (bind_typ T) E ->
    wf_typ E T kn_nonlin ->
    x `notin` dom lgsubst /\ x `notin` dom lgsubst' /\
    (exists v, exists v',
                ((binds x (v) gsubst)
                *(binds x (v') gsubst')
                *(typing Env lempty v (apply_delta_subst_typ dsubst T))*(typing Env lempty v' (apply_delta_subst_typ dsubst' T))
                *(F_Related_ovalues T rsubst dsubst dsubst' v v' Env lempty))%type)
    .

Axiom lbindosgE__lbindosgsubst: forall E gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv x T,
    F_Related_osubst E [(x, lbind_typ T)] gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
    wf_typ E T kn_lin ->
    x `notin` dom gsubst /\ x `notin` dom gsubst' /\
    (exists v, exists v',
                ((binds x (v) lgsubst)
                *(binds x (v') lgsubst')
                *(typing Env lEnv v (apply_delta_subst_typ dsubst T))*(typing Env lEnv v' (apply_delta_subst_typ dsubst' T))
                *(F_Related_ovalues T rsubst dsubst dsubst' v v' Env lEnv))%type)
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

Axiom F_FORel__R__wfor: forall (E:env) (t:typ) (rsubst:rho_subst) dsubst dsubst' Env (R:rel) K,
  F_FORel__R t E rsubst dsubst dsubst' Env R -> 
  wf_typ E t K ->
  wfor Env R (apply_delta_subst_typ dsubst t) (apply_delta_subst_typ dsubst' t) K.

Axiom oparametricity_subst_value : forall t E E' e e' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 Env lEnv X R t2 k K Q,
  wf_typ (E'++[(X, bind_kn Q)]++E) (open_tt_rec k (typ_fvar X) t) K ->
  wf_typ (E'++E) (open_tt_rec k t2 t) K ->
  wf_typ (E'++E) t2 Q ->
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
  wf_rho_subst (E'++[(X, bind_kn Q)]++E) (rsubst'++[(X, R)]++rsubst) ->
  wf_delta_osubst (E'++[(X, bind_kn Q)]++E) (dsubst0++[(X, (apply_delta_subst_typ (dsubst0++dsubst) t2))]++dsubst) Env -> 
  wf_delta_osubst (E'++[(X, bind_kn Q)]++E) (dsubst'0++[(X, (apply_delta_subst_typ (dsubst'0++dsubst') t2))]++dsubst') Env -> 
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
*** coq-prog-args: ("-emacs-U" "-I" "../../../metatheory" "-I" "../linf") ***
*** End: ***
 *)
