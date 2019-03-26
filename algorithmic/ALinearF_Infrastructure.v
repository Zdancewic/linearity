(** Infrastructure lemmas and tactic definitions for 
     Algorithmic Lightweight Linear F.

    Authors: Aileen Zhang, Jianzhou Zhao, and Steve Zdancewic.

    This file contains a number of definitions, tactics, and lemmas
    that are based only on the syntax of the language at hand.  While
    the exact statements of everything here would change for a
    different language, the general structure of this file (i.e., the
    sequence of definitions, tactics, and lemmas) would remain the
    same.

    Table of contents:
      - #<a href="##subst">Substitution</a>#
      - #<a href="##auto">Automation</a># *)

Require Export ALinearF_Definitions.

(* ********************************************************************** *)
(** * #<a name="subst"></a># Substitution *)

(** In this section, we define substitution for expression and type
    variables appearing in types, expressions, and environments.
    Substitution differs from opening because opening replaces indices
    whereas substitution replaces free variables.  The definitions
    below are relatively simple for two reasons.
      - We are using locally nameless representation, where bound
        variables are represented using indices.  Thus, there is no
        need to rename variables to avoid capture.
      - The definitions below assume that the term being substituted
        in, i.e., the second argument to each function, is locally
        closed.  Thus, there is no need to shift indices when passing
        under a binder. *)

Definition subst_tgb (Z : atom) (P : typ) (b : gbinding) : gbinding :=
  match b with
  | gbind_kn K => gbind_kn K
  | gbind_typ T => gbind_typ (subst_tt Z P T)
  end.

Definition subst_tdb (Z : atom) (P : typ) (b : dbinding) : dbinding :=
  match b with
  | dbind_typ T => dbind_typ (subst_tt Z P T)
  end.

Fixpoint denv_fv_tt (D : denv) : atoms :=
  match D with
    | nil => {}
    | (x, dbind_typ T) :: D' => (fv_tt T) `union` (denv_fv_tt D')
  end.

Fixpoint genv_fv_tt (G : genv) : atoms :=
  match G with 
   | nil => {}
   | (x, gbind_typ T) :: G' => (fv_tt T) `union` (genv_fv_tt G')
   | (X, gbind_kn K) :: G' => genv_fv_tt G'
  end.

Lemma subst_tdb_fresh : forall D Z T,
   Z `notin` denv_fv_tt D ->
   D = map (subst_tdb Z T) D.
Proof with auto*.
  induction D; simpl; intros Z T H; f_equal...
    destruct a as [x b]. destruct b.
    simpl. rewrite <- subst_tt_fresh; auto.
    rewrite <- IHD; auto.
Qed.

(* ********************************************************************** *)
(** * free vars *)

Lemma in_fv_ee_open_ee_rec : forall (x y : atom) e kk,
  x `in` fv_ee e ->
  x `in` fv_ee (open_ee_rec kk y e).
Proof.
  (exp_cases (induction e) Case); intros kk; simpl in *; auto.
  Case "exp_bvar".
    intros. absurd_hyp H; fsetdec.
  Case "exp_app".
Admitted.

Lemma in_fv_ee_open_ee : forall (x y : atom) e,
  x `in` fv_ee e ->
  x `in` fv_ee (open_ee e y).
Proof.
  unfold open_ee.
  auto using in_fv_ee_open_ee_rec.
Qed.

Hint Resolve in_fv_ee_open_ee.

Lemma notin_open_ee_fv_ee : forall (x y : atom) e, 
  x `notin` fv_ee (open_ee e y) ->
  x `notin` fv_ee e.
Proof with eauto.
  intros. assert (x `in` fv_ee e -> False). intros.
  assert ( x `in` fv_ee (open_ee e y)). auto. fsetdec. fsetdec.
Qed.

Lemma in_fv_ee_open_te_rec : forall (x Y : atom) e kk,
  x `in` fv_ee e ->
  x `in` fv_ee (open_te_rec kk Y e).
Proof.
  (exp_cases (induction e) Case); intros kk; simpl in *; auto.
  Case "exp_app".
Admitted.

Lemma in_fv_ee_open_te : forall (x Y : atom) e,
  x `in` fv_ee e ->
  x `in` fv_ee (open_te e Y).
Proof.
  unfold open_te.
  auto using in_fv_ee_open_te_rec.
Qed.

Lemma notin_fv_ee_open_ee_rec : forall (x y : atom) e kk,
  x `notin` fv_ee e ->
  x <> y ->
  x `notin` fv_ee (open_ee_rec kk y e).
Proof.
  (exp_cases (induction e) Case); intros kk; simpl in *; auto.
  Case "exp_bvar".   
    destruct (kk === n); simpl; auto.
Qed.

Lemma notin_fv_ee_open_ee : forall (x y : atom) e,
  x `notin` fv_ee e ->
  x <> y ->
  x `notin` fv_ee (open_ee e y).
Proof.
  unfold open_ee.
  auto using notin_fv_ee_open_ee_rec.
Qed.
Hint Resolve notin_fv_ee_open_ee.

Lemma in_open_ee_fv_ee : forall (x y : atom) e, 
  x `in` fv_ee (open_ee e y) ->
  x <> y ->
  x `in` fv_ee e.
Proof with eauto.
  intros. assert (x `notin` fv_ee e -> False). 
  intros. assert (x `notin` fv_ee (open_ee e y)). auto. fsetdec. fsetdec.
Qed.
Hint Resolve in_open_ee_fv_ee.

Lemma notin_fv_ee_open_te_rec : forall (x Y : atom) e kk,
  x `notin` fv_ee e ->
  x <> Y ->
  x `notin` fv_ee (open_te_rec kk Y e).
Proof.
  (exp_cases (induction e) Case); intros kk; simpl in *; auto.
Qed.

Lemma notin_fv_ee_open_te : forall (x Y : atom) e,
  x `notin` fv_ee e ->
  x <> Y ->
  x `notin` fv_ee (open_te e Y).
Proof.
  unfold open_te.
  auto using notin_fv_ee_open_te_rec.
Qed.

Hint Resolve notin_fv_ee_open_te.

Lemma  in_open_te_fv_ee : forall (x Y : atom) e,
  x `in` fv_ee (open_te e Y)->
  x <> Y ->
  x `in` fv_ee e.
Proof with eauto.
  intros. assert (x `notin` fv_ee e -> False). intros.
  assert (x `notin` fv_ee (open_te e Y)). auto. auto. fsetdec.
Qed.

Hint Resolve in_open_te_fv_ee.

Lemma notin_open_te_fv_ee_rec : forall (x Y : atom) e k,
  x `notin` fv_ee (open_te_rec k Y e)->
  x <> Y ->
  x `notin` fv_ee e.
Proof with eauto.
  intros. generalize dependent k.
  (exp_cases (induction e) Case); intros; simpl in *; auto. eapply IHe. eauto.
  assert (x `notin` (fv_ee (open_te_rec k Y e1)))...
  assert (x `notin` (fv_ee (open_te_rec k Y e2))). auto. 
  apply IHe1 in H1. apply IHe2 in H2. auto.
  eapply IHe. eauto.
  eapply IHe. eauto.
Qed.

Lemma notin_open_te_fv_ee :  forall (x Y : atom) e,
  x `notin` fv_ee (open_te e Y)->
  x <> Y ->
  x `notin` fv_ee e.
Proof with eauto.
  unfold open_te. intros. eapply notin_open_te_fv_ee_rec. eauto. auto.
Qed.

Hint Resolve notin_open_te_fv_ee.

Lemma notin_fv_tt_open_tt_rec : forall (x y : atom) e kk,
  x `notin` fv_tt e ->
  x <> y ->
  x `notin` fv_tt (open_tt_rec kk y e).
Proof.
  induction e; intros ; simpl in *; auto.
  Case "exp_bvar".   
    destruct (kk === n); simpl; auto.
Qed.

Lemma notin_fv_tt_open_tt : forall (x y : atom) e,
  x `notin` fv_tt e ->
  x <> y ->
  x `notin` fv_tt (open_tt e y).
Proof.
  unfold open_tt.
  auto using notin_fv_tt_open_tt_rec.
Qed.
Hint Resolve notin_fv_tt_open_tt.

Lemma notin_open_tt_fv_tt_rec : forall (x Y : atom) e k,
  x `notin` fv_tt (open_tt_rec k Y e)->
  x <> Y ->
  x `notin` fv_tt e.
Proof with eauto.
  intros. generalize dependent k.
   induction e; intros; simpl in *; auto.
  assert (x `notin` (fv_tt (open_tt_rec k0 Y e1))). fsetdec.
  assert (x `notin` (fv_tt (open_tt_rec k0 Y e2))). fsetdec. 
  apply IHe1 in H1. apply IHe2 in H2. auto.
  eapply IHe. eauto.
Qed.

Lemma notin_open_tt_fv_tt :  forall (x Y : atom) e,
  x `notin` fv_tt (open_tt e Y)->
  x <> Y ->
  x `notin` fv_tt e.
Proof with eauto.
  unfold open_tt. intros. eapply notin_open_tt_fv_tt_rec. eauto. auto.
Qed.

Hint Resolve notin_open_tt_fv_tt.
(* ********************************************************************** *)
(** * #<a name="pick_fresh"></a># The "[pick fresh]" tactic *)

(** The "[pick fresh]" tactic introduces a fresh atom into the context.
    We define it in two steps.

    The first step is to define an auxiliary tactic [gather_atoms],
    meant to be used in the definition of other tactics, which returns
    a set of atoms in the current context.  The definition of
    [gather_atoms] follows a pattern based on repeated calls to
    [gather_atoms_with].  The one argument to this tactic is a
    function that takes an object of some particular type and returns
    a set of atoms that appear in that argument.  It is not necessary
    to understand exactly how [gather_atoms_with] works.  If we add a
    new inductive datatype, say for kinds, to our language, then we
    would need to modify [gather_atoms].  On the other hand, if we
    merely add a new type, say products, then there is no need to
    modify [gather_atoms]; the required changes would be made in
    [fv_tt]. *)

Ltac gather_atoms :=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : exp => fv_te x) in
  let D := gather_atoms_with (fun x : exp => fv_ee x) in
  let E := gather_atoms_with (fun x : typ => fv_tt x) in
  let F := gather_atoms_with (fun x : env => dom x) in
  let G := gather_atoms_with (fun x : genv => dom x) in
  let H := gather_atoms_with (fun x : denv => dom x) in
  let I := gather_atoms_with (fun x : denv => denv_fv_tt x) in
  let J := gather_atoms_with (fun x : genv => genv_fv_tt x) in
  constr:(A `union` B `union` C `union` D `union` E `union` F `union` G `union` H `union` I `union` J).

(** The second step in defining "[pick fresh]" is to define the tactic
    itself.  It is based on the [(pick fresh ... for ...)] tactic
    defined in the [Atom] library.  Here, we use [gather_atoms] to
    construct the set [L] rather than leaving it to the user to
    provide.  Thus, invoking [(pick fresh x)] introduces a new atom
    [x] into the current context that is fresh for "everything" in the
    context. *)

Tactic Notation "pick" "fresh" ident(x) :=
  let L := gather_atoms in (pick fresh x for L).

(* *********************************************************************** *)
(** * #<a name="apply_fresh"></a># The "[pick fresh and apply]" tactic *)

(** This tactic is implementation specific only because of its
    reliance on [gather_atoms], which is itself implementation
    specific.  The definition below may be copied between developments
    without any changes, assuming that the other other developments
    define an appropriate [gather_atoms] tactic.  For documentation on
    the tactic on which the one below is based, see the
    [Metatheory] library. *)

Tactic Notation
      "pick" "fresh" ident(atom_name) "and" "apply" constr(lemma) :=
  let L := gather_atoms in
  pick fresh atom_name excluding L and apply lemma.


(* *********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

(** When reasoning about the [binds] relation and [map], we
    occasionally encounter situations where the binding is
    over-simplified.  The following hint undoes that simplification,
    thus enabling [Hint]s from the [Environment] library. *)

Hint Extern 1 (binds _ (?F (subst_tt ?X ?U ?T)) _) =>
  unsimpl (subst_tgb X U (F T)).

Hint Extern 1 (binds _ (?F (subst_tt ?X ?U ?T)) _) =>
  unsimpl (subst_tdb X U (F T)).
