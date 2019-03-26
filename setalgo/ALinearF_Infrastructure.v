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

Definition subst_tdb := subst_tt.

Fixpoint denv_fv_tt (D : denv) : atoms :=
  match D with
    | nil => {}
    | (x, T) :: D' => (fv_tt T) `union` (denv_fv_tt D')
  end.

Fixpoint genv_fv_tt (G : genv) : atoms :=
  match G with
    | nil => {}
    | (x, gbind_typ T) :: G' => (fv_tt T) `union` (genv_fv_tt G')
    | (x, gbind_kn K) :: G' => genv_fv_tt G'
  end.

Lemma subst_tdb_fresh : forall D Z T,
   Z `notin` denv_fv_tt D ->
   D = map (subst_tdb Z T) D. 
Proof with auto.
  induction D; simpl; intros Z T H; f_equal...
    destruct a as [x b].
    simpl. rewrite <- subst_tt_fresh; auto.
    destruct a as [x b].
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
    intros. contradict H; fsetdec.
  Case "exp_app".
    intros.
    assert (x `in` fv_ee e1 \/ x `in` fv_ee e2) as J. fsetdec.
    destruct J as [J | J].
      apply IHe1 with (kk:=kk) in J. fsetdec.
      apply IHe2 with (kk:=kk) in J. fsetdec.
  Case "exp_apair".
    intros.
    assert (x `in` fv_ee e1 \/ x `in` fv_ee e2) as J. fsetdec.
    destruct J as [J | J].
      apply IHe1 with (kk:=kk) in J. fsetdec.
      apply IHe2 with (kk:=kk) in J. fsetdec.
Qed.

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
    intros.
    assert (x `in` fv_ee e1 \/ x `in` fv_ee e2) as J. fsetdec.
    destruct J as [J | J].
      apply IHe1 with (kk:=kk) in J. fsetdec.
      apply IHe2 with (kk:=kk) in J. fsetdec.
  Case "exp_apair".
    intros.
    assert (x `in` fv_ee e1 \/ x `in` fv_ee e2) as J. fsetdec.
    destruct J as [J | J].
      apply IHe1 with (kk:=kk) in J. fsetdec.
      apply IHe2 with (kk:=kk) in J. fsetdec.
Qed.

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
    destruct (kk == n); simpl; auto.
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
  (exp_cases (induction e) Case); intros; simpl in *; eauto.
Qed.

Lemma notin_open_te_fv_ee :  forall (x Y : atom) e,
  x `notin` fv_ee (open_te e Y)->
  x <> Y ->
  x `notin` fv_ee e.
Proof with eauto.
  unfold open_te. intros. eapply notin_open_te_fv_ee_rec. eauto. auto.
Qed.

Hint Resolve notin_open_te_fv_ee.

Lemma notin_fv_tt_open_tt_rec : forall (X Y : atom) T kk,
  X `notin` fv_tt T ->
  X <> Y ->
  X `notin` fv_tt (open_tt_rec kk Y T).
Proof.
  (typ_cases (induction T) Case); intros kk; simpl in *; auto.
  Case "typ_bvar".   
    destruct (kk == n); simpl; auto.
Qed.

Lemma notin_fv_tt_open_tt : forall (X Y : atom) T,
  X `notin` fv_tt T ->
  X <> Y ->
  X `notin` fv_tt (open_tt T Y).
Proof.
  unfold open_tt.
  auto using notin_fv_tt_open_tt_rec.
Qed.

Lemma notin_fv_tt_open_tt_rec_inv : forall (Y X : atom) T k,
  X `notin` fv_tt (open_tt_rec k Y T) ->
  X `notin` fv_tt T.
Proof.
  induction T; intros kk Fr; simpl in *; destruct_notin; eauto.
Qed.

Lemma notin_fv_tt_open_tt_inv : forall (Y X : atom) T,
  X `notin` fv_tt (open_tt T Y) ->
  X `notin` fv_tt T.
Proof.
  unfold open_tt.
  eauto using notin_fv_tt_open_tt_rec_inv.
Qed.


Lemma notin_fv_ee_subst_ee : forall (x y : atom) e e',
  x `notin` fv_ee e ->
  x `notin` fv_ee e' ->
  x `notin` fv_ee (subst_ee y e' e).
Proof.
  (exp_cases (induction e) Case); simpl in *; auto.
  Case "exp_fvar".   
    intros e' H1 H2.
    destruct (a == y); simpl; auto.
Qed.
  
Lemma notin_fv_te_subst_ee : forall (x y : atom) e e',
  x `notin` fv_te e ->
  x `notin` fv_te e' ->
  x `notin` fv_te (subst_ee y e' e).
Proof.
  (exp_cases (induction e) Case); simpl in *; auto.
  Case "exp_fvar".   
    intros e' H1 H2.
    destruct (a == y); simpl; auto.
Qed.

Lemma open_ee_rec_commute : forall e e' (x : atom) k1 k2,
  k1 <> k2 ->
  expr e' ->
  (open_ee_rec k1 x (open_ee_rec k2 e' e) =
    open_ee_rec k2 e' (open_ee_rec k1 x e)).
Proof with repeat progress (rewrite <- open_ee_rec_expr; [auto | solve [auto]]).
  intros e e' x k1 k2 Neq Expr.
  generalize dependent k1.
  generalize dependent k2.
  (exp_cases (induction e) Case); intros k2 k1 Neq; simpl in *;
    try solve [ auto |
                rewrite IHe; auto |
                rewrite IHe1; auto; rewrite IHe2; auto ].
  Case "exp_bvar".
    destruct (k2 == n); destruct (k1 == n); subst; simpl in *...
    intuition.
    destruct (n == n); subst; intuition.
    destruct (n == n); subst; intuition.
    destruct (k1 == n); destruct (k2 == n); subst; simpl in *; intuition.
Qed.

Lemma open_te_ee_rec_commute : forall (X x: atom) e k1 k2,
  (open_te_rec k1 X (open_ee_rec k2 x e) =
    open_ee_rec k2 x (open_te_rec k1 X e)).
Proof with auto.
  intros X x e k1 k2.
  generalize dependent k1.
  generalize dependent k2.
  (exp_cases (induction e) Case); intros k1 k2; simpl in *;
    try solve [ auto |
                rewrite IHe; auto |
                rewrite IHe1; auto; rewrite IHe2; auto |
                rewrite IHe1; auto; rewrite IHe2; auto ; rewrite IHe3; auto ].
  Case "exp_bvar".
    destruct (k1==n); simpl; auto.
Qed.

Hint Resolve notin_fv_tt_open_tt.

Fixpoint exp_size (e : exp) {struct e} :=
  match e with
  | exp_bvar n => 1
  | exp_fvar x => 1
  | exp_abs k t e' => 1 + exp_size e'
  | exp_app e1 e2 => 1 + exp_size e1 + exp_size e2
  | exp_tabs k e' => 1 + exp_size e'
  | exp_tapp e' t => 1 + exp_size e'
  | exp_apair e1 e2 => 1 + exp_size e1 + exp_size e2
  | exp_fst e1 => 1 + exp_size e1
  | exp_snd e1 => 1 + exp_size e1
  end.

Lemma open_ee_rec_exp_size_eq : forall (x : atom) e kk,
  exp_size (open_ee_rec kk (exp_fvar x) e) = exp_size e.
Proof.
  (exp_cases (induction e) Case); intros kk; simpl; auto.
  Case "exp_bvar".
    destruct (kk == n); simpl; auto.
Qed.

Lemma open_ee_exp_size_eq : forall (x : atom) e,
  exp_size (open_ee e x) = exp_size e.
Proof.
  unfold open_ee.
  auto using open_ee_rec_exp_size_eq.
Qed.


Lemma open_te_rec_exp_size_eq : forall (X : atom) e kk,
  exp_size (open_te_rec kk X e) = exp_size e.
Proof.
  (exp_cases (induction e) Case); intros kk; simpl; auto.
Qed.

Lemma open_te_exp_size_eq : forall (X : atom) e,
  exp_size (open_te e X) = exp_size e.
Proof.
  unfold open_te.
  auto using open_te_rec_exp_size_eq.
Qed.


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
  let A := ltac_map (fun x : atoms => x) in
  let B := ltac_map (fun x : atom => singleton x) in
  let C := ltac_map (fun x : exp => fv_te x) in
  let D := ltac_map (fun x : exp => fv_ee x) in
  let E := ltac_map (fun x : typ => fv_tt x) in
  let F := ltac_map (fun x : env => dom x) in
  let G := ltac_map (fun x : genv => dom x) in
  let H := ltac_map (fun x : denv => dom x) in
  let I := ltac_map (fun x : denv => denv_fv_tt x) in
  let J := ltac_map (fun x : genv => genv_fv_tt x) in
  simplify_list_of_atom_sets (A ++ B ++ C ++ D ++ E ++ F ++ G ++ H ++ I ++ J).

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

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../../../metatheory" "-I" "../linf") ***
*** End: ***
 *)
