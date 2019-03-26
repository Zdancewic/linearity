(** Infrastructure lemmas and tactic definitions.

    Authors: Steve Zdancewic and Karl Mazurak.
    
    This file contains a number of definitions, tactics, and lemmas
    that are based only on the syntax of the language at hand.  While
    the exact statements of everything here would change for a
    different language, the general structure of this file (i.e., the
    sequence of definitions, tactics, and lemmas) would remain the
    same.

    Table of contents:
      - #<a href="##fv">Free variables</a>#
      - #<a href="##subst">Substitution</a>#
      - #<a href="##pick_fresh">The "pick fresh" tactic</a>#
      - #<a href="##apply_fresh">The "pick fresh and apply" tactic</a>#
      - #<a href="##properties">Properties of opening and substitution</a>#
      - #<a href="##lc">Local closure is preserved under substitution</a>#
      - #<a href="##auto">Automation</a># *)

Require Export LinF_Definitions.

(* ********************************************************************** *)
(** * #<a name="fv"></a># Free variables *)

(** In this section, we define free variable functions.  The functions
    [fv_tt] and [fv_te] calculate the set of atoms used as free type
    variables in a type or expression, respectively.  The function
    [fv_ee] calculates the set of atoms used as free expression
    variables in an expression.  Cases involving binders are
    straightforward since bound variables are indices, not names, in
    locally nameless representation. *)

Fixpoint fv_tt (T : typ) {struct T} : atoms :=
  match T with
  | typ_bvar J => {}
  | typ_fvar X => singleton X
  | typ_arrow K T1 T2 => (fv_tt T1) `union` (fv_tt T2)
  | typ_all K T2 => (fv_tt T2)
  | typ_with T1 T2 => (fv_tt T1) `union` (fv_tt T2)
  end.

Fixpoint fv_te (e : exp) {struct e} : atoms :=
  match e with
  | exp_bvar i => {}
  | exp_fvar x => {}
  | exp_abs K V e1  => (fv_tt V) `union` (fv_te e1)
  | exp_app e1 e2 => (fv_te e1) `union` (fv_te e2)
  | exp_tabs K e1 => (fv_te e1)
  | exp_tapp e1 V => (fv_tt V) `union` (fv_te e1)
  | exp_apair e1 e2 => (fv_te e1) `union` (fv_te e2)
  | exp_fst e1 => (fv_te e1)
  | exp_snd e1 => (fv_te e1)
  end.

Fixpoint fv_ee (e : exp) {struct e} : atoms :=
  match e with
  | exp_bvar i => {}
  | exp_fvar x => singleton x
  | exp_abs K V e1 => (fv_ee e1)
  | exp_app e1 e2 => (fv_ee e1) `union` (fv_ee e2)
  | exp_tabs K e1 => (fv_ee e1)
  | exp_tapp e1 V => (fv_ee e1)
  | exp_apair e1 e2 => (fv_ee e1) `union` (fv_ee e2)
  | exp_fst e1 => (fv_ee e1)
  | exp_snd e1 => (fv_ee e1)
  end.

Fixpoint fv_env (E : env) {struct E} : atoms :=
  match E with
  | nil => {}
  | (x, bind_kn _) :: E' =>
      singleton x `union` fv_env E'
  | (x, bind_typ t) :: E' =>
      singleton x `union` (fv_tt t) `union` fv_env E'
  end.
  
Fixpoint fv_lenv (D : lenv) {struct D} : atoms :=
  match D with
  | nil => {}
  | cons (x, lbind_typ T) l => 
      singleton x `union` fv_tt T `union` fv_lenv l
  end.

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

Fixpoint subst_tt (Z : atom) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_bvar J => typ_bvar J
  | typ_fvar X => if X == Z then U else T
  | typ_arrow K T1 T2 => typ_arrow K (subst_tt Z U T1) (subst_tt Z U T2)
  | typ_all K T2 => typ_all K (subst_tt Z U T2)
  | typ_with T1 T2 => typ_with (subst_tt Z U T1) (subst_tt Z U T2)
  end.

Fixpoint subst_te (Z : atom) (U : typ) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_abs K V e1 => exp_abs  K (subst_tt Z U V)  (subst_te Z U e1)
  | exp_app e1 e2 => exp_app  (subst_te Z U e1) (subst_te Z U e2)
  | exp_tabs K e1 => exp_tabs K  (subst_te Z U e1)
  | exp_tapp e1 V => exp_tapp (subst_te Z U e1) (subst_tt Z U V)
  | exp_apair e1 e2 => exp_apair  (subst_te Z U e1) (subst_te Z U e2)
  | exp_fst e1 => exp_fst  (subst_te Z U e1)
  | exp_snd e1 => exp_snd  (subst_te Z U e1)
  end.

Fixpoint subst_ee (z : atom) (u : exp) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => if x == z then u else e
  | exp_abs K V e1 => exp_abs K V (subst_ee z u e1)
  | exp_app e1 e2 => exp_app (subst_ee z u e1) (subst_ee z u e2)
  | exp_tabs K e1 => exp_tabs K (subst_ee z u e1)
  | exp_tapp e1 V => exp_tapp (subst_ee z u e1) V
  | exp_apair e1 e2 => exp_apair (subst_ee z u e1) (subst_ee z u e2)
  | exp_fst e1 => exp_fst (subst_ee z u e1)
  | exp_snd e1 => exp_snd (subst_ee z u e1)
  end.

Definition subst_tb (Z : atom) (P : typ) (b : binding) : binding :=
  match b with
  | bind_kn K => bind_kn K
  | bind_typ T => bind_typ (subst_tt Z P T)
  end.

Definition subst_tlb (Z : atom) (P : typ) (b : lbinding) : lbinding :=
  match b with
  | lbind_typ T => lbind_typ (subst_tt Z P T)
  end.


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
  let G := ltac_map (fun x : env => fv_env x) in
  let H := ltac_map (fun x : lenv => dom x) in
  let I := ltac_map (fun x : lenv => fv_lenv x) in
  simplify_list_of_atom_sets (A ++ B ++ C ++ D ++ E ++ F ++ G ++ H ++ I).

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


(* ********************************************************************** *)
(** * #<a name="properties"></a># Properties of opening and substitution *)

(** The following lemmas provide useful structural properties of
    substitution and opening.  While the exact statements are language
    specific, we have found that similar properties are needed in a
    wide range of languages.

    Below, we indicate which lemmas depend on which other lemmas.
    Since [te] functions depend on their [tt] counterparts, a similar
    dependency can be found in the lemmas.

    The lemmas are split into three sections, one each for the [tt],
    [te], and [ee] functions.  The most important lemmas are the
    following:
      - Substitution and opening commute with each other, e.g.,
        [subst_tt_open_tt_var].
      - Opening a term is equivalent to opening the term with a fresh
        name and then substituting for that name, e.g.,
        [subst_tt_intro].

    We keep the sections as uniform in structure as possible.  In
    particular, we state explicitly strengthened induction hypotheses
    even when there are more concise ways of proving the lemmas of
    interest. *)


(* ********************************************************************** *)
(** ** Properties of type substitution in types *)

(** The next lemma is the strengthened induction hypothesis for the
    lemma that follows, which states that opening a locally closed
    term is the identity.  This lemma is not otherwise independently
    useful. *)

Lemma open_tt_rec_type_aux : forall T j V i U,
  i <> j ->
  open_tt_rec j V T = open_tt_rec i U (open_tt_rec j V T) ->
  T = open_tt_rec i U T.
Proof with try solve [congruence | eauto].
  induction T; intros j V i U Neq H; simpl in *; inversion H; f_equal...
  Case "typ_bvar".
    destruct (j == n)... destruct (i == n)...
Qed.

(** Opening a locally closed term is the identity.  This lemma depends
    on the immediately preceding lemma. *)

Lemma open_tt_rec_type : forall T U k,
  type T ->
  T = open_tt_rec k U T.
Proof with try solve [congruence | intuition].
  intros T U k Htyp. revert k.
  induction Htyp; intros k; simpl; f_equal...
  Case "typ_all".
    unfold open_tt in *.
    pick fresh X.
    apply (open_tt_rec_type_aux T2 0 (typ_fvar X))...
Qed.

(** If a name is fresh for a term, then substituting for it is the
    identity. *)

Lemma subst_tt_fresh : forall Z U T,
   Z `notin` fv_tt T ->
   T = subst_tt Z U T.
Proof with try solve [congruence | intuition].
  induction T; simpl; intro H; f_equal...
  Case "typ_fvar".
    destruct (a == Z)...
    (*contradict H; fsetdec.*)
Qed.

(** Substitution commutes with opening under certain conditions.  This
    lemma depends on the fact that opening a locally closed term is
    the identity. *)

Lemma subst_tt_open_tt_rec : forall T1 T2 X P k,
  type P ->
  subst_tt X P (open_tt_rec k T2 T1) =
    open_tt_rec k (subst_tt X P T2) (subst_tt X P T1).
Proof with try solve [congruence | intuition].
  intros T1 T2 X P k WP. revert k.
  induction T1; intros K; simpl; f_equal...
  Case "typ_bvar".
    destruct (K == n); subst...
  Case "typ_fvar".
    destruct (a == X); subst... apply open_tt_rec_type...
Qed.

(** The next lemma is a direct corollary of the immediately preceding
    lemma---the index is specialized to zero. *)

Lemma subst_tt_open_tt : forall T1 T2 (X:atom) P,
  type P ->
  subst_tt X P (open_tt T1 T2) = open_tt (subst_tt X P T1) (subst_tt X P T2).
Proof with try solve [congruence | intuition].
  intros.
  unfold open_tt.
  apply subst_tt_open_tt_rec...
Qed.

(** The next lemma is a direct corollary of the immediately preceding
    lemma---here, we're opening the term with a variable.  In
    practice, this lemma seems to be needed as a left-to-right rewrite
    rule, when stated in its current form. *)

Lemma subst_tt_open_tt_var : forall (X Y:atom) P T,
  Y <> X ->
  type P ->
  open_tt (subst_tt X P T) Y = subst_tt X P (open_tt T Y).
Proof with try solve [congruence | intuition].
  intros X Y P T Neq Wu.
  unfold open_tt.
  rewrite subst_tt_open_tt_rec...
  simpl.
  destruct (Y == X)...
Qed.

(** The next lemma states that opening a term is equivalent to first
    opening the term with a fresh name and then substituting for the
    name.  This is actually the strengthened induction hypothesis for
    the version we use in practice. *)

Lemma subst_tt_intro_rec : forall X T2 U k,
  X `notin` fv_tt T2 ->
  open_tt_rec k U T2 = subst_tt X U (open_tt_rec k (typ_fvar X) T2).
Proof with try solve [congruence | intuition].
  induction T2; intros U K Fr; simpl in *; f_equal...
  Case "typ_bvar".
    destruct (K == n)... simpl. destruct (X == X)...
  Case "typ_fvar".
    destruct (a == X)... (*contradict Fr; fsetdec.*)
Qed.

(** The next lemma is a direct corollary of the immediately preceding
    lemma---the index is specialized to zero.  *)

Lemma subst_tt_intro : forall (X : atom) T2 U,
  X `notin` fv_tt T2 ->
  open_tt T2 U = subst_tt X U (open_tt T2 X).
Proof with try solve [congruence | intuition].
  intros.
  unfold open_tt.
  apply subst_tt_intro_rec...
Qed.


(* ********************************************************************** *)
(** ** Properties of type substitution in expressions *)

(** This section follows the structure of the previous section.  The
    one notable difference is that we require two auxiliary lemmas to
    show that substituting a type in a locally-closed expression is
    the identity. *)

Lemma open_te_rec_expr_aux : forall e j u i P ,
  open_ee_rec j u e = open_te_rec i P (open_ee_rec j u e) ->
  e = open_te_rec i P e.
Proof with try solve [congruence | eauto].
  induction e; intros j u i P H; simpl in *; inversion H; f_equal...
Qed.

Lemma open_te_rec_type_aux : forall e j Q i P,
  i <> j ->
  open_te_rec j Q e = open_te_rec i P (open_te_rec j Q e) ->
  e = open_te_rec i P e.
Proof.
  induction e; intros j Q i P Neq Heq; simpl in *; inversion Heq;
    f_equal; eauto using open_tt_rec_type_aux.
Qed.

Lemma open_te_rec_expr : forall e U k,
  expr e ->
  e = open_te_rec k U e.
Proof with try solve [congruence | intuition].
  intros e U k WF. revert k.
  induction WF; intros k; simpl; f_equal; auto using open_tt_rec_type;
  try solve [
    unfold open_ee in *;
    pick fresh x;
    eapply open_te_rec_expr_aux with (j := 0) (u := exp_fvar x);
    try solve [congruence | intuition]
  | unfold open_te in *;
    pick fresh X;
    eapply open_te_rec_type_aux with (j := 0) (Q := typ_fvar X);
    try solve [congruence | intuition]
  ].
Qed.

Lemma subst_te_fresh : forall X U e,
  X `notin` fv_te e ->
  e = subst_te X U e.
Proof.
  induction e; simpl; intros; f_equal; auto using subst_tt_fresh.
Qed.

Lemma subst_te_open_te_rec : forall e T X U k,
  type U ->
  subst_te X U (open_te_rec k T e) =
    open_te_rec k (subst_tt X U T) (subst_te X U e).
Proof.
  intros e T X U k WU. revert k.
  induction e; intros K; simpl; f_equal; auto using subst_tt_open_tt_rec.
Qed.

Lemma subst_te_open_te : forall e T X U,
  type U ->
  subst_te X U (open_te e T) = open_te (subst_te X U e) (subst_tt X U T).
Proof with try solve [congruence | intuition].
  intros.
  unfold open_te.
  apply subst_te_open_te_rec...
Qed.

Lemma subst_te_open_te_var : forall (X Y:atom) U e,
  Y <> X ->
  type U ->
  open_te (subst_te X U e) Y = subst_te X U (open_te e Y).
Proof with try solve [congruence | intuition].
  intros X Y U e Neq WU.
  unfold open_te.
  rewrite subst_te_open_te_rec...
  simpl.
  destruct (Y == X)...
Qed.

Lemma subst_te_intro_rec : forall X e U k,
  X `notin` fv_te e ->
  open_te_rec k U e = subst_te X U (open_te_rec k (typ_fvar X) e).
Proof.
  induction e; intros U K Fr; simpl in *; f_equal;
    auto using subst_tt_intro_rec.
Qed.

Lemma subst_te_intro : forall (X : atom) e U,
  X `notin` fv_te e ->
  open_te e U = subst_te X U (open_te e X).
Proof with try solve [congruence | intuition].
  intros.
  unfold open_te.
  apply subst_te_intro_rec...
Qed.


(* ********************************************************************** *)
(** ** Properties of expression substitution in expressions *)

(** This section follows the structure of the previous two sections. *)

Lemma open_ee_rec_expr_aux : forall e j v u i,
  i <> j ->
  open_ee_rec j v e = open_ee_rec i u (open_ee_rec j v e) ->
  e = open_ee_rec i u e.
Proof with try solve [congruence | eauto].
  induction e; intros j v u i Neq H; simpl in *; inversion H; f_equal...
  Case "exp_bvar".
    destruct (j==n)... destruct (i==n)...
Qed.

Lemma open_ee_rec_type_aux : forall e j V u i,
  open_te_rec j V e = open_ee_rec i u (open_te_rec j V e) ->
  e = open_ee_rec i u e.
Proof.
  induction e; intros j V u i H; simpl; inversion H; f_equal; eauto.
Qed.

Lemma open_ee_rec_expr : forall u e k,
  expr e ->
  e = open_ee_rec k u e.
Proof with try solve [congruence | intuition].
  intros u e k Hexpr. revert k.
  induction Hexpr; intro k; simpl; f_equal; try solve [congruence | intuition];
  try solve [
    unfold open_ee in *;
    pick fresh x;
    eapply open_ee_rec_expr_aux with (j := 0) (v := exp_fvar x);
    try solve [congruence | intuition]
  | unfold open_te in *;
    pick fresh X;
    eapply open_ee_rec_type_aux with (j := 0) (V := typ_fvar X);
    try solve [congruence | intuition]
  ].
Qed.

Lemma subst_ee_fresh : forall (x: atom) u e,
  x `notin` fv_ee e ->
  e = subst_ee x u e.
Proof with try solve [congruence | intuition].
  intros x u e; induction e; simpl; intro H; f_equal...
  Case "exp_fvar".
    destruct (a==x)...
    (*contradict H; fsetdec.*)
Qed.

Lemma subst_ee_open_ee_rec : forall e1 e2 x u k,
  expr u ->
  subst_ee x u (open_ee_rec k e2 e1) =
    open_ee_rec k (subst_ee x u e2) (subst_ee x u e1).
Proof with try solve [congruence | intuition].
  intros e1 e2 x u k WP. revert k.
  induction e1; intros K; simpl; f_equal...
  Case "exp_bvar".
    destruct (K == n); subst...
  Case "exp_fvar".
    destruct (a == x); subst... apply open_ee_rec_expr...
Qed.

Lemma subst_ee_open_ee : forall e1 e2 x u,
  expr u ->
  subst_ee x u (open_ee e1 e2) =
    open_ee (subst_ee x u e1) (subst_ee x u e2).
Proof with try solve [congruence | intuition].
  intros.
  unfold open_ee.
  apply subst_ee_open_ee_rec...
Qed.

Lemma subst_ee_open_ee_var : forall (x y:atom) u e,
  y <> x ->
  expr u ->
  open_ee (subst_ee x u e) y = subst_ee x u (open_ee e y).
Proof with try solve [congruence | intuition].
  intros x y u e Neq Wu.
  unfold open_ee.
  rewrite subst_ee_open_ee_rec...
  simpl.
  destruct (y == x)...
Qed.

Lemma subst_te_open_ee_rec : forall e1 e2 Z P k,
  subst_te Z P (open_ee_rec k e2 e1) =
    open_ee_rec k (subst_te Z P e2) (subst_te Z P e1).
Proof with try solve [congruence | intuition].
  induction e1; intros e2 Z P K; simpl; f_equal...
  Case "exp_bvar".
    destruct (K == n)...
Qed.

Lemma subst_te_open_ee : forall e1 e2 Z P,
  subst_te Z P (open_ee e1 e2) = open_ee (subst_te Z P e1) (subst_te Z P e2).
Proof with try solve [congruence | intuition].
  intros.
  unfold open_ee.
  apply subst_te_open_ee_rec...
Qed.

Lemma subst_te_open_ee_var : forall Z (x:atom) P e,
  open_ee (subst_te Z P e) x = subst_te Z P (open_ee e x).
Proof with try solve [congruence | intuition].
  intros.
  rewrite subst_te_open_ee...
Qed.

Lemma subst_ee_open_te_rec : forall e P z u k,
  expr u ->
  subst_ee z u (open_te_rec k P e) = open_te_rec k P (subst_ee z u e).
Proof with try solve [congruence | intuition].
  induction e; intros P z u K H; simpl; f_equal...
  Case "exp_fvar".
    destruct (a == z)... apply open_te_rec_expr...
Qed.

Lemma subst_ee_open_te : forall e P z u,
  expr u ->
  subst_ee z u (open_te e P) = open_te (subst_ee z u e) P.
Proof with try solve [congruence | intuition].
  intros.
  unfold open_te.
  apply subst_ee_open_te_rec...
Qed.

Lemma subst_ee_open_te_var : forall z (X:atom) u e,
  expr u ->
  open_te (subst_ee z u e) X = subst_ee z u (open_te e X).
Proof with try solve [congruence | intuition].
  intros z X u e H.
  rewrite subst_ee_open_te...
Qed.

Lemma subst_ee_intro_rec : forall x e u k,
  x `notin` fv_ee e ->
  open_ee_rec k u e = subst_ee x u (open_ee_rec k (exp_fvar x) e).
Proof with try solve [congruence | intuition].
  induction e; intros u K Fr; simpl in *; f_equal...
  Case "exp_bvar".
    destruct (K == n)... simpl. destruct (x == x)...
  Case "exp_fvar".
    destruct (a == x)... (*contradict Fr; fsetdec.*)
Qed.

Lemma subst_ee_intro : forall (x : atom) e u,
  x `notin` fv_ee e ->
  open_ee e u = subst_ee x u (open_ee e x).
Proof with try solve [congruence | intuition].
  intros.
  unfold open_ee.
  apply subst_ee_intro_rec...
Qed.


(* *********************************************************************** *)
(** * #<a name="lc"></a># Local closure is preserved under substitution *)

(** While these lemmas may be considered properties of substitution, we
    separate them out due to the lemmas that they depend on. *)

(** The following lemma depends on [subst_tt_open_tt_var]. *)

Lemma subst_tt_type : forall Z P T,
  type T ->
  type P ->
  type (subst_tt Z P T).
Proof with auto.
  intros Z P T HT HP.
  induction HT; simpl...
  Case "type_fvar".
    destruct (X == Z)...
  Case "type_all".
    pick fresh Y and apply type_all...
    rewrite subst_tt_open_tt_var...
Qed.

(** The following lemma depends on [subst_tt_type] and
    [subst_te_open_ee_var]. *)

Lemma subst_te_expr : forall Z P e,
  expr e ->
  type P ->
  expr (subst_te Z P e).
Proof with eauto using subst_tt_type.
  intros Z P e He Hp.
  induction He; simpl; auto using subst_tt_type;
  try solve [
    econstructor;
    try instantiate (1 := L `union` singleton Z);
    intros;
    try rewrite subst_te_open_ee_var;
    try rewrite subst_te_open_te_var;
    eauto using subst_tt_type
  ].
Qed.

(** The following lemma depends on [subst_ee_open_ee_var] and
    [subst_ee_open_te_var]. *)

Lemma subst_ee_expr : forall z e1 e2,
  expr e1 ->
  expr e2 ->
  expr (subst_ee z e2 e1).
Proof with auto.
  intros z e1 e2 He1 He2.
  induction He1; simpl; auto;
  try solve [
    econstructor;
    try instantiate (1 := L `union` singleton z);
    intros;
    try rewrite subst_ee_open_ee_var;
    try rewrite subst_ee_open_te_var;
    auto
  ].
  Case "expr_var".
    destruct (x == z)...
Qed.

(* *********************************************************************** *)
(* more properties of fv *)

Lemma fv_in_open_ee:  forall x e1 e2 k,
   x `in` fv_ee e1 -> 
   x `in` fv_ee (open_ee_rec k e2 e1).
Proof.
  intros x. induction e1; intros e2 k1 IN; simpl in IN; simpl; 
    try solve [fsetdec |
               apply IHe1; auto].
  assert ((x `in` fv_ee e1_1) \/ (x `in` fv_ee e1_2)) as H.
    fsetdec. 
  destruct H as [H | H].
    assert (x `in` fv_ee (open_ee_rec k1 e2 e1_1)).
      apply IHe1_1; auto. 
    fsetdec.
    assert (x `in` fv_ee (open_ee_rec k1 e2 e1_2)).
      apply IHe1_2; auto. 
    fsetdec.

  assert ((x `in` fv_ee e1_1) \/ (x `in` fv_ee e1_2)) as H.
    fsetdec. 
  destruct H as [H | H].
    assert (x `in` fv_ee (open_ee_rec k1 e2 e1_1)).
      apply IHe1_1; auto. 
    fsetdec.
    assert (x `in` fv_ee (open_ee_rec k1 e2 e1_2)).
      apply IHe1_2; auto. 
    fsetdec.
Qed.

Lemma fv_in_open_te:  forall x e1 e2 k,
   x `in` fv_ee e1 -> 
   x `in` fv_ee (open_te_rec k e2 e1).
Proof.
  intros x. induction e1; intros e2 k1 IN; simpl in IN; simpl;
    try solve [fsetdec |
               apply IHe1; auto].
  assert ((x `in` fv_ee e1_1) \/ (x `in` fv_ee e1_2)) as H.
    fsetdec. 
  destruct H as [H | H].
    assert (x `in` fv_ee (open_te_rec k1 e2 e1_1)).
      apply IHe1_1; auto. 
    fsetdec.
    assert (x `in` fv_ee (open_te_rec k1 e2 e1_2)).
      apply IHe1_2; auto. 
    fsetdec.
  assert ((x `in` fv_ee e1_1) \/ (x `in` fv_ee e1_2)) as H.
    fsetdec. 
  destruct H as [H | H].
    assert (x `in` fv_ee (open_te_rec k1 e2 e1_1)).
      apply IHe1_1; auto. 
    fsetdec.
    assert (x `in` fv_ee (open_te_rec k1 e2 e1_2)).
      apply IHe1_2; auto. 
    fsetdec.
Qed.

Lemma notin_open_tt_rec_fv : forall (Y X : atom) T n,
  X `notin` fv_tt T ->
  X <> Y ->
  X `notin` fv_tt (open_tt_rec n Y T).
Proof.
  intros. 
  generalize dependent n. generalize dependent X.
  induction T; simpl; intros X Nin Neq n0; simpl; auto. 
    destruct (n0 == n); simpl; auto. 
Qed.

Lemma notin_open_tt_fv : forall (Y X : atom) T,
  X `notin` fv_tt T ->
  X <> Y ->
  X `notin` fv_tt (open_tt T Y).
Proof.
  intros. unfold open_tt.
  apply (notin_open_tt_rec_fv Y X T 0); auto.
Qed.

Lemma notin_fv_tt_open : forall (Y X : atom) T,
  X `notin` fv_tt (open_tt T Y) ->
  X `notin` fv_tt T.
Proof.
 intros Y X T. unfold open_tt.
 generalize 0.
 induction T; simpl; intros K Fr; destruct_notin; try apply notin_union; eauto.
Qed.

(* *********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

(** We add as hints the fact that local closure is preserved under
    substitution.  This is part of our strategy for automatically
    discharging local-closure proof obligations. *)

Hint Resolve subst_tt_type subst_te_expr subst_ee_expr.

(** When reasoning about the [binds] relation and [map], we
    occasionally encounter situations where the binding is
    over-simplified.  The following hint undoes that simplification,
    thus enabling [Hint]s from the [Environment] library. *)

Hint Extern 1 (binds _ (?F (subst_tt ?X ?U ?T)) _) =>
  unsimpl (subst_tb X U (F T)).

Hint Extern 1 (binds _ (?F (subst_tt ?X ?U ?T)) _) =>
  unsimpl (subst_tlb X U (F T)).

(* 
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../../../metatheory") ***
*** End: ***
 *)
