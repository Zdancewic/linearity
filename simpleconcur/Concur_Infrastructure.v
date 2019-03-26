(** Infrastructure lemmas and tactic definitions for [?].

    
    Based on work by Brian Aydemir and Arthur Chargu¨¦raud, with help from
    Aaron Bohannon, Jeffrey Vaughan, and Dimitrios Vytiniotis.

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

Require Export Concur_Definitions.

(*Axiom skip : False.
Ltac skip := assert False; [ apply skip | contradiction ].*)

(* ********************************************************************** *)
(** * #<a name="fv"></a># Free variables *)

(** In this section, we define free variable functions.  The functions
    [fv_tt] and [fv_te] calculate the set of atoms used as free type
    variables in a type or expression, respectively.  The function
    [fv_ee] calculates the set of atoms used as free expression
    variables in an expression.  Cases involving binders are
    straightforward since bound variables are indices, not names, in
    locally nameless representation. *)

Definition fv_cc (C : chan) : atoms :=
  match C with
  | bchan J => {}
  | fchan X => singleton X
  end.

Fixpoint fv_ce (e : exp) {struct e} : atoms :=
  match e with
  | exp_bvar i => {}
  | exp_fvar x => {}
  | exp_unit => {}
  | exp_seq e1 e2 => (fv_ce e1) `union` (fv_ce e2)
  | exp_abs V e1  => fv_ce e1
  | exp_app e1 e2 => (fv_ce e1) `union` (fv_ce e2)
  | exp_apair e1 e2 => (fv_ce e1) `union` (fv_ce e2)
  | exp_fst e1 => fv_ce e1
  | exp_snd e1 => fv_ce e1
  | exp_mpair e1 e2 => (fv_ce e1) `union` (fv_ce e2)
  | exp_let e1 e2 => (fv_ce e1) `union` (fv_ce e2)
  | exp_inl T e1 => fv_ce e1
  | exp_inr T e1 => fv_ce e1
  | exp_case e1 e2 e3 => (fv_ce e1) `union` (fv_ce e2) `union` (fv_ce e3)
  | exp_go T e1 => fv_ce e1
  | exp_yield e1 => fv_ce e1
  | exp_snk A T => fv_cc A
  | exp_src A T => fv_cc A
  | exp_done A => fv_cc A
  end.

Fixpoint fv_cp (P : proc) {struct P} : atoms :=
  match P with
  | proc_exp e => fv_ce e
  | proc_par P1 P2 => (fv_cp P1) `union` (fv_cp P2)
  | proc_new T P1 => fv_cp P1
  end.

Fixpoint fv_ee (e : exp) {struct e} : atoms :=
  match e with
  | exp_bvar i => {}
  | exp_fvar x => singleton x
  | exp_unit => {}
  | exp_seq e1 e2 => (fv_ee e1) `union` (fv_ee e2)
  | exp_abs V e1 => fv_ee e1
  | exp_app e1 e2 => (fv_ee e1) `union` (fv_ee e2)
  | exp_apair e1 e2 => (fv_ee e1) `union` (fv_ee e2)
  | exp_fst e1 => fv_ee e1
  | exp_snd e1 => fv_ee e1
  | exp_mpair e1 e2 => (fv_ee e1) `union` (fv_ee e2)
  | exp_let e1 e2 => (fv_ee e1) `union` (fv_ee e2)
  | exp_inl T e1 => fv_ee e1
  | exp_inr T e1 => fv_ee e1
  | exp_case e1 e2 e3 => (fv_ee e1) `union` (fv_ee e2) `union` (fv_ee e3)
  | exp_go T e1 => fv_ee e1
  | exp_yield e1 => fv_ee e1
  | exp_snk A T => {}
  | exp_src A T => {}
  | exp_done A => {}
  end.

Fixpoint fv_env (E : env) {struct E} : atoms :=
  match E with
  | nil => {}
  | (x, bind_kn) :: E' =>
      singleton x `union` fv_env E'
  end.
  
Fixpoint fv_lenv (D : lenv) {struct D} : atoms :=
  match D with
  | nil => {}
  | (x, lbind_typ T) :: D' => 
      singleton x `union` fv_lenv D'
  end.

Fixpoint fv_cenv (Q : cenv) {struct Q} : atoms :=
  match Q with
  | nil => {}
  | (x, cbind_proto d T) :: Q' => 
      singleton x `union` fv_cenv Q'
  end.

Fixpoint fv_cenvs (Qs : cenvs) {struct Qs} : atoms :=
  match Qs with
  | nil => {}
  | Q :: Qs' => 
      fv_cenv Q `union` fv_cenvs Qs'
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

Fixpoint subst_cc (Z : atom) (C : chan) (A : chan) {struct A} : chan :=
  match A with
  | bchan J => bchan J
  | fchan X => if X == Z then C else (fchan X)
  end.

Fixpoint subst_ce (Z : atom) (C : chan) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_unit => exp_unit
  | exp_seq e1 e2 => exp_seq (subst_ce Z C e1) (subst_ce Z C e2)
  | exp_abs V e1 => exp_abs V (subst_ce Z C e1)
  | exp_app e1 e2 => exp_app (subst_ce Z C e1) (subst_ce Z C e2)
  | exp_apair e1 e2 => exp_apair (subst_ce Z C e1) (subst_ce Z C e2)
  | exp_fst e1 => exp_fst (subst_ce Z C e1)
  | exp_snd e1 => exp_snd (subst_ce Z C e1)
  | exp_mpair e1 e2 => exp_mpair (subst_ce Z C e1) (subst_ce Z C e2)
  | exp_let e1 e2 => exp_let (subst_ce Z C e1) (subst_ce Z C e2)
  | exp_inl V e1 => exp_inl V (subst_ce Z C e1)
  | exp_inr V e1 => exp_inr V (subst_ce Z C e1)
  | exp_case e1 e2 e3 =>
      exp_case (subst_ce Z C e1) (subst_ce Z C e2) (subst_ce Z C e3)
  | exp_go V e1 => exp_go V (subst_ce Z C e1)
  | exp_yield e1 => exp_yield (subst_ce Z C e1)
  | exp_snk A T => exp_snk (subst_cc Z C A) T
  | exp_src A T => exp_src (subst_cc Z C A) T
  | exp_done A => exp_done (subst_cc Z C A)
  end.

Fixpoint subst_cp (Z : atom) (C : chan) (P : proc) {struct P} : proc :=
  match P with
  | proc_exp e => proc_exp (subst_ce Z C e)
  | proc_par P1 P2 => proc_par (subst_cp Z C P1) (subst_cp Z C P2)
  | proc_new T P1 => proc_new T (subst_cp Z C P1)
  end.

Fixpoint subst_ee (z : atom) (u : exp) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => if x == z then u else (exp_fvar x)
  | exp_unit => exp_unit
  | exp_seq e1 e2 => exp_seq (subst_ee z u e1) (subst_ee z u e2)
  | exp_abs V e1 => exp_abs V (subst_ee z u e1)
  | exp_app e1 e2 => exp_app (subst_ee z u e1) (subst_ee z u e2)
  | exp_apair e1 e2 => exp_apair (subst_ee z u e1) (subst_ee z u e2)
  | exp_fst e1 => exp_fst (subst_ee z u e1)
  | exp_snd e1 => exp_snd (subst_ee z u e1)
  | exp_mpair e1 e2 => exp_mpair (subst_ee z u e1) (subst_ee z u e2)
  | exp_let e1 e2 => exp_let (subst_ee z u e1) (subst_ee z u e2)
  | exp_inl V e1 => exp_inl V (subst_ee z u e1)
  | exp_inr V e1 => exp_inr V (subst_ee z u e1)
  | exp_case e1 e2 e3 =>
      exp_case (subst_ee z u e1) (subst_ee z u e2) (subst_ee z u e3)
  | exp_go V e1 => exp_go V (subst_ee z u e1)
  | exp_yield e1 => exp_yield (subst_ee z u e1)
  | exp_snk A T => exp_snk A T
  | exp_src A T => exp_src A T
  | exp_done A => exp_done A
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
  let C := ltac_map (fun x : exp => fv_ce x) in
  let D := ltac_map (fun x : proc => fv_cp x) in
  let E := ltac_map (fun x : exp => fv_ee x) in
  let F := ltac_map (fun x : env => dom x) in
  let G := ltac_map (fun x : env => fv_env x) in
  let H := ltac_map (fun x : lenv => dom x) in
  let J := ltac_map (fun x : lenv => fv_lenv x) in
  let K := ltac_map (fun x : cenv => dom x) in
  let L := ltac_map (fun x : cenv => fv_cenv x) in
  let M := ltac_map (fun x : cenvs => doms cbinding x) in
  let N := ltac_map (fun x : cenvs => fv_cenvs x) in
  simplify_list_of_atom_sets
    (A ++ B ++ C ++ D ++ E ++ F ++ G ++ H ++ J ++ K ++ L ++ M ++ N).

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
(** ** Properties of channel substitution in channels *)

(** The next lemma is the strengthened induction hypothesis for the
    lemma that follows, which states that opening a locally closed
    term is the identity.  This lemma is not otherwise independently
    useful.

    This should be easy for the channel/channel case... right? *)

Lemma open_cc_rec_channel_aux : forall A j B i C,
  i <> j ->
  open_cc_rec j B A = open_cc_rec i C (open_cc_rec j B A) ->
  A = open_cc_rec i C A.
Proof with try solve [congruence | eauto].
  induction A; intros j B i C Neq H; simpl in *; inversion H; f_equal...
  Case "bchan".
    destruct (j == n)... destruct (i == n)...
Qed.

(** Opening a locally closed channel is the identity.  This lemma depends
    on the immediately preceding lemma. *)

Lemma open_cc_rec_channel : forall A C k,
  channel A ->
  A = open_cc_rec k C A.
Proof with try solve [congruence | intuition].
  intros A C k Htyp. revert k.
  induction Htyp; intros k; simpl; f_equal...
Qed.

(** If a name is fresh for a channel, then substituting for it is the
    identity. *)

Lemma subst_cc_fresh : forall Z C A,
   Z `notin` fv_cc A ->
   A = subst_cc Z C A.
Proof with try solve [congruence | intuition].
  induction A; simpl; intro H; f_equal...
  Case "fchan".
    destruct (a == Z)...
    contradict H; fsetdec.
Qed.

(** Substitution commutes with opening under certain conditions.  This
    lemma depends on the fact that opening a locally closed term is
    the identity. *)

Lemma subst_cc_open_cc_rec : forall A1 A2 X C k,
  channel C ->
  subst_cc X C (open_cc_rec k A2 A1) =
    open_cc_rec k (subst_cc X C A2) (subst_cc X C A1).
Proof with try solve [congruence | intuition].
  intros A1 A2 X C k WC. revert k.
  induction A1; intros K; simpl; f_equal...
  Case "bchan".
    destruct (K == n); subst...
  Case "fchan".
    destruct (a == X); subst... apply open_cc_rec_channel...
Qed.

(** The next lemma is a direct corollary of the immediately preceding
    lemma---the index is specialized to zero. *)

Lemma subst_cc_open_cc : forall A1 A2 (X:atom) C,
  channel C ->
  subst_cc X C (open_cc A1 A2) = open_cc (subst_cc X C A1) (subst_cc X C A2).
Proof with try solve [congruence | intuition].
  intros.
  unfold open_cc.
  apply subst_cc_open_cc_rec...
Qed.

(** The next lemma is a direct corollary of the immediately preceding
    lemma---here, we're opening the term with a variable.  In
    practice, this lemma seems to be needed as a left-to-right rewrite
    rule, when stated in its current form. *)

Lemma subst_cc_open_cc_var : forall (X Y:atom) C A,
  Y <> X ->
  channel C ->
  open_cc (subst_cc X C A) Y = subst_cc X C (open_cc A Y).
Proof with try solve [congruence | intuition].
  intros X Y C A Neq Wu.
  unfold open_cc.
  rewrite subst_cc_open_cc_rec...
  simpl.
  destruct (Y == X)...
Qed.

(** The next lemma states that opening a term is equivalent to first
    opening the term with a fresh name and then substituting for the
    name.  This is actually the strengthened induction hypothesis for
    the version we use in practice. *)

Lemma subst_cc_intro_rec : forall X A2 C k,
  X `notin` fv_cc A2 ->
  open_cc_rec k C A2 = subst_cc X C (open_cc_rec k (fchan X) A2).
Proof with try solve [congruence | intuition].
  induction A2; intros C K Fr; simpl in *; f_equal...
  Case "bchan".
    destruct (K == n)... simpl. destruct (X == X)...
  Case "fchan".
    destruct (a == X)... contradict Fr; fsetdec.
Qed.

(** The next lemma is a direct corollary of the immediately preceding
    lemma---the index is specialized to zero.  *)

Lemma subst_cc_intro : forall (X : atom) A2 C,
  X `notin` fv_cc A2 ->
  open_cc A2 C = subst_cc X C (open_cc A2 X).
Proof with try solve [congruence | intuition].
  intros.
  unfold open_cc.
  apply subst_cc_intro_rec...
Qed.


(* ********************************************************************** *)
(** ** Properties of channel substitution in expressions *)

(** This section follows the structure of the previous section.  The
    one notable difference is that we require two auxiliary lemmas to
    show that substituting a channel in a locally-closed expression is
    the identity.  (Or do we?  I don't really know.) *)

Lemma open_ce_rec_expr_aux : forall e j u i C ,
  open_ee_rec j u e = open_ce_rec i C (open_ee_rec j u e) ->
  e = open_ce_rec i C e.
Proof with try solve [congruence | eauto].
  induction e; intros j u i C H; simpl in *; inversion H; f_equal...
Qed.

Lemma open_ce_rec_channel_aux : forall e j A i C,
  i <> j ->
  open_ce_rec j A e = open_ce_rec i C (open_ce_rec j A e) ->
  e = open_ce_rec i C e.
Proof.
  induction e; intros j A i C Neq Heq; simpl in *; inversion Heq;
    f_equal; eauto using open_cc_rec_channel_aux.
Qed.

Lemma open_ce_rec_expr : forall e C k,
  expr e ->
  e = open_ce_rec k C e.
Proof with try solve [congruence | intuition].
  intros e C k WF. revert k.
  induction WF; intros k; simpl; f_equal; auto using open_cc_rec_channel;
  try solve [
    unfold open_ee in *;
    pick fresh x;
    eapply open_ce_rec_expr_aux with (j := 0) (u := exp_fvar x);
    try solve [congruence | intuition]
  | unfold open_ce in *;
    pick fresh X;
    eapply open_ce_rec_channel_aux with (j := 0) (A := fchan X);
    try solve [congruence | intuition]
  ].
(*  assert (exp_apair e1 e2 = open_ce_rec 0 C (exp_apair e1 e2)).
    apply IHWF.
  inversion H0.
  assert (exp_apair e1 e2 = open_ce_rec k C (exp_apair e1 e2)).
    apply IHWF.
  inversion H1.
  rewrite <- H5. rewrite <- H2. auto.
  assert (exp_apair e1 e2 = open_ce_rec 0 C (exp_apair e1 e2)).
    apply IHWF.
  inversion H0.
  assert (exp_apair e1 e2 = open_ce_rec k C (exp_apair e1 e2)).
    apply IHWF.
  inversion H1.
  rewrite <- H6. rewrite <- H3. auto. *)
Qed.

Lemma subst_ce_fresh : forall X C e,
  X `notin` fv_ce e ->
  e = subst_ce X C e.
Proof.
  induction e; simpl; intros; f_equal; auto using subst_cc_fresh.
Qed.

Lemma subst_ce_open_ce_rec : forall e A X C k,
  channel C ->
  subst_ce X C (open_ce_rec k A e) =
    open_ce_rec k (subst_cc X C A) (subst_ce X C e).
Proof.
  intros e A X C k WC. revert k.
  induction e; intros K; simpl; f_equal; auto using subst_cc_open_cc_rec.
Qed.

Lemma subst_ce_open_ce : forall e A X C,
  channel C ->
  subst_ce X C (open_ce e A) = open_ce (subst_ce X C e) (subst_cc X C A).
Proof with try solve [congruence | intuition].
  intros.
  unfold open_ce.
  apply subst_ce_open_ce_rec...
Qed.

Lemma subst_ce_open_ce_var : forall (X Y:atom) C e,
  Y <> X ->
  channel C ->
  open_ce (subst_ce X C e) Y = subst_ce X C (open_ce e Y).
Proof with try solve [congruence | intuition].
  intros X Y C e Neq WC.
  unfold open_ce.
  rewrite subst_ce_open_ce_rec...
  simpl.
  destruct (Y == X)...
Qed.

Lemma subst_ce_intro_rec : forall X e C k,
  X `notin` fv_ce e ->
  open_ce_rec k C e = subst_ce X C (open_ce_rec k (fchan X) e).
Proof.
  induction e; intros C K Fr; simpl in *; f_equal;
    auto using subst_cc_intro_rec.
Qed.

Lemma subst_ce_intro : forall (X : atom) e C,
  X `notin` fv_ce e ->
  open_ce e C = subst_ce X C (open_ce e X).
Proof with try solve [congruence | intuition].
  intros.
  unfold open_ce.
  apply subst_ce_intro_rec...
Qed.


(* ********************************************************************** *)
(** ** Properties of channel substitution in processes *)

(** This section follows the structure of the previous section.  *)

Lemma open_cp_rec_channel_aux : forall P j A i C,
  i <> j ->
  open_cp_rec j A P = open_cp_rec i C (open_cp_rec j A P) ->
  P = open_cp_rec i C P.
Proof.
  induction P; intros j A i C Neq Heq; simpl in *; inversion Heq;
    f_equal; eauto using open_ce_rec_channel_aux.
Qed.

Lemma open_cp_rec_process : forall P C k,
  process P ->
  P = open_cp_rec k C P.
Proof with try solve [congruence | intuition].
  intros P C k WF. revert k.
  induction WF; intros k; simpl; f_equal; auto using open_ce_rec_expr;
  unfold open_cp in *; pick fresh X;
  eapply open_cp_rec_channel_aux with (j := 0) (A := fchan X);
  try solve [congruence | intuition].
Qed.

Lemma subst_cp_fresh : forall X C P,
  X `notin` fv_cp P ->
  P = subst_cp X C P.
Proof.
  induction P; simpl; intros; f_equal; auto using subst_ce_fresh.
Qed.

Lemma subst_cp_open_cp_rec : forall P A X C k,
  channel C ->
  subst_cp X C (open_cp_rec k A P) =
    open_cp_rec k (subst_cc X C A) (subst_cp X C P).
Proof.
  intros P A X C k WC. revert k.
  induction P; intros K; simpl; f_equal; auto using subst_ce_open_ce_rec.
Qed.

Lemma subst_cp_open_cp : forall P A X C,
  channel C ->
  subst_cp X C (open_cp P A) = open_cp (subst_cp X C P) (subst_cc X C A).
Proof with try solve [congruence | intuition].
  intros.
  unfold open_cp.
  apply subst_cp_open_cp_rec...
Qed.

Lemma subst_cp_open_cp_var : forall (X Y:atom) C P,
  Y <> X ->
  channel C ->
  open_cp (subst_cp X C P) Y = subst_cp X C (open_cp P Y).
Proof with try solve [congruence | intuition].
  intros X Y C P Neq WC.
  unfold open_cp.
  rewrite subst_cp_open_cp_rec...
  simpl.
  destruct (Y == X)...
Qed.

Lemma subst_cp_intro_rec : forall X P C k,
  X `notin` fv_cp P ->
  open_cp_rec k C P = subst_cp X C (open_cp_rec k (fchan X) P).
Proof.
  induction P; intros C K Fr; simpl in *; f_equal;
    auto using subst_ce_intro_rec.
Qed.

Lemma subst_cp_intro : forall (X : atom) P C,
  X `notin` fv_cp P ->
  open_cp P C = subst_cp X C (open_cp P X).
Proof with try solve [congruence | intuition].
  intros.
  unfold open_cp.
  apply subst_cp_intro_rec...
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

Lemma open_ee_rec_channel_aux : forall e j C u i,
  open_ce_rec j C e = open_ee_rec i u (open_ce_rec j C e) ->
  e = open_ee_rec i u e.
Proof.
  induction e; intros j C u i H; simpl; inversion H; f_equal; eauto.
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
    eapply open_ee_rec_channel_aux with (j := 0) (A := fchan X);
    try solve [congruence | intuition]
  ].
  (*assert (exp_apair e1 e2 = open_ee_rec k u (exp_apair e1 e2)); auto.
  inversion H0. rewrite <- H2. auto.
  assert (exp_apair e1 e2 = open_ee_rec k u (exp_apair e1 e2)); auto.
  inversion H0. rewrite <- H3. auto.*)
Qed.

Lemma subst_ee_fresh : forall (x: atom) u e,
  x `notin` fv_ee e ->
  e = subst_ee x u e.
Proof with try solve [congruence | intuition].
  intros x u e; induction e; simpl; intro H; f_equal...
  Case "exp_fvar".
    destruct (a==x)...
    contradict H; fsetdec.
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

Lemma subst_ce_open_ee_rec : forall e1 e2 Z C k,
  subst_ce Z C (open_ee_rec k e2 e1) =
    open_ee_rec k (subst_ce Z C e2) (subst_ce Z C e1).
Proof with try solve [congruence | intuition].
  induction e1; intros e2 Z C K; simpl; f_equal...
  Case "exp_bvar".
    destruct (K == n)...
Qed.

Lemma subst_ce_open_ee : forall e1 e2 Z C,
  subst_ce Z C (open_ee e1 e2) = open_ee (subst_ce Z C e1) (subst_ce Z C e2).
Proof with try solve [congruence | intuition].
  intros.
  unfold open_ee.
  apply subst_ce_open_ee_rec...
Qed.

Lemma subst_ce_open_ee_var : forall Z (x:atom) C e,
  open_ee (subst_ce Z C e) x = subst_ce Z C (open_ee e x).
Proof with try solve [congruence | intuition].
  intros.
  rewrite subst_ce_open_ee...
Qed.

Lemma subst_ee_open_ce_rec : forall e C z u k,
  expr u ->
  subst_ee z u (open_ce_rec k C e) = open_ce_rec k C (subst_ee z u e).
Proof with try solve [congruence | intuition].
  induction e; intros C z u K H; simpl; f_equal...
  Case "exp_fvar".
    destruct (a == z)... apply open_ce_rec_expr...
Qed.

Lemma subst_ee_open_ce : forall e C z u,
  expr u ->
  subst_ee z u (open_ce e C) = open_ce (subst_ee z u e) C.
Proof with try solve [congruence | intuition].
  intros.
  unfold open_ce.
  apply subst_ee_open_ce_rec...
Qed.

Lemma subst_ee_open_ce_var : forall z (X:atom) u e,
  expr u ->
  open_ce (subst_ee z u e) X = subst_ee z u (open_ce e X).
Proof with try solve [congruence | intuition].
  intros z X u e H.
  rewrite subst_ee_open_ce...
Qed.

Lemma subst_ee_intro_rec : forall x e u k,
  x `notin` fv_ee e ->
  open_ee_rec k u e = subst_ee x u (open_ee_rec k (exp_fvar x) e).
Proof with try solve [congruence | intuition].
  induction e; intros u K Fr; simpl in *; f_equal...
  Case "exp_bvar".
    destruct (K == n)... simpl. destruct (x == x)...
  Case "exp_fvar".
    destruct (a == x)... contradict Fr; fsetdec.
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

(** The following lemma depends on [subst_cc_open_cc_var]. *)

Lemma subst_cc_channel : forall Z C A,
  channel A ->
  channel C ->
  channel (subst_cc Z C A).
Proof with auto.
  intros Z C A HA HC.
  induction HA; simpl...
  Case "fchan".
    destruct (x == Z)...
Qed.

(** The following lemma depends on [subst_cc_channel] and
    [subst_ce_open_ee_var]. *)

Lemma subst_ce_expr : forall Z C e,
  expr e ->
  channel C ->
  expr (subst_ce Z C e).
Proof with eauto using subst_cc_channel.
  intros Z C e He Hc.
  induction He; simpl; auto using subst_cc_channel;
  try solve [
    econstructor;
    try instantiate (1 := L `union` singleton Z);
    intros;
    try rewrite subst_ce_open_ee_var;
    try rewrite subst_ce_open_ce_var;
    eauto using subst_cc_channel
  ].
Qed.

(** The following lemma depends on things. *)

Lemma subst_cp_process : forall Z C P,
  process P ->
  channel C ->
  process (subst_cp Z C P).
Proof with eauto using subst_ce_expr.
  intros Z C P Hp Hc.
  induction Hp; simpl; auto using subst_ce_expr.
  econstructor... instantiate (1 := L `union` singleton Z).
  intros. rewrite subst_cp_open_cp_var...
Qed.

(** The following lemma depends on [subst_ee_open_ee_var] and
    [subst_ee_open_ce_var]. *)

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
    try rewrite subst_ee_open_ce_var;
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
               apply IHe1; auto |
  assert ((x `in` fv_ee e1_1) \/ (x `in` fv_ee e1_2)) as H;
    [ fsetdec
    | destruct H as [H | H] ;
      [ assert (x `in` fv_ee (open_ee_rec k1 e2 e1_1));
        [ apply IHe1_1; auto
        | fsetdec ]
      | assert (x `in` fv_ee (open_ee_rec k1 e2 e1_2));
        [ apply IHe1_2; auto
        | fsetdec ]]]].
  assert ((x `in` fv_ee e1_1) \/ (x `in` fv_ee e1_2) \/ (x `in` fv_ee e1_3)) as H.
    fsetdec.
  destruct H as [H | [H | H]].
    assert (x `in` fv_ee (open_ee_rec k1 e2 e1_1)).
      apply IHe1_1; auto.
    fsetdec.
    assert (x `in` fv_ee (open_ee_rec k1 e2 e1_2)).
      apply IHe1_2; auto.
    fsetdec.
    assert (x `in` fv_ee (open_ee_rec k1 e2 e1_3)).
      apply IHe1_3; auto.
    fsetdec.
Qed.

Lemma fv_in_open_ce:  forall x e1 C2 k,
   x `in` fv_ee e1 -> 
   x `in` fv_ee (open_ce_rec k C2 e1).
Proof.
  intros x. induction e1; intros C2 k1 IN; simpl in IN; simpl;
    try solve [fsetdec |
               apply IHe1; auto |
  assert ((x `in` fv_ee e1_1) \/ (x `in` fv_ee e1_2)) as H;
    [ fsetdec
    | destruct H as [H | H]; 
      [ assert (x `in` fv_ee (open_ce_rec k1 C2 e1_1));
        [ apply IHe1_1; auto
        | fsetdec ]
      | assert (x `in` fv_ee (open_ce_rec k1 C2 e1_2));
        [ apply IHe1_2; auto
        | fsetdec ]]]].
  assert ((x `in` fv_ee e1_1) \/ (x `in` fv_ee e1_2) \/ (x `in` fv_ee e1_3)) as H.
    fsetdec. 
  destruct H as [H | [H | H]].
    assert (x `in` fv_ee (open_ce_rec k1 C2 e1_1)).
      apply IHe1_1; auto. 
    fsetdec.
    assert (x `in` fv_ee (open_ce_rec k1 C2 e1_2)).
      apply IHe1_2; auto. 
    fsetdec.
    assert (x `in` fv_ee (open_ce_rec k1 C2 e1_3)).
      apply IHe1_3; auto. 
    fsetdec.
Qed.

Lemma notin_open_cc_rec_fv : forall (Y X : atom) A n,
  X `notin` fv_cc A ->
  X <> Y ->
  X `notin` fv_cc (open_cc_rec n Y A).
Proof.
  intros. 
  generalize dependent n. generalize dependent X.
  induction A; simpl; intros X Nin Neq n0; simpl; auto. 
    destruct (n0 == n); simpl; auto. 
Qed.

Lemma notin_open_cc_fv : forall (Y X : atom) A,
  X `notin` fv_cc A ->
  X <> Y ->
  X `notin` fv_cc (open_cc A Y).
Proof.
  intros. unfold open_cc.
  apply (notin_open_cc_rec_fv Y X A 0); auto.
Qed.

Lemma notin_fv_cc_open : forall (Y X : atom) A,
  X `notin` fv_cc (open_cc A Y) ->
  X `notin` fv_cc A.
Proof.
 intros Y X A. unfold open_cc.
 generalize 0.
 induction A; simpl; intros K Fr; destruct_notin; try apply notin_union; eauto.
Qed.

(* *********************************************************************** *)
(** * #<a name="close"></a># Properties about close *)



Lemma close_open_cc_rec : forall  (K:nat) (X:atom) (A:chan) ,
  X `notin` fv_cc A ->
  close_cc_rec K X (open_cc_rec K (fchan X) A) = A.
Proof.
  intros K X A NI.
  destruct A; simpl.
  destruct (K == n).
  simpl. (destruct (X == X)). inversion e. auto. tauto.
  simpl. auto.

  destruct (X == a). auto. subst. simpl in NI. fsetdec. auto.
Qed.

Lemma close_open_cc :forall (X:atom) (A:chan),
  X `notin` fv_cc A ->
  close_cc (open_cc A X) X = A.
Proof.
  intros X A NI.
  unfold close_cc. unfold open_cc. apply close_open_cc_rec; auto.
Qed.

Lemma open_close_cc_rec : forall (K:nat) (X:atom) (A:chan),
  channel A ->
  open_cc_rec K (fchan X) (close_cc_rec K X A) = A.
Proof.
  intros K X A CH.
  destruct A. inversion CH.
  simpl. destruct (X == a). simpl. destruct (K == K). inversion e. auto. 
  tauto.  simpl. auto.
Qed.

Lemma open_close_cc : forall (X:atom) (A:chan),
  channel A ->
  open_cc (close_cc A X) (fchan X) = A.
Proof.
  intros X A CH.
  unfold open_cc. unfold close_cc. apply open_close_cc_rec. auto.
Qed.

Lemma close_open_ce_rec : forall (K:nat) (X:atom) (e:exp),
  X `notin` fv_ce e ->
  close_ce_rec K X (open_ce_rec K (fchan X) e) = e.
Proof.
 intros K X e.
 induction e; intros; simpl in *; auto; 
   try (rewrite IHe; auto; fsetdec);
   try (rewrite IHe1; try fsetdec; try rewrite IHe2; auto; try fsetdec);
   try (rewrite IHe1; try fsetdec; try rewrite IHe2; try fsetdec; try rewrite IHe3; auto; try fsetdec); try (rewrite close_open_cc_rec; auto); auto.

   rewrite IHe3. auto. fsetdec.
Qed.

Lemma open_ee_rec_inj : forall e1 e2 (Z:atom) i,
  Z `notin` fv_ee e1 ->
  Z `notin` fv_ee e2 ->
  open_ee_rec i Z e1 = open_ee_rec i Z e2 ->
  e1 = e2.
Proof.
  intros e1.
  (exp_cases (induction e1) Case); intros e2 Z i NI1 NI2 EQ;
    destruct e2; simpl in *; subst; (
    try (destruct (i == n); inversion EQ; auto);
    try (inversion EQ; subst; rewrite (IHe1 e2 Z i); auto);
    try (inversion EQ; (rewrite (IHe1_1 e2_1 Z i); try rewrite (IHe1_2 e2_2 Z i))); auto
   ); auto.

  destruct (i == n0).
  subst; auto. inversion EQ.
  destruct (i == n0).
  inversion EQ. auto.
  subst. fsetdec. subst. fsetdec.
  
  rewrite (IHe1 e2 Z (S i)); auto.

  rewrite (IHe1_3 e2_3 Z i); auto.
Qed.

Lemma fv_ee_open_ce: forall e (X:atom) i,
  fv_ee (open_ce_rec i X e) = fv_ee e.
Proof.
  induction e; intros X i; simpl in *; (
    try rewrite IHe;
    try rewrite IHe1;
    try rewrite IHe2;
    try rewrite IHe3
  ); auto.
Qed.

Lemma fv_ee_close_ce: forall e (X:atom) i,
  fv_ee (close_ce_rec i X e) = fv_ee e.
Proof.
  induction e; intros X i; simpl in *; (
    try rewrite IHe;
    try rewrite IHe1;
    try rewrite IHe2;
    try rewrite IHe3
  ); auto.
Qed.

Lemma close_ce_open_ee_comm: forall e (X Y:atom) i j,
  close_ce_rec i X (open_ee_rec j Y e) = open_ee_rec j Y (close_ce_rec i X e).
Proof.
  induction e; intros X Y i j; simpl in *; (
    try rewrite (IHe X Y i j);
    try rewrite (IHe1 X Y i j);
    try rewrite (IHe2 X Y i j);
    try rewrite (IHe3 X Y i j)
  ); auto.

  destruct (j == n). simpl. auto.
  simpl. auto.

  rewrite (IHe X Y i (S j)); auto.
Qed.

Lemma close_open_cp_rec : forall P X i,
  X `notin` fv_cp P ->
  close_cp_rec i X (open_cp_rec i X P) = P.
Proof.
  induction P; intros X i NI; simpl in *; subst; auto.
  rewrite close_open_ce_rec; auto.
  rewrite (IHP1 X i); auto.
  rewrite (IHP2 X i); auto.
  rewrite (IHP X (S i)); auto.
Qed.

Lemma close_cc_open_cc_comm : forall C i j X v,
  channel v ->
  X `notin` fv_cc v ->
  i <> j ->
  close_cc_rec i X (open_cc_rec j v C) = open_cc_rec j v (close_cc_rec i X C).
Proof.
  destruct C; intros i j X v CH NI NE; simpl in *; auto.
  destruct (j == n); simpl in *.
  destruct v. simpl. auto. simpl. 
  destruct (X == a). subst. simpl in *. fsetdec. auto. auto.

  destruct (X == a). subst. destruct v. simpl in*. 
  destruct (j == i). subst. tauto. auto. simpl. 
  destruct (j == i). subst. tauto. auto. 
  simpl. auto.
Qed.

Lemma close_ce_open_ce_comm : forall e i j X v,
  channel v ->
  X `notin` fv_cc v ->
  i <> j ->
  close_ce_rec i X (open_ce_rec j v e) = open_ce_rec j v (close_ce_rec i X e).
Proof.
  induction e; intros i j X v C1 NI NE; simpl in *; (
    try rewrite IHe;
    try rewrite IHe1;
    try rewrite IHe2;
    try rewrite IHe3; 
    try rewrite close_cc_open_cc_comm
  ); auto.
Qed.

Lemma close_cp_open_cp_comm : forall P i j X v,
  channel v ->
  X `notin` fv_cc v ->
  i <> j ->
  close_cp_rec i X (open_cp_rec j v P) = open_cp_rec j v (close_cp_rec i X P).
Proof.
  induction P; intros i j X v C1 NI NE; simpl in *; (
    try rewrite IHP;
    try rewrite IHP1;
    try rewrite IHP2;
    try rewrite close_ce_open_ce_comm
  ); auto.
Qed.

Lemma fv_cc_close_cc : forall Z C (X:atom) i,
  Z `notin` fv_cc C ->
  Z `notin` fv_cc (close_cc_rec i X C).
Proof.
  intros Z C.
  destruct C; intros X i NI; simpl in *; auto.
  destruct (X == a).
  subst. simpl. fsetdec. simpl. auto.
Qed.

Lemma fv_ce_close_ce : forall Z e (X:atom) i,
  Z `notin` fv_ce e ->
  Z `notin` fv_ce (close_ce_rec i X e).
Proof.
  intros Z e.
  induction e; intros X i NI; simpl in *; try (apply fv_cc_close_cc); auto.
Qed.

Lemma fv_cp_close_cp: forall Z P (X:atom) i,
  Z `notin` fv_cp P ->
  Z `notin` fv_cp (close_cp_rec i X P).
Proof.
  intros Z P.
  induction P; intros X i NI; simpl in *; auto.
  apply fv_ce_close_ce; auto.
Qed.



Lemma notin_close_cc: forall Y C i X,
  Y `notin` fv_cc C ->
  Y `notin` fv_cc (close_cc_rec i X C).
Proof.
  intros Y C.
  induction C; intros i X NI; simpl in *; auto.
  destruct (X == a). simpl. fsetdec. simpl. auto.
Qed.

Lemma notin_close_ce: forall Y e i X,
  Y `notin` fv_ce e ->
  Y `notin` fv_ce (close_ce_rec i X e).
Proof.
  intros Y e.
  induction e; intros i X NI; simpl in *; try fsetdec; try apply notin_close_cc; auto.
Qed.

Lemma notin_close_cp: forall Y P i X,
  Y `notin` fv_cp P ->
  Y `notin` fv_cp (close_cp_rec i X P).
Proof.
  intros Y P.
  induction P; intros i X NI; simpl in *; auto.
  apply notin_close_ce; auto.
Qed.

Lemma fv_ce_close_ee: forall e i Z,
  fv_ce (close_ee_rec i Z e) = fv_ce e.
Proof.
  induction e; intros i Z; simpl in *; (
    try rewrite IHe;
    try rewrite IHe1;
    try rewrite IHe2;
    try rewrite IHe3
  ); auto.
  destruct (Z == a). simpl. auto. simpl. auto.
Qed.

Lemma fv_ce_open_ee: forall e i (Z:atom),
  fv_ce (open_ee_rec i Z e) = fv_ce e.
Proof.
  induction e; intros i Z; simpl in *; (
    try rewrite IHe;
    try rewrite IHe1;
    try rewrite IHe2;
    try rewrite IHe3
  ); auto.
  destruct (i == n). simpl. auto. simpl. auto.
Qed.



Lemma fv_close_cc_aux : forall K X A,
  X `notin` fv_cc (close_cc_rec K X A).
Proof.
  intros K X A.
  destruct A. simpl.  fsetdec. simpl. 
  destruct (X == a). fsetdec. fsetdec.
Qed.

Lemma fv_close_ce_aux : forall K X e,
  X `notin` fv_ce (close_ce_rec K X e).
Proof.
  intros K X e.
  (exp_cases (induction e) Case); simpl; try fsetdec;
  try (assert (X `notin` fv_cc (close_cc_rec K X c)); try (apply fv_close_cc_aux); fsetdec).
Qed.

Lemma fv_close_cp_aux : forall X K P,
  X `notin` fv_cp (close_cp_rec K X P).
Proof.
  intros X K P.
  generalize K.
  (proc_cases (induction P) Case); intros; simpl.
  apply fv_close_ce_aux. 
  
  assert (X `notin` fv_cp (close_cp_rec K0 X P1)); auto.
  
  auto.
Qed.

Lemma fv_close_cp : forall X P,
  X `notin` fv_cp (close_cp P X).
Proof.
  intros. unfold close_cp. apply fv_close_cp_aux.
Qed.

Lemma fv_ce_notin_open: forall X (u:atom) e i,
  X `notin` fv_cc u ->
  X `notin` fv_ce e ->
  X `notin` fv_ce (open_ce_rec i u e).
Proof.
  intros X u e.
  induction e; intros; simpl in *; try (eapply notin_open_cc_rec_fv); auto.
Qed.

Lemma fv_cp_notin_open: forall X (u:atom) P i,
  X `notin` fv_cc u ->
  X `notin` fv_cp P ->
  X `notin` fv_cp (open_cp_rec i u P).
Proof.
  intros X u P.
  induction P; intros; simpl in *; auto.

  apply fv_ce_notin_open; auto.
Qed.


Lemma open_cc_aux_inj : forall K X A1 A2, 
  X `notin` (fv_cc A1) `union` (fv_cc A2) ->
  open_cc_rec K (fchan X) A1 = open_cc_rec K (fchan X) A2 ->
  A1 = A2.
Proof.
  intros K X A1 A2 NI EQ.
  destruct A1; destruct A2; simpl in *; subst; auto.
  destruct (K == n).
  destruct (K == n0).
  subst.  auto. inversion e. inversion EQ.
  destruct (K == n0). inversion EQ. auto.
  destruct (K == n). inversion EQ. subst. fsetdec. auto.
  destruct (K == n). inversion EQ. subst. fsetdec. auto.
Qed.

Lemma open_ce_aux_inj : forall K X e1 e2,
  X `notin` (fv_ce e1) `union` (fv_ce e2) ->
  open_ce_rec K X e1 = open_ce_rec K X e2 ->
  e1 = e2.
Proof.
  intros K X e1. 
  generalize dependent K.
  (exp_cases (induction e1) Case); intros K e2 NI EQ; destruct e2; 
      simpl in *; inversion EQ; subst;
   first [   rewrite (IHe1 K e2); auto
           | rewrite (IHe1_1 K e2_1); ( auto || rewrite (IHe1_2 K e2_2); auto)
           | idtac ]; (try rewrite (open_cc_aux_inj K X c c0)) ; auto.

  Case "exp_case".
  rewrite (IHe1_3 K e2_3); auto.
Qed.

Lemma open_cp_aux_inj : forall K X P1 P2,
  X `notin` (fv_cp P1) `union` (fv_cp P2) ->
  open_cp_rec K X P1 = open_cp_rec K X P2 ->
  P1 = P2.
Proof.
  intros K X P1.
  generalize dependent K. generalize dependent X.
  (proc_cases (induction P1) Case); intros X K P2 NI EQ; destruct P2;
  simpl in *; inversion EQ; subst.
  assert (e = e0). eapply open_ce_aux_inj; eauto. subst. auto.

  rewrite (IHP1_1 X K P2_1); auto. 
  rewrite (IHP1_2 X K P2_2); auto.

  rewrite (IHP1 X (S K) P2); auto.
Qed.

Lemma open_cp_inj : forall X P1 P2,
  X `notin` (fv_cp P1) `union` (fv_cp P2) ->
  open_cp P1 X = open_cp P2 X ->
  P1 = P2.
Proof.
  intros. unfold open_cp in  H0.
  eapply open_cp_aux_inj. apply H.
  apply H0.
Qed.

Lemma open_cc_open_cc_comm : forall C i j u v,
  channel u ->
  channel v ->
  i <> j ->
  open_cc_rec i u (open_cc_rec j v C) = open_cc_rec j v (open_cc_rec i u C).
Proof.
  induction C; intros i j u v C1 C2 NE; simpl in *; auto.
  destruct (j == n). subst.
  destruct (i == n). subst. tauto.
  inversion C2. subst. simpl.
  destruct (n == n); tauto.
  destruct (i == n). subst. 
  inversion C1. subst. simpl.
  destruct (n == n); tauto.
  simpl.
  destruct (i == n); subst.
  destruct (j == n); subst. tauto. tauto.
  destruct (j == n); subst. tauto. auto.
Qed.
  
Lemma open_ce_open_ce_comm : forall e i j u v,
  channel u ->
  channel v ->
  i <> j ->
  open_ce_rec i u (open_ce_rec j v e) = open_ce_rec j v (open_ce_rec i u e).
Proof.
  induction e; intros i j u v C1 C2 NE; simpl in *; (
    try rewrite IHe;
    try rewrite IHe1;
    try rewrite IHe2;
    try rewrite IHe3; 
    try rewrite open_cc_open_cc_comm
  ); auto.
Qed.

Lemma open_cp_open_cp_comm : forall P i j u v,
  channel u ->
  channel v ->
  i <> j ->
  open_cp_rec i u (open_cp_rec j v P) = open_cp_rec j v (open_cp_rec i u P).
Proof.
  induction P; intros i j u v C1 C2 NE; simpl in *; auto.
  rewrite open_ce_open_ce_comm; auto.
  rewrite IHP1; auto. rewrite IHP2; auto.
  rewrite IHP; auto.
Qed.

  
Lemma open_ee_open_ce_comm: forall e f K J X,
  open_ee_rec K (open_ce_rec J X f) (open_ce_rec J X e) = open_ce_rec J X (open_ee_rec K f e).
Proof.
  (exp_cases (induction e) Case); intros f K J X; simpl in *; 
  first [  
          rewrite IHe1; rewrite IHe2; auto
         | rewrite IHe; auto
         | idtac ]; auto.
  
  destruct (K == n). auto. simpl. auto.

  rewrite IHe3. auto.
Qed.

Lemma open_close_ce_rec: forall (X:atom) e i,
  expr e ->
  open_ce_rec i X (close_ce_rec i X e) = e.
Proof.
  intros X e i EXP.
  generalize dependent i.
  induction EXP; intros i; simpl in *; subst; (
    try rewrite (IHEXP i);
    try rewrite (IHEXP1 i);
    try rewrite (IHEXP2 i);
    try rewrite (IHEXP3 i);
    try rewrite open_close_cc_rec
  ); auto.

  pick fresh Z.
  lapply (H1 Z); intros; auto.
  assert (open_ce_rec i X (close_ce_rec i X (open_ee e1 Z)) = open_ee e1 Z).
  apply H2; auto.
  unfold open_ee in H3.
  rewrite close_ce_open_ee_comm in H3.
  rewrite <- open_ee_open_ce_comm in H3.
  simpl in H3.
  rewrite (open_ee_rec_inj (open_ce_rec i X (close_ce_rec i X e1)) e1 Z 0); auto.  
  rewrite fv_ee_open_ce. rewrite fv_ee_close_ce. fsetdec.
Qed.

Lemma open_close_cp_rec: forall (X:atom) P i,
  process P ->
  open_cp_rec i X (close_cp_rec i X P) = P.
Proof.
  intros X P i PR.
  generalize dependent i.
  (process_cases (induction PR) Case); intros i; simpl in *; auto.

  Case "process_exp".
  rewrite open_close_ce_rec; auto. 

  Case "process_par".
  rewrite IHPR1; auto. rewrite IHPR2; auto.

  Case "process_new". 
  pick fresh Z.  
  assert (open_cp_rec (S i) X (close_cp_rec (S i) X (open_cp P1 Z)) = open_cp P1 Z).
  apply (H1 Z); auto.
  unfold open_cp in H2.
  rewrite close_cp_open_cp_comm in H2; auto.
  rewrite open_cp_open_cp_comm in H2; auto.
  rewrite (open_cp_aux_inj 0 Z (open_cp_rec (S i) X (close_cp_rec (S i) X P1)) P1); auto.
  assert (Z `notin` fv_cp (open_cp_rec (S i) X (close_cp_rec (S i) X P1))).
  apply fv_cp_notin_open. simpl. fsetdec.
  apply fv_cp_close_cp; auto. 
  apply notin_union; auto.
Qed.


Lemma close_open_ee : forall e Z i,
  Z `notin` fv_ee e -> 
  close_ee_rec i Z (open_ee_rec i Z e) = e.
Proof.
  induction e; intros Z i NI; simpl in *;  (
    try rewrite IHe;
    try rewrite IHe1; 
    try rewrite IHe2;
    try rewrite IHe3
  ); 
  auto.
  destruct (i == n). simpl. destruct (Z == Z). subst. auto.
  tauto.
  simpl. auto.
  destruct (Z == a). subst. fsetdec. auto.
Qed.

Lemma open_ce_close_ee_comm : forall e i j u Z,
  open_ce_rec i u (close_ee_rec j Z e) = close_ee_rec j Z (open_ce_rec i u e).
Proof.
 induction e; intros i j u Z; simpl in *; (
   try rewrite IHe;
   try rewrite IHe1;
   try rewrite IHe2;
   try rewrite IHe3
 ); auto.
 destruct (Z == a). simpl. auto.
 simpl. auto.
Qed.


Lemma close_open_cp : forall P i X,
  X `notin` fv_cp P ->
  close_cp_rec i X (open_cp_rec i X P) = P.
Proof.
  induction P; intros i X NI; simpl in *.

  rewrite close_open_ce_rec; auto.

  rewrite (IHP1 i X); auto.
  rewrite (IHP2 i X); auto.

  rewrite (IHP (S i) X); auto.
Qed.

Lemma open_close_ce : forall (X:atom) (e:exp),
  expr e ->
  open_ce (close_ce e X) (fchan X) = e.
Proof.
  intros X e Expr. unfold open_ce. unfold close_ce.
  apply open_close_ce_rec. auto.
Qed.

Lemma open_close_cp : forall (X:atom) (P:proc),
  process P ->
  open_cp (close_cp P X) (fchan X) = P.
Proof.
  intros X P Proc. unfold open_cp. unfold close_cp.
  apply open_close_cp_rec. auto.
Qed.

(* *********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

(** We add as hints the fact that local closure is preserved under
    substitution.  This is part of our strategy for automatically
    discharging local-closure proof obligations. *)

Hint Resolve subst_cc_channel subst_ce_expr subst_cp_process subst_ee_expr.

(** When reasoning about the [binds] relation and [map], we
    occasionally encounter situations where the binding is
    over-simplified.  The following hint undoes that simplification,
    thus enabling [Hint]s from the [Environment] library. *)

(* These don't seem to make sense for us... *)

(*Hint Extern 1 (binds _ (?F (subst_tt ?X ?U ?T)) _) =>
  unsimpl (subst_tb X U (F T)).

Hint Extern 1 (binds _ (?F (subst_tt ?X ?U ?T)) _) =>
  unsimpl (subst_tlb X U (F T)).*)

(* 
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../../../metatheory") ***
*** End: ***
 *)
