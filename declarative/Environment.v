(** Operations, lemmas, and tactics for working with environments,
    association lists whose keys are atoms.  Unless stated otherwise,
    implicit arguments will not be declared by default.

    Authors: Brian Aydemir and Arthur Charguéraud, with help from
    Aaron Bohannon, Benjamin Pierce, Jeffrey Vaughan, Dimitrios
    Vytiniotis, Stephanie Weirich, and Steve Zdancewic.

    Table of contents:
      - #<a href="##overview">Overview</a>#
      - #<a href="##functions">Functions on environments</a>#
      - #<a href="##env_rel">Relations on environments</a>#
      - #<a href="##op_prop">Properties of operations</a>#
      - #<a href="##auto1">Automation and tactics (I)</a>#
      - #<a href="##props">Properties of well-formedness and freshness</a>#
      - #<a href="##binds_prop">Properties of binds</a>#
      - #<a href="##auto2">Automation and tactics (II)</a>#
      - #<a href="##binds_prop2">Additional properties of binds</a>#
      - #<a href="##auto3">Automation and tactics (III)</a># *)

Require Export List.
Require Export ListFacts.
Require Import Atom.

Import AtomSet.F.
Hint Local Unfold E.eq.


(* ********************************************************************** *)
(** * #<a name="overview"></a># Overview *)

(** An environment is a list of pairs, where the first component of
    each pair is an [atom].  We view the second component of each pair
    as being bound to the first component.  In a well-formed
    environment, there is at most one binding for any given atom.
    Bindings at the head of the list are "more recent" than bindings
    toward the tail of the list, and we view an environment as growing
    on the left, i.e., at its head.

    We normally work only with environments built up from the
    following: the empty list, one element lists, and concatenations
    of two lists.  This seems to be more convenient in practice.  For
    example, we don't need to distinguish between consing on a binding
    and concatenating a binding, a difference that Coq's tactics can
    be sensitive to.

    However, basic definitions are by induction on the usual structure
    of lists ([nil] and [cons]).

    To make it convenient to write one element lists, we define a
    special notation.  Note that this notation is local to this
    particular library, to allow users to use alternate notations if
    they desire. *)

Notation Local "[ x ]" := (cons x nil).

(** In the remainder of this library, we define a number of
    operations, lemmas, and tactics that simplify working with
    environments. *)


(* ********************************************************************** *)
(** * #<a name="functions"></a># Functions on environments *)

(** Implicit arguments will be declared by default for the definitions
    in this section. *)

Set Implicit Arguments.

Section Definitions.

Variables A B : Type.

(** The domain of an environment is the set of atoms that it maps. *)

Fixpoint dom (E : list (atom * A)) : atoms :=
  match E with
  | nil => empty
  | (x, _) :: E' => union (singleton x) (dom E')
  end.

(** [map] applies a function to all bindings in the environment. *)

Fixpoint map (f : A -> B) (E : list (atom * A)) : list (atom * B) :=
  match E with
  | nil => nil
  | (x, V) :: E' => (x, f V) :: map f E'
  end.

(** [get] returns the value bound to the given atom in an environment
    or [None] if the given atom is not bound.  If the atom has
    multiple bindings, the one nearest to the head of the environment
    is returned. *)

Fixpoint get (x : atom) (E : list (atom * A)) : option A :=
  match E with
  | nil => None
  | (y,a) :: E' => if eq_atom_dec x y then Some a else get x E'
  end.

End Definitions.

Unset Implicit Arguments.


(* ********************************************************************** *)
(** * #<a name="env_rel"></a># Relations on environments *)

(** Implicit arguments will be declared by default for the definitions
    in this section. *)

Set Implicit Arguments.

Section Relations.

Variable A : Type.

(** An environment is well-formed if and only if each atom is bound at
    most once. *)

Inductive ok : list (atom * A) -> Prop :=
  | ok_nil :
      ok nil
  | ok_cons : forall (E : list (atom * A)) (x : atom) (a : A),
      ok E -> ~ In x (dom E) -> ok ((x, a) :: E).

(** #<a name="binds_doc"></a># An environment [E] contains a binding
    from [x] to [b], denoted [(binds x b E)], if and only if the most
    recent binding for [x] is mapped to [b]. *)

Definition binds x b (E : list (atom * A)) :=
  get x E = Some b.

End Relations.

Unset Implicit Arguments.


(* ********************************************************************** *)
(** * #<a name="op_prop"></a># Properties of operations *)

Section OpProperties.
Variable A B : Type.
Implicit Types E F : list (atom * A).
Implicit Types a b : A.

(** ** Facts about concatenation *)

Lemma concat_nil : forall E,
  E ++ nil = E.
Proof.
  auto using List.app_nil_end.
Qed.

Lemma nil_concat : forall E,
  nil ++ E = E.
Proof.
  reflexivity.
Qed.

Lemma concat_assoc : forall E F G,
  (G ++ F) ++ E = G ++ (F ++ E).
Proof.
  auto using List.app_ass.
Qed.

(** ** [map] commutes with environment-building operations *)

Lemma map_nil : forall (f : A -> B),
  map f nil = nil.
Proof.
  reflexivity.
Qed.

Lemma map_single : forall (f : A -> B) y b,
  map f [(y,b)] = [(y, f b)].
Proof.
  reflexivity.
Qed.

Lemma map_push : forall (f : A -> B) y b E,
  map f ([(y,b)] ++ E) = [(y, f b)] ++ map f E.
Proof.
  reflexivity.
Qed.

Lemma map_concat : forall (f : A -> B) E F,
  map f (F ++ E) = (map f F) ++ (map f E).
Proof.
  induction F as [|(x,a)]; simpl; congruence.
Qed.

(** ** Facts about the domain of an environment *)

Lemma dom_nil :
  @dom A nil = empty.
Proof.
  reflexivity.
Qed.

Lemma dom_single : forall x a,
  dom [(x,a)] = singleton x.
Proof.
  simpl. intros. fsetdec.
Qed.

Lemma dom_push : forall x a E,
  dom ([(x,a)] ++ E) = union (singleton x) (dom E).
Proof.
  simpl. intros. reflexivity.
Qed.

Lemma dom_concat : forall E F,
  dom (F ++ E) = union (dom F) (dom E).
Proof.
  induction F as [|(x,a) F IH]; simpl.
  fsetdec.
  rewrite IH. fsetdec.
Qed.

Lemma dom_map : forall (f : A -> B) E,
  dom (map f E) = dom E.
Proof.
  induction E as [|(x,a)]; simpl; congruence.
Qed.

(** ** Other trivial rewrites *)

Lemma cons_concat_assoc : forall x a E F,
   ((x, a) :: E) ++ F = (x, a) :: (E ++ F).
Proof.
  reflexivity.
Qed.

End OpProperties.


(* ********************************************************************** *)
(** * #<a name="auto1"></a># Automation and tactics (I) *)

(** ** [simpl_env] *)

(** The [simpl_env] tactic can be used to put environments in the
    standardized form described above, with the additional properties
    that concatenation is associated to the right and empty
    environments are removed.  Similar to the [simpl] tactic, we
    define "[in *]" and "[in H]" variants of [simpl_env]. *)

Definition singleton_list (A : Type) (x : atom * A) := x :: nil.
Implicit Arguments singleton_list [A].

Lemma cons_concat : forall (A : Type) (E : list (atom * A)) x a,
  (x, a) :: E = singleton_list (x, a) ++ E.
Proof.
  reflexivity.
Qed.

Lemma map_singleton_list : forall (A B : Type) (f : A -> B) y b,
  map f (singleton_list (y,b)) = [(y, f b)].
Proof.
  reflexivity.
Qed.

Lemma dom_singleton_list : forall (A : Type) (x : atom) (a : A),
  dom (singleton_list (x,a)) = singleton x.
Proof.
  simpl. intros. fsetdec.
Qed.

Hint Rewrite
  cons_concat map_singleton_list dom_singleton_list
  concat_nil nil_concat concat_assoc
  map_nil map_single map_push map_concat
  dom_nil dom_single dom_push dom_concat dom_map : rew_env.

Ltac simpl_env_change_aux :=
  match goal with
    | H : context[?x :: nil] |- _ =>
      progress (change (x :: nil) with (singleton_list x) in H);
      simpl_env_change_aux
    | |- context[?x :: nil] =>
      progress (change (x :: nil) with (singleton_list x));
      simpl_env_change_aux
    | _ =>
      idtac
  end.

Ltac simpl_env :=
  simpl_env_change_aux;
  autorewrite with rew_env;
  unfold singleton_list in *.

Tactic Notation "simpl_env" "in" hyp(H) :=
  simpl_env_change_aux;
  autorewrite with rew_env in H;
  unfold singleton_list in *.

Tactic Notation "simpl_env" "in" "*" :=
  simpl_env_change_aux;
  autorewrite with rew_env in *;
  unfold singleton_list in *.

(** ** [rewrite_env] *)

(** The tactic [(rewrite_env E)] replaces an environment in the
    conclusion of the goal with [E].  Suitability for replacement is
    determined by whether [simpl_env] can put [E] and the chosen
    environment in the same normal form, up to convertability in Coq.
    We also define a "[in H]" variant that performs the replacement in
    a hypothesis [H]. *)

Tactic Notation "rewrite_env" constr(E) :=
  match goal with
    | |- context[?x] =>
      change x with E
    | |- context[?x] =>
      replace x with E; [ | try reflexivity; simpl_env; reflexivity ]
  end.

Tactic Notation "rewrite_env" constr(E) "in" hyp(H) :=
  match type of H with
    | context[?x] =>
      change x with E in H
    | context[?x] =>
      replace x with E in H; [ | try reflexivity; simpl_env; reflexivity ]
  end.

(** ** Hints *)

Hint Constructors ok.

Hint Local Extern 1 (~ In _ _) => simpl_env in *; fsetdec.


(* ********************************************************************** *)
(** * #<a name="props"></a># Properties of well-formedness and freshness *)

Section OkProperties.
Variable A B : Type.
Implicit Types E F : list (atom * A).
Implicit Types a b : A.

(** Facts about when an environment is well-formed. *)

Lemma ok_push :  forall (E : list (atom * A)) (x : atom) (a : A),
      ok E -> ~ In x (dom E) -> ok ([(x, a)] ++ E).
Proof.
  exact (@ok_cons A).
Qed.

Lemma ok_singleton : forall x a,
  ok [(x,a)].
Proof.
  auto.
Qed.

Lemma ok_remove_mid : forall F E G,
  ok (G ++ F ++ E) -> ok (G ++ E).
Proof with auto.
  induction G as [|(y,a)]; intros Ok.
    induction F as [|(y,a)]; simpl... inversion Ok...
    inversion Ok. simpl...
Qed.

Lemma ok_remove_mid_cons : forall x a E G,
  ok (G ++ (x, a) :: E) ->
  ok (G ++ E).
Proof.
  intros. simpl_env in *. eauto using ok_remove_mid.
Qed.

Lemma ok_remove_head : forall E F,
  ok (E ++ F) ->
  ok F.
Proof.
  intros.
  rewrite_env (nil ++ F).
  rewrite_env (nil ++ E ++ F) in H.
  eauto using ok_remove_mid.
Qed.

Lemma ok_map : forall E (f : A -> B),
  ok E -> ok (map f E).
Proof with auto.
  intros.
  induction E as [ | (y,b) E ] ; simpl...
  inversion H...
Qed.

Lemma ok_map_inv : forall E (f : A -> B),
  ok (map f E) -> ok E.
Proof with auto.
  intros.
  induction E as [ | (y,b) E ] ; simpl in *...
  inversion H...
Qed.

Lemma ok_map_app_l : forall E F (f : A -> A),
  ok (F ++ E) -> ok (map f F ++ E).
Proof with auto.
  intros. induction F as [|(y,a)]; simpl...
  inversion H...
Qed.

(** A binding in the middle of an environment has an atom fresh from
    all bindings before and after it. *)

Lemma fresh_tail_In : forall F G x,
    ok (F ++ G) -> In x (dom F) -> ~ In x (dom G).
Proof with auto.
  induction F as [|(y,b)]; intros G x H J; simpl_env in *.
  assert False by fsetdec. intuition.
  destruct (AtomSet.F.union_1 J) as [K | K].
    assert (x = y) by fsetdec; subst.
      inversion H; subst...
    assert (ok (F ++ G)) by eauto using ok_remove_head...
Qed.

Lemma fresh_mid_head_In : forall E F G x,
  ok (G ++ F ++ E) -> In x (dom F) -> ~ In x (dom G).
Proof with auto.
  induction G as [|(y,b)]; intros x Ok J; simpl_env in *...
  inversion Ok; subst; simpl_env in *...
  repeat apply notin_union...
Qed.

Lemma fresh_mid_tail_In : forall E F G x,
  ok (G ++ F ++ E) -> In x (dom F) -> ~ In x (dom E).
Proof with auto.
  induction E as [|(y,b)]; intros F G x Ok J; simpl_env in *...
  assert (ok (G ++ F ++ E)).
    rewrite_env ((G ++ F) ++ E).
    rewrite_env ((G ++ F) ++ [(y,b)] ++ E) in Ok.
    eauto using ok_remove_mid.
  assert (ok (F ++ [(y,b)] ++ E)) by eauto using ok_remove_head.
  assert (~ In x (dom ([(y,b)] ++ E))).
    eapply fresh_tail_In. apply H0. auto.
  auto.
Qed.

Lemma fresh_mid_tail : forall E F x a,
  ok (F ++ [(x,a)] ++ E) -> ~ In x (dom E).
Proof with auto.
  induction F as [|(y,b)]; intros x c Ok; simpl_env in *.
    inversion Ok...
    inversion Ok; subst. simpl_env in *. apply (IHF _ _ H1).
Qed.

Lemma fresh_mid_head : forall E F x a,
  ok (F ++ [(x,a)] ++ E) -> ~ In x (dom F).
Proof with auto.
  induction F as [|(y,b)]; intros x c Ok; simpl_env in *.
    inversion Ok...
    inversion Ok; subst. simpl_env in *. pose proof (IHF _ _ H1)...
Qed.

End OkProperties.


(* ********************************************************************** *)
(** * #<a name="binds_prop"></a># Properties of [binds] *)

Section BindsProperties.
Variable A B : Type.
Implicit Types E F : list (atom * A).
Implicit Types a b : A.

(** ** Introduction forms for [binds] *)

(** The following properties allow one to view [binds] as an
    inductively defined predicate.  This is the preferred way of
    working with the relation. *)

Lemma binds_singleton : forall x a,
  binds x a [(x,a)].
Proof.
  intros x a. unfold binds. simpl. destruct (eq_atom_dec x x); intuition.
Qed.

Lemma binds_tail : forall x a E F,
  binds x a E -> ~ In x (dom F) -> binds x a (F ++ E).
Proof with auto.
  unfold binds. induction F as [|(y,b)]; simpl...
  destruct (eq_atom_dec x y)... intros _ J. destruct J. fsetdec.
Qed.

Lemma binds_head : forall x a E F,
  binds x a F -> binds x a (F ++ E).
Proof.
  unfold binds. induction F as [|(y,b)]; simpl; intros H.
  discriminate.
  destruct (eq_atom_dec x y); intuition.
Qed.

(** ** Case analysis on [binds] *)

Lemma binds_concat_inv : forall x a E F,
  binds x a (F ++ E) -> (~ In x (dom F) /\ binds x a E) \/ (binds x a F).
Proof with auto.
  unfold binds. induction F as [|(y,b)]; simpl; intros H...
  destruct (eq_atom_dec x y).
    right...
    destruct (IHF H) as [[? ?] | ?]. left... right...
Qed.

Lemma binds_singleton_inv : forall x y a b,
  binds x a [(y,b)] -> x = y /\ a = b.
Proof.
  unfold binds. simpl. intros. destruct (eq_atom_dec x y).
    split; congruence.
    discriminate.
Qed.

(** ** Retrieving bindings from an environment *)

Lemma binds_mid : forall x a E F,
  ok (F ++ [(x,a)] ++ E) -> binds x a (F ++ [(x,a)] ++ E).
Proof with auto.
  unfold binds. induction F as [|(z,b)]; simpl; intros Ok.
  destruct (eq_atom_dec x x); intuition.
  inversion Ok; subst. destruct (eq_atom_dec x z)...
    destruct H3. simpl_env. fsetdec.
Qed.

Lemma binds_mid_eq : forall z a b E F,
  binds z a (F ++ [(z,b)] ++ E) -> ok (F ++ [(z,b)] ++ E) -> a = b.
Proof with auto.
  unfold binds. induction F as [|(x,c)]; simpl; intros H Ok.
  destruct (eq_atom_dec z z). congruence. intuition.
  inversion Ok; subst. destruct (eq_atom_dec z x)...
    destruct H4. simpl_env. fsetdec.
Qed.

Lemma binds_mid_eq_cons : forall x a b E F,
  binds x a (F ++ (x,b) :: E) ->
  ok (F ++ (x,b) :: E) ->
  a = b.
Proof.
  intros. simpl_env in *. eauto using binds_mid_eq.
Qed.

End BindsProperties.


(* ********************************************************************** *)
(** * #<a name="auto2"></a># Automation and tactics (II) *)

(** ** Hints *)

Hint Immediate ok_remove_mid ok_remove_mid_cons.

Hint Resolve
  ok_push ok_singleton ok_map ok_map_app_l
  binds_singleton binds_head binds_tail.

(** ** [binds_get] *)

(** The tactic [(binds_get H)] takes a hypothesis [H] of the form
    [(binds x a (F ++ [(x,b)] ++ E))] and introduces the equality
    [a=b] into the context.  Then, the tactic checks if the equality
    is discriminable and otherwise tries substituting [b] for [a].
    The [auto] tactic is used to show that [(ok (F ++ [(x,b)] ++ E))],
    which is needed to prove the equality [a=b] from [H]. *)

Ltac binds_get H :=
  match type of H with
    | binds ?z ?a (?F ++ [(?z,?b)] ++ ?E) =>
        let K := fresh in
          assert (K : ok (F ++ [(z,b)] ++ E));
          [ auto
          | let J := fresh in
              assert (J := @binds_mid_eq _ _ _ _ _ _ H K);
              clear K;
              try discriminate;
              try match type of J with
                    | ?a = ?b => subst a
                  end
          ]
  end.

(** ** [binds_cases] *)

(** The tactic [(binds_case H)] performs a case analysis on an
    hypothesis [H] of the form [(binds x a E)].  There will be one
    subgoal for each component of [E] that [x] could be bound in, and
    each subgoal will have appropriate freshness conditions on [x].
    Some attempts are made to automatically discharge contradictory
    cases. *)

Ltac binds_cases H :=
  let Fr := fresh "Fr" in
  let J1 := fresh in
  let J2 := fresh in
    match type of H with
      | binds _ _ nil =>
          inversion H
      | binds ?x ?a [(?y,?b)] =>
          destruct (@binds_singleton_inv _ _ _ _ _ H);
          clear H;
          try discriminate;
          try subst y;
          try match goal with
                | _ : ?z <> ?z |- _ => intuition
              end
      | binds ?x ?a (?F ++ ?E) =>
          destruct (@binds_concat_inv _ _ _ _ _ H) as [[Fr J1] | J2];
          clear H;
          [ binds_cases J1 | binds_cases J2 ]
      | _ => idtac
  end.


(* *********************************************************************** *)
(** * #<a name="binds_prop2"></a># Additional properties of [binds] *)

(** The following lemmas are proven in manner that should be
    independent of the concrete definition of [binds]. *)

Section AdditionalBindsProperties.
Variable A B : Type.
Implicit Types E F : list (atom * A).
Implicit Types a b : A.

(** Lemmas about the relationship between [binds] and the domain of an
    environment. *)

Lemma binds_In : forall a x E,
  binds x a E -> In x (dom E).
Proof.
  induction E as [|(y,b)]; simpl_env; intros H.
  binds_cases H.
  binds_cases H; subst. auto using union_3. fsetdec.
Qed.

Lemma binds_fresh : forall x a E,
  ~ In x (dom E) -> ~ binds x a E.
Proof.
  induction E as [|(y,b)]; simpl_env; intros Fresh H.
  binds_cases H.
  binds_cases H. intuition. fsetdec.
Qed.

(** Additional lemmas for showing that a binding is in an
    environment. *)

Lemma binds_map : forall x a (f : A -> B) E,
  binds x a E -> binds x (f a) (map f E).
Proof.
  induction E as [|(y,b)]; simpl_env; intros H.
  binds_cases H.
  binds_cases H; auto. subst; auto.
Qed.

Lemma binds_map_inv : forall x a (f : A -> B) E,
  (forall a b, f a = f b -> a = b) ->
  binds x (f a) (map f E) ->
  binds x a E.
Proof.
  induction E as [|(y,b)]; simpl_env in *; intros J H.
  binds_cases H.
  binds_cases H; auto. assert (a = b) by eauto. subst; auto.
Qed.

Lemma binds_concat_ok : forall x a E F,
  binds x a E -> ok (F ++ E) -> binds x a (F ++ E).
Proof.
  induction F as [|(y,b)]; simpl_env; intros H Ok.
  auto.
  inversion Ok; subst. destruct (eq_atom_dec x y); subst; auto.
    assert (In y (dom (F ++ E))) by eauto using binds_In.
    intuition.
Qed.

Lemma binds_weaken : forall x a E F G,
  binds x a (G ++ E) ->
  ok (G ++ F ++ E) ->
  binds x a (G ++ F ++ E).
Proof.
  induction G as [|(y,b)]; simpl_env; intros H Ok.
  auto using binds_concat_ok.
  inversion Ok; subst. binds_cases H; subst; auto.
Qed.

Lemma binds_weaken_at_head : forall x a F G,
  binds x a G ->
  ok (F ++ G) ->
  binds x a (F ++ G).
Proof.
  intros x a F G H J.
  rewrite_env (nil ++ F ++ G).
  apply binds_weaken; simpl_env; trivial.
Qed.

Lemma binds_remove_mid : forall x y a b F G,
  binds x a (F ++ [(y,b)] ++ G) ->
  x <> y ->
  binds x a (F ++ G).
Proof.
  intros x y a b F G H J.
  binds_cases H; auto.
Qed.

Lemma binds_remove_mid_cons : forall x y a b E G,
  binds x a (G ++ (y, b) :: E) ->
  x <> y ->
  binds x a (G ++ E).
Proof.
  intros. simpl_env in *. eauto using binds_remove_mid.
Qed.

End AdditionalBindsProperties.


(* *********************************************************************** *)
(** * #<a name="auto3"></a># Automation and tactics (III) *)

Hint Resolve binds_map binds_concat_ok binds_weaken binds_weaken_at_head.

Hint Immediate binds_remove_mid binds_remove_mid_cons.
