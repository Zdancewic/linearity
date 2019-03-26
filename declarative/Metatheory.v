(** Library for programming languages metatheory.

    Authors: Brian Aydemir and Arthur Charguéraud, with help from
    Aaron Bohannon, Benjamin Pierce, Jeffrey Vaughan, Dimitrios
    Vytiniotis, Stephanie Weirich, and Steve Zdancewic. *)

Require Export AdditionalTactics.
Require Export Atom.
Require Export Environment.


(* ********************************************************************** *)
(** * Notations *)

(** Decidable equality on atoms and natural numbers may be written
    using natural notation. *)

Notation "x == y" :=
  (eq_atom_dec x y) (at level 67) : metatheory_scope.
Notation "i === j" :=
  (Peano_dec.eq_nat_dec i j) (at level 67) : metatheory_scope.

(** Common set operations may be written using infix notation. *)

Notation "E `union` F" :=
  (AtomSet.F.union E F)
  (at level 69, right associativity, format "E  `union`  '/' F")
  : set_scope.
Notation "E `inter` F" :=
  (AtomSet.F.inter E F)
  (at level 69, right associativity, format "E  `inter`  '/' F")
  : set_scope.
Notation "x `in` E" :=
  (AtomSet.F.In x E) (at level 69) : set_scope.
Notation "x `notin` E" :=
  (~ AtomSet.F.In x E) (at level 69) : set_scope.

(** The empty set may be written similarly to informal practice. *)

Notation "{}" :=
  (AtomSet.F.empty) : metatheory_scope.

(** It is useful to have an abbreviation for constructing singleton
    sets. *)

Notation singleton := (AtomSet.F.singleton).

(** Open the notation scopes declared above. *)

Open Scope metatheory_scope.
Open Scope set_scope.


(* ********************************************************************** *)
(** * Tactic for working with cofinite quantification *)

(** Consider a rule [H] (equivalently, hypothesis, constructor, lemma,
    etc.) of the form [(forall L ..., ... -> (forall y, y `notin` L ->
    P) -> ... -> Q)], where [Q]'s outermost constructor is not a
    [forall].  There may be multiple hypotheses of with the indicated
    form in [H].

    The tactic [(pick fresh x and apply H)] applies [H] to the current
    goal, instantiating [H]'s first argument (i.e., [L]) with the
    finite set of atoms [L'].  In each new subgoal arising from a
    hypothesis of the form [(forall y, y `notin` L -> P)], the atom
    [y] is introduced as [x], and [(y `notin` L)] is introduced using
    a generated name.

    If we view [H] as a rule that uses cofinite quantification, the
    tactic can be read as picking a sufficiently fresh atom to open a
    term with.  *)

Tactic Notation
      "pick" "fresh" ident(atom_name)
      "excluding" constr(L)
      "and" "apply" constr(H) :=
  let L := beautify_fset L in
    first [apply (@H L) | eapply (@H L)];
    match goal with
      | |- forall _, _ `notin` _ -> _ =>
            let Fr := fresh "Fr" in intros atom_name Fr
      | |- forall _, _ `notin` _ -> _ =>
            fail 1 "because" atom_name "is already defined"
      | _ =>
            idtac
    end.


(* ********************************************************************** *)
(** * Automation *)

(** These hints should discharge many of the freshness and inequality
    goals that arise in programming language metatheory proofs, in
    particular those arising from cofinite quantification. *)

Hint Resolve notin_empty notin_singleton notin_union.
Hint Extern 4 (_ `notin` _) => simpl_env; notin_solve.
Hint Extern 4 (_ <> _ :> atom) => simpl_env; notin_solve.
