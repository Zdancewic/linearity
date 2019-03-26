(** Support for atoms, i.e., objects with decidable equality.  We
    provide here the ability to generate an atom fresh for any finite
    collection, e.g., the lemma [atom_fresh_for_set], and a tactic to
    pick an atom fresh for the current proof context.

    Authors: Arthur Charguéraud and Brian Aydemir.

    Implementation note: In older versions of Coq, [OrderedTypeEx]
    redefines decimal constants to be integers and not natural
    numbers.  The following scope declaration is intended to address
    this issue.  In newer versions of Coq, the declaration should be
    benign. *)

Require Import List.
Require Import Max.
Require Import OrderedType.
Require Import OrderedTypeEx.
Open Scope nat_scope.

Require Import FiniteSets.
Require Import FSetDecide.
Require Import FSetNotin.
Require Import ListFacts.


(* ********************************************************************** *)
(** * Definition *)

(** Atoms are structureless objects such that we can always generate
    one fresh from a finite collection.  Equality on atoms is [eq] and
    decidable.  We use Coq's module system to make abstract the
    implementation of atoms.  The [Export AtomImpl] line below allows
    us to refer to the type [atom] and its properties without having
    to qualify everything with "[AtomImpl.]". *)

Module Type ATOM.

  Parameter atom : Set.

  Parameter atom_fresh_for_list :
    forall (xs : list atom), {x : atom | ~ List.In x xs}.

  Declare Module Atom_as_OT : UsualOrderedType with Definition t := atom.

  Parameter eq_atom_dec : forall x y : atom, {x = y} + {x <> y}.

End ATOM.

(** The implementation of the above interface is hidden for
    documentation purposes. *)

Module AtomImpl : ATOM.

  (* begin hide *)

  Definition atom := nat.

  Lemma max_lt_r : forall x y z,
    x <= z -> x <= max y z.
  Proof.
    induction x. auto with arith.
    induction y; auto with arith.
      simpl. induction z. omega. auto with arith.
  Qed.

  Lemma nat_list_max : forall (xs : list nat),
    { n : nat | forall x, In x xs -> x <= n }.
  Proof.
    induction xs as [ | x xs [y H] ].
    (* case: nil *)
    exists 0. inversion 1.
    (* case: cons x xs *)
    exists (max x y). intros z J. simpl in J. destruct J as [K | K].
      subst. auto with arith.
      auto using max_lt_r.
  Qed.

  Lemma atom_fresh_for_list :
    forall (xs : list nat), { n : nat | ~ List.In n xs }.
  Proof.
    intros xs. destruct (nat_list_max xs) as [x H].
    exists (S x). intros J. lapply (H (S x)). omega. trivial.
  Qed.

  Module Atom_as_OT := Nat_as_OT.
  Module Facts := OrderedTypeFacts Atom_as_OT.

  Definition eq_atom_dec : forall x y : atom, {x = y} + {x <> y} :=
    Facts.eq_dec.

  (* end hide *)

End AtomImpl.

Export AtomImpl.


(* ********************************************************************** *)
(** * Finite sets of atoms *)


(* ********************************************************************** *)
(** ** Definitions *)

Module AtomSet : FiniteSets.S with Module E := Atom_as_OT :=
  FiniteSets.Make Atom_as_OT.

(** The type [atoms] is the type of finite sets of [atom]s. *)

Notation atoms := AtomSet.F.t.

(** Basic operations on finite sets of atoms are available, in the
    remainder of this file, without qualification.  We use [Import]
    instead of [Export] in order to avoid unnecessary namespace
    pollution. *)

Import AtomSet.F.

(** We instantiate two modules which provide useful lemmas and tactics
    work working with finite sets of atoms. *)

Module AtomSetDecide := FSetDecide.Decide AtomSet.F.
Module AtomSetNotin  := FSetNotin.Notin   AtomSet.F.


(* *********************************************************************** *)
(** ** Tactics for working with finite sets of atoms *)

(** The tactic [fsetdec] is a general purpose decision procedure
    for solving facts about finite sets of atoms. *)

Ltac fsetdec := try apply AtomSet.eq_if_Equal; AtomSetDecide.fsetdec.

(** The tactic [notin_simpl] simplifies all hypotheses of the form [(~
    In x F)], where [F] is constructed from the empty set, singleton
    sets, and unions. *)

Ltac notin_simpl := AtomSetNotin.notin_simpl_hyps.

(** The tactic [notin_solve], solves goals of the form [(~ In x F)],
    where [F] is constructed from the empty set, singleton sets, and
    unions.  The goal must be provable from hypothesis of the form
    simplified by [notin_simpl]. *)

Ltac notin_solve := AtomSetNotin.notin_solve.


(* *********************************************************************** *)
(** ** Lemmas for working with finite sets of atoms *)

(** We make some lemmas about finite sets of atoms available without
    qualification by using abbreviations. *)

Notation eq_if_Equal        := AtomSet.eq_if_Equal.
Notation notin_empty        := AtomSetNotin.notin_empty.
Notation notin_singleton    := AtomSetNotin.notin_singleton.
Notation notin_singleton_rw := AtomSetNotin.notin_singleton_rw.
Notation notin_union        := AtomSetNotin.notin_union.


(* ********************************************************************** *)
(** * Additional properties *)

(** One can generate an atom fresh for a given finite set of atoms. *)

Lemma atom_fresh_for_set : forall L : atoms, { x : atom | ~ In x L }.
Proof.
  intros L. destruct (atom_fresh_for_list (elements L)) as [a H].
  exists a. intros J. contradiction H.
  rewrite <- InA_iff_In. auto using elements_1.
Qed.


(* ********************************************************************** *)
(** * Additional tactics *)


(* ********************************************************************** *)
(** ** #<a name="pick_fresh"></a># Picking a fresh atom *)

(** We define three tactics which, when combined, provide a simple
    mechanism for picking a fresh atom.  We demonstrate their use
    below with an example, the [example_pick_fresh] tactic.

   [(gather_atoms_with F)] returns the union of [(F x)], where [x]
   ranges over all objects in the context such that [(F x)] is
   well typed.  The return type of [F] should be [atoms].  The
   complexity of this tactic is due to the fact that there is no
   support in [Ltac] for folding a function over the context. *)

Ltac gather_atoms_with F :=
  let rec gather V :=
    match goal with
    | H: ?S |- _ =>
      let FH := constr:(F H) in
      match V with
      | empty => gather FH
      | context [FH] => fail 1
      | _ => gather (union FH V)
      end
    | _ => V
    end in
  let L := gather empty in eval simpl in L.

(** [(beautify_fset V)] takes a set [V] built as a union of finite
    sets and returns the same set with empty sets removed and union
    operations associated to the right.  Duplicate sets are also
    removed from the union. *)

Ltac beautify_fset V :=
  let rec go Acc E :=
     match E with
     | union ?E1 ?E2 => let Acc1 := go Acc E2 in go Acc1 E1
     | empty => Acc
     | ?E1 => match Acc with
              | empty => E1
              | context [E1] => Acc
              | _ => constr:(union E1 Acc)
              end
     end
  in go empty V.

(** The tactic [(pick fresh Y for L)] takes a finite set of atoms [L]
    and a fresh name [Y], and adds to the context an atom with name
    [Y] and a proof that [(~ In Y L)], i.e., that [Y] is fresh for
    [L].  The tactic will fail if [Y] is already declared in the
    context. *)

Tactic Notation "pick" "fresh" ident(Y) "for" constr(L) :=
  let Fr := fresh "Fr" in
  let L := beautify_fset L in
  (destruct (atom_fresh_for_set L) as [Y Fr]).


(* ********************************************************************** *)
(** ** Demonstration *)

(** The [example_pick_fresh] tactic below illustrates the general
    pattern for using the above three tactics to define a tactic which
    picks a fresh atom.  The pattern is as follows:
      - Repeatedly invoke [gather_atoms_with], using functions with
        different argument types each time.
      - Union together the result of the calls, and invoke
        [(pick fresh ... for ...)] with that union of sets. *)

Ltac example_pick_fresh Y :=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  pick fresh Y for (union A B).

Lemma example_pick_fresh_use : forall (x y z : atom) (L1 L2 L3: atoms), True.
(* begin show *)
Proof.
  intros x y z L1 L2 L3. example_pick_fresh k.

  (** At this point in the proof, we have a new atom [k] and a
      hypothesis [Fr : ~ In k (union L1 (union L2 (union L3 (union
      (singleton x) (union (singleton y) (singleton z))))))]. *)

  trivial.
Qed.
(* end show *)
