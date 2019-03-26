(** A library of additional tactics. *)

Require Export String.
Open Scope string_scope.


(* *********************************************************************** *)
(** * Extensions of the standard library *)

(** "[remember c as x in |-]" replaces the term [c] by the identifier
    [x] in the conclusion of the current goal and introduces the
    hypothesis [x=c] into the context.  This tactic differs from a
    similar one in the standard library in that the replacmement is
    made only in the conclusion of the goal; the context is left
    unchanged. *)

Tactic Notation "remember" constr(c) "as" ident(x) "in" "|-" :=
  let x := fresh x in
  let H := fresh "Heq" x in
  (set (x := c); assert (H : x = c) by reflexivity; clearbody x).

(** "[unsimpl E]" replaces all occurence of [X] by [E], where [X] is
    the result that tactic [simpl] would give when used to evaluate
    [E]. *)

Tactic Notation "unsimpl" constr(E) :=
  let F := (eval simpl in E) in change F with E.

(** The following tactic calls the [apply] tactic with the first
    hypothesis that succeeds, "first" meaning the hypothesis that
    comes earlist in the context (i.e., higher up in the list). *)

Ltac apply_first_hyp :=
  match reverse goal with
    | H : _ |- _ => apply H
  end.


(* *********************************************************************** *)
(** * Variations on [auto] *)

(** The [auto*] and [eauto*] tactics are intended to be "stronger"
    versions of the [auto] and [eauto] tactics.  Similar to [auto] and
    [eauto], they each take an optional "depth" argument.  Note that
    if we declare these tactics using a single string, e.g., "auto*",
    then the resulting tactics are unusable since they fail to
    parse. *)

Tactic Notation "auto" "*" :=
  try solve [ congruence | auto | intuition auto ].

Tactic Notation "auto" "*" integer(n) :=
  try solve [ congruence | auto n | intuition (auto n) ].

Tactic Notation "eauto" "*" :=
  try solve [ congruence | eauto | intuition eauto ].

Tactic Notation "eauto" "*" integer(n) :=
  try solve [ congruence | eauto n | intuition (eauto n) ].


(* *********************************************************************** *)
(** * Delineating cases in proofs *)

(** This section was taken from the POPLmark Wiki
    ( http://alliance.seas.upenn.edu/~plclub/cgi-bin/poplmark/ ). *)

(** ** Tactic definitions *)

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name
  | fail 1 "because we are working on a different case." ].

Ltac Case name := Case_aux case name.
Ltac SCase name := Case_aux subcase name.
Ltac SSCase name := Case_aux subsubcase name.

(** ** Example

    One mode of use for the above tactics is to wrap Coq's [induction]
    tactic such that automatically inserts "case" markers into each
    branch of the proof.  For example:

<<
 Tactic Notation "induction" "nat" ident(n) :=
   induction n; [ Case "O" | Case "S" ].
 Tactic Notation "sub" "induction" "nat" ident(n) :=
   induction n; [ SCase "O" | SCase "S" ].
 Tactic Notation "sub" "sub" "induction" "nat" ident(n) :=
   induction n; [ SSCase "O" | SSCase "S" ].
>>

    If you use such customized versions of the induction tactics, then
    the [Case] tactic will verify that you are working on the case
    that you think you are.  You may also use the [Case] tactic with
    the standard version of [induction], in which case no verification
    is done. *)
