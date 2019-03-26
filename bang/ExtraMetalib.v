(** Authors: Jianzhou Zhao. *)

Require Import Metatheory.

Lemma app_nil_inv : forall A (E E':list (atom*A)),
  nil = E ++ E' ->
  E = nil /\ E' = nil.
Proof.
  induction E; intros; auto.
    simpl_env in H. inversion H.
Qed.

(* ********************************************************************** *)
(** * Helper Lemma of Atomsetdec *)
Lemma atomsetdec_union1 : forall  (A B:atoms) X,
  A [=] B ->
  union (singleton X) A [=] union (singleton X) B.
Proof.
  intros A B X H.
  rewrite H.
  fsetdec.
Qed.

Lemma atomsetdec_union2 : forall  (A A' B B':atoms) X,
  A [=] B ->
  A' [=] B' ->
  union A (union (singleton X) A') [=] union B (union (singleton X) B').
Proof.
  intros A A' B B' X H1 H2.
  rewrite H1. rewrite H2.
  fsetdec.
Qed.

Lemma atomsetdec_union3 : forall  (A A' B B':atoms),
  A [=] B ->
  A' [=] B' ->
  union A A' [=] union B B'.
Proof.
  intros A A' B B' H1 H2.
  rewrite H1. rewrite H2.
  fsetdec.
Qed.

Lemma atomsetdec_empty : empty [=] empty.
Proof.
  fsetdec.
Qed.

Hint Resolve atomsetdec_union1 atomsetdec_union2 atomsetdec_union3 atomsetdec_empty.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../../../metatheory" "-I" "../Bang") ***
*** End: ***
 *)



