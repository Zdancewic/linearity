 (** Administrative lemmas for Algorithmic Lightweight Linear F

    Table of contents:
      - #<a href="##wft">Properties of wf_typ</a>#
      - #<a href="##oktwft">Properties of wf_env and wf_typ</a>#
      - #<a href="##okt">Properties of wf_env</a>#
      - #<a href="##subst">Properties of substitution</a>#
      - #<a href="##regularity">Regularity lemmas</a>#
      - #<a href="##auto">Automation</a># *)

Require Export ALinearF_Lemmas.
Require Import Omega.
Require Import Decidable.

Ltac SSCase name := Case_aux subsubcase name.
Ltac SSSCase name := Case_aux subsubsubcase name.
Ltac SSSSCase name := Case_aux subsubsubsubcase name.

(* ********************************************************************** *)
(** *  Properties of <<= *)

Lemma denv_sub_refl : forall D,
  D <<= D.
Admitted.

Lemma denv_sub_trans : forall D D' D'',
  D <<= D' -> D' <<= D'' -> D <<= D''.
Admitted.

Lemma wf_denv__sub : forall G D1 D2 D1' D2',
  wf_denv G (D1++D2) ->
  D1' <<= D1 ->
  D2' <<= D2 ->
  wf_denv G (D1'++D2').
Admitted.

Lemma sub_concat : forall D1 D2 D3,
  D1 <<= D2 ->
  D1 <<= (D2++D3).
Admitted.

(* ********************************************************************** *)
(** *  Properties of ~~ *)

Definition D'_eq_D := 
 fun (D' : denv) =>
  fun (D : denv) =>
   (forall x b, binds x b D <-> binds x b D') .  

Notation "D' ~~ D" := (D'_eq_D D' D) (at level 70, no associativity).

Lemma denv_eq_refl : forall D,
  D ~~ D.
Admitted.

Lemma denv_eq_symm : forall D D',
  D ~~ D' -> D' ~~ D.
Admitted.

Lemma denv_eq_trans : forall D D' D'',
  D ~~ D' -> D' ~~ D'' -> D ~~ D''.
Admitted.

Lemma denv_eq_empty_inv : forall D,
  dempty ~~ D -> D = dempty.
Admitted.

Lemma denv_eq_hd_inv : forall x b D D',
  ([(x, b)] ++ D) ~~ D' -> D ~~ (D' [-] x).
Admitted.


(* ********************************************************************** *)
(** *  Properties of --, [-] *)

Lemma minus_unchanged : forall D D',
  D' <<= D -> D' ++ (D -- D') ~~ D.
Admitted.

Lemma minus_refl : forall D,
  (D -- D) ~~ dempty.
Admitted.

Lemma minus_fresh : forall D x,
  x `notin` dom D ->
  (D [-] x) = D.
Admitted.

Lemma minus_dist : forall (D D':denv) x b,
  x `notin` dom D ->
  x `notin` dom D' ->
  ((D' ++ [(x, b)] ++ D) [-] x) = (D' ++ D).
Admitted.

Lemma minus_commut : forall D x y,
  ((D [-] x) [-] y) = ((D [-] y) [-] x).
Admitted.

Lemma minus_empty : forall x,
  dempty [-] x = dempty.
Admitted.

Lemma minus_inclusion : forall (D D':denv),
  (D -- D') <<= D.
Admitted.

Lemma minus_flip : forall (D D' D'':denv),
  (D <<= D') ->
  (D'' -- D') <<= (D'' -- D).
Admitted.

Lemma minus_stable : forall (D D' D'':denv),
  (D <<= D') ->
  (D -- D'') <<= (D' -- D'').
Admitted.

(* ********************************************************************** *)
(** *  Properties of || *)

Definition D'_disjoin_D := 
 fun (D' : atoms) =>
  fun (D : atoms) =>
   (forall x, 
       (x `in` D -> x `notin` D') /\
       (x `in` D' -> x `notin` D)
   ).  

Notation "D' ** D" := (D'_disjoin_D D' D) (at level 70, no associativity).

Lemma denv_disjoin_antirefl : forall D,
  (D ** D) -> False.
Admitted.

Lemma denv_disjoin_symm : forall D D',
  (D ** D') -> (D' ** D).
Admitted.

Lemma denv_disjoin_concat : forall (D1 D1' D2 D2':denv),
  (dom(D1) ** dom(D2)) ->
  D2' <<= D2 ->
  D1' <<= D1 ->
  (dom(D1') ** dom(D2')).
Admitted.

Lemma ok__disjoin : forall (D1 D2:denv),
  ok (D1++D2) -> dom(D1) ** dom(D2).
Admitted.

Lemma denv_notin_disjoin : forall (D:denv) x,
  x `notin` dom D ->
  (dom D) ** (singleton x).
Admitted.

Lemma denv_disjoin_weakening : forall D (D1 D2 D3:denv),
  (D ** dom (D1 ++ D3)) -> 
  (D ** dom D2) ->
  (D ** dom (D1 ++ D2 ++ D3)).
Admitted.

(* ********************************************************************** *)
(** *  Properties of union *)

Definition D'_union_D := 
 fun (D' : denv) =>
  fun (D : denv) =>
    D' ++ (D -- D')
    .

Notation "D' || D" := (D'_union_D D' D) (at level 70, no associativity).

Lemma denv_union_refl : forall D,
  (D || D) ~~ D.
Admitted.

Lemma denv_union_symm : forall D D',
  (D || D') ~~ (D' || D).
Admitted.

Lemma denv_union_assoc : forall D D' D'',
  (D || (D' || D'')) ~~ ((D || D') || D'').
Admitted.

Lemma denv_union_empty : forall D,
  (D || dempty) = D.
Admitted.

Lemma denv_union_inclusion : forall D D',
  D' <<= D -> (D || D') ~~ D.
Admitted.

Lemma denv_union_concat : forall D1 D2 D,
  ((D1 ++ D2) || D) ~~ ((D1 || D) || (D2 || D)).
Admitted.

Lemma denv_union_disjoin : forall D1 D2,
  dom(D1) ** dom(D2) -> (D1 ++ D2) ~~ (D1 || D2).
Admitted.

Lemma denv_union_disjoin_dist : forall (D1 D2 D3:denv),
  dom(D1) ** dom(D3) -> 
  dom(D2) ** dom(D3) -> 
  dom(D1 || D2) ** dom(D3).
Admitted.

Lemma denv_union_minus_dist : forall (D1 D2 D3:denv),
  dom(D2) ** dom(D3) -> 
  ((D1 -- D2) || D3) ~~ ((D1 -- D3) || D2).
Admitted.

Lemma denv_union_minus_dist2 : forall (D1 D2 D3:denv),
  ((D1 -- D2) || (D2 -- D3)) ~~ (D1 -- D3).
Admitted.

(* ********************************************************************** *)
(** *  ~~ preserves properties *)

Lemma eq_preserves_eq : forall D1 D2 D2' D3 D,
  D1 ++ D2 ++ D3 ~~ D ->
  D2 ~~ D2' ->
  D1 ++ D2' ++ D3 ~~ D.
Admitted.

Lemma eq_preserves_wf_denv : forall G D D',
  wf_denv G D ->
  D ~~ D' ->
  wf_denv G D'.
Proof.
  intros G D D' Hwfdenv Heq.
  generalize dependent D'.
  induction Hwfdenv; intros D' Heq.
     apply denv_eq_empty_inv in Heq; subst; auto.
     apply denv_eq_hd_inv in Heq.
         apply IHHwfdenv in Heq.
Admitted.

Lemma eq_preserves_atyping : forall G D1 D1' e T D2 D2',
  atyping G D1 e T D2 ->
  D1 ~~ D1' ->
  D2 ~~ D2' ->
  atyping G D1' e T D2'.
Proof.
Admitted.

(* ********************************************************************** *)
(** *  decidable *)

Lemma in_dec : forall x d, {x `in` d} + {x `notin` d}.
Admitted.
  
(* ********************************************************************** *)
(** *  strengthening and weakening *)

Lemma wf_genv__ok : forall G,
  wf_genv G ->
  ok G.
Admitted.

Lemma wf_denv__ok : forall G D,
  wf_denv G D ->
  wf_genv G /\ ok D.
Admitted.

Lemma wf_denv_lin_strengthening3 : forall G D1 D2 D2' D3,
  wf_denv G (D1 ++ D2 ++ D3) ->
  D2' <<= D2 ->
  wf_denv G (D1 ++ D2' ++ D3).
Admitted.

Lemma atyping_lin_strengthening2 : forall G D e T D' D'',
  atyping G D e T D' ->
  (fv_ee(e)) ** (dom D'') ->
  atyping G (D -- D'') e T (D' -- D'').
Admitted.

Lemma atyping_lin_strengthening3 : forall G D e T D',
  atyping G D e T D' ->
  atyping G (D -- D') e T dempty.
Admitted.

Lemma atyping_lin_weakening2: forall G D2 D1 e T D,
  atyping G D1 e T D2 ->
  wf_denv G (D || D1) ->
  atyping G (D || D1) e T (D || D2).
Admitted.

Lemma denv_mono_aux2 : forall G D1 e T D2 x b, 
  atyping G D1 e T D2 ->
  binds x b D1 ->
  (x `in` fv_ee e /\ x `notin` dom D2) \/
  (x `notin` fv_ee e /\ binds x b D2).
Proof with simpl_env; eauto.
Admitted.

Corollary denv_mono_app2 : forall G D1 e1 e2 T D2 x b,
  atyping G D1 (exp_app e1 e2) T D2  ->
  binds x b D1 ->
  (x `in` fv_ee e1 /\ x `notin` fv_ee e2 /\ x `notin` dom D2) \/
  (x `notin` fv_ee e1 /\ x `in` fv_ee e2 /\ x `notin` dom D2) \/
  (x `notin` fv_ee e1 /\ x `notin` fv_ee e2 /\ binds x b D2).
Proof with simpl_env; eauto.
Admitted.

