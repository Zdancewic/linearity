(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)



(* Usual notions of neighborhood and degree for multigraphs. *)

(* The following notions are defined :                                  *)
(*      - mneighbor : relation between 2 vertices;                       *)
(*      - mneighborhood : list of neighbors of a vertex;                 *)
(*      - mdegree : number of neighbors of a vertex;                     *)
(*      - misolated : vertex without neighbor;                           *)
(*      - mpendant : vertex with only one neighbor.                      *)

Require Export Multigraphs.
Require Export GraphBasics.Degrees.

Section MULTIDEGREE.

Fixpoint mneighborhood (x : Vertex) (v : V_set) (a : A_set) 
 (g : Multigraph v a) {struct g} : V_list :=
  match g with
  | M_empty => V_nil
  | M_vertex v' a' g' x' _ => mneighborhood x v' a' g'
  | M_edge v' a' g' x' y' _ _ =>
      if V_eq_dec x x'
      then y' :: mneighborhood x v' a' g'
      else
       if V_eq_dec x y'
       then x' :: mneighborhood x v' a' g'
       else mneighborhood x v' a' g'
  | M_eq v' _ a' _ _ _ g' => mneighborhood x v' a' g'
  end.

Fixpoint mdegree (x : Vertex) (v : V_set) (a : A_set) 
 (g : Multigraph v a) {struct g} : nat :=
  match g with
  | M_empty => 0
  | M_vertex v' a' g' x' _ => mdegree x v' a' g'
  | M_edge v' a' g' x' y' _ _ =>
      if V_eq_dec x x'
      then S (mdegree x v' a' g')
      else
	if V_eq_dec x y'
	then S (mdegree x v' a' g')
	else mdegree x v' a' g'
  | M_eq v' _ a' _ _ _ g' => mdegree x v' a' g'
  end.

Lemma mdegree_mneighborhood :
 forall (x : Vertex) (v : V_set) (a : A_set) (g : Multigraph v a),
 mdegree x v a g = length (mneighborhood x v a g).
Proof.
        simple induction g; simpl in |- *; intros.
        trivial.

        trivial.

        case (V_eq_dec x x0); intros.
        rewrite H; auto.

        case (V_eq_dec x y); rewrite H; auto.

        trivial.
Qed.

End MULTIDEGREE.

Section REMULTIPLE_DEGREE.

Definition misolated (x : Vertex) (v : V_set) (a : A_set) 
  (g : Multigraph v a) := forall y : Vertex, ~ a (A_ends x y).

Lemma mdegree_misolated :
 forall (v : V_set) (a : A_set) (g : Multigraph v a) (x : Vertex),
 misolated x v a g -> mdegree x v a g = 0.
Proof.
        unfold misolated in |- *; simple induction g; simpl in |- *; intros.
        trivial.

        auto.

        case (V_eq_dec x0 x); intros.
        absurd (A_union (E_set x y) a0 (A_ends x0 y)).
        auto.

        rewrite e; apply A_in_left; apply E_right.

        case (V_eq_dec x0 y); intros.
        absurd (A_union (E_set x y) a0 (A_ends x0 x)).
        auto.

        rewrite e; apply A_in_left; apply E_left.

        apply (H x0); red in |- *; intros.
        elim (H0 y0); apply A_in_right; trivial.

        apply (H x); rewrite e0; trivial.
Qed.

Definition mpendant (x : Vertex) (v : V_set) (a : A_set) 
  (g : Multigraph v a) :=
  exists2 y : Vertex,
    a (A_ends x y) & (forall z : Vertex, a (A_ends x z) -> z = y).

(* Not sure how to fix this one... maybe it won't be needed? *)
(*Lemma mdegree_mpendant :
 forall (v : V_set) (a : A_set) (g : Multigraph v a) (x : Vertex),
 mpendant x v a g -> mdegree x v a g = 1.
Proof.
        unfold mpendant in |- *; simple induction g; simpl in |- *; intros.
        elim H; intros.
        inversion H0.

        auto.

        case (V_eq_dec x0 x); intros.
        rewrite (mdegree_misolated v0 a0 d x0).
        trivial.

        elim H0; rewrite e; intros.
        unfold misolated in |- *; red in |- *; intros.
        absurd (y0 = x1).
        red in |- *; intros.
        absurd (y = x1).
        red in |- *; intros; elim n0.
        rewrite H5; rewrite <- H4; trivial.

        apply H2; apply A_in_left; apply E_right.

        apply H2; apply A_in_right; trivial.

        case (V_eq_dec x0 y); intros.
        rewrite (mdegree_misolated v0 a0 d x0).
        trivial.

        elim H0; rewrite e; intros.
        unfold misolated in |- *; red in |- *; intros.
        absurd (y0 = x1).
        red in |- *; intros.
        absurd (x = x1).
        red in |- *; intros; elim n1.
        rewrite H5; rewrite <- H4; trivial.

        apply H2; apply A_in_left; apply E_left.

        apply H2; apply A_in_right; trivial.

        apply H; elim H0; intros.
        split with x1.
        apply (A_in_union_edge _ _ _ _ _ H1).
        apply E_not_set_eq123; auto.

        intros; apply H2; apply A_in_right; trivial.

        apply H; rewrite e0; trivial.
Qed.*)

Lemma mdegree_not_isolated :
 forall (v : V_set) (a : A_set) (g : Multigraph v a) (x : Vertex),
 (exists y : Vertex, a (A_ends x y)) -> mdegree x v a g > 0.
Proof.
        simple induction g; simpl in |- *; intros.
        elim H; intros.
        inversion H0.

        auto.

        case (V_eq_dec x0 x); intros.
        omega.

        case (V_eq_dec x0 y); intros.
        omega.

        apply H; elim H0; intros.
        split with x1.
        apply (A_in_union_edge _ _ _ _ _ H1).
        apply E_not_set_eq123; auto.

        apply H; rewrite e0; trivial.
Qed.

Lemma mdegree_not_mpendant :
 forall (v : V_set) (a : A_set) (g : Multigraph v a) (x : Vertex),
 (exists2 y : Vertex,
    a (A_ends x y) & (exists2 z : Vertex, a (A_ends x z) & y <> z)) ->
 mdegree x v a g > 1.
Proof.
        simple induction g; simpl in |- *; intros.
        elim H; intros.
        inversion H0.

        auto.

        case (V_eq_dec x0 x); intros.
        apply gt_n_S; apply mdegree_not_isolated.
        elim H0; rewrite e; intros.
        case (V_eq_dec x1 y); intros.
        elim H2; rewrite e0; intros.
        split with x2.
        apply (A_in_union_edge _ _ _ _ _ H3).
        apply E_not_set_eq24; auto.

        split with x1.
        apply (A_in_union_edge _ _ _ _ _ H1).
        apply E_not_set_eq24; auto.

        case (V_eq_dec x0 y); intros.
        apply gt_n_S; apply mdegree_not_isolated.
        elim H0; rewrite e; intros.
        case (V_eq_dec x x1); intros.
        elim H2; rewrite e0; intros.
        split with x2; apply (A_in_union_edge _ _ _ _ _ H3).
        apply E_not_set_eq14; trivial.

        split with x1; apply (A_in_union_edge _ _ _ _ _ H1).
        apply E_not_set_eq14; trivial.

        apply H; elim H0; intros.
        split with x1.
        apply (A_in_union_edge _ _ _ _ _ H1).
        apply E_not_set_eq123; auto.

        elim H2; intros.
        split with x2.
        apply (A_in_union_edge _ _ _ _ _ H3).
        apply E_not_set_eq123; auto.

        trivial.

        apply H; rewrite e0; trivial.
Qed.

End REMULTIPLE_DEGREE.