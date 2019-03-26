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



(* Based on the GraphBasics library, a Multigraph is like a Graph but allows *)
(* multiple edges between nodes, along with self-loops. *)

(* The following notion are defined :                                   *)
(*      - (Multigraph v a): dependant of a set of vertices and a set of arcs *)
(*              constructors : M_empty, M_vertex, M_edge, M_eq;         *)
(*      - MV_list : list of vertices in order of construction;          *)
(*      - ME_list : list of edge containing (xy) or (yx);               *)
(*      - M_order : number of vertices;                                 *)
(*      - M_size : number of edges.                                     *)

Require Export Metatheory.
Require Import Sets.Multiset.

Section VERTEX.

Definition Vertex := atom.
Definition V_set := atoms.

Definition V_empty : V_set := empty.
Definition V_single : Vertex -> V_set := singleton.
Definition V_union : V_set -> V_set -> V_set := union.
Definition V_add x v : V_set := (V_union (V_single x) v).
Definition V_eq : V_set -> V_set -> Prop := AtomSetImpl.Equal.

End VERTEX.

Section ARC.

Inductive Arc :=
  A_ends : Vertex -> Vertex -> Arc.

Lemma Arc_eq_dec : forall (x y : Arc),
  {x = y} + {x <> y}.
Proof with auto.
  intros. destruct x as [w x]. destruct y as [y z].
  destruct (w == y).
    destruct (x == z).
      left. f_equal...
      right. intuition. inversion H...
    right. intuition. inversion H...
Qed.

Definition A_set := multiset Arc.

Definition A_empty : A_set := EmptyBag Arc.
Definition A_union : A_set -> A_set -> A_set := @munion Arc.
Definition A_eq : A_set -> A_set -> Prop := @meq Arc.

End ARC.

Section EDGE.

Definition edge (x : Vertex) (y : Vertex) : A_set :=
  A_union (SingletonBag eq Arc_eq_dec (A_ends x y))
                (SingletonBag eq Arc_eq_dec (A_ends y x)).

Definition edge_add (x : Vertex) (y : Vertex) (a : A_set) : A_set :=
  A_union (edge x y) a.

Definition E_set (a : A_set) := forall x y,
  multiplicity a (A_ends x y) = multiplicity a (A_ends y x).

Lemma Edge : forall x y, E_set (edge x y).
Proof with auto.
  intros. unfold edge. red. intros. simpl.
  destruct (x == x0); destruct (x == y0);
      destruct (y == x0); destruct (y == y0); repeat subst...
  
    destruct (Arc_eq_dec (A_ends x0 x0) (A_ends x0 x0));
    destruct (Arc_eq_dec (A_ends x0 x0) (A_ends x0 y0));
    destruct (Arc_eq_dec (A_ends x0 x0) (A_ends y0 x0));
    destruct (Arc_eq_dec (A_ends x0 x0) (A_ends y0 y0));
    destruct (Arc_eq_dec (A_ends x0 y0) (A_ends x0 x0));
    destruct (Arc_eq_dec (A_ends x0 y0) (A_ends x0 y0));
    destruct (Arc_eq_dec (A_ends x0 y0) (A_ends y0 x0));
    destruct (Arc_eq_dec (A_ends x0 y0) (A_ends y0 y0));
    destruct (Arc_eq_dec (A_ends y0 x0) (A_ends x0 x0));
    destruct (Arc_eq_dec (A_ends y0 x0) (A_ends x0 y0));
    destruct (Arc_eq_dec (A_ends y0 x0) (A_ends y0 x0));
    destruct (Arc_eq_dec (A_ends y0 x0) (A_ends y0 y0));
    destruct (Arc_eq_dec (A_ends y0 y0) (A_ends x0 x0));
    destruct (Arc_eq_dec (A_ends y0 y0) (A_ends x0 y0));
    destruct (Arc_eq_dec (A_ends y0 y0) (A_ends y0 x0));
    destruct (Arc_eq_dec (A_ends y0 y0) (A_ends y0 y0)).

    destruct (Arc_eq_dec (A_ends x0 x0) (A_ends x0 y0));
      destruct (Arc_eq_dec (A_ends x0 x0) (A_ends y0 x0));
        try solve [auto | inversion e; intuition].
    destruct (Arc_eq_dec (A_ends x0 y0) (A_ends y0 x0));
      destruct (Arc_eq_dec (A_ends y0 x0) (A_ends x0 y0));
        try solve [auto | inversion e; intuition].
        destruct (Arc_eq_dec (A_ends x0 y0) (A_ends x0 y0));
          destruct (Arc_eq_dec (A_ends y0 x0) (A_ends y0 x0));
            try solve [auto | inversion e; intuition | inversion e0; intuition].
      
    

End EDGE.

Section MULTIGRAPH.

Inductive Multigraph : V_set -> E_set -> Set :=
  | M_empty : Multigraph V_empty E_empty
  | M_vertex :
      forall (v : V_set) (e : E_set) (d : Multigraph v e) (x : Vertex),
      x `notin` v -> Multigraph (V_union (V_single x) v) e
  | M_edge :
      forall (v : V_set) (e : E_set) (d : Multigraph v e) (x y : Vertex),
      x `in` v ->
      y `in` v ->
      Multigraph v (munion (E_single (E_ends x y)) e)
  | M_eq :
      forall (v v' : V_set) (e e' : E_set),
      v = v' -> e = e' -> Multigraph v e -> Multigraph v' e'
.

Fixpoint MV_list (v : V_set) (a : A_set) (g : Multigraph v a) {struct g} :
 V_list :=
  match g with
  | M_empty => V_nil
  | M_vertex v' a' g' x _ => x :: MV_list v' a' g'
  | M_edge v' a' g' x y _ _ => MV_list v' a' g'
  | M_eq v' _ a' _ _ _ g' => MV_list v' a' g'
  end.

(* Not quite correct - skipping for now. *)
(*Fixpoint MA_list (v : V_set) (a : A_set) (g : Multigraph v a) {struct g} :
 A_list :=
  match g with
  | M_empty => A_nil
  | M_vertex v' a' g' x _ => MA_list v' a' g'
  | M_edge v' a' g' x y _ _ =>
      A_ends x y :: A_ends y x :: MA_list v' a' g'
  | M_eq v' _ a' _ _ _ g' => MA_list v' a' g'
  end.*)

Fixpoint ME_list (v : V_set) (a : A_set) (g : Multigraph v a) {struct g} :
 E_list :=
  match g with
  | M_empty => E_nil
  | M_vertex v' a' g' x _ => ME_list v' a' g'
  | M_edge v' a' g' x y _ _ => E_ends x y :: ME_list v' a' g'
  | M_eq v' _ a' _ _ _ g' => ME_list v' a' g'
  end.

Definition M_order (v : V_set) (a : A_set) (g : Multigraph v a) :=
  length (MV_list v a g).

Definition M_size (v : V_set) (a : A_set) (g : Multigraph v a) :=
  length (ME_list v a g).

Lemma M_v_dec :
 forall (v : V_set) (a : A_set) (g : Multigraph v a) (x : Vertex), {v x} + {~ v x}.
Proof.
        intros v a g; elim g; intros.
        right; apply V_empty_nothing.

        case (H x0); intros.
        left; apply V_in_right; trivial.

        case (V_eq_dec x x0); intros.
        left; apply V_in_left; rewrite e; apply V_in_single.

        right; red in |- *; intros; inversion H0.
        elim n1; inversion H1; trivial.

        elim n0; trivial.

        auto.

        case (H x); intros.
        left; elim e; trivial.

        right; elim e; trivial.
Qed.

Lemma M_a_dec :
 forall (v : V_set) (a : A_set) (g : Multigraph v a) (x : Arc), {a x} + {~ a x}.
Proof with auto.
  intros v a g. induction g; intros...
    right. apply A_empty_nothing.
    destruct (IHg x0).
      left. apply A_in_right...
      destruct (A_eq_dec (A_ends x y) x0); subst.
        left. apply A_in_left. constructor.
        destruct (A_eq_dec (A_ends y x) x0); subst.
          left. apply A_in_left. constructor.
          right. red in |- *. intros. inversion H; subst...
            inversion H0; subst...
    destruct (IHg x); subst.
      left...
      right...
Qed.

Lemma M_non_directed :
 forall (v : V_set) (a : A_set) (g : Multigraph v a) (x y : Vertex),
 a (A_ends x y) -> a (A_ends y x).
Proof.
        intros v a g; elim g; intros.
        inversion H.

        auto.

        inversion H0.
        apply A_in_left.
        inversion H1.
        apply E_left.

        apply E_right.

        apply A_in_right; auto.

        generalize H0; elim e0; auto.
Qed.

Lemma M_ina_inv1 :
 forall (v : V_set) (a : A_set) (g : Multigraph v a) (x y : Vertex),
 a (A_ends x y) -> v x.
Proof.
        intros v a g; elim g; intros.
        inversion H.

        apply V_in_right; apply (H x0 y); trivial.

        inversion H0.
        inversion H1; rewrite <- H4; trivial.

        apply (H x0 y0); trivial.

        rewrite <- e; apply (H x y); rewrite e0; trivial.
Qed.

Lemma M_ina_inv2 :
 forall (v : V_set) (a : A_set) (g : Multigraph v a) (x y : Vertex),
 a (A_ends x y) -> v y.
Proof.
        intros v a g; elim g; intros.
        inversion H.

        apply V_in_right; apply (H x0 y); trivial.

        inversion H0.
        inversion H1; rewrite <- H5; trivial.

        apply (H x0 y0); trivial.

        rewrite <- e; apply (H x y); rewrite e0; trivial.
Qed.

End MULTIGRAPH.

Section GRAPH_TO_MULTIGRAPH.

Lemma graph_isa_multigraph :
 forall (v : V_set) (a : A_set) (d : Graph v a), Multigraph v a.
Proof.
  intros v a d. induction d; intros; try solve [constructor; auto].
    subst. auto.
Defined.

End GRAPH_TO_MULTIGRAPH.

Section UNION_MULTIGRAPHS.

Lemma M_union :
 forall (v1 v2 : V_set) (a1 a2 : A_set),
 Multigraph v1 a1 -> Multigraph v2 a2 ->
 Multigraph (V_union v1 v2) (A_union a1 a2).
Proof.
        intros; elim H; intros.
        apply M_eq with (v := v2) (a := a2).
        symmetry  in |- *; apply V_union_neutral.

        symmetry  in |- *; apply A_union_neutral.

        trivial.

        case (M_v_dec v2 a2 H0 x); intros.
        apply M_eq with (v := V_union v v2) (a := A_union a a2).
        rewrite V_union_assoc; rewrite (V_union_absorb (V_single x)); trivial.
        apply V_included_single; apply V_in_right; trivial.

        trivial.

        trivial.

        apply
         M_eq
          with (v := V_union (V_single x) (V_union v v2)) (a := A_union a a2).
        symmetry  in |- *; apply V_union_assoc.

        trivial.

        apply M_vertex.
        trivial.

        apply V_not_union; trivial.

        case (M_a_dec v2 a2 H0 (A_ends x y)); intros.
        apply M_eq with (v := V_union v v2) (a := A_union a a2).
        trivial.

        rewrite A_union_assoc; rewrite (A_union_absorb (E_set x y)); trivial.
        apply E_inclusion.
        apply A_in_right; trivial.

        apply A_in_right; apply (M_non_directed v2 a2 H0); auto.

        trivial.

        apply
         M_eq
          with (v := V_union v v2) (a := A_union (E_set x y) (A_union a a2)).
        trivial.

        symmetry  in |- *; apply A_union_assoc.

        apply M_edge.
        trivial.

        apply V_in_left; trivial.

        apply V_in_left; trivial.

        trivial.

        apply M_eq with (v := V_union v v2) (a := A_union a a2).
        elim e; trivial.

        elim e0; trivial.

        trivial.
Qed.

End UNION_MULTIGRAPHS.

Section INVERSION_MULTIGRAPH.

Lemma M_empty_empty :
 forall (v : V_set) (a : A_set), Multigraph v a -> v = V_empty -> a = A_empty.
Proof.
        intros v a g; elim g; intros.
        trivial.

        elim (V_empty_nothing x); fold V_empty in |- *; rewrite <- H0;
         apply V_in_left; apply V_in_single.

        elim (V_empty_nothing x); fold V_empty in |- *; rewrite <- H0;
         trivial.

        rewrite <- e0; apply H; rewrite e; trivial.
Qed.

Lemma M_minus_vertex :
 forall (v : V_set) (a : A_set) (g : Multigraph v a) (x : Vertex),
 v x ->
 (forall y : Vertex, ~ a (A_ends x y)) ->
 forall v' : V_set, ~ v' x -> v = V_union (V_single x) v' -> Multigraph v' a.
Proof.
intros v a g; elim g; intros.
elim (V_empty_nothing x); trivial.

case (V_union_single_dec x x0 v0 n H0); intros.
apply M_eq with (v := v0) (a := a0).
apply V_union_inversion with (E := V_single x).
apply V_single_disjoint; trivial.

apply V_single_disjoint; rewrite e; trivial.

pattern x at 2 in |- *; rewrite e; trivial.

trivial.

trivial.

generalize (H x0 v1 H1); intros.
apply M_eq with (v := V_union (V_single x) (V_inter v0 v')) (a := a0).
apply (V_union_single_inter x x0).
trivial.

red in |- *; intros Heq; elim n; rewrite Heq; trivial.

trivial.

trivial.

apply M_vertex.
apply H4.
unfold V_inter in |- *.
rewrite (V_inter_commut v0 v'); apply V_not_inter; trivial.

rewrite V_inter_commut; symmetry  in |- *; apply (V_union_single_inter x0 x).
trivial.

red in |- *; intros Heq; elim n; rewrite <- Heq; trivial.

auto.

apply V_not_inter; trivial.

apply M_edge.
apply (H x0).
trivial.

red in |- *; intros; elim (H1 y0).
apply A_in_right; trivial.

trivial.

trivial.

rewrite H3 in v1; inversion v1.
elim (H1 y); inversion H4; apply A_in_left; apply E_right.

trivial.

rewrite H3 in v2; inversion v2.
elim (H1 x); inversion H4; apply A_in_left; apply E_left.

trivial.

trivial.

trivial.

trivial.

apply M_eq with (v := v'0) (a := a0).
trivial.

trivial.

apply (H x).
rewrite e; rewrite H3; apply V_in_left; apply V_in_single.

rewrite e0; trivial.

trivial.

rewrite e; trivial.
Qed.

(* The graph version isn't used, and I can't think of the right version
    for multigraphs. *)
(*Lemma M_minus_edge :
 forall (v : V_set) (a : A_set) (g : Multigraph v a) (x y : Vertex),
 a (A_ends x y) ->
 forall a' : A_set,
 a = A_union (E_set x y) a' -> Multigraph v a'.
Proof with auto.
  intros v a g. induction g; intros; subst.
    unfold A_empty in *. tauto.
    apply M_vertex... eapply IHg; eauto.
      

    destruct (E_set_eq_dec x x0 y y0).
      apply M_eq with (v := v) (a := a)...
        apply (A_union_inversion (E_set x y) a a').
          apply E_set_disjoint...

intros v a g; elim g.
unfold A_empty in |- *. tauto.

intros; apply M_vertex; eauto 2.

intros; case (E_set_eq_dec x x0 y y0); intros.
apply M_eq with (v := v0) (a := a0).
trivial.

apply (A_union_inversion (E_set x y) a0 a').
apply E_set_disjoint; trivial.

rewrite e; apply E_set_disjoint; trivial.

rewrite <- e in H3; trivial.

trivial.

apply M_eq with (v := v0) (a := A_union (E_set x y) (A_inter a0 a')).
trivial.

apply A_union_single_inter with (x' := x0) (y' := y0); trivial.

apply M_edge.
apply (H x0 y0).
inversion H0.
absurd (E_set x y = E_set x0 y0).
trivial.

inversion H4.
trivial.

apply E_set_eq.

trivial.

red in |- *; intros Ha; inversion Ha; elim H1; trivial.

red in |- *; intros Ha; inversion Ha; elim H2; trivial.

rewrite A_inter_commut; symmetry  in |- *;
 apply A_union_single_inter with (x' := x) (y' := y).
trivial.

trivial.

auto.

auto.

trivial.

trivial.

trivial.

red in |- *; intros Ha; inversion Ha; elim n0; trivial.

red in |- *; intros Ha; inversion Ha; elim n1; trivial.

intros.
apply M_eq with (v := v0) (a := a'0).
trivial.

trivial.

apply (H x y).
rewrite e0; trivial.

trivial.

trivial.

rewrite e0; trivial.
Qed.*)

End INVERSION_MULTIGRAPH.
