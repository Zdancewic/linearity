 (** Dmap lemmas for Algorithmic Lightweight Linear F *)
 
Require Export LinF_Definitions.
Require Import Metatheory.
Require Import FMaps FMapWeakList.
Set Implicit Arguments.

Module EMap := FMapWeakList.Make(AtomDT).
Module EMapP := FMapFacts.Properties EMap.
Export EMapP.
Export F. (* a sub-module of EMapP,
             containing more elementary properties *)

(** definition of eq to define a map
    and corresponding dec lemmas *)

Definition beq_kn (k1 k2 : kn) : bool :=
  match (k1, k2) with
  | (kn_lin, kn_lin) => true
  | (kn_nonlin, kn_nonlin) => true
  | _ => false
  end.


Definition beq_atom (x1 x2 : atom) : bool :=
  if (x1 == x2) then true else false.

Fixpoint beq_typ (t1 t2 : typ) {struct t1} : bool :=
  match (t1, t2) with
  | (typ_bvar i1, typ_bvar i2) => beq_nat i1 i2
  | (typ_fvar x1, typ_fvar x2) => beq_atom x1 x2
  | (typ_arrow k1 t11 t12, typ_arrow k2 t21 t22) => 
      (beq_kn k1 k2) && (beq_typ t11 t21) && (beq_typ t12 t22)
  | (typ_all k1 t1', typ_all k2 t2') => 
      (beq_kn k1 k2) && (beq_typ t1' t2')
  | (typ_with t11 t12, typ_with t21 t22) => 
      (beq_typ t11 t21) && (beq_typ t12 t22)
  | (_, _) => false
  end.

Lemma beq_nat_iff_eq : forall n n', 
  beq_nat n n' = true <-> n = n'.
Proof.
  induction n; destruct n';
    try solve [split; auto |
               split; intro H; try solve [simpl in H; inversion H]
              ].
    split; intro H; simpl in H.
      apply IHn in H. auto.
      inversion H. apply IHn in H1. apply sym_eq. apply beq_nat_refl.
Qed.

Lemma beq_atom_iff_eq : forall x x', 
  beq_atom x x' = true <-> x = x'.
Proof.
  intros x x'.
  unfold beq_atom.
  destruct (x == x').
    split; intro H; auto.
    split; intro H; auto.
      inversion H.
Qed.

Lemma beq_kn_iff_eq : forall k k', 
  beq_kn k k' = true <-> k = k'.
Proof.
  intros k k'.
  unfold beq_kn; destruct k; destruct k'; simpl.
    split; auto.
    split; intro H; inversion H.
    split; intro H; inversion H.
    split; auto.
Qed.

Lemma beq_typ_iff_eq : forall t t', 
  beq_typ t t' = true <-> t = t'.
Proof.
  induction t; destruct t'; 
    try solve [split; auto |
               split; intro H; try solve [simpl in H; inversion H]
              ].
    split; intro H; simpl in *.
      apply beq_nat_iff_eq in H; auto.
      eapply beq_nat_iff_eq; eauto.
        injection H. auto.

    split; intro H; simpl in *.
      apply beq_atom_iff_eq in H. rewrite H. auto.
      eapply beq_atom_iff_eq; eauto.
        injection H. auto.

    split; intro H; simpl in H.
      apply andb_true_iff in H.
      destruct H as [H H2].
      apply andb_true_iff in H.
      destruct H as [H0 H1].
      apply beq_kn_iff_eq in H0.
      apply IHt1 in H1.
      apply IHt2 in H2.
      subst. auto.

      inversion H; subst.
      simpl.
      assert (t'1 = t'1) as Eq1. auto.
      apply IHt1 in Eq1.
      assert (t'2 = t'2) as Eq2. auto.
      apply IHt2 in Eq2.
      assert (k0 = k0) as Eq0. auto.
      apply beq_kn_iff_eq in Eq0.      
      eapply andb_true_iff.
      split; auto.
        eapply andb_true_iff; eauto.

    split; intro H; simpl in H.
      apply andb_true_iff in H.
      destruct H as [H0 H1].
      apply beq_kn_iff_eq in H0.
      apply IHt in H1.
      subst. auto.

      inversion H; subst.
      simpl.
      assert (t' = t') as Eq1. auto.
      apply IHt in Eq1.
      assert (k0 = k0) as Eq0. auto.
      apply beq_kn_iff_eq in Eq0.      
      eapply andb_true_iff; auto.

    split; intro H; simpl in H.
      apply andb_true_iff in H.
      destruct H as [H1 H2].
      apply IHt1 in H1.
      apply IHt2 in H2.
      subst. auto.

      inversion H; subst.
      simpl.
      assert (t'1 = t'1) as Eq1. auto.
      apply IHt1 in Eq1.
      assert (t'2 = t'2) as Eq2. auto.
      apply IHt2 in Eq2.
      eapply andb_true_iff.
      split; auto.
Qed.    

Lemma beq_nat_dec : forall n n',
 { beq_nat n n' = true } + { ~ beq_nat n n' = true }.
Proof.
  induction n; destruct n'; simpl; auto.
Qed.    
  
Lemma beq_atom_dec : forall x x',
 { beq_atom x x' = true } + { ~ beq_atom x x' = true }.
Proof.
  intros x x'.
  unfold beq_atom.
  destruct (x == x'); auto.
Qed.    

Lemma beq_kn_dec : forall k k',
 { beq_kn k k' = true } + { ~ beq_kn k k' = true }.
Proof.
  unfold beq_kn.
  destruct k; destruct k'; simpl; auto.
Qed.    

Lemma beq_typ_dec : forall t t',
 { beq_typ t t' = true } + { ~ beq_typ t t' = true }.
Proof.
  induction t; destruct t'; simpl; auto.
  apply beq_nat_dec.
  apply beq_atom_dec.
  destruct (@IHt1 t'1) as [tIHt1 | fIHt1]; auto.
   destruct (@IHt2 t'2) as [tIHt2 | fIHt2]; auto.
     destruct (@beq_kn_dec k k0) as [tIHk | fIHk]; auto.
       left. eapply andb_true_iff. 
               split; auto.
                  eapply andb_true_iff; auto.
       right. unfold not. intro H.
         apply andb_true_iff in H.
         destruct H as [H H3].
         apply andb_true_iff in H.
         destruct H as [H1 H2].
         auto.
     right. unfold not. intro H.
       apply andb_true_iff in H.
       destruct H as [H H3].
       auto.
   right. unfold not. intro H.
     apply andb_true_iff in H.
     destruct H as [H H3].
     apply andb_true_iff in H.
     destruct H as [H1 H2].
     auto.
  destruct (@IHt t') as [tIHt | fIHt]; auto.
    destruct (@beq_kn_dec k k0) as [tIHk | fIHk]; auto.
       left. eapply andb_true_iff. 
               split; auto.
       right. unfold not. intro H.
         apply andb_true_iff in H.
         destruct H as [H1 H2].
         auto.
    right. unfold not. intro H.
      apply andb_true_iff in H.
      destruct H as [H1 H2].
      auto.
  destruct (@IHt1 t'1) as [tIHt1 | fIHt1]; auto.
   destruct (@IHt2 t'2) as [tIHt2 | fIHt2]; auto.
     left. eapply andb_true_iff. 
            split; auto.
     right. unfold not. intro H.
       apply andb_true_iff in H.
       destruct H as [H H3].
       auto.
   right. unfold not. intro H.
     apply andb_true_iff in H.
     destruct H as [H1 H2].
     auto.
Qed.

Lemma EMapsTo_dec : forall k (t:typ) M, 
 { EMap.MapsTo k t M } + { ~ EMap.MapsTo k t M }.
Proof.
  intros k t M.
  unfold EMap.MapsTo.
  unfold EMap.Raw.PX.MapsTo.
  apply InA_dec.
  unfold EMap.Raw.PX.eqke.
  intros x y.
  destruct (@eq_dec (fst x) (fst y)) as [tHfst | fHfst]; auto.
    destruct (@beq_typ_dec (snd x) (snd y)) as [tHsnd | fHsnd]; auto.
      apply beq_typ_iff_eq in tHsnd.
      left. auto.

      right. unfold not. intros H.
      destruct H as [tH fH].
      apply beq_typ_iff_eq in fH.
      auto.

    right. unfold not. intros H.
    destruct H as [tH fH].
    apply beq_typ_iff_eq in fH.
    auto.
Qed.

Notation dmap := (EMap.t typ).

Definition EMap_Submap m m' :=
  (forall k, EMap.In k m -> EMap.In k m') /\
  (forall k t t', EMap.MapsTo k t m -> EMap.MapsTo k t' m' -> beq_typ t t' = true).

Definition mdom (m : dmap) := EMap.fold (fun k t r => add k r ) m empty.
Definition mbinds x t (m :dmap) := EMap.find x m = Some t.

Notation "M ~~ M'" := (EMap.Equal M M') (at level 70, right associativity).
Notation "M [-] x" := (EMap.remove x M) (at level 70, no associativity).
Notation "M -- M'" := (diff M M') (at level 70, no associativity).
Notation "M' <<= M" := (EMap_Submap M' M) (at level 70, no associativity).
Notation "M ** M'" := (Disjoint M M') (at level 70, no associativity).
Notation "M |_| M'" := (update M M') (at level 70, right associativity).
Notation "M |^| M'" := (restrict M M') (at level 70, no associativity).
Notation "@@" := (EMap.empty typ).
Notation "x ::: t [+] M" := (EMap.add x t M) (at level 70, no associativity).

(* in mapsto *)
Lemma in_mapsto_iff : forall (m : dmap) x, 
  (exists e, EMap.MapsTo x e m) <-> EMap.In x m.
Proof.
  intros m x.
  split; intro J.
    destruct J as [e J].
    apply find_mapsto_iff in J.
    eapply in_find_iff.
    rewrite J. intro H. inversion H.

    apply in_find_iff in J.
    remember (EMap.find (elt:=typ) x m) as R.
    destruct R; apply sym_eq in HeqR.
      apply find_mapsto_iff in HeqR.
      exists t. auto.

      contradict J; auto.
Qed.

(* remove *)
Lemma dmap_remove_preserves_Equal : forall (M M':dmap) x,
  M ~~ M' -> (M [-] x) ~~ (M' [-] x).
Proof.
  intros M M' x H.
  unfold EMap.Equal.
  intro y.
  destruct (eq_atom_dec x y) as [H1 | H1].
   assert (H2 := H1).
   apply EMap.remove_1 with (elt:=typ) (m:=M) in H1.
   apply not_find_in_iff in H1.
   apply EMap.remove_1 with (elt:=typ) (m:=M') in H2.
   apply not_find_in_iff in H2.
   rewrite H1. rewrite H2. auto.

   remember (EMap.find (elt:=typ) y (EMap.remove (elt:=typ) x M)) as R.
   remember (EMap.find (elt:=typ) y (EMap.remove (elt:=typ) x M')) as R'.
   apply sym_eq in HeqR. 
   apply sym_eq in HeqR'. 
   destruct R.
     destruct R'.
       apply find_mapsto_iff in HeqR; auto.
       apply find_mapsto_iff in HeqR'; auto.
       apply EMap.remove_3 in HeqR; auto.
       apply EMap.remove_3 in HeqR'; auto.
       unfold EMap.Equal in H.
       apply find_mapsto_iff in HeqR.
       apply find_mapsto_iff in HeqR'.
       rewrite (@H y) in HeqR.
       rewrite HeqR in HeqR'. 
       auto.

       apply find_mapsto_iff in HeqR.
       unfold EMap.Equal in H.
       apply EMap.remove_3 in HeqR; auto.
       apply find_mapsto_iff in HeqR.
       rewrite (@H y) in HeqR.
       apply find_mapsto_iff in HeqR.
       apply EMap.remove_2 with (elt:=typ) (m:=M') (x:=x) in HeqR; auto.
       apply find_mapsto_iff in HeqR.
       rewrite HeqR in HeqR'. auto.

     destruct R'; auto.
       apply find_mapsto_iff in HeqR'.
       unfold EMap.Equal in H.
       apply EMap.remove_3 in HeqR'; auto.
       apply find_mapsto_iff in HeqR'.
       rewrite <- (@H y) in HeqR'.
       apply find_mapsto_iff in HeqR'.
       apply EMap.remove_2 with (elt:=typ) (m:=M) (x:=x) in HeqR'; auto.
       apply find_mapsto_iff in HeqR'.
       rewrite HeqR in HeqR'. auto.
Qed.

Lemma dmap_remove_clear : forall x (M : dmap),
  ~ EMap.In x (M [-] x).
Proof.
  unfold not.
  intros x M H.
  apply remove_in_iff in H.
  destruct H as [H1 H2]; auto.
Qed.

Lemma dmap_remove_mono : forall (M: dmap) x,
  (M [-] x) <<= M.
Proof.
  intros M x.
  unfold EMap_Submap.
  split.
    intros k H.
    apply remove_in_iff in H.
    destruct H; auto.
     
    intros k t1 t2 H1 H2.
    apply remove_mapsto_iff in H1.
    destruct H1 as [H11 H12].
    apply MapsTo_fun with (e':=t2) in H12; auto.
    apply beq_typ_iff_eq in H12; auto.
Qed.

Lemma dmap_sub_remove_free : forall M M' x,
  ~ EMap.In x M ->
  M <<= M' ->
  M <<= (M' [-] x).
Proof.
  unfold EMap_Submap.
  intros M M' x Hnotin Hsub.
  destruct Hsub as [Hsub1 Hsub2].
  split.
    intros k H.
    eapply remove_in_iff.
    split; auto. 
      destruct (x==k); subst; auto.
     
    intros k t1 t2 H1 H2.
    apply remove_mapsto_iff in H2.
    destruct H2 as [H21 H22].
    apply Hsub2 with (k:=k); auto.
Qed.

Lemma dmap_remove_preserves_disjoint : forall (M M':dmap) x,
  M ** M' ->
  (M[-]x) ** (M'[-]x).
Proof.
  intros M M' x Hdisj.
  unfold Disjoint in *.
  intro k.
  unfold not. intro J.
  destruct J as [J1 J2].
  apply (@Hdisj k).
  split.
    apply remove_in_iff in J1.
    destruct J1; auto.

    apply remove_in_iff in J2.
    destruct J2; auto.
Qed.


Lemma dmap_remove_refl : forall x (M :dmap),
  ~ EMap.In x M ->
  M ~~ (M [-] x).
Proof.
  intros x M Hnotin y.
  remember (EMap.find (elt:=typ) y M) as R.
  destruct R; apply sym_eq in HeqR; apply sym_eq.
    apply find_mapsto_iff in HeqR.
    eapply find_mapsto_iff.
    eapply remove_mapsto_iff.
    destruct (x==y); subst; auto.
      assert (False) as H.
        apply Hnotin.
        destruct(@in_mapsto_iff M y) as [H1 H2].
        apply H1.
        exists t. auto.
      inversion H.

    apply not_find_in_iff in HeqR.
    eapply not_find_in_iff.
    unfold not. intro J. apply HeqR. clear HeqR. 
    apply remove_in_iff in J.
    destruct J; auto.
Qed.

Lemma dmap_empty_remove_refl : forall x,
  (@@[-]x) ~~ @@.
Proof.
  intros x y.
  remember (EMap.find (elt:=typ) y @@) as R.
  destruct R; apply sym_eq in HeqR. 
    apply find_mapsto_iff in HeqR.
    apply empty_mapsto_iff in HeqR.
    inversion HeqR.

    apply not_find_in_iff in HeqR.
    eapply not_find_in_iff.
    unfold not. intro J.
    apply remove_in_iff in J.
    destruct J as [J1 J2].
    apply empty_in_iff in J2.
    auto.
Qed.   

Lemma dmap_sub_remove_left : forall M M' x,
  M <<= M' ->
  (M [-] x) <<= M'.
Proof.
  unfold EMap_Submap.
  intros M M' x Hsub.
  destruct Hsub as [Hsub1 Hsub2].
  split.
    intros k H.
    apply remove_in_iff in H.
    destruct H; auto.
     
    intros k t1 t2 H1 H2.
    apply remove_mapsto_iff in H1.
    destruct H1 as [H11 H12].
    apply Hsub2 with (k:=k); auto.
Qed.

Lemma dmap_Equal_rewrite_remove_left : forall (M M1 M1':dmap) x,
  M1 ~~ M1' -> M ~~ (M1 [-] x) -> M ~~ (M1' [-] x).
Proof.
  intros M M1 M1' x Heq Heq' y.
  rewrite Heq'. clear Heq'.
  remember (EMap.find (elt:=typ) y (M1 [-] x)) as R.
  destruct R; apply sym_eq; apply sym_eq in HeqR.
    apply find_mapsto_iff in HeqR.
    eapply find_mapsto_iff.
    eapply remove_mapsto_iff.
    apply remove_mapsto_iff in HeqR.
    destruct HeqR as [H1 H2].
      split; auto.
        eapply find_mapsto_iff.
        rewrite <- Heq.
        apply find_mapsto_iff in H2. auto.
 
    apply not_find_in_iff in HeqR.
    eapply not_find_in_iff. 
    unfold not. intro J. apply HeqR. clear HeqR.
    eapply remove_in_iff.
    apply remove_in_iff in J. 
    destruct J as [J1 J2].
      split; auto.
        eapply in_find_iff.
        rewrite Heq.
        apply in_find_iff in J2. auto.
Qed.


Lemma dmap_remove_remove_commut : forall (M:dmap) x y,
  ((M [-] x ) [-] y) ~~ ((M [-] y) [-] x).
Proof.
  intros M x y z.
  remember (EMap.find (elt:=typ) z ((M[-]y)[-]x)) as R.
  apply sym_eq in HeqR.
  destruct R.
    eapply find_mapsto_iff.
    eapply remove_mapsto_iff.
    apply find_mapsto_iff in HeqR.
    apply remove_mapsto_iff in HeqR.
    destruct HeqR as [H1 H2].
    apply remove_mapsto_iff in H2.
    destruct H2 as [H21 H22].
    split; auto.
      eapply remove_mapsto_iff.
      split; auto.
  
    eapply not_find_in_iff.
    apply not_find_in_iff in HeqR.
    intro J. apply HeqR. clear HeqR.
    eapply remove_in_iff.
    apply remove_in_iff in J.
    destruct J as [H1 H2].
    apply remove_in_iff in H2.
    destruct H2 as [H21 H22].
    split; auto.
      eapply remove_in_iff.
      split; auto.
Qed.

Lemma dmap_remove_in_noteq : forall (M:dmap) x y,  
  EMap.In y (M[-]x) ->
  x <> y ->  
  EMap.In y M.
Proof.
  intros M x y Hin Hnot.  
  apply remove_in_iff in Hin.
  destruct Hin; auto.
Qed.

(* Empty *)
Lemma dmap_Empty_inv : forall (M M' : dmap),
  M ~~ M' -> EMap.Empty M -> EMap.Empty M'.
Proof.
  intros M M' G G'.
  unfold EMap.Empty in *.  
  unfold EMap.Equal in *.
  unfold EMap.Raw.Empty in *.  
  intro x.
  unfold not.
  intros t J.
  apply (@G' x t).
  apply find_mapsto_iff in J.
  rewrite <- G in J.
  eapply find_mapsto_iff; eauto.
Qed.

Lemma dmap_eq_empty_inv : forall M,
  @@ ~~ M -> EMap.Empty M.
Proof.
  intros M.
  destruct M.
  unfold EMap.Empty in *.  
  unfold EMap.Raw.Empty in *.  
  destruct this.
    unfold EMap.Equal.
    intros H a e.
    unfold not.
    intros J.
    apply find_mapsto_iff in J.
    rewrite <- H in J.
    rewrite empty_o in J.
    inversion J.

    unfold EMap.Equal.
    simpl in *.
    intros H a e.
    unfold not.
    intros J.
    assert (K1 := @H a).
    assert (K2 := @empty_o typ a).
    rewrite K2 in K1.
    apply sym_eq in K1. 
    apply not_find_in_iff in K1.
    apply K1.
    exists e. simpl. auto.
Qed.

(* Sub *)
Lemma dmap_Sub_refl : forall M, M <<= M.
Proof.
  intros M.
  unfold EMap_Submap.
  split; auto.
    intros k t t' H1 H2.
    assert (J := @MapsTo_fun typ M k t t' H1 H2).
    destruct (@beq_typ_iff_eq t t'); auto.
Qed.   

Lemma dmap_Sub_trans : forall M M' M'', 
  M <<= M' -> M' <<= M'' -> M <<= M''.
Proof.
  intros M M' M''.
  unfold EMap_Submap.
  intros (H11, H12) (H21, H22).
  split; auto.
    intros k t t'' H1 H3.
    assert (J:=H1).
    apply -> elements_mapsto_iff in J.
    assert (exists e, InA (@EMap.eq_key_elt typ) (k,e) (EMap.elements (elt:=typ) M)) as H2.
      exists t. auto.
    apply elements_in_iff in H2.
    apply H11 in H2.
    apply -> elements_in_iff in H2.
    destruct H2 as [t' H2].
    apply elements_mapsto_iff in H2.
    apply H12 with (t':=t') in H1; auto.
    apply H22 with (t':=t'') in H2; auto.
         
    apply beq_typ_iff_eq in H1.
    apply beq_typ_iff_eq in H2.
    subst. apply <- beq_typ_iff_eq; auto.
Qed.   

Lemma dmap_Equal_rewrite_Sub_left : forall M1 M1' M2,
  M1 ~~ M1' -> M1 <<= M2 -> M1' <<= M2.
Proof.
  unfold EMap_Submap.
  unfold EMap.Equal.
  intros M1 M1' M2 Heq Hsub.
  destruct Hsub as [Hsub1 Hsub2].
  split.
    intros k H.
    apply in_find_iff in H.
    rewrite <- Heq in H.
    eapply in_find_iff.  
    apply in_find_iff in H.
    apply Hsub1 in H. 
    apply in_find_iff in H; auto.


    intros k t t' H1 H2.
    apply find_mapsto_iff in H1.
    apply find_mapsto_iff in H2.
    rewrite <- Heq in H1.
    eapply Hsub2 with (k:=k); 
      eapply find_mapsto_iff; auto.
Qed.

Lemma dmap_Equal_rewrite_Sub_right : forall M1 M2 M2',
  M2 ~~ M2' -> M1 <<= M2 -> M1 <<= M2'.
Proof.
  unfold EMap_Submap.
  unfold EMap.Equal.
  intros M1 M2 M2' Heq Hsub.
  destruct Hsub as [Hsub1 Hsub2].
  split.
    intros k H.
    apply in_find_iff in H.
    eapply in_find_iff.  
    apply in_find_iff in H.
    rewrite <- Heq.
    apply Hsub1 in H. 
    apply in_find_iff in H; auto.


    intros k t t' H1 H2.
    apply find_mapsto_iff in H1.
    apply find_mapsto_iff in H2.
    eapply Hsub2 with (k:=k); 
      eapply find_mapsto_iff; auto.
    rewrite Heq. auto.    
Qed.


Lemma Sub_Empty_Empty : forall M,
  M <<= @@ ->
  M ~~ @@.
Proof.
  unfold EMap_Submap.
  unfold EMap.Equal.
  intros M Hsub y.
    destruct Hsub as [Hsub1 Hsub2].
    remember (EMap.find (elt:=typ) y M) as R.
    destruct R; apply sym_eq; apply sym_eq in HeqR.
      assert (EMap.find (elt:=typ) y M <> None) as J.
        rewrite HeqR. unfold not. intro J. inversion J.
      apply in_find_iff in J.
      apply Hsub1 in J.
      apply empty_in_iff in J.
      inversion J.

      apply not_find_in_iff in HeqR.
      eapply not_find_in_iff.
      unfold not.
      intro J.
      apply HeqR. clear HeqR.
      apply empty_in_iff in J.
      inversion J.
Qed.

Lemma dmap_Sub_diff_right : forall M1 M2 M,
  M1 <<= M2 ->
  (M -- M2) <<= (M -- M1).
Proof.
  intros M1 M2 M Hsub.
  unfold EMap_Submap.
  unfold EMap_Submap in Hsub.
  destruct Hsub as [Hsub1 Hsub2].
  split.
    intros k H.
    apply diff_in_iff in H.
    eapply diff_in_iff.
    destruct H as [H1 H2]; auto.

    intros k t t' H1 H2.
    apply diff_mapsto_iff in H1.
    apply diff_mapsto_iff in H2.
    destruct H1 as [H11 H12]; auto.
    destruct H2 as [H21 H22]; auto.
      eapply beq_typ_iff_eq.
      eapply MapsTo_fun; eauto.
Qed.
  
Lemma dmap_Sub_diff_left : forall M1 M2 M,
  M1 <<= M2 ->
  (M1 -- M) <<= (M2 -- M).
Proof.
  intros M1 M2 M Hsub.
  unfold EMap_Submap.
  unfold EMap_Submap in Hsub.
  destruct Hsub as [Hsub1 Hsub2].
  split.
    intros k H.
    apply diff_in_iff in H.
    eapply diff_in_iff.
    destruct H as [H1 H2]; auto.

    intros k t t' H1 H2.
    apply diff_mapsto_iff in H1.
    apply diff_mapsto_iff in H2.
    destruct H1 as [H11 H12]; auto.
    destruct H2 as [H21 H22]; auto.
    eauto.
Qed.

Lemma dmap_remove_preserves_Sub_right : forall x M M',
  M <<= M' ->
  (M[-]x) <<= (M'[-]x).
Proof.
  intros x M M' Hsub.
  destruct Hsub as [Hsub1 Hsub2].
  split.
    intros k J.
    eapply remove_in_iff.
    apply remove_in_iff in J.
    destruct J as [J1 J2].
    split; auto.
   
    intros k t t' J J'.
    apply remove_mapsto_iff in J.
    apply remove_mapsto_iff in J'.
    destruct J as [J1 J2].
    destruct J' as [J1' J2'].
    eauto.
Qed.    

Lemma dmap_Sub_rewrite_Union_right : forall M1 M2 M2',
  M1 ** M2' ->
  M2 <<= M2' -> 
  (M1 |_| M2) <<= (M1 |_| M2').
Proof.
  intros M1 M2 M2' Disj Hsub.
  destruct Hsub as [Hsub1 Hsub2].
  split.
    intros k H.
    apply update_in_iff in H.
    eapply update_in_iff.
    destruct H as [H | H]; auto.

    intros k t t' H1 H2.
    apply update_mapsto_iff in H1.
    apply update_mapsto_iff in H2.
    destruct H1 as [H1 | [H11 H12]].
      destruct H2 as [H2 | [H21 H22]].
        eapply Hsub2; eauto.

        assert (False) as F.
          apply H22.
          apply Hsub1.
          apply find_mapsto_iff in H1.
          eapply in_find_iff.
          rewrite H1.
          intro J. inversion J.
        inversion F.

      destruct H2 as [H2 | [H21 H22]].
        assert (False) as F.
          apply (@Disj k).
          split; auto.
            eapply in_find_iff.
            apply find_mapsto_iff in H11.
            rewrite H11.
            intro J. inversion J.

            eapply in_find_iff.
            apply find_mapsto_iff in H2.
            rewrite H2.
            intro J. inversion J.
        inversion F.

        eapply beq_typ_iff_eq.
        eapply MapsTo_fun; eauto.
Qed.

(*  diff *)
Lemma dmap_diff_refl : forall (M : dmap),
  (M -- M) ~~ @@ .
Proof.
  intros M.
  unfold EMap.Equal.
  intro y.
  rewrite empty_o.
  eapply not_find_in_iff.
  unfold not.
  intro H.
  apply diff_in_iff in H.
  destruct H as [H1 H2].
  apply H2; auto.
Qed.

Lemma dmap_diff_mono : forall (M M': dmap),
  (M -- M') <<= M.
Proof.
  intros M M'.
  unfold EMap_Submap.
  split.
    intros k H.
    apply diff_in_iff in H.
    destruct H; auto.
     
    intros k t1 t2 H1 H2.
    apply diff_mapsto_iff in H1.
    destruct H1 as [H11 H12].
    apply MapsTo_fun with (e':=t2) in H11; auto.
    apply beq_typ_iff_eq in H11; auto.
Qed.

Lemma dmap_diff_union_refl : forall (M M': dmap),
  M' <<= M ->
  ((M -- M') |_| M') ~~ M.
Proof.
  intros M M' Hsub.
  unfold EMap_Submap in Hsub. 
  destruct Hsub as [Hsub1 Hsub2].
  unfold EMap.Equal.  
  intro y.
  remember (EMap.find (elt:=typ) y M) as R.
  destruct R.
    apply sym_eq in HeqR.
    apply find_mapsto_iff in HeqR.
    eapply find_mapsto_iff.
    eapply update_mapsto_iff.
    destruct (@EMapsTo_dec y t M') as [tH | fH]; auto.
      right.
      split.
        eapply diff_mapsto_iff.
        split; auto.
          unfold EMap.In. unfold EMap.Raw.PX.In.
          unfold not. intro H.
          destruct H as [t' H].
          assert (J:=H).
          apply Hsub2 with (t':=t) in H; auto.
          apply beq_typ_iff_eq in H. subst.
          apply fH. auto.
          
        unfold EMap.In. unfold EMap.Raw.PX.In.
        unfold not. intro H.
        destruct H as [t' H].
        assert (J:=H).
        apply Hsub2 with (t':=t) in H; auto.
        apply beq_typ_iff_eq in H. subst.
        apply fH. auto.
    apply sym_eq in HeqR.
    apply not_find_in_iff in HeqR.
    eapply not_find_in_iff.
    unfold not. intro H.
    apply HeqR.
    apply update_in_iff in H.
    destruct H as [tH | fH]; auto.
      apply diff_in_iff in tH.
      destruct tH; auto.
Qed.

Lemma dmap_Equal_diff_refl : forall (M M': dmap),
  M ~~ M' ->
  @@ ~~ (M -- M').
Proof.
  intros M M' Heq.
  intro y.
  rewrite empty_o.
  apply sym_eq.
  eapply not_find_in_iff.
  unfold not.
  intro H.
  apply diff_in_iff in H.
  destruct H as [H1 H2].
  apply H2.
  eapply in_find_iff.
  rewrite <- Heq.
  eapply in_find_iff; auto.
Qed.

Lemma dmap_diff_preserves_Equal : forall (M M' M'':dmap),
  M ~~ M' -> (M --  M'') ~~ (M' --  M'').
Proof.
  intros M M' M'' H y.
  remember (EMap.find (elt:=typ) y (M -- M'')) as R.
  apply sym_eq in HeqR. apply sym_eq.
  destruct R.
    apply find_mapsto_iff in HeqR; auto.
    apply diff_mapsto_iff in HeqR; auto.
    eapply find_mapsto_iff.
    eapply diff_mapsto_iff.
    destruct HeqR as [H1 H2].
      split; auto.
        eapply find_mapsto_iff.
        rewrite <- H.
        eapply find_mapsto_iff; auto.

    apply not_find_in_iff in HeqR; auto.
    eapply not_find_in_iff; auto.
    intro J. apply HeqR. clear HeqR.
    apply diff_in_iff in J; auto.
    eapply diff_in_iff.
    destruct J as [H1 H2].
      split; auto.
        eapply in_find_iff.
        rewrite H.
        eapply in_find_iff; auto.
Qed.

Lemma dmap_union_diff_distr : forall (M1 M2 M:dmap), 
  ((M1 |_| M2) -- M) ~~ ((M1 -- M) |_| (M2 -- M)).
Proof with simpl_env; eauto.
  intros M1 M2 M y.
  remember (EMap.find (elt:=typ) y ((M1 |_| M2) -- M)) as R.
  destruct R; apply sym_eq in HeqR; apply sym_eq.
    apply find_mapsto_iff in HeqR.
    eapply find_mapsto_iff.
    eapply update_mapsto_iff.
    apply diff_mapsto_iff in HeqR.
    destruct HeqR as [H1 H2].
    apply update_mapsto_iff in H1.
    destruct H1 as [H1 | [H11 H12]].
      left.
      eapply diff_mapsto_iff. auto.
   
      right.
      split.
        eapply diff_mapsto_iff. auto.
  
        unfold not. intro J. apply H12.
        apply diff_in_iff in J. 
        destruct J; auto.
       
     apply not_find_in_iff in HeqR.
     eapply not_find_in_iff. 
     unfold not. intro J. apply HeqR. clear HeqR.
     eapply diff_in_iff.
     apply update_in_iff in J. 
     destruct J as [J | J].
       apply diff_in_iff in J.
       destruct J as [J1 J2].
       split; auto.
       eapply update_in_iff; auto.
     
       apply diff_in_iff in J.
       destruct J as [J1 J2].
       split; auto.
       eapply update_in_iff; auto. 
Qed. 

Lemma dmap_Equal_rewrite_diff_left : forall (M M1 M1' M2:dmap),
  M1 ~~ M1' -> M ~~ (M1 -- M2) -> M ~~ (M1' -- M2).
Proof.
  intros M M1 M1' M2 Heq Heq' y.
  rewrite Heq'. clear Heq'.
  remember (EMap.find (elt:=typ) y (M1 -- M2)) as R.
  destruct R; apply sym_eq; apply sym_eq in HeqR.
    apply find_mapsto_iff in HeqR.
    eapply find_mapsto_iff.
    eapply diff_mapsto_iff.
    apply diff_mapsto_iff in HeqR.
    destruct HeqR as [H1 H2].
      split; auto.
        eapply find_mapsto_iff.
        rewrite <- Heq.
        apply find_mapsto_iff in H1. auto.
 
    apply not_find_in_iff in HeqR.
    eapply not_find_in_iff. 
    unfold not. intro J. apply HeqR. clear HeqR.
    eapply diff_in_iff.
    apply diff_in_iff in J. 
    destruct J as [J1 J2].
      split; auto.
        eapply in_find_iff.
        rewrite Heq.
        apply in_find_iff in J1. auto.
Qed.

Lemma dmap_diff_commut : forall (M M1 M2:dmap),
  ((M -- M1) -- M2) ~~ ((M -- M2) -- M1).
Proof.
  intros M M1 M2 y.
  remember (EMap.find (elt:=typ) y ((M--M2)--M1)) as R.
  apply sym_eq in HeqR.
  destruct R.
    eapply find_mapsto_iff.
    eapply diff_mapsto_iff.
    apply find_mapsto_iff in HeqR.
    apply diff_mapsto_iff in HeqR.
    destruct HeqR as [H1 H2].
    apply diff_mapsto_iff in H1.
    destruct H1 as [H11 H12].
    split; auto.
      eapply diff_mapsto_iff.
      split; auto.
  
    eapply not_find_in_iff.
    apply not_find_in_iff in HeqR.
    intro J. apply HeqR. clear HeqR.
    eapply diff_in_iff.
    apply diff_in_iff in J.
    destruct J as [H1 H2].
    apply diff_in_iff in H1.
    destruct H1 as [H11 H12].
    split; auto.
      eapply diff_in_iff.
      split; auto.
Qed.

Lemma dmap_diff_remove_commut : forall (M M1:dmap) x,
  ((M -- M1) [-] x) ~~ ((M [-] x) -- M1).
Proof.
  intros M M1 x y.
  remember (EMap.find (elt:=typ) y ((M[-]x)--M1)) as R.
  apply sym_eq in HeqR.
  destruct R.
    eapply find_mapsto_iff.
    eapply remove_mapsto_iff.
    apply find_mapsto_iff in HeqR.
    apply diff_mapsto_iff in HeqR.
    destruct HeqR as [H1 H2].
    apply remove_mapsto_iff in H1.
    destruct H1 as [H11 H12].
    split; auto.
      eapply diff_mapsto_iff.
      split; auto.
  
    eapply not_find_in_iff.
    apply not_find_in_iff in HeqR.
    intro J. apply HeqR. clear HeqR.
    eapply diff_in_iff.
    apply remove_in_iff in J.
    destruct J as [H1 H2].
    apply diff_in_iff in H2.
    destruct H2 as [H21 H22].
    split; auto.
      eapply remove_in_iff.
      split; auto.
Qed.

Lemma dmap_diff_distr : forall x T M M',
  ~ EMap.In (elt:=typ) x M' ->
  x:::T[+](M -- M') ~~ ((x:::T[+]M) -- M').
Proof.
  intros x T M M' H1 k.
  remember (EMap.find (elt:=typ) k ((x:::T[+]M) -- M')) as R.
  destruct R; apply sym_eq in HeqR.
    eapply find_mapsto_iff.
    apply find_mapsto_iff in HeqR.
    eapply add_mapsto_iff.
    apply diff_mapsto_iff in HeqR.
    destruct HeqR as [J1 J2].
    apply add_mapsto_iff in J1.
    destruct J1 as [[J11 J12]|[J11 J12]]; subst; auto.
      right. split; auto.
        eapply diff_mapsto_iff; auto.

    eapply not_find_in_iff.
    apply not_find_in_iff in HeqR.
    intro J. apply HeqR. clear HeqR.
    eapply diff_in_iff.
    apply add_in_iff in J.
    destruct J as [J | J]; subst.
      split; auto.
        eapply add_in_iff; auto.
      
      apply diff_in_iff in J.
      destruct J as [J1 J2].
      split; auto.
        eapply add_in_iff; auto.
Qed.

Lemma dmap_Equal_rewrite_diff_right : forall (M M1 M2 M2':dmap),
  M2 ~~ M2' -> M ~~ (M1 -- M2) -> M ~~ (M1 -- M2').
Proof.
  intros M M1 M2 M2' Heq Heq' y.
  rewrite Heq'. clear Heq'.
  remember (EMap.find (elt:=typ) y (M1 -- M2)) as R.
  destruct R; apply sym_eq; apply sym_eq in HeqR.
    apply find_mapsto_iff in HeqR.
    eapply find_mapsto_iff.
    eapply diff_mapsto_iff.
    apply diff_mapsto_iff in HeqR.
    destruct HeqR as [H1 H2].
      split; auto.
        intro J. apply H2. clear H2.
        rewrite Heq. auto.

    apply not_find_in_iff in HeqR.
    eapply not_find_in_iff. 
    unfold not. intro J. apply HeqR. clear HeqR.
    eapply diff_in_iff.
    apply diff_in_iff in J. 
    destruct J as [J1 J2].
      split; auto.
        intro J. apply J2. clear J2.
        rewrite <- Heq. auto.
Qed.

Lemma dmap_diff_merge : forall M1 M2 M3,
  M3 <<= M2 ->
  M2 <<= M1 ->
  ((M1 -- M2) |_| (M2 -- M3)) ~~ (M1 -- M3).
Proof.
  intros M1 M2 M3 sub1 sub2 x.
  remember (EMap.find (elt:=typ) x (M1 -- M3)) as R.
  destruct R; apply sym_eq in HeqR.
    eapply find_mapsto_iff.
    eapply update_mapsto_iff.
    apply find_mapsto_iff in HeqR.
    apply diff_mapsto_iff in HeqR.
    destruct HeqR as [H1 H2].
    destruct sub2 as [sub21 sub22].   
    destruct (@In_dec typ M2 x) as [J | J].
      (* x in M2 *)
      left. eapply diff_mapsto_iff; auto.
        eapply in_mapsto_iff in J.
        destruct J as [t' J].
        split; auto.
          assert (t' = t) as eqt.
            eapply beq_typ_iff_eq.
            eapply sub22 with (k:=x); eauto.
          subst; auto.
      (* x notin M2 *)
      right. split.
        eapply diff_mapsto_iff; auto.

        intro H.
        apply diff_in_iff in H.
        destruct H as [HH1 HH2].
        apply J; auto.

    eapply not_find_in_iff.
    apply not_find_in_iff in HeqR.
    intro J. apply HeqR. clear HeqR.
    apply update_in_iff in J.
    destruct J as [J | J]; auto.
      apply diff_in_iff in J.
      eapply diff_in_iff.
      destruct J as [J1 J2].
      split; auto.
        intro H. apply J2. clear J2.
        destruct sub1 as [sub11 sub12]; auto.
         
      apply diff_in_iff in J.
      eapply diff_in_iff.
      destruct J as [J1 J2].
      split; auto.
        destruct sub2 as [sub21 sub22]; auto.
Qed.

(* union *)
Lemma dmap_union_refl : forall (M : dmap),
  (M |_| M) ~~ M.
Proof.
  intros M.
  unfold EMap.Equal.
  intro y.
  remember (EMap.find (elt:=typ) y (update M M)) as H.
  apply sym_eq in HeqH.
  destruct H.
    apply find_mapsto_iff in HeqH.
    apply update_mapsto_iff in HeqH.
    destruct HeqH as [HeqH | [HeqH1 HeqH2]].
       apply find_mapsto_iff in HeqH. auto.
       apply find_mapsto_iff in HeqH1. auto.

    apply sym_eq.
    apply -> not_find_in_iff.
    apply not_find_in_iff in HeqH.
    unfold not.
    intro H.
    apply HeqH.
    apply <- update_in_iff. auto.
Qed.

  
Lemma dmap_union_empty_refl : forall M,
  (@@ |_| M) ~~ M.
Proof.
  intros M y.
  remember (EMap.find (elt:=typ) y M) as R.
  destruct R; apply sym_eq in HeqR.
    eapply find_mapsto_iff.
    eapply update_mapsto_iff.
    left.
    eapply find_mapsto_iff; auto.

    apply not_find_in_iff in HeqR.
    eapply not_find_in_iff.
    unfold not. intro J. apply HeqR.
    apply update_in_iff in J.
    destruct J as [J | J]; auto.
      apply empty_in_iff in J. inversion J.
Qed.
    
Lemma dmap_union_add_distr_left : forall (M1 M2:dmap) x T,
 ~ EMap.In x M2 -> (x:::T[+](M1 |_| M2)) ~~ ((x:::T[+]M1) |_| M2). 
Proof with simpl_env; eauto.  
  intros M1 M2 x T Hnotin y.
  remember (EMap.find (elt:=typ) y (x:::T[+](M1 |_| M2))) as R.
  destruct R; apply sym_eq in HeqR; apply sym_eq.
    eapply find_mapsto_iff.
    apply find_mapsto_iff in HeqR.
    eapply update_mapsto_iff.
    apply add_mapsto_iff in HeqR.
    destruct HeqR as [[Hxy HTt] | [Hxny HeqR]]; subst.
      destruct (@EMapsTo_dec y t M2) as [J | J].
        left; auto.
        right. split; auto.
          eapply add_mapsto_iff; auto.

      apply update_mapsto_iff in HeqR.
      destruct HeqR as [H1 | [H1 H2]]; auto.
        right.
        split; auto.
          eapply add_mapsto_iff; auto.
  
    eapply not_find_in_iff.
    apply not_find_in_iff in HeqR.
    unfold not. intro J. apply HeqR. clear HeqR.
    eapply add_in_iff.
      apply update_in_iff in J.
      destruct J as [J | J].
        apply add_in_iff in J.
          destruct J as [J | J]; auto.
            right.
            eapply update_in_iff. auto.
        right.
        eapply update_in_iff. auto. 
Qed.


Lemma dmap_union_remove_distr : forall (M1 M2:dmap) x, ((M1 |_| M2) [-] x) ~~ ((M1 [-] x) |_| (M2 [-] x)).
Proof with simpl_env; eauto.
  intros M1 M2 x y.
  remember (EMap.find (elt:=typ) y ((M1 |_| M2) [-] x)) as R.
  destruct R; apply sym_eq in HeqR; apply sym_eq.
    apply find_mapsto_iff in HeqR.
    eapply find_mapsto_iff.
    eapply update_mapsto_iff.
    apply remove_mapsto_iff in HeqR.
    destruct HeqR as [Hxny Hmapsto].
    apply update_mapsto_iff in Hmapsto.
    destruct Hmapsto as [Hmapsto2 | [Hmapsto1 Hmapston2]].
      left.
      eapply remove_mapsto_iff. auto.
   
      right.
      split.
        eapply remove_mapsto_iff. auto.
  
        unfold not. intro J. apply Hmapston2.
        apply remove_in_iff in J. 
        destruct J; auto.
       
     apply not_find_in_iff in HeqR.
     eapply not_find_in_iff. 
     unfold not. intro J. apply HeqR. clear HeqR.
     eapply remove_in_iff.
     apply update_in_iff in J. 
     destruct J as [J | J].
       apply remove_in_iff in J.
       destruct J as [J1 J2].
       split; auto.
       eapply update_in_iff; auto.
     
       apply remove_in_iff in J.
       destruct J as [J1 J2].
       split; auto.
       eapply update_in_iff; auto. 
Qed.  

Lemma dmap_Equal_rewrite_Union_right : forall (M M1 M2 M2':dmap),
  M2 ~~ M2' -> M ~~ (M1 |_| M2) -> M ~~ (M1 |_| M2').
Proof.
  unfold EMap.Equal.
  intros M M1 M2 M2' Heq Heq' y.
  rewrite Heq'. clear Heq'.
  remember (EMap.find (elt:=typ) y (M1 |_| M2)) as R.
  destruct R; apply sym_eq; apply sym_eq in HeqR.
    apply find_mapsto_iff in HeqR.
    eapply find_mapsto_iff.
    eapply update_mapsto_iff.
    apply update_mapsto_iff in HeqR.
    destruct HeqR as [H1 | [H1 H2]].
      left.
      eapply find_mapsto_iff.
      rewrite <- Heq.
      apply find_mapsto_iff in H1. auto.

      right.
      split; auto.
      unfold not. intro J. apply H2.
      eapply in_find_iff.
      rewrite Heq.
      apply in_find_iff in J. auto.
 
     apply not_find_in_iff in HeqR.
     eapply not_find_in_iff. 
     unfold not. intro J. apply HeqR. clear HeqR.
     eapply update_in_iff.
     apply update_in_iff in J. 
     destruct J as [J | J].
       left. auto.

       right. 
       eapply in_find_iff.
       rewrite Heq.
       apply in_find_iff in J. auto.
Qed.

Lemma dmap_Equal_rewrite_Union_left : forall (M M1 M1' M2:dmap),
  M1 ~~ M1' -> M ~~ (M1 |_| M2) -> M ~~ (M1' |_| M2).
Proof.
  unfold EMap.Equal.
  intros M M1 M1' M2 Heq Heq' y.
  rewrite Heq'. clear Heq'.
  remember (EMap.find (elt:=typ) y (M1 |_| M2)) as R.
  destruct R; apply sym_eq; apply sym_eq in HeqR.
    apply find_mapsto_iff in HeqR.
    eapply find_mapsto_iff.
    eapply update_mapsto_iff.
    apply update_mapsto_iff in HeqR.
    destruct HeqR as [H1 | [H1 H2]].
      left. auto.

      right.
      split; auto.
      eapply find_mapsto_iff.
      rewrite <- Heq.
      apply find_mapsto_iff in H1. auto.

    apply not_find_in_iff in HeqR.
    eapply not_find_in_iff. 
    unfold not. intro J. apply HeqR. clear HeqR.
    eapply update_in_iff.
    apply update_in_iff in J. 
    destruct J as [J | J].
      left.
      eapply in_find_iff.
      rewrite Heq.
      apply in_find_iff in J. auto.
 
      right. auto.
Qed.

Lemma dmap_union_sym : forall (M1 M2:dmap),
  M1 ** M2 ->
  (M1 |_| M2) ~~ (M2 |_| M1).
Proof.
  intros M1 M2 Hdisj y.
  remember (EMap.find (elt:=typ) y (M1 |_| M2)) as R.
  destruct R; apply sym_eq; apply sym_eq in HeqR.
    apply find_mapsto_iff in HeqR.
    eapply find_mapsto_iff.
    eapply update_mapsto_iff.
    apply update_mapsto_iff in HeqR.
    destruct HeqR as [H1 | [H1 H2]]; auto.
      right.
      split; auto.
        unfold not. intro J.
        destruct (@Disjoint_alt typ M1 M2) as [H2 H3].
        apply <- in_mapsto_iff in J.
        destruct J as [e J].
        apply H2 with (k:=y) (e:=e) (e':=t) in Hdisj; auto.

    apply not_find_in_iff in HeqR.
    eapply not_find_in_iff. 
    unfold not. intro J. apply HeqR. clear HeqR.
    eapply update_in_iff.
    apply update_in_iff in J.
    destruct J as [J | J]; auto.
Qed.

Lemma dmap_Sub_rewrite_Union_left : forall M1 M1' M2,
  M1 <<= M1' -> (M1 |_| M2) <<= (M1' |_| M2).
Proof.
  intros M1 M1' M2 Hsub.
  unfold EMap_Submap.
  unfold EMap_Submap in Hsub.
  destruct Hsub as [Hsub1 Hsub2].
  split.
    intros k H.
    apply update_in_iff in H.
    eapply update_in_iff.
    destruct H as [H | H]; auto.

    intros k t t' H1 H2.
    apply update_mapsto_iff in H1.
    apply update_mapsto_iff in H2.
    destruct H1 as [H1 | [H11 H12]].
      destruct H2 as [H2 | [H21 H22]].
        eapply beq_typ_iff_eq.
        eapply MapsTo_fun; eauto.

        apply find_mapsto_iff in H1.
        apply not_find_in_iff in H22.
        rewrite H22 in H1. 
        inversion H1.
      destruct H2 as [H2 | [H21 H22]].
        apply find_mapsto_iff in H2.
        apply not_find_in_iff in H12.
        rewrite H12 in H2.
        inversion H2.

        eapply Hsub2; eauto.
Qed.

Lemma dmap_union_distr : forall (M1 M2 M3:dmap), 
  ((M1 |_| M2) |_| M3) ~~ ((M1 |_| M3) |_| (M2 |_| M3)).
Proof with simpl_env; eauto.
  intros M1 M2 M3 y.
  remember (EMap.find (elt:=typ) y ((M1 |_| M2) |_| M3)) as R.
  destruct R; apply sym_eq in HeqR; apply sym_eq.
    apply find_mapsto_iff in HeqR.
    eapply find_mapsto_iff.
    eapply update_mapsto_iff.
    apply update_mapsto_iff in HeqR.
    destruct HeqR as [Hmapsto3 | [Hmapsto12 Hmapston3]].
      left. eapply update_mapsto_iff. auto.
   
      apply update_mapsto_iff in Hmapsto12.
      destruct Hmapsto12 as [Hmapsto2 | [Hmapsto1 Hmapston2]].
        left. eapply update_mapsto_iff. auto.
        right. split.
          eapply update_mapsto_iff. auto.
          intro J.
          apply update_in_iff in J. 
          destruct J as [J | J].
            apply Hmapston2; auto.
            apply Hmapston3; auto.
       
     apply not_find_in_iff in HeqR.
     eapply not_find_in_iff. 
     unfold not. intro J. apply HeqR. clear HeqR.
     eapply update_in_iff.
     apply update_in_iff in J. 
     destruct J as [J | J].
       apply update_in_iff in J.
       destruct J as [J | J]; auto.
         left. eapply update_in_iff; auto.

       apply update_in_iff in J.
       destruct J as [J | J]; auto.
         left. eapply update_in_iff; auto.
Qed.  



Lemma dmap_union_assoc : forall (M1 M2 M3 : dmap),
  ((M1 |_| M2) |_| M3) ~~ (M1 |_| (M2 |_| M3)).
Proof.
  intros M1 M2 M3 x.
  remember (EMap.find (elt:=typ) x (M1 |_| (M2 |_| M3))) as R.
  apply sym_eq in HeqR.
  destruct R.
    apply find_mapsto_iff in HeqR.
    eapply find_mapsto_iff.
    apply update_mapsto_iff in HeqR.
    destruct HeqR as [H | [H1 H2]].
      apply update_mapsto_iff in H.
        destruct H as [H | [H1 H2]].
          eapply update_mapsto_iff. auto.
          eapply update_mapsto_iff.
            right. split; auto.
            eapply update_mapsto_iff; auto.
  
      eapply update_mapsto_iff.
        right. split.
          eapply update_mapsto_iff.
            right. split; auto.
              intro J. apply H2. clear H2.
              eapply update_in_iff; auto.
    
              intro J. apply H2. clear H2.
              eapply update_in_iff; auto.

    apply not_find_in_iff in HeqR.
    eapply not_find_in_iff.
    intro J. apply HeqR. clear HeqR.
    apply update_in_iff in J.
    destruct J as [J | J].
      apply update_in_iff in J.
        destruct J as [J | J].
          eapply update_in_iff. auto.
          eapply update_in_iff.
            right. eapply update_in_iff; auto.
  
      eapply update_in_iff.
        right. eapply update_in_iff. auto.
Qed.

Lemma dmap_union_preserves_Equal_right : forall (M M' M'':dmap),
  M ~~ M' ->
  (M |_| M'') ~~ (M' |_| M'').
Proof.
  intros M M' M'' H y.
  remember (EMap.find (elt:=typ) y (M |_| M'')) as R.
  apply sym_eq in HeqR. apply sym_eq.
  destruct R.
    apply find_mapsto_iff in HeqR.
    eapply find_mapsto_iff.
    apply update_mapsto_iff in HeqR.
    destruct HeqR as [H1 | [H1 H2]]; subst.
      eapply update_mapsto_iff; auto.
      eapply update_mapsto_iff.
        right. split; auto.
          eapply find_mapsto_iff. 
          rewrite <- H.
          eapply find_mapsto_iff. auto.

    apply not_find_in_iff in HeqR.
    eapply not_find_in_iff.
    unfold not. intro J. 
    apply HeqR. clear HeqR.
    apply update_in_iff in J.
    destruct J as [J | J]; subst.
      eapply update_in_iff; auto.
        left.
        apply in_find_iff in J.
        eapply in_find_iff.
        rewrite H. auto.
      eapply update_in_iff. auto.
Qed.

(* add remove *)               
Lemma dmap_eq_hd_inv : forall A x (T:A) M M',
  ~ EMap.In x M ->
  (EMap.add x T M) ~~ M' -> M ~~ (M' [-] x).
Proof.
  unfold EMap.Equal.
  intros A x T M M' H1 H2 y.
  remember (EMap.find (elt:=A) y M) as R.
  destruct R.
    rename a into s.
    apply sym_eq in HeqR. apply sym_eq.
    eapply find_mapsto_iff.
    assert (EMap.find (elt:=A) y M <> None) as J.
      unfold not. intro K. rewrite K in HeqR. inversion HeqR.
    eapply in_find_iff in J.
    eapply remove_neq_mapsto_iff.
      destruct (x == y); auto.
        subst. contradict J; auto.
     
      eapply find_mapsto_iff.
      rewrite <- H2.
      eapply find_mapsto_iff.
      eapply add_neq_mapsto_iff.
        destruct (x == y); auto.
          subst. contradict J; auto.
        eapply find_mapsto_iff; auto.

    apply sym_eq in HeqR. apply sym_eq.
    eapply not_find_in_iff.
    apply not_find_in_iff in HeqR.
    unfold not. intro J.
    apply HeqR.
    apply remove_in_iff in J.
    destruct J; auto.
    apply in_find_iff in H0.
    rewrite <- H2 in H0.
    apply in_find_iff in H0.
    eapply add_neq_in_iff; eauto.
Qed.

Lemma dmap_add_remove_inv : forall (M M':dmap) (x y:atom) T,
  ((x ::: T [+] M) [-] y) ~~ M' ->
  ~ EMap.In x M' ->
  x = y.
Proof.
  intros M M' x y T Heq Hnotin.
  destruct (x==y); auto.
  assert (J:=@Heq x).
  remember (EMap.find (elt:=typ) x ((x:::T[+]M)[-]y)) as R.
  destruct R; apply sym_eq in HeqR; apply sym_eq in J.
    assert (EMap.find (elt:=typ) x M' <> None) as H.
      rewrite J. intro W. inversion W.
    apply in_find_iff in H.
    contradict H; auto.

    apply not_find_in_iff in HeqR.
    assert (False) as H.
      apply HeqR.
      eapply remove_in_iff.
      split; auto.
        eapply add_in_iff; auto.
    inversion H.
Qed.

(* add *)
Lemma dmap_add_preserves_Equal : forall (M M':dmap) x T,
  M ~~ M' ->
  (EMap.add x T M) ~~ (EMap.add x T M').
Proof.
  intros M M' x T H y.
  remember (EMap.find (elt:=typ) y (x:::T[+]M)) as R.
  apply sym_eq in HeqR. apply sym_eq.
  destruct R.
    apply find_mapsto_iff in HeqR.
    eapply find_mapsto_iff.
    apply add_mapsto_iff in HeqR.
    destruct HeqR as [[H1 H2] | [H1 H2]]; subst.
      eapply add_mapsto_iff; auto.
      eapply add_neq_mapsto_iff; auto.
        eapply find_mapsto_iff.
        rewrite <- H.
        eapply find_mapsto_iff. auto.

    apply not_find_in_iff in HeqR.
    eapply not_find_in_iff.
    unfold not. intro J. 
    apply HeqR.
    apply add_in_iff in J.
    destruct J as [J | J]; subst.
      eapply add_in_iff; auto.
      eapply add_in_iff.
        right.
        apply in_find_iff in J.
        eapply in_find_iff.
        rewrite H. auto.
Qed.

Lemma dmap_add_remove_refl : forall (M:dmap) x T,
  ~ EMap.In x M ->
  ((x ::: T [+] M) [-] x) ~~ M.
Proof.
  intros M x T Hnotin.
  unfold EMap.Equal.
  intros y.
  remember (EMap.find (elt:=typ) y ((x:::T[+]M)[-]x)) as R.
  destruct R; apply sym_eq; apply sym_eq in HeqR.
    apply find_mapsto_iff in HeqR.
    eapply find_mapsto_iff.
    apply remove_mapsto_iff in HeqR.
    destruct HeqR as [Hxny HeqR].
    apply add_mapsto_iff in HeqR.
    destruct HeqR as [[Hxy HTt] | [Hxny' HeqR]]; subst; auto.
      contradict Hxny; auto.

    apply not_find_in_iff in HeqR.
    eapply not_find_in_iff.
    unfold not. intro J. apply HeqR. clear HeqR.
    eapply remove_in_iff.
    destruct (x==y); subst.
      contradict Hnotin; auto.
      split; auto.
        eapply add_in_iff; auto.
Qed.

Lemma dmap_add_preserves_disjoint : forall (M1 M2:dmap) x T,
  ~ EMap.In x M1 ->
  (x:::T[+]M1) ** M2 -> M1 ** M2.
Proof.
  intros M1 M2 x T Hnotin Hdisj.
  eapply Disjoint_alt.
  intros k e e' HinM1 HinM2.
  destruct (@Disjoint_alt typ (x:::T[+]M1) M2) as [H1 H2].
  apply H1 with (k:=k) (e:=e) (e':=e') in Hdisj; auto.
    destruct (x==k); subst.
      assert (False).
        apply Hnotin.
        assert (exists e, EMap.MapsTo k e M1) as J.
          exists e. auto.
        apply in_mapsto_iff in J; auto.
      inversion H.
    map_iff. auto.
Qed.

Lemma dmap_Equal_rewrite_add_right : forall (M M':dmap) x S,
  M ~~ M' ->
  (x:::S[+]M) ~~ (x:::S[+]M').
Proof.
  intros M M' x S MeqM'.
  intro y.
  remember (EMap.find (elt:=typ) y (x:::S[+]M')) as R.
  destruct R; apply sym_eq in HeqR.
    apply find_mapsto_iff in HeqR.
    apply add_mapsto_iff in HeqR.
    destruct HeqR as [[H1 H2] | [H1 H2]]; subst.
      eapply find_mapsto_iff; auto.
      eapply add_mapsto_iff; auto.

      eapply find_mapsto_iff; auto.
      eapply add_mapsto_iff.
        right. split; auto.
          eapply find_mapsto_iff; auto.
          rewrite MeqM'.
          eapply find_mapsto_iff; auto.

    apply not_find_in_iff in HeqR.
    eapply not_find_in_iff.
    intro J. apply HeqR. clear HeqR.
    apply add_in_iff in J.
    destruct J as [J | J]; subst.
      eapply add_in_iff; auto.
      eapply add_in_iff.
        right.
        eapply in_find_iff; auto.
        rewrite <- MeqM'.
        eapply in_find_iff; auto.
Qed.

(* Equal *)
Lemma in_if_Equal : forall (m1 m2 : dmap),
  m1 ~~ m2 -> (forall k, EMap.In k m1 <-> EMap.In k m2).
Proof.
  intros m1 m2.
  destruct (@Equal_mapsto_iff typ m1 m2) as [H1 H2].
  intro J.
    intro k.
    split; intro H.
      apply in_mapsto_iff in H.
      destruct H as [e H].
      apply (@H1 J) in H.
      assert (exists e, EMap.MapsTo k e m2) as P.
        exists e. auto.
      apply -> in_mapsto_iff in P. auto.

      apply in_mapsto_iff in H.
      destruct H as [e H].
      apply (@H1 J) in H.
      assert (exists e, EMap.MapsTo k e m1) as P.
        exists e. auto.
      apply -> in_mapsto_iff in P. auto.
Qed.

Lemma dmap_map_preserves_Equal : forall (m m':dmap) (f:typ->typ),
  m ~~ m' ->
  EMap.map f m ~~ EMap.map f m'.
Proof.
  intros m m' f Heq y.
  remember (EMap.find (elt:=typ) y (EMap.map f m)) as R.
  destruct R; apply sym_eq in HeqR; apply sym_eq.
    apply find_mapsto_iff in HeqR.
    eapply find_mapsto_iff.
    map_iff. apply map_mapsto_iff in HeqR.
    destruct HeqR as [a [H1 H2]].
    exists a. 
    split; auto.
      eapply find_mapsto_iff.
      rewrite <- Heq.
      eapply find_mapsto_iff; auto.

    apply not_find_in_iff in HeqR.
    eapply not_find_in_iff. 
    unfold not. intro J. apply HeqR. clear HeqR.
    eapply in_find_iff.
    rewrite Heq.
    eapply in_find_iff. auto.
Qed.  

Lemma Equal_mapsto_rewrite : forall m1 m2 : dmap,
  EMap.Equal m1 m2 ->
  (forall k e, EMap.MapsTo k e m1 <-> EMap.MapsTo k e m2).
Proof.
  intros m1 m2 EQ.
  destruct (@Equal_mapsto_iff typ m1 m2) as [H1 H2].
  auto.
Qed.

(* Disjoint *)
Lemma dmap_Disjoint_in_notin : forall M M' x T,
  M ** M' ->
  EMap.MapsTo x T M ->
  ~ EMap.In (elt:=typ) x M'.
Proof.
  intros M M' x T disj xinM.
  unfold Disjoint in disj.
  intro J.
  apply (@disj x).
  split; auto.
    apply find_mapsto_iff in xinM.
    eapply in_find_iff.
    rewrite xinM.
    intro H. inversion H.
Qed.

Lemma dmap_Disjoint_sym : forall (M M':dmap),
  M ** M' ->
  M' ** M.
Proof.
  intros M M' disj x J.
  apply (@disj x).
  destruct J as [J1 J2].
  split; auto.
Qed.  

Lemma dmap_add_preserves_disjoint_left : forall (M1 M2:dmap) x T,
  ~ EMap.In x M2 ->
  M1 ** M2 ->
  (x:::T[+]M1) ** M2.
Proof.
  intros M1 M2 x T Hnotin Hdisj.
  eapply Disjoint_alt.
  intros k e e' HinM1 HinM2.
  destruct (@Disjoint_alt typ M1 M2) as [H1 H2].
  apply H1 with (k:=k) (e:=e) (e':=e') in Hdisj; auto.
    destruct (x==k); subst.
      assert (False).
        apply Hnotin.
        assert (exists e, EMap.MapsTo k e M2) as J.
          exists e'. auto.
        apply in_mapsto_iff in J; auto.
      inversion H.
    apply add_mapsto_iff in HinM1.
    destruct HinM1 as [[HH1 HH2]|[HH1 HH2]]; subst; auto.
      contradict n; auto.
Qed.
 
Lemma dmap_union_preserves_Sub_right : forall (M M' M'':dmap),
  M <<= M' ->
  (M |_| M'') <<= (M' |_| M'').
Proof.
  intros M M' M'' H.
  destruct H as [H1 H2].
  split.
    intros k J.
    apply update_in_iff in J.
    eapply update_in_iff.
    destruct J as [J | J]; auto.

    intros k t t' J1 J2.
    apply update_mapsto_iff in J1.
    apply update_mapsto_iff in J2.
    destruct J1 as [J1 | [J11 J12]].
      destruct J2 as [J2 | [J21 J22]].
        eapply beq_typ_iff_eq.
        eapply MapsTo_fun; eauto.

        assert (False) as H.
          apply J22.
          apply find_mapsto_iff in J1.
          eapply in_find_iff.
          rewrite J1. intro J. inversion J.
        inversion H.  

      destruct J2 as [J2 | [J21 J22]].
        assert (False) as H.
          apply J12.
          apply find_mapsto_iff in J2.
          eapply in_find_iff.
          rewrite J2. intro J. inversion J.
        inversion H.  

        eapply H2; eauto.
Qed.

Lemma dmap_Sub_preserves_disjoint_left : forall (M1 M1' M2:dmap),
  M1 ** M2 ->
  M1' <<= M1 ->
  M1' ** M2.  
Proof.
  intros M1 M1' M2 Disj Sub.
  intros k.
  intro J. apply (@Disj k).
  destruct J as [J1 J2].
  split; auto.
    destruct Sub as [Sub1 Sub2]; auto.
Qed.

Lemma empty_disjoint : forall (M : dmap),
  @@ ** M.
Proof.
  intros M.
  unfold Disjoint.
  intro k.
  unfold not.
  intro J.
  destruct J as [J1 J2].
  apply empty_in_iff in J1.
  auto.
Qed.    

Lemma dmap_Equal_preserves_disjoint_left : forall (M1 M1' M2:dmap),
  M1 ** M2 ->
  M1' ~~ M1 ->
  M1' ** M2.  
Proof.
  intros M1 M1' M2 Disj EQ.
  intros k.
  intro J. apply (@Disj k).
  destruct J as [J1 J2].
  split; auto.
    rewrite <- EQ. auto.
Qed.

Lemma dmap_Equal_preserves_disjoint_right : forall (M1 M2 M2':dmap),
  M1 ** M2 ->
  M2' ~~ M2 ->
  M1 ** M2'.  
Proof.
  intros M1 M2 M2' Disj EQ.
  intros k.
  intro J. apply (@Disj k).
  destruct J as [J1 J2].
  split; auto.
    rewrite <- EQ. auto.
Qed.


Lemma diff_disjoint : forall (M M':dmap),
  (M -- M') ** M'.
Proof.
  intros M M' k J.
  destruct J as [J1 J2].
  apply diff_in_iff in J1.
  destruct J1 as [J11 J12].
  apply J12; auto.
Qed.              



Lemma dmap_disjoint_app : forall (M M1 M2 : dmap),
  M ** M1 ->
  M ** M2 ->
  M ** (M1 |_| M2).
Proof.
  intros M M1 M2 disj1 disj2 k J.
  destruct J as [J1 J2].
  apply update_in_iff in J2.
  destruct J2 as [J2 | J2].
    apply (@disj1 k); auto.
    apply (@disj2 k); auto.
Qed.


Lemma dmap_Sub_preserves_disjoint_right : forall (M1 M2 M2':dmap),
  M1 ** M2 ->
  M2' <<= M2 ->
  M1 ** M2'.  
Proof.
  intros M1 M2 M2' Disj Sub.
  intros k.
  intro J. apply (@Disj k).
  destruct J as [J1 J2].
  split; auto.
    destruct Sub as [Sub1 Sub2]; auto.
Qed.

Lemma dmap_disjoint_cons : forall (M M1 : dmap) x S,
  ~ EMap.In x M ->
  M ** M1 ->
  M ** (x:::S[+]M1).
Proof.
  intros M M1 x S xnotinM disj k J.
  destruct J as [J1 J2].
  apply add_in_iff in J2.
  destruct J2 as [J2 | J2]; subst.
    apply xnotinM; auto.
    apply (@disj k); auto.
Qed.          


Lemma disjoint_diff_refl : forall (M M':dmap),
  M ** M' ->
  M -- M' ~~ M.
Proof.
  intros M M' Disj x.
  remember (EMap.find (elt:=typ) x M) as R.
  destruct R; apply sym_eq in HeqR.
    eapply find_mapsto_iff.
    apply find_mapsto_iff in HeqR.
    eapply diff_mapsto_iff.
    split; auto.
      eapply dmap_Disjoint_in_notin; eauto.

    eapply not_find_in_iff.
    apply not_find_in_iff in HeqR.
    intro J. apply HeqR. clear HeqR.
    apply diff_in_iff in J.
    destruct J; auto.
Qed.  

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../../../metatheory" "-I" "../linf") ***
*** End: ***
 *)