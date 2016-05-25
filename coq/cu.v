(* A formalization of Zeilberger's CU *)

Require Import Arith List.
Require Import Omega.
Require Import FunctionalExtensionality.


Import ListNotations.

Set Implicit Arguments.
Set Contextual Implicit.

(* UTILITIES: Should be in the List library *)
Lemma nth_error_nil : forall A n, nth_error ([]:list A) n = None.
Proof.
  intros. destruct n; simpl; auto.
Qed.  

(*  ------------------------------------------------------------------------- *)

Definition atom := nat.

Inductive pos : Set :=
| PAtom : atom -> pos
| PUnit : pos
| PProd : pos -> pos -> pos
| PZero : pos
| PSum  : pos -> pos -> pos
| PNeg  : pos -> pos
.

(* Proper sub-formula *)
Inductive sub : pos -> pos -> Prop :=
| s_prod1 : forall P Q, sub P (PProd P Q)
| s_prod2 : forall P Q, sub Q (PProd P Q)
| s_sum1  : forall P Q, sub P (PSum P Q)
| s_sum2  : forall P Q, sub Q (PSum P Q)
| s_neg   : forall P, sub P (PNeg P)
| s_trans : forall P Q R, sub P Q -> sub Q R -> sub P R
.                     

Lemma sub_atom_inversion : forall X, forall Q, ~sub Q (PAtom X).
Proof.
  intros X Q Hs.
  remember (PAtom X) as P.
  generalize dependent HeqP.
  induction Hs; intros HeqP; try inversion HeqP.
  apply IHHs2. auto.
Qed.

Lemma sub_unit_inversion : forall Q, ~sub Q PUnit.
Proof.
  intros Q Hs.
  remember PUnit as P.
  generalize dependent HeqP.
  induction Hs; intros HeqP; try inversion HeqP.
  apply IHHs2. auto.
Qed.

Lemma sub_zero_inversion : forall Q, ~sub Q PZero.
Proof.
  intros Q Hs.
  remember PZero as P.
  generalize dependent HeqP.
  induction Hs; intros HeqP; try inversion HeqP.
  apply IHHs2. auto.
Qed.

Lemma sub_prod_inversion : forall Q P1 P2, sub Q (PProd P1 P2) -> Q = P1 \/ Q = P2 \/ sub Q P1 \/ sub Q P2.
Proof.
  intros Q P1 P2 Hs.
  remember (PProd P1 P2) as R.
  generalize dependent P2. generalize dependent P1.
  induction Hs; intros P1 P2 HeqR; try inversion HeqR; subst; try tauto.
  - destruct (IHHs2 P1 P2 H) as [Heq|[Heq|[HSub1|HSub2]]]; subst; try tauto.
    + right. right. left. eapply s_trans. apply Hs1. assumption.
    + right. right. right. eapply s_trans. apply Hs1. assumption.
Qed.

Lemma sub_sum_inversion :  forall Q P1 P2, sub Q (PSum P1 P2) -> Q = P1 \/ Q = P2 \/ sub Q P1 \/ sub Q P2.
Proof.  
  intros Q P1 P2 Hs.
  remember (PSum P1 P2) as R.
  generalize dependent P2. generalize dependent P1.
  induction Hs; intros P1 P2 HeqR; try inversion HeqR; subst; try tauto.
  - destruct (IHHs2 P1 P2 H) as [Heq|[Heq|[HSub1|HSub2]]]; subst; try tauto.
    + right. right. left. eapply s_trans. apply Hs1. assumption.
    + right. right. right. eapply s_trans. apply Hs1. assumption.
Qed.

Lemma sub_neg_inversion : forall Q P, sub Q (PNeg P) -> Q = P \/ sub Q P.
Proof.  
  intros Q P Hs.
  remember (PNeg P) as R.
  generalize dependent P.
  induction Hs; intros P1 HeqR; try inversion HeqR; subst; try tauto.
  - destruct (IHHs2 P1 H) as [Heq|HSub1]; subst; try tauto.
    right. eapply s_trans. apply Hs1. assumption.
Qed.


Inductive hyp : Set :=
| HTriv : atom -> hyp
| HFalse : pos -> hyp
.

Definition lctx := list hyp.
Definition hasl (i:nat) (D:lctx) (h:hyp) := nth_error D i = Some h.

Inductive pat : Set :=
| p_val : pat
| p_cnt : pat
| p_unit : pat
| p_prod : pat -> pat -> pat
| p_inj1 : pat -> pat
| p_inj2 : pat -> pat
.                   

Fixpoint size (p:pat) : nat :=
  match p with
    | p_val | p_cnt => 1
    | p_unit => 0
    | p_prod p1 p2 => (size p1) + (size p2)
    | p_inj1 p1 => size p1
    | p_inj2 p2 => size p2
  end.

Inductive wf_pat : pat -> lctx -> pos -> Prop :=
| wf_p_val : forall (X:atom), wf_pat p_val [HTriv X] (PAtom X)
| wf_p_cnt : forall (P:pos), wf_pat p_cnt [HFalse P] (PNeg P)
| wf_p_unit : wf_pat p_unit [] PUnit
| wf_p_prod : forall p1 p2 D1 D2 P Q,
                wf_pat p1 D1 P ->
                wf_pat p2 D2 Q ->
                wf_pat (p_prod p1 p2) (D1 ++ D2) (PProd P Q)
| wf_p_inj1 : forall p D P Q, wf_pat p D P -> wf_pat (p_inj1 p) D (PSum P Q)
| wf_p_inj2 : forall p D P Q, wf_pat p D Q -> wf_pat (p_inj2 p) D (PSum P Q)
.

Lemma pat_size : forall p D P, wf_pat p D P -> size p = length D.
Proof.
  intros p D P Hwf.
  induction Hwf; simpl; auto.
  rewrite IHHwf1. rewrite IHHwf2.
  rewrite app_length. reflexivity.
Qed.  

Lemma proper_subformula_hfalse : forall p D P, wf_pat p D P -> forall i Q, hasl i D (HFalse Q) -> sub Q P.
Proof.
  intros p D P Hwf.
  induction Hwf; intros i Q1 Hhas; unfold hasl in Hhas.
  - destruct i; simpl in Hhas; try rewrite nth_error_nil in Hhas; try inversion Hhas.
  - destruct i; simpl in Hhas; try rewrite nth_error_nil in Hhas; try inversion Hhas.
    apply s_neg.
  - rewrite nth_error_nil in Hhas; try inversion Hhas.
  - destruct (le_lt_dec (length D1) i).
    + rewrite nth_error_app2 in Hhas.
      eapply s_trans. apply (IHHwf2 (i - length D1)). assumption.
      apply s_prod2. assumption.
    + rewrite nth_error_app1 in Hhas.
      eapply s_trans. apply (IHHwf1 i). assumption.
      apply s_prod1. assumption.
  - eapply s_trans. apply (IHHwf i). assumption.
    apply s_sum1.
  - eapply s_trans. apply (IHHwf i). assumption.
    apply s_sum2.
Qed.    

Lemma proper_subformula_htriv : forall p D P, wf_pat p D P -> forall i X, hasl i D (HTriv X) -> (sub (PAtom X) P) \/ P = (PAtom X).
Proof.
  intros p D P Hwf.
  induction Hwf; intros i X1 Hhas; unfold hasl in Hhas.
  - destruct i; simpl in Hhas; try rewrite nth_error_nil in Hhas; try inversion Hhas.
    right. reflexivity.
  - destruct i; simpl in Hhas; try rewrite nth_error_nil in Hhas; try inversion Hhas.
  - rewrite nth_error_nil in Hhas. inversion Hhas.
  - destruct (le_lt_dec (length D1) i).
    + rewrite nth_error_app2 in Hhas.
      destruct (IHHwf2 (i - length D1) X1) as [Hs | Heq]; try assumption.
      left. eapply s_trans. apply Hs. apply s_prod2.
      subst. left. apply s_prod2. assumption.
    + rewrite nth_error_app1 in Hhas.
      destruct (IHHwf1 i X1) as [Hs | Heq]; try assumption.
      left. eapply s_trans. apply Hs. apply s_prod1.
      subst. left. apply s_prod1. assumption.
  - destruct (IHHwf i X1) as [Hs | Heq]; try assumption.
    left. eapply s_trans. apply Hs. apply s_sum1.
    subst. left. apply s_sum1.
  - destruct (IHHwf i X1) as [Hs | Heq]; try assumption.
    left. eapply s_trans. apply Hs. apply s_sum2.
    subst. left. apply s_sum2.
Qed.    

Section StrongNat.
  Hypothesis P : nat -> Prop.
  Hypothesis HSub: forall n, (forall m, m < n -> P m) -> P n.
  Lemma ind_aux : forall n, P n /\ (forall m, m < n -> P m).
    induction n.
    - split.
      + apply HSub.
        intros. omega.
      + intros. omega.
    - split.
      apply HSub.
      intros.
      unfold lt in H.
      destruct (le_lt_or_eq (S m) (S n)) as [Hlt | Heq].
      assumption.
      apply IHn. omega.
      inversion Heq. subst. tauto.
      intros.
      destruct (le_lt_or_eq (S m) (S n)) as [Hlt | Heq]. omega.
      apply IHn. omega.
      inversion Heq. tauto.
  Qed.

  Lemma ind : forall n, P n.
  Proof.
    intros n.
    destruct (@ind_aux n) as [H1 H2].
    assumption.
  Qed.
End StrongNat.

Check ind.
      
Section StrongPosInduction.
  Hypothesis F : pos -> Prop.
  Hypothesis HSub : forall P, (forall Q, sub Q P -> F Q) -> F P.

  Lemma sub_induction_aux : forall P, F P /\ (forall Q, sub Q P -> F Q).
  Proof.
    induction P; auto.
    - split.
      + apply HSub.
        intros. apply sub_atom_inversion in H. inversion H.
      + intros Q Hs. apply sub_atom_inversion in Hs. inversion Hs.
    - split.
      + apply HSub.
        intros. apply sub_unit_inversion in H. inversion H.
      + intros Q Hs. apply sub_unit_inversion in Hs. inversion Hs.
    - split.
      apply HSub.
      intros Q Hs.
      destruct (sub_prod_inversion Hs) as [Heq|[Heq|[Hsub1|Hsub2]]]; subst; try tauto.
      + apply IHP1. assumption.
      + apply IHP2. assumption.
      + intros Q HS.
        destruct (sub_prod_inversion HS) as [Heq|[Heq|[Hsub1|Hsub2]]]; subst; try tauto.
        * apply IHP1. assumption.
        * apply IHP2. assumption.
    - split.
      + apply HSub.
        intros. apply sub_zero_inversion in H. inversion H.
      + intros Q Hs. apply sub_zero_inversion in Hs. inversion Hs.
    - split.
      apply HSub.
      intros Q Hs.
      destruct (sub_sum_inversion Hs) as [Heq|[Heq|[Hsub1|Hsub2]]]; subst; try tauto.
      + apply IHP1. assumption.
      + apply IHP2. assumption.
      + intros Q HS.
        destruct (sub_sum_inversion HS) as [Heq|[Heq|[Hsub1|Hsub2]]]; subst; try tauto.
        * apply IHP1. assumption.
        * apply IHP2. assumption.
    - split.
      + apply HSub.
        intros Q Hs.
        destruct (sub_neg_inversion Hs) as [Heq|Hsub1]; subst; try tauto.
        apply IHP. assumption.
      + intros Q HS.
        destruct (sub_neg_inversion HS) as [Heq|Hsub1]; subst; try tauto.
        apply IHP. assumption.
  Qed.  

  Corollary sub_induction : forall P, F P.
  Proof.
    intros P.
    destruct (@sub_induction_aux P) as [H1 H2].
    assumption.
  Qed.
End StrongPosInduction.

Check sub_induction.

Definition ctx := list lctx.
Definition has (i:nat) (G:ctx) (h:hyp) := nth_error (concat G) i = Some h.

Definition sizeG' (G:ctx) (n:nat) : nat := List.fold_left (fun acc D => acc + (length D)) G n.
Definition sizeG (G:ctx) : nat := sizeG' G 0.

Lemma len_size': forall G n m, n + sizeG' G m = sizeG' G (n+m).
Proof.
  induction G; intros n m. simpl. omega.
  simpl. rewrite IHG.
  assert ((n + (m + length a)) = (n + m + length a)).
  omega. rewrite H. reflexivity.
Qed.  

Lemma len_size: forall G D, sizeG (D::G) = (length D) + sizeG G.
Proof.
  intros G D. unfold sizeG. simpl.
  rewrite (len_size' G (length D) 0).
  rewrite plus_0_r. reflexivity.
Qed.  


Lemma hasl_app1 : forall i D1 D2 h, hasl i D1 h -> hasl i (D1 ++ D2) h.
Proof.
  intros i D1 D2 h H.
  unfold hasl.
  unfold hasl in H.
  rewrite nth_error_app1. auto.
  apply nth_error_Some. unfold not. intros. rewrite H in H0. inversion H0.
Qed.  

Lemma has_hasl_cons :
  forall G i D h,
    has i (D::G) h <-> ((i < length D) /\ hasl i D h)
                     \/ ((length D <= i) /\ has (i-(length D)) G h).
Proof.
  intros G i D h.
  unfold has. unfold hasl. split; intros; simpl in *;
  destruct (le_lt_dec (length D) i).  
  - right. split. assumption. rewrite <- nth_error_app2; assumption.
  - left. split. assumption. rewrite nth_error_app1 in H; assumption.
  - destruct H as [HD | HG].
    rewrite <- nth_error_None in l. rewrite l in HD. inversion HD. inversion H0.
    rewrite nth_error_app2; tauto.
  - destruct H as [[Hlen HD] | [Hlen HG]].
    rewrite nth_error_app1; assumption.
    omega.
Qed.
    
Lemma has_weaken_hd: forall D G i J, has i G J -> has ((length D) + i) (D :: G) J.
Proof.
  induction D; intros; simpl in *.
  unfold has. simpl. apply H.
  unfold has. simpl. rewrite <- concat_cons.
  apply IHD. exact H.
Qed.  

Lemma has_weaken_l : forall G1 G2 i J, has i G2 J -> has (sizeG G1 + i) (G1 ++ G2) J.
Proof.
  induction G1; intros G2 i J H; simpl; auto.
  unfold has. simpl. rewrite len_size.
  apply IHG1 in H.
  unfold has in H.
  rewrite nth_error_app2.
  assert (length a + sizeG G1 + i - length a = sizeG G1 + i). omega. rewrite H0. assumption.
  omega.
Qed.

Lemma has_weaken_r : forall G1 G2 i J, has i G1 J -> has i (G1 ++ G2) J.
Proof.
  intros G2 G1 i J H.
  unfold has in *.
  rewrite concat_app.
  rewrite nth_error_app1. assumption.
  apply nth_error_Some.
  unfold not. intros.
  rewrite H in H0. inversion H0.
Qed.  

Lemma hasl_has :
  forall G i D h,
    hasl i D h -> has i (D::G) h.
Proof.
  intros G i D h H.
  unfold has. simpl. rewrite nth_error_app1. assumption.
  apply nth_error_Some. unfold not. intros. unfold hasl in H. rewrite H in H0. inversion H0.
Qed.  

Lemma hasl_app_inversion :
  forall i D1 D2 h,
    hasl i (D1 ++ D2) h ->
    ((i < length D1) /\ hasl i D1 h) \/
    ((length D1 <= i) /\ hasl (i - (length D1)) D2 h).
Proof.
  intros i D1 D2 h Hhas.
  destruct (le_lt_dec (length D1) i).
  - right. split; auto.
    unfold hasl in *.
    rewrite nth_error_app2 in Hhas; auto.
  - left. split; auto.
    unfold hasl in *.
    rewrite nth_error_app1 in Hhas; auto.
Qed.
  
Lemma has_app_inversion:
  forall i G1 G2 h,
    has i (G1 ++ G2) h ->
    ((i < sizeG G1) /\ has i G1 h) \/
    ((sizeG G1) <= i /\ has (i - (sizeG G1)) G2 h).
Proof.
  intros i G1. generalize dependent i.
  induction G1; simpl; intros.
  - right. unfold sizeG. simpl. split. omega.
    assert (i-0 = i) by omega. rewrite H0. assumption.
  - unfold has in H.
    simpl in H.
    apply hasl_app_inversion in H.
    destruct H as [[Hl Hhasl]|[Hle Hhasl]].
    left. split.
    rewrite len_size. omega.
    apply hasl_has. assumption.
    destruct (IHG1 (i - length a) G2 h) as [[Hlt1 HHas]|[Hle1 HHas]].
    unfold has. apply Hhasl.
    left.
    split. rewrite len_size. omega.
    apply has_hasl_cons.
    right; tauto.
    right. split.  rewrite len_size. omega.
    assert (i - (sizeG (a::G1)) = i - length a - sizeG G1).
    rewrite len_size. omega.
    rewrite H. assumption.
Qed.    


Inductive tm : Set :=
| subst_empty : tm
| subst_cons_triv : nat -> tm -> tm
| subst_cons_false : tm -> tm -> tm
| triv : pat -> tm -> tm
| refute : (pat -> tm) -> tm
| contra : nat -> tm -> tm
.                      

Inductive judg :=
| JTriv : pos -> judg
| JFalse : pos -> judg
| JHyp : lctx -> judg
| JContra : judg
.                  

Inductive wf_tm : tm -> ctx -> judg -> Prop :=
| HypNil : forall G, wf_tm subst_empty G (JHyp [])

| HypConsTriv : forall t G D (X:atom) i,
                  has i G (HTriv X) ->
                  wf_tm t G (JHyp D) ->
                  wf_tm (subst_cons_triv i t) G (JHyp (HTriv X :: D))

| HypConsFalse : forall t1 t2 G D (P:pos),
                   wf_tm t1 G (JFalse P) ->
                   wf_tm t2 G (JHyp D) ->
                   wf_tm (subst_cons_false t1 t2) G (JHyp (HFalse P :: D))

| HypTriv : forall p t G D (P:pos),
              wf_pat p D P ->
              wf_tm t G (JHyp D) ->
              wf_tm (triv p t) G (JTriv P)

| HypFalse : forall (cases:pat -> tm) G (P:pos),
               (forall D, forall p : pat,
                  wf_pat p D P -> wf_tm (cases p) (D::G) JContra) ->
               wf_tm (refute cases) G (JFalse P)

| HypContra : forall t G (P:pos) i,
                has i G (HFalse P) ->
                wf_tm t G (JTriv P) ->
                wf_tm (contra i t) G JContra
.                                                                  

(* Weakening ---------------------------------------------------------------- *)

Lemma weakening : forall t G1 J, wf_tm t G1 J ->
                            forall G2, wf_tm t (G1++G2) J.
Proof.
  intros t G1 J Hwf.
  induction Hwf; intros.
  - apply HypNil.
  - apply HypConsTriv.
    apply has_weaken_r. assumption.
    apply IHHwf.
  - apply HypConsFalse.
    apply IHHwf1.
    apply IHHwf2.
  - apply HypTriv with (D:=D).
    assumption.
    apply IHHwf.
  - apply HypFalse.
    simpl in H0.
    intros.
    apply H0.
    assumption.
  - apply HypContra with (P:=P).
    apply has_weaken_r. assumption.
    apply IHHwf.
Qed.

Lemma weakening_cases :
  forall (cases:pat -> tm) G1 (P:pos),
    (forall D p, wf_pat p D P -> wf_tm (cases p) (D::G1) JContra) ->
    forall G2 D p, wf_pat p D P -> wf_tm (cases p) (D::(G1++G2)) JContra.
Proof.
  intros cases G1 P H G2 D p H0.
  assert (D::(G1 ++ G2) = (D::G1)++G2).
  simpl. reflexivity.
  rewrite H1.
  apply weakening.
  apply H. assumption.
Qed.  


Lemma has_weakening_nil: forall n G1 G2 j, has n (G1++G2) j -> has n (G1 ++ []::G2) j.
Proof.
  intros n G1 G2 j H.
  destruct (has_app_inversion H) as [[Hlt Hhas] | [Hle Hhas]].
  apply has_weaken_r. apply Hhas.
  assert (n = (sizeG G1 + (n - sizeG G1))). omega.
  rewrite H0. apply has_weaken_l.
  assert (n - sizeG G1 = (length ([]:lctx) + (n - sizeG G1))). simpl. reflexivity.
  rewrite H1. apply has_weaken_hd. assumption.
Qed.  
  

Lemma weakening_nil : forall t G1 G2 J, wf_tm t (G1 ++ G2) J ->
                                   wf_tm t (G1 ++ []::G2) J.
Proof.
  induction t; intros G1 G2 J Hwf; inversion Hwf; subst.
  - apply HypNil.
  - apply HypConsTriv.
    apply has_weakening_nil; auto.
    apply IHt. assumption.
  - apply HypConsFalse.
    apply IHt1; auto.
    apply IHt2; auto.
  - apply HypTriv with (D:=D); auto.
  - apply HypFalse.
    intros.
    assert (D :: G1 ++ [] :: G2 = ((D :: G1) ++ [] :: G2)).
    simpl. reflexivity.
    rewrite H2. apply H. apply H1; auto.
  - apply HypContra with (P := P).
    apply has_weakening_nil; auto.
    apply IHt; auto.
Qed.    

(* Shifting ----------------------------------------------------------------- *)

Definition shiftI (g:nat) (d:nat) (i:nat) :=
  if lt_dec i g then i else d + i.

(* Shift indices >= g by d *)
Fixpoint shift (g:nat) (d:nat) (t:tm) : tm :=
  match t with
    | subst_empty => subst_empty
    | subst_cons_triv i u => subst_cons_triv (shiftI g d i) (shift g d u)
    | subst_cons_false u1 u2 => subst_cons_false (shift g d u1) (shift g d u2)
    | triv p u => triv p (shift g d u)
    | refute cases  => refute (fun p => shift (size p + g) d (cases p))
    | contra i t => contra (shiftI g d i) (shift g d t)
  end.

Lemma shift0 : forall t g, shift g 0 t = t.
Proof.
  induction t; intros g; simpl in *; unfold shiftI; simpl; auto.
  - rewrite IHt. destruct (lt_dec n g); auto.
  - rewrite IHt1. rewrite IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - assert ((fun p:pat => shift (size p + g) 0 (t p)) = t).
    apply functional_extensionality.
    intros x. rewrite H. reflexivity.
    rewrite H0. reflexivity.
  - rewrite IHt. destruct (lt_dec n g); auto.
Qed.    

Lemma has_shiftI : forall n G1 G2 j D, has n (G1 ++ G2) j -> has (shiftI (sizeG G1) (length D) n) (G1 ++ D :: G2) j.
Proof.
  intros n G1 G2 j D H.
  destruct (has_app_inversion H) as [[Hlt Hhas] | [Hle Hhas]].
  - unfold shiftI.
    destruct (lt_dec n (sizeG G1)).
    + apply has_weaken_r. apply Hhas.
    + contradiction.
  - unfold shiftI.
    destruct (lt_dec n (sizeG G1)).
    + omega.
    + assert (length D + n = (sizeG G1 + ((length D + n) - (sizeG G1)))). omega.
      rewrite H0. apply has_weaken_l.
      assert ((length D + n - sizeG G1) = (length D + (n - sizeG G1))). omega.
      rewrite H1. apply has_weaken_hd. assumption.
Qed.      
      

Lemma shift_wf : forall t G1 G2 J,
                   wf_tm t (G1++G2) J -> forall D, wf_tm (shift (sizeG G1) (length D) t) (G1++D::G2) J.
Proof.
  induction t; intros G1 G2 J Hwf; remember (G1++G2) as G; inversion Hwf; intros D0; subst.
  - apply HypNil.
  - apply HypConsTriv.
    apply has_shiftI. assumption.
    apply IHt. assumption.
  - simpl. apply HypConsFalse.
    apply IHt1; auto.
    apply IHt2; auto.
  - simpl.
    apply HypTriv with (D:=D).
    auto.
    apply IHt; auto.
  - simpl.
    apply HypFalse.
    intros D p Hwfp.
    rewrite (pat_size Hwfp).
    rewrite <- len_size.
    assert ((D :: G1 ++ D0 :: G2) = ((D :: G1) ++ D0 :: G2)).
    simpl. reflexivity.
    rewrite H0.
    apply H.
    apply H1; auto.
  - simpl. apply HypContra with (P:=P).
    apply has_shiftI; auto.
    apply IHt; auto.
Qed.    


(* Permutations ------------------------------------------------------------- *)
Module Permutations.

Record FPerm (n:nat) (f:nat -> nat) : Set :=
  {
    inv : nat -> nat;
    linv : forall (x:nat), x < n -> inv (f x) = x;
    rinv : forall (x:nat), x < n -> f (inv x) = x;
    dom: forall x:nat, x < n -> (f x) < n;
    rng: forall x:nat, x < n -> (inv x) < n;
  }.
      
Program Definition ident : forall (n:nat), FPerm n (fun x => x).
intros n.
split with (inv := (fun x => x)); auto.
Defined.


Definition shiftP (r: nat -> nat) (d:nat) : nat -> nat :=
  fun i => if (lt_dec i d) then i else d + (r (i - d)).

Program Definition shift_perm : forall {n:nat} {r:nat -> nat} (p:FPerm n r) (d:nat),
                                  FPerm (n+d) (shiftP r d).
intros n r H d.
destruct H; intros.
  split with (inv := fun i => if lt_dec i d then i else d + (inv0 (i - d))); intros; auto.
  - unfold shiftP.
    destruct (lt_dec x d).
    + destruct (lt_dec x d ); auto.
      omega.
    + destruct (lt_dec (d + r (x - d)) d).
      * omega.
      * assert ((d + r (x - d) - d) = r (x - d)) as Heq.
        omega.
        rewrite Heq.
        rewrite linv0. omega.
        omega.
  - unfold shiftP.
    destruct (lt_dec x d).
    + destruct (lt_dec x d); auto.
      contradiction.
    + destruct (lt_dec (d + inv0 (x - d)) d).
      * omega.
      * assert ((d + inv0 (x - d) - d) = inv0 (x - d)) as Heq.
        omega.
        rewrite Heq.
        rewrite rinv0.
        omega.
        omega.
  - unfold shiftP.
    destruct (lt_dec x d).
    omega. assert (r(x - d) < n).
    apply dom0. omega.
    omega.
  - destruct (lt_dec x d).
    omega.
    assert (inv0 (x - d) < n).
    apply rng0. omega.
    omega.
Defined.

Program Definition compose_p : forall {n:nat} {r:nat -> nat} {s:nat -> nat} (p:FPerm n r) (q:FPerm n s),
                                 FPerm n (fun x => r ( s x )).
intros n r s p q.
  destruct p.
  destruct q.
  split with (inv := fun i => inv1 (inv0 i)); intros; auto.
  - rewrite linv0; auto.
  - rewrite rinv1; auto.
Defined.

Program Definition invert_p : forall {n:nat} {r:nat -> nat} (p:FPerm n r),
                                FPerm n (inv p).
Proof.
  intros n r p.
  destruct p.
  split with (inv := r); auto.
Qed.  

Lemma compose_invert_id : forall {n:nat} {r:nat -> nat} (p:FPerm n r) (x:nat),
                            (x < n) -> inv p (r x) = x.
Proof.
  intros n r p x H.
  destruct p.
  simpl.
  apply linv0.
  auto.
Qed.  


Fixpoint map_partial {A:Type} {B:Type} (f: A -> option B) (l:list A) : option (list B) :=
  match l with
    | [] => Some []
    | x::xs => match f x, map_partial f xs with
                | Some hd, Some tl => Some (hd::tl)
                | _, _ => None
              end
  end.

Definition swap (i:nat) (j:nat) (x:nat) :=
  if eq_nat_dec i x then j
  else if eq_nat_dec j x then i
       else x.

Lemma swap_swap : forall i j x, (swap i j (swap i j x)) = x.
Proof.
  intros i j x.
  unfold swap.
  destruct (eq_nat_dec i x).
  - destruct (eq_nat_dec i j).
    subst; auto.
    destruct (eq_nat_dec j j); auto.
    omega.
  - destruct (eq_nat_dec j x).
    destruct (eq_nat_dec i i); omega.
    destruct (eq_nat_dec i x).
    omega.
    destruct (eq_nat_dec j x).
    omega. omega.
Qed.    

Lemma swap_lt : forall i j x n, max i j < n -> x < n -> swap i j x < n.
Proof.
  intros i j x n Hmax H.
  unfold swap.
  destruct (eq_nat_dec i x).
  rewrite Nat.max_lub_lt_iff in Hmax.
  omega.
  destruct (eq_nat_dec j x).
  rewrite Nat.max_lub_lt_iff in Hmax.
  omega.
  assumption.
Qed.

Definition swap_p : forall (i j n:nat), (max i j) < n -> FPerm n (swap i j).
intros i j n.
split with (inv := (swap i j)); intros.
- rewrite swap_swap. reflexivity.
- rewrite swap_swap. reflexivity.
- apply swap_lt; auto.
- apply swap_lt; auto.
Defined.

(*
Lemma map_partial_total : (A:Type) (B:Type) (f: A -> option B) (l:list A)
                                   (H: forall x, In x l -> exists b, f x = Some b),
                          map_partial f l = Some
*)
Definition permute {A:Type} {r:nat -> nat} (l:list A) (p:FPerm (length l) r) : option (list A) :=
  let f (x:nat) := nth_error l (inv p x) in
  map_partial f (seq 0 (length l)).

(*
Definition foo : (max 0 2) < 3.
  simpl. omega.
Defined.  

Eval compute in (permute [1;2;3] (swap_p foo)).
*)

Fixpoint perm_tm {n:nat} {r:nat -> nat} (p:FPerm n r) (t:tm) :=
  match t with
    | subst_empty => subst_empty
    | subst_cons_triv i u => subst_cons_triv (r i) (perm_tm p u)
    | subst_cons_false t1 t2 => subst_cons_false (perm_tm p t1) (perm_tm p t2)
    | triv pt t => triv pt (perm_tm p t)
    | refute cases => refute (fun pt => perm_tm (@shift_perm _ _ p (size pt)) (cases pt))
    | contra i u => contra (r i) (perm_tm p u)
  end.

Lemma permutation : forall t G J {r:nat -> nat} (p:FPerm (sizeG G) r),
                      wf_tm t G J -> wf_tm (perm_tm p t) 

Lemma exchange : forall t G1 G2 G3 J,
                     wf_tm t (G1 ++ G2 ++ G3) J -> wf_tm (? t) (G2 ++ G1 ++ G3)

Lemma wf_lctx_cxt1: forall t D1 D2 G J, wf_tm t ((D1++D2)::G) J -> wf_tm t ([D1]++[D2]++G) J.
Proof.
  induction t; intros D1 D2 G J Hwft; inversion Hwft; subst.
  - apply HypNil.
  - apply HypConsTriv. unfold has in *. simpl in *. rewrite <- H1.
    rewrite app_assoc. reflexivity.
    apply IHt; auto.
  - apply HypConsFalse. apply IHt1; auto. apply IHt2; auto.
  - apply HypTriv with (D := D). assumption.
    apply IHt; auto.
  - apply HypFalse. intros D p Hwfp.
    simpl. simpl in H.
    apply H. 
Abort.  

Lemma shift_wf : forall D1 t G1 G2 J,
                   wf_tm t ([D2] ++ G2) J -> wf_tm (shift  (length D1) t) ((D1++D2)::G2) J.
Proof.
  induction t; intros G1 G2 J Hwf; remember (G1++G2) as G; inversion Hwf; intros D0; subst.
  - apply HypNil.
  - apply HypConsTriv.
    apply has_shiftI. assumption.
    apply IHt. assumption.
  - simpl. apply HypConsFalse.
    apply IHt1; auto.
    apply IHt2; auto.
  - simpl.
    apply HypTriv with (D:=D).
    auto.
    apply IHt; auto.
  - simpl.
    apply HypFalse.
    intros D p Hwfp.
    rewrite (pat_size Hwfp).
    rewrite <- len_size.
    assert ((D :: G1 ++ D0 :: G2) = ((D :: G1) ++ D0 :: G2)).
    simpl. reflexivity.
    rewrite H0.
    apply H.
    apply H1; auto.
  - simpl. apply HypContra with (P:=P).
    apply has_shiftI; auto.
    apply IHt; auto.
Qed.    


Fixpoint tm_len t : nat :=
  match t with
    | subst_empty => 0
    | subst_cons_triv _ t1 => 1 + (tm_len t1)
    | subst_cons_false _ t1 => 1 + (tm_len t1)
    | _ => 0 (* SHOULDN'T HAPPEN IN WELL TYPED TERMS *)
  end.

Fixpoint tm_app' d1 d2 (t u:tm) : tm :=
  match t with
    | subst_empty => shift 0 d1 u

    | subst_cons_triv i t1 =>
      subst_cons_triv (shiftI d1 d2 i) (tm_app' d1 d2 t1 u)

    | subst_cons_false t1 t2 =>
      subst_cons_false (shift d1 d2 t1) (tm_app' d1 d2 t2 u)

    | _ => subst_empty
  end.

Definition tm_app t u := tm_app' (tm_len t) (tm_len u) t u.

Lemma wf_tm_len : forall t D G, wf_tm t G (JHyp D) -> tm_len t = length D.
Proof.
  induction t; intros D G Hwf; inversion Hwf; subst; simpl in *; auto.
  - rewrite (IHt D0 G). reflexivity. auto.
  - rewrite (IHt2 D0 G); auto.
Qed.    

Lemma wf_tm_app : forall t D1 G,
                    wf_tm t (D1::G) (JHyp D1) ->
                    forall u D2, wf_tm u (D2::G) (JHyp D2) ->
                            wf_tm (tm_app' (length D1) (length D2) t u) ((D1++D2)::G) (JHyp (D1++D2)).
Proof.
  induction t; intros D1 G Hwft; inversion Hwft; subst; intros u D2 Hwfu; simpl in *.
  - rewrite shift0. assumption.
  - apply HypConsTriv.
    unfold shiftI.
    apply has_hasl_cons in H3.
    destruct H3 as [[Hlt Hhas]|[Hle Hhas]].

    + destruct (lt_dec n (S (length D))).
      * apply hasl_has.
        assert ((HTriv X :: D ++ D2) = ((HTriv X :: D) ++ D2)).
        simpl. reflexivity.
        rewrite H.
        apply hasl_app1. assumption.
      * contradiction.
    + destruct (lt_dec n (S (length D))).
      * simpl in Hle. omega.
      * assert (length D2 + n = (length (HTriv X :: D ++ D2) + (n - S (length D)))).
        simpl. rewrite app_length. omega.
        rewrite H. apply has_weaken_hd. assumption.
    + assert ((HTriv X :: D ++ D2) = ((HTriv X :: D) ++ D2)).
      simpl. reflexivity.
      rewrite H.
      assert (S (tm_len t) = length (HTriv X ::D)).
      simpl. rewrite (wf_tm_len H4). reflexivity.
      rewrite H0. apply IHt.

    
Admitted.    
    

(* Input: P : pos and p:pat 
   with the assumption that wf_pat p D P for some D 

   Output:  t:tm such that wf_tm t [D]  (JHyp D)
 *)


Program Fixpoint ctxt_ident (P:pos) (p:pat) : {t : tm | forall D G, wf_pat p D P -> wf_tm t (D::G) (JHyp D) } :=
  match P, p with
    | PAtom _, p_val => subst_cons_triv 0 subst_empty
    | PNeg Q, p_cnt => subst_cons_false (false_ident 0 Q) subst_empty 
    | PUnit, p_unit => subst_empty
    | PProd P1 P2, p_prod p1 p2 => tm_app (ctxt_ident P1 p1) (ctxt_ident P2 p2)
    | PSum P1 P2, p_inj1 p1 => ctxt_ident P1 p1
    | PSum P1 P2, p_inj2 p2 => ctxt_ident P2 p2
    | _, _ => subst_empty  (* THIS SHOULD BE UNREACHABLE assuming wf_pat p D P *)
  end
    
with false_ident (i:nat) (Q:pos) : tm :=
       refute (fun (p:pat) =>
                 match Q, p with
                   | PAtom _, p_val => contra i subst_empty
                   | PNeg Q, p_cnt => contra i subst_empty
                   | PUnit, p_unit => contra i subst_empty
                   | PProd P1 P2, p_prod p1 p2 => contra i subst_empty
                   | PSum P1 P2, p_inj1 p1 => contra i subst_empty
                   | PSum P1 P2, p_inj2 p2 => contra i subst_empty
                   | _, _ => subst_empty  (* THIS SHOULD BE UNREACHABLE assuming wf_pat p D P *)
                 end)
.


Lemma identities : forall Q G,
                     (forall i ,(has i G (HFalse Q) -> wf_tm (ident i Q) G (JFalse Q))) /\
                     (forall P, sub P Q -> forall p D, wf_pat p D P -> wf_tm (ctxt_ident P p) (D::G) (JHyp D)).
Proof.
  induction Q using sub_induction; intros G; split.
  - intros i Hhas.
    unfold ident.
    simpl. apply HFalse.

  


Lemma context_identity : forall p D P,
  wf_pat p D P -> wf_tm (ctxt_ident p) [D] (JHyp D).

Definition identity P G:=
  forall i, has i G (HFalse P) -> exists t, wf_tm t G (JFalse P).
    


Lemma expansion1 : forall t G D,
                    wf_tm t G (JHyp D) ->
                    (forall (X:atom) i, hasl i D (HTriv X) ->
                                   exists j, has j G (HTriv X)) *
                    (forall (P:pos) i, hasl i D (HFalse P) ->
                                  exists u, wf_tm u G (JFalse P)).
Proof.
  intros t G D Hwf.
  remember (JHyp D) as J. generalize dependent D.
  induction Hwf; intros D' Heq; inversion Heq; subst; split; intros h n Hhas.

  - unfold hasl in Hhas. rewrite nth_error_nil in Hhas. inversion Hhas.
  - unfold hasl in Hhas. rewrite nth_error_nil in Hhas. inversion Hhas.
  - destruct n.
    + unfold hasl in Hhas. simpl in Hhas. inversion Hhas. subst.
      exists i. assumption.
    + unfold hasl in Hhas. simpl in Hhas. apply IHHwf in Hhas.
      assumption. reflexivity.
  - destruct n.
    + unfold hasl in Hhas. simpl in Hhas. inversion Hhas.
    + unfold hasl in Hhas. simpl in Hhas. apply IHHwf in Hhas.
      assumption. reflexivity.
  - destruct n.
    + unfold hasl in Hhas. simpl in Hhas. inversion Hhas.
    + unfold hasl in Hhas. simpl in Hhas. apply IHHwf2 in Hhas.
      assumption. reflexivity.
  - destruct n.
    + unfold hasl in Hhas. simpl in Hhas. inversion Hhas. subst.
      exists t1. apply Hwf1.
    + unfold hasl in Hhas. simpl in Hhas. inversion Hhas. subst.
      destruct (IHHwf2 D) as [H1 H2].
      reflexivity.
      eapply H2. apply Hhas.
Qed.      

Lemma expansion2 : forall D G,
                     (forall (X:atom) i, hasl i D (HTriv X) -> exists j, has j G (HTriv X)) ->
                     (forall (P:pos) i, hasl i D (HFalse P) -> exists u, wf_tm u G (JFalse P)) ->
                     exists t, wf_tm t G (JHyp D).
Proof.
  induction D; intros G H1 H2.
  - exists subst_empty. apply HypNil.
  - destruct (IHD G) as [t Hwft].
    intros. apply H1 with (i:=S i). unfold hasl. simpl. assumption.
    intros. apply H2 with (i:=S i). unfold hasl. simpl. assumption.
    destruct a as [X | P].
    + destruct (H1 X 0) as [j Hhas].
      unfold hasl. simpl. reflexivity.
      exists (subst_cons_triv j t). apply HypConsTriv. apply Hhas. apply Hwft.
    + destruct (H2 P 0) as [u Hwfu].
      unfold hasl. simpl. reflexivity.
      exists (subst_cons_false u t). apply HypConsFalse; auto.
Qed.      



Lemma test : exists t, wf_tm t [[HFalse (PAtom 0)]] (JFalse (PAtom 0)).
Proof.
  eexists.
  eapply HypFalse.
  intros D p H.
  eapply HypContra with (i:=(size p)).
  rewrite (pat_size H).
  assert (length D = length D + 0).
  { omega. }
  rewrite H0.
  apply has_weaken_l with (i:=0).
  unfold has. simpl. reflexivity.
  eapply HypTriv.
  apply H.
  remember (PAtom 0) as P.
  generalize dependent HeqP.
  induction H; intros HeqP; try inversion HeqP; subst.
  apply HypConsTriv with (i:=0).
  unfold has. simpl. reflexivity.
  apply HypNil.
Qed.  

Fixpoint sh (u v:tm) := subst_empty.

Lemma hyp_merge : forall p1 D1 P1, 
                    wf_pat p1 D1 P1 ->
                  forall p2 D2 P2, wf_pat p2 D2 P2 ->
                              forall u G, wf_tm u (D1::G) (JHyp D1) ->
                                     forall v, wf_tm v (D2::G) (JHyp D2) ->
                                          wf_tm (sh u v) ((D1++D2)::G) (JHyp (D1++D2)).
Proof.
Admitted.

(*  
  intros p1 D1 P1 Hpat1.
  induction Hpat1; intros p2' D2' P2' Hpat2; induction Hpat2; intros u G Hwfu v Hwfv; simpl in *.
  - eexists.
    apply HypConsTriv.
    inversion Hwfu. subst.
    unfold has. simpl. 
*)

Definition context_identity p D P G :=
  wf_pat p D P -> exists u, wf_tm u (D::G) (JHyp D).

Definition identity P G:=
  forall i, has i G (HFalse P) -> exists t, wf_tm t G (JFalse P).

Lemma identities :
  forall P p D G,
    context_identity p D P G /\
    identity P G.
Proof.
  intros P.
  unfold context_identity. unfold identity.
  induction P using sub_induction; intros p D G.
  split.
  - intros Hwfpat.
    induction Hwfpat.
    + eexists. apply HypConsTriv with (i:=0).
      unfold has. simpl. reflexivity.
      apply HypNil.
    + destruct (H P) with (p:=p_cnt)(D:=([]:lctx))(G:=[HFalse P]::G) as [H1 H2].
      apply s_neg.
      destruct (H2 0) as [tx Ht].
      unfold has. simpl. reflexivity.
      eexists.
      apply HypConsFalse.
      apply Ht.
      apply HypNil.
    + eexists. apply HypNil.
    + apply expansion2.
      * intros X i Hhas.
        exists i.
        apply hasl_has. assumption.
      * intros R i Hhas.
        destruct (H R) with (p:=p1)(D:=D1)(G:=(D1++D2)::G) as [Ha Hb].
        apply hasl_app_inversion in Hhas.
        destruct Hhas as [[Hlen Hhas1]|[Hlen Hhas2]].
        eapply s_trans.
        eapply proper_subformula_hfalse with (P:=P).
        apply Hwfpat1. apply Hhas1.
        apply s_prod1.
        eapply s_trans.
        eapply proper_subformula_hfalse with (P:=Q).
        apply Hwfpat2.
        apply Hhas2.
        apply s_prod2.
        apply (Hb i).
        apply hasl_has. apply Hhas.
    + destruct (H P) with (p:=p)(D:=D)(G:=G) as [Ha Hb].
      apply s_sum1.
      apply Ha. assumption.
    + destruct (H Q) with (p:=p)(D:=D)(G:=G) as [Ha Hb].
      apply s_sum2.
      apply Ha. assumption.
  - intros i Hhas.
    destruct P.
    + eexists.
      eapply HypFalse.
      intros D1 p1 Hwfp1.
      eapply HypContra with (i:=(size p1)+i).
      rewrite (pat_size Hwfp1).
      apply has_weaken_l.
      apply Hhas.
      eapply HypTriv.
      apply Hwfp1.
      inversion Hwfp1. subst.
      apply HypConsTriv with (i:=0).
      unfold has. simpl. reflexivity.
      apply HypNil.
    + eexists.
      apply HypFalse.
      intros D1 p1 Hwfp1.
      eapply HypContra with (i:=(size p1)+i).
      rewrite (pat_size Hwfp1).
      apply has_weaken_l. apply Hhas.
      eapply HypTriv.
      apply Hwfp1.
      inversion Hwfp1. subst.
      apply HypNil.
    + eexists.
      apply HypFalse.
      intros D1 p1 Hwfp1.
      remember p1 as p1'.
      inversion Hwfp1. subst.
      destruct (H P1) with (p:=p0)(D:=D0)(G:=G) as [Ha Hb].
      apply s_prod1.
      destruct (Ha H4) as [u Hwfu].
      destruct (H P2) with (p:=p2)(D:=D2)(G:=G) as [Ha2 Hb2].
      apply s_prod2.
      destruct (Ha2 H5) as [v Hwfv].
      rewrite H2.
      eapply HypContra with (i:=(size p1) + i).
      rewrite (pat_size Hwfp1).
      apply has_weaken_l. apply Hhas.
      eapply HypTriv.
      apply Hwfp1.
      apply (hyp_merge H4 H5 Hwfu Hwfv).
    + exists (refute (fun p => subst_empty)).
      apply HypFalse.
      intros D1 p1 Hwfp1.
      remember p1 as p1'.
      rewrite Heqp1' in Hwfp1.
      destruct p1; inversion Hwfp1.
    + eexists (refute (fun p => contra ((size p) + i)
                                        (match p with
                                           | p_inj1 q1 => _
                                           | p_inj2 q2 => _
                                           | _ => subst_empty
                                         end)
                          )).
      apply HypFalse.
      intros D1 p1 Hwfp1.
      eapply HypContra.
      rewrite (pat_size Hwfp1).
      apply has_weaken_l. apply Hhas.
      destruct p1; inversion Hwfp1. 
      * destruct (H P1) with (p:=p1)(D:=D1)(G:=G) as [Ha Hb].
        apply s_sum1.
        destruct (Ha H3) as [u Hwfu].
        eapply HypTriv.
        apply Hwfp1.
        apply Hwfu.
        
        rewrite (pat_size H3).
        apply has_weaken_l. apply Hhas.
        eapply HypTriv.
        apply Hwfp1.      
        apply Hwfu.                                                                 
      * destruct (H P2) with (p:=p0)(D:=D1)(G:=G) as [Ha Hb].
        apply s_sum2.
        destruct (Ha H3) as [u Hwfu].
        eapply HypContra with (i:=(size p1') + i).
        rewrite Heqp1'.
        rewrite (pat_size Hwfp1).
        apply has_weaken_l. apply Hhas.
        eapply HypTriv.
        apply Hwfp1.      
        apply Hwfu.
    + eexists.
      apply HypFalse.
      intros D1 p1 Hwfp1.
      remember p1 as p1'.
      rewrite Heqp1' in Hwfp1.
      inversion Hwfp1.
      rewrite Heqp1'.
      destruct (H P) with (p:=p_cnt)(D:=D)(G:=[HFalse P]::G) as [Ha Hb].
      apply s_neg.
      destruct (Hb 0) as [uX Hwfu].
      unfold has. simpl. reflexivity.
      eapply HypContra with (i:=(size p1) + i).
      rewrite <- H0.
      unfold has. simpl.
      apply Hhas.
      eapply HypTriv.
      apply Hwfp1.
      subst.
      apply HypConsFalse. apply Hwfu.
      apply HypNil.
      
Qed.

      
      

Definition substitution :=
  forall D G J t, wf_tm t (D::G) J -> forall u, wf_tm u G (JHyp D) -> exists v, wf_tm v G J.

Lemma facts :
  forall G P,
    (forall D p, wf_pat p D P -> exists u, wf_tm u (D::G) (JHyp D)) /\
    (forall t, wf_tm t G (JFalse P)
          -> forall u, wf_tm u G (JTriv P)
                 -> exists v, wf_tm v G JContra) /\
    
Proof.
  induction G.
  - intros P. repeat split.
    + intros i Hhas. unfold has in Hhas. simpl in Hhas.
      rewrite nth_error_nil in Hhas. inversion Hhas.
    + intros D p Hwfpat.
      induction Hwfpat.
      * exists (subst_cons_triv 0 subst_empty).
          apply HypConsTriv. unfold has. simpl. reflexivity.
          apply HypNil.
      * eexists (subst_cons_false (refute (fun p => contra (size p) _)) subst_empty).
        apply HypConsFalse.
        apply HypFalse.
        intros D p Hwfpat2.
        apply HypContra with (P := P).
        rewrite pat_size with (D:=D)(P:=P).
        assert (length D = (length D) + 0). omega.
        rewrite H.
        apply has_weaken_l.
        unfold has. simpl. reflexivity.
        assumption.
        apply HypTriv with (D:=D).
        apply Hwfpat2.
        

        apply HypConsFalse.
        apply HypFalse.
        intros.
        eapply HypContra.
        
      
    + intros i Hhas.
      unfold has in Hhas. rewrite nth_error_nil in Hhas. inversion Hhas.
    + intros D p Hwfpat.
      induction Hwfpat.
      * exists (subst_cons_triv 0 subst_empty).
          apply HypConsTriv.
          unfold has. reflexivity.
          apply HypNil.
      * destruct (H P) as [H1 [H2 [H3 H4]]].
        apply s_neg.
        clear H.
        eexists (subst_cons_false (refute (fun p => contra (size p) _)) subst_empty).
        apply HypConsFalse.
        apply HypFalse.
        intros D p Hwfpat2.
        apply HypContra with (P := P).
        rewrite pat_size with (D:=D)(P:=P).
        assert (length D = (length D) + 0). omega.
        rewrite H.
        apply has_weaken_l.
        unfold has. simpl. reflexivity.
        apply Hwfpat2.
        apply HypTriv with (D:=D).
        apply Hwfpat2.
        destruct (H2 D p Hwfpat2) as [u Hwfu].
        
  
  induction G.
  - split.
    + intros i Hhas.
      unfold has in Hhas. rewrite nth_error_nil in Hhas. inversion Hhas.
    + intros D p Hwfpat.
      induction Hwfpat.
      * exists (subst_cons_triv 0 subst_empty).
          apply HypConsTriv.
          unfold has. reflexivity.
          apply HypNil.
      * destruct (H P) with (G:=([]:ctx)) as [H1 H2].
        apply s_neg.
        
  
  
  intros P i [Hctx Hhas].
  - unfold has in Hhas. simpl in Hhas. rewrite nth_error_nil in Hhas.
    inversion Hhas.
  - induction D.
    
  
Lemma context_identity : 
Proof.
  intros G D.
  apply expansion2.
  intros. exists i. apply hasl_has. assumption.
  intros.


Proof.
  induction P; induction G; intros i; split; intros; try (unfold has in H; simpl in H; rewrite nth_error_nil in H; inversion H).
  induction G; intros P i; split
  - intros H. unfold has in H. simpl in H. destruct i; simpl in H; inversion H.
  - intros D. apply expansion2.
    intros X n Hhas. exists n. unfold has. simpl.  rewrite app_nil_r. assumption.
    intros Q n Hhas. 
    
  - apply HypFalse. intros.
    eapply HypContra.
    eapply has_weaken. apply H.
    eapply HypTriv. apply p.
    generalize dependent G.
    induction p; intros.
    apply HypConsTriv with (i:=0).
    unfold has. simpl. reflexivity.
    apply HypNil.
    apply HypConsFals. apply HypFalse. intros.
    eapply HypContra with (i:=(length D)+0).
    eapply has_weaken. unfold has. simpl. reflexivity.

    Lemma has_inversion : has i (a::G) h ->
                          (
    
    
  destruct H as [D [Hin Hhas]].
  