(** Authors: Jianzhou Zhao. *)

Require Import LinF_PreLib.
Require Import LinF_ContextualEq_Def.
Require Import Coq.Arith.Max.
Require Import Coq.Arith.Compare_dec.

Lemma shift_ee_rec__open_ee_rec : forall e (x:atom) m b k,
  match (le_lt_dec b k) with
  | left _    (* b <= k *) =>   shift_ee_rec m b (open_ee_rec k x e) = open_ee_rec (k + m) x (shift_ee_rec m b e)
  | right _  (* b > k *) => shift_ee_rec m b (open_ee_rec k x e) = open_ee_rec k x (shift_ee_rec m b e)
  end.
Proof.
  induction e; intros x m b k0; simpl; subst;
    destruct (le_lt_dec b k0); try solve[
      auto |
      assert (J1 := IHe1 x m b k0);
      assert (J2 := IHe2 x m b k0);
      destruct (le_lt_dec b k0); try solve[
        rewrite J1; rewrite J2; auto |
        apply le_not_gt in l; contradict l0; auto] |
      assert (J1 := IHe1 x m b k0);
      assert (J2 := IHe2 x m b k0);
      destruct (le_lt_dec b k0); try solve[
        rewrite J1; rewrite J2; auto |
        apply le_not_gt in l0; contradict l; auto] |
      assert (J := IHe x m b k0);
      destruct (le_lt_dec b k0); try solve [
        rewrite J; auto |
        apply le_not_gt in l; contradict l0; auto] |
      assert (J := IHe x m b k0);
      destruct (le_lt_dec b k0); try solve [
        apply le_not_gt in l0; contradict l; auto |
        rewrite J; auto ]
    ].

    destruct (k0 === n); subst; simpl.
       destruct (le_lt_dec b n); subst; simpl.
         destruct (n + m === n + m); simpl; auto.
           contradict n0; auto.
           apply le_not_gt in l; contradict l0; auto.
       destruct (le_lt_dec b n); subst; simpl.
         destruct (k0 + m === n + m); simpl; auto.
           assert (k0 = n).
              clear n0. omega.
            subst. contradict n0; auto.
         destruct (k0 + m === n); simpl; auto.
            subst.
            assert (k0 < b) as EQ.
              clear l. omega.
           apply le_not_gt in l; contradict EQ; auto.

    destruct (k0 === n); subst; simpl.
       destruct (le_lt_dec b n); subst; simpl.
         destruct (n === n + m); simpl; auto.
           apply le_not_gt in l0; contradict l; auto.
           destruct (n === n); simpl; auto.
             contradict n0; auto.
       destruct (le_lt_dec b n); subst; simpl.
         destruct (k0 === n+m); simpl; auto.
            subst.
            assert (n < b) as EQ.
              clear l0. omega.
           apply le_not_gt in l0; contradict EQ; auto.
         destruct (k0 === n); simpl; auto.
            subst.
            contradict n0; auto.

      assert (J := IHe x m (S b) (S k0));
      destruct (le_lt_dec (S b) (S k0)); try solve [
        rewrite J; auto |
        apply le_not_gt in l; apply lt_S_n in l0; contradict l0; auto].

      assert (J := IHe x m (S b) (S k0));
      destruct (le_lt_dec (S b) (S k0)); try solve [
        apply le_not_gt in l0; apply lt_n_S in l; contradict l; auto |
        rewrite J; auto].
Qed.

Lemma open_shift_ee__notin_fv : forall e x n b,
  x `notin` (fv_ee e) ->
  x `notin` (fv_ee (shift_ee_rec n b e)).
Proof.
  induction e; intros x i b H; simpl in *; auto.
    destruct (le_lt_dec b n); simpl; auto.
Qed.

Lemma shift_ee_rec__open_te_rec : forall e T m b k,
  shift_ee_rec m b (open_te_rec k T e) = open_te_rec k T (shift_ee_rec m b e).
Proof.
  induction e; intros T m b k0; simpl; subst; try solve[
      auto |
      rewrite IHe1; rewrite IHe2; auto |
      rewrite IHe; auto
      ].

     destruct (le_lt_dec b n); subst; simpl; auto.
Qed.

Lemma open_te_shift_ee__notin_fv : forall e X n b,
  X `notin` (fv_te e) ->
  X `notin` (fv_te (shift_ee_rec n b e)).
Proof.
  induction e; intros X i b H; simpl in *; auto.
    destruct (le_lt_dec b n); simpl; auto.
Qed.

Lemma shift_ee_rec_expr : forall e k b,
  expr e ->
  e = shift_ee_rec k b e.
Proof.
  intros e k b H.
  generalize dependent k.
  generalize dependent b.
  induction H; intros; simpl; try solve [
    auto |
    rewrite <- IHexpr1; rewrite <- IHexpr2; auto |
    rewrite <- IHexpr; auto
    ].

    pick fresh x.
    assert (x `notin` L) as Heq. auto.
    apply H1 with (b:=S b) (k:=k) in Heq.
    unfold open_ee in Heq.
    assert (J := @shift_ee_rec__open_ee_rec e1 x k (S b) 0).
    destruct (le_lt_dec (S b) 0).
       contradict l; omega.
       rewrite J in Heq.
       apply open_ee_rec_inv in Heq; auto.
           rewrite <- Heq. auto.
           destruct_notin. 
           assert (G:=NotInTac0).
           apply open_shift_ee__notin_fv with (n:=k) (b:=S b) in G; auto.

    pick fresh X.
    assert (X `notin` L) as Heq. auto.
    apply H0 with (b:=b) (k:=k) in Heq.
    unfold open_te in Heq.
    rewrite shift_ee_rec__open_te_rec in Heq.
    apply open_te_rec_inv in Heq; auto.
       rewrite <- Heq. auto.
       destruct_notin.
       assert (G:=NotInTac). 
       apply open_te_shift_ee__notin_fv with (n:=k) (b:=b) in G; auto.       
Qed.

Lemma aux_shift_ee_rec__open_ee_rec : forall e e0 m b k,
  expr e0 ->
  match (le_lt_dec b k) with
  | left _    (* b <= k *) =>   shift_ee_rec m b (open_ee_rec k e0 e) = open_ee_rec (k + m) e0 (shift_ee_rec m b e)
  | right _  (* b > k *) => shift_ee_rec m b (open_ee_rec k e0 e) = open_ee_rec k e0 (shift_ee_rec m b e)
  end.
Proof.
  induction e; intros e0 m b k0 He0; simpl; subst;
    destruct (le_lt_dec b k0); try solve[
      auto |

      assert (J1 := IHe1 e0 m b k0); auto;
      assert (J2 := IHe2 e0 m b k0); auto;
      destruct (le_lt_dec b k0); try solve[
        rewrite J1; auto; rewrite J2; auto |
        apply le_not_gt in l; contradict l0; auto] |

      assert (J1 := IHe1 e0 m b k0); auto;
      assert (J2 := IHe2 e0 m b k0); auto;
      destruct (le_lt_dec b k0); try solve[
        rewrite J1; auto; rewrite J2; auto |
        apply le_not_gt in l0; contradict l; auto] |

      assert (J := IHe e0 m b k0); auto;
      destruct (le_lt_dec b k0); try solve [
        rewrite J; auto |
        apply le_not_gt in l; contradict l0; auto] |

      assert (J := IHe e0 m b k0); auto;
      destruct (le_lt_dec b k0); try solve [
        apply le_not_gt in l0; contradict l; auto |
        rewrite J; auto ] |

      assert (J := IHe e0 m (S b) (S k0));
      destruct (le_lt_dec (S b) (S k0)); try solve [
        rewrite J; auto |
        apply le_not_gt in l; apply lt_S_n in l0; contradict l0; auto] |

      assert (J := IHe e0 m (S b) (S k0));
      destruct (le_lt_dec (S b) (S k0)); try solve [
        apply le_not_gt in l0; apply lt_n_S in l; contradict l; auto |
        rewrite J; auto]
      ].

    destruct (k0 === n); subst; simpl.
       destruct (le_lt_dec b n); subst; simpl.
         destruct (n + m === n + m); simpl; auto.
           rewrite <- shift_ee_rec_expr; auto.          
           contradict n0; auto.
           apply le_not_gt in l; contradict l0; auto.
       destruct (le_lt_dec b n); subst; simpl.
         destruct (k0 + m === n + m); simpl; auto.
           assert (k0 = n).
              clear n0. omega.
            subst. contradict n0; auto.
         destruct (k0 + m === n); simpl; auto.
            subst.
            assert (k0 < b) as EQ.
              clear l. omega.
           apply le_not_gt in l; contradict EQ; auto.

    destruct (k0 === n); subst; simpl.
       destruct (le_lt_dec b n); subst; simpl.
         destruct (n === n + m); simpl; auto.
           rewrite <- shift_ee_rec_expr; auto.          
           apply le_not_gt in l0; contradict l; auto.
           destruct (n === n); simpl; auto.
              rewrite <- shift_ee_rec_expr; auto.          
              contradict n0; auto.
       destruct (le_lt_dec b n); subst; simpl.
         destruct (k0 === n+m); simpl; auto.
            subst.
            assert (n < b) as EQ.
              clear l0. omega.
           apply le_not_gt in l0; contradict EQ; auto.
         destruct (k0 === n); simpl; auto.
            subst.
            contradict n0; auto.
Qed.

Lemma shift_ee_expr : forall e,
  expr e ->
  e = shift_ee e.
Proof.
  intros e He.
  unfold shift_ee.
  apply shift_ee_rec_expr; auto.
Qed.

Lemma close_ee_rec_expr : forall x e k,
  x `notin` (fv_ee e) ->
  e = close_ee_rec k x e.
Proof with auto*.
  intros x e k0 Hfv. revert k0.
  induction e; intro k0; simpl in *; f_equal; auto*.
  
  destruct (x == a); subst; auto.
    destruct_notin.
    contradict Hfv; auto. 
Qed.

Lemma close_ee_expr : forall x e,
  x `notin` (fv_ee e) ->
  e = close_ee e x.
Proof.
  intros x e Fv.
  unfold close_ee.
  apply close_ee_rec_expr; auto.
Qed.

Lemma close_open_ee_rec_commut : forall e x kx ey ky,
  kx <> ky ->
  x `notin` fv_ee ey ->
  close_ee_rec kx x (open_ee_rec ky ey e) =
  open_ee_rec ky ey (close_ee_rec kx x e).
Proof.
  induction e; intros x kx ey ky xny xney; simpl; auto.
    destruct (ky==n); subst; simpl; auto.
      rewrite <- close_ee_rec_expr; auto.
       
    destruct (x==a); subst; simpl; auto.
      destruct (ky==kx); subst; simpl; auto.
         contradict xny; auto.

    rewrite IHe; auto.

    rewrite IHe1; auto.
    rewrite IHe2; auto.

    rewrite IHe; auto.

    rewrite IHe; auto.

    rewrite IHe1; auto.
    rewrite IHe2; auto.

    rewrite IHe; auto.

    rewrite IHe; auto.
Qed.  

Lemma shift_te_rec__open_ee_rec : forall e (x:atom) m b k,
  shift_te_rec m b (open_ee_rec k x e) = open_ee_rec k x (shift_te_rec m b e).
Proof.
  induction e; intros x m b k0; simpl; subst; try solve[
      auto |
      rewrite IHe1; rewrite IHe2; auto |
      rewrite IHe; auto
      ].

     destruct (k0 == n); subst; auto.
Qed.

Lemma shift_tt_rec__open_tt_rec : forall t (X:atom) m b k,
  match (le_lt_dec b k) with
  | left _    (* b <= k *) =>   shift_tt_rec m b (open_tt_rec k X t) = open_tt_rec (k + m) X (shift_tt_rec m b t)
  | right _  (* b > k *) => shift_tt_rec m b (open_tt_rec k X t) = open_tt_rec k X (shift_tt_rec m b t)
  end.
Proof.
  induction t; intros X m b k0; simpl; subst;
    destruct (le_lt_dec b k0); try solve[
      auto |
      assert (J1 := IHt1 X m b k0);
      assert (J2 := IHt2 X m b k0);
      destruct (le_lt_dec b k0); try solve[
        rewrite J1; rewrite J2; auto |
        apply le_not_gt in l; contradict l0; auto] |
      assert (J1 := IHt1 X m b k0);
      assert (J2 := IHt2 X m b k0);
      destruct (le_lt_dec b k0); try solve[
        rewrite J1; rewrite J2; auto |
        apply le_not_gt in l0; contradict l; auto] |
      assert (J := IHt X m b k0);
      destruct (le_lt_dec b k0); try solve [
        rewrite J; auto |
        apply le_not_gt in l; contradict l0; auto] |
      assert (J := IHt X m b k0);
      destruct (le_lt_dec b k0); try solve [
        apply le_not_gt in l0; contradict l; auto |
        rewrite J; auto ]
    ].

    destruct (k0 === n); subst; simpl.
       destruct (le_lt_dec b n); subst; simpl.
         destruct (n + m === n + m); simpl; auto.
           contradict n0; auto.
           apply le_not_gt in l; contradict l0; auto.
       destruct (le_lt_dec b n); subst; simpl.
         destruct (k0 + m === n + m); simpl; auto.
           assert (k0 = n).
              clear n0. omega.
            subst. contradict n0; auto.
         destruct (k0 + m === n); simpl; auto.
            subst.
            assert (k0 < b) as EQ.
              clear l. omega.
           apply le_not_gt in l; contradict EQ; auto.

    destruct (k0 === n); subst; simpl.
       destruct (le_lt_dec b n); subst; simpl.
         destruct (n === n + m); simpl; auto.
           apply le_not_gt in l0; contradict l; auto.
           destruct (n === n); simpl; auto.
             contradict n0; auto.
       destruct (le_lt_dec b n); subst; simpl.
         destruct (k0 === n+m); simpl; auto.
            subst.
            assert (n < b) as EQ.
              clear l0. omega.
           apply le_not_gt in l0; contradict EQ; auto.
         destruct (k0 === n); simpl; auto.
            subst.
            contradict n0; auto.

      assert (J := IHt X m (S b) (S k0));
      destruct (le_lt_dec (S b) (S k0)); try solve [
        rewrite J; auto |
        apply le_not_gt in l; apply lt_S_n in l0; contradict l0; auto].

      assert (J := IHt X m (S b) (S k0));
      destruct (le_lt_dec (S b) (S k0)); try solve [
        apply le_not_gt in l0; apply lt_n_S in l; contradict l; auto |
        rewrite J; auto].
Qed.

Lemma shift_te_rec__open_te_rec : forall e (X:atom) m b k,
  match (le_lt_dec b k) with
  | left _    (* b <= k *) =>   shift_te_rec m b (open_te_rec k X e) = open_te_rec (k + m) X (shift_te_rec m b e)
  | right _  (* b > k *) => shift_te_rec m b (open_te_rec k X e) = open_te_rec k X (shift_te_rec m b e)
  end.
Proof.
  induction e; intros X m b k0; simpl; subst;
    destruct (le_lt_dec b k0); try solve[
      auto |
      assert (J1 := IHe1 X m b k0);
      assert (J2 := IHe2 X m b k0);
      destruct (le_lt_dec b k0); try solve[
        rewrite J1; rewrite J2; auto |
        apply le_not_gt in l; contradict l0; auto] |
      assert (J1 := IHe1 X m b k0);
      assert (J2 := IHe2 X m b k0);
      destruct (le_lt_dec b k0); try solve[
        rewrite J1; rewrite J2; auto |
        apply le_not_gt in l0; contradict l; auto] |
      assert (J := IHe X m b k0);
      assert (J' := @shift_tt_rec__open_tt_rec t X m b k0); 
      destruct (le_lt_dec b k0); try solve [
        rewrite J; try solve [rewrite J'; auto] |
        contradict l; try solve [omega] ] |
      assert (J := IHe X m b k0);
      destruct (le_lt_dec b k0); try solve [
        apply le_not_gt in l; contradict l0; auto |
        rewrite J; auto ] |
      assert (J := IHe X m b k0);
      destruct (le_lt_dec b k0); try solve [
        rewrite J; auto |
        contradict l0; omega] |
      assert (J := IHe X m (S b) (S k0));
      destruct (le_lt_dec (S b) (S k0)); try solve [
        rewrite J; auto |
        apply le_not_gt in l; apply lt_S_n in l0; contradict l0; auto] |
      assert (J := IHe X m (S b) (S k0));
      destruct (le_lt_dec (S b) (S k0)); try solve [
        apply le_not_gt in l0; apply lt_n_S in l; contradict l; auto |
        rewrite J; auto]
    ].
Qed.

Lemma open_tt_shift_tt__notin_fv : forall t X n b,
  X `notin` (fv_tt t) ->
  X `notin` (fv_tt (shift_tt_rec n b t)).
Proof.
  induction t; intros X i b H; simpl in *; auto.
    destruct (le_lt_dec b n); simpl; auto.
Qed.

Lemma shift_tt_rec_typ : forall T k b,
  type T ->
  T = shift_tt_rec k b T.
Proof.
  intros T k b H.
  generalize dependent k.
  generalize dependent b.
  induction H; intros; simpl; try solve [
    auto |
    rewrite <- IHtype1; rewrite <- IHtype2; auto
    ].

    pick fresh X.
    assert (X `notin` L) as Heq. auto.
    apply H0 with (b:=S b) (k:=k) in Heq.
    unfold open_tt in Heq.
    assert (J := @shift_tt_rec__open_tt_rec T2 X k (S b) 0).
    rewrite J in Heq.
    apply open_tt_rec_inv in Heq; auto.
       rewrite <- Heq. auto.
       destruct_notin.
       assert (G:=NotInTac). 
       apply open_tt_shift_tt__notin_fv with (n:=k) (b:=S b) in G; auto.       
Qed.

Lemma open_shift_te__notin_fv : forall e X n b,
  X `notin` (fv_te e) ->
  X `notin` (fv_te (shift_te_rec n b e)).
Proof.
  induction e; intros X i b H; simpl in *; auto.
    destruct_notin.
    apply open_tt_shift_tt__notin_fv with (n:=i) (b:=b) in H; auto.       

    destruct_notin.
    apply open_tt_shift_tt__notin_fv with (n:=i) (b:=b) in H; auto.       
Qed.

Lemma open_ee_shift_te__notin_fv : forall e X n b,
  X `notin` (fv_ee e) ->
  X `notin` (fv_ee (shift_te_rec n b e)).
Proof.
  induction e; intros X i b H; simpl in *; auto.
Qed.

Lemma shift_te_rec_expr : forall e k b,
  expr e ->
  e = shift_te_rec k b e.
Proof.
  intros e k b H.
  generalize dependent k.
  generalize dependent b.
  induction H; intros; simpl; try solve [
    auto |
    rewrite <- IHexpr1; rewrite <- IHexpr2; auto |
    rewrite <- IHexpr; auto
    ].

    pick fresh x.
    assert (x `notin` L) as Heq. auto.
    apply H1 with (b:=b) (k:=k) in Heq.
    unfold open_ee in Heq.
    assert (J := @shift_te_rec__open_ee_rec e1 x k b 0).
    rewrite J in Heq.
    apply open_ee_rec_inv in Heq; auto.
       rewrite <- shift_tt_rec_typ; auto.
       rewrite <- Heq; auto.

       destruct_notin.
       assert (G:=NotInTac0). 
       apply open_ee_shift_te__notin_fv with (n:=k) (b:=b) in G; auto.       

    pick fresh X.
    assert (X `notin` L) as Heq. auto.
    apply H0 with (b:=S b) (k:=k) in Heq.
    unfold open_te in Heq.
    assert (J := @shift_te_rec__open_te_rec e1 X k (S b) 0).
    destruct (le_lt_dec (S b) 0).
       contradict l; omega.
       rewrite J in Heq.
       apply open_te_rec_inv in Heq; auto.
           rewrite <- Heq. auto.
           destruct_notin. 
           assert (G:=NotInTac).
           apply open_shift_te__notin_fv with (n:=k) (b:=S b) in G; auto.

    rewrite <- IHexpr.
    rewrite <- shift_tt_rec_typ; auto.
Qed.

Lemma aux_shift_te_rec__open_ee_rec : forall e e0 m b k,
  expr e0 ->
  shift_te_rec m b (open_ee_rec k e0 e) = open_ee_rec k e0 (shift_te_rec m b e).
Proof.
  induction e; intros e0 m b k0 He0; simpl; subst; try solve [
    auto |

    assert (J := IHe e0 m b (S k0)); auto;
    destruct (le_lt_dec b (S k0)); try solve [
      rewrite J; auto |
      apply le_not_gt in l; contradict l0; auto] |

    assert (J := IHe e0 m (S b) k0); auto;
    destruct (le_lt_dec (S b) k0); try solve [
      rewrite J; auto |
      apply le_not_gt in l; contradict l0; auto] |

    assert (J1 := IHe1 e0 m b k0); auto;
    assert (J2 := IHe2 e0 m b k0); auto;
    destruct (le_lt_dec b k0); try solve[
      rewrite J1; auto; rewrite J2; auto |
      apply le_not_gt in l; contradict l0; auto] |

    assert (J := IHe e0 m b k0); auto;
    destruct (le_lt_dec b k0); try solve [
      rewrite J; auto |
      apply le_not_gt in l; contradict l0; auto]

    ].

    destruct (k0 === n); subst; simpl; auto.
       destruct (le_lt_dec b n); subst; simpl.
         rewrite <- shift_te_rec_expr; auto.          
         rewrite <- shift_te_rec_expr; auto.     
Qed.

Lemma close_tt_rec_typ : forall X t k,
  X `notin` (fv_tt t) ->
  t = close_tt_rec k X t.
Proof with auto*.
  intros X t k0 Hfv. revert k0.
  induction t; intro k0; simpl in *; f_equal; auto*.
  
  destruct (X == a); subst; auto.
    destruct_notin.
    contradict Hfv; auto. 
Qed.

Lemma close_tt_typ : forall X t,
  X `notin` (fv_tt t) ->
  t = close_tt t X.
Proof.
  intros X t Fv.
  unfold close_tt.
  apply close_tt_rec_typ; auto.
Qed.

Lemma close_te_rec_expr : forall X e k,
  X `notin` (fv_te e) ->
  e = close_te_rec k X e.
Proof with auto*.
  intros X e k0 Hfv. revert k0.
  induction e; intro k0; simpl in *; f_equal; auto*.
    apply close_tt_rec_typ; auto.
    apply close_tt_rec_typ; auto.
Qed.

Lemma close_te_expr : forall X e,
  X `notin` (fv_te e) ->
  e = close_te e X.
Proof.
  intros x e Fv.
  unfold close_te.
  apply close_te_rec_expr; auto.
Qed.

Lemma close_te_open_ee_rec_commut : forall e X kX ey ky,
  X `notin` fv_te ey ->
  close_te_rec kX X (open_ee_rec ky ey e) =
  open_ee_rec ky ey (close_te_rec kX X e).
Proof.
  induction e; intros X kX ey ky Xney; simpl; auto.
    destruct (ky==n); subst; simpl; auto.
      rewrite <- close_te_rec_expr; auto.
       
    rewrite IHe; auto.

    rewrite IHe1; auto.
    rewrite IHe2; auto.

    rewrite IHe; auto.

    rewrite IHe; auto.

    rewrite IHe1; auto.
    rewrite IHe2; auto.

    rewrite IHe; auto.

    rewrite IHe; auto.
Qed.  

Lemma open_ee_rec_plug : forall C k e' e,
  expr e' ->
  disjdom ((fv_ee e') `union` (fv_te e')) (cv_ec C) ->
  open_ee_rec k e' (plug C e) =  plug (open_ec_rec k e' C) (open_ee_rec k e' e).
Proof.
  induction C; intros k0 e'0 e' He'0 Hc; simpl; 
    try solve [
      auto |
      rewrite IHC; auto
    ].

   simpl in Hc.
   rewrite IHC; auto.
     assert (J1 := @aux_shift_ee_rec__open_ee_rec e' e'0 1 0 k0 He'0); auto.
     destruct (le_lt_dec 0 k0).
       unfold shift_ee.
       assert (k0+1 = S k0) as EQ. omega. 
       rewrite <- EQ. rewrite J1. auto.

       contradict l. omega.       

   simpl in Hc.
   rewrite IHC; auto.
     assert (J1 := @aux_shift_ee_rec__open_ee_rec e' e'0 1 0 k0 He'0); auto.
     destruct (le_lt_dec 0 k0).
       unfold shift_ee.
       assert (k0+1 = S k0) as EQ. omega. 
       rewrite <- EQ. rewrite J1.
       unfold close_ee.
       rewrite <- close_open_ee_rec_commut; auto.
         omega.
       
         apply disjdom_app_1 in Hc. 
         destruct Hc as [Hc1 Hc2].
           apply Hc2. auto. 

       contradict l. omega.       

     apply disjdom_sub with (D1:=union {{a}} (cv_ec C)); auto.
        fsetdec.

   simpl in Hc.
   rewrite IHC; auto.
     assert (J1 := @aux_shift_te_rec__open_ee_rec e' e'0 1 0 k0 He'0); auto.
     unfold shift_te.
     rewrite J1. auto.

   simpl in Hc.
   rewrite IHC; auto.
     assert (J1 := @aux_shift_te_rec__open_ee_rec e' e'0 1 0 k0 He'0); auto.
     unfold shift_te.
     rewrite J1.
     unfold close_te.
     rewrite <- close_te_open_ee_rec_commut; auto.
         apply disjdom_app_2 in Hc. 
         destruct Hc as [Hc1 Hc2].
           apply Hc2. auto. 

     apply disjdom_sub with (D1:=union {{a}} (cv_ec C)); auto.
        fsetdec.
Qed.

Lemma open_ee_plug : forall C e' e,
  expr e' ->
  disjdom ((fv_ee e') `union` (fv_te e')) (cv_ec C) ->
  open_ee (plug C e)e'  =  plug (open_ec C e') (open_ee e e').
Proof.
  unfold open_ee. unfold open_ec.
  intros C e' e He'.
  apply open_ee_rec_plug; auto.
Qed.

Lemma close_ee_open_te_rec_commut : forall e x kx ty ky,
  x `notin` fv_tt ty ->
  close_ee_rec kx x (open_te_rec ky ty e) =
  open_te_rec ky ty (close_ee_rec kx x e).
Proof.
  induction e; intros x kx ey ky xnty; simpl; auto.
    destruct (x==a); subst; simpl; auto.
       
    rewrite IHe; auto.

    rewrite IHe1; auto.
    rewrite IHe2; auto.

    rewrite IHe; auto.

    rewrite IHe; auto.

    rewrite IHe1; auto.
    rewrite IHe2; auto.

    rewrite IHe; auto.

    rewrite IHe; auto.
Qed.  

Lemma aux_shift_tt_rec__open_tt_rec : forall t t0 m b k,
  type t0 ->
  match (le_lt_dec b k) with
  | left _    (* b <= k *) =>   shift_tt_rec m b (open_tt_rec k t0 t) = open_tt_rec (k + m) t0 (shift_tt_rec m b t)
  | right _  (* b > k *) => shift_tt_rec m b (open_tt_rec k t0 t) = open_tt_rec k t0 (shift_tt_rec m b t)
  end.
Proof.
  induction t; intros t0 m b k0 Ht0; simpl; subst;
    destruct (le_lt_dec b k0); try solve[
      auto |

      assert (J1 := IHt1 t0 m b k0); auto;
      assert (J2 := IHt2 t0 m b k0); auto;
      destruct (le_lt_dec b k0); try solve[
        rewrite J1; auto; rewrite J2; auto |
        apply le_not_gt in l; contradict l0; auto] |

      assert (J1 := IHt1 t0 m b k0); auto;
      assert (J2 := IHt2 t0 m b k0); auto;
      destruct (le_lt_dec b k0); try solve[
        rewrite J1; auto; rewrite J2; auto |
        apply le_not_gt in l0; contradict l; auto] |

      assert (J := IHt t0 m b k0); auto;
      destruct (le_lt_dec b k0); try solve [
        rewrite J; auto |
        apply le_not_gt in l; contradict l0; auto] |

      assert (J := IHt t0 m b k0); auto;
      destruct (le_lt_dec b k0); try solve [
        apply le_not_gt in l0; contradict l; auto |
        rewrite J; auto ] |

      assert (J := IHt t0 m (S b) (S k0));
      destruct (le_lt_dec (S b) (S k0)); try solve [
        rewrite J; auto |
        apply le_not_gt in l; apply lt_S_n in l0; contradict l0; auto] |

      assert (J := IHt t0 m (S b) (S k0));
      destruct (le_lt_dec (S b) (S k0)); try solve [
        apply le_not_gt in l0; apply lt_n_S in l; contradict l; auto |
        rewrite J; auto]
      ].

    destruct (k0 === n); subst; simpl.
       destruct (le_lt_dec b n); subst; simpl.
         destruct (n + m === n + m); simpl; auto.
           rewrite <- shift_tt_rec_typ; auto.          
           contradict n0; auto.
           apply le_not_gt in l; contradict l0; auto.
       destruct (le_lt_dec b n); subst; simpl.
         destruct (k0 + m === n + m); simpl; auto.
           assert (k0 = n).
              clear n0. omega.
            subst. contradict n0; auto.
         destruct (k0 + m === n); simpl; auto.
            subst.
            assert (k0 < b) as EQ.
              clear l. omega.
           apply le_not_gt in l; contradict EQ; auto.

    destruct (k0 === n); subst; simpl.
       destruct (le_lt_dec b n); subst; simpl.
         destruct (n === n + m); simpl; auto.
           rewrite <- shift_tt_rec_typ; auto.          
           apply le_not_gt in l0; contradict l; auto.
           destruct (n === n); simpl; auto.
              rewrite <- shift_tt_rec_typ; auto.          
              contradict n0; auto.
       destruct (le_lt_dec b n); subst; simpl.
         destruct (k0 === n+m); simpl; auto.
            subst.
            assert (n < b) as EQ.
              clear l0. omega.
           apply le_not_gt in l0; contradict EQ; auto.
         destruct (k0 === n); simpl; auto.
            subst.
            contradict n0; auto.
Qed.

Lemma aux_shift_te_rec__open_te_rec : forall e t0 m b k,
  type t0 ->
  match (le_lt_dec b k) with
  | left _    (* b <= k *) =>   shift_te_rec m b (open_te_rec k t0 e) = open_te_rec (k + m) t0 (shift_te_rec m b e)
  | right _  (* b > k *) => shift_te_rec m b (open_te_rec k t0 e) = open_te_rec k t0 (shift_te_rec m b e)
  end.
Proof.
  induction e; intros t0 m b k0 Ht0; simpl; subst; try solve [
    auto |

    assert (J := IHe t0 m b k0); auto;
    assert (J' := @aux_shift_tt_rec__open_tt_rec  t t0 m b k0); auto;
    destruct (le_lt_dec b k0); try solve [
            rewrite J; auto; try solve [rewrite J'; auto]] |

    assert (J := IHe t0 m b k0); auto;
    destruct (le_lt_dec b k0); try solve [
      rewrite J; auto |
      apply le_not_gt in l; contradict l0; auto] |

    assert (J1 := IHe1 t0 m b k0); auto;
    assert (J2 := IHe2 t0 m b k0); auto;
    destruct (le_lt_dec b k0); try solve[
      rewrite J1; auto; rewrite J2; auto |
      apply le_not_gt in l; contradict l0; auto]
    ].

    destruct (le_lt_dec b k0); subst; simpl; auto.
    destruct (le_lt_dec b k0); subst; simpl; auto.

    assert (J := IHe t0 m (S b) (S k0)); auto.
    destruct (le_lt_dec b k0).
      destruct (le_lt_dec (S b) (S k0)).
         rewrite J; auto.
         contradict l. omega. 
      destruct (le_lt_dec (S b) (S k0)).
         contradict l. omega. 
         rewrite J; auto.
Qed.    

Lemma close_open_tt_rec_commut : forall t X kX tY kY,
  kX <> kY ->
  X `notin` fv_tt tY ->
  close_tt_rec kX X (open_tt_rec kY tY t) =
  open_tt_rec kY tY (close_tt_rec kX X t).
Proof.
  induction t; intros X kX tY kY XnY XntY; simpl; auto.
    destruct (kY==n); subst; simpl; auto.
      rewrite <- close_tt_rec_typ; auto.
       
    destruct (X==a); subst; simpl; auto.
      destruct (kY==kX); subst; simpl; auto.
         contradict XnY; auto.

    rewrite IHt1; auto.
    rewrite IHt2; auto.

    rewrite IHt; auto.

    rewrite IHt1; auto.
    rewrite IHt2; auto.
Qed.  

Lemma close_open_te_rec_commut : forall e X kX ty ky,
  kX <> ky ->
  X `notin` fv_tt ty ->
  close_te_rec kX X (open_te_rec ky ty e) =
  open_te_rec ky ty (close_te_rec kX X e).
Proof.
  induction e; intros X kX ty ky Xny Xnty; simpl; auto.
    rewrite IHe; auto.
    rewrite close_open_tt_rec_commut; auto.

    rewrite IHe1; auto.
    rewrite IHe2; auto.

    rewrite IHe; auto.

    rewrite IHe; auto.
    rewrite close_open_tt_rec_commut; auto.

    rewrite IHe1; auto.
    rewrite IHe2; auto.

    rewrite IHe; auto.

    rewrite IHe; auto.
Qed.  

Lemma open_te_rec_plug : forall C k t e,
  type t ->
  disjdom (fv_tt t) (cv_ec C) ->
  open_te_rec k t (plug C e) =  plug (open_tc_rec k t C) (open_te_rec k t e).
Proof.
  induction C; intros k0 t0 e0 Ht0 Hc; simpl; 
    try solve [
      auto |
      rewrite IHC; auto
    ].

   simpl in Hc.
   rewrite IHC; auto.
     assert (J1 := @shift_ee_rec__open_te_rec e0 t0 1 0 k0).
     unfold shift_ee.
     rewrite J1. auto.

   simpl in Hc.
   rewrite IHC; auto.
     assert (J1 := @shift_ee_rec__open_te_rec e0 t0 1 0 k0).
     unfold shift_ee.
     rewrite J1.
     unfold close_ee.
     rewrite <- close_ee_open_te_rec_commut; auto.
       destruct Hc as [Hc1 Hc2].
         apply Hc2. auto. 

     apply disjdom_sub with (D1:=union {{a}} (cv_ec C)); auto.
        fsetdec.

   simpl in Hc.
   rewrite IHC; auto.
     assert (J1 := @aux_shift_te_rec__open_te_rec e0 t0 1 0 k0 Ht0); auto.
     destruct (le_lt_dec 0 (S k0)).
       unfold shift_te.
       rewrite J1.
       assert (k0 + 1 = S k0) as EQ. omega.
       rewrite EQ. auto.

       contradict l. omega.

   simpl in Hc.
   rewrite IHC; auto.
     assert (J1 := @aux_shift_te_rec__open_te_rec e0 t0 1 0 k0 Ht0); auto.
     destruct (le_lt_dec 0 (S k0)).
       unfold shift_te.
       unfold close_te.
       rewrite J1.
       assert (k0 + 1 = S k0) as EQ. omega.
       rewrite EQ.
       rewrite <- close_open_te_rec_commut; auto.
         destruct Hc as [Hc1 Hc2].
           apply Hc2. auto. 

       contradict l. omega.

     apply disjdom_sub with (D1:=union {{a}} (cv_ec C)); auto.
        fsetdec.
Qed.

Lemma open_te_plug : forall C t e,
  type t ->
  disjdom (fv_tt t) (cv_ec C) ->
  open_te (plug C e) t  =  plug (open_tc C t) (open_te e t).
Proof.
  unfold open_te. unfold open_tc.
  intros C t e Ht.
  apply open_te_rec_plug; auto.
Qed.

Lemma close_ee_commut : forall e x kx y ky,
  x <> y ->
  close_ee_rec kx x (close_ee_rec ky y e) =
  close_ee_rec ky y (close_ee_rec kx x e).
Proof.
  induction e; intros x kx y ky xny; simpl; auto.
    destruct (y==a); subst.
      destruct (x==a); subst.
        contradict xny; auto.
        simpl.
        destruct (a==a); auto.
          contradict n0; auto.
 
      destruct (x==a); subst.
        simpl.
        destruct (a==a); auto.
          contradict n0; auto.

        simpl.
        destruct (y==a); subst; auto.
          contradict n; auto.
        destruct (x==a); subst; auto.
          contradict n0; auto.

    rewrite IHe; auto.
    rewrite IHe1;auto. rewrite IHe2; auto.
    rewrite IHe; auto.
    rewrite IHe; auto.
    rewrite IHe1;auto. rewrite IHe2; auto.
    rewrite IHe; auto.
    rewrite IHe; auto.
Qed.

Lemma open_ee_rec_exp_size_eq : forall (x : atom) e k,
  exp_size (open_ee_rec k (exp_fvar x) e) = exp_size e.
Proof.
  (exp_cases (induction e) Case); intros k0; simpl; auto.
  Case "exp_bvar".
    destruct (k0 === n); simpl; auto.
Qed.

Lemma open_ee_exp_size_eq : forall (x : atom) e,
  exp_size (open_ee e x) = exp_size e.
Proof.
  unfold open_ee.
  auto using open_ee_rec_exp_size_eq.
Qed.

Lemma open_ee_bexp_eupper : forall e k (x:atom),
  bexp_eupper (open_ee_rec k x e) <= bexp_eupper e.
Proof.
  induction e; intros k0 x; simpl.
    destruct (k0==n); subst; simpl; omega.

    omega.

    assert (J:=@IHe (S k0) x). omega.

    assert (J1:=@IHe1 k0 x). 
    assert (J2:=@IHe2 k0 x). 
    apply max_injective; auto.

    assert (J:=@IHe k0 x). omega.

    assert (J:=@IHe k0 x). omega.

    assert (J1:=@IHe1 k0 x). 
    assert (J2:=@IHe2 k0 x). 
    apply max_injective; auto.

    assert (J:=@IHe k0 x). omega.

    assert (J:=@IHe k0 x). omega.
Qed.

Lemma bexp_eupper_open_ee_rec_inv : forall e k (x:atom) i,
  bexp_eupper (open_ee_rec k x e)  = i ->
  bexp_eupper e = k +1 \/ bexp_eupper e = i.
Proof.
  induction e; intros kk x i EQ; simpl in *; auto.
    destruct (kk == n); subst; auto.

    destruct (le_lt_dec (bexp_eupper (open_ee_rec (S kk) x e)) 0).
      assert (bexp_eupper (open_ee_rec (S kk) x e) = 0) as EQ'.
        omega.
      rewrite EQ' in *.
      assert (i = 0) as J. omega.
      subst. clear l J.
      apply IHe in EQ'.
      destruct EQ' as [J | J].
      left. rewrite J. omega.
      right. rewrite J. omega.

      assert (bexp_eupper (open_ee_rec (S kk) x e)  = i  + 1) as EQ'.
         rewrite <- EQ.
        omega.
      apply IHe in EQ'.
      destruct EQ' as [J | J].
      left. rewrite J. omega.
      right. rewrite J. omega.

    destruct (@max_dec (bexp_eupper (open_ee_rec kk x e1)) (bexp_eupper (open_ee_rec kk x e2))) as [J | J].
      rewrite J in EQ.
      assert ((bexp_eupper (open_ee_rec kk x e2))<= (bexp_eupper (open_ee_rec kk x e1))) as J'.
        rewrite <- J.
        apply le_max_r.
      remember (bexp_eupper (open_ee_rec kk x e2)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHe1 in EQ.
      symmetry in Heqi'.
      apply IHe2 in Heqi'.
      destruct EQ as [EQ1 | EQ1].
        destruct Heqi' as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          left. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          left. apply max_l.
            assert (J''':=@open_ee_bexp_eupper e1 kk x).
            omega.
        destruct Heqi' as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          destruct (le_lt_dec i (kk+1)).
             left. apply max_r. auto.
             right. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          right. apply max_l. auto.

      rewrite J in EQ.
      assert ((bexp_eupper (open_ee_rec kk x e1))<= (bexp_eupper (open_ee_rec kk x e2))) as J'.
        rewrite <- J.
        apply le_max_l.
      remember (bexp_eupper (open_ee_rec kk x e1)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHe2 in EQ.
      symmetry in Heqi'.
      apply IHe1 in Heqi'.
      destruct EQ as [EQ2 | EQ2].
        destruct Heqi' as [EQ1 | EQ1].
          rewrite EQ1. rewrite EQ2.
          left. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          left. apply max_r.
            assert (J''':=@open_ee_bexp_eupper e2 kk x).
            omega.
        destruct Heqi' as [EQ1 | EQ1].
          rewrite EQ1. rewrite EQ2.
          destruct (le_lt_dec i (kk+1)).
             left. apply max_l. auto.
             right. apply max_r. omega.

          rewrite EQ1. rewrite EQ2.
          right. apply max_r. auto.
    
    apply IHe in EQ.
    destruct EQ as [J | J].
    left. rewrite J. omega.
    right. rewrite J. omega.

    apply IHe in EQ.
    destruct EQ as [J | J].
    left. rewrite J. omega.
    right. rewrite J. omega.

    destruct (@max_dec (bexp_eupper (open_ee_rec kk x e1)) (bexp_eupper (open_ee_rec kk x e2))) as [J | J].
      rewrite J in EQ.
      assert ((bexp_eupper (open_ee_rec kk x e2))<= (bexp_eupper (open_ee_rec kk x e1))) as J'.
        rewrite <- J.
        apply le_max_r.
      remember (bexp_eupper (open_ee_rec kk x e2)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHe1 in EQ.
      symmetry in Heqi'.
      apply IHe2 in Heqi'.
      destruct EQ as [EQ1 | EQ1].
        destruct Heqi' as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          left. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          left. apply max_l.
            assert (J''':=@open_ee_bexp_eupper e1 kk x).
            omega.
        destruct Heqi' as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          destruct (le_lt_dec i (kk+1)).
             left. apply max_r. auto.
             right. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          right. apply max_l. auto.

      rewrite J in EQ.
      assert ((bexp_eupper (open_ee_rec kk x e1))<= (bexp_eupper (open_ee_rec kk x e2))) as J'.
        rewrite <- J.
        apply le_max_l.
      remember (bexp_eupper (open_ee_rec kk x e1)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHe2 in EQ.
      symmetry in Heqi'.
      apply IHe1 in Heqi'.
      destruct EQ as [EQ2 | EQ2].
        destruct Heqi' as [EQ1 | EQ1].
          rewrite EQ1. rewrite EQ2.
          left. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          left. apply max_r.
            assert (J''':=@open_ee_bexp_eupper e2 kk x).
            omega.
        destruct Heqi' as [EQ1 | EQ1].
          rewrite EQ1. rewrite EQ2.
          destruct (le_lt_dec i (kk+1)).
             left. apply max_l. auto.
             right. apply max_r. omega.

          rewrite EQ1. rewrite EQ2.
          right. apply max_r. auto.
        
    apply IHe in EQ.
    destruct EQ as [J | J].
    left. rewrite J. omega.
    right. rewrite J. omega.

    apply IHe in EQ.
    destruct EQ as [J | J].
    left. rewrite J. omega.
    right. rewrite J. omega.
Qed.

Lemma bexp_eupper__open_te_rec : forall e kk X,
  bexp_eupper e = bexp_eupper (open_te_rec kk X e).
Proof.
  induction e; intros kk X; simpl; auto.
Qed.  

Lemma expr_bexp_eupper : forall e,
  expr e ->
  bexp_eupper e = 0.
Proof.
  intros e He.
  induction He; simpl; auto.
    pick fresh x.
    assert (x `notin` L) as xnL. auto.
    apply H1 in xnL; auto.
    apply bexp_eupper_open_ee_rec_inv in xnL.
    destruct xnL as [J | J].
      rewrite J.  omega.
      rewrite J.  omega.

   rewrite IHHe1. rewrite IHHe2.
   apply max_l. auto.

    pick fresh X.
    assert (X `notin` L) as XnL. auto.
    apply H0 in XnL; auto.
    unfold open_te in XnL.
    rewrite <- bexp_eupper__open_te_rec in XnL.
    assumption.

   rewrite IHHe1. rewrite IHHe2.
   apply max_l. auto.
Qed.

Lemma close_open_ee_rec__subst_ee : forall e x y k,
  bexp_eupper e <= k ->
  open_ee_rec k y (close_ee_rec k x e) = subst_ee x y e.
Proof.
  induction e; intros x y k0 Hup; simpl; simpl in Hup; auto.
    destruct (k0==n); subst; auto.
      contradict Hup.
      omega.

    destruct (x==a); subst.
      destruct (a==a).
        simpl.
        destruct (k0==k0); auto.
          contradict n; auto.
        contradict n; auto.
      destruct (a==x); subst.
        contradict n; auto.
        simpl. auto.

    rewrite IHe; auto.
    omega.

    rewrite IHe1; auto.
    rewrite IHe2; auto.
    assert (J:=@le_max_r (bexp_eupper e1) (bexp_eupper e2)).  omega.
    assert (J:=@le_max_l (bexp_eupper e1) (bexp_eupper e2)).  omega.

    rewrite IHe; auto.

    rewrite IHe; auto.

    rewrite IHe1; auto.
    rewrite IHe2; auto.
    assert (J:=@le_max_r (bexp_eupper e1) (bexp_eupper e2)).  omega.
    assert (J:=@le_max_l (bexp_eupper e1) (bexp_eupper e2)).  omega.

    rewrite IHe; auto.

    rewrite IHe; auto.
Qed.    

Lemma close_open_ee__subst_ee : forall e x y,
  expr e ->
  open_ee (close_ee e x) y = subst_ee x y e.
Proof.
  intros e x y He.
  unfold open_ee.
  unfold close_ee.
  apply close_open_ee_rec__subst_ee; auto.
    rewrite expr_bexp_eupper; auto.
Qed.

Lemma open_ec_bctx_eupper : forall C k (x:atom),
  bctx_eupper (open_ec_rec k x C) <= bctx_eupper C.
Proof.
  induction C; intros k0 x; simpl; 
  try solve [
    auto |
    assert (J:=@IHC (S k0) x); omega |
    assert (J1:=@IHC k0 x);
    assert (J2:=@open_ee_bexp_eupper e k0 x);
    apply max_injective; auto
  ].
Qed.

Lemma bctx_eupper_open_ec_rec_inv : forall C k (x:atom) i,
  bctx_eupper (open_ec_rec k x C)  = i ->
  bctx_eupper C = k +1 \/ bctx_eupper C = i.
Proof.
  induction C; intros kk x i EQ; simpl in *; auto.
    destruct (le_lt_dec (bctx_eupper (open_ec_rec (S kk) x C)) 0).
      assert (bctx_eupper (open_ec_rec (S kk) x C) = 0) as EQ'.
        omega.
      rewrite EQ' in *.
      assert (i = 0) as J. omega.
      subst. clear l J.
      apply IHC in EQ'.
      destruct EQ' as [J | J].
      left. rewrite J. omega.
      right. rewrite J. omega.

      assert (bctx_eupper (open_ec_rec (S kk) x C)  = i  + 1) as EQ'.
         rewrite <- EQ.
        omega.
      apply IHC in EQ'.
      destruct EQ' as [J | J].
      left. rewrite J. omega.
      right. rewrite J. omega.

    destruct (le_lt_dec (bctx_eupper (open_ec_rec (S kk) x C)) 0).
      assert (bctx_eupper (open_ec_rec (S kk) x C) = 0) as EQ'.
        omega.
      rewrite EQ' in *.
      assert (i = 0) as J. omega.
      subst. clear l J.
      apply IHC in EQ'.
      destruct EQ' as [J | J].
      left. rewrite J. omega.
      right. rewrite J. omega.

      assert (bctx_eupper (open_ec_rec (S kk) x C)  = i  + 1) as EQ'.
         rewrite <- EQ.
        omega.
      apply IHC in EQ'.
      destruct EQ' as [J | J].
      left. rewrite J. omega.
      right. rewrite J. omega.

    destruct (@max_dec (bctx_eupper (open_ec_rec kk x C)) (bexp_eupper (open_ee_rec kk x e))) as [J | J].
      rewrite J in EQ.
      assert ((bexp_eupper (open_ee_rec kk x e))<= (bctx_eupper (open_ec_rec kk x C))) as J'.
        rewrite <- J.
        apply le_max_r.
      remember (bexp_eupper (open_ee_rec kk x e)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHC in EQ.
      symmetry in Heqi'.
      apply bexp_eupper_open_ee_rec_inv in Heqi'.
      destruct EQ as [EQ1 | EQ1].
        destruct Heqi' as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          left. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          left. apply max_l.
            assert (J''':=@open_ec_bctx_eupper C kk x).
            omega.
        destruct Heqi' as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          destruct (le_lt_dec i (kk+1)).
             left. apply max_r. auto.
             right. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          right. apply max_l. auto.

      rewrite J in EQ.
      assert ((bctx_eupper (open_ec_rec kk x C))<= (bexp_eupper (open_ee_rec kk x e))) as J'.
        rewrite <- J.
        apply le_max_l.
      remember (bctx_eupper (open_ec_rec kk x C)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply bexp_eupper_open_ee_rec_inv in EQ.
      symmetry in Heqi'.
      apply IHC in Heqi'.
      destruct EQ as [EQ2 | EQ2].
        destruct Heqi' as [EQ1 | EQ1].
          rewrite EQ1. rewrite EQ2.
          left. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          left. apply max_r.
            assert (J''':=@open_ee_bexp_eupper e kk x).
            omega.
        destruct Heqi' as [EQ1 | EQ1].
          rewrite EQ1. rewrite EQ2.
          destruct (le_lt_dec i (kk+1)).
             left. apply max_l. auto.
             right. apply max_r. omega.

          rewrite EQ1. rewrite EQ2.
          right. apply max_r. auto.
    
    destruct (@max_dec (bexp_eupper (open_ee_rec kk x e)) (bctx_eupper (open_ec_rec kk x C))) as [J | J].
      rewrite J in EQ.
      assert ((bctx_eupper (open_ec_rec kk x C))<= (bexp_eupper (open_ee_rec kk x e))) as J'.
        rewrite <- J.
        apply le_max_r.
      remember (bctx_eupper (open_ec_rec kk x C)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply bexp_eupper_open_ee_rec_inv in EQ.
      symmetry in Heqi'.
      apply IHC in Heqi'.
      destruct EQ as [EQ2 | EQ2].
        destruct Heqi' as [EQ1 | EQ1].
          rewrite EQ1. rewrite EQ2.
          left. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          left. apply max_l.
            assert (J''':=@open_ee_bexp_eupper e kk x).
            omega.
        destruct Heqi' as [EQ1 | EQ1].
          rewrite EQ1. rewrite EQ2.
          destruct (le_lt_dec i (kk+1)).
             left. apply max_r. auto.
             right. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          right. apply max_l. auto.

      rewrite J in EQ.
      assert ((bexp_eupper (open_ee_rec kk x e))<= (bctx_eupper (open_ec_rec kk x C))) as J'.
        rewrite <- J.
        apply le_max_l.
      remember (bexp_eupper (open_ee_rec kk x e)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHC in EQ.
      symmetry in Heqi'.
      apply bexp_eupper_open_ee_rec_inv in Heqi'.
      destruct EQ as [EQ1 | EQ1].
        destruct Heqi' as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          left. apply max_r. omega.

          rewrite EQ1. rewrite EQ2.
          left. apply max_r.
            assert (J''':=@open_ec_bctx_eupper C kk x).
            omega.
        destruct Heqi' as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          destruct (le_lt_dec i (kk+1)).
             left. apply max_l. auto.
             right. apply max_r. omega.

          rewrite EQ1. rewrite EQ2.
          right. apply max_r. auto.

    apply IHC in EQ.
    destruct EQ as [J | J].
    left. rewrite J. omega.
    right. rewrite J. omega.

    apply IHC in EQ.
    destruct EQ as [J | J].
    left. rewrite J. omega.
    right. rewrite J. omega.

    apply IHC in EQ.
    destruct EQ as [J | J].
    left. rewrite J. omega.
    right. rewrite J. omega.

    destruct (@max_dec (bctx_eupper (open_ec_rec kk x C)) (bexp_eupper (open_ee_rec kk x e))) as [J | J].
      rewrite J in EQ.
      assert ((bexp_eupper (open_ee_rec kk x e))<= (bctx_eupper (open_ec_rec kk x C))) as J'.
        rewrite <- J.
        apply le_max_r.
      remember (bexp_eupper (open_ee_rec kk x e)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHC in EQ.
      symmetry in Heqi'.
      apply bexp_eupper_open_ee_rec_inv in Heqi'.
      destruct EQ as [EQ1 | EQ1].
        destruct Heqi' as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          left. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          left. apply max_l.
            assert (J''':=@open_ec_bctx_eupper C kk x).
            omega.
        destruct Heqi' as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          destruct (le_lt_dec i (kk+1)).
             left. apply max_r. auto.
             right. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          right. apply max_l. auto.

      rewrite J in EQ.
      assert ((bctx_eupper (open_ec_rec kk x C))<= (bexp_eupper (open_ee_rec kk x e))) as J'.
        rewrite <- J.
        apply le_max_l.
      remember (bctx_eupper (open_ec_rec kk x C)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply bexp_eupper_open_ee_rec_inv in EQ.
      symmetry in Heqi'.
      apply IHC in Heqi'.
      destruct EQ as [EQ2 | EQ2].
        destruct Heqi' as [EQ1 | EQ1].
          rewrite EQ1. rewrite EQ2.
          left. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          left. apply max_r.
            assert (J''':=@open_ee_bexp_eupper e kk x).
            omega.
        destruct Heqi' as [EQ1 | EQ1].
          rewrite EQ1. rewrite EQ2.
          destruct (le_lt_dec i (kk+1)).
             left. apply max_l. auto.
             right. apply max_r. omega.

          rewrite EQ1. rewrite EQ2.
          right. apply max_r. auto.
    
    destruct (@max_dec (bexp_eupper (open_ee_rec kk x e)) (bctx_eupper (open_ec_rec kk x C))) as [J | J].
      rewrite J in EQ.
      assert ((bctx_eupper (open_ec_rec kk x C))<= (bexp_eupper (open_ee_rec kk x e))) as J'.
        rewrite <- J.
        apply le_max_r.
      remember (bctx_eupper (open_ec_rec kk x C)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply bexp_eupper_open_ee_rec_inv in EQ.
      symmetry in Heqi'.
      apply IHC in Heqi'.
      destruct EQ as [EQ2 | EQ2].
        destruct Heqi' as [EQ1 | EQ1].
          rewrite EQ1. rewrite EQ2.
          left. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          left. apply max_l.
            assert (J''':=@open_ee_bexp_eupper e kk x).
            omega.
        destruct Heqi' as [EQ1 | EQ1].
          rewrite EQ1. rewrite EQ2.
          destruct (le_lt_dec i (kk+1)).
             left. apply max_r. auto.
             right. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          right. apply max_l. auto.

      rewrite J in EQ.
      assert ((bexp_eupper (open_ee_rec kk x e))<= (bctx_eupper (open_ec_rec kk x C))) as J'.
        rewrite <- J.
        apply le_max_l.
      remember (bexp_eupper (open_ee_rec kk x e)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHC in EQ.
      symmetry in Heqi'.
      apply bexp_eupper_open_ee_rec_inv in Heqi'.
      destruct EQ as [EQ1 | EQ1].
        destruct Heqi' as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          left. apply max_r. omega.

          rewrite EQ1. rewrite EQ2.
          left. apply max_r.
            assert (J''':=@open_ec_bctx_eupper C kk x).
            omega.
        destruct Heqi' as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          destruct (le_lt_dec i (kk+1)).
             left. apply max_l. auto.
             right. apply max_r. omega.

          rewrite EQ1. rewrite EQ2.
          right. apply max_r. auto.
        
    apply IHC in EQ.
    destruct EQ as [J | J].
    left. rewrite J. omega.
    right. rewrite J. omega.

    apply IHC in EQ.
    destruct EQ as [J | J].
    left. rewrite J. omega.
    right. rewrite J. omega.
Qed.

Lemma bexp_eupper_open_te_rec_inv : forall e k (X:atom) i,
  bexp_eupper (open_te_rec k X e)  = i ->
  bexp_eupper e = i.
Proof.
  induction e; intros kk X i EQ; simpl in *; auto.
    destruct (le_lt_dec (bexp_eupper (open_te_rec kk X e)) 0).
      assert (bexp_eupper (open_te_rec kk X e) = 0) as EQ'.
        omega.
      rewrite EQ' in *.
      assert (i = 0) as J. omega.
      subst. clear l J.
      apply IHe in EQ'.
      rewrite EQ'. omega.

      assert (bexp_eupper (open_te_rec kk X e)  = i  + 1) as EQ'.
         rewrite <- EQ.
        omega.
      apply IHe in EQ'.
      rewrite EQ'. omega.

    destruct (@max_dec (bexp_eupper (open_te_rec kk X e1)) (bexp_eupper (open_te_rec kk X e2))) as [J | J].
      rewrite J in EQ.
      assert ((bexp_eupper (open_te_rec kk X e2))<= (bexp_eupper (open_te_rec kk X e1))) as J'.
        rewrite <- J.
        apply le_max_r.
      remember (bexp_eupper (open_te_rec kk X e2)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHe1 in EQ.
      symmetry in Heqi'.
      apply IHe2 in Heqi'.
      rewrite EQ. rewrite Heqi'.
      apply max_l. assumption.

      rewrite J in EQ.
      assert ((bexp_eupper (open_te_rec kk X e1))<= (bexp_eupper (open_te_rec kk X e2))) as J'.
        rewrite <- J.
        apply le_max_l.
      remember (bexp_eupper (open_te_rec kk X e1)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHe2 in EQ.
      symmetry in Heqi'.
      apply IHe1 in Heqi'.
      rewrite EQ. rewrite Heqi'.
      apply max_r. assumption.
    
    apply IHe in EQ. assumption.

    apply IHe in EQ. assumption.

    destruct (@max_dec (bexp_eupper (open_te_rec kk X e1)) (bexp_eupper (open_te_rec kk X e2))) as [J | J].
      rewrite J in EQ.
      assert ((bexp_eupper (open_te_rec kk X e2))<= (bexp_eupper (open_te_rec kk X e1))) as J'.
        rewrite <- J.
        apply le_max_r.
      remember (bexp_eupper (open_te_rec kk X e2)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHe1 in EQ.
      symmetry in Heqi'.
      apply IHe2 in Heqi'.
      rewrite EQ. rewrite Heqi'.
      apply max_l. assumption.

      rewrite J in EQ.
      assert ((bexp_eupper (open_te_rec kk X e1))<= (bexp_eupper (open_te_rec kk X e2))) as J'.
        rewrite <- J.
        apply le_max_l.
      remember (bexp_eupper (open_te_rec kk X e1)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHe2 in EQ.
      symmetry in Heqi'.
      apply IHe1 in Heqi'.
      rewrite EQ. rewrite Heqi'.
      apply max_r. assumption.
    
    apply IHe in EQ. assumption.

    apply IHe in EQ. assumption.
Qed.

Lemma bctx_eupper_open_tc_rec_inv : forall C k (X:atom) i,
  bctx_eupper (open_tc_rec k X C)  = i ->
  bctx_eupper C = i.
Proof.
  induction C; intros kk X i EQ; simpl in *; eauto.
    destruct (le_lt_dec (bctx_eupper (open_tc_rec kk X C)) 0).
      assert (bctx_eupper (open_tc_rec kk X C) = 0) as EQ'.
        omega.
      rewrite EQ' in *.
      assert (i = 0) as J. omega.
      subst. clear l J.
      apply IHC in EQ'.
      rewrite EQ'. omega.

      assert (bctx_eupper (open_tc_rec kk X C)  = i  + 1) as EQ'.
         rewrite <- EQ.
        omega.
      apply IHC in EQ'.
      rewrite EQ'. omega.

    destruct (le_lt_dec (bctx_eupper (open_tc_rec kk X C)) 0).
      assert (bctx_eupper (open_tc_rec kk X C) = 0) as EQ'.
        omega.
      rewrite EQ' in *.
      assert (i = 0) as J. omega.
      subst. clear l J.
      apply IHC in EQ'.
      rewrite EQ'. omega.

      assert (bctx_eupper (open_tc_rec kk X C)  = i  + 1) as EQ'.
         rewrite <- EQ.
        omega.
      apply IHC in EQ'.
      rewrite EQ'. omega.

    destruct (@max_dec (bctx_eupper (open_tc_rec kk X C)) (bexp_eupper (open_te_rec kk X e))) as [J | J].
      rewrite J in EQ.
      assert ((bexp_eupper (open_te_rec kk X e))<= (bctx_eupper (open_tc_rec kk X C))) as J'.
        rewrite <- J.
        apply le_max_r.
      remember (bexp_eupper (open_te_rec kk X e)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHC in EQ.
      symmetry in Heqi'.
      apply bexp_eupper_open_te_rec_inv in Heqi'.
      rewrite EQ. rewrite Heqi'.
      apply max_l. assumption.

      rewrite J in EQ.
      assert ((bctx_eupper (open_tc_rec kk X C))<= (bexp_eupper (open_te_rec kk X e))) as J'.
        rewrite <- J.
        apply le_max_l.
      remember (bctx_eupper (open_tc_rec kk X C)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply bexp_eupper_open_te_rec_inv in EQ.
      symmetry in Heqi'.
      apply IHC in Heqi'.
      rewrite EQ. rewrite Heqi'.
      apply max_r. assumption.
    
    destruct (@max_dec (bexp_eupper (open_te_rec kk X e)) (bctx_eupper (open_tc_rec kk X C))) as [J | J].
      rewrite J in EQ.
      assert ((bctx_eupper (open_tc_rec kk X C))<= (bexp_eupper (open_te_rec kk X e))) as J'.
        rewrite <- J.
        apply le_max_r.
      remember (bctx_eupper (open_tc_rec kk X C)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply bexp_eupper_open_te_rec_inv in EQ.
      symmetry in Heqi'.
      apply IHC in Heqi'.
      rewrite EQ. rewrite Heqi'.
      apply max_l. assumption.

      rewrite J in EQ.
      assert ((bexp_eupper (open_te_rec kk X e))<= (bctx_eupper (open_tc_rec kk X C))) as J'.
        rewrite <- J.
        apply le_max_l.
      remember (bexp_eupper (open_te_rec kk X e)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHC in EQ.
      symmetry in Heqi'.
      apply bexp_eupper_open_te_rec_inv in Heqi'.
      rewrite EQ. rewrite Heqi'.
      apply max_r. assumption.

    destruct (@max_dec (bctx_eupper (open_tc_rec kk X C)) (bexp_eupper (open_te_rec kk X e))) as [J | J].
      rewrite J in EQ.
      assert ((bexp_eupper (open_te_rec kk X e))<= (bctx_eupper (open_tc_rec kk X C))) as J'.
        rewrite <- J.
        apply le_max_r.
      remember (bexp_eupper (open_te_rec kk X e)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHC in EQ.
      symmetry in Heqi'.
      apply bexp_eupper_open_te_rec_inv in Heqi'.
      rewrite EQ. rewrite Heqi'.
      apply max_l. assumption.

      rewrite J in EQ.
      assert ((bctx_eupper (open_tc_rec kk X C))<= (bexp_eupper (open_te_rec kk X e))) as J'.
        rewrite <- J.
        apply le_max_l.
      remember (bctx_eupper (open_tc_rec kk X C)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply bexp_eupper_open_te_rec_inv in EQ.
      symmetry in Heqi'.
      apply IHC in Heqi'.
      rewrite EQ. rewrite Heqi'.
      apply max_r. assumption.
    
    destruct (@max_dec (bexp_eupper (open_te_rec kk X e)) (bctx_eupper (open_tc_rec kk X C))) as [J | J].
      rewrite J in EQ.
      assert ((bctx_eupper (open_tc_rec kk X C))<= (bexp_eupper (open_te_rec kk X e))) as J'.
        rewrite <- J.
        apply le_max_r.
      remember (bctx_eupper (open_tc_rec kk X C)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply bexp_eupper_open_te_rec_inv in EQ.
      symmetry in Heqi'.
      apply IHC in Heqi'.
      rewrite EQ. rewrite Heqi'.
      apply max_l. assumption.

      rewrite J in EQ.
      assert ((bexp_eupper (open_te_rec kk X e))<= (bctx_eupper (open_tc_rec kk X C))) as J'.
        rewrite <- J.
        apply le_max_l.
      remember (bexp_eupper (open_te_rec kk X e)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHC in EQ.
      symmetry in Heqi'.
      apply bexp_eupper_open_te_rec_inv in Heqi'.
      rewrite EQ. rewrite Heqi'.
      apply max_r. assumption.
Qed.

Lemma context_bctx_eupper : forall C,
  context C ->
  bctx_eupper C = 0.
Proof.
  intros C HC.
  induction HC; simpl; 
  try solve [
    auto |
    rewrite IHHC; rewrite expr_bexp_eupper; auto].
    pick fresh x.
    assert (x `notin` L) as xnL. auto.
    apply H1 in xnL; auto.
    apply bctx_eupper_open_ec_rec_inv in xnL.
    destruct xnL as [J | J].
      rewrite J.  omega.
      rewrite J.  omega.

    pick fresh x.
    assert (x `notin` L) as xnL. auto.
    apply H1 in xnL; auto.
    apply bctx_eupper_open_ec_rec_inv in xnL.
    destruct xnL as [J | J].
      rewrite J.  omega.
      rewrite J.  omega.

    pick fresh X.
    assert (X `notin` L) as XnL. auto.
    apply H0 in XnL; auto.
    apply bctx_eupper_open_tc_rec_inv in XnL.
    rewrite XnL.  omega.

    pick fresh X.
    assert (X `notin` L) as XnL. auto.
    apply H0 in XnL; auto.
    apply bctx_eupper_open_tc_rec_inv in XnL.
    rewrite XnL.  omega.
Qed.

Lemma subst_ee_shift_ee_rec : forall e x e0 m b,
  expr e0 ->
  subst_ee x e0 (shift_ee_rec m b e) =
    shift_ee_rec m b (subst_ee x e0 e).
Proof with auto*.
  intros e x e0 m b. revert b. revert m. revert x. revert e0.
  induction e; intros e0 x m b He0; simpl; f_equal...
  Case "exp_bvar".
    destruct (le_lt_dec b n); auto.
  Case "exp_fvar".
    destruct (a == x ); auto.
       apply shift_ee_rec_expr; auto.
Qed.

Lemma subst_ee_shift_te_rec : forall e x e0 m b,
  expr e0 ->
  subst_ee x e0 (shift_te_rec m b e) =
    shift_te_rec m b (subst_ee x e0 e).
Proof with auto*.
  intros e x e0 m b. revert b. revert m. revert x. revert e0.
  induction e; intros e0 x m b He0; simpl; f_equal...
  Case "exp_fvar".
    destruct (a == x ); auto.
       apply shift_te_rec_expr; auto.
Qed.

Lemma subst_te_shift_ee_rec : forall e X T m b,
  subst_te X T (shift_ee_rec m b e) =
    shift_ee_rec m b (subst_te X T e).
Proof with auto*.
  intros e X T m b. revert b. revert m. revert X. revert T.
  induction e; intros T X m b; simpl; f_equal...
  Case "exp_bvar".
    destruct (le_lt_dec b n); auto.
Qed.

Lemma close_subst_ee_rec_commut : forall e x kx ey y,
  x `notin` fv_ee ey ->
  x <> y ->
  close_ee_rec kx x (subst_ee y ey e) =
  subst_ee y ey (close_ee_rec kx x e).
Proof.
  induction e; intros x kx ey y xney xny; simpl; auto.
    destruct (a==y); subst; simpl; auto.
      destruct (x==y); subst; simpl; auto.
         contradict xny; auto.
         destruct (y==y); subst; simpl; auto.
           rewrite <- close_ee_rec_expr; auto.
           contradict n0; auto.
      destruct (x==a); subst; simpl; auto.
         destruct (a==y); subst; simpl; auto.
           contradict n; auto.

    rewrite IHe; auto.

    rewrite IHe1; auto.
    rewrite IHe2; auto.

    rewrite IHe; auto.

    rewrite IHe; auto.

    rewrite IHe1; auto.
    rewrite IHe2; auto.

    rewrite IHe; auto.

    rewrite IHe; auto.
Qed.  

Lemma close_te_subst_ee_rec_commut : forall e X kX ey y,
  X `notin` fv_te ey ->
  X <> y ->
  close_te_rec kX X (subst_ee y ey e) =
  subst_ee y ey (close_te_rec kX X e).
Proof.
  induction e; intros X kX ey y Xney Xny; simpl; auto.
    destruct (a==y); subst; simpl; auto.
      destruct (X==y); subst; simpl; auto.
         contradict Xny; auto.
         rewrite <- close_te_rec_expr; auto.

    rewrite IHe; auto.

    rewrite IHe1; auto.
    rewrite IHe2; auto.

    rewrite IHe; auto.

    rewrite IHe; auto.

    rewrite IHe1; auto.
    rewrite IHe2; auto.

    rewrite IHe; auto.

    rewrite IHe; auto.
Qed.  

Lemma close_ee_subst_te_rec_commut : forall e x kx tY Y,
  x `notin` fv_tt tY ->
  x <> Y ->
  close_ee_rec kx x (subst_te Y tY e) =
  subst_te Y tY (close_ee_rec kx x e).
Proof.
  induction e; intros x kx tY Y xntY xnY; simpl; auto.
    destruct (x==a); subst; simpl; auto.

    rewrite IHe; auto.

    rewrite IHe1; auto.
    rewrite IHe2; auto.

    rewrite IHe; auto.

    rewrite IHe; auto.

    rewrite IHe1; auto.
    rewrite IHe2; auto.

    rewrite IHe; auto.

    rewrite IHe; auto.
Qed.  

Lemma subst_ee_plug : forall C z u e,
  disjdom ({{z}} `union`  (fv_ee u)  `union`  (fv_te u)) (cv_ec C) ->
  expr u ->
  subst_ee z u (plug C e) =  plug (subst_ec z u C) (subst_ee z u e).
Proof.
  induction C; intros z u e0 Disj Hu; simpl; 
    try solve [
      auto |
      rewrite IHC; auto
    ].

    simpl in Disj.
    destruct Disj as [Disj1 Disj2].
    rewrite IHC; auto.
       unfold shift_ee. 
       rewrite <- subst_ee_shift_ee_rec; auto.

       split; intros x Hx.
         apply Disj1 in Hx. auto.
         apply Disj2. auto.

    simpl in Disj.
    destruct Disj as [Disj1 Disj2].
    rewrite IHC; auto.
       unfold shift_ee. 
       rewrite <- subst_ee_shift_ee_rec; auto.
         unfold close_ee.
         rewrite <- close_subst_ee_rec_commut; auto.
           assert (a `in` union {{a}} (cv_ec C)) as ain. auto.
           apply Disj2 in ain. auto.

           assert (a `in` union {{a}} (cv_ec C)) as ain. auto.
           apply Disj2 in ain. auto.
       split; intros x Hx.
         apply Disj1 in Hx. auto.
         apply Disj2. auto.

    simpl in Disj.
    destruct Disj as [Disj1 Disj2].
    rewrite IHC; auto.
       unfold shift_te. 
       rewrite <- subst_ee_shift_te_rec; auto.

       split; intros x Hx.
         apply Disj1 in Hx. auto.
         apply Disj2. auto.

    simpl in Disj.
    destruct Disj as [Disj1 Disj2].
    rewrite IHC; auto.
       unfold shift_te. 
       rewrite <- subst_ee_shift_te_rec; auto.
         unfold close_te.
         rewrite <- close_te_subst_ee_rec_commut; auto.
           assert (a `in` union {{a}} (cv_ec C)) as ain. auto.
           apply Disj2 in ain. auto.

           assert (a `in` union {{a}} (cv_ec C)) as ain. auto.
           apply Disj2 in ain. auto.
       split; intros x Hx.
         apply Disj1 in Hx. auto.
         apply Disj2. auto.
Qed.

Lemma subst_tt_shift_tt_rec : forall t X t0 m b,
  type t0 ->
  subst_tt X t0 (shift_tt_rec m b t) =
    shift_tt_rec m b (subst_tt X t0 t).
Proof with auto*.
  intros t X t0 m b. revert b. revert m. revert X. revert t0.
  induction t; intros t0 X m b Ht0; simpl; f_equal...
  Case "typ_bvar".
    destruct (le_lt_dec b n); auto.
  Case "typ_fvar".
    destruct (a == X ); auto.
       apply shift_tt_rec_typ; auto.
Qed.

Lemma subst_te_shift_te_rec : forall e x t0 m b,
  type t0 ->
  subst_te x t0 (shift_te_rec m b e) =
    shift_te_rec m b (subst_te x t0 e).
Proof with auto*.
  intros e x t0 m b. revert b. revert m. revert x. revert t0.
  induction e; intros t0 x m b Ht0; simpl; f_equal...
    apply subst_tt_shift_tt_rec; auto.
    apply subst_tt_shift_tt_rec; auto.
Qed.

Lemma close_subst_tt_rec_commut : forall t X kX tY Y,
  X `notin` fv_tt tY ->
  X <> Y ->
  close_tt_rec kX X (subst_tt Y tY t) =
  subst_tt Y tY (close_tt_rec kX X t).
Proof.
  induction t; intros X kX tY Y XntY XnY; simpl; auto.
    destruct (a==Y); subst; simpl; auto.
      destruct (X==Y); subst; simpl; auto.
         contradict XnY; auto.
         destruct (Y==Y); subst; simpl; auto.
           rewrite <- close_tt_rec_typ; auto.
           contradict n0; auto.
      destruct (X==a); subst; simpl; auto.
         destruct (a==Y); subst; simpl; auto.
           contradict n; auto.

    rewrite IHt1; auto.
    rewrite IHt2; auto.

    rewrite IHt; auto.

    rewrite IHt1; auto.
    rewrite IHt2; auto.
Qed.  

Lemma close_subst_te_rec_commut : forall e X kX tY Y,
  X `notin` fv_tt tY ->
  X <> Y ->
  close_te_rec kX X (subst_te Y tY e) =
  subst_te Y tY (close_te_rec kX X e).
Proof.
  induction e; intros X kX tY Y XntY XnY; simpl; auto.
    rewrite close_subst_tt_rec_commut; auto.
    rewrite IHe; auto.

    rewrite IHe1; auto.
    rewrite IHe2; auto.

    rewrite IHe; auto.

    rewrite close_subst_tt_rec_commut; auto.
    rewrite IHe; auto.

    rewrite IHe1; auto.
    rewrite IHe2; auto.

    rewrite IHe; auto.

    rewrite IHe; auto.
Qed.  

Lemma subst_te_plug : forall C z U e,
  disjdom ({{z}} `union`  (fv_tt U)) (cv_ec C) ->
  type U ->
  subst_te z U (plug C e) =  plug (subst_tc z U C) (subst_te z U e).
Proof.
  induction C; intros z u e0 Disj Hu; simpl; 
    try solve [
      auto |
      rewrite IHC; auto
    ].

    simpl in Disj.
    destruct Disj as [Disj1 Disj2].
    rewrite IHC; auto.
       unfold shift_ee. 
       rewrite <- subst_te_shift_ee_rec; auto.

       split; intros x Hx.
         apply Disj1 in Hx. auto.
         apply Disj2. auto.

    simpl in Disj.
    destruct Disj as [Disj1 Disj2].
    rewrite IHC; auto.
       unfold shift_ee. 
       rewrite <- subst_te_shift_ee_rec; auto.
         unfold close_ee.
         rewrite <- close_ee_subst_te_rec_commut; auto.
           assert (a `in` union {{a}} (cv_ec C)) as ain. auto.
           apply Disj2 in ain. auto.

           assert (a `in` union {{a}} (cv_ec C)) as ain. auto.
           apply Disj2 in ain. auto.
       split; intros x Hx.
         apply Disj1 in Hx. auto.
         apply Disj2. auto.

    simpl in Disj.
    destruct Disj as [Disj1 Disj2].
    rewrite IHC; auto.
       unfold shift_te. 
       rewrite <- subst_te_shift_te_rec; auto.

       split; intros x Hx.
         apply Disj1 in Hx. auto.
         apply Disj2. auto.

    simpl in Disj.
    destruct Disj as [Disj1 Disj2].
    rewrite IHC; auto.
       unfold shift_te. 
       rewrite <- subst_te_shift_te_rec; auto.
         unfold close_te.
         rewrite <- close_subst_te_rec_commut; auto.
           assert (a `in` union {{a}} (cv_ec C)) as ain. auto.
           apply Disj2 in ain. auto.

           assert (a `in` union {{a}} (cv_ec C)) as ain. auto.
           apply Disj2 in ain. auto.
       split; intros x Hx.
         apply Disj1 in Hx. auto.
         apply Disj2. auto.
Qed.

Lemma close_open_ec_rec__subst_ec : forall C x y k,
  bctx_eupper C <= k ->
  open_ec_rec k y (close_ec_rec k x C) = subst_ec x y C.
Proof.
  induction C; intros x y k0 Hup; simpl; simpl in Hup; 
  try solve [
    auto |
    rewrite IHC; auto; omega |
    rewrite IHC; auto].

    rewrite IHC; auto.
    rewrite close_open_ee_rec__subst_ee; auto.
    assert (J:=@le_max_r (bctx_eupper C) (bexp_eupper e)).  omega.
    assert (J:=@le_max_l (bctx_eupper C) (bexp_eupper e)).  omega.

    rewrite IHC; auto.
    rewrite close_open_ee_rec__subst_ee; auto.
    assert (J:=@le_max_l (bexp_eupper e) (bctx_eupper C)).  omega.
    assert (J:=@le_max_r (bexp_eupper e) (bctx_eupper C)).  omega.

    rewrite IHC; auto.
    rewrite close_open_ee_rec__subst_ee; auto.
    assert (J:=@le_max_r (bctx_eupper C) (bexp_eupper e)).  omega.
    assert (J:=@le_max_l (bctx_eupper C) (bexp_eupper e)).  omega.

    rewrite IHC; auto.
    rewrite close_open_ee_rec__subst_ee; auto.
    assert (J:=@le_max_l (bexp_eupper e) (bctx_eupper C)).  omega.
    assert (J:=@le_max_r (bexp_eupper e) (bctx_eupper C)).  omega.
Qed.    

Lemma close_open_ec__subst_ec : forall C x y,
  context C ->
  open_ec (close_ec C x) y = subst_ec x y C.
Proof.
  intros C x y HC.
  unfold open_ec.
  unfold close_ec.
  apply close_open_ec_rec__subst_ec; auto.
    rewrite context_bctx_eupper; auto.
Qed.

Lemma close_ec_rec_context : forall x C k,
  x `notin` fv_ec C ->
  C = close_ec_rec k x C.
Proof with auto*.
  intros x C k0 Hfv. revert k0.
  induction C; intro k0; simpl in *; f_equal; auto*.
    auto using close_ee_rec_expr.
    auto using close_ee_rec_expr.
    auto using close_ee_rec_expr.
    auto using close_ee_rec_expr.
Qed.

Lemma close_ec_context : forall x C,
  x `notin` (fv_ec C) ->
  C = close_ec C x.
Proof.
  intros x e Fv.
  unfold close_ee.
  apply close_ec_rec_context; auto.
Qed.

Lemma open_ec_rec_context_aux : forall C j v u i,
  i <> j ->
  open_ec_rec j v C = open_ec_rec i u (open_ec_rec j v C) ->
  C = open_ec_rec i u C.
Proof with try solve [congruence | eauto].
  induction C; intros j v u i Neq H; simpl in *; inversion H; f_equal...
    apply open_ee_rec_expr_aux in H2; auto.
    apply open_ee_rec_expr_aux in H1; auto.
    apply open_ee_rec_expr_aux in H2; auto.
    apply open_ee_rec_expr_aux in H1; auto.
Qed.

Lemma open_ec_rec_tc_aux : forall C j V u i,
  open_tc_rec j V C = open_ec_rec i u (open_tc_rec j V C) ->
  C = open_ec_rec i u C.
Proof with try solve [congruence | eauto].
  induction C; intros j V u i H; simpl in *; inversion H; f_equal...
    apply open_ee_rec_type_aux in H2; auto.
    apply open_ee_rec_type_aux in H1; auto.
    apply open_ee_rec_type_aux in H2; auto.
    apply open_ee_rec_type_aux in H1; auto.
Qed.

Lemma open_ec_rec_context : forall C u k,
  context C ->
  C = open_ec_rec k u C.
Proof.
  intros C u k HC.
  generalize dependent k.
  induction HC; intro; simpl; 
  try solve [
    auto |
    rewrite <- IHHC ;
    rewrite <- open_ee_rec_expr with (k:=k) (u:=u); auto |
    rewrite <- IHHC; auto ].

    pick fresh x.
    assert (x `notin` L) as xnL. auto.
    apply H1 with (k:= S k) in xnL;  auto.
    apply open_ec_rec_context_aux  in xnL; auto.
    rewrite <- xnL; auto.

    pick fresh x.
    assert (x `notin` L) as xnL. auto.
    apply H1 with (k:= S k) in xnL;  auto.
    apply open_ec_rec_context_aux  in xnL; auto.
    rewrite <- xnL; auto.

    pick fresh X.
    assert (X `notin` L) as XnL. auto.
    apply H0 with (k:= k) in XnL;  auto.
    apply open_ec_rec_tc_aux  in XnL; auto.
    rewrite <- XnL; auto.

    pick fresh X.
    assert (X `notin` L) as XnL. auto.
    apply H0 with (k:= k) in XnL;  auto.
    apply open_ec_rec_tc_aux  in XnL; auto.
    rewrite <- XnL; auto.
Qed.

Lemma open_ec_context : forall u C,
  context C ->
  C = open_ec C u.
Proof.
  intros u HC.
  unfold open_ec.
  apply open_ec_rec_context; auto.
Qed.

Lemma open_tc_rec_ec_aux : forall C j v U i,
  open_ec_rec j v C = open_tc_rec i U (open_ec_rec j v C) ->
  C = open_tc_rec i U C.
Proof with try solve [congruence | eauto].
  induction C; intros j v U i H; simpl in *; inversion H; f_equal...
    apply open_te_rec_expr_aux in H2; auto.
    apply open_te_rec_expr_aux in H1; auto.
    apply open_te_rec_expr_aux in H2; auto.
    apply open_te_rec_expr_aux in H1; auto.
Qed.

Lemma open_tc_rec_tc_aux : forall C j V U i,
  i <> j ->
  open_tc_rec j V C = open_tc_rec i U (open_tc_rec j V C) ->
  C = open_tc_rec i U C.
Proof with try solve [congruence | eauto].
  induction C; intros j V U i Neq H; simpl in *; inversion H; f_equal...
    apply open_tt_rec_type_aux in H1; auto.
    apply open_tt_rec_type_aux in H1; auto.
    apply open_te_rec_type_aux in H2; auto.
    apply open_te_rec_type_aux in H1; auto.
    apply open_tt_rec_type_aux in H2; auto.
    apply open_te_rec_type_aux in H2; auto.
    apply open_te_rec_type_aux in H1; auto.
Qed.

Lemma open_tc_rec_context : forall C U k,
  context C ->
  C = open_tc_rec k U C.
Proof.
  intros C U k HC.
  generalize dependent k.
  induction HC; intro; simpl; 
  try solve [auto |
    rewrite <- IHHC; auto;
    rewrite <- open_tt_rec_type; auto|
    rewrite <- IHHC;
    rewrite <- open_te_rec_expr with (k:=k) (U:=U); auto].

    pick fresh x.
    assert (x `notin` L) as xnL. auto.
    apply H1 with (k:= k) in xnL;  auto.
    apply open_tc_rec_ec_aux  in xnL; auto.
    rewrite <- xnL; auto.
    rewrite <- open_tt_rec_type; auto.

    pick fresh x.
    assert (x `notin` L) as xnL. auto.
    apply H1 with (k:= k) in xnL;  auto.
    apply open_tc_rec_ec_aux  in xnL; auto.
    rewrite <- xnL; auto.
    rewrite <- open_tt_rec_type; auto.

    pick fresh X.
    assert (X `notin` L) as XnL. auto.
    apply H0 with (k:= S k) in XnL;  auto.
    apply open_tc_rec_tc_aux  in XnL; auto.
    rewrite <- XnL; auto.

    pick fresh X.
    assert (X `notin` L) as XnL. auto.
    apply H0 with (k:= S k) in XnL;  auto.
    apply open_tc_rec_tc_aux  in XnL; auto.
    rewrite <- XnL; auto.
Qed.

Lemma open_tc_context : forall U C,
  context C ->
  C = open_tc C U.
Proof.
  intros u HC.
  unfold open_tc.
  apply open_tc_rec_context; auto.
Qed.

Lemma subst_ec_open_ec_rec : forall C1 e2 x u k,
  expr u ->
  subst_ec x u (open_ec_rec k e2 C1) =
    open_ec_rec k (subst_ee x u e2) (subst_ec x u C1).
Proof with try solve [congruence | intuition].
  intros C1 e2 x u k WP. revert k.
  induction C1; intros K; simpl; f_equal...
    apply subst_ee_open_ee_rec; auto.
    apply subst_ee_open_ee_rec; auto.
    apply subst_ee_open_ee_rec; auto.
    apply subst_ee_open_ee_rec; auto.
Qed.

Lemma subst_ec_open_ec_var : forall (x y:atom) u C,
  y <> x ->
  expr u ->
  open_ec (subst_ec x u C) y = subst_ec x u (open_ec C y).
Proof with try solve [congruence | intuition].
  intros x y u C Neq Wu.
  unfold open_ec.
  rewrite subst_ec_open_ec_rec...
  simpl.
  destruct (y == x)...
Qed.

Lemma subst_ec_open_tc_rec : forall C1 t2 x u k,
  expr u ->
  subst_ec x u (open_tc_rec k t2 C1) =
    open_tc_rec k t2 (subst_ec x u C1).
Proof with try solve [congruence | intuition].
  intros C1 t2 x u k WP. revert k.
  induction C1; intros K; simpl; f_equal...
    apply subst_ee_open_te_rec; auto.
    apply subst_ee_open_te_rec; auto.
    apply subst_ee_open_te_rec; auto.
    apply subst_ee_open_te_rec; auto.
Qed.

Lemma subst_ec_open_tc_var : forall (x Y:atom) u C,
  Y <> x ->
  expr u ->
  open_tc (subst_ec x u C) Y = subst_ec x u (open_tc C Y).
Proof with try solve [congruence | intuition].
  intros x y u C Neq Wu.
  unfold open_tc.
  rewrite subst_ec_open_tc_rec...
Qed.

Lemma subst_ec_context : forall z C e,
  context C ->
  expr e ->
  context (subst_ec z e C).
Proof with auto.
  intros z C e HC He.
  induction HC; simpl; auto.
    apply context_abs_free with (L:=L `union` singleton z); auto.
      intros x xnL.
      rewrite subst_ec_open_ec_var; auto.
    apply context_abs_capture with (L:=L `union` singleton z); auto.
      intros x xnL.
      rewrite subst_ec_open_ec_var; auto.
    apply context_tabs_free with (L:=L `union` singleton z); auto.
      intros X XnL.
      rewrite subst_ec_open_tc_var; auto.
    apply context_tabs_capture with (L:=L `union` singleton z); auto.
      intros X XnL.
      rewrite subst_ec_open_tc_var; auto.
Qed.

Lemma close_open_tt_rec__subst_tt : forall t X Y k,
  btyp_upper t <= k ->
  open_tt_rec k Y (close_tt_rec k X t) = subst_tt X Y t.
Proof.
  induction t; intros X Y k0 Hup; simpl; simpl in Hup; auto.
    destruct (k0==n); subst; auto.
      contradict Hup.
      omega.

    destruct (X==a); subst.
      destruct (a==a).
        simpl.
        destruct (k0==k0); auto.
          contradict n; auto.
        contradict n; auto.
      destruct (a==X); subst.
        contradict n; auto.
        simpl. auto.

    rewrite IHt1; auto.
    rewrite IHt2; auto.
    assert (J:=@le_max_r (btyp_upper t1) (btyp_upper t2)).  omega.
    assert (J:=@le_max_l (btyp_upper t1) (btyp_upper t2)).  omega.

    rewrite IHt; auto.
      omega.

    rewrite IHt1; auto.
    rewrite IHt2; auto.
    assert (J:=@le_max_r (btyp_upper t1) (btyp_upper t2)).  omega.
    assert (J:=@le_max_l (btyp_upper t1) (btyp_upper t2)).  omega.
Qed.    

Lemma open_tt_btyp_upper : forall t k (X:atom),
  btyp_upper (open_tt_rec k X t) <= btyp_upper t.
Proof.
  induction t; intros k0 x; simpl.
    destruct (k0==n); subst; simpl; omega.

    omega.

    assert (J1:=@IHt1 k0 x). 
    assert (J2:=@IHt2 k0 x). 
    apply max_injective; auto.

    assert (J:=@IHt (S k0) x). omega.

    assert (J1:=@IHt1 k0 x). 
    assert (J2:=@IHt2 k0 x). 
    apply max_injective; auto.
Qed.

Lemma btyp_upper_open_tt_rec_inv : forall t k (X:atom) i,
  btyp_upper (open_tt_rec k X t)  = i ->
  btyp_upper t = k +1 \/ btyp_upper t = i.
Proof.
  induction t; intros kk X i EQ; simpl in *; auto.
    destruct (kk == n); subst; auto.

    destruct (@max_dec (btyp_upper (open_tt_rec kk X t1)) (btyp_upper (open_tt_rec kk X t2))) as [J | J].
      rewrite J in EQ.
      assert ((btyp_upper (open_tt_rec kk X t2))<= (btyp_upper (open_tt_rec kk X t1))) as J'.
        rewrite <- J.
        apply le_max_r.
      remember (btyp_upper (open_tt_rec kk X t2)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHt1 in EQ.
      symmetry in Heqi'.
      apply IHt2 in Heqi'.
      destruct EQ as [EQ1 | EQ1].
        destruct Heqi' as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          left. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          left. apply max_l.
            assert (J''':=@open_tt_btyp_upper t1 kk X).
            omega.
        destruct Heqi' as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          destruct (le_lt_dec i (kk+1)).
             left. apply max_r. auto.
             right. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          right. apply max_l. auto.

      rewrite J in EQ.
      assert ((btyp_upper (open_tt_rec kk X t1))<= (btyp_upper (open_tt_rec kk X t2))) as J'.
        rewrite <- J.
        apply le_max_l.
      remember (btyp_upper (open_tt_rec kk X t1)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHt2 in EQ.
      symmetry in Heqi'.
      apply IHt1 in Heqi'.
      destruct EQ as [EQ2 | EQ2].
        destruct Heqi' as [EQ1 | EQ1].
          rewrite EQ1. rewrite EQ2.
          left. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          left. apply max_r.
            assert (J''':=@open_tt_btyp_upper t2 kk X).
            omega.
        destruct Heqi' as [EQ1 | EQ1].
          rewrite EQ1. rewrite EQ2.
          destruct (le_lt_dec i (kk+1)).
             left. apply max_l. auto.
             right. apply max_r. omega.

          rewrite EQ1. rewrite EQ2.
          right. apply max_r. auto.
    
    destruct (le_lt_dec (btyp_upper (open_tt_rec (S kk) X t)) 0).
      assert (btyp_upper (open_tt_rec (S kk) X t) = 0) as EQ'.
        omega.
      rewrite EQ' in *.
      assert (i = 0) as J. omega.
      subst. clear l J.
      apply IHt in EQ'.
      destruct EQ' as [J | J].
      left. rewrite J. omega.
      right. rewrite J. omega.

      assert (btyp_upper (open_tt_rec (S kk) X t)  = i  + 1) as EQ'.
         rewrite <- EQ.
        omega.
      apply IHt in EQ'.
      destruct EQ' as [J | J].
      left. rewrite J. omega.
      right. rewrite J. omega.

    destruct (@max_dec (btyp_upper (open_tt_rec kk X t1)) (btyp_upper (open_tt_rec kk X t2))) as [J | J].
      rewrite J in EQ.
      assert ((btyp_upper (open_tt_rec kk X t2))<= (btyp_upper (open_tt_rec kk X t1))) as J'.
        rewrite <- J.
        apply le_max_r.
      remember (btyp_upper (open_tt_rec kk X t2)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHt1 in EQ.
      symmetry in Heqi'.
      apply IHt2 in Heqi'.
      destruct EQ as [EQ1 | EQ1].
        destruct Heqi' as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          left. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          left. apply max_l.
            assert (J''':=@open_tt_btyp_upper t1 kk X).
            omega.
        destruct Heqi' as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          destruct (le_lt_dec i (kk+1)).
             left. apply max_r. auto.
             right. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          right. apply max_l. auto.

      rewrite J in EQ.
      assert ((btyp_upper (open_tt_rec kk X t1))<= (btyp_upper (open_tt_rec kk X t2))) as J'.
        rewrite <- J.
        apply le_max_l.
      remember (btyp_upper (open_tt_rec kk X t1)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHt2 in EQ.
      symmetry in Heqi'.
      apply IHt1 in Heqi'.
      destruct EQ as [EQ2 | EQ2].
        destruct Heqi' as [EQ1 | EQ1].
          rewrite EQ1. rewrite EQ2.
          left. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          left. apply max_r.
            assert (J''':=@open_tt_btyp_upper t2 kk X).
            omega.
        destruct Heqi' as [EQ1 | EQ1].
          rewrite EQ1. rewrite EQ2.
          destruct (le_lt_dec i (kk+1)).
             left. apply max_l. auto.
             right. apply max_r. omega.

          rewrite EQ1. rewrite EQ2.
          right. apply max_r. auto.
Qed.

Lemma type_btyp_upper : forall t,
  type t ->
  btyp_upper t = 0.
Proof.
  intros t Ht.
  induction Ht; simpl; auto.
    rewrite IHHt1. rewrite IHHt2.
   apply max_l. auto.

    pick fresh X.
    assert (X `notin` L) as XnL. auto.
    apply H0 in XnL; auto.
    unfold open_tt in XnL.
    apply btyp_upper_open_tt_rec_inv in XnL.
    destruct XnL as [J | J].
      rewrite J.  omega.
      rewrite J.  omega.

   rewrite IHHt1. rewrite IHHt2.
   apply max_l. auto.
Qed.

Lemma close_open_tt__subst_tt : forall t X Y,
  type t ->
  open_tt (close_tt t X) Y = subst_tt X Y t.
Proof.
  intros t X Y Ht.
  unfold open_tt.
  unfold close_tt.
  apply close_open_tt_rec__subst_tt; auto.
    rewrite type_btyp_upper; auto.
Qed.

Lemma close_open_te_rec__subst_te : forall e X Y k,
  bexp_tupper e <= k ->
  open_te_rec k Y (close_te_rec k X e) = subst_te X Y e.
Proof.
  induction e; intros X Y k0 Hup; simpl; simpl in Hup; auto.
    rewrite IHe; auto.
    rewrite close_open_tt_rec__subst_tt; auto.
    assert (J:=@le_max_l (btyp_upper t) (bexp_tupper e)).  omega.
    assert (J:=@le_max_r (btyp_upper t) (bexp_tupper e)).  omega.

    rewrite IHe1; auto.
    rewrite IHe2; auto.
    assert (J:=@le_max_r (bexp_tupper e1) (bexp_tupper e2)).  omega.
    assert (J:=@le_max_l (bexp_tupper e1) (bexp_tupper e2)).  omega.

    rewrite IHe; auto.
      omega.

    rewrite IHe; auto.
    rewrite close_open_tt_rec__subst_tt; auto.
    assert (J:=@le_max_r (bexp_tupper e) (btyp_upper t)).  omega.
    assert (J:=@le_max_l (bexp_tupper e) (btyp_upper t)).  omega.

    rewrite IHe1; auto.
    rewrite IHe2; auto.
    assert (J:=@le_max_r (bexp_tupper e1) (bexp_tupper e2)).  omega.
    assert (J:=@le_max_l (bexp_tupper e1) (bexp_tupper e2)).  omega.

    rewrite IHe; auto.

    rewrite IHe; auto.
Qed.    

Lemma close_open_tc_rec__subst_tc : forall C X Y k,
  bctx_tupper C <= k ->
  open_tc_rec k Y (close_tc_rec k X C) = subst_tc X Y C.
Proof.
  induction C; intros x y k0 Hup; simpl; simpl in Hup; auto.
    rewrite IHC; auto.
    rewrite close_open_tt_rec__subst_tt; auto.
    assert (J:=@le_max_l (btyp_upper t) (bctx_tupper C)).  omega.
    assert (J:=@le_max_r (btyp_upper t) (bctx_tupper C)).  omega.

    rewrite IHC; auto.
    rewrite close_open_tt_rec__subst_tt; auto.
    assert (J:=@le_max_l (btyp_upper t) (bctx_tupper C)).  omega.
    assert (J:=@le_max_r (btyp_upper t) (bctx_tupper C)).  omega.

    rewrite IHC; auto.
    rewrite close_open_te_rec__subst_te; auto.
    assert (J:=@le_max_r (bctx_tupper C) (bexp_tupper e)).  omega.
    assert (J:=@le_max_l (bctx_tupper C) (bexp_tupper e)).  omega.

    rewrite IHC; auto.
    rewrite close_open_te_rec__subst_te; auto.
    assert (J:=@le_max_l (bexp_tupper e) (bctx_tupper C)).  omega.
    assert (J:=@le_max_r (bexp_tupper e) (bctx_tupper C)).  omega.

    rewrite IHC; auto.
      omega.

    rewrite IHC; auto.
      omega.

    rewrite IHC; auto.
    rewrite close_open_tt_rec__subst_tt; auto.
    assert (J:=@le_max_r (bctx_tupper C) (btyp_upper t)).  omega.
    assert (J:=@le_max_l (bctx_tupper C) (btyp_upper t)).  omega.

    rewrite IHC; auto.
    rewrite close_open_te_rec__subst_te; auto.
    assert (J:=@le_max_r (bctx_tupper C) (bexp_tupper e)).  omega.
    assert (J:=@le_max_l (bctx_tupper C) (bexp_tupper e)).  omega.

    rewrite IHC; auto.
    rewrite close_open_te_rec__subst_te; auto.
    assert (J:=@le_max_l (bexp_tupper e) (bctx_tupper C)).  omega.
    assert (J:=@le_max_r (bexp_tupper e) (bctx_tupper C)).  omega.

    rewrite IHC; auto.

    rewrite IHC; auto.
Qed.    

Lemma bexp_tupper_open_ee_rec_inv : forall e k (x:atom) i,
  bexp_tupper (open_ee_rec k x e)  = i ->
  bexp_tupper e = i.
Proof.
  induction e; intros kk x i EQ; simpl in *; auto.
    destruct (kk == n); auto.

    destruct (@max_dec (btyp_upper t) (bexp_tupper (open_ee_rec (S kk) x e))) as [J | J].
      rewrite J in EQ.
      assert ((bexp_tupper (open_ee_rec (S kk) x e)) <= (btyp_upper t)) as J'.
        rewrite <- J.
        apply le_max_r.
      remember (bexp_tupper (open_ee_rec (S kk) x e)) as i'.
      assert (i' <= i) as J''.
        omega.
      symmetry in Heqi'.
      apply IHe in Heqi'.
      rewrite EQ. rewrite Heqi'.
      apply max_l. assumption.

      rewrite J in EQ.
      assert ((btyp_upper t) <= (bexp_tupper (open_ee_rec (S kk) x e))) as J'.
        rewrite <- J.
        apply le_max_l.
      remember ((btyp_upper t)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHe in EQ.
      rewrite EQ.
      apply max_r. assumption.

    destruct (@max_dec (bexp_tupper (open_ee_rec kk x e1)) (bexp_tupper (open_ee_rec kk x e2))) as [J | J].
      rewrite J in EQ.
      assert ((bexp_tupper (open_ee_rec kk x e2))<= (bexp_tupper (open_ee_rec kk x e1))) as J'.
        rewrite <- J.
        apply le_max_r.
      remember (bexp_tupper (open_ee_rec kk x e2)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHe1 in EQ.
      symmetry in Heqi'.
      apply IHe2 in Heqi'.
      rewrite EQ. rewrite Heqi'.
      apply max_l. assumption.

      rewrite J in EQ.
      assert ((bexp_tupper (open_ee_rec kk x e1))<= (bexp_tupper (open_ee_rec kk x e2))) as J'.
        rewrite <- J.
        apply le_max_l.
      remember (bexp_tupper (open_ee_rec kk x e1)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHe2 in EQ.
      symmetry in Heqi'.
      apply IHe1 in Heqi'.
      rewrite EQ. rewrite Heqi'.
      apply max_r. assumption.

    destruct (le_lt_dec (bexp_tupper (open_ee_rec kk x e)) 0).
      assert (bexp_tupper (open_ee_rec kk x e) = 0) as EQ'.
        omega.
      rewrite EQ' in *.
      assert (i = 0) as J. omega.
      subst. clear l J.
      apply IHe in EQ'.
      rewrite EQ'. omega.

      assert (bexp_tupper (open_ee_rec kk x e)  = i  + 1) as EQ'.
         rewrite <- EQ.
        omega.
      apply IHe in EQ'.
      rewrite EQ'. omega.

    destruct (@max_dec (bexp_tupper (open_ee_rec kk x e)) (btyp_upper t)) as [J | J].
      rewrite J in EQ.
      assert ((btyp_upper t) <= (bexp_tupper (open_ee_rec kk x e))) as J'.
        rewrite <- J.
        apply le_max_r.
      remember ((btyp_upper t)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHe in EQ.
      rewrite EQ.
      apply max_l. assumption.

      rewrite J in EQ.
      assert ((bexp_tupper (open_ee_rec kk x e)) <= (btyp_upper t)) as J'.
        rewrite <- J.
        apply le_max_l.
      remember (bexp_tupper (open_ee_rec kk x e)) as i'.
      assert (i' <= i) as J''.
        omega.
      symmetry in Heqi'.
      apply IHe in Heqi'.
      rewrite EQ. rewrite Heqi'.
      apply max_r. assumption.

    destruct (@max_dec (bexp_tupper (open_ee_rec kk x e1)) (bexp_tupper (open_ee_rec kk x e2))) as [J | J].
      rewrite J in EQ.
      assert ((bexp_tupper (open_ee_rec kk x e2))<= (bexp_tupper (open_ee_rec kk x e1))) as J'.
        rewrite <- J.
        apply le_max_r.
      remember (bexp_tupper (open_ee_rec kk x e2)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHe1 in EQ.
      symmetry in Heqi'.
      apply IHe2 in Heqi'.
      rewrite EQ. rewrite Heqi'.
      apply max_l. assumption.

      rewrite J in EQ.
      assert ((bexp_tupper (open_ee_rec kk x e1))<= (bexp_tupper (open_ee_rec kk x e2))) as J'.
        rewrite <- J.
        apply le_max_l.
      remember (bexp_tupper (open_ee_rec kk x e1)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHe2 in EQ.
      symmetry in Heqi'.
      apply IHe1 in Heqi'.
      rewrite EQ. rewrite Heqi'.
      apply max_r. assumption.
    
    apply IHe in EQ. assumption.

    apply IHe in EQ. assumption.
Qed.

Lemma bctx_tupper_open_ec_rec_inv : forall C k (x:atom) i,
  bctx_tupper (open_ec_rec k x C)  = i ->
  bctx_tupper C = i.
Proof.
  induction C; intros kk x i EQ; simpl in *; eauto.
    destruct (@max_dec (btyp_upper t) (bctx_tupper (open_ec_rec (S kk) x C))) as [J | J].
      rewrite J in EQ.
      assert ((bctx_tupper (open_ec_rec (S kk) x C)) <= (btyp_upper t)) as J'.
        rewrite <- J.
        apply le_max_r.
      remember (bctx_tupper (open_ec_rec (S kk) x C)) as i'.
      assert (i' <= i) as J''.
        omega.
      symmetry in Heqi'.
      apply IHC in Heqi'.
      rewrite EQ. rewrite Heqi'.
      apply max_l. assumption.

      rewrite J in EQ.
      assert ((btyp_upper t) <= (bctx_tupper (open_ec_rec (S kk) x C))) as J'.
        rewrite <- J.
        apply le_max_l.
      remember (btyp_upper t) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHC in EQ.
      rewrite EQ.
      apply max_r. assumption.
    
    destruct (@max_dec (btyp_upper t) (bctx_tupper (open_ec_rec (S kk) x C))) as [J | J].
      rewrite J in EQ.
      assert ((bctx_tupper (open_ec_rec (S kk) x C)) <= (btyp_upper t)) as J'.
        rewrite <- J.
        apply le_max_r.
      remember (bctx_tupper (open_ec_rec (S kk) x C)) as i'.
      assert (i' <= i) as J''.
        omega.
      symmetry in Heqi'.
      apply IHC in Heqi'.
      rewrite EQ. rewrite Heqi'.
      apply max_l. assumption.

      rewrite J in EQ.
      assert ((btyp_upper t) <= (bctx_tupper (open_ec_rec (S kk) x C))) as J'.
        rewrite <- J.
        apply le_max_l.
      remember (btyp_upper t) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHC in EQ.
      rewrite EQ.
      apply max_r. assumption.

    destruct (@max_dec (bctx_tupper (open_ec_rec kk x C)) (bexp_tupper (open_ee_rec kk x e))) as [J | J].
      rewrite J in EQ.
      assert ((bexp_tupper (open_ee_rec kk x e)) <= (bctx_tupper (open_ec_rec kk x C))) as J'.
        rewrite <- J.
        apply le_max_r.
      remember (bexp_tupper (open_ee_rec kk x e)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHC in EQ.
      symmetry in Heqi'.
      apply bexp_tupper_open_ee_rec_inv in Heqi'.
      rewrite EQ. rewrite Heqi'.
      apply max_l. assumption.

      rewrite J in EQ.
      assert ((bctx_tupper (open_ec_rec kk x C)) <= (bexp_tupper (open_ee_rec kk x e))) as J'.
        rewrite <- J.
        apply le_max_l.
      remember (bctx_tupper (open_ec_rec kk x C)) as i'.
      assert (i' <= i) as J''.
        omega.
      symmetry in Heqi'.
      apply IHC in Heqi'.
      apply bexp_tupper_open_ee_rec_inv in EQ.
      rewrite EQ. rewrite Heqi'.
      apply max_r. assumption.

    destruct (@max_dec (bexp_tupper (open_ee_rec kk x e)) (bctx_tupper (open_ec_rec kk x C))) as [J | J].
      rewrite J in EQ.
      assert ((bctx_tupper (open_ec_rec kk x C)) <= (bexp_tupper (open_ee_rec kk x e))) as J'.
        rewrite <- J.
        apply le_max_r.
      remember (bctx_tupper (open_ec_rec kk x C)) as i'.
      assert (i' <= i) as J''.
        omega.
      symmetry in Heqi'.
      apply IHC in Heqi'.
      apply bexp_tupper_open_ee_rec_inv in EQ.
      rewrite EQ. rewrite Heqi'.
      apply max_l. assumption.

      rewrite J in EQ.
      assert ((bexp_tupper (open_ee_rec kk x e)) <= (bctx_tupper (open_ec_rec kk x C))) as J'.
        rewrite <- J.
        apply le_max_l.
      remember (bexp_tupper (open_ee_rec kk x e)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHC in EQ.
      symmetry in Heqi'.
      apply bexp_tupper_open_ee_rec_inv in Heqi'.
      rewrite EQ. rewrite Heqi'.
      apply max_r. assumption.

    destruct (le_lt_dec (bctx_tupper (open_ec_rec kk x C)) 0).
      assert (bctx_tupper (open_ec_rec kk x C) = 0) as EQ'.
        omega.
      rewrite EQ' in *.
      assert (i = 0) as J. omega.
      subst. clear l J.
      apply IHC in EQ'.
      rewrite EQ'. omega.

      assert (bctx_tupper (open_ec_rec kk x C)  = i  + 1) as EQ'.
         rewrite <- EQ.
        omega.
      apply IHC in EQ'.
      rewrite EQ'. omega.

    destruct (le_lt_dec (bctx_tupper (open_ec_rec kk x C)) 0).
      assert (bctx_tupper (open_ec_rec kk x C) = 0) as EQ'.
        omega.
      rewrite EQ' in *.
      assert (i = 0) as J. omega.
      subst. clear l J.
      apply IHC in EQ'.
      rewrite EQ'. omega.

      assert (bctx_tupper (open_ec_rec kk x C)  = i  + 1) as EQ'.
         rewrite <- EQ.
        omega.
      apply IHC in EQ'.
      rewrite EQ'. omega.

    destruct (@max_dec (bctx_tupper (open_ec_rec kk x C)) (btyp_upper t)) as [J | J].
      rewrite J in EQ.
      assert ((btyp_upper t) <= (bctx_tupper (open_ec_rec kk x C))) as J'.
        rewrite <- J.
        apply le_max_r.
      remember (btyp_upper t) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHC in EQ.
      rewrite EQ.
      apply max_l. assumption.
    
      rewrite J in EQ.
      assert ((bctx_tupper (open_ec_rec kk x C)) <= (btyp_upper t)) as J'.
        rewrite <- J.
        apply le_max_l.
      remember (bctx_tupper (open_ec_rec kk x C)) as i'.
      assert (i' <= i) as J''.
        omega.
      symmetry in Heqi'.
      apply IHC in Heqi'.
      rewrite EQ. rewrite Heqi'.
      apply max_r. assumption.

    destruct (@max_dec (bctx_tupper (open_ec_rec kk x C)) (bexp_tupper (open_ee_rec kk x e))) as [J | J].
      rewrite J in EQ.
      assert ((bexp_tupper (open_ee_rec kk x e)) <= (bctx_tupper (open_ec_rec kk x C))) as J'.
        rewrite <- J.
        apply le_max_r.
      remember (bexp_tupper (open_ee_rec kk x e)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHC in EQ.
      symmetry in Heqi'.
      apply bexp_tupper_open_ee_rec_inv in Heqi'.
      rewrite EQ. rewrite Heqi'.
      apply max_l. assumption.

      rewrite J in EQ.
      assert ((bctx_tupper (open_ec_rec kk x C)) <= (bexp_tupper (open_ee_rec kk x e))) as J'.
        rewrite <- J.
        apply le_max_l.
      remember (bctx_tupper (open_ec_rec kk x C)) as i'.
      assert (i' <= i) as J''.
        omega.
      symmetry in Heqi'.
      apply IHC in Heqi'.
      apply bexp_tupper_open_ee_rec_inv in EQ.
      rewrite EQ. rewrite Heqi'.
      apply max_r. assumption.

    destruct (@max_dec (bexp_tupper (open_ee_rec kk x e)) (bctx_tupper (open_ec_rec kk x C))) as [J | J].
      rewrite J in EQ.
      assert ((bctx_tupper (open_ec_rec kk x C)) <= (bexp_tupper (open_ee_rec kk x e))) as J'.
        rewrite <- J.
        apply le_max_r.
      remember (bctx_tupper (open_ec_rec kk x C)) as i'.
      assert (i' <= i) as J''.
        omega.
      symmetry in Heqi'.
      apply IHC in Heqi'.
      apply bexp_tupper_open_ee_rec_inv in EQ.
      rewrite EQ. rewrite Heqi'.
      apply max_l. assumption.

      rewrite J in EQ.
      assert ((bexp_tupper (open_ee_rec kk x e)) <= (bctx_tupper (open_ec_rec kk x C))) as J'.
        rewrite <- J.
        apply le_max_l.
      remember (bexp_tupper (open_ee_rec kk x e)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHC in EQ.
      symmetry in Heqi'.
      apply bexp_tupper_open_ee_rec_inv in Heqi'.
      rewrite EQ. rewrite Heqi'.
      apply max_r. assumption.
Qed.

Lemma open_te_bexp_tupper : forall e k (X:atom),
  bexp_tupper (open_te_rec k X e) <= bexp_tupper e.
Proof.
  induction e; intros k0 X; simpl.
    omega.

    omega.

    assert (J:=@IHe k0 X). 
    assert (J':=@open_tt_btyp_upper t k0 X).
    apply max_injective; auto.

    assert (J1:=@IHe1 k0 X). 
    assert (J2:=@IHe2 k0 X). 
    apply max_injective; auto.

    assert (J:=@IHe (S k0) X). omega.

    assert (J:=@IHe k0 X). 
    assert (J':=@open_tt_btyp_upper t k0 X).
    apply max_injective; auto.

    assert (J1:=@IHe1 k0 X). 
    assert (J2:=@IHe2 k0 X). 
    apply max_injective; auto.

    assert (J:=@IHe k0 X). omega.

    assert (J:=@IHe k0 X). omega.
Qed.

Lemma bexp_tupper_open_te_rec_inv : forall e k (X:atom) i,
  bexp_tupper (open_te_rec k X e) = i ->
  bexp_tupper e = k +1 \/ bexp_tupper e = i.
Proof.
  induction e; intros kk X i EQ; simpl in *; auto.
    destruct (@max_dec (btyp_upper (open_tt_rec kk X t)) (bexp_tupper (open_te_rec kk X e))) as [J | J].
      rewrite J in EQ.
      assert ((bexp_tupper (open_te_rec kk X e))<= (btyp_upper (open_tt_rec kk X t))) as J'.
        rewrite <- J.
        apply le_max_r.
      remember (bexp_tupper (open_te_rec kk X e)) as i'.
      assert (i' <= i) as J''.
        omega.
      symmetry in Heqi'.
      apply IHe in Heqi'.
      destruct (@btyp_upper_open_tt_rec_inv t kk X i EQ) as [EQ1 | EQ1].
        destruct Heqi' as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          left. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          left. apply max_l.
            assert (J''':=@open_tt_btyp_upper t kk X).
            omega.
        destruct Heqi' as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          destruct (le_lt_dec i (kk+1)).
             left. apply max_r. auto.
             right. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          right. apply max_l. auto.

      rewrite J in EQ.
      assert ((btyp_upper (open_tt_rec kk X t))<= (bexp_tupper (open_te_rec kk X e))) as J'.
        rewrite <- J.
        apply le_max_l.
      remember (btyp_upper (open_tt_rec kk X t)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHe in EQ.
      symmetry in Heqi'.
      destruct (@btyp_upper_open_tt_rec_inv t kk X i' Heqi') as [EQ1 | EQ1].
        destruct EQ as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          left. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          destruct (le_lt_dec (kk+1) i) as [E | E].
            right. apply max_r. auto.
            left. apply max_l. omega.
        destruct EQ as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          left. apply max_r.
            assert (J''':=@open_te_bexp_tupper e kk X).
            omega.

          rewrite EQ1. rewrite EQ2.
          right. apply max_r. assumption.

    destruct (@max_dec (bexp_tupper (open_te_rec kk X e1)) (bexp_tupper (open_te_rec kk X e2))) as [J | J].
      rewrite J in EQ.
      assert ((bexp_tupper (open_te_rec kk X e2))<= (bexp_tupper (open_te_rec kk X e1))) as J'.
        rewrite <- J.
        apply le_max_r.
      remember (bexp_tupper (open_te_rec kk X e2)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHe1 in EQ.
      symmetry in Heqi'.
      apply IHe2 in Heqi'.
      destruct EQ as [EQ1 | EQ1].
        destruct Heqi' as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          left. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          left. apply max_l.
            assert (J''':=@open_te_bexp_tupper e1 kk X).
            omega.
        destruct Heqi' as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          destruct (le_lt_dec i (kk+1)).
             left. apply max_r. auto.
             right. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          right. apply max_l. auto.

      rewrite J in EQ.
      assert ((bexp_tupper (open_te_rec kk X e1))<= (bexp_tupper (open_te_rec kk X e2))) as J'.
        rewrite <- J.
        apply le_max_l.
      remember (bexp_tupper (open_te_rec kk X e1)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHe2 in EQ.
      symmetry in Heqi'.
      apply IHe1 in Heqi'.
      destruct EQ as [EQ2 | EQ2].
        destruct Heqi' as [EQ1 | EQ1].
          rewrite EQ1. rewrite EQ2.
          left. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          left. apply max_r.
            assert (J''':=@open_te_bexp_tupper e2 kk X).
            omega.
        destruct Heqi' as [EQ1 | EQ1].
          rewrite EQ1. rewrite EQ2.
          destruct (le_lt_dec i (kk+1)).
             left. apply max_l. auto.
             right. apply max_r. omega.

          rewrite EQ1. rewrite EQ2.
          right. apply max_r. auto.

    destruct (le_lt_dec (bexp_tupper (open_te_rec (S kk) X e)) 0).
      assert (bexp_tupper (open_te_rec (S kk) X e) = 0) as EQ'.
        omega.
      rewrite EQ' in *.
      assert (i = 0) as J. omega.
      subst. clear l J.
      apply IHe in EQ'.
      destruct EQ' as [J | J].
      left. rewrite J. omega.
      right. rewrite J. omega.
 
      assert (bexp_tupper (open_te_rec (S kk) X e)  = i  + 1) as EQ'.
         rewrite <- EQ.
        omega.
      apply IHe in EQ'.
      destruct EQ' as [J | J].
      left. rewrite J. omega.
      right. rewrite J. omega.
        
    destruct (@max_dec (bexp_tupper (open_te_rec kk X e)) (btyp_upper (open_tt_rec kk X t))) as [J | J].
      rewrite J in EQ.
      assert ((btyp_upper (open_tt_rec kk X t)) <=  (bexp_tupper (open_te_rec kk X e))) as J'.
        rewrite <- J.
        apply le_max_r.
      remember (btyp_upper (open_tt_rec kk X t)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHe in EQ.
      symmetry in Heqi'.
      destruct (@btyp_upper_open_tt_rec_inv t kk X i' Heqi') as [EQ1 | EQ1].
        destruct EQ as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          left. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          destruct (le_lt_dec i (kk+1)).
             left. apply max_r. auto.
             right. apply max_l. omega.
        destruct EQ as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          left. apply max_l.
            assert (J''':=@open_te_bexp_tupper e kk X).
            omega.

          rewrite EQ1. rewrite EQ2.
          right. apply max_l. auto.

      rewrite J in EQ.
      assert ((bexp_tupper (open_te_rec kk X e)) <= (btyp_upper (open_tt_rec kk X t))) as J'.
        rewrite <- J.
        apply le_max_l.
      remember (bexp_tupper (open_te_rec kk X e)) as i'.
      assert (i' <= i) as J''.
        omega.
      symmetry in Heqi'.
      apply IHe in Heqi'.
      destruct (@btyp_upper_open_tt_rec_inv t kk X i EQ) as [EQ1 | EQ1].
        destruct Heqi' as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          left. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          left. apply max_r.
            assert (J''':=@open_tt_btyp_upper t kk X).
            omega.
        destruct Heqi' as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          destruct (le_lt_dec (kk+1) i) as [E | E].
            right. apply max_r. auto.
            left. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          right. apply max_r. assumption.

    destruct (@max_dec (bexp_tupper (open_te_rec kk X e1)) (bexp_tupper (open_te_rec kk X e2))) as [J | J].
      rewrite J in EQ.
      assert ((bexp_tupper (open_te_rec kk X e2))<= (bexp_tupper (open_te_rec kk X e1))) as J'.
        rewrite <- J.
        apply le_max_r.
      remember (bexp_tupper (open_te_rec kk X e2)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHe1 in EQ.
      symmetry in Heqi'.
      apply IHe2 in Heqi'.
      destruct EQ as [EQ1 | EQ1].
        destruct Heqi' as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          left. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          left. apply max_l.
            assert (J''':=@open_te_bexp_tupper e1 kk X).
            omega.
        destruct Heqi' as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          destruct (le_lt_dec i (kk+1)).
             left. apply max_r. auto.
             right. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          right. apply max_l. auto.

      rewrite J in EQ.
      assert ((bexp_tupper (open_te_rec kk X e1))<= (bexp_tupper (open_te_rec kk X e2))) as J'.
        rewrite <- J.
        apply le_max_l.
      remember (bexp_tupper (open_te_rec kk X e1)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHe2 in EQ.
      symmetry in Heqi'.
      apply IHe1 in Heqi'.
      destruct EQ as [EQ2 | EQ2].
        destruct Heqi' as [EQ1 | EQ1].
          rewrite EQ1. rewrite EQ2.
          left. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          left. apply max_r.
            assert (J''':=@open_te_bexp_tupper e2 kk X).
            omega.
        destruct Heqi' as [EQ1 | EQ1].
          rewrite EQ1. rewrite EQ2.
          destruct (le_lt_dec i (kk+1)).
             left. apply max_l. auto.
             right. apply max_r. omega.

          rewrite EQ1. rewrite EQ2.
          right. apply max_r. auto.

    apply IHe in EQ.
    destruct EQ as [J | J].
    left. rewrite J. omega.
    right. rewrite J. omega.

    apply IHe in EQ.
    destruct EQ as [J | J].
    left. rewrite J. omega.
    right. rewrite J. omega.
Qed.

Lemma expr_bexp_tupper : forall e,
  expr e ->
  bexp_tupper e = 0.
Proof.
  intros e He.
  induction He; simpl; auto.
    pick fresh x.
    assert (x `notin` L) as xnL. auto.
    apply H1 in xnL; auto.
    apply bexp_tupper_open_ee_rec_inv in xnL.
    rewrite xnL.  rewrite type_btyp_upper; auto.

   rewrite IHHe1. rewrite IHHe2.
   apply max_l. auto.

    pick fresh X.
    assert (X `notin` L) as XnL. auto.
    apply H0 in XnL; auto.
    unfold open_te in XnL.
    apply bexp_tupper_open_te_rec_inv in XnL.
    destruct XnL as [J | J].
      rewrite J. omega.
      rewrite J. omega.

   rewrite type_btyp_upper; auto.
   rewrite IHHe; auto.

   rewrite IHHe1. rewrite IHHe2. auto.
Qed.

Lemma open_tc_bctx_tupper : forall C k (X:atom),
  bctx_tupper (open_tc_rec k X C) <= bctx_tupper C.
Proof.
  induction C; intros k0 X; simpl; auto.
    assert (J1:=@IHC k0 X).
    assert (J2:=@open_tt_btyp_upper t k0 X).     
    apply max_injective; auto.

    assert (J1:=@IHC k0 X).
    assert (J2:=@open_tt_btyp_upper t k0 X).     
    apply max_injective; auto.

    assert (J1:=@IHC k0 X). 
    assert (J2:=@open_te_bexp_tupper e k0 X).     
    apply max_injective; auto.

    assert (J1:=@open_te_bexp_tupper e k0 X). 
    assert (J2:=@IHC k0 X). 
    apply max_injective; auto.

    assert (J:=@IHC (S k0) X).
    omega. 

    assert (J:=@IHC (S k0) X).
    omega. 

    assert (J1:=@IHC k0 X).
    assert (J2:=@open_tt_btyp_upper t k0 X). 
    apply max_injective; auto.

    assert (J1:=@IHC k0 X).
    assert (J2:=@open_te_bexp_tupper e k0 X). 
    apply max_injective; auto.

    assert (J1:=@IHC k0 X).
    assert (J2:=@open_te_bexp_tupper e k0 X). 
    apply max_injective; auto.
Qed.

Lemma bctx_tupper_open_tc_rec_inv : forall C k (X:atom) i,
  bctx_tupper (open_tc_rec k X C)  = i ->
  bctx_tupper C = k +1 \/ bctx_tupper C = i.
Proof.
  induction C; intros kk X i EQ; simpl in *; auto.
    destruct (@max_dec (btyp_upper (open_tt_rec kk X t)) (bctx_tupper (open_tc_rec kk X C))) as [J | J].
      rewrite J in EQ.
      assert ((bctx_tupper (open_tc_rec kk X C))<= (btyp_upper (open_tt_rec kk X t))) as J'.
        rewrite <- J.
        apply le_max_r.
      remember (bctx_tupper (open_tc_rec kk X C)) as i'.
      assert (i' <= i) as J''.
        omega.
      symmetry in Heqi'.
      apply IHC in Heqi'.
      apply btyp_upper_open_tt_rec_inv in EQ.
      destruct EQ as [EQ1 | EQ1].
        destruct Heqi' as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          left. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          left. apply max_l.
            assert (J''':=@open_tt_btyp_upper t kk X).
            omega.
        destruct Heqi' as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          destruct (le_lt_dec i (kk+1)).
             left. apply max_r. auto.
             right. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          right. apply max_l. auto.

      rewrite J in EQ.
      assert ((btyp_upper (open_tt_rec kk X t)) <= (bctx_tupper (open_tc_rec kk X C))) as J'.
        rewrite <- J.
        apply le_max_l.
      remember (btyp_upper (open_tt_rec kk X t)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHC in EQ.
      symmetry in Heqi'.
      apply btyp_upper_open_tt_rec_inv in Heqi'.
      destruct EQ as [EQ2 | EQ2].
        destruct Heqi' as [EQ1 | EQ1].
          rewrite EQ1. rewrite EQ2.
          left. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          left. apply max_r.
            assert (J''':=@open_tc_bctx_tupper C kk X).
            omega.
        destruct Heqi' as [EQ1 | EQ1].
          rewrite EQ1. rewrite EQ2.
          destruct (le_lt_dec i (kk+1)).
             left. apply max_l. auto.
             right. apply max_r. omega.

          rewrite EQ1. rewrite EQ2.
          right. apply max_r. auto.
    
    destruct (@max_dec (btyp_upper (open_tt_rec kk X t)) (bctx_tupper (open_tc_rec kk X C))) as [J | J].
      rewrite J in EQ.
      assert ((bctx_tupper (open_tc_rec kk X C))<= (btyp_upper (open_tt_rec kk X t))) as J'.
        rewrite <- J.
        apply le_max_r.
      remember (bctx_tupper (open_tc_rec kk X C)) as i'.
      assert (i' <= i) as J''.
        omega.
      symmetry in Heqi'.
      apply IHC in Heqi'.
      apply btyp_upper_open_tt_rec_inv in EQ.
      destruct EQ as [EQ1 | EQ1].
        destruct Heqi' as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          left. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          left. apply max_l.
            assert (J''':=@open_tt_btyp_upper t kk X).
            omega.
        destruct Heqi' as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          destruct (le_lt_dec i (kk+1)).
             left. apply max_r. auto.
             right. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          right. apply max_l. auto.

      rewrite J in EQ.
      assert ((btyp_upper (open_tt_rec kk X t)) <= (bctx_tupper (open_tc_rec kk X C))) as J'.
        rewrite <- J.
        apply le_max_l.
      remember (btyp_upper (open_tt_rec kk X t)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHC in EQ.
      symmetry in Heqi'.
      apply btyp_upper_open_tt_rec_inv in Heqi'.
      destruct EQ as [EQ2 | EQ2].
        destruct Heqi' as [EQ1 | EQ1].
          rewrite EQ1. rewrite EQ2.
          left. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          left. apply max_r.
            assert (J''':=@open_tc_bctx_tupper C kk X).
            omega.
        destruct Heqi' as [EQ1 | EQ1].
          rewrite EQ1. rewrite EQ2.
          destruct (le_lt_dec i (kk+1)).
             left. apply max_l. auto.
             right. apply max_r. omega.

          rewrite EQ1. rewrite EQ2.
          right. apply max_r. auto.

    destruct (@max_dec (bctx_tupper (open_tc_rec kk X C)) (bexp_tupper (open_te_rec kk X e))) as [J | J].
      rewrite J in EQ.
      assert ((bexp_tupper (open_te_rec kk X e)) <= (bctx_tupper (open_tc_rec kk X C))) as J'.
        rewrite <- J.
        apply le_max_r.
      remember (bexp_tupper (open_te_rec kk X e)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHC in EQ.
      symmetry in Heqi'.
      apply bexp_tupper_open_te_rec_inv in Heqi'.
      destruct EQ as [EQ2 | EQ2].
        destruct Heqi' as [EQ1 | EQ1].
          rewrite EQ1. rewrite EQ2.
          left. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          left. apply max_l.
            assert (J''':=@open_tc_bctx_tupper C kk X).
            omega.
        destruct Heqi' as [EQ1 | EQ1].
          rewrite EQ1. rewrite EQ2.
          destruct (le_lt_dec i (kk+1)).
             left. apply max_r. auto.
             right. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          right. apply max_l. auto.

      rewrite J in EQ.
      assert ((bctx_tupper (open_tc_rec kk X C)) <= (bexp_tupper (open_te_rec kk X e))) as J'.
        rewrite <- J.
        apply le_max_l.
      remember (bctx_tupper (open_tc_rec kk X C)) as i'.
      assert (i' <= i) as J''.
        omega.
      symmetry in Heqi'.
      apply IHC in Heqi'.
      apply bexp_tupper_open_te_rec_inv in EQ.
      destruct EQ as [EQ1 | EQ1].
        destruct Heqi' as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          left. apply max_r. omega.

          rewrite EQ1. rewrite EQ2.
          left. apply max_r.
            assert (J''':=@open_te_bexp_tupper e kk X).
            omega.
        destruct Heqi' as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          destruct (le_lt_dec i (kk+1)).
             left. apply max_l. auto.
             right. apply max_r. omega.

          rewrite EQ1. rewrite EQ2.
          right. apply max_r. auto.

    destruct (@max_dec (bexp_tupper (open_te_rec kk X e)) (bctx_tupper (open_tc_rec kk X C))) as [J | J].
      rewrite J in EQ.
      assert ((bctx_tupper (open_tc_rec kk X C)) <= (bexp_tupper (open_te_rec kk X e))) as J'.
        rewrite <- J.
        apply le_max_r.
      remember (bctx_tupper (open_tc_rec kk X C)) as i'.
      assert (i' <= i) as J''.
        omega.
      symmetry in Heqi'.
      apply IHC in Heqi'.
      apply bexp_tupper_open_te_rec_inv in EQ.
      destruct EQ as [EQ1 | EQ1].
        destruct Heqi' as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          left. apply max_r. omega.

          rewrite EQ1. rewrite EQ2.
          left. apply max_l.
            assert (J''':=@open_te_bexp_tupper e kk X).
            omega.
        destruct Heqi' as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          destruct (le_lt_dec i (kk+1)).
             left. apply max_r. auto.
             right. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          right. apply max_l. auto.

      rewrite J in EQ.
      assert ((bexp_tupper (open_te_rec kk X e)) <= (bctx_tupper (open_tc_rec kk X C))) as J'.
        rewrite <- J.
        apply le_max_l.
      remember (bexp_tupper (open_te_rec kk X e)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHC in EQ.
      symmetry in Heqi'.
      apply bexp_tupper_open_te_rec_inv in Heqi'.
      destruct EQ as [EQ2 | EQ2].
        destruct Heqi' as [EQ1 | EQ1].
          rewrite EQ1. rewrite EQ2.
          left. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          left. apply max_r.
            assert (J''':=@open_tc_bctx_tupper C kk X).
            omega.
        destruct Heqi' as [EQ1 | EQ1].
          rewrite EQ1. rewrite EQ2.
          destruct (le_lt_dec i (kk+1)).
             left. apply max_l. auto.
             right. apply max_r. omega.

          rewrite EQ1. rewrite EQ2.
          right. apply max_r. auto.

    destruct (le_lt_dec (bctx_tupper (open_tc_rec (S kk) X C)) 0).
      assert (bctx_tupper (open_tc_rec (S kk) X C) = 0) as EQ'.
        omega.
      rewrite EQ' in *.
      assert (i = 0) as J. omega.
      subst. clear l J.
      apply IHC in EQ'.
      destruct EQ' as [J | J].
      left. rewrite J. omega.
      right. rewrite J. omega.

      assert (bctx_tupper (open_tc_rec (S kk) X C)  = i  + 1) as EQ'.
         rewrite <- EQ.
        omega.
      apply IHC in EQ'.
      destruct EQ' as [J | J].
      left. rewrite J. omega.
      right. rewrite J. omega.

    destruct (le_lt_dec (bctx_tupper (open_tc_rec (S kk) X C)) 0).
      assert (bctx_tupper (open_tc_rec (S kk) X C) = 0) as EQ'.
        omega.
      rewrite EQ' in *.
      assert (i = 0) as J. omega.
      subst. clear l J.
      apply IHC in EQ'.
      destruct EQ' as [J | J].
      left. rewrite J. omega.
      right. rewrite J. omega.

      assert (bctx_tupper (open_tc_rec (S kk) X C)  = i  + 1) as EQ'.
         rewrite <- EQ.
        omega.
      apply IHC in EQ'.
      destruct EQ' as [J | J].
      left. rewrite J. omega.
      right. rewrite J. omega.

    destruct (@max_dec (bctx_tupper (open_tc_rec kk X C)) (btyp_upper (open_tt_rec kk X t))) as [J | J].
      rewrite J in EQ.
      assert ((btyp_upper (open_tt_rec kk X t)) <= (bctx_tupper (open_tc_rec kk X C))) as J'.
        rewrite <- J.
        apply le_max_r.
      remember (btyp_upper (open_tt_rec kk X t)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHC in EQ.
      symmetry in Heqi'.
      apply btyp_upper_open_tt_rec_inv in Heqi'.
      destruct EQ as [EQ2 | EQ2].
        destruct Heqi' as [EQ1 | EQ1].
          rewrite EQ1. rewrite EQ2.
          left. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          left. apply max_l.
            assert (J''':=@open_tc_bctx_tupper C kk X).
            omega.
        destruct Heqi' as [EQ1 | EQ1].
          rewrite EQ1. rewrite EQ2.
          destruct (le_lt_dec i (kk+1)).
             left. apply max_r. auto.
             right. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          right. apply max_l. auto.

      rewrite J in EQ.
      assert ((bctx_tupper (open_tc_rec kk X C))<= (btyp_upper (open_tt_rec kk X t))) as J'.
        rewrite <- J.
        apply le_max_l.
      remember (bctx_tupper (open_tc_rec kk X C)) as i'.
      assert (i' <= i) as J''.
        omega.
      symmetry in Heqi'.
      apply IHC in Heqi'.
      apply btyp_upper_open_tt_rec_inv in EQ.
      destruct EQ as [EQ1 | EQ1].
        destruct Heqi' as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          left. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          left. apply max_r.
            assert (J''':=@open_tt_btyp_upper t kk X).
            omega.
        destruct Heqi' as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          destruct (le_lt_dec i (kk+1)).
             left. apply max_l. auto.
             right. apply max_r. omega.

          rewrite EQ1. rewrite EQ2.
          right. apply max_r. auto.

    destruct (@max_dec (bctx_tupper (open_tc_rec kk X C)) (bexp_tupper (open_te_rec kk X e))) as [J | J].
      rewrite J in EQ.
      assert ((bexp_tupper (open_te_rec kk X e)) <= (bctx_tupper (open_tc_rec kk X C))) as J'.
        rewrite <- J.
        apply le_max_r.
      remember (bexp_tupper (open_te_rec kk X e)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHC in EQ.
      symmetry in Heqi'.
      apply bexp_tupper_open_te_rec_inv in Heqi'.
      destruct EQ as [EQ2 | EQ2].
        destruct Heqi' as [EQ1 | EQ1].
          rewrite EQ1. rewrite EQ2.
          left. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          left. apply max_l.
            assert (J''':=@open_tc_bctx_tupper C kk X).
            omega.
        destruct Heqi' as [EQ1 | EQ1].
          rewrite EQ1. rewrite EQ2.
          destruct (le_lt_dec i (kk+1)).
             left. apply max_r. auto.
             right. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          right. apply max_l. auto.

      rewrite J in EQ.
      assert ((bctx_tupper (open_tc_rec kk X C)) <= (bexp_tupper (open_te_rec kk X e))) as J'.
        rewrite <- J.
        apply le_max_l.
      remember (bctx_tupper (open_tc_rec kk X C)) as i'.
      assert (i' <= i) as J''.
        omega.
      symmetry in Heqi'.
      apply IHC in Heqi'.
      apply bexp_tupper_open_te_rec_inv in EQ.
      destruct EQ as [EQ1 | EQ1].
        destruct Heqi' as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          left. apply max_r. omega.

          rewrite EQ1. rewrite EQ2.
          left. apply max_r.
            assert (J''':=@open_te_bexp_tupper e kk X).
            omega.
        destruct Heqi' as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          destruct (le_lt_dec i (kk+1)).
             left. apply max_l. auto.
             right. apply max_r. omega.

          rewrite EQ1. rewrite EQ2.
          right. apply max_r. auto.

    destruct (@max_dec (bexp_tupper (open_te_rec kk X e)) (bctx_tupper (open_tc_rec kk X C))) as [J | J].
      rewrite J in EQ.
      assert ((bctx_tupper (open_tc_rec kk X C)) <= (bexp_tupper (open_te_rec kk X e))) as J'.
        rewrite <- J.
        apply le_max_r.
      remember (bctx_tupper (open_tc_rec kk X C)) as i'.
      assert (i' <= i) as J''.
        omega.
      symmetry in Heqi'.
      apply IHC in Heqi'.
      apply bexp_tupper_open_te_rec_inv in EQ.
      destruct EQ as [EQ1 | EQ1].
        destruct Heqi' as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          left. apply max_r. omega.

          rewrite EQ1. rewrite EQ2.
          left. apply max_l.
            assert (J''':=@open_te_bexp_tupper e kk X).
            omega.
        destruct Heqi' as [EQ2 | EQ2].
          rewrite EQ1. rewrite EQ2.
          destruct (le_lt_dec i (kk+1)).
             left. apply max_r. auto.
             right. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          right. apply max_l. auto.

      rewrite J in EQ.
      assert ((bexp_tupper (open_te_rec kk X e)) <= (bctx_tupper (open_tc_rec kk X C))) as J'.
        rewrite <- J.
        apply le_max_l.
      remember (bexp_tupper (open_te_rec kk X e)) as i'.
      assert (i' <= i) as J''.
        omega.
      apply IHC in EQ.
      symmetry in Heqi'.
      apply bexp_tupper_open_te_rec_inv in Heqi'.
      destruct EQ as [EQ2 | EQ2].
        destruct Heqi' as [EQ1 | EQ1].
          rewrite EQ1. rewrite EQ2.
          left. apply max_l. omega.

          rewrite EQ1. rewrite EQ2.
          left. apply max_r.
            assert (J''':=@open_tc_bctx_tupper C kk X).
            omega.
        destruct Heqi' as [EQ1 | EQ1].
          rewrite EQ1. rewrite EQ2.
          destruct (le_lt_dec i (kk+1)).
             left. apply max_l. auto.
             right. apply max_r. omega.

          rewrite EQ1. rewrite EQ2.
          right. apply max_r. auto.
    
    apply IHC in EQ.
    destruct EQ as [J | J].
    left. rewrite J. omega.
    right. rewrite J. omega.

    apply IHC in EQ.
    destruct EQ as [J | J].
    left. rewrite J. omega.
    right. rewrite J. omega.
Qed.

Lemma context_bctx_tupper : forall C,
  context C ->
  bctx_tupper C = 0.
Proof.
  intros C HC.
  induction HC; simpl; auto.
    pick fresh x.
    assert (x `notin` L) as xnL. auto.
    apply H1 in xnL; auto.
    apply bctx_tupper_open_ec_rec_inv in xnL.
    rewrite xnL.  rewrite type_btyp_upper; auto.

    pick fresh x.
    assert (x `notin` L) as xnL. auto.
    apply H1 in xnL; auto.
    apply bctx_tupper_open_ec_rec_inv in xnL.
    rewrite xnL.  rewrite type_btyp_upper; auto.

   rewrite IHHC. rewrite expr_bexp_tupper; auto.

   rewrite IHHC. rewrite expr_bexp_tupper; auto.

    pick fresh X.
    assert (X `notin` L) as XnL. auto.
    apply H0 in XnL; auto.
    apply bctx_tupper_open_tc_rec_inv in XnL.
    destruct XnL as [J | J].
      rewrite J. omega.
      rewrite J. omega.

    pick fresh X.
    assert (X `notin` L) as XnL. auto.
    apply H0 in XnL; auto.
    apply bctx_tupper_open_tc_rec_inv in XnL.
    destruct XnL as [J | J].
      rewrite J. omega.
      rewrite J. omega.

   rewrite IHHC. rewrite type_btyp_upper; auto.

   rewrite IHHC. rewrite expr_bexp_tupper; auto.

   rewrite IHHC. rewrite expr_bexp_tupper; auto.
Qed.

Lemma close_open_tc__subst_tc : forall C X Y,
  context C ->
  open_tc (close_tc C X) Y = subst_tc X Y C.
Proof.
  intros C x y HC.
  unfold open_tc.
  unfold close_tc.
  apply close_open_tc_rec__subst_tc; auto.
    rewrite context_bctx_tupper; auto.
Qed.

Lemma subst_tc_open_ec_rec : forall C1 e2 X U k,
  type U ->
  subst_tc X U (open_ec_rec k e2 C1) =
    open_ec_rec k (subst_te X U e2) (subst_tc X U C1).
Proof with try solve [congruence | intuition].
  intros C1 e2 X U k WP. revert k.
  induction C1; intros K; simpl; f_equal...
    apply subst_te_open_ee_rec; auto.
    apply subst_te_open_ee_rec; auto.
    apply subst_te_open_ee_rec; auto.
    apply subst_te_open_ee_rec; auto.
Qed.

Lemma subst_tc_open_ec_var : forall (X y:atom) U C,
  y <> X ->
  type U ->
  open_ec (subst_tc X U C) y = subst_tc X U (open_ec C y).
Proof with try solve [congruence | intuition].
  intros X y U C Neq Wu.
  unfold open_ec.
  rewrite subst_tc_open_ec_rec...
Qed.

Lemma subst_tc_open_tc_rec : forall C1 t2 X U k,
  type U ->
  subst_tc X U (open_tc_rec k t2 C1) =
    open_tc_rec k  (subst_tt X U t2) (subst_tc X U C1).
Proof with try solve [congruence | intuition].
  intros C1 t2 X U k WP. revert k.
  induction C1; intros K; simpl; f_equal...
    apply subst_tt_open_tt_rec; auto.
    apply subst_tt_open_tt_rec; auto.
    apply subst_te_open_te_rec; auto.
    apply subst_te_open_te_rec; auto.
    apply subst_tt_open_tt_rec; auto.
    apply subst_te_open_te_rec; auto.
    apply subst_te_open_te_rec; auto.
Qed.

Lemma subst_tc_open_tc_var : forall (X Y:atom) U C,
  Y <> X ->
  type U ->
  open_tc (subst_tc X U C) Y = subst_tc X U (open_tc C Y).
Proof with try solve [congruence | intuition].
  intros X Y U C Neq Wu.
  unfold open_tc.
  rewrite subst_tc_open_tc_rec...
    simpl.
    destruct (Y == X); subst; auto.
       contradict Neq; auto.
Qed.

Lemma subst_tc_context : forall z C t,
  context C ->
  type t ->
  context (subst_tc z t C).
Proof with auto.
  intros z C e HC He.
  induction HC; simpl; auto.
    apply context_abs_free with (L:=L `union` singleton z); auto.
      intros x xnL.
      rewrite subst_tc_open_ec_var; auto.
    apply context_abs_capture with (L:=L `union` singleton z); auto.
      intros x xnL.
      rewrite subst_tc_open_ec_var; auto.
    apply context_tabs_free with (L:=L `union` singleton z); auto.
      intros X XnL.
      rewrite subst_tc_open_tc_var; auto.
    apply context_tabs_capture with (L:=L `union` singleton z); auto.
      intros X XnL.
      rewrite subst_tc_open_tc_var; auto.
Qed.

Lemma cv_ec_open_ec_rec : forall C k x,
  cv_ec (open_ec_rec k x C) [=] cv_ec C.
Proof.
  induction C; intros k0 x; simpl; auto.
Qed.

Lemma cv_ec_open_tc_rec : forall C k X,
  cv_ec (open_tc_rec k X C) [=] cv_ec C.
Proof.
  induction C; intros k0 X; simpl; auto.
Qed.

Lemma cv_ec_close_ec_rec : forall C k x,
  cv_ec (close_ec_rec k x C) [=] cv_ec C.
Proof.
  induction C; intros k0 x; simpl; auto.
Qed.

Lemma cv_ec_close_tc_rec : forall C k X,
  cv_ec (close_tc_rec k X C) [=] cv_ec C.
Proof.
  induction C; intros k0 X; simpl; auto.
Qed.

Lemma subst_ee_close_ee_rec : forall e1 y x u k,
  y `notin` (fv_ee u) ->
  x <> y ->
  subst_ee x u (close_ee_rec k y e1) =
    close_ee_rec k y (subst_ee x u e1).
Proof with auto*.
  intros e1 y x u k H1 H2. revert k.
  induction e1; intros k0; simpl; f_equal...
  Case "exp_fvar".
    destruct (y == a); subst...
      destruct (a == x); simpl; subst...
        contradict H2; auto.
        destruct (a == a); subst...
          contradict n0; auto.
      destruct (a == x); subst...
        rewrite <- close_ee_rec_expr; auto.
        simpl.
        destruct (x == x); subst...
          contradict n0; auto.

        rewrite <- close_ee_rec_expr; auto.
        simpl.
        destruct (a == x); subst...
          contradict n0; auto.
Qed.

Lemma subst_ee_close_ee : forall e1 y x u,
  y `notin` (fv_ee u) ->
  x <> y ->
  subst_ee x u (close_ee e1 y) =
    close_ee (subst_ee x u e1) y.
Proof with auto*.
  intros.
  unfold close_ee.
  apply subst_ee_close_ee_rec...
Qed.

Lemma subst_ec_close_ec_rec : forall C1 y x u k,
  y `notin` (fv_ee u) ->
  x <> y ->
  subst_ec x u (close_ec_rec k y C1) =
    close_ec_rec k y (subst_ec x u C1).
Proof with auto*.
  intros C1 y x u k H1 H2. revert k.
  induction C1; intros k0; simpl; f_equal...
    rewrite subst_ee_close_ee_rec; auto.
    rewrite subst_ee_close_ee_rec; auto.
    rewrite subst_ee_close_ee_rec; auto.
    rewrite subst_ee_close_ee_rec; auto.
Qed.

Lemma subst_ec_close_ec : forall C1 y x u,
  y `notin` (fv_ee u) ->
  x <> y ->
  subst_ec x u (close_ec C1 y) =
    close_ec (subst_ec x u C1) y.
Proof with auto*.
  intros.
  unfold close_ec.
  apply subst_ec_close_ec_rec...
Qed.

Lemma subst_ee_close_te_rec : forall e1 Y x u k,
  Y `notin` (fv_te u) ->
  x <> Y ->
  subst_ee x u (close_te_rec k Y e1) =
    close_te_rec k Y (subst_ee x u e1).
Proof with auto*.
  intros e1 Y x u k H1 H2. revert k.
  induction e1; intros k0; simpl; f_equal...
  Case "exp_fvar".
      destruct (a == x); simpl; subst...
        rewrite <- close_te_rec_expr; auto.
Qed.

Lemma subst_ee_close_te : forall e1 Y x u,
  Y `notin` (fv_te u) ->
  x <> Y ->
  subst_ee x u (close_te e1 Y) =
    close_te (subst_ee x u e1) Y.
Proof with auto*.
  intros.
  unfold close_te.
  apply subst_ee_close_te_rec...
Qed.

Lemma subst_ec_close_tc_rec : forall C1 Y x u k,
  Y `notin` (fv_te u) ->
  x <> Y ->
  subst_ec x u (close_tc_rec k Y C1) =
    close_tc_rec k Y (subst_ec x u C1).
Proof with auto*.
  intros C1 Y x u k H1 H2. revert k.
  induction C1; intros k0; simpl; f_equal...
    rewrite subst_ee_close_te_rec; auto.
    rewrite subst_ee_close_te_rec; auto.
    rewrite subst_ee_close_te_rec; auto.
    rewrite subst_ee_close_te_rec; auto.
Qed.

Lemma subst_ec_close_tc : forall C1 Y x u,
  Y `notin` (fv_te u) ->
  x <> Y ->
  subst_ec x u (close_tc C1 Y) =
    close_tc (subst_ec x u C1) Y.
Proof with auto*.
  intros.
  unfold close_tc.
  apply subst_ec_close_tc_rec...
Qed.


Lemma notin_close_tt_rec : forall T Y kk,
  Y `notin` (fv_tt (close_tt_rec kk Y T)).
Proof.
  induction T; intros  kk; intros; simpl; auto.
    destruct (kk==a); auto.
Qed.

Lemma notin_close_tt : forall T Y,
  Y `notin` (fv_tt (close_tt T Y)).
Proof.
  intros. unfold close_tt.
  apply notin_close_tt_rec; auto.
Qed.    

Lemma cv_ec_subst_ec_rec : forall C x e,
  cv_ec (subst_ec x e C) [=] cv_ec C.
Proof.
  induction C; intros x ee; simpl; auto.
Qed.

Lemma cv_ec_subst_tc_rec : forall C x t,
  cv_ec (subst_tc x t C) [=] cv_ec C.
Proof.
  induction C; intros x tt; simpl; auto.
Qed.

Lemma open_ec_rec_fv_ec_upper : forall C1 e2 kk,
  fv_ec (open_ec_rec kk e2 C1) [<=] fv_ec C1 `union` fv_ee e2.
Proof.
  induction C1; intros e2 kk; simpl; try solve [eauto | fsetdec].
    assert (J:=@open_ee_rec_fv_ee_upper e e2 kk).
    assert (J':=@IHC1 e2 kk).
    fsetdec.

    assert (J:=@open_ee_rec_fv_ee_upper e e2 kk).
    assert (J':=@IHC1 e2 kk).
    fsetdec.

    assert (J:=@open_ee_rec_fv_ee_upper e e2 kk).
    assert (J':=@IHC1 e2 kk).
    fsetdec.

    assert (J:=@open_ee_rec_fv_ee_upper e e2 kk).
    assert (J':=@IHC1 e2 kk).
    fsetdec.
Qed.

Lemma open_ec_fv_ec_upper : forall C1 e2,
  fv_ec (open_ec C1 e2) [<=] fv_ec C1 `union` fv_ee e2.
Proof.
  intros. apply open_ec_rec_fv_ec_upper.
Qed.

Lemma open_ec_rec_fv_ec_lower : forall C1 e2 kk,
  fv_ec C1 [<=] fv_ec (open_ec_rec kk e2 C1).
Proof.
  induction C1; intros e2 kk; simpl; try solve [eauto | fsetdec].
    assert (J:=@open_ee_rec_fv_ee_lower e e2 kk).
    assert (J':=@IHC1 e2 kk).
    fsetdec.

    assert (J:=@open_ee_rec_fv_ee_lower e e2 kk).
    assert (J':=@IHC1 e2 kk).
    fsetdec.

    assert (J:=@open_ee_rec_fv_ee_lower e e2 kk).
    assert (J':=@IHC1 e2 kk).
    fsetdec.

    assert (J:=@open_ee_rec_fv_ee_lower e e2 kk).
    assert (J':=@IHC1 e2 kk).
    fsetdec.
Qed.

Lemma open_ec_fv_ec_lower : forall C1 e2,
  fv_ec C1 [<=] fv_ec (open_ec C1 e2).
Proof.
  intros. apply open_ec_rec_fv_ec_lower.
Qed.

Lemma close_ee_rec_fv_ee_upper : forall e1 x kk,
  fv_ee (close_ee_rec kk x e1) [<=] fv_ee e1.
Proof.
  induction e1; intros x kk; simpl; try solve [eauto | fsetdec].
     destruct (x==a); subst; simpl; fsetdec.

     assert (J1:=@IHe1_1 x kk).
     assert (J2:=@IHe1_2 x kk).
     fsetdec.
    
     assert (J1:=@IHe1_1 x kk).
     assert (J2:=@IHe1_2 x kk).
     fsetdec.
Qed.

Lemma close_ee_fv_ee_upper : forall e1 x,
  fv_ee (close_ee e1 x) [<=] fv_ee e1.
Proof.
  intros. apply close_ee_rec_fv_ee_upper.
Qed.

Lemma close_ec_rec_fv_ec_upper : forall C1 x kk,
  fv_ec (close_ec_rec kk x C1) [<=] fv_ec C1.
Proof.
  induction C1; intros x kk; simpl; try solve [eauto | fsetdec].
    assert (J:=@close_ee_rec_fv_ee_upper e x kk).
    assert (J':=@IHC1 x kk).
    fsetdec.

    assert (J:=@close_ee_rec_fv_ee_upper e x kk).
    assert (J':=@IHC1 x kk).
    fsetdec.

    assert (J:=@close_ee_rec_fv_ee_upper e x kk).
    assert (J':=@IHC1 x kk).
    fsetdec.

    assert (J:=@close_ee_rec_fv_ee_upper e x kk).
    assert (J':=@IHC1 x kk).
    fsetdec.
Qed.

Lemma close_ec_fv_ec_upper : forall C1 x,
  fv_ec (close_ec C1 x) [<=] fv_ec C1.
Proof.
  intros. apply close_ec_rec_fv_ec_upper.
Qed.

Lemma subst_ec_fresh : forall (x: atom) u C,
  x `notin` fv_ec C ->
  C = subst_ec x u C.
Proof with try solve [congruence | intuition].
  intros x u C; induction C; simpl; intro H; f_equal...
    apply subst_ee_fresh; auto.
    apply subst_ee_fresh; auto.
    apply subst_ee_fresh; auto.
    apply subst_ee_fresh; auto.
Qed.

Lemma close_ec_rec_fv_ec_eq : forall C k x,
  cv_ec (close_ec_rec k x C) [=] cv_ec C.
Proof.
  induction C; intros kk x; simpl; auto.
Qed.

Lemma close_ec_fv_ec_eq : forall C x,
  cv_ec (close_ec C x) [=] cv_ec C.
Proof.
  unfold close_ec. intros.
  apply close_ec_rec_fv_ec_eq; auto.
Qed.

Lemma shift_te_expr : forall e,
  expr e ->
  e = shift_te e.
Proof.
  intros e He.
  unfold shift_te.
  apply shift_te_rec_expr; auto.
Qed.

Lemma open_te_expr' : forall u e,
  expr e ->
  e = open_te e u.
Proof.
  intros e He.
  unfold open_te.
  apply open_te_rec_expr; auto.
Qed.

Lemma close_open_te__subst_te : forall e X Y,
  expr e ->
  open_te (close_te e X) Y = subst_te X Y e.
Proof.
  intros e X Y He.
  unfold open_te.
  unfold close_te.
  apply close_open_te_rec__subst_te; auto.
    rewrite expr_bexp_tupper; auto.
Qed.

Lemma subst_tlb_id : forall E X,
  map (subst_tlb X X) E = E.
Proof.
  induction E; intros X; simpl; auto.
    destruct a. 
    destruct l; simpl. 
    rewrite IHE.
    rewrite subst_tt_id; auto.
Qed.

Lemma subst_te_id : forall e X,
  subst_te X X e = e.
Proof.
  induction e; intros X; simpl; auto.
    rewrite IHe.
    rewrite subst_tt_id; auto.

    rewrite IHe1.
    rewrite IHe2; auto.

    rewrite IHe; auto.

    rewrite IHe.
    rewrite subst_tt_id; auto.

    rewrite IHe1.
    rewrite IHe2; auto.

    rewrite IHe; auto.

    rewrite IHe; auto.
Qed.

Lemma subst_tc_id : forall C X,
  subst_tc X X C = C.
Proof.
  induction C; intros X; simpl; 
  try solve [
    auto |
    rewrite IHC;
    rewrite subst_tt_id; auto |
    rewrite IHC;
    rewrite subst_te_id; auto |
    rewrite IHC; auto].
Qed.

Lemma subst_te_close_ee_rec : forall e1 y X U k,
  subst_te X U (close_ee_rec k y e1) =
    close_ee_rec k y (subst_te X U e1).
Proof with auto*.
  intros e1 y X U k. revert k.
  induction e1; intros k0; simpl; f_equal...
  Case "exp_fvar".
    destruct (y == a); subst...
Qed.

Lemma subst_te_close_ee : forall e1 y X U,
  subst_te X U (close_ee e1 y) =
    close_ee (subst_te X U e1) y.
Proof with auto*.
  intros.
  unfold close_ee.
  apply subst_te_close_ee_rec...
Qed.

Lemma subst_tc_close_ec_rec : forall C1 y X U k,
  subst_tc X U (close_ec_rec k y C1) =
    close_ec_rec k y (subst_tc X U C1).
Proof with auto*.
  intros C1 y X U k. revert k.
  induction C1; intros k0; simpl; f_equal...
    rewrite subst_te_close_ee_rec; auto.
    rewrite subst_te_close_ee_rec; auto.
    rewrite subst_te_close_ee_rec; auto.
    rewrite subst_te_close_ee_rec; auto.
Qed.

Lemma subst_tc_close_ec : forall C1 y X U,
  subst_tc X U (close_ec C1 y) =
    close_ec (subst_tc X U C1) y.
Proof with auto*.
  intros.
  unfold close_ec.
  apply subst_tc_close_ec_rec...
Qed.

Lemma subst_tt_close_tt_rec : forall T Y X U k,
  Y `notin` (fv_tt U) ->
  X <> Y ->
  subst_tt X U (close_tt_rec k Y T) =
    close_tt_rec k Y (subst_tt X U T).
Proof with auto*.
  intros T Y X U k H1 H2. revert k.
  induction T; intros k0; simpl; f_equal...
  Case "typ_fvar".
    destruct (Y == a); subst...
      destruct (a == X); simpl; subst...
        contradict H2; auto.
        destruct (a == a); subst...
          contradict n0; auto.
      destruct (a == X); subst...
        rewrite <- close_tt_rec_typ; auto.
        simpl.
        destruct (X == X); subst...
          contradict n0; auto.

        rewrite <- close_tt_rec_typ; auto.
        simpl.
        destruct (a == X); subst...
          contradict n0; auto.
Qed.

Lemma subst_tt_close_tt : forall T Y X U,
  Y `notin` (fv_tt U) ->
  X <> Y ->
  subst_tt X U (close_tt T Y) =
    close_tt (subst_tt X U T) Y.
Proof with auto*.
  intros.
  unfold close_tt.
  apply subst_tt_close_tt_rec...
Qed.

Lemma subst_te_close_te_rec : forall e1 Y X U k,
  Y `notin` (fv_tt U) ->
  X <> Y ->
  subst_te X U (close_te_rec k Y e1) =
    close_te_rec k Y (subst_te X U e1).
Proof with auto*.
  intros e1 Y X U k H1 H2. revert k.
  induction e1; intros k0; simpl; f_equal...
    rewrite subst_tt_close_tt_rec; auto.
    rewrite subst_tt_close_tt_rec; auto.
Qed.

Lemma subst_te_close_te : forall e1 Y X U,
  Y `notin` (fv_tt U) ->
  X <> Y ->
  subst_te X U (close_te e1 Y) =
    close_te (subst_te X U e1) Y.
Proof with auto*.
  intros.
  unfold close_te.
  apply subst_te_close_te_rec...
Qed.

Lemma subst_tc_close_tc_rec : forall C1 Y X U k,
  Y `notin` (fv_tt U) ->
  X <> Y ->
  subst_tc X U (close_tc_rec k Y C1) =
    close_tc_rec k Y (subst_tc X U C1).
Proof with auto*.
  intros C1 Y X U k H1 H2. revert k.
  induction C1; intros k0; simpl; f_equal...
    rewrite subst_tt_close_tt_rec; auto.
    rewrite subst_tt_close_tt_rec; auto.
    rewrite subst_te_close_te_rec; auto.
    rewrite subst_te_close_te_rec; auto.
    rewrite subst_tt_close_tt_rec; auto.
    rewrite subst_te_close_te_rec; auto.
    rewrite subst_te_close_te_rec; auto.
Qed.

Lemma subst_tc_close_tc : forall C1 Y X U,
  Y `notin` (fv_tt U) ->
  X <> Y ->
  subst_tc X U (close_tc C1 Y) =
    close_tc (subst_tc X U C1) Y.
Proof with auto*.
  intros.
  unfold close_tc.
  apply subst_tc_close_tc_rec...
Qed.

Lemma subst_te_fv_ee_eq : forall e X U,
  fv_ee (subst_te X U e) [=] fv_ee e.
Proof.
  induction e; intros X U; simpl; try solve [eauto | fsetdec].
Qed.

  
Lemma open_ee_open_ee_rec__commut : forall e kx ky (x y:atom),
  kx <> ky ->
  (open_ee_rec kx x (open_ee_rec ky y e)) = 
    (open_ee_rec ky y (open_ee_rec kx x e)).
Proof.
  induction e; intros kx ky x y; intros; simpl; auto.
    destruct (ky == n); subst; simpl.
      destruct (kx == n); subst; simpl; auto.
        contradict H; auto.
        destruct (n == n); subst; simpl; auto.
          contradict n1; auto.
      destruct (kx == n); subst; simpl; auto.
        destruct (ky == n); subst; simpl; auto.
          contradict n0; auto.

    rewrite IHe; auto.

    rewrite IHe1; auto.
    rewrite IHe2; auto.

    rewrite IHe; auto.

    rewrite IHe; auto.

    rewrite IHe1; auto.
    rewrite IHe2; auto.

    rewrite IHe; auto.

    rewrite IHe; auto.
Qed.

Lemma open_ee_open_te_rec__commut : forall e kx kY (x Y:atom),
  (open_ee_rec kx x (open_te_rec kY Y e)) = 
    (open_te_rec kY Y (open_ee_rec kx x e)).
Proof.
  induction e; intros kx kY x Y; intros; simpl; auto.
    destruct (kx == n); subst; simpl; auto.

    rewrite IHe; auto.

    rewrite IHe1; auto.
    rewrite IHe2; auto.

    rewrite IHe; auto.

    rewrite IHe; auto.

    rewrite IHe1; auto.
    rewrite IHe2; auto.

    rewrite IHe; auto.

    rewrite IHe; auto.
Qed.

Lemma open_tt_open_tt_rec__commut : forall t kx ky (x y:atom),
  kx <> ky ->
  (open_tt_rec kx x (open_tt_rec ky y t)) = 
    (open_tt_rec ky y (open_tt_rec kx x t)).
Proof.
  induction t; intros kx ky x y; intros; simpl; auto.
    destruct (ky == n); subst; simpl.
      destruct (kx == n); subst; simpl; auto.
        contradict H; auto.
        destruct (n == n); subst; simpl; auto.
          contradict n1; auto.
      destruct (kx == n); subst; simpl; auto.
        destruct (ky == n); subst; simpl; auto.
          contradict n0; auto.

    rewrite IHt1; auto.
    rewrite IHt2; auto.

    rewrite IHt; auto.

    rewrite IHt1; auto.
    rewrite IHt2; auto.
Qed.

Lemma open_te_open_te_rec__commut : forall e kx ky (x y:atom),
  kx <> ky ->
  (open_te_rec kx x (open_te_rec ky y e)) = 
    (open_te_rec ky y (open_te_rec kx x e)).
Proof.
  induction e; intros kx ky x y; intros; simpl; auto.
    rewrite IHe; auto.
    rewrite open_tt_open_tt_rec__commut; auto.

    rewrite IHe1; auto.
    rewrite IHe2; auto.

    rewrite IHe; auto.

    rewrite IHe; auto.
    rewrite open_tt_open_tt_rec__commut; auto.

    rewrite IHe1; auto.
    rewrite IHe2; auto.

    rewrite IHe; auto.

    rewrite IHe; auto.
Qed.

Lemma open_close_ee_rec__expr : forall e k (x y:atom),
  expr e ->
  expr (open_ee_rec k x (close_ee_rec k y e)).
Proof.
  intros e k x y He.
  generalize dependent k.
  induction He; intros; simpl; auto.
    destruct (y==x0); subst; simpl; auto.
      destruct (k==k); subst; auto.
        contradict n; auto.

    apply expr_abs with (L:=L `union` {{y}}); auto.
      intros x0 x0nL.
      assert (x0 `notin` L) as FV. auto.
      apply H1 with (k:=S k) in FV; auto.
      unfold open_ee in *.
      rewrite close_open_ee_rec_commut in FV; simpl; auto.
      rewrite open_ee_open_ee_rec__commut in FV; auto.

    apply expr_tabs with (L:=L `union` {{y}}); auto.
      intros X0 X0nL.
      assert (X0 `notin` L) as FV. auto.
      apply H0 with (k:=k) in FV; auto.
      unfold open_te in *.
      rewrite close_ee_open_te_rec_commut in FV; simpl; auto.
      rewrite open_ee_open_te_rec__commut in FV; auto.
Qed.

Lemma open_close_tt_rec__type : forall t k (X Y:atom),
  type t ->
  type (open_tt_rec k X (close_tt_rec k Y t)).
Proof.
  intros t k x y Ht.
  generalize dependent k.
  induction Ht; intros; simpl; auto.
    destruct (y == X); subst; simpl; auto.
      destruct (k == k); subst; simpl; auto.
        contradict n; auto.

    apply type_all with (L:=L `union` {{y}}); auto.
      intros X0 X0nL.
      assert (X0 `notin` L) as FV. auto.
      apply H0 with (k:=S k) in FV; auto.
      unfold open_tt in *.
      rewrite close_open_tt_rec_commut in FV; simpl; auto.
      rewrite open_tt_open_tt_rec__commut in FV; auto.
Qed.

Lemma open_close_te_rec__expr : forall e k (X Y:atom),
  expr e ->
  expr (open_te_rec k X (close_te_rec k Y e)).
Proof.
  intros e k x y He.
  generalize dependent k.
  induction He; intros; simpl; auto.
    apply expr_abs with (L:=L `union` {{y}}); auto.
      apply open_close_tt_rec__type; auto.

      intros x0 x0nL.
      assert (x0 `notin` L) as FV. auto.
      apply H1 with (k:=k) in FV; auto.
      unfold close_te in *.
      unfold open_ee in *.
      rewrite close_te_open_ee_rec_commut in FV; simpl; auto.
      rewrite open_ee_open_te_rec__commut; auto.

    apply expr_tabs with (L:=L `union` {{y}}); auto.
      intros X0 X0nL.
      assert (X0 `notin` L) as FV. auto.
      apply H0 with (k:=S k) in FV; auto.
      unfold close_te in *.
      unfold open_te in *.
      rewrite close_open_te_rec_commut in FV; simpl; auto.
      rewrite open_te_open_te_rec__commut; auto.

    apply expr_tapp; auto.
      apply open_close_tt_rec__type; auto.
Qed.

Lemma aux_shift_ec_rec__open_ec_rec : forall C e0 m b k,
  expr e0 ->
  match (le_lt_dec b k) with
  | left _    (* b <= k *) =>   shift_ec_rec m b (open_ec_rec k e0 C) = open_ec_rec (k + m) e0 (shift_ec_rec m b C)
  | right _  (* b > k *) => shift_ec_rec m b (open_ec_rec k e0 C) = open_ec_rec k e0 (shift_ec_rec m b C)
  end.
Proof.
  induction C; intros e0 m b k0 He0; simpl; subst;
    destruct (le_lt_dec b k0); try solve[
      auto |

      assert (J1 := IHC e0 m b k0); auto;
      assert (J2 := @aux_shift_ee_rec__open_ee_rec e e0 m b k0); auto;
      destruct (le_lt_dec b k0); try solve[
        rewrite J1; auto; rewrite J2; auto |
        apply le_not_gt in l; contradict l0; auto] |

      assert (J1 := @aux_shift_ee_rec__open_ee_rec e e0 m b k0); auto;
      assert (J2 := IHC e0 m b k0); auto;
      destruct (le_lt_dec b k0); try solve[
        rewrite J1; auto; rewrite J2; auto |
        apply le_not_gt in l0; contradict l; auto] |

      assert (J := IHC e0 m b k0); auto;
      destruct (le_lt_dec b k0); try solve [
        rewrite J; auto |
        apply le_not_gt in l; contradict l0; auto] |

      assert (J := IHC e0 m b k0); auto;
      destruct (le_lt_dec b k0); try solve [
        apply le_not_gt in l0; contradict l; auto |
        rewrite J; auto ] |

      assert (J := IHC e0 m (S b) (S k0));
      destruct (le_lt_dec (S b) (S k0)); try solve [
        rewrite J; auto |
        apply le_not_gt in l; apply lt_S_n in l0; contradict l0; auto] |

      assert (J := IHC e0 m (S b) (S k0));
      destruct (le_lt_dec (S b) (S k0)); try solve [
        apply le_not_gt in l0; apply lt_n_S in l; contradict l; auto |
        rewrite J; auto]
      ].
Qed.

Lemma close_open_ec_rec_commut : forall C x kx ey ky,
  kx <> ky ->
  x `notin` fv_ee ey ->
  close_ec_rec kx x (open_ec_rec ky ey C) =
  open_ec_rec ky ey (close_ec_rec kx x C).
Proof.
  induction C; intros x kx ey ky xny xney; simpl; 
  try solve [
    auto |
    rewrite IHC; auto |
    rewrite IHC; auto;
    rewrite close_open_ee_rec_commut; auto].
Qed.  

Lemma cv_ec_shift_ec_rec : forall C k b,
  cv_ec C [=] cv_ec (shift_ec_rec k b C).
Proof.
  induction C; intros kk b; simpl; auto.
Qed.

Lemma aux_shift_tc_rec__open_ec_rec : forall C e0 m b k,
  expr e0 ->
  shift_tc_rec m b (open_ec_rec k e0 C) = open_ec_rec k e0 (shift_tc_rec m b C).
Proof.
  induction C; intros e0 m b k0 He0; simpl; subst; try solve [
    auto |

    assert (J := IHC e0 m b (S k0)); auto;
    destruct (le_lt_dec b (S k0)); try solve [
      rewrite J; auto |
      apply le_not_gt in l; contradict l0; auto] |

    assert (J := IHC e0 m (S b) k0); auto;
    destruct (le_lt_dec (S b) k0); try solve [
      rewrite J; auto |
      apply le_not_gt in l; contradict l0; auto] |

    assert (J1 := IHC e0 m b k0); auto;
    assert (J2 := @aux_shift_te_rec__open_ee_rec e e0 m b k0); auto;
    destruct (le_lt_dec b k0); try solve[
      rewrite J1; auto; rewrite J2; auto |
      apply le_not_gt in l; contradict l0; auto] |

    assert (J := IHC e0 m b k0); auto;
    destruct (le_lt_dec b k0); try solve [
      rewrite J; auto |
      apply le_not_gt in l; contradict l0; auto]

    ].
Qed.

Lemma close_tc_open_ec_rec_commut : forall C X kX ey ky,
  X `notin` fv_te ey ->
  close_tc_rec kX X (open_ec_rec ky ey C) =
  open_ec_rec ky ey (close_tc_rec kX X C).
Proof.
  induction C; intros X kX ey ky Xney; simpl; 
  try solve [
    auto |
    rewrite IHC; auto |
    rewrite IHC; auto;
    rewrite close_te_open_ee_rec_commut; auto].
Qed.  

Lemma cv_ec_shift_tc_rec : forall C k b,
  cv_ec C [=] cv_ec (shift_tc_rec k b C).
Proof.
  induction C; intros kk b; simpl; auto.
Qed.

Lemma open_ec_rec_plugC : forall C1 C2 k e,
  expr e ->
  disjdom ((fv_ee e) `union` (fv_te e)) (cv_ec C1) ->
  open_ec_rec k e (plugC C1 C2) =  plugC (open_ec_rec k e C1) (open_ec_rec k e C2).
Proof.
  induction C1; intros C2 k0 e0 He0 Disj; simpl; 
    try solve [
      auto |
      rewrite IHC1; auto
    ].

   simpl in Disj.
   rewrite IHC1; auto.
     assert (J1 := @aux_shift_ec_rec__open_ec_rec C2 e0 1 0 k0 He0); auto.
     destruct (le_lt_dec 0 k0).
       unfold shift_ec.
       assert (k0+1 = S k0) as EQ. omega. 
       rewrite <- EQ. rewrite J1. auto.

       contradict l. omega.       

   simpl in Disj.
   rewrite IHC1; auto.
     assert (J1 := @aux_shift_ec_rec__open_ec_rec C2 e0 1 0 k0 He0); auto.
     destruct (le_lt_dec 0 k0).
       unfold shift_ec.
       assert (k0+1 = S k0) as EQ. omega. 
       rewrite <- EQ. rewrite J1.
       unfold close_ec.
       rewrite <- close_open_ec_rec_commut; auto.
         omega.
       
         apply disjdom_app_1 in Disj. 
         destruct Disj as [Disj1 Disj2].
           apply Disj2. auto. 

       contradict l. omega.       

     apply disjdom_sub with (D1:= union {{a}} (cv_ec C1)); auto.
       fsetdec.

   simpl in Disj.
   rewrite IHC1; auto.
     assert (J1 := @aux_shift_tc_rec__open_ec_rec C2 e0 1 0 k0 He0); auto.
     unfold shift_tc.
     rewrite J1. auto.

   simpl in Disj.
   rewrite IHC1; auto.
     assert (J1 := @aux_shift_tc_rec__open_ec_rec C2 e0 1 0 k0 He0); auto.
     unfold shift_tc.
     rewrite J1.
     unfold close_tc.
     rewrite <- close_tc_open_ec_rec_commut; auto.
         apply disjdom_app_2 in Disj. 
         destruct Disj as [Disj1 Disj2].
           apply Disj2. auto. 

     apply disjdom_sub with (D1:= union {{a}} (cv_ec C1)); auto.
       fsetdec.
Qed.

Lemma open_ec_plugC : forall C1 C2 e,
  expr e ->
  disjdom ((fv_ee e) `union` (fv_te e)) (cv_ec C1) ->
  open_ec (plugC C1 C2) e  =  plugC (open_ec C1 e) (open_ec C2 e).
Proof.
  unfold open_ec.
  intros C1 C2 e He.
  apply open_ec_rec_plugC; auto.
Qed.

Lemma shift_ec_rec__open_ec_rec : forall C (x:atom) m b k,
  match (le_lt_dec b k) with
  | left _    (* b <= k *) =>   shift_ec_rec m b (open_ec_rec k x C) = open_ec_rec (k + m) x (shift_ec_rec m b C)
  | right _  (* b > k *) => shift_ec_rec m b (open_ec_rec k x C) = open_ec_rec k x (shift_ec_rec m b C)
  end.
Proof.
  induction C; intros x m b k0; simpl; subst;
    destruct (le_lt_dec b k0); try solve[
      auto |
      assert (J1 := IHC x m b k0);
      assert (J2 := @shift_ee_rec__open_ee_rec e x m b k0);
      destruct (le_lt_dec b k0); try solve[
        rewrite J1; rewrite J2; auto |
        apply le_not_gt in l; contradict l0; auto] |
      assert (J1 := IHC x m b k0);
      assert (J2 := @shift_ee_rec__open_ee_rec e x m b k0);
      destruct (le_lt_dec b k0); try solve[
        rewrite J1; rewrite J2; auto |
        apply le_not_gt in l0; contradict l; auto] |
      assert (J := IHC x m b k0);
      assert (J' := @shift_ee_rec__open_ee_rec t x m b k0); 
      destruct (le_lt_dec b k0); try solve [
        rewrite J; try solve [rewrite J'; auto] |
        contradict l; try solve [omega] ] |
      assert (J := IHC x m b k0);
      destruct (le_lt_dec b k0); try solve [
        apply le_not_gt in l; contradict l0; auto |
        rewrite J; auto ] |
      assert (J := IHC x m b k0);
      destruct (le_lt_dec b k0); try solve [
        rewrite J; auto |
        contradict l0; omega] |
      assert (J := IHC x m b (S k0));
      destruct (le_lt_dec b (S k0)); try solve [
        contradict l; omega |
        rewrite J; auto] |
      assert (J := IHC x m (S b) (S k0));
      destruct (le_lt_dec (S b) (S k0)); try solve [
        rewrite J; auto |
        apply le_not_gt in l; apply lt_S_n in l0; contradict l0; auto] |
      assert (J := IHC x m (S b) (S k0));
      destruct (le_lt_dec (S b) (S k0)); try solve [
        contradict l; omega |
        rewrite J; auto]
    ].
Qed.

Lemma open_ec_rec_inv : forall C C' i (x:atom),
  x `notin` ((fv_ec C) `union` (fv_ec C')) ->
  open_ec_rec i x C = open_ec_rec i x C' ->
  C = C'.
Proof.
  intros C C' n x Hfv Heq.
  generalize dependent x.
  generalize dependent n.
  generalize dependent C'.
  induction C; intros; destruct C'; simpl in *; 
    try solve [
       inversion Heq |
       destruct (n0===n); inversion Heq |
       destruct (n===n0); inversion Heq |
       inversion Heq; subst;
         rewrite IHC with (C':=C') (n:=n) (x:=x); auto;
         apply open_ee_rec_inv in H1; subst; auto |
       inversion Heq; subst;
         rewrite IHC with (C':=C') (n:=n) (x:=x); auto;
         apply open_ee_rec_inv in H0; subst; auto |
       inversion Heq; subst;
         rewrite IHC with (C':=C') (n:=n) (x:=x); auto|
       inversion Heq; subst;
         rewrite IHC with (C':=C') (n:=S n) (x:=x); auto|
       auto
       ].
Qed.

Lemma open_ec_shift_ec__notin_fv : forall C x n b,
  x `notin` (fv_ec C) ->
  x `notin` (fv_ec (shift_ec_rec n b C)).
Proof.
  induction C; intros x i b H; simpl in *; auto.
    destruct_notin.
    apply open_shift_ee__notin_fv with (n:=i) (b:=b) in NotInTac; auto.

    destruct_notin.
    apply open_shift_ee__notin_fv with (n:=i) (b:=b) in H; auto.

    destruct_notin.
    apply open_shift_ee__notin_fv with (n:=i) (b:=b) in NotInTac; auto.

    destruct_notin.
    apply open_shift_ee__notin_fv with (n:=i) (b:=b) in H; auto.
Qed.

Lemma shift_ec_rec__open_tc_rec : forall C (X:atom) m b k,
  shift_ec_rec m b (open_tc_rec k X C) = open_tc_rec k X (shift_ec_rec m b C).
Proof.
  induction C; intros X m b k0; simpl; subst; try solve[
      auto |
      rewrite IHC; auto
      ].

      rewrite IHC.
      rewrite shift_ee_rec__open_te_rec; auto.

      rewrite IHC.
      rewrite shift_ee_rec__open_te_rec; auto.

      rewrite IHC.
      rewrite shift_ee_rec__open_te_rec; auto.

      rewrite IHC.
      rewrite shift_ee_rec__open_te_rec; auto.
Qed.

Lemma open_tc_rec_inv : forall C C' i (X:atom),
  X `notin` ((fv_tc C) `union` (fv_tc C')) ->
  open_tc_rec i X C = open_tc_rec i X C' ->
  C = C'.
Proof.
  intros C C' n x Hfv Heq.
  generalize dependent x.
  generalize dependent n.
  generalize dependent C'.
  induction C; intros; destruct C'; simpl in *; 
    try solve [
       inversion Heq |
       destruct (n0===n); inversion Heq |
       destruct (n===n0); inversion Heq |
       inversion Heq; subst;
         rewrite IHC with (C':=C') (n:=n) (x:=x); auto;
         apply open_te_rec_inv in H1; subst; auto |
       inversion Heq; subst;
         rewrite IHC with (C':=C') (n:=n) (x:=x); auto;
         apply open_te_rec_inv in H0; subst; auto |
       inversion Heq; subst;
         rewrite IHC with (C':=C') (n:=n) (x:=x); auto|
       auto
       ].

    inversion Heq; subst.
      rewrite IHC with (C':=C') (n:=n) (x:=x); auto.
      apply open_tt_rec_inv in H1; auto. 
      subst; auto.

    inversion Heq; subst.
      rewrite IHC with (C':=C') (n:=n) (x:=x); auto.
      apply open_tt_rec_inv in H2; auto. 
      subst; auto.

    inversion Heq; subst.
      rewrite IHC with (C':=C') (n:=S n) (x:=x); auto.

    inversion Heq; subst.
      rewrite IHC with (C':=C') (n:=S n) (x:=x); auto.

    inversion Heq; subst.
      rewrite IHC with (C':=C') (n:=n) (x:=x); auto.
      apply open_tt_rec_inv in H1; auto. 
      subst; auto.
Qed.

Lemma open_tc_shift_ec__notin_fv : forall C x n b,
  x `notin` (fv_tc C) ->
  x `notin` (fv_tc (shift_ec_rec n b C)).
Proof.
  induction C; intros x i b H; simpl in *; auto.
    destruct_notin.
    apply open_te_shift_ee__notin_fv with (n:=i) (b:=b) in NotInTac; auto.

    destruct_notin.
    apply open_te_shift_ee__notin_fv with (n:=i) (b:=b) in H; auto.

    destruct_notin.
    apply open_te_shift_ee__notin_fv with (n:=i) (b:=b) in NotInTac; auto.

    destruct_notin.
    apply open_te_shift_ee__notin_fv with (n:=i) (b:=b) in H; auto.
Qed.

Lemma shift_ec_rec_context : forall C k b,
  context C ->
  C = shift_ec_rec k b C.
Proof.
  intros C k b H.
  generalize dependent k.
  generalize dependent b.
  induction H; intros; simpl; try solve [
    auto |
    rewrite <- IHcontext; auto;
    rewrite <- shift_ee_rec_expr; auto
    ].

    pick fresh x.
    assert (x `notin` L) as Heq. auto.
    apply H1 with (b:=S b) (k:=k) in Heq.
    unfold open_ec in Heq.
    assert (J := @shift_ec_rec__open_ec_rec C1 x k (S b) 0).
    destruct (le_lt_dec (S b) 0).
       contradict l; omega.
       rewrite J in Heq.
       apply open_ec_rec_inv in Heq; auto.
         rewrite <- Heq. auto.

         destruct_notin. 
         assert (G:=NotInTac1).
         apply open_ec_shift_ec__notin_fv with (n:=k) (b:=S b) in G; auto.

    pick fresh x.
    assert (x `notin` L) as Heq. auto.
    apply H1 with (b:=S b) (k:=k) in Heq.
    unfold open_ec in Heq.
    assert (J := @shift_ec_rec__open_ec_rec C1 x k (S b) 0).
    destruct (le_lt_dec (S b) 0).
       contradict l; omega.
       rewrite J in Heq.
       apply open_ec_rec_inv in Heq; auto.
         rewrite <- Heq. auto.

         destruct_notin. 
         assert (G:=NotInTac3).
         apply open_ec_shift_ec__notin_fv with (n:=k) (b:=S b) in G; auto.

    pick fresh X.
    assert (X `notin` L) as Heq. auto.
    apply H0 with (b:=b) (k:=k) in Heq.
    unfold open_tc in Heq.
    assert (J := @shift_ec_rec__open_tc_rec C1 X k b 0).
    rewrite J in Heq.
    apply open_tc_rec_inv in Heq; auto.
       rewrite <- Heq; auto.

       destruct_notin.
       assert (G:=NotInTac1). 
       apply open_tc_shift_ec__notin_fv with (n:=k) (b:=b) in G; auto.       

    pick fresh X.
    assert (X `notin` L) as Heq. auto.
    apply H0 with (b:=b) (k:=k) in Heq.
    unfold open_tc in Heq.
    assert (J := @shift_ec_rec__open_tc_rec C1 X k b 0).
    rewrite J in Heq.
    apply open_tc_rec_inv in Heq; auto.
       rewrite <- Heq; auto.

       destruct_notin.
       assert (G:=NotInTac3). 
       apply open_tc_shift_ec__notin_fv with (n:=k) (b:=b) in G; auto.       
Qed.

Lemma close_ee_rec_fv_ee_notin : forall e x kk, 
  x `notin` fv_ee (close_ee_rec kk x e).
Proof.
  induction e; intros x kk; simpl; try solve [eauto | fsetdec].
     destruct (x==a); subst; simpl; fsetdec.
Qed.

Lemma close_ee_fv_ee_notin : forall e x,
  x  `notin` fv_ee (close_ee e x).
Proof.
  intros. apply close_ee_rec_fv_ee_notin.
Qed.

Lemma close_ec_rec_fv_ec_notin : forall C x kk, 
  x `notin` fv_ec (close_ec_rec kk x C).
Proof.
  induction C; intros x kk; simpl; try solve [auto using close_ee_rec_fv_ee_notin].
Qed.

Lemma close_ec_fv_ec_notin : forall C x,
  x  `notin` fv_ec (close_ec C x).
Proof.
  intros. apply close_ec_rec_fv_ec_notin.
Qed.

Lemma open_tc_rec_fv_ec_eq : forall C1 T2 kk,
  fv_ec (open_tc_rec kk T2 C1) [=] fv_ec C1.
Proof.
  induction C1; intros T2 kk; simpl; try solve [eauto | fsetdec].
    assert (J:=@open_te_rec_fv_ee_eq e T2 kk).
    assert (J':=@IHC1 T2 kk).
    fsetdec.

    assert (J:=@open_te_rec_fv_ee_eq e T2 kk).
    assert (J':=@IHC1 T2 kk).
    fsetdec.

    assert (J:=@open_te_rec_fv_ee_eq e T2 kk).
    assert (J':=@IHC1 T2 kk).
    fsetdec.

    assert (J:=@open_te_rec_fv_ee_eq e T2 kk).
    assert (J':=@IHC1 T2 kk).
    fsetdec.
Qed.

Lemma open_tc_fv_ec_eq : forall C1 T2,
  fv_ec (open_tc C1 T2) [=] fv_ec C1.
Proof.
  intros. apply open_tc_rec_fv_ec_eq.
Qed.

Lemma fv_ee_close_te_rec : forall e kk X,
  fv_ee e [=]fv_ee (close_te_rec kk X e).
Proof.
  induction e; intros kk X; simpl; auto.
    fsetdec.
Qed.

Lemma fv_ee_close_te : forall e X,
  fv_ee e [=]fv_ee (close_te e X).
Proof.
  intros e kk X.
  unfold close_te.
  apply fv_ee_close_te_rec.
Qed.

Lemma fv_ec_close_tc_rec : forall C kk X,
  fv_ec C [=]fv_ec (close_tc_rec kk X C).
Proof.
  induction C; intros kk X; simpl; auto.
    rewrite <- IHC.
    rewrite <- fv_ee_close_te_rec.
    fsetdec.

    rewrite <- IHC.
    rewrite <- fv_ee_close_te_rec.
    fsetdec.

    rewrite <- IHC.
    rewrite <- fv_ee_close_te_rec.
    fsetdec.

    rewrite <- IHC.
    rewrite <- fv_ee_close_te_rec.
    fsetdec.
Qed.

Lemma fv_ec_close_tc : forall C X,
  fv_ec C [=] fv_ec (close_tc C X).
Proof.
  intros C X.
  unfold close_tc.
  apply fv_ec_close_tc_rec.
Qed.

Lemma close_ee_rec_fv_ee_lower : forall e x kk, 
  fv_ee e [<=] fv_ee (close_ee_rec kk x e) `union` {{x}}.
Proof.
  induction e; intros x kk; simpl; try solve [eauto | fsetdec].
     destruct (x==a); subst; simpl; fsetdec.

     assert (J1:=@IHe1 x kk).
     assert (J2:=@IHe2 x kk).
     fsetdec.
    
     assert (J1:=@IHe1 x kk).
     assert (J2:=@IHe2 x kk).
     fsetdec.
Qed.

Lemma close_ee_fv_ee_lower : forall e x,
  fv_ee e [<=] fv_ee (close_ee e x) `union` {{x}}.
Proof.
  intros. apply close_ee_rec_fv_ee_lower.
Qed.

Lemma close_ec_rec_fv_ec_lower : forall C x kk, 
  fv_ec C [<=] fv_ec (close_ec_rec kk x C) `union` {{x}}.
Proof.
  induction C; intros x kk; simpl; try solve [eauto | fsetdec].
    assert (J:=@close_ee_rec_fv_ee_lower e x kk).
    assert (J':=@IHC x kk).
    fsetdec.

    assert (J:=@close_ee_rec_fv_ee_lower e x kk).
    assert (J':=@IHC x kk).
    fsetdec.

    assert (J:=@close_ee_rec_fv_ee_lower e x kk).
    assert (J':=@IHC x kk).
    fsetdec.

    assert (J:=@close_ee_rec_fv_ee_lower e x kk).
    assert (J':=@IHC x kk).
    fsetdec.
Qed.

Lemma close_ec_fv_ec_lower : forall C x,
  fv_ec C [<=] fv_ec (close_ec C x) `union` {{x}}.
Proof.
  intros. apply close_ec_rec_fv_ec_lower.
Qed.


Lemma close_ee_rec_fv_ee_eq : forall e1 x kk,
  fv_ee (close_ee_rec kk x e1) [=] AtomSetImpl.diff (fv_ee e1) {{x}}.
Proof.
  induction e1; intros x kk; simpl; try solve [eauto | fsetdec].
     destruct (x==a); subst; simpl; fsetdec.

     assert (J1:=@IHe1_1 x kk).
     assert (J2:=@IHe1_2 x kk).
     fsetdec.
    
     assert (J1:=@IHe1_1 x kk).
     assert (J2:=@IHe1_2 x kk).
     fsetdec.
Qed.

Lemma close_ee_fv_ee_eq : forall e1 x,
  fv_ee (close_ee e1 x) [=] AtomSetImpl.diff (fv_ee e1) {{x}}.
Proof.
  intros. apply close_ee_rec_fv_ee_eq.
Qed.

Lemma aux_shift_ee_rec__close_ee_rec : forall e x m b k,
  match (le_lt_dec b k) with
  | left _    (* b <= k *) =>   shift_ee_rec m b (close_ee_rec k x e) = close_ee_rec (k + m) x (shift_ee_rec m b e)
  | right _  (* b > k *) => shift_ee_rec m b (close_ee_rec k x e) = close_ee_rec k x (shift_ee_rec m b e)
  end.
Proof.
  induction e; intros x m b k0; simpl; subst; try solve [
    auto |

    assert (J := IHe x m b k0); auto;
    destruct (le_lt_dec b k0); try solve [
            rewrite J; auto; try solve [rewrite J'; auto]] |

    assert (J := IHe x m b k0); auto;
    destruct (le_lt_dec b k0); try solve [
      rewrite J; auto |
      apply le_not_gt in l; contradict l0; auto] |

    assert (J1 := IHe1 x m b k0); auto;
    assert (J2 := IHe2 x m b k0); auto;
    destruct (le_lt_dec b k0); try solve[
      rewrite J1; auto; rewrite J2; auto |
      apply le_not_gt in l; contradict l0; auto]
    ].

    destruct (le_lt_dec b k0); subst; simpl; auto.
      destruct (le_lt_dec b n); subst; simpl; auto.
      destruct (le_lt_dec b n); subst; simpl; auto.

    destruct (le_lt_dec b k0); subst; simpl; auto.
      destruct (x == a); subst; simpl; auto.
        destruct (le_lt_dec b k0); subst; simpl; auto.
          assert (k0 < k0) as H. omega.
          contradict H. omega.
      destruct (x == a); subst; simpl; auto.
        destruct (le_lt_dec b k0); subst; simpl; auto.
          assert (b < b) as H. omega.
          contradict H. omega.

    assert (J := IHe x m (S b) (S k0)); auto.
    destruct (le_lt_dec b k0).
      destruct (le_lt_dec (S b) (S k0)).
         rewrite J; auto.
         contradict l. omega. 
      destruct (le_lt_dec (S b) (S k0)).
         contradict l. omega. 
         rewrite J; auto.
Qed. 

Lemma close_ee_rec_commute : forall (x  y: atom) e k1 k2,
  x <> y ->
  (close_ee_rec k1 x (close_ee_rec k2 y e) =
    close_ee_rec k2 y (close_ee_rec k1 x e)).
Proof with auto.
  intros x y e k1 k2 Neq.
  generalize dependent k1.
  generalize dependent k2.
  (exp_cases (induction e) Case); intros k2 k1; simpl in *;
    try solve [ auto |
                rewrite IHe; auto |
                rewrite IHe1; auto; rewrite IHe2; auto |
                rewrite IHe1; auto; rewrite IHe2; auto ; rewrite IHe3; auto ].
  destruct (y == a); subst; simpl; auto.
    destruct (x == a); subst; simpl; auto.
       contradict Neq; auto.
       destruct (a == a); subst; simpl; auto.
         contradict n0; auto.
    destruct (x == a); subst; simpl; auto.
       destruct (y == a); subst; simpl; auto.
         contradict n; auto.
Qed.

Lemma shift_te_rec__close_ee_rec : forall e x m b k,
  shift_te_rec m b (close_ee_rec k x e) = close_ee_rec k x (shift_te_rec m b e).
Proof.
  induction e; intros x m b k0; simpl; subst; try solve[
      auto |
      rewrite IHe1; rewrite IHe2; auto |
      rewrite IHe; auto
      ].

     destruct (x==a); subst; simpl; auto.
Qed.

Lemma close_ee_close_te_rec_commut : forall e x kx y ky,
  close_ee_rec kx x (close_te_rec ky y e) =
  close_te_rec ky y (close_ee_rec kx x e).
Proof.
  induction e; intros x kx y ky; simpl; auto.
    destruct (x==a); subst; simpl; auto.
       
    rewrite IHe; auto.

    rewrite IHe1; auto.
    rewrite IHe2; auto.

    rewrite IHe; auto.

    rewrite IHe; auto.

    rewrite IHe1; auto.
    rewrite IHe2; auto.

    rewrite IHe; auto.

    rewrite IHe; auto.
Qed.  

Lemma close_ee_rec_plug : forall C k x e,
  x `notin`  (cv_ec C) ->
  close_ee_rec k x (plug C e) =  plug (close_ec_rec k x C) (close_ee_rec k x e).
Proof.
  induction C; intros kk x ee Hx; simpl;
    try solve [
      auto |
      rewrite IHC; auto
    ].

   simpl in Hx.
   rewrite IHC; auto.
     assert (J1 := @aux_shift_ee_rec__close_ee_rec ee x 1 0 kk); auto.
     destruct (le_lt_dec 0 (S kk)).
       unfold shift_ee.
       rewrite J1.
       assert (kk + 1 = S kk) as EQ. omega.
       rewrite EQ. auto.

       contradict l. omega.

   simpl in Hx.
   rewrite IHC; auto.
     assert (J1 := @aux_shift_ee_rec__close_ee_rec ee x 1 0 kk); auto.
     destruct (le_lt_dec 0 (S kk)).
       unfold shift_ee.
       unfold close_ee.
       rewrite J1.
       assert (kk + 1 = S kk) as EQ. omega.
       rewrite EQ.
       rewrite close_ee_rec_commute; auto.

       contradict l. omega.

   simpl in Hx.
   rewrite IHC; auto.
     assert (J1 := @shift_te_rec__close_ee_rec ee x 1 0 kk).
     unfold shift_te.
     rewrite J1. auto.

   simpl in Hx.
   rewrite IHC; auto.
     assert (J1 := @shift_te_rec__close_ee_rec ee x 1 0 kk).
     unfold shift_te.
     rewrite J1.
     unfold close_te.
     rewrite close_ee_close_te_rec_commut; auto.
Qed.

Lemma aux_shift_ec_rec__close_ec_rec : forall C x m b k,
  match (le_lt_dec b k) with
  | left _    (* b <= k *) =>   shift_ec_rec m b (close_ec_rec k x C) = close_ec_rec (k + m) x (shift_ec_rec m b C)
  | right _  (* b > k *) => shift_ec_rec m b (close_ec_rec k x C) = close_ec_rec k x (shift_ec_rec m b C)
  end.
Proof.
  induction C; intros x m b k0; simpl; subst; try solve [
    auto |

    assert (J := IHC x m b k0); auto;
    destruct (le_lt_dec b k0); try solve [
            rewrite J; auto; try solve [rewrite J'; auto]] |

    assert (J := IHC x m b k0); auto;
    destruct (le_lt_dec b k0); try solve [
      rewrite J; auto |
      apply le_not_gt in l; contradict l0; auto] |

    assert (J1 := IHC x m b k0); auto;
    assert (J2 := @aux_shift_ee_rec__close_ee_rec e x m b k0); auto;
    destruct (le_lt_dec b k0); try solve[
      rewrite J1; auto; rewrite J2; auto |
      apply le_not_gt in l; contradict l0; auto]
    ].

    destruct (le_lt_dec b k0); subst; simpl; auto.

    assert (J := IHC x m (S b) (S k0)); auto.
    destruct (le_lt_dec b k0).
      destruct (le_lt_dec (S b) (S k0)).
         rewrite J; auto.
         contradict l. omega. 
      destruct (le_lt_dec (S b) (S k0)).
         contradict l. omega. 
         rewrite J; auto.

    assert (J := IHC x m (S b) (S k0)); auto.
    destruct (le_lt_dec b k0).
      destruct (le_lt_dec (S b) (S k0)).
         rewrite J; auto.
         contradict l. omega. 
      destruct (le_lt_dec (S b) (S k0)).
         contradict l. omega. 
         rewrite J; auto.
Qed. 

Lemma close_ec_rec_commute : forall (x  y: atom) C k1 k2,
  x <> y ->
  (close_ec_rec k1 x (close_ec_rec k2 y C) =
    close_ec_rec k2 y (close_ec_rec k1 x C)).
Proof with auto.
  intros x y C k1 k2 Neq.
  generalize dependent k1.
  generalize dependent k2.
  induction C; intros k2 k1; simpl in *;
    try solve [ auto |
                rewrite IHC; auto |
                rewrite IHC; auto; rewrite close_ee_rec_commute; auto ].
Qed.

Lemma shift_tc_rec__close_ec_rec : forall C x m b k,
  shift_tc_rec m b (close_ec_rec k x C) = close_ec_rec k x (shift_tc_rec m b C).
Proof.
  induction C; intros x m b k0; simpl; subst; try solve[
      auto |
      rewrite IHC; rewrite shift_te_rec__close_ee_rec; auto |
      rewrite IHC; auto
      ].
Qed.

Lemma close_ec_close_tc_rec_commut : forall C x kx y ky,
  close_ec_rec kx x (close_tc_rec ky y C) =
  close_tc_rec ky y (close_ec_rec kx x C).
Proof.
  induction C; intros x kx y ky; simpl; 
  try solve [
    auto |
    rewrite IHC; auto |
    rewrite IHC; auto;
    rewrite close_ee_close_te_rec_commut; auto].
Qed.  

Lemma close_ec_rec_plugC : forall C k x C',
  x `notin`  (cv_ec C) ->
  close_ec_rec k x (plugC C C') =  plugC (close_ec_rec k x C) (close_ec_rec k x C').
Proof.
  induction C; intros kk x C' Hx; simpl;
    try solve [
      auto |
      rewrite IHC; auto
    ].

   simpl in Hx.
   rewrite IHC; auto.
     assert (J1 := @aux_shift_ec_rec__close_ec_rec C' x 1 0 kk); auto.
     destruct (le_lt_dec 0 (S kk)).
       unfold shift_ec.
       rewrite J1.
       assert (kk + 1 = S kk) as EQ. omega.
       rewrite EQ. auto.

       contradict l. omega.

   simpl in Hx.
   rewrite IHC; auto.
     assert (J1 := @aux_shift_ec_rec__close_ec_rec C' x 1 0 kk); auto.
     destruct (le_lt_dec 0 (S kk)).
       unfold shift_ec.
       unfold close_ec.
       rewrite J1.
       assert (kk + 1 = S kk) as EQ. omega.
       rewrite EQ.
       rewrite close_ec_rec_commute; auto.

       contradict l. omega.

   simpl in Hx.
   rewrite IHC; auto.
     assert (J1 := @shift_tc_rec__close_ec_rec C' x 1 0 kk).
     unfold shift_tc.
     rewrite J1. auto.

   simpl in Hx.
   rewrite IHC; auto.
     assert (J1 := @shift_tc_rec__close_ec_rec C' x 1 0 kk).
     unfold shift_tc.
     rewrite J1.
     unfold close_tc.
     rewrite close_ec_close_tc_rec_commut; auto.
Qed.

Lemma cv_ec_plugC : forall C1 C2,
  cv_ec (plugC C1 C2) [=] cv_ec C1 `union` cv_ec C2.
Proof.
  induction C1; intros; simpl; auto.
    fsetdec.

    rewrite IHC1. 
    unfold shift_ec. rewrite <- cv_ec_shift_ec_rec. fsetdec.

    rewrite IHC1. 
    unfold close_ec. rewrite cv_ec_close_ec_rec. 
    unfold shift_ec. rewrite <- cv_ec_shift_ec_rec. fsetdec.

    rewrite IHC1. 
    unfold shift_tc. rewrite <- cv_ec_shift_tc_rec. fsetdec.

    rewrite IHC1. 
    unfold close_tc. rewrite cv_ec_close_tc_rec. 
    unfold shift_tc. rewrite <- cv_ec_shift_tc_rec. fsetdec.
Qed.

Lemma shift_tc_rec__open_ec_rec : forall C (x:atom) m b k,
  shift_tc_rec m b (open_ec_rec k x C) = open_ec_rec k x (shift_tc_rec m b C).
Proof.
  induction C; intros x m b k0; simpl; subst; try solve[
      auto |
      rewrite IHC; rewrite shift_te_rec__open_ee_rec; auto |
      rewrite IHC; auto
      ].
Qed.

Lemma open_ec_shift_tc__notin_fv : forall C X n b,
  X `notin` (fv_ec C) ->
  X `notin` (fv_ec (shift_tc_rec n b C)).
Proof.
  induction C; intros X i b H; simpl in *; auto.
    destruct_notin.
    apply IHC with (n:=i) (b:=b) in H.
    apply open_ee_shift_te__notin_fv with (n:=i) (b:=b) in NotInTac. auto.

    destruct_notin.
    apply IHC with (n:=i) (b:=b) in NotInTac.
    apply open_ee_shift_te__notin_fv with (n:=i) (b:=b) in H. auto.

    destruct_notin.
    apply IHC with (n:=i) (b:=b) in H.
    apply open_ee_shift_te__notin_fv with (n:=i) (b:=b) in NotInTac. auto.

    destruct_notin.
    apply IHC with (n:=i) (b:=b) in NotInTac.
    apply open_ee_shift_te__notin_fv with (n:=i) (b:=b) in H. auto.
Qed.

Lemma shift_tc_rec__open_tc_rec : forall C (X:atom) m b k,
  match (le_lt_dec b k) with
  | left _    (* b <= k *) =>   shift_tc_rec m b (open_tc_rec k X C) = open_tc_rec (k + m) X (shift_tc_rec m b C)
  | right _  (* b > k *) => shift_tc_rec m b (open_tc_rec k X C) = open_tc_rec k X (shift_tc_rec m b C)
  end.
Proof.
  induction C; intros X m b k0; simpl; subst;
    destruct (le_lt_dec b k0); try solve[
      auto |
      assert (J1 := IHC  X m b k0);
      assert (J2 := shift_te_rec__open_te_rec e X m b k0);
      destruct (le_lt_dec b k0); try solve[
        rewrite J1; rewrite J2; auto |
        apply le_not_gt in l; contradict l0; auto] |
      assert (J1 := IHC  X m b k0);
      assert (J2 := shift_te_rec__open_te_rec e X m b k0);
      destruct (le_lt_dec b k0); try solve[
        rewrite J1; rewrite J2; auto |
        apply le_not_gt in l0; contradict l; auto] |
      assert (J := IHC X m b k0);
      assert (J' := @shift_tt_rec__open_tt_rec t X m b k0); 
      destruct (le_lt_dec b k0); try solve [
        rewrite J; try solve [rewrite J'; auto] |
        contradict l; try solve [omega] ] |
      assert (J := IHC X m b k0);
      destruct (le_lt_dec b k0); try solve [
        apply le_not_gt in l; contradict l0; auto |
        rewrite J; auto ] |
      assert (J := IHC X m b k0);
      destruct (le_lt_dec b k0); try solve [
        rewrite J; auto |
        contradict l0; omega] |
      assert (J := IHC X m (S b) (S k0));
      destruct (le_lt_dec (S b) (S k0)); try solve [
        rewrite J; auto |
        apply le_not_gt in l; apply lt_S_n in l0; contradict l0; auto] |
      assert (J := IHC X m (S b) (S k0));
      destruct (le_lt_dec (S b) (S k0)); try solve [
        apply le_not_gt in l0; apply lt_n_S in l; contradict l; auto |
        rewrite J; auto]
    ].
Qed.

Lemma open_shift_tc__notin_fv : forall C X n b,
  X `notin` (fv_tc C) ->
  X `notin` (fv_tc (shift_tc_rec n b C)).
Proof.
  induction C; intros X i b H; simpl in *; auto.
    destruct_notin.
    apply IHC with (n:=i) (b:=b) in NotInTac.
    apply open_tt_shift_tt__notin_fv with (n:=i) (b:=b) in H. auto.

    destruct_notin.
    apply IHC with (n:=i) (b:=b) in NotInTac.
    apply open_tt_shift_tt__notin_fv with (n:=i) (b:=b) in H. auto.

    destruct_notin.
    apply IHC with (n:=i) (b:=b) in H.
    apply open_shift_te__notin_fv with (n:=i) (b:=b) in NotInTac. auto.

    destruct_notin.
    apply IHC with (n:=i) (b:=b) in NotInTac.
    apply open_shift_te__notin_fv with (n:=i) (b:=b) in H. auto.

    destruct_notin.
    apply IHC with (n:=i) (b:=b) in H.
    apply open_tt_shift_tt__notin_fv with (n:=i) (b:=b) in NotInTac. auto.

    destruct_notin.
    apply IHC with (n:=i) (b:=b) in H.
    apply open_shift_te__notin_fv with (n:=i) (b:=b) in NotInTac. auto.

    destruct_notin.
    apply IHC with (n:=i) (b:=b) in NotInTac.
    apply open_shift_te__notin_fv with (n:=i) (b:=b) in H. auto.
Qed.

Lemma shift_tc_rec_context : forall C k b,
  context C ->
  C = shift_tc_rec k b C.
Proof.
  intros C k b H.
  generalize dependent k.
  generalize dependent b.
  induction H; intros; simpl; try solve [
    auto |
    rewrite <- H1; auto;
    rewrite <- shift_tt_rec_type; auto |
    rewrite <- IHcontext; auto;
    rewrite <- shift_te_rec_expr; auto
    ].

    pick fresh x.
    assert (x `notin` L) as Heq. auto.
    apply H1 with (b:=b) (k:=k) in Heq.
    unfold open_ec in Heq.
    assert (J := @shift_tc_rec__open_ec_rec C1 x k b 0).
    rewrite J in Heq.
    apply open_ec_rec_inv in Heq; auto.
       rewrite <- shift_tt_rec_typ; auto.
       rewrite <- Heq; auto.

       destruct_notin.
       assert (G:=NotInTac1). 
       apply open_ec_shift_tc__notin_fv with (n:=k) (b:=b) in G; auto.       

    pick fresh x.
    assert (x `notin` L) as Heq. auto.
    apply H1 with (b:=b) (k:=k) in Heq.
    unfold open_ec in Heq.
    assert (J := @shift_tc_rec__open_ec_rec C1 x k b 0).
    rewrite J in Heq.
    apply open_ec_rec_inv in Heq; auto.
       rewrite <- shift_tt_rec_typ; auto.
       rewrite <- Heq; auto.

       destruct_notin.
       assert (G:=NotInTac3). 
       apply open_ec_shift_tc__notin_fv with (n:=k) (b:=b) in G; auto.       

    pick fresh X.
    assert (X `notin` L) as Heq. auto.
    apply H0 with (b:=S b) (k:=k) in Heq.
    unfold open_tc in Heq.
    assert (J := @shift_tc_rec__open_tc_rec C1 X k (S b) 0).
    destruct (le_lt_dec (S b) 0).
       contradict l; omega.
       rewrite J in Heq.
       apply open_tc_rec_inv in Heq; auto.
           rewrite <- Heq. auto.
           destruct_notin. 
           assert (G:=NotInTac1).
           apply open_shift_tc__notin_fv with (n:=k) (b:=S b) in G; auto.

    pick fresh X.
    assert (X `notin` L) as Heq. auto.
    apply H0 with (b:=S b) (k:=k) in Heq.
    unfold open_tc in Heq.
    assert (J := @shift_tc_rec__open_tc_rec C1 X k (S b) 0).
    destruct (le_lt_dec (S b) 0).
       contradict l; omega.
       rewrite J in Heq.
       apply open_tc_rec_inv in Heq; auto.
           rewrite <- Heq. auto.
           destruct_notin. 
           assert (G:=NotInTac3).
           apply open_shift_tc__notin_fv with (n:=k) (b:=S b) in G; auto.

    rewrite <- IHcontext.
    rewrite <- shift_tt_rec_typ; auto.
Qed.

Lemma close_tc_rec_context : forall X C k,
  X `notin` (fv_tc C) ->
  C = close_tc_rec k X C.
Proof with auto*.
  intros X C k0 Hfv. revert k0.
  induction C; intro k0; simpl in *; f_equal; auto*.
    auto using close_tt_rec_typ.
    auto using close_tt_rec_typ.
    auto using close_te_rec_expr.
    auto using close_te_rec_expr.
    auto using close_tt_rec_typ.
    auto using close_te_rec_expr.
    auto using close_te_rec_expr.
Qed.

Lemma shift_ec_rec__open_tc_rec' : forall C T m b k,
  shift_ec_rec m b (open_tc_rec k T C) = open_tc_rec k T (shift_ec_rec m b C).
Proof.
  induction C; intros T m b k0; simpl; subst; try solve[
      auto |
      rewrite IHC; rewrite shift_ee_rec__open_te_rec; auto |
      rewrite IHC; auto
      ].
Qed.

Lemma close_ec_open_tc_rec_commut : forall C x kx ty ky,
  x `notin` fv_tt ty ->
  close_ec_rec kx x (open_tc_rec ky ty C) =
  open_tc_rec ky ty (close_ec_rec kx x C).
Proof.
  induction C; intros x kx ey ky xnty; simpl; 
  try solve [
    auto |
    rewrite IHC; auto |
    rewrite IHC; auto;
    rewrite close_ee_open_te_rec_commut; auto].
Qed.  

Lemma aux_shift_tc_rec__open_tc_rec : forall C t0 m b k,
  type t0 ->
  match (le_lt_dec b k) with
  | left _    (* b <= k *) =>   shift_tc_rec m b (open_tc_rec k t0 C) = open_tc_rec (k + m) t0 (shift_tc_rec m b C)
  | right _  (* b > k *) => shift_tc_rec m b (open_tc_rec k t0 C) = open_tc_rec k t0 (shift_tc_rec m b C)
  end.
Proof.
  induction C; intros t0 m b k0 Ht0; simpl; subst; try solve [
    auto |

    assert (J := IHC t0 m b k0); auto;
    assert (J' := @aux_shift_tt_rec__open_tt_rec  t t0 m b k0); auto;
    destruct (le_lt_dec b k0); try solve [
            rewrite J; auto; try solve [rewrite J'; auto]] |

    assert (J := IHC t0 m b k0); auto;
    destruct (le_lt_dec b k0); try solve [
      rewrite J; auto |
      apply le_not_gt in l; contradict l0; auto] |

    assert (J1 := IHC t0 m b k0); auto;
    assert (J2 :=  aux_shift_te_rec__open_te_rec e t0 m b k0); auto;
    destruct (le_lt_dec b k0); try solve[
      rewrite J1; auto; rewrite J2; auto |
      apply le_not_gt in l; contradict l0; auto]
    ].

    destruct (le_lt_dec b k0); subst; simpl; auto.

    assert (J := IHC t0 m (S b) (S k0)); auto.
    destruct (le_lt_dec b k0).
      destruct (le_lt_dec (S b) (S k0)).
         rewrite J; auto.
         contradict l. omega. 
      destruct (le_lt_dec (S b) (S k0)).
         contradict l. omega. 
         rewrite J; auto.

    assert (J := IHC t0 m (S b) (S k0)); auto.
    destruct (le_lt_dec b k0).
      destruct (le_lt_dec (S b) (S k0)).
         rewrite J; auto.
         contradict l. omega. 
      destruct (le_lt_dec (S b) (S k0)).
         contradict l. omega. 
         rewrite J; auto.
Qed.    

Lemma close_open_tc_rec_commut : forall C X kX ty ky,
  kX <> ky ->
  X `notin` fv_tt ty ->
  close_tc_rec kX X (open_tc_rec ky ty C) =
  open_tc_rec ky ty (close_tc_rec kX X C).
Proof.
  induction C; intros X kX ty ky Xny Xnty; simpl; 
  try solve [
    auto |
    rewrite IHC; auto;
    rewrite close_open_tt_rec_commut; auto |
    rewrite IHC; auto;
    rewrite close_open_te_rec_commut; auto].
Qed.  

Lemma open_tc_rec_plugC : forall C k t C',
  type t ->
  disjdom (fv_tt t) (cv_ec C) ->
  open_tc_rec k t (plugC C C') =  plugC (open_tc_rec k t C) (open_tc_rec k t C').
Proof.
  induction C; intros k0 t0 C0 Ht0 Hc; simpl; 
    try solve [
      auto |
      rewrite IHC; auto
    ].

   simpl in Hc.
   rewrite IHC; auto.
     assert (J1 := @shift_ec_rec__open_tc_rec' C0 t0 1 0 k0).
     unfold shift_ec.
     rewrite J1. auto.

   simpl in Hc.
   rewrite IHC; auto.
     assert (J1 := @shift_ec_rec__open_tc_rec' C0 t0 1 0 k0).
     unfold shift_ec.
     rewrite J1.
     unfold close_ec.
     rewrite <- close_ec_open_tc_rec_commut; auto.
       destruct Hc as [Hc1 Hc2].
         apply Hc2. auto. 

     apply disjdom_sub with (D1:=union {{a}} (cv_ec C)); auto.
        fsetdec.

   simpl in Hc.
   rewrite IHC; auto.
     assert (J1 := @aux_shift_tc_rec__open_tc_rec C0 t0 1 0 k0 Ht0); auto.
     destruct (le_lt_dec 0 (S k0)).
       unfold shift_tc.
       rewrite J1.
       assert (k0 + 1 = S k0) as EQ. omega.
       rewrite EQ. auto.

       contradict l. omega.

   simpl in Hc.
   rewrite IHC; auto.
     assert (J1 := @aux_shift_tc_rec__open_tc_rec C0 t0 1 0 k0 Ht0); auto.
     destruct (le_lt_dec 0 (S k0)).
       unfold shift_tc.
       unfold close_tc.
       rewrite J1.
       assert (k0 + 1 = S k0) as EQ. omega.
       rewrite EQ.
       rewrite <- close_open_tc_rec_commut; auto.
         destruct Hc as [Hc1 Hc2].
           apply Hc2. auto. 

       contradict l. omega.

     apply disjdom_sub with (D1:=union {{a}} (cv_ec C)); auto.
        fsetdec.
Qed.

Lemma open_tc_plugC : forall C t C',
  type t ->
  disjdom (fv_tt t) (cv_ec C) ->
  open_tc (plugC C C') t  =  plugC (open_tc C t) (open_tc C' t).
Proof.
  unfold open_tc.
  intros C t e Ht.
  apply open_tc_rec_plugC; auto.
Qed.

Lemma shift_ee_rec_commute : forall e k1 b1 k2 b2,
  match (le_lt_dec b1 b2) with
  | left _    (* b1 <= b2 *) => (shift_ee_rec k1 b1 (shift_ee_rec k2 b2 e) = shift_ee_rec k2 (b2+k1) (shift_ee_rec k1 b1 e))
  | right _  (* b1 > b2 *) => (shift_ee_rec k1 b1 (shift_ee_rec k2 b2 e) = shift_ee_rec k2 b2 (shift_ee_rec k1 (max (b1-k2) b2) e))
  end.
Proof with auto.
  (exp_cases (induction e) Case); intros k1 b1 k2 b2; simpl in *.
  Case "exp_bvar".
    destruct (le_lt_dec b1 b2); subst; simpl.
      destruct (le_lt_dec b2 n); subst; simpl.
        destruct (le_lt_dec b1 n); subst; simpl.
          destruct (le_lt_dec b1 (n+k2)); subst; simpl.
            destruct (le_lt_dec (b2+k1) (n+k1)); subst; simpl.
              assert (k2+k1=k1+k2) as EQ. omega.
              assert (n+k2+k1=n+(k2+k1)) as EQ'. omega.
              assert (n+k1+k2=n+(k1+k2)) as EQ''. omega.
              rewrite EQ'. rewrite EQ. rewrite EQ''. auto.

              contradict l0. clear - l3. omega.
            assert (b2 < b1) as H.
              clear - l0 l2. omega.
            contradict H. clear - l. omega.
          assert (b2 < b1) as H.
            clear - l0 l1. omega.
          contradict H. clear - l. omega.
        destruct (le_lt_dec b1 n); subst; simpl.
          destruct (le_lt_dec (b2+k1) (n+k1)); subst; simpl; auto.
            assert (b2 <= n) as H.
              clear - l2. omega.
            contradict l0. clear - H. omega.
          destruct (le_lt_dec (b2+k1) n); subst; simpl; auto.
            assert (b2 <= n) as H.
              clear - l2. omega.
            contradict l0. clear - H. omega.
      destruct (le_lt_dec b2 n); subst; simpl.
        destruct (le_lt_dec b1 (n+k2)); subst; simpl.
          destruct (le_lt_dec (max (b1-k2) b2) n); subst; simpl.
            destruct (le_lt_dec b2 (n+k1)); subst; simpl.
              assert (k2+k1=k1+k2) as EQ. omega.
              assert (n+k2+k1=n+(k2+k1)) as EQ'. omega.
              assert (n+k1+k2=n+(k1+k2)) as EQ''. omega.
              rewrite EQ'. rewrite EQ. rewrite EQ''. auto.

              assert (n < b2) as H.
                clear - l3. omega.
              contradict l0. clear - H. omega.
            destruct (le_lt_dec (b1 - k2) b2).
              rewrite max_r in l2; auto.
              assert (b2 < b2) as H.
                clear - l2 l0. 
                omega.
              contradict H. omega.

              rewrite max_l in l2; try solve [omega].
              assert (n+k2 < b1) as H.
                clear - l2. 
                omega.
              assert (b1 < b1) as H'.
                clear - l1 H. omega.
              contradict H'. omega.
          destruct (le_lt_dec (max (b1-k2) b2) n); subst; simpl.
            assert (b1 - k2 <= max (b1 - k2) b2) as J.
              apply le_max_l; auto.
            assert (b1 - k2 <= n) as J'.
              omega.
            assert (b1 <= n+k2) as H.
              clear - J'. omega.
            assert (b1 < b1) as H'.
              clear - l1 H. omega.
            contradict H'. omega.

            destruct (le_lt_dec b2 n); subst; simpl; auto.
              assert (b2 < b2) as H.
                clear - l0 l3. omega.
              contradict H. omega.
          destruct (le_lt_dec (max (b1-k2) b2) n); subst; simpl.
            destruct (le_lt_dec b1 n); subst; simpl.
              destruct (le_lt_dec b2 (n+k1)); subst; simpl; auto.
                assert (b1 < b2) as H.
                  clear - l0 l2. omega.
                contradict H. clear - l. omega.
              assert (b2 <= max (b1 - k2) b2) as J.
                apply le_max_r; auto.
              assert (b2 <= n) as J'. omega.
              contradict J'. omega.
            destruct (le_lt_dec b1 n); subst; simpl.
              assert (b1 < b2) as J. omega.
              contradict J. omega.

              destruct (le_lt_dec b2 n); subst; simpl; auto.
                contradict l0. omega.

  Case "exp_fvar".
    destruct (le_lt_dec b1 b2); subst; simpl; auto.

  Case "exp_abs".
    assert (J := IHe k1 (S b1) k2 (S b2)).
    destruct (le_lt_dec b1 b2); subst; simpl.
      destruct (le_lt_dec (S b1) (S b2)); subst; simpl.
        rewrite J. auto.

        assert (b2 < b1) as J'. clear - l0. omega.
        contradict J'. omega.

      destruct (le_lt_dec (S b1) (S b2)); subst; simpl.
        assert (b1 <= b2) as J'. clear - l0. omega.
        contradict J'. omega.

        rewrite J. rewrite max_SS.
        destruct (le_lt_dec (S b1) k2).
          assert (S b1 - k2 = 0) as EQ. omega.
          assert (S (b1 - k2) = 1) as EQ'. omega.
          rewrite EQ. rewrite EQ'. clear EQ EQ'.
          assert (max 0 (S b2) = S b2) as EQ.
            rewrite max_r; auto.
              omega.
          assert (max 1 (S b2) = S b2) as EQ'.
            rewrite max_r; auto.
              omega.
          rewrite EQ. rewrite EQ'. auto.

          assert (S b1 - k2 = S (b1 - k2)) as EQ. omega.
          rewrite EQ. auto. 

  Case "exp_app".
    assert (J1 := IHe1 k1 b1 k2 b2).
    assert (J2 := IHe2 k1 b1 k2 b2).
    destruct (le_lt_dec b1 b2); subst; simpl.
      rewrite J1. rewrite J2. auto.
      rewrite J1. rewrite J2. auto.

  Case "exp_tabs".
    assert (J := IHe k1 b1 k2 b2).
    destruct (le_lt_dec b1 b2); subst; simpl.
      rewrite J. auto.
      rewrite J. auto.

  Case "exp_tapp".
    assert (J := IHe k1 b1 k2 b2).
    destruct (le_lt_dec b1 b2); subst; simpl.
      rewrite J. auto.
      rewrite J. auto.

  Case "exp_apair".
    assert (J1 := IHe1 k1 b1 k2 b2).
    assert (J2 := IHe2 k1 b1 k2 b2).
    destruct (le_lt_dec b1 b2); subst; simpl.
      rewrite J1. rewrite J2. auto.
      rewrite J1. rewrite J2. auto.

  Case "exp_fst".
    assert (J := IHe k1 b1 k2 b2).
    destruct (le_lt_dec b1 b2); subst; simpl.
      rewrite J. auto.
      rewrite J. auto.

  Case "exp_snd".
    assert (J := IHe k1 b1 k2 b2).
    destruct (le_lt_dec b1 b2); subst; simpl.
      rewrite J. auto.
      rewrite J. auto.
Qed.

Lemma shift_ee_rec__close_te_rec : forall e X m b k,
  shift_ee_rec m b (close_te_rec k X e) = close_te_rec k X (shift_ee_rec m b e).
Proof.
  induction e; intros X m b k0; simpl; subst; try solve[
      auto |
      rewrite IHe1; rewrite IHe2; auto |
      rewrite IHe; auto
      ].

     destruct (le_lt_dec b n); subst; simpl; auto.
Qed.

Lemma shift_ee_shift_te_rec_commut : forall e k1 b1 k2 b2,
  shift_ee_rec k1 b1 (shift_te_rec k2 b2 e) =
  shift_te_rec k2 b2 (shift_ee_rec k1 b1 e).
Proof.
  induction e; intros k1 b1 k2 b2; simpl; auto.
    destruct (le_lt_dec b1 n); simpl; auto.
       
    rewrite IHe; auto.

    rewrite IHe1; auto.
    rewrite IHe2; auto.

    rewrite IHe; auto.

    rewrite IHe; auto.

    rewrite IHe1; auto.
    rewrite IHe2; auto.

    rewrite IHe; auto.

    rewrite IHe; auto.
Qed.  

Lemma shift_ee_rec_plug : forall C k b e,
  shift_ee_rec k b (plug C e) =  plug (shift_ec_rec k b C) (shift_ee_rec k b e).
Proof.
  induction C; intros kk b ee; simpl;
    try solve [
      auto |
      rewrite IHC; auto
    ].

   rewrite IHC; auto.
     destruct (le_lt_dec (S b) 0).
       contradict l. omega.

       unfold shift_ee. 
       assert (J2 := @shift_ee_rec_commute ee kk (S b) 1 0).
       destruct (le_lt_dec (S b) 0).
         contradict l. omega.

          rewrite J2.
          assert (S b - 1 = b)  as EQ. omega.
          rewrite EQ.
          assert (max b 0 = b) as EQ'.
            rewrite max_l; auto.
              omega.
          rewrite EQ'. auto.

   rewrite IHC; auto.
     assert (J1 := @aux_shift_ee_rec__close_ee_rec (shift_ee ee) a kk (S b) 0); auto.
     destruct (le_lt_dec (S b) 0).
       contradict l. omega.

       unfold close_ee.
       rewrite J1.
       unfold shift_ee. 
       assert (J2 := @shift_ee_rec_commute ee kk (S b) 1 0).
       destruct (le_lt_dec (S b) 0).
         contradict l0. omega.

          rewrite J2.
          assert (S b - 1 = b)  as EQ. omega.
          rewrite EQ.
          assert (max b 0 = b) as EQ'.
            rewrite max_l; auto.
              omega.
          rewrite EQ'. auto.

   rewrite IHC; auto.
     unfold shift_ee.
     unfold shift_te.
     rewrite -> shift_ee_shift_te_rec_commut; auto.

   rewrite IHC; auto.
     assert (J1 := @shift_ee_rec__close_te_rec (shift_te ee) a kk b 0).
     unfold shift_ee.
     unfold close_te.
     rewrite J1.
     unfold shift_te.
     rewrite -> shift_ee_shift_te_rec_commut; auto.
Qed.

Lemma aux_shift_tt_rec__close_tt_rec : forall t X m b k,
  match (le_lt_dec b k) with
  | left _    (* b <= k *) =>   shift_tt_rec m b (close_tt_rec k X t) = close_tt_rec (k + m) X (shift_tt_rec m b t)
  | right _  (* b > k *) => shift_tt_rec m b (close_tt_rec k X t) = close_tt_rec k X (shift_tt_rec m b t)
  end.
Proof.
  induction t; intros X m b k0; simpl; subst;
    destruct (le_lt_dec b k0); try solve[
      auto |

      assert (J1 := IHt1 X m b k0); auto;
      assert (J2 := IHt2 X m b k0); auto;
      destruct (le_lt_dec b k0); try solve[
        rewrite J1; auto; rewrite J2; auto |
        apply le_not_gt in l; contradict l0; auto] |

      assert (J1 := IHt1 X m b k0); auto;
      assert (J2 := IHt2 X m b k0); auto;
      destruct (le_lt_dec b k0); try solve[
        rewrite J1; auto; rewrite J2; auto |
        apply le_not_gt in l0; contradict l; auto] |

      assert (J := IHt X m b k0); auto;
      destruct (le_lt_dec b k0); try solve [
        rewrite J; auto |
        apply le_not_gt in l; contradict l0; auto] |

      assert (J := IHt X m b k0); auto;
      destruct (le_lt_dec b k0); try solve [
        apply le_not_gt in l0; contradict l; auto |
        rewrite J; auto ] |

      assert (J := IHt X m (S b) (S k0));
      destruct (le_lt_dec (S b) (S k0)); try solve [
        rewrite J; auto |
        apply le_not_gt in l; apply lt_S_n in l0; contradict l0; auto] |

      assert (J := IHt X m (S b) (S k0));
      destruct (le_lt_dec (S b) (S k0)); try solve [
        apply le_not_gt in l0; apply lt_n_S in l; contradict l; auto |
        rewrite J; auto]
      ].

    destruct (le_lt_dec b n); simpl; auto.

    destruct (le_lt_dec b n); simpl; auto.

    destruct (X==a); subst; simpl; auto.
      destruct (le_lt_dec b k0); simpl; auto.
        contradict l0. omega.

    destruct (X==a); subst; simpl; auto.
      destruct (le_lt_dec b k0); simpl; auto.
        contradict l0. omega.
Qed.

Lemma aux_shift_te_rec__close_te_rec : forall e X m b k,
  match (le_lt_dec b k) with
  | left _    (* b <= k *) =>   shift_te_rec m b (close_te_rec k X e) = close_te_rec (k + m) X (shift_te_rec m b e)
  | right _  (* b > k *) => shift_te_rec m b (close_te_rec k X e) = close_te_rec k X (shift_te_rec m b e)
  end.
Proof.
  induction e; intros X m b k0; simpl; subst; try solve [
    auto |

    assert (J := IHe X m b k0); auto;
    assert (J' := @aux_shift_tt_rec__close_tt_rec  t X m b k0); auto;
    destruct (le_lt_dec b k0); try solve [
            rewrite J; auto; try solve [rewrite J'; auto]] |

    assert (J := IHe X m b k0); auto;
    destruct (le_lt_dec b k0); try solve [
      rewrite J; auto |
      apply le_not_gt in l; contradict l0; auto] |

    assert (J1 := IHe1 X m b k0); auto;
    assert (J2 := IHe2 X m b k0); auto;
    destruct (le_lt_dec b k0); try solve[
      rewrite J1; auto; rewrite J2; auto |
      apply le_not_gt in l; contradict l0; auto]
    ].

    destruct (le_lt_dec b k0); subst; simpl; auto.
    destruct (le_lt_dec b k0); subst; simpl; auto.

    assert (J := IHe X m (S b) (S k0)); auto.
    destruct (le_lt_dec b k0).
      destruct (le_lt_dec (S b) (S k0)).
         rewrite J; auto.
         contradict l. omega. 
      destruct (le_lt_dec (S b) (S k0)).
         contradict l. omega. 
         rewrite J; auto.
Qed. 

Lemma close_tt_rec_commute : forall T (X Y: atom) k1 k2,
  X <> Y ->
  (close_tt_rec k1 X (close_tt_rec k2 Y T) =
    close_tt_rec k2 Y (close_tt_rec k1 X T)).
Proof.
  intros T X Y k1 k2 Neq.
  generalize dependent k1.
  generalize dependent k2.
  (typ_cases (induction T) Case); intros k2 k1; simpl in *;
    try solve [ auto |
                rewrite IHT; auto |
                rewrite IHT1; auto; rewrite IHT2; auto ].
  Case "typ_fvar".
    destruct (Y == a); destruct (X == a); subst; simpl in *; auto.
      contradict Neq; auto.
      destruct (a == a); subst; auto.
        contradict n0; auto.
      destruct (a == a); subst; auto.
        contradict n0; auto.
      destruct (Y == a); destruct (X == a); subst; auto.
        contradict n0; auto.
        contradict n; auto.
        contradict n0; auto.
Qed.

Lemma close_te_rec_commute : forall (X  Y: atom) e k1 k2,
  X <> Y ->
  (close_te_rec k1 X (close_te_rec k2 Y e) =
    close_te_rec k2 Y (close_te_rec k1 X e)).
Proof with auto.
  intros X Y e k1 k2 Neq.
  generalize dependent k1.
  generalize dependent k2.
  (exp_cases (induction e) Case); intros k2 k1; simpl in *;
    try solve [ auto |
                rewrite IHe; auto |
                rewrite IHe1; auto; rewrite IHe2; auto |
                rewrite IHe1; auto; rewrite IHe2; auto ; rewrite IHe3; auto ].
  Case "exp_abs".
    rewrite IHe...
    rewrite close_tt_rec_commute...
  Case "exp_tapp".
    rewrite IHe...
    rewrite close_tt_rec_commute...
Qed.

Lemma close_te_rec_plug : forall C k X e,
  X `notin`  (cv_ec C) ->
  close_te_rec k X (plug C e) =  plug (close_tc_rec k X C) (close_te_rec k X e).
Proof.
  induction C; intros kk X ee HX; simpl;
    try solve [
      auto |
      rewrite IHC; auto
    ].

   simpl in HX.
   rewrite IHC; auto.
     assert (J1 := @shift_ee_rec__close_te_rec ee X 1 0 kk).
     unfold shift_ee.
     rewrite J1. auto.

   simpl in HX.
   rewrite IHC; auto.
     assert (J1 := @shift_ee_rec__close_te_rec ee X 1 0 kk).
     unfold shift_ee.
     rewrite J1.
     unfold close_ee.
     rewrite -> close_ee_close_te_rec_commut; auto.

   simpl in HX.
   rewrite IHC; auto.
     assert (J1 := @aux_shift_te_rec__close_te_rec ee X 1 0 kk); auto.
     destruct (le_lt_dec 0 (S kk)).
       unfold shift_te.
       rewrite J1.
       assert (kk + 1 = S kk) as EQ. omega.
       rewrite EQ. auto.

       contradict l. omega.

   simpl in HX.
   rewrite IHC; auto.
     assert (J1 := @aux_shift_te_rec__close_te_rec ee X 1 0 kk); auto.
     destruct (le_lt_dec 0 (S kk)).
       unfold shift_te.
       unfold close_te.
       rewrite J1.
       assert (kk + 1 = S kk) as EQ. omega.
       rewrite EQ.
       rewrite close_te_rec_commute; auto.

       contradict l. omega.
Qed.

Lemma shift_tt_rec_commute : forall T k1 b1 k2 b2,
  match (le_lt_dec b1 b2) with
  | left _    (* b1 <= b2 *) => (shift_tt_rec k1 b1 (shift_tt_rec k2 b2 T) = shift_tt_rec k2 (b2+k1) (shift_tt_rec k1 b1 T))
  | right _  (* b1 > b2 *) => (shift_tt_rec k1 b1 (shift_tt_rec k2 b2 T) = shift_tt_rec k2 b2 (shift_tt_rec k1 (max (b1-k2) b2) T))
  end.
Proof with auto.
  (typ_cases (induction T) Case); intros k1 b1 k2 b2; simpl in *.
  Case "typ_bvar".
    destruct (le_lt_dec b1 b2); subst; simpl.
      destruct (le_lt_dec b2 n); subst; simpl.
        destruct (le_lt_dec b1 n); subst; simpl.
          destruct (le_lt_dec b1 (n+k2)); subst; simpl.
            destruct (le_lt_dec (b2+k1) (n+k1)); subst; simpl.
              assert (k2+k1=k1+k2) as EQ. omega.
              assert (n+k2+k1=n+(k2+k1)) as EQ'. omega.
              assert (n+k1+k2=n+(k1+k2)) as EQ''. omega.
              rewrite EQ'. rewrite EQ. rewrite EQ''. auto.

              contradict l0. clear - l3. omega.
            assert (b2 < b1) as H.
              clear - l0 l2. omega.
            contradict H. clear - l. omega.
          assert (b2 < b1) as H.
            clear - l0 l1. omega.
          contradict H. clear - l. omega.
        destruct (le_lt_dec b1 n); subst; simpl.
          destruct (le_lt_dec (b2+k1) (n+k1)); subst; simpl; auto.
            assert (b2 <= n) as H.
              clear - l2. omega.
            contradict l0. clear - H. omega.
          destruct (le_lt_dec (b2+k1) n); subst; simpl; auto.
            assert (b2 <= n) as H.
              clear - l2. omega.
            contradict l0. clear - H. omega.
      destruct (le_lt_dec b2 n); subst; simpl.
        destruct (le_lt_dec b1 (n+k2)); subst; simpl.
          destruct (le_lt_dec (max (b1-k2) b2) n); subst; simpl.
            destruct (le_lt_dec b2 (n+k1)); subst; simpl.
              assert (k2+k1=k1+k2) as EQ. omega.
              assert (n+k2+k1=n+(k2+k1)) as EQ'. omega.
              assert (n+k1+k2=n+(k1+k2)) as EQ''. omega.
              rewrite EQ'. rewrite EQ. rewrite EQ''. auto.

              assert (n < b2) as H.
                clear - l3. omega.
              contradict l0. clear - H. omega.
            destruct (le_lt_dec (b1 - k2) b2).
              rewrite max_r in l2; auto.
              assert (b2 < b2) as H.
                clear - l2 l0. 
                omega.
              contradict H. omega.

              rewrite max_l in l2; try solve [omega].
              assert (n+k2 < b1) as H.
                clear - l2. 
                omega.
              assert (b1 < b1) as H'.
                clear - l1 H. omega.
              contradict H'. omega.
          destruct (le_lt_dec (max (b1-k2) b2) n); subst; simpl.
            assert (b1 - k2 <= max (b1 - k2) b2) as J.
              apply le_max_l; auto.
            assert (b1 - k2 <= n) as J'.
              omega.
            assert (b1 <= n+k2) as H.
              clear - J'. omega.
            assert (b1 < b1) as H'.
              clear - l1 H. omega.
            contradict H'. omega.

            destruct (le_lt_dec b2 n); subst; simpl; auto.
              assert (b2 < b2) as H.
                clear - l0 l3. omega.
              contradict H. omega.
          destruct (le_lt_dec (max (b1-k2) b2) n); subst; simpl.
            destruct (le_lt_dec b1 n); subst; simpl.
              destruct (le_lt_dec b2 (n+k1)); subst; simpl; auto.
                assert (b1 < b2) as H.
                  clear - l0 l2. omega.
                contradict H. clear - l. omega.
              assert (b2 <= max (b1 - k2) b2) as J.
                apply le_max_r; auto.
              assert (b2 <= n) as J'. omega.
              contradict J'. omega.
            destruct (le_lt_dec b1 n); subst; simpl.
              assert (b1 < b2) as J. omega.
              contradict J. omega.

              destruct (le_lt_dec b2 n); subst; simpl; auto.
                contradict l0. omega.

  Case "typ_fvar".
    destruct (le_lt_dec b1 b2); subst; simpl; auto.

  Case "typ_arrow".
    assert (J1 := IHT1 k1 b1 k2 b2).
    assert (J2 := IHT2 k1 b1 k2 b2).
    destruct (le_lt_dec b1 b2); subst; simpl.
      rewrite J1. rewrite J2. auto.
      rewrite J1. rewrite J2. auto.

  Case "typ_all".
    assert (J := IHT k1 (S b1) k2 (S b2)).
    destruct (le_lt_dec b1 b2); subst; simpl.
      destruct (le_lt_dec (S b1) (S b2)); subst; simpl.
        rewrite J. auto.

        assert (b2 < b1) as J'. clear - l0. omega.
        contradict J'. omega.

      destruct (le_lt_dec (S b1) (S b2)); subst; simpl.
        assert (b1 <= b2) as J'. clear - l0. omega.
        contradict J'. omega.

        rewrite J. rewrite max_SS.
        destruct (le_lt_dec (S b1) k2).
          assert (S b1 - k2 = 0) as EQ. omega.
          assert (S (b1 - k2) = 1) as EQ'. omega.
          rewrite EQ. rewrite EQ'. clear EQ EQ'.
          assert (max 0 (S b2) = S b2) as EQ.
            rewrite max_r; auto.
              omega.
          assert (max 1 (S b2) = S b2) as EQ'.
            rewrite max_r; auto.
              omega.
          rewrite EQ. rewrite EQ'. auto.

          assert (S b1 - k2 = S (b1 - k2)) as EQ. omega.
          rewrite EQ. auto. 

  Case "typ_with".
    assert (J1 := IHT1 k1 b1 k2 b2).
    assert (J2 := IHT2 k1 b1 k2 b2).
    destruct (le_lt_dec b1 b2); subst; simpl.
      rewrite J1. rewrite J2. auto.
      rewrite J1. rewrite J2. auto.
Qed.

Lemma shift_te_rec_commute : forall e k1 b1 k2 b2,
  match (le_lt_dec b1 b2) with
  | left _    (* b1 <= b2 *) => (shift_te_rec k1 b1 (shift_te_rec k2 b2 e) = shift_te_rec k2 (b2+k1) (shift_te_rec k1 b1 e))
  | right _  (* b1 > b2 *) => (shift_te_rec k1 b1 (shift_te_rec k2 b2 e) = shift_te_rec k2 b2 (shift_te_rec k1 (max (b1-k2) b2) e))
  end.
Proof with auto.
  (exp_cases (induction e) Case); intros k1 b1 k2 b2; simpl in *.
  Case "exp_bvar".
    destruct (le_lt_dec b1 b2); subst; simpl; auto.

  Case "exp_fvar".
    destruct (le_lt_dec b1 b2); subst; simpl; auto.

  Case "exp_abs".
    assert (J := IHe k1 b1 k2 b2).
    assert (J':=@shift_tt_rec_commute t k1 b1 k2 b2).
    destruct (le_lt_dec b1 b2); subst; simpl.
      rewrite J. rewrite J'. auto.
      rewrite J. rewrite J'. auto.

  Case "exp_app".
    assert (J1 := IHe1 k1 b1 k2 b2).
    assert (J2 := IHe2 k1 b1 k2 b2).
    destruct (le_lt_dec b1 b2); subst; simpl.
      rewrite J1. rewrite J2. auto.
      rewrite J1. rewrite J2. auto.

  Case "exp_tabs".
    assert (J := IHe k1 (S b1) k2 (S b2)).
    destruct (le_lt_dec b1 b2); subst; simpl.
      destruct (le_lt_dec (S b1) (S b2)); subst; simpl.
        rewrite J. auto.

        assert (b2 < b1) as J'. clear - l0. omega.
        contradict J'. omega.

      destruct (le_lt_dec (S b1) (S b2)); subst; simpl.
        assert (b1 <= b2) as J'. clear - l0. omega.
        contradict J'. omega.

        rewrite J. rewrite max_SS.
        destruct (le_lt_dec (S b1) k2).
          assert (S b1 - k2 = 0) as EQ. omega.
          assert (S (b1 - k2) = 1) as EQ'. omega.
          rewrite EQ. rewrite EQ'. clear EQ EQ'.
          assert (max 0 (S b2) = S b2) as EQ.
            rewrite max_r; auto.
              omega.
          assert (max 1 (S b2) = S b2) as EQ'.
            rewrite max_r; auto.
              omega.
          rewrite EQ. rewrite EQ'. auto.

          assert (S b1 - k2 = S (b1 - k2)) as EQ. omega.
          rewrite EQ. auto. 

  Case "exp_tapp".
    assert (J := IHe k1 b1 k2 b2).
    assert (J':=@shift_tt_rec_commute t k1 b1 k2 b2).
    destruct (le_lt_dec b1 b2); subst; simpl.
      rewrite J. rewrite J'. auto.
      rewrite J. rewrite J'. auto.

  Case "exp_apair".
    assert (J1 := IHe1 k1 b1 k2 b2).
    assert (J2 := IHe2 k1 b1 k2 b2).
    destruct (le_lt_dec b1 b2); subst; simpl.
      rewrite J1. rewrite J2. auto.
      rewrite J1. rewrite J2. auto.

  Case "exp_fst".
    assert (J := IHe k1 b1 k2 b2).
    destruct (le_lt_dec b1 b2); subst; simpl.
      rewrite J. auto.
      rewrite J. auto.

  Case "exp_snd".
    assert (J := IHe k1 b1 k2 b2).
    destruct (le_lt_dec b1 b2); subst; simpl.
      rewrite J. auto.
      rewrite J. auto.
Qed.

Lemma shift_te_rec_plug : forall C k b e,
  shift_te_rec k b (plug C e) =  plug (shift_tc_rec k b C) (shift_te_rec k b e).
Proof.
  induction C; intros kk b ee; simpl;
    try solve [
      auto |
      rewrite IHC; auto
    ].

   rewrite IHC; auto.
     unfold shift_te.
     unfold shift_ee.
     rewrite -> shift_ee_shift_te_rec_commut; auto.

   rewrite IHC; auto.
     assert (J1 := @shift_te_rec__close_ee_rec (shift_ee ee) a kk b 0).
     unfold shift_te.
     unfold close_ee.
     rewrite J1.
     unfold shift_ee.
     rewrite -> shift_ee_shift_te_rec_commut; auto.

   rewrite IHC; auto.
     destruct (le_lt_dec (S b) 0).
       contradict l. omega.

       unfold shift_te. 
       assert (J2 := @shift_te_rec_commute ee kk (S b) 1 0).
       destruct (le_lt_dec (S b) 0).
         contradict l. omega.

          rewrite J2.
          assert (S b - 1 = b)  as EQ. omega.
          rewrite EQ.
          assert (max b 0 = b) as EQ'.
            rewrite max_l; auto.
              omega.
          rewrite EQ'. auto.

   rewrite IHC; auto.
     assert (J1 := @aux_shift_te_rec__close_te_rec (shift_te ee) a kk (S b) 0); auto.
     destruct (le_lt_dec (S b) 0).
       contradict l. omega.

       unfold close_te.
       rewrite J1.
       unfold shift_te. 
       assert (J2 := @shift_te_rec_commute ee kk (S b) 1 0).
       destruct (le_lt_dec (S b) 0).
         contradict l0. omega.

          rewrite J2.
          assert (S b - 1 = b)  as EQ. omega.
          rewrite EQ.
          assert (max b 0 = b) as EQ'.
            rewrite max_l; auto.
              omega.
          rewrite EQ'. auto.
Qed.

Lemma open_ee_rec_fv_te_eq : forall e1 (x2:atom) kk,
  fv_te e1 [=] fv_te (open_ee_rec kk x2 e1).
Proof.
  induction e1; intros x2 kk; simpl; try solve [eauto | fsetdec].
    destruct (kk==n); auto.

    assert (J:=@IHe1 x2 (S kk)). fsetdec.
     
    assert (J:=@IHe1 x2 kk). fsetdec.
Qed.

Lemma open_ee_fv_te_eq : forall e1 (x2:atom),
  fv_te e1 [=] fv_te (open_ee e1 x2).
Proof.
  intros. apply open_ee_rec_fv_te_eq.
Qed.

Lemma open_ec_rec_fv_tc_eq : forall C1 (x2:atom) kk,
  fv_tc (open_ec_rec kk x2 C1) [=] fv_tc C1.
Proof.
  induction C1; intros x2 kk; simpl; try solve [eauto | fsetdec].
    assert (J':=@IHC1 x2 (S kk)).
    fsetdec.

    assert (J':=@IHC1 x2 (S kk)).
    fsetdec.

    assert (J:=@open_ee_rec_fv_te_eq e x2 kk).
    assert (J':=@IHC1 x2 kk).
    fsetdec.

    assert (J:=@open_ee_rec_fv_te_eq e x2 kk).
    assert (J':=@IHC1 x2 kk).
    fsetdec.

    assert (J':=@IHC1 x2 kk).
    fsetdec.

    assert (J:=@open_ee_rec_fv_te_eq e x2 kk).
    assert (J':=@IHC1 x2 kk).
    fsetdec.

    assert (J:=@open_ee_rec_fv_te_eq e x2 kk).
    assert (J':=@IHC1 x2 kk).
    fsetdec.
Qed.

Lemma open_ec_fv_tc_eq : forall C1 (x2:atom),
  fv_tc (open_ec C1 x2) [=] fv_tc C1.
Proof.
  intros. apply open_ec_rec_fv_tc_eq.
Qed.

Lemma fv_te_close_ee_rec : forall e kk x,
  fv_te e [=]fv_te (close_ee_rec kk x e).
Proof.
  induction e; intros kk X; simpl; auto.
    destruct (X==a); auto.
    rewrite <- IHe. fsetdec.
    rewrite <- IHe. fsetdec.
Qed.

Lemma fv_te_close_ee : forall e x,
  fv_te e [=]fv_te (close_ee e x).
Proof.
  intros e kk X.
  unfold close_ee.
  apply fv_te_close_ee_rec.
Qed.

Lemma fv_tc_close_ec_rec : forall C kk x,
  fv_tc C [=]fv_tc (close_ec_rec kk x C).
Proof.
  induction C; intros kk x; simpl; 
  try solve [
    auto |
    rewrite <- IHC; fsetdec |
    rewrite <- IHC;
    rewrite <- fv_te_close_ee_rec;
    fsetdec].
Qed.

Lemma fv_tc_close_ec : forall C x,
  fv_tc C [=] fv_tc (close_ec C x).
Proof.
  intros C x.
  unfold close_ec.
  apply fv_tc_close_ec_rec.
Qed.

Lemma fv_te_open_ee_rec_eq : forall e kk (x:atom),
  fv_te (open_ee_rec kk x e) [=] fv_te e.
Proof.
  induction e; intros kk x; simpl; auto.
    destruct (kk==n); simpl; fsetdec.

    assert (J:=@IHe (S kk)). rewrite J. fsetdec.

    assert (J:=@IHe kk). rewrite J. fsetdec.
Qed.

Lemma fv_te_open_ee_eq : forall e (x:atom),
  fv_te (open_ee e x) [=] fv_te e.
Proof.
  intros e x.
  unfold open_ee.
  apply fv_te_open_ee_rec_eq.
Qed.

Lemma open_te_rec_fv_te_lower : forall e1 T2 kk,
  fv_te e1 [<=] fv_te (open_te_rec kk T2 e1).
Proof.
  induction e1; intros T2 kk; simpl; try solve [eauto | fsetdec].
    assert (J1:=@IHe1 T2 kk).
    assert (J2:=@open_tt_rec_fv_tt_lower t T2 kk).
    fsetdec.
    
    assert (J1:=@IHe1_1 T2 kk).
    assert (J2:=@IHe1_2 T2 kk).
    fsetdec.

    assert (J1:=@IHe1 T2 kk).
    assert (J2:=@open_tt_rec_fv_tt_lower t T2 kk).
    fsetdec.
    
    assert (J1:=@IHe1_1 T2 kk).
    assert (J2:=@IHe1_2 T2 kk).
    fsetdec.
Qed.

Lemma open_te_fv_te_lower : forall e1 T2,
  fv_te e1 [<=] fv_te (open_te e1 T2).
Proof.
  intros. apply open_te_rec_fv_te_lower.
Qed.

Lemma open_tc_rec_fv_tc_lower : forall C1 T2 kk,
  fv_tc C1 [<=] fv_tc (open_tc_rec kk T2 C1).
Proof.
  induction C1; intros T2 kk; simpl; try solve [eauto | fsetdec].
    assert (J:=@open_tt_rec_fv_tt_lower t T2 kk).
    assert (J':=@IHC1 T2 kk).
    fsetdec.

    assert (J:=@open_tt_rec_fv_tt_lower t T2 kk).
    assert (J':=@IHC1 T2 kk).
    fsetdec.

    assert (J:=@open_te_rec_fv_te_lower e T2 kk).
    assert (J':=@IHC1 T2 kk).
    fsetdec.

    assert (J:=@open_te_rec_fv_te_lower e T2 kk).
    assert (J':=@IHC1 T2 kk).
    fsetdec.

    assert (J:=@open_tt_rec_fv_tt_lower t T2 kk).
    assert (J':=@IHC1 T2 kk).
    fsetdec.

    assert (J:=@open_te_rec_fv_te_lower e T2 kk).
    assert (J':=@IHC1 T2 kk).
    fsetdec.

    assert (J:=@open_te_rec_fv_te_lower e T2 kk).
    assert (J':=@IHC1 T2 kk).
    fsetdec.
Qed.

Lemma open_tc_fv_tc_lower : forall C1 T2,
  fv_tc C1 [<=] fv_tc (open_tc C1 T2).
Proof.
  intros. apply open_tc_rec_fv_tc_lower.
Qed.

Lemma close_tt_rec_fv_tt_notin : forall t X kk, 
  X `notin` fv_tt (close_tt_rec kk X t).
Proof.
  induction t; intros X kk; simpl; try solve [eauto | fsetdec].
     destruct (X==a); subst; simpl; fsetdec.
Qed.

Lemma close_tt_fv_tt_notin : forall t X,
  X  `notin` fv_tt (close_tt t X).
Proof.
  intros. apply close_tt_rec_fv_tt_notin.
Qed.

Lemma close_te_rec_fv_te_notin : forall e X kk, 
  X `notin` fv_te (close_te_rec kk X e).
Proof.
  induction e; intros x kk; simpl; try solve [eauto using close_tt_rec_fv_tt_notin | fsetdec ].
Qed.

Lemma close_te_fv_te_notin : forall e X,
  X  `notin` fv_te (close_te e X).
Proof.
  intros. apply close_te_rec_fv_te_notin.
Qed.

Lemma close_tc_rec_fv_tc_notin : forall C X kk, 
  X `notin` fv_tc (close_tc_rec kk X C).
Proof.
  induction C; intros X kk; simpl; 
    try solve [auto using close_te_rec_fv_te_notin, close_tt_rec_fv_tt_notin].
Qed.

Lemma close_tc_fv_tc_notin : forall C X,
  X  `notin` fv_tc (close_tc C X).
Proof.
  intros. apply close_tc_rec_fv_tc_notin.
Qed.

Lemma close_tt_rec_fv_tt_upper : forall t1 X kk,
  fv_tt (close_tt_rec kk X t1) [<=] fv_tt t1.
Proof.
  induction t1; intros X kk; simpl; try solve [eauto | fsetdec].
     destruct (X==a); subst; simpl; fsetdec.

     assert (J1:=@IHt1_1 X kk).
     assert (J2:=@IHt1_2 X kk).
     fsetdec.
    
     assert (J1:=@IHt1_1 X kk).
     assert (J2:=@IHt1_2 X kk).
     fsetdec.
Qed.

Lemma close_tt_fv_tt_upper : forall t1 X,
  fv_tt (close_tt t1 X) [<=] fv_tt t1.
Proof.
  intros. apply close_tt_rec_fv_tt_upper.
Qed.

Lemma close_te_rec_fv_te_upper : forall e1 X kk,
  fv_te (close_te_rec kk X e1) [<=] fv_te e1.
Proof.
  induction e1; intros X kk; simpl; try solve [eauto | fsetdec].
     assert (J1:=@IHe1 X kk).
     assert (J2:=@close_tt_rec_fv_tt_upper t X kk).
     fsetdec.
    
     assert (J1:=@IHe1_1 X kk).
     assert (J2:=@IHe1_2 X kk).
     fsetdec.

     assert (J1:=@IHe1 X kk).
     assert (J2:=@close_tt_rec_fv_tt_upper t X kk).
     fsetdec.

     assert (J1:=@IHe1_1 X kk).
     assert (J2:=@IHe1_2 X kk).
     fsetdec.
Qed.

Lemma close_te_fv_te_upper : forall e1 X,
  fv_te (close_te e1 X) [<=] fv_te e1.
Proof.
  intros. apply close_te_rec_fv_te_upper.
Qed.

Lemma close_tc_rec_fv_tc_upper : forall C1 X kk,
  fv_tc (close_tc_rec kk X C1) [<=] fv_tc C1.
Proof.
  induction C1; intros X kk; simpl; try solve [eauto | fsetdec].
    assert (J:=@close_tt_rec_fv_tt_upper t X kk).
    assert (J':=@IHC1 X kk).
    fsetdec.

    assert (J:=@close_tt_rec_fv_tt_upper t X kk).
    assert (J':=@IHC1 X kk).
    fsetdec.

    assert (J:=@close_te_rec_fv_te_upper e X kk).
    assert (J':=@IHC1 X kk).
    fsetdec.

    assert (J:=@close_te_rec_fv_te_upper e X kk).
    assert (J':=@IHC1 X kk).
    fsetdec.

    assert (J:=@close_tt_rec_fv_tt_upper t X kk).
    assert (J':=@IHC1 X kk).
    fsetdec.

    assert (J:=@close_te_rec_fv_te_upper e X kk).
    assert (J':=@IHC1 X kk).
    fsetdec.

    assert (J:=@close_te_rec_fv_te_upper e X kk).
    assert (J':=@IHC1 X kk).
    fsetdec.
Qed.

Lemma close_tc_fv_tc_upper : forall C1 X,
  fv_tc (close_tc C1 X) [<=] fv_tc C1.
Proof.
  intros. apply close_tc_rec_fv_tc_upper.
Qed.

Lemma shift_ec_rec__close_tc_rec : forall C X m b k,
  shift_ec_rec m b (close_tc_rec k X C) = close_tc_rec k X (shift_ec_rec m b C).
Proof.
  induction C; intros X m b k0; simpl; subst; try solve[
      auto |
      rewrite IHC; rewrite shift_ee_rec__close_te_rec; auto |
      rewrite IHC; auto
      ].
Qed.

Lemma aux_shift_tc_rec__close_tc_rec : forall C X m b k,
  match (le_lt_dec b k) with
  | left _    (* b <= k *) =>   shift_tc_rec m b (close_tc_rec k X C) = close_tc_rec (k + m) X (shift_tc_rec m b C)
  | right _  (* b > k *) => shift_tc_rec m b (close_tc_rec k X C) = close_tc_rec k X (shift_tc_rec m b C)
  end.
Proof.
  induction C; intros X m b k0; simpl; subst; try solve [
    auto |

    assert (J := IHC X m b k0); auto;
    assert (J' := @aux_shift_tt_rec__close_tt_rec  t X m b k0); auto;
    destruct (le_lt_dec b k0); try solve [
            rewrite J; auto; try solve [rewrite J'; auto]] |

    assert (J := IHC X m b k0); auto;
    destruct (le_lt_dec b k0); try solve [
      rewrite J; auto |
      apply le_not_gt in l; contradict l0; auto] |

    assert (J1 := IHC X m b k0); auto;
    assert (J2 := aux_shift_te_rec__close_te_rec e X m b k0); auto;
    destruct (le_lt_dec b k0); try solve[
      rewrite J1; auto; rewrite J2; auto |
      apply le_not_gt in l; contradict l0; auto]
    ].

    destruct (le_lt_dec b k0); subst; simpl; auto.

    assert (J := IHC X m (S b) (S k0)); auto.
    destruct (le_lt_dec b k0).
      destruct (le_lt_dec (S b) (S k0)).
         rewrite J; auto.
         contradict l. omega. 
      destruct (le_lt_dec (S b) (S k0)).
         contradict l. omega. 
         rewrite J; auto.

    assert (J := IHC X m (S b) (S k0)); auto.
    destruct (le_lt_dec b k0).
      destruct (le_lt_dec (S b) (S k0)).
         rewrite J; auto.
         contradict l. omega. 
      destruct (le_lt_dec (S b) (S k0)).
         contradict l. omega. 
         rewrite J; auto.
Qed. 

Lemma close_tc_rec_commute : forall (X  Y: atom) C k1 k2,
  X <> Y ->
  (close_tc_rec k1 X (close_tc_rec k2 Y C) =
    close_tc_rec k2 Y (close_tc_rec k1 X C)).
Proof with auto.
  intros X Y C k1 k2 Neq.
  generalize dependent k1.
  generalize dependent k2.
  induction C; intros k2 k1; simpl in *;
    try solve [ auto |
                rewrite IHC; auto |
                rewrite IHC; auto; rewrite close_te_rec_commute; auto ].
    rewrite IHC...
    rewrite close_tt_rec_commute...

    rewrite IHC...
    rewrite close_tt_rec_commute...

    rewrite IHC...
    rewrite close_tt_rec_commute...
Qed.

Lemma close_tc_rec_plugC : forall C k X C',
  X `notin`  (cv_ec C) ->
  close_tc_rec k X (plugC C C') =  plugC (close_tc_rec k X C) (close_tc_rec k X C').
Proof.
  induction C; intros kk X C' HX; simpl;
    try solve [
      auto |
      rewrite IHC; auto
    ].

   simpl in HX.
   rewrite IHC; auto.
     assert (J1 := @shift_ec_rec__close_tc_rec C' X 1 0 kk).
     unfold shift_ec.
     rewrite J1. auto.

   simpl in HX.
   rewrite IHC; auto.
     assert (J1 := @shift_ec_rec__close_tc_rec C' X 1 0 kk).
     unfold shift_ec.
     rewrite J1.
     unfold close_ec.
     rewrite -> close_ec_close_tc_rec_commut; auto.

   simpl in HX.
   rewrite IHC; auto.
     assert (J1 := @aux_shift_tc_rec__close_tc_rec C' X 1 0 kk); auto.
     destruct (le_lt_dec 0 (S kk)).
       unfold shift_tc.
       rewrite J1.
       assert (kk + 1 = S kk) as EQ. omega.
       rewrite EQ. auto.

       contradict l. omega.

   simpl in HX.
   rewrite IHC; auto.
     assert (J1 := @aux_shift_tc_rec__close_tc_rec C' X 1 0 kk); auto.
     destruct (le_lt_dec 0 (S kk)).
       unfold shift_tc.
       unfold close_tc.
       rewrite J1.
       assert (kk + 1 = S kk) as EQ. omega.
       rewrite EQ.
       rewrite close_tc_rec_commute; auto.

       contradict l. omega.
Qed.

Lemma open_close_ee_rec__id : forall e x k,
  x `notin` fv_ee e ->
  close_ee_rec k x (open_ee_rec k x e) = e.
Proof.
  induction e; intros x k0 Hnotin; simpl; simpl in Hnotin; auto.
    destruct (k0==n); subst; simpl; auto.
      destruct (x==x); auto.
        contradict n0; auto.

    destruct (x==a); subst; auto.
      contradict Hnotin; auto.

    rewrite IHe; auto.

    rewrite IHe1; auto.
    rewrite IHe2; auto.

    rewrite IHe; auto.

    rewrite IHe; auto.

    rewrite IHe1; auto.
    rewrite IHe2; auto.

    rewrite IHe; auto.

    rewrite IHe; auto.
Qed.    

Lemma open_close_ee__id : forall e x,
  x `notin` fv_ee e ->
  close_ee (open_ee e x) x = e.
Proof.
  intros e x He.
  unfold open_ee.
  unfold close_ee.
  apply open_close_ee_rec__id; auto.
Qed.

Lemma open_close_tt_rec__id : forall t X k,
  X `notin` fv_tt t ->
  close_tt_rec k X (open_tt_rec k X t) = t.
Proof.
  induction t; intros X k0 Hnotin; simpl; simpl in Hnotin; auto.
    destruct (k0==n); subst; simpl; auto.
      destruct (X==X); auto.
        contradict n0; auto.

    destruct (X==a); subst; auto.
      contradict Hnotin; auto.

    rewrite IHt1; auto.
    rewrite IHt2; auto.

    rewrite IHt; auto.

    rewrite IHt1; auto.
    rewrite IHt2; auto.
Qed.    

Lemma open_close_tt__id : forall t X,
  X `notin` fv_tt t ->
  close_tt (open_tt t X) X = t.
Proof.
  intros t X Ht.
  unfold open_tt.
  unfold close_tt.
  apply open_close_tt_rec__id; auto.
Qed.

Lemma open_close_te_rec__id : forall e X k,
  X `notin` fv_te e ->
  close_te_rec k X (open_te_rec k X e) = e.
Proof.
  induction e; intros X k0 Hnotin; simpl; simpl in Hnotin; auto.
    rewrite IHe; auto.
    rewrite open_close_tt_rec__id; auto.

    rewrite IHe1; auto.
    rewrite IHe2; auto.

    rewrite IHe; auto.

    rewrite IHe; auto.
    rewrite open_close_tt_rec__id; auto.

    rewrite IHe1; auto.
    rewrite IHe2; auto.

    rewrite IHe; auto.

    rewrite IHe; auto.
Qed.    

Lemma open_close_te__id : forall e X,
  X `notin` fv_te e ->
  close_te (open_te e X) X = e.
Proof.
  intros e X He.
  unfold open_ee.
  unfold close_ee.
  apply open_close_te_rec__id; auto.
Qed.

Lemma cv_ec_close_ec_rec' : forall C kk X,
  cv_ec C [=] cv_ec (close_ec_rec kk X C).
Proof.
  induction C; intros kk X; simpl; auto.
Qed.

Lemma cv_ec_close_ec : forall C X,
  cv_ec C [=] cv_ec (close_ec C X).
Proof.
  intros C X.
  unfold close_ec.
  apply cv_ec_close_ec_rec'.
Qed.

Lemma close_tc_context : forall X C,
  X `notin` (fv_tc C) ->
  C = close_tc C X.
Proof.
  intros X C Fv.
  unfold close_tc.
  apply close_tc_rec_context; auto.
Qed.

Lemma cv_tc_close_ec_rec : forall C kk x,
  cv_tc C [=] cv_tc (close_ec_rec kk x C).
Proof.
  induction C; intros kk x; simpl; auto.
Qed.

Lemma cv_tc_close_ec : forall C x,
  cv_tc C [=] cv_tc (close_ec C x).
Proof.
  intros C x.
  unfold close_ec.
  apply cv_tc_close_ec_rec.
Qed.


Lemma cv_tc_close_tc_rec : forall C kk X,
  cv_tc C [=] cv_tc (close_tc_rec kk X C).
Proof.
  induction C; intros kk X; simpl; auto.
Qed.

Lemma cv_tc_close_tc : forall C X,
  cv_tc C [=] cv_tc (close_tc C X).
Proof.
  intros C X.
  unfold close_tc.
  apply cv_tc_close_tc_rec.
Qed.

Lemma cv_ec__includes__cv_tc : forall C,
  cv_tc C [<=] cv_ec C.
Proof.
  induction C; simpl; auto.
    fsetdec.
    fsetdec.
    fsetdec.
Qed. 

Lemma notin_remove_tmvar_dom : forall x E,
  x `notin` dom E ->
  x `notin` dom (remove_tmvar E).
Proof.
  intros x.
  induction E; intros; simpl; auto.
    destruct a.
    simpl_env in H.
    destruct_notin.
    destruct b; simpl; auto.
Qed.

Lemma fv_env_is_ddom_env : forall E,
  gdom_env E [=] {} ->
  fv_env E [=] ddom_env E.
Proof.
  induction E; simpl; intros; auto.
    destruct a.
    destruct b.
      apply IHE in H; auto.
      assert (a `in` {}) as FALSE.
        rewrite <- H.
      auto.
      contradict FALSE; auto.
Qed.

Lemma cv_ec_close_tc_rec' : forall C kk X,
  cv_ec C [=] cv_ec (close_tc_rec kk X C).
Proof.
  induction C; intros kk X; simpl; auto.
Qed.

Lemma cv_ec_close_tc : forall C X,
  cv_ec C [=] cv_ec (close_tc C X).
Proof.
  intros C X.
  unfold close_tc.
  apply cv_ec_close_tc_rec'.
Qed.

Lemma open_tc_shift_tc__notin_fv : forall C X n b,
  X `notin` (fv_tc C) ->
  X `notin` (fv_tc (shift_tc_rec n b C)).
Proof.
  induction C; intros X i b H; simpl in *; auto.
    destruct_notin.
    apply open_tt_shift_tt__notin_fv with (n:=i) (b:=b) in H; auto.

    destruct_notin.
    apply open_tt_shift_tt__notin_fv with (n:=i) (b:=b) in H; auto.

    destruct_notin.
    apply open_shift_te__notin_fv with (n:=i) (b:=b) in NotInTac; auto.

    destruct_notin.
    apply open_shift_te__notin_fv with (n:=i) (b:=b) in H; auto.

    destruct_notin.
    apply open_tt_shift_tt__notin_fv with (n:=i) (b:=b) in NotInTac; auto.

    destruct_notin.
    apply open_shift_te__notin_fv with (n:=i) (b:=b) in NotInTac; auto.

    destruct_notin.
    apply open_shift_te__notin_fv with (n:=i) (b:=b) in H; auto.
Qed.

Lemma subst_tt_tt' : forall T (X Y:atom) t K Env,
  wf_typ Env t K ->
  Y `notin` fv_tt T `union` dom Env ->
  subst_tt Y t (subst_tt X Y T) = subst_tt X t T.
Proof.
  induction T; intros X Y t K Env Wft Fv; simpl; auto.
    destruct (a == X); subst; simpl.
      destruct (Y == Y); subst; simpl; auto.
         contradict n; auto.
      destruct (a == Y); subst; simpl; auto.
         simpl in Fv.
         contradict Fv; auto.

    simpl in Fv.
    rewrite IHT1 with (Env:=Env) (K:=K); auto.
    rewrite IHT2 with (Env:=Env)  (K:=K); auto.

    simpl in Fv.
    rewrite IHT with (Env:=Env) (K:=K); auto.

    simpl in Fv.
    rewrite IHT1 with (Env:=Env) (K:=K); auto.
    rewrite IHT2 with (Env:=Env) (K:=K); auto.
Qed.

Lemma close_te_rec_fv_ee_eq : forall e X kk, 
  fv_ee e [=] fv_ee (close_te_rec kk X e).
Proof.
  induction e; intros X kk; simpl; try solve [eauto | fsetdec].
Qed.

Lemma close_te_fv_ee_eq : forall e X,
  fv_ee e [=] fv_ee (close_te e X).
Proof.
  intros. apply close_te_rec_fv_ee_eq.
Qed.

Lemma close_tc_rec_fv_ec_eq : forall C X kk, 
  fv_ec C [=] fv_ec (close_tc_rec kk X C).
Proof.
  induction C; intros X kk; simpl; try solve [eauto | fsetdec].
    assert (J:=@close_te_rec_fv_ee_eq e X kk).
    assert (J':=@IHC X kk).
    fsetdec.

    assert (J:=@close_te_rec_fv_ee_eq e X kk).
    assert (J':=@IHC X kk).
    fsetdec.

    assert (J:=@close_te_rec_fv_ee_eq e X kk).
    assert (J':=@IHC X kk).
    fsetdec.

    assert (J:=@close_te_rec_fv_ee_eq e X kk).
    assert (J':=@IHC X kk).
    fsetdec.
Qed.

Lemma close_tc_fv_ec_eq : forall C X,
  fv_ec C [=] fv_ec (close_tc C X).
Proof.
  intros. apply close_tc_rec_fv_ec_eq.
Qed.

Lemma close_tc_rec_cv_ec_eq : forall C X kk, 
  cv_ec C [=] cv_ec (close_tc_rec kk X C).
Proof.
  induction C; intros X kk; simpl; try solve [eauto | fsetdec].
Qed.

Lemma close_tc_cv_ec_eq : forall C X,
  cv_ec C [=] cv_ec (close_tc C X).
Proof.
  intros. apply close_tc_rec_cv_ec_eq.
Qed.

Lemma close_tt_rec_fv_tt_lower : forall T X kk, 
  fv_tt T [<=] fv_tt (close_tt_rec kk X T) `union` {{X}}.
Proof.
  induction T; intros X kk; simpl; try solve [eauto | fsetdec].
     destruct (X==a); subst; simpl; fsetdec.

     assert (J1:=@IHT1 X kk).
     assert (J2:=@IHT2 X kk).
     fsetdec.
    
     assert (J1:=@IHT1 X kk).
     assert (J2:=@IHT2 X kk).
     fsetdec.
Qed.

Lemma close_tt_fv_tt_lower : forall T X,
  fv_tt T [<=] fv_tt (close_tt T X) `union` {{X}}.
Proof.
  intros. apply close_tt_rec_fv_tt_lower.
Qed.

Lemma close_ee_rec_fv_ee_eq' : forall e1 x kk,
  fv_ee (close_ee_rec kk x e1) [=] AtomSetImpl.diff (fv_ee e1) {{x}}.
Proof.
  induction e1; intros x kk; simpl; try solve [eauto | fsetdec].
     destruct (x==a); subst; simpl; fsetdec.

     assert (J1:=@IHe1_1 x kk).
     assert (J2:=@IHe1_2 x kk).
     fsetdec.
    
     assert (J1:=@IHe1_1 x kk).
     assert (J2:=@IHe1_2 x kk).
     fsetdec.
Qed.

Lemma close_ee_fv_ee_eq' : forall e1 x,
  fv_ee (close_ee e1 x) [=] AtomSetImpl.diff (fv_ee e1) {{x}}.
Proof.
  intros. apply close_ee_rec_fv_ee_eq'.
Qed.

Lemma close_ec_rec_fv_ec_eq' : forall C1 x kk,
  fv_ec (close_ec_rec kk x C1) [=] AtomSetImpl.diff (fv_ec C1) {{x}}.
Proof.
  induction C1; intros x kk; simpl; try solve [eauto | fsetdec].
    assert (J:=@close_ee_rec_fv_ee_eq' e x kk).
    assert (J':=@IHC1 x kk).
    fsetdec.

    assert (J:=@close_ee_rec_fv_ee_eq' e x kk).
    assert (J':=@IHC1 x kk).
    fsetdec.

    assert (J:=@close_ee_rec_fv_ee_eq' e x kk).
    assert (J':=@IHC1 x kk).
    fsetdec.

    assert (J:=@close_ee_rec_fv_ee_eq' e x kk).
    assert (J':=@IHC1 x kk).
    fsetdec.
Qed.

Lemma close_ec_fv_ec_eq' : forall C1 x,
  fv_ec (close_ec C1 x) [=] AtomSetImpl.diff (fv_ec C1) {{x}}.
Proof.
  intros. apply close_ec_rec_fv_ec_eq'.
Qed.
