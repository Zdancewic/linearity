Require Export LinF_Soundness.
Require Export ALinearF_Soundness.
Require Import LinF_ExtraLemmas.
Fixpoint from_genv_to_env (G : genv) {struct G} : env :=
  match G with
  | nil => empty
  | h :: t => 
    match h with 
    | (A, gbind_kn K) => (A, bind_kn K) :: (from_genv_to_env t)
    | (A, gbind_typ T) => (A, bind_typ T) :: (from_genv_to_env t)
    end
  end.

Lemma dom_G_remain : forall G,
  dom G = dom (from_genv_to_env G).
Proof with eauto.
  intros G.
  induction G... 
   destruct a... 
    simpl. destruct g; rewrite IHG...
Qed.

Fixpoint from_denv_to_lenv (D : denv) {struct D} : lenv :=
  match D with 
  | nil => lempty 
  | h :: t =>
    match h with
    | (A, T) => (A, lbind_typ T) :: (from_denv_to_lenv t)
    end
  end.

Lemma dom_D_remain : forall D,
  dom D = dom (from_denv_to_lenv D).
Proof with eauto.
  intros D.
  induction D... 
   destruct a... 
    simpl. rewrite IHD...
Qed.

Fixpoint from_lenv_to_denv (D : lenv) {struct D} : denv :=
  match D with 
  | nil => dempty 
  | h :: t =>
    match h with
    | (A, m) => 
       match m with  
       | lbind_typ T => (A, T) :: (from_lenv_to_denv t)
       end
    end
  end.

Lemma dom_D_remain_2 : forall D,
  dom D = dom (from_lenv_to_denv D).
Proof with eauto.
  intros D.
  induction D... 
   destruct a... destruct l. 
    simpl. rewrite IHD...
Qed.

Lemma uniq_genv_sound : forall G,
  uniq G ->
  uniq (from_genv_to_env G).
Proof with eauto.
  intros G H.
  induction G; simpl...
   destruct a...
    inversion H; subst...
     apply IHG in H2. destruct g; simpl_env;  apply uniq_push; try( rewrite <- dom_G_remain)...
Qed.
Hint Resolve uniq_genv_sound.

Lemma uniq_lenv_compl : forall D,
  uniq D ->
  uniq (from_lenv_to_denv D).
Proof with eauto.
  intros D Uniq.
  induction D; simpl...
   destruct a. destruct l.
   apply uniq_cons.
    apply IHD. solve_uniq.
    inversion Uniq...
    rewrite <- dom_D_remain_2...
Qed.

Theorem binds_kn_sound : forall X K G,
  binds X (gbind_kn K) G ->
  binds X (bind_kn K) (from_genv_to_env G)
 .
Proof with eauto.
  intros X K G H. 
  induction G...
   destruct a...
    apply binds_cons_1 in H. inversion H; subst...
     destruct H0 as [H1 H2]; subst; simpl...
     apply IHG in H0. simpl. destruct g; apply binds_cons_3...
Qed.

Theorem binds_typ_sound : forall x T G,
  binds x (gbind_typ T) G ->
  binds x (bind_typ T) (from_genv_to_env G)
 .
Proof with eauto.
  intros x T G H. 
  induction G...
   destruct a...
    apply binds_cons_1 in H. inversion H; subst...
     destruct H0 as [H1 H2]; subst; simpl...
     apply IHG in H0. simpl. destruct g; apply binds_cons_3...
Qed.
   
  
Lemma wf_atyp_sound : forall G T K,
 wf_atyp G T K ->
 wf_typ (from_genv_to_env G) T K
 .
Proof with eauto.
 intros G T K H.
 (wf_atyp_cases (induction H) Case)...
 Case "wf_atyp_var".
  apply binds_kn_sound in H0.
  destruct K; destruct K'; subst; 
    try  (apply wf_typ)...
   inversion H1...
 Case "wf_atyp_arrow".
  destruct K; destruct K'; subst;
    try (apply wf_arrow)...
   inversion H1...
Qed.

Lemma wf_genv_sound : forall G,
 wf_genv G ->
 wf_env (from_genv_to_env G).
Proof with eauto.
 intros G H. 
 (wf_genv_cases (induction H) Case); simpl; simpl_env...
 Case "wf_genv_kn".
  rewrite dom_G_remain in H0.
  apply wf_env_kn...
 Case "wf_genv_typ".
  rewrite dom_G_remain in H1.
  apply wf_atyp_sound in H0.
  apply wf_env_typ...
Qed.
   
Theorem uvar_sound : forall x T G,
  wf_genv G ->
  binds x (gbind_typ T) G ->
  typing (from_genv_to_env G) lempty x T
 .
Proof with eauto.
  intros x T G Wfg Binds.
  apply binds_typ_sound in Binds...
  apply typing_var...
   apply wf_genv_sound...
Qed.

Lemma perm_length_eq : forall A,
  (forall (x y:(atom * A)%type), {x = y}+{~x = y})->
  forall (D1 D2:list (atom*A)),
  permute  D1 D2 ->
  length D1 = length D2.
Proof with eauto.
  intros. induction H... simpl in *...
  rewrite app_length in *. simpl. rewrite IHpermute...
Qed.

Lemma perm_dempty : forall D2 D1,
  uniq D2 ->
  permute D2 (D2 ++ D1) ->
  D1 = dempty.
Proof with eauto; try (inversion 2).
  intros D2 D1 Uniq Perm.
  destruct D1...
  apply perm_length_eq in Perm.
  rewrite app_length in Perm.  simpl in *.
  assert (length D2 + O < length D2 + S (length D1)).
   apply plus_le_lt_compat... apply lt_O_Sn. rewrite plus_0_r in H.
   rewrite <- Perm in H. assert (~ (length D2 < length D2)).
    apply lt_irrefl. apply H0 in H. 
    inversion H.
    decide equality. apply eq_typ_dec.
Qed.

Lemma card_eq_len : forall D,
  uniq D ->
  EMap.cardinal (<# D #>) = length D.
Proof with eauto.
  intros D Uniq.
  induction D...
  destruct a; simpl; simpl_env in *...
   assert (uniq D). solve_uniq.
   apply IHD in H.
   rewrite <- H. 
   apply cardinal_2 with (x := a) (e := t).
   inversion Uniq; subst...
   apply notin_dom_implies_notIn...
   unfold Add...
Qed.
   
Lemma remove_notin_equiv : forall D3 x D2,
  (<# D3 #> [-] x) ~~ <# D2 #> ->
  x `notin` dom D2.
Proof with eauto.
  intros D3 x D2 Eq.
  assert (~ EMap.In x (<# D3 #> [-] x)) as NotIn.
   apply dmap_remove_clear.
  apply notIn_implies_notin_dom in NotIn.
  assert ((<# D3 #> [-] x) ~~ <# <@(<# D3 #> [-] x)@> #>).
   apply denv_to_from_dmap.
  assert (<# <@(<# D3 #> [-] x)@> #> ~~ <# D2 #>).
   eapply Equal_trans.
    apply Equal_sym in H. eauto. auto.
  assert (x `notin` dom D2).
   eapply denv_Equal_notin_dom. eauto. auto. auto.
Qed.

Lemma conc_after_minus_eq : forall x T D3 D2,
  (<# D3 #> [-] x) ~~ <# D2 #> ->
  <#[(x, T)] ++ <@ <# D3 #> [-] x @> #> ~~ <#[(x, T)] ++ D2 #>
 .
Proof with eauto.
  intros x T D3 D2 H.
  apply denv_add_preserves_Equal...
   assert (<# D3 #> [-] x ~~ <# <@ <# D3 #> [-] x @> #> ).
    apply denv_to_from_dmap. 
   apply Equal_sym in H0.
   assert (<# <@ <# D3 #> [-] x @> #> ~~ <# D2 #>).
    eapply Equal_trans. eauto. auto. auto.
Qed.

Lemma conc_after_minus_eq_refl : forall D3 x T,
  binds x T D3 ->
  uniq D3 ->
  <# D3 #> ~~ <# [(x, T)] ++ <@<# D3 #> [-] x@> #>.
Proof with eauto.
  intros D3 x T Binds Uniq. 
   unfold EMap.Equal.
   intros y.
   destruct (x == y); subst... (*simpl in *...*)
    Case "x = y".
     simpl in *.
     assert (binds y T D3 <-> EMap.find y <# D3 #> = Some T) as BFIso.
      apply denv_to_dmap_iso... 
     inversion BFIso as [BTF FTB]. clear FTB. 
     apply BTF in Binds. clear BFIso BTF. rewrite Binds.

     assert (EMap.find (elt:=typ) y
      (y ::: T[+]<# EMap.Raw.remove (elt:=typ) y <# D3 #> #>) = Some T) as FAA.
      apply EMap.find_1. apply EMap.add_1...
     rewrite FAA...
    Case "x <> y".
     remember (EMap.find (elt:=typ) y <# D3 #>) as e.
     destruct e.
     SCase "Some t".
     assert ( EMap.MapsTo y t
      ( EMap.add x T <# <@ <# D3 #>[-]x @> #>)).
      apply EMap.add_2...
      assert (EMap.MapsTo y t <# D3 #>).
       apply EMap.find_2. apply sym_eq...
      apply (EMap.remove_2 n) in H. 
      assert ((<# D3 #>[-]x) ~~  <# <@ <# D3 #>[-]x @> #>) as Tr.
       apply denv_to_from_dmap. 
      unfold EMap.Equal in Tr.
      apply EMap.find_1 in H.
      assert (       EMap.find (elt:=typ) y (<# D3 #>[-]x) =
       EMap.find (elt:=typ) y <# <@ <# D3 #>[-]x @> #>) as TrY...
      rewrite H in TrY. apply sym_eq in TrY.
      apply EMap.find_2...
      apply sym_eq.
      apply EMap.find_1...
     SCase "None".
      remember (EMap.find (elt:=typ) y <# [(x, T)] ++ <@ <# D3 #>[-]x @> #>) as e.
      destruct e...
      SSCase "Some t".
       assert (<# [(x, T)] ++ <@ <# D3 #>[-]x @> #>=(x:::T [+] <# <@ <# D3 #>[-]x @> #>)) as EQ...
       rewrite EQ in Heqe0. clear EQ.
       apply sym_eq in Heqe0.
       apply EMap.find_2 in Heqe0.
       apply (EMap.add_3 n) in Heqe0. 

       assert (EMap.MapsTo y t (<# D3 #> [-] x)) as TAR.
        assert ((<# D3 #>[-]x) ~~ <# <@ <# D3 #>[-]x @> #>) as Tr.
         apply denv_to_from_dmap.
        assert (       EMap.find (elt:=typ) y (<# D3 #>[-]x) =
        EMap.find (elt:=typ) y <# <@ <# D3 #>[-]x @> #>) as TrY...
        apply EMap.find_1 in Heqe0.
        rewrite <- TrY in Heqe0. clear Tr TrY.
        apply EMap.find_2...
       apply EMap.remove_3 in TAR. apply EMap.find_1 in TAR.
       rewrite TAR in Heqe. inversion Heqe.
Qed.

Lemma lvar_case_lemma1 : forall D3 x T D2,
  uniq D3 ->
  binds x T D3 ->
  uniq D2 ->
  (<# D3 #> [-] x) ~~ <# D2 #> ->
  <# D3 #> ~~ <# D2 ++ [(x, T)] #>
 .   
Proof with eauto.
  intros D3 x T D2 UD3 Binds UD2 Eq.
  assert (x `notin` dom D2) as notinD2.
   eapply remove_notin_equiv. eauto.

  assert (<#[(x, T)] ++ <@ <# D3 #> [-] x @> #> ~~ <#[(x, T)] ++ D2 #>) as HMid.
   apply conc_after_minus_eq...

  assert (<# D3 #> ~~ <# [(x, T)] ++ <@<# D3 #> [-] x@> #>) as HD3.
   apply conc_after_minus_eq_refl...

  eapply Equal_trans.
   eauto.
  eapply Equal_trans.
   eauto.
  apply disjoint_denv_cons_commut.
   solve_uniq.
Qed.
   
Lemma perm_uniq_implies_eq : forall D1 D2,
  permute D1 D2 ->
  uniq D1 ->
  D1 ~~~ D2.
Proof with eauto.
  intros D1 D2 Perm Uniq.
  induction Perm...
  Case "empty".
   rewrite_env (dempty ++ dempty ++ dempty).
   apply disjoint_denv_cons_3commut_aux...
  Case "cons". 
   assert ([(x, b)] ++ D ~~~ [(x, b)] ++ DL ++ DR) as H.
    apply denv_add_preserves_Equal...
     apply IHPerm... inversion Uniq...
   assert (uniq ([(x, b)] ++ DL)) as UniqDL.
    assert (uniq D) as UniqD. inversion Uniq...
    assert (uniq (DL ++ DR)) as H1.
      apply uniq_env_permute with D...
    assert (uniq DL) as H2.
      solve_uniq.
    assert (x `notin` dom D).
      solve_uniq.
    assert (x `notin` dom D <-> x `notin` dom (DL ++ DR)).
      apply IHPerm in UniqD. apply denv_equal_notin_dom_iff...
    inversion H3 as [H4 H5]. clear H3 H5.
     apply H4 in H0. simpl_env in H0.
     assert (x `notin` dom DL). fsetdec.
     solve_uniq.
   assert ([(x, b)] ++ DL ~~~ DL ++ [(x, b)]) as H1.
    rewrite_env ([(x, b)] ++ DL ++ dempty).
    rewrite_env (dempty ++ DL ++ [(x, b)]).
    apply disjoint_denv_cons_3commut_aux...
     simpl_env...
   assert ([(x, b)] ++ DL ++ DR ~~~ DL ++ [(x, b)] ++ DR).
    rewrite_env (dempty ++ [(x, b)] ++ dempty ++ DL ++ DR).
    rewrite_env (dempty ++ DL ++ dempty ++ [(x, b)] ++ DR).
    apply disjoint_denv_cons_commut_aux. 
     simpl_env.
     assert (uniq D). inversion Uniq...
     assert (uniq (DL ++ DR)).
      apply uniq_env_permute with D...
     assert (x `notin` dom D). inversion Uniq...
     assert (x `notin` dom D <-> x `notin` dom (DL ++ DR)).
      apply IHPerm in H0.
      apply denv_equal_notin_dom_iff...
     inversion H4. apply H5 in H3.
     solve_uniq.
   eapply Equal_trans. eauto. auto.
Qed.

Lemma eq_uniq_implies_perm : forall D1 D2,
  <# D1 #> ~~ <# D2 #> ->
  uniq D1 ->
  uniq D2 ->
  permute D1 D2.
Proof with eauto.
  intros D1 D2 EQ Uniq1 Uniq2.
  generalize dependent D2.
  induction D1; intros D2 EQ Uniq2...
  Case "empty". 
   simpl in *...
   apply dmap_eq_empty_inv in EQ.
   apply denv_eq_empty_inv in EQ.
   subst. apply permute_empty.
  Case "cons".
   destruct a as [x T]. simpl_env in *.
   assert (forall x0 T0, binds x0 T0 ([(x, T)] ++ D1) <-> binds x0 T0 D2) as H.
    apply dmap_eq__binds_iff...
   assert (binds x T ([(x, T)] ++ D1) <-> binds x T D2) as H1...
   inversion H1 as [H2 H3]. clear H H1 H3.
   assert (binds x T ([(x, T)] ++ D1)) as H4...
   apply H2 in H4.
   apply binds_inv in H4. inversion H4 as [E1 [E2 H]]; subst. clear H4.
   apply permute_cons.
   apply IHD1...
    inversion Uniq1...
   assert ( (dempty ++ dempty ++ E2 ++ [(x, T)] ++ E1) ~~~
      (dempty ++ [(x, T)] ++ E2 ++ dempty ++ E1)) as H.
    apply disjoint_denv_cons_commut_aux. simpl_env...
   simpl_env in *. 
   unfold denv_Equal in H.
   assert (<# [(x, T)] ++ D1 #> ~~ <# [(x, T)] ++ E2 ++ E1 #>) as H1.
   eapply Equal_trans. eauto.  auto.
   assert (uniq ([(x, T)] ++ E2 ++ E1)) as H3.
    solve_uniq.
   clear H H2 EQ Uniq2.
   unfold EMap.Equal in *.
   assert (x `notin` dom D1).
    inversion Uniq1; subst...
   assert (x `notin` dom (E2 ++ E1)).
    inversion H3; subst...
   intros y.
   destruct (y == x); subst...
    SCase "y = x".
     apply notin_dom_implies_notIn in H.
     apply notin_dom_implies_notIn in H0.
     apply not_find_in_iff in H. rewrite H. 
     apply not_find_in_iff in H0. rewrite H0...
    SCase "y <> x".
     assert ( EMap.find (elt:=typ) y <# [(x, T)] ++ D1 #> =
       EMap.find (elt:=typ) y <# [(x, T)] ++ E2 ++ E1 #>) as HF...
      simpl in HF.
      assert (EMap.find (elt:=typ) y (x ::: T[+]<# D1 #>) =
        EMap.find (elt:=typ) y (<# D1 #>)) as HA1.
       apply add_neq_o... rewrite <- HA1.
      assert (EMap.find (elt:=typ) y (x ::: T[+]<# E2 ++ E1 #>) =
        EMap.find (elt:=typ) y <# E2 ++ E1 #>) as HA2.
       apply add_neq_o... rewrite <- HA2...
Qed.

  
Lemma lvar_case_lemma2 : forall D3 D2 D1 x T,
  permute D3 (D2 ++ D1) ->
  <# D3 #> ~~ <# D2 ++ [(x, T)] #> ->
  uniq D3 ->
  uniq (D2 ++ [(x, T)]) ->
  x `notin` dom D2 ->
  binds x T D3 ->
  D1 = [(x, T)].
Proof with eauto.
  intros D3 D2 D1 x T Perm Eq Uniq3 Uniq2 NotIn Binds.
  assert (x `in` dom D3) as H3.
   apply binds_In with T... 
  assert (D3 ~~~ D2 ++ D1) as Eq2.
   apply perm_uniq_implies_eq...
  assert (x `in` dom D3 <-> x `in` dom (D2 ++ D1)) as H.
   apply denv_equal_in_dom_iff... 
  inversion H as [H1 H2]. clear H H2.
  apply H1 in H3.
  assert (x `in` dom D1) as InD1.
   simpl_env in H3. fsetdec.
  assert (binds x T (D2 ++ D1)).
   apply binds_permutation with D3...
   apply uniq_env_permute with D3...
   assert (binds x T D2 \/ binds x T D1) as Bindsx.
    apply binds_app_1...
   inversion Bindsx. apply binds_In in H0. fsetdec.
  
  assert (permute D3 (D2 ++ [(x, T)])) as Perm2.
   apply eq_uniq_implies_perm...
  
  apply perm_length_eq in Perm. 
  apply perm_length_eq in Perm2.
  rewrite Perm in Perm2.
  rewrite app_length in Perm2. rewrite app_length in Perm2.
  apply plus_reg_l in Perm2. simpl in *.
  
  destruct D1; simpl in Perm2; inversion Perm2...
   destruct p. destruct D1; simpl in H4; inversion H4...
   simpl_env in *.
   assert (x = a).
    eapply binds_one_1... subst.
   apply binds_one_2 in H0; subst...
  
  intros x0 y. decide equality.
  remember (beq_typ b t) as e.
  destruct e.
   apply sym_eq in Heqe.
   apply beq_typ_iff_eq in Heqe; subst...
   right. unfold not. intros contra.
    apply beq_typ_iff_eq in contra. rewrite contra in Heqe. inversion Heqe.

 intros x0 y. decide equality.
  remember (beq_typ b t) as e.
  destruct e.
   apply sym_eq in Heqe.
   apply beq_typ_iff_eq in Heqe; subst...
   right. unfold not. intros contra.
    apply beq_typ_iff_eq in contra. rewrite contra in Heqe. inversion Heqe.
Qed.

Lemma perm_trans : forall (D1 D2 D3 : denv),
 uniq D1 ->
 uniq D2 ->
 permute D1 D2 ->
 permute D2 D3 ->
 permute D1 D3.
Proof with eauto.
  intros.
  assert (D1 ~~~ D2) as Eq1.
   apply perm_uniq_implies_eq...
  assert (D2 ~~~ D3) as Eq2.
   apply perm_uniq_implies_eq...
  assert (D1 ~~~ D3) as Eq3.
   eapply Equal_trans.
    eauto. auto.
  assert (uniq D3).
   apply uniq_env_permute with D2...
  apply eq_uniq_implies_perm...
Qed.

Lemma eq_uniq_perm_dempty : forall D1 D2 D3,
  D3 ~~~ D2 ->
  uniq D3 ->
  uniq D2 ->
  permute D3 (D2 ++ D1) ->
  D1 = dempty.
Proof with eauto.
 intros D1 D2 D3 EQ Uniq3 Uniq2 Perm.
 apply Equal_sym in EQ.
 assert (permute D2 D3) as Perm2.
  apply eq_uniq_implies_perm...
 assert (permute D2 (D2 ++ D1)).
  eapply perm_trans.
   auto. apply Uniq3. auto. auto.
 apply perm_dempty  with D2...
Qed.

Lemma denv_conc_preserves_Equal_1 : forall D D' D1 : denv,
  D ~~~ D' ->
  D1 ++ D ~~~ D1 ++ D'.
Proof with eauto.
  intros D D' D1 EQ.
  induction D1...
  destruct a. simpl_env.
   apply denv_add_preserves_Equal...
Qed.
   
Lemma denv_conc_preserves_Equal_2 : forall D D' D1 : denv,
  D ~~~ D' ->
  uniq (D ++ D1) ->
  uniq (D' ++ D1) ->
  D ++ D1 ~~~ D' ++ D1.
Proof with eauto.
  intros D D' D1 Uniq1 Uniq2 EQ.
  assert (D1 ++ D ~~~ D1 ++ D') as H.
   apply denv_conc_preserves_Equal_1...
  assert (D ++ dempty ++ D1 ~~~ D1 ++ dempty ++ D) as H1.
   apply disjoint_denv_cons_3commut_aux...
  assert (D' ++ dempty ++ D1 ~~~ D1 ++ dempty ++ D') as H2.
   apply disjoint_denv_cons_3commut_aux...
  simpl_env in *.
  eapply Equal_trans. 
   eauto. 
  eapply Equal_trans.
   eauto.
  apply Equal_sym...
Qed.

Lemma perm_subst_1 : forall D1 D2 D3 D4 : denv,
  uniq D1 ->
  permute D1 (D2 ++ D3) ->
  permute D2 D4 ->
  permute D1 (D4 ++ D3).
Proof with eauto.
  intros D1 D2 D3 D4 Uniq Perm1 Perm2.
  assert (uniq (D2 ++ D3)) as H1.
   apply uniq_env_permute with D1...
  assert (uniq D2) as Uniq2.
   apply uniq_app_1 with D3...
  assert (uniq D3) as Uniq3.
   apply uniq_app_2 with D2...
  assert (uniq D4) as Uniq4.
   apply uniq_env_permute with D2...
  assert (D1 ~~~ D2 ++ D3) as Eq1.
   apply perm_uniq_implies_eq...
  assert (D2 ~~~ D4) as Eq2.
   apply perm_uniq_implies_eq...
  assert (uniq (D4 ++ D3)) as Uniq43.
   apply uniq_app_iff in H1. destruct H1 as [H2 [H3 H4]].
    assert (disjoint D4 D3) as Disj.
     apply dmap_denv_disjoint.
      eapply dmap_Equal_preserves_disjoint_left.
       apply denv_dmap_disjoint in H4...
       apply Equal_sym...
      apply uniq_app_4...
  assert (D2 ++ D3 ~~~ D4 ++ D3) as Eq3.
   apply denv_conc_preserves_Equal_2...
   
  assert (D1 ~~~ D4 ++ D3) as Eq4.
   eapply Equal_trans.
    eauto. auto.
  apply eq_uniq_implies_perm...
Qed.

Lemma perm_subst_2 : forall D1 D2 D3 D4 : denv,
  uniq D1 ->
  permute D1 (D2 ++ D3) ->
  permute D3 D4 ->
  permute D1 (D2 ++ D4).
Proof with eauto.
  intros D1 D2 D3 D4 Uniq Perm1 Perm2.
  generalize dependent D1. 
  generalize dependent D2.
  induction Perm2; intros; simpl_env in *...
   assert (permute D1 ((D2 ++ [(x, b)]) ++ DL ++ DR)) as Perm3.
    apply IHPerm2... simpl_env...
   rewrite_env (D2 ++ [(x, b)] ++ dempty ++  DL ++ DR) in Perm3.
   assert (D1 ~~~ D2 ++ [(x, b)] ++ dempty ++  DL ++ DR) as H1.
    apply perm_uniq_implies_eq... 
   assert (D2 ++ [(x, b)] ++ dempty ++  DL ++ DR ~~~ D2 ++ DL ++ dempty ++ [(x, b)] ++ DR) as H2.
    apply disjoint_denv_cons_commut_aux.
     apply uniq_env_permute with D1...
   assert (D1 ~~~ D2 ++ DL ++ dempty ++ [(x, b)] ++ DR) as H3.
     eapply Equal_trans. eauto. auto.
   apply eq_uniq_implies_perm...
    simpl_env in *. 
    assert (uniq (D2 ++ [(x, b)] ++ DL ++ DR)) as H4.
     apply uniq_env_permute with D1...
    solve_uniq.
Qed.

Lemma perm_strengthening_head : forall (D1 D2 : denv) x T,
  uniq ([(x, T)] ++ D1) ->
  permute ([(x, T)] ++ D1) ([(x, T)] ++ D2) ->
  permute D1 D2. 
Proof with eauto.
  intros D1 D2 x T Uniq Perm.
  remember ([(x, T)] ++ D1) as e1.
  remember ([(x, T)] ++ D2) as e2.
  generalize dependent D1.
  generalize dependent D2.
  generalize dependent x.
  generalize dependent T.
  induction Perm; intros; subst...
   inversion Heqe1.
   inversion Heqe1; subst...
    destruct DL; simpl_env in *.
      inversion Heqe2; subst...
      destruct p. inversion Heqe2; subst...
       assert (x0 `notin` dom D1) as Notin.
        inversion Uniq...
       assert (dom D1 [=] dom ([(x0, T)] ++ DL ++ DR)) as Domeq.
        apply dom_permute... rewrite Domeq in Notin. 
        simpl_env in Notin. fsetdec.
Qed.
        
Lemma perm_strengthening_1 : forall D1 D2 D3 : denv,
  uniq (D1 ++ D2) ->
  permute (D1 ++ D2) (D1 ++ D3) ->
  permute D2 D3.
Proof with eauto.
  intros D1 D2 D3 Uniq Perm.
  assert (uniq (D1 ++ D3)) as H1.
   apply uniq_env_permute with (D1 ++ D2)...
  assert (uniq D1) as Uniq1.
   apply uniq_app_1 with D2...
  induction D1...
   destruct a in *. simpl_env in *.
   apply IHD1...
    inversion Uniq...
    eapply perm_strengthening_head.
     eauto. auto.
     inversion H1...
     inversion Uniq1...
Qed.

Lemma lenv_to_denv : forall D1 D2,
  D1 = from_denv_to_lenv D2 ->
  D2 = from_lenv_to_denv D1.
Proof with eauto.
  intros D1 D2 EQ.
  generalize dependent D1.
  induction D2; intros; subst...
   destruct a.
   simpl in *.
   assert (D2 = from_lenv_to_denv (from_denv_to_lenv D2)).
    apply IHD2... rewrite <- H...
Qed.

Lemma lenv_refl : forall D,
  D = from_denv_to_lenv (from_lenv_to_denv D).
Proof with eauto.
  intros D.
  induction D...
   destruct a. destruct l. simpl. rewrite <- IHD...
Qed.

Lemma denv_to_lenv_conc : forall D1 D2,
  from_denv_to_lenv (D1 ++ D2) = from_denv_to_lenv D1 ++ from_denv_to_lenv D2.
Proof with eauto.
  intros D1 D2.
  induction D1...
   destruct a. simpl in *. rewrite IHD1...
Qed.

Lemma lenv_to_denv_conc : forall D1 D2,
  from_lenv_to_denv (D1 ++ D2) = from_lenv_to_denv D1 ++ from_lenv_to_denv D2.
Proof with eauto.
  intros D1 D2.
  induction D1...
   destruct a. destruct l. simpl in *. rewrite IHD1...
Qed.

Lemma lempty_implies_lempty : forall D1 D2,
 lempty = D1 ++ D2 ->
 D1 = lempty /\ D2 = lempty.
Proof with eauto.
  intros. destruct D1; destruct D2...
  inversion H... inversion H.
Qed.

Lemma perm_denv_to_lenv : forall D1 D2,
  permute (from_denv_to_lenv D1) (from_denv_to_lenv D2) ->
  permute D1 D2.
Proof with eauto.
  intros D1 D2 H.
  remember (from_denv_to_lenv D1) as e1.
  remember (from_denv_to_lenv D2) as e2.
  generalize dependent D1.
  generalize dependent D2.
  induction H; intros; subst.
   destruct D2; destruct D1; simpl_env in *; subst;
    try (apply permute_empty);
    try (destruct p; simpl in *; inversion Heqe1);
    try (inversion Heqe2).
    destruct D1.
     simpl in Heqe1. inversion Heqe1.
     destruct p. simpl in Heqe1. inversion Heqe1; subst.
      apply lenv_to_denv in Heqe2.
      rewrite Heqe2.
    assert (permute D1 (from_lenv_to_denv  (DL ++ DR))) as HP.
     apply IHpermute...
      apply lenv_refl.
      rewrite lenv_to_denv_conc in *.
      rewrite lenv_to_denv_conc. simpl. simpl_env.
      apply permute_cons...
Qed.

Lemma denv_to_lenv : forall D1 D2,
  D1 = from_lenv_to_denv D2 ->
  D2 = from_denv_to_lenv D1.
Proof with eauto.
  intros.
  subst. apply lenv_refl.
Qed.

Lemma denv_refl : forall D,
  D = (from_lenv_to_denv (from_denv_to_lenv D)).
Proof with eauto.
  intros. apply lenv_to_denv...
Qed.

Lemma perm_lenv_to_denv : forall D1 D2,
  permute (from_lenv_to_denv D1) (from_lenv_to_denv D2) ->
  permute D1 D2.
Proof with eauto.
  intros D1 D2 H.
  remember (from_lenv_to_denv D1) as e1.
  remember (from_lenv_to_denv D2) as e2.
  generalize dependent D1.
  generalize dependent D2.
  induction H; intros; subst.
 destruct D2; destruct D1; simpl_env in *; subst;
    try (apply permute_empty);
    try (destruct p; destruct l; simpl in *; inversion Heqe1);
    try (inversion Heqe2).
    destruct D1.
     simpl in Heqe1. inversion Heqe1.
     destruct p. destruct l in *. simpl in *. inversion Heqe1; subst.
      apply denv_to_lenv in Heqe2.
      rewrite Heqe2.
    assert (permute D1 (from_denv_to_lenv  (DL ++ DR))) as HP.
     apply IHpermute...
      apply denv_refl.
      rewrite denv_to_lenv_conc in *. simpl_env.
      rewrite denv_to_lenv_conc. simpl. simpl_env.
      apply permute_cons...
Qed.

Lemma perm_lenv_to_denv_2 : forall D1 D2,
  permute D1 D2 ->
  permute (from_lenv_to_denv D1) (from_lenv_to_denv D2).
Proof with eauto.
  intros D1 D2 Perm.
  induction Perm...
   simpl. apply permute_empty.
   destruct b. simpl. simpl_env.
   rewrite lenv_to_denv_conc. rewrite lenv_to_denv_conc. simpl. simpl_env.
   apply permute_cons... rewrite <- lenv_to_denv_conc...
Qed.

Lemma perm_denv_to_lenv_2 : forall D1 D2, 
  permute D1 D2 ->
  permute (from_denv_to_lenv D1) (from_denv_to_lenv D2). 
Proof with eauto.
  intros D1 D2 Perm.
  generalize dependent D2.
  induction D1; intros...
   inversion Perm; simpl; subst...
    apply permute_empty.
   inversion Perm; simpl; subst...
   assert (permute (from_denv_to_lenv D1) (from_denv_to_lenv (DL ++ DR))).
    apply IHD1...
   rewrite denv_to_lenv_conc. simpl. simpl_env.
   apply permute_cons...
    rewrite <- denv_to_lenv_conc.
    apply IHD1...
Qed.

Lemma perm_to_lenv_split : forall G D1 D2 D3,
  wf_lenv G D1 ->
  permute D1 (D2 ++ D3) ->
  exists D22, 
    exists D33,
      permute D2 D22 /\
      permute D3 D33 /\
      lenv_split G D22 D33 D1.
Proof with eauto.
  intros G D1 D2 D3 Wflenv Perm.
  remember D1 as e1.
  remember (D2 ++ D3) as e2.
  generalize dependent D1.
  generalize dependent D2.
  generalize dependent D3.
  induction Perm; intros; subst...
   exists (lempty). exists (lempty).
   apply lempty_implies_lempty in Heqe2.
   destruct Heqe2; subst...
   repeat split...
    apply permute_empty.
    apply permute_empty.
   
   assert (  
   (exists F1, D2 = DL ++ [(x, b)] ++ F1 /\ DR = F1 ++ D3) \/
   (exists F2, DL = D2 ++ F2 /\ D3 = F2 ++ [(x, b)] ++ DR)) as Mid.
    apply uniq_eq_mid... 
     apply eq_lbinding_dec.
     assert (permute ([(x, b)] ++ D) (DL ++ [(x, b)] ++ DR)) as Perm2.
      apply permute_cons...
     apply uniq_env_permute with ([(x, b)] ++ D).
      apply uniq_from_wf_lenv with G...
     auto.
   
   destruct Mid.
    destruct H as [F1 [EQD2 EQD3]].
    assert (exists D21, 
             exists D31,
               permute (DL ++ F1) D21 /\ permute D3 D31 /\ lenv_split G D21 D31 D) as HP.
     apply IHPerm with D...
      inversion Wflenv...
      subst...
    destruct HP as [D21 [D31 [Perm2 [Perm3 Lsplit]]]].
    subst.
    exists ([(x, b)] ++ D21).
     exists D31.
     repeat split.
      assert (uniq ([(x, b)] ++ D)) as Uniq.
       apply uniq_from_wf_lenv with G...
      apply permute_sym...
       apply eq_lbinding_dec.
       assert (permute (lempty ++ [(x, b)] ++ D) (lempty ++ [(x, b)] ++ DL ++ F1 ++ D3)).
        apply permute_weakening. apply eq_lbinding_dec.
         simpl_env... simpl_env...
       simpl_env in H. 
       assert (uniq ([(x, b)] ++ DL ++ F1 ++ D3)) as Uniq2.
        eapply uniq_env_permute. apply Uniq. auto.
       assert (uniq ([(x, b)] ++ DL ++ F1)) as Uniq3.
        apply uniq_app_1 with D3... simpl_env...
       assert (permute (lempty ++ [(x, b)] ++ DL ++ F1) (lempty ++ [(x, b)] ++ D21)) as Perm4.
        apply permute_weakening. apply eq_lbinding_dec.
         simpl_env... simpl_env...
       simpl_env in Perm4.
       apply uniq_env_permute with ([(x, b)] ++ DL ++ F1)...
      apply permute_cons. 
       apply permute_sym. apply eq_lbinding_dec.
        assert (uniq (DL ++ F1 ++ D3)) as Uniq2.
         apply uniq_env_permute with D...
        apply uniq_app_1 with D3. simpl_env... auto. auto.

      destruct b.
      apply lenv_split_left...
       inversion Wflenv...
       inversion Wflenv...
       inversion Wflenv...


   destruct H as [F2 [EQD2 EQD3]].
    assert (exists D21, 
             exists D31,
               permute D2 D21 /\ permute (F2 ++ DR) D31 /\ lenv_split G D21 D31 D) as HP.
     apply IHPerm with D...
      inversion Wflenv...
      subst...
    destruct HP as [D21 [D31 [Perm2 [Perm3 Lsplit]]]].
    subst.
    exists D21.
     exists ([(x, b)] ++ D31).
     repeat split.
      auto.
      assert (uniq ([(x, b)] ++ D)) as Uniq.
       apply uniq_from_wf_lenv with G...
      assert (uniq D) as Uniq2.
        inversion Uniq...
      apply permute_sym.
       apply eq_lbinding_dec.
       simpl_env in Perm.
       assert (uniq (D2 ++ F2 ++ DR)) as Uniq3.
        apply uniq_env_permute with D...
       assert (uniq (F2 ++ DR)) as Uniq4.
        apply uniq_app_2 with D2...
       assert (uniq D31) as Uniq5.
        apply uniq_env_permute with (F2 ++ DR)...
       destruct b. simpl.
       apply uniq_cons...
        assert (dom (F2 ++ DR) [=] dom D31) as Dom1.
         apply dom_permute...
        assert (dom D [=] dom (D2 ++ F2 ++ DR)) as Dom2.
         apply dom_permute...
        assert (x `notin` dom D).
         inversion Wflenv...
        simpl_env in *. fsetdec.
        
       assert (permute D31 (F2 ++ DR)) as Perm4.
        apply permute_sym. apply eq_lbinding_dec.
         assert (uniq (D2 ++ F2 ++ DR)) as Uniq3.
          simpl_env in Perm. apply uniq_env_permute with D...
         apply uniq_app_2 in Uniq3...
       auto.
       apply permute_cons...

      destruct b.
      apply lenv_split_right...
       inversion Wflenv...
       inversion Wflenv...
       inversion Wflenv...  
Qed.

Lemma wf_lenv_env_permute : forall G D1 D2,
  wf_lenv G D1 ->
  permute D1 D2 ->
  wf_lenv G D2.
Proof with eauto.
  intros G D1 D2 Wflenv Perm.
  generalize dependent G.
  induction Perm; intros...
   assert (wf_lenv G (DL ++ DR)).
    apply IHPerm. rewrite_env ([(x, b)] ++ D ++ lempty) in Wflenv. 
     eapply wf_lenv_lin_strengthening. eauto.
   destruct b. apply wf_lenv_lin_weakening...
    inversion Wflenv... inversion Wflenv... 
    apply dom_permute in Perm. rewrite <- Perm.
    inversion Wflenv...
Qed.

Lemma permute_union : forall D0 D1 D2 D3 D21 D32 : denv,
  uniq D1 ->
  permute D1 (D3 ++ D0) ->
  permute D1 (D2 ++ D21) ->
  permute D2 (D3 ++ D32) ->
  permute D0 (D32 ++ D21).
Proof with eauto.
  intros D0 D1 D2 D3 D21 D32 Uniq Perm1 Perm2 Perm3.
  assert (permute D1 ((D3 ++ D32) ++ D21)) as Perm4.
   apply perm_subst_1 with D2...
  simpl_env in *.
  assert (permute (D3 ++ D0) D1) as Perm5.
   apply permute_sym.
    intros x0 y. decide equality.
    remember (beq_typ b t) as e.
    destruct e.
    apply sym_eq in Heqe.
    apply beq_typ_iff_eq in Heqe; subst...
    right. unfold not. intros contra.
    apply beq_typ_iff_eq in contra. rewrite contra in Heqe. inversion Heqe.
    auto. auto.
  assert (permute (D3 ++ D0) (D3 ++ D32 ++ D21)) as Perm6.
   eapply perm_trans. 
    apply uniq_env_permute with D1... eauto.
    auto. auto.
    
  apply perm_strengthening_1 with D3...
   apply uniq_env_permute with D1...
Qed.

Lemma app_case_lemma : forall G D0 D1 D2 D3 D32 D21,
  wf_lenv G D1 ->
  permute D1 (D3 ++ D0) ->
  permute D1 (D2 ++ D21) ->
  permute D2 (D3 ++ D32) ->
  exists D11, exists D12,
    permute D1 (D2 ++ D11) /\
    permute D2 (D3 ++ D12) /\
    lenv_split G D12 D11 D0.
Proof with eauto.
  intros G D0 D1 D2 D3 D32 D21 Wflenv Perm1 Perm2 Perm3.
  assert (permute (from_lenv_to_denv D0) (from_lenv_to_denv D32 ++ from_lenv_to_denv D21)) as PermD0.
   apply permute_union with  (from_lenv_to_denv D1) (from_lenv_to_denv D2) (from_lenv_to_denv D3).
    assert (uniq D1). 
     apply uniq_from_wf_lenv with G...
      apply uniq_lenv_compl...
   rewrite <- lenv_to_denv_conc.
   apply perm_lenv_to_denv_2...
   rewrite <-lenv_to_denv_conc.
   apply perm_lenv_to_denv_2...
    rewrite <-lenv_to_denv_conc.
   apply perm_lenv_to_denv_2...
   rewrite <- lenv_to_denv_conc in PermD0.
   apply perm_lenv_to_denv in PermD0.
   assert (exists D22, 
            exists D33,
              permute D32 D22 /\
              permute D21 D33 /\
              lenv_split G D22 D33 D0) as HE.
     apply perm_to_lenv_split...
      assert (wf_lenv G (D3 ++ D0)) as Wf2.
       apply wf_lenv_env_permute with D1...
      rewrite_env (D3 ++ D0 ++ lempty) in Wf2.
       eapply wf_lenv_lin_strengthening. eauto.
  destruct HE as [D22 [D33 [Perm4 [Perm5 LSplit]]]].
  exists D33. exists D22.
  repeat split...
   assert (permute (from_lenv_to_denv D1) (from_lenv_to_denv D2 ++ from_lenv_to_denv D33)) as Perm6.
    apply perm_subst_2 with (from_lenv_to_denv D21).
     apply uniq_lenv_compl. apply uniq_from_wf_lenv with G...
     rewrite <- lenv_to_denv_conc.
     apply perm_lenv_to_denv_2...
     apply perm_lenv_to_denv_2...
   rewrite <- lenv_to_denv_conc in Perm6.
    apply perm_lenv_to_denv...
   assert (permute (from_lenv_to_denv D2) (from_lenv_to_denv D3 ++ from_lenv_to_denv D22)) as Perm6.
    apply perm_subst_2 with (from_lenv_to_denv D32).
     apply uniq_lenv_compl. apply uniq_from_wf_lenv with G...
      assert (wf_lenv G (D2 ++ D21)) as Wf1.
       apply wf_lenv_env_permute with D1...
      rewrite_env (lempty ++ D2 ++ D21) in Wf1.
      eapply wf_lenv_lin_strengthening. eauto.
     rewrite <- lenv_to_denv_conc.
     apply perm_lenv_to_denv_2...
     apply perm_lenv_to_denv_2...
   rewrite <- lenv_to_denv_conc in Perm6.
    apply perm_lenv_to_denv...
Qed.

Lemma dempty_implies_dempty : forall D1 D2,
 dempty = D1 ++ D2 ->
 D1 = dempty /\ D2 = dempty.
Proof with eauto.
  intros. destruct D1; destruct D2...
  inversion H... inversion H.
Qed.

Lemma perm_comm_right : forall D1 D2 D3 : denv,
  uniq D1 ->
  permute D1 (D2 ++ D3) ->
  permute D1 (D3 ++ D2).
Proof with eauto.
  intros D1 D2 D3 Uniq Perm.
  remember (D2 ++ D3) as e.
  remember D1 as e'.
  generalize dependent D2.
  generalize dependent D3.
  generalize dependent D1.
  induction Perm; intros; subst...
   apply dempty_implies_dempty in Heqe.
    destruct Heqe; subst... simpl_env. apply permute_empty.
   
   assert (  
   (exists F1, D2 = DL ++ [(x, b)] ++ F1 /\ DR = F1 ++ D3) \/
   (exists F2, DL = D2 ++ F2 /\ D3 = F2 ++ [(x, b)] ++ DR)) as Mid.
    apply uniq_eq_mid... 
  intros x0 y. decide equality.
  remember (beq_typ b0 t) as e.
  destruct e.
   apply sym_eq in Heqe0.
   apply beq_typ_iff_eq in Heqe0; subst...
   right. unfold not. intros contra.
    apply beq_typ_iff_eq in contra. rewrite contra in Heqe0. inversion Heqe0.
  assert (x `notin` dom D). inversion Uniq...
    assert (dom D [=] dom (DL ++ DR)).
      apply dom_permute...
    rewrite H0 in H. simpl_env in *.
  apply uniq_insert_mid.
   apply uniq_env_permute with D. inversion Uniq... auto.
   fsetdec. fsetdec.

  destruct Mid.
   destruct H as [F1 [EQ1 EQ2]].
    subst.
    assert (permute D (D3 ++ DL ++ F1)) as Perm1.
     apply IHPerm with D... inversion Uniq...
     rewrite_env ((D3 ++ DL) ++ [(x, b)] ++ F1).
     rewrite_env ((D3 ++ DL) ++ F1) in Perm1.
     apply permute_cons...
   destruct H as [F2 [EQ1 EQ2]].
    subst. simpl_env in *.
    assert (permute D ( (F2 ++ DR) ++ D2)) as Perm1.
     apply IHPerm with D... inversion Uniq...
     rewrite_env ((F2 ++ DR ++ D2)) in Perm1.
     apply permute_cons...
Qed.

Lemma atyping_denv_ex_eq : forall G D1 e T D2,
  atyping G D1 e T D2 ->
  exists D, permute D1 (D2 ++ D).
Proof with eauto.
  intros G D1 e T D2 ATyping.
  remember (<# D2 #>) as e2.
  remember (<# D1 #>) as e1.
  assert (e2 <<= e1) as Mono.
   subst. eapply denv_mono. eauto.

  assert (((e1 -- e2) |_| e2) ~~ e1) as Eq.
   apply dmap_diff_union_refl...
  assert (wf_genv G  /\ wf_denv G D1 /\ wf_denv G D2 /\ (exists K, wf_atyp G T K) /\ expr e) as H.
   apply atyping_regular... destruct H as [Wfg [Wfd1 [Wfd2 EX]]].
  assert (uniq D1) as Uniq1.
   apply uniq_from_wf_denv_lin with G...
  assert (uniq D2) as Uniq2.
   apply uniq_from_wf_denv_lin with G...
  assert (<# <@ (<#D1#> -- <#D2#>) @> ++ D2 #> ~~ (<# <@ (<#D1#> -- <#D2#>) @> #> |_| <#D2#>)) as Eq2.
   apply disjoint_denv_cons_union.
    apply uniq_app_4...
     apply dmap_to_denv_is_uniq.
     apply dmap_denv_disjoint.
     assert (<# D1 #> -- <# D2 #> ~~ <# <@<# D1 #> -- <# D2 #>@> #>) as Eq3.
      apply denv_to_from_dmap.
     apply dmap_Equal_preserves_disjoint_left with (<# D1 #> -- <# D2 #>)...
     apply diff_disjoint.
     apply Equal_sym...
   subst.
   assert (<# <@ <# D1 #> -- <# D2 #> @> ++ D2 #> ~~ <# D1 #>) as Eq3.
    eapply Equal_trans. eauto. 
    apply Equal_sym in Eq. apply Equal_sym.
    apply dmap_Equal_rewrite_Union_left with (<# D1 #> -- <# D2 #>).
    apply denv_to_from_dmap. auto.
   apply Equal_sym in Eq3.
   assert (permute D1 (<@ <# D1 #> -- <# D2 #> @> ++ D2)) as Perm.
    apply eq_uniq_implies_perm...
     apply uniq_app_4...
      apply dmap_to_denv_is_uniq.
      apply dmap_denv_disjoint.
      assert (<# D1 #> -- <# D2 #> ~~ <# <@<# D1 #> -- <# D2 #>@> #>) as Eq4.
      apply denv_to_from_dmap.
     apply dmap_Equal_preserves_disjoint_left with (<# D1 #> -- <# D2 #>)...
     apply diff_disjoint.
     apply Equal_sym...
   exists (<@ <# D1 #> -- <# D2 #> @>).
   apply perm_comm_right...
Qed.

Lemma wf_lenv_permute : forall G D1 D2, 
  wf_lenv G D1 ->
  permute D1 D2 ->
  wf_lenv G D2.
Proof with eauto.
  intros G D1 D2 Wfl Perm.
  generalize dependent D2.
  induction Wfl; intros...
   inversion Perm; subst...
   inversion Perm; subst...
   assert (wf_lenv E (DL ++ DR)) as Hwfl.
    apply IHWfl...
   apply wf_lenv_lin_weakening...
   assert (dom D [=] dom (DL ++ DR)). 
    apply dom_permute... rewrite <- H2...
Qed.

Lemma wf_denv_sound : forall G D,
  wf_denv G D ->
  wf_lenv (from_genv_to_env G) (from_denv_to_lenv D).
Proof with eauto.
  intros G D Wfd.
  induction Wfd; intros; subst...
   simpl. apply wf_genv_sound in H.
   apply wf_lenv_empty...
   
   assert (permute ([(x, T)] ++ D) D') as Perm.
    apply eq_uniq_implies_perm...
     assert (uniq D).
      apply uniq_from_wf_denv_lin with G...
      solve_uniq.
   assert (wf_lenv (from_genv_to_env G) (from_denv_to_lenv ([(x, T)] ++ D))) as Wfl.
    simpl. simpl_env. apply wf_lenv_typ... 
     rewrite <- dom_G_remain...
     rewrite <- dom_D_remain...
     apply wf_atyp_sound in H. destruct K...
   eapply wf_lenv_permute. eauto.
   apply perm_denv_to_lenv_2...
Qed.

Theorem Soundness : forall G D3 e T D2 D1, 
  atyping G D3 e T D2 ->
  permute D3 (D2 ++ D1) ->
  typing (from_genv_to_env G) (from_denv_to_lenv D1) e T
 .
Proof with eauto.
  intros G D3 e T D2 D1 ATyp Perm.
   
  remember G as GG. remember D3 as DD3. remember e as ee. remember T as TT. remember D2 as DD2.
  generalize dependent G. 
  generalize dependent D3. 
  generalize dependent e. 
  generalize dependent T. 
  generalize dependent D2.
  generalize dependent D1.
  (atyping_cases (induction ATyp) Case); intros; subst; simpl_env in *.
  Case "atyping_uvar".
   assert (D1 = dempty).
    apply perm_dempty with D2... 
     apply uniq_from_wf_denv_lin with G0...
   subst; simpl.
   apply typing_var...
   apply wf_genv_sound... apply wf_genv_from_wf_denv with D3...
   apply binds_typ_sound... auto.
  Case "atyping_lvar".
   assert (<# D3 #> ~~ <# D2 ++ [(x, T0)] #>).
    apply lvar_case_lemma1...
   apply uniq_from_wf_denv_lin with G0...
   assert (x `notin` dom D2) as xNotinD2.
    assert (~ EMap.In x (<# D3 #>[-]x)) as H4.
      apply dmap_remove_clear.
     apply notIn_implies_notin_dom in H4.
     assert (x `notin` dom <@ <# D3 #>[-]x @> <-> x `notin` dom D2) as H5.
      apply denv_equal_notin_dom_iff. unfold denv_Equal.
      eapply Equal_trans. apply Equal_sym. apply denv_to_from_dmap.
       auto.
    apply H5 in H4. solve_uniq.
   assert (D1 = [(x, T0)]) as HD1.
    eapply lvar_case_lemma2.
     eauto. auto. eapply uniq_from_wf_denv_lin. eauto.
     solve_uniq.
     auto.
     auto.
   
   subst. simpl.
   apply typing_lvar.
    rewrite_env ([(x, lbind_typ T0)] ++ lempty). apply wf_lenv_typ.
    apply wf_lenv_empty. apply wf_genv_sound. 
     eapply wf_genv_from_wf_denv. eauto.
     rewrite <- dom_G_remain. eapply denv_dom_dinv. eauto.
      apply binds_In with T0... auto.
    apply wf_atyp_sound.
     destruct (wf_atyp_from_dbinds_typ x T0 G0 D3 H0 H) as [K WfAtyp].
      destruct K...
       eapply wf_atyp_sub. eauto. auto.
  
  Case "atyping_uabs".
   assert (wf_typ (from_genv_to_env G0) V kn_nonlin) as Wftyp.
    apply wf_atyp_sound...
   pick fresh x.
   assert ( atyping ([(x, gbind_typ V)] ++ G0) D3 (open_ee e1 x) T1 D2) as ATyping...
   apply atyping_regular in ATyping. 
   destruct ATyping as [WfG [WfD3 [WfD2 [Wfatyp Expr]]]].
   assert (uniq D3) as Uniq3. 
    apply uniq_from_wf_denv_lin with ([(x, gbind_typ V)] ++ G0)...
   assert (uniq D2) as Uniq2.
    apply uniq_from_wf_denv_lin with ([(x, gbind_typ V)] ++ G0)...
   
   assert (typing (from_genv_to_env ([(x, gbind_typ V)] ++ G0))
         (from_denv_to_lenv D1) (open_ee e1 x) T1) as Typing.
    apply H1 with D2 T1 (open_ee e1 x) D3 ([(x, gbind_typ V)] ++ G0)...
    (* simpl. rewrite_env (empty ++ [(x, bind_typ V)] ++ from_genv_to_env G0).
    apply lenv_split_weakening...
     simpl_env. rewrite_env (from_genv_to_env ([(x, gbind_typ V)] ++ G0)).
      apply wf_genv_sound...
      apply disjoint_one_2.
       rewrite <- dom_D_remain. auto. *)

   assert (D3 ~~~ D2 -> D1 = dempty) as H3.
    intros EQD3D2.
    eapply eq_uniq_perm_dempty. 
     eauto. auto. auto. auto.
   assert (K = kn_nonlin -> D1 = dempty) as Imp.
    intros KEq. 
    apply H2 in KEq.
    apply H3. auto.
   apply typing_abs with (union L
                 (union (fv_te e1)
                    (union (fv_ee e1)
                       (union (fv_tt V)
                          (union (fv_tt T1)
                             (union (dom G0)
                                (union (dom D1)
                                   (union (dom D2)
                                      (union (dom D3)
                                         (union (denv_fv_tt D1)
                                            (union 
                                               (denv_fv_tt D2)
                                               (union 
                                                  (denv_fv_tt D3)
                                                  (genv_fv_tt G0)))))))))))))...
    simpl in H1. 
    intros x0 NotinL. 
    rewrite_env ((x0, bind_typ V) :: (from_genv_to_env G0)). 
    eapply H1.
     auto.
    (* simpl. rewrite_env (empty ++ [(x0, bind_typ V)] ++ from_genv_to_env G0).
    apply lenv_split_weakening...
     simpl_env. rewrite_env (from_genv_to_env ([(x0, gbind_typ V)] ++ G0)).
      apply wf_genv_sound... assert (atyping ([(x0, gbind_typ V)] ++ G0) D3 (open_ee e1 x0) T1 D2)...
      apply disjoint_one_2.
       rewrite <- dom_D_remain. auto.*) auto. eauto. eauto. eauto. eauto. eauto.
    intros Keq.
     apply Imp in Keq. subst...

  Case "atyping_labs".
   assert (wf_typ (from_genv_to_env G0) V Q) as Wftyp.
    apply wf_atyp_sound...

   pick fresh x.
   assert ( atyping G0 ([(x, V)] ++ D3) (open_ee e1 x) T1 D2) as ATyping...
   apply atyping_regular in ATyping. 
   destruct ATyping as [WfG [WfD3 [WfD2 [Wfatyp Expr]]]].
   assert (uniq ([(x, V)] ++ D3)) as U3. 
    apply uniq_from_wf_denv_lin with G0...
   assert (uniq D3) as Uniq3.
    inversion U3...
   assert (uniq D2) as Uniq2.
    apply uniq_from_wf_denv_lin with G0...
   assert (uniq (D2 ++ D1)) as Uniq12.
    apply uniq_env_permute with D3...

   assert (typing (from_genv_to_env G0)
         (from_denv_to_lenv ([(x, V)] ++ D1)) (open_ee e1 x) T1) as Typing.
    apply H1 with D2 T1 (open_ee e1 x) ([(x, V)] ++ D3) G0...
    (*simpl. simpl_env. apply lenv_split_right...
      rewrite <- dom_G_remain...
      rewrite <- dom_D_remain...
      destruct Q...*)
     
     assert (D3 ~~~ (D2 ++ D1)) as EQ.
      apply perm_uniq_implies_eq...
     assert (([(x, V)] ++ D3) ~~~ ([(x, V)] ++ D2 ++ D1)) as EQ2.
      apply denv_add_preserves_Equal...
     assert ( dempty ++ [(x, V)] ++ dempty ++ D2 ++ D1 ~~~ 
       dempty ++ D2 ++ dempty ++ [(x, V)] ++ D1) as EQ3.
      apply disjoint_denv_cons_commut_aux.
       simpl_env. rewrite_env((x, V) :: (D2 ++ D1)).
        apply uniq_cons...
     simpl_env in *.
     assert ([(x, V)] ++ D3 ~~~ D2 ++ [(x, V)] ++ D1) as EQ4.
      eapply Equal_trans. eauto. auto.
     apply eq_uniq_implies_perm...
   
   assert (D3 ~~~ D2 -> D1 = dempty) as H3.
    intros EQD3D2.
    eapply eq_uniq_perm_dempty. 
     eauto. auto. auto. auto.
   assert (K = kn_nonlin -> D1 = dempty) as Imp.
    intros KEq. 
    apply H2 in KEq.
    apply H3. auto.

   apply typing_labs with (union L
                 (union (fv_te e1)
                    (union (fv_ee e1)
                       (union (fv_tt V)
                          (union (fv_tt T1)
                             (union (dom G0)
                                (union (dom D1)
                                   (union (dom D2)
                                      (union (dom D3)
                                         (union (denv_fv_tt D1)
                                            (union 
                                               (denv_fv_tt D2)
                                               (union 
                                                  (denv_fv_tt D3)
                                                  (genv_fv_tt G0))))))))))))).
    destruct Q...
    intros x0 NotinL. 
    rewrite_env (from_denv_to_lenv ([(x0, V)] ++ D1)). 
    eapply H1.
     auto. 
     (*simpl. simpl_env. apply lenv_split_right...
      rewrite <- dom_G_remain...
      rewrite <- dom_D_remain...
      destruct Q...*)
     assert (D3 ~~~ (D2 ++ D1)) as EQ.
      apply perm_uniq_implies_eq...
     assert (([(x0, V)] ++ D3) ~~~ ([(x0, V)] ++ D2 ++ D1)) as EQ2.
      apply denv_add_preserves_Equal...
     assert ( dempty ++ [(x0, V)] ++ dempty ++ D2 ++ D1 ~~~ 
       dempty ++ D2 ++ dempty ++ [(x0, V)] ++ D1) as EQ3.
      apply disjoint_denv_cons_commut_aux.
       simpl_env. rewrite_env((x0, V) :: (D2 ++ D1)).
        apply uniq_cons... 

     simpl_env in *.
     assert ([(x0, V)] ++ D3 ~~~ D2 ++ [(x0, V)] ++ D1) as EQ4.
      eapply Equal_trans. eauto. auto.

     apply eq_uniq_implies_perm...
     auto. eauto. eauto. eauto. eauto.
    intros Keq.
     apply Imp in Keq. subst...
  Case "atyping_app".
   rename D5 into D1. rename D4 into D3.
   (*remember (from_genv_to_env G0) as g0.
   remember (from_denv_to_lenv D1) as d1.
   remember (from_denv_to_lenv D2) as d2.
   remember (from_denv_to_lenv D3) as d3.
   remember (from_denv_to_lenv D0) as d0.*)
   assert (exists D, permute D1 (D2 ++ D)) as EX1.
    eapply atyping_denv_ex_eq. apply ATyp1.
   assert (exists D, permute D2 (D3 ++ D)) as EX2.
    eapply atyping_denv_ex_eq. apply ATyp2.
   destruct EX1 as [D21 Perm1].
   destruct EX2 as [D32 Perm2].
   assert (exists D11, exists D12, 
        permute (from_denv_to_lenv D1) ((from_denv_to_lenv D2) ++ D11) /\
        permute (from_denv_to_lenv D2) ((from_denv_to_lenv D3) ++ D12) /\
        lenv_split (from_genv_to_env G0)  D12 D11 (from_denv_to_lenv D0)) as HApp.
    apply app_case_lemma with (from_denv_to_lenv D32) (from_denv_to_lenv D21)...
    apply wf_denv_sound...
    rewrite <- denv_to_lenv_conc. 
     apply perm_denv_to_lenv_2...
    rewrite <- denv_to_lenv_conc.
     apply perm_denv_to_lenv_2...
    rewrite <- denv_to_lenv_conc.
     apply perm_denv_to_lenv_2...    
   destruct HApp as [D11 [D12 [Perm3 [Perm4 Lsplit]]]].
   assert (D11 = from_denv_to_lenv (from_lenv_to_denv D11)) as EQ1.
    apply lenv_refl.
   assert (D12 =  from_denv_to_lenv (from_lenv_to_denv D12) ) as EQ2.
    apply lenv_refl.
   rewrite EQ1 in Perm3. rewrite EQ2 in Perm4.
   rewrite <- denv_to_lenv_conc in Perm3. 
   rewrite <- denv_to_lenv_conc in Perm4.
   apply perm_denv_to_lenv in Perm3.
   apply perm_denv_to_lenv in Perm4.
   assert (typing (from_genv_to_env G0) (from_denv_to_lenv (from_lenv_to_denv D11)) e1 (typ_arrow K T1 T)) as typing1.
    eapply IHATyp1...
   assert (typing (from_genv_to_env G0)
              (from_denv_to_lenv (from_lenv_to_denv D12)) e2 T1) as typing2.
     eapply IHATyp2...
   rewrite <- lenv_refl in typing1.
   rewrite <- lenv_refl in typing2.
   eapply typing_app... apply lenv_split_commute...
  Case "atyping_tabs".
   apply typing_tabs with L...
    intros X Notin. simpl in H1. 
    rewrite_env ((X, bind_kn K) :: from_genv_to_env G0). 
    eapply H1...
  Case "atyping_tapp".
   apply typing_tapp with K...
    apply wf_atyp_sound in H.
    destruct K';
     destruct K;
      try(inversion H0)...
Qed.
     