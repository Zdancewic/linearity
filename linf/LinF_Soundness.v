
(** Type-safety proofs.

    Authors: Steve Zdancewic and Karl Mazurak.

    Table of contents:
      - #<a href="##subtyping">Properties of subtyping</a>#
      - #<a href="##typing">Properties of typing</a>#
      - #<a href="##preservation">Preservation</a>#
      - #<a href="##progress">Progress</a># *)

Require Export LinF_Lemmas.
Require Import Omega.

(* ********************************************************************** *)
(** * Weakening *)

Lemma wf_lenv_disjoint: forall G D,
  wf_lenv G D ->
  disjoint G D.
Proof.
  induction D; simpl_env; intros.
  SCase "nil".
    unfold disjoint. fsetdec.
  SCase "con".
    inversion H; subst.
    solve_uniq.
Qed.

Lemma wf_lenv_weakening: forall E F G D,
  wf_lenv (G ++ E) D ->
  wf_env (G ++ F ++ E) ->
  disjoint F D ->
  wf_lenv (G ++ F ++ E) D.
Proof.
  intros E F G D WFL.
  remember (G ++ E) as G0.
  generalize dependent G. 
  (wf_lenv_cases (induction WFL) Case);
    intros G EQ WFE NIN; subst; simpl_env in *; auto.
  Case "wf_lenv_typ".
    apply wf_lenv_typ; auto.
      apply IHWFL; auto.
       intros. solve_uniq.

      repeat rewrite dom_app.
      assert (x `notin` dom F) as J. 
        solve_uniq.
      fsetdec.

      eapply wf_typ_weakening; auto. 
Qed.

Lemma lenv_split_weakening: forall E F G D1 D2 D3,
  lenv_split (E ++ G) D1 D2 D3 ->
  wf_env (E ++ F ++ G) ->
  disjoint F D3 ->
  lenv_split (E ++ F ++ G) D1 D2 D3.
Proof.
  intros E F G D1 D2 D3 S.
  remember (E ++ G) as G0.
  generalize dependent E. generalize dependent G. generalize dependent F.
  (lenv_split_cases (induction S) Case); intros F1 G1 E1 EQ WFE NIN; auto.
  Case "lenv_split_left".
    apply lenv_split_left; subst; auto using wf_typ_weakening.
      apply IHS; auto. 
        solve_uniq.
      simpl; solve_uniq.
  Case "lenv_split_right".
    apply lenv_split_right; subst; auto using wf_typ_weakening.
      apply IHS; auto. 
        solve_uniq.
      simpl; solve_uniq.
Qed.
  
Lemma typing_weakening: forall E F G D e T,
  typing (G ++ E) D e T ->
  wf_lenv (G ++ F ++ E) D ->
  typing (G ++ F ++ E) D e T.
Proof with simpl_env;
           eauto using wf_typ_weakening,
                       wf_typ_from_wf_env_typ.
  intros E F G D e T Typ.
  remember (G ++ E) as H.
  generalize dependent G. generalize dependent E.
  (typing_cases (induction Typ) Case); intros E0 G EQ WFL; subst...
  Case "typing_abs".
    pick fresh x and apply typing_abs; subst; auto.
      apply wf_typ_weakening; auto.

      lapply (H1 x); intros; auto.
      rewrite <- app_assoc.
      eapply H3; eauto.
      simpl_env. rewrite_env (nil ++ [(x, bind_typ T1)] ++ G ++ F ++ E0).
      eapply wf_lenv_weakening; auto.
        apply wf_env_typ; auto.
          apply wf_typ_weakening; eauto. 
  Case "typing_labs".
    pick fresh x and apply typing_labs; subst; auto.
      apply wf_typ_weakening; auto.
  
      eapply (H1 x); auto. 
        apply wf_lenv_typ; auto. 
          apply wf_typ_weakening; auto.
  Case "typing_app".
    eapply typing_app.
      eapply IHTyp1; eauto.
        eapply wf_lenv_split_left.
          apply lenv_split_weakening; eauto. 
            apply wf_lenv_disjoint in WFL. solve_uniq.
      eapply IHTyp2; eauto.
        eapply wf_lenv_split_right.
          apply lenv_split_weakening; eauto.
            apply wf_lenv_disjoint in WFL. solve_uniq.
      eapply lenv_split_weakening; auto.
        apply wf_lenv_disjoint in WFL. solve_uniq.
  Case "typing_tabs".
    pick fresh X and apply typing_tabs; auto.
    lapply (H1 X); [intros Q | auto].
    rewrite <- app_assoc.
    apply H1...
      rewrite_env (nil ++ [(X, bind_kn K)] ++ G ++ F ++ E0).
      apply wf_lenv_weakening; auto. 
        simpl_env. apply wf_env_kn; auto.
Qed.

(************************************************************************ *)
(** * Type substitution preserves typing *)

Lemma lenv_split_subst_tb : forall G1 G2 D1 D2 D3 X K P,
  lenv_split (G1 ++ [(X, bind_kn K)] ++ G2) D1 D2 D3 ->
  wf_typ G2 P K ->
  lenv_split (map (subst_tb X P) G1 ++ G2)
             (map (subst_tlb X P) D1)
             (map (subst_tlb X P) D2)
             (map (subst_tlb X P) D3).
Proof.
  intros G1 G2 D1 D2 D3 X K P S.
  remember (G1 ++ [(X, bind_kn K)] ++ G2) as G.
  generalize dependent G1. generalize dependent G2.
  (lenv_split_cases (induction S) Case);
    intros G2 G1 EQ WFT; subst; simpl_env in *; auto.
  Case "lenv_split_empty".
    apply lenv_split_empty; auto.
      eapply wf_env_subst_tb; eauto.
  Case "lenv_split_left".
    apply lenv_split_left; auto.
      eapply wf_typ_subst_tb; eauto.
  Case "lenv_split_right".
    apply lenv_split_right; auto.
      eapply wf_typ_subst_tb; eauto.
Qed.
    
Lemma value_through_subst_te : forall e Z P,
  type P ->
  value e ->
  value (subst_te Z P e).
Proof.
  intros e Z P Typ H.
  (value_cases (induction H) Case); simpl; auto using subst_te_expr.
  Case "value_abs".
    assert (expr (subst_te Z P (exp_abs K T e1))) as J.
      apply subst_te_expr; auto.
    apply value_abs; auto.
  Case "value_tabs".
    assert (expr (subst_te Z P (exp_tabs K e1))) as J.
      apply subst_te_expr; auto.
    apply value_tabs; auto.
Qed.

Lemma typing_through_subst_te : forall K E F D Z e T P,
  typing (F ++ [(Z, bind_kn K)] ++ E) D e T ->
  wf_typ E P K ->
  typing (map (subst_tb Z P) F ++ E) (map (subst_tlb Z P) D) (subst_te Z P e) (subst_tt Z P T).
Proof with simpl_env;
           eauto 6 using wf_env_subst_tb,
                         wf_typ_subst_tb.
  intros K E F D Z e T P Typ PsubK.
  remember (F ++ [(Z, bind_kn K)] ++ E) as G.
  generalize dependent F. generalize dependent E.
  (typing_cases (induction Typ) Case); intros E0 WFT F EQ; subst;
    simpl subst_te in *; simpl subst_tt in *...
  Case "typing_var".
    apply typing_var...
    rewrite (map_subst_tb_id E0 Z P).
      analyze_binds_uniq H0... 

      eapply wf_env_strengthening_tail.
      eapply wf_env_strengthening_tail; eauto.

      assert (wf_env ([(Z, bind_kn K)] ++ E0)) as J.
        eapply wf_env_strengthening_tail; eauto.
      inversion J; auto.
  Case "typing_lvar".
     simpl. apply typing_lvar. 
     assert ([(x, lbind_typ (subst_tt Z P T))] = 
             map (subst_tlb Z P) [(x, lbind_typ T)]) as J. auto.
     simpl_env. rewrite J.
     eapply wf_lenv_subst_tb; eauto.
  Case "typing_abs".
    pick fresh y and apply typing_abs...
    rewrite subst_te_open_ee_var...
    rewrite_env (map (subst_tb Z P) ([(y, bind_typ T1)] ++ F) ++ E0).
    simpl in H1.
    apply H1...
    intros. rewrite H2; auto.
  Case "typing_labs".
    pick fresh y and apply typing_labs...
    rewrite subst_te_open_ee_var...
    rewrite_env (map (subst_tlb Z P) ([(y, lbind_typ T1)] ++ D)).
    apply H1...
    intros. rewrite H2; auto.
  Case "typing_app".
    eapply typing_app; eauto. 
      eapply lenv_split_subst_tb; eauto.
  Case "typing_tabs".
    pick fresh Y and apply typing_tabs.
      rewrite subst_tt_fresh with (T:=Y) (Z:=Z) (U:=P); auto.
      rewrite <- subst_te_open_te; auto.
        apply value_through_subst_te; auto.
          eapply type_from_wf_typ; eauto.
        eapply type_from_wf_typ; eauto.
      rewrite subst_te_open_te_var; eauto using type_from_wf_typ.
      rewrite subst_tt_open_tt_var; eauto using type_from_wf_typ.
      rewrite_env (map (subst_tb Z P) ([(Y, bind_kn K0)] ++ F) ++ E0); eauto.
  Case "typing_tapp".
    rewrite subst_tt_open_tt... 
      eapply type_from_wf_typ; eauto.
Qed.

(************************************************************************ *)
(** * Substitution preserves typing *)

Lemma value_through_open_te: forall e1 T,
  value e1 ->
  value (open_te e1 T).
Proof.
  intros e1 T H.
  unfold open_te. 
  rewrite <- open_te_rec_expr; auto.
Qed.

Lemma typing_fv: forall E D e T x,
  typing E D e T ->
  x `notin` dom E ->
  x `notin` dom D ->
  x `notin` fv_ee e.
Proof.
  intros E D e T x H.
  (typing_cases (induction H) Case); intros NIE NID; simpl; auto.
  Case "typing_var".
    assert (x0 `in` dom E) as J. 
      eapply binds_In; eauto. 
    fsetdec.
  Case "typing_abs".
    pick fresh y. 
    lapply (H1 y); intros; auto.
    simpl in H3. unfold not. intros. apply H3; auto.
    assert (x `notin` singleton y) as J. destruct_notin; auto.
    unfold open_ee. apply fv_in_open_ee; auto.
  Case "typing_labs".
    pick fresh y. 
    lapply (H1 y); intros; auto.
    simpl in H3. unfold not. intros. apply H3; auto. 
    assert (x `notin` singleton y) as J. destruct_notin; auto.
    unfold open_ee. apply fv_in_open_ee; auto.
  Case "typing_app".
    assert (x `notin` fv_ee e1) as J1. 
      apply IHtyping1; auto.
        rewrite (dom_lenv_split E D1 D2 D3) in NID; auto.
    assert (x `notin` fv_ee e2) as J2. 
      apply IHtyping2; auto.
        rewrite (dom_lenv_split E D1 D2 D3) in NID; auto.
    fsetdec.
  Case "typing_tabs".
    pick fresh y. lapply (H1 y); intros; auto.
    unfold not. intros. apply H2; auto.
    unfold open_te. apply fv_in_open_te. auto.
Qed.

Lemma non_subst: forall E D e T x u,
  typing E D e T ->
  x `notin` dom E ->
  x `notin` dom D ->
  e = subst_ee x u e.
Proof.
  intros E D e T x y H1 H2 H3.
  apply subst_ee_fresh.
  eapply typing_fv; eauto.
Qed.

Lemma lenv_split_strengthening: forall G2 G1 x T D1 D2 D3,
  lenv_split (G2 ++ [(x, bind_typ T)] ++ G1) D1 D2 D3 ->
  lenv_split (G2 ++ G1) D1 D2 D3.
Proof.
  intros G2 G1 x T D1 D2 D3 S.
  remember (G2 ++ [(x, bind_typ T)] ++ G1) as G.
  generalize dependent G1. generalize dependent G2.
  (lenv_split_cases (induction S) Case); 
    intros G2 G1 EQ; simpl_env in *; subst; auto.
  Case "lenv_split_empty".
    apply lenv_split_empty. 
      eapply wf_env_strengthening; eauto.
  Case "lenv_split_left".
    apply lenv_split_left; auto. 
      simpl_env in *.
      eapply wf_typ_strengthening; eauto. 
  Case "lenv_split_right".
    apply lenv_split_right; auto. 
      simpl_env in *.
      eapply wf_typ_strengthening; eauto.
Qed.

Lemma value_through_subst_ee: forall e1 x u,
  expr u ->
  value e1 ->
  value (subst_ee x u e1).
Proof.
  intros e1 x u EX V.
  (value_cases (induction V) Case); simpl; auto.
  Case "value_abs".
    inversion H; subst.
    apply value_abs. 
      pick fresh z and apply expr_abs; auto.
        rewrite subst_ee_open_ee_var; auto.
  Case "value_tabs".
    inversion H; subst.
    apply value_tabs.
      pick fresh X and apply expr_tabs.
        rewrite subst_ee_open_te_var; auto.
Qed.

Lemma typing_through_subst_ee_nonlin: forall G2 G1 x U0 D e T u,
  typing (G2 ++ [(x, bind_typ U0)] ++ G1) D e T ->
  typing G1 lempty u U0 ->
  value u ->
  typing (G2 ++ G1) D (subst_ee x u e) T.
Proof.
  intros G2 G1 x U0 D e T u Typ.
  remember (G2 ++ [(x, bind_typ U0)] ++ G1) as G.
  generalize dependent G2. generalize dependent G1.
  (typing_cases (induction Typ) Case);   
    intros G1 G2 EQ TYP V; simpl_env in *; simpl; subst; eauto.
  Case "typing_var".
    destruct (x0 == x); subst.
    SCase "x0 == x".
      rewrite_env (nil ++ G2 ++ G1).
      apply typing_weakening; auto.
        assert (bind_typ T = bind_typ U0) as J.
          eauto using binds_mid_eq.
       inversion J; subst; auto.

       simpl_env. apply wf_lenv_empty. 
       eapply wf_env_strengthening; eauto.
    SCase "x0 <> x".
      apply typing_var; auto.
        eapply wf_env_strengthening; eauto.
        analyze_binds_uniq H0.
  Case "typing_lvar".
    destruct (x0 == x); subst.
    SCase "x0 == x".
      inversion H; subst. 
      assert False as J. 
        apply H5. 
        repeat rewrite dom_app. 
        simpl. fsetdec. 
      tauto.
    SCase "x0 <> x".
      apply typing_lvar.  
        eapply wf_lenv_strengthening; eauto.
  Case "typing_abs".
    pick fresh y and apply typing_abs; auto.
      eapply wf_typ_strengthening; eauto.

      rewrite_env (([(y, bind_typ T1)] ++ G2) ++ G1).
      rewrite subst_ee_open_ee_var; auto.
  Case "typing_labs".
    pick fresh y and apply typing_labs; auto.
      eapply wf_typ_strengthening; eauto.
      rewrite subst_ee_open_ee_var; eauto.
  Case "typing_app".
    eapply typing_app; eauto.
      eapply lenv_split_strengthening; eauto.
  Case "typing_tabs".
    pick fresh X and apply typing_tabs; auto.
      rewrite <- subst_ee_open_te; auto.
      apply value_through_subst_ee; auto.

      rewrite_env (([(X, bind_kn K)] ++ G2) ++ G1).
      rewrite subst_ee_open_te_var; eauto.
  Case "typing_tapp".
    eapply typing_tapp. eapply IHTyp; auto.
    eapply wf_typ_strengthening; eauto.
Qed.

Lemma typing_through_subst_ee_nonlin2: forall G2 G1 x U0 D e T u,
  typing (G2 ++ [(x, bind_typ U0)] ++ G1) D e T ->
  typing G1 lempty u U0 ->
  typing (G2 ++ G1) D (subst_ee x u e) T.
Proof.
  intros G2 G1 x U0 D e T u Typ.
  remember (G2 ++ [(x, bind_typ U0)] ++ G1) as G.
  generalize dependent G2. generalize dependent G1.
  (typing_cases (induction Typ) Case);   
    intros G1 G2 EQ TYP; simpl_env in *; simpl; subst; eauto.
  Case "typing_var".
    destruct (x0 == x); subst.
    SCase "x0 == x".
      rewrite_env (nil ++ G2 ++ G1).
      apply typing_weakening; auto.
        assert (bind_typ T = bind_typ U0) as J.
          eauto using binds_mid_eq.
       inversion J; subst; auto.

       simpl_env. apply wf_lenv_empty. 
       eapply wf_env_strengthening; eauto.
    SCase "x0 <> x".
      apply typing_var; auto.
        eapply wf_env_strengthening; eauto.
        analyze_binds_uniq H0.
  Case "typing_lvar".
    destruct (x0 == x); subst.
    SCase "x0 == x".
      inversion H; subst. 
      assert False as J. 
        apply H5. 
        repeat rewrite dom_app. 
        simpl. fsetdec. 
      tauto.
    SCase "x0 <> x".
      apply typing_lvar.  
        eapply wf_lenv_strengthening; eauto.
  Case "typing_abs".
    pick fresh y and apply typing_abs; auto.
      eapply wf_typ_strengthening; eauto.

      rewrite_env (([(y, bind_typ T1)] ++ G2) ++ G1).
      rewrite subst_ee_open_ee_var; auto.
  Case "typing_labs".
    pick fresh y and apply typing_labs; auto.
      eapply wf_typ_strengthening; eauto.
      rewrite subst_ee_open_ee_var; eauto.
  Case "typing_app".
    eapply typing_app; eauto.
      eapply lenv_split_strengthening; eauto.
  Case "typing_tabs".
    pick fresh X and apply typing_tabs; auto.
      rewrite <- subst_ee_open_te; auto.
      apply value_through_subst_ee; auto.

      rewrite_env (([(X, bind_kn K)] ++ G2) ++ G1).
      rewrite subst_ee_open_te_var; eauto.
  Case "typing_tapp".
    eapply typing_tapp. eapply IHTyp; auto.
    eapply wf_typ_strengthening; eauto.
Qed.

Lemma contraction: forall G2 G1 x y U0 D e T,
  typing (G2 ++ [(y, bind_typ U0)] ++ [(x, bind_typ U0)] ++ G1) D e T ->
  typing (G2 ++ [(x, bind_typ U0)] ++ G1) D (subst_ee y x e) T.
Proof.
  intros G2 G1 x y U0 D e T Typ.
  remember (G2 ++ [(y, bind_typ U0)] ++ [(x, bind_typ U0)] ++ G1) as G.
  generalize dependent G2. generalize dependent G1.
  (typing_cases (induction Typ) Case);   
    intros G1 G2 EQ; simpl_env in *; simpl; subst; eauto.
  Case "typing_var".
    destruct (x0 == y); subst.
    SCase "x0 == y".
      simpl_env. apply typing_var.
       eapply wf_env_strengthening; eauto.
       assert (bind_typ T = bind_typ U0) as J.
          eauto using binds_mid_eq.
       inversion J; subst; auto.
    SCase "x0 <> x".
      simpl_env.
      apply typing_var; auto.
      eapply wf_env_strengthening; eauto.
      analyze_binds_uniq H0.
  Case "typing_lvar".
    destruct (x0 == y); subst.
    SCase "x0 == y".
      inversion H; subst. 
      assert False as J. 
        apply H5. 
        repeat rewrite dom_app. 
        simpl. fsetdec. 
      tauto.
    SCase "x0 <> y".
      apply typing_lvar.  
        eapply wf_lenv_strengthening; eauto.
  Case "typing_abs".
    pick fresh z and apply typing_abs; auto.
      eapply wf_typ_strengthening; eauto.

      rewrite_env (([(z, bind_typ T1)] ++ G2) ++ [(x, bind_typ U0)] ++ G1).
      rewrite subst_ee_open_ee_var; auto.
  Case "typing_labs".
    pick fresh z and apply typing_labs; auto.
      eapply wf_typ_strengthening; eauto.
      rewrite subst_ee_open_ee_var; eauto. simpl_env. eauto.
  Case "typing_app".
    simpl_env.
    eapply typing_app; eauto. 
      eapply lenv_split_strengthening; eauto.
  Case "typing_tabs".
    simpl_env.
    pick fresh X and apply typing_tabs; auto.
      rewrite <- subst_ee_open_te; auto.
      apply value_through_subst_ee; auto.

      rewrite_env (([(X, bind_kn K)] ++ G2) ++ [(x, bind_typ U0)] ++ G1).
      rewrite subst_ee_open_te_var; eauto.
  Case "typing_tapp".
    simpl_env.
    eapply typing_tapp. eapply IHTyp; auto.
    eapply wf_typ_strengthening; eauto.
  Case "typing_apair".
    simpl_env. apply typing_apair. eauto. eauto.
  Case "typing_fst".
    simpl_env. eapply typing_fst; eauto.
  Case "typing_snd".
    simpl_env. eapply typing_snd; eauto.
Qed.

Lemma lenv_split_cases_mid: forall G D1 D2 DL x T DR,
  lenv_split G D1 D2 (DL ++ [(x, lbind_typ T)] ++ DR) ->
  (exists D1L, exists D1R, exists D2L, exists D2R,
    D1 = D1L ++ [(x, lbind_typ T)] ++ D1R /\
    D2 = D2L ++ D2R /\
    lenv_split G D1L D2L DL /\
    lenv_split G D1R D2R DR) \/
  (exists D1L, exists D1R, exists D2L, exists D2R,
    D1 = D1L ++ D1R /\
    D2 = D2L ++ [(x, lbind_typ T)] ++ D2R /\
    lenv_split G D1L D2L DL /\
    lenv_split G D1R D2R DR).
Proof.
  intros G D1 D2 DL x T DR S.
  remember (DL ++ [(x, lbind_typ T)] ++ DR) as D3.
  generalize dependent DR. generalize dependent DL.
  (lenv_split_cases (induction S) Case);  
    intros DL DR EQ; subst; simpl_env in *.
  Case "lenv_split_empty".
    destruct DL; inversion EQ.
  Case "lenv_split_left".
    destruct DL; simpl in *; inversion EQ; subst; simpl_env in *.
    SCase "nil".
      left. 
      exists lempty. exists D1. exists lempty. exists D2. 
      simpl_env. 
      repeat split; auto. 
        apply lenv_split_empty.
          eapply wf_env_from_wf_lenv. 
            eapply wf_lenv_split_left; eauto.
    SCase "con".
      lapply (IHS DL DR); auto.
      intros J.
      destruct J as [J | J].
      SSCase "left".
        destruct J as [D1L [D1R [D2L [D2R [Q1 [Q2 [S1 S2]]]]]]].
        left. exists ([(x0, lbind_typ T0)] ++ D1L).
        exists D1R. exists D2L. exists D2R.
        simpl_env in *. 
        repeat split; subst; auto.
      SSCase "right".
        destruct J as [D1L [D1R [D2L [D2R [Q1 [Q2 [S1 S2]]]]]]].
        right. exists ([(x0, lbind_typ T0)] ++ D1L).
        exists D1R. exists D2L. exists D2R.
        simpl_env in *. 
        repeat split; subst; auto.
  Case "lenv_split_right".
    destruct DL; simpl in *; inversion EQ; subst; simpl_env in *.
    SCase "nil".
      right.
      exists lempty. exists D1. exists lempty. exists D2.
      simpl_env in *. 
      repeat split; auto. 
        apply lenv_split_empty.
          eapply wf_env_from_wf_lenv. 
            eapply wf_lenv_split_left; eauto.
    SCase "con".
      lapply (IHS DL DR); auto.
      intros J.
      destruct J as [J | J].
      SSCase "left".
        destruct J as [D1L [D1R [D2L [D2R [Q1 [Q2 [S1 S2]]]]]]].
        left. exists D1L. 
        exists D1R. exists ([(x0, lbind_typ T0)] ++ D2L). exists D2R.
        simpl_env in *. repeat split; subst; auto.
    
      SSCase "right".
        destruct J as [D1L [D1R [D2L [D2R [Q1 [Q2 [S1 S2]]]]]]].
        right. exists D1L. 
        exists D1R. exists ([(x0, lbind_typ T0)] ++ D2L). exists D2R.
        subst. simpl_env in *. repeat split; auto.
Qed.

Lemma lenv_split_not_in_left: forall G D1 D2 D3 x,
  lenv_split G D1 D2 D3 ->
  x `in` dom D1 ->
  x `notin` (dom D2 `union` dom G).
Proof.
  intros G D1 D2 D3 x S.
  (lenv_split_cases (induction S) Case);  
    intros; simpl_env in *; try fsetdec.
  Case "lenv_split_left".
    rewrite (dom_lenv_split E D1 D2 D3) in H0; auto.
      fsetdec.
  Case "lenv_split_right".
    rewrite (dom_lenv_split E D1 D2 D3) in H0; auto.
      fsetdec.
Qed.

Lemma lenv_split_not_in_right: forall G D1 D2 D3 x,
  lenv_split G D1 D2 D3 ->
  x `in` dom D2 ->
  x `notin` (dom D1 `union` dom G).
Proof.
  intros.
  eapply lenv_split_not_in_left.
    eapply lenv_split_commute; eauto.  
    auto.
Qed.

Lemma lenv_split_lin_weakening_left: forall E F D1 D2 D3,
  lenv_split E D1 D2 D3 ->
  wf_lenv E (F ++ D3) ->
  lenv_split E (F ++ D1) D2 (F ++ D3).
Proof.
  intros E F. 
  induction F; intros D1 D2 D3 S WFL; simpl_env in *; auto.
  Case "con".
    destruct a. simpl_env in *.
    inversion WFL; subst.
    apply lenv_split_left; auto.
Qed.

Lemma lenv_split_sub_left: forall E D1L D1R D2 DL DR x U F,
   lenv_split E 
        (D1L ++ [(x, lbind_typ U)] ++ D1R) 
        D2 
        (DL ++ [(x, lbind_typ U)] ++ DR) ->
   wf_lenv E (DL ++ F ++ DR) ->
   lenv_split E
        (D1L ++ F ++ D1R) 
        D2
        (DL ++ F ++ DR).
Proof.
  intros E D1L D1R D2 DL DR x U F S.
  remember (D1L ++ [(x, lbind_typ U)] ++ D1R) as D1.
  remember (DL ++ [(x, lbind_typ U)] ++ DR) as D3.
  generalize dependent D1R. generalize dependent D1L.
  generalize dependent DR. generalize dependent DL.
  (lenv_split_cases (induction S) Case);  
    intros DL DR EQ1 D1L D1R EQ2 WFL; subst; auto.
  Case "lenv_split_empty".
    destruct DL; inversion EQ1.
  Case "lenv_split_left".
    destruct DL; inversion EQ1; subst.
    SCase "nil".
      destruct D1L; inversion EQ2; subst; simpl_env in *. 
      SSCase "nil".
        apply lenv_split_lin_weakening_left; auto.
      SSCase "con".
        rewrite (dom_lenv_split E (D1L ++ [(x, lbind_typ U)] ++ D1R) D2 DR) in H0; auto.
          simpl_env in *.
          assert False as J. fsetdec. 
          tauto. 
    SCase "nil".
      destruct D1L; inversion EQ2; subst; simpl_env in *. 
      SSCase "nil".
        assert False. fsetdec. 
        tauto. 
      SSCase "con".
        inversion WFL; subst.
        apply lenv_split_left; auto.
  Case "lenv_split_right".
    destruct DL; inversion EQ1; subst; simpl_env in *. 
    SCase "nil".
      rewrite (dom_lenv_split E (D1L ++ [(x, lbind_typ U)] ++ D1R) D2 DR) in H0; auto.
        simpl_env in *. 
        assert False. fsetdec. 
        tauto.
    SCase "con".
      inversion WFL; subst.
      apply lenv_split_right; auto.
Qed.

Lemma lenv_split_sub_right: forall E D1 D2L D2R DL DR x U F,
   lenv_split E 
        D1
        (D2L ++ [(x, lbind_typ U)] ++ D2R) 
        (DL ++ [(x, lbind_typ U)] ++ DR) ->
   wf_lenv E (DL ++ F ++ DR) ->
   lenv_split E
        D1
        (D2L ++ F ++ D2R) 
        (DL ++ F ++ DR).
Proof.
  intros.
  apply lenv_split_commute. 
  eapply lenv_split_sub_left; eauto.
    apply lenv_split_commute; eauto.
Qed.
  
Lemma wf_lenv_lin_strengthening: forall G D1 D2 D3,
  wf_lenv G (D1 ++ D2 ++ D3) ->
  wf_lenv G D2.
Proof.
  intros.
  remember (D1 ++ D2 ++ D3) as D.
  generalize dependent D1. generalize dependent D2. generalize dependent D3.
  (wf_lenv_cases (induction H) Case);  
    intros D3 D2 D1 EQ.
  Case "wf_lenv_empty".
    destruct D1; destruct D2; destruct D3; inversion EQ; auto.
  Case "wf_lenv_typ".
    destruct D1; destruct D2; simpl_env in *; inversion EQ; subst; auto.
    SCase "D1=nil, D2=con".
      apply wf_lenv_typ; auto. 
        apply (IHwf_lenv D3 D2 lempty); auto.
    SCase "D1=con, D2=con".
      apply (IHwf_lenv D3 (p0 :: D2) D1); auto.
Qed.

Lemma typing_through_subst_ee_lin: forall G D2 x U D1 e T F u,
  typing G (D2 ++ [(x, lbind_typ U)] ++ D1) e T ->
  typing G F u U ->
  wf_lenv G (D2 ++ F ++ D1) ->
  typing G (D2 ++ F ++ D1) (subst_ee x u e) T.
Proof.
  intros G D2 x U D1 e T F u TYP.
  remember (D2 ++ [(x, lbind_typ U)] ++ D1) as D.
  generalize dependent D2. generalize dependent D1.
  (typing_cases (induction TYP) Case);  
    intros DR DL EQ TYPU WFL; subst; simpl_env in *; simpl; eauto.
  Case "typing_var".
    destruct DL; inversion EQ.
  Case "typing_lvar".
    destruct DL; inversion EQ; subst. 
    SCase "DL=nil".
      simpl_env in *. simpl.
      destruct (x == x); tauto.
    SCase "DL=con".
      destruct DL; inversion EQ.
  Case "typing_abs".
    pick fresh y and apply typing_abs; auto.
      rewrite subst_ee_open_ee_var; auto.
      apply H1; auto. 
        rewrite_env (nil ++ [(y, bind_typ T1)] ++ E).
        apply typing_weakening; auto. 
          apply wf_lenv_weakening; simpl_env; auto.
        rewrite_env (nil ++ [(y, bind_typ T1)] ++ E). 
        apply wf_lenv_weakening; auto.
          simpl_env; apply wf_env_typ; auto.
      intros. lapply H2; auto. 
      intros. destruct DL; inversion H4.
  Case "typing_labs".
    pick fresh y and apply typing_labs; auto.
      rewrite_env (([(y, lbind_typ T1)] ++ DL) ++ F ++ DR).
      rewrite subst_ee_open_ee_var; auto.
      apply H1; simpl_env; auto. 
      intros. lapply H2; auto. 
      intros. destruct DL; inversion H4.
  Case "typing_app".
    lapply (lenv_split_cases_mid E D1 D2 DL x U DR); auto.
    intros C.
    destruct C as [LEFT | RIGHT].
    SCase "left".
      destruct LEFT as [D1L [D1R [D2L [D2R [Q1 [Q2 [S1 S2]]]]]]]; subst.
      lapply (IHTYP1 D1R D1L); auto.
      intros I. 
      assert (x `notin` (dom (D2L++D2R) `union` dom E)) as J.
        eapply lenv_split_not_in_left; eauto.
          simpl_env. fsetdec.
      lapply I; auto. intros TYPE1. 
      rewrite <- (non_subst E (D2L++D2R) e2 T1 x u); auto.
        apply (typing_app T1 K E (D1L ++ F ++ D1R) (D2L ++ D2R)); auto.
          assert (wf_lenv E (D1L ++ F ++ D1R)) as JJ.
            eapply wf_lenv_split_left. 
              eapply lenv_split_sub_left; eauto.
          apply TYPE1; auto.

          eapply lenv_split_sub_left; eauto.
    SCase "right".
      destruct RIGHT as [D1L [D1R [D2L [D2R [Q1 [Q2 [S1 S2]]]]]]]; subst.
      lapply (IHTYP2 D2R D2L); auto. 
      intros I.
      assert (x `notin` (dom (D1L++D1R) `union` dom E)) as J.
        eapply lenv_split_not_in_right; eauto.
          simpl_env. fsetdec.
      lapply I; auto. intros TYPE2. 
      rewrite <- (non_subst E (D1L ++ D1R) e1 (typ_arrow K T1 T2) x u); auto.
        apply (typing_app T1 K E (D1L ++ D1R) (D2L ++ F ++ D2R)); auto.
          assert (wf_lenv E (D2L ++ F ++ D2R)) as JJ.
            eapply wf_lenv_split_right. 
              eapply lenv_split_sub_right; eauto.
          apply TYPE2; auto. 

          eapply lenv_split_sub_right; eauto.
  Case "typing_tabs".
    pick fresh X and apply typing_tabs.
      rewrite <- subst_ee_open_te; auto.
      apply value_through_subst_ee; auto.

      rewrite subst_ee_open_te_var; auto.
      apply H1; auto. 
        rewrite_env (nil ++ [(X, bind_kn K)] ++ E). 
        apply typing_weakening; auto.
          eapply wf_lenv_weakening; eauto.
            simpl_env. eapply wf_env_kn; eauto.
          rewrite_env (nil ++ [(X, bind_kn K)] ++ E). 
          apply wf_lenv_weakening; auto.
            simpl_env. apply wf_env_kn; auto.
Qed.
    
(* ********************************************************************** *)
(* ********************************************************************** *)
(** * Preservation *)

Lemma value_nonlin_inversion: forall E D e T,
  typing E D e T ->
  value e ->
  wf_typ E T kn_nonlin ->
  D = lempty.
Proof.
  intros E D e T Typ.
  (typing_cases (induction Typ) Case);  
    intros V WFT; 
    try solve [ auto | 
                inversion V |
                inversion WFT; subst; auto].
  Case "typing_tabs".
    inversion V; subst. 
    inversion WFT; subst.
    pick fresh X.
    apply (H1 X); auto.
Qed.

Lemma lenv_split_weakening_left: forall E D1L D1R D2L D2R D3L D3R x T,
  lenv_split E (D1L ++ D1R) (D2L ++ D2R) (D3L ++ D3R) ->
  lenv_split E D1L D2L D3L ->
  lenv_split E D1R D2R D3R ->
  wf_lenv E (D3L ++ [(x, lbind_typ T)] ++ D3R) ->
  lenv_split E (D1L ++ [(x, lbind_typ T)] ++ D1R) (D2L ++ D2R) (D3L ++ [(x, lbind_typ T)]++ D3R).
Proof.
  intros E D1L D1R D2L D2R D3L D3R x T S.
  remember (D1L ++ D1R) as D1.
  remember (D2L ++ D2R) as D2.
  remember (D3L ++ D3R) as D3.
  generalize dependent D1L. generalize dependent D1R.
  generalize dependent D2L. generalize dependent D2R.
  generalize dependent D3L. generalize dependent D3R.
  (lenv_split_cases (induction S) Case);
    intros D3R D3L EQ3 D2R D2L EQ2 D1R D1L EQ1 SL SR WFL; subst; simpl_env in *.
  Case "lenv_split_empty".
    destruct D3L; destruct D3R; inversion EQ3; subst; simpl_env.
    destruct D2L; destruct D2R; inversion EQ2; subst; simpl_env.
    destruct D1L; destruct D1R; inversion EQ1; subst; simpl_env.
    rewrite_env ([(x, lbind_typ T)] ++ nil).
    simpl_env in WFL. inversion WFL; subst.
    apply lenv_split_left; auto. 
  Case "lenv_split_left".
    destruct D3L; inversion EQ3.
    SCase "D3L=nil".
      destruct D1L; inversion EQ1.
      SSCase "D1L=nil".
        destruct D3R; simpl_env in EQ3; inversion EQ3.
        SSSCase "D3R=con".
          destruct D1R; simpl_env in EQ1; inversion EQ1.
          SSSSCase "D1R=con"; subst; simpl_env in *.
            inversion WFL; subst.
            apply lenv_split_left; auto.
      SSCase "D1L=con".
        inversion SL.
    SCase "D3L=con".
      destruct D1R; simpl_env in EQ1; inversion EQ1; subst.
      SSCase "D2R=nil".
        simpl_env in *. 
        inversion WFL; subst.
        apply lenv_split_left; auto.
          rewrite_env (D1 ++ [(x, lbind_typ T)] ++ nil).
          eapply IHS; auto.
          inversion SL; auto. subst.
          rewrite (dom_lenv_split E ([(x0, lbind_typ T0)] ++ D1) D2 D3L) in H0; auto.
          simpl in H0.
          assert False. fsetdec. tauto.
      SSCase "D2R=con".
        inversion SL; subst; simpl_env in *.
        SSSCase "SL1".
          inversion WFL; subst.
          apply lenv_split_left; auto. 
            eapply IHS; auto. 
              inversion EQ1; auto.
        SSSCase "SL2".
          assert (dom (D3L ++ D3R) [=] dom D3L `union` dom D3R) as J.
            rewrite dom_app; auto. fsetdec.
          rewrite <- J in H0.
          rewrite (dom_lenv_split E D1 ([(x0, lbind_typ T0)] ++ D2 ++ D2R) (D3L ++ D3R)) in H0; auto.
          simpl in H0; auto.
          assert False. fsetdec. tauto.
  Case "lenv_split_right".
    destruct D3L; inversion EQ3.
    SCase "D3L=nil".
      destruct D2L; inversion EQ2.
      SSCase "D2L=nil".
        destruct D3R; inversion EQ3.
        SSSCase "D3R=con".
          destruct D2R; inversion EQ2.
          SSSSCase "D2R=con"; subst; simpl_env in *.
            inversion SL; simpl_env in *.
            inversion WFL; subst.
            apply lenv_split_left; auto. 
      SSCase "D2L=con".
        inversion SL.
    SCase "D3L=con".
      subst. simpl_env in *.
      destruct D2L; inversion EQ2.
      SSCase "D2L=nil".
        destruct D2R; inversion EQ2.
        SSSCase "D2R=con".
          subst. simpl_env in *.
          rewrite (dom_lenv_split E D1R ([(x0, lbind_typ T0)] ++ D2R) D3R) in H0; auto.
          simpl in H0. 
          assert False. fsetdec. tauto.
      SSCase "D2L=con".
        inversion WFL; subst.
        apply lenv_split_right; subst; auto.  
          eapply IHS; auto.  
          inversion SL; subst; simpl_env in *.
          SSSCase "SL1".
            assert (dom (D3L ++ D3R) [=] dom D3L `union` dom D3R) as J.
              rewrite dom_app; fsetdec.
            rewrite <- J in H0.
            rewrite (dom_lenv_split E ([(x0, lbind_typ T0)] ++ D1 ++ D1R) 
               (D2L ++ D2R) (D3L ++ D3R)) in H0; auto.
            simpl in H0; auto.
            assert False. fsetdec. tauto.
          SSSCase "SL2".
            inversion WFL; auto.
Qed.
      
Lemma lenv_split_weakening_right: forall E D1L D1R D2L D2R D3L D3R x T,
  lenv_split E (D1L ++ D1R) (D2L ++ D2R) (D3L ++ D3R) ->
  lenv_split E D1L D2L D3L ->
  lenv_split E D1R D2R D3R ->
  wf_lenv E (D3L ++ [(x, lbind_typ T)] ++ D3R) ->
  lenv_split E (D1L ++ D1R) (D2L ++ [(x, lbind_typ T)] ++ D2R) (D3L ++ [(x, lbind_typ T)]++ D3R).
Proof.   
  intros. 
  apply lenv_split_commute. 
  apply lenv_split_weakening_left; try (apply lenv_split_commute; auto); auto.
Qed.

Lemma wf_lenv_lin_weakening: forall E D1 D2 x TX,
  wf_typ E TX kn_lin ->
  wf_lenv E (D1 ++ D2) ->
  x `notin` dom E ->
  x `notin` dom (D1 ++ D2) ->
  wf_lenv E (D1 ++ [(x, lbind_typ TX)] ++ D2).
Proof.
  intros E D1 D2 x TX WFT WFL.
  remember (D1 ++ D2) as D.
  generalize dependent D1. generalize dependent D2.
  (wf_lenv_cases (induction WFL) Case);
    intros D2 D1 EQ NIN1 NIN2.
  Case "wf_lenv_empty".
   destruct D1; destruct D2; inversion EQ; subst; simpl_env in *.
   rewrite_env ([(x, lbind_typ TX)] ++ nil).
   apply wf_lenv_typ; auto.
  Case "wf_lenv_typ".
    destruct D1; destruct D2; inversion EQ; subst; simpl_env in *.
    SCase "D1=nil, D2=con".
      apply wf_lenv_typ; auto. 
    SCase "D1=con, D2=nil".
      rewrite_env (D1 ++ [(x, lbind_typ TX)] ++ nil); auto.
    SCase "D1=con, D2=con".
      apply wf_lenv_typ; auto. 
Qed.

Lemma lenv_split_cases_app: forall E DL D1 D2 DR,
  lenv_split E D1 D2 (DL ++ DR) ->
  exists D1L, exists D1R, exists D2L, exists D2R,
    lenv_split E D1L D2L DL /\
    lenv_split E D1R D2R DR /\
    D1L ++ D1R = D1 /\
    D2L ++ D2R = D2.
Proof.
  intros E DL.
  induction DL; intros D1 D2 DR S.
  Case "empty".
    exists lempty. exists D1. exists lempty. exists D2.
    simpl_env in *; repeat split; auto. 
    apply lenv_split_empty.
      eapply wf_env_from_wf_lenv; eauto.
  Case "cons".
    destruct a. simpl_env in S.
    inversion S; subst.
    SCase "left".
      lapply (IHDL D0 D2 DR); auto.
      intros.
      destruct H as [D1L [D1R [D2L [D2R [S2 [S3 [Q1 Q2]]]]]]].
      exists ([(a, lbind_typ T)] ++ D1L).
      exists D1R.
      exists D2L.
      exists D2R.
      subst; simpl_env in *; repeat split; auto.
    SCase "right".
      lapply (IHDL D1 D3 DR); auto.
      intros.
      destruct H as [D1L [D1R [D2L [D2R [S2 [S3 [Q1 Q2]]]]]]].
      exists D1L.
      exists D1R.
      exists ([(a, lbind_typ T)] ++ D2L).
      exists D2R.
      subst; simpl_env in *; repeat split; auto.
Qed.

Lemma eq_kn_dec: forall (k1 k2:kn), {k1 = k2} + {~k1 = k2}.
Proof.
  decide equality.
Qed.

Lemma eq_typ_dec: forall (t1 t2:typ), {t1 = t2} + {~t1 = t2}.
Proof.
  decide equality. 
    apply eq_nat_dec.
    apply eq_kn_dec. 
    apply eq_kn_dec.
Qed.

Lemma eq_lbnd_dec: forall (a b:lbinding), {a = b}+{~a=b}.
Proof.
  decide equality. 
    apply eq_typ_dec.
Qed.
  
Lemma eq_lbinding_dec: forall (x y:(atom * lbinding)%type), {x = y}+{~x = y}.
Proof.
  decide equality.
    apply eq_lbnd_dec.
Qed.

Lemma lenv_split_permute: forall E D1 D2 D3,
  lenv_split E D1 D2 D3 ->
  permute D3 (D1 ++ D2).
Proof.
  intros E D1 D2 D3 S.
  (lenv_split_cases (induction S) Case); simpl_env; auto.
  Case "lenv_split_empty".
    apply permute_empty.
  Case "lenv_split_left".
    rewrite_env (lempty ++ [(x, lbind_typ T)] ++ (D1 ++ D2)).
    apply permute_cons; auto.
  Case "lenv_split_right".
    apply permute_cons; auto.
Qed.

Lemma lenv_split_exists_permute: forall E D1 D2 D3 DX,
  lenv_split E D1 D2 D3 ->
  permute D3 DX ->
  exists D1P, exists D2P,
    permute D1 D1P /\
    permute D2 D2P /\
    lenv_split E D1P D2P DX.
Proof.
  intros E D1 D2 D3 DX.
  intros S.
  generalize dependent DX.
  (lenv_split_cases (induction S) Case); 
    intros DX PERM; inversion PERM; subst.
  Case "lenv_split_empty".
    exists lempty. exists lempty.
    repeat split; try apply permute_empty; try apply lenv_split_empty. 
    auto.
  Case "lenv_split_left".
    lapply (IHS (DL ++ DR)); auto.
    intros EX.
    destruct EX as [D1P [D2P [PERM1 [PERM2 S2]]]].
    lapply (lenv_split_cases_app E DL D1P D2P DR); intros; auto.
    destruct H2 as [D1l [D1R [D2L [D2R [S3 [S4 [Q1 Q2]]]]]]]; subst.
    exists (D1l ++ [(x, lbind_typ T)] ++ D1R).
    exists (D2L ++ D2R).
    repeat split; auto.
      apply permute_cons. auto.
      apply lenv_split_weakening_left; auto.
        apply wf_lenv_lin_weakening; auto.
          rewrite (dom_permute _ D3 (DL ++ DR)) in H0; auto.
  Case "lenv_split_right".
    lapply (IHS (DL ++ DR)); auto.
    intros EX.
    destruct EX as [D1P [D2P [PERM1 [PERM2 S2]]]].
    lapply (lenv_split_cases_app E DL D1P D2P DR); intros; auto.
    destruct H2 as [D1l [D1R [D2L [D2R [S3 [S4 [Q1 Q2]]]]]]]; subst.
    exists (D1l ++ D1R).
    exists (D2L ++ [(x, lbind_typ T)] ++ D2R).
    repeat split; auto.
      apply permute_cons; auto.
      apply lenv_split_weakening_right; auto.
        apply wf_lenv_lin_weakening; auto. 
          rewrite (dom_permute _ D3 (DL ++ DR)) in H0; auto.
Qed.
    
Lemma typing_permute: forall E D1 D2 e t,
  typing E D1 e t ->
  permute D1 D2 ->
  typing E D2 e t.
Proof.
  intros E D1 D2 e t TYP PERM.
  generalize dependent D2.
  (typing_cases (induction TYP) Case); 
    intros DX PERM; eauto.
  Case "typing_var".
    inversion PERM; subst; auto.
  Case "typing_lvar".
    inversion PERM; subst.
    inversion H4; subst.
    destruct DL; destruct DR; subst; simpl_env in *;
      try solve [inversion H0].
      apply typing_lvar; auto.
  Case "typing_abs".
    pick fresh x and apply typing_abs; auto.
      intros. lapply H2; intros; auto. subst.
      inversion PERM; auto.
  Case "typing_labs".
    pick fresh x and apply typing_labs; auto.
      apply (H1 x); auto.
        rewrite_env (lempty ++ [(x, lbind_typ T1)] ++ DX).
        apply permute_cons; auto.

        intros. lapply H2; intros; auto. subst. 
        inversion PERM; auto.
  Case "typing_app".
    assert (exists D1P, exists D2P,
      permute D1 D1P /\
      permute D2 D2P /\
      lenv_split E D1P D2P DX) as J.
      eapply lenv_split_exists_permute; eauto.
    destruct J as [D1P [D2P [PERM2 [PERM3 S]]]].
    apply (typing_app T1 K E D1P D2P DX); auto.
  Case "typing_tabs".
    pick fresh X and apply typing_tabs; eauto.
Qed.

Lemma typing_split: forall E D3 e T D1 D2,
  typing E (D1 ++ D2) e T ->
  lenv_split E D1 D2 D3 ->
  typing E D3 e T.
Proof.
  intros.
  apply (typing_permute E (D1 ++ D2) D3); auto.
    apply permute_sym; eauto.
      apply eq_lbinding_dec.
      eapply lenv_split_permute; eauto.
Qed.
  
Lemma wf_lenv_split_both: forall E D1 D2 D3,
  lenv_split E D1 D2 D3 ->
  wf_lenv E (D1 ++ D2).
Proof.
  intros E D1 D2 D3 S.
  (lenv_split_cases (induction S) Case); simpl_env in *; auto.
  Case "lenv_split_left".
    apply wf_lenv_typ; auto. 
      rewrite (dom_lenv_split E D1 D2 D3) in H0; auto.
  Case "lenv_split_right".
    apply wf_lenv_lin_weakening; auto.
      rewrite (dom_lenv_split E D1 D2 D3) in H0; auto.
Qed.

Lemma subst_tlb_identity: forall D X T,
  X `notin` fv_lenv D ->
  D = (map (subst_tlb X T) D).
Proof.
  intros D X T H. 
  induction D; simpl; auto.
  Case "D=con".
    destruct a. destruct l.
    simpl; simpl in H. 
    rewrite <- IHD; auto.
    rewrite <- subst_tt_fresh; auto.
Qed.

Lemma preservation : forall E D e e' T,
  typing E D e T ->
  red e e' ->
  typing E D e' T.
Proof with simpl_env; eauto.
  intros E D e e' T Typ. 
  generalize dependent e'.
  (typing_cases (induction Typ) Case); 
    intros e' Red; try solve [ inversion Red; subst; eauto ].
  Case "typing_app".
    inversion Red; subst...
    inversion Typ1; subst.
    SCase "typing_abs".
      pick fresh x.
      rewrite (subst_ee_intro x); auto.
      assert (D2 = lempty) as J.
        apply (value_nonlin_inversion E D2 e2 T1); auto.
      subst D2.
      lapply (H11 x); auto.
        intros H0.
        assert (D1 = D3) as J.
          apply (lenv_split_empty_right E D1 D3); auto. 
        subst D1.
        rewrite_env (nil ++ E).
        eapply typing_through_subst_ee_nonlin; eauto. 
    SCase "typing_labs".
      pick fresh x.
      rewrite (subst_ee_intro x); auto.
      apply (typing_split E D3 (subst_ee x e2 (open_ee e0 x)) T2 D2 D1); auto.
        rewrite_env (lempty ++ D2 ++ D1).
        apply (typing_through_subst_ee_lin E lempty x T1 D1); simpl_env; auto.
          eapply wf_lenv_split_both. 
            eapply lenv_split_commute; eauto.
          apply lenv_split_commute; auto.
  Case "typing_tapp".
    inversion Red; subst...
    inversion Typ. subst.
    pick fresh X.
    lapply (H9 X); auto.
      intros.
      rewrite (subst_te_intro X)...
      rewrite (subst_tt_intro X)...
      rewrite_env (map (subst_tb X T) nil ++ E).
      rewrite (subst_tlb_identity D X T); auto.
      apply (typing_through_subst_te K)...
  Case "typing_fst".
    inversion Red; subst...
    inversion Typ; subst...
  Case "typing_snd".
    inversion Red; subst...
    inversion Typ; subst...
Qed.

(* ********************************************************************** *)
(** * Canonical forms *)

Lemma canonical_form_abs : forall e K U1 U2,
  value e ->
  typing nil lempty e (typ_arrow K U1 U2) ->
  exists K1, exists V, exists e1, (e = exp_abs K1 V e1) /\ (K = kn_nonlin -> K1 = kn_nonlin).
Proof.
  intros e K U1 U2 Val Typ.
  remember LinF_Definitions.empty as E.
  remember lempty as D.
  remember (typ_arrow K U1 U2) as T.
  revert U1 U2 HeqT HeqE HeqD.
  (typing_cases (induction Typ) Case); 
    intros U1 U2 EQT EQE EQD; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
  Case "typing_abs".
    inversion EQT. subst. 
    exists K. exists U1. exists e1. tauto.
  Case "typing_labs".
    inversion EQT. subst. 
    exists K. exists U1. exists e1. tauto.
Qed.

Lemma canonical_form_tabs : forall e Q U1,
  value e ->
  typing nil lempty e (typ_all Q U1) ->
  exists V, exists e1, e = exp_tabs V e1.
Proof.
  intros e Q U1 Val Typ.
  remember LinF_Definitions.empty as E.
  remember (typ_all Q U1) as T.
  revert Q U1 HeqT HeqE.
  (typing_cases (induction Typ) Case); 
    intros Q U1 EQT EQE; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
Qed.

Lemma canonical_form_with : forall e U1 U2,
  value e ->
  typing nil lempty e (typ_with U1 U2) ->
  exists e1, exists e2, e = exp_apair e1 e2.
Proof.
  intros e U1 U2 Val Typ.
  remember LinF_Definitions.empty as E.
  remember (typ_with U1 U2) as T.
  revert U1 U2 HeqT HeqE.
  (typing_cases (induction Typ) Case); 
    intros U1 U2 EQT EQE; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
Qed.

(* ********************************************************************** *)
(** * Progress *)

Lemma progress : forall e T,
  typing nil lempty e T ->
  value e \/ exists e', red e e'.
Proof with eauto.
  intros e T Typ.
  remember LinF_Definitions.empty as E.
  remember lempty as D. generalize dependent HeqE.
  generalize dependent HeqD.
  assert (Typ' : typing E D e T)...
  (typing_cases (induction Typ) Case); intros EQD EQE; subst...
  Case "typing_var".
    inversion H0.
  Case "typing_lvar".
    inversion EQD.
  Case "typing_app".
    right.
    inversion H; subst.
    destruct IHTyp1 as [Val1 | [e1' Rede1']]...
    SCase "Val1".
      destruct IHTyp2 as [Val2 | [e2' Rede2']]...
      SSCase "Val2".
        destruct (canonical_form_abs _ _ _ _ Val1 Typ1) as [K1 [S [e3 [EQE EQK]]]]; subst.
        exists (open_ee e3 e2)...
  Case "typing_tapp".
    right.
    destruct IHTyp as [Val1 | [e1' Rede1']]...
    SCase "Val1".
      destruct (canonical_form_tabs _ _ _ Val1 Typ) as [S [e3 EQ]]; subst.
      exists (open_te e3 T)...
      apply red_tabs; eauto using type_from_wf_typ.
    SCase "e1' Rede1'".
      exists (exp_tapp e1' T)...
      apply red_tapp; eauto using type_from_wf_typ.
  Case "typing_fst".
    right.
    destruct IHTyp as [Val | [e' Rede']]...
    SCase "Val".
      destruct (canonical_form_with _ _ _ Val Typ) as [e1 [e2 EQE]]; subst.
      apply value_regular in Val. inversion Val; subst.
      exists e1...
  Case "typing_snd".
    right.
    destruct IHTyp as [Val | [e' Rede']]...
    SCase "Val".
      destruct (canonical_form_with _ _ _ Val Typ) as [e1 [e2 EQE]]; subst.
      apply value_regular in Val. inversion Val; subst.
      exists e2...
Qed.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../../../metatheory") ***
*** End: ***
 *)
