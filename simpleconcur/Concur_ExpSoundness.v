(** Substitution and preservation for expressions. *)

Require Export Concur_Regularity.

(************************************************************************ *)
(** ** Type substitution preserves typing (11) *)
    
Lemma value_through_subst_ce : forall e Z C,
  channel C ->
  value e ->
  value (subst_ce Z C e).
Proof.
  intros e Z C Chan H.
  (value_cases (induction H) Case); simpl; auto using subst_ce_expr;
  try solve [ inversion H; repeat constructor; auto using subst_ce_expr ].
  Case "value_abs".
    assert (expr (subst_ce Z C (exp_abs T e1))) as J.
      apply subst_ce_expr; auto.
    apply value_abs; auto.
Qed.

(* Not true as stated, but I don't think we need this...
Lemma typing_through_subst_ce : forall E D1 D2 Z b e T W,
  typing E (D1 ++ [(Z, b)] ++ D2) e T ->
  wf_lenv E (D1 ++ [(W, b)] ++ D2) ->
  typing E (D1 ++ [(W, b)] ++ D2) (subst_ce Z (fchan W) e) T.
Proof with simpl_env;
           eauto 6.
  intros E D1 D2 Z b e T W Typ Wfe.
  remember (D1 ++ [(Z, b)] ++ D2) as D.
  generalize dependent D2. generalize dependent D1.
  (typing_cases (induction Typ) Case); intros D01 D02 EQ WFE; subst;
    simpl subst_ce in *; simpl subst_cc in *...
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
      apply value_through_subst_te; auto.
        eapply type_from_wf_typ; eauto.
      rewrite subst_te_open_te_var; eauto using type_from_wf_typ.
      rewrite subst_tt_open_tt_var; eauto using type_from_wf_typ.
      rewrite_env (map (subst_tb Z P) ([(Y, bind_kn K0)] ++ F) ++ E0); eauto.
  Case "typing_tapp".
    rewrite subst_tt_open_tt... 
      eapply type_from_wf_typ; eauto.
Qed.
*)

(************************************************************************ *)
(** ** Substitution preserves typing (8) *)

Lemma value_through_open_ce: forall e1 C,
  value e1 ->
  value (open_ce e1 C).
Proof.
  intros e1 C H.
  unfold open_ce. 
  rewrite <- open_ce_rec_expr; auto.
Qed.

(*Lemma snk_fv: forall E T C e x,
  snk E T C e ->
  x `notin` fv_ee e.
Proof with auto.
  intros E T C e x Snk.
  induction Snk; simpl...
Qed.

Lemma src_fv: forall E T C e x,
  src E T C e ->
  x `notin` fv_ee e.
Proof with auto.
  intros E T C e x Src.
  induction Src; simpl...
Qed.*)

Lemma typing_fv: forall E D Q e T x,
  typing E D Q e T ->
  x `notin` dom E ->
  x `notin` dom D ->
  x `notin` dom Q ->
  x `notin` fv_ee e.
Proof.
  intros E D Q e T x H.
  (typing_cases (induction H) Case); intros NIE NID NIQ; simpl; auto.
  Case "typing_seq".
    assert (x `notin` fv_ee e1) as J1. 
      apply IHtyping1; auto.
        rewrite (dom_lenv_split E Q3 D1 D2 D3) in NID; auto.
        rewrite (dom_cenv_split_exp E Q1 Q2 Q3) in NIQ; auto.
    assert (x `notin` fv_ee e2) as J2. 
      apply IHtyping2; auto.
        rewrite (dom_lenv_split E Q3 D1 D2 D3) in NID; auto.
        rewrite (dom_cenv_split_exp E Q1 Q2 Q3) in NIQ; auto.
    fsetdec.
  Case "typing_abs".
    pick fresh y. 
    lapply (H1 y); intros; auto.
    simpl in H2. unfold not. intros. apply H2; auto.
    assert (x `notin` singleton y) as J. destruct_notin; auto.
    unfold open_ee. apply fv_in_open_ee; auto.
  Case "typing_app".
    assert (x `notin` fv_ee e1) as J1. 
      apply IHtyping1; auto.
        rewrite (dom_lenv_split E Q3 D1 D2 D3) in NID; auto.
        rewrite (dom_cenv_split_exp E Q1 Q2 Q3) in NIQ; auto.
    assert (x `notin` fv_ee e2) as J2. 
      apply IHtyping2; auto.
        rewrite (dom_lenv_split E Q3 D1 D2 D3) in NID; auto.
        rewrite (dom_cenv_split_exp E Q1 Q2 Q3) in NIQ; auto.
    fsetdec.
  Case "typing_mpair".
    assert (x `notin` fv_ee e1) as J1. 
      apply IHtyping1; auto.
        rewrite (dom_lenv_split E Q3 D1 D2 D3) in NID; auto.
        rewrite (dom_cenv_split_exp E Q1 Q2 Q3) in NIQ; auto.
    assert (x `notin` fv_ee e2) as J2. 
      apply IHtyping2; auto.
        rewrite (dom_lenv_split E Q3 D1 D2 D3) in NID; auto.
        rewrite (dom_cenv_split_exp E Q1 Q2 Q3) in NIQ; auto.
    fsetdec.
  Case "typing_let".
    assert (x `notin` fv_ee e1) as J1. 
      apply IHtyping1; auto.
        rewrite (dom_lenv_split E Q3 D1 D2 D3) in NID; auto.
        rewrite (dom_cenv_split_exp E Q1 Q2 Q3) in NIQ; auto.
    assert (x `notin` fv_ee e2) as J2. 
      apply IHtyping2; auto.
        rewrite (dom_lenv_split E Q3 D1 D2 D3) in NID; auto.
        rewrite (dom_cenv_split_exp E Q1 Q2 Q3) in NIQ; auto.
    fsetdec.
  Case "typing_case".
    assert (x `notin` fv_ee e1) as J1. 
      apply IHtyping1; auto.
        rewrite (dom_lenv_split E Q3 D1 D2 D3) in NID; auto.
        rewrite (dom_cenv_split_exp E Q1 Q2 Q3) in NIQ; auto.
    assert (x `notin` fv_ee e2) as J2. 
      apply IHtyping2; auto.
        rewrite (dom_lenv_split E Q3 D1 D2 D3) in NID; auto.
        rewrite (dom_cenv_split_exp E Q1 Q2 Q3) in NIQ; auto.
    assert (x `notin` fv_ee e3) as J3. 
      apply IHtyping3; auto.
        rewrite (dom_lenv_split E Q3 D1 D2 D3) in NID; auto.
        rewrite (dom_cenv_split_exp E Q1 Q2 Q3) in NIQ; auto.
    fsetdec.
Qed.

Lemma non_subst: forall E D Q e T x u,
  typing E D Q e T ->
  x `notin` dom E ->
  x `notin` dom D ->
  x `notin` dom Q ->
  e = subst_ee x u e.
Proof.
  intros E D Q e T x y H1 H2 H3 H4.
  apply subst_ee_fresh.
  eapply typing_fv; eauto.
Qed.

(* Lemma lenv_split_strengthening: forall G2 G1 x T D1 D2 D3,
  lenv_split (G2 ++ [(x, bind_typ T)] ++ G1) D1 D2 D3 ->
  lenv_split (G2 ++ G1) D1 D2 D3.
Proof.
  intros G2 G1 x D1 D2 D3 S.
  remember (G2 ++ [(x, bind_typ T)] ++ G1) as G.
  generalize dependent G1. generalize dependent G2.
  (lenv_split_cases (induction S) Case); 
    intros G2 G1 EQ; simpl_env in *; subst; auto.
  Case "lenv_split_empty".
    apply lenv_split_empty. 
      eapply wf_env_strengthening; eauto.
Qed.*)

Lemma value_through_subst_ee: forall e1 x u,
  expr u ->
  value e1 ->
  value (subst_ee x u e1).
Proof.
  intros e1 x u EX V.
  (value_cases (induction V) Case); simpl; auto;
  try solve [ inversion H; repeat constructor; auto ].
  Case "value_abs".
    inversion H; subst.
    apply value_abs. 
      pick fresh z and apply expr_abs; auto.
        rewrite subst_ee_open_ee_var; auto.
Qed.

(*Lemma typing_through_subst_ee_nonlin: forall G2 G1 x U0 D e T u,
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
      apply value_through_subst_ee; auto.

      rewrite_env (([(X, bind_kn K)] ++ G2) ++ G1).
      rewrite subst_ee_open_te_var; eauto.
  Case "typing_tapp".
    eapply typing_tapp. eapply IHTyp; auto.
    eapply wf_typ_strengthening; eauto.
Qed.*)

Lemma lenv_split_sub_left: forall E Q D1L D1R D2 DL DR x U F,
   lenv_split E Q
        (D1L ++ [(x, lbind_typ U)] ++ D1R) 
        D2 
        (DL ++ [(x, lbind_typ U)] ++ DR) ->
   vwf_envs E Q (DL ++ F ++ DR) ->
   lenv_split E Q
        (D1L ++ F ++ D1R) 
        D2
        (DL ++ F ++ DR).
Proof.
  intros E Q D1L D1R D2 DL DR x U F S.
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
        rewrite (dom_lenv_split E Q (D1L ++ [(x, lbind_typ U)] ++ D1R) D2 DR)
            in H1; auto.
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
      rewrite (dom_lenv_split E Q (D1L ++ [(x, lbind_typ U)] ++ D1R) D2 DR)
          in H1; auto.
        simpl_env in *. 
        assert False. fsetdec. 
        tauto.
    SCase "con".
      inversion WFL; subst.
      apply lenv_split_right; auto.
Qed.

Lemma lenv_split_sub_right: forall E Q D1 D2L D2R DL DR x U F,
   lenv_split E Q
        D1
        (D2L ++ [(x, lbind_typ U)] ++ D2R) 
        (DL ++ [(x, lbind_typ U)] ++ DR) ->
   vwf_envs E Q (DL ++ F ++ DR) ->
   lenv_split E Q
        D1
        (D2L ++ F ++ D2R) 
        (DL ++ F ++ DR).
Proof.
  intros.
  apply lenv_split_commute. 
  eapply lenv_split_sub_left; eauto.
    apply lenv_split_commute; eauto.
Qed.

(*Lemma covers_trans: forall d1 d2 d3,
  covers d1 d2 ->
  covers d2 d3 ->
  covers d1 d3.
Proof with auto.
  intros. inversion H; subst...
Qed.*)

Lemma typing_through_subst_ee_lin: forall G D2 x U D1 Q Q' Q'' e T F u,
  typing G (D2 ++ [(x, lbind_typ U)] ++ D1) Q e T ->
  typing G F Q' u U ->
  vwf_envs G Q'' (D2 ++ F ++ D1) ->
  cenv_split_exp G Q Q' Q'' ->
  typing G (D2 ++ F ++ D1) Q'' (subst_ee x u e) T.
Proof.
  intros G D2 x U D1 Q Q' Q'' e T F u TYP.
  remember (D2 ++ [(x, lbind_typ U)] ++ D1) as D.
  generalize dependent D2. generalize dependent D1.
  generalize dependent Q''. generalize dependent Q'.
  (typing_cases (induction TYP) Case);  
    intros Q' Q'' DR DL EQ TYPU VWF CS; subst; simpl_env in *; simpl; eauto.
  Case "typing_var".
    destruct DL; inversion EQ; subst. 
    SCase "DL=nil".
      simpl_env in *. simpl.
     (* WEIRD BUG: if assert/apply/subst replaced by rewrite *)
      assert (Q' = Q'').
        apply cenv_split_exp_empty_left with (G := E); auto.
      subst. destruct (x == x); tauto.
    SCase "DL=con".
      destruct DL; inversion EQ.
  Case "typing_unit".
    absurd (lempty = DL ++ [(x, lbind_typ U)] ++ DR); auto.
  Case "typing_seq".
    lapply (lenv_split_cases_mid E Q3 D1 D2 DL x U DR); auto.
    intros C.
    destruct C as [LEFT | RIGHT].
    SCase "left".
      destruct LEFT as [D1L [D1R [D2L [D2R [EQ1 [EQ2 [S1 S2]]]]]]]; subst.
      assert (exists Q0, cenv_split_exp E Q1 Q' Q0 /\ cenv_split_exp E Q2 Q0 Q'').
        apply cenv_split_exp_commute in H0.
        apply cenv_split_exp_assoc with (Q13 := Q3); auto.
      destruct H1 as [Q0 [H1 H2]].
      apply cenv_split_exp_commute in H2.
      lapply (IHTYP1 Q' Q0 D1R D1L); auto.
      intros I. 
      assert (x `notin` (dom (D2L++D2R) `union` dom E `union` dom Q3)) as J.
        eapply lenv_split_not_in_left; eauto.
          simpl_env. fsetdec.
      lapply I; auto. intros TYPE1.
      rewrite <- (non_subst E (D2L++D2R) Q2 e2 T2 x u); auto.
        apply (typing_seq E (D1L ++ F ++ D1R) (D2L ++ D2R))
          with (Q1 := Q0) (Q2 := Q2); auto.
          assert (vwf_envs E Q3 (D1L ++ F ++ D1R)) as JJ.
            eapply wf_lenv_split_left.
              eapply lenv_split_sub_left; eauto.
              eapply vwf_envs_strengthen_cenv_left; eauto.
              apply cenv_split_exp_proc; eauto.
          apply TYPE1; auto. apply vwf_envs_pack.
            apply vwf_envs_unpack in JJ; intuition...
            eapply wf_cenv_split_exp; eauto.
            apply vwf_envs_unpack in VWF. destruct VWF as [WFL [WFC DJ]].
            (*apply dom_cenv_split_exp in H1.*) apply dom_cenv_split_exp in H2.
            apply dom_lenv_split in S1. apply dom_lenv_split in S2.
            unfold disjoint in *. simpl_env in *. 
            clear - DJ S1 S2 H2. fsetdec.
          apply lenv_split_disjoint_cenv with (Q := Q3); auto.
            eapply lenv_split_sub_left; eauto.
            apply vwf_envs_unpack in VWF. destruct VWF as [WFL [WFC DJ]].
            apply vwf_envs_pack; auto.
            apply dom_cenv_split_exp in CS.
            apply dom_lenv_split in S1. apply dom_lenv_split in S2.
            unfold disjoint in *. simpl_env in *.
            clear - DJ S1 S2 CS. fsetdec.
          apply dom_cenv_split_exp in H0. fsetdec.
    SCase "right".
      destruct RIGHT as [D1L [D1R [D2L [D2R [EQ1 [EQ2 [S1 S2]]]]]]]; subst.
      assert (exists Q0, cenv_split_exp E Q2 Q' Q0 /\ cenv_split_exp E Q1 Q0 Q'').
        apply cenv_split_exp_assoc with (Q13 := Q3); auto.
      destruct H1 as [Q0 [H1 H2]].
      lapply (IHTYP2 Q' Q0 D2R D2L); auto. 
      intros I.
      assert (x `notin` (dom (D1L++D1R) `union` dom E `union` dom Q3)) as J.
        eapply lenv_split_not_in_right; eauto.
          simpl_env. fsetdec.
      lapply I; auto. intros TYPE2.
      rewrite <- (non_subst E (D1L ++ D1R) Q1 e1 typ_unit x u); auto.
        apply (typing_seq E (D1L ++ D1R) (D2L ++ F ++ D2R))
          with (Q1 := Q1) (Q2 := Q0); auto.
          assert (vwf_envs E Q3 (D2L ++ F ++ D2R)) as JJ.
            eapply wf_lenv_split_right. 
              eapply lenv_split_sub_right; eauto.
              eapply vwf_envs_strengthen_cenv_left; eauto.
              apply cenv_split_exp_proc; eauto.
          apply TYPE2; auto. apply vwf_envs_pack.
            apply vwf_envs_unpack in JJ; intuition...
            eapply wf_cenv_split_exp; eauto.
            apply vwf_envs_unpack in VWF. destruct VWF as [WFL [WFC DJ]].
            (*apply dom_cenv_split_exp in H1.*) apply dom_cenv_split_exp in H2.
            apply dom_lenv_split in S1. apply dom_lenv_split in S2.
            unfold disjoint in *. simpl_env in *. 
            clear - DJ S1 S2 H2. fsetdec.
          apply lenv_split_disjoint_cenv with (Q := Q3); auto.
            eapply lenv_split_sub_right; eauto.
            apply vwf_envs_unpack in VWF. destruct VWF as [WFL [WFC DJ]].
            apply vwf_envs_pack; auto.
            apply dom_cenv_split_exp in CS.
            apply dom_lenv_split in S1. apply dom_lenv_split in S2.
            unfold disjoint in *. simpl_env in *.
            clear - DJ S1 S2 CS. fsetdec.
          apply dom_cenv_split_exp in H0. fsetdec.
  Case "typing_abs".
    pick fresh y and apply typing_abs; auto.
      rewrite_env (([(y, lbind_typ T1)] ++ DL) ++ F ++ DR).
      rewrite subst_ee_open_ee_var; auto.
      apply H1 with (Q' := Q'); simpl_env; auto.
  Case "typing_app".
    lapply (lenv_split_cases_mid E Q3 D1 D2 DL x U DR); auto.
    intros C.
    destruct C as [LEFT | RIGHT].
    SCase "left".
      destruct LEFT as [D1L [D1R [D2L [D2R [EQ1 [EQ2 [S1 S2]]]]]]]; subst.
      assert (exists Q0, cenv_split_exp E Q1 Q' Q0 /\ cenv_split_exp E Q2 Q0 Q'').
        apply cenv_split_exp_commute in H0.
        apply cenv_split_exp_assoc with (Q13 := Q3); auto.
      destruct H1 as [Q0 [H1 H2]].
      apply cenv_split_exp_commute in H2.
      lapply (IHTYP1 Q' Q0 D1R D1L); auto.
      intros I. 
      assert (x `notin` (dom (D2L++D2R) `union` dom E `union` dom Q3)) as J.
        eapply lenv_split_not_in_left; eauto.
        simpl_env. fsetdec.
      lapply I; auto. intros TYPE1. 
      rewrite <- (non_subst E (D2L++D2R) Q2 e2 T1 x u); auto.
        apply (typing_app T1 E (D1L ++ F ++ D1R) (D2L ++ D2R))
          with (Q1 := Q0) (Q2 := Q2); auto.
          assert (vwf_envs E Q3 (D1L ++ F ++ D1R)) as JJ.
            eapply wf_lenv_split_left.
              eapply lenv_split_sub_left; eauto.
              eapply vwf_envs_strengthen_cenv_left; eauto.
              apply cenv_split_exp_proc; eauto.
          apply TYPE1; auto. apply vwf_envs_pack.
            apply vwf_envs_unpack in JJ; intuition...
            eapply wf_cenv_split_exp; eauto.
            apply vwf_envs_unpack in VWF. destruct VWF as [WFL [WFC DJ]].
            (*apply dom_cenv_split_exp in H1.*) apply dom_cenv_split_exp in H2.
            apply dom_lenv_split in S1. apply dom_lenv_split in S2.
            unfold disjoint in *. simpl_env in *. 
            clear - DJ S1 S2 H2. fsetdec.
          apply lenv_split_disjoint_cenv with (Q := Q3); auto.
            eapply lenv_split_sub_left; eauto.
            apply vwf_envs_unpack in VWF. destruct VWF as [WFL [WFC DJ]].
            apply vwf_envs_pack; auto.
            apply dom_cenv_split_exp in CS.
            apply dom_lenv_split in S1. apply dom_lenv_split in S2.
            unfold disjoint in *. simpl_env in *.
            clear - DJ S1 S2 CS. fsetdec.
          apply dom_cenv_split_exp in H0. fsetdec.
    SCase "right".
      destruct RIGHT as [D1L [D1R [D2L [D2R [EQ1 [EQ2 [S1 S2]]]]]]]; subst.
      assert (exists Q0, cenv_split_exp E Q2 Q' Q0 /\ cenv_split_exp E Q1 Q0 Q'').
        apply cenv_split_exp_assoc with (Q13 := Q3); auto.
      destruct H1 as [Q0 [H1 H2]].
      lapply (IHTYP2 Q' Q0 D2R D2L); auto. 
      intros I.
      assert (x `notin` (dom (D1L++D1R) `union` dom E `union` dom Q3)) as J.
        eapply lenv_split_not_in_right; eauto.
        simpl_env. fsetdec.
      lapply I; auto. intros TYPE2.
      rewrite <- (non_subst E (D1L ++ D1R) Q1 e1 (typ_arrow T1 T2) x u); auto.
        apply (typing_app T1 E (D1L ++ D1R) (D2L ++ F ++ D2R))
          with (Q1 := Q1) (Q2 := Q0); auto.
          assert (vwf_envs E Q3 (D2L ++ F ++ D2R)) as JJ.
            eapply wf_lenv_split_right. 
              eapply lenv_split_sub_right; eauto.
              eapply vwf_envs_strengthen_cenv_left; eauto.
              apply cenv_split_exp_proc; eauto.
          apply TYPE2; auto. apply vwf_envs_pack.
            apply vwf_envs_unpack in JJ; intuition...
            eapply wf_cenv_split_exp; eauto.
            apply vwf_envs_unpack in VWF. destruct VWF as [WFL [WFC DJ]].
            (*apply dom_cenv_split_exp in H1.*) apply dom_cenv_split_exp in H2.
            apply dom_lenv_split in S1. apply dom_lenv_split in S2.
            unfold disjoint in *. simpl_env in *. 
            clear - DJ S1 S2 H2. fsetdec.
          apply lenv_split_disjoint_cenv with (Q := Q3); auto.
            eapply lenv_split_sub_right; eauto.
            apply vwf_envs_unpack in VWF. destruct VWF as [WFL [WFC DJ]].
            apply vwf_envs_pack; auto.
            apply dom_cenv_split_exp in CS.
            apply dom_lenv_split in S1. apply dom_lenv_split in S2.
            unfold disjoint in *. simpl_env in *.
            clear - DJ S1 S2 CS. fsetdec.
          apply dom_cenv_split_exp in H0. fsetdec.
  Case "typing_mpair".
    lapply (lenv_split_cases_mid E Q3 D1 D2 DL x U DR); auto.
    intros C.
    destruct C as [LEFT | RIGHT].
    SCase "left".
      destruct LEFT as [D1L [D1R [D2L [D2R [EQ1 [EQ2 [S1 S2]]]]]]]; subst.
      assert (exists Q0, cenv_split_exp E Q1 Q' Q0 /\ cenv_split_exp E Q2 Q0 Q'').
        apply cenv_split_exp_commute in H0.
        apply cenv_split_exp_assoc with (Q13 := Q3); auto.
      destruct H1 as [Q0 [H1 H2]].
      apply cenv_split_exp_commute in H2.
      lapply (IHTYP1 Q' Q0 D1R D1L); auto.
      intros I. 
      assert (x `notin` (dom (D2L++D2R) `union` dom E `union` dom Q3)) as J.
        eapply lenv_split_not_in_left; eauto.
        simpl_env. fsetdec.
      lapply I; auto. intros TYPE1. 
      rewrite <- (non_subst E (D2L++D2R) Q2 e2 T2 x u); auto.
        apply (typing_mpair E (D1L ++ F ++ D1R) (D2L ++ D2R))
          with (Q1 := Q0) (Q2 := Q2); auto.
          assert (vwf_envs E Q3 (D1L ++ F ++ D1R)) as JJ.
            eapply wf_lenv_split_left.
              eapply lenv_split_sub_left; eauto.
              eapply vwf_envs_strengthen_cenv_left; eauto.
              apply cenv_split_exp_proc; eauto.
          apply TYPE1; auto. apply vwf_envs_pack.
            apply vwf_envs_unpack in JJ; intuition...
            eapply wf_cenv_split_exp; eauto.
            apply vwf_envs_unpack in VWF. destruct VWF as [WFL [WFC DJ]].
            (*apply dom_cenv_split_exp in H1.*) apply dom_cenv_split_exp in H2.
            apply dom_lenv_split in S1. apply dom_lenv_split in S2.
            unfold disjoint in *. simpl_env in *. 
            clear - DJ S1 S2 H2. fsetdec.
          apply lenv_split_disjoint_cenv with (Q := Q3); auto.
            eapply lenv_split_sub_left; eauto.
            apply vwf_envs_unpack in VWF. destruct VWF as [WFL [WFC DJ]].
            apply vwf_envs_pack; auto.
            apply dom_cenv_split_exp in CS.
            apply dom_lenv_split in S1. apply dom_lenv_split in S2.
            unfold disjoint in *. simpl_env in *.
            clear - DJ S1 S2 CS. fsetdec.
          apply dom_cenv_split_exp in H0. fsetdec.
    SCase "right".
      destruct RIGHT as [D1L [D1R [D2L [D2R [EQ1 [EQ2 [S1 S2]]]]]]]; subst.
      assert (exists Q0, cenv_split_exp E Q2 Q' Q0 /\ cenv_split_exp E Q1 Q0 Q'').
        apply cenv_split_exp_assoc with (Q13 := Q3); auto.
      destruct H1 as [Q0 [H1 H2]].
      lapply (IHTYP2 Q' Q0 D2R D2L); auto. 
      intros I.
      assert (x `notin` (dom (D1L++D1R) `union` dom E `union` dom Q3)) as J.
        eapply lenv_split_not_in_right; eauto.
        simpl_env. fsetdec.
      lapply I; auto. intros TYPE2. 
      rewrite <- (non_subst E (D1L ++ D1R) Q1 e1 T1 x u); auto.
        apply (typing_mpair E (D1L ++ D1R) (D2L ++ F ++ D2R))
          with (Q1 := Q1) (Q2 := Q0); auto.
          assert (vwf_envs E Q3 (D2L ++ F ++ D2R)) as JJ.
            eapply wf_lenv_split_right. 
              eapply lenv_split_sub_right; eauto.
              eapply vwf_envs_strengthen_cenv_left; eauto.
              apply cenv_split_exp_proc; eauto.
          apply TYPE2; auto. apply vwf_envs_pack.
            apply vwf_envs_unpack in JJ; intuition...
            eapply wf_cenv_split_exp; eauto.
            apply vwf_envs_unpack in VWF. destruct VWF as [WFL [WFC DJ]].
            (*apply dom_cenv_split_exp in H1.*) apply dom_cenv_split_exp in H2.
            apply dom_lenv_split in S1. apply dom_lenv_split in S2.
            unfold disjoint in *. simpl_env in *. 
            clear - DJ S1 S2 H2. fsetdec.
          apply lenv_split_disjoint_cenv with (Q := Q3); auto.
            eapply lenv_split_sub_right; eauto.
            apply vwf_envs_unpack in VWF. destruct VWF as [WFL [WFC DJ]].
            apply vwf_envs_pack; auto.
            apply dom_cenv_split_exp in CS.
            apply dom_lenv_split in S1. apply dom_lenv_split in S2.
            unfold disjoint in *. simpl_env in *.
            clear - DJ S1 S2 CS. fsetdec.
          apply dom_cenv_split_exp in H0. fsetdec.
  Case "typing_let".
    lapply (lenv_split_cases_mid E Q3 D1 D2 DL x U DR); auto.
    intros C.
    destruct C as [LEFT | RIGHT].
    SCase "left".
      destruct LEFT as [D1L [D1R [D2L [D2R [EQ1 [EQ2 [S1 S2]]]]]]]; subst.
      assert (exists Q0, cenv_split_exp E Q1 Q' Q0 /\ cenv_split_exp E Q2 Q0 Q'').
        apply cenv_split_exp_commute in H0.
        apply cenv_split_exp_assoc with (Q13 := Q3); auto.
      destruct H1 as [Q0 [H1 H2]].
      apply cenv_split_exp_commute in H2.
      lapply (IHTYP1 Q' Q0 D1R D1L); auto.
      intros I. 
      assert (x `notin` (dom (D2L++D2R) `union` dom E `union` dom Q3)) as J.
        eapply lenv_split_not_in_left; eauto.
        simpl_env. fsetdec.
      lapply I; auto. intros TYPE1. 
      rewrite <- (non_subst E (D2L++D2R) Q2 e2 (typ_arrow T1 (typ_arrow T2 T3)) x u); auto.
        apply (typing_let E (D1L ++ F ++ D1R) (D2L ++ D2R))
          with (T1 := T1) (T2 := T2) (Q1 := Q0) (Q2 := Q2); auto.
          assert (vwf_envs E Q3 (D1L ++ F ++ D1R)) as JJ.
            eapply wf_lenv_split_left.
              eapply lenv_split_sub_left; eauto.
              eapply vwf_envs_strengthen_cenv_left; eauto.
              apply cenv_split_exp_proc; eauto.
          apply TYPE1; auto. apply vwf_envs_pack.
            apply vwf_envs_unpack in JJ; intuition...
            eapply wf_cenv_split_exp; eauto.
            apply vwf_envs_unpack in VWF. destruct VWF as [WFL [WFC DJ]].
            (*apply dom_cenv_split_exp in H1.*) apply dom_cenv_split_exp in H2.
            apply dom_lenv_split in S1. apply dom_lenv_split in S2.
            unfold disjoint in *. simpl_env in *. 
            clear - DJ S1 S2 H2. fsetdec.
          apply lenv_split_disjoint_cenv with (Q := Q3); auto.
            eapply lenv_split_sub_left; eauto.
            apply vwf_envs_unpack in VWF. destruct VWF as [WFL [WFC DJ]].
            apply vwf_envs_pack; auto.
            apply dom_cenv_split_exp in CS.
            apply dom_lenv_split in S1. apply dom_lenv_split in S2.
            unfold disjoint in *. simpl_env in *.
            clear - DJ S1 S2 CS. fsetdec.
          apply dom_cenv_split_exp in H0. fsetdec.
    SCase "right".
      destruct RIGHT as [D1L [D1R [D2L [D2R [EQ1 [EQ2 [S1 S2]]]]]]]; subst.
      assert (exists Q0, cenv_split_exp E Q2 Q' Q0 /\ cenv_split_exp E Q1 Q0 Q'').
        apply cenv_split_exp_assoc with (Q13 := Q3); auto.
      destruct H1 as [Q0 [H1 H2]].
      lapply (IHTYP2 Q' Q0 D2R D2L); auto. 
      intros I.
      assert (x `notin` (dom (D1L++D1R) `union` dom E `union` dom Q3)) as J.
        eapply lenv_split_not_in_right; eauto.
        simpl_env. fsetdec.
      lapply I; auto. intros TYPE2. 
      rewrite <- (non_subst E (D1L ++ D1R) Q1 e1 (typ_tensor T1 T2) x u); auto.
        apply (typing_let E (D1L ++ D1R) (D2L ++ F ++ D2R))
          with (T1 := T1) (T2 := T2) (Q1 := Q1) (Q2 := Q0); auto.
          assert (vwf_envs E Q3 (D2L ++ F ++ D2R)) as JJ.
            eapply wf_lenv_split_right. 
              eapply lenv_split_sub_right; eauto.
              eapply vwf_envs_strengthen_cenv_left; eauto.
              apply cenv_split_exp_proc; eauto.
          apply TYPE2; auto. apply vwf_envs_pack.
            apply vwf_envs_unpack in JJ; intuition...
            eapply wf_cenv_split_exp; eauto.
            apply vwf_envs_unpack in VWF. destruct VWF as [WFL [WFC DJ]].
            (*apply dom_cenv_split_exp in H1.*) apply dom_cenv_split_exp in H2.
            apply dom_lenv_split in S1. apply dom_lenv_split in S2.
            unfold disjoint in *. simpl_env in *. 
            clear - DJ S1 S2 H2. fsetdec.
          apply lenv_split_disjoint_cenv with (Q := Q3); auto.
            eapply lenv_split_sub_right; eauto.
            apply vwf_envs_unpack in VWF. destruct VWF as [WFL [WFC DJ]].
            apply vwf_envs_pack; auto.
            apply dom_cenv_split_exp in CS.
            apply dom_lenv_split in S1. apply dom_lenv_split in S2.
            unfold disjoint in *. simpl_env in *.
            clear - DJ S1 S2 CS. fsetdec.
          apply dom_cenv_split_exp in H0. fsetdec.
  Case "typing_case".
    lapply (lenv_split_cases_mid E Q3 D1 D2 DL x U DR); auto.
    intros C.
    destruct C as [LEFT | RIGHT].
    SCase "left".
      destruct LEFT as [D1L [D1R [D2L [D2R [EQ1 [EQ2 [S1 S2]]]]]]]; subst.
      assert (exists Q0, cenv_split_exp E Q1 Q' Q0 /\ cenv_split_exp E Q2 Q0 Q'').
        apply cenv_split_exp_commute in H0.
        apply cenv_split_exp_assoc with (Q13 := Q3); auto.
      destruct H1 as [Q0 [H1 H2]].
      apply cenv_split_exp_commute in H2.
      lapply (IHTYP1 Q' Q0 D1R D1L); auto.
      intros I. 
      assert (x `notin` (dom (D2L++D2R) `union` dom E `union` dom Q3)) as J.
        eapply lenv_split_not_in_left; eauto.
        simpl_env. fsetdec.
      lapply I; auto. intros TYPE1. 
      rewrite <- (non_subst E (D2L++D2R) Q2 e2 (typ_arrow T1 T3) x u); auto.
      rewrite <- (non_subst E (D2L++D2R) Q2 e3 (typ_arrow T2 T3) x u); auto.
        apply (typing_case E (D1L ++ F ++ D1R) (D2L ++ D2R))
          with (T1 := T1) (T2 := T2) (Q1 := Q0) (Q2 := Q2); auto.
          assert (vwf_envs E Q3 (D1L ++ F ++ D1R)) as JJ.
            eapply wf_lenv_split_left.
              eapply lenv_split_sub_left; eauto.
              eapply vwf_envs_strengthen_cenv_left; eauto.
              apply cenv_split_exp_proc; eauto.
          apply TYPE1; auto. apply vwf_envs_pack.
            apply vwf_envs_unpack in JJ; intuition...
            eapply wf_cenv_split_exp; eauto.
            apply vwf_envs_unpack in VWF. destruct VWF as [WFL [WFC DJ]].
            (*apply dom_cenv_split_exp in H1.*) apply dom_cenv_split_exp in H2.
            apply dom_lenv_split in S1. apply dom_lenv_split in S2.
            unfold disjoint in *. simpl_env in *. 
            clear - DJ S1 S2 H2. fsetdec.
          apply lenv_split_disjoint_cenv with (Q := Q3); auto.
            eapply lenv_split_sub_left; eauto.
            apply vwf_envs_unpack in VWF. destruct VWF as [WFL [WFC DJ]].
            apply vwf_envs_pack; auto.
            apply dom_cenv_split_exp in CS.
            apply dom_lenv_split in S1. apply dom_lenv_split in S2.
            unfold disjoint in *. simpl_env in *.
            clear - DJ S1 S2 CS. fsetdec.
          apply dom_cenv_split_exp in H0. fsetdec.
          apply dom_cenv_split_exp in H0. fsetdec.
    SCase "right".
      destruct RIGHT as [D1L [D1R [D2L [D2R [EQ1 [EQ2 [S1 S2]]]]]]]; subst.
      assert (exists Q0, cenv_split_exp E Q2 Q' Q0 /\ cenv_split_exp E Q1 Q0 Q'').
        apply cenv_split_exp_assoc with (Q13 := Q3); auto.
      destruct H1 as [Q0 [H1 H2]].
      lapply (IHTYP2 Q' Q0 D2R D2L); auto.
      lapply (IHTYP3 Q' Q0 D2R D2L); auto.
      intros I3 I2.
      assert (x `notin` (dom (D1L++D1R) `union` dom E `union` dom Q3)) as J.
        eapply lenv_split_not_in_right; eauto.
        simpl_env. fsetdec.
      lapply I2; auto. intros TYPE2.
      lapply I3; auto. intros TYPE3.
      rewrite <- (non_subst E (D1L ++ D1R) Q1 e1 (typ_plus T1 T2) x u); auto.
          assert (vwf_envs E Q3 (D2L ++ F ++ D2R)) as JJ.
            eapply wf_lenv_split_right. 
              eapply lenv_split_sub_right; eauto.
              eapply vwf_envs_strengthen_cenv_left; eauto.
              apply cenv_split_exp_proc; eauto.
        apply (typing_case E (D1L ++ D1R) (D2L ++ F ++ D2R))
          with (T1 := T1) (T2 := T2) (Q1 := Q1) (Q2 := Q0); auto.
          apply TYPE2; auto. apply vwf_envs_pack.
            apply vwf_envs_unpack in JJ; intuition...
            eapply wf_cenv_split_exp; eauto.
            apply vwf_envs_unpack in VWF. destruct VWF as [WFL [WFC DJ]].
            (*apply dom_cenv_split_exp in H1.*) apply dom_cenv_split_exp in H2.
            apply dom_lenv_split in S1. apply dom_lenv_split in S2.
            unfold disjoint in *. simpl_env in *. 
            clear - DJ S1 S2 H2. fsetdec.
          apply TYPE3; auto. apply vwf_envs_pack.
            apply vwf_envs_unpack in JJ; intuition...
            eapply wf_cenv_split_exp; eauto.
            apply vwf_envs_unpack in VWF. destruct VWF as [WFL [WFC DJ]].
            (*apply dom_cenv_split_exp in H1.*) apply dom_cenv_split_exp in H2.
            apply dom_lenv_split in S1. apply dom_lenv_split in S2.
            unfold disjoint in *. simpl_env in *. 
            clear - DJ S1 S2 H2. fsetdec.
          apply lenv_split_disjoint_cenv with (Q := Q3); auto.
            eapply lenv_split_sub_right; eauto.
            apply vwf_envs_unpack in VWF. destruct VWF as [WFL [WFC DJ]].
            apply vwf_envs_pack; auto.
            apply dom_cenv_split_exp in CS.
            apply dom_lenv_split in S1. apply dom_lenv_split in S2.
            unfold disjoint in *. simpl_env in *.
            clear - DJ S1 S2 CS. fsetdec.
          apply dom_cenv_split_exp in H0. fsetdec.
  Case "typing_yield".
    constructor. apply IHTYP with (Q' := Q'); auto.
  Case "typing_snk".
    destruct DL; simpl_env in *.
      discriminate EQ.
      inversion EQ.
  Case "typing_src".
    destruct DL; simpl_env in *.
      discriminate EQ.
      inversion EQ.
  Case "typing_done".
    destruct DL; simpl_env in *.
      discriminate EQ.
      inversion EQ.
Qed.

(* ********************************************************************** *)
(** ** Preservation (20) *)

(*Lemma value_nonlin_inversion: forall E D e T,
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
    apply value_through_open_te; auto.
Qed.*)

(*Lemma eq_kn_dec: forall (k1 k2:kn), {k1 = k2} + {~k1 = k2}.
Proof.
  decide equality.
Qed.*)

Lemma eq_typ_dec: forall (t1 t2:typ), {t1 = t2} + {~t1 = t2}.
Proof.
  decide equality.
Qed.

Lemma eq_lbnd_dec: forall (a b:lbinding), {a = b}+{~a=b}.
Proof.
  decide equality;
    apply eq_typ_dec.
Qed.
  
Lemma eq_lbinding_dec: forall (x y:(atom * lbinding)%type), {x = y}+{~x = y}.
Proof.
  decide equality.
    apply eq_lbnd_dec.
Qed.

Lemma lenv_split_permute: forall E Q D1 D2 D3,
  lenv_split E Q D1 D2 D3 ->
  permute D3 (D1 ++ D2).
Proof.
  intros E Q D1 D2 D3 S.
  (lenv_split_cases (induction S) Case); simpl_env; auto.
  Case "lenv_split_empty".
    apply permute_empty.
  Case "lenv_split_left".
    rewrite_env (lempty ++ [(x, lbind_typ T)] ++ (D1 ++ D2)).
    apply permute_cons; auto.
  Case "lenv_split_right".
    apply permute_cons; auto.
Qed.

Lemma lenv_split_exists_permute: forall E Q D1 D2 D3 DX,
  lenv_split E Q D1 D2 D3 ->
  permute D3 DX ->
  exists D1P, exists D2P,
    permute D1 D1P /\
    permute D2 D2P /\
    lenv_split E Q D1P D2P DX.
Proof.
  intros E Q D1 D2 D3 DX S.
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
    lapply (lenv_split_cases_app E Q DL D1P D2P DR); intros; auto.
    destruct H3 as [D1L [D1R [D2L [D2R [S3 [S4 [EQ1 EQ2]]]]]]]; subst.
    exists (D1L ++ [(x, lbind_typ T)] ++ D1R).
    exists (D2L ++ D2R).
    repeat split; auto.
      apply permute_cons. auto.
      apply lenv_split_weakening_left; auto.
        apply vwf_envs_lin_weakening; auto.
          eapply wf_lenv_split; eauto.
          rewrite (dom_permute _ D3 (DL ++ DR)) in H1; auto.
  Case "lenv_split_right".
    lapply (IHS (DL ++ DR)); auto.
    intros EX.
    destruct EX as [D1P [D2P [PERM1 [PERM2 S2]]]].
    lapply (lenv_split_cases_app E Q DL D1P D2P DR); intros; auto.
    destruct H3 as [D1L [D1R [D2L [D2R [S3 [S4 [EQ1 EQ2]]]]]]]; subst.
    exists (D1L ++ D1R).
    exists (D2L ++ [(x, lbind_typ T)] ++ D2R).
    repeat split; auto.
      apply permute_cons; auto.
      apply lenv_split_weakening_right; auto.
        apply vwf_envs_lin_weakening; auto.
          eapply wf_lenv_split; eauto. 
          rewrite (dom_permute _ D3 (DL ++ DR)) in H1; auto.
Qed.

Lemma cenv_split_exp_exists_permute: forall E Q1 Q2 Q3 QX,
  cenv_split_exp E Q1 Q2 Q3 ->
  permute Q3 QX ->
  exists Q1P, exists Q2P,
    permute Q1 Q1P /\
    permute Q2 Q2P /\
    cenv_split_exp E Q1P Q2P QX.
Proof.
  intros E Q1 Q2 Q3 QX S.
  generalize dependent QX.
  (cenv_split_exp_cases (induction S) Case); 
    intros QX PERM; inversion PERM; subst.
  Case "cenv_split_exp_empty".
    exists cempty. exists cempty.
    repeat split; try apply permute_empty; try apply cenv_split_empty. 
    auto.
  Case "cenv_split_exp_left".
    lapply (IHS (DL ++ DR)); auto.
    intros EX.
    destruct EX as [Q1P [Q2P [PERM1 [PERM2 S2]]]].
    lapply (cenv_split_exp_cases_app E DL Q1P Q2P DR); intros; auto.
    destruct H2 as [Q1L [Q1R [Q2L [Q2R [S3 [S4 [EQ1 EQ2]]]]]]]; subst.
    exists (Q1L ++ [(X, cbind_proto d T)] ++ Q1R).
    exists (Q2L ++ Q2R).
    repeat split; auto.
      apply permute_cons. auto.
      apply cenv_split_exp_weakening_left; auto.
        apply wf_cenv_proto_weakening; auto.
          rewrite (dom_permute _ Q3 (DL ++ DR)) in H0; auto.
  Case "cenv_split_exp_right".
    lapply (IHS (DL ++ DR)); auto.
    intros EX.
    destruct EX as [Q1P [Q2P [PERM1 [PERM2 S2]]]].
    lapply (cenv_split_exp_cases_app E DL Q1P Q2P DR); intros; auto.
    destruct H2 as [Q1L [Q1R [Q2L [Q2R [S3 [S4 [EQ1 EQ2]]]]]]]; subst.
    exists (Q1L ++ Q1R).
    exists (Q2L ++ [(X, cbind_proto d T)] ++ Q2R).
    repeat split; auto.
      apply permute_cons; auto.
      apply cenv_split_exp_weakening_right; auto.
        apply wf_cenv_proto_weakening; auto.
          rewrite (dom_permute _ Q3 (DL ++ DR)) in H0; auto.
Qed.

Lemma wf_cenv_permute: forall E Q QX,
  wf_cenv E Q ->
  permute Q QX ->
  wf_cenv E QX.
Proof with auto.
  intros. lapply (cenv_split_exp_right_id E Q)... intros.
  apply cenv_split_exp_exists_permute with (QX := QX) in H1...
  destruct H1 as [Q1P [Q2P [Perm1 [Perm2 CS]]]].
  apply wf_cenv_split_exp in CS...
Qed.

Lemma lenv_split_permute_cenv: forall E Q D1 D2 D3 QX,
  lenv_split E Q D1 D2 D3 ->
  permute Q QX ->
  lenv_split E QX D1 D2 D3.
Proof with auto.
  intros. apply lenv_split_disjoint_cenv with (Q := Q)...
    apply wf_lenv_split in H. apply vwf_envs_unpack in H.
      destruct H as [WFL [WFC DJ]].
      apply vwf_envs_pack...
        apply wf_cenv_permute with (Q := Q)...
        apply dom_permute in H0. unfold disjoint in *. 
          rewrite <- H0...
Qed.

Lemma typing_permute_lenv: forall E Q D1 D2 e t,
  typing E D1 Q e t ->
  permute D1 D2 ->
  typing E D2 Q e t.
Proof.
  intros E Q D1 D2 e t TYP PERM.
  generalize dependent D2.
  (typing_cases (induction TYP) Case);
    intros DX PERM; eauto; try solve [inversion PERM; auto].
  Case "typing_var".
    inversion PERM; subst.
    inversion H4; subst.
    destruct DL; destruct DR; subst; simpl_env in *;
      try solve [inversion H0].
      apply typing_var; auto.
  Case "typing_seq".
    assert (exists D1P, exists D2P,
      permute D1 D1P /\
      permute D2 D2P /\
      lenv_split E Q3 D1P D2P DX) as J.
      eapply lenv_split_exists_permute; eauto.
    destruct J as [D1P [D2P [PERM2 [PERM3 S]]]].
    eapply (typing_seq E D1P D2P DX); eauto.
  Case "typing_abs".
    pick fresh x and apply typing_abs; auto.
      apply (H1 x); auto.
        rewrite_env (lempty ++ [(x, lbind_typ T1)] ++ DX).
        apply permute_cons; auto.
  Case "typing_app".
    assert (exists D1P, exists D2P,
      permute D1 D1P /\
      permute D2 D2P /\
      lenv_split E Q3 D1P D2P DX) as J.
      eapply lenv_split_exists_permute; eauto.
    destruct J as [D1P [D2P [PERM2 [PERM3 S]]]].
    eapply (typing_app T1 E D1P D2P DX); eauto.
  Case "typing_mpair".
    assert (exists D1P, exists D2P,
      permute D1 D1P /\
      permute D2 D2P /\
      lenv_split E Q3 D1P D2P DX) as J.
      eapply lenv_split_exists_permute; eauto.
    destruct J as [D1P [D2P [PERM2 [PERM3 S]]]].
    eapply (typing_mpair E D1P D2P DX); eauto.
  Case "typing_let".
    assert (exists D1P, exists D2P,
      permute D1 D1P /\
      permute D2 D2P /\
      lenv_split E Q3 D1P D2P DX) as J.
      eapply lenv_split_exists_permute; eauto.
    destruct J as [D1P [D2P [PERM2 [PERM3 S]]]].
    eapply (typing_let E D1P D2P DX); eauto.
  Case "typing_case".
    assert (exists D1P, exists D2P,
      permute D1 D1P /\
      permute D2 D2P /\
      lenv_split E Q3 D1P D2P DX) as J.
      eapply lenv_split_exists_permute; eauto.
    destruct J as [D1P [D2P [PERM2 [PERM3 S]]]].
    eapply (typing_case E D1P D2P DX); eauto.
  Case "typing_yield".
    constructor. apply IHTYP; auto.
Qed.

Lemma typing_permute_cenv: forall E Q1 Q2 D e t,
  typing E D Q1 e t ->
  permute Q1 Q2 ->
  typing E D Q2 e t.
Proof.
  intros E Q1 Q2 D e t TYP PERM.
  generalize dependent Q2.
  (typing_cases (induction TYP) Case);
    intros QX PERM; eauto; try solve [inversion PERM; auto].
  Case "typing_seq".
    assert (exists Q1P, exists Q2P,
      permute Q1 Q1P /\
      permute Q2 Q2P /\
      cenv_split_exp E Q1P Q2P QX) as J.
      eapply cenv_split_exp_exists_permute; eauto.
    destruct J as [Q1P [Q2P [PERM2 [PERM3 S]]]].
    eapply (typing_seq E D1 D2 D3 Q1P Q2P QX); eauto.
      eapply lenv_split_permute_cenv; eauto.
  Case "typing_abs".
    pick fresh x and apply typing_abs; auto.
  Case "typing_app".
    assert (exists Q1P, exists Q2P,
      permute Q1 Q1P /\
      permute Q2 Q2P /\
      cenv_split_exp E Q1P Q2P QX) as J.
      eapply cenv_split_exp_exists_permute; eauto.
    destruct J as [Q1P [Q2P [PERM2 [PERM3 S]]]].
    eapply (typing_app T1 E D1 D2 D3 Q1P Q2P QX); eauto.
      eapply lenv_split_permute_cenv; eauto.
  Case "typing_mpair".
    assert (exists Q1P, exists Q2P,
      permute Q1 Q1P /\
      permute Q2 Q2P /\
      cenv_split_exp E Q1P Q2P QX) as J.
      eapply cenv_split_exp_exists_permute; eauto.
    destruct J as [Q1P [Q2P [PERM2 [PERM3 S]]]].
    eapply (typing_mpair E D1 D2 D3 Q1P Q2P QX); eauto.
      eapply lenv_split_permute_cenv; eauto.
  Case "typing_let".
    assert (exists Q1P, exists Q2P,
      permute Q1 Q1P /\
      permute Q2 Q2P /\
      cenv_split_exp E Q1P Q2P QX) as J.
      eapply cenv_split_exp_exists_permute; eauto.
    destruct J as [Q1P [Q2P [PERM2 [PERM3 S]]]].
    eapply (typing_let E D1 D2 D3 Q1P Q2P QX); eauto.
      eapply lenv_split_permute_cenv; eauto.
  Case "typing_case".
    assert (exists Q1P, exists Q2P,
      permute Q1 Q1P /\
      permute Q2 Q2P /\
      cenv_split_exp E Q1P Q2P QX) as J.
      eapply cenv_split_exp_exists_permute; eauto.
    destruct J as [Q1P [Q2P [PERM2 [PERM3 S]]]].
    eapply (typing_case E D1 D2 D3 Q1P Q2P QX); eauto.
      eapply lenv_split_permute_cenv; eauto.
  Case "typing_yield".
    constructor. apply IHTYP; auto.
  Case "typing_snk".
    inversion PERM; subst.
    inversion H4; subst.
    destruct DL; destruct DR; subst; simpl_env in *;
      try solve [inversion H0].
      apply typing_snk; auto.
  Case "typing_src".
    inversion PERM; subst.
    inversion H5; subst.
    destruct DL; destruct DR; subst; simpl_env in *;
      try solve [inversion H1].
      apply typing_src; auto.
  Case "typing_done".
    inversion PERM; subst.
    inversion H4; subst.
    destruct DL; destruct DR; subst; simpl_env in *;
      try solve [inversion H0].
      apply typing_done; auto.
Qed.

Lemma typing_split: forall E Q D3 e T D1 D2,
  typing E (D1 ++ D2) Q e T ->
  lenv_split E Q D1 D2 D3 ->
  typing E D3 Q e T.
Proof with auto.
  intros.
  apply (typing_permute_lenv E Q (D1 ++ D2) D3)...
    apply permute_sym; eauto.
      apply eq_lbinding_dec...
      apply wf_lenv_split in H0. eapply uniq_from_wf_lenv...
      eapply lenv_split_permute; eauto.
Qed.

(* Lemma subst_tlb_identity: forall D X T,
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
Qed.*)

Lemma preservation : forall E D Q e e' T,
  typing E D Q e T ->
  red e e' ->
  typing E D Q e' T.
Proof with simpl_env; eauto.
  intros E D Q e e' T Typ.
  generalize dependent e'.
  (typing_cases (induction Typ) Case); 
    intros e' Red; inversion Red; subst...
  Case "typing_seq".
    inversion Typ1; subst.
    apply lenv_split_empty_left in H; subst.
    apply cenv_split_exp_empty_left in H0; subst...
  Case "typing_app".
    SCase "typing_abs".
      inversion Typ1.
      pick fresh x.
      rewrite (subst_ee_intro x); auto.
      apply (typing_split E Q3 D3 (subst_ee x e2 (open_ee e0 x)) T2 D2 D1); auto.
        rewrite_env (lempty ++ D2 ++ D1).
        apply (typing_through_subst_ee_lin E lempty x T1 D1)
            with (Q := Q1) (Q' := Q2); simpl_env; auto.
          eapply vwf_envs_split_both. 
            eapply lenv_split_commute; eauto.
          apply lenv_split_commute; auto.
    SCase "typing_src".
      inversion Typ1; inversion H10; subst.
      eapply typing_app. eauto.
        instantiate (2 := lempty).
        instantiate (1 := [(X, cbind_proto cdir_src (typ_arrow T3 T4))]).
        constructor...
        apply lenv_split_commute...
        apply cenv_split_exp_commute...
      eapply typing_app. eauto.
        instantiate (2 := lempty).
        instantiate (1 := [(X, cbind_proto cdir_src (typ_with T3 T4))]).
        constructor...
        apply lenv_split_commute...
        apply cenv_split_exp_commute...
  Case "typing_fst".
    inversion Typ; subst...
  Case "typing_snd".
    inversion Typ; subst...
  Case "typing_let".
    inversion Typ1; subst.
    assert (exists Q', cenv_split_exp E Q0 Q2 Q' /\ cenv_split_exp E Q4 Q' Q3).
      apply cenv_split_exp_commute in H13.
      eapply cenv_split_exp_assoc; eauto.
    destruct H1 as [Q' [H14 H15]].
    apply cenv_split_exp_commute in H14.
    apply cenv_split_exp_commute in H15.
    assert (exists D', lenv_split E Q3 D0 D2 D' /\ lenv_split E Q3 D4 D' D3).
      apply lenv_split_commute in H12.
      apply lenv_split_disjoint_cenv with (Q' := Q3) in H12.
      eapply lenv_split_assoc; eauto.
      eapply wf_lenv_split_left; eauto.
    destruct H1 as [D' [H16 H17]].
    apply lenv_split_commute in H16.
    apply lenv_split_commute in H17.
    apply typing_app
        with (T1 := T2) (D1 := D') (D2 := D4) (Q1 := Q') (Q2 := Q4)...
      apply typing_app
          with (T1 := T1) (D1 := D2) (D2 := D0) (Q1 := Q2) (Q2 := Q0)...
        eapply lenv_split_strengthen_cenv_left; eauto.
        apply cenv_split_exp_proc; eauto.
  Case "typing_case".
    inversion Typ1; subst.
    eapply typing_app; eauto.
      apply lenv_split_commute...
      apply cenv_split_exp_commute...
    inversion Typ1; subst.
    eapply typing_app; eauto.
      apply lenv_split_commute...
      apply cenv_split_exp_commute...
  Case "typing_yield".
    assert (vwf_envs E Q D) as VWF...
    assert (wf_cenv E Q) as WFC...
    inversion Typ; subst.
    apply typing_app with (T1 := typ_tensor T1 typ_unit)
        (D1 := lempty) (D2 := D) (Q1 := cempty) (Q2 := Q).
      pick fresh x and apply typing_abs; auto.
      compute. simpl_env.
      apply typing_let with (D1 := [(x, lbind_typ (typ_tensor T1  typ_unit))])
          (D2 := lempty) (Q1 := cempty) (Q2 := cempty)
          (T1 := T1)  (T2 := typ_unit); auto.
        apply typing_var.
          rewrite_env ([(x, lbind_typ (typ_tensor T1 typ_unit))] ++ lempty).
          constructor; auto.
        pick fresh y and apply typing_abs; auto.
          compute. simpl_env.
          pick fresh z and apply typing_abs; auto.
            compute. simpl_env.
            apply typing_seq with (Q1 := cempty) (Q2 := cempty)
                (D1 := [(z, lbind_typ typ_unit)])
                (D2 := [(y, lbind_typ T1)]); auto.
              apply typing_var.
                rewrite_env ([(z, lbind_typ typ_unit)] ++ lempty).
                constructor; auto.
              apply typing_var.
                rewrite_env ([(y, lbind_typ T1)] ++ lempty).
                constructor; auto.
              rewrite_env ([(z, lbind_typ typ_unit)] ++ lempty).
              rewrite_env ([(y, lbind_typ T1)] ++ lempty).
              apply lenv_split_left; auto.
        rewrite_env ([(x, lbind_typ (typ_tensor T1 typ_unit))] ++ lempty); auto.
      repeat constructor; auto.
      apply lenv_split_left_id; auto.
      apply cenv_split_exp_left_id; auto.
    assert (vwf_envs E Q D) as VWF...
    assert (wf_cenv E Q) as WFC...
    inversion Typ; subst.
    apply typing_app with (T1 := typ_tensor T1 typ_unit)
        (D1 := lempty) (D2 := lempty) (Q1 := cempty)
        (Q2 := [(X, cbind_proto cdir_snk (typ_src T1))]).
      pick fresh x and apply typing_abs; auto.
      compute. simpl_env.
      apply typing_let with (D1 := [(x, lbind_typ (typ_tensor T1 typ_unit))])
          (D2 := lempty) (Q1 := cempty) (Q2 := cempty)
          (T1 :=  T1)  (T2 := typ_unit); auto.
        apply typing_var.
          rewrite_env ([(x, lbind_typ (typ_tensor T1 typ_unit))] ++ lempty).
          constructor; auto.
        pick fresh y and apply typing_abs; auto.
          compute. simpl_env.
          pick fresh z and apply typing_abs; auto.
            compute. simpl_env.
            apply typing_seq with (Q1 := cempty) (Q2 := cempty)
                (D1 := [(z, lbind_typ typ_unit)])
                (D2 := [(y, lbind_typ T1)]); auto.
              apply typing_var.
                rewrite_env ([(z, lbind_typ typ_unit)] ++ lempty).
                constructor; auto.
              apply typing_var.
                rewrite_env ([(y, lbind_typ T1)] ++ lempty).
                constructor; auto.
              rewrite_env ([(z, lbind_typ typ_unit)] ++ lempty).
              rewrite_env ([(y, lbind_typ T1)] ++ lempty).
              apply lenv_split_left; auto.
        rewrite_env ([(x, lbind_typ (typ_tensor T1 typ_unit))] ++ lempty); auto.
      repeat constructor; auto.
      inversion H4; subst; auto.
      apply cenv_split_exp_left_id; auto.
Qed.