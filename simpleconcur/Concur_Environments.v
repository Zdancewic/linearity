(** Weakening and environment splitting lemmas for the simple
      concurrent system.

     Added because the soundness file was getting too long. *)

Require Export Concur_Lemmas.

(************************************************************************ *)
(** Weakening lemmas *)

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
Qed.

Lemma wf_cenv_weakening: forall E F G Q,
  wf_cenv (G ++ E) Q ->
  wf_env (G ++ F ++ E) ->
  disjoint F Q ->
  wf_cenv (G ++ F ++ E) Q.
Proof.
  intros E F G D WFL.
  remember (G ++ E) as G0.
  generalize dependent G. 
  (wf_cenv_cases (induction WFL) Case);
    intros G EQ WFE NIN; subst; simpl_env in *; auto.
  Case "wf_cenv_proto".
    apply wf_cenv_proto; auto.
      apply IHWFL; auto.
       intros. solve_uniq.
      repeat rewrite dom_app.
      assert (X `notin` dom F) as J. 
        solve_uniq.
      fsetdec.
      apply wf_proto_weakening; auto.
Qed.

Lemma vwf_envs_weakening: forall E F G Q D,
  vwf_envs (G ++ E) Q D ->
  wf_env (G ++ F ++ E) ->
  disjoint F Q ->
  disjoint F D ->
  vwf_envs (G ++ F ++ E) Q D.
Proof with auto.
  intros E F G Q D VWF WFE Dc Dl.
  apply vwf_envs_pack.
    apply wf_lenv_weakening...
    apply wf_cenv_weakening...
    apply vwf_envs_unpack in VWF. intuition...
Qed.

Lemma lenv_split_weakening: forall E F G Q D1 D2 D3,
  lenv_split (E ++ G) Q D1 D2 D3 ->
  wf_cenv (E ++ F ++ G) Q ->
  disjoint F D3 ->
  lenv_split (E ++ F ++ G) Q D1 D2 D3.
Proof.
  intros E F G Q D1 D2 D3 S.
  remember (E ++ G) as G0.
  generalize dependent E. generalize dependent G. generalize dependent F.
  (lenv_split_cases (induction S) Case); intros F1 G1 E1 EQ WFE NIN; auto.
  Case "lenv_split_left".
    apply lenv_split_left; subst; auto.
      apply IHS; auto. 
        solve_uniq.
      simpl; solve_uniq.
  Case "lenv_split_right".
    apply lenv_split_right; subst; auto.
      apply IHS; auto. 
        solve_uniq.
      simpl; solve_uniq.
Qed.

Lemma lenv_split_lin_weakening_left: forall E F Q D1 D2 D3,
  lenv_split E Q D1 D2 D3 ->
  vwf_envs E Q (F ++ D3) ->
  lenv_split E Q (F ++ D1) D2 (F ++ D3).
Proof.
  intros E F Q. 
  induction F; intros D1 D2 D3 S WFL; simpl_env in *; auto.
  Case "con".
    destruct a. simpl_env in *.
    inversion WFL; subst.
    apply lenv_split_left; auto.
Qed.

Lemma lenv_split_lin_weakening_right: forall E F Q D1 D2 D3,
  lenv_split E Q D1 D2 D3 ->
  vwf_envs E Q (F ++ D3) ->
  lenv_split E Q D1 (F ++ D2) (F ++ D3).
Proof with auto.
  intros.
  apply lenv_split_commute. apply lenv_split_commute in H.
  apply lenv_split_lin_weakening_left...
Qed.

Lemma lenv_agree_weakening: forall E F G Q D1 D2,
  lenv_agree (E ++ G) Q D1 D2 ->
  wf_cenv (E ++ F ++ G) Q ->
  disjoint F D1 ->
  disjoint F D2 ->
  lenv_agree (E ++ F ++ G) Q D1 D2.
Proof with try solve_uniq; auto.
  intros E F G Q D1 D2 Agree.
  remember (E ++ G) as G0.
  generalize dependent E. generalize dependent G. generalize dependent F.
  induction Agree; intros F1 G1 E1 EQ WFC DJ1 DJ2...
    constructor... subst; simpl; solve_uniq.
    constructor... subst; simpl; solve_uniq.
    constructor... subst; simpl; solve_uniq.
Qed.

Lemma cenv_split_exp_weakening: forall E F G Q1 Q2 Q3,
  cenv_split_exp (E ++ G) Q1 Q2 Q3 ->
  wf_env (E ++ F ++ G) ->
  disjoint F Q3 ->
  cenv_split_exp (E ++ F ++ G) Q1 Q2 Q3.
Proof with auto using wf_proto_weakening.
  intros E F G Q1 Q2 Q3 S.
  remember (E ++ G) as G0.
  generalize dependent E. generalize dependent G. generalize dependent F.
  (cenv_split_exp_cases (induction S) Case); intros F1 G1 E1 EQ WFE NIN; auto.
  Case "cenv_split_exp_left".
    apply cenv_split_exp_left; subst...
      apply IHS; auto. 
        solve_uniq.
      simpl; solve_uniq.
  Case "cenv_split_exp_right".
    apply cenv_split_exp_right; subst...
      apply IHS; auto. 
        solve_uniq.
      simpl; solve_uniq.
Qed.

Lemma cenv_split_proc_weakening: forall E F G Q1 Q2 Q3 Z,
  cenv_split_proc (E ++ G) Q1 Q2 Q3 Z ->
  wf_env (E ++ F ++ G) ->
  disjoint F Q3 ->
  cenv_split_proc (E ++ F ++ G) Q1 Q2 Q3 Z.
Proof with auto using wf_proto_weakening.
  intros E F G Q1 Q2 Q3 Z S.
  remember (E ++ G) as G0.
  generalize dependent E. generalize dependent G. generalize dependent F.
  (cenv_split_proc_cases (induction S) Case); intros F1 G1 E1 EQ WFE NIN; auto.
  Case "cenv_split_proc_left".
    apply cenv_split_proc_left; subst...
      apply IHS; auto. 
        solve_uniq.
      simpl; solve_uniq.
  Case "cenv_split_proc_right".
    apply cenv_split_proc_right; subst...
      apply IHS; auto. 
        solve_uniq.
      simpl; solve_uniq.
  Case "cenv_split_proc_snksrc".
    apply cenv_split_proc_snksrc; subst...
      apply cenv_split_exp_weakening; auto. 
        solve_uniq.
      simpl; solve_uniq.
  Case "cenv_split_proc_srcsnk".
    apply cenv_split_proc_srcsnk; subst...
      apply cenv_split_exp_weakening; auto. 
        solve_uniq.
      simpl; solve_uniq.
Qed.

Lemma cenv_agree_weakening: forall E F G Q1 Q2,
  cenv_agree (E ++ G) Q1 Q2 ->
  wf_env (E ++ F ++ G) ->
  disjoint F Q1 ->
  disjoint F Q2 ->
  cenv_agree (E ++ F ++ G) Q1 Q2.
Proof with try solve_uniq; auto.
  intros E F G Q1 Q2 Agree.
  remember (E ++ G) as G0.
  generalize dependent E. generalize dependent G. generalize dependent F.
  induction Agree; intros F1 G1 E1 EQ WFE DJ1 DJ2...
    constructor... subst; simpl; solve_uniq.
      apply wf_proto_weakening; subst...
    constructor... subst; simpl; solve_uniq.
      apply wf_proto_weakening; subst...
    constructor... subst; simpl; solve_uniq.
      apply wf_proto_weakening; subst...
Qed.

Lemma lenv_split_disjoint_cenv: forall G Q Q' D1 D2 D3,
  lenv_split G Q D1 D2 D3 ->
  vwf_envs G Q' D3 ->
  lenv_split G Q' D1 D2 D3.
Proof with auto.
  intros G Q Q' D1 D2 D3 LS VWF.
  apply vwf_envs_unpack in VWF. destruct VWF as [WFL [WFC DJ]].
  induction LS; constructor...
    apply IHLS...
      apply wf_lenv_split in LS. apply vwf_envs_unpack in LS; intuition...
      unfold disjoint in *; simpl_env in DJ; fsetdec.
    unfold disjoint in *; simpl_env in DJ; fsetdec.
    apply IHLS...
      apply wf_lenv_split in LS. apply vwf_envs_unpack in LS; intuition...
      unfold disjoint in *; simpl_env in DJ; fsetdec.
    unfold disjoint in *; simpl_env in DJ; fsetdec.
Qed.

Lemma lenv_agree_disjoint_cenv: forall G Q Q' D1 D2,
  lenv_agree G Q D1 D2 ->
  vwf_envs G Q' D1 ->
  vwf_envs G Q' D2 ->
  lenv_agree G Q' D1 D2.
Proof with auto.
  intros G Q Q' D1 D2 Agree VWF1 VWF2.
  apply vwf_envs_unpack in VWF1. destruct VWF1 as [WFL1 [WFC1 DJ1]].
  apply vwf_envs_unpack in VWF2. destruct VWF2 as [WFL2 [WFC2 DJ2]].
  induction Agree; constructor...
    apply IHAgree...
      apply wf_lenv_agree_left in Agree.
        apply vwf_envs_unpack in Agree; intuition...
      unfold disjoint in *; simpl_env in DJ1; fsetdec.
      apply wf_lenv_agree_right in Agree.
        apply vwf_envs_unpack in Agree; intuition...
      unfold disjoint in *; simpl_env in DJ2; fsetdec.
    unfold disjoint in *; simpl_env in *; fsetdec.
    apply IHAgree...
      apply wf_lenv_agree_left in Agree.
        apply vwf_envs_unpack in Agree; intuition...
      unfold disjoint in *; simpl_env in DJ1; fsetdec.
    unfold disjoint in *; simpl_env in *; fsetdec.
    apply IHAgree...
      apply wf_lenv_agree_right in Agree.
        apply vwf_envs_unpack in Agree; intuition...
      unfold disjoint in *; simpl_env in DJ2; fsetdec.
    unfold disjoint in *; simpl_env in *; fsetdec.
Qed.

Lemma lenv_split_weakening_left: forall E Q D1L D1R D2L D2R D3L D3R x T,
  lenv_split E Q (D1L ++ D1R) (D2L ++ D2R) (D3L ++ D3R) ->
  lenv_split E Q D1L D2L D3L ->
  lenv_split E Q D1R D2R D3R ->
  vwf_envs E Q (D3L ++ [(x, lbind_typ T)] ++ D3R) ->
  lenv_split E Q (D1L ++ [(x, lbind_typ T)] ++ D1R) (D2L ++ D2R) (D3L ++ [(x, lbind_typ T)]++ D3R).
Proof.
  intros E Q D1L D1R D2L D2R D3L D3R x T S.
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
          rewrite (dom_lenv_split E Q ([(x0, lbind_typ T0)] ++ D1) D2 D3L) in H1; auto.
          simpl in H1.
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
          rewrite <- J in H1.
          rewrite (dom_lenv_split E Q D1 ([(x0, lbind_typ T0)] ++ D2 ++ D2R) (D3L ++ D3R)) in H1; auto.
          simpl in H1; auto.
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
          rewrite (dom_lenv_split E Q D1R ([(x0, lbind_typ T0)] ++ D2R) D3R) in H1; auto.
          simpl in H1. 
          assert False. fsetdec. tauto.
      SSCase "D2L=con".
        inversion WFL; subst.
        apply lenv_split_right; subst; auto.  
          eapply IHS; auto.  
          inversion SL; subst; simpl_env in *.
          SSSCase "SL1".
            assert (dom (D3L ++ D3R) [=] dom D3L `union` dom D3R) as J.
              rewrite dom_app; fsetdec.
            rewrite <- J in H1.
            rewrite (dom_lenv_split E Q ([(x0, lbind_typ T0)] ++ D1 ++ D1R) 
               (D2L ++ D2R) (D3L ++ D3R)) in H1; auto.
            simpl in H1; auto.
            assert False. fsetdec. tauto.
          SSSCase "SL2".
            inversion WFL; auto.
Qed.

Lemma lenv_split_weakening_right: forall E Q D1L D1R D2L D2R D3L D3R x T,
  lenv_split E Q (D1L ++ D1R) (D2L ++ D2R) (D3L ++ D3R) ->
  lenv_split E Q D1L D2L D3L ->
  lenv_split E Q D1R D2R D3R ->
  vwf_envs E Q (D3L ++ [(x, lbind_typ T)] ++ D3R) ->
  lenv_split E Q (D1L ++ D1R) (D2L ++ [(x, lbind_typ T)] ++ D2R) (D3L ++ [(x, lbind_typ T)]++ D3R).
Proof.
  intros. 
  apply lenv_split_commute. 
  apply lenv_split_weakening_left; try (apply lenv_split_commute; auto); auto.
Qed.

Lemma cenv_split_exp_weakening_left: forall E Q1L Q1R Q2L Q2R Q3L Q3R X d T,
  cenv_split_exp E (Q1L ++ Q1R) (Q2L ++ Q2R) (Q3L ++ Q3R) ->
  cenv_split_exp E Q1L Q2L Q3L ->
  cenv_split_exp E Q1R Q2R Q3R ->
  wf_cenv E (Q3L ++ [(X, cbind_proto d T)] ++ Q3R) ->
  cenv_split_exp E (Q1L ++ [(X, cbind_proto d T)] ++ Q1R) (Q2L ++ Q2R) (Q3L ++ [(X, cbind_proto d T)]++ Q3R).
Proof.
  intros E Q1L Q1R Q2L Q2R Q3L Q3R X d T S.
  remember (Q1L ++ Q1R) as Q1.
  remember (Q2L ++ Q2R) as Q2.
  remember (Q3L ++ Q3R) as Q3.
  generalize dependent Q1L. generalize dependent Q1R.
  generalize dependent Q2L. generalize dependent Q2R.
  generalize dependent Q3L. generalize dependent Q3R.
  (cenv_split_exp_cases (induction S) Case);
    intros Q3R Q3L EQ3 Q2R Q2L EQ2 Q1R Q1L EQ1 SL SR WFC; subst; simpl_env in *.
  Case "cenv_split_exp_empty".
    destruct Q3L; destruct Q3R; inversion EQ3; subst; simpl_env.
    destruct Q2L; destruct Q2R; inversion EQ2; subst; simpl_env.
    destruct Q1L; destruct Q1R; inversion EQ1; subst; simpl_env.
    rewrite_env ([(X, cbind_proto d T)] ++ nil).
    simpl_env in WFC. inversion WFC; subst.
    apply cenv_split_exp_left; auto. 
  Case "cenv_split_exp_left".
    destruct Q3L; inversion EQ3.
    SCase "Q3L=nil".
      destruct Q1L; inversion EQ1.
      SSCase "Q1L=nil".
        destruct Q3R; simpl_env in EQ3; inversion EQ3.
        SSSCase "Q3R=con".
          destruct Q1R; simpl_env in EQ1; inversion EQ1.
          SSSSCase "Q1R=con"; subst; simpl_env in *.
            inversion WFC; subst.
            apply cenv_split_exp_left; auto.
      SSCase "Q1L=con".
        inversion SL.
    SCase "Q3L=con".
      destruct Q1R; simpl_env in EQ1; inversion EQ1; subst.
      SSCase "Q2R=nil".
        simpl_env in *. 
        inversion WFC; subst.
        apply cenv_split_exp_left; auto.
          rewrite_env (Q1 ++ [(X, cbind_proto d T)] ++ nil).
          eapply IHS; auto.
          inversion SL; auto. subst.
          rewrite (dom_cenv_split_exp E ([(X0, cbind_proto d0 T0)] ++ Q1) Q2 Q3L) in H16; auto.
          simpl in H16.
          assert False. fsetdec. tauto.
      SSCase "Q2R=con".
        inversion SL; subst; simpl_env in *.
        SSSCase "SL1".
          inversion WFC; subst.
          apply cenv_split_exp_left; auto. 
            eapply IHS; auto. 
              inversion EQ1; auto.
        SSSCase "SL2".
          assert (dom (Q3L ++ Q3R) [=] dom Q3L `union` dom Q3R) as J.
            rewrite dom_app; auto. fsetdec.
          rewrite <- J in H0.
          rewrite (dom_cenv_split_exp E Q1 ([(X0, cbind_proto d0 T0)] ++ Q2 ++ Q2R) (Q3L ++ Q3R)) in H0; auto.
          simpl in H0; auto.
          assert False. fsetdec. tauto.
  Case "cenv_split_exp_right".
    destruct Q3L; inversion EQ3.
    SCase "Q3L=nil".
      destruct Q2L; inversion EQ2.
      SSCase "Q2L=nil".
        destruct Q3R; inversion EQ3.
        SSSCase "Q3R=con".
          destruct Q2R; inversion EQ2.
          SSSSCase "Q2R=con"; subst; simpl_env in *.
            inversion SL; simpl_env in *.
            inversion WFC; subst.
            apply cenv_split_exp_left; auto. 
      SSCase "Q2L=con".
        inversion SL.
    SCase "Q3L=con".
      subst. simpl_env in *.
      destruct Q2L; inversion EQ2.
      SSCase "Q2L=nil".
        destruct Q2R; inversion EQ2.
        SSSCase "Q2R=con".
          subst. simpl_env in *.
          rewrite (dom_cenv_split_exp E Q1R ([(X0, cbind_proto d0 T0)] ++ Q2R) Q3R) in H0; auto.
          simpl in H0. 
          assert False. fsetdec. tauto.
      SSCase "Q2L=con".
        inversion WFC; subst.
        apply cenv_split_exp_right; subst; auto.  
          eapply IHS; auto.
          inversion SL; subst; simpl_env in *.
          SSSCase "SL1".
            assert (dom (Q3L ++ Q3R) [=] dom Q3L `union` dom Q3R) as J.
              rewrite dom_app; fsetdec.
            rewrite <- J in H0.
            rewrite (dom_cenv_split_exp E ([(X0, cbind_proto d0 T0)] ++ Q1 ++ Q1R) 
               (Q2L ++ Q2R) (Q3L ++ Q3R)) in H0; auto.
            simpl in H0; auto.
            assert False. fsetdec. tauto.
          SSSCase "SL2".
            inversion WFC; auto.
Qed.

Lemma cenv_split_exp_weakening_right: forall E Q1L Q1R Q2L Q2R Q3L Q3R X d T,
  cenv_split_exp E (Q1L ++ Q1R) (Q2L ++ Q2R) (Q3L ++ Q3R) ->
  cenv_split_exp E Q1L Q2L Q3L ->
  cenv_split_exp E Q1R Q2R Q3R ->
  wf_cenv E (Q3L ++ [(X, cbind_proto d T)] ++ Q3R) ->
  cenv_split_exp E (Q1L ++ Q1R) (Q2L ++ [(X, cbind_proto d T)] ++ Q2R) (Q3L ++ [(X, cbind_proto d T)]++ Q3R).
Proof.
  intros. 
  apply cenv_split_exp_commute. 
  apply cenv_split_exp_weakening_left; try (apply cenv_split_exp_commute; auto); auto.
Qed.

Lemma wf_lenv_lin_weakening: forall E D1 D2 x T,
  wf_typ E T ->
  wf_lenv E (D1 ++ D2) ->
  x `notin` dom E ->
  x `notin` dom (D1 ++ D2) ->
  wf_lenv E (D1 ++ [(x, lbind_typ T)] ++ D2).
Proof.
  intros E D1 D2 x T WFT WFL.
  remember (D1 ++ D2) as D.
  generalize dependent D1. generalize dependent D2.
  (wf_lenv_cases (induction WFL) Case);
    intros D2 D1 EQ NIN1 NIN2.
  Case "wf_lenv_empty".
   destruct D1; destruct D2; inversion EQ; subst; simpl_env in *.
   rewrite_env ([(x, lbind_typ T)] ++ nil).
   apply wf_lenv_typ; auto.
  Case "wf_lenv_typ".
    destruct D1; destruct D2; inversion EQ; subst; simpl_env in *.
    SCase "D1=nil, D2=con".
      apply wf_lenv_typ; auto. 
    SCase "D1=con, D2=nil".
      rewrite_env (D1 ++ [(x, lbind_typ T)] ++ nil); auto.
    SCase "D1=con, D2=con".
      apply wf_lenv_typ; auto. 
Qed.

Lemma wf_cenv_proto_weakening: forall E Q1 Q2 X d T,
  wf_proto E T ->
  wf_cenv E (Q1 ++ Q2) ->
  X `notin` dom E ->
  X `notin` dom (Q1 ++ Q2) ->
  wf_cenv E (Q1 ++ [(X, cbind_proto d T)] ++ Q2).
Proof.
  intros E Q1 Q2 X d T WFP WFC.
  remember (Q1 ++ Q2) as Q.
  generalize dependent Q1. generalize dependent Q2.
  (wf_cenv_cases (induction WFC) Case);
    intros Q2 Q1 EQ NIN1 NIN2.
  Case "wf_cenv_empty".
   destruct Q1; destruct Q2; inversion EQ; subst; simpl_env in *.
   rewrite_env ([(X, cbind_proto d T)] ++ nil).
   apply wf_cenv_proto; auto.
  Case "wf_cenv_proto".
    destruct Q1; destruct Q2; inversion EQ; subst; simpl_env in *.
    SCase "Q1=nil, Q2=con".
      apply wf_cenv_proto; auto. 
    SCase "Q1=con, Q2=nil".
      rewrite_env (Q1 ++ [(X, cbind_proto d T)] ++ nil); auto.
    SCase "Q1=con, Q2=con".
      apply wf_cenv_proto; auto. 
Qed.

Lemma vwf_envs_lin_weakening: forall E Q D1 D2 x T,
  wf_typ E T ->
  vwf_envs E Q (D1 ++ D2) ->
  x `notin` dom E ->
  x `notin` dom Q ->
  x `notin` dom (D1 ++ D2) ->
  vwf_envs E Q (D1 ++ [(x, lbind_typ T)] ++ D2).
Proof.
  intros E Q D1 D2 x T WFP VWF.
  remember (D1 ++ D2) as D.
  generalize dependent D1. generalize dependent D2.
  (vwf_envs_cases (induction VWF) Case);
    intros D2 D1 EQ NIN1 NIN2 NIN3.
  Case "vwf_envs_empty".
   destruct D1; destruct D2; inversion EQ; subst; simpl_env in *.
   rewrite_env ([(x, lbind_typ T)] ++ nil).
   apply vwf_envs_typ; auto.
  Case "vwf_envs_typ".
    destruct D1; destruct D2; inversion EQ; subst; simpl_env in *.
    SCase "D1=nil, D2=con".
      apply vwf_envs_typ; auto. 
    SCase "D1=con, D2=nil".
      rewrite_env (D1 ++ [(x, lbind_typ T)] ++ nil); auto.
    SCase "D1=con, D2=con".
      apply vwf_envs_typ; auto. 
Qed.

Lemma lenv_split_cases_app: forall E Q DL D1 D2 DR,
  lenv_split E Q D1 D2 (DL ++ DR) ->
  exists D1L, exists D1R, exists D2L, exists D2R,
    lenv_split E Q D1L D2L DL /\
    lenv_split E Q D1R D2R DR /\
    D1L ++ D1R = D1 /\
    D2L ++ D2R = D2.
Proof.
  intros E Q DL.
  induction DL; intros D1 D2 DR S.
  Case "empty".
    exists lempty. exists D1. exists lempty. exists D2.
    simpl_env in *; repeat split; auto. 
    apply lenv_split_empty.
      apply wf_lenv_split in S.
      eapply wf_cenv_from_vwf_envs; eauto.
  Case "cons".
    destruct a. simpl_env in S.
    inversion S; subst.
    SCase "left".
      lapply (IHDL D0 D2 DR); auto.
      intros.
      destruct H as [D1L [D1R [D2L [D2R [S2 [S3 [EQ1 EQ2]]]]]]].
      exists ([(a, lbind_typ T)] ++ D1L).
      exists D1R.
      exists D2L.
      exists D2R.
      subst; simpl_env in *; repeat split; auto.
    SCase "right".
      lapply (IHDL D1 D3 DR); auto.
      intros.
      destruct H as [D1L [D1R [D2L [D2R [S2 [S3 [EQ1 EQ2]]]]]]].
      exists D1L.
      exists D1R.
      exists ([(a, lbind_typ T)] ++ D2L).
      exists D2R.
      subst; simpl_env in *; repeat split; auto.
Qed.

Lemma cenv_split_exp_cases_app: forall E QL Q1 Q2 QR,
  cenv_split_exp E Q1 Q2 (QL ++ QR) ->
  exists Q1L, exists Q1R, exists Q2L, exists Q2R,
    cenv_split_exp E Q1L Q2L QL /\
    cenv_split_exp E Q1R Q2R QR /\
    Q1L ++ Q1R = Q1 /\
    Q2L ++ Q2R = Q2.
Proof.
  intros E QL.
  induction QL; intros Q1 Q2 QR S.
  Case "empty".
    exists cempty. exists Q1. exists cempty. exists Q2.
    simpl_env in *; repeat split; auto. 
    apply cenv_split_exp_empty.
      apply wf_cenv_split_exp in S. auto.
  Case "cons".
    destruct a. simpl_env in S.
    inversion S; subst.
    SCase "left".
      lapply (IHQL Q0 Q2 QR); auto.
      intros.
      destruct H as [Q1L [Q1R [Q2L [Q2R [S2 [S3 [EQ1 EQ2]]]]]]].
      exists ([(a, cbind_proto d T)] ++ Q1L).
      exists Q1R.
      exists Q2L.
      exists Q2R.
      subst; simpl_env in *; repeat split; auto.
    SCase "right".
      lapply (IHQL Q1 Q3 QR); auto.
      intros.
      destruct H as [Q1L [Q1R [Q2L [Q2R [S2 [S3 [EQ1 EQ2]]]]]]].
      exists Q1L.
      exists Q1R.
      exists ([(a, cbind_proto d T)] ++ Q2L).
      exists Q2R.
      subst; simpl_env in *; repeat split; auto.
Qed.

(* This will be harder in the polymorphic case... *)
Lemma dual_weakening: forall E F G T1 T2,
  dual (G ++ E) T1 T2 ->
  wf_env (G ++ F ++ E) ->
  dual (G ++ F ++ E) T1 T2.
Proof with auto.
  intros E F G T1 T2 Hd Hwf.
  induction Hd...
Qed.

(*Lemma snk_weakening: forall E F G T C e,
  snk (G ++ E) T C e ->
  wf_chan (G ++ F ++ E) C ->
  snk (G ++ F ++ E) T C e.
Proof with auto.
  intros E F G T C e Snk WF.
  induction Snk...
Qed.

Lemma src_weakening: forall E F G T C e,
  src (G ++ E) T C e ->
  wf_chan (G ++ F ++ E) C ->
  src (G ++ F ++ E) T C e.
Proof with auto.
  intros E F G T C e Src WF.
  remember (G ++ E) as E0. generalize dependent E.
  generalize dependent F. generalize dependent G.
  induction Src; intros; subst...
  pick fresh x and apply src_arrow...
  inversion WF; subst. constructor...
    apply dual_weakening...
    apply dual_weakening... 
Qed.*)

Lemma typing_weakening: forall E F G D Q e T,
  typing (G ++ E) D Q e T ->
  vwf_envs (G ++ F ++ E) Q D ->
  typing (G ++ F ++ E) D Q e T.
Proof with simpl_env;
           eauto using wf_typ_weakening,
                       wf_proto_from_wf_cenv,
                       vwf_envs_pack,
                       lenv_split_strengthen_cenv_left,
                       lenv_split_strengthen_cenv_right.
  intros E F G D Q e T Typ.
  remember (G ++ E) as H.
  generalize dependent G. generalize dependent E.
  (typing_cases (induction Typ) Case); intros E0 G EQ VWF; subst;
    apply vwf_envs_unpack in VWF; destruct VWF as [WFL [WFC DJ]];
    assert (wf_env (G ++ F ++ E0)) as WFE; try apply wf_env_from_wf_lenv...
  Case "typing_seq".
    apply typing_seq with (D1 := D1) (D2 := D2) (Q1 := Q1) (Q2 := Q2)...
    apply IHTyp1... apply wf_lenv_split_left with (D2 := D2) (D3 := D3).
      apply lenv_split_weakening...
        apply lenv_split_strengthen_cenv_left with (Q2 := Q2) (Q3 := Q3) (Z := None)...
          apply cenv_split_exp_proc...
        apply wf_cenv_weakening...
        apply wf_cenv_disjoint in WFC. unfold disjoint in *.
          assert (dom Q3 [=] dom Q1 `union` dom Q2).
            apply dom_cenv_split_exp with (G := G ++ E0)... 
          simpl_env in WFC. fsetdec.
      apply wf_lenv_disjoint in WFL. solve_uniq.
    apply IHTyp2... apply wf_lenv_split_right with (D1 := D1) (D3 := D3).
      apply lenv_split_weakening...
        apply lenv_split_strengthen_cenv_right with (Q1 := Q1) (Q3 := Q3) (Z := None)...
          apply cenv_split_exp_proc...
        apply wf_cenv_weakening...
        apply wf_cenv_disjoint in WFC. unfold disjoint in *.
          assert (dom Q3 [=] dom Q1 `union` dom Q2).
            apply dom_cenv_split_exp with (G := G ++ E0)... 
          simpl_env in WFC. fsetdec.
      apply wf_lenv_disjoint in WFL. solve_uniq.
    apply lenv_split_weakening...
      apply wf_lenv_disjoint in WFL. solve_uniq.
      apply cenv_split_exp_weakening...
      apply wf_cenv_disjoint in WFC. solve_uniq.
  Case "typing_abs".
    pick fresh x and apply typing_abs; subst; auto.
    apply H1...
  Case "typing_app".
    eapply typing_app.
      eapply IHTyp1; eauto.
        eapply wf_lenv_split_left.
          eapply lenv_split_strengthen_cenv_left with (Q2 := Q2) (Z := None) in H; eauto.
          apply lenv_split_weakening; eauto.
            apply wf_cenv_split_exp_left with (Q2 := Q2) (Q3 := Q3).
              apply cenv_split_exp_weakening...
              apply wf_cenv_disjoint in WFC. unfold disjoint in *.
              assert (dom Q3 [=] dom Q1 `union` dom Q2).
                apply dom_cenv_split_exp with (G := G ++ E0)... 
              simpl_env in WFC. fsetdec.
            apply wf_lenv_disjoint in WFL. solve_uniq.
          apply cenv_split_exp_proc...
      eapply IHTyp2; eauto.
        eapply wf_lenv_split_right.
          eapply lenv_split_strengthen_cenv_right with (Q1 := Q1) (Z := None) in H; eauto.
          apply lenv_split_weakening; eauto.
            apply wf_cenv_split_exp_right with (Q1 := Q1) (Q3 := Q3).
              apply cenv_split_exp_weakening...
              apply wf_cenv_disjoint in WFC. unfold disjoint in *.
              assert (dom Q3 [=] dom Q1 `union` dom Q2).
                apply dom_cenv_split_exp with (G := G ++ E0)... 
              simpl_env in WFC. fsetdec.
            apply wf_lenv_disjoint in WFL. solve_uniq.
          apply cenv_split_exp_proc...
      eapply lenv_split_weakening; auto.
        apply wf_lenv_disjoint in WFL. solve_uniq.
      eapply cenv_split_exp_weakening; auto.
        apply wf_cenv_disjoint in WFC. solve_uniq.
  Case "typing_apair".
    constructor. apply IHTyp1... apply IHTyp2...
  Case "typing_mpair".
    apply typing_mpair with (D1 := D1) (D2 := D2) (Q1 := Q1) (Q2 := Q2).
    apply IHTyp1... apply wf_lenv_split_left with (D2 := D2) (D3 := D3).
      eapply lenv_split_strengthen_cenv_left with (Q2 := Q2) (Z := None) in H; eauto.
        apply lenv_split_weakening...
          apply wf_cenv_split_exp_left with (Q2 := Q2) (Q3 := Q3).
          apply cenv_split_exp_weakening...
          apply wf_cenv_disjoint in WFC.
          assert (dom Q3 [=] dom Q1 `union` dom Q2).
            apply dom_cenv_split_exp with (G := G ++ E0)...
          unfold disjoint in *. simpl_env in WFC. fsetdec.
        apply wf_lenv_disjoint in WFL. solve_uniq.
        apply cenv_split_exp_proc...
    apply IHTyp2... apply wf_lenv_split_right with (D1 := D1) (D3 := D3).
      eapply lenv_split_strengthen_cenv_right with (Q1 := Q1) (Z := None) in H; eauto.
        apply lenv_split_weakening...
          apply wf_cenv_split_exp_right with (Q1 := Q1) (Q3 := Q3).
          apply cenv_split_exp_weakening...
          apply wf_cenv_disjoint in WFC.
          assert (dom Q3 [=] dom Q1 `union` dom Q2).
            apply dom_cenv_split_exp with (G := G ++ E0)...
          unfold disjoint in *. simpl_env in WFC. fsetdec.
        apply wf_lenv_disjoint in WFL. solve_uniq.
        apply cenv_split_exp_proc...
    apply lenv_split_weakening...
      apply wf_lenv_disjoint in WFL. solve_uniq.
      apply cenv_split_exp_weakening...
      apply wf_cenv_disjoint in WFC. solve_uniq.
  Case "typing_let".
    apply typing_let
      with (D1 := D1) (D2 := D2) (Q1 := Q1) (Q2 := Q2) (T1 := T1) (T2 := T2).
    apply IHTyp1... apply wf_lenv_split_left with (D2 := D2) (D3 := D3).
      eapply lenv_split_strengthen_cenv_left with (Q2 := Q2) (Z := None) in H; eauto.
        apply lenv_split_weakening...
          apply wf_cenv_split_exp_left with (Q2 := Q2) (Q3 := Q3).
          apply cenv_split_exp_weakening...
          apply wf_cenv_disjoint in WFC.
          assert (dom Q3 [=] dom Q1 `union` dom Q2).
            apply dom_cenv_split_exp with (G := G ++ E0)...
          unfold disjoint in *. simpl_env in WFC. fsetdec.
        apply wf_lenv_disjoint in WFL. solve_uniq.
        apply cenv_split_exp_proc...
    apply IHTyp2... apply wf_lenv_split_right with (D1 := D1) (D3 := D3).
      eapply lenv_split_strengthen_cenv_right with (Q1 := Q1) (Z := None) in H; eauto.
        apply lenv_split_weakening...
          apply wf_cenv_split_exp_right with (Q1 := Q1) (Q3 := Q3).
          apply cenv_split_exp_weakening...
          apply wf_cenv_disjoint in WFC.
          assert (dom Q3 [=] dom Q1 `union` dom Q2).
            apply dom_cenv_split_exp with (G := G ++ E0)...
          unfold disjoint in *. simpl_env in WFC. fsetdec.
        apply wf_lenv_disjoint in WFL. solve_uniq.
        apply cenv_split_exp_proc...
    apply lenv_split_weakening...
      apply wf_lenv_disjoint in WFL. solve_uniq.
      apply cenv_split_exp_weakening...
      apply wf_cenv_disjoint in WFC. solve_uniq.
  Case "typing_case".
    apply typing_case
      with (D1 := D1) (D2 := D2) (Q1 := Q1) (Q2 := Q2) (T1 := T1) (T2 := T2).
    apply IHTyp1... apply wf_lenv_split_left with (D2 := D2) (D3 := D3).
      eapply lenv_split_strengthen_cenv_left with (Q2 := Q2) (Z := None) in H; eauto.
        apply lenv_split_weakening...
          apply wf_cenv_split_exp_left with (Q2 := Q2) (Q3 := Q3).
          apply cenv_split_exp_weakening...
          apply wf_cenv_disjoint in WFC.
          assert (dom Q3 [=] dom Q1 `union` dom Q2).
            apply dom_cenv_split_exp with (G := G ++ E0)...
          unfold disjoint in *. simpl_env in WFC. fsetdec.
        apply wf_lenv_disjoint in WFL. solve_uniq.
        apply cenv_split_exp_proc...
    apply IHTyp2... apply wf_lenv_split_right with (D1 := D1) (D3 := D3).
      eapply lenv_split_strengthen_cenv_right with (Q1 := Q1) (Z := None) in H; eauto.
        apply lenv_split_weakening...
          apply wf_cenv_split_exp_right with (Q1 := Q1) (Q3 := Q3).
          apply cenv_split_exp_weakening...
          apply wf_cenv_disjoint in WFC.
          assert (dom Q3 [=] dom Q1 `union` dom Q2).
            apply dom_cenv_split_exp with (G := G ++ E0)...
          unfold disjoint in *. simpl_env in WFC. fsetdec.
        apply wf_lenv_disjoint in WFL. solve_uniq.
        apply cenv_split_exp_proc...
    apply IHTyp3... apply wf_lenv_split_right with (D1 := D1) (D3 := D3).
      eapply lenv_split_strengthen_cenv_right with (Q1 := Q1) (Z := None) in H; eauto.
        apply lenv_split_weakening...
          apply wf_cenv_split_exp_right with (Q1 := Q1) (Q3 := Q3).
          apply cenv_split_exp_weakening...
          apply wf_cenv_disjoint in WFC.
          assert (dom Q3 [=] dom Q1 `union` dom Q2).
            apply dom_cenv_split_exp with (G := G ++ E0)...
          unfold disjoint in *. simpl_env in WFC. fsetdec.
        apply wf_lenv_disjoint in WFL. solve_uniq.
        apply cenv_split_exp_proc...
    apply lenv_split_weakening...
      apply wf_lenv_disjoint in WFL. solve_uniq.
      apply cenv_split_exp_weakening...
      apply wf_cenv_disjoint in WFC. solve_uniq.
  Case "typing_go".
    constructor...
    apply dual_weakening...
  Case "typing_yield".
    constructor...
  Case "typing_src".
    constructor...
    apply dual_weakening...
Qed.

Lemma plug_typing_weakening: forall E F G D Q M T T',
  ectx_typing (G ++ E) D Q M T T' ->
  vwf_envs (G ++ F ++ E) Q D ->
  ectx_typing (G ++ F ++ E) D Q M T T'.
Proof with simpl_env;
           eauto using wf_typ_weakening,
                       wf_proto_from_wf_cenv,
                       vwf_envs_pack,
                       lenv_split_strengthen_cenv_left,
                       lenv_split_strengthen_cenv_right.
  intros E F G D Q M T T' ETyp.
  remember (G ++ E) as H.
  generalize dependent G. generalize dependent E.
  (ectx_typing_cases (induction ETyp) Case); intros E0 G EQ VWF; subst;
    apply vwf_envs_unpack in VWF; destruct VWF as [WFL [WFC DJ]];
    assert (wf_env (G ++ F ++ E0)) as WFE; try apply wf_env_from_wf_lenv...
  Case "ectx_typing_hole".
    constructor...
  Case "ectx_typing_seq".
    apply ectx_typing_seq with (D1 := D1) (D2 := D2) (Q1 := Q1) (Q2 := Q2)...
    apply IHETyp... apply wf_lenv_split_left with (D2 := D2) (D3 := D3).
      apply lenv_split_weakening...
        apply lenv_split_strengthen_cenv_left with (Q2 := Q2) (Q3 := Q3) (Z := None)...
          apply cenv_split_exp_proc...
        apply wf_cenv_weakening...
          apply wf_cenv_disjoint in WFC. unfold disjoint in *.
          assert (dom Q3 [=] dom Q1 `union` dom Q2).
            apply dom_cenv_split_exp with (G := G ++ E0)... 
          simpl_env in WFC. fsetdec.
      apply wf_lenv_disjoint in WFL. solve_uniq.
    apply typing_weakening... apply wf_lenv_split_right with (D1 := D1) (D3 := D3).
      apply lenv_split_weakening...
        apply lenv_split_strengthen_cenv_right with (Q1 := Q1) (Q3 := Q3) (Z := None)...
          apply cenv_split_exp_proc...
        apply wf_cenv_weakening...
          apply wf_cenv_disjoint in WFC. unfold disjoint in *.
          assert (dom Q3 [=] dom Q1 `union` dom Q2).
            apply dom_cenv_split_exp with (G := G ++ E0)... 
          simpl_env in WFC. fsetdec.
      apply wf_lenv_disjoint in WFL. solve_uniq.
    apply lenv_split_weakening...
      apply wf_lenv_disjoint in WFL. solve_uniq.
      apply cenv_split_exp_weakening...
      apply wf_cenv_disjoint in WFC. solve_uniq.
  Case "ectx_typing_appl".
    eapply ectx_typing_appl.
      eapply IHETyp; eauto.
        eapply wf_lenv_split_left.
          eapply lenv_split_strengthen_cenv_left with (Q2 := Q2) (Z := None) in H0; eauto.
            apply lenv_split_weakening; eauto.
              apply wf_cenv_split_exp_left with (Q2 := Q2) (Q3 := Q3).
                apply cenv_split_exp_weakening...
                apply wf_cenv_disjoint in WFC. unfold disjoint in *.
                assert (dom Q3 [=] dom Q1 `union` dom Q2).
                  apply dom_cenv_split_exp with (G := G ++ E0)... 
                simpl_env in WFC. fsetdec.
              apply wf_lenv_disjoint in WFL. solve_uniq.
            apply cenv_split_exp_proc...
      eapply typing_weakening; eauto.
        eapply wf_lenv_split_right.
          eapply lenv_split_strengthen_cenv_right with (Q1 := Q1) (Z := None) in H0; eauto.
            apply lenv_split_weakening; eauto.
              apply wf_cenv_split_exp_right with (Q1 := Q1) (Q3 := Q3).
                apply cenv_split_exp_weakening...
                apply wf_cenv_disjoint in WFC. unfold disjoint in *.
                assert (dom Q3 [=] dom Q1 `union` dom Q2).
                  apply dom_cenv_split_exp with (G := G ++ E0)... 
                simpl_env in WFC. fsetdec.
              apply wf_lenv_disjoint in WFL. solve_uniq.
            apply cenv_split_exp_proc...
      eapply lenv_split_weakening; auto.
        apply wf_lenv_disjoint in WFL. solve_uniq.
      eapply cenv_split_exp_weakening; auto.
        apply wf_cenv_disjoint in WFC. solve_uniq.
  Case "ectx_typing_appr".
    eapply ectx_typing_appr.
      eapply typing_weakening; eauto.
        eapply wf_lenv_split_left.
          eapply lenv_split_strengthen_cenv_left with (Q2 := Q2) (Z := None) in H0; eauto.
            apply lenv_split_weakening; eauto.
              apply wf_cenv_split_exp_left with (Q2 := Q2) (Q3 := Q3).
                apply cenv_split_exp_weakening...
                apply wf_cenv_disjoint in WFC. unfold disjoint in *.
                assert (dom Q3 [=] dom Q1 `union` dom Q2).
                  apply dom_cenv_split_exp with (G := G ++ E0)... 
                simpl_env in WFC. fsetdec.
              apply wf_lenv_disjoint in WFL. solve_uniq.
            apply cenv_split_exp_proc...
      eapply IHETyp; eauto.
        eapply wf_lenv_split_right.
          eapply lenv_split_strengthen_cenv_right with (Q1 := Q1) (Z := None) in H0; eauto.
            apply lenv_split_weakening; eauto.
              apply wf_cenv_split_exp_right with (Q1 := Q1) (Q3 := Q3).
                apply cenv_split_exp_weakening...
                apply wf_cenv_disjoint in WFC. unfold disjoint in *.
                assert (dom Q3 [=] dom Q1 `union` dom Q2).
                  apply dom_cenv_split_exp with (G := G ++ E0)... 
                simpl_env in WFC. fsetdec.
              apply wf_lenv_disjoint in WFL. solve_uniq.
            apply cenv_split_exp_proc...
      eapply lenv_split_weakening; auto.
        apply wf_lenv_disjoint in WFL. solve_uniq.
      eapply cenv_split_exp_weakening; auto.
        apply wf_cenv_disjoint in WFC. solve_uniq.
  Case "ectx_typing_fst".
    econstructor...
  Case "ectx_typing_snd".
    econstructor...
  Case "ectx_typing_mpairl".
    apply ectx_typing_mpairl with (D1 := D1) (D2 := D2) (Q1 := Q1) (Q2 := Q2).
    apply IHETyp... apply wf_lenv_split_left with (D2 := D2) (D3 := D3).
      eapply lenv_split_strengthen_cenv_left with (Q2 := Q2) (Z := None) in H0; eauto.
        apply lenv_split_weakening...
          apply wf_cenv_split_exp_left with (Q2 := Q2) (Q3 := Q3).
            apply cenv_split_exp_weakening...
            apply wf_cenv_disjoint in WFC.
            assert (dom Q3 [=] dom Q1 `union` dom Q2).
              apply dom_cenv_split_exp with (G := G ++ E0)...
            unfold disjoint in *. simpl_env in WFC. fsetdec.
          apply wf_lenv_disjoint in WFL. solve_uniq.
        apply cenv_split_exp_proc...
    apply typing_weakening... apply wf_lenv_split_right with (D1 := D1) (D3 := D3).
      eapply lenv_split_strengthen_cenv_right with (Q1 := Q1) (Z := None) in H0; eauto.
        apply lenv_split_weakening...
          apply wf_cenv_split_exp_right with (Q1 := Q1) (Q3 := Q3).
            apply cenv_split_exp_weakening...
            apply wf_cenv_disjoint in WFC.
            assert (dom Q3 [=] dom Q1 `union` dom Q2).
              apply dom_cenv_split_exp with (G := G ++ E0)...
            unfold disjoint in *. simpl_env in WFC. fsetdec.
          apply wf_lenv_disjoint in WFL. solve_uniq.
        apply cenv_split_exp_proc...
    apply lenv_split_weakening...
      apply wf_lenv_disjoint in WFL. solve_uniq.
      apply cenv_split_exp_weakening...
      apply wf_cenv_disjoint in WFC. solve_uniq.
  Case "ectx_typing_mpairr".
    apply ectx_typing_mpairr with (D1 := D1) (D2 := D2) (Q1 := Q1) (Q2 := Q2).
    apply typing_weakening... apply wf_lenv_split_left with (D2 := D2) (D3 := D3).
      eapply lenv_split_strengthen_cenv_left with (Q2 := Q2) (Z := None) in H0; eauto.
        apply lenv_split_weakening...
          apply wf_cenv_split_exp_left with (Q2 := Q2) (Q3 := Q3).
            apply cenv_split_exp_weakening...
            apply wf_cenv_disjoint in WFC.
            assert (dom Q3 [=] dom Q1 `union` dom Q2).
              apply dom_cenv_split_exp with (G := G ++ E0)...
            unfold disjoint in *. simpl_env in WFC. fsetdec.
          apply wf_lenv_disjoint in WFL. solve_uniq.
        apply cenv_split_exp_proc...
    apply IHETyp... apply wf_lenv_split_right with (D1 := D1) (D3 := D3).
      eapply lenv_split_strengthen_cenv_right with (Q1 := Q1) (Q3 := Q3) in H0; eauto.
        apply lenv_split_weakening...
          apply wf_cenv_split_exp_right with (Q1 := Q1) (Q3 := Q3).
            apply cenv_split_exp_weakening...
            apply wf_cenv_disjoint in WFC.
            assert (dom Q3 [=] dom Q1 `union` dom Q2).
              apply dom_cenv_split_exp with (G := G ++ E0)...
            unfold disjoint in *. simpl_env in WFC. fsetdec.
          apply wf_lenv_disjoint in WFL. solve_uniq.
        apply cenv_split_exp_proc...
    apply lenv_split_weakening...
      apply wf_lenv_disjoint in WFL. solve_uniq.
      apply cenv_split_exp_weakening...
      apply wf_cenv_disjoint in WFC. solve_uniq.
  Case "ectx_typing_let".
    apply ectx_typing_let
      with (D1 := D1) (D2 := D2) (Q1 := Q1) (Q2 := Q2) (T1 := T1) (T2 := T2).
    apply IHETyp... apply wf_lenv_split_left with (D2 := D2) (D3 := D3).
      eapply lenv_split_strengthen_cenv_left with (Q2 := Q2) (Z := None) in H0; eauto.
        apply lenv_split_weakening...
          apply wf_cenv_split_exp_left with (Q2 := Q2) (Q3 := Q3).
            apply cenv_split_exp_weakening...
            apply wf_cenv_disjoint in WFC.
            assert (dom Q3 [=] dom Q1 `union` dom Q2).
              apply dom_cenv_split_exp with (G := G ++ E0)...
            unfold disjoint in *. simpl_env in WFC. fsetdec.
          apply wf_lenv_disjoint in WFL. solve_uniq.
        apply cenv_split_exp_proc...
    apply typing_weakening... apply wf_lenv_split_right with (D1 := D1) (D3 := D3).
      eapply lenv_split_strengthen_cenv_right with (Q1 := Q1) (Z := None) in H0; eauto.
        apply lenv_split_weakening...
          apply wf_cenv_split_exp_right with (Q1 := Q1) (Q3 := Q3).
            apply cenv_split_exp_weakening...
            apply wf_cenv_disjoint in WFC.
            assert (dom Q3 [=] dom Q1 `union` dom Q2).
              apply dom_cenv_split_exp with (G := G ++ E0)...
            unfold disjoint in *. simpl_env in WFC. fsetdec.
          apply wf_lenv_disjoint in WFL. solve_uniq.
        apply cenv_split_exp_proc...
    apply lenv_split_weakening...
      apply wf_lenv_disjoint in WFL. solve_uniq.
      apply cenv_split_exp_weakening...
      apply wf_cenv_disjoint in WFC. solve_uniq.
  Case "ectx_typing_inl".
    econstructor...
  Case "ectx_typing_inr".
    econstructor...
  Case "ectx_typing_case".
    apply ectx_typing_case
      with (D1 := D1) (D2 := D2) (Q1 := Q1) (Q2 := Q2) (T1 := T1) (T2 := T2).
    apply IHETyp... apply wf_lenv_split_left with (D2 := D2) (D3 := D3).
      eapply lenv_split_strengthen_cenv_left with (Q2 := Q2) (Z := None) in H1; eauto.
        apply lenv_split_weakening...
          apply wf_cenv_split_exp_left with (Q2 := Q2) (Q3 := Q3).
            apply cenv_split_exp_weakening...
            apply wf_cenv_disjoint in WFC.
            assert (dom Q3 [=] dom Q1 `union` dom Q2).
              apply dom_cenv_split_exp with (G := G ++ E0)...
            unfold disjoint in *. simpl_env in WFC. fsetdec.
          apply wf_lenv_disjoint in WFL. solve_uniq.
        apply cenv_split_exp_proc...
    apply typing_weakening... apply wf_lenv_split_right with (D1 := D1) (D3 := D3).
      eapply lenv_split_strengthen_cenv_right with (Q1 := Q1) (Z := None) in H1; eauto.
        apply lenv_split_weakening...
          apply wf_cenv_split_exp_right with (Q1 := Q1) (Q3 := Q3).
            apply cenv_split_exp_weakening...
            apply wf_cenv_disjoint in WFC.
            assert (dom Q3 [=] dom Q1 `union` dom Q2).
              apply dom_cenv_split_exp with (G := G ++ E0)...
            unfold disjoint in *. simpl_env in WFC. fsetdec.
          apply wf_lenv_disjoint in WFL. solve_uniq.
        apply cenv_split_exp_proc...
    apply typing_weakening... apply wf_lenv_split_right with (D1 := D1) (D3 := D3).
      eapply lenv_split_strengthen_cenv_right with (Q1 := Q1) (Z := None) in H1; eauto.
        apply lenv_split_weakening...
          apply wf_cenv_split_exp_right with (Q1 := Q1) (Q3 := Q3).
            apply cenv_split_exp_weakening...
            apply wf_cenv_disjoint in WFC.
            assert (dom Q3 [=] dom Q1 `union` dom Q2).
              apply dom_cenv_split_exp with (G := G ++ E0)...
            unfold disjoint in *. simpl_env in WFC. fsetdec.
          apply wf_lenv_disjoint in WFL. solve_uniq.
        apply cenv_split_exp_proc...
    apply lenv_split_weakening...
      apply wf_lenv_disjoint in WFL. solve_uniq.
      apply cenv_split_exp_weakening...
      apply wf_cenv_disjoint in WFC. solve_uniq.
  Case "ectx_typing_go".
    constructor...
    apply dual_weakening...
  Case "ectx_typing_yield".
    constructor...
Qed.

(************************************************************************ *)
(** Environments and splitting *)

Lemma list_eq_case3' : forall (A : Type) (a b : A) (aL aR bL bR : list A),
  aL ++ [a] ++ aR = bL ++ [b] ++ bR ->
  a = b \/ In a bL \/ In a bR.
Proof.
  induction aL; induction bL; simpl; intros.
  injection H; auto.
  injection H; auto.
  injection H; simpl in *; intros. subst. auto with datatypes.
  injection H; simpl in *; intros. subst.
    injection H. intros.
    specialize (IHaL aR bL bR H1).
    intuition.
Qed.

Lemma list_eq_case3 : forall (A : Type) (a b : A) (aL aR bL bR : list A),
  aL ++ [a] ++ aR = bL ++ [b] ++ bR ->
  a = b \/ (exists bLL, exists bLR, bL = bLL ++ [a] ++ bLR)
            \/ (exists bRL, exists bRR, bR = bRL ++ [a] ++ bRR).
Proof with auto.
  intros. apply list_eq_case3' in H.
  destruct H as [Eq | [Left | Right]]...
    right. left. simpl. apply In_split...
    right. right. simpl. apply In_split...
Qed.

Lemma lenv_split_cases_mid: forall G Q D1 D2 DL x T DR,
  lenv_split G Q D1 D2 (DL ++ [(x, lbind_typ T)] ++ DR) ->
  (exists D1L, exists D1R, exists D2L, exists D2R,
    D1 = D1L ++ [(x, lbind_typ T)] ++ D1R /\
    D2 = D2L ++ D2R /\
    lenv_split G Q D1L D2L DL /\
    lenv_split G Q D1R D2R DR) \/
  (exists D1L, exists D1R, exists D2L, exists D2R,
    D1 = D1L ++ D1R /\
    D2 = D2L ++ [(x, lbind_typ T)] ++ D2R /\
    lenv_split G Q D1L D2L DL /\
    lenv_split G Q D1R D2R DR).
Proof.
  intros G Q D1 D2 DL x T DR S.
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
          eapply wf_cenv_from_vwf_envs. 
            eapply wf_lenv_split_left; eauto.
    SCase "con".
      lapply (IHS DL DR); auto.
      intros J.
      destruct J as [J | J].
      SSCase "left".
        destruct J as [D1L [D1R [D2L [D2R [Q1 [Q2 [S1 S2]]]]]]].
        left. subst. exists ([(x0, lbind_typ T0)] ++ D1L).
        exists D1R. exists D2L. exists D2R.
        simpl_env in *;
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
          eapply wf_cenv_from_vwf_envs. 
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

Lemma lenv_split_not_in_left: forall G Q D1 D2 D3 x,
  lenv_split G Q D1 D2 D3 ->
  x `in` dom D1 ->
  x `notin` (dom D2 `union` dom G `union` dom Q).
Proof.
  intros G Q D1 D2 D3 x S.
  (lenv_split_cases (induction S) Case);  
    intros; simpl_env in *; try fsetdec.
  Case "lenv_split_left".
    rewrite (dom_lenv_split E Q D1 D2 D3) in H1; auto.
      fsetdec.
  Case "lenv_split_right".
    rewrite (dom_lenv_split E Q D1 D2 D3) in H1; auto.
      fsetdec.
Qed.

Lemma lenv_split_not_in_right: forall G Q D1 D2 D3 x,
  lenv_split G Q D1 D2 D3 ->
  x `in` dom D2 ->
  x `notin` (dom D1 `union` dom G `union` dom Q).
Proof.
  intros.
  eapply lenv_split_not_in_left.
    eapply lenv_split_commute; eauto.  
    auto.
Qed.

Lemma cenv_split_exp_cases_mid: forall G Q1 Q2 QL X d T QR,
  cenv_split_exp G Q1 Q2 (QL ++ [(X, cbind_proto d T)] ++ QR) ->
  (exists Q1L, exists Q1R, exists Q2L, exists Q2R,
    Q1 = Q1L ++ [(X, cbind_proto d T)] ++ Q1R /\
    Q2 = Q2L ++ Q2R /\
    cenv_split_exp G Q1L Q2L QL /\
    cenv_split_exp G Q1R Q2R QR) \/
  (exists Q1L, exists Q1R, exists Q2L, exists Q2R,
    Q1 = Q1L ++ Q1R /\
    Q2 = Q2L ++ [(X, cbind_proto d T)] ++ Q2R /\
    cenv_split_exp G Q1L Q2L QL /\
    cenv_split_exp G Q1R Q2R QR).
Proof.
  intros G D1 D2 DL x d T DR S.
  remember (DL ++ [(x, cbind_proto d T)] ++ DR) as D3.
  generalize dependent DR. generalize dependent DL.
  (cenv_split_exp_cases (induction S) Case);  
    intros DL DR EQ; subst; simpl_env in *.
  Case "cenv_split_exp_empty".
    destruct DL; inversion EQ.
  Case "cenv_split_exp_left".
    destruct DL; simpl in *; inversion EQ; subst; simpl_env in *.
    SCase "nil".
      left. 
      exists cempty. exists Q1. exists cempty. exists Q2. 
      simpl_env. 
      repeat split; auto. 
        apply cenv_split_exp_empty.
          apply wf_cenv_split_exp in S. auto.
    SCase "con".
      lapply (IHS DL DR); auto.
      intros J.
      destruct J as [J | J].
      SSCase "left".
        destruct J as [D1L [D1R [D2L [D2R [EQ1 [EQ2 [S1 S2]]]]]]].
        left. subst. exists ([(X, cbind_proto d0 T0)] ++ D1L).
        exists D1R. exists D2L. exists D2R.
        simpl_env in *;
        repeat split; subst; auto.
      SSCase "right".
        destruct J as [D1L [D1R [D2L [D2R [EQ1 [EQ2 [S1 S2]]]]]]].
        right. exists ([(X, cbind_proto d0 T0)] ++ D1L).
        exists D1R. exists D2L. exists D2R.
        simpl_env in *. 
        repeat split; subst; auto.
  Case "cenv_split_exp_right".
    destruct DL; simpl in *; inversion EQ; subst; simpl_env in *.
    SCase "nil".
      right.
      exists cempty. exists Q1. exists cempty. exists Q2.
      simpl_env in *. 
      repeat split; auto. 
        apply cenv_split_exp_empty.
          apply wf_cenv_split_exp in S. auto.
    SCase "con".
      lapply (IHS DL DR); auto.
      intros J.
      destruct J as [J | J].
      SSCase "left".
        destruct J as [D1L [D1R [D2L [D2R [EQ1 [EQ2 [S1 S2]]]]]]].
        left. exists D1L.
        exists D1R. exists ([(X, cbind_proto d0 T0)] ++ D2L). exists D2R.
        simpl_env in *. repeat split; subst; auto.
    
      SSCase "right".
        destruct J as [D1L [D1R [D2L [D2R [EQ1 [EQ2 [S1 S2]]]]]]].
        right. exists D1L. 
        exists D1R. exists ([(X, cbind_proto d0 T0)] ++ D2L). exists D2R.
        subst. simpl_env in *. repeat split; auto.
Qed.

Lemma cenv_split_exp_not_in_left: forall G Q1 Q2 Q3 X,
  cenv_split_exp G Q1 Q2 Q3 ->
  X `in` dom Q1 ->
  X `notin` (dom Q2 `union` dom G).
Proof.
  intros G Q1 Q2 Q3 x S.
  (cenv_split_exp_cases (induction S) Case);  
    intros; simpl_env in *; try fsetdec.
  Case "cenv_split_exp_left".
    rewrite (dom_cenv_split_exp E Q1 Q2 Q3) in H0; auto.
      fsetdec.
  Case "cenv_split_exp_right".
    rewrite (dom_cenv_split_exp E Q1 Q2 Q3) in H0; auto.
      fsetdec.
Qed.

Lemma cenv_split_exp_not_in_right: forall G Q1 Q2 Q3 X,
  cenv_split_exp G Q1 Q2 Q3 ->
  X `in` dom Q2 ->
  X `notin` (dom Q1 `union` dom G).
Proof.
  intros.
  eapply cenv_split_exp_not_in_left.
    eapply cenv_split_exp_commute; eauto.  
    auto.
Qed.

Lemma cenv_split_exp_mid_left: forall E X d T QL QR Q Q',
  cenv_split_exp E (QL ++ [(X, cbind_proto d T)] ++ QR) Q Q' ->
  exists QL', exists QR', Q' = (QL' ++ [(X, cbind_proto d T)] ++ QR').
Proof with auto.
  intros E X d T QL QR Q Q' CS.
  remember (QL ++ [(X, cbind_proto d T)] ++ QR) as Q0.
  generalize dependent QL. generalize dependent QR.
  (cenv_split_exp_cases (induction CS) Case); intros QR QL EQ; 
    destruct QL; simpl_env in *; inversion EQ; subst...
  
  Case "cenv_split_exp_left".
    exists cempty. exists Q3. simpl_env; auto.

    destruct (IHCS QR QL) as [QL' [QR' EQ']]; auto.
    exists ([(X0, cbind_proto d0 T0)] ++ QL').
    exists QR'. subst. simpl_env; auto.

  Case "cenv_split_exp_right".
   destruct (IHCS QR cempty) as [QL' [QR' EQ']]; auto.
   exists ([(X0, cbind_proto d0 T0)] ++ QL').
   exists QR'. subst.  simpl_env; auto.

   destruct (IHCS QR ([p] ++ QL)) as [QL' [QR' EQ']]; auto.
   exists ([(X0, cbind_proto d0 T0)] ++ QL').
   exists QR'. subst. simpl_env; auto.
Qed.

Lemma cenv_split_exp_mid_right: forall E Q X d T QL QR Q',
  cenv_split_exp E Q (QL ++ [(X, cbind_proto d T)] ++ QR) Q' ->
  exists QL', exists QR', Q' = (QL' ++ [(X, cbind_proto d T)] ++ QR').
Proof with eauto.
  intros. apply cenv_split_exp_commute in H.
  eapply cenv_split_exp_mid_left...
Qed.

Lemma cenv_split_proc_mid_left: forall E X d T QL QR Q Q' Z,
  cenv_split_proc E (QL ++ [(X, cbind_proto d T)] ++ QR) Q Q' Z ->
  exists QL', exists QR', exists d', Q' = (QL' ++ [(X, cbind_proto d' T)] ++ QR').
Proof with auto.
  intros E X d T QL QR Q Q' Z CS.
  remember (QL ++ [(X, cbind_proto d T)] ++ QR) as Q0.
  generalize dependent QL. generalize dependent QR.
  (cenv_split_proc_cases (induction CS) Case); intros QR QL EQ; 
    destruct QL; simpl_env in *; inversion EQ; subst...
  
  Case "cenv_split_proc_left".
    exists cempty. exists Q3. exists d. simpl_env; auto.

    destruct (IHCS QR QL) as [QL' [QR' [d' EQ']]]; auto.
    exists ([(X0, cbind_proto d0 T0)] ++ QL').
    exists QR'. exists d'. subst. simpl_env; auto.

  Case "cenv_split_proc_right".
   destruct (IHCS QR cempty) as [QL' [QR' [d' EQ']]]; auto.
   exists ([(X0, cbind_proto d0 T0)] ++ QL').
   exists QR'. exists d'. subst.  simpl_env; auto.

   destruct (IHCS QR ([p] ++ QL)) as [QL' [QR' [d' EQ']]]; auto.
   exists ([(X0, cbind_proto d0 T0)] ++ QL').
   exists QR'. exists d'. subst. simpl_env; auto.

 Case "cenv_split_proc_snksrc".
   exists cempty. exists Q3. exists cdir_both. simpl_env; auto.

   simpl_env in *. apply cenv_split_exp_mid_left in H.
   destruct H as [QL' [QR' EQ']].   

   exists ([(X0, cbind_proto cdir_both T0)] ++ QL').
   exists QR'. exists d. subst. simpl_env; auto.

 Case "cenv_split_proc_srcsnk".
   exists cempty. exists Q3. exists cdir_both. simpl_env; auto.

   simpl_env in *. apply cenv_split_exp_mid_left in H.
   destruct H as [QL' [QR' EQ']]; auto.

   exists ([(X0, cbind_proto cdir_both T0)] ++ QL').
   exists QR'. exists d. subst. simpl_env; auto.
Qed.

Lemma cenv_split_proc_mid_right: forall E Q X d T QL QR Q' Z,
  cenv_split_proc E Q (QL ++ [(X, cbind_proto d T)] ++ QR) Q' Z ->
  exists QL', exists QR', exists d', Q' = (QL' ++ [(X, cbind_proto d' T)] ++ QR').
Proof with eauto.
  intros. apply cenv_split_proc_commute in H.
  eapply cenv_split_proc_mid_left...
Qed.

Lemma lenv_split_notin_dom : forall E Q D1 D2 D3 x,
  x `notin` dom D3 ->
  lenv_split E Q D1 D2 D3 ->
  (x `notin` dom D1 /\ x `notin` dom D2).
Proof.
  intros E Q D1 D2 D3 x NI S.
  induction S; intros; auto.
Qed.

Lemma cenv_split_exp_notin_dom : forall E Q1 Q2 Q3 X,
  X `notin` dom Q3 ->
  cenv_split_exp E Q1 Q2 Q3 ->
  (X `notin` dom Q1 /\ X `notin` dom Q2).
Proof.
  intros E Q1 Q2 Q3 X NI S.
  induction S; intros; auto.
Qed.

Lemma cenv_split_proc_notin_dom : forall E Q1 Q2 Q3 X Z,
  X `notin` dom Q3 ->
  cenv_split_proc E Q1 Q2 Q3 Z ->
  (X `notin` dom Q1 /\ X `notin` dom Q2).
Proof with auto.
  intros E Q1 Q2 Q3 X Z NI S.
  induction S; intros...
    apply cenv_split_exp_notin_dom with (X := X) in H...
    apply cenv_split_exp_notin_dom with (X := X) in H...
Qed.

Lemma cenv_split_exp_mid_left_strengthen: forall E Q1L X d T Q1R Q2 Q3L d' Q3R,
  cenv_split_exp E (Q1L ++ [(X, cbind_proto d T)] ++ Q1R) Q2 (Q3L ++ [(X, cbind_proto d' T)] ++ Q3R) 
  -> (d = d' /\ X `notin` dom Q2).
Proof.
  intros E Q1L X d T Q1R Q2 Q3L d' Q3R S.
  remember (Q1L ++ [(X, cbind_proto d T)] ++ Q1R) as Q1.
  remember (Q3L ++ [(X, cbind_proto d' T)] ++ Q3R) as Q3.
  generalize dependent Q3R. generalize dependent Q3L.
  generalize dependent Q1R. generalize dependent Q1L.
  
  (cenv_split_exp_cases (induction S) Case); intros Q1L Q1R EQ1 Q3L Q3R EQ2; destruct Q1L; simpl_env in *; inversion EQ1; subst; destruct Q3L; simpl_env in*; inversion EQ2; subst; simpl_env in *; try fsetdec; auto.

  Case "cenv_split_exp_left".
    split; auto.
    apply cenv_split_exp_notin_dom
      with (E := E) (Q1 := Q1R) (Q2 := Q2) in H0; auto.

    assert (X `notin` dom (Q1L ++ [(X, cbind_proto d T)] ++ Q1R)).
    apply cenv_split_exp_notin_dom
      with (E := E) (Q1 := Q1L ++ [(X, cbind_proto d T)] ++ Q1R) (Q2 := Q2)
      in H0; auto. intuition.

    simpl_env in H2. fsetdec.

    destruct (IHS Q1L Q1R) with (Q3L0:=Q3L)(Q3R0:=Q3R) as [EQD NI]; auto.
  
  Case "cenv_split_exp_right".
    assert (X `notin` dom ([(X, cbind_proto d T)] ++ Q1R)).
    apply cenv_split_exp_notin_dom
      with (E := E) (Q1 := [(X, cbind_proto d T)] ++ Q1R) (Q2 := Q2)
      in H0; auto. intuition.

    simpl_env in H3. fsetdec.

    destruct (IHS cempty Q1R) with (Q3L0:=Q3L)(Q3R0:=Q3R) as [EQD NI]; auto. subst.

    assert (X `notin` dom ([p] ++ Q1L ++ [(X, cbind_proto d T)] ++ Q1R)).
    apply cenv_split_exp_notin_dom
      with (E := E) (Q1 := [p] ++ Q1L ++ [(X, cbind_proto d T)] ++ Q1R) (Q2 := Q2)
      in H0; auto. intuition.

    simpl_env in H3. fsetdec.

    destruct (IHS ([p] ++ Q1L) Q1R) with (Q3L0:=Q3L)(Q3R0:=Q3R) as [EQD NI]; auto.
Qed.

Lemma cenv_split_exp_mid_right_strengthen: forall E Q2L X d T Q2R Q1 Q3L d' Q3R,
  cenv_split_exp E Q1 (Q2L ++ [(X, cbind_proto d T)] ++ Q2R) (Q3L ++ [(X, cbind_proto d' T)] ++ Q3R) 
  ->
  d = d' /\ X `notin` dom Q1.
Proof.
  intros. apply cenv_split_exp_commute in H.
  eapply cenv_split_exp_mid_left_strengthen; eauto.
Qed.

Lemma cenv_split_proc_mid_left_strengthen: forall E Q1L X d T Q1R Q2 Q3L d' Q3R Z,
  cenv_split_proc E (Q1L ++ [(X, cbind_proto d T)] ++ Q1R) Q2 (Q3L ++ [(X, cbind_proto d' T)] ++ Q3R) Z
  ->
  (d = d' /\ X `notin` dom Q2) \/
  (exists Q2L, exists Q2R, exists d'', Q2 = Q2L ++ [(X, cbind_proto d'' T)] ++ Q2R).
Proof.
  intros E Q1L X d T Q1R Q2 Q3L d' Q3R Z S.
  remember (Q1L ++ [(X, cbind_proto d T)] ++ Q1R) as Q1.
  remember (Q3L ++ [(X, cbind_proto d' T)] ++ Q3R) as Q3.
  generalize dependent Q3R. generalize dependent Q3L.
  generalize dependent Q1R. generalize dependent Q1L.
  
  (cenv_split_proc_cases (induction S) Case); intros Q1L Q1R EQ1 Q3L Q3R EQ2; destruct Q1L; simpl_env in *; inversion EQ1; subst; destruct Q3L; simpl_env in*; inversion EQ2; subst; simpl_env in *; try fsetdec; auto.

  Case "cenv_split_proc_left".
    left; split; auto.
    apply cenv_split_proc_notin_dom
      with (E := E) (Q1 := Q1R) (Q2 := Q2) (Z := Z) in H0; auto.

    assert (X `notin` dom (Q1L ++ [(X, cbind_proto d T)] ++ Q1R)).
    apply cenv_split_proc_notin_dom
      with (E := E) (Q1 := Q1L ++ [(X, cbind_proto d T)] ++ Q1R) (Q2 := Q2) (Z := Z)
      in H0; auto. intuition.

    simpl_env in H2. fsetdec.

    destruct (IHS Q1L Q1R) with (Q3L0:=Q3L)(Q3R0:=Q3R) as [[EQD NI] | EX]; auto.
  
  Case "cenv_split_proc_right".
    assert (X `notin` dom ([(X, cbind_proto d T)] ++ Q1R)).
    apply cenv_split_proc_notin_dom
      with (E := E) (Q1 := [(X, cbind_proto d T)] ++ Q1R) (Q2 := Q2) (Z := Z)
      in H0; auto. intuition.

    simpl_env in H3. fsetdec.

    destruct (IHS cempty Q1R) with (Q3L0:=Q3L)(Q3R0:=Q3R) as [[EQD NI] | [Q2L [Q2R [d'' EQX]]]]; auto. subst.
    right. exists ([(X0, cbind_proto d0 T0)] ++ Q2L). 
    exists Q2R. exists d''. simpl_env; auto.

    assert (X `notin` dom ([p] ++ Q1L ++ [(X, cbind_proto d T)] ++ Q1R)).
    apply cenv_split_proc_notin_dom
      with (E := E) (Q1 := [p] ++ Q1L ++ [(X, cbind_proto d T)] ++ Q1R) (Q2 := Q2) (Z := Z)
      in H0; auto. intuition.

    simpl_env in H3. fsetdec.

    destruct (IHS ([p] ++ Q1L) Q1R) with (Q3L0:=Q3L)(Q3R0:=Q3R) as [[EQD NI] | [Q2L [Q2R [d'' EQX]]]]; auto. subst.
    right. exists ([(X0, cbind_proto d0 T0)] ++ Q2L). 
    exists Q2R. exists d''. simpl_env; auto.

  Case "cenv_split_proc_snksrc".
    right.
    exists cempty. exists Q2. exists cdir_src. simpl_env; auto.

    assert (X `notin` dom (Q1L ++ [(X, cbind_proto d T)] ++ Q1R)).
    apply cenv_split_exp_notin_dom
      with (X := X) (E := E) (Q1 := Q1L ++ [(X, cbind_proto d T)] ++ Q1R) (Q2 := Q2)
      in H; auto. intuition.

    assert (X `notin` (dom Q2 `union` dom E)) as NI.
      eapply cenv_split_exp_not_in_left; eauto.
      simpl_env. fsetdec.

    right. exists cempty. exists Q2. exists cdir_src. simpl_env; auto.
    left. apply cenv_split_exp_mid_left_strengthen in H.
    split. intuition. fsetdec.

  Case "cenv_split_proc_srcsnk".
    right.
    exists cempty. exists Q2. exists cdir_snk. simpl_env; auto.

    assert (X `notin` dom (Q1L ++ [(X, cbind_proto d T)] ++ Q1R)).
    apply cenv_split_exp_notin_dom
      with (X := X) (E := E) (Q1 := Q1L ++ [(X, cbind_proto d T)] ++ Q1R) (Q2 := Q2)
      in H; auto. intuition.

    assert (X `notin` (dom Q2 `union` dom E)) as NI.
      eapply cenv_split_exp_not_in_left; eauto.
      simpl_env. fsetdec.

    right. exists cempty. exists Q2. exists cdir_snk. simpl_env; auto.
    left. apply cenv_split_exp_mid_left_strengthen in H.
    split. intuition. fsetdec.
Qed.

Lemma cenv_split_proc_mid_right_strengthen: forall E Q2L X d T Q2R Q1 Q3L d' Q3R Z,
  cenv_split_proc E Q1 (Q2L ++ [(X, cbind_proto d T)] ++ Q2R) (Q3L ++ [(X, cbind_proto d' T)] ++ Q3R) Z
  ->
  (d = d' /\ X `notin` dom Q1) \/
  (exists Q1L, exists Q1R, exists d'', Q1 = Q1L ++ [(X, cbind_proto d'' T)] ++ Q1R).
Proof.
  intros. apply cenv_split_proc_commute in H.
  eapply cenv_split_proc_mid_left_strengthen; eauto.
Qed.

Lemma lenv_split_assoc: forall E Q D11 D12 D13 D21 D,
  lenv_split E Q D11 D12 D13 ->
  lenv_split E Q D13 D21 D ->
  exists D23, lenv_split E Q D12 D21 D23 /\ lenv_split E Q D11 D23 D.
Proof.
  intros E Q D11 D12 D13 D21 D S1 S2.  
  generalize dependent D. generalize dependent D21. 
  (lenv_split_cases (induction S1) Case); intros D21 D S2.

  Case "lenv_split_empty".
    exists D.
    split; auto. apply lenv_split_left_id. eapply wf_lenv_split. eauto.

  Case "lenv_split_left".
    remember ([(x, lbind_typ T)] ++ D3) as DD.
    generalize dependent D3.
    (lenv_split_cases (induction S2) SCase); intros D3' LS NI IHO EQ; inversion EQ; subst.
    
    SCase "lenv_split_left".
      destruct (IHO D3 D4) as [D23 [S1' S2']].
      auto.
      exists D23. split; auto.

    SCase "lenv_split_right".
      destruct IHS2 with (D5:=D3') as [D23 [S1' S2']]; auto.
      exists ([(x0, lbind_typ T0)] ++ D23).
      split.  apply lenv_split_right; auto. 
      apply lenv_split_notin_dom
        with (E := E) (Q := Q) (D1 := [(x, lbind_typ T)] ++ D1) (D2 := D23) in H4;
      auto.
      apply lenv_split_right; auto.
      
  Case "lenv_split_right".
    remember ([(x, lbind_typ T)] ++ D3) as DD.
    generalize dependent D3.
    (lenv_split_cases (induction S2) SCase); intros D3' LS NI IHO EQ; inversion EQ; subst.
    
    SCase "lenv_split_left".
      destruct (IHO D3 D4) as [D23 [S1' S2']].
      auto.
      exists ([(x, lbind_typ T)] ++ D23). split; auto.
      apply lenv_split_left; auto.
      apply lenv_split_notin_dom
        with (E := E) (Q := Q) (D1 := D1) (D2 := D23) in H4; auto.

    SCase "lenv_split_right".
      destruct IHS2 with (D5:=D3') as [D23 [S1' S2']]; auto.
      exists ([(x0, lbind_typ T0)] ++ D23).
      split. apply lenv_split_right; auto.
      apply lenv_split_notin_dom
        with (E := E) (Q := Q) (D1 := D1) (D2 := D23) in H4; auto.
      apply lenv_split_right; auto.
Qed.

Lemma cenv_split_exp_assoc: forall E Q11 Q12 Q13 Q21 Q,
  cenv_split_exp E Q11 Q12 Q13 ->
  cenv_split_exp E Q13 Q21 Q ->
  exists Q23, cenv_split_exp E Q12 Q21 Q23 /\ cenv_split_exp E Q11 Q23 Q.
Proof.
  intros E Q11 Q12 Q13 Q21 Q S1.
  revert Q21. revert Q. 
  
  (cenv_split_exp_cases (induction S1) Case); intros Q Q21 S2.

  Case "cenv_split_exp_empty".
    exists Q21; split; auto. apply cenv_split_exp_left_id. 
    eapply wf_cenv_split_exp_right. apply S2.

  Case "cenv_split_exp_left".
    remember ([(X, cbind_proto d T)] ++ Q3) as QL.
    generalize dependent Q3.
    (cenv_split_exp_cases (induction S2) SCase); intros Q3' S2' NI IHO EQ; inversion EQ; subst.

    SCase "cenv_split_exp_left".
      destruct (IHO Q4 Q3) as [Q23 [SA SB]]; auto.
      exists Q23; split; auto.

    SCase "cenv_split_exp_right".
      destruct IHS2 with (Q5:=Q3') as [Q23 [SA SB]]; auto.
      exists ([(X0, cbind_proto d0 T0)] ++ Q23); split; auto.
      apply cenv_split_exp_right; auto. 
      apply cenv_split_proc_notin_dom
        with (E := E) (Q1 := [(X, cbind_proto d T)] ++ Q1) (Q2 := Q23) (Z := None) in H2;
      try apply cenv_split_exp_proc; auto.

  Case "cenv_split_exp_right".
    remember ([(X, cbind_proto d T)] ++ Q3) as QL.
    generalize dependent Q3.
    (cenv_split_exp_cases (induction S2) SCase); intros Q3' S2' NI IHO EQ; inversion EQ; subst.
    
    SCase "cenv_split_exp_left".
      destruct (IHO Q4 Q3) as [Q23 [SA SB]]; auto.
      exists ([(X, cbind_proto d T)] ++ Q23); split ;auto.
      apply cenv_split_exp_left; auto.
      apply cenv_split_proc_notin_dom
        with (E := E) (Q1 := Q1) (Q2 := Q23) (Z := None) in H2;
      try apply cenv_split_exp_proc; auto.

    SCase "cenv_split_exp_right".
      destruct IHS2 with (Q5:=Q3') as [Q23 [SA SB]]; auto.
      exists ([(X0, cbind_proto d0 T0)] ++ Q23); split; auto.
      apply cenv_split_exp_right; auto.
      apply cenv_split_proc_notin_dom
        with (E := E) (Q1 := Q1) (Q2 := Q23) (Z := None) in H2;
      try apply cenv_split_exp_proc; auto.
Qed.

Lemma cenv_split_exp_proc_assoc: forall E Q11 Q12 Q13 Q21 Q Z,
  cenv_split_exp E Q11 Q12 Q13 ->
  cenv_split_proc E Q13 Q21 Q Z ->
  exists Q23, exists Z', cenv_split_proc E Q12 Q21 Q23 Z' /\ 
                                     (Z = None -> Z' = None).
Proof with auto.
  intros E Q11 Q12 Q13 Q21 Q Z S1.
  revert Z. revert Q21. revert Q.

  (cenv_split_exp_cases (induction S1) Case); intros Q Q21 Z S2.

  Case "cenv_split_exp_empty".
    exists Q21. exists None. split... apply cenv_split_proc_left_id...
    eapply wf_cenv_split_proc_right. apply S2.

  Case "cenv_split_exp_left".
    remember ([(X, cbind_proto d T)] ++ Q3) as QL.
    generalize dependent Q3.
    (cenv_split_proc_cases (induction S2) SCase); intros Q3' S2' NI IHO EQ; inversion EQ; subst.

    SCase "cenv_split_proc_left".
      destruct (IHO Q4 Q3 Z) as [Q23 [Z' [S' EQ']]]...
      exists Q23. exists Z'...

    SCase "cenv_split_proc_right".
      destruct IHS2 with (Q4:=Q3') as [Q23 [Z' [S' EQ']]]...
      exists ([(X0, cbind_proto d0 T0)] ++ Q23). exists Z'. split...
      apply cenv_split_proc_right...
      apply dom_cenv_split_proc in S'. apply dom_cenv_split_proc in S2.
      apply dom_cenv_split_exp in S2'. simpl_env in S2. fsetdec.

    SCase "cenv_split_proc_snksrc".
      destruct (IHO Q4 Q3 None) as [Q23 [Z' [S' EQ']]]...
        apply cenv_split_exp_proc...
      exists ([(X, cbind_proto cdir_src T)] ++ Q23). exists Z'. split...
      apply cenv_split_proc_right...
      apply dom_cenv_split_proc in S'. apply dom_cenv_split_exp in S2'.
      apply dom_cenv_split_exp in H0. fsetdec.

    SCase "cenv_split_proc_srcsnk".
      destruct (IHO Q4 Q3 None) as [Q23 [Z' [S' EQ']]]...
        apply cenv_split_exp_proc...
      exists ([(X, cbind_proto cdir_snk T)] ++ Q23). exists Z'. split...
      apply cenv_split_proc_right...
      apply dom_cenv_split_proc in S'. apply dom_cenv_split_exp in S2'.
      apply dom_cenv_split_exp in H0. fsetdec.

  Case "cenv_split_exp_right".
    remember ([(X, cbind_proto d T)] ++ Q3) as QL.
    generalize dependent Q3.
    (cenv_split_proc_cases (induction S2) SCase); intros Q3' S2' NI IHO EQ; inversion EQ; subst.
    
    SCase "cenv_split_proc_left".
      destruct (IHO Q4 Q3 Z) as [Q23 [Z' [S' EQ']]]...
      exists ([(X, cbind_proto d T)] ++ Q23). exists Z'. split...
      apply cenv_split_proc_left...
      apply dom_cenv_split_proc in S'. apply dom_cenv_split_proc in S2.
      apply dom_cenv_split_exp in S2'. fsetdec.

    SCase "cenv_split_proc_right".
      destruct IHS2 with (Q4:=Q3') as [Q23 [Z' [S' EQ']]]...
      exists ([(X0, cbind_proto d0 T0)] ++ Q23). exists Z'. split...
      apply cenv_split_proc_right...
      apply dom_cenv_split_proc in S'. apply dom_cenv_split_proc in S2.
      apply dom_cenv_split_exp in S2'. simpl_env in *. fsetdec.

    SCase "cenv_split_proc_snksrc".
      destruct (IHO Q4 Q3 None) as [Q23 [Z' [S' EQ']]]...
        apply cenv_split_exp_proc...
      exists ([(X, cbind_proto cdir_both T)] ++ Q23). exists (Some X). split...
      apply cenv_split_proc_snksrc...
      apply cenv_split_proc_exp... rewrite <- EQ'...
      apply dom_cenv_split_proc in S'. apply dom_cenv_split_exp in S2'.
      apply dom_cenv_split_exp in H0. fsetdec.

    SCase "cenv_split_proc_srcsnk".
      destruct (IHO Q4 Q3 None) as [Q23 [Z' [S' EQ']]]...
        apply cenv_split_exp_proc...
      exists ([(X, cbind_proto cdir_both T)] ++ Q23). exists (Some X). split...
      apply cenv_split_proc_srcsnk...
      apply cenv_split_proc_exp... rewrite <- EQ'...
      apply dom_cenv_split_proc in S'. apply dom_cenv_split_exp in S2'.
      apply dom_cenv_split_exp in H0. fsetdec.
Qed.

(* Semi-associativity?  Let's hope this is true... *)
Lemma cenv_split_proc_assoc: forall E Q11 Q12 Q13 Q21 Q Z1 Z2,
  cenv_split_proc E Q11 Q12 Q13 Z1 ->
  cenv_split_proc E Q13 Q21 Q Z2 ->
  exists Q23, exists Z3, cenv_split_proc E Q12 Q21 Q23 Z3 /\ 
                                     (Z2 = None -> Z3 = None).
Proof with auto.
  intros E Q11 Q12 Q13 Q21 Q Z1 Z2 S1.
  revert Z2. revert Q21. revert Q.
  
  (cenv_split_proc_cases (induction S1) Case); intros Q Q21 Z2 S2.

  Case "cenv_split_proc_empty".
    exists Q21. exists None. split... apply cenv_split_proc_left_id...
    eapply wf_cenv_split_proc_right. apply S2.

  Case "cenv_split_proc_left".
    remember ([(X, cbind_proto d T)] ++ Q3) as QL.
    generalize dependent Q3.
    (cenv_split_proc_cases (induction S2) SCase); intros Q3' S2' NI IHO EQ; inversion EQ; subst.

    SCase "cenv_split_proc_left".
      destruct (IHO Q4 Q3 Z0) as [Q23 [Z' [S' EQ']]]...
      exists Q23. exists Z'...

    SCase "cenv_split_proc_right".
      destruct IHS2 with (Q4:=Q3') as [Q23 [Z' [S' EQ']]]...
      exists ([(X0, cbind_proto d0 T0)] ++ Q23). exists Z'. split...
      apply cenv_split_proc_right...
      apply dom_cenv_split_proc in S'. apply dom_cenv_split_proc in S2.
      apply dom_cenv_split_proc in S2'. simpl_env in S2. fsetdec.

    SCase "cenv_split_proc_snksrc".
      destruct (IHO Q4 Q3 None) as [Q23 [Z' [S' EQ']]]...
        apply cenv_split_exp_proc...
      exists ([(X, cbind_proto cdir_src T)] ++ Q23). exists Z'. split...
      apply cenv_split_proc_right...
      apply dom_cenv_split_proc in S'. apply dom_cenv_split_proc in S2'.
      apply dom_cenv_split_exp in H0. fsetdec.

    SCase "cenv_split_proc_srcsnk".
      destruct (IHO Q4 Q3 None) as [Q23 [Z' [S' EQ']]]...
        apply cenv_split_exp_proc...
      exists ([(X, cbind_proto cdir_snk T)] ++ Q23). exists Z'. split...
      apply cenv_split_proc_right...
      apply dom_cenv_split_proc in S'. apply dom_cenv_split_proc in S2'.
      apply dom_cenv_split_exp in H0. fsetdec.

  Case "cenv_split_proc_right".
    remember ([(X, cbind_proto d T)] ++ Q3) as QL.
    generalize dependent Q3.
    (cenv_split_proc_cases (induction S2) SCase); intros Q3' S2' NI IHO EQ; inversion EQ; subst.
    
    SCase "cenv_split_proc_left".
      destruct (IHO Q4 Q3 Z0) as [Q23 [Z' [S' EQ']]]...
      exists ([(X, cbind_proto d T)] ++ Q23). exists Z'. split...
      apply cenv_split_proc_left...
      apply dom_cenv_split_proc in S'. apply dom_cenv_split_proc in S2.
      apply dom_cenv_split_proc in S2'. fsetdec.

    SCase "cenv_split_proc_right".
      destruct IHS2 with (Q4:=Q3') as [Q23 [Z' [S' EQ']]]...
      exists ([(X0, cbind_proto d0 T0)] ++ Q23). exists Z'. split...
      apply cenv_split_proc_right...
      apply dom_cenv_split_proc in S'. apply dom_cenv_split_proc in S2.
      apply dom_cenv_split_proc in S2'. simpl_env in *. fsetdec.

    SCase "cenv_split_proc_snksrc".
      destruct (IHO Q4 Q3 None) as [Q23 [Z' [S' EQ']]]...
        apply cenv_split_exp_proc...
      exists ([(X, cbind_proto cdir_both T)] ++ Q23). exists (Some X). split...
      apply cenv_split_proc_snksrc...
      apply cenv_split_proc_exp... rewrite <- EQ'...
      apply dom_cenv_split_proc in S'. apply dom_cenv_split_proc in S2'.
      apply dom_cenv_split_exp in H0. fsetdec.

    SCase "cenv_split_proc_srcsnk".
      destruct (IHO Q4 Q3 None) as [Q23 [Z' [S' EQ']]]...
        apply cenv_split_exp_proc...
      exists ([(X, cbind_proto cdir_both T)] ++ Q23). exists (Some X). split...
      apply cenv_split_proc_srcsnk...
      apply cenv_split_proc_exp... rewrite <- EQ'...
      apply dom_cenv_split_proc in S'. apply dom_cenv_split_proc in S2'.
      apply dom_cenv_split_exp in H0. fsetdec.

  Case "cenv_split_proc_snksrc".
    remember ([(X, cbind_proto cdir_both T)] ++ Q3) as QL.
    generalize dependent Q3.
    (cenv_split_proc_cases (induction S2) SCase); intros Q3' S2' NI EQ; inversion EQ; subst.

    SCase "cenv_split_proc_left".
      lapply (cenv_split_exp_proc_assoc E Q1 Q2 Q3' Q3 Q4 Z S2')...
      intros. destruct H4 as [Q23 [Z' [S' EQ']]].
      exists ([(X, cbind_proto cdir_src T)] ++ Q23). exists Z'. split...
      apply cenv_split_proc_left...
      apply dom_cenv_split_proc in S'. apply dom_cenv_split_proc in S2.
      apply dom_cenv_split_exp in S2'. fsetdec.

    SCase "cenv_split_proc_right".
      destruct IHS2 with (Q4:=Q3') as [Q23 [Z' [S' EQ']]]...
      exists ([(X0, cbind_proto d T0)] ++ Q23). exists Z'. split...
      apply cenv_split_proc_right...
      apply dom_cenv_split_proc in S'. apply dom_cenv_split_proc in S2.
      apply dom_cenv_split_exp in S2'. simpl_env in *. fsetdec.

  Case "cenv_split_proc_srcsnk".
    remember ([(X, cbind_proto cdir_both T)] ++ Q3) as QL.
    generalize dependent Q3.
    (cenv_split_proc_cases (induction S2) SCase); intros Q3' S2' NI EQ; inversion EQ; subst.

    SCase "cenv_split_proc_left".
      lapply (cenv_split_exp_proc_assoc E Q1 Q2 Q3' Q3 Q4 Z S2')...
      intros. destruct H4 as [Q23 [Z' [S' EQ']]].
      exists ([(X, cbind_proto cdir_snk T)] ++ Q23). exists Z'. split...
      apply cenv_split_proc_left...
      apply dom_cenv_split_proc in S'. apply dom_cenv_split_proc in S2.
      apply dom_cenv_split_exp in S2'. fsetdec.

    SCase "cenv_split_proc_right".
      destruct IHS2 with (Q4:=Q3') as [Q23 [Z' [S' EQ']]]...
      exists ([(X0, cbind_proto d T0)] ++ Q23). exists Z'. split...
      apply cenv_split_proc_right...
      apply dom_cenv_split_proc in S'. apply dom_cenv_split_proc in S2.
      apply dom_cenv_split_exp in S2'. simpl_env in *. fsetdec.
Qed.

Lemma app_eq_cases_mid: forall (A:Type) L1 L2 L3 L4 (a:A),
  L1 ++ L2 = L3 ++ [a] ++ L4 ->
  exists L', ((L1 = L3 ++ [a] ++ L' /\ L4 = L' ++ L2) \/
                  (L2 = L' ++ [a] ++ L4 /\ L3 = L1 ++ L')).
Proof with auto.
  intros A L1 L2 L3 L4. revert L1.
  induction L3; intros;
      destruct L1; inversion H; simpl_env in *; subst.
    exists nil. right...
    exists L1. left...
    exists ([a] ++ L3). right...
    destruct (IHL3 L1 a0 H2) as [L' [[Eq1 Eq2] | [Eq1 Eq2]]];
        subst; exists L'...
Qed.

Lemma cenv_split_multi_strengthen_cenv: forall E Qs1 Qs3 Q2 Q Z,
  cenv_split_multi E (Qs1 ++ [Q2] ++ Qs3) Q Z ->
  Qs1 ++ Qs3 = lcempty \/ exists Q', exists Z',
                                             cenv_split_multi E (Qs1 ++ Qs3) Q' Z'.
Proof with auto.
  intros. remember (Qs1 ++ [Q2] ++ Qs3) as Qs.
  generalize dependent Q2. revert Qs1 Qs3.
  induction H; intros; subst.
    symmetry in HeqQs. apply app_eq_nil in HeqQs.
      intuition. apply app_eq_nil in H1. intuition.
      symmetry in H2. apply nil_cons in H2. intuition.
    symmetry in HeqQs. apply app_eq_unit in HeqQs. intuition; subst.
      left. simpl in H2. inversion H2...
      symmetry in H2. simpl in H2. destruct (nil_cons H2).
    apply app_eq_cases_mid in HeqQs.
      destruct HeqQs as [Qs' [[H2 H3] | [H2 H3]]].
        destruct (IHcenv_split_multi1 Qs0 Qs' Q0) as [Emp | [Q' [Z' H4]]]...
          apply app_eq_nil in Emp. intuition. subst. simpl.
            right. exists Q2. exists Y... (*exists Q3. exists Z. split...
              simpl in H. apply cenv_split_multi_single in H. intuition.
                subst. apply cenv_split_proc_commute...*)
          right. subst. rewrite_env ((Qs0 ++ Qs') ++ Qs2).
            eexists. eexists.
            econstructor; eauto.
            (* Needs tree rebalancing *)
Admitted.

Lemma cenv_split_multi_strengthen_cenvs: forall E Qs1 Qs2 Qs3 Q Z,
  cenv_split_multi E (Qs1 ++ Qs2 ++ Qs3) Q Z ->
  Qs1 ++ Qs3 = lcempty \/ exists Q', exists Z',
                                             cenv_split_multi E (Qs1 ++ Qs3) Q' Z'.
Proof with auto.
  intros E Qs1 Qs2. revert Qs1. induction Qs2; intros.
    simpl in H. right. exists Q. exists Z...
    simpl_env in H. apply cenv_split_multi_strengthen_cenv in H.
      destruct H as [Emp | [Q' [Z' H]]].
        left. apply app_eq_nil in Emp. intuition.
          apply app_eq_nil in H0. intuition. subst...
        destruct (IHQs2 Qs1 Qs3 Q' Z')...
Qed.

Lemma wf_cenvs_strengthen_cenvs: forall E Qs1 Qs2 Qs3,
  wf_cenvs E (Qs1 ++ Qs2 ++ Qs3) ->
  wf_cenvs E (Qs1 ++ Qs3).
Proof with auto.
  intros. inversion H; subst.
    symmetry in H0. apply app_eq_nil in H0. intuition.
      apply app_eq_nil in H3. intuition. subst. simpl...
    apply cenv_split_multi_strengthen_cenvs in H0.
      destruct H0 as [Emp | [Q' [Z' H0]]].
        rewrite Emp. constructor. auto...
        econstructor. eauto.
Qed.

Lemma wf_cenvs_append_wf: forall E Qs1 Qs2,
  wf_cenvs E (Qs1 ++ Qs2) ->
  wf_cenvs E Qs1 /\ wf_cenvs E Qs2.
Proof with auto.
  intros. split.
    rewrite_env (Qs1 ++ Qs2 ++ lcempty) in H.
      apply wf_cenvs_strengthen_cenvs in H. simpl_env in H...
    rewrite_env (lcempty ++ Qs1 ++ Qs2) in H.
      apply wf_cenvs_strengthen_cenvs in H. simpl_env in H...
Qed.

Lemma cenvs_split_simple_left_id: forall E Qs,
  cenvs_split_simple E lcempty Qs Qs.
Proof with auto.
  intros. induction Qs...
Qed.

Lemma cenvs_split_simple_right_id: forall E Qs,
  cenvs_split_simple E Qs lcempty Qs.
Proof with auto.
  intros. induction Qs...
Qed.

Lemma cenvs_split_multi_id: forall E Qs,
  wf_cenvs E Qs ->
  cenvs_split_multi E Qs Qs.
Proof with auto.
  intros. induction Qs.
    constructor...
    rewrite_env (lcempty ++ [a] ++ Qs) in H.
      assert (a :: Qs = [a] ++ Qs). simpl...
      rewrite H0 at 1. apply cenvs_split_multi_cons with (Z := None)...
        apply IHQs. apply wf_cenvs_strengthen_cenvs in H. simpl in H...
        constructor... rewrite_env ((lcempty ++ [a]) ++ Qs) in H.
          apply wf_cenvs_append_wf in H. intuition. simpl in H1.
          apply wf_cenvs_to_single...
Qed.

Lemma cenvs_split_left_id: forall E Qs,
  wf_cenvs E Qs ->
  cenvs_split E lcempty Qs Qs.
Proof with auto.
  intros. apply cenvs_split_ms with (Qs' := Qs)...
    apply cenvs_split_multi_id...
    apply cenvs_split_simple_left_id...
Qed.

Lemma cenvs_split_right_id: forall E Qs,
  wf_cenvs E Qs ->
  cenvs_split E Qs lcempty Qs.
Proof with auto.
  intros. apply cenvs_split_commute.
  apply cenvs_split_left_id...
Qed.

Lemma cenvs_split_simple_assoc: forall E Qs11 Qs12 Qs13 Qs21 Qs,
  cenvs_split_simple E Qs11 Qs12 Qs13 ->
  cenvs_split_simple E Qs13 Qs21 Qs ->
  exists Qs23, cenvs_split_simple E Qs12 Qs21 Qs23 /\ cenvs_split_simple E Qs11 Qs23 Qs.
Proof with auto.
  intros E Qs11 Qs12 Qs13 Qs21 Qs S1 S2.
  generalize dependent Qs. revert Qs21.
  (cenvs_split_simple_cases (induction S1) Case); intros Qs21 Qs S2.
    Case "cenvs_split_simple_nil".
      exists Qs. split... apply cenvs_split_simple_left_id.
    Case "cenvs_split_simple_left".
      remember (Q :: Qs3) as QsQs.
      generalize dependent Qs3.
      (cenvs_split_simple_cases (induction S2) SCase);
          intros Qs3' SS IHO EQ; inversion EQ; subst.
        SCase "cenvs_split_simple_left".
          destruct (IHO Qs3 Qs4) as [D23 [S1' S2']]...
          exists D23...
        SCase "cenvs_split_simple_right".
          destruct IHS2 with (Qs5:=Qs3') as [Qs23 [S1' S2']]...
          exists (Q0 :: Qs23). split...
    Case "cenvs_split_simple_right".
      remember (Q :: Qs3) as QsQs.
      generalize dependent Qs3.
      (cenvs_split_simple_cases (induction S2) SCase);
          intros Qs3' SS IHO EQ; inversion EQ; subst.
        SCase "cenvs_split_simple_left".
          destruct (IHO Qs3 Qs4) as [D23 [S1' S2']]...
          exists (Q :: D23)...
        SCase "cenvs_split_simple_right".
          destruct IHS2 with (Qs5:=Qs3') as [Qs23 [S1' S2']]...
          exists (Q0 :: Qs23). split...
Qed.

Lemma cenvs_split_simple_append: forall E Qs1 Qs2 Qs3 Qs1' Qs2' Qs3',
  cenvs_split_simple E Qs1 Qs2 Qs3 ->
  cenvs_split_simple E Qs1' Qs2' Qs3' ->
  cenvs_split_simple E (Qs1 ++ Qs1') (Qs2 ++ Qs2') (Qs3 ++ Qs3').
Proof.
  intros E Qs1 Qs2 Qs3. revert Qs1 Qs2.
  induction Qs3; intros; inversion H; subst; simpl; auto.
Qed.

(* I don't think this is necessary anymore, so I'm not bothering to fix it.
Lemma cenv_split_multi_two: forall E Q1 Q2 Q3 Z,
  cenv_split_multi E (Q1 :: Q2 :: lcempty) Q3 Z ->
  cenv_split_proc E Q1 Q2 Q3 Z.
Proof with auto.
  intros. inversion H; subst...
    destruct Qs1; simpl in *; subst...
      apply cenv_split_multi_empty in H1. subst.
        apply cenv_split_proc_empty_left in H4. intuition. subst.
      inversion H0; subst. apply app_eq_unit in H6. intuition; subst.
        apply cenv_split_multi_single in H1.
          apply cenv_split_multi_single in H2. intuition. subst...
        apply cenv_split_multi_not_empty in H2. intuition.
Qed.*)

Lemma cenvs_split_multi_append: forall E Qs1 Qs1' Qs2 Qs2',
  cenvs_split_multi E Qs1 Qs1' ->
  cenvs_split_multi E Qs2 Qs2' ->
  wf_cenvs E (Qs1' ++ Qs2') ->
  cenvs_split_multi E (Qs1 ++ Qs2) (Qs1' ++ Qs2').
Proof with auto.
  intros. generalize dependent Qs1.
  induction Qs1'; intros; inversion H; subst.
    simpl...
    simpl_env. rewrite_env (a :: (Qs1' ++ Qs2')).
      rewrite_env (a :: (Qs1' ++ Qs2')) in H1.
      econstructor... apply IHQs1'...
        simpl_env in H1. apply wf_cenvs_append_wf in H1. intuition...
        eauto.
Qed.

Lemma cenvs_split_multi_divide: forall E Qs' Qs1 Qs2,
  cenvs_split_multi E Qs' (Qs1 ++ Qs2) ->
  exists Qs1', exists Qs2', Qs' = Qs1' ++ Qs2'
    /\ cenvs_split_multi E Qs1' Qs1
    /\ cenvs_split_multi E Qs2' Qs2.
Proof with auto.
  intros. generalize dependent Qs'.
  induction Qs1; intros; simpl in H.
    exists lcempty. exists Qs'. repeat split...
      constructor... inversion H...
    inversion H; subst. apply IHQs1 in H2.
      destruct H2 as [Qs1' [Qs2' [Eq [S1 S2]]]]. subst.
      exists (Qs ++ Qs1'). exists Qs2'. repeat split...
        econstructor...
          eauto.
          rewrite_env ((a::Qs1) ++ Qs2) in H6.
            apply wf_cenvs_append_wf in H6... intuition.
Qed.

Lemma cenv_split_multi_trans: forall E Qs1 Qs2 Q3 Z,
  cenvs_split_multi E Qs1 Qs2 ->
  cenv_split_multi E Qs2 Q3 Z ->
  exists Z', cenv_split_multi E Qs1 Q3 Z'.
Proof with auto.
(* Lets revisit this later...

  intros E Qs1 Qs2. revert Qs1.
  induction Qs2; intros; inversion H0; inversion H; subst...
    exists None...
    exists Z...
    inversion H9; subst. exists Z0. simpl_env in *...
    destruct Qs0 as [ | Q [ | Q' Qs0']]; simpl in H1; subst.
      apply cenv_split_multi_empty in H2. subst.
        
      inversion H1. apply cenv_split_multi_single in H2.
        intuition. repeat subst. lapply (IHQs2 Qs4 Q2 Y H10)...
        intros. destruct H2 as [Z' H2]. exists Z.
        eapply cenv_split_multi_branch; eauto.
      inversion H1. subst. clear H1.
        simpl_env in *.

            lapply (IHQs2 Qs4 )... intros.
        apply cenv_split_multi_chroot in H0.
        destruct H0 as [H0 | [H0 | [Q1' [Q2' [H6 [H7 H8]]]]]].
          symmetry in H0. apply nil_cons in H0. intuition.
          apply app_eq_nil in H0. intuition. symmetry in H4.
            apply nil_cons in H4. intuition.
          inversion H7; subst.
            econstructor; eauto.
            apply app_eq_unit in H0. destruct H0; intuition; subst.
              apply cenv_split_multi_not_empty in H4. intuition.
              apply cenv_split_multi_not_empty in H10. intuition. *)
Admitted.

Lemma cenvs_split_multi_trans: forall E Qs1 Qs2 Qs3,
  cenvs_split_multi E Qs1 Qs2 ->
  cenvs_split_multi E Qs2 Qs3 ->
  cenvs_split_multi E Qs1 Qs3.
Proof with auto.
  intros E Qs1 Qs2 Qs3 S1 S2.
  generalize dependent Qs2. generalize dependent Qs1.
  induction Qs3; intros; inversion S2; subst...
    apply cenvs_split_multi_divide in S1.
      destruct S1 as [Qs' [Qs0' [Eq [S S0]]]]. subst.
      lapply (IHQs3 Qs0' Qs0 S0)... intros.
      simpl_env in *. apply cenvs_split_multi_append...
      apply cenv_split_multi_trans with (Qs1 := Qs') in H4...
      rewrite_env (Qs' ++ lcempty). destruct H4 as [Z' H4].
      econstructor; eauto.
        apply wf_cenvs_append_wf in H5. intuition...
Qed.

Lemma cenvs_split_sub_right: forall E Qs1 Qs2 Qs3 Qs3',
  cenvs_split E Qs1 Qs2 Qs3 ->
  cenvs_split E Qs3 lcempty Qs3' ->
  cenvs_split E Qs1 Qs2 Qs3'.
Proof with eauto.
  intros. inversion H; inversion H0; subst.
  apply cenvs_split_simple_empty_right in H8. subst.
  assert (cenvs_split_multi E Qs' Qs3').
    eapply cenvs_split_multi_trans...
  eapply cenvs_split_ms...
Qed.

Lemma cenvs_split_assoc: forall E Qs11 Qs12 Qs13 Qs21 Qs,
  cenvs_split E Qs11 Qs12 Qs13 ->
  cenvs_split E Qs13 Qs21 Qs ->
  exists Qs23, cenvs_split E Qs12 Qs21 Qs23 /\ cenvs_split E Qs11 Qs23 Qs.
Proof with auto.
  intros E Qs11 Qs12 Qs13 Qs21 Qs S1 S2.
  inversion S1. inversion S2. subst.
  (* This is confusing... *)
Admitted.

Lemma cenv_split_exp_rebind_chan_left: forall E X d1 T1 Q1L Q1R Q2 Q3L Q3R d2 T2,
  cenv_split_exp E (Q1L ++ [(X, cbind_proto d1 T1)] ++ Q1R) Q2
    (Q3L ++ [(X, cbind_proto d1 T1)] ++ Q3R) ->
  wf_proto E T2 ->
  cenv_split_exp E (Q1L ++ [(X, cbind_proto d2 T2)] ++ Q1R) Q2
    (Q3L ++ [(X, cbind_proto d2 T2)] ++ Q3R).
Proof with auto.
  intros E X d1 T1 Q1L Q1R Q2 Q3L Q3R d2 T2 S WF.
  remember (Q1L ++ [(X, cbind_proto d1 T1)] ++ Q1R) as Q1.
  remember (Q3L ++ [(X, cbind_proto d1 T1)] ++ Q3R) as Q3.
  generalize dependent Q3R. generalize dependent Q3L.
  generalize dependent Q1R. generalize dependent Q1L.
  generalize dependent T2. revert d1 d2 T1.
  
  (cenv_split_exp_cases (induction S) Case); intros d1 d2 T1 T2 WF2 Q1L Q1R EQ1 Q3L Q3R EQ2.

  Case "cenv_split_exp_empty".
    destruct Q1L; destruct Q3L; simpl_env in *; inversion EQ1.

  Case "cenv_split_exp_left".
    destruct Q1L; destruct Q3L; simpl_env in *; inversion EQ1; subst.
    inversion EQ2; subst. apply cenv_split_exp_left; auto.

    inversion EQ2; subst. simpl_env in H0. fsetdec.
 
    inversion EQ2; subst.
    assert (X `notin` dom (Q1L ++ [(X, cbind_proto d1 T1)] ++ Q1R)).
    simpl_env in *. apply cenv_split_proc_notin_dom
      with (E := E) (Q1 := Q1L ++ [(X, cbind_proto d1 T1)] ++ Q1R) (Q2 := Q2) (Z := None)
      in H0; auto.
      simpl_env in H0. fsetdec.
      apply cenv_split_exp_proc...
    simpl_env in *. fsetdec.

    inversion EQ2; subst. apply cenv_split_exp_left; auto.
    eapply IHS; auto. simpl_env. eauto. simpl_env. auto.

  Case "cenv_split_exp_right".
    destruct Q3L; simpl_env in *; inversion EQ2; subst.

    assert (X `notin` dom (Q1L ++ [(X, cbind_proto d1 T1)] ++ Q1R)).
    apply cenv_split_proc_notin_dom
      with (E := E) (Q1 := Q1L ++ [(X, cbind_proto d1 T1)] ++ Q1R) (Q2 := Q2) (Z := None)
      in H0; auto. fsetdec.
      apply cenv_split_exp_proc...
    simpl_env in H2. fsetdec.

    apply cenv_split_exp_right; auto.
    eapply IHS; auto.
Qed.

Lemma cenv_split_exp_rebind_chan_right: forall E Q1 X d1 T1 Q2L Q2R Q3L Q3R d2 T2,
  cenv_split_exp E Q1 (Q2L ++ [(X, cbind_proto d1 T1)] ++ Q2R)
    (Q3L ++ [(X, cbind_proto d1 T1)] ++ Q3R) ->
  wf_proto E T2 ->
  cenv_split_exp E Q1 (Q2L ++ [(X, cbind_proto d2 T2)] ++ Q2R)
    (Q3L ++ [(X, cbind_proto d2 T2)] ++ Q3R).
Proof with eauto.
  intros. apply cenv_split_exp_commute. apply cenv_split_exp_commute in H.
  eapply cenv_split_exp_rebind_chan_left...
Qed.

Lemma cenv_split_proc_rebind_chan_left: forall E X d T1 Q1L Q1R Q2 Q3L Q3R T2 Z,
  cenv_split_proc E (Q1L ++ [(X, cbind_proto d T1)] ++ Q1R) Q2
    (Q3L ++ [(X, cbind_proto d T1)] ++ Q3R) Z ->
  X `notin` dom Q2 ->
  wf_proto E T2 ->
  cenv_split_proc E (Q1L ++ [(X, cbind_proto d T2)] ++ Q1R) Q2
    (Q3L ++ [(X, cbind_proto d T2)] ++ Q3R) Z.
Proof with auto.
  intros E X d T1 Q1L Q1R Q2 Q3L Q3R T2 Z S NI WF.
  remember (Q1L ++ [(X, cbind_proto d T1)] ++ Q1R) as Q1.
  remember (Q3L ++ [(X, cbind_proto d T1)] ++ Q3R) as Q3.
  generalize dependent Q3R. generalize dependent Q3L.
  generalize dependent Q1R. generalize dependent Q1L.
  generalize dependent T2. generalize dependent T1.
  
  (cenv_split_proc_cases (induction S) Case); intros T1 T2 WF2 Q1L Q1R EQ1 Q3L Q3R EQ2.

  Case "cenv_split_proc_empty".
    destruct Q1L; destruct Q3L; simpl_env in *; inversion EQ1.

  Case "cenv_split_proc_left".
    destruct Q1L; destruct Q3L; simpl_env in *; inversion EQ1; subst.
    inversion EQ2; subst. apply cenv_split_proc_left; auto.

    inversion EQ2; subst. simpl_env in H0. fsetdec.
 
    inversion EQ2; subst. 
    assert (X `notin` dom (Q1L ++ (X, cbind_proto d T1) :: Q1R)).
    apply cenv_split_proc_notin_dom
      with (E := E) (Q1 :=  Q1L ++ (X, cbind_proto d T1) :: Q1R) (Q2 := Q2) (Z := Z)
      in H0; auto. fsetdec.
    simpl_env in *. fsetdec.

    inversion EQ2; subst. apply cenv_split_proc_left; auto.
    eapply IHS; auto. simpl_env. eauto. simpl_env. auto.

  Case "cenv_split_proc_right".
    destruct Q3L; simpl_env in *; inversion EQ2; subst.

    assert (X `notin` dom (Q1L ++ [(X, cbind_proto d T1)] ++ Q1R)).
    apply cenv_split_proc_notin_dom
      with (E := E) (Q1 :=  Q1L ++ (X, cbind_proto d T1) :: Q1R) (Q2 := Q2) (Z := Z)
      in H0; auto.
    simpl_env in H2. fsetdec.

    apply cenv_split_proc_right; auto.
    eapply IHS; auto.

  Case "cenv_split_proc_snksrc".
    destruct Q1L; simpl_env in EQ1; inversion EQ1; subst.
    simpl_env in NI. fsetdec.

    destruct Q3L; simpl_env in EQ2; inversion EQ2; subst.
    simpl_env in NI. fsetdec. 

    simpl_env in *.
    apply cenv_split_proc_snksrc; auto.
    eapply cenv_split_exp_rebind_chan_left; eauto.

  Case "cenv_split_proc_srcsnk".
    destruct Q1L; simpl_env in EQ1; inversion EQ1; subst.
    simpl_env in NI. fsetdec.
    
    destruct Q3L; simpl_env in EQ2; inversion EQ2; subst.
    simpl_env in NI. fsetdec. 

    simpl_env in *.
    apply cenv_split_proc_srcsnk; auto.
    eapply cenv_split_exp_rebind_chan_left; eauto.
Qed.

Lemma cenv_split_proc_rebind_chan_right: forall E Q1 X d T1 Q2L Q2R Q3L Q3R T2 Z,
  cenv_split_proc E Q1 (Q2L ++ [(X, cbind_proto d T1)] ++ Q2R)
    (Q3L ++ [(X, cbind_proto d T1)] ++ Q3R) Z ->
  X `notin` dom Q1 ->
  wf_proto E T2 ->
  cenv_split_proc E Q1 (Q2L ++ [(X, cbind_proto d T2)] ++ Q2R)
    (Q3L ++ [(X, cbind_proto d T2)] ++ Q3R) Z.
Proof with eauto.
  intros. apply cenv_split_proc_commute. apply cenv_split_proc_commute in H.
  eapply cenv_split_proc_rebind_chan_left...
Qed.

Lemma cenv_split_proc_rebind_chan_both: forall E X d1 d2 d3 T1 Q1L Q1R Q2L Q2R Q3L Q3R T2 Z,
  cenv_split_proc E (Q1L ++ [(X, cbind_proto d1 T1)] ++ Q1R) (Q2L ++ [(X, cbind_proto d2 T1)] ++ Q2R)
    (Q3L ++ [(X, cbind_proto d3 T1)] ++ Q3R) Z ->
  wf_proto E T2 ->
  cenv_split_proc E (Q1L ++ [(X, cbind_proto d1 T2)] ++ Q1R) (Q2L ++ [(X, cbind_proto d2 T2)] ++ Q2R)
    (Q3L ++ [(X, cbind_proto d3 T2)] ++ Q3R) Z.
Proof with auto.
  intros E X d1 d2 d3 T1 Q1L Q1R Q2L Q2R Q3L Q3R T2 Z S WF.
  remember (Q1L ++ [(X, cbind_proto d1 T1)] ++ Q1R) as Q1.
  remember (Q2L ++ [(X, cbind_proto d2 T1)] ++ Q2R) as Q2.
  remember (Q3L ++ [(X, cbind_proto d3 T1)] ++ Q3R) as Q3.
  generalize dependent Q3R. generalize dependent Q3L.
  generalize dependent Q2R. generalize dependent Q2L.
  generalize dependent Q1R. generalize dependent Q1L.
  generalize dependent T2. generalize dependent T1.
  
  (cenv_split_proc_cases (induction S) Case); intros T1 T2 WF2 Q1L Q1R EQ1 Q2L Q2R EQ2 Q3L Q3R EQ3.

  Case "cenv_split_proc_empty".
    destruct Q1L; destruct Q3L; simpl_env in EQ1; inversion EQ1.

  Case "cenv_split_proc_left".
    destruct Q1L; destruct Q3L; simpl_env in *; inversion EQ1; subst.
    assert (X `notin` dom (Q2L ++ [(X, cbind_proto d2 T1)] ++ Q2R)).
    eapply cenv_split_proc_notin_dom in H0.
    Focus 2. apply S. intuition. simpl_env in H2. fsetdec.

    assert (X `notin` dom (Q2L ++ [(X, cbind_proto d2 T1)] ++ Q2R)).
    eapply cenv_split_proc_notin_dom in H0.
    Focus 2. apply S. intuition. simpl_env in H2. fsetdec.

    inversion EQ3; subst. 
    assert (X `notin` dom (Q2L ++ [(X, cbind_proto d2 T1)] ++ Q2R)).
    eapply cenv_split_proc_notin_dom in H0.
    Focus 2. apply S. intuition. simpl_env in H2. fsetdec.

    inversion EQ3; subst. 
    apply cenv_split_proc_left; auto.
    apply (IHS T1 T2); auto.

  Case "cenv_split_proc_right".
    destruct Q3L; simpl_env in *; inversion EQ3; subst.

    assert (X `notin` dom (Q1L ++ [(X, cbind_proto d1 T1)] ++ Q1R)).
    eapply cenv_split_proc_notin_dom in H0.
    Focus 2. apply S. intuition. simpl_env in H2. fsetdec.

    destruct Q2L; simpl_env in *; inversion EQ2; subst.
    fsetdec.

    apply cenv_split_proc_right; auto.
    eapply IHS; auto.

  Case "cenv_split_proc_snksrc".
    destruct Q1L; simpl_env in EQ1; inversion EQ1; subst;
    destruct Q2L; simpl_env in *; inversion EQ2; subst;
    destruct Q3L; simpl_env in *; inversion EQ3; subst; simpl_env in *; try fsetdec.

    apply cenv_split_proc_snksrc; auto.

    assert (X `notin` dom (Q2L ++ [(X, cbind_proto d2 T1)] ++ Q2R)).
    apply cenv_split_exp_notin_dom with (X := X) in H; auto.
    intuition. simpl_env in H3. fsetdec.

    assert (X `notin` dom (Q1L ++ [(X, cbind_proto d1 T1)] ++ Q1R)).
    apply cenv_split_exp_notin_dom with (X := X) in H; auto.
    intuition. simpl_env in H3. fsetdec.

    assert (X `notin` dom (Q1L ++ [(X, cbind_proto d1 T1)] ++ Q1R)).
    apply cenv_split_exp_notin_dom with (X := X) in H; auto.
    intuition. simpl_env in H3. fsetdec.

    assert (X `notin` dom (Q1L ++ [(X, cbind_proto d1 T1)] ++ Q1R) `union` dom E).
    eapply cenv_split_exp_not_in_right; eauto. simpl_env. fsetdec.
    simpl_env in H3. fsetdec.

  Case "cenv_split_proc_srcsnk".
    destruct Q1L; simpl_env in EQ1; inversion EQ1; subst;
    destruct Q2L; simpl_env in *; inversion EQ2; subst;
    destruct Q3L; simpl_env in *; inversion EQ3; subst; simpl_env in *; try fsetdec.

    apply cenv_split_proc_srcsnk; auto.

    assert (X `notin` dom (Q2L ++ [(X, cbind_proto d2 T1)] ++ Q2R)).
    apply cenv_split_exp_notin_dom with (X := X) in H; auto.
    intuition. simpl_env in H3. fsetdec.

    assert (X `notin` dom (Q1L ++ [(X, cbind_proto d1 T1)] ++ Q1R)).
    apply cenv_split_exp_notin_dom with (X := X) in H; auto.
    intuition. simpl_env in H3. fsetdec.

    assert (X `notin` dom (Q1L ++ [(X, cbind_proto d1 T1)] ++ Q1R)).
    apply cenv_split_exp_notin_dom with (X := X) in H; auto.
    intuition. simpl_env in H3. fsetdec.

    assert (X `notin` dom (Q1L ++ [(X, cbind_proto d1 T1)] ++ Q1R) `union` dom E).
    eapply cenv_split_exp_not_in_right; eauto. simpl_env. fsetdec.
    simpl_env in H3. fsetdec.
Qed.

Lemma vwf_envs_split_both: forall E Q D1 D2 D3,
  lenv_split E Q D1 D2 D3 ->
  vwf_envs E Q (D1 ++ D2).
Proof.
  intros E Q D1 D2 D3 S.
  (lenv_split_cases (induction S) Case); simpl_env in *; auto.
  Case "lenv_split_left".
    apply vwf_envs_typ; auto. 
      rewrite (dom_lenv_split E Q D1 D2 D3) in H1; auto.
  Case "lenv_split_right".
    apply vwf_envs_lin_weakening; auto.
      rewrite (dom_lenv_split E Q D1 D2 D3) in H1; auto.
Qed.

Lemma cenv_split_proc_left_empty: forall E Q1 Q2 Z,
  cenv_split_proc E Q1 Q2 Q2 Z ->
  Q1 = cempty.
Proof with auto.
  intros E Q1 Q2 Z. generalize dependent Q1.
  induction Q2; intros Q1 CS; inversion CS; subst; simpl_env in *...
    apply dom_cenv_split_proc in H1. simpl_env in H1. fsetdec.
Qed.

Lemma cenv_split_proc_right_empty: forall E Q1 Q2 Z,
  cenv_split_proc E Q1 Q2 Q1 Z ->
  Q2 = cempty.
Proof.
  intros. apply cenv_split_proc_commute in H.
  eapply cenv_split_proc_left_empty; eauto.
Qed.

Lemma cenv_split_exp_left_empty: forall E Q1 Q2,
  cenv_split_exp E Q1 Q2 Q2 ->
  Q1 = cempty.
Proof.
  intros. apply cenv_split_exp_proc in H.
  eapply cenv_split_proc_left_empty; eauto.
Qed.

Lemma cenv_split_exp_right_empty: forall E Q1 Q2,
  cenv_split_exp E Q1 Q2 Q1 ->
  Q2 = cempty.
Proof.
  intros. apply cenv_split_exp_commute in H.
  eapply cenv_split_exp_left_empty; eauto.
Qed.

Lemma lenv_split_left_empty: forall E Q D1 D2,
  lenv_split E Q D1 D2 D2 ->
  D1 = lempty.
Proof with auto.
  intros E Q D1 D2. generalize dependent D1.
  induction D2; intros D1 LS; inversion LS; subst; simpl_env in *...
    apply dom_lenv_split in H1. simpl_env in H1. fsetdec.
Qed.

Lemma lenv_split_right_empty: forall E Q D1 D2,
  lenv_split E Q D1 D2 D1 ->
  D2 = lempty.
Proof.
  intros. apply lenv_split_commute in H.
  eapply lenv_split_left_empty; eauto.
Qed.

(************************************************************************ *)
(** Environment agreeing and eventual equality *)

Lemma cenv_agree_id: forall E Q,
  wf_cenv E Q ->
  cenv_agree E Q Q.
Proof with auto.
  intros E Q Hwf. induction Q...
    simpl_env in *. destruct a as [X [d T]]. inversion Hwf; subst.
    constructor...
Qed.

Lemma lenv_agree_id: forall E Q D,
  vwf_envs E Q D ->
  lenv_agree E Q D D.
Proof with auto.
  intros E Q D Hwf. induction D...
    simpl_env in *. destruct a as [X [T]]. inversion Hwf; subst.
    constructor...
Qed.

Lemma cenv_agree_empty_left: forall E Q,
  wf_cenv E Q ->
  cenv_agree E cempty Q.
Proof with auto.
  intros. induction Q...
  destruct a as [X [d T]]. simpl_env in *.
  inversion H; subst. constructor...
Qed.

Lemma cenv_agree_empty_right: forall E Q,
  wf_cenv E Q ->
  cenv_agree E Q cempty.
Proof.
  intros. apply cenv_agree_commute.
  apply cenv_agree_empty_left. auto.
Qed.

Lemma cenv_agree_strengthen_left: forall E Q1 Q2 X d T,
  cenv_agree E ([(X, cbind_proto d T)] ++ Q1) Q2 ->
  cenv_agree E Q1 Q2.
Proof with auto.
  intros E Q1 Q2 X d T Agree.
  generalize dependent Q1. revert X d T.
    induction Q2; intros.
    Case "nil".
      apply cenv_agree_empty_right.
      eapply wf_cenv_agree_left.
      inversion Agree; subst. eauto.
    Case "cons".
      destruct a as [Y [d' T']]. simpl_env in *.
      remember ([(X, cbind_proto d T)] ++ Q1) as Q1'.
      remember ([(Y, cbind_proto d' T')] ++ Q2) as Q2'.
      generalize dependent Q1. revert X d T.
      generalize dependent Q2. revert Y d' T'.
      (cenv_agree_cases (induction Agree) SCase);
        intros; inversion HeqQ1'; inversion HeqQ2'; repeat subst...
        SCase "cenv_agree_right".
          apply cenv_agree_right...
          eapply IHQ2. apply Agree.
Qed.

Lemma cenv_agree_strengthen_right: forall E Q1 Q2 X d T,
  cenv_agree E Q1 ([(X, cbind_proto d T)] ++ Q2) ->
  cenv_agree E Q1 Q2.
Proof.
  intros. apply cenv_agree_commute.
  apply cenv_agree_commute in H.
  eapply cenv_agree_strengthen_left; eauto.
Qed.

Lemma cenv_agree_left_sub: forall E Q1 Q2 Q3 Q0,
  cenv_split_exp E Q1 Q2 Q3 ->
  cenv_agree E Q3 Q0 ->
  cenv_agree E Q2 Q0.
Proof with auto.
  intros E Q1 Q2 Q3 Q0 CS Agree.
  generalize dependent Q2. generalize dependent Q1.
  (cenv_agree_cases (induction Agree) Case); intros Q1' Q2' S...
  
  Case "cenv_agree_empty".
  inversion S. subst. auto.

  Case "cenv_agree_both".
  inversion S; subst.
    apply cenv_agree_right. eapply IHAgree. apply H10. auto.
    lapply (cenv_split_proc_notin_dom E Q0 Q2' Q1 X None H12); auto. 
    apply cenv_split_exp_proc... auto. auto.

    apply cenv_agree_both; auto. eapply IHAgree. apply H10. auto.
    lapply (cenv_split_proc_notin_dom E Q1' Q3 Q1 X None H12); auto. 
    apply cenv_split_exp_proc...

(*    apply cenv_agree_both; auto. eapply IHAgree. 
    apply cenv_split_exp_proc. apply H10. auto.
    lapply (cenv_split_proc_notin_dom E Q0 Q3 Q1 X H12); auto.

    apply cenv_agree_both; auto. eapply IHAgree. 
    apply cenv_split_exp_proc. apply H10. auto.
    lapply (cenv_split_proc_notin_dom E Q0 Q3 Q1 X H12); auto.*)

  Case "cenv_agree_left".     
  inversion S; subst.
    eapply IHAgree. apply H10.

    apply cenv_agree_left; auto. eapply IHAgree. apply H10.
    lapply (cenv_split_proc_notin_dom E Q1' Q3 Q1 X None H12); auto.
    apply cenv_split_exp_proc...

(*    apply cenv_agree_left; auto. eapply IHAgree. 
    apply cenv_split_exp_proc. apply H10.
    lapply (cenv_split_proc_notin_dom E Q0 Q3 Q1 X H12); auto.

    apply cenv_agree_left; auto. eapply IHAgree.
    apply cenv_split_exp_proc. apply H10.
    lapply (cenv_split_proc_notin_dom E Q0 Q3 Q1 X H12); auto.*)

  Case "cenv_agree_right".    
  inversion S; subst.
    apply cenv_agree_right; auto.

    apply cenv_agree_right; auto. eapply IHAgree. apply S.
    simpl in H0. assert (X `notin` dom Q4). fsetdec.
    lapply (cenv_split_proc_notin_dom E Q0 Q2' Q4 X None H7); auto.
    apply cenv_split_exp_proc...

    apply cenv_agree_right; auto. eapply IHAgree. apply S.
    simpl in H0. assert (X `notin` dom Q4). fsetdec.
    lapply (cenv_split_proc_notin_dom E Q1' Q3 Q4 X None H7); auto.
    apply cenv_split_exp_proc...

(*    apply cenv_agree_right; auto. eapply IHAgree. apply S.
    simpl in H0. assert (X `notin` dom Q4). fsetdec.
    lapply (cenv_split_proc_notin_dom E Q0 Q3 Q4 X H7); auto.

    apply cenv_agree_right; auto. eapply IHAgree. apply S.
    simpl in H0. assert (X `notin` dom Q4). fsetdec.
    lapply (cenv_split_proc_notin_dom E Q0 Q3 Q4 X H7); auto.*)
Qed.
    

Lemma cenv_agree_right_sub: forall E Q1 Q2 Q3 Q0,
  cenv_split_exp E Q1 Q2 Q3 ->
  cenv_agree E Q0 Q3 ->
  cenv_agree E Q0 Q2.
Proof.
  intros E Q1 Q2 Q3 Q0 CS Agree.
  apply cenv_agree_commute. apply cenv_agree_commute in Agree.
  eapply cenv_agree_left_sub; eauto.
Qed.

Lemma lenv_agree_left_sub: forall E Q D1 D2 D3 D0,
  lenv_split E Q D1 D2 D3 ->
  lenv_agree E Q D3 D0 ->
  lenv_agree E Q D2 D0.
Proof with auto.
  intros E Q D1 D2 D3 D0 LS Agree.
  generalize dependent D2. generalize dependent D1.
  (lenv_agree_cases (induction Agree) Case); intros D1' D2' S...
  
  Case "lenv_agree_empty".
  inversion S; subst; auto.

  Case "lenv_agree_both".
  inversion S; subst; auto.

  apply lenv_agree_right; auto. eapply IHAgree. apply H7.
  lapply (lenv_split_notin_dom E Q D0 D2' D1 X H14); auto.

  apply lenv_agree_both; auto. eapply IHAgree. apply H7.
  lapply (lenv_split_notin_dom E Q D1' D3 D1 X H14); auto.

  Case "lenv_agree_left".
  inversion S; subst; auto.

  eapply IHAgree. apply H7.

  apply lenv_agree_left; auto. eapply IHAgree. apply H7.
  lapply (lenv_split_notin_dom E Q D1' D3 D1 X H14); auto.

  Case "lenv_agree_right".
  inversion S; subst; auto.

  apply lenv_agree_right; auto. eapply IHAgree. apply S.
  simpl in H1. assert (X `notin` dom D4). fsetdec.
  lapply (lenv_split_notin_dom E Q D0 D2' D4 X H9); auto.

  apply lenv_agree_right; auto. eapply IHAgree. apply S.
  simpl in H1. assert (X `notin` dom D4). fsetdec.
  lapply (lenv_split_notin_dom E Q D1' D3 D4 X H9); auto.
Qed.

Lemma lenv_agree_right_sub: forall E Q D1 D2 D3 D0,
  lenv_split E Q D1 D2 D3 ->
  lenv_agree E Q D0 D3 ->
  lenv_agree E Q D0 D2.
Proof.
  intros E Q D1 D2 D3 D0 LS Agree.
  apply lenv_agree_commute. apply lenv_agree_commute in Agree.
  eapply lenv_agree_left_sub; eauto.
Qed.

Lemma agree_regular_right: forall E Q1 Q2 Q3 Q4 Q5 Q6 D1 D2 D3 D4 D5 D6,
  cenv_agree E Q3 Q6 ->
  lenv_agree E Q3 D3 D6 ->
  lenv_agree E Q6 D3 D6 ->
  cenv_split_exp E Q1 Q2 Q3 ->
  cenv_split_exp E Q4 Q5 Q6 ->
  lenv_split E Q3 D1 D2 D3 ->
  lenv_split E Q6 D4 D5 D6 ->
  cenv_agree E Q2 Q5 /\ lenv_agree E Q2 D2 D5 /\ lenv_agree E Q5 D2 D5.
Proof with auto.
  intros E Q1 Q2 Q3 Q4 Q5 Q6 D1 D2 D3 D4 D5 D6 CA LA1 LA2 H0 H10 H H8.
  assert (cenv_agree E Q3 Q5).
    apply cenv_agree_right_sub with (Q0 := Q3) in H10...
  assert (lenv_agree E Q6 D3 D5).
    apply lenv_agree_right_sub with (D0 := D3) in H8...
  repeat split.
      apply cenv_agree_left_sub with (Q0 := Q5) in H0...
      assert (lenv_agree E Q3 D2 D5).
        apply lenv_agree_left_sub with (D0 := D5) in H...
        apply lenv_agree_disjoint_cenv with (Q := Q6)...
          apply wf_lenv_split in H...
          apply vwf_envs_pack...
            apply wf_lenv_split_right in H8.
              apply vwf_envs_unpack in H8. intuition...
            apply dom_cenv_split_exp in H0. apply wf_lenv_agree_right in LA1.
            apply vwf_envs_unpack in LA1. intuition.
            apply dom_lenv_split in H8. unfold disjoint in *. fsetdec.
        apply lenv_agree_disjoint_cenv with (Q := Q3)...
          apply wf_lenv_agree_left in H3. apply vwf_envs_unpack in H3. intuition.
            apply vwf_envs_pack... apply dom_cenv_split_exp in H0.
            unfold disjoint in *. fsetdec.
          apply wf_lenv_agree_right in H3.
            apply vwf_envs_unpack in H3. intuition. apply vwf_envs_pack...
            apply dom_cenv_split_exp in H0. unfold disjoint in *. fsetdec.
        apply lenv_agree_left_sub with (D1 := D1) (D3 := D3)...
          apply lenv_split_disjoint_cenv with (Q := Q3)...
            apply wf_lenv_agree_left in H2. apply vwf_envs_unpack in H2. intuition.
            apply vwf_envs_pack... apply dom_cenv_split_exp in H10.
            unfold disjoint in *. fsetdec.
          assert (vwf_envs E Q6 D5).
            apply wf_lenv_split_right in H8...
            apply vwf_envs_unpack in H3. intuition.
          apply lenv_agree_disjoint_cenv with (Q := Q6)...
            apply wf_lenv_agree_left in LA2. apply vwf_envs_unpack in LA2. intuition.
              apply vwf_envs_pack... apply dom_cenv_split_exp in H10.
              unfold disjoint in *. fsetdec.
            apply wf_lenv_split_right in H8. apply vwf_envs_unpack in H8. intuition.
              apply vwf_envs_pack... apply dom_cenv_split_exp in H10.
              unfold disjoint in *. fsetdec.
Qed.

Lemma agree_regular_left: forall E Q1 Q2 Q3 Q4 Q5 Q6 D1 D2 D3 D4 D5 D6,
  cenv_agree E Q3 Q6 ->
  lenv_agree E Q3 D3 D6 ->
  lenv_agree E Q6 D3 D6 ->
  cenv_split_exp E Q1 Q2 Q3 ->
  cenv_split_exp E Q4 Q5 Q6 ->
  lenv_split E Q3 D1 D2 D3 ->
  lenv_split E Q6 D4 D5 D6 ->
  cenv_agree E Q1 Q4 /\ lenv_agree E Q1 D1 D4 /\ lenv_agree E Q4 D1 D4.
Proof.
  intros.
  apply cenv_split_exp_commute in H2. apply cenv_split_exp_commute in H3.
  apply lenv_split_commute in H4. apply lenv_split_commute in H5.
  eapply agree_regular_right; eauto.
Qed.

Lemma cenv_agree_eq: forall E Q1 Q2,
  cenv_agree E Q1 Q2 ->
  dom Q1 [=] dom Q2 ->
  Q1 = Q2.
Proof with auto; try fsetdec.
  intros E Q1.
  induction Q1; intros Q2 Agree Eq; inversion Agree; subst; simpl_env in *...
    f_equal. apply IHQ1...
Qed.

Lemma lenv_agree_eq: forall E Q D1 D2,
  lenv_agree E Q D1 D2 ->
  dom D1 [=] dom D2 ->
  D1 = D2.
Proof with auto; try fsetdec.
  intros E Q D1.
  induction D1; intros D2 Agree Eq; inversion Agree; subst; simpl_env in *...
    f_equal. apply IHD1...
Qed.

Lemma eq_dom_reduce : forall R x S1 S2,
  x `notin` @dom R S1 ->
  x `notin` @dom R S2 ->
  singleton x `union` dom S1 [=] singleton x `union` dom S2 ->
  dom S1 [=] dom S2.
Proof.
  intros. fsetdec.
Qed.

Lemma typing_eq_dom: forall E E' Q Q' D D' e T T',
  typing E D Q e T ->
  typing E' D' Q' e T' ->
  dom Q [=] dom Q' /\ dom D [=] dom D'.
Proof with auto.
  intros E E' Q Q' D D' e T T' Typ Typ'.
  generalize dependent T'. generalize dependent D'.
  generalize dependent Q'. generalize dependent E'.
  (typing_cases (induction Typ) Case); intros E0 Q0 D0 T0 Typ0;
      inversion Typ0; subst; simpl_env in *; try solve [ intuition; fsetdec
                                                                                | eapply IHTyp; eauto ].
    Case "typing_seq".
      apply IHTyp1 in H3.
      apply IHTyp2 in H4.
      apply dom_lenv_split in H. apply dom_cenv_split_exp in H0.
      apply dom_lenv_split in H8. apply dom_cenv_split_exp in H10.
      intuition; fsetdec.
    Case "typing_abs".
      pick fresh x. lapply (H0 x)... lapply (H9 x)... intros.
      apply H1 in H2... simpl_env in H2. intuition.
      apply eq_dom_reduce in H5...
    Case "typing_app".
      apply IHTyp1 in H3.
      apply IHTyp2 in H4.
      apply dom_lenv_split in H. apply dom_cenv_split_exp in H0.
      apply dom_lenv_split in H8. apply dom_cenv_split_exp in H10.
      intuition; fsetdec.
    Case "typing_apair".
      eapply IHTyp1; eauto.
    Case "typing_mpair".
      apply IHTyp1 in H3.
      apply IHTyp2 in H4.
      apply dom_lenv_split in H. apply dom_cenv_split_exp in H0.
      apply dom_lenv_split in H8. apply dom_cenv_split_exp in H10.
      intuition; fsetdec.
    Case "typing_let".
      apply IHTyp1 in H3.
      apply IHTyp2 in H4.
      apply dom_lenv_split in H. apply dom_cenv_split_exp in H0.
      apply dom_lenv_split in H8. apply dom_cenv_split_exp in H10.
      intuition; fsetdec.
    Case "typing_case".
      apply IHTyp1 in H4.
      apply IHTyp2 in H5.
      apply dom_lenv_split in H. apply dom_cenv_split_exp in H0.
      apply dom_lenv_split in H11. apply dom_cenv_split_exp in H12.
      intuition; fsetdec.
Qed.