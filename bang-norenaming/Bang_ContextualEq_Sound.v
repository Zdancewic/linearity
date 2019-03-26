(** Authors: Jianzhou Zhao. *)

Require Export Bang_Parametricity.
Require Import Bang_Parametricity_Macro.
Require Import Bang_PreLib.
Require Import Bang_Renaming.
Require Export Bang_ContextualEq_Def.
Require Import Bang_ContextualEq_Infrastructure.
Require Export Bang_ContextualEq_Lemmas.

Lemma commut_lgamma_subst_close_ee: forall E D dsubst gsubst lgsubst e y,
   wf_lgamma_subst E D dsubst gsubst lgsubst ->
   y `notin` dom lgsubst ->
   apply_gamma_subst lgsubst (close_ee e y)
= close_ee (apply_gamma_subst lgsubst e) y.
Proof.
  intros E D dsubst gsubst lgsubst e y Hwfg Hfv.
  generalize dependent y.
  generalize dependent e.
  induction Hwfg; intros; simpl; auto.
    rewrite subst_ee_close_ee; auto.
      apply notin_fv_ee_typing with (y:=y) in H1; auto.
Qed.

Lemma commut_gamma_subst_close_ee: forall E D dsubst gsubst lgsubst e y,
   wf_lgamma_subst E D dsubst gsubst lgsubst ->
   y `notin` dom gsubst ->
   apply_gamma_subst gsubst (close_ee e y)
= close_ee (apply_gamma_subst gsubst e) y.
Proof.
  intros E D dsubst gsubst lgsubst e y Hwfg Hfv.
  generalize dependent y.
  generalize dependent e.
  induction Hwfg; intros; simpl; auto.
    rewrite subst_ee_close_ee; auto.
      apply notin_fv_ee_typing with (y:=y) in H1; auto.
Qed.

Lemma commut_delta_subst_close_ee: forall dE dsubst e y,
   wf_delta_subst dE dsubst ->
   y `notin` dom dsubst ->
   apply_delta_subst dsubst (close_ee e y)
= close_ee (apply_delta_subst dsubst e) y.
Proof.
  intros dE dsubst e y Hwfd Hfv.
  generalize dependent e.
  generalize dependent y.
  induction Hwfd; intros; simpl; auto.
    rewrite subst_te_close_ee; auto.
Qed.

Lemma wf_lgamma_subst_disjoint' : forall E lE dsubst gsubst lgsubst,
  wf_lgamma_subst E lE dsubst gsubst lgsubst ->
  disjoint dsubst gsubst.
Proof.
  intros E lE dsubst gsubst lgsubst H.
  induction H; auto.
    apply dom_lgamma_subst in H.
    decompose [and] H. clear H.
    apply dom__ddom in H0.
    rewrite H4 in H0.
    solve_uniq.

    apply dom_lgamma_subst in H.
    decompose [and] H. clear H.
    apply dom__gdom in H0.
    rewrite H5 in H0.
    solve_uniq.
Qed.

Lemma dsubst__preserves__in_fv_ee : forall E dsubst e x,
  wf_delta_subst E dsubst ->
  x `in` fv_ee e ->
  x `notin` dom dsubst ->
  x `in` fv_ee (apply_delta_subst dsubst e).
Proof.
  intros E dsubst e x H.
  induction H; intros; simpl; auto.
    rewrite <- swap_subst_te_dsubst with (E:=E); auto.
      assert (J:=@subst_te_fv_ee_eq (apply_delta_subst SE e) X T).
      apply IHwf_delta_subst in H2;auto.
      fsetdec.

      apply dom_delta_subst in H.
      rewrite <- H.
      apply dom__ddom in H0; auto.
Qed.
  
Lemma gsubst__preserves__in_fv_ee : forall E D dsubst gsubst lgsubst e x,
  wf_lgamma_subst E D dsubst gsubst lgsubst ->
  x `in` fv_ee e ->
  x `notin` dom gsubst ->
  x `in` fv_ee (apply_gamma_subst gsubst e).
Proof.
  intros E D dsubst gsubst lgsubst e x H.
  generalize dependent x.
  induction H; intros; simpl; auto.
    rewrite <- swap_subst_ee_gsubst with (E:=E)(D:=lE)(lgsubst:=lgsE)(dsubst:=dsE)(t:=apply_delta_subst_typ dsE T); auto.
      destruct (@in_dec x (fv_ee (apply_gamma_subst gsE e))) as [J | J].
        assert (J':=@subst_ee_fv_ee_in (apply_gamma_subst gsE e) x e0 J).
        apply IHwf_lgamma_subst in H4; auto.
        apply typing_fv_ee_upper in H2. simpl in H2.
        rewrite J'. simpl_env in H5. fsetdec.

        rewrite <- subst_ee_fresh; auto.

      apply wf_lgamma_subst__nfv with (x:=x) in H; auto.
Qed.

Lemma lgsubst__preserves__in_fv_ee : forall E D dsubst gsubst lgsubst e x,
  wf_lgamma_subst E D dsubst gsubst lgsubst ->
  x `in` fv_ee e ->
  x `notin` dom lgsubst ->
  x `in` fv_ee (apply_gamma_subst lgsubst e).
Proof.
  intros E D dsubst gsubst lgsubst e x H.
  generalize dependent x.
  induction H; intros; simpl; auto.
    rewrite <- swap_subst_ee_lgsubst with (E:=E)(D:=lE)(gsubst:=gsE)(dsubst:=dsE)(t:=apply_delta_subst_typ dsE T); auto.
      destruct (@in_dec x (fv_ee (apply_gamma_subst lgsE e))) as [J | J].
        assert (J':=@subst_ee_fv_ee_in (apply_gamma_subst lgsE e) x e0 J).
        apply IHwf_lgamma_subst in H4; auto.
        apply typing_fv_ee_upper in H2. simpl in H2.
        rewrite J'. simpl_env in H5. fsetdec.

        rewrite <- subst_ee_fresh; auto.

      apply wf_lgamma_subst__nfv with (x:=x) in H; auto.
Qed.

Lemma contexting_regular : forall E D T C E' D' T',
  contexting E D T C E' D' T' ->
  wf_env E /\ wf_lenv E D /\ wf_typ E T /\
  wf_env E' /\ wf_lenv E' D' /\ wf_typ E' T'.
Proof.
  intros E D T C E' D' T' Hcontexting.
  (contexting_cases (induction Hcontexting) Case); auto.
  Case "contexting_hole".
    repeat(split; auto).
  Case "contexting_abs_free".
    pick fresh x.
    assert (x `notin` L) as xnotin. auto.
    apply H1 in xnotin.
    destruct xnotin as [J1 [J2 [J3 [J4 [J5 J6]]]]].
    repeat(split; auto).
       inversion J5; subst; auto.
  Case "contexting_abs_capture".
    destruct IHHcontexting as [J1 [J2 [J3 [J4 [J5 J6]]]]].
    assert (J:=@lenv_remove_inv E' D' y (lbind_typ T1') J5 H0).
    destruct J as [D1'0 [D2'0 [EQ1 EQ2]]]; subst.
    rewrite EQ1 in *.
    repeat(split; auto).
      apply wf_lenv_lin_strengthening' in J5; auto.
  Case "contexting_app1".
    destruct IHHcontexting as [J1 [J2 [J3 [J4 [J5 J6]]]]].
    repeat(split; auto).
     inversion J6; subst; auto.
  Case "contexting_app2".
    destruct IHHcontexting as [J1 [J2 [J3 [J4 [J5 J6]]]]].
    repeat(split; auto).
      apply typing_regular in H. 
      destruct H as [J7 [J8 [J9 J10]]].
      inversion J10; subst; auto.
  Case "contexting_tabs_free".
    pick fresh X.
    assert (X `notin` L) as Xnotin. auto.
    apply H0 in Xnotin.
    destruct Xnotin as [J1 [J2 [J3 [J4 [J5 J6]]]]].
    repeat(split; auto).
       inversion J4; subst; auto.

       apply wf_lenv_strengthening_typ in J5; auto.

       apply wf_all_exists with (x:=X); auto.
         inversion J4; subst; auto.
  Case "contexting_tabs_capture".
    destruct IHHcontexting as [J1 [J2 [J3 [J4 [J5 J6]]]]].
    assert (J:=@env_remove_inv E' Y (bind_kn) J4 H).
    destruct J as [E1'0 [E2'0 [EQ1 EQ2]]]; subst.
    rewrite EQ1 in *.
    repeat(split; auto).
     apply wf_all_exists with (x:=Y); auto.
       assert (Y `notin` (fv_tt (close_tt T1' Y))) as YnT1'.
         apply  notin_close_tt; auto.
       apply uniq_from_wf_env in J4.
       assert (Y `notin` dom E1'0) as YnE1'0.
         apply fresh_mid_head in J4; auto.
       assert (Y `notin` dom E2'0) as YnE1'2.
         apply fresh_mid_tail in J4; auto.
       simpl_env. auto.

       rewrite close_open_tt__subst_tt; eauto using type_from_wf_typ.
       apply wf_typ_typ_permute; auto.
       apply wf_typ_typ_renaming_one; auto.
         apply uniq_from_wf_env in J4. solve_uniq.
  Case "contexting_tapp".
    destruct IHHcontexting as [J1 [J2 [J3 [J4 [J5 J6]]]]].
    repeat(split; auto).
      inversion J6; subst... 
      SSCase "wf_typ_all".
        pick fresh Y.
        rewrite (subst_tt_intro Y); auto.
        rewrite_env ((map (subst_tb Y T') empty) ++ E'); auto.
        eapply (wf_typ_subst_tb empty); auto.
        rewrite_env ([(Y, bind_kn)] ++ E'); auto.
  Case "contexting_bang".
    destruct IHHcontexting as [J1 [J2 [J3 [J4 [J5 J6]]]]].
    repeat(split; eauto).
  Case "contexting_let1".
    destruct IHHcontexting as [J1 [J2 [J3 [J4 [J5 J6]]]]].
    repeat(split; auto).
      pick fresh x.
      assert (x `notin` L) as xnotin. auto.
      apply H in xnotin.
      apply typing_regular in xnotin.
      destruct xnotin as [_ [_ [_ WFT2']]].
      rewrite_env (nil++[(x, bind_typ T1')]++E') in WFT2'.
      apply wf_typ_strengthening in WFT2'. auto.
  Case "contexting_let2_free".
    pick fresh x.
    assert (x `notin` L) as xnotin. auto.
    apply H1 in xnotin.
    destruct xnotin as [J1 [J2 [J3 [J4 [J5 J6]]]]].
    repeat(split; auto).
      rewrite_env (nil++[(x, bind_typ T1')]++E') in J6.
      apply wf_typ_strengthening in J6. auto.
  Case "contexting_let2_capture".
    destruct IHHcontexting as [J1 [J2 [J3 [J4 [J5 J6]]]]].
    assert (J:=@env_remove_inv E' y (bind_typ T1') J4 H0).
    destruct J as [E1'0 [E2'0 [EQ1 EQ2]]]; subst.
    rewrite EQ1 in *.
    repeat(split; auto).
      apply wf_typ_strengthening in J6; auto.
  Case "contexting_apair1".
    destruct IHHcontexting as [J1 [J2 [J3 [J4 [J5 J6]]]]].
    apply typing_regular in H. 
    destruct H as [J7 [J8 [J9 J10]]]. 
    repeat(split; eauto).
  Case "contexting_apair2".
    destruct IHHcontexting as [J1 [J2 [J3 [J4 [J5 J6]]]]].
    apply typing_regular in H. 
    destruct H as [J7 [J8 [J9 J10]]]. 
    repeat(split; eauto).
  Case "contexting_fst".
    destruct IHHcontexting as [J1 [J2 [J3 [J4 [J5 J6]]]]].
    repeat(split; eauto).
      inversion J6; subst; auto.
  Case "contexting_snd".
    destruct IHHcontexting as [J1 [J2 [J3 [J4 [J5 J6]]]]].
    repeat(split; eauto).
      inversion J6; subst; auto.
Qed.

Lemma contexting_nonlin_renaming_one : forall E1 E2 D t t' T T' (x y:atom) C E1' E2' D',
  contexting (E1++[(x,bind_typ t)]++E2) D T C (E1'++[(x,bind_typ t')]++E2') D' T' ->
  y `notin` dom E1 `union` dom E2 `union` dom D  `union` dom E1' `union` dom E2' `union` dom D' `union` cv_ec C ->
  contexting (E1++[(y,bind_typ t)]++E2) D T (subst_ec x y C) (E1'++[(y,bind_typ t')]++E2') D' T'.
Proof.
  intros E1 E2 D t t' T T' x y C E1' E2' D' Hcontexting yndom.
  remember (E1++[(x, bind_typ t)]++E2) as E.
  remember (E1'++[(x, bind_typ t')]++E2') as E'.
  generalize dependent E1.
  generalize dependent E2.
  generalize dependent E1'.
  generalize dependent E2'.
  generalize dependent x.
  generalize dependent t.
  generalize dependent t'.
  (contexting_cases (induction Hcontexting) Case); intros; subst; simpl.
  Case "contexting_hole".
    assert (uniq (E1'++[(x,bind_typ t')]++E2')) as Uniq. auto.
    apply mid_list_inv' in HeqE; auto.
    destruct HeqE as [J1 [J2 J3]]; subst.  
    inversion J3; subst.
    apply contexting_hole; simpl_env; auto.
      apply wf_lenv_nonlin_renaming_one with (x:=x); auto.
      apply wf_typ_renaming_one with (x:=x); auto.
  Case "contexting_abs_free".
    apply contexting_abs_free with (L:=L `union` {{y}} `union` {{x}}); simpl_env; auto.
      apply wf_typ_renaming_one with (x:=x); auto.
        pick fresh z.
        assert (z `notin` L) as zn. auto.
        apply H0 in zn.
        apply contexting_regular in zn.
        decompose [and] zn.
        inversion H6; subst; auto.

      simpl in yndom. simpl_env in H0. simpl_env. auto.

      intros x0 x0n.
      assert (x0 `notin` L) as J. auto.
      apply H1 with (E1'0:=E1') (E2'0:=E2') (t0:=t) (t'0:=t')  (x1:=x) (E3:=E2) (E4:=E1) in J; auto.
        simpl_env.
        rewrite subst_ec_open_ec_var; auto.

        rewrite (@cv_ec_open_ec_rec C1 0 x0). simpl. simpl in yndom. auto.
  Case "contexting_abs_capture".
    assert (wf_lenv (E1'++[(x, bind_typ t')]++E2') D') as Wfle.
      apply contexting_regular in Hcontexting.
      decompose [and] Hcontexting; auto.
    assert (J:=@lenv_remove_inv (E1'++[(x, bind_typ t')]++E2') D' y0 (lbind_typ T1') Wfle H0).
    destruct J as [D1'0 [D2'0 [EQ1 EQ2]]]; subst.
    simpl_env.
    simpl_env in yndom. simpl in yndom.
    unfold close_ec in yndom.
    rewrite cv_ec_close_ec_rec in yndom.
    rewrite subst_ec_close_ec; auto.
      apply contexting_abs_capture; simpl; auto.
        simpl_env.
        apply wf_typ_renaming_one with (x:=x); simpl_env; auto.
  
        simpl_env in H1. simpl_env. auto.

        rewrite cv_ec_subst_ec_rec. auto.

        simpl_env in yndom.
        rewrite EQ1 in yndom.
        simpl_env.
        apply IHHcontexting; auto.

      apply wf_lenv_notin_dom with (x:=y0) (T:=T1') in Wfle; auto.
  Case "contexting_app1".
    simpl_env.
    apply contexting_app1 with (D1':=D1') (D2':=D2') (T1':=T1'); auto.
      apply IHHcontexting; auto.
        apply dom_lenv_split in H0.
        rewrite H0 in yndom. auto.

      apply dom_lenv_split in H0. rewrite H0 in yndom.
      apply typing_nonlin_renaming_one with (x:=x); simpl_env; auto.

      apply lenv_split_nonlin_renaming_one with (x:=x); simpl_env; auto.

      apply disjdom_sym_1.
      apply disjdom_sub with (D1:=fv_ee e2 `union` fv_ee y).
        eapply  disjdom_app_r.
        split; auto.
          simpl.
          apply disjdom_one_2; auto.
        apply subst_ee_fv_ee_sub; auto.
  Case "contexting_app2".
    simpl_env.
    apply contexting_app2 with (D1':=D1') (D2':=D2') (T1':=T1'); auto.
      apply dom_lenv_split in H0. rewrite H0 in yndom.
      apply typing_nonlin_renaming_one with (x:=x); simpl_env; auto.

      apply IHHcontexting; auto.
        apply dom_lenv_split in H0.
        rewrite H0 in yndom. auto.

      apply lenv_split_nonlin_renaming_one with (x:=x); simpl_env; auto.

      apply disjdom_sym_1.
      apply disjdom_sub with (D1:=fv_ee e1  `union` fv_ee y).
        eapply  disjdom_app_r.
        split; auto.
          simpl.
          apply disjdom_one_2; auto.
        apply subst_ee_fv_ee_sub; auto.
  Case "contexting_tabs_free".
    apply contexting_tabs_free with (L:=L `union` {{y}} `union` {{x}}); simpl_env; auto.
      simpl in yndom. simpl_env in H0. simpl_env. auto.

      intros X0 X0n.
      assert (X0 `notin` L) as J. auto.
      apply H0 with (E1'0:=[(X0, bind_kn)]++E1') (E2'0:=E2') (t0:=t) (t'0:=t') (x0:=x) (E3:=E2) (E4:=E1) in J; auto.
        simpl_env.
        rewrite subst_ec_open_tc_var; auto.

        rewrite (@cv_ec_open_tc_rec C1 0 X0). simpl. simpl in yndom. auto.
  Case "contexting_tabs_capture".
    assert (wf_env E') as Wfe.
      apply contexting_regular in Hcontexting.
      decompose [and] Hcontexting; auto.
    assert (J:=@env_remove_inv E' Y (bind_kn) Wfe H).
    destruct J as [E1'0 [E2'0 [EQ1 EQ2]]]; subst.
    rewrite EQ1 in *.

    assert (uniq (E1'0++E2'0)) as Uniq.
      apply uniq_from_wf_env in Wfe.
       solve_uniq.
    apply app_mid_inv in HeqE'; auto.
    destruct HeqE' as [[F [fEQ1 fEQ2]] | [F [fEQ1 fEQ2]]]; subst.
      assert ((E1'++[(x, bind_typ t')]++F)++[(Y, bind_kn)]++E2'0 =
                        E1'++[(x, bind_typ t')]++(F++[(Y, bind_kn)]++E2'0)) as J. 
        simpl_env. auto.
      simpl in yndom. simpl_env in yndom. simpl_env. 
      unfold close_tc in yndom. rewrite cv_ec_close_tc_rec in yndom.
      apply IHHcontexting with (E3:=E2) (E4:=E1) (t0:=t) in J; auto.
        assert (env_remove (Y, bind_kn) (E1'++[(y, bind_typ t')]++F++[(Y, bind_kn)]++E2'0) 
                          = E1'++[(y, bind_typ t')]++F++E2'0) as EQ.
          rewrite_env ((E1'++[(y, bind_typ t')]++F)++[(Y, bind_kn)]++E2'0).
          rewrite_env ((E1'++[(y, bind_typ t')]++F)++E2'0).
          apply env_remove_opt.
            apply contexting_regular in J.
            simpl_env.
            decompose [and] J; auto.
        rewrite <- EQ.
        rewrite subst_ec_close_tc; auto.
          apply contexting_tabs_capture; auto.
            apply binds_weaken.
            apply binds_weaken.
            apply binds_app_3.
            apply binds_app_2. auto.

             rewrite cv_ec_subst_ec_rec. auto.

             rewrite EQ.
             simpl_env in H1.
             apply wf_lenv_nonlin_renaming_one with (x:=x); auto.

          simpl.
          apply uniq_from_wf_env in Wfe.
          apply fresh_mid_head in Wfe.
          simpl_env in Wfe.
          auto.          

      assert (E1'0++[(Y, bind_kn)]++F++[(x, bind_typ t')]++E2' =
                        (E1'0++[(Y, bind_kn)]++F)++[(x, bind_typ t')]++E2') as J. 
        simpl_env. auto.
      simpl in yndom. simpl_env in yndom. simpl_env. 
      unfold close_tc in yndom. rewrite cv_ec_close_tc_rec in yndom.
      apply IHHcontexting with (E3:=E2) (E4:=E1) (t0:=t) in J; auto.
        assert (env_remove (Y, bind_kn) (E1'0++[(Y, bind_kn)]++F++[(y, bind_typ t')]++E2') 
                          = E1'0++F++[(y, bind_typ t')]++E2') as EQ.
          apply env_remove_opt.
            apply contexting_regular in J.
            decompose [and] J.
            simpl_env in H6. auto.
        rewrite <- EQ.
        rewrite subst_ec_close_tc; auto.
          simpl_env in J.
          apply contexting_tabs_capture; auto.
            rewrite cv_ec_subst_ec_rec. auto.

            rewrite EQ.
            rewrite_env ((E1'0++F)++[(y, bind_typ t')]++E2').
            apply wf_lenv_nonlin_renaming_one with (x:=x); simpl_env; auto.

          simpl.
          apply uniq_from_wf_env in Wfe.
          apply fresh_mid_tail in Wfe.
          simpl_env in Wfe.
          auto.          
  Case "contexting_tapp".
    simpl_env.
    apply contexting_tapp; auto.
      apply wf_typ_renaming_one with (x:=x); simpl_env; auto.
        apply contexting_regular in Hcontexting. 
        decompose [and] Hcontexting; auto.
  Case "contexting_bang".
    simpl_env.
    apply contexting_bang; auto.
  Case "contexting_let1".
    simpl_env.
    apply contexting_let1 with (L:=L `union` {{x}} `union` {{y}}) (D1':=D1') (D2':=D2') (T1':=T1'); auto.
      apply IHHcontexting; auto.
        apply dom_lenv_split in H0.
        rewrite H0 in yndom. auto.

      intros x0 x0n.
      assert (x0 `notin` L) as x0nL. auto.
      apply H in x0nL.
      apply dom_lenv_split in H0. rewrite H0 in yndom.
      rewrite_env (([(x0,bind_typ T1')]++E1')++[(y,bind_typ t')]++E2').
      rewrite subst_ee_open_ee_var; auto.
      apply typing_nonlin_renaming_one with (x:=x); simpl_env; auto.

      apply lenv_split_nonlin_renaming_one with (x:=x); simpl_env; auto.

      apply disjdom_sym_1.
      apply disjdom_sub with (D1:=fv_ee e2 `union` fv_ee y).
        eapply  disjdom_app_r.
        split; auto.
          simpl.
          apply disjdom_one_2; auto.
        apply subst_ee_fv_ee_sub; auto.
  Case "contexting_let2_free".
    apply contexting_let2_free with (L:=L `union` {{y}} `union` {{x}}) (D1':=D1') (D2':=D2') (T1':=T1'); simpl_env; auto.
      apply dom_lenv_split in H2. rewrite H2 in yndom.
      apply typing_nonlin_renaming_one with (x:=x); simpl_env; auto.

      simpl in yndom. simpl_env in H0. simpl_env. auto.

      intros x0 x0n.
      assert (x0 `notin` L) as JJ. auto.
      apply H1 with (E1'0:=[(x0, bind_typ T1')]++E1') (E2'0:=E2') (t0:=t) (t'0:=t') (x1:=x) (E3:=E2) (E4:=E1) in JJ; auto.
        simpl_env.
        rewrite subst_ec_open_ec_var; auto.

        apply dom_lenv_split in H2. rewrite H2 in yndom.
        rewrite (@cv_ec_open_ec_rec C2 0 x0). simpl. simpl in yndom. auto.

      apply lenv_split_nonlin_renaming_one with (x:=x); simpl_env; auto.
  
      apply disjdom_sym_1.
      apply disjdom_sub with (D1:=fv_ee e1 `union` fv_ee y).
        eapply  disjdom_app_r.
        split; auto.
          simpl.
          apply disjdom_one_2; auto.
        apply subst_ee_fv_ee_sub; auto.
  Case "contexting_let2_capture".
    assert (wf_env E') as Wfe.
      apply contexting_regular in Hcontexting.
      decompose [and] Hcontexting; auto.
    assert (J:=@env_remove_inv E' y0 (bind_typ T1') Wfe H0).
    destruct J as [E1'0 [E2'0 [EQ1 EQ2]]]; subst.
    rewrite EQ1 in *.

    assert (uniq (E1'0++E2'0)) as Uniq.
      apply uniq_from_wf_env in Wfe.
       solve_uniq.
    apply app_mid_inv in HeqE'; auto.
    destruct HeqE' as [[F [fEQ1 fEQ2]] | [F [fEQ1 fEQ2]]]; subst.
      assert ((E1'++[(x, bind_typ t')]++F)++[(y0, bind_typ T1')]++E2'0 =
                        E1'++[(x, bind_typ t')]++(F++[(y0, bind_typ T1')]++E2'0)) as J. 
        simpl_env. auto.
      simpl in yndom. simpl_env in yndom. simpl_env. 
      unfold close_ec in yndom. rewrite cv_ec_close_ec_rec in yndom.
      apply IHHcontexting with (E3:=E2) (E4:=E1) (t0:=t) in J; auto.
        assert (env_remove (y0, bind_typ T1') (E1'++[(y, bind_typ t')]++F++[(y0, bind_typ T1')]++E2'0) 
                          = E1'++[(y, bind_typ t')]++F++E2'0) as EQ.
          rewrite_env ((E1'++[(y, bind_typ t')]++F)++[(y0, bind_typ T1')]++E2'0).
          rewrite_env ((E1'++[(y, bind_typ t')]++F)++E2'0).
          apply env_remove_opt.
            apply contexting_regular in J.
            simpl_env.
            decompose [and] J; auto.
        rewrite <- EQ.
        rewrite subst_ec_close_ec; auto.
          apply contexting_let2_capture with (D1':=D1') (D2':=D2') (T1':=T1'); simpl_env; auto.
            rewrite EQ.
            apply dom_lenv_split in H2. rewrite H2 in yndom. 
            simpl_env in H.
            apply typing_nonlin_renaming_one with (x:=x); simpl_env; auto.

            apply binds_weaken.
            apply binds_weaken.
            apply binds_app_3.
            apply binds_app_2. auto.

            rewrite cv_ec_subst_ec_rec. auto.

            simpl_env in H2.
            rewrite EQ.
            apply lenv_split_nonlin_renaming_one with (x:=x); simpl_env; auto.

            apply disjdom_sym_1.
            apply disjdom_sub with (D1:=fv_ee e1 `union` fv_ee y).
              eapply  disjdom_app_r.
              split; auto.
                simpl.
                apply disjdom_one_2; auto.
              apply subst_ee_fv_ee_sub; auto.

          simpl.
          apply uniq_from_wf_env in Wfe.
          apply fresh_mid_head in Wfe.
          simpl_env in Wfe.
          auto.          

        apply dom_lenv_split in H2. rewrite H2 in yndom. 
        simpl in yndom. simpl_env. auto.

      assert (E1'0++[(y0, bind_typ T1')]++F++[(x, bind_typ t')]++E2' =
                        (E1'0++[(y0, bind_typ T1')]++F)++[(x, bind_typ t')]++E2') as J. 
        simpl_env. auto.
      simpl in yndom. simpl_env in yndom. simpl_env. 
      unfold close_ec in yndom. rewrite cv_ec_close_ec_rec in yndom.
      apply IHHcontexting with (E3:=E2) (E4:=E1) (t0:=t) in J; auto.
        assert (env_remove (y0, bind_typ T1') (E1'0++[(y0, bind_typ T1')]++F++[(y, bind_typ t')]++E2') 
                          = E1'0++F++[(y, bind_typ t')]++E2') as EQ.
          apply env_remove_opt.
            apply contexting_regular in J.
            decompose [and] J.
            simpl_env in H7. auto.
        rewrite <- EQ.
        rewrite subst_ec_close_ec; auto.
          simpl_env in J.
          apply contexting_let2_capture with (D1':=D1') (D2':=D2') (T1':=T1'); simpl_env; auto.
            rewrite EQ.
            apply dom_lenv_split in H2. rewrite H2 in yndom. 
            simpl_env in H.
            rewrite_env ((E1'0++F)++[(y, bind_typ t')]++E2').
            apply typing_nonlin_renaming_one with (x:=x); simpl_env; auto.

            rewrite cv_ec_subst_ec_rec. auto.

            simpl_env in H2.
            rewrite EQ.
            rewrite_env ((E1'0++F)++[(y, bind_typ t')]++E2').
            apply lenv_split_nonlin_renaming_one with (x:=x); simpl_env; auto.

            apply disjdom_sym_1.
            apply disjdom_sub with (D1:=fv_ee e1 `union` fv_ee y).
              eapply  disjdom_app_r.
              split; auto.
                simpl.
                apply disjdom_one_2; auto.
              apply subst_ee_fv_ee_sub; auto.

          simpl.
          apply uniq_from_wf_env in Wfe.
          apply fresh_mid_tail in Wfe.
          simpl_env in Wfe.
          auto.          

        apply dom_lenv_split in H2. rewrite H2 in yndom. 
        simpl in yndom. simpl_env. auto.
  Case "contexting_apair1".
    simpl_env.
    apply contexting_apair1 with (T1':=T1'); auto.
      apply typing_nonlin_renaming_one with (x:=x); simpl_env; auto.
  Case "contexting_apair2".
    simpl_env.
    apply contexting_apair2 with (T1':=T1'); auto.
      apply typing_nonlin_renaming_one with (x:=x); simpl_env; auto.
  Case "contexting_fst".
    simpl_env.
    apply contexting_fst with (T2':=T2'); auto.
  Case "contexting_snd".
    simpl_env.
    apply contexting_snd with (T1':=T1'); auto.
Qed.

Lemma contexting_lin_renaming_one : forall E D1 D2 t t' T T' (x y:atom) C E' D1' D2',
  contexting E (D1++[(x,lbind_typ t)]++D2) T C E' (D1'++[(x,lbind_typ t')]++D2') T' ->
  y `notin` dom D1 `union` dom D2 `union` dom E  `union` dom D1' `union` dom D2' `union` dom E' `union` cv_ec C ->
  contexting E (D1++[(y,lbind_typ t)]++D2) T (subst_ec x y C) E' (D1'++[(y,lbind_typ t')]++D2') T'.
Proof.
  intros E D1 D2 t t' T T' x y C E' D1' D2' Hcontexting yndom.
  remember (D1++[(x, lbind_typ t)]++D2) as D.
  remember (D1'++[(x, lbind_typ t')]++D2') as D'.
  generalize dependent D1.
  generalize dependent D2.
  generalize dependent D1'.
  generalize dependent D2'.
  generalize dependent x.
  generalize dependent t.
  generalize dependent t'.
  (contexting_cases (induction Hcontexting) Case); intros; subst; simpl.
  Case "contexting_hole".
    assert (uniq (D1'++[(x,lbind_typ t')]++D2')) as Uniq. eauto.
    apply mid_list_inv' in HeqD; auto.
    destruct HeqD as [J1 [J2 J3]]; subst.  
    inversion J3; subst.
    apply contexting_hole; auto.
      simpl_env.
      apply wf_lenv_renaming_one with (x0:=x); auto.
        assert (x `notin` dom E) as xnE. 
          apply wf_lenv_notin_dom with (x:=x) (T:=t) in H; auto.
        assert (x `notin` dom D1) as xnD1. 
          apply fresh_mid_head in Uniq; auto.
        assert (x `notin` dom D2) as xnD2. 
          apply fresh_mid_tail in Uniq; auto.
        auto.
  Case "contexting_abs_free".
    apply contexting_abs_free with (L:=L `union` {{y}} `union` {{x}}); auto.
      simpl in yndom. simpl_env in H0. simpl_env. auto.

      intros x0 x0n.
      assert (x0 `notin` L) as J. auto.
      apply H1 with (D1'0:=[(x0, lbind_typ T1')]++D1') (D2'0:=D2') (t0:=t) (t'0:=t')  (x1:=x) (D3:=D2) (D4:=D1) in J; auto.
        simpl_env.
        rewrite subst_ec_open_ec_var; auto.

        rewrite (@cv_ec_open_ec_rec C1 0 x0). simpl. simpl in yndom. auto.
  Case "contexting_abs_capture".
    assert (wf_lenv E' D') as Wfle.
      apply contexting_regular in Hcontexting.
      decompose [and] Hcontexting; auto.
    assert (J:=@lenv_remove_inv E' D' y0 (lbind_typ T1') Wfle H0).
    destruct J as [D1'0 [D2'0 [EQ1 EQ2]]]; subst.
    rewrite EQ1 in *.
    assert (uniq (D1'0++D2'0)) as Uniq.
      apply uniq_from_wf_lenv in Wfle.
      solve_uniq.
    apply app_mid_inv in HeqD'; auto.
    destruct HeqD' as [[F [fEQ1 fEQ2]] | [F [fEQ1 fEQ2]]]; subst.
      assert ((D1'++[(x, lbind_typ t')]++F)++[(y0, lbind_typ T1')]++D2'0 =
                        D1'++[(x, lbind_typ t')]++(F++[(y0, lbind_typ T1')]++D2'0)) as J. 
        simpl_env. auto.
      simpl in yndom. simpl_env in yndom. simpl_env. 
      unfold close_ec in yndom. rewrite cv_ec_close_ec_rec in yndom.
      apply IHHcontexting with (D3:=D2) (D4:=D1) (t0:=t) in J; auto.
        assert (lenv_remove (y0, lbind_typ T1') (D1'++[(y, lbind_typ t')]++F++[(y0, lbind_typ T1')]++D2'0) 
                          = D1'++[(y, lbind_typ t')]++F++D2'0) as EQ.
          rewrite_env ((D1'++[(y, lbind_typ t')]++F)++[(y0, lbind_typ T1')]++D2'0).
          rewrite_env ((D1'++[(y, lbind_typ t')]++F)++D2'0).
          apply lenv_remove_opt.
            apply contexting_regular in J.
            simpl_env.
            decompose [and] J; eauto.

        rewrite <- EQ.
        rewrite subst_ec_close_ec; auto.
          apply contexting_abs_capture; auto.
            apply binds_weaken.
            apply binds_weaken.
            apply binds_app_3.
            apply binds_app_2. auto.

             rewrite cv_ec_subst_ec_rec. auto.

          simpl.
          apply uniq_from_wf_lenv in Wfle.
          apply fresh_mid_head in Wfle.
          simpl_env in Wfle.
          auto.          

      assert (D1'0++[(y0, lbind_typ T1')]++F++[(x, lbind_typ t')]++D2' =
                        (D1'0++[(y0, lbind_typ T1')]++F)++[(x, lbind_typ t')]++D2') as J. 
        simpl_env. auto.
      simpl in yndom. simpl_env in yndom. simpl_env. 
      unfold close_ec in yndom. rewrite cv_ec_close_ec_rec in yndom.
      apply IHHcontexting with (D3:=D2) (D4:=D1) (t0:=t) in J; auto.
        assert (lenv_remove (y0, lbind_typ T1') (D1'0++[(y0, lbind_typ T1')]++F++[(y, lbind_typ t')]++D2') 
                          = D1'0++F++[(y, lbind_typ t')]++D2') as EQ.
          apply lenv_remove_opt.
            apply contexting_regular in J.
            decompose [and] J.
            simpl_env in H6; eauto.

        rewrite <- EQ.
        rewrite subst_ec_close_ec; auto.
          simpl_env in J.
          apply contexting_abs_capture; auto.
             rewrite cv_ec_subst_ec_rec. auto.

          simpl.
          apply uniq_from_wf_lenv in Wfle.
          apply fresh_mid_tail in Wfle.
          simpl_env in Wfle.
          auto.          
  Case "contexting_app1".
    simpl_env.
    assert (Split:=H0).
    apply lenv_split_cases_mid in H0.
    destruct H0 as [LEFT | RIGHT].
    SCase "left".
      destruct LEFT as [D1L' [D1R' [D2L' [D2R' [Q1 [Q2 [S1 S2]]]]]]]; subst.
      assert (D1L' ++ [(x, lbind_typ t')] ++ D1R'=D1L' ++ [(x, lbind_typ t')] ++ D1R') as IH1. auto.
      assert (DomEq2:=S2).
      apply dom_lenv_split in DomEq2.
      rewrite DomEq2 in yndom.
      assert (DomEq1:=S1).
      apply dom_lenv_split in DomEq1.
      rewrite DomEq1 in yndom.
      apply IHHcontexting with (D3:=D2) (D4:=D1) (t0:=t) in IH1; auto.
      clear IHHcontexting.
      assert (x `notin` (dom (D2L'++D2R') `union` dom E')) as J.
        eapply lenv_split_not_in_left; eauto.
          simpl_env. auto.
      rewrite <- (non_subst E' (D2L'++D2R') e2 T1' x y); auto.
      apply contexting_app1 with (D1':=D1L' ++ [(y, lbind_typ t')] ++ D1R') (D2':=D2L' ++ D2R') (T1':=T1'); auto.
        eapply lenv_split_sub_left; eauto.
          apply wf_lenv_split in Split.
          assert (x `notin` dom D1'0) as xnotinD1'0.
            apply uniq_from_wf_lenv in Split.
            apply fresh_mid_head in Split; auto.
          assert (x `notin` dom D2'0) as xnotinD2'0.
            apply uniq_from_wf_lenv in Split.
            apply fresh_mid_tail in Split; auto.
          clear - Split xnotinD1'0 xnotinD2'0 DomEq1 DomEq2 yndom J.
          apply wf_lenv_renaming_one with (x0:=x); auto.
             rewrite DomEq1. rewrite DomEq2. auto.
        destruct H1 as [H11 H12].
        assert (y `notin` fv_ee e2) as yne2.
          apply notin_fv_ee_typing with (y:=y) in H; auto.
        split; intros x0 x0Fv.
          destruct (y==x0); subst.
            contradict x0Fv; auto.

            apply H11 in x0Fv.
            simpl_env. simpl_env in x0Fv. auto.  
          destruct (y==x0); subst; auto.
            apply H12.
            clear J yne2 IH1 Split yndom H11 H12 Hcontexting Split DomEq2 DomEq1 S1 S2 H.  
            simpl_env in *. fsetdec.
    SCase "right".
      destruct RIGHT as [D1L' [D1R' [D2L' [D2R' [Q1 [Q2 [S1 S2]]]]]]]; subst.
      assert (x `in` fv_ee e2) as xine2.
        apply in_lfv_ee_typing with (y:=x) in H; auto.
          simpl_env. auto.
      assert (x `notin` fv_ee e2) as xnotine2.
        destruct H1 as [J1 J2].
        assert (x `in` dom (D1++[(x, lbind_typ t)]++D2)) as J. simpl_env. auto.
        apply J2 in J. auto.
      contradict xine2; auto.
  Case "contexting_app2".
    simpl_env.
    assert (Split:=H0).
    apply lenv_split_cases_mid in H0.
    destruct H0 as [LEFT | RIGHT].
    SCase "left".
      destruct LEFT as [D1L' [D1R' [D2L' [D2R' [Q1 [Q2 [S1 S2]]]]]]]; subst.
      assert (x `in` fv_ee e1) as xinv1.
        apply in_lfv_ee_typing with (y:=x) in H; auto.
          simpl_env. auto.
      assert (x `notin` fv_ee e1) as xnotinv1.
        destruct H1 as [J1 J2].
        assert (x `in` dom (D1++[(x, lbind_typ t)]++D2)) as J. simpl_env. auto.
        apply J2 in J. auto.
      contradict xinv1; auto.
    SCase "right".
      destruct RIGHT as [D1L' [D1R' [D2L' [D2R' [Q1 [Q2 [S1 S2]]]]]]]; subst.
      assert (D2L' ++ [(x, lbind_typ t')] ++ D2R'=D2L' ++ [(x, lbind_typ t')] ++ D2R') as IH2. auto.
      assert (DomEq2:=S2).
      apply dom_lenv_split in DomEq2.
      rewrite DomEq2 in yndom.
      assert (DomEq1:=S1).
      apply dom_lenv_split in DomEq1.
      rewrite DomEq1 in yndom.
      apply IHHcontexting with (D3:=D2) (D4:=D1) (t0:=t) in IH2; auto.
      clear IHHcontexting.
      assert (x `notin` (dom (D1L'++D1R') `union` dom E')) as J.
        eapply lenv_split_not_in_right; eauto.
          simpl_env. auto.
      rewrite <- (non_subst E' (D1L'++D1R') e1 (typ_arrow T1' T2') x y); auto.
      apply contexting_app2 with (T1':=T1') (D1':=D1L' ++ D1R') (D2':=D2L' ++ [(y, lbind_typ t')] ++ D2R'); auto.
        simpl_env.
        eapply lenv_split_sub_right; eauto.
          apply wf_lenv_split in Split.
          assert (x `notin` dom D1'0) as xnotinD1'0.
            apply uniq_from_wf_lenv in Split.
            apply fresh_mid_head in Split; auto.
          assert (x `notin` dom D2'0) as xnotinD2'0.
            apply uniq_from_wf_lenv in Split.
            apply fresh_mid_tail in Split; auto.
          clear - Split xnotinD1'0 xnotinD2'0 DomEq1 DomEq2 yndom J.
          apply wf_lenv_renaming_one with (x0:=x); auto.
             rewrite DomEq1. rewrite DomEq2. auto.
        destruct H1 as [H21 H22].
        assert (y `notin` fv_ee e1) as yne1.
          apply notin_fv_ee_typing with (y:=y) in H; auto.
        split; intros x0 x0Fv.
          destruct (y==x0); subst.
            contradict x0Fv; auto.

            apply H21 in x0Fv.
            simpl_env. simpl_env in x0Fv. auto.  
          destruct (y==x0); subst; auto.
            apply H22.
            clear J yne1 IH2 Split yndom H21 H22 Hcontexting Split DomEq2 DomEq1 S1 S2 H.  
            simpl_env in *. fsetdec.
  Case "contexting_tabs_free".
    apply contexting_tabs_free with (L:=L `union` {{y}} `union` {{x}}); auto.
      simpl in yndom. simpl_env in H0. simpl_env. auto.

      intros X0 X0n.
      assert (X0 `notin` L) as J. auto.
      apply H0 with (D1'0:=D1') (D2'0:=D2') (t0:=t) (t'0:=t') (x0:=x) (D3:=D2) (D4:=D1) in J; auto.
        simpl_env.
        rewrite subst_ec_open_tc_var; auto.

        rewrite (@cv_ec_open_tc_rec C1 0 X0). simpl. simpl in yndom. auto.
  Case "contexting_tabs_capture".
    assert (wf_env E') as Wfe.
      apply contexting_regular in Hcontexting.
      decompose [and] Hcontexting; auto.
    assert (J:=@env_remove_inv E' Y (bind_kn) Wfe H).
    destruct J as [E1'0 [E2'0 [EQ1 EQ2]]]; subst.
    simpl_env.
    simpl_env in yndom. simpl in yndom.
    unfold close_tc in yndom.
    rewrite cv_ec_close_tc_rec in yndom.
    rewrite subst_ec_close_tc; auto.
      apply contexting_tabs_capture; simpl; auto.
        rewrite cv_ec_subst_ec_rec. auto. 

        simpl_env in yndom.
        rewrite EQ1 in yndom.
        simpl_env.
        apply IHHcontexting; auto.

        simpl_env.
        simpl_env in yndom.
        rewrite EQ1 in *.
        assert (x `notin` dom (E1'0++E2'0)) as ynE0.
          apply wf_lenv_notin_dom with (x:=x) (T:=t') in H1; auto.
        assert (x `notin` dom D1') as ynD1'.
          apply fresh_mid_head with (E:=D2') (a:=lbind_typ t'); auto.
            apply uniq_from_wf_lenv in H1; auto.
        assert (x `notin` dom D2') as ynD2'.
          apply fresh_mid_tail with (F:=D1') (a:=lbind_typ t'); auto.
             apply uniq_from_wf_lenv in H1; auto.
        apply wf_lenv_renaming_one with (x0:=x); auto.

      apply contexting_regular in Hcontexting.
      decompose [and] Hcontexting.
      apply wf_lenv_notin_dom with (x:=x) (T:=t') in H6; auto.
  Case "contexting_tapp".
    simpl_env.
    apply contexting_tapp; auto.
  Case "contexting_bang".
    contradict HeqD'. apply nil_neq_one_mid.
  Case "contexting_let1".
    simpl_env.
    assert (Split:=H0).
    apply lenv_split_cases_mid in H0.
    destruct H0 as [LEFT | RIGHT].
    SCase "left".
      destruct LEFT as [D1L' [D1R' [D2L' [D2R' [Q1 [Q2 [S1 S2]]]]]]]; subst.
      assert (D1L' ++ [(x, lbind_typ t')] ++ D1R'=D1L' ++ [(x, lbind_typ t')] ++ D1R') as IH1. auto.
      assert (DomEq2:=S2).
      apply dom_lenv_split in DomEq2.
      rewrite DomEq2 in yndom.
      assert (DomEq1:=S1).
      apply dom_lenv_split in DomEq1.
      rewrite DomEq1 in yndom.
      apply IHHcontexting with (D3:=D2) (D4:=D1) (t0:=t) in IH1; auto.
      clear IHHcontexting.
      assert (x `notin` (dom (D2L'++D2R') `union` dom E')) as J.
        eapply lenv_split_not_in_left; eauto.
          simpl_env. auto.
      assert (x `notin` fv_ee e2) as xne2.
        pick fresh z.
        assert (z `notin` L) as znL. auto.
        apply H in znL.
        apply notin_fv_ee_typing with (y:=x) in znL; auto.
        apply notin_fv_ee_open_ee_inv in znL; auto.
      rewrite <- subst_ee_fresh; auto.
      apply contexting_let1 with (L:=L `union` {{x}}) (D1':=D1L' ++ [(y, lbind_typ t')] ++ D1R') (D2':=D2L' ++ D2R') (T1':=T1'); auto.
        eapply lenv_split_sub_left; eauto.
          apply wf_lenv_split in Split.
          assert (x `notin` dom D1'0) as xnotinD1'0.
            apply uniq_from_wf_lenv in Split.
            apply fresh_mid_head in Split; auto.
          assert (x `notin` dom D2'0) as xnotinD2'0.
            apply uniq_from_wf_lenv in Split.
            apply fresh_mid_tail in Split; auto.
          clear - Split xnotinD1'0 xnotinD2'0 DomEq1 DomEq2 yndom J.
          apply wf_lenv_renaming_one with (x0:=x); auto.
             rewrite DomEq1. rewrite DomEq2. auto.

        destruct H1 as [H11 H12].
        assert (y `notin` fv_ee e2) as yne2.
          pick fresh z.
          assert (z `notin` L) as znL. auto.
          apply H in znL.
          apply notin_fv_ee_typing with (y:=y) in znL; auto.
          apply notin_fv_ee_open_ee_inv in znL; auto.
        split; intros x0 x0Fv.
          destruct (y==x0); subst.
            contradict x0Fv; auto.

            apply H11 in x0Fv.
            simpl_env. simpl_env in x0Fv. auto.  
          destruct (y==x0); subst; auto.
            apply H12.
            clear J yne2 IH1 Split yndom H11 H12 Hcontexting Split DomEq2 DomEq1 S1 S2 H.  
            simpl_env in *. fsetdec.

    SCase "right".
      destruct RIGHT as [D1L' [D1R' [D2L' [D2R' [Q1 [Q2 [S1 S2]]]]]]]; subst.
      assert (x `in` fv_ee e2) as xine2.
        pick fresh z.
        assert (z `notin` L) as znL. auto.
        apply H in znL.
        apply in_lfv_ee_typing with (y:=x) in znL; auto.
          unfold open_ee in znL.
          apply fv_in_open_ee_inv in znL; auto.
          simpl_env. auto.
      assert (x `notin` fv_ee e2) as xnotine2.
        destruct H1 as [J1 J2].
        assert (x `in` dom (D1++[(x, lbind_typ t)]++D2)) as J. simpl_env. auto.
        apply J2 in J. auto.
      contradict xine2; auto.
  Case "contexting_let2_free".
    simpl_env.
    assert (Split:=H2).
    apply lenv_split_cases_mid in H2.
    destruct H2 as [LEFT | RIGHT].
    SCase "left".
      destruct LEFT as [D1L' [D1R' [D2L' [D2R' [Q1 [Q2 [S1 S2]]]]]]]; subst.
      assert (x `in` fv_ee e1) as xine1.
        apply in_lfv_ee_typing with (y:=x) in H; auto.
          simpl_env. auto.
      assert (x `notin` fv_ee e1) as xnotine1.
        destruct H3 as [J1 J2].
        assert (x `in` dom (D1++[(x, lbind_typ t)]++D2)) as J. simpl_env. auto.
        apply J2 in J. auto.
      contradict xine1; auto.
    SCase "right".
      destruct RIGHT as [D1L' [D1R' [D2L' [D2R' [Q1 [Q2 [S1 S2]]]]]]]; subst.
      assert (D2L' ++ [(x, lbind_typ t')] ++ D2R'=D2L' ++ [(x, lbind_typ t')] ++ D2R') as IH1. auto.
      assert (DomEq2:=S2).
      apply dom_lenv_split in DomEq2.
      rewrite DomEq2 in yndom.
      assert (DomEq1:=S1).
      apply dom_lenv_split in DomEq1.
      rewrite DomEq1 in yndom.
      assert (x `notin` (dom (D1L'++D1R') `union` dom E')) as J.
        eapply lenv_split_not_in_right; eauto.
          simpl_env. auto.
      assert (x `notin` fv_ee e1) as xne1.
        apply notin_fv_ee_typing with (y:=x) in H; auto.
      rewrite <- subst_ee_fresh; auto.
      apply contexting_let2_free with (L:=L `union` {{x}} `union` {{y}})  (D1':=D1L' ++ D1R') (D2':=D2L' ++ [(y, lbind_typ t')] ++ D2R') (T1':=T1'); auto.
        simpl in yndom. simpl_env in H0. simpl_env. auto.

        intros x0 x0n.
        assert (x0 <> x) as xnx0. destruct_notin. clear - NotInTac2. auto.
        assert (expr y) as Expy. auto.
        rewrite subst_ec_open_ec_var; try solve [assumption].
        apply H1 with (D3:=D2) (D4:=D1) (t0:=t) (x0:=x0) in IH1; auto.
          rewrite (@cv_ec_open_ec_rec C2 0 x0). simpl. simpl in yndom. auto.

        eapply lenv_split_sub_right; eauto.
          apply wf_lenv_split in Split.
          assert (x `notin` dom D1'0) as xnotinD1'0.
            apply uniq_from_wf_lenv in Split.
            apply fresh_mid_head in Split; auto.
          assert (x `notin` dom D2'0) as xnotinD2'0.
            apply uniq_from_wf_lenv in Split.
            apply fresh_mid_tail in Split; auto.
          clear - Split xnotinD1'0 xnotinD2'0 DomEq1 DomEq2 yndom J.
          apply wf_lenv_renaming_one with (x0:=x); auto.
             rewrite DomEq1. rewrite DomEq2. auto.

        destruct H3 as [H11 H12].
        assert (y `notin` fv_ee e1) as yne1.
          apply notin_fv_ee_typing with (y:=y) in H; auto.
        split; intros x0 x0Fv.
          destruct (y==x0); subst.
            contradict x0Fv; auto.

            apply H11 in x0Fv.
            simpl_env. simpl_env in x0Fv. auto.  
          destruct (y==x0); subst; auto.
            apply H12.
            clear J yne1 IH1 Split yndom H11 H12 H1 Split DomEq2 DomEq1 S1 S2 H.  
            simpl_env in *. fsetdec.
  Case "contexting_let2_capture".
    assert (Split:=H2).
    apply lenv_split_cases_mid in H2.
    destruct H2 as [LEFT | RIGHT].
    SCase "left".
      destruct LEFT as [D1L' [D1R' [D2L' [D2R' [Q1 [Q2 [S1 S2]]]]]]]; subst.
      assert (x `in` fv_ee e1) as xine1.
        apply in_lfv_ee_typing with (y:=x) in H; auto.
          simpl_env. auto.
      assert (x `notin` fv_ee e1) as xnotine1.
        destruct H3 as [J1 J2].
        assert (x `in` dom (D1++[(x, lbind_typ t)]++D2)) as J. simpl_env. auto.
        apply J2 in J. auto.
      contradict xine1; auto.
    SCase "right".
      destruct RIGHT as [D1L' [D1R' [D2L' [D2R' [Q1 [Q2 [S1 S2]]]]]]]; subst.
      assert (D2L' ++ [(x, lbind_typ t')] ++ D2R'=D2L' ++ [(x, lbind_typ t')] ++ D2R') as IH1. auto.
      assert (DomEq2:=S2).
      apply dom_lenv_split in DomEq2.
      rewrite DomEq2 in yndom.
      assert (DomEq1:=S1).
      apply dom_lenv_split in DomEq1.
      rewrite DomEq1 in yndom.
      assert (x `notin` (dom (D1L'++D1R') `union` dom E')) as J.
        apply lenv_split_not_in_right with (x:=x) in Split; simpl_env; auto.  
          assert (uniq E') as UniqE'.
            apply contexting_regular in Hcontexting.
            decompose [and] Hcontexting; auto.

          destruct (@_env_remove_dom E' y0 (bind_typ T1') UniqE') as [J1 J2].
          apply J1 in H0. rewrite H0 in Split. simpl_env in Split. simpl_env in H1.
          clear - Split H1. fsetdec.
      assert (wf_env E') as Wfe.
        apply contexting_regular in Hcontexting.
        decompose [and] Hcontexting; auto.
      assert (JJ:=@env_remove_inv E' y0 (bind_typ T1') Wfe H0).
      destruct JJ as [E1'0 [E2'0 [EQ1 EQ2]]]; subst.
      simpl_env.
      simpl_env in yndom. simpl in yndom.
      unfold close_ec in yndom.
      rewrite cv_ec_close_ec_rec in yndom.
      rewrite subst_ec_close_ec; auto.
      assert (x `notin` fv_ee e1) as xne1.
        rewrite EQ1 in H.
        apply notin_fv_ee_typing with (y:=x) in H; auto.
      rewrite <- subst_ee_fresh; auto.
      simpl_env in yndom.
      rewrite EQ1 in yndom.
      apply contexting_let2_capture with (D1':=D1L' ++ D1R') (D2':=D2L' ++ [(y, lbind_typ t')] ++ D2R') (T1':=T1'); auto.
        rewrite cv_ec_subst_ec_rec. 
        simpl in yndom. simpl_env in H0. simpl_env. auto.

        eapply lenv_split_sub_right; eauto.
          apply wf_lenv_split in Split.
          assert (x `notin` dom D1'0) as xnotinD1'0.
            apply uniq_from_wf_lenv in Split.
            apply fresh_mid_head in Split; auto.
          assert (x `notin` dom D2'0) as xnotinD2'0.
            apply uniq_from_wf_lenv in Split.
            apply fresh_mid_tail in Split; auto.
          rewrite EQ1. rewrite EQ1 in Split.
          clear - Split xnotinD1'0 xnotinD2'0 DomEq1 DomEq2 yndom J.
          apply wf_lenv_renaming_one with (x0:=x); auto.
             rewrite DomEq1. rewrite DomEq2. auto.

        destruct H3 as [H11 H12].
        assert (y `notin` fv_ee e1) as yne1.
           rewrite EQ1 in H.
          apply notin_fv_ee_typing with (y:=y) in H; auto.
        split; intros x0 x0Fv.
          destruct (y==x0); subst.
            contradict x0Fv; auto.

            apply H11 in x0Fv.
            simpl_env. simpl_env in x0Fv. auto.  
          destruct (y==x0); subst; auto.
            apply H12.
            clear J yne1 IH1 Split yndom H11 H12 Split DomEq2 DomEq1 S1 S2 H.  
            simpl_env in *. fsetdec.
  Case "contexting_apair1".
    simpl_env.
    apply contexting_apair1 with (T1':=T1'); auto.
      apply typing_lin_renaming_one; auto.
  Case "contexting_apair2".
    simpl_env.
    apply contexting_apair2 with (T1':=T1'); auto.
      apply typing_lin_renaming_one; auto.
  Case "contexting_fst".
    simpl_env.
    apply contexting_fst with (T2':=T2'); auto.
  Case "contexting_snd".
    simpl_env.
    apply contexting_snd with (T1':=T1'); auto.
Qed.

Lemma contexting_plug_typing : forall E D T C E' D' T' e,
  contexting E D T C E' D' T' ->
  typing E D e T ->
  typing E' D' (plug C e) T'.
Proof.
  intros E D T C E' D' T' e Hcontexting Htyping.
  generalize dependent e.
  (contexting_cases (induction Hcontexting) Case); 
    intros e Htyping; simpl in *; eauto.
  Case "contexting_abs_free".
    apply typing_abs with (L:=L `union` cv_ec C1); auto.
      intros x xn.
      assert (x `notin` L) as xnL. auto.
      apply H1 with (e:=open_ee (shift_ee e) x) in xnL; auto.
        rewrite open_ee_plug; auto.
          eapply disjdom_app_l; auto.
          split; simpl.
            apply disjdom_one_2; auto.
            apply disjdom_nil_1.

        rewrite <- shift_ee_expr; auto.
        rewrite <- open_ee_expr; auto.

  Case "contexting_abs_capture".
    apply typing_abs with (L:=dom E' `union` dom (lenv_remove (y, lbind_typ T1') D') `union` cv_ec C1 `union`  (cv_ec (close_ec C1 y))); auto.
      intros x xnL.
      assert (disjdom (union (fv_ee x) (fv_te x)) (cv_ec (close_ec C1 y))) as Disj.
        eapply disjdom_app_l.
        split.
          apply disjdom_one_2; auto.
          simpl. apply disjdom_nil_1.
      rewrite open_ee_plug; auto.
      assert (J:=Htyping).
      apply IHHcontexting in J.
        rewrite <- shift_ee_expr; auto.
        assert (wf_lenv E' D') as Wfle. 
          apply contexting_regular in Hcontexting.
          decompose [and] Hcontexting; auto.
        assert (J':=@lenv_remove_inv E' D' y (lbind_typ T1') Wfle H0).
        destruct J' as [D1' [D2' [EQ1 EQ2]]]; subst.
        rewrite EQ1 in *.
        rewrite close_open_ee__subst_ee; auto.
        assert (context C1) as Ctx1.
          apply contexting__context in Hcontexting; auto.
        rewrite close_open_ec__subst_ec; auto.
      assert (disjdom (union {{y}} (union (fv_ee x) (fv_te x))) (cv_ec C1)) as Disj'.
        eapply disjdom_app_l.
        split.
          apply disjdom_one_2; auto.
        eapply disjdom_app_l.
        split.
          apply disjdom_one_2; auto.
          simpl. apply disjdom_nil_1.
        rewrite <- subst_ee_plug; auto.
       apply typing_lin_renaming_permute with (x:=y); auto.

  Case "contexting_tabs_free".
    apply typing_tabs with (L:=L `union` cv_ec C1); auto.
      intros X Xn.
      assert (X `notin` L) as XnL. auto.
      apply H0 with (e:=open_te (shift_te e) X) in XnL; auto.
        rewrite open_te_plug; auto.
          apply disjdom_one_2; auto.
        rewrite <- shift_te_expr; auto.
        rewrite <- open_te_expr'; auto.

  Case "contexting_tabs_capture".
    apply typing_tabs with (L:=dom D' `union` dom (env_remove (Y, bind_kn) E') `union` cv_ec C1 `union`  (cv_ec (close_tc C1 Y))); auto.
      intros X XnL.
      assert (disjdom (fv_tt X) (cv_ec (close_tc C1 Y))) as Disj.
        apply disjdom_one_2; auto.
      rewrite open_te_plug; auto.
      assert (J:=Htyping).
      apply IHHcontexting in J.
      rewrite <- shift_te_expr; auto.
      assert (wf_env E') as Wfe. 
        apply contexting_regular in Hcontexting.
        decompose [and] Hcontexting; auto.
      assert (J':=@env_remove_inv E' Y (bind_kn) Wfe H).
      destruct J' as [E1' [E2' [EQ1 EQ2]]]; subst.
      rewrite EQ1 in *.
      rewrite close_open_te__subst_te; auto.
      assert (context C1) as Ctx1.
        apply contexting__context in Hcontexting; auto.
      rewrite close_open_tc__subst_tc; auto.
      assert (disjdom (union {{Y}} (fv_tt X)) (cv_ec C1)) as Disj'.
        eapply disjdom_app_l.
        split.
          apply disjdom_one_2; auto.
          apply disjdom_one_2; auto.
      rewrite <- subst_te_plug; auto.
      rewrite close_open_tt__subst_tt; auto.
        apply typing_typ_renaming_permute with (X:=Y); auto.

  Case "contexting_let1".
    apply typing_let with (L:=L)(D1:=D1')(D2:=D2')(T1:=T1'); auto.

  Case "contexting_let2_free".
    apply typing_let with (L:=L `union` cv_ec C2)(D1:=D1')(D2:=D2')(T1:=T1'); auto.
      intros x xn.
      assert (x `notin` L) as xnL. auto.
      apply H1 with (e:=open_ee (shift_ee e) x) in xnL; auto.
        rewrite open_ee_plug; auto.
          eapply disjdom_app_l; auto.
          split; simpl.
            apply disjdom_one_2; auto.
            apply disjdom_nil_1.

        rewrite <- shift_ee_expr; auto.
        rewrite <- open_ee_expr; auto.

  Case "contexting_let2_capture".
    apply typing_let with (L:=dom D3' `union` dom (env_remove (y, bind_typ T1') E') `union` cv_ec C2 `union`  (cv_ec (close_ec C2 y)))(D1:=D1')(D2:=D2')(T1:=T1'); auto.
      intros x xnL.
      assert (disjdom (union (fv_ee x) (fv_te x)) (cv_ec (close_ec C2 y))) as Disj.
        eapply disjdom_app_l.
        split.
          apply disjdom_one_2; auto.
          simpl. apply disjdom_nil_1.
      rewrite open_ee_plug; auto.
      assert (J:=Htyping).
      apply IHHcontexting in J.
      rewrite <- shift_ee_expr; auto.
      assert (wf_env E') as Wfe. 
        apply contexting_regular in Hcontexting.
        decompose [and] Hcontexting; auto.
      assert (J':=@env_remove_inv E' y (bind_typ T1') Wfe H0).
      destruct J' as [E1' [E2' [EQ1 EQ2]]]; subst.
      rewrite EQ1 in *.
      rewrite close_open_ee__subst_ee; auto.
      assert (context C2) as Ctx1.
        apply contexting__context in Hcontexting; auto.
      rewrite close_open_ec__subst_ec; auto.
      assert (disjdom (union {{y}} (union (fv_ee x) (fv_te x))) (cv_ec C2)) as Disj'.
        eapply disjdom_app_l.
        split.
          apply disjdom_one_2; auto.
        eapply disjdom_app_l.
        split.
          apply disjdom_one_2; auto.
          simpl. apply disjdom_nil_1.
      rewrite <- subst_ee_plug; auto.
     apply dom_lenv_split in H2. rewrite H2 in xnL.
     apply typing_nonlin_renaming_permute with (x:=y); auto.
Qed.

Lemma contexting_typ_renaming_one : forall E1 E2 D T T' (X Y:atom) C E1' E2' D',
  contexting (E1++[(X,bind_kn)]++E2) D T C (E1'++[(X,bind_kn)]++E2') D' T' ->
  Y `notin` dom E1 `union` dom E2 `union` dom D  `union` dom E1' `union` dom E2' `union` dom D' `union` cv_ec C ->
  contexting (map (subst_tb X Y) E1 ++[(Y,bind_kn)]++E2) (map (subst_tlb X Y) D) (subst_tt X Y T) (subst_tc X Y C) (map (subst_tb X Y) E1' ++[(Y,bind_kn)]++E2') (map (subst_tlb X Y) D') (subst_tt X Y T').
Proof.
  intros E1 E2 D T T' X Y C E1' E2' D' Hcontexting yndom.
  remember (E1++[(X, bind_kn)]++E2) as E.
  remember (E1'++[(X, bind_kn)]++E2') as E'.
  generalize dependent E1.
  generalize dependent E2.
  generalize dependent E1'.
  generalize dependent E2'.
  generalize dependent X.
  (contexting_cases (induction Hcontexting) Case); intros; subst; simpl.
  Case "contexting_hole".
    assert (uniq (E1'++[(X,bind_kn)]++E2')) as Uniq. auto.
    apply mid_list_inv' in HeqE; auto.
    destruct HeqE as [J1 [J2 J3]]; subst.  
    inversion J3; subst.
    apply contexting_hole; simpl_env; auto.
      apply wf_lenv_typ_renaming_one with (X:=X); auto.
      apply wf_typ_typ_renaming_one' with (X:=X); auto.
  Case "contexting_abs_free".
    apply contexting_abs_free with (L:=L `union` {{Y}} `union` {{X}}); simpl_env; auto.
      apply wf_typ_typ_renaming_one' with (X:=X); auto.
        pick fresh z.
        assert (z `notin` L) as zn. auto.
        apply H0 in zn.
        apply contexting_regular in zn.
        decompose [and] zn.
        inversion H6; subst; auto.

      simpl in yndom. simpl_env in H0. simpl_env. auto.

      intros x0 x0n.
      assert (x0 `notin` L) as J. auto.
      apply H1 with (E1'0:=E1') (E2'0:=E2') (X0:=X) (E3:=E2) (E4:=E1) in J; auto.
        simpl_env.
        rewrite subst_tc_open_ec_var; auto.

        rewrite (@cv_ec_open_ec_rec C1 0 x0). simpl. simpl in yndom. auto.

  Case "contexting_abs_capture".
    assert (wf_lenv (E1'++[(X, bind_kn)]++E2') D') as Wfle.
      apply contexting_regular in Hcontexting.
      decompose [and] Hcontexting; auto.
    assert (J:=@lenv_remove_inv (E1'++[(X, bind_kn)]++E2') D' y (lbind_typ T1') Wfle H0).
    destruct J as [D1'0 [D2'0 [EQ1 EQ2]]]; subst.
    simpl_env.
    simpl_env in yndom. simpl in yndom.
    unfold close_ec in yndom.
    rewrite cv_ec_close_ec_rec in yndom.
    rewrite subst_tc_close_ec; auto.
      destruct (X == Y); subst.
        repeat (rewrite subst_tb_id).
        repeat (rewrite subst_tlb_id).
        repeat (rewrite subst_tt_id).
        repeat (rewrite subst_tc_id).
        apply contexting_abs_capture; simpl; auto.

        simpl_env in yndom.
        rewrite EQ1 in yndom.
        assert (uniq (D1'0 ++ [(y, lbind_typ T1')] ++ D2'0)) as UniqD. eauto.       
        assert (Y `notin` union (fv_lenv (D1'0 ++ [(y, lbind_typ T1')] ++ D2'0)) (fv_tt T1')) as YnD.
          apply notin_fv_wf with (X:=Y) in H; auto.
          apply notin_fv_lenv_wfle with (X:=Y) in Wfle; auto.
        rewrite map_lenv_remove; auto.
        apply contexting_abs_capture; simpl; auto.
          simpl_env.
          apply wf_typ_typ_renaming_one' with (X:=X); simpl_env; auto.
  
          rewrite cv_ec_subst_tc_rec.
          simpl_env in H1. simpl_env. simpl. 
          rewrite gdom_map. fsetdec.

          simpl_env in yndom.
          simpl_env.
          rewrite_env (map (subst_tlb X Y) (D1'0 ++ [(y, lbind_typ T1')] ++ D2'0)).
          apply IHHcontexting; auto.

  Case "contexting_app1".
    simpl_env.
    apply contexting_app1 with (D1':=map (subst_tlb X Y) D1') (D2':=map (subst_tlb X Y) D2') (T1':=subst_tt X Y T1'); auto.
      apply IHHcontexting; auto.
        apply dom_lenv_split in H0.
        rewrite H0 in yndom. auto.

      apply dom_lenv_split in H0. rewrite H0 in yndom.
      apply typing_typ_renaming_one with (X:=X); simpl_env; auto.

      apply lenv_split_typ_renaming_one with (X:=X); simpl_env; auto.

      apply disjdom_eq with (D1:=fv_ee e2).
        apply disjdom_sym_1.
        apply disjdom_eq with (D1:=dom D).
          apply disjdom_sym_1; auto.
          
          assert (J:=@dom_map lbinding lbinding (subst_tlb X Y) D).
          rewrite J. clear. fsetdec.
        rewrite subst_te_fv_ee_eq. clear. fsetdec.
  Case "contexting_app2".
    simpl_env.
    apply contexting_app2 with (D1':=map (subst_tlb X Y) D1') (D2':=map (subst_tlb X Y) D2') (T1':=subst_tt X Y T1'); auto.
      apply dom_lenv_split in H0. rewrite H0 in yndom.
      assert (typ_arrow (subst_tt X Y T1') (subst_tt X Y T2') = subst_tt X Y (typ_arrow T1' T2')) as EQ. auto.
      rewrite EQ.
      apply typing_typ_renaming_one with (X:=X); simpl_env; auto.

      apply IHHcontexting; auto.
        apply dom_lenv_split in H0.
        rewrite H0 in yndom. auto.

      apply lenv_split_typ_renaming_one with (X:=X); simpl_env; auto.

      apply disjdom_eq with (D1:=fv_ee e1).
        apply disjdom_sym_1.
        apply disjdom_eq with (D1:=dom D).
          apply disjdom_sym_1; auto.
          
          assert (J:=@dom_map lbinding lbinding (subst_tlb X Y) D).
          rewrite J. clear. fsetdec.
        rewrite subst_te_fv_ee_eq. clear. fsetdec.
  Case "contexting_tabs_free".
    apply contexting_tabs_free with (L:=L `union` {{Y}} `union` {{X}}); simpl_env; auto.
      simpl in yndom. simpl_env in H0. simpl_env. auto.

      intros X0 X0n.
      assert (X0 `notin` L) as J. auto.
      apply H0 with (E1'0:=[(X0, bind_kn)]++E1') (E2'0:=E2') (X1:=X) (E3:=E2) (E4:=E1) in J; auto.
        simpl_env.
        rewrite map_app in J.
        simpl in J. simpl_env in J.
        rewrite subst_tc_open_tc_var; auto.
        rewrite subst_tt_open_tt_var; auto.

        rewrite (@cv_ec_open_tc_rec C1 0 X0). simpl. simpl in yndom. auto.
  Case "contexting_tabs_capture".
    assert (wf_env E') as Wfe.
      apply contexting_regular in Hcontexting.
      decompose [and] Hcontexting; auto.
    assert (J:=@env_remove_inv E' Y0 (bind_kn) Wfe H).
    destruct J as [E1'0 [E2'0 [EQ1 EQ2]]]; subst.
    rewrite EQ1 in *.

    assert (uniq (E1'0++E2'0)) as Uniq.
      apply uniq_from_wf_env in Wfe.
       solve_uniq.
    apply app_mid_inv in HeqE'; auto.
    destruct HeqE' as [[F [fEQ1 fEQ2]] | [F [fEQ1 fEQ2]]]; subst.
      assert ((E1'++[(X, bind_kn)]++F)++[(Y0, bind_kn)]++E2'0 =
                        E1'++[(X, bind_kn)]++(F++[(Y0, bind_kn)]++E2'0)) as J. 
        simpl_env. auto.
      simpl in yndom. simpl_env in yndom. simpl_env. 
      unfold close_tc in yndom. rewrite cv_ec_close_tc_rec in yndom.
      apply IHHcontexting with (E3:=E2) (E4:=E1) in J; auto.
        assert (env_remove (Y0, bind_kn) (map (subst_tb X Y) E1'++[(Y, bind_kn)]++F++[(Y0, bind_kn)]++E2'0) 
                          = map (subst_tb X Y) E1'++[(Y, bind_kn)]++F++E2'0) as EQ.
          rewrite_env ((map (subst_tb X Y) E1'++[(Y, bind_kn)]++F)++[(Y0, bind_kn)]++E2'0).
          rewrite_env ((map (subst_tb X Y) E1'++[(Y, bind_kn)]++F)++E2'0).
          apply env_remove_opt.
            apply contexting_regular in J.
            decompose [and] J; auto.
            apply uniq_from_wf_env in H5.
            clear - H5.
            rewrite_env ((map (subst_tb X Y) E1'++[(Y, bind_kn)]++F)++[(Y0, bind_kn)]++E2'0) in H5.
            apply uniq_insert_mid; auto.     
              apply uniq_remove_mid in H5; auto.
              solve_uniq.
              solve_uniq.
        rewrite <- EQ.
        assert (X <> Y0) as XnY0.
          apply uniq_from_wf_env in Wfe.
          apply fresh_mid_head in Wfe.
          simpl_env in Wfe.
          auto.
        rewrite subst_tc_close_tc; auto.
        rewrite subst_tt_close_tt; auto.
          apply contexting_tabs_capture; auto.
            apply binds_weaken.
            apply binds_weaken.
            apply binds_app_3.
            apply binds_app_2. auto.

             rewrite cv_ec_subst_tc_rec. auto.

             rewrite EQ.
             simpl_env in H1.
             apply wf_lenv_typ_renaming_one with (X:=X); auto.

      assert (E1'0++[(Y0, bind_kn)]++F++[(X, bind_kn)]++E2' =
                        (E1'0++[(Y0, bind_kn)]++F)++[(X, bind_kn)]++E2') as J. 
        simpl_env. auto.
      simpl in yndom. simpl_env in yndom. simpl_env. 
      unfold close_tc in yndom. rewrite cv_ec_close_tc_rec in yndom.
      apply IHHcontexting with (E3:=E2) (E4:=E1) in J; auto.
        assert (env_remove (Y0, bind_kn) (map (subst_tb X Y)  E1'0++[(Y0, bind_kn)]++map (subst_tb X Y) F++[(Y, bind_kn)]++E2') 
                          = map (subst_tb X Y) E1'0++map (subst_tb X Y) F++[(Y, bind_kn)]++E2') as EQ.
          apply env_remove_opt.
            apply contexting_regular in J.
            decompose [and] J.
            apply uniq_from_wf_env in H5.
            clear - H5.
            rewrite map_app in H5.
            rewrite map_app in H5.
            simpl in H5. simpl_env in H5. auto.
        rewrite <- EQ.
        assert (X <> Y0) as XnY0.
          apply uniq_from_wf_env in Wfe.
          apply fresh_mid_tail in Wfe.
          simpl_env in Wfe.
          auto.
        rewrite subst_tc_close_tc; auto.
        rewrite subst_tt_close_tt; auto.
          simpl_env in J.
          apply contexting_tabs_capture; auto.
            rewrite cv_ec_subst_tc_rec. auto.

            rewrite EQ.
            rewrite_env (map (subst_tb X Y) (E1'0++F)++[(Y, bind_kn)]++E2').
            apply wf_lenv_typ_renaming_one with (X:=X); simpl_env; auto.

  Case "contexting_tapp".
    simpl_env.
    rewrite subst_tt_open_tt; auto.
    apply contexting_tapp; auto.
      assert (subst_tt X Y (typ_all T2') = typ_all (subst_tt X Y T2')) as EQ. auto.
      rewrite <- EQ.
      auto.

      apply wf_typ_typ_renaming_one' with (X:=X); simpl_env; auto.
        apply contexting_regular in Hcontexting. 
        decompose [and] Hcontexting; auto.

  Case "contexting_bang".
    simpl_env.
    apply contexting_bang.
      apply IHHcontexting; auto.

  Case "contexting_let1".
    simpl_env.
    apply contexting_let1 with (L:=L `union` {{Y}}) (D1':=map (subst_tlb X Y) D1') (D2':=map (subst_tlb X Y) D2') (T1':=subst_tt X Y T1'); auto.
      apply IHHcontexting; auto.
        apply dom_lenv_split in H0.
        rewrite H0 in yndom. auto.

      intros x xn.
      assert (x `notin` L) as xnL. auto.
      apply H in xnL.
      apply dom_lenv_split in H0. rewrite H0 in yndom.
      rewrite subst_te_open_ee_var; auto.
      rewrite_env (([(x, bind_typ T1')]++E1')++[(X,bind_kn)]++E2') in xnL.
      apply typing_typ_renaming_one with (Y:=Y) in xnL; simpl_env; auto.

      apply lenv_split_typ_renaming_one with (X:=X); simpl_env; auto.

      apply disjdom_eq with (D1:=fv_ee e2).
        apply disjdom_sym_1.
        apply disjdom_eq with (D1:=dom D).
          apply disjdom_sym_1; auto.
          
          assert (J:=@dom_map lbinding lbinding (subst_tlb X Y) D).
          rewrite J. clear. fsetdec.
        rewrite subst_te_fv_ee_eq. clear. fsetdec.

  Case "contexting_let2_free".
    simpl_env.
    apply contexting_let2_free with (L:=L `union` {{Y}} `union` {{X}})(D1':=map (subst_tlb X Y) D1') (D2':=map (subst_tlb X Y) D2') (T1':=subst_tt X Y T1'); auto.
      assert (subst_tt X Y (typ_bang T1') = typ_bang (subst_tt X Y T1')) as EQ. auto.
      rewrite <- EQ.
      apply typing_typ_renaming_one with (X:=X); auto.
        apply dom_lenv_split in H2.
        rewrite H2 in yndom. simpl in yndom. simpl_env. auto.

      intros x0 x0n.
      assert (x0 `notin` L) as J. auto.
      rewrite subst_tc_open_ec_var; auto.
      apply H1 with (E1'0:=[(x0, bind_typ T1')]++E1') (E2'0:=E2') (X0:=X) (E3:=E2) (E4:=E1) in J; auto.
        apply dom_lenv_split in H2.
        rewrite H2 in yndom. simpl in yndom. 
        rewrite (@cv_ec_open_ec_rec C2 0 x0). simpl. auto.

      apply lenv_split_typ_renaming_one with (X:=X); simpl_env; auto.

      apply disjdom_eq with (D1:=fv_ee e1).
        apply disjdom_sym_1.
        apply disjdom_eq with (D1:=dom D).
          apply disjdom_sym_1; auto.
          
          assert (J:=@dom_map lbinding lbinding (subst_tlb X Y) D).
          rewrite J. clear. fsetdec.
        rewrite subst_te_fv_ee_eq. clear. fsetdec.

  Case "contexting_let2_capture".
    assert (wf_env E') as Wfe.
      apply contexting_regular in Hcontexting.
      decompose [and] Hcontexting; auto.
    assert (J:=@env_remove_inv E' y (bind_typ T1') Wfe H0).
    destruct J as [E1'0 [E2'0 [EQ1 EQ2]]]; subst.
    rewrite EQ1 in *.

    assert (uniq (E1'0++E2'0)) as Uniq.
      apply uniq_from_wf_env in Wfe.
       solve_uniq.
    apply app_mid_inv in HeqE'; auto.
    destruct HeqE' as [[F [fEQ1 fEQ2]] | [F [fEQ1 fEQ2]]]; subst.
      assert ((E1'++[(X, bind_kn)]++F)++[(y, bind_typ T1')]++E2'0 =
                        E1'++[(X, bind_kn)]++(F++[(y, bind_typ T1')]++E2'0)) as J. 
        simpl_env. auto.
      simpl in yndom. simpl_env in yndom. simpl_env. 
      unfold close_ec in yndom. rewrite cv_ec_close_ec_rec in yndom.
      apply IHHcontexting with (E3:=E2) (E4:=E1) in J; auto.
        assert (env_remove (y, bind_typ (subst_tt X Y T1')) (map (subst_tb X Y) E1'++[(Y, bind_kn)]++F++[(y, bind_typ (subst_tt X Y T1'))]++E2'0) 
                          = map (subst_tb X Y) E1'++[(Y, bind_kn)]++F++E2'0) as EQ.
          rewrite_env ((map (subst_tb X Y) E1'++[(Y, bind_kn)]++F)++[(y, bind_typ (subst_tt X Y T1'))]++E2'0).
          rewrite_env ((map (subst_tb X Y) E1'++[(Y, bind_kn)]++F)++E2'0).
          apply env_remove_opt.
            apply contexting_regular in J.
            decompose [and] J; auto.
            apply uniq_from_wf_env in H7.
            clear H3 H5 H6 H8 H10 J Uniq EQ1 Wfe IHHcontexting H0 H yndom H1.
            rewrite_env ((map (subst_tb X Y) E1'++[(Y, bind_kn)]++F)++[(y, bind_typ T1')]++E2'0) in H7.
            apply uniq_insert_mid; auto.     
              apply uniq_remove_mid in H7; auto.
              solve_uniq.
              solve_uniq.
        rewrite <- EQ.
        rewrite subst_tc_close_ec; auto.
          apply contexting_let2_capture with (D1':=map (subst_tlb X Y) D1') (D2':=map (subst_tlb X Y) D2') (T1':=subst_tt X Y T1'); auto.
            rewrite EQ.
            assert (subst_tt X Y (typ_bang T1') = typ_bang (subst_tt X Y T1')) as EQ'. auto.
            rewrite <- EQ'.
            simpl_env in H.
            apply typing_typ_renaming_one with (X:=X); auto.
              apply dom_lenv_split in H2.
              rewrite H2 in yndom. simpl in yndom. simpl_env. auto.

            apply binds_weaken.
            apply binds_weaken.
            apply binds_app_3.
            apply binds_app_2. auto.

            rewrite cv_ec_subst_tc_rec. auto.

            rewrite <- subst_tt_fresh with (T:=T1'); auto.
              apply notin_fv_wf with (E:=E2'0); auto.
                apply wf_env_strengthening_tail in Wfe.
                inversion Wfe; subst; auto.

                apply uniq_from_wf_env in Wfe.
                clear EQ1 Uniq J EQ IHHcontexting Hcontexting H0 yndom.
                solve_uniq.

           rewrite EQ. simpl_env in H2.       
           apply lenv_split_typ_renaming_one with (X:=X); simpl_env; auto.

           apply disjdom_eq with (D1:=fv_ee e1).
             apply disjdom_sym_1.
             apply disjdom_eq with (D1:=dom D).
               apply disjdom_sym_1; auto.
          
               assert (JJ:=@dom_map lbinding lbinding (subst_tlb X Y) D).
               rewrite JJ. clear. fsetdec.
             rewrite subst_te_fv_ee_eq. clear. fsetdec.

         apply dom_lenv_split in H2.
         rewrite H2 in yndom. simpl in H0. simpl in yndom. simpl_env. auto.

      assert (E1'0++[(y, bind_typ T1')]++F++[(X, bind_kn)]++E2' =
                        (E1'0++[(y, bind_typ T1')]++F)++[(X, bind_kn)]++E2') as J. 
        simpl_env. auto.
      simpl in yndom. simpl_env in yndom. simpl_env. 
      unfold close_ec in yndom. rewrite cv_ec_close_ec_rec in yndom.
      apply IHHcontexting with (E3:=E2) (E4:=E1) in J; auto.
        assert (env_remove (y, bind_typ (subst_tt X Y T1')) (map (subst_tb X Y)  E1'0++[(y, bind_typ (subst_tt X Y T1'))]++map (subst_tb X Y) F++[(Y, bind_kn)]++E2') 
                          = map (subst_tb X Y) E1'0++map (subst_tb X Y) F++[(Y, bind_kn)]++E2') as EQ.
          apply env_remove_opt.
            apply contexting_regular in J.
            decompose [and] J.
            apply uniq_from_wf_env in H7.
            clear H3 H5 H6 H8 H10 J Uniq EQ1 Wfe IHHcontexting H0 H yndom H1.
            rewrite map_app in H7.
            rewrite map_app in H7.
            simpl in H7. simpl_env in H7. auto.
        rewrite <- EQ.
        rewrite subst_tc_close_ec; auto.
          simpl_env in J.
          apply contexting_let2_capture with (D1':=map (subst_tlb X Y) D1') (D2':=map (subst_tlb X Y) D2') (T1':=subst_tt X Y T1'); auto.
            rewrite EQ.
            assert (subst_tt X Y (typ_bang T1') = typ_bang (subst_tt X Y T1')) as EQ'. auto.
            rewrite <- EQ'.
            rewrite_env ((map (subst_tb X Y) (E1'0 ++ F))++[(Y, bind_kn)]++E2').
            apply typing_typ_renaming_one with (X:=X); auto.
              apply dom_lenv_split in H2.
              rewrite H2 in yndom. simpl in yndom. simpl_env. auto.

            apply dom_lenv_split in H2.
            rewrite H2 in yndom. simpl in H0. simpl in yndom. simpl_env. auto.

            rewrite cv_ec_subst_tc_rec. auto.

           rewrite EQ. simpl_env in H2.       
           rewrite_env ((map (subst_tb X Y) (E1'0 ++ F))++[(Y, bind_kn)]++E2').
           apply lenv_split_typ_renaming_one with (X:=X); simpl_env; auto.

           apply disjdom_eq with (D1:=fv_ee e1).
             apply disjdom_sym_1.
             apply disjdom_eq with (D1:=dom D).
               apply disjdom_sym_1; auto.
          
               assert (JJ:=@dom_map lbinding lbinding (subst_tlb X Y) D).
               rewrite JJ. clear. fsetdec.
             rewrite subst_te_fv_ee_eq. clear. fsetdec.

         apply dom_lenv_split in H2.
         rewrite H2 in yndom. simpl in H0. simpl in yndom. simpl_env. auto.

  Case "contexting_apair1".
    simpl_env.
    apply contexting_apair1 with (T1':=subst_tt X Y T1'); auto.
      apply typing_typ_renaming_one with (X:=X); simpl_env; auto.
  Case "contexting_apair2".
    simpl_env.
    apply contexting_apair2 with (T1':=subst_tt X Y T1'); auto.
      apply typing_typ_renaming_one with (X:=X); simpl_env; auto.
  Case "contexting_fst".
    simpl_env.
    apply contexting_fst with (T2':=subst_tt X Y T2'); auto.
      assert (subst_tt X Y (typ_with T1' T2') = typ_with (subst_tt X Y T1') (subst_tt X Y T2')) as EQ. auto.
      rewrite <- EQ.
      auto.
  Case "contexting_snd".
    simpl_env.
    apply contexting_snd with (T1':=subst_tt X Y T1'); auto.
      assert (subst_tt X Y (typ_with T1' T2') = typ_with (subst_tt X Y T1') (subst_tt X Y T2')) as EQ. auto.
      rewrite <- EQ.
      auto.
Qed.

Export Parametricity.

Definition F_logical_related E lE e e' t : Prop :=
  typing E lE e t /\
  typing E lE e' t /\
  forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
   F_related_subst E lE gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
   F_Rsubst E rsubst dsubst dsubst'->
   F_related_terms t rsubst dsubst dsubst'
                                 (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
                                 (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e'))).

Lemma F_logical_related_congruence__abs_free :
  forall e e' E D T,
  typing E D e T ->
  typing E D e' T ->
  (forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
   F_related_subst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
   F_Rsubst E rsubst dsubst dsubst' ->
   F_related_terms T rsubst dsubst dsubst' 
     (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
     (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e')))
  ) ->
  forall L T1' C1 T2' E' D',
  wf_typ E' T1' ->
  (forall x,
    x `notin` L ->
    contexting E D T (open_ec C1 x) E' ((x, lbind_typ T1')::D') T2'
  ) ->
  (forall x,
    x `notin` L ->
   typing E D e T ->
   typing E D e' T ->
    (forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
     F_related_subst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
     F_Rsubst E rsubst dsubst dsubst' ->
     F_related_terms T rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e')))
    ) ->
   forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
     F_related_subst E' ((x, lbind_typ T1')::D') gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
     F_Rsubst E' rsubst dsubst dsubst' ->
     F_related_terms T2' rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (plug (open_ec C1 x) e))))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (plug (open_ec C1 x) e'))))
  ) ->
  forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
  F_related_subst E' D' gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
  F_Rsubst E' rsubst dsubst dsubst' ->
  F_related_terms (typ_arrow T1' T2') rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_abs T1' (plug C1 (shift_ee e))))))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_abs T1' (plug C1 (shift_ee e')))))).
Proof.
    intros e e' E D T Htyp Htyp' Hlr L T1' C1 T2' E' D' H H0 H1 dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Hrel_sub HRsub.
    assert (J:=Hrel_sub). apply F_related_subst__inversion in J. 
    destruct J as [[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe].

    rename H into WFTV.

    assert (value (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_abs T1' (plug C1 (shift_ee e))))))) as Value.
      apply delta_gamma_lgamma_subst_value with (E:=E') (D:=D'); auto.
        apply FrTyping__labsvalue with (L:=L `union` cv_ec C1) (E:=E') (D:=D') (T1:=T2'); auto.
          intros x xn.
          assert (x `notin` L) as xnFv. auto.
          apply H0 in xnFv.
          apply contexting_plug_typing with (e:=e) in xnFv; auto.
          simpl_env in xnFv.
          rewrite open_ee_expr with (e:=e) (u:=x) in xnFv; auto.
          assert (disjdom (fv_ee x `union` fv_te x) (cv_ec C1)) as Disj.
            eapply disjdom_app_l.
            split.
              apply disjdom_one_2; auto.
              simpl. apply disjdom_nil_1.
          rewrite <- open_ee_plug in xnFv; auto. 
          rewrite shift_ee_expr with (e:=e) in xnFv; auto.
    assert (value (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_abs T1' (plug C1 (shift_ee e'))))))) as Value'.
      apply delta_gamma_lgamma_subst_value with (E:=E') (D:=D'); auto.
        apply FrTyping__labsvalue with (L:=L  `union` cv_ec C1) (E:=E') (D:=D') (T1:=T2'); auto.
          intros x xn.
          assert (x `notin` L) as xnFv. auto.
          apply H0 in xnFv.
          apply contexting_plug_typing with (e:=e') in xnFv; auto.
          simpl_env in xnFv.
          rewrite open_ee_expr with (e:=e') (u:=x) in xnFv; auto.
          assert (disjdom (fv_ee x `union` fv_te x) (cv_ec C1)) as Disj.
            eapply disjdom_app_l.
            split.
              apply disjdom_one_2; auto.
              simpl. apply disjdom_nil_1.
          rewrite <- open_ee_plug in xnFv; auto. 
          rewrite shift_ee_expr with (e:=e') in xnFv; auto.
    
    exists (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_abs T1' (plug C1 (shift_ee e)))))).
    exists (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_abs T1' (plug C1 (shift_ee e')))))).
    split.
      assert (typing E' D' (plug (ctx_abs_free T1' C1) e) (typ_arrow T1' T2')) as Hptyp.
        apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.
           apply contexting_abs_free with (L:=L); auto.
      apply typing_subst with (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst) in Hptyp; auto.
    split.
      assert (typing E' D' (plug (ctx_abs_free T1' C1) e') (typ_arrow T1' T2')) as Hptyp'.
        apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.
           apply contexting_abs_free with (L:=L); auto.
      apply typing_subst with (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst') in Hptyp'; auto.
    split. split; auto.
    split. split; auto.
      SCase "Frel".
      apply F_related_values_arrow_req.
      split; auto.
      split; auto.
      SSCase "arrow".
        intros x x' Htyping Htyping' Harrow_left.
        destruct Harrow_left as [w [w' [Hxw [Hx'w' Harrow_left]]]].
        pick fresh z.
        assert (z `notin` L) as Fry. auto.
        assert (wf_typ E' T2') as WFT'. 
          apply H0 in Fry.
          apply contexting_regular in Fry.
          decompose [and] Fry; auto.
        assert (F_related_subst E' ([(z, lbind_typ T1')]++D') gsubst gsubst' ([(z,x)]++lgsubst) ([(z,x')]++lgsubst') rsubst dsubst dsubst') as Hrel_sub'.        
          apply F_related_subst_ltyp; auto.
            exists w. exists w'. repeat (split; auto).
        apply H1 with (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=[(z,x)]++lgsubst) (dsubst':=dsubst') (gsubst':=gsubst') (lgsubst':=[(z,x')]++lgsubst') (rsubst:=rsubst) in Fry; auto.
        simpl_env in Fry.
        assert (
            apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst ([(z,x)]++lgsubst) (plug (open_ec C1 z) e))) =
            apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (subst_ee z x (plug (open_ec C1 z) e))))
                  ) as Heq1. simpl. reflexivity.
         assert (
            apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst ([(z,x')]++lgsubst') (plug (open_ec C1 z) e'))) =
            apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (subst_ee z x' (plug (open_ec C1 z) e'))))
                  ) as Heq2.  simpl. reflexivity.
         rewrite Heq1 in Fry. rewrite Heq2 in Fry. clear Heq1 Heq2.
         destruct Fry as [v [v' [Ht [Ht' [[Hbrc Hv] [[Hbrc' Hv'] Hrel]]]]]].
         exists (v). exists (v').
         split.
           SSSCase "norm".
           split; auto.
           apply bigstep_red_trans with (e':=(apply_delta_subst dsubst (apply_gamma_subst gsubst  (apply_gamma_subst lgsubst (subst_ee z x (plug (open_ec C1 z) e)))))); auto.
              rewrite <- shift_ee_expr; auto.
             assert (plug (open_ec C1 z) e = open_ee (plug C1 e) z) as EQ.
              assert (disjdom (fv_ee z `union` fv_te z) (cv_ec C1)) as Disj.
                eapply disjdom_app_l.
                split.
                  apply disjdom_one_2; auto.
                  simpl. apply disjdom_nil_1.
               rewrite open_ee_plug; auto.
               rewrite <- open_ee_expr; auto.
             rewrite EQ.
             eapply m_red_labs_subst with (T1:=T2') (L:=L `union` cv_ec C1); eauto.
               apply F_related_values_inversion in Harrow_left.
               decompose [prod] Harrow_left; auto.

               assert (typing E' D' (plug (ctx_abs_free T1' C1) e) (typ_arrow T1' T2')) as Hptyp.
                 apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.
                   apply contexting_abs_free with (L:=L); auto.
               apply notin_fv_ee_typing with (y:=z) in Hptyp; auto.
               simpl in Hptyp.
               rewrite <- shift_ee_expr in Hptyp; auto.

               intros x0 x0dom.
               assert (x0 `notin` L) as x0n. auto.
               apply H0 in x0n.
               assert (disjdom (fv_ee x0 `union` fv_te x0) (cv_ec C1)) as Disj.
                 eapply disjdom_app_l.
                 split.
                   apply disjdom_one_2; auto.
                   simpl. apply disjdom_nil_1.
               rewrite open_ee_plug; auto.
               rewrite <- open_ee_expr; auto.
               apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.       
         split; auto.
           SSSCase "norm".
           split; auto.
           apply bigstep_red_trans with (e':=(apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (subst_ee z x' (plug (open_ec C1 z) e')))))); auto.
              rewrite <- shift_ee_expr; auto.
             assert (plug (open_ec C1 z) e' = open_ee (plug C1 e') z) as EQ.
               assert (disjdom (fv_ee z `union` fv_te z) (cv_ec C1)) as Disj.
                 eapply disjdom_app_l.
                 split.
                   apply disjdom_one_2; auto.
                   simpl. apply disjdom_nil_1.
               rewrite open_ee_plug; auto.
               rewrite <- open_ee_expr; auto.
             rewrite EQ.
             eapply m_red_labs_subst with (T1:=T2') (L:=L`union` cv_ec C1); eauto.
               apply F_related_values_inversion in Harrow_left.
               decompose [prod] Harrow_left; auto.

               assert (typing E' D' (plug (ctx_abs_free T1' C1) e') (typ_arrow T1' T2')) as Hptyp.
                 apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.
                   apply contexting_abs_free with (L:=L); auto.
               apply notin_fv_ee_typing with (y:=z) in Hptyp; auto.
               simpl in Hptyp.
               rewrite <- shift_ee_expr in Hptyp; auto.

               intros x0 x0dom.
               assert (x0 `notin` L) as x0n. auto.
               apply H0 in x0n.
               assert (disjdom (fv_ee x0 `union` fv_te x0) (cv_ec C1)) as Disj.
                 eapply disjdom_app_l.
                 split.
                   apply disjdom_one_2; auto.
                   simpl. apply disjdom_nil_1.
             rewrite open_ee_plug; auto.
               rewrite <- open_ee_expr; auto.
               apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.       
Qed.

Lemma F_logical_related_congruence__abs_capture :
  forall e e' E D T,
  typing E D e T ->
  typing E D e' T ->
  (forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
   F_related_subst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
   F_Rsubst E rsubst dsubst dsubst' ->
   F_related_terms T rsubst dsubst dsubst' 
     (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
     (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e')))
  ) ->
  forall y T1' C1 T2' E' D',
  wf_typ E' T1' ->
  binds y (lbind_typ T1') D' ->
  y `notin` gdom_env E `union` cv_ec C1 ->
  contexting E D T C1 E' D' T2' ->
  (typing E D e T ->
   typing E D e' T ->
    (forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
     F_related_subst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
     F_Rsubst E rsubst dsubst dsubst' ->
     F_related_terms T rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e')))
    ) ->
   forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
     F_related_subst E' D' gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
     F_Rsubst E' rsubst dsubst dsubst' ->
     F_related_terms T2' rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (plug C1 e))))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (plug C1 e'))))
  ) ->
  forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
  F_related_subst E' (lenv_remove (y, lbind_typ T1') D') gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
  F_Rsubst E' rsubst dsubst dsubst' ->
  F_related_terms (typ_arrow T1' T2') rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_abs T1' (plug (close_ec C1 y) (close_ee (shift_ee e) y))))))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_abs T1' (plug (close_ec C1 y) (close_ee (shift_ee e') y)))))).
Proof.
    intros e e' E D T Htyp Htyp' Hlr y T1' C1 T2' E' D' H H0 H1 Hcontexting IHHcontexting dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Hrel_sub HRsub.  
    assert (J:=Hrel_sub). apply F_related_subst__inversion in J. 
    destruct J as [[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe].

    rename H into WFTV.
    
    assert (wf_typ E' T2') as WFT'. 
      apply contexting_regular in Hcontexting.
      decompose [and] Hcontexting; auto.
    assert (Fry := @IHHcontexting Htyp Htyp' Hlr).
    assert (wf_lenv E' D') as Wfle'.
      apply contexting_regular in Hcontexting.
      decompose [and] Hcontexting; auto.
    assert (EQ1:=@lenv_remove_inv E' D' y (lbind_typ T1')  Wfle' H0).
    destruct EQ1 as [D1' [D2' [EQ1' EQ2']]]; subst.
    rewrite EQ1' in *.

    assert (EQ:=Hwflg).
    apply wf_lgsubst_lapp_inv in EQ.
    destruct EQ as [lgsubst1 [lgsubst2 [gEQ1 [gEQ2 gEQ3]]]]; subst.

    assert (EQ:=Hwflg').
    apply wf_lgsubst_lapp_inv in EQ.
    destruct EQ as [lgsubst1' [lgsubst2' [gEQ1' [gEQ2' gEQ3']]]]; subst.
       
    assert (value (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst (lgsubst1++lgsubst2) (exp_abs T1' (plug (close_ec C1 y) (close_ee (shift_ee e) y))))))) as Value.
      apply delta_gamma_lgamma_subst_value with (E:=E') (D:=D1'++D2'); auto.
        apply FrTyping__labsvalue with (L:=dom E' `union` dom (D1'++D2') `union` cv_ec (close_ec C1 y) `union` cv_ec C1) (D:=D1'++D2') (E:=E') (T1:=T2'); auto.
          intros x xnFv.
          rewrite <- shift_ee_expr with (e:=e); auto.
          assert (disjdom (fv_ee x `union` fv_te x) (cv_ec (close_ec C1 y))) as Disj.
            eapply disjdom_app_l.
            split.
              apply disjdom_one_2; auto.
              simpl. apply disjdom_nil_1.
          rewrite open_ee_plug; auto. 
          rewrite <- EQ1'.
          rewrite close_open_ee__subst_ee; auto.
          assert (context C1) as Ctx1.
            apply contexting__context in Hcontexting; auto.
          rewrite close_open_ec__subst_ec; auto.
          assert (disjdom (union {{y}} (fv_ee x `union` fv_te x)) (cv_ec C1)) as Disj'.
             eapply disjdom_app_l.
             split.
               apply disjdom_one_2; auto.
             eapply disjdom_app_l.
             split.
               apply disjdom_one_2; auto.
               simpl. apply disjdom_nil_1.
          rewrite <- subst_ee_plug; auto. 
          assert (typing E' (D1'++[(y, lbind_typ T1')]++D2') (plug C1 e) T2') as Htyp2.
            apply contexting_plug_typing with (e:=e) in Hcontexting; auto.
              rewrite EQ1'. auto.
         apply typing_lin_renaming_permute with (x:=y); auto.
    assert (value (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst (lgsubst1'++lgsubst2') (exp_abs T1' (plug (close_ec C1 y)  (close_ee (shift_ee e') y))))))) as Value'.
      apply delta_gamma_lgamma_subst_value with (E:=E') (D:=D1'++D2'); auto.
        apply FrTyping__labsvalue with (L:=dom E' `union` dom (D1'++D2') `union` cv_ec (close_ec C1 y) `union` cv_ec C1) (D:=D1'++D2') (E:=E') (T1:=T2'); auto.
          intros x xnFv.
          rewrite <- shift_ee_expr with (e:=e'); auto.
          assert (disjdom (fv_ee x `union` fv_te x) (cv_ec (close_ec C1 y))) as Disj.
            eapply disjdom_app_l.
            split.
              apply disjdom_one_2; auto.
              simpl. apply disjdom_nil_1.
          rewrite open_ee_plug; auto. 
          rewrite <- EQ1'.
          rewrite close_open_ee__subst_ee; auto.
          assert (context C1) as Ctx1.
            apply contexting__context in Hcontexting; auto.
          rewrite close_open_ec__subst_ec; auto.
          assert (disjdom (union {{y}} (fv_ee x `union` fv_te x)) (cv_ec C1)) as Disj'.
            eapply disjdom_app_l.
            split.
              apply disjdom_one_2; auto.
            eapply disjdom_app_l.
            split.
              apply disjdom_one_2; auto.
              simpl. apply disjdom_nil_1.
          rewrite <- subst_ee_plug; auto. 
          assert (typing E' (D1'++[(y, lbind_typ T1')]++D2') (plug C1 e') T2') as Htyp2'.
            apply contexting_plug_typing with (e:=e') in Hcontexting; auto.
              rewrite EQ1'. auto.
         apply typing_lin_renaming_permute with (x:=y); auto.
    exists (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst (lgsubst1++lgsubst2) (exp_abs T1' (plug (close_ec C1 y) (close_ee (shift_ee e) y)))))).
    exists (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst (lgsubst1'++lgsubst2') (exp_abs T1' (plug (close_ec C1 y) (close_ee (shift_ee e') y)))))).
    split. 
      assert (typing E' (D1'++D2') (plug (ctx_abs_capture y T1' (close_ec C1 y)) e) (typ_arrow T1' T2')) as Hptyp.
        destruct (in_dec y (fv_ee e)) as [yine | ynine].
          simpl.
          apply typing_abs with (L:=dom (D1'++D2') `union` dom E' `union` dom E `union` dom D `union` cv_ec C1 `union` cv_ec (close_ec C1 y)); auto.
            intros x xn.
            rewrite <- shift_ee_expr; auto.
            assert (disjdom (fv_ee x `union` fv_te x) (cv_ec (close_ec C1 y))) as Disj.
              eapply disjdom_app_l.
              split.
                apply disjdom_one_2; auto.
                simpl. apply disjdom_nil_1.
            rewrite open_ee_plug; auto.
            assert (y `in` gdom_env E \/ y `in` dom D) as yED.
              assert (y `in` gdom_env E `union` dom D) as J.
                apply in_fv_ee_typing' with (x:=y) in Htyp; auto.
              fsetdec.
            rewrite close_open_ee__subst_ee; auto.
            assert (context C1) as Ctx1.
              apply contexting__context in Hcontexting; auto.
            rewrite close_open_ec__subst_ec; auto.
            destruct yED as [yE | yD].
              contradict H1; auto.

              apply binds_In_inv in yD.
              destruct yD as [b Binds]. destruct b.
              assert (wf_lenv E D) as Wfle. auto.
              assert (J:=@lenv_remove_inv E D y (lbind_typ t) Wfle Binds).
              destruct J as [D1 [D2 [dEQ1 dEQ2]]]; subst.
              apply typing_lin_permute.
              simpl_env in xn.
              apply contexting_plug_typing with (E:=E) (D:=D1++[(x, lbind_typ t)]++D2) (T:=T); auto.
                apply contexting_lin_renaming_one; auto.

                apply typing_lin_renaming_one with (x:=y); auto.

          rewrite <- EQ1'.
          apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.
            apply contexting_abs_capture; auto.
      apply typing_subst with (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst1++lgsubst2) in Hptyp; auto.
    split.
      assert (typing E' (D1'++D2') (plug (ctx_abs_capture y T1' (close_ec C1 y)) e') (typ_arrow T1' T2')) as Hptyp'.
        destruct (in_dec y (fv_ee e')) as [yine' | ynine'].
          simpl.
          apply typing_abs with (L:=dom (D1'++D2') `union` dom E' `union` dom D `union` dom E `union` cv_ec C1 `union` cv_ec (close_ec C1 y)); auto.
            intros x xn.
            rewrite <- shift_ee_expr; auto.
            assert (disjdom (fv_ee x `union` fv_te x) (cv_ec (close_ec C1 y))) as Disj.
              eapply disjdom_app_l.
              split.
                apply disjdom_one_2; auto.
                simpl. apply disjdom_nil_1.
            rewrite open_ee_plug; auto.
            assert (y `in` gdom_env E \/ y `in` dom D) as yED.
              assert (y `in` gdom_env E `union` dom D) as J.
                apply in_fv_ee_typing' with (x:=y) in Htyp'; auto.
              fsetdec.
            rewrite close_open_ee__subst_ee; auto.
            assert (context C1) as Ctx1.
              apply contexting__context in Hcontexting; auto.
            rewrite close_open_ec__subst_ec; auto.
            destruct yED as [yE | yD].
              contradict H1; auto.

              apply binds_In_inv in yD.
              destruct yD as [b Binds]. destruct b.
              assert (wf_lenv E D) as Wfle. auto.
              assert (J:=@lenv_remove_inv E D y (lbind_typ t) Wfle Binds).
              destruct J as [D1 [D2 [dEQ1 dEQ2]]]; subst.
              apply typing_lin_permute.
              simpl_env in xn.
              apply contexting_plug_typing with (E:=E) (D:=D1++[(x, lbind_typ t)]++D2) (T:=T); auto.
                apply contexting_lin_renaming_one; auto.

                apply typing_lin_renaming_one with (x:=y); auto.
          rewrite <- EQ1'.
          apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.
            apply contexting_abs_capture; auto.
      apply typing_subst with (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst1'++lgsubst2') in Hptyp'; auto.
    split. split; auto.
    split. split; auto.
      SCase "Frel".
      apply F_related_values_arrow_req.
      split; auto.
      split; auto.
      SSCase "arrow".
        intros x x' Htyping Htyping' Harrow_left.
        destruct Harrow_left as [w [w' [Hxw [Hx'w' Harrow_left]]]].

        assert (F_related_subst E' (D1'++[(y, lbind_typ T1')]++D2') gsubst gsubst' (lgsubst1++[(y,x)]++lgsubst2) (lgsubst1'++[(y,x')]++lgsubst2') rsubst dsubst dsubst') as Hrel_sub'.        
          apply F_related_subst_lgweaken; auto.
             assert (y `notin` dom D1') as ynD1'.
                apply fresh_mid_head with (E:=D2') (a:=lbind_typ T1'); auto.
                  apply contexting_regular in Hcontexting.
                  decompose [and] Hcontexting. eauto.
             assert (y `notin` dom D2') as ynD2'.
                apply fresh_mid_tail with (F:=D1') (a:=lbind_typ T1'); auto.
                  apply contexting_regular in Hcontexting.
                  decompose [and] Hcontexting. eauto.
             assert (y `notin` dom E') as ynE'.
               apply contexting_regular in Hcontexting.
               decompose [and] Hcontexting.
              apply wf_lenv_notin_dom with (x:=y) (T:=T1') in H5; auto.
             auto.

             exists w. exists w'. repeat (split; auto).
        assert (J:=@Fry dsubst dsubst' gsubst gsubst' (lgsubst1++[(y,x)]++lgsubst2) (lgsubst1'++[(y,x')]++lgsubst2') rsubst Hrel_sub' HRsub).
        assert (
            apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst (lgsubst1++[(y,x)]++lgsubst2) (plug C1 e))) =
            apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst (lgsubst1++lgsubst2) (subst_ee y x (plug C1 e))))
                  ) as Heq1.
           simpl_env.
           rewrite lgamma_subst_opt with (D':=D1') (D:=D2') (E:=E') (dsubst:=dsubst) (t:=T1') (gsubst:=gsubst); auto.
             apply F_related_subst__inversion in Hrel_sub'.
             decompose [prod] Hrel_sub'; auto.
         assert (
            apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst  (lgsubst1'++[(y,x')]++lgsubst2') (plug C1 e'))) =
            apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst  (lgsubst1'++lgsubst2') (subst_ee y x' (plug C1 e'))))
                  ) as Heq2.
           simpl_env.
           rewrite lgamma_subst_opt with (D':=D1') (D:=D2') (E:=E') (dsubst:=dsubst') (t:=T1') (gsubst:=gsubst'); auto.
             apply F_related_subst__inversion in Hrel_sub'.
             decompose [prod] Hrel_sub'; auto.
         rewrite Heq1 in J. rewrite Heq2 in J. clear Heq1 Heq2.
         destruct J as [v [v' [Ht [Ht' [[Hbrc Hv] [[Hbrc' Hv'] Hrel]]]]]].
         exists (v). exists (v').
         split.
           SSSCase "norm".
           split; auto.
           apply bigstep_red_trans with (e':=(apply_delta_subst dsubst (apply_gamma_subst gsubst  (apply_gamma_subst (lgsubst1++lgsubst2) (subst_ee y x (plug C1 e)))))); auto.
              assert (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst (lgsubst1++lgsubst2) x)) =x) as Heq1.
                 rewrite gamma_subst_closed_exp with (t:= apply_delta_subst_typ dsubst T1'); auto.
                 rewrite gamma_subst_closed_exp with (t:= apply_delta_subst_typ dsubst T1'); auto.
                 rewrite delta_subst_closed_exp with (t:= apply_delta_subst_typ dsubst T1'); auto.
                 rewrite gamma_subst_closed_exp with (t:= apply_delta_subst_typ dsubst T1'); auto.
              rewrite <- Heq1.
              rewrite commut_gamma_subst_abs.
              rewrite commut_gamma_subst_abs.
              assert (subst_ee y (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst (lgsubst1++lgsubst2) x))) (plug C1 e) = subst_ee y x (plug C1 e)) as Heq2. 
                 rewrite Heq1. auto. 
              rewrite Heq2.
              assert (typing E' (D1'++[(y, lbind_typ T1')]++D2') (plug C1 e) T2') as Typinge.
                apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.
             assert (disjdom (union {{y}} (fv_ee x `union` fv_te x)) (cv_ec C1)) as Disj'.
               eapply disjdom_app_l.
               split.
                 apply disjdom_one_2; auto.
               eapply disjdom_app_l.
               split.
                 eapply empty_typing_disjdom; eauto.
                 eapply empty_typing_disjdom'; eauto.
              rewrite subst_ee_plug; auto.
              rewrite <- close_open_ee__subst_ee; auto.
              assert (context C1) as Context1.
                apply contexting__context in Hcontexting; auto.    
              rewrite <- close_open_ec__subst_ec; auto.
              assert (disjdom (fv_ee x `union` fv_te x) (cv_ec (close_ec C1 y))) as Disj.
               eapply disjdom_app_l.
               split.
                 eapply empty_typing_disjdom; eauto.
                 eapply empty_typing_disjdom'; eauto.
              rewrite <- open_ee_plug; auto.
              rewrite commut_lgamma_subst_open_ee with (D:=D1'++D2')(E:=E')(dsubst:=dsubst)(gsubst:=gsubst); auto.
              rewrite commut_gamma_subst_open_ee with (D:=D1'++D2')(E:=E')(dsubst:=dsubst)(lgsubst:=lgsubst1++lgsubst2); auto.
              rewrite <- shift_ee_expr; auto.
              apply red_abs_preserved_under_delta_subst with (dE:=E'); auto.

              rewrite <- commut_gamma_subst_abs; auto.
              rewrite <- commut_gamma_subst_open_ee with (D:=D1'++D2') (dsubst:=dsubst) (E:=E') (lgsubst:=lgsubst1++lgsubst2); auto.
              apply red_abs_preserved_under_gamma_subst with (D:=D1'++D2') (dsubst:=dsubst) (E:=E')(lgsubst:=lgsubst1++lgsubst2); auto.

              rewrite <- commut_gamma_subst_abs; auto.
              rewrite <- commut_lgamma_subst_open_ee with (D:=D1'++D2')(E:=E')(dsubst:=dsubst)(gsubst:=gsubst); auto.
              apply red_abs_preserved_under_lgamma_subst with (D:=D1'++D2')(E:=E')(dsubst:=dsubst)(gsubst:=gsubst); auto. 

              apply red_abs.
                apply expr_abs with (L:=cv_ec (close_ec C1 y) `union` cv_ec C1).
                   apply type_from_wf_typ in WFTV; assumption.

                   intros.
                   assert (disjdom (fv_ee x0 `union` fv_te x0) (cv_ec (close_ec C1 y))) as Disj0'.
                     eapply disjdom_app_l.
                     split.
                       apply disjdom_one_2; auto.
                       simpl. apply disjdom_nil_1.
                   rewrite open_ee_plug; auto.
                   rewrite close_open_ec__subst_ec; auto.
                   rewrite close_open_ee__subst_ee; auto.
                  assert (disjdom (union {{y}} (fv_ee x0 `union` fv_te x0)) (cv_ec C1)) as Disj1'.
                     eapply disjdom_app_l.
                     split.
                       apply disjdom_one_2; auto.
                     eapply disjdom_app_l.
                     split.
                       apply disjdom_one_2; auto.
                       simpl. apply disjdom_nil_1.
                   rewrite <- subst_ee_plug; auto.
               apply F_related_values_inversion in Harrow_left.
               decompose [prod] Harrow_left; auto.
         split; auto.
           SSSCase "norm".
           split; auto.
           apply bigstep_red_trans with (e':=(apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst (lgsubst1'++lgsubst2') (subst_ee y x' (plug C1 e')))))); auto.
              assert (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst (lgsubst1'++lgsubst2') x')) =x') as Heq1'.
                 rewrite gamma_subst_closed_exp with (t:= apply_delta_subst_typ dsubst' T1'); auto.
                 rewrite gamma_subst_closed_exp with (t:= apply_delta_subst_typ dsubst' T1'); auto.
                 rewrite delta_subst_closed_exp with (t:= apply_delta_subst_typ dsubst' T1'); auto.
                 rewrite gamma_subst_closed_exp with (t:= apply_delta_subst_typ dsubst' T1'); auto.
              rewrite <- Heq1'.
              rewrite commut_gamma_subst_abs.
              rewrite commut_gamma_subst_abs.
              assert (subst_ee y (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst (lgsubst1'++lgsubst2') x'))) (plug C1 e') = subst_ee y x' (plug C1 e')) as Heq2'. 
                 rewrite Heq1'. auto. 
              rewrite Heq2'.
              assert (typing E' (D1'++[(y, lbind_typ T1')]++D2') (plug C1 e') T2') as Typinge'.
                apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.
             assert (disjdom (union {{y}} (fv_ee x' `union` fv_te x')) (cv_ec C1)) as Disj0'.
               eapply disjdom_app_l.
               split.
                 apply disjdom_one_2; auto.
               eapply disjdom_app_l.
               split.
                 eapply empty_typing_disjdom; eauto.
                 eapply empty_typing_disjdom'; eauto.
              rewrite subst_ee_plug; auto.
              rewrite <- close_open_ee__subst_ee; auto.
              assert (context C1) as Context1.
                apply contexting__context in Hcontexting; auto.    
              rewrite <- close_open_ec__subst_ec; auto.
              assert (disjdom (fv_ee x' `union` fv_te x') (cv_ec (close_ec C1 y))) as Disj.
                eapply disjdom_app_l.
                split.
                  eapply empty_typing_disjdom; eauto.
                  eapply empty_typing_disjdom'; eauto.
              rewrite <- open_ee_plug; auto.
              rewrite commut_lgamma_subst_open_ee with (D:=D1'++D2')(E:=E')(dsubst:=dsubst')(gsubst:=gsubst'); auto.
              rewrite commut_gamma_subst_open_ee with (D:=D1'++D2')(E:=E')(dsubst:=dsubst')(lgsubst:=lgsubst1'++lgsubst2'); auto.
              rewrite <- shift_ee_expr; auto.
              apply red_abs_preserved_under_delta_subst with (dE:=E'); auto.

              rewrite <- commut_gamma_subst_abs; auto.
              rewrite <- commut_gamma_subst_open_ee with (D:=D1'++D2') (dsubst:=dsubst') (E:=E') (lgsubst:=lgsubst1'++lgsubst2'); auto.
              apply red_abs_preserved_under_gamma_subst with (D:=D1'++D2') (dsubst:=dsubst') (E:=E')(lgsubst:=lgsubst1'++lgsubst2'); auto.

              rewrite <- commut_gamma_subst_abs; auto.
              rewrite <- commut_lgamma_subst_open_ee with (D:=D1'++D2')(E:=E')(dsubst:=dsubst')(gsubst:=gsubst'); auto.
              apply red_abs_preserved_under_lgamma_subst with (D:=D1'++D2')(E:=E')(dsubst:=dsubst')(gsubst:=gsubst'); auto. 

              apply red_abs.
                apply expr_abs with (L:=cv_ec (close_ec C1 y) `union` cv_ec C1).
                   apply type_from_wf_typ in WFTV; assumption.

                   intros.
                   assert (disjdom (fv_ee x0 `union` fv_te x0) (cv_ec (close_ec C1 y))) as Disj'.
                     eapply disjdom_app_l.
                     split.
                       apply disjdom_one_2; auto.
                       simpl. apply disjdom_nil_1.
                   rewrite open_ee_plug; auto.
                   rewrite close_open_ec__subst_ec; auto.
                   rewrite close_open_ee__subst_ee; auto.
                  assert (disjdom (union {{y}} (fv_ee x0 `union` fv_te x0)) (cv_ec C1)) as Disj1'.
                     eapply disjdom_app_l.
                     split.
                       apply disjdom_one_2; auto.
                     eapply disjdom_app_l.
                     split.
                       apply disjdom_one_2; auto.
                       simpl. apply disjdom_nil_1.
                   rewrite <- subst_ee_plug; auto.
               apply F_related_values_inversion in Harrow_left.
               decompose [prod] Harrow_left; auto.
Qed.

Lemma F_logical_related_congruence__app1 :
  forall e e' E D T,
  typing E D e T ->
  typing E D e' T ->
  (forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
   F_related_subst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
   F_Rsubst E rsubst dsubst dsubst' ->
   F_related_terms T rsubst dsubst dsubst' 
     (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
     (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e')))
  ) ->
  forall T1' E' D1' D2' D3' C1 e2 T2',
  contexting E D T C1 E' D1' (typ_arrow T1' T2') ->
  typing E' D2' e2 T1' ->
  lenv_split E' D1' D2' D3' ->
  disjdom (fv_ee e2) (dom D) ->
  (typing E D e T ->
   typing E D e' T ->
    (forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
     F_related_subst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
     F_Rsubst E rsubst dsubst dsubst' ->
     F_related_terms T rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e')))
    ) ->
   forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
     F_related_subst E' D1' gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
     F_Rsubst E' rsubst dsubst dsubst' ->
     F_related_terms (typ_arrow T1' T2') rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (plug C1 e))))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (plug C1 e'))))
  ) ->
  forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
  F_related_subst E' D3' gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
  F_Rsubst E' rsubst dsubst dsubst' ->
  F_related_terms T2' rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_app (plug C1 e) e2))))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_app (plug C1 e') e2)))).
Proof.
   intros e e' E D T Htyp Htyp' Hlr T1' E' D1' D2' D3' C1 e2 T2' Hcontexting H H0 H1 IHHcontexting dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Hrel_sub HRsub.  
   assert (J:=Hrel_sub). apply F_related_subst__inversion in J. 
   destruct J as [[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe].
   apply F_related_subst_split with (lE1:=D1') (lE2:=D2') in Hrel_sub; auto.
   destruct Hrel_sub as [lgsubst1 [lgsubst1' [lgsubst2 [lgsubst2' [J1 [J2 [J3 J4]]]]]]].

   assert (
      F_related_terms (typ_arrow T1' T2') rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst1 (plug C1 e))))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst1' (plug C1 e'))))
     ) as FR_ArrowType.
    apply IHHcontexting; auto.
   destruct FR_ArrowType as [v [v' [Ht [Ht' [Hn [Hn' Hrel]]]]]].

   apply F_related_values_arrow_leq in Hrel.
   destruct Hrel as [Hv [Hv' Harrow]]; subst.

   assert (
      F_related_terms T1' rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst2 e2)))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst'(apply_gamma_subst lgsubst2' e2)))
     ) as FR_T1.
    apply parametricity with (E:=E') (lE:=D2'); auto.
   destruct FR_T1 as [v0 [v'0 [Ht1 [Ht1' [Hn1 [Hn1' Hrel_wft1]]]]]].

   destruct (@Harrow (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst2 e2)))
                                             (apply_delta_subst dsubst' (apply_gamma_subst gsubst'(apply_gamma_subst lgsubst2' e2)))
                      ) as [u [u' [Hnorm_vxu [Hnorm_v'x'u' Hrel_wft2]]]]; auto.
    exists v0. exists v'0. repeat (split; auto).

   exists(u). exists(u').
   split. 
     assert (typing E' D3' (exp_app (plug C1 e) e2) T2') as Hptyp.
       apply typing_app with (D1:=D1') (D2:=D2') (T1:=T1'); auto.
          apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.
      apply typing_subst with (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst) in Hptyp; auto. 
   split.
     assert (typing E' D3' (exp_app (plug C1 e') e2) T2') as Hptyp'.
       apply typing_app with (D1:=D1') (D2:=D2') (T1:=T1'); auto.
          apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.
      apply typing_subst with (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst') in Hptyp'; auto. 
   assert (apply_delta_subst dsubst
            (apply_gamma_subst gsubst
              (apply_gamma_subst lgsubst (exp_app (plug C1 e) e2)) 
            ) =
            apply_delta_subst dsubst
            (apply_gamma_subst gsubst
              (exp_app 
                (apply_gamma_subst lgsubst1 (plug C1 e))
                (apply_gamma_subst lgsubst2 e2)
              )               
            )
          ) as EQ.
     simpl_commut_subst in *.
     rewrite lgamma_subst_split_subst' with (lgsubst1:=lgsubst1) (lgsubst2:=lgsubst2) (E:=E') (lE:=D3') (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst); auto.
     rewrite lgamma_subst_split_subst with (lgsubst1:=lgsubst1) (lgsubst2:=lgsubst2) (E:=E') (lE:=D3') (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst); auto.
     apply F_related_subst__inversion in J3.
     decompose [prod] J3; auto.
     apply F_related_subst__inversion in J4.
     decompose [prod] J4; auto.
     rewrite lgamma_subst_split_shuffle2 with (lgsubst:=lgsubst) (lgsubst1:=lgsubst1) (E:=E') (lE:=D3') ; auto.
     erewrite gamma_subst_closed_exp; eauto.
     rewrite lgamma_subst_split_shuffle1 with (lgsubst:=lgsubst) (lgsubst2:=lgsubst2) (E:=E') (lE:=D3') (e:=apply_gamma_subst lgsubst2 e2) ; auto.
     erewrite gamma_subst_closed_exp with 
         (e:=apply_delta_subst dsubst
            (apply_gamma_subst gsubst
              (apply_gamma_subst lgsubst2 e2))
          ); eauto.
   repeat(rewrite EQ). clear EQ.
   assert (apply_delta_subst dsubst'
            (apply_gamma_subst gsubst'
              (apply_gamma_subst lgsubst' (exp_app (plug C1 e') e2)) 
            ) =
            apply_delta_subst dsubst'
            (apply_gamma_subst gsubst'
              (exp_app 
                (apply_gamma_subst lgsubst1' (plug C1 e'))
                (apply_gamma_subst lgsubst2' e2)
              )               
            )
          ) as EQ.
     simpl_commut_subst in *.
     rewrite lgamma_subst_split_subst' with (lgsubst1:=lgsubst1') (lgsubst2:=lgsubst2') (E:=E') (lE:=D3') (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst'); auto.
     rewrite lgamma_subst_split_subst with (lgsubst1:=lgsubst1') (lgsubst2:=lgsubst2') (E:=E') (lE:=D3') (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst'); auto.
     apply F_related_subst__inversion in J3.
     decompose [prod] J3; auto.
     apply F_related_subst__inversion in J4.
     decompose [prod] J4; auto.
     rewrite lgamma_subst_split_shuffle2 with (lgsubst:=lgsubst') (lgsubst1:=lgsubst1') (E:=E') (lE:=D3') ; auto.
     erewrite gamma_subst_closed_exp; eauto.
     rewrite lgamma_subst_split_shuffle1 with (lgsubst:=lgsubst') (lgsubst2:=lgsubst2') (E:=E') (lE:=D3') (e:=apply_gamma_subst lgsubst2' e2) ; auto.
     erewrite gamma_subst_closed_exp with 
         (e:=apply_delta_subst dsubst'
            (apply_gamma_subst gsubst'
              (apply_gamma_subst lgsubst2' e2))
          ); eauto.
   repeat(rewrite EQ). clear EQ.
   repeat(split; try solve [simpl_commut_subst in *; eauto |
                                              simpl_commut_subst; apply congr_app with (v1:=v); auto |
                                              simpl_commut_subst; apply congr_app with (v1:=v'); auto]).
Qed.

Lemma F_logical_related_congruence__app2 :
  forall e e' E D T,
  typing E D e T ->
  typing E D e' T ->
  (forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
   F_related_subst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
   F_Rsubst E rsubst dsubst dsubst' ->
   F_related_terms T rsubst dsubst dsubst' 
     (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
     (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e')))
  ) ->
  forall T1' E' D1' D2' D3' e1 C2 T2',
  typing E' D1' e1 (typ_arrow T1' T2') ->
  contexting E D T C2 E' D2' T1' ->
  disjdom (fv_ee e1) (dom D) ->
  lenv_split E' D1' D2' D3' ->
  (typing E D e T ->
   typing E D e' T ->
    (forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
     F_related_subst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst'->
     F_Rsubst E rsubst dsubst dsubst' ->
     F_related_terms T rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e')))
    ) ->
   forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
     F_related_subst E' D2' gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
     F_Rsubst E' rsubst dsubst dsubst' ->
     F_related_terms T1' rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (plug C2 e))))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (plug C2 e'))))
  ) ->
  forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
  F_related_subst E' D3' gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
  F_Rsubst E' rsubst dsubst dsubst' ->
  F_related_terms T2' rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_app e1 (plug C2 e)))))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_app e1 (plug C2 e'))))).
Proof.
   intros e e' E D T Htyp Htyp' Hlr T1' E' D1' D2' D3' e1 C2 T2' H Hcontexting H0 H1 IHHcontexting dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Hrel_sub HRsub.  
   assert (J:=Hrel_sub). apply F_related_subst__inversion in J. 
   destruct J as [[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe].
   apply F_related_subst_split with (lE1:=D1') (lE2:=D2') in Hrel_sub; auto.
   destruct Hrel_sub as [lgsubst1 [lgsubst1' [lgsubst2 [lgsubst2' [J1 [J2 [J3 J4]]]]]]].

   assert (
      F_related_terms (typ_arrow T1' T2') rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst1 e1)))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst1' e1)))
     ) as FR_ArrowType.
    apply parametricity with (E:=E') (lE:=D1'); auto.
   destruct FR_ArrowType as [v [v' [Ht [Ht' [Hn [Hn' Hrel]]]]]].

   apply F_related_values_arrow_leq in Hrel.
   destruct Hrel as [Hv [Hv' Harrow]]; subst.

   assert (
      F_related_terms T1' rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst2 (plug C2 e))))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst'(apply_gamma_subst lgsubst2' (plug C2 e'))))
     ) as FR_T1.
    apply IHHcontexting; auto.
   destruct FR_T1 as [v0 [v'0 [Ht1 [Ht1' [Hn1 [Hn1' Hrel_wft1]]]]]].

   destruct (@Harrow
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst2 (plug C2 e))))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst'(apply_gamma_subst lgsubst2' (plug C2 e'))))
                     ) as [u [u' [Hnorm_vxu [Hnorm_v'x'u' Hrel_wft2]]]]; auto.
    exists v0. exists v'0. repeat (split; auto).

   exists(u). exists(u').
   split. 
     assert (typing E' D3' (exp_app e1 (plug C2 e)) T2') as Hptyp.
       apply typing_app with (D1:=D1') (D2:=D2') (T1:=T1'); auto.
          apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.
      apply typing_subst with (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst) in Hptyp; auto. 
   split.
     assert (typing E' D3' (exp_app e1 (plug C2 e')) T2') as Hptyp'.
       apply typing_app with (D1:=D1') (D2:=D2') (T1:=T1'); auto.
          apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.
      apply typing_subst with (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst') in Hptyp'; auto. 
   assert (apply_delta_subst dsubst
            (apply_gamma_subst gsubst
              (apply_gamma_subst lgsubst (exp_app e1 (plug C2 e))) 
            ) =
            apply_delta_subst dsubst
            (apply_gamma_subst gsubst
              (exp_app 
                (apply_gamma_subst lgsubst1 e1)
                (apply_gamma_subst lgsubst2 (plug C2 e))
              )               
            )
          ) as EQ.
     simpl_commut_subst in *.
     rewrite lgamma_subst_split_subst' with (lgsubst1:=lgsubst1) (lgsubst2:=lgsubst2) (E:=E') (lE:=D3') (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst); auto.
     rewrite lgamma_subst_split_subst with (lgsubst1:=lgsubst1) (lgsubst2:=lgsubst2) (E:=E') (lE:=D3') (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst); auto.
     apply F_related_subst__inversion in J3.
     decompose [prod] J3; auto.
     apply F_related_subst__inversion in J4.
     decompose [prod] J4; auto.
     rewrite lgamma_subst_split_shuffle2 with (lgsubst:=lgsubst) (lgsubst1:=lgsubst1) (E:=E') (lE:=D3') ; auto.
     erewrite gamma_subst_closed_exp; eauto.
     rewrite lgamma_subst_split_shuffle1 with (lgsubst:=lgsubst) (lgsubst2:=lgsubst2) (E:=E') (lE:=D3') (e:=apply_gamma_subst lgsubst2 (plug C2 e)) ; auto.
     erewrite gamma_subst_closed_exp with 
         (e:=apply_delta_subst dsubst
            (apply_gamma_subst gsubst
              (apply_gamma_subst lgsubst2 (plug C2 e)))
          ); eauto.
   repeat(rewrite EQ). clear EQ.
   assert (apply_delta_subst dsubst'
            (apply_gamma_subst gsubst'
              (apply_gamma_subst lgsubst' (exp_app e1 (plug C2 e'))) 
            ) =
            apply_delta_subst dsubst'
            (apply_gamma_subst gsubst'
              (exp_app 
                (apply_gamma_subst lgsubst1' e1 )
                (apply_gamma_subst lgsubst2' (plug C2 e'))
              )               
            )
          ) as EQ.
     simpl_commut_subst in *.
     rewrite lgamma_subst_split_subst' with (lgsubst1:=lgsubst1') (lgsubst2:=lgsubst2') (E:=E') (lE:=D3') (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst'); auto.
     rewrite lgamma_subst_split_subst with (lgsubst1:=lgsubst1') (lgsubst2:=lgsubst2') (E:=E') (lE:=D3') (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst'); auto.
     apply F_related_subst__inversion in J3.
     decompose [prod] J3; auto.
     apply F_related_subst__inversion in J4.
     decompose [prod] J4; auto.
     rewrite lgamma_subst_split_shuffle2 with (lgsubst:=lgsubst') (lgsubst1:=lgsubst1') (E:=E') (lE:=D3') ; auto.
     erewrite gamma_subst_closed_exp; eauto.
     rewrite lgamma_subst_split_shuffle1 with (lgsubst:=lgsubst') (lgsubst2:=lgsubst2') (E:=E') (lE:=D3') (e:=apply_gamma_subst lgsubst2' (plug C2 e')) ; auto.
     erewrite gamma_subst_closed_exp with 
         (e:=apply_delta_subst dsubst'
            (apply_gamma_subst gsubst'
              (apply_gamma_subst lgsubst2' (plug C2 e')))
          ); eauto.
   repeat(rewrite EQ). clear EQ.
   repeat(split; try solve [simpl_commut_subst in *; eauto |
                                              simpl_commut_subst; apply congr_app with (v1:=v); auto |
                                              simpl_commut_subst; apply congr_app with (v1:=v'); auto]).
Qed.

Lemma F_logical_related_congruence__tabs_free :
  forall e e' E D T,
  typing E D e T ->
  typing E D e' T ->
  (forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
   F_related_subst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
   F_Rsubst E rsubst dsubst dsubst' ->
   F_related_terms T rsubst dsubst dsubst' 
     (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
     (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e')))
  ) ->
  forall L C1 T1' E' D',
  (forall X,
    X `notin` L ->
    contexting E D T (open_tc C1 X) ((X, bind_kn)::E') D' (open_tt T1' X)
  ) ->
  (forall X,
   X `notin` L ->
   typing E D e T ->
   typing E D e' T ->
    (forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
     F_related_subst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
     F_Rsubst E rsubst dsubst dsubst' ->
     F_related_terms T rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e')))
    ) ->
   forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
     F_related_subst ((X, bind_kn)::E') D' gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
     F_Rsubst ((X, bind_kn)::E') rsubst dsubst dsubst' ->
     F_related_terms (open_tt T1' X) rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (plug (open_tc C1 X) e))))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (plug (open_tc C1 X) e'))))
  ) ->
  forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
  F_related_subst E' D' gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
  F_Rsubst E' rsubst dsubst dsubst' ->
  F_related_terms (typ_all T1') rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_tabs (plug C1 (shift_te e))))))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_tabs (plug C1 (shift_te e')))))).
Proof.
  intros e e' E D T Htyp Htyp' Hlr L C1 T1' E' D' H1 H2 dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Hrel_sub HRsub.
  assert (J:=Hrel_sub). apply F_related_subst__inversion in J.
  destruct J as [[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe].
  assert (value (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_tabs (plug C1 (shift_te e))))))) as Value.
    apply delta_gamma_lgamma_subst_value with (E:=E') (D:=D'); auto.
      apply value_tabs; auto.
        apply expr_tabs with (L:=L `union` cv_ec C1); auto.
          intros X Xn.
          assert (X `notin` L) as XnFv. auto.
          apply H1 in XnFv.
          apply contexting_plug_typing with (e:=e) in XnFv; auto.
          simpl_env in XnFv.
          rewrite open_te_expr' with (e:=e) (u:=X) in XnFv; auto.
          assert (disjdom (fv_tt X) (cv_ec C1)) as Disj.
            apply disjdom_one_2; auto.
          rewrite <- open_te_plug in XnFv; auto. 
          rewrite shift_te_expr with (e:=e) in XnFv; auto.
  assert (value (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_tabs (plug C1 (shift_te e'))))))) as Value'.
    apply delta_gamma_lgamma_subst_value with (E:=E') (D:=D'); auto.
      apply value_tabs; auto.
        apply expr_tabs with (L:=L `union` cv_ec C1); auto.
          intros X Xn.
          assert (X `notin` L) as XnFv. auto.
          apply H1 in XnFv.
          apply contexting_plug_typing with (e:=e') in XnFv; auto.
          simpl_env in XnFv.
          rewrite open_te_expr' with (e:=e') (u:=X) in XnFv; auto.
          assert (disjdom (fv_tt X) (cv_ec C1)) as Disj.
            apply disjdom_one_2; auto.
          rewrite <- open_te_plug in XnFv; auto. 
          rewrite shift_te_expr with (e:=e') in XnFv; auto.
    
  exists (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_tabs (plug C1 (shift_te e)))))).
  exists (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_tabs (plug C1 (shift_te e')))))).
    split.
      assert (typing E' D' (plug (ctx_tabs_free C1) e) (typ_all T1')) as Hptyp.
        apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.
           apply contexting_tabs_free with (L:=L); auto.
      apply typing_subst with (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst) in Hptyp; auto.
    split.
      assert (typing E' D' (plug (ctx_tabs_free C1) e') (typ_all T1')) as Hptyp'.
        apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.
           apply contexting_tabs_free with (L:=L); auto.
      apply typing_subst with (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst') in Hptyp'; auto.
    split. split; auto.
    split. split; auto.
      SCase "Frel".
      apply F_related_values_all_req.
      split; auto.
      split; auto.
        SSCase "Frel".
        exists (L `union` fv_te e `union` dom E `union` fv_env E `union` fv_lenv D `union` fv_env E' `union` fv_lenv D' `union` cv_ec C1 `union` fv_te (plug C1 e) `union` fv_te (plug C1 e')).
        intros X t2 t2' R Fr HwfR Hfv.
        assert (X `notin` L) as FryL. auto.
        assert (wf_typ ([(X,bind_kn)]++E') (open_tt T1' X)) as WFT'.
          apply H1 in FryL.
          apply contexting_regular in FryL.
          decompose [and] FryL; auto.
        apply H2 with (dsubst:=[(X, t2)]++dsubst) 
                         (dsubst':=[(X, t2')]++dsubst') 
                         (gsubst:=gsubst)
                         (gsubst':=gsubst') 
                         (lgsubst:=lgsubst)
                         (lgsubst':=lgsubst') 
                         (rsubst:=[(X,R)]++rsubst)in FryL; auto.
        simpl in FryL. simpl_env in FryL.
        erewrite swap_subst_te_gsubst with (E:=E') (dsubst:=dsubst) in FryL; eauto using wfr_left_inv. 
        erewrite swap_subst_te_lgsubst with (E:=E') (dsubst:=dsubst) in FryL; eauto using wfr_left_inv. 
        erewrite swap_subst_te_gsubst with  (E:=E')  (dsubst:=dsubst') in FryL; eauto using wfr_right_inv.
        erewrite swap_subst_te_lgsubst with  (E:=E')  (dsubst:=dsubst') in FryL; eauto using wfr_right_inv.
        destruct FryL as [v [v' [Ht [Ht' [[Hbrc Hv] [[Hbrc' Hv'] Hrel]]]]]].
        exists (v). exists (v').
        split.
          SSSCase "norm".
          split; auto.
          apply bigstep_red_trans with (e':=(apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (subst_te X t2 (plug (open_tc C1 X) e)))))); auto.
              rewrite <- shift_te_expr; auto.
             assert (plug (open_tc C1 X) e = open_te (plug C1 e) X) as EQ.
               rewrite open_te_plug; auto.
                 rewrite <- open_te_expr'; auto.
                 apply disjdom_one_2; auto.
             rewrite EQ.
             eapply m_red_tabs_subst with (T1:=T1') (L:=L `union` cv_ec C1); eauto.
               apply wfr_left_inv in HwfR; auto.

               intros X0 X0dom.
               assert (X0 `notin` L) as X0n. auto.
               apply H1 in X0n.
               assert (disjdom (fv_tt X0) (cv_ec C1)) as Disj.
                 apply disjdom_one_2; auto.
               rewrite open_te_plug; auto.
               rewrite <- open_te_expr'; auto.
               apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.       

        split; auto.
          SSSCase "norm".
          split; auto.
          apply bigstep_red_trans with (e':=(apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (subst_te X t2' (plug (open_tc C1 X) e')))))); auto.
              rewrite <- shift_te_expr; auto.
             assert (plug (open_tc C1 X) e' = open_te (plug C1 e') X) as EQ.
               rewrite open_te_plug; auto.
                 rewrite <- open_te_expr'; auto.
                 apply disjdom_one_2; auto.
             rewrite EQ.
             eapply m_red_tabs_subst with (T1:=T1') (L:=L `union` cv_ec C1); eauto.
               apply wfr_right_inv in HwfR; auto.

               intros X0 X0dom.
               assert (X0 `notin` L) as X0n. auto.
               apply H1 in X0n.
               assert (disjdom (fv_tt X0) (cv_ec C1)) as Disj.
                 apply disjdom_one_2; auto.
               rewrite open_te_plug; auto.
               rewrite <- open_te_expr'; auto.
               apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.       

          SSSCase "Fsubst".
          simpl_env.
          apply F_related_subst_kind; auto.
          SSSCase "FRsubst".
          simpl_env.
          apply F_Rsubst_rel; auto.
Qed.

Lemma F_logical_related_congruence__tabs_capture :
  forall e e' E D T,
  typing E D e T ->
  typing E D e' T ->
  (forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
   F_related_subst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
   F_Rsubst E rsubst dsubst dsubst' ->
   F_related_terms T rsubst dsubst dsubst' 
     (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
     (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e')))
  ) ->
  forall Y C1 T1' E' D',
  binds Y (bind_kn) E' ->
  Y `notin` cv_ec C1 ->
  contexting E D T C1 E' D' T1' ->
  wf_lenv (env_remove (Y, bind_kn) E') D' ->
  (typing E D e T ->
   typing E D e' T ->
    (forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
     F_related_subst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst'->
     F_Rsubst E rsubst dsubst dsubst' ->
     F_related_terms T rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e')))
    ) ->
   forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
     F_related_subst E' D' gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
     F_Rsubst E' rsubst dsubst dsubst' ->
     F_related_terms T1' rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (plug C1 e))))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (plug C1 e'))))
  ) ->
  forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
  F_related_subst (env_remove (Y, bind_kn) E') D' gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
  F_Rsubst (env_remove (Y, bind_kn) E') rsubst dsubst dsubst' ->
  F_related_terms (typ_all (close_tt T1' Y)) rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_tabs (plug (close_tc C1 Y) (close_te (shift_te e) Y))))))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_tabs (plug (close_tc C1 Y) (close_te (shift_te e') Y)))))).
Proof.
    intros e e' E D T Htyp Htyp' Hlr Y C1 T1' E' D' H H0 Hcontexting H2 IHHcontexting dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Hrel_sub HRsub.
    assert (J:=Hrel_sub). apply F_related_subst__inversion in J. 
    destruct J as [[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe].

    assert (Fry := @IHHcontexting Htyp Htyp' Hlr).
    assert (wf_env E') as Wfe'.
      apply contexting_regular in Hcontexting.
      decompose [and] Hcontexting; auto.
    assert (EQ1:=@env_remove_inv E' Y (bind_kn)  Wfe' H).
    destruct EQ1 as [E1' [E2' [EQ1' EQ2']]]; subst.
    rewrite EQ1' in *.

    assert (EQ:=Hwflg).
    apply wf_lgsubst_app_inv in EQ.
    destruct EQ as [dsubst1 [dsubst2 [gsubst1 [gsubst2 [dEQ1 [dEQ2 [dEQ3 [gEQ1 [gEQ2 gEQ3]]]]]]]]]; subst.

    assert (EQ:=Hwflg').
    apply wf_lgsubst_app_inv in EQ.
    destruct EQ as [dsubst1' [dsubst2' [gsubst1' [gsubst2' [dEQ1' [dEQ2' [dEQ3' [gEQ1' [gEQ2' gEQ3']]]]]]]]]; subst.
       
    assert (EQ:=Hwfr).
    apply wf_rsubst_app_inv in EQ.
    destruct EQ as [rsubst1 [rsubst2 [rEQ1 [rEQ2 rEQ3]]]]; subst.

    assert (value (apply_delta_subst (dsubst1++dsubst2) (apply_gamma_subst (gsubst1++gsubst2) (apply_gamma_subst lgsubst (exp_tabs (plug (close_tc C1 Y) (close_te (shift_te e) Y))))))) as Value.
      apply delta_gamma_lgamma_subst_value with (E:=E1'++E2') (D:=D'); auto.
        apply value_tabs.
        apply expr_tabs with (L:=dom (E1'++E2') `union` dom D' `union` cv_ec (close_tc C1 Y) `union` cv_ec C1); auto.
          intros X XnFv.
          rewrite <- shift_te_expr with (e:=e); auto.
          assert (disjdom (fv_tt X) (cv_ec (close_tc C1 Y))) as Disj.
            apply disjdom_one_2; auto.
          rewrite open_te_plug; auto. 
          rewrite close_open_te__subst_te; auto.
          assert (context C1) as Ctx1.
            apply contexting__context in Hcontexting; auto.
          rewrite close_open_tc__subst_tc; auto.
          assert (disjdom (union {{Y}} (fv_tt X)) (cv_ec C1)) as Disj'.
            eapply disjdom_app_l.
            split.
              apply disjdom_one_2; auto.
              apply disjdom_one_2; auto.
          rewrite <- subst_te_plug; auto. 
          assert (typing (E1'++[(Y, bind_kn)]++E2') D' (plug C1 e) T1') as Htyp2.
            apply contexting_plug_typing with (e:=e) in Hcontexting; auto.
          apply subst_te_expr; auto.

    assert (value (apply_delta_subst (dsubst1'++dsubst2') (apply_gamma_subst (gsubst1'++gsubst2') (apply_gamma_subst lgsubst' (exp_tabs (plug (close_tc C1 Y)  (close_te (shift_te e') Y))))))) as Value'.
      apply delta_gamma_lgamma_subst_value with (E:=E1'++E2') (D:=D'); auto.
        apply value_tabs.
        apply expr_tabs with (L:=dom (E1'++E2') `union` dom D' `union` cv_ec (close_tc C1 Y) `union` cv_ec C1); auto.
          intros X XnFv.
          rewrite <- shift_te_expr with (e:=e'); auto.
          assert (disjdom (fv_tt X) (cv_ec (close_tc C1 Y))) as Disj.
            apply disjdom_one_2; auto.
          rewrite open_te_plug; auto. 
          rewrite close_open_te__subst_te; auto.
          assert (context C1) as Ctx1.
            apply contexting__context in Hcontexting; auto.
          rewrite close_open_tc__subst_tc; auto.
          assert (disjdom (union {{Y}} (fv_tt X)) (cv_ec C1)) as Disj'.
            eapply disjdom_app_l.
            split.
              apply disjdom_one_2; auto.
              apply disjdom_one_2; auto.
          rewrite <- subst_te_plug; auto. 
          assert (typing (E1'++[(Y, bind_kn)]++E2') D' (plug C1 e') T1') as Htyp2'.
            apply contexting_plug_typing with (e:=e') in Hcontexting; auto.
          apply subst_te_expr; auto.

    exists (apply_delta_subst (dsubst1++dsubst2) (apply_gamma_subst (gsubst1++gsubst2) (apply_gamma_subst lgsubst (exp_tabs (plug (close_tc C1 Y) (close_te (shift_te e) Y)))))).
    exists (apply_delta_subst (dsubst1'++dsubst2') (apply_gamma_subst (gsubst1'++gsubst2') (apply_gamma_subst lgsubst' (exp_tabs (plug (close_tc C1 Y) (close_te (shift_te e') Y)))))).
    split.
      assert (typing (E1'++E2') D' (plug (ctx_tabs_capture Y (close_tc C1 Y)) e) (typ_all (close_tt T1' Y))) as Hptyp.
        destruct (in_dec Y (fv_te e)) as [yine | ynine].
          simpl.
          apply typing_tabs with (L:=dom (E1'++E2') `union` dom D' `union` dom E `union` dom D `union` {{Y}} `union` cv_ec C1 `union` cv_ec (close_tc C1 Y)); auto.
            intros X Xn.
            rewrite <- shift_te_expr; auto.
            assert (disjdom (fv_tt X) (cv_ec (close_tc C1 Y))) as Disj.
              apply disjdom_one_2; auto.
            rewrite open_te_plug; auto.
            assert (Y `in` ddom_env E) as Binds.
              apply in_fv_te_typing' with (X:=Y) in Htyp; auto.
            rewrite close_open_te__subst_te; auto.
            assert (context C1) as Ctx1.
              apply contexting__context in Hcontexting; auto.
            rewrite close_open_tc__subst_tc; auto.
            apply dbinds_In_inv in Binds.
            assert (wf_env E) as Wfe. auto.
            assert (J:=@env_remove2_inv E Y (bind_kn) Wfe Binds).
            destruct J as [E1 [E2 [EQ1 EQ2]]]; subst.

            apply typing_typ_permute; auto. 
            assert (J:=Hcontexting).
            apply contexting_typ_renaming_one with (Y:=X) in Hcontexting; auto.
            assert (Y `notin` fv_env E1' `union` fv_env E2' `union` fv_lenv D') as YnE1'E2'D'.
              apply wf_lenv_notin_fv_env; auto.          
                 apply contexting_regular in J.
                 decompose [and] J; auto.
            assert (Y `notin` dom (E1' ++ E2')) as YndE1'E2'D'.
              clear Xn.
              destruct_notin.
              apply free_env__free_dom in YnE1'E2'D'.
              apply free_env__free_dom in NotInTac.
              auto.
            rewrite <- map_subst_tlb_id with (G:=E1'++E2') (D:=D') in Hcontexting; try solve [assumption].
            rewrite <- map_subst_tb_id' with (G:=E1') (G':=E2') in Hcontexting; try solve [assumption].
            apply contexting_plug_typing with (E:=map (subst_tb Y X) E1++[(X, bind_kn)]++E2) (D:=map (subst_tlb Y X) D) (T:=subst_tt Y X T); auto.
              rewrite close_open_tt__subst_tt; auto.
                apply contexting_regular in J.
                decompose [and] J.
                apply type_from_wf_typ in H8; auto.

              simpl_env in Xn.
              apply typing_typ_renaming_one with (Y:=X) in Htyp; auto.

          rewrite <- EQ1'.
          apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.
            apply contexting_tabs_capture; auto.
              rewrite EQ1'. auto.
      apply typing_subst with (dsubst:=dsubst1++dsubst2) (gsubst:=gsubst1++gsubst2) (lgsubst:=lgsubst) in Hptyp; auto.
    split.
      assert (typing (E1'++E2') D' (plug (ctx_tabs_capture Y (close_tc C1 Y)) e') (typ_all (close_tt T1' Y))) as Hptyp'.
        destruct (in_dec Y (fv_te e')) as [yine' | ynine'].
          simpl.
          apply typing_tabs with (L:=dom (E1'++E2') `union` dom D' `union` dom E `union` dom D `union` {{Y}} `union` cv_ec C1 `union` cv_ec (close_tc C1 Y)); auto.
            intros X Xn.
            rewrite <- shift_te_expr; auto.
            assert (disjdom (fv_tt X) (cv_ec (close_tc C1 Y))) as Disj.
              apply disjdom_one_2; auto.
            rewrite open_te_plug; auto.
            assert (Y `in` ddom_env E) as Binds.
              apply in_fv_te_typing' with (X:=Y) in Htyp'; auto.
            rewrite close_open_te__subst_te; auto.
            assert (context C1) as Ctx1.
              apply contexting__context in Hcontexting; auto.
            rewrite close_open_tc__subst_tc; auto.
            apply dbinds_In_inv in Binds.
            assert (wf_env E) as Wfe. auto.
            assert (J:=@env_remove2_inv E Y (bind_kn) Wfe Binds).
            destruct J as [E1 [E2 [EQ1 EQ2]]]; subst.

            apply typing_typ_permute; auto. 
            assert (J:=Hcontexting).
            apply contexting_typ_renaming_one with (Y:=X) in Hcontexting; auto.
            assert (Y `notin` fv_env E1' `union` fv_env E2' `union` fv_lenv D') as YnE1'E2'D'.
              apply wf_lenv_notin_fv_env; auto.          
                 apply contexting_regular in J.
                 decompose [and] J; auto.
            assert (Y `notin` dom (E1' ++ E2')) as YndE1'E2'D'.
              clear Xn.
              destruct_notin.
              apply free_env__free_dom in YnE1'E2'D'.
              apply free_env__free_dom in NotInTac.
              auto.
            rewrite <- map_subst_tlb_id with (G:=E1'++E2') (D:=D') in Hcontexting; try solve [assumption].
            rewrite <- map_subst_tb_id' with (G:=E1') (G':=E2') in Hcontexting; try solve [assumption].
            apply contexting_plug_typing with (E:=map (subst_tb Y X) E1++[(X, bind_kn)]++E2) (D:=map (subst_tlb Y X) D) (T:=subst_tt Y X T); auto.
              rewrite close_open_tt__subst_tt; auto.
                apply contexting_regular in J.
                decompose [and] J.
                apply type_from_wf_typ in H8; auto.

              simpl_env in Xn.
              apply typing_typ_renaming_one with (Y:=X) in Htyp'; auto.

          rewrite <- EQ1'.
          apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.
            apply contexting_tabs_capture; auto.
              rewrite EQ1'. auto.
      apply typing_subst with (dsubst:=dsubst1'++dsubst2') (gsubst:=gsubst1'++gsubst2') (lgsubst:=lgsubst') in Hptyp'; auto.
    split. split; auto.
    split. split; auto.
      SCase "Frel".
      apply F_related_values_all_req.
      split; auto.
      split; auto.

        SSCase "Frel".
        exists (fv_te e `union` dom E `union` fv_env E `union` fv_lenv D `union` {{Y}} `union` fv_env E1' `union` fv_lenv D' `union` cv_ec C1 `union` fv_te (plug C1 e) `union` fv_te (plug C1 e') `union` dom E1' `union` dom E2' `union` fv_tt T1').
        intros X t2 t2' R Fr HwfR Hfv.

        assert (F_related_subst (E1'++[(Y, bind_kn)]++E2') D' (gsubst1++gsubst2) (gsubst1'++gsubst2') lgsubst lgsubst' (rsubst1++[(Y,R)]++rsubst2) (dsubst1++[(Y,t2)]++dsubst2) (dsubst1'++[(Y,t2')]++dsubst2')) as Hrel_sub'.
          apply F_related_subst_dweaken; auto.
             assert (Y `notin` dom E1') as YnE1'.
                apply fresh_mid_head with (E:=E2') (a:=bind_kn); auto.
             assert (Y `notin` dom E2') as YnE2'.
                apply fresh_mid_tail with (F:=E1') (a:=bind_kn); auto.
             assert (Y `notin` dom D') as YnD'.
               apply contexting_regular in Hcontexting.
               decompose [and] Hcontexting.
               apply wf_lenv_notin_fv_env with (E1:=E1') (E2:=E2') (X:=Y) in H6; auto.
             auto.

        assert (F_Rsubst (E1'++[(Y, bind_kn)] ++E2') (rsubst1++[(Y, R)]++rsubst2) (dsubst1++[(Y, t2)] ++dsubst2) (dsubst1'++[(Y, t2')] ++dsubst2')) as HRsub'. 
          apply F_Rsubst_dweaken; auto.       
             assert (Y `notin` dom E1') as ynE1'.
                apply fresh_mid_head with (E:=E2') (a:=bind_kn); auto.
             assert (Y `notin` dom E2') as ynE2'.
                apply fresh_mid_tail with (F:=E1') (a:=bind_kn); auto.
             auto.

        assert (J:=@Fry (dsubst1++[(Y, t2)]++dsubst2) (dsubst1'++[(Y, t2')]++dsubst2') (gsubst1++gsubst2) (gsubst1'++gsubst2') lgsubst lgsubst' (rsubst1++[(Y, R)]++rsubst2) Hrel_sub' HRsub').

        assert (
            apply_delta_subst (dsubst1++[(Y, t2)]++dsubst2) (apply_gamma_subst (gsubst1++gsubst2) (apply_gamma_subst lgsubst (plug C1 e))) =
            apply_delta_subst (dsubst1++dsubst2) (apply_gamma_subst (gsubst1++gsubst2) (apply_gamma_subst lgsubst (subst_te Y t2 (plug C1 e))))
                  ) as Heq1. simpl.
           simpl_env.
           assert (wf_typ nil t2) as Wft2. apply wfr_left_inv in HwfR; auto.
           apply F_related_subst__inversion in Hrel_sub'.
           decompose [prod] Hrel_sub'; auto.
           apply F_related_subst__inversion in Hrel_sub.
           decompose [prod] Hrel_sub; auto.
           rewrite delta_subst_opt' with (E':=E1') (E:=E2'); auto.
           rewrite swap_subst_te_gsubst with  (D:=D') (E:=E1'++E2') (dsubst:=dsubst1++dsubst2) (lgsubst:=lgsubst); auto.
           rewrite swap_subst_te_lgsubst with  (D:=D') (E:=E1'++E2') (dsubst:=dsubst1++dsubst2) (gsubst:=gsubst1++gsubst2); auto.

         assert (
            apply_delta_subst (dsubst1'++[(Y,t2')]++dsubst2') (apply_gamma_subst (gsubst1'++gsubst2') (apply_gamma_subst lgsubst' (plug C1 e'))) =
            apply_delta_subst (dsubst1'++dsubst2') (apply_gamma_subst (gsubst1'++gsubst2') (apply_gamma_subst lgsubst' (subst_te Y t2' (plug C1 e'))))
                  ) as Heq2.  simpl.
           simpl_env.
           assert (wf_typ nil t2') as Wft2. apply wfr_right_inv in HwfR; auto.
           apply F_related_subst__inversion in Hrel_sub'.
           decompose [prod] Hrel_sub'; auto.
           apply F_related_subst__inversion in Hrel_sub.
           decompose [prod] Hrel_sub; auto.
           rewrite delta_subst_opt' with (E':=E1') (E:=E2'); auto.
           rewrite swap_subst_te_gsubst with  (D:=D') (E:=E1'++E2') (dsubst:=dsubst1'++dsubst2') (lgsubst:=lgsubst'); auto.
           rewrite swap_subst_te_lgsubst with  (D:=D') (E:=E1'++E2') (dsubst:=dsubst1'++dsubst2') (gsubst:=gsubst1'++gsubst2'); auto.

         rewrite Heq1 in J. rewrite Heq2 in J. clear Heq1 Heq2.
         destruct J as [v [v' [Ht [Ht' [[Hbrc Hv] [[Hbrc' Hv'] Hrel]]]]]].
         exists (v). exists (v').
         split.
           SSSCase "norm".
           split; auto.
           apply bigstep_red_trans with (e':=(apply_delta_subst (dsubst1++dsubst2) (apply_gamma_subst (gsubst1++gsubst2)  (apply_gamma_subst lgsubst (subst_te Y t2 (plug C1 e)))))); auto.
              assert (apply_delta_subst_typ (dsubst1++dsubst2) t2 = t2) as Heq1.
                 rewrite delta_subst_closed_typ; auto.
                   apply wfr_left_inv in HwfR; auto.
              rewrite <- Heq1.
              rewrite commut_gamma_subst_tabs.
              rewrite commut_gamma_subst_tabs.
              assert (subst_te Y (apply_delta_subst_typ  (dsubst1++dsubst2) t2) (plug C1 e) = subst_te Y t2 (plug C1 e)) as Heq2. 
                 rewrite Heq1. auto. 
              rewrite Heq2.
              assert (typing (E1'++[(Y, bind_kn)]++E2') D' (plug C1 e) T1') as Typinge.
                apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.
             assert (disjdom (union {{Y}} (fv_tt t2)) (cv_ec C1)) as Disj0.
               eapply disjdom_app_l.
               split.
                 apply disjdom_one_2; auto.
                 eapply empty_wft_disjdom; eauto using wfr_left_inv.
             assert (type t2) as Type2.
               apply wfr_left_inv in HwfR.
               apply type_from_wf_typ in HwfR; auto. 
              rewrite subst_te_plug; auto.
              rewrite <- close_open_te__subst_te; auto.
              assert (context C1) as Context1.
                apply contexting__context in Hcontexting; auto.    
              rewrite <- close_open_tc__subst_tc; auto.
              assert (disjdom (fv_tt t2) (cv_ec (close_tc C1 Y))) as Disj.
                eapply empty_wft_disjdom; eauto using wfr_left_inv.
              rewrite <- open_te_plug; auto.
              rewrite commut_lgamma_subst_open_te with (E:=E1'++E2')(D:=D')(dsubst:=dsubst1++dsubst2)(gsubst:=gsubst1++gsubst2); auto.
              rewrite commut_gamma_subst_open_te with (E:=E1'++E2')(D:=D')(dsubst:=dsubst1++dsubst2)(lgsubst:=lgsubst); auto.
              rewrite <- shift_te_expr; auto.
              apply red_tabs_preserved_under_delta_subst with (dE:=E1'++E2'); auto.

              rewrite <- commut_gamma_subst_tabs; auto.
              rewrite <- commut_gamma_subst_open_te with (E:=E1'++E2') (dsubst:=dsubst1++dsubst2) (D:=D') (lgsubst:=lgsubst); auto.
              apply red_tabs_preserved_under_gamma_subst with (E:=E1'++E2') (dsubst:=dsubst1++dsubst2) (D:=D') (lgsubst:=lgsubst); auto. 

              rewrite <- commut_gamma_subst_tabs; auto.
              rewrite <- commut_lgamma_subst_open_te with (E:=E1'++E2')(D:=D')(dsubst:=dsubst1++dsubst2)(gsubst:=gsubst1++gsubst2); auto.
              apply red_tabs_preserved_under_lgamma_subst with (E:=E1'++E2')(D:=D')(dsubst:=dsubst1++dsubst2)(gsubst:=gsubst1++gsubst2); auto. 

              apply red_tabs; auto.
                apply expr_tabs with (L:=(cv_ec (close_tc C1 Y)) `union` cv_ec C1).
                   intros.
                   assert (disjdom (fv_tt X0) (cv_ec (close_tc C1 Y))) as Disj'.
                     apply disjdom_one_2; auto.
                   rewrite open_te_plug; auto.
                   rewrite close_open_tc__subst_tc; auto.
                   rewrite close_open_te__subst_te; auto.
                  assert (disjdom (union {{Y}} (fv_tt X0)) (cv_ec C1)) as Disj0'.
                     eapply disjdom_app_l.
                     split.
                       apply disjdom_one_2; auto.
                       apply disjdom_one_2; auto.
                   rewrite <- subst_te_plug; auto.

         split; auto.
           SSSCase "norm".
           split; auto.
           apply bigstep_red_trans with (e':=(apply_delta_subst (dsubst1'++dsubst2') (apply_gamma_subst (gsubst1'++gsubst2')  (apply_gamma_subst lgsubst' (subst_te Y t2' (plug C1 e')))))); auto.
              assert (apply_delta_subst_typ (dsubst1'++dsubst2') t2' = t2') as Heq1.
                 rewrite delta_subst_closed_typ; auto.
                   apply wfr_right_inv in HwfR; auto.
              rewrite <- Heq1.
              rewrite commut_gamma_subst_tabs.
              rewrite commut_gamma_subst_tabs.
              assert (subst_te Y (apply_delta_subst_typ  (dsubst1'++dsubst2') t2') (plug C1 e') = subst_te Y t2' (plug C1 e')) as Heq2. 
                 rewrite Heq1. auto. 
              rewrite Heq2.
              assert (typing (E1'++[(Y, bind_kn)]++E2') D' (plug C1 e') T1') as Typinge'.
                apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.
             assert (disjdom (union {{Y}} (fv_tt t2')) (cv_ec C1)) as Disj0.
               eapply disjdom_app_l.
               split.
                 apply disjdom_one_2; auto.
                 eapply empty_wft_disjdom; eauto using wfr_right_inv.
             assert (type t2') as Type2'.
               apply wfr_right_inv in HwfR.
               apply type_from_wf_typ in HwfR; auto. 
              rewrite subst_te_plug; auto.
              rewrite <- close_open_te__subst_te; auto.
              assert (context C1) as Context1.
                apply contexting__context in Hcontexting; auto.    
              rewrite <- close_open_tc__subst_tc; auto.
              assert (disjdom (fv_tt t2') (cv_ec (close_tc C1 Y))) as Disj.
                eapply empty_wft_disjdom; eauto using wfr_right_inv.
              rewrite <- open_te_plug; auto.
              rewrite commut_lgamma_subst_open_te with (E:=E1'++E2')(D:=D')(dsubst:=dsubst1'++dsubst2')(gsubst:=gsubst1'++gsubst2'); auto.
              rewrite commut_gamma_subst_open_te with (E:=E1'++E2')(D:=D')(dsubst:=dsubst1'++dsubst2')(lgsubst:=lgsubst'); auto.
              rewrite <- shift_te_expr; auto.
              apply red_tabs_preserved_under_delta_subst with (dE:=E1'++E2'); auto.

              rewrite <- commut_gamma_subst_tabs; auto.
              rewrite <- commut_gamma_subst_open_te with (E:=E1'++E2') (dsubst:=dsubst1'++dsubst2') (D:=D') (lgsubst:=lgsubst'); auto.
              apply red_tabs_preserved_under_gamma_subst with (E:=E1'++E2') (dsubst:=dsubst1'++dsubst2') (D:=D') (lgsubst:=lgsubst'); auto. 

              rewrite <- commut_gamma_subst_tabs; auto.
              rewrite <- commut_lgamma_subst_open_te with (E:=E1'++E2')(D:=D')(dsubst:=dsubst1'++dsubst2')(gsubst:=gsubst1'++gsubst2'); auto.
              apply red_tabs_preserved_under_lgamma_subst with (E:=E1'++E2')(D:=D')(dsubst:=dsubst1'++dsubst2')(gsubst:=gsubst1'++gsubst2'); auto. 

              apply red_tabs; auto.
                apply expr_tabs with (L:=(cv_ec (close_tc C1 Y)) `union` cv_ec C1).
                   intros.
                   assert (disjdom (fv_tt X0) (cv_ec (close_tc C1 Y))) as Disj'.
                     apply disjdom_one_2; auto.
                   rewrite open_te_plug; auto.
                   rewrite close_open_tc__subst_tc; auto.
                   rewrite close_open_te__subst_te; auto.
                  assert (disjdom (union {{Y}} (fv_tt X0)) (cv_ec C1)) as Disj0'.
                     eapply disjdom_app_l.
                     split.
                       apply disjdom_one_2; auto.
                       apply disjdom_one_2; auto.
                   rewrite <- subst_te_plug; auto.

               simpl_env.
               rewrite close_open_tt__subst_tt; auto.
                 assert (wf_delta_subst ([(X, bind_kn)]++E1'++E2') ([(X, t2)]++dsubst1++dsubst2)) as Wfd.
                   apply F_Rsubst__wf_subst in HRsub.
                   decompose [prod] HRsub.
                   eapply dsubst_weaken_head; simpl_env; eauto using wfr_left_inv.

                 assert (wf_delta_subst ([(X, bind_kn)]++E1'++E2') ([(X, t2')]++dsubst1'++dsubst2')) as Wfd'.
                   apply F_Rsubst__wf_subst in HRsub.
                   decompose [prod] HRsub.
                   eapply dsubst_weaken_head; simpl_env; eauto using wfr_right_inv.

                 apply F_Rsubst__wf_subst in HRsub'.
                 decompose [prod] HRsub'; auto.
                 apply Frel_typ_permute_renaming_one with (E1:=E1')(E2:=E2') (X:=Y); auto.
               
                 apply contexting_regular in Hcontexting.
                 decompose [and] Hcontexting.
                 apply type_from_wf_typ in H8; auto.
Qed.

Lemma F_logical_related_congruence__tapp :
  forall e e' E D T,
  typing E D e T ->
  typing E D e' T ->
  (forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
   F_related_subst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
   F_Rsubst E rsubst dsubst dsubst' ->
   F_related_terms T rsubst dsubst dsubst' 
     (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
     (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e')))
  ) ->
  forall C1 T' T2' E' D',
  contexting E D T C1 E' D' (typ_all T2') ->
  wf_typ E' T' ->
  (typing E D e T ->
   typing E D e' T ->
    (forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
     F_related_subst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
     F_Rsubst E rsubst dsubst dsubst' ->
     F_related_terms T rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e')))
    ) ->
   forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
     F_related_subst E' D' gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
     F_Rsubst E' rsubst dsubst dsubst' ->
     F_related_terms (typ_all T2') rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (plug C1 e))))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (plug C1 e'))))
  ) ->
  forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
  F_related_subst E' D' gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
  F_Rsubst E' rsubst dsubst dsubst' ->
  F_related_terms (open_tt T2' T') rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_tapp (plug C1 e) T'))))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_tapp (plug C1 e') T')))).
Proof.
   intros e e' E D T Htyp Htyp' Hlr C1 T' T2' E' D' Hcontexting H IHHcontexting dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Hrel_sub HRsub.  
   assert (J:=Hrel_sub). apply F_related_subst__inversion in J. 
   destruct J as [[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe].
   assert (
      F_related_terms (typ_all T2') rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (plug C1 e))))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (plug C1 e'))))
     ) as FR_AllType.
      apply IHHcontexting; auto.
   destruct FR_AllType as [v [v' [Ht [Ht' [Hn [Hn' Hrel]]]]]].

   apply F_related_values_all_leq in Hrel.
   destruct Hrel as [Hv [Hv' [L Hall]]]; subst.
   unfold open_tt in Hall.

   assert (forall X,
     X `notin` dom (E') `union` fv_tt T2' ->
     wf_typ ([(X, bind_kn)]++E') (open_tt T2' X)) as w.
     apply contexting_regular in Hcontexting.
     destruct Hcontexting as [J1 [J2 [J3 [J4 [J5 J6]]]]].
     eapply wft_all_inv; eauto.

   pick fresh y.
   assert (y `notin` L) as Fr'. auto.
   destruct (@Hall y (apply_delta_subst_typ dsubst T') (apply_delta_subst_typ dsubst' T') 
                                (F_Rel T' (rho_nil++rsubst) (delta_nil++dsubst) (delta_nil++dsubst'))
                                Fr'
                   ) as [u [u' [Hn_vt2u [Hn_v't2'u' Hrel_wft]]]]; auto.
          split; try solve [apply wft_subst with (E:=E'); auto].
              assert (ddom_env E' [=] dom rsubst) as EQ.
                apply dom_rho_subst; auto.
              assert (y `notin` ddom_env E') as Fv.
                 apply dom__ddom; auto.
              rewrite EQ in Fv. auto.

   exists(u). exists (u').
       split. simpl_commut_subst in *; rewrite commut_delta_subst_open_tt with (dE:=E'); auto.
                eapply typing_tapp; eauto using wft_subst.
       split. simpl_commut_subst in *; rewrite commut_delta_subst_open_tt with (dE:=E'); auto.
                eapply typing_tapp; eauto using wft_subst.
       split.
       SCase "Norm".
       simpl_commut_subst.
       eapply m_congr_tapp; eauto.

      split.
      SCase "Norm".
      simpl_commut_subst.
      eapply m_congr_tapp; eauto.

      SCase "Frel".
      unfold open_tt.
      assert (F_related_values (open_tt_rec 0 T' T2') (rho_nil++rsubst) (delta_nil++dsubst) (delta_nil++dsubst') u u' =
                  F_related_values (open_tt_rec 0 T' T2') rsubst dsubst dsubst' u u').
         simpl. reflexivity.
      rewrite <- H0.
      apply parametricity_subst_value with
                (E:=E') (E':=@nil (atom*binding))
                (rsubst:=rsubst) (rsubst':=rho_nil)
                (k:=0)
                (t:=T2') (t2:=T')
                (X:=y) (R:=(F_Rel T' (rho_nil++rsubst) (delta_nil++dsubst) (delta_nil++dsubst')))
                ; auto.
        SSCase "wft".
          simpl_env. unfold open_tt in w. apply w; auto.

        SSCase "wft".
          simpl_env. rewrite subst_tt_intro_rec with (X:=y); auto.
          rewrite_env (map (subst_tb y T') nil ++ E').
          eapply wf_typ_subst_tb; auto.
          apply w; auto.

        SSCase "Rel__R".
        unfold F_Rel__R. split; auto.

        SSCase "fv".
        eapply m_tapp_fv with (dsubst:=dsubst) (dsubst':=dsubst') (v:=v) (v':=v'); 
           eauto using notin_fv_te_typing.

        SSCase "eq".
        apply dom_delta_subst; auto.
        apply dom_delta_subst; auto.
        apply dom_rho_subst; auto.
        SSCase "rsubst".
        eapply rsubst_weaken with (X:=y) (rsubst:=rsubst) (rsubst':=rho_nil); eauto.
          apply dom_rho_subst; auto.
        SSCase "dsubst".   
        apply dsubst_weaken with (X:=y) (dsubst:=dsubst) (dsubst':=delta_nil) (t:=(apply_delta_subst_typ dsubst T')); auto.
          apply wft_subst_closed with (E:=E') (E':=@nil (atom*binding)) (dsubst:=dsubst) ; auto.
          apply dom_delta_subst in Hwfd; auto.
        SSCase "dsubst'".
        apply dsubst_weaken with (X:=y) (dsubst:=dsubst') (dsubst':=delta_nil) (t:=(apply_delta_subst_typ dsubst' T')); auto.
          apply wft_subst_closed with (E:=E') (E':=@nil (atom*binding)) (dsubst:=dsubst'); auto.
          apply dom_delta_subst in Hwfd'; auto.
Qed.

Lemma F_logical_related_congruence__let1 :
  forall e e' E D T,
  typing E D e T ->
  typing E D e' T ->
  (forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
   F_related_subst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
   F_Rsubst E rsubst dsubst dsubst' ->
   F_related_terms T rsubst dsubst dsubst' 
     (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
     (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e')))
  ) ->
  forall L T1' E' D1' D2' D3' C1 e2 T2',
  contexting E D T C1 E' D1' (typ_bang T1') ->
  (forall x, x `notin` L -> typing ((x,bind_typ T1')::E') D2' (open_ee e2 x) T2') ->
  lenv_split E' D1' D2' D3' ->
  disjdom (fv_ee e2) (dom D) ->
  (typing E D e T ->
   typing E D e' T ->
    (forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
     F_related_subst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
     F_Rsubst E rsubst dsubst dsubst' ->
     F_related_terms T rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e')))
    ) ->
   forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
     F_related_subst E' D1' gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
     F_Rsubst E' rsubst dsubst dsubst' ->
     F_related_terms (typ_bang T1') rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (plug C1 e))))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (plug C1 e'))))
  ) ->
  forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
  F_related_subst E' D3' gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
  F_Rsubst E' rsubst dsubst dsubst' ->
  F_related_terms T2' rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_let (plug C1 e) e2))))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_let (plug C1 e') e2)))).
Proof.
   intros e e' E D T Htyp Htyp' Hlr L T1' E' D1' D2' D3' C1 e2 T2' Hcontexting H H0 H1 IHHcontexting dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Hrel_sub HRsub.  

   assert (J:=Hrel_sub). apply F_related_subst__inversion in J. 
   destruct J as [[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe].
   apply F_related_subst_split with (lE1:=D1') (lE2:=D2') in Hrel_sub; auto.
   destruct Hrel_sub as [lgsubst1 [lgsubst1' [lgsubst2 [lgsubst2' [J1 [J2 [J3 J4]]]]]]].

   assert (
      F_related_terms (typ_bang T1') rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst1 (plug C1 e))))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst'(apply_gamma_subst lgsubst1' (plug C1 e'))))
     ) as FR_T1.
    apply IHHcontexting; auto.
   destruct FR_T1 as [v1 [v'1 [Ht1 [Ht1' [Hn1 [Hn1' Hrel1]]]]]].

   apply F_related_values_bang_leq in Hrel1.
   destruct Hrel1 as [Hv1 [Hv'1 [x1 [x1' [EQ1 [EQ1' Hrel1]]]]]]; subst.

   assert (apply_delta_subst dsubst
            (apply_gamma_subst gsubst
              (apply_gamma_subst lgsubst (exp_let (plug C1 e) e2)) 
            ) =
            apply_delta_subst dsubst
            (apply_gamma_subst gsubst
              (exp_let 
                (apply_gamma_subst lgsubst1 (plug C1 e))
                (apply_gamma_subst lgsubst2 e2)
              )               
            )
          ) as EQ.
     simpl_commut_subst in *.
     rewrite lgamma_subst_split_subst' with (lgsubst1:=lgsubst1) (lgsubst2:=lgsubst2) (E:=E') (lE:=D3') (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst); auto.
     rewrite lgamma_subst_split_subst with (lgsubst1:=lgsubst1) (lgsubst2:=lgsubst2) (E:=E') (lE:=D3') (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst); auto.
     apply F_related_subst__inversion in J3.
     decompose [prod] J3; auto.
     apply F_related_subst__inversion in J4.
     decompose [prod] J4; auto.
     rewrite lgamma_subst_split_shuffle2 with (lgsubst:=lgsubst) (lgsubst1:=lgsubst1) (E:=E') (lE:=D3') ; auto.
     erewrite gamma_subst_closed_exp; eauto.
     rewrite lgamma_subst_split_shuffle1 with (lgsubst:=lgsubst) (lgsubst2:=lgsubst2) (E:=E') (lE:=D3') (e:=apply_gamma_subst lgsubst2 e2) ; auto.

     pick fresh x.
     assert (x `notin` L) as xnL. auto.
     apply H in xnL. simpl_env in xnL. 
     rewrite_env (nil++D2') in xnL. 
     apply typing_subst_closed with (dsubst:=dsubst)(gsubst:=gsubst)(lgsubst:=lgsubst2) in xnL; auto.
       simpl in xnL.
       rewrite gamma_osubst_closed_exp with 
         (e:=apply_delta_subst dsubst
            (apply_gamma_subst gsubst
              (apply_gamma_subst lgsubst2 e2))); auto.
         apply disjdom_eq with (D1:={}).
           apply disjdom_nil_1.

           apply typing_fv_ee_upper in xnL.
           simpl in xnL.
           rewrite commut_lgamma_subst_open_ee with (E:=E')(D:=D2')(gsubst:=gsubst)(dsubst:=dsubst) in xnL; auto.
           rewrite commut_gamma_subst_open_ee with (E:=E')(D:=D2')(lgsubst:=lgsubst2)(dsubst:=dsubst) in xnL; auto.
           rewrite commut_delta_subst_open_ee with (dE:=E')(dsubst:=dsubst) in xnL; auto.
           assert (J:=b7).
           apply wf_lgamma_subst__nfv with (x:=x) in J; auto.
           decompose [and] J.
           rewrite apply_gamma_subst_nfv in xnL; auto.
           rewrite apply_gamma_subst_nfv in xnL; auto.
           rewrite apply_delta_subst_nfv in xnL; auto.
           assert (J5:=@fv_ee_open_ee_sub_right 
               (apply_delta_subst dsubst
                (apply_gamma_subst gsubst
                  (apply_gamma_subst lgsubst2 e2)))
               x).
           assert (x `notin` fv_ee (apply_delta_subst dsubst
                (apply_gamma_subst gsubst
                  (apply_gamma_subst lgsubst2 e2)))) as J7.

             apply dsubst__preserves__notin_fv_ee with (E:=E'); auto.
             apply gsubst__preserves__notin_fv_ee with (E:=E')(D:=D2')(dsubst:=dsubst)(lgsubst:=lgsubst2); auto.
             apply lgsubst__preserves__notin_fv_ee with (E:=E')(D:=D2')(dsubst:=dsubst)(gsubst:=gsubst); auto.
           clear - xnL J5 J7.
           fsetdec.

       simpl. apply wf_lenv_empty.
       rewrite_env ([(x, bind_typ (apply_delta_subst_typ dsubst T1'))]++nil).
       apply wf_env_typ; auto.
         apply typing_regular in Ht1.
         decompose [and] Ht1. 
         inversion H6; auto.
   repeat(rewrite EQ). 
   assert (apply_delta_subst dsubst'
            (apply_gamma_subst gsubst'
              (apply_gamma_subst lgsubst' (exp_let (plug C1 e') e2)) 
            ) =
            apply_delta_subst dsubst'
            (apply_gamma_subst gsubst'
              (exp_let 
                (apply_gamma_subst lgsubst1' (plug C1 e'))
                (apply_gamma_subst lgsubst2' e2)
              )               
            )
          ) as EQ'.
     simpl_commut_subst in *.
     rewrite lgamma_subst_split_subst' with (lgsubst1:=lgsubst1') (lgsubst2:=lgsubst2') (E:=E') (lE:=D3') (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst'); auto.
     rewrite lgamma_subst_split_subst with (lgsubst1:=lgsubst1') (lgsubst2:=lgsubst2') (E:=E') (lE:=D3') (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst'); auto.
     apply F_related_subst__inversion in J3.
     decompose [prod] J3; auto.
     apply F_related_subst__inversion in J4.
     decompose [prod] J4; auto.
     rewrite lgamma_subst_split_shuffle2 with (lgsubst:=lgsubst') (lgsubst1:=lgsubst1') (E:=E') (lE:=D3') ; auto.
     erewrite gamma_subst_closed_exp; eauto.
     rewrite lgamma_subst_split_shuffle1 with (lgsubst:=lgsubst') (lgsubst2:=lgsubst2') (E:=E') (lE:=D3') (e:=apply_gamma_subst lgsubst2' e2) ; auto.

     pick fresh x.
     assert (x `notin` L) as xnL. auto.
     apply H in xnL. simpl_env in xnL.
     rewrite_env (nil++D2') in xnL.
     apply typing_subst_closed with (dsubst:=dsubst')(gsubst:=gsubst')(lgsubst:=lgsubst2') in xnL; auto.
       simpl in xnL.
       rewrite gamma_osubst_closed_exp with 
         (e:=apply_delta_subst dsubst'
            (apply_gamma_subst gsubst'
              (apply_gamma_subst lgsubst2' e2))); auto.
         apply disjdom_eq with (D1:={}).
           apply disjdom_nil_1.

           apply typing_fv_ee_upper in xnL.
           simpl in xnL.
           rewrite commut_lgamma_subst_open_ee with (E:=E')(D:=D2')(gsubst:=gsubst')(dsubst:=dsubst') in xnL; auto.
           rewrite commut_gamma_subst_open_ee with (E:=E')(D:=D2')(lgsubst:=lgsubst2')(dsubst:=dsubst') in xnL; auto.
           rewrite commut_delta_subst_open_ee with (dE:=E')(dsubst:=dsubst') in xnL; auto.
           assert (J:=b6).
           apply wf_lgamma_subst__nfv with (x:=x) in J; auto.
           decompose [and] J.
           rewrite apply_gamma_subst_nfv in xnL; auto.
           rewrite apply_gamma_subst_nfv in xnL; auto.
           rewrite apply_delta_subst_nfv in xnL; auto.
           assert (J5:=@fv_ee_open_ee_sub_right 
               (apply_delta_subst dsubst'
                (apply_gamma_subst gsubst'
                  (apply_gamma_subst lgsubst2' e2)))
               x).
           assert (x `notin` fv_ee (apply_delta_subst dsubst'
                (apply_gamma_subst gsubst'
                  (apply_gamma_subst lgsubst2' e2)))) as J7.

             apply dsubst__preserves__notin_fv_ee with (E:=E'); auto.
             apply gsubst__preserves__notin_fv_ee with (E:=E')(D:=D2')(dsubst:=dsubst')(lgsubst:=lgsubst2'); auto.
             apply lgsubst__preserves__notin_fv_ee with (E:=E')(D:=D2')(dsubst:=dsubst')(gsubst:=gsubst'); auto.
           clear - xnL J5 J7.
           fsetdec.

       simpl. apply wf_lenv_empty.
       rewrite_env ([(x, bind_typ (apply_delta_subst_typ dsubst' T1'))]++nil).
       apply wf_env_typ; auto.
         apply typing_regular in Ht1'.
         decompose [and] Ht1'. 
         inversion H6; auto.
   repeat(rewrite EQ').

   pick fresh y.
   assert (y `notin` L) as Fry. auto.
   assert (wf_typ ([(y, bind_typ T1')]++E') T2') as WFT2. 
     apply H in Fry.
     apply typing_regular in Fry.
     decompose [and] Fry; auto.
   assert (wf_typ E' T1') as WFT1. 
     apply contexting_regular in Hcontexting.
     decompose [and] Hcontexting.
     inversion H8; auto.
   assert (wf_lgamma_subst E' D2' dsubst gsubst lgsubst2) as Wflg2.
     apply F_related_subst__inversion in J4. decompose [prod] J4; auto.
     assert (wf_lgamma_subst E' D2' dsubst' gsubst' lgsubst2') as Wflg2'.
     apply F_related_subst__inversion in J4. decompose [prod] J4; auto.
   assert (typing empty lempty x1 (apply_delta_subst_typ dsubst T1')) as Typing1.
     apply preservation_normalization with (v:=exp_bang x1) in Ht1; auto.
     simpl_commut_subst in Ht1. inversion Ht1; subst; auto.             
   assert (typing empty lempty x1' (apply_delta_subst_typ dsubst' T1')) as Typing1'.
     apply preservation_normalization with (v:=exp_bang x1') in Ht1'; auto.
     simpl_commut_subst in Ht1'. inversion Ht1'; subst; auto.             
   assert (expr (exp_let (plug C1 e) e2)) as Expr2.
     assert (typing E' D3' (exp_let  (plug C1 e) e2) T2') as Typing2.
        apply typing_let with (L:=L)(D1:=D1')(D2:=D2')(T1:=T1'); auto.
          apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.
      apply typing_regular in Typing2.
      decompose [and] Typing2; auto.
   assert (expr (exp_let (plug C1 e') e2)) as Expr2'.
     assert (typing E' D3' (exp_let  (plug C1 e') e2) T2') as Typing2'.
        apply typing_let with (L:=L)(D1:=D1')(D2:=D2')(T1:=T1'); auto.
          apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.
      apply typing_regular in Typing2'.
      decompose [and] Typing2'; auto.
   apply H in Fry. simpl_env in Fry.
   apply parametricity with (dsubst:=dsubst) (dsubst':=dsubst') 
                         (gsubst:=[(y,x1)]++gsubst)
                         (gsubst':=[(y,x1')]++gsubst') 
                         (lgsubst:=lgsubst2)
                         (lgsubst':=lgsubst2') 
                         (rsubst:=rsubst) in Fry; auto.
         assert (
           apply_delta_subst dsubst (apply_gamma_subst ([(y,x1)]++gsubst) (apply_gamma_subst lgsubst2 (open_ee e2 y))) =
           apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst2 (subst_ee y x1 (open_ee e2 y))))
            ) as Heq1. simpl. 
           rewrite swap_subst_ee_lgsubst with (E:=E')(D:=D2')(dsubst:=dsubst)(lgsubst:=lgsubst2)(gsubst:=gsubst)(t:=apply_delta_subst_typ dsubst T1'); auto.
             apply wf_lgamma_subst__nfv with (x:=y) in Wflg2; auto.
         assert (
          apply_delta_subst dsubst' (apply_gamma_subst ([(y,x1')]++gsubst') (apply_gamma_subst lgsubst2' (open_ee e2 y))) =
          apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst2' (subst_ee y x1' (open_ee e2 y))))
            ) as Heq2.  simpl.
           rewrite swap_subst_ee_lgsubst with (E:=E')(D:=D2')(dsubst:=dsubst')(lgsubst:=lgsubst2')(gsubst:=gsubst')(t:=apply_delta_subst_typ dsubst' T1'); auto.
             apply wf_lgamma_subst__nfv with (x:=y) in Wflg2'; auto.
         rewrite Heq1 in Fry. rewrite Heq2 in Fry. clear Heq1 Heq2.
         destruct Fry as [v2 [v2' [Ht2 [Ht2' [[Hbrc2 Hv2] [[Hbrc2' Hv2'] Hrel2]]]]]].
         exists (v2). exists (v2').
         split.
           SCase "typing".
           simpl_commut_subst. simpl_commut_subst in Ht1.
           apply typing_let with (L:=L `union` dom (gsubst) `union` dom (lgsubst2) `union` dom E)(D1:=lempty)(D2:=lempty)(T1:=apply_delta_subst_typ dsubst T1'); auto.
             intros x Hfv.
             assert (x `notin` L) as Htyping2; auto.
             apply H in Htyping2. simpl_env in Htyping2.
             apply m_typing_subst_typ_closed with (E:=E') (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst2) in Htyping2; auto.
         split.
           SCase "typing".
           simpl_commut_subst. simpl_commut_subst in Ht1'.
           apply typing_let with (L:=L `union` dom (gsubst') `union` dom (lgsubst2') `union` dom E)(D1:=lempty)(D2:=lempty)(T1:=apply_delta_subst_typ dsubst' T1'); auto.
             intros x Hfv.
             assert (x `notin` L) as Htyping2; auto.
             apply H in Htyping2. simpl_env in Htyping2. 
             apply m_typing_subst_typ_closed with (E:=E') (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst2') in Htyping2; auto.
         split.
           SSSCase "norm".
           split; auto.
           apply bigstep_red__trans with (e':=(apply_delta_subst dsubst (apply_gamma_subst gsubst  (apply_gamma_subst lgsubst2 (subst_ee y x1 (open_ee e2 y)))))); auto.
             simpl_commut_subst.
             apply bigstep_red__trans with (e':=exp_let (exp_bang x1) (apply_delta_subst dsubst (apply_gamma_subst gsubst  (apply_gamma_subst lgsubst2 e2)))); auto.
               destruct Hn1 as [Hbrc1 Hx1].
               apply _congr_let_arg; auto.
                 apply expr_preserved_under_lgamma_subst with (E:=E')(D:=D3')(dsubst:=dsubst)(gsubst:=gsubst)(lgsubst:=lgsubst) in Expr2; auto.
                 apply expr_preserved_under_gamma_subst with (E:=E')(D:=D3')(dsubst:=dsubst)(gsubst:=gsubst)(lgsubst:=lgsubst) in Expr2; auto.
                 apply expr_preserved_under_delta_subst with (E:=E')(dsubst:=dsubst) in Expr2; auto.
                 rewrite EQ in Expr2. simpl_commut_subst in Expr2; auto.

                 apply bigstep_red_trans with (e':=(apply_delta_subst dsubst (apply_gamma_subst gsubst  (apply_gamma_subst lgsubst2 (subst_ee y x1 (open_ee e2 y)))))); auto.
                   apply m_red_bang_subst with (D2:=D2')(lgsubst2:=lgsubst2)(E:=E')(T1:=T1')(T2:=T2')(L:=L); auto.

         split; auto.
           SSSCase "norm".
           split; auto.
           apply bigstep_red__trans with (e':=(apply_delta_subst dsubst' (apply_gamma_subst gsubst'  (apply_gamma_subst lgsubst2' (subst_ee y x1' (open_ee e2 y)))))); auto.
             simpl_commut_subst.
             apply bigstep_red__trans with (e':=exp_let (exp_bang x1') (apply_delta_subst dsubst' (apply_gamma_subst gsubst'  (apply_gamma_subst lgsubst2' e2)))); auto.
               destruct Hn1' as [Hbrc1' Hx1'].
               apply _congr_let_arg; auto.
                 apply expr_preserved_under_lgamma_subst with (E:=E')(D:=D3')(dsubst:=dsubst')(gsubst:=gsubst')(lgsubst:=lgsubst') in Expr2'; auto.
                 apply expr_preserved_under_gamma_subst with (E:=E')(D:=D3')(dsubst:=dsubst')(gsubst:=gsubst')(lgsubst:=lgsubst') in Expr2'; auto.
                 apply expr_preserved_under_delta_subst with (E:=E')(dsubst:=dsubst') in Expr2'; auto.
                 rewrite EQ' in Expr2'. simpl_commut_subst in Expr2'; auto.

                 apply bigstep_red_trans with (e':=(apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst2' (subst_ee y x1' (open_ee e2 y)))))); auto.
                   apply m_red_bang_subst with (D2:=D2')(lgsubst2:=lgsubst2')(E:=E')(T1:=T1')(T2:=T2')(L:=L); auto.
           SSSCase "Fsubst".
           apply F_related_subst_typ; auto.
           destruct Hrel1 as [u1 [u1' [Hx1u1 [Hx1'u1' Hrel1]]]].
           exists (u1). exists (u1'). split; auto.
           SSSCase "FRsubst".
           apply F_Rsubst_typ; auto.
Qed.

Lemma F_logical_related_congruence__let2_free :
  forall e e' E D T,
  typing E D e T ->
  typing E D e' T ->
  (forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
   F_related_subst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
   F_Rsubst E rsubst dsubst dsubst' ->
   F_related_terms T rsubst dsubst dsubst' 
     (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
     (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e')))
  ) ->
  forall L T1' e1 C2 T2' E' D1' D2' D3',
  typing E' D1' e1 (typ_bang T1') ->
  (forall x, x `notin` L -> contexting E D T (open_ec C2 x) ((x,bind_typ T1')::E') D2' T2') ->
  (forall x, x `notin` L ->
   typing E D e T ->
   typing E D e' T ->
    (forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
     F_related_subst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
     F_Rsubst E rsubst dsubst dsubst' ->
     F_related_terms T rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e')))
    ) ->
   forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
     F_related_subst ((x,bind_typ T1')::E') D2' gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
     F_Rsubst ((x,bind_typ T1')::E') rsubst dsubst dsubst' ->
     F_related_terms T2' rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (plug (open_ec C2 x) e))))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (plug (open_ec C2 x) e'))))
  ) ->
  lenv_split E' D1' D2' D3' ->
  disjdom (fv_ee e1) (dom D) ->
  forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
  F_related_subst E' D3' gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
  F_Rsubst E' rsubst dsubst dsubst' ->
  F_related_terms T2' rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_let e1 (plug C2 (shift_ee e))))))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_let e1 (plug C2 (shift_ee e')))))).
Proof.
   intros e e' E D T Htyp Htyp' Hlr L T1' e1 C2 T2' E' D1' D2' D3' H H1 H2 H3 H4 dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Hrel_sub HRsub.  

   assert (J:=Hrel_sub). apply F_related_subst__inversion in J. 
   destruct J as [[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe].
   apply F_related_subst_split with (lE1:=D1') (lE2:=D2') in Hrel_sub; auto.
   destruct Hrel_sub as [lgsubst1 [lgsubst1' [lgsubst2 [lgsubst2' [J1 [J2 [J3 J4]]]]]]].

   assert (
      F_related_terms (typ_bang T1') rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst1 e1)))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst'(apply_gamma_subst lgsubst1' e1)))
     ) as FR_T1.
     apply parametricity with (E:=E') (lE:=D1') ; auto.
   destruct FR_T1 as [v1 [v'1 [Ht1 [Ht1' [Hn1 [Hn1' Hrel1]]]]]].

   apply F_related_values_bang_leq in Hrel1.
   destruct Hrel1 as [Hv1 [Hv'1 [x1 [x1' [EQ1 [EQ1' Hrel1]]]]]]; subst.

   rewrite <- shift_ee_expr with (e:=e); auto.
   rewrite <- shift_ee_expr with (e:=e'); auto.
   assert (apply_delta_subst dsubst
            (apply_gamma_subst gsubst
              (apply_gamma_subst lgsubst (exp_let e1 (plug C2 e))) 
            ) =
            apply_delta_subst dsubst
            (apply_gamma_subst gsubst
              (exp_let 
                (apply_gamma_subst lgsubst1 e1)
                (apply_gamma_subst lgsubst2 (plug C2 e))
              )               
            )
          ) as EQ.
     simpl_commut_subst in *.
     rewrite lgamma_subst_split_subst' with (lgsubst1:=lgsubst1) (lgsubst2:=lgsubst2) (E:=E') (lE:=D3') (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst); auto.
     rewrite lgamma_subst_split_subst with (lgsubst1:=lgsubst1) (lgsubst2:=lgsubst2) (E:=E') (lE:=D3') (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst); auto.
     apply F_related_subst__inversion in J3.
     decompose [prod] J3; auto.
     apply F_related_subst__inversion in J4.
     decompose [prod] J4; auto.
     rewrite lgamma_subst_split_shuffle2 with (lgsubst:=lgsubst) (lgsubst1:=lgsubst1) (E:=E') (lE:=D3') ; auto.
     erewrite gamma_subst_closed_exp; eauto.
     rewrite lgamma_subst_split_shuffle1 with (lgsubst:=lgsubst) (lgsubst2:=lgsubst2) (E:=E') (lE:=D3') (e:=apply_gamma_subst lgsubst2 (plug C2 e)) ; auto.

     pick fresh x.
      assert (x `notin` L) as xnL. auto.
     apply H1 in xnL. simpl_env in xnL. 
     apply contexting_plug_typing with (e:=e) in xnL; auto.
     rewrite_env (nil++D2') in xnL. 
     apply typing_subst_closed with (dsubst:=dsubst)(gsubst:=gsubst)(lgsubst:=lgsubst2) in xnL; auto.
       simpl in xnL.
       rewrite gamma_osubst_closed_exp with 
         (e:=apply_delta_subst dsubst
            (apply_gamma_subst gsubst
              (apply_gamma_subst lgsubst2 (plug C2 e)))); auto.
         apply disjdom_eq with (D1:={}).
           apply disjdom_nil_1.

           apply typing_fv_ee_upper in xnL.
           simpl in xnL.
           rewrite <- open_ee_var_plug in xnL; auto.
           rewrite commut_lgamma_subst_open_ee with (E:=E')(D:=D2')(gsubst:=gsubst)(dsubst:=dsubst) in xnL; auto.
           rewrite commut_gamma_subst_open_ee with (E:=E')(D:=D2')(lgsubst:=lgsubst2)(dsubst:=dsubst) in xnL; auto.
           rewrite commut_delta_subst_open_ee with (dE:=E')(dsubst:=dsubst) in xnL; auto.
           assert (J:=b7).
           apply wf_lgamma_subst__nfv with (x:=x) in J; auto.
           decompose [and] J.
           rewrite apply_gamma_subst_nfv in xnL; auto.
           rewrite apply_gamma_subst_nfv in xnL; auto.
           rewrite apply_delta_subst_nfv in xnL; auto.
           assert (J5:=@fv_ee_open_ee_sub_right 
               (apply_delta_subst dsubst
                (apply_gamma_subst gsubst
                  (apply_gamma_subst lgsubst2 (plug C2 e))))
               x).
           assert (x `notin` fv_ee (apply_delta_subst dsubst
                (apply_gamma_subst gsubst
                  (apply_gamma_subst lgsubst2 (plug C2 e))))) as J7.
             assert (J8:=@fv_ee_plug C2 e). 
             assert (x `notin` fv_ec C2 `union` fv_ee e) as J9.
               destruct_notin.
               clear - NotInTac4 NotInTac25. fsetdec.
             apply dsubst__preserves__notin_fv_ee with (E:=E'); auto.
             apply gsubst__preserves__notin_fv_ee with (E:=E')(D:=D2')(dsubst:=dsubst)(lgsubst:=lgsubst2); auto.
             apply lgsubst__preserves__notin_fv_ee with (E:=E')(D:=D2')(dsubst:=dsubst)(gsubst:=gsubst); auto.

           clear - xnL J5 J7.
           fsetdec.

       simpl. apply wf_lenv_empty.
       rewrite_env ([(x, bind_typ (apply_delta_subst_typ dsubst T1'))]++nil).
       apply wf_env_typ; auto.
         apply typing_regular in Ht1.
         decompose [and] Ht1. 
         inversion H8; auto.
   repeat(rewrite EQ). 
   assert (apply_delta_subst dsubst'
            (apply_gamma_subst gsubst'
              (apply_gamma_subst lgsubst' (exp_let e1 (plug C2 e'))) 
            ) =
            apply_delta_subst dsubst'
            (apply_gamma_subst gsubst'
              (exp_let 
                (apply_gamma_subst lgsubst1' e1)
                (apply_gamma_subst lgsubst2' (plug C2 e'))
              )               
            )
          ) as EQ'.
     simpl_commut_subst in *.
     rewrite lgamma_subst_split_subst' with (lgsubst1:=lgsubst1') (lgsubst2:=lgsubst2') (E:=E') (lE:=D3') (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst'); auto.
     rewrite lgamma_subst_split_subst with (lgsubst1:=lgsubst1') (lgsubst2:=lgsubst2') (E:=E') (lE:=D3') (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst'); auto.
     apply F_related_subst__inversion in J3.
     decompose [prod] J3; auto.
     apply F_related_subst__inversion in J4.
     decompose [prod] J4; auto.
     rewrite lgamma_subst_split_shuffle2 with (lgsubst:=lgsubst') (lgsubst1:=lgsubst1') (E:=E') (lE:=D3') ; auto.
     erewrite gamma_subst_closed_exp; eauto.
     rewrite lgamma_subst_split_shuffle1 with (lgsubst:=lgsubst') (lgsubst2:=lgsubst2') (E:=E') (lE:=D3') (e:=apply_gamma_subst lgsubst2' (plug C2 e')) ; auto.

     pick fresh x.
     assert (x `notin` L) as xnL. auto.
     apply H1 in xnL. simpl_env in xnL. 
     apply contexting_plug_typing with (e:=e') in xnL; auto.
     rewrite_env (nil++D2') in xnL. 
     apply typing_subst_closed with (dsubst:=dsubst')(gsubst:=gsubst')(lgsubst:=lgsubst2') in xnL; auto.
       simpl in xnL.
       rewrite gamma_osubst_closed_exp with 
         (e:=apply_delta_subst dsubst'
            (apply_gamma_subst gsubst'
              (apply_gamma_subst lgsubst2' (plug C2 e')))); auto.
         apply disjdom_eq with (D1:={}).
           apply disjdom_nil_1.

           apply typing_fv_ee_upper in xnL.
           simpl in xnL.
           rewrite <- open_ee_var_plug in xnL; auto.
           rewrite commut_lgamma_subst_open_ee with (E:=E')(D:=D2')(gsubst:=gsubst')(dsubst:=dsubst') in xnL; auto.
           rewrite commut_gamma_subst_open_ee with (E:=E')(D:=D2')(lgsubst:=lgsubst2')(dsubst:=dsubst') in xnL; auto.
           rewrite commut_delta_subst_open_ee with (dE:=E')(dsubst:=dsubst') in xnL; auto.
           assert (J:=b6).
           apply wf_lgamma_subst__nfv with (x:=x) in J; auto.
           decompose [and] J.
           rewrite apply_gamma_subst_nfv in xnL; auto.
           rewrite apply_gamma_subst_nfv in xnL; auto.
           rewrite apply_delta_subst_nfv in xnL; auto.
           assert (J5:=@fv_ee_open_ee_sub_right 
               (apply_delta_subst dsubst'
                (apply_gamma_subst gsubst'
                  (apply_gamma_subst lgsubst2' (plug C2 e'))))
               x).
           assert (x `notin` fv_ee (apply_delta_subst dsubst'
                (apply_gamma_subst gsubst'
                  (apply_gamma_subst lgsubst2' (plug C2 e'))))) as J7.

             assert (J8:=@fv_ee_plug C2 e'). 
             assert (x `notin` fv_ec C2 `union` fv_ee e') as J9.
               destruct_notin.
               clear - NotInTac5 NotInTac25. fsetdec.
             apply dsubst__preserves__notin_fv_ee with (E:=E'); auto.
             apply gsubst__preserves__notin_fv_ee with (E:=E')(D:=D2')(dsubst:=dsubst')(lgsubst:=lgsubst2'); auto.
             apply lgsubst__preserves__notin_fv_ee with (E:=E')(D:=D2')(dsubst:=dsubst')(gsubst:=gsubst'); auto.

           clear - xnL J5 J7.
           fsetdec.

       simpl. apply wf_lenv_empty.
       rewrite_env ([(x, bind_typ (apply_delta_subst_typ dsubst' T1'))]++nil).
       apply wf_env_typ; auto.
         apply typing_regular in Ht1'.
         decompose [and] Ht1'. 
         inversion H8; auto.
   repeat(rewrite EQ').

   pick fresh z.
   assert (z `notin` L) as Fry. auto.
   assert (wf_typ ([(z, bind_typ T1')]++E') T2') as WFT2. 
     apply H1 in Fry.
     apply contexting_regular in Fry.
     decompose [and] Fry; auto.
   assert (wf_typ E' T1') as WFT1. 
     apply typing_regular in H.
     decompose [and] H.
     inversion H8; auto.
   assert (wf_lgamma_subst E' D2' dsubst gsubst lgsubst2) as Wflg2.
     apply F_related_subst__inversion in J4. decompose [prod] J4; auto.
     assert (wf_lgamma_subst E' D2' dsubst' gsubst' lgsubst2') as Wflg2'.
     apply F_related_subst__inversion in J4. decompose [prod] J4; auto.
   assert (typing empty lempty x1 (apply_delta_subst_typ dsubst T1')) as Typing1.
     apply preservation_normalization with (v:=exp_bang x1) in Ht1; auto.
     simpl_commut_subst in Ht1. inversion Ht1; subst; auto.             
   assert (typing empty lempty x1' (apply_delta_subst_typ dsubst' T1')) as Typing1'.
     apply preservation_normalization with (v:=exp_bang x1') in Ht1'; auto.
     simpl_commut_subst in Ht1'. inversion Ht1'; subst; auto.             
   assert (expr (exp_let e1 (plug C2 e))) as Expr2.
     assert (typing E' D3' (exp_let e1 (plug C2 e)) T2') as Typing2.
        apply typing_let with (L:=L `union` cv_ec C2)(D1:=D1')(D2:=D2')(T1:=T1'); auto.
          intros x xn. 
          assert (x `notin` L) as xnL. auto.
          apply H1 in xnL. 
           rewrite open_ee_var_plug with (e:=e); auto.
          apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.
      apply typing_regular in Typing2.
      decompose [and] Typing2; auto.
   assert (expr (exp_let e1 (plug C2 e'))) as Expr2'.
     assert (typing E' D3' (exp_let e1 (plug C2 e')) T2') as Typing2'.
        apply typing_let with (L:=L `union` cv_ec C2)(D1:=D1')(D2:=D2')(T1:=T1'); auto.
          intros x xn. 
          assert (x `notin` L) as xnL. auto.
          apply H1 in xnL. 
          rewrite open_ee_var_plug with (e:=e'); auto.
          apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.
      apply typing_regular in Typing2'.
      decompose [and] Typing2'; auto.
   apply H2 with (dsubst:=dsubst) (dsubst':=dsubst') 
                         (gsubst:=[(z,x1)]++gsubst)
                         (gsubst':=[(z,x1')]++gsubst') 
                         (lgsubst:=lgsubst2)
                         (lgsubst':=lgsubst2') 
                         (rsubst:=rsubst) in Fry; auto.
         assert (
           apply_delta_subst dsubst (apply_gamma_subst ([(z,x1)]++gsubst) (apply_gamma_subst lgsubst2 (open_ee (plug C2 e) z))) =
           apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst2 (subst_ee z x1 (open_ee (plug C2 e) z))))
            ) as Heq1. simpl.
           rewrite swap_subst_ee_lgsubst with (E:=E')(D:=D2')(dsubst:=dsubst)(lgsubst:=lgsubst2)(gsubst:=gsubst)(t:=apply_delta_subst_typ dsubst T1'); auto.
             apply wf_lgamma_subst__nfv with (x:=z) in Wflg2; auto.
         assert (
          apply_delta_subst dsubst' (apply_gamma_subst ([(z,x1')]++gsubst') (apply_gamma_subst lgsubst2' (open_ee (plug C2 e') z))) =
          apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst2' (subst_ee z x1' (open_ee (plug C2 e') z))))
            ) as Heq2.  simpl.
           rewrite swap_subst_ee_lgsubst with (E:=E')(D:=D2')(dsubst:=dsubst')(lgsubst:=lgsubst2')(gsubst:=gsubst')(t:=apply_delta_subst_typ dsubst' T1'); auto.
             apply wf_lgamma_subst__nfv with (x:=z) in Wflg2'; auto.
         rewrite <- open_ee_var_plug in Fry; auto.
         rewrite <- open_ee_var_plug in Fry; auto.
         rewrite Heq1 in Fry. rewrite Heq2 in Fry. clear Heq1 Heq2.
         destruct Fry as [v2 [v2' [Ht2 [Ht2' [[Hbrc2 Hv2] [[Hbrc2' Hv2'] Hrel2]]]]]].
         exists (v2). exists (v2').
         split.
           SCase "typing".
           simpl_commut_subst. simpl_commut_subst in Ht1.
           apply typing_let with (L:=L `union` cv_ec C2 `union` dom (gsubst) `union` dom (lgsubst2) `union` dom E)(D1:=lempty)(D2:=lempty)(T1:=apply_delta_subst_typ dsubst T1'); auto.
             intros x Hfv.
             assert (x `notin` L) as Htyping2; auto.
             apply H1 in Htyping2.
             apply contexting_plug_typing with (e:=e) in Htyping2; auto. 
             simpl_env in Htyping2. 
             rewrite <- open_ee_var_plug in Htyping2; auto.
             apply m_typing_subst_typ_closed with (E:=E') (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst2) in Htyping2; auto.
         split.
           SCase "typing".
           simpl_commut_subst. simpl_commut_subst in Ht1'.
           apply typing_let with (L:=L `union` cv_ec C2 `union` dom (gsubst') `union` dom (lgsubst2') `union` dom E)(D1:=lempty)(D2:=lempty)(T1:=apply_delta_subst_typ dsubst' T1'); auto.
             intros x Hfv.
             assert (x `notin` L) as Htyping2; auto.
             apply H1 in Htyping2. simpl_env in Htyping2. 
             apply contexting_plug_typing with (e:=e') in Htyping2; auto. 
             simpl_env in Htyping2. 
             rewrite <- open_ee_var_plug in Htyping2; auto.
             apply m_typing_subst_typ_closed with (E:=E') (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst2') in Htyping2; auto.
         split.
           SSSCase "norm".
           split; auto.
           apply bigstep_red__trans with (e':=(apply_delta_subst dsubst (apply_gamma_subst gsubst  (apply_gamma_subst lgsubst2 (subst_ee z x1 (open_ee (plug C2 e) z)))))); auto.
             simpl_commut_subst.
             apply bigstep_red__trans with (e':=exp_let (exp_bang x1) (apply_delta_subst dsubst (apply_gamma_subst gsubst  (apply_gamma_subst lgsubst2 (plug C2 e))))); auto.
               destruct Hn1 as [Hbrc1 Hx1].
               apply _congr_let_arg; auto.
                 apply expr_preserved_under_lgamma_subst with (E:=E')(D:=D3')(dsubst:=dsubst)(gsubst:=gsubst)(lgsubst:=lgsubst) in Expr2; auto.
                 apply expr_preserved_under_gamma_subst with (E:=E')(D:=D3')(dsubst:=dsubst)(gsubst:=gsubst)(lgsubst:=lgsubst) in Expr2; auto.
                 apply expr_preserved_under_delta_subst with (E:=E')(dsubst:=dsubst) in Expr2; auto.
                 rewrite EQ in Expr2. simpl_commut_subst in Expr2; auto.

                 apply bigstep_red_trans with (e':=(apply_delta_subst dsubst (apply_gamma_subst gsubst  (apply_gamma_subst lgsubst2 (subst_ee z x1 (open_ee (plug C2 e) z)))))); auto.
                   assert (J8:=@fv_ee_plug C2 e). 
                   assert (z `notin` fv_ec C2 `union` fv_ee e) as J9.
                     destruct_notin.
                     clear - NotInTac4 NotInTac25. fsetdec.
                   apply m_red_bang_subst with (D2:=D2')(lgsubst2:=lgsubst2)(E:=E')(T1:=T1')(T2:=T2')(L:=L `union` cv_ec C2); auto.
                     intros x xn.
                     assert (x `notin` L) as xnL. auto.
                     apply H1 in xnL.                     
                     apply contexting_plug_typing with (e:=e) in xnL; auto. 
                     simpl_env in xnL.
                     rewrite <- open_ee_var_plug in xnL; auto.

         split; auto.
           SSSCase "norm".
           split; auto.
           apply bigstep_red__trans with (e':=(apply_delta_subst dsubst' (apply_gamma_subst gsubst'  (apply_gamma_subst lgsubst2' (subst_ee z x1' (open_ee (plug C2 e') z)))))); auto.
             simpl_commut_subst.
             apply bigstep_red__trans with (e':=exp_let (exp_bang x1') (apply_delta_subst dsubst' (apply_gamma_subst gsubst'  (apply_gamma_subst lgsubst2' (plug C2 e'))))); auto.
               destruct Hn1' as [Hbrc1' Hx1'].
               apply _congr_let_arg; auto.
                 apply expr_preserved_under_lgamma_subst with (E:=E')(D:=D3')(dsubst:=dsubst')(gsubst:=gsubst')(lgsubst:=lgsubst') in Expr2'; auto.
                 apply expr_preserved_under_gamma_subst with (E:=E')(D:=D3')(dsubst:=dsubst')(gsubst:=gsubst')(lgsubst:=lgsubst') in Expr2'; auto.
                 apply expr_preserved_under_delta_subst with (E:=E')(dsubst:=dsubst') in Expr2'; auto.
                 rewrite EQ' in Expr2'. simpl_commut_subst in Expr2'; auto.

                 apply bigstep_red_trans with (e':=(apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst2' (subst_ee z x1' (open_ee (plug C2 e') z)))))); auto.
                   assert (J8:=@fv_ee_plug C2 e'). 
                   assert (z `notin` fv_ec C2 `union` fv_ee e') as J9.
                     destruct_notin.
                     clear - NotInTac5 NotInTac25. fsetdec.
                   apply m_red_bang_subst with (D2:=D2')(lgsubst2:=lgsubst2')(E:=E')(T1:=T1')(T2:=T2')(L:=L `union` cv_ec C2); auto.
                     intros x xn.
                     assert (x `notin` L) as xnL. auto.
                     apply H1 in xnL.                     
                     apply contexting_plug_typing with (e:=e') in xnL; auto. 
                     simpl_env in xnL.
                     rewrite <- open_ee_var_plug in xnL; auto.

           SSSCase "Fsubst".
           simpl_env.
           apply F_related_subst_typ; auto.
           destruct Hrel1 as [u1 [u1' [Hx1u1 [Hx1'u1' Hrel1]]]].
           exists (u1). exists (u1'). split; auto.
           SSSCase "FRsubst".
           simpl_env.
           apply F_Rsubst_typ; auto.
Qed.

Lemma F_logical_related_congruence__let2_capture :
  forall e e' E D T,
  typing E D e T ->
  typing E D e' T ->
  (forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
   F_related_subst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
   F_Rsubst E rsubst dsubst dsubst' ->
   F_related_terms T rsubst dsubst dsubst' 
     (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
     (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e')))
  ) ->
  forall y T1' e1 C2 T2' E' D1' D2' D3',
  typing (env_remove (y,bind_typ T1') E') D1' e1 (typ_bang T1') ->
  binds y (bind_typ T1') E' ->
  y `notin` union (dom D) (cv_ec C2) ->
  contexting E D T C2 E' D2' T2' ->
  lenv_split (env_remove (y,bind_typ T1') E') D1' D2' D3' ->
  disjdom (fv_ee e1) (dom D) ->
  (typing E D e T ->
   typing E D e' T ->
    (forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
     F_related_subst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
     F_Rsubst E rsubst dsubst dsubst' ->
     F_related_terms T rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e')))
    ) ->
   forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
     F_related_subst E' D2' gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
     F_Rsubst E' rsubst dsubst dsubst' ->
     F_related_terms T2' rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (plug C2 e))))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (plug C2 e'))))
  ) ->
  forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst,
  F_related_subst (env_remove (y,bind_typ T1') E') D3' gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
  F_Rsubst (env_remove (y,bind_typ T1') E') rsubst dsubst dsubst' ->
  F_related_terms T2' rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_let e1 (plug (close_ec C2 y) (close_ee (shift_ee e) y))))))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_let e1 (plug (close_ec C2 y) (close_ee (shift_ee e') y)))))).
Proof.
   intros e e' E D T Htyp Htyp' Hlr y T1' e1 C2  T2' E' D1' D2' D3' H H0 H1 Hcontexting H2 H3 IHHcontexting dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Hrel_sub HRsub.  
   assert (J:=Hrel_sub). apply F_related_subst__inversion in J. 
   destruct J as [[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe].
   apply F_related_subst_split with (lE1:=D1') (lE2:=D2') in Hrel_sub; auto.
   destruct Hrel_sub as [lgsubst1 [lgsubst1' [lgsubst2 [lgsubst2' [J1 [J2 [J3 J4]]]]]]].

   assert (
      F_related_terms (typ_bang T1') rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst1 e1)))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst'(apply_gamma_subst lgsubst1' e1)))
     ) as FR_T1.
     apply parametricity with (E:=env_remove (y,bind_typ T1') E') (lE:=D1') ; auto.
   destruct FR_T1 as [v1 [v'1 [Ht1 [Ht1' [Hn1 [Hn1' Hrel1]]]]]].

   apply F_related_values_bang_leq in Hrel1.
   destruct Hrel1 as [Hv1 [Hv'1 [x1 [x1' [EQ1 [EQ1' Hrel1]]]]]]; subst.

    assert (wf_typ E' T2') as WFT'. 
      apply contexting_regular in Hcontexting.
      decompose [and] Hcontexting; auto.
    assert (Fry := @IHHcontexting Htyp Htyp' Hlr).
    assert (wf_env E') as Wfe'.
      apply contexting_regular in Hcontexting.
      decompose [and] Hcontexting; auto.
    assert (EQ1:=@env_remove_typ_inv E' y T1'  Wfe' H0).
    destruct EQ1 as [E1' [E2' [EQ1' [EQ2' Sub]]]]; subst.
    rewrite EQ1' in *.

    assert (EQ:=Hwflg).
    apply wf_lgsubst_app_inv in EQ.
    destruct EQ as [dsubst1 [dsubst2 [gsubst1 [gsubst2 [dEQ1 [dEQ2 [dEQ3 [gEQ1 [gEQ2 gEQ3]]]]]]]]]; subst.

    assert (EQ:=Hwflg').
    apply wf_lgsubst_app_inv in EQ.
    destruct EQ as [dsubst1' [dsubst2' [gsubst1' [gsubst2' [dEQ1' [dEQ2' [dEQ3' [gEQ1' [gEQ2' gEQ3']]]]]]]]]; subst.
       
    assert (EQ:=Hwfr).
    apply wf_rsubst_app_inv in EQ.
    destruct EQ as [rsubst1 [rsubst2 [rEQ1 [rEQ2 rEQ3]]]]; subst.

    assert (wf_typ E2' T1') as WFTV'.
      apply typing_regular in H. 
      decompose [and] H. inversion H8; subst.
      apply wft_strengthen_sub with (F:=E1'); auto.

   assert (wf_lgamma_subst (E1'++E2') D2' (dsubst1++dsubst2) (gsubst1++gsubst2) lgsubst2) as Wflg2.
     apply F_related_subst__inversion in J4. decompose [prod] J4; auto.
   assert (wf_lgamma_subst (E1'++E2') D2' (dsubst1'++dsubst2') (gsubst1'++gsubst2') lgsubst2') as Wflg2'.
     apply F_related_subst__inversion in J4. decompose [prod] J4; auto.
   assert (typing empty lempty x1 (apply_delta_subst_typ (dsubst1++dsubst2) T1')) as Typing1.
     apply preservation_normalization with (v:=exp_bang x1) in Ht1; auto.
     simpl_commut_subst in Ht1. inversion Ht1; subst; auto.             
   assert (typing empty lempty x1' (apply_delta_subst_typ (dsubst1'++dsubst2') T1')) as Typing1'.
     apply preservation_normalization with (v:=exp_bang x1') in Ht1'; auto.
     simpl_commut_subst in Ht1'. inversion Ht1'; subst; auto.             

    assert (F_related_terms T1' rsubst2 dsubst2 dsubst2' x1 x1') as Hrel1'.
      destruct Hrel1 as [u1 [u1' [Hnx1u1 [Hnx1'u1' Hrel1]]]].
      exists u1. exists u1'. repeat (split;auto).
        rewrite apply_delta_subst_typ_strenghen with (E1:=E1') (E2:=E2') in Typing1;auto.
        rewrite apply_delta_subst_typ_strenghen with (E1:=E1') (E2:=E2') in Typing1'; auto.

        apply Frel_stronger_heads with (E:=E2') (E':=E1') in Hrel1; auto.       

    assert (F_related_subst (E1'++[(y, bind_typ T1')]++E2') D2' (gsubst1++[(y,x1)]++gsubst2) (gsubst1'++[(y,x1')]++gsubst2') lgsubst2 lgsubst2' (rsubst1++rsubst2) (dsubst1++dsubst2) (dsubst1'++dsubst2')) as Hrel_sub'.
          apply F_related_subst_gweaken; auto.
             assert (y `notin` dom E1') as ynE1'.
                apply fresh_mid_head with (E:=E2') (a:=bind_typ T1'); auto.
             assert (y `notin` dom E2') as ynE2'.
                apply fresh_mid_tail with (F:=E1') (a:=bind_typ T1'); auto.
             assert (y `notin` dom D2') as ynD2'.
               apply contexting_regular in Hcontexting.
               decompose [and] Hcontexting.
               apply wf_lenv_notin_fv_lenv with (x:=y) (T:=T1') in H8; auto.
             auto.

             rewrite apply_delta_subst_typ_strenghen with (E1:=E1') (E2:=E2') in Typing1;auto.
             rewrite apply_delta_subst_typ_strenghen with (E1:=E1') (E2:=E2') in Typing1'; auto.

    assert (F_Rsubst (E1'++[(y, bind_typ T1')] ++E2') (rsubst1++rsubst2) (dsubst1++dsubst2) (dsubst1'++dsubst2')) as HRsub'. 
          apply F_Rsubst_gweaken; auto.       
             assert (y `notin` dom E1') as ynE1'.
                apply fresh_mid_head with (E:=E2') (a:=bind_typ T1'); auto.
             assert (y `notin` dom E2') as ynE2'.
                apply fresh_mid_tail with (F:=E1') (a:=bind_typ T1'); auto.
             auto.

   assert (y `notin` dom lgsubst2) as ynlgsubst2.
                apply contexting_regular in Hcontexting.
                decompose [and] Hcontexting.
                assert (y `notin` dom (E1'++E2')) as ynE'.
                  apply uniq_from_wf_env in H7.
                  simpl_env. solve_uniq.
                assert (y `notin` dom D2') as ynD2'.
                  apply wf_lenv_notin_fv_lenv with (x:=y) (T:=T1') in H8; auto.
                apply wf_lgamma_subst__nfv with (x:=y) in Wflg2; auto.
   assert (wf_lgamma_subst (E1'++[(y,bind_typ T1')]++E2') D2' (dsubst1++dsubst2) (gsubst1++[(y,x1)]++gsubst2) lgsubst2) as Wflg2y.
             apply F_related_subst__inversion in Hrel_sub'.
             decompose [prod] Hrel_sub'; auto.
   assert (y `notin` dom lgsubst2') as ynlgsubst2'.
                apply contexting_regular in Hcontexting.
                decompose [and] Hcontexting.
                assert (y `notin` dom (E1'++E2')) as ynE'.
                  apply uniq_from_wf_env in H7.
                  simpl_env. solve_uniq.
                assert (y `notin` dom D2') as ynD2'.
                  apply wf_lenv_notin_fv_lenv with (x:=y) (T:=T1') in H8; auto.
                apply wf_lgamma_subst__nfv with (x:=y) in Wflg2'; auto.
   assert (wf_lgamma_subst (E1'++[(y,bind_typ T1')]++E2') D2' (dsubst1'++dsubst2') (gsubst1'++[(y,x1')]++gsubst2') lgsubst2') as Wflg2y'.
             apply F_related_subst__inversion in Hrel_sub'.
             decompose [prod] Hrel_sub'; auto.

    assert (J:=@IHHcontexting Htyp Htyp' Hlr (dsubst1++dsubst2) (dsubst1'++dsubst2') (gsubst1++[(y,x1)]++gsubst2) (gsubst1'++[(y,x1')]++gsubst2') lgsubst2 lgsubst2' (rsubst1++rsubst2) Hrel_sub' HRsub').
        
    assert (
            apply_delta_subst (dsubst1++dsubst2) (apply_gamma_subst (gsubst1++[(y,x1)]++gsubst2) (apply_gamma_subst lgsubst2 (plug C2 e))) =
            apply_delta_subst (dsubst1++dsubst2) (apply_gamma_subst (gsubst1++gsubst2) (apply_gamma_subst lgsubst2 (subst_ee y x1 (plug C2 e))))
                  ) as Heq1. simpl.
           simpl_env.
           rewrite gamma_subst_opt with (E':=E1') (E:=E2') (D:=D2') (dsubst:=dsubst1++dsubst2) (t:=T1') (lgsubst:=lgsubst2); auto.
             rewrite swap_subst_ee_lgsubst with  (D:=D2') (E:=E1'++E2') (dsubst:=dsubst1++dsubst2) (t:=apply_delta_subst_typ (dsubst1++dsubst2) T1') (gsubst:=gsubst1++gsubst2); auto.
    assert (
            apply_delta_subst (dsubst1'++dsubst2') (apply_gamma_subst (gsubst1'++[(y,x1')]++gsubst2') (apply_gamma_subst lgsubst2' (plug C2 e'))) =
            apply_delta_subst (dsubst1'++dsubst2') (apply_gamma_subst (gsubst1'++gsubst2') (apply_gamma_subst lgsubst2' (subst_ee y x1' (plug C2 e'))))
                  ) as Heq2.  simpl.
           simpl_env.
           rewrite gamma_subst_opt with (E':=E1') (E:=E2') (D:=D2') (dsubst:=dsubst1'++dsubst2') (t:=T1') (lgsubst:=lgsubst2'); auto.
             rewrite swap_subst_ee_lgsubst with  (D:=D2') (E:=E1'++E2') (dsubst:=dsubst1'++dsubst2') (t:=apply_delta_subst_typ (dsubst1'++dsubst2') T1') (gsubst:=gsubst1'++gsubst2'); auto.
   rewrite Heq1 in J. rewrite Heq2 in J. 
   destruct J as [v [v' [Ht [Ht' [[Hbrc Hv] [[Hbrc' Hv'] Hrel]]]]]].

   rewrite <- shift_ee_expr; auto.
   rewrite <- shift_ee_expr; auto.
   assert (apply_delta_subst (dsubst1++dsubst2)
            (apply_gamma_subst (gsubst1++gsubst2)
              (apply_gamma_subst lgsubst (exp_let e1 (plug (close_ec C2 y) (close_ee e y)))) 
            ) =
            apply_delta_subst (dsubst1++dsubst2)
            (apply_gamma_subst (gsubst1++gsubst2)
              (exp_let 
                (apply_gamma_subst lgsubst1 e1)
                (apply_gamma_subst lgsubst2 (plug (close_ec C2 y) (close_ee e y)))
              )               
            )
          ) as EQ.
     simpl_commut_subst in *.
     rewrite lgamma_subst_split_subst' with (lgsubst1:=lgsubst1) (lgsubst2:=lgsubst2) (E:=E1'++E2') (lE:=D3') (dsubst:=dsubst1++dsubst2) (gsubst:=gsubst1++gsubst2) (lgsubst:=lgsubst); auto.
     rewrite lgamma_subst_split_subst with (lgsubst1:=lgsubst1) (lgsubst2:=lgsubst2) (E:=E1'++E2') (lE:=D3') (dsubst:=dsubst1++dsubst2) (gsubst:=gsubst1++gsubst2) (lgsubst:=lgsubst); auto.
     apply F_related_subst__inversion in J3.
     decompose [prod] J3; auto.
     apply F_related_subst__inversion in J4.
     decompose [prod] J4; auto.
     rewrite lgamma_subst_split_shuffle2 with (lgsubst:=lgsubst) (lgsubst1:=lgsubst1) (E:=E1'++E2') (lE:=D3') ; auto.
     erewrite gamma_subst_closed_exp; eauto.
     rewrite lgamma_subst_split_shuffle1 with (lgsubst:=lgsubst) (lgsubst2:=lgsubst2) (E:=E1'++E2') (lE:=D3') (e:=apply_gamma_subst lgsubst2  (plug (close_ec C2 y) (close_ee e y))) ; auto.

     apply contexting_plug_typing with (e:=e) in Hcontexting; auto.
     assert (TypingC2e := Hcontexting).
     apply typing_subst with (dsubst:=dsubst1++dsubst2)(gsubst:=gsubst1++[(y,x1)]++gsubst2)(lgsubst:=lgsubst2) in Hcontexting; auto.
       rewrite gamma_osubst_closed_exp with 
         (e:=apply_delta_subst (dsubst1++dsubst2)
            (apply_gamma_subst (gsubst1++gsubst2)
              (apply_gamma_subst lgsubst2 (plug (close_ec C2 y) (close_ee e y))))); auto.
         apply disjdom_eq with (D1:={}).
           apply disjdom_nil_1.

           apply typing_fv_ee_upper in Hcontexting.
           rewrite Heq1 in Hcontexting.
           rewrite <- swap_subst_ee_lgsubst with (E:=E1'++E2')(D:=D2')(gsubst:=gsubst1++gsubst2)(dsubst:=dsubst1++dsubst2) (t:=apply_delta_subst_typ (dsubst1++dsubst2) T1') in Hcontexting; auto.
           assert (y `notin` dom (gsubst1++gsubst2)) as yngsubst12.
             assert (y `notin` dom gsubst1) as yngsubst1.
                apply wf_lgamma_subst__uniq in Wflg2y. decompose [and] Wflg2y.
                apply fresh_mid_head with (E:=gsubst2) (a:=x1); auto.
             assert (y `notin` dom gsubst2) as yngsubst2.
                apply wf_lgamma_subst__uniq in Wflg2y. decompose [and] Wflg2y.
                apply fresh_mid_tail with (F:=gsubst1) (a:=x1); auto.
             simpl_env. auto.
           rewrite <- swap_subst_ee_gsubst with (E:=E1'++E2')(D:=D2')(lgsubst:=lgsubst2)(dsubst:=dsubst1++dsubst2)(t:=apply_delta_subst_typ (dsubst1++dsubst2) T1')  in Hcontexting; auto.
           assert (y `notin` dom (dsubst1++dsubst2)) as yndsubst12.
             clear - Wflg2y.
             apply wf_lgamma_subst_disjoint' in Wflg2y.
             solve_uniq.
           rewrite <- swap_subst_ee_dsubst with (E:=E1'++E2')(dsubst:=dsubst1++dsubst2)(t:=apply_delta_subst_typ (dsubst1++dsubst2) T1')  in Hcontexting; auto.

           rewrite <- close_ee_plug; auto.
           rewrite commut_lgamma_subst_close_ee with (E:=E1'++E2')(D:=D2')(dsubst:=dsubst1++dsubst2)(gsubst:=gsubst1++gsubst2)(lgsubst:=lgsubst2); auto.
           rewrite commut_gamma_subst_close_ee with (E:=E1'++E2')(D:=D2')(dsubst:=dsubst1++dsubst2)(gsubst:=gsubst1++gsubst2)(lgsubst:=lgsubst2); auto.
           rewrite commut_delta_subst_close_ee with (dE:=E1'++E2')(dsubst:=dsubst1++dsubst2); auto.
           rewrite close_ee_fv_ee_eq'.

           destruct (@in_dec y (fv_ee (plug C2 e))) as [yinC2e | ynotinC2e].
           SCase "y in C2e".
             apply lgsubst__preserves__in_fv_ee with (E:=E1'++E2')(D:=D2')(dsubst:=dsubst1++dsubst2)(gsubst:=gsubst1++gsubst2)(lgsubst:=lgsubst2) in yinC2e; auto.
             apply gsubst__preserves__in_fv_ee with (E:=E1'++E2')(D:=D2')(dsubst:=dsubst1++dsubst2)(gsubst:=gsubst1++gsubst2)(lgsubst:=lgsubst2) in yinC2e; auto.
             apply dsubst__preserves__in_fv_ee with (E:=E1'++E2')(dsubst:=dsubst1++dsubst2) in yinC2e; auto.

             assert (J5:=@subst_ee_fv_ee_in
               (apply_delta_subst (dsubst1++dsubst2)
                (apply_gamma_subst (gsubst1++gsubst2)
                  (apply_gamma_subst lgsubst2 (plug C2 e))))
               y x1 yinC2e).
             rewrite J5 in Hcontexting. clear J5 yinC2e.
             apply typing_fv_ee_upper in Typing1. simpl in Typing1.

             clear - Hcontexting Typing1.
             fsetdec.
           SCase "y notin C2e".            
             apply lgsubst__preserves__notin_fv_ee with  (E:=E1'++E2')(D:=D2')(dsubst:=dsubst1++dsubst2)(gsubst:=gsubst1++gsubst2)(lgsubst:=lgsubst2) in ynotinC2e; auto.
             apply gsubst__preserves__notin_fv_ee with  (E:=E1'++E2')(D:=D2')(dsubst:=dsubst1++dsubst2)(gsubst:=gsubst1++gsubst2)(lgsubst:=lgsubst2) in ynotinC2e; auto.
             apply dsubst__preserves__notin_fv_ee with  (E:=E1'++E2')(dsubst:=dsubst1++dsubst2) in ynotinC2e; auto.
             rewrite <- subst_ee_fresh in Hcontexting; auto.
             clear - Hcontexting. 
             fsetdec.
   repeat(rewrite EQ). 
   assert (apply_delta_subst (dsubst1'++dsubst2')
            (apply_gamma_subst (gsubst1'++gsubst2')
              (apply_gamma_subst lgsubst' (exp_let e1 (plug (close_ec C2 y) (close_ee e' y)))) 
            ) =
            apply_delta_subst (dsubst1'++dsubst2')
            (apply_gamma_subst (gsubst1'++gsubst2')
              (exp_let 
                (apply_gamma_subst lgsubst1' e1)
                (apply_gamma_subst lgsubst2' (plug (close_ec C2 y) (close_ee e' y)))
              )               
            )
          ) as EQ'.
     simpl_commut_subst in *.
     rewrite lgamma_subst_split_subst' with (lgsubst1:=lgsubst1') (lgsubst2:=lgsubst2') (E:=E1'++E2') (lE:=D3') (dsubst:=dsubst1'++dsubst2') (gsubst:=gsubst1'++gsubst2') (lgsubst:=lgsubst'); auto.
     rewrite lgamma_subst_split_subst with (lgsubst1:=lgsubst1') (lgsubst2:=lgsubst2') (E:=E1'++E2') (lE:=D3') (dsubst:=dsubst1'++dsubst2') (gsubst:=gsubst1'++gsubst2') (lgsubst:=lgsubst'); auto.
     apply F_related_subst__inversion in J3.
     decompose [prod] J3; auto.
     apply F_related_subst__inversion in J4.
     decompose [prod] J4; auto.
     rewrite lgamma_subst_split_shuffle2 with (lgsubst:=lgsubst') (lgsubst1:=lgsubst1') (E:=E1'++E2') (lE:=D3') ; auto.
     erewrite gamma_subst_closed_exp; eauto.
     rewrite lgamma_subst_split_shuffle1 with (lgsubst:=lgsubst') (lgsubst2:=lgsubst2') (E:=E1'++E2') (lE:=D3') (e:=apply_gamma_subst lgsubst2'  (plug (close_ec C2 y) (close_ee e' y))) ; auto.

     apply contexting_plug_typing with (e:=e') in Hcontexting; auto.
     assert (TypingC2e' := Hcontexting).
     apply typing_subst with (dsubst:=dsubst1'++dsubst2')(gsubst:=gsubst1'++[(y,x1')]++gsubst2')(lgsubst:=lgsubst2') in Hcontexting; auto.
       rewrite gamma_osubst_closed_exp with 
         (e:=apply_delta_subst (dsubst1'++dsubst2')
            (apply_gamma_subst (gsubst1'++gsubst2')
              (apply_gamma_subst lgsubst2' (plug (close_ec C2 y) (close_ee e' y))))); auto.
         apply disjdom_eq with (D1:={}).
           apply disjdom_nil_1.

           apply typing_fv_ee_upper in Hcontexting.
           rewrite Heq2 in Hcontexting.
           rewrite <- swap_subst_ee_lgsubst with (E:=E1'++E2')(D:=D2')(gsubst:=gsubst1'++gsubst2')(dsubst:=dsubst1'++dsubst2') (t:=apply_delta_subst_typ (dsubst1'++dsubst2') T1') in Hcontexting; auto.
           assert (y `notin` dom (gsubst1'++gsubst2')) as yngsubst12.
             assert (y `notin` dom gsubst1') as yngsubst1'.
                apply wf_lgamma_subst__uniq in Wflg2y'. decompose [and] Wflg2y'.
                apply fresh_mid_head with (E:=gsubst2') (a:=x1'); auto.
             assert (y `notin` dom gsubst2') as yngsubst2'.
                apply wf_lgamma_subst__uniq in Wflg2y'. decompose [and] Wflg2y'.
                apply fresh_mid_tail with (F:=gsubst1') (a:=x1'); auto.
             simpl_env. auto.
           rewrite <- swap_subst_ee_gsubst with (E:=E1'++E2')(D:=D2')(lgsubst:=lgsubst2')(dsubst:=dsubst1'++dsubst2')(t:=apply_delta_subst_typ (dsubst1'++dsubst2') T1')  in Hcontexting; auto.
           assert (y `notin` dom (dsubst1'++dsubst2')) as yndsubst12'.
             clear - Wflg2y'.
             apply wf_lgamma_subst_disjoint' in Wflg2y'.
             solve_uniq.
           rewrite <- swap_subst_ee_dsubst with (E:=E1'++E2')(dsubst:=dsubst1'++dsubst2')(t:=apply_delta_subst_typ (dsubst1'++dsubst2') T1')  in Hcontexting; auto.

           rewrite <- close_ee_plug; auto.
           rewrite commut_lgamma_subst_close_ee with (E:=E1'++E2')(D:=D2')(dsubst:=dsubst1'++dsubst2')(gsubst:=gsubst1'++gsubst2')(lgsubst:=lgsubst2'); auto.
           rewrite commut_gamma_subst_close_ee with (E:=E1'++E2')(D:=D2')(dsubst:=dsubst1'++dsubst2')(gsubst:=gsubst1'++gsubst2')(lgsubst:=lgsubst2'); auto.
           rewrite commut_delta_subst_close_ee with (dE:=E1'++E2')(dsubst:=dsubst1'++dsubst2'); auto.
           rewrite close_ee_fv_ee_eq'.

           destruct (@in_dec y (fv_ee (plug C2 e'))) as [yinC2e' | ynotinC2e'].
           SCase "y in C2e'".
             apply lgsubst__preserves__in_fv_ee with (E:=E1'++E2')(D:=D2')(dsubst:=dsubst1'++dsubst2')(gsubst:=gsubst1'++gsubst2')(lgsubst:=lgsubst2') in yinC2e'; auto.
             apply gsubst__preserves__in_fv_ee with (E:=E1'++E2')(D:=D2')(dsubst:=dsubst1'++dsubst2')(gsubst:=gsubst1'++gsubst2')(lgsubst:=lgsubst2') in yinC2e'; auto.
             apply dsubst__preserves__in_fv_ee with (E:=E1'++E2')(dsubst:=dsubst1'++dsubst2') in yinC2e'; auto.

             assert (J5:=@subst_ee_fv_ee_in
               (apply_delta_subst (dsubst1'++dsubst2')
                (apply_gamma_subst (gsubst1'++gsubst2')
                  (apply_gamma_subst lgsubst2' (plug C2 e'))))
               y x1' yinC2e').
             rewrite J5 in Hcontexting. clear J5 yinC2e'.
             apply typing_fv_ee_upper in Typing1'. simpl in Typing1'.

             clear - Hcontexting Typing1'.
             fsetdec.
           SCase "y notin C2e'".            
             apply lgsubst__preserves__notin_fv_ee with  (E:=E1'++E2')(D:=D2')(dsubst:=dsubst1'++dsubst2')(gsubst:=gsubst1'++gsubst2')(lgsubst:=lgsubst2') in ynotinC2e'; auto.
             apply gsubst__preserves__notin_fv_ee with  (E:=E1'++E2')(D:=D2')(dsubst:=dsubst1'++dsubst2')(gsubst:=gsubst1'++gsubst2')(lgsubst:=lgsubst2') in ynotinC2e'; auto.
             apply dsubst__preserves__notin_fv_ee with  (E:=E1'++E2')(dsubst:=dsubst1'++dsubst2') in ynotinC2e'; auto.
             rewrite <- subst_ee_fresh in Hcontexting; auto.
             clear - Hcontexting. 
             fsetdec.
   repeat(rewrite EQ'). 

   exists (v). exists (v').
         split.
           SCase "typing".
           simpl_commut_subst. simpl_commut_subst in Ht1.
           apply typing_let with (L:={{y}} `union` cv_ec C2 `union` dom (gsubst1++gsubst2) `union` dom (lgsubst2) `union` dom E)(D1:=lempty)(D2:=lempty)(T1:=apply_delta_subst_typ (dsubst1++dsubst2) T1'); auto.
             intros x Hfv.
             apply contexting_plug_typing with (e:=e) in Hcontexting; auto. 
             rewrite <- close_ee_plug; auto.
             destruct (@in_dec y (fv_ee (plug C2 e))) as [yinC2e | ynotinC2e].
             SSCase "y in C2e".
               assert (y `notin` dom (gsubst1++gsubst2)) as yngsubst12.
                 assert (y `notin` dom gsubst1) as yngsubst1.
                    apply wf_lgamma_subst__uniq in Wflg2y. decompose [and] Wflg2y.
                    apply fresh_mid_head with (E:=gsubst2) (a:=x1); auto.
                 assert (y `notin` dom gsubst2) as yngsubst2.
                    apply wf_lgamma_subst__uniq in Wflg2y. decompose [and] Wflg2y.
                    apply fresh_mid_tail with (F:=gsubst1) (a:=x1); auto.
                 simpl_env. auto.
               assert (y `notin` dom (dsubst1++dsubst2)) as yndsubst12.
                 clear - Wflg2y.
                 apply wf_lgamma_subst_disjoint' in Wflg2y.
                 solve_uniq.
               rewrite commut_lgamma_subst_close_ee with (E:=E1'++E2')(D:=D2')(dsubst:=dsubst1++dsubst2)(gsubst:=gsubst1++gsubst2)(lgsubst:=lgsubst2); auto.
               rewrite commut_gamma_subst_close_ee with (E:=E1'++E2')(D:=D2')(dsubst:=dsubst1++dsubst2)(gsubst:=gsubst1++gsubst2)(lgsubst:=lgsubst2); auto.
               rewrite commut_delta_subst_close_ee with (dE:=E1'++E2')(dsubst:=dsubst1++dsubst2); auto.
               rewrite close_open_ee__subst_ee; auto.
                 rewrite_env (nil++[(x,bind_typ (apply_delta_subst_typ (dsubst1++dsubst2) T1'))]++nil).
                 apply typing_nonlin_renaming_one; auto.

                 apply typing_nonlin_permute in Hcontexting. 
                 rewrite_env (nil++D2') in Hcontexting.
                 apply typing_subst_closed with (dsubst:=dsubst1++dsubst2)(gsubst:=gsubst1++gsubst2)(lgsubst:=lgsubst2) in Hcontexting; auto.
                   simpl. 
                   rewrite_env ([(y,bind_typ (apply_delta_subst_typ (dsubst1++dsubst2) T1'))]++nil).
                   auto.
                   
                 apply typing_regular in Hcontexting. 
                 decompose [and] Hcontexting.
                 apply expr_preserved_under_delta_subst with (E:=E1'++E2'); auto.
                 apply expr_preserved_under_gamma_subst with (E:=E1'++E2')(D:=D2')(dsubst:=dsubst1++dsubst2)(gsubst:=gsubst1++gsubst2)(lgsubst:=lgsubst2); auto.
                 apply expr_preserved_under_lgamma_subst with (E:=E1'++E2')(D:=D2')(dsubst:=dsubst1++dsubst2)(gsubst:=gsubst1++gsubst2)(lgsubst:=lgsubst2); auto.
             SSCase "y notin C2e".
               rewrite <- close_ee_expr; auto.
               rewrite <- subst_ee_fresh in Ht; auto.
               rewrite <- open_ee_expr; auto.
               rewrite_env (nil++[(x,bind_typ (apply_delta_subst_typ (dsubst1++dsubst2) T1'))]++nil).
               apply typing_weakening; auto.
                 rewrite_env ([(x,bind_typ (apply_delta_subst_typ (dsubst1++dsubst2) T1'))]++nil).
                 auto.
         split.
           SCase "typing".
           simpl_commut_subst. simpl_commut_subst in Ht1'.
           apply typing_let with (L:={{y}} `union` cv_ec C2 `union` dom (gsubst1'++gsubst2') `union` dom (lgsubst2') `union` dom E)(D1:=lempty)(D2:=lempty)(T1:=apply_delta_subst_typ (dsubst1'++dsubst2') T1'); auto.
             intros x Hfv.
             apply contexting_plug_typing with (e:=e') in Hcontexting; auto. 
             rewrite <- close_ee_plug; auto.
             destruct (@in_dec y (fv_ee (plug C2 e'))) as [yinC2e' | ynotinC2e'].
             SSCase "y in C2e'".
               assert (y `notin` dom (gsubst1'++gsubst2')) as yngsubst12'.
                 assert (y `notin` dom gsubst1') as yngsubst1'.
                    apply wf_lgamma_subst__uniq in Wflg2y'. decompose [and] Wflg2y'.
                    apply fresh_mid_head with (E:=gsubst2') (a:=x1'); auto.
                 assert (y `notin` dom gsubst2') as yngsubst2'.
                    apply wf_lgamma_subst__uniq in Wflg2y'. decompose [and] Wflg2y'.
                    apply fresh_mid_tail with (F:=gsubst1') (a:=x1'); auto.
                 simpl_env. auto.
               assert (y `notin` dom (dsubst1'++dsubst2')) as yndsubst12'.
                 clear - Wflg2y'.
                 apply wf_lgamma_subst_disjoint' in Wflg2y'.
                 solve_uniq.
               rewrite commut_lgamma_subst_close_ee with (E:=E1'++E2')(D:=D2')(dsubst:=dsubst1'++dsubst2')(gsubst:=gsubst1'++gsubst2')(lgsubst:=lgsubst2'); auto.
               rewrite commut_gamma_subst_close_ee with (E:=E1'++E2')(D:=D2')(dsubst:=dsubst1'++dsubst2')(gsubst:=gsubst1'++gsubst2')(lgsubst:=lgsubst2'); auto.
               rewrite commut_delta_subst_close_ee with (dE:=E1'++E2')(dsubst:=dsubst1'++dsubst2'); auto.
               rewrite close_open_ee__subst_ee; auto.
                 rewrite_env (nil++[(x,bind_typ (apply_delta_subst_typ (dsubst1'++dsubst2') T1'))]++nil).
                 apply typing_nonlin_renaming_one; auto.

                 apply typing_nonlin_permute in Hcontexting. 
                 rewrite_env (nil++D2') in Hcontexting.
                 apply typing_subst_closed with (dsubst:=dsubst1'++dsubst2')(gsubst:=gsubst1'++gsubst2')(lgsubst:=lgsubst2') in Hcontexting; auto.
                   simpl. 
                   rewrite_env ([(y,bind_typ (apply_delta_subst_typ (dsubst1'++dsubst2') T1'))]++nil).
                   auto.
                   
                 apply typing_regular in Hcontexting. 
                 decompose [and] Hcontexting.
                 apply expr_preserved_under_delta_subst with (E:=E1'++E2'); auto.
                 apply expr_preserved_under_gamma_subst with (E:=E1'++E2')(D:=D2')(dsubst:=dsubst1'++dsubst2')(gsubst:=gsubst1'++gsubst2')(lgsubst:=lgsubst2'); auto.
                 apply expr_preserved_under_lgamma_subst with (E:=E1'++E2')(D:=D2')(dsubst:=dsubst1'++dsubst2')(gsubst:=gsubst1'++gsubst2')(lgsubst:=lgsubst2'); auto.
             SSCase "y notin C2e'".
               rewrite <- close_ee_expr; auto.
               rewrite <- subst_ee_fresh in Ht'; auto.
               rewrite <- open_ee_expr; auto.
               rewrite_env (nil++[(x,bind_typ (apply_delta_subst_typ (dsubst1'++dsubst2') T1'))]++nil).
               apply typing_weakening; auto.
                 rewrite_env ([(x,bind_typ (apply_delta_subst_typ (dsubst1'++dsubst2') T1'))]++nil).
                auto.
         split.
           SSSCase "norm".
           split; auto.
             assert (expr (exp_let e1 (plug (close_ec C2 y) (close_ee e y)))) as Expr2.
               assert (typing (E1'++E2') D3' (exp_let e1 (plug (close_ec C2 y) (close_ee e y))) T2') as Typing2.
                  apply typing_let with (L:={{y}} `union` cv_ec C2 `union` dom E1' `union` dom E2' `union` dom D2')(D1:=D1')(D2:=D2')(T1:=T1'); auto.
                    intros x xn.
                    rewrite <- close_ee_plug; auto.
                    rewrite close_open_ee__subst_ee; auto.
                      apply contexting_plug_typing with (e:=e) in Hcontexting; auto.
                      apply typing_nonlin_permute.
                      apply typing_nonlin_renaming_one; auto.

                    apply contexting_plug_typing with (e:=e) in Hcontexting; auto.
                apply typing_regular in Typing2.
                decompose [and] Typing2; auto.
           apply bigstep_red__trans with (e':=(apply_delta_subst (dsubst1++dsubst2) (apply_gamma_subst (gsubst1++gsubst2)  (apply_gamma_subst lgsubst2 (subst_ee y x1 (plug C2 e)))))); auto.
             apply bigstep_red__trans with (e':=exp_let (exp_bang x1) (apply_delta_subst (dsubst1++dsubst2) (apply_gamma_subst (gsubst1++gsubst2)  (apply_gamma_subst lgsubst2 (plug (close_ec C2 y) (close_ee e y)))))); auto.
               destruct Hn1 as [Hbrc1 Hx1].
               simpl_commut_subst.
               apply _congr_let_arg; auto.

                 apply expr_preserved_under_lgamma_subst with (E:=E1'++E2')(D:=D3')(dsubst:=dsubst1++dsubst2)(gsubst:=gsubst1++gsubst2)(lgsubst:=lgsubst) in Expr2; auto.
                 apply expr_preserved_under_gamma_subst with (E:=E1'++E2')(D:=D3')(dsubst:=dsubst1++dsubst2)(gsubst:=gsubst1++gsubst2)(lgsubst:=lgsubst) in Expr2; auto.
                 apply expr_preserved_under_delta_subst with (E:=E1'++E2')(dsubst:=dsubst1++dsubst2) in Expr2; auto.
                 rewrite EQ in Expr2. simpl_commut_subst in Expr2; auto.

              apply bigstep_red_trans with (e':=(apply_delta_subst (dsubst1++dsubst2) (apply_gamma_subst (gsubst1++gsubst2)  (apply_gamma_subst lgsubst2 (subst_ee y x1 (plug C2 e)))))); auto.
              assert (apply_delta_subst (dsubst1++dsubst2) (apply_gamma_subst (gsubst1++gsubst2) (apply_gamma_subst lgsubst2 x1)) =x1) as Heq3.
                 rewrite gamma_subst_closed_exp with (t:= apply_delta_subst_typ (dsubst1++dsubst2) T1'); auto.
                 rewrite gamma_subst_closed_exp with (t:= apply_delta_subst_typ  (dsubst1++dsubst2) T1'); auto.
                 rewrite delta_subst_closed_exp with (t:= apply_delta_subst_typ  (dsubst1++dsubst2) T1'); auto.
                 rewrite gamma_subst_closed_exp with (t:= apply_delta_subst_typ  (dsubst1++dsubst2) T1'); auto.
              rewrite <- Heq3.
             assert (subst_ee y (apply_delta_subst  (dsubst1++dsubst2) (apply_gamma_subst  (gsubst1++gsubst2) (apply_gamma_subst lgsubst2 x1))) (plug C2 e) = subst_ee y x1 (plug C2 e)) as Heq4. 
                rewrite Heq3. auto. 
             rewrite Heq4.

             assert (typing (E1'++[(y, bind_typ T1')]++E2') D2' (plug C2 e) T2') as Typinge.
                apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.

             assert (disjdom (union {{y}} (fv_ee x1 `union` fv_te x1)) (cv_ec C2)) as Disj0.
               eapply disjdom_app_l.
               split.
                 apply disjdom_one_2; auto.
               eapply disjdom_app_l.
               split.
                  eapply empty_typing_disjdom; eauto.
                  eapply empty_typing_disjdom'; eauto.
              rewrite subst_ee_plug; auto.
              rewrite <- close_open_ee__subst_ee; auto.
              assert (context C2) as Context2.
                apply contexting__context in Hcontexting; auto.    
              rewrite <- close_open_ec__subst_ec; auto.
              assert (disjdom (fv_ee x1 `union` fv_te x1) (cv_ec (close_ec C2 y))) as Disj.
               eapply disjdom_app_l.
               split.
                  eapply empty_typing_disjdom; eauto.
                  eapply empty_typing_disjdom'; eauto.
              rewrite <- open_ee_plug; auto.
              rewrite commut_lgamma_subst_open_ee with (E:=E1'++E2')(D:=D2')(dsubst:=dsubst1++dsubst2)(gsubst:=gsubst1++gsubst2); auto.
              rewrite commut_gamma_subst_open_ee with (E:=E1'++E2')(D:=D2')(dsubst:=dsubst1++dsubst2)(lgsubst:=lgsubst2); auto.
              rewrite <- commut_delta_subst_ebang; auto.
              apply red_bang_preserved_under_delta_subst with (dE:=E1'++E2'); auto.

              rewrite <- commut_gamma_subst_open_ee with (E:=E1'++E2') (dsubst:=dsubst1++dsubst2) (D:=D2') (lgsubst:=lgsubst2); auto.
              rewrite <- commut_gamma_subst_bang; auto.
              apply red_bang_preserved_under_gamma_subst with (E:=E1'++E2') (dsubst:=dsubst1++dsubst2) (D:=D2') (lgsubst:=lgsubst2); auto. 

              rewrite <- commut_gamma_subst_bang; auto.
              rewrite <- commut_lgamma_subst_open_ee with (E:=E1'++E2')(D:=D2')(dsubst:=dsubst1++dsubst2)(gsubst:=gsubst1++gsubst2); auto.
              apply red_bang_preserved_under_lgamma_subst with (E:=E1'++E2')(D:=D2')(dsubst:=dsubst1++dsubst2)(gsubst:=gsubst1++gsubst2); auto. 

              apply red_let_beta.
                apply expr_let with (L:=(cv_ec (close_ec C2 y)) `union` cv_ec C2); auto.
                   intros x xn.
                   assert (disjdom (fv_ee x `union` fv_te x) (cv_ec (close_ec C2 y))) as Disj'.
                     eapply disjdom_app_l.
                     split.
                       apply disjdom_one_2; auto.
                       simpl. apply disjdom_nil_1.
                   rewrite open_ee_plug; auto.
                   rewrite close_open_ec__subst_ec; auto.
                   rewrite close_open_ee__subst_ee; auto.
                  assert (disjdom (union {{y}} (fv_ee x `union` fv_te x)) (cv_ec C2)) as Disj0'.
                     eapply disjdom_app_l.
                     split.
                       apply disjdom_one_2; auto.
                     eapply disjdom_app_l.
                     split.
                       apply disjdom_one_2; auto.
                       simpl. apply disjdom_nil_1.
                   rewrite <- subst_ee_plug; auto.

         split; auto.
           SSSCase "norm".
           split; auto.
             assert (expr (exp_let e1 (plug (close_ec C2 y) (close_ee e' y)))) as Expr2'.
               assert (typing (E1'++E2') D3' (exp_let e1 (plug (close_ec C2 y) (close_ee e' y))) T2') as Typing2'.
                  apply typing_let with (L:={{y}} `union` cv_ec C2 `union` dom E1' `union` dom E2' `union` dom D2')(D1:=D1')(D2:=D2')(T1:=T1'); auto.
                    intros x xn.
                    rewrite <- close_ee_plug; auto.
                    rewrite close_open_ee__subst_ee; auto.
                      apply contexting_plug_typing with (e:=e') in Hcontexting; auto.
                      apply typing_nonlin_permute.
                      apply typing_nonlin_renaming_one; auto.

                    apply contexting_plug_typing with (e:=e') in Hcontexting; auto.
                apply typing_regular in Typing2'.
                decompose [and] Typing2'; auto.
           apply bigstep_red__trans with (e':=(apply_delta_subst (dsubst1'++dsubst2') (apply_gamma_subst (gsubst1'++gsubst2')  (apply_gamma_subst lgsubst2' (subst_ee y x1' (plug C2 e')))))); auto.
             apply bigstep_red__trans with (e':=exp_let (exp_bang x1') (apply_delta_subst (dsubst1'++dsubst2') (apply_gamma_subst (gsubst1'++gsubst2')  (apply_gamma_subst lgsubst2' (plug (close_ec C2 y) (close_ee e' y)))))); auto.
               destruct Hn1' as [Hbrc1' Hx1'].
               simpl_commut_subst.
               apply _congr_let_arg; auto.

                 apply expr_preserved_under_lgamma_subst with (E:=E1'++E2')(D:=D3')(dsubst:=dsubst1'++dsubst2')(gsubst:=gsubst1'++gsubst2')(lgsubst:=lgsubst') in Expr2'; auto.
                 apply expr_preserved_under_gamma_subst with (E:=E1'++E2')(D:=D3')(dsubst:=dsubst1'++dsubst2')(gsubst:=gsubst1'++gsubst2')(lgsubst:=lgsubst') in Expr2'; auto.
                 apply expr_preserved_under_delta_subst with (E:=E1'++E2')(dsubst:=dsubst1'++dsubst2') in Expr2'; auto.
                 rewrite EQ' in Expr2'. simpl_commut_subst in Expr2'; auto.

              apply bigstep_red_trans with (e':=(apply_delta_subst (dsubst1'++dsubst2') (apply_gamma_subst (gsubst1'++gsubst2')  (apply_gamma_subst lgsubst2' (subst_ee y x1' (plug C2 e')))))); auto.
              assert (apply_delta_subst (dsubst1'++dsubst2') (apply_gamma_subst (gsubst1'++gsubst2') (apply_gamma_subst lgsubst2' x1')) =x1') as Heq3.
                 rewrite gamma_subst_closed_exp with (t:= apply_delta_subst_typ (dsubst1'++dsubst2') T1'); auto.
                 rewrite gamma_subst_closed_exp with (t:= apply_delta_subst_typ  (dsubst1'++dsubst2') T1'); auto.
                 rewrite delta_subst_closed_exp with (t:= apply_delta_subst_typ  (dsubst1'++dsubst2') T1'); auto.
                 rewrite gamma_subst_closed_exp with (t:= apply_delta_subst_typ  (dsubst1'++dsubst2') T1'); auto.
              rewrite <- Heq3.
             assert (subst_ee y (apply_delta_subst  (dsubst1'++dsubst2') (apply_gamma_subst  (gsubst1'++gsubst2') (apply_gamma_subst lgsubst2' x1'))) (plug C2 e') = subst_ee y x1' (plug C2 e')) as Heq4. 
                rewrite Heq3. auto. 
             rewrite Heq4.

             assert (typing (E1'++[(y, bind_typ T1')]++E2') D2' (plug C2 e') T2') as Typinge'.
                apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.

             assert (disjdom (union {{y}} (fv_ee x1' `union` fv_te x1')) (cv_ec C2)) as Disj0.
               eapply disjdom_app_l.
               split.
                 apply disjdom_one_2; auto.
               eapply disjdom_app_l.
               split.
                  eapply empty_typing_disjdom; eauto.
                  eapply empty_typing_disjdom'; eauto.
              rewrite subst_ee_plug; auto.
              rewrite <- close_open_ee__subst_ee; auto.
              assert (context C2) as Context2.
                apply contexting__context in Hcontexting; auto.    
              rewrite <- close_open_ec__subst_ec; auto.
              assert (disjdom (fv_ee x1' `union` fv_te x1') (cv_ec (close_ec C2 y))) as Disj.
               eapply disjdom_app_l.
               split.
                  eapply empty_typing_disjdom; eauto.
                  eapply empty_typing_disjdom'; eauto.
              rewrite <- open_ee_plug; auto.
              rewrite commut_lgamma_subst_open_ee with (E:=E1'++E2')(D:=D2')(dsubst:=dsubst1'++dsubst2')(gsubst:=gsubst1'++gsubst2'); auto.
              rewrite commut_gamma_subst_open_ee with (E:=E1'++E2')(D:=D2')(dsubst:=dsubst1'++dsubst2')(lgsubst:=lgsubst2'); auto.
              rewrite <- commut_delta_subst_ebang; auto.
              apply red_bang_preserved_under_delta_subst with (dE:=E1'++E2'); auto.

              rewrite <- commut_gamma_subst_open_ee with (E:=E1'++E2') (dsubst:=dsubst1'++dsubst2') (D:=D2') (lgsubst:=lgsubst2'); auto.
              rewrite <- commut_gamma_subst_bang; auto.
              apply red_bang_preserved_under_gamma_subst with (E:=E1'++E2') (dsubst:=dsubst1'++dsubst2') (D:=D2') (lgsubst:=lgsubst2'); auto. 

              rewrite <- commut_gamma_subst_bang; auto.
              rewrite <- commut_lgamma_subst_open_ee with (E:=E1'++E2')(D:=D2')(dsubst:=dsubst1'++dsubst2')(gsubst:=gsubst1'++gsubst2'); auto.
              apply red_bang_preserved_under_lgamma_subst with (E:=E1'++E2')(D:=D2')(dsubst:=dsubst1'++dsubst2')(gsubst:=gsubst1'++gsubst2'); auto. 

              apply red_let_beta.
                apply expr_let with (L:=(cv_ec (close_ec C2 y)) `union` cv_ec C2); auto.
                   intros x xn.
                   assert (disjdom (fv_ee x `union` fv_te x) (cv_ec (close_ec C2 y))) as Disj'.
                     eapply disjdom_app_l.
                     split.
                       apply disjdom_one_2; auto.
                       simpl. apply disjdom_nil_1.
                   rewrite open_ee_plug; auto.
                   rewrite close_open_ec__subst_ec; auto.
                   rewrite close_open_ee__subst_ee; auto.
                  assert (disjdom (union {{y}} (fv_ee x `union` fv_te x)) (cv_ec C2)) as Disj0'.
                     eapply disjdom_app_l.
                     split.
                       apply disjdom_one_2; auto.
                     eapply disjdom_app_l.
                     split.
                       apply disjdom_one_2; auto.
                       simpl. apply disjdom_nil_1.
                   rewrite <- subst_ee_plug; auto.
Qed.

Lemma F_logical_related_congruence : forall E lE e e' t C E' lE' t',
  F_logical_related E lE e e' t ->
  contexting E lE t C E' lE' t' ->
  F_logical_related E' lE' (plug C e) (plug C e') t'.
Proof.
  intros E lE e e' t C E' lE' t' Hlr Hcontexting.
  destruct Hlr as [Htyp [Htyp' Hlr]]. 
  split. apply contexting_plug_typing with (e:=e) in Hcontexting; auto.
  split. apply contexting_plug_typing with (e:=e') in Hcontexting; auto.
  (contexting_cases (induction Hcontexting) Case); 
    intros dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Hrel_sub HRsub; simpl in *; auto.
  Case "contexting_abs_free".
    apply F_logical_related_congruence__abs_free with 
     (e:=e) (e':=e') (E:=E) (D:=D) (T:=T) (L:=L) (T1':=T1') (C1:=C1) (T2':=T2') (E':=E') (D':=D') 
     (dsubst:=dsubst) (dsubst':=dsubst') (gsubst:=gsubst) (gsubst':=gsubst') (lgsubst:=lgsubst) (lgsubst':=lgsubst') (rsubst:=rsubst); assumption.

  Case "contexting_abs_capture". 
    apply F_logical_related_congruence__abs_capture with 
     (e:=e) (e':=e') (E:=E) (D:=D) (T:=T) (y:=y) (T1':=T1') (C1:=C1) (T2':=T2') (E':=E') (D':=D') 
     (dsubst:=dsubst) (dsubst':=dsubst') (gsubst:=gsubst) (gsubst':=gsubst') (lgsubst:=lgsubst) (lgsubst':=lgsubst') (rsubst:=rsubst); assumption.

  Case "contexting_app1". 
    apply F_logical_related_congruence__app1 with 
     (e:=e) (e':=e') (E:=E) (D:=D) (T:=T) (T1':=T1') (C1:=C1) (T2':=T2') (E':=E') (D1':=D1')  (D2':=D2')  (D3':=D3') 
     (dsubst:=dsubst) (dsubst':=dsubst') (gsubst:=gsubst) (gsubst':=gsubst') (lgsubst:=lgsubst) (lgsubst':=lgsubst') (rsubst:=rsubst); assumption.

  Case "contexting_app2". 
    apply F_logical_related_congruence__app2 with 
     (e:=e) (e':=e') (E:=E) (D:=D) (T:=T) (T1':=T1') (C2:=C2) (T2':=T2') (E':=E') (D1':=D1')  (D2':=D2')  (D3':=D3') 
     (dsubst:=dsubst) (dsubst':=dsubst') (gsubst:=gsubst) (gsubst':=gsubst') (lgsubst:=lgsubst) (lgsubst':=lgsubst') (rsubst:=rsubst); assumption.

   Case "contexting_tabs_free".
     apply F_logical_related_congruence__tabs_free with 
     (e:=e) (e':=e') (E:=E) (D:=D) (T:=T) (L:=L) (T1':=T1') (C1:=C1) (E':=E') (D':=D')
     (dsubst:=dsubst) (dsubst':=dsubst') (gsubst:=gsubst) (gsubst':=gsubst') (lgsubst:=lgsubst) (lgsubst':=lgsubst') (rsubst:=rsubst); assumption.

   Case "contexting_tabs_capture".
    apply F_logical_related_congruence__tabs_capture with 
     (e:=e) (e':=e') (E:=E) (D:=D) (T:=T) (T1':=T1') (C1:=C1) (E':=E') (D':=D')
     (dsubst:=dsubst) (dsubst':=dsubst') (gsubst:=gsubst) (gsubst':=gsubst') (lgsubst:=lgsubst) (lgsubst':=lgsubst') (rsubst:=rsubst); assumption.

   Case "contexting_tapp".
    apply F_logical_related_congruence__tapp with 
     (e:=e) (e':=e') (E:=E) (D:=D) (T:=T) (T':=T') (C1:=C1) (E':=E') (D':=D')
     (dsubst:=dsubst) (dsubst':=dsubst') (gsubst:=gsubst) (gsubst':=gsubst') (lgsubst:=lgsubst) (lgsubst':=lgsubst') (rsubst:=rsubst); assumption.

    Case "contexting_bang".
    assert (J:=Hrel_sub). apply F_related_subst__inversion in J. decompose [prod] J. clear J.

    assert (
      F_related_terms T1' rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (plug C1 e))))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (plug C1 e'))))
     ) as FR_T1.
       apply IHHcontexting; auto.
    destruct FR_T1 as [v [v' [Ht1 [Ht1' [Hn1 [Hn1' Hrel1]]]]]].

    exists (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_bang (plug C1 e))))).
    exists (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_bang (plug C1 e'))))).
    split; simpl_commut_subst; auto.
    split; simpl_commut_subst; auto.
    split. split; simpl_commut_subst; auto.
    split. split; simpl_commut_subst; auto.
      SCase "Frel".
        SSCase "Frel".
        apply F_related_values_bang_req.
        repeat (split; simpl_commut_subst; auto).
        exists (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (plug C1 e)))).
        exists (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (plug C1 e')))).
        repeat(split; auto).
          exists (v). exists (v'). split; auto.

  Case "contexting_let1". 
    apply F_logical_related_congruence__let1 with 
     (e:=e) (e':=e') (E:=E) (D:=D) (T:=T) (T1':=T1') (T2':=T2') (C1:=C1) (E':=E') (D1':=D1') (L:=L) (D2':=D2') (D3':=D3')
     (dsubst:=dsubst) (dsubst':=dsubst') (gsubst:=gsubst) (gsubst':=gsubst') (lgsubst:=lgsubst) (lgsubst':=lgsubst') (rsubst:=rsubst); assumption.

  Case "contexting_let2_free". 
    apply F_logical_related_congruence__let2_free with 
     (e:=e) (e':=e') (E:=E) (D:=D) (T:=T) (L:=L) (T1':=T1') (C2:=C2) (T2':=T2') (E':=E') (D1':=D1')  (D2':=D2') (D3':=D3')
     (dsubst:=dsubst) (dsubst':=dsubst') (gsubst:=gsubst) (gsubst':=gsubst') (lgsubst:=lgsubst) (lgsubst':=lgsubst') (rsubst:=rsubst); assumption.

  Case "contexting_let2_capture". 
    apply F_logical_related_congruence__let2_capture with 
     (e:=e) (e':=e') (E:=E) (D:=D) (T:=T) (y:=y) (T1':=T1') (C2:=C2) (T2':=T2') (E':=E') (D1':=D1') (D2':=D2') (D3':=D3') 
     (dsubst:=dsubst) (dsubst':=dsubst') (gsubst:=gsubst) (gsubst':=gsubst') (lgsubst:=lgsubst) (lgsubst':=lgsubst') (rsubst:=rsubst); assumption.

    Case "contexting_apair1".
    assert (J:=Hrel_sub). apply F_related_subst__inversion in J. decompose [prod] J. clear J.

    assert (
      F_related_terms T1' rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (plug C1 e))))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (plug C1 e'))))
     ) as FR_T1.
       apply IHHcontexting; auto.
    destruct FR_T1 as [v [v' [Ht1 [Ht1' [Hn1 [Hn1' Hrel1]]]]]].

    assert (
      F_related_terms T2' rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e2)))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e2)))
     ) as FR_T2.
       apply parametricity with (E:=E') (lE:=D'); auto.
    destruct FR_T2 as [v0 [v'0 [Ht2 [Ht2' [Hn2 [Hn2' Hrel2]]]]]].

    exists (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_apair (plug C1 e)  e2)))).
    exists (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_apair (plug C1 e') e2)))).
    split; simpl_commut_subst; auto.
    split; simpl_commut_subst; auto.
    split. split; simpl_commut_subst; auto.
    split. split; simpl_commut_subst; auto.
      SCase "Frel".
        SSCase "Frel".
        apply F_related_values_with_req.
        repeat (split; simpl_commut_subst; auto).
        exists (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (plug C1 e)))).
        exists (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e2))).
        exists (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (plug C1 e')))).
        exists (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e2))).
        repeat(split; auto).
          exists (v). exists (v'). split; auto.
          exists (v0). exists (v'0). split; auto.

    Case "contexting_apair2".
    assert (J:=Hrel_sub). apply F_related_subst__inversion in J. decompose [prod] J. clear J.

    assert (
      F_related_terms T1' rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e1)))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e1)))
     ) as FR_T1.
       apply parametricity with (E:=E') (lE:=D'); auto.
    destruct FR_T1 as [v [v' [Ht1 [Ht1' [Hn1 [Hn1' Hrel1]]]]]].

    assert (
      F_related_terms T2' rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (plug C2 e))))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (plug C2 e'))))
     ) as FR_T2.
       apply IHHcontexting; auto.
    destruct FR_T2 as [v0 [v'0 [Ht2 [Ht2' [Hn2 [Hn2' Hrel2]]]]]].

    exists (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_apair e1 (plug C2 e))))).
    exists (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_apair e1 (plug C2 e'))))).
    split; simpl_commut_subst; auto.
    split; simpl_commut_subst; auto.
    split. split; simpl_commut_subst; auto.
    split. split; simpl_commut_subst; auto.
      SCase "Frel".
        SSCase "Frel".
        apply F_related_values_with_req.
        repeat (split; simpl_commut_subst; auto).
        exists (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e1))).
        exists (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (plug C2 e)))).
        exists (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e1))).
        exists (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (plug C2 e')))).
        repeat(split; auto).
          exists (v). exists (v'). split; auto.
          exists (v0). exists (v'0). split; auto.

    Case "contexting_fst".
    assert (J:=Hrel_sub). apply F_related_subst__inversion in J.
    destruct J as [[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe].
    assert (wf_typ E' (typ_with T1' T2')) as WFTwith.
      apply contexting_regular in Hcontexting.
      decompose [and] Hcontexting; auto.
    assert (
      F_related_terms (typ_with T1' T2') rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (plug C1 e))))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (plug C1 e'))))
     ) as FR_With.
       apply IHHcontexting; auto.
    destruct FR_With as [ee1 [ee1' [Ht [Ht' [Hn [Hn' FR_With]]]]]].

    simpl_commut_subst in Ht. simpl_commut_subst in Ht'. 
    apply congr_fst with (T1:=apply_delta_subst_typ dsubst T1') (T2:=apply_delta_subst_typ dsubst T2') in Hn; auto.
    apply congr_fst with (T1:=apply_delta_subst_typ dsubst' T1') (T2:=apply_delta_subst_typ dsubst' T2') in Hn'; auto.
    destruct Hn as [e1 [e2 [Hbrc Heq]]].
    destruct Hn' as [e1' [e2' [Hbrc' Heq']]].
    apply F_related_values_with_leq in FR_With.
    subst.
    destruct FR_With as [Hv [Hv' [ee1 [ee2 [ee1' [ee2' [Heq [Heq' 
                                [[u1 [u1' [[Hbrc_e1u1 Hu1][[Hbrc_e1'u1' Hu1'] Hrel_wft1]]]] 
                                 [u2 [u2' [[Hbrc_e2u2 Hu2][[Hbrc_e2'u2' Hu2'] Hrel_wft2]]]]]
                              ]]]]]]]]; subst.
    inversion Heq. inversion Heq'. subst. clear Heq Heq'.
    exists(u1). exists(u1').
        repeat(split; simpl_commut_subst; auto; try solve [
          apply typing_fst with (T2:=apply_delta_subst_typ dsubst T2'); auto |
          apply typing_fst with (T2:=apply_delta_subst_typ dsubst' T2');auto |
          split; auto; apply bigstep_red__trans with (e':=ee1); auto |
          split; auto; apply bigstep_red__trans with (e':=ee1'); auto]).

    Case "contexting_snd".
    assert (J:=Hrel_sub). apply F_related_subst__inversion in J.
    destruct J as [[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe].
    assert (wf_typ E' (typ_with T1' T2')) as WFTwith.
      apply contexting_regular in Hcontexting.
      decompose [and] Hcontexting; auto.
    assert (
      F_related_terms (typ_with T1' T2') rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (plug C1 e))))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (plug C1 e'))))
     ) as FR_With.
       apply IHHcontexting; auto.
    destruct FR_With as [ee2 [ee2' [Ht [Ht' [Hn [Hn' FR_With]]]]]].

    simpl_commut_subst in Ht. simpl_commut_subst in Ht'. 
    apply congr_snd with (T1:=apply_delta_subst_typ dsubst T1') (T2:=apply_delta_subst_typ dsubst T2') in Hn; auto.
    apply congr_snd with (T1:=apply_delta_subst_typ dsubst' T1') (T2:=apply_delta_subst_typ dsubst' T2') in Hn'; auto.
    destruct Hn as [e1 [e2 [Hbrc Heq]]].
    destruct Hn' as [e1' [e2' [Hbrc' Heq']]].
    apply F_related_values_with_leq in FR_With.
    subst.
    destruct FR_With as [Hv [Hv' [ee1 [ee2 [ee1' [ee2' [Heq [Heq' 
                                [[u1 [u1' [[Hbrc_e1u1 Hu1][[Hbrc_e1'u1' Hu1'] Hrel_wft1]]]] 
                                 [u2 [u2' [[Hbrc_e2u2 Hu2][[Hbrc_e2'u2' Hu2'] Hrel_wft2]]]]]
                              ]]]]]]]]; subst.
    inversion Heq. inversion Heq'. subst. clear Heq Heq'.
    exists (u2). exists (u2').
        repeat(split; simpl_commut_subst; auto; try solve [
          apply typing_snd with (T1:=apply_delta_subst_typ dsubst T1'); auto |
          apply typing_snd with (T1:=apply_delta_subst_typ dsubst' T1'); auto |
          split; auto; apply bigstep_red__trans with (e':=ee2); auto |
          split; auto; apply bigstep_red__trans with (e':=ee2'); auto]).
Qed.

Lemma F_Rsubst_refl : forall E rsubst dsubst,
  wf_rho_subst E rsubst ->
  wf_delta_subst E dsubst ->
  F_Rsubst E rsubst dsubst dsubst.
Proof.
  induction E; intros rsubst dsubst Hwfr Hwfd.
     inversion Hwfr; subst.
     inversion Hwfd; subst. auto.

     destruct a.
     inversion Hwfr; subst.
       inversion Hwfd; subst. simpl_env in *.
       apply F_Rsubst_rel; auto.
         unfold wfr. split; auto.
         apply notin_wf_env; auto.
           apply wf_delta_subst__uniq in H1. decompose [and] H1; auto.

       inversion Hwfd; subst. simpl_env in *.
       apply F_Rsubst_typ; auto.
         apply notin_wf_env; auto.
           apply wf_delta_subst__uniq in H3. decompose [and] H3; auto.
Qed.

Lemma F_related_subst_refl : forall E rsubst dsubst,
  wf_rho_subst E rsubst ->
  wf_delta_subst E dsubst ->
  gdom_env E [=] {} ->
  F_related_subst E nil nil nil nil nil rsubst dsubst dsubst.
Proof.
  induction E; intros rsubst dsubst Hwfr Hwfd EQ.
     inversion Hwfr; subst.
     inversion Hwfd; subst. auto.

     destruct a.
     inversion Hwfr; subst; simpl in EQ.
       inversion Hwfd; subst. simpl_env in *.
       apply F_related_subst_kind; auto.
         apply notin_wf_env in H4; auto.
           apply wf_delta_subst__uniq in H1. decompose [and] H1; auto.
 
         unfold wfr. split; auto.
 
       assert (a `in` Metatheory.empty) as FALSE.
         rewrite <- EQ. auto.
       contradict FALSE; auto.
Qed.

Axiom F_related_values__consistent : forall v v',
  F_related_values Two nil nil nil v v' ->
  ((v = tt /\ v' =tt) \/ (v = ff /\ v' =ff)).

Require Import Bang_Parametricity_App.

Lemma wf_delta_subst__wf_rho_subst : forall E dsubst,
  wf_delta_subst E dsubst ->
  exists rsubst, wf_rho_subst E rsubst.
Proof.
  intros E dsubst H.
  induction H.
    exists nil. auto.

    destruct IHwf_delta_subst as [rsubst Hwfr].
    exists ([(X, Rid T)]++rsubst).
    apply wf_rho_subst_srel; auto.

    destruct IHwf_delta_subst as [rsubst Hwfr].
    exists (rsubst). auto.
Qed.

Lemma F_logical_related__sound : forall E lE e e' t,
  F_logical_related E lE e e' t ->
  F_observational_eq E lE e e' t.
Proof.
  intros E lE e e' t Hlr.
  assert (J:=Hlr).
  destruct J as [Htyp [Htyp' J]].
  split; auto.
  split; auto.
    intros C Hcontext.
    apply F_logical_related_congruence with (C:=C) (E':=nil) (lE':=nil) (t':=Two) in Hlr; auto.
    split. eapply contexting_plug_typing; eauto.
    split. eapply contexting_plug_typing; eauto.
      assert (F_Rsubst nil nil nil nil) as J1. auto.
      assert (F_related_subst nil nil nil nil nil nil nil nil nil) as J2. auto.
      destruct Hlr as [Htyp1 [Htyp1' Hlr]].
      assert (Hrel:=@Hlr nil nil nil nil nil nil nil J2 J1).
      destruct Hrel as [v [v' [Htypv [Htypv' [Hn [Hn' Hrel]]]]]].
      simpl in *.
      assert (JJ:=@F_related_values__consistent v v' Hrel).
      destruct JJ as [[EQ EQ'] | [EQ EQ']]; subst; auto.
Qed.
