(** Authors: Jianzhou Zhao. *)

Require Import LinF_PreLib.
Require Import LinF_Renaming.
Require Export LinF_OParametricity.
Require Import LinF_OParametricity_Macro.
Require Export LinF_ContextualEq_Def.
Require Import LinF_ContextualEq_Infrastructure.
Require Export LinF_ContextualEq_Lemmas.
Require Export LinF_ContextualEq_Sound.
Require Export LinF_OContextualEq_Lemmas.

Export OParametricity.

Definition F_ological_related E lE e e' t : Prop :=
  typing E lE e t /\
  typing E lE e' t /\
  exists L,
  forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
   disjdom L (fv_env Env) ->
   disjdom L (fv_lenv lEnv) ->
   F_Related_osubst E lE gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
   F_Rosubst E rsubst dsubst dsubst' Env ->
   F_Related_oterms t rsubst dsubst dsubst'
                                 (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
                                 (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e'))) Env lEnv.

Lemma F_ological_related_congruence__abs_free :
  forall e e' E D T,
  typing E D e T ->
  typing E D e' T ->
  forall L0,
  (forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
   disjdom L0 (fv_env Env) ->
   disjdom L0 (fv_lenv lEnv) ->
   F_Related_osubst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
   F_Rosubst E rsubst dsubst dsubst' Env ->
   F_Related_oterms T rsubst dsubst dsubst' 
     (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
     (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e')))
     Env lEnv
  ) ->
  forall L K T1' C1 T2' E' D',
  wf_typ E' T1' kn_nonlin ->
  (forall x,
    x `notin` L ->
    contexting E D T (open_ec C1 x) ((x, bind_typ T1')::E') D' T2'
  ) ->
  (forall x,
    x `notin` L ->
   typing E D e T ->
   typing E D e' T ->
    (forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
     disjdom L0 (fv_env Env) ->
     disjdom L0 (fv_lenv lEnv) ->
     F_Related_osubst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
     F_Rosubst E rsubst dsubst dsubst' Env ->
     F_Related_oterms T rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e')))
      Env lEnv
    ) ->
   forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
     disjdom (L0 `union` cv_ec (open_ec C1 x) `union` fv_ec (open_ec C1 x) `union` dom E `union` dom D `union` fv_tt T `union` fv_tt T2' `union` (add x (dom E')) `union` dom D') (fv_env Env) ->
     disjdom (L0 `union` cv_ec (open_ec C1 x) `union` fv_ec (open_ec C1 x) `union` dom E `union` dom D `union` fv_tt T `union` fv_tt T2' `union` (add x (dom E')) `union` dom D') (fv_lenv lEnv) ->
     F_Related_osubst ((x, bind_typ T1')::E') D' gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
     F_Rosubst ((x, bind_typ T1')::E') rsubst dsubst dsubst' Env ->
     F_Related_oterms T2' rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (plug (open_ec C1 x) e))))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (plug (open_ec C1 x) e'))))
      Env lEnv
  ) ->
  (K = kn_nonlin -> D' = lempty) ->
  forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
  disjdom (L0 `union` cv_ec C1 `union` fv_ec C1 `union` dom E `union` dom D `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2') `union` dom E' `union` dom D') (fv_env Env) ->
  disjdom (L0 `union` cv_ec C1 `union` fv_ec C1 `union` dom E `union` dom D `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2') `union` dom E' `union` dom D') (fv_lenv lEnv) ->
  F_Related_osubst E' D' gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
  F_Rosubst E' rsubst dsubst dsubst' Env  ->
  F_Related_oterms (typ_arrow K T1' T2') rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_abs K T1' (plug C1 (shift_ee e))))))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_abs K T1' (plug C1 (shift_ee e'))))))
      Env lEnv.
Proof.
    intros e e' E D T Htyp Htyp' L0 Hlr L K T1' C1 T2' E' D' H H1 H2 H3 dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv Disj00 Disj01 Hrel_sub HRsub.
    assert (J:=Hrel_sub). apply F_Related_osubst__inversion in J. 
    destruct J as [[[[[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe] Hwfe'] HwfEnv] HwflEnv].

    rename H into WFTV.
    
    assert (value (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_abs K T1' (plug C1 (shift_ee e))))))) as Value.
      clear Disj00 Disj01.
      apply delta_gamma_lgamma_osubst_value with (E:=E') (D:=D') (Env:=Env) (lEnv:=lEnv); auto.
        apply FrTyping__absvalue with (L:=L `union` cv_ec C1) (E:=E') (D:=D') (T1:=T2') (K:=kn_nonlin); auto.
          intros x xn.
          assert (x `notin` L) as xnFv. auto.
          apply H1 in xnFv.
          apply contexting_plug_typing with (e:=e) in xnFv; auto.
          simpl_env in xnFv.
          rewrite open_ee_expr with (e:=e) (u:=x) in xnFv; auto.
          assert (disjdom ((fv_ee x) `union` (fv_te x)) (cv_ec C1)) as Disj.
            eapply disjdom_app_l.
            split.
              apply disjdom_one_2; auto.
              simpl. apply disjdom_nil_1.
          rewrite <- open_ee_plug in xnFv; auto. 
          rewrite shift_ee_expr with (e:=e) in xnFv; auto.
    assert (value (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_abs K T1' (plug C1 (shift_ee e'))))))) as Value'.
      clear Disj00 Disj01.
      apply delta_gamma_lgamma_osubst_value with (E:=E') (D:=D') (Env:=Env) (lEnv:=lEnv); auto.
        apply FrTyping__absvalue with (L:=L `union` cv_ec C1) (E:=E') (D:=D') (T1:=T2') (K:=kn_nonlin); auto.
          intros x xn.
          assert (x `notin` L) as xnFv. auto.
          apply H1 in xnFv.
          apply contexting_plug_typing with (e:=e') in xnFv; auto.
          simpl_env in xnFv.
          rewrite open_ee_expr with (e:=e') (u:=x) in xnFv; auto.
          assert (disjdom ((fv_ee x) `union` (fv_te x)) (cv_ec C1)) as Disj.
            eapply disjdom_app_l.
            split.
              apply disjdom_one_2; auto.
              simpl. apply disjdom_nil_1.
          rewrite <- open_ee_plug in xnFv; auto. 
          rewrite shift_ee_expr with (e:=e') in xnFv; auto.
    exists (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_abs K T1' (plug C1 (shift_ee e)))))).
    exists (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_abs K T1' (plug C1 (shift_ee e')))))).
    split.
      clear Disj00 Disj01.
      assert (typing E' D' (plug (ctx_abs_free K T1' C1) e) (typ_arrow K T1' T2')) as Hptyp.
        apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.
           apply contexting_abs_free with (L:=L); auto.
      apply typing_osubst with (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst) (Env:=Env) (lEnv:=lEnv) in Hptyp; auto.
    split. 
      clear Disj00 Disj01.
      assert (typing E' D' (plug (ctx_abs_free K T1' C1) e') (typ_arrow K T1' T2')) as Hptyp'.
        apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.
           apply contexting_abs_free with (L:=L); auto.
      apply typing_osubst with (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst') (Env:=Env) (lEnv:=lEnv) in Hptyp'; auto.
    split. split; auto.
    split. split; auto.
      SCase "Frel".
      apply F_Related_ovalues_arrow_req.
      split; auto.
      split; auto.
      SSCase "arrow".
        exists {}.
        intros lEnv1 x x' Htyping Htyping' Hwfle Disj Harrow_left.
        pick fresh z.
        assert (z `notin` L) as Fry. auto.
        assert (wf_typ ([(z, bind_typ T1')]++E') T2' kn_lin) as WFT'. 
          apply H1 in Fry.
          apply contexting_regular in Fry.
          decompose [and] Fry; auto.
        assert (lEnv1 = nil) as EQ.
          apply value_nonlin_inversion in Htyping; subst; auto.
            apply F_Related_ovalues_inversion in Harrow_left.
            decompose [prod] Harrow_left; auto.

            apply wft_osubst with (E:=E') (dsubst:=dsubst); auto.
        subst.
        assert (F_Related_osubst ([(z, bind_typ T1')]++E') D' ([(z,x)]++gsubst) ([(z,x')]++gsubst') lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv) as Hrel_sub'.           
          apply F_Related_osubst_typ; auto.
        assert (F_Rosubst ([(z, bind_typ T1')]++E') rsubst dsubst dsubst' Env) as HRsub'. 
          apply F_Rosubst_typ; auto.
        apply H2 with (dsubst:=dsubst) (gsubst:=[(z,x)]++gsubst) (lgsubst:=lgsubst) (dsubst':=dsubst') (gsubst':=[(z,x')]++gsubst') (lgsubst':=lgsubst') (rsubst:=rsubst) (Env:=Env) (lEnv:=lEnv) in Fry; auto.
        clear Disj00 Disj01.
        simpl_env in Fry.
        assert (
            apply_delta_subst dsubst (apply_gamma_subst ([(z,x)]++gsubst) (apply_gamma_subst lgsubst (plug (open_ec C1 z) e))) =
            apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (subst_ee z x (plug (open_ec C1 z) e))))
                  ) as Heq1. simpl. 
           rewrite swap_subst_ee_olgsubst with (E:=E')(D:=D') (Env:=Env) (lEnv:=lEnv) (lEnv':=nil) (dsubst:=dsubst)(lgsubst:=lgsubst)(gsubst:=gsubst)(t:=apply_delta_subst_typ dsubst T1'); auto.
             apply wf_lgamma_osubst__nfv with (x:=z) in Hwflg; auto.
         assert (
            apply_delta_subst dsubst' (apply_gamma_subst ([(z,x')]++gsubst') (apply_gamma_subst lgsubst' (plug (open_ec C1 z) e'))) =
            apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (subst_ee z x' (plug (open_ec C1 z) e'))))
                  ) as Heq2.  simpl.
           rewrite swap_subst_ee_olgsubst with (E:=E')(D:=D')(Env:=Env) (lEnv:=lEnv) (lEnv':=nil) (dsubst:=dsubst')(lgsubst:=lgsubst')(gsubst:=gsubst')(t:=apply_delta_subst_typ dsubst' T1'); auto.
             apply wf_lgamma_osubst__nfv with (x:=z) in Hwflg'; auto.
         rewrite Heq1 in Fry. rewrite Heq2 in Fry. clear Heq1 Heq2.
         destruct Fry as [v [v' [Ht [Ht' [[Hbrc Hv] [[Hbrc' Hv'] Hrel]]]]]].
         exists (v). exists (v').
         split.
           SSSCase "norm".
           split; auto.
           apply bigstep_red_trans with (e':=(apply_delta_subst dsubst (apply_gamma_subst gsubst  (apply_gamma_subst lgsubst (subst_ee z x (plug (open_ec C1 z) e)))))); auto.
              rewrite <- shift_ee_expr; auto.
             assert (plug (open_ec C1 z) e = open_ee (plug C1 e) z) as EQ.
               rewrite open_ee_plug; auto.
               rewrite <- open_ee_expr; auto.
                eapply disjdom_app_l.
                split.
                  apply disjdom_one_2; auto.
                  simpl. apply disjdom_nil_1.
             rewrite EQ.
             eapply m_red_abs_osubst with (T1:=T2') (L:=L `union` cv_ec C1); eauto.
               apply F_Related_ovalues_inversion in Harrow_left.
               decompose [prod] Harrow_left; auto.

               assert (typing E' D' (plug (ctx_abs_free K T1' C1) e) (typ_arrow K T1' T2')) as Hptyp.
                 apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.
                   apply contexting_abs_free with (L:=L); auto.
               apply notin_fv_ee_typing with (y:=z) in Hptyp; auto.
               simpl in Hptyp.
               rewrite <- shift_ee_expr in Hptyp; auto.

               intros x0 x0dom.
               assert (x0 `notin` L) as x0n. auto.
               apply H1 in x0n.
               assert (disjdom ((fv_ee x0) `union` fv_te x0) (cv_ec C1)) as Disj'.
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
               assert (disjdom (fv_ee z `union` fv_te z) (cv_ec C1)) as Disj'.
                 eapply disjdom_app_l.
                 split.
                   apply disjdom_one_2; auto.
                   simpl. apply disjdom_nil_1.
               rewrite open_ee_plug; auto.
               rewrite <- open_ee_expr; auto.
             rewrite EQ.
             eapply m_red_abs_osubst with (T1:=T2') (L:=L `union` cv_ec C1); eauto.
               apply F_Related_ovalues_inversion in Harrow_left.
               decompose [prod] Harrow_left; auto.

               assert (typing E' D' (plug (ctx_abs_free K T1' C1) e') (typ_arrow K T1' T2')) as Hptyp.
                 apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.
                   apply contexting_abs_free with (L:=L); auto.
               apply notin_fv_ee_typing with (y:=z) in Hptyp; auto.
               simpl in Hptyp.
               rewrite <- shift_ee_expr in Hptyp; auto.

               intros x0 x0dom.
               assert (x0 `notin` L) as x0n. auto.
               apply H1 in x0n.
               assert (disjdom (fv_ee x0 `union` fv_te x0) (cv_ec C1)) as Disj'.
                 eapply disjdom_app_l.
                 split.
                   apply disjdom_one_2; auto.
                   simpl. apply disjdom_nil_1.
               rewrite open_ee_plug; auto.
               rewrite <- open_ee_expr; auto.
               apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.       

        clear - Fr Disj00.
        assert (J:=@open_ec_fv_ec_upper C1 z).
        assert (J':=@cv_ec_open_ec_rec C1 0 z).
        unfold open_ec in *.
        apply disjdom_sym_1.
        apply disjdom_sub with (D1:={{z}} `union` L0 `union` cv_ec C1 `union` fv_ec C1 `union` dom E `union` dom D `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2') `union` dom E' `union` dom D').
          eapply disjdom_app_r.
          split; auto.
            destruct_notin.
            clear - NotInTac16.
            apply disjdom_one_2; auto.
           
            rewrite J'.
            clear - J. simpl in J. fsetdec.

        clear - Fr Disj01.
        assert (J:=@open_ec_fv_ec_upper C1 z).
        assert (J':=@cv_ec_open_ec_rec C1 0 z).
        unfold open_ec in *.
        apply disjdom_sym_1.
        apply disjdom_sub with (D1:={{z}} `union` L0 `union` cv_ec C1 `union` fv_ec C1 `union` dom E `union` dom D `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2') `union` dom E' `union` dom D').
          eapply disjdom_app_r.
          split; auto.
            destruct_notin.
            clear - NotInTac23.
            apply disjdom_one_2; auto.
           
            rewrite J'.
            clear - J. simpl in J. fsetdec.
Qed.

Lemma F_ological_related_congruence__labs_free :
  forall e e' E D T,
  typing E D e T ->
  typing E D e' T ->
  forall L0,
  (forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
   disjdom L0 (fv_env Env) ->
   disjdom L0 (fv_lenv lEnv) ->
   F_Related_osubst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
   F_Rosubst E rsubst dsubst dsubst' Env ->
   F_Related_oterms T rsubst dsubst dsubst' 
     (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
     (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e')))
     Env lEnv
  ) ->
  forall L K T1' C1 T2' E' D',
  wf_typ E' T1' kn_lin ->
  (forall x,
    x `notin` L ->
    contexting E D T (open_ec C1 x) E' ((x, lbind_typ T1')::D') T2'
  ) ->
  (forall x,
    x `notin` L ->
   typing E D e T ->
   typing E D e' T ->
    (forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
     disjdom L0 (fv_env Env) ->
     disjdom L0 (fv_lenv lEnv) ->
     F_Related_osubst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
     F_Rosubst E rsubst dsubst dsubst' Env ->
     F_Related_oterms T rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e')))
      Env lEnv
    ) ->
   forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
     disjdom (L0 `union` cv_ec (open_ec C1 x) `union` fv_ec (open_ec C1 x) `union` dom E `union` dom D `union` fv_tt T `union` fv_tt T2' `union` dom E' `union` (add x (dom D'))) (fv_env Env) ->
     disjdom (L0 `union` cv_ec (open_ec C1 x) `union` fv_ec (open_ec C1 x) `union` dom E `union` dom D `union` fv_tt T `union` fv_tt T2' `union` dom E' `union` (add x (dom D'))) (fv_lenv lEnv) ->
     F_Related_osubst E' ((x, lbind_typ T1')::D') gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
     F_Rosubst E' rsubst dsubst dsubst' Env ->
     F_Related_oterms T2' rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (plug (open_ec C1 x) e))))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (plug (open_ec C1 x) e'))))
      Env lEnv
  ) ->
  (K = kn_nonlin -> D' = lempty) ->
  forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
  disjdom (L0 `union` cv_ec C1 `union` fv_ec C1 `union` dom E `union` dom D `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2') `union` dom E' `union` dom D') (fv_env Env) ->
  disjdom (L0 `union` cv_ec C1 `union` fv_ec C1 `union` dom E `union` dom D `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2') `union` dom E' `union` dom D') (fv_lenv lEnv) ->
  F_Related_osubst E' D' gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
  F_Rosubst E' rsubst dsubst dsubst' Env  ->
  F_Related_oterms (typ_arrow K T1' T2') rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_abs K T1' (plug C1 (shift_ee e))))))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_abs K T1' (plug C1 (shift_ee e'))))))
      Env lEnv.
Proof.
    intros e e' E D T Htyp Htyp' L0 Hlr L K T1' C1 T2' E' D' H H1 H2 H3 dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv Disj00 Disj01 Hrel_sub HRsub.
    assert (J:=Hrel_sub). apply F_Related_osubst__inversion in J. 
    destruct J as [[[[[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe] Hwfe'] HwfEnv] HwflEnv].

    rename H into WFTV.

    assert (value (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_abs K T1' (plug C1 (shift_ee e))))))) as Value.
      clear Disj00 Disj01.
      apply delta_gamma_lgamma_osubst_value with (E:=E') (D:=D') (Env:=Env) (lEnv:=lEnv); auto.
        apply FrTyping__labsvalue with (L:=L `union` cv_ec C1) (E:=E') (D:=D') (T1:=T2') (K:=kn_lin); auto.
          intros x xn.
          assert (x `notin` L) as xnFv. auto.
          apply H1 in xnFv.
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
    assert (value (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_abs K T1' (plug C1 (shift_ee e'))))))) as Value'.
      clear Disj00 Disj01.
      apply delta_gamma_lgamma_osubst_value with (E:=E') (D:=D') (Env:=Env) (lEnv:=lEnv); auto.
        apply FrTyping__labsvalue with (L:=L `union` cv_ec C1) (E:=E') (D:=D') (T1:=T2') (K:=kn_lin); auto.
          intros x xn.
          assert (x `notin` L) as xnFv. auto.
          apply H1 in xnFv.
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
    
    exists (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_abs K T1' (plug C1 (shift_ee e)))))).
    exists (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_abs K T1' (plug C1 (shift_ee e')))))).
    split.
      clear Disj00 Disj01.
      assert (typing E' D' (plug (ctx_abs_free K T1' C1) e) (typ_arrow K T1' T2')) as Hptyp.
        apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.
           apply contexting_labs_free with (L:=L); auto.
      apply typing_osubst with (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst) (Env:=Env) (lEnv:=lEnv) in Hptyp; auto.
    split.
      clear Disj00 Disj01.
      assert (typing E' D' (plug (ctx_abs_free K T1' C1) e') (typ_arrow K T1' T2')) as Hptyp'.
        apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.
           apply contexting_labs_free with (L:=L); auto.
      apply typing_osubst with (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst')  (Env:=Env) (lEnv:=lEnv) in Hptyp'; auto.
    split. split; auto.
    split. split; auto.
      SCase "Frel".
      apply F_Related_ovalues_arrow_req.
      split; auto.
      split; auto.
      SSCase "arrow".
        exists (dom gsubst `union` dom lgsubst `union` dom gsubst' `union` dom lgsubst' `union` dom E `union` dom D `union` dom E' `union` dom D' `union` L0 `union` cv_ec C1 `union` fv_ec C1 `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2')).
        intros lEnv1 x x' Htyping Htyping' Hwfle Disj' Harrow_left.

        assert (disjoint lEnv1 gsubst /\ disjoint lEnv1 lgsubst /\ disjoint lEnv1 gsubst' /\ disjoint lEnv1 lgsubst' /\ disjoint lEnv1 E /\ disjoint lEnv1 D /\ disjoint lEnv1 E' /\ disjoint lEnv1 D') as Disj.
          apply disjdom_sym_1 in Disj'.
          split.
            apply disjdom__disjoint.
            apply disjdom_sub with (D1:=dom gsubst `union` dom lgsubst `union` dom gsubst' `union` dom lgsubst' `union` dom E `union` dom D `union` dom E' `union` dom D' `union` L0 `union` cv_ec C1 `union` fv_ec C1 `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2')); auto.
               fsetdec.
          split.
            apply disjdom__disjoint.
            apply disjdom_sub with (D1:=dom gsubst `union` dom lgsubst `union` dom gsubst' `union` dom lgsubst' `union` dom E `union` dom D `union` dom E' `union` dom D' `union` L0 `union` cv_ec C1 `union` fv_ec C1 `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2')); auto.
               fsetdec.
          split.
            apply disjdom__disjoint.
            apply disjdom_sub with (D1:=dom gsubst `union` dom lgsubst `union` dom gsubst' `union` dom lgsubst' `union` dom E `union` dom D `union` dom E' `union` dom D' `union` L0 `union` cv_ec C1 `union` fv_ec C1 `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2')); auto.
               fsetdec.
          split.
            apply disjdom__disjoint.
            apply disjdom_sub with (D1:=dom gsubst `union` dom lgsubst `union` dom gsubst' `union` dom lgsubst' `union` dom E `union` dom D `union` dom E' `union` dom D' `union` L0 `union` cv_ec C1 `union` fv_ec C1 `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2')); auto.
               fsetdec.
          split.
            apply disjdom__disjoint.
            apply disjdom_sub with (D1:=dom gsubst `union` dom lgsubst `union` dom gsubst' `union` dom lgsubst' `union` dom E `union` dom D `union` dom E' `union` dom D' `union` L0 `union` cv_ec C1 `union` fv_ec C1 `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2')); auto.
               fsetdec.
          split.
            apply disjdom__disjoint.
            apply disjdom_sub with (D1:=dom gsubst `union` dom lgsubst `union` dom gsubst' `union` dom lgsubst' `union` dom E `union` dom D `union` dom E' `union` dom D' `union` L0 `union` cv_ec C1 `union` fv_ec C1 `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2')); auto.
               fsetdec.
          split.
            apply disjdom__disjoint.
            apply disjdom_sub with (D1:=dom gsubst `union` dom lgsubst `union` dom gsubst' `union` dom lgsubst' `union` dom E `union` dom D `union` dom E' `union` dom D' `union` L0 `union` cv_ec C1 `union` fv_ec C1 `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2')); auto.
               fsetdec.
            apply disjdom__disjoint.
            apply disjdom_sub with (D1:=dom gsubst `union` dom lgsubst `union` dom gsubst' `union` dom lgsubst' `union` dom E `union` dom D `union` dom E' `union` dom D' `union` L0 `union` cv_ec C1 `union` fv_ec C1 `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2')); auto.
               fsetdec.

        pick fresh z.
        assert (z `notin` L) as Fry. auto.
        assert (wf_typ E' T2' kn_lin) as WFT'. 
          apply H1 in Fry.
          apply contexting_regular in Fry.
          decompose [and] Fry; auto.
        assert (F_Related_osubst E' ([(z, lbind_typ T1')]++D') gsubst gsubst' ([(z,x)]++lgsubst) ([(z,x')]++lgsubst') rsubst dsubst dsubst' Env (lEnv1++lEnv)) as Hrel_sub'.        
          apply F_Related_osubst_ltyp; auto.
             decompose [and] Disj. split; auto.
        apply H2 with (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=[(z,x)]++lgsubst) (dsubst':=dsubst') (gsubst':=gsubst') (lgsubst':=[(z,x')]++lgsubst') (rsubst:=rsubst) (Env:=Env) (lEnv:=lEnv1++lEnv) in Fry; auto.
        clear Disj00 Disj01.
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
              assert (disjdom (fv_ee z `union` fv_te z) (cv_ec C1)) as Disj0.
                eapply disjdom_app_l.
                split.
                  apply disjdom_one_2; auto.
                  simpl. apply disjdom_nil_1.
               rewrite open_ee_plug; auto.
               rewrite <- open_ee_expr; auto.
             rewrite EQ.
             eapply m_red_labs_osubst with (T1:=T2') (L:=L `union` cv_ec C1) (lEnv':=lEnv1); eauto.
               apply F_Related_ovalues_inversion in Harrow_left.
               decompose [prod] Harrow_left; auto.

               decompose [and] Disj. split; auto.

               assert (typing E' D' (plug (ctx_abs_free K T1' C1) e) (typ_arrow K T1' T2')) as Hptyp.
                 apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.
                   apply contexting_labs_free with (L:=L); auto.
               apply notin_fv_ee_typing with (y:=z) in Hptyp; auto.
               simpl in Hptyp.
               rewrite <- shift_ee_expr in Hptyp; auto.

               intros x0 x0dom.
               assert (x0 `notin` L) as x0n. auto.
               apply H1 in x0n.
               assert (disjdom (fv_ee x0 `union` fv_te x0) (cv_ec C1)) as Disj0.
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
               assert (disjdom (fv_ee z `union` fv_te z) (cv_ec C1)) as Disj0.
                 eapply disjdom_app_l.
                 split.
                   apply disjdom_one_2; auto.
                   simpl. apply disjdom_nil_1.
               rewrite open_ee_plug; auto.
               rewrite <- open_ee_expr; auto.
             rewrite EQ.
             eapply m_red_labs_osubst with (T1:=T2') (L:=L `union` cv_ec C1) (lEnv':=lEnv1); eauto.
               apply F_Related_ovalues_inversion in Harrow_left.
               decompose [prod] Harrow_left; auto.

               decompose [and] Disj. split; auto.

               assert (typing E' D' (plug (ctx_abs_free K T1' C1) e') (typ_arrow K T1' T2')) as Hptyp.
                 apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.
                   apply contexting_labs_free with (L:=L); auto.
               apply notin_fv_ee_typing with (y:=z) in Hptyp; auto.
               simpl in Hptyp.
               rewrite <- shift_ee_expr in Hptyp; auto.

               intros x0 x0dom.
               assert (x0 `notin` L) as x0n. auto.
               apply H1 in x0n.
               assert (disjdom (fv_ee x0 `union` fv_te x0) (cv_ec C1)) as Disj0.
                 eapply disjdom_app_l.
                 split.
                   apply disjdom_one_2; auto.
                   simpl. apply disjdom_nil_1.
             rewrite open_ee_plug; auto.
               rewrite <- open_ee_expr; auto.
               apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.       

        clear - Fr Disj00.
        assert (J:=@open_ec_fv_ec_upper C1 z).
        assert (J':=@cv_ec_open_ec_rec C1 0 z).
        unfold open_ec in *.
        apply disjdom_sym_1.
        apply disjdom_sub with (D1:={{z}} `union` L0 `union` cv_ec C1 `union` fv_ec C1 `union` dom E `union` dom D `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2') `union` dom E' `union` dom D').
          eapply disjdom_app_r.
          split; auto.
            destruct_notin.
            clear - NotInTac16.
            apply disjdom_one_2; auto.
           
            rewrite J'.
            clear - J. simpl in J. fsetdec.

        clear - Fr Disj01 Disj' Disj00 Htyping Hrel_sub'.
        assert (J:=@open_ec_fv_ec_upper C1 z).
        assert (J':=@cv_ec_open_ec_rec C1 0 z).
        unfold open_ec in *.
        apply disjdom_sym_1.
        apply disjdom_sub with (D1:={{z}} `union` L0 `union` cv_ec C1 `union` fv_ec C1 `union` dom E `union` dom D `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2') `union` dom E' `union` dom D').
          eapply disjdom_app_r.
          split; auto.
            destruct_notin.
            clear - NotInTac23  NotInTac24.
            apply disjdom_one_2; simpl_env; auto.
           
            apply disjdom_sym_1.
            apply disjdom_eq with (D1:=fv_lenv lEnv1 `union` fv_lenv lEnv).
              eapply disjdom_app_l.
              split; auto.
                 apply disjdom_sub with (D1:=dom gsubst `union` dom lgsubst `union` dom gsubst' `union` dom lgsubst' `union` dom E `union` dom D `union` dom E' `union` dom D' `union` L0 `union` cv_ec C1 `union` fv_ec C1 `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2')); auto.
                   apply disjdom_sym_1. 
                   apply disjdom_fv_lenv_wfle with (Env:=Env); auto.
                     apply F_Related_osubst__inversion in Hrel_sub'; auto.
                     decompose [prod] Hrel_sub'. clear Hrel_sub'.
                     apply disjoint_lgamma_osubst in b4.                    
                     decompose [and] b4. clear b4.
                     apply disjoint_lgamma_osubst in b5.                    
                     decompose [and] b5. clear b5.
                     eapply disjdom_app_l.
                     split.
                       apply disjoint__disjdom. assumption.
                     eapply disjdom_app_l.
                     split.
                       apply disjoint__disjdom.
                       clear - H13. solve_uniq.
                     eapply disjdom_app_l.
                     split.
                       apply disjoint__disjdom. assumption.
                     eapply disjdom_app_l.
                     split.
                       apply disjoint__disjdom.
                       clear - H3. solve_uniq.

                       clear - Disj00.
                       apply disjdom_sym_1.         
                       apply disjdom_sub with (L0 `union` cv_ec C1 `union` fv_ec C1 `union` dom E `union` dom D `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2') `union` dom E' `union` dom D').
                         apply disjdom_sym_1.         
                         apply disjdom_sub with (fv_env Env); auto.
                           apply fv_env__includes__dom.
                           clear. fsetdec.
           
                   clear. fsetdec.

                 clear - Disj01.
                 apply disjdom_sym_1; auto.
               simpl_env. clear. fsetdec.
             rewrite J'. clear - J. simpl in J. fsetdec.
Qed.

Lemma F_ological_related_congruence__abs_capture :
  forall e e' E D T,
  typing E D e T ->
  typing E D e' T ->
  forall L0,
  (forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
   disjdom L0 (fv_env Env) ->
   disjdom L0 (fv_lenv lEnv) ->
   F_Related_osubst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
   F_Rosubst E rsubst dsubst dsubst' Env ->
   F_Related_oterms T rsubst dsubst dsubst' 
     (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
     (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e')))
     Env lEnv
  ) ->
  forall K y T1' C1 T2' E' D',
  wf_typ (env_remove (y, bind_typ T1') E') T1' kn_nonlin ->
  binds y (bind_typ T1') E' ->
  y `notin` dom D `union` cv_ec C1 ->
  contexting E D T C1 E' D' T2' ->
  (K = kn_nonlin -> D' = lempty) ->
  (typing E D e T ->
   typing E D e' T ->
    (forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
     disjdom L0 (fv_env Env) ->
     disjdom L0 (fv_lenv lEnv) ->
     F_Related_osubst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
     F_Rosubst E rsubst dsubst dsubst' Env ->
     F_Related_oterms T rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e')))
      Env lEnv
    ) ->
   forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
     disjdom (L0 `union` cv_ec C1 `union` fv_ec C1 `union` dom E `union` dom D `union` fv_tt T `union` fv_tt T2' `union` dom E' `union` dom D') (fv_env Env) ->
     disjdom (L0 `union` cv_ec C1 `union` fv_ec C1 `union` dom E `union` dom D `union` fv_tt T `union` fv_tt T2' `union` dom E' `union` dom D') (fv_lenv lEnv) ->
     F_Related_osubst E' D' gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
     F_Rosubst E' rsubst dsubst dsubst' Env ->
     F_Related_oterms T2' rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (plug C1 e))))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (plug C1 e'))))
      Env lEnv
  ) ->
  forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
  disjdom (L0 `union` ({{y}} `union` cv_ec (close_ec C1 y)) `union` fv_ec (close_ec C1 y) `union` dom E `union` dom D `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2') `union` dom (env_remove (y, bind_typ T1') E') `union` dom D') (fv_env Env) ->
  disjdom (L0 `union` ({{y}} `union` cv_ec (close_ec C1 y)) `union` fv_ec (close_ec C1 y) `union` dom E `union` dom D `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2') `union` dom (env_remove (y, bind_typ T1') E') `union` dom D') (fv_lenv lEnv) ->
  F_Related_osubst (env_remove (y, bind_typ T1') E') D' gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
  F_Rosubst (env_remove (y, bind_typ T1') E') rsubst dsubst dsubst' Env  ->
  F_Related_oterms (typ_arrow K T1' T2') rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_abs K T1' (plug (close_ec C1 y) (close_ee (shift_ee e) y))))))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_abs K T1' (plug (close_ec C1 y) (close_ee (shift_ee e') y))))))
      Env lEnv.
Proof.
    intros e e' E D T Htyp Htyp' L0 Hlr K y T1' C1 T2' E' D' H H0 H1 Hcontexting H2 IHHcontexting dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv Disj00 Disj01 Hrel_sub HRsub. 
    assert (J:=Hrel_sub). apply F_Related_osubst__inversion in J. 
    destruct J as [[[[[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe] Hwfe'] HwfEnv] HwflEnv].

    rename H into WFTV.
    
    assert (wf_typ E' T2' kn_lin) as WFT'. 
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
    apply wf_olgsubst_app_inv in EQ.
    destruct EQ as [dsubst1 [dsubst2 [gsubst1 [gsubst2 [dEQ1 [dEQ2 [dEQ3 [gEQ1 [gEQ2 gEQ3]]]]]]]]]; subst.

    assert (EQ:=Hwflg').
    apply wf_olgsubst_app_inv in EQ.
    destruct EQ as [dsubst1' [dsubst2' [gsubst1' [gsubst2' [dEQ1' [dEQ2' [dEQ3' [gEQ1' [gEQ2' gEQ3']]]]]]]]]; subst.
       
    assert (EQ:=Hwfr).
    apply wf_rsubst_app_inv in EQ.
    destruct EQ as [rsubst1 [rsubst2 [rEQ1 [rEQ2 rEQ3]]]]; subst.

    assert (wf_typ E2' T1' kn_nonlin) as WFTV'.
    apply wft_strengthen_sub with (F:=E1'); auto.

    assert (value (apply_delta_subst (dsubst1++dsubst2) (apply_gamma_subst (gsubst1++gsubst2) (apply_gamma_subst lgsubst (exp_abs K T1' (plug (close_ec C1 y) (close_ee (shift_ee e) y))))))) as Value.
      clear Disj00 Disj01.
      apply delta_gamma_lgamma_osubst_value with (Env:=Env) (lEnv:=lEnv) (E:=E1'++E2') (D:=D'); auto.
        apply FrTyping__absvalue with (L:=dom (E1'++E2') `union` dom D' `union` cv_ec (close_ec C1 y) `union` cv_ec C1 `union` dom Env `union` dom lEnv) (E:=E1'++E2') (D:=D') (T1:=T2') (K:=kn_nonlin); auto.
          intros x xnFv.
          rewrite <- shift_ee_expr with (e:=e); auto.
          assert (disjdom (fv_ee x `union` fv_te x) (cv_ec (close_ec C1 y))) as Disj.
            eapply disjdom_app_l.
            split.
              apply disjdom_one_2; auto.
              simpl. apply disjdom_nil_1.
          rewrite open_ee_plug; auto. 
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
          assert (typing (E1'++[(y, bind_typ T1')]++E2') D' (plug C1 e) T2') as Htyp2.
            apply contexting_plug_typing with (e:=e) in Hcontexting; auto.
          apply typing_nonlin_renaming_permute with (x:=y); auto.
    assert (value (apply_delta_subst (dsubst1'++dsubst2') (apply_gamma_subst (gsubst1'++gsubst2') (apply_gamma_subst lgsubst' (exp_abs K T1' (plug (close_ec C1 y)  (close_ee (shift_ee e') y))))))) as Value'.
      clear Disj00 Disj01.
      apply delta_gamma_lgamma_osubst_value with (E:=E1'++E2') (D:=D') (Env:=Env) (lEnv:=lEnv); auto.
        apply FrTyping__absvalue with (L:=dom (E1'++E2') `union` dom D' `union` cv_ec (close_ec C1 y) `union` cv_ec C1 `union` dom Env `union` dom lEnv) (E:=E1'++E2') (D:=D') (T1:=T2') (K:=kn_nonlin); auto.
          intros x xnFv.
          rewrite <- shift_ee_expr with (e:=e'); auto.
          assert (disjdom (fv_ee x `union` fv_te x) (cv_ec (close_ec C1 y))) as Disj.
            eapply disjdom_app_l.
            split.
              apply disjdom_one_2; auto.
              simpl. apply disjdom_nil_1.
          rewrite open_ee_plug; auto. 
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
          assert (typing (E1'++[(y, bind_typ T1')]++E2') D' (plug C1 e') T2') as Htyp2'.
            apply contexting_plug_typing with (e:=e') in Hcontexting; auto.
          apply typing_nonlin_renaming_permute with (x:=y); auto.
    exists (apply_delta_subst (dsubst1++dsubst2) (apply_gamma_subst (gsubst1++gsubst2) (apply_gamma_subst lgsubst (exp_abs K T1' (plug (close_ec C1 y) (close_ee (shift_ee e) y)))))).
    exists (apply_delta_subst (dsubst1'++dsubst2') (apply_gamma_subst (gsubst1'++gsubst2') (apply_gamma_subst lgsubst' (exp_abs K T1' (plug (close_ec C1 y) (close_ee (shift_ee e') y)))))).
    split.
      assert (typing (E1'++E2') D' (plug (ctx_abs_capture K y T1' (close_ec C1 y)) e) (typ_arrow K T1' T2')) as Hptyp.
        clear Disj00 Disj01.
        destruct (in_dec y (fv_ee e)) as [yine | ynine].
          simpl.
          apply typing_abs with (L:=dom (E1'++E2') `union` dom D' `union` dom E `union` dom D `union` {{y}} `union` cv_ec C1 `union` cv_ec (close_ec C1 y) `union` dom Env `union` dom lEnv); auto.
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
              apply gbinds_In_inv in yE.
              destruct yE as [t Binds].
              assert (wf_env E) as Wfe. auto.
              assert (J:=@env_remove_inv E y (bind_typ t) Wfe Binds).
              destruct J as [E1 [E2 [EQ1 EQ2]]]; subst.

              apply typing_nonlin_permute; auto. 
              apply contexting_plug_typing with (E:=E1++[(x, bind_typ t)]++E2) (D:=D) (T:=T); auto.

                apply contexting_nonlin_renaming_one; auto.

                simpl_env in xn.
                apply typing_nonlin_renaming_one with (x:=y); auto.

              contradict yD; auto.
          rewrite <- EQ1'.
          apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.
            apply contexting_abs_capture; auto.
              rewrite EQ1'. auto.
      apply typing_osubst with (dsubst:=dsubst1++dsubst2) (gsubst:=gsubst1++gsubst2) (lgsubst:=lgsubst) (Env:=Env) (lEnv:=lEnv) in Hptyp; auto.
    split.
      assert (typing (E1'++E2') D' (plug (ctx_abs_capture K y T1' (close_ec C1 y)) e') (typ_arrow K T1' T2')) as Hptyp'.
        clear Disj00 Disj01.
        destruct (in_dec y (fv_ee e')) as [yine | ynine'].
          simpl.
          apply typing_abs with (L:=dom (E1'++E2') `union` dom D' `union` dom E `union` dom D `union` cv_ec C1 `union` cv_ec (close_ec C1 y) `union` dom Env `union` dom lEnv); auto.
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
              apply gbinds_In_inv in yE.
              destruct yE as [t Binds].
              assert (wf_env E) as Wfe. auto.
              assert (J:=@env_remove_inv E y (bind_typ t) Wfe Binds).
              destruct J as [E1 [E2 [EQ1 EQ2]]]; subst.
              apply typing_nonlin_permute; auto. 
              apply contexting_plug_typing with (E:=E1++[(x, bind_typ t)]++E2) (D:=D) (T:=T); auto.
                apply contexting_nonlin_renaming_one; auto.

                simpl_env in xn.
                apply typing_nonlin_renaming_one with (x:=y); auto.

              contradict yD; auto.
          rewrite <- EQ1'.
          apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.
            apply contexting_abs_capture; auto.
              rewrite EQ1'. auto.
      apply typing_osubst with (dsubst:=dsubst1'++dsubst2') (gsubst:=gsubst1'++gsubst2') (lgsubst:=lgsubst') (Env:=Env) (lEnv:=lEnv) in Hptyp'; auto.
    split. split; auto.
    split. split; auto.
      SCase "Frel".
      apply F_Related_ovalues_arrow_req.
      split; auto.
      split; auto.
      SSCase "arrow".
        exists {}.
        intros lEnv1 x x' Htyping Htyping' Hwfle Disj Harrow_left.

        assert (lEnv1 = nil) as EQ.
          apply value_nonlin_inversion in Htyping; subst; auto.
            apply F_Related_ovalues_inversion in Harrow_left.
            decompose [prod] Harrow_left; auto.

            apply wft_osubst with (E:=E1'++E2') (dsubst:=dsubst1++dsubst2); auto.
        subst.
        assert (F_Related_ovalues T1' rsubst2 dsubst2 dsubst2' x x' Env nil) as Harrow_left'.
          apply Forel_stronger_heads with (E:=E2') (E':=E1') in Harrow_left; auto.       
            simpl. apply disjdom_sym_1. apply disjdom_nil_1.
        assert (F_Related_osubst (E1'++[(y, bind_typ T1')]++E2') D' (gsubst1++[(y,x)]++gsubst2) (gsubst1'++[(y,x')]++gsubst2') lgsubst lgsubst' (rsubst1++rsubst2) (dsubst1++dsubst2) (dsubst1'++dsubst2') Env lEnv) as Hrel_sub'.
          assert (y `notin` fv_env Env) as ynEnv.
            clear Disj01 Sub H1 Hcontexting IHHcontexting Fry dEQ3 dEQ2 dEQ3 gEQ2 gEQ3 rEQ2 rEQ3 Value Value' Disj Htyping Htyping'.
            apply disjdom_app_2 in Disj00.
            apply disjdom_app_1 in Disj00.
            apply disjdom_app_1 in Disj00.
            destruct Disj00 as [J1 J2].
            apply J1; auto.
          assert (y `notin` fv_lenv lEnv) as ynlEnv.
            clear Disj00 Sub H1 Hcontexting IHHcontexting Fry dEQ3 dEQ2 dEQ3 gEQ2 gEQ3 rEQ2 rEQ3 Value Value' Disj Htyping Htyping'.
            apply disjdom_app_2 in Disj01.
            apply disjdom_app_1 in Disj01.
            apply disjdom_app_1 in Disj01.
            destruct Disj01 as [J1 J2].
            apply J1; auto.
          clear Disj00 Disj01.
          assert (y `notin` dom E1') as ynE1'.
             apply fresh_mid_head with (E:=E2') (a:=bind_typ T1'); auto.
          assert (y `notin` dom E2') as ynE2'.
             apply fresh_mid_tail with (F:=E1') (a:=bind_typ T1'); auto.
          assert (y `notin` dom D') as ynD'.
             apply contexting_regular in Hcontexting.
             decompose [and] Hcontexting.
             apply wf_lenv_notin_fv_lenv with (x:=y) (T:=T1') in H6; auto.
          apply F_Related_osubst_gweaken; auto.
             rewrite apply_delta_osubst_typ_strenghen with (E1:=E1') (E2:=E2') (Env:=Env) in Htyping; auto.
             rewrite apply_delta_osubst_typ_strenghen with (E1:=E1') (E2:=E2') (Env:=Env) in Htyping'; auto.

        assert (F_Rosubst (E1'++[(y, bind_typ T1')] ++E2') (rsubst1++rsubst2) (dsubst1++dsubst2) (dsubst1'++dsubst2') Env) as HRsub'. 
          assert (y `notin` fv_env Env) as ynEnv.
            clear Disj01 Sub H1 Hcontexting IHHcontexting Fry dEQ3 dEQ2 dEQ3 gEQ2 gEQ3 rEQ2 rEQ3 Value Value' Disj Htyping Htyping'.
            apply disjdom_app_2 in Disj00.
            apply disjdom_app_1 in Disj00.
            apply disjdom_app_1 in Disj00.
            destruct Disj00 as [J1 J2].
            apply J1; auto.
          assert (y `notin` fv_lenv lEnv) as ynlEnv.
            clear Disj00 Sub H1 Hcontexting IHHcontexting Fry dEQ3 dEQ2 dEQ3 gEQ2 gEQ3 rEQ2 rEQ3 Value Value' Disj Htyping Htyping'.
            apply disjdom_app_2 in Disj01.
            apply disjdom_app_1 in Disj01.
            apply disjdom_app_1 in Disj01.
            destruct Disj01 as [J1 J2].
            apply J1; auto.
          clear Disj00 Disj01.
          assert (y `notin` dom E1') as ynE1'.
             apply fresh_mid_head with (E:=E2') (a:=bind_typ T1'); auto.
          assert (y `notin` dom E2') as ynE2'.
             apply fresh_mid_tail with (F:=E1') (a:=bind_typ T1'); auto.
          apply F_Rosubst_gweaken; auto.       
       assert (
       disjdom
         (union L0
            (union (cv_ec C1)
               (union (fv_ec C1)
                  (union (dom E)
                     (union (dom D)
                        (union (fv_tt T)
                           (union (fv_tt T2')
                              (union (dom (E1' ++ [(y, bind_typ T1')] ++ E2')) (dom D')))))))))
         (fv_env Env)) as Disj00'.

           clear - Disj00.
           assert (J:=@close_ec_fv_ec_eq C1 y).
           assert (J':=@close_ec_fv_ec_lower C1 y).
           apply disjdom_sym_1.
           apply disjdom_sub with (D1:=L0 `union` ({{y}} `union` (cv_ec (close_ec C1 y))) `union` (fv_ec (close_ec C1 y)) `union` dom E `union` dom D `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2') `union` (dom (E1'++E2')) `union` dom D').
             apply disjdom_sym_1; auto.
             simpl_env. rewrite J. clear - J'. fsetdec.
       assert (
       disjdom
         (union L0
            (union (cv_ec C1)
               (union (fv_ec C1)
                  (union (dom E)
                     (union (dom D)
                        (union (fv_tt T)
                           (union (fv_tt T2')
                              (union (dom (E1' ++ [(y, bind_typ T1')] ++ E2')) (dom D')))))))))
         (fv_lenv lEnv)) as Disj01'.
           clear - Disj01.
           assert (J:=@close_ec_fv_ec_eq C1 y).
           assert (J':=@close_ec_fv_ec_lower C1 y).
           apply disjdom_sym_1.
           apply disjdom_sub with (D1:=L0 `union` ({{y}} `union` (cv_ec (close_ec C1 y))) `union` (fv_ec (close_ec C1 y)) `union` dom E `union` dom D `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2') `union` (dom (E1'++E2')) `union` dom D').
             apply disjdom_sym_1; auto.
             simpl_env. rewrite J. clear - J'. fsetdec.
        assert (J:=@Fry (dsubst1++dsubst2) (dsubst1'++dsubst2') (gsubst1++[(y,x)]++gsubst2) (gsubst1'++[(y,x')]++gsubst2') lgsubst lgsubst' (rsubst1++rsubst2) Env lEnv Disj00' Disj01' Hrel_sub' HRsub').
        clear Disj00' Disj01'.
        assert (
            apply_delta_subst (dsubst1++dsubst2) (apply_gamma_subst (gsubst1++[(y,x)]++gsubst2) (apply_gamma_subst lgsubst (plug C1 e))) =
            apply_delta_subst (dsubst1++dsubst2) (apply_gamma_subst (gsubst1++gsubst2) (apply_gamma_subst lgsubst (subst_ee y x (plug C1 e))))
                  ) as Heq1. simpl.
           simpl_env.
           rewrite gamma_osubst_opt with (E':=E1') (E:=E2') (D:=D') (dsubst:=dsubst1++dsubst2) (t:=T1') (lgsubst:=lgsubst) (Env:=Env) (lEnv:=lEnv); auto.
            assert (y `notin` fv_env Env) as ynEnv.
              clear Disj01 Sub H1 Hcontexting IHHcontexting Fry dEQ3 dEQ2 dEQ3 gEQ2 gEQ3 rEQ2 rEQ3 Value Value' Disj Htyping Htyping'.
              apply disjdom_app_2 in Disj00.
              apply disjdom_app_1 in Disj00.
              apply disjdom_app_1 in Disj00.
              destruct Disj00 as [J1 J2].
              apply J1; auto.
            assert (y `notin` fv_lenv lEnv) as ynlEnv.
              clear Disj00 Sub H1 Hcontexting IHHcontexting Fry dEQ3 dEQ2 dEQ3 gEQ2 gEQ3 rEQ2 rEQ3 Value Value' Disj Htyping Htyping'.
              apply disjdom_app_2 in Disj01.
              apply disjdom_app_1 in Disj01.
              apply disjdom_app_1 in Disj01.
              destruct Disj01 as [J1 J2].
              apply J1; auto.
             clear Disj00 Disj01.
             assert (y `notin` dom (E1'++E2')) as ynE'.
               apply contexting_regular in Hcontexting.
               decompose [and] Hcontexting.
               apply uniq_from_wf_env in H5.
               simpl_env. solve_uniq.
             assert (y `notin` dom D') as ynD'.
               apply contexting_regular in Hcontexting.
               decompose [and] Hcontexting.
               apply wf_lenv_notin_fv_lenv with (x:=y) (T:=T1') in H6; auto.
             assert (JJ:=Hwflg).
             apply wf_lgamma_osubst__nfv with (x:=y) in JJ; auto.
             rewrite swap_subst_ee_olgsubst with  (D:=D') (E:=E1'++E2') (dsubst:=dsubst1++dsubst2) (t:=apply_delta_subst_typ (dsubst1++dsubst2) T1') (gsubst:=gsubst1++gsubst2) (Env:=Env) (lEnv:=lEnv) (lEnv':=nil); auto.

             apply F_Related_osubst__inversion in Hrel_sub'.
             decompose [prod] Hrel_sub'; auto.
         assert (
            apply_delta_subst (dsubst1'++dsubst2') (apply_gamma_subst (gsubst1'++[(y,x')]++gsubst2') (apply_gamma_subst lgsubst' (plug C1 e'))) =
            apply_delta_subst (dsubst1'++dsubst2') (apply_gamma_subst (gsubst1'++gsubst2') (apply_gamma_subst lgsubst' (subst_ee y x' (plug C1 e'))))
                  ) as Heq2.  simpl.
           simpl_env.
           rewrite gamma_osubst_opt with (E':=E1') (E:=E2') (D:=D') (dsubst:=dsubst1'++dsubst2') (t:=T1') (lgsubst:=lgsubst') (Env:=Env) (lEnv:=lEnv); auto.
            assert (y `notin` fv_env Env) as ynEnv.
              clear Disj01 Sub H1 Hcontexting IHHcontexting Fry dEQ3 dEQ2 dEQ3 gEQ2 gEQ3 rEQ2 rEQ3 Value Value' Disj Htyping Htyping'.
              apply disjdom_app_2 in Disj00.
              apply disjdom_app_1 in Disj00.
              apply disjdom_app_1 in Disj00.
              destruct Disj00 as [J1 J2].
              apply J1; auto.
            assert (y `notin` fv_lenv lEnv) as ynlEnv.
              clear Disj00 Sub H1 Hcontexting IHHcontexting Fry dEQ3 dEQ2 dEQ3 gEQ2 gEQ3 rEQ2 rEQ3 Value Value' Disj Htyping Htyping'.
              apply disjdom_app_2 in Disj01.
              apply disjdom_app_1 in Disj01.
              apply disjdom_app_1 in Disj01.
              destruct Disj01 as [J1 J2].
              apply J1; auto.
             clear Disj00 Disj01.
             assert (y `notin` dom (E1'++E2')) as ynE'.
               apply contexting_regular in Hcontexting.
               decompose [and] Hcontexting.
               apply uniq_from_wf_env in H5.
               simpl_env. solve_uniq.
             assert (y `notin` dom D') as ynD'.
               apply contexting_regular in Hcontexting.
               decompose [and] Hcontexting.
               apply wf_lenv_notin_fv_lenv with (x:=y) (T:=T1') in H6; auto.
             assert (JJ:=Hwflg').
             apply wf_lgamma_osubst__nfv with (x:=y) in JJ; auto.
             rewrite swap_subst_ee_olgsubst with  (D:=D') (E:=E1'++E2') (dsubst:=dsubst1'++dsubst2') (t:=apply_delta_subst_typ (dsubst1'++dsubst2') T1') (gsubst:=gsubst1'++gsubst2') (Env:=Env) (lEnv:=lEnv) (lEnv':=nil); auto.

             apply F_Related_osubst__inversion in Hrel_sub'.
             decompose [prod] Hrel_sub'; auto.
         rewrite Heq1 in J. rewrite Heq2 in J. clear Heq1 Heq2.
         destruct J as [v [v' [Ht [Ht' [[Hbrc Hv] [[Hbrc' Hv'] Hrel]]]]]].
         exists (v). exists (v').
         split.
           SSSCase "norm".
           split; auto.
           apply bigstep_red_trans with (e':=(apply_delta_subst (dsubst1++dsubst2) (apply_gamma_subst (gsubst1++gsubst2)  (apply_gamma_subst lgsubst (subst_ee y x (plug C1 e)))))); auto.
              assert (apply_delta_subst (dsubst1++dsubst2) (apply_gamma_subst (gsubst1++gsubst2) (apply_gamma_subst lgsubst x)) =x) as Heq1.
                 assert (disjdom (fv_te x) (dom (dsubst1 ++ dsubst2))) as Disj03.
                   assert (disjdom (dom (E1'++E2')) (fv_env Env)) as Disj001.
                     apply disjdom_sym_1 in Disj00.
                     apply disjdom_sub with (D2:=dom (E1'++E2')) in Disj00.
                       apply disjdom_sym_1 in Disj00; auto.
                       clear. simpl_env. fsetdec.
                   clear Disj00 Disj01.
                   split; intros x0 x0notin.
                     simpl_env. rewrite <- dEQ2. rewrite <- dEQ3.
                     clear - Htyping x0notin Disj001.
                     apply in_fv_te_typing with (X:=x0) in Htyping; auto.
                       destruct Disj001 as [J1 J2].
                       apply free_dom__free_env in Htyping.
                       apply J2 in Htyping; auto.

                     simpl_env in x0notin. rewrite <- dEQ2 in x0notin. rewrite <- dEQ3 in x0notin.
                     clear - Htyping x0notin Disj001.
                     apply notin_fv_te_typing with (X:=x0) in Htyping; auto.
                       destruct Disj001 as [J1 J2].
                       apply free_env__free_dom.
                       apply J1.
                       apply ddom__dom; simpl_env; auto.
                 assert (disjdom (fv_ee x) (dom lgsubst)) as Disj04.
                   assert (disjdom (dom (D')) (fv_env Env)) as Disj001.
                     apply disjdom_sym_1 in Disj00.
                     apply disjdom_sub with (D2:=dom (D')) in Disj00.
                       apply disjdom_sym_1 in Disj00; auto.
                       clear. simpl_env. fsetdec.
                   clear Disj00 Disj01.
                   split; intros x0 x0notin.
                     apply dom_lgamma_osubst in Hwflg.
                     decompose [and] Hwflg.
                     rewrite <- H5.
                     clear - Htyping x0notin Disj001.
                     apply in_fv_ee_typing with (x:=x0) in Htyping; auto.
                       destruct Disj001 as [J1 J2].
                       apply J2.
                       apply free_dom__free_env. fsetdec.

                     apply dom_lgamma_osubst in Hwflg.
                     decompose [and] Hwflg.
                     rewrite <- H5 in x0notin. 
                     clear - Htyping x0notin Disj001.
                     apply notin_fv_ee_typing with (y:=x0) in Htyping; auto.
                       destruct Disj001 as [J1 J2].
                       apply J1 in x0notin.
                       apply free_env__free_dom in x0notin; auto.
                 assert (disjdom (fv_ee x) (dom (gsubst1 ++ gsubst2))) as Disj05.
                   assert (disjdom (dom (E1'++E2')) (fv_env Env)) as Disj001.
                     apply disjdom_sym_1 in Disj00.
                     apply disjdom_sub with (D2:=dom (E1'++E2')) in Disj00.
                       apply disjdom_sym_1 in Disj00; auto.
                       clear. simpl_env. fsetdec.
                   clear Disj00 Disj01.
                   split; intros x0 x0notin.
                     simpl_env. rewrite <- gEQ2. rewrite <- gEQ3.
                     clear - Htyping x0notin Disj001.
                     apply in_fv_ee_typing with (x:=x0) in Htyping; auto.
                       destruct Disj001 as [J1 J2].
                       assert (x0 `in` dom Env) as J. fsetdec.
                       apply free_dom__free_env in J.
                       apply J2 in J.
                       apply dom__gdom in J.
                       simpl_env in J; auto.

                     simpl_env in x0notin. rewrite <- gEQ2 in x0notin. rewrite <- gEQ3 in x0notin.
                     clear - Htyping x0notin Disj001.
                     apply notin_fv_ee_typing with (y:=x0) in Htyping; auto.
                       destruct Disj001 as [J1 J2].
                       assert (x0 `in` gdom_env (E1'++E2')) as J. simpl_env. assumption.
                       apply gdom__dom in J.                
                       apply J1 in J.
                       apply free_env__free_dom in J. auto.
                 clear Disj00 Disj01.
                 rewrite gamma_osubst_closed_exp; auto.
                 rewrite gamma_osubst_closed_exp; auto.
                 rewrite delta_osubst_closed_exp; auto.                   
                 rewrite gamma_osubst_closed_exp; auto.
              rewrite <- Heq1.
              rewrite commut_gamma_subst_abs.
              rewrite commut_gamma_subst_abs.
              assert (subst_ee y (apply_delta_subst  (dsubst1++dsubst2) (apply_gamma_subst  (gsubst1++gsubst2) (apply_gamma_subst lgsubst x))) (plug C1 e) = subst_ee y x (plug C1 e)) as Heq2. 
                 rewrite Heq1. auto. 
              rewrite Heq2.
              assert (typing (E1'++[(y, bind_typ T1')]++E2') D' (plug C1 e) T2') as Typinge.
                apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.

             assert (disjdom (union {{y}} (fv_ee x `union` fv_te x)) (cv_ec C1)) as Disj0.
               eapply disjdom_app_l.
               split.
                 clear Disj00 Disj01.
                 apply disjdom_one_2; auto.
               eapply disjdom_app_l.
               split.
                  clear - Htyping Disj00.
                  apply typing_fv_ee_upper in Htyping.
                  apply disjdom_sym_1.
                  simpl in Htyping.
                  apply disjdom_sub with (D1:= dom Env `union` {}); auto.
                  apply disjdom_sub with (D1:= fv_env Env).
                    assert (J:=@close_ec_fv_ec_eq C1 y).
                    apply disjdom_sym_1.
                    apply disjdom_sub with (D1:=L0 `union` ({{y}} `union` (cv_ec (close_ec C1 y))) `union` (fv_ec (close_ec C1 y)) `union` dom E `union` dom D `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2') `union` (dom (E1'++E2')) `union` dom D').
                      apply disjdom_sym_1; auto.
                      simpl_env. rewrite J. clear. fsetdec.                                       
                    assert (J:=@fv_env__includes__dom Env). clear - J. fsetdec.

                  clear - Htyping Disj00.
                  apply typing_fv_te_upper in Htyping.
                  apply disjdom_sym_1.
                  apply disjdom_sub with (D1:= dom Env `union` {}); auto.
                    apply disjdom_sub with (D1:= fv_env Env).
                      assert (J:=@close_ec_fv_ec_eq C1 y).
                      apply disjdom_sym_1.
                      apply disjdom_sub with (D1:=L0 `union` ({{y}} `union` (cv_ec (close_ec C1 y))) `union` (fv_ec (close_ec C1 y)) `union` dom E `union` dom D `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2') `union` (dom (E1'++E2')) `union` dom D').
                        apply disjdom_sym_1; auto.
                        simpl_env. rewrite J. clear. fsetdec.                                       
                      assert (J:=@fv_env__includes__dom Env). clear - J. fsetdec.
                    simpl_env. fsetdec.

              rewrite subst_ee_plug; auto.
              rewrite <- close_open_ee__subst_ee; auto.
              assert (context C1) as Context1.
                apply contexting__context in Hcontexting; auto.    
              rewrite <- close_open_ec__subst_ec; auto.
              assert (disjdom (fv_ee x `union` fv_te x) (cv_ec (close_ec C1 y))) as Disj1.
                eapply disjdom_app_l.
                split.
                  clear - Htyping Disj00.
                  apply typing_fv_ee_upper in Htyping.
                  apply disjdom_sym_1.
                  simpl in Htyping.
                  apply disjdom_sub with (D1:= dom Env `union` {}); auto.
                  apply disjdom_sub with (D1:= fv_env Env).
                    assert (J:=@close_ec_fv_ec_eq C1 y).
                    apply disjdom_sym_1.
                    apply disjdom_sub with (D1:=L0 `union` ({{y}} `union` (cv_ec (close_ec C1 y))) `union` (fv_ec (close_ec C1 y)) `union` dom E `union` dom D `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2') `union` (dom (E1'++E2')) `union` dom D').
                      apply disjdom_sym_1; auto.
                      simpl_env. rewrite J. clear. fsetdec.                                       
                    assert (J:=@fv_env__includes__dom Env). clear - J. fsetdec.

                  clear - Htyping Disj00.
                  apply typing_fv_te_upper in Htyping.
                  apply disjdom_sym_1.
                  apply disjdom_sub with (D1:= dom Env `union` {}); auto.
                    apply disjdom_sub with (D1:= fv_env Env).
                      assert (J:=@close_ec_fv_ec_eq C1 y).
                      apply disjdom_sym_1.
                      apply disjdom_sub with (D1:=L0 `union` ({{y}} `union` (cv_ec (close_ec C1 y))) `union` (fv_ec (close_ec C1 y)) `union` dom E `union` dom D `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2') `union` (dom (E1'++E2')) `union` dom D').
                        apply disjdom_sym_1; auto.
                        simpl_env. rewrite J. clear. fsetdec.                                       
                      assert (J:=@fv_env__includes__dom Env). clear - J. fsetdec.
                    simpl_env. fsetdec.

              rewrite <- open_ee_plug; auto.
              rewrite commut_lgamma_osubst_open_ee with (E:=E1'++E2')(D:=D')(dsubst:=dsubst1++dsubst2)(gsubst:=gsubst1++gsubst2) (Env:=Env) (lEnv:=lEnv); auto.
              rewrite commut_gamma_osubst_open_ee with (E:=E1'++E2')(D:=D')(dsubst:=dsubst1++dsubst2)(lgsubst:=lgsubst) (Env:=Env) (lEnv:=lEnv); auto.
              rewrite <- shift_ee_expr; auto.
              apply red_abs_preserved_under_delta_osubst with (dE:=E1'++E2') (Env:=Env); auto.

              rewrite <- commut_gamma_subst_abs; auto.
              rewrite <- commut_gamma_osubst_open_ee with (E:=E1'++E2') (dsubst:=dsubst1++dsubst2) (D:=D') (lgsubst:=lgsubst) (Env:=Env) (lEnv:=lEnv); auto.
              apply red_abs_preserved_under_gamma_osubst with (E:=E1'++E2') (dsubst:=dsubst1++dsubst2) (D:=D') (lgsubst:=lgsubst) (Env:=Env) (lEnv:=lEnv); auto. 

              rewrite <- commut_gamma_subst_abs; auto.
              rewrite <- commut_lgamma_osubst_open_ee with (E:=E1'++E2')(D:=D')(dsubst:=dsubst1++dsubst2)(gsubst:=gsubst1++gsubst2) (Env:=Env) (lEnv:=lEnv); auto.
              apply red_abs_preserved_under_lgamma_osubst with (E:=E1'++E2')(D:=D')(dsubst:=dsubst1++dsubst2)(gsubst:=gsubst1++gsubst2) (Env:=Env) (lEnv:=lEnv); auto. 

              apply red_abs.
                apply expr_abs with (L:=(cv_ec (close_ec C1 y)) `union` cv_ec C1).
                   apply type_from_wf_typ in WFTV; assumption.

                   intros.
                   assert (disjdom (fv_ee x0 `union` fv_te x0) (cv_ec (close_ec C1 y))) as Disj'.
                     eapply disjdom_app_l.
                     split.
                       clear Disj00 Disj01.
                       apply disjdom_one_2; auto.
                       simpl. apply disjdom_nil_1.
                   rewrite open_ee_plug; auto.
                   rewrite close_open_ec__subst_ec; auto.
                   rewrite close_open_ee__subst_ee; auto.
                  assert (disjdom (union {{y}} (fv_ee x0 `union` fv_te x0)) (cv_ec C1)) as Disj0'.
                     eapply disjdom_app_l.
                     split.
                       clear Disj00 Disj01.
                       apply disjdom_one_2; auto.
                     eapply disjdom_app_l.
                     split.
                       clear Disj00 Disj01.
                       apply disjdom_one_2; auto.
                       simpl. apply disjdom_nil_1.
                   rewrite <- subst_ee_plug; auto.

               apply F_Related_ovalues_inversion in Harrow_left'.
               decompose [prod] Harrow_left'; auto.
         split; auto.
           SSSCase "norm".
           split; auto.
           apply bigstep_red_trans with (e':=(apply_delta_subst (dsubst1'++dsubst2') (apply_gamma_subst (gsubst1'++gsubst2') (apply_gamma_subst lgsubst' (subst_ee y x' (plug C1 e')))))); auto.
              assert (apply_delta_subst (dsubst1'++dsubst2') (apply_gamma_subst (gsubst1'++gsubst2') (apply_gamma_subst lgsubst' x')) =x') as Heq1'.
                 assert (disjdom (fv_te x') (dom (dsubst1' ++ dsubst2'))) as Disj03.
                   assert (disjdom (dom (E1'++E2')) (fv_env Env)) as Disj001.
                     apply disjdom_sym_1 in Disj00.
                     apply disjdom_sub with (D2:=dom (E1'++E2')) in Disj00.
                       apply disjdom_sym_1 in Disj00; auto.
                       clear. simpl_env. fsetdec.
                   clear Disj00 Disj01.
                   split; intros x0 x0notin.
                     simpl_env. rewrite <- dEQ2'. rewrite <- dEQ3'.
                     clear - Htyping' x0notin Disj001.
                     apply in_fv_te_typing with (X:=x0) in Htyping'; auto.
                       destruct Disj001 as [J1 J2].
                       apply free_dom__free_env in Htyping'.
                       apply J2 in Htyping'; auto.

                     simpl_env in x0notin. rewrite <- dEQ2' in x0notin. rewrite <- dEQ3' in x0notin.
                     clear - Htyping' x0notin Disj001.
                     apply notin_fv_te_typing with (X:=x0) in Htyping'; auto.
                       destruct Disj001 as [J1 J2].
                       apply free_env__free_dom.
                       apply J1.
                       apply ddom__dom; simpl_env; auto.
                 assert (disjdom (fv_ee x') (dom lgsubst')) as Disj04.
                   assert (disjdom (dom (D')) (fv_env Env)) as Disj001.
                     apply disjdom_sym_1 in Disj00.
                     apply disjdom_sub with (D2:=dom (D')) in Disj00.
                       apply disjdom_sym_1 in Disj00; auto.
                       clear. simpl_env. fsetdec.
                   clear Disj00 Disj01.
                   split; intros x0 x0notin.
                     apply dom_lgamma_osubst in Hwflg'.
                     decompose [and] Hwflg'.
                     rewrite <- H5.
                     clear - Htyping' x0notin Disj001.
                     apply in_fv_ee_typing with (x:=x0) in Htyping'; auto.
                       destruct Disj001 as [J1 J2].
                       apply J2.
                       apply free_dom__free_env. fsetdec.

                     apply dom_lgamma_osubst in Hwflg'.
                     decompose [and] Hwflg'.
                     rewrite <- H5 in x0notin. 
                     clear - Htyping' x0notin Disj001.
                     apply notin_fv_ee_typing with (y:=x0) in Htyping'; auto.
                       destruct Disj001 as [J1 J2].
                       apply J1 in x0notin.
                       apply free_env__free_dom in x0notin; auto.
                 assert (disjdom (fv_ee x') (dom (gsubst1' ++ gsubst2'))) as Disj05.
                   assert (disjdom (dom (E1'++E2')) (fv_env Env)) as Disj001.
                     apply disjdom_sym_1 in Disj00.
                     apply disjdom_sub with (D2:=dom (E1'++E2')) in Disj00.
                       apply disjdom_sym_1 in Disj00; auto.
                       clear. simpl_env. fsetdec.
                   clear Disj00 Disj01.
                   split; intros x0 x0notin.
                     simpl_env. rewrite <- gEQ2'. rewrite <- gEQ3'.
                     clear - Htyping' x0notin Disj001.
                     apply in_fv_ee_typing with (x:=x0) in Htyping'; auto.
                       destruct Disj001 as [J1 J2].
                       assert (x0 `in` dom Env) as J. fsetdec.
                       apply free_dom__free_env in J.
                       apply J2 in J.
                       apply dom__gdom in J.
                       simpl_env in J; auto.

                     simpl_env in x0notin. rewrite <- gEQ2' in x0notin. rewrite <- gEQ3' in x0notin.
                     clear - Htyping' x0notin Disj001.
                     apply notin_fv_ee_typing with (y:=x0) in Htyping'; auto.
                       destruct Disj001 as [J1 J2].
                       assert (x0 `in` gdom_env (E1'++E2')) as J. simpl_env. assumption.
                       apply gdom__dom in J.                
                       apply J1 in J.
                       apply free_env__free_dom in J. auto.
                 clear Disj00 Disj01.
                 rewrite gamma_osubst_closed_exp; auto.
                 rewrite gamma_osubst_closed_exp; auto.
                 rewrite delta_osubst_closed_exp; auto.                   
                 rewrite gamma_osubst_closed_exp; auto.
              rewrite <- Heq1'.
              rewrite commut_gamma_subst_abs.
              rewrite commut_gamma_subst_abs.
              assert (subst_ee y (apply_delta_subst  (dsubst1'++dsubst2') (apply_gamma_subst  (gsubst1'++gsubst2') (apply_gamma_subst lgsubst' x'))) (plug C1 e') = subst_ee y x' (plug C1 e')) as Heq2'. 
                 rewrite Heq1'. auto. 
              rewrite Heq2'.
              assert (typing (E1'++[(y, bind_typ T1')]++E2') D' (plug C1 e') T2') as Typinge'.
                apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.
             assert (disjdom (union {{y}} (fv_ee x' `union` fv_te x')) (cv_ec C1)) as Disj0.
               eapply disjdom_app_l.
               split.
                 clear Disj00 Disj01.
                 apply disjdom_one_2; auto.
               eapply disjdom_app_l.
               split.
                  clear - Htyping' Disj00.
                  apply typing_fv_ee_upper in Htyping'.
                  apply disjdom_sym_1.
                  simpl in Htyping'.
                  apply disjdom_sub with (D1:= dom Env `union` {}); auto.
                  apply disjdom_sub with (D1:= fv_env Env).
                    assert (J:=@close_ec_fv_ec_eq C1 y).
                    apply disjdom_sym_1.
                    apply disjdom_sub with (D1:=L0 `union` ({{y}} `union` (cv_ec (close_ec C1 y))) `union` (fv_ec (close_ec C1 y)) `union` dom E `union` dom D `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2') `union` (dom (E1'++E2')) `union` dom D').
                      apply disjdom_sym_1; auto.
                      simpl_env. rewrite J. clear. fsetdec.                                       
                    assert (J:=@fv_env__includes__dom Env). clear - J. fsetdec.

                  clear - Htyping' Disj00.
                  apply typing_fv_te_upper in Htyping'.
                  apply disjdom_sym_1.
                  apply disjdom_sub with (D1:= dom Env `union` {}); auto.
                    apply disjdom_sub with (D1:= fv_env Env).
                      assert (J:=@close_ec_fv_ec_eq C1 y).
                      apply disjdom_sym_1.
                      apply disjdom_sub with (D1:=L0 `union` ({{y}} `union` (cv_ec (close_ec C1 y))) `union` (fv_ec (close_ec C1 y)) `union` dom E `union` dom D `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2') `union` (dom (E1'++E2')) `union` dom D').
                        apply disjdom_sym_1; auto.
                        simpl_env. rewrite J. clear. fsetdec.                                       
                      assert (J:=@fv_env__includes__dom Env). clear - J. fsetdec.
                    simpl_env. fsetdec.

              rewrite subst_ee_plug; auto.
              rewrite <- close_open_ee__subst_ee; auto.
              assert (context C1) as Context1.
                apply contexting__context in Hcontexting; auto.    
              rewrite <- close_open_ec__subst_ec; auto.
              assert (disjdom (fv_ee x' `union` fv_te x') (cv_ec (close_ec C1 y))) as Disj1.
                eapply disjdom_app_l.
                split.
                  clear - Htyping' Disj00.
                  apply typing_fv_ee_upper in Htyping'.
                  apply disjdom_sym_1.
                  simpl in Htyping'.
                  apply disjdom_sub with (D1:= dom Env `union` {}); auto.
                  apply disjdom_sub with (D1:= fv_env Env).
                    assert (J:=@close_ec_fv_ec_eq C1 y).
                    apply disjdom_sym_1.
                    apply disjdom_sub with (D1:=L0 `union` ({{y}} `union` (cv_ec (close_ec C1 y))) `union` (fv_ec (close_ec C1 y)) `union` dom E `union` dom D `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2') `union` (dom (E1'++E2')) `union` dom D').
                      apply disjdom_sym_1; auto.
                      simpl_env. rewrite J. clear. fsetdec.                                       
                    assert (J:=@fv_env__includes__dom Env). clear - J. fsetdec.

                  clear - Htyping' Disj00.
                  apply typing_fv_te_upper in Htyping'.
                  apply disjdom_sym_1.
                  apply disjdom_sub with (D1:= dom Env `union` {}); auto.
                    apply disjdom_sub with (D1:= fv_env Env).
                      assert (J:=@close_ec_fv_ec_eq C1 y).
                      apply disjdom_sym_1.
                      apply disjdom_sub with (D1:=L0 `union` ({{y}} `union` (cv_ec (close_ec C1 y))) `union` (fv_ec (close_ec C1 y)) `union` dom E `union` dom D `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2') `union` (dom (E1'++E2')) `union` dom D').
                        apply disjdom_sym_1; auto.
                        simpl_env. rewrite J. clear. fsetdec.                                       
                      assert (J:=@fv_env__includes__dom Env). clear - J. fsetdec.
                    simpl_env. fsetdec.

              rewrite <- open_ee_plug; auto.
              rewrite commut_lgamma_osubst_open_ee with (E:=E1'++E2')(D:=D')(dsubst:=dsubst1'++dsubst2')(gsubst:=gsubst1'++gsubst2') (Env:=Env) (lEnv:=lEnv); auto.
              rewrite commut_gamma_osubst_open_ee with (E:=E1'++E2')(D:=D')(dsubst:=dsubst1'++dsubst2')(lgsubst:=lgsubst') (Env:=Env) (lEnv:=lEnv); auto.
              rewrite <- shift_ee_expr; auto.
              apply red_abs_preserved_under_delta_osubst with (dE:=E1'++E2') (Env:=Env); auto.

              rewrite <- commut_gamma_subst_abs; auto.
              rewrite <- commut_gamma_osubst_open_ee with (E:=E1'++E2') (dsubst:=dsubst1'++dsubst2') (D:=D') (lgsubst:=lgsubst') (Env:=Env) (lEnv:=lEnv); auto.
              apply red_abs_preserved_under_gamma_osubst with (E:=E1'++E2') (dsubst:=dsubst1'++dsubst2') (D:=D') (lgsubst:=lgsubst') (Env:=Env) (lEnv:=lEnv); auto. 

              rewrite <- commut_gamma_subst_abs; auto.
              rewrite <- commut_lgamma_osubst_open_ee with (E:=E1'++E2')(D:=D')(dsubst:=dsubst1'++dsubst2')(gsubst:=gsubst1'++gsubst2') (Env:=Env) (lEnv:=lEnv); auto.
              apply red_abs_preserved_under_lgamma_osubst with (E:=E1'++E2')(D:=D')(dsubst:=dsubst1'++dsubst2')(gsubst:=gsubst1'++gsubst2') (Env:=Env) (lEnv:=lEnv); auto. 

              apply red_abs.
                apply expr_abs with (L:=cv_ec (close_ec C1 y) `union` cv_ec C1).
                   apply type_from_wf_typ in WFTV; assumption.

                   intros.
                   assert (disjdom (fv_ee x0 `union` fv_te x0) (cv_ec (close_ec C1 y))) as Disj'.
                     eapply disjdom_app_l.
                     split.
                       clear Disj00 Disj01.
                       apply disjdom_one_2; auto.
                       simpl. apply disjdom_nil_1.
                   rewrite open_ee_plug; auto.
                   rewrite close_open_ec__subst_ec; auto.
                   rewrite close_open_ee__subst_ee; auto.
                  assert (disjdom (union {{y}} (fv_ee x0 `union` fv_te x0)) (cv_ec C1)) as Disj0'.
                    eapply disjdom_app_l.
                    split.
                      clear Disj00 Disj01.
                      apply disjdom_one_2; auto.
                    eapply disjdom_app_l.
                    split.
                      clear Disj00 Disj01.
                      apply disjdom_one_2; auto.
                      simpl. apply disjdom_nil_1.
                   rewrite <- subst_ee_plug; auto.

               apply F_Related_ovalues_inversion in Harrow_left'.
               decompose [prod] Harrow_left'; auto.
Qed.

Lemma F_ological_related_congruence__labs_capture :
  forall e e' E D T,
  typing E D e T ->
  typing E D e' T ->
  forall L0,
  (forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
   disjdom L0 (fv_env Env) ->
   disjdom L0 (fv_lenv lEnv) ->
   F_Related_osubst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
   F_Rosubst E rsubst dsubst dsubst' Env ->
   F_Related_oterms T rsubst dsubst dsubst' 
     (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
     (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e')))
     Env lEnv
  ) ->
  forall K y T1' C1 T2' E' D',
  wf_typ E' T1' kn_lin ->
  binds y (lbind_typ T1') D' ->
  y `notin` gdom_env E `union` cv_ec C1 ->
  contexting E D T C1 E' D' T2' ->
  (K = kn_nonlin -> lenv_remove (y, lbind_typ T1') D' = lempty) ->
  (typing E D e T ->
   typing E D e' T ->
    (forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
     disjdom L0 (fv_env Env) ->
     disjdom L0 (fv_lenv lEnv) ->
     F_Related_osubst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
     F_Rosubst E rsubst dsubst dsubst' Env ->
     F_Related_oterms T rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e')))
      Env lEnv
    ) ->
   forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
     disjdom (L0 `union` cv_ec C1 `union` fv_ec C1 `union` dom E `union` dom D `union` fv_tt T `union` fv_tt T2' `union` dom E' `union` dom D') (fv_env Env) ->
     disjdom (L0 `union` cv_ec C1 `union` fv_ec C1 `union` dom E `union` dom D `union` fv_tt T `union` fv_tt T2' `union` dom E' `union` dom D') (fv_lenv lEnv) ->
     F_Related_osubst E' D' gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
     F_Rosubst E' rsubst dsubst dsubst' Env ->
     F_Related_oterms T2' rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (plug C1 e))))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (plug C1 e'))))
      Env lEnv
  ) ->
  forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
  disjdom (L0 `union` ({{y}} `union` cv_ec (close_ec C1 y)) `union` fv_ec (close_ec C1 y) `union` dom E `union` dom D `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2') `union` dom E' `union` dom (lenv_remove (y, lbind_typ T1') D')) (fv_env Env) ->
  disjdom (L0 `union` ({{y}} `union` cv_ec (close_ec C1 y)) `union` fv_ec (close_ec C1 y) `union` dom E `union` dom D `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2') `union` dom E' `union` dom (lenv_remove (y, lbind_typ T1') D')) (fv_lenv lEnv) ->
  F_Related_osubst E' (lenv_remove (y, lbind_typ T1') D') gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
  F_Rosubst E' rsubst dsubst dsubst' Env  ->
  F_Related_oterms (typ_arrow K T1' T2') rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_abs K T1' (plug (close_ec C1 y) (close_ee (shift_ee e) y))))))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_abs K T1' (plug (close_ec C1 y) (close_ee (shift_ee e') y))))))
      Env lEnv.
Proof.
    intros e e' E D T Htyp Htyp' L0 Hlr K y T1' C1 T2' E' D' H H0 H1 Hcontexting H2 IHHcontexting dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv Disj00 Disj01 Hrel_sub HRsub.  
    assert (J:=Hrel_sub). apply F_Related_osubst__inversion in J. 
    destruct J as [[[[[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe] Hwfe'] HwfEnv] HwflEnv].

    rename H into WFTV.
    
    assert (wf_typ E' T2' kn_lin) as WFT'. 
      apply contexting_regular in Hcontexting.
      decompose [and] Hcontexting; auto.
    assert (Fry := @IHHcontexting Htyp Htyp' Hlr).
    assert (wf_lenv E' D') as Wfle'.
      apply contexting_regular in Hcontexting.
      decompose [and] Hcontexting; auto.
    assert (EQ1:=@lenv_remove_inv E' D' y (lbind_typ T1')  Wfle' H0).
    destruct EQ1 as [D1' [D2' [EQ1' EQ2']]]; subst.
    rewrite EQ1' in *.

    assert (EQ:=Hrel_sub).
    apply F_Related_olgsubst_lapp_inv in EQ.
    destruct EQ as [lgsubst1 [lgsubst2 [lgsubst1' [lgsubst2' [lEnv1 [lEnv2 [gEQ1 [gEQ2 [gEQ3 [gEQ4 [gEQ5 [gEQ6 [gEQ7 [Hrel_sub1 Hrel_sub2]]]]]]]]]]]]]]; subst.

    assert (value (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst (lgsubst1++lgsubst2) (exp_abs K T1' (plug (close_ec C1 y) (close_ee (shift_ee e) y))))))) as Value.
      clear Disj00 Disj01.
      apply delta_gamma_lgamma_osubst_value with (E:=E') (D:=D1'++D2') (Env:=Env) (lEnv:=lEnv1++lEnv2); auto.
        apply FrTyping__labsvalue with (L:=dom E' `union` dom (D1'++D2') `union` cv_ec (close_ec C1 y) `union` cv_ec C1) (D:=D1'++D2') (E:=E') (T1:=T2') (K:=kn_lin); auto.
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
    assert (value (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst (lgsubst1'++lgsubst2') (exp_abs K T1' (plug (close_ec C1 y)  (close_ee (shift_ee e') y))))))) as Value'.
      clear Disj00 Disj01.
      apply delta_gamma_lgamma_osubst_value with (E:=E') (D:=D1'++D2') (Env:=Env) (lEnv:=lEnv1++lEnv2); auto.
        apply FrTyping__labsvalue with (L:=dom E' `union` dom (D1'++D2') `union` cv_ec (close_ec C1 y) `union` cv_ec C1) (D:=D1'++D2') (E:=E') (T1:=T2') (K:=kn_lin); auto.
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
    exists (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst (lgsubst1++lgsubst2) (exp_abs K T1' (plug (close_ec C1 y) (close_ee (shift_ee e) y)))))).
    exists (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst (lgsubst1'++lgsubst2') (exp_abs K T1' (plug (close_ec C1 y) (close_ee (shift_ee e') y)))))).
    split. 
      clear Disj00 Disj01.
      assert (typing E' (D1'++D2') (plug (ctx_abs_capture K y T1' (close_ec C1 y)) e) (typ_arrow K T1' T2')) as Hptyp.
        destruct (in_dec y (fv_ee e)) as [yine | ynine].
          simpl.
          apply typing_labs with (L:=dom (D1'++D2') `union` dom E' `union` dom E `union` dom D `union` cv_ec C1 `union` cv_ec (close_ec C1 y) `union` dom Env `union` dom lEnv1 `union` dom lEnv2); auto.
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
              clear - J. fsetdec.
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
            apply contexting_labs_capture; auto.
              intros J. apply H2 in J.
              rewrite lenv_remove_opt; auto.
              apply uniq_from_wf_lenv in Wfle'. assumption.
               
      apply typing_osubst with (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst1++lgsubst2) (Env:=Env) (lEnv:=lEnv1++lEnv2) in Hptyp; auto.
    split.
      clear Disj00 Disj01.
      assert (typing E' (D1'++D2') (plug (ctx_abs_capture K y T1' (close_ec C1 y)) e') (typ_arrow K T1' T2')) as Hptyp'.
        destruct (in_dec y (fv_ee e')) as [yine' | ynine'].
          simpl.
          apply typing_labs with (L:=dom (D1'++D2') `union` dom E' `union` dom D `union` dom E `union` cv_ec C1 `union` cv_ec (close_ec C1 y) `union` dom Env `union` dom lEnv1 `union` dom lEnv2); auto.
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
              clear - J.
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
            apply contexting_labs_capture; auto.
              intros J. apply H2 in J.
              rewrite lenv_remove_opt; auto.
              apply uniq_from_wf_lenv in Wfle'. assumption.
      apply typing_osubst with (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst1'++lgsubst2') (Env:=Env) (lEnv:=lEnv1++lEnv2) in Hptyp'; auto.
    split. split; auto.
    split. split; auto.
      SCase "Frel".
      apply F_Related_ovalues_arrow_req.
      split; auto.
      split; auto.
      SSCase "arrow".
        exists (L0 `union` (cv_ec C1) `union` (fv_ec C1) `union` (fv_tt T) `union` (fv_tt T1') `union` (fv_tt T2') `union`  
                       dom gsubst `union` dom lgsubst1 `union` dom lgsubst2  `union` dom gsubst' `union` dom lgsubst1' `union` dom lgsubst2'  `union` dom E `union` dom D `union` dom Env `union` dom lEnv1 `union` dom lEnv2 `union` {{y}} `union` dom E' `union` dom D1' `union` dom D2').
        intros lEnv x x' Htyping Htyping' Hwfle Disj' Harrow_left.

        assert (F_Related_osubst E' (D1'++[(y, lbind_typ T1')]++D2') gsubst gsubst' (lgsubst1++[(y,x)]++lgsubst2) (lgsubst1'++[(y,x')]++lgsubst2') rsubst dsubst dsubst' Env (lEnv1++lEnv++lEnv2)) as Hrel_sub'.        
          assert (y `notin` fv_env Env) as ynEnv.
            clear - Disj00.
            apply disjdom_app_2 in Disj00.
            apply disjdom_app_1 in Disj00.
            apply disjdom_app_1 in Disj00.
            destruct Disj00 as [J1 J2].
            apply J1; auto.
          assert (y `notin` fv_lenv (lEnv1++lEnv2)) as ynlEnv12.
            clear - Disj01.
            apply disjdom_app_2 in Disj01.
            apply disjdom_app_1 in Disj01.
            apply disjdom_app_1 in Disj01.
            destruct Disj01 as [J1 J2].
            apply J1; auto.
          assert (y `notin` dom lEnv) as ynlEnv.
            clear - Disj'.
            apply disjdom_app_2 in Disj'.
            apply disjdom_app_2 in Disj'.
            apply disjdom_app_2 in Disj'.
            apply disjdom_app_2 in Disj'.
            apply disjdom_app_2 in Disj'.
            apply disjdom_app_2 in Disj'.
            apply disjdom_app_2 in Disj'.
            apply disjdom_app_2 in Disj'.
            apply disjdom_app_2 in Disj'.
            apply disjdom_app_2 in Disj'.
            apply disjdom_app_2 in Disj'.
            apply disjdom_app_2 in Disj'.
            apply disjdom_app_2 in Disj'.
            apply disjdom_app_2 in Disj'.
            apply disjdom_app_2 in Disj'.
            apply disjdom_app_2 in Disj'.
            apply disjdom_app_2 in Disj'.
            apply disjdom_app_1 in Disj'.
            destruct Disj' as [J1 J2]. auto.
          clear Disj00 Disj01.
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
           apply wf_lenv_notin_dom with (x:=y) (T:=T1') in H6; auto.
         simpl_env in ynlEnv12.
         apply F_Related_osubst_lgweaken; auto.
           apply disjdom__disjoint.
           apply disjdom_sym_1 in Disj'.           
           apply disjdom_sub with (D2:=dom E') in Disj'; auto.
             clear. fsetdec.

           apply disjdom__disjoint.
           apply disjdom_sym_1 in Disj'.           
           apply disjdom_sub with (D2:=dom (D1'++D2')) in Disj'; auto.
             clear. simpl_env. fsetdec.

          apply wf_lenv_merge.
            rewrite_env (nil ++ lEnv++(lEnv1++lEnv2)) in Hwfle.
            apply wf_lenv_lin_strengthening' in Hwfle.
            rewrite_env (lEnv1++lEnv2++nil) in Hwfle.
            apply wf_lenv_lin_strengthening' in Hwfle.
            simpl_env in Hwfle. assumption.

            apply wf_lenv_lin_strengthening' in Hwfle; auto.

            apply uniq_from_wf_lenv in Hwfle.
            clear - Hwfle.
            solve_uniq.
     
          apply F_Related_osubst__inversion in Hrel_sub1.  
          decompose [prod] Hrel_sub1; auto.

          apply F_Related_osubst__inversion in Hrel_sub2.  
          decompose [prod] Hrel_sub2; auto.

       assert (
       disjdom
         (union L0
            (union (cv_ec C1)
               (union (fv_ec C1)
                  (union (dom E)
                     (union (dom D)
                        (union (fv_tt T)
                           (union (fv_tt T2')
                              (union (dom E') (dom (D1' ++ [(y, lbind_typ T1')] ++ D2'))))))))))
         (fv_env Env)) as Disj00'.
           clear - Disj00.
           assert (J:=@close_ec_fv_ec_eq C1 y).
           assert (J':=@close_ec_fv_ec_lower C1 y).
           apply disjdom_sym_1.
           apply disjdom_sub with (D1:=L0 `union` ({{y}} `union` (cv_ec (close_ec C1 y))) `union` (fv_ec (close_ec C1 y)) `union` dom E `union` dom D `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2') `union` dom E' `union` dom (D1'++D2')).
             apply disjdom_sym_1; auto.
             simpl_env. rewrite J. clear - J'. fsetdec.
       assert (
       disjdom
         (union L0
            (union (cv_ec C1)
               (union (fv_ec C1)
                  (union (dom E)
                     (union (dom D)
                        (union (fv_tt T)
                           (union (fv_tt T2')
                              (union (dom E') (dom (D1' ++ [(y, lbind_typ T1')] ++ D2'))))))))))
         (fv_lenv (lEnv1++lEnv++lEnv2))) as Disj01'.
           clear - Disj01 Disj' Disj00 Htyping WFTV.
           assert (J:=@close_ec_fv_ec_eq C1 y).
           assert (J':=@close_ec_fv_ec_lower C1 y).
           apply disjdom_sym_1.
           apply disjdom_sub with (D1:=L0 `union` ({{y}} `union` (cv_ec (close_ec C1 y))) `union` (fv_ec (close_ec C1 y)) `union` dom E `union` dom D `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2') `union` dom E' `union` (dom (D1'++D2'))).
             apply disjdom_eq with (D1:=fv_lenv (lEnv1++lEnv2) `union` fv_lenv lEnv).
               eapply disjdom_app_l.
               split.
                 apply disjdom_sym_1; auto.
                 apply disjdom_sym_1.
                   apply disjdom_fv_lenv_wfle with (Env:=Env); auto.
                     clear - Disj00.
                     apply disjdom_sub with (D1:=fv_env Env); auto.
                        apply fv_env__includes__dom.

                     clear - Disj'.
                     assert (J:=@close_ec_fv_ec_eq C1 y).
                     assert (J':=@close_ec_fv_ec_upper C1 y).
                     apply disjdom_sym_1 in Disj'.
                     apply disjdom_sub with (D2:=L0 `union` ({{y}} `union` cv_ec (close_ec C1 y)) `union` fv_ec (close_ec C1 y) `union` dom E `union` dom D `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2') `union` dom E' `union` dom (D1'++D2')) in Disj'.
                       apply disjdom_sym_1; auto. 
                       rewrite J. clear - J'. simpl_env. fsetdec.
               simpl_env. clear. fsetdec.
             simpl_env. rewrite J. clear - J'. fsetdec.
        assert (J:=@Fry dsubst dsubst' gsubst gsubst' (lgsubst1++[(y,x)]++lgsubst2) (lgsubst1'++[(y,x')]++lgsubst2') rsubst Env (lEnv1++lEnv++lEnv2) Disj00' Disj01' Hrel_sub' HRsub).
        assert (
            apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst (lgsubst1++[(y,x)]++lgsubst2) (plug C1 e))) =
            apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst (lgsubst1++lgsubst2) (subst_ee y x (plug C1 e))))
                  ) as Heq1.
           simpl_env.
           rewrite lgamma_osubst_opt with (D':=D1') (D:=D2') (E:=E') (dsubst:=dsubst) (t:=T1') (gsubst:=gsubst) (Env:=Env) (lEnv':=lEnv1) (lEnv0:=lEnv) (lEnv:=lEnv2); auto.
             apply F_Related_osubst__inversion in Hrel_sub'.
             decompose [prod] Hrel_sub'; auto.

             apply F_Related_osubst__inversion in Hrel_sub2.
             decompose [prod] Hrel_sub2; auto.

             apply F_Related_osubst__inversion in Hrel_sub1.
             decompose [prod] Hrel_sub1; auto.
         assert (
            apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst  (lgsubst1'++[(y,x')]++lgsubst2') (plug C1 e'))) =
            apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst  (lgsubst1'++lgsubst2') (subst_ee y x' (plug C1 e'))))
                  ) as Heq2.
           simpl_env.
           rewrite lgamma_osubst_opt with (D':=D1') (D:=D2') (E:=E') (dsubst:=dsubst') (t:=T1') (gsubst:=gsubst') (Env:=Env) (lEnv':=lEnv1) (lEnv0:=lEnv) (lEnv:=lEnv2); auto.
             apply F_Related_osubst__inversion in Hrel_sub'.
             decompose [prod] Hrel_sub'; auto.

             apply F_Related_osubst__inversion in Hrel_sub2.
             decompose [prod] Hrel_sub2; auto.

             apply F_Related_osubst__inversion in Hrel_sub1.
             decompose [prod] Hrel_sub1; auto.
         rewrite Heq1 in J. rewrite Heq2 in J. clear Heq1 Heq2.
         destruct J as [v [v' [Ht [Ht' [[Hbrc Hv] [[Hbrc' Hv'] Hrel]]]]]].
         exists (v). exists (v').
         split.
           SSSCase "norm".
           split; auto.
           apply bigstep_red_trans with (e':=(apply_delta_subst dsubst (apply_gamma_subst gsubst  (apply_gamma_subst (lgsubst1++lgsubst2) (subst_ee y x (plug C1 e)))))); auto.
              assert (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst (lgsubst1++lgsubst2) x)) =x) as Heq1.
                 assert (disjdom (fv_te x) (dom dsubst)) as Disj03.
                   assert (disjdom (dom E') (fv_env Env)) as Disj001.
                     apply disjdom_sym_1 in Disj00.
                     apply disjdom_sub with (D2:=dom E') in Disj00.
                       apply disjdom_sym_1 in Disj00; auto.
                       clear. simpl_env. fsetdec.
                   clear Disj00 Disj01.
                   split; intros x0 x0notin.
                     apply dom_delta_osubst in Hwfd.
                     rewrite <- Hwfd.
                     clear - Htyping x0notin Disj001.
                     apply in_fv_te_typing with (X:=x0) in Htyping; auto.
                       destruct Disj001 as [J1 J2].
                       apply free_dom__free_env in Htyping.
                       apply J2 in Htyping; auto.

                     apply dom_delta_osubst in Hwfd.
                     rewrite <- Hwfd in x0notin. 
                     clear - Htyping x0notin Disj001.
                     apply notin_fv_te_typing with (X:=x0) in Htyping; auto.
                       destruct Disj001 as [J1 J2].
                       apply free_env__free_dom.
                       apply J1.
                       apply ddom__dom; simpl_env; auto.
                 assert (disjdom (fv_ee x) (dom (lgsubst1++lgsubst2))) as Disj04.
                   assert (disjdom (dom (D1'++D2')) (fv_env Env)) as Disj001.
                     apply disjdom_sym_1 in Disj00.
                     apply disjdom_sub with (D2:=dom (D1'++D2')) in Disj00.
                       apply disjdom_sym_1 in Disj00; auto.
                       clear. simpl_env. fsetdec.
                   assert (disjdom (dom (D1'++D2')) (dom lEnv)) as Disj002.
                     apply disjdom_sym_1 in Disj'.
                     apply disjdom_sub with (D2:=dom (D1'++D2')) in Disj'.
                       apply disjdom_sym_1 in Disj'; auto.
                       clear. simpl_env. fsetdec.
                   clear Disj00 Disj01.
                   split; intros x0 x0notin.
                     simpl_env. rewrite <- gEQ3. rewrite <- gEQ4.
                     clear - Htyping x0notin Disj001 Disj002.
                     apply in_fv_ee_typing with (x:=x0) in Htyping; auto.
                     assert (x0 `in` dom Env \/ x0 `in` dom lEnv) as J.
                       clear - Htyping.  fsetdec.
                     destruct J as [J | J].
                       destruct Disj001 as [J1 J2].
                       apply free_dom__free_env in J.
                       apply J2 in J. simpl_env in J. auto.

                       destruct Disj002 as [J1 J2].
                       apply J2 in J. simpl_env in J. auto.

                     simpl_env in x0notin. rewrite <- gEQ3 in x0notin. rewrite <- gEQ4 in x0notin.
                     clear - Htyping x0notin Disj001 Disj002.
                     apply notin_fv_ee_typing with (y:=x0) in Htyping; auto.
                     assert (x0 `in` dom (D1'++D2')) as J. 
                       clear - x0notin. simpl_env. fsetdec.
                     assert (J':=J).
                     destruct Disj001 as [J1 J2].
                     apply J1 in J.
                     apply free_env__free_dom in J.

                     destruct Disj002 as [J3 J4].
                     apply J3 in J'.
                     auto.
                 assert (disjdom (fv_ee x) (dom gsubst)) as Disj05.
                   assert (disjdom (dom E') (fv_env Env)) as Disj001.
                     apply disjdom_sym_1 in Disj00.
                     apply disjdom_sub with (D2:=dom E') in Disj00.
                       apply disjdom_sym_1 in Disj00; auto.
                       clear. simpl_env. fsetdec.
                   assert (disjdom (dom E') (dom lEnv)) as Disj002.
                     apply disjdom_sym_1 in Disj'.
                     apply disjdom_sub with (D2:=dom E') in Disj'.
                       apply disjdom_sym_1 in Disj'; auto.
                       clear. simpl_env. fsetdec.
                   clear Disj00 Disj01.
                   split; intros x0 x0notin.
                     apply dom_lgamma_osubst in Hwflg.
                     decompose [and] Hwflg.
                     rewrite <- H4.
                     clear - Htyping x0notin Disj001 Disj002.
                     apply in_fv_ee_typing with (x:=x0) in Htyping; auto.
                     assert (x0 `in` dom Env \/ x0 `in` dom lEnv) as J.
                       clear - Htyping.  fsetdec.
                     destruct J as [J | J].
                       destruct Disj001 as [J1 J2].
                       apply free_dom__free_env in J.
                       apply J2 in J.
                       apply dom__gdom in J; auto.

                       destruct Disj002 as [J1 J2].
                       apply J2 in J.
                       apply dom__gdom in J; auto.

                     apply dom_lgamma_osubst in Hwflg.
                     decompose [and] Hwflg.
                     rewrite <- H4 in x0notin.
                     clear - Htyping x0notin Disj001 Disj002.
                     apply notin_fv_ee_typing with (y:=x0) in Htyping; auto.
                     assert (J:=x0notin).
                     destruct Disj001 as [J1 J2].
                     apply gdom__dom in J.                
                     apply J1 in J.
                     apply free_env__free_dom in J.
                     destruct Disj002 as [J3 J4].
                     apply gdom__dom in x0notin.                
                     apply J3 in x0notin. auto.
                 clear Disj00 Disj01.
                 rewrite gamma_osubst_closed_exp; auto.
                 rewrite gamma_osubst_closed_exp; auto.
                 rewrite delta_osubst_closed_exp; auto.
                 rewrite gamma_osubst_closed_exp; auto.
              rewrite <- Heq1.
              rewrite commut_gamma_subst_abs.
              rewrite commut_gamma_subst_abs.
              assert (subst_ee y (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst (lgsubst1++lgsubst2) x))) (plug C1 e) = subst_ee y x (plug C1 e)) as Heq2. 
                 rewrite Heq1. auto. 
              rewrite Heq2.
              assert (typing E' (D1'++[(y, lbind_typ T1')]++D2') (plug C1 e) T2') as Typinge.
                apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.
             assert (disjdom (union {{y}} (fv_ee x `union` fv_te x)) (cv_ec C1)) as Disj0.
               eapply disjdom_app_l.
               split.
                 clear - H1.
                 apply disjdom_one_2; auto.
               eapply disjdom_app_l.
               split.
                  clear - Htyping Disj00 Disj'.
                  apply typing_fv_ee_upper in Htyping.
                  apply disjdom_sym_1.
                  simpl in Htyping.
                  apply disjdom_sub with (D1:= dom Env `union` dom lEnv); auto.
                  apply disjdom_sub with (D1:= fv_env Env `union` dom lEnv).
                    eapply disjdom_app_r.
                    split.
                      clear - Disj00.
                      assert (J:=@close_ec_fv_ec_eq C1 y).
                      apply disjdom_sub with (D1:=L0 `union` ({{y}} `union` (cv_ec (close_ec C1 y))) `union` (fv_ec (close_ec C1 y)) `union` dom E `union` dom D `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2') `union` (dom E') `union` dom ((D1'++D2'))).
                        apply disjdom_sym_1; auto.
                        simpl_env. rewrite J. clear. fsetdec.                                       

                      clear - Disj'.
                      apply disjdom_sym_1 in Disj'.
                      apply disjdom_sub with (D2:=cv_ec C1) in Disj'; auto.
                        clear. fsetdec.                                       
                    assert (J:=@fv_env__includes__dom Env). clear - J. fsetdec.

                  clear - Htyping Disj00.
                  apply typing_fv_te_upper in Htyping.
                  apply disjdom_sym_1.
                  apply disjdom_sub with (D1:= dom Env `union` {}); auto.
                    apply disjdom_sub with (D1:= fv_env Env).
                      assert (J:=@close_ec_fv_ec_eq C1 y).
                      apply disjdom_sym_1.
                      apply disjdom_sub with (D1:=L0 `union` ({{y}} `union` (cv_ec (close_ec C1 y))) `union` (fv_ec (close_ec C1 y)) `union` dom E `union` dom D `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2') `union` (dom E') `union` dom (D1'++D2')).
                        apply disjdom_sym_1; auto.
                        simpl_env. rewrite J. clear. fsetdec.                                       
                      assert (J:=@fv_env__includes__dom Env). clear - J. fsetdec.
                    simpl_env. fsetdec.

              rewrite subst_ee_plug; auto.
              rewrite <- close_open_ee__subst_ee; auto.
              assert (context C1) as Context1.
                apply contexting__context in Hcontexting; auto.    
              rewrite <- close_open_ec__subst_ec; auto.
              assert (disjdom (fv_ee x `union` fv_te x) (cv_ec (close_ec C1 y))) as Disj.
               eapply disjdom_app_l.
               split.
                  clear - Htyping Disj00 Disj'.
                  apply typing_fv_ee_upper in Htyping.
                  apply disjdom_sym_1.
                  simpl in Htyping.
                  apply disjdom_sub with (D1:= dom Env `union` dom lEnv); auto.
                  apply disjdom_sub with (D1:= fv_env Env `union` dom lEnv).
                    eapply disjdom_app_r.
                    split.
                      clear - Disj00.
                      assert (J:=@close_ec_fv_ec_eq C1 y).
                      apply disjdom_sub with (D1:=L0 `union` ({{y}} `union` (cv_ec (close_ec C1 y))) `union` (fv_ec (close_ec C1 y)) `union` dom E `union` dom D `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2') `union` (dom E') `union` dom ((D1'++D2'))).
                        apply disjdom_sym_1; auto.
                        simpl_env. rewrite J. clear. fsetdec.                                       

                      clear - Disj'.
                      apply disjdom_sym_1 in Disj'.
                      assert (J:=@close_ec_fv_ec_eq C1 y).
                      apply disjdom_sub with (D2:=cv_ec (close_ec C1 y)) in Disj'; auto.
                        rewrite J. clear. fsetdec.                                       
                    assert (J:=@fv_env__includes__dom Env). clear - J. fsetdec.

                  clear - Htyping Disj00.
                  apply typing_fv_te_upper in Htyping.
                  apply disjdom_sym_1.
                  apply disjdom_sub with (D1:= dom Env `union` {}); auto.
                    apply disjdom_sub with (D1:= fv_env Env).
                      assert (J:=@close_ec_fv_ec_eq C1 y).
                      apply disjdom_sym_1.
                      apply disjdom_sub with (D1:=L0 `union` ({{y}} `union` (cv_ec (close_ec C1 y))) `union` (fv_ec (close_ec C1 y)) `union` dom E `union` dom D `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2') `union` (dom E') `union` dom (D1'++D2')).
                        apply disjdom_sym_1; auto.
                        simpl_env. rewrite J. clear. fsetdec.                                       
                      assert (J:=@fv_env__includes__dom Env). clear - J. fsetdec.
                    simpl_env. fsetdec.

              rewrite <- open_ee_plug; auto.
              rewrite commut_lgamma_osubst_open_ee with (D:=D1'++D2')(E:=E')(dsubst:=dsubst)(gsubst:=gsubst) (Env:=Env) (lEnv:=lEnv1++lEnv2); auto.
              rewrite commut_gamma_osubst_open_ee with (D:=D1'++D2')(E:=E')(dsubst:=dsubst)(lgsubst:=lgsubst1++lgsubst2) (Env:=Env) (lEnv:=lEnv1++lEnv2); auto.
              rewrite <- shift_ee_expr; auto.
              apply red_abs_preserved_under_delta_osubst with (dE:=E') (Env:=Env); auto.

              rewrite <- commut_gamma_subst_abs; auto.
              rewrite <- commut_gamma_osubst_open_ee with (D:=D1'++D2') (dsubst:=dsubst) (E:=E') (lgsubst:=lgsubst1++lgsubst2) (Env:=Env) (lEnv:=lEnv1++lEnv2); auto.
              apply red_abs_preserved_under_gamma_osubst with (D:=D1'++D2') (dsubst:=dsubst) (E:=E')(lgsubst:=lgsubst1++lgsubst2) (Env:=Env) (lEnv:=lEnv1++lEnv2); auto.

              rewrite <- commut_gamma_subst_abs; auto.
              rewrite <- commut_lgamma_osubst_open_ee with (D:=D1'++D2')(E:=E')(dsubst:=dsubst)(gsubst:=gsubst) (Env:=Env) (lEnv:=lEnv1++lEnv2); auto.
              apply red_abs_preserved_under_lgamma_osubst with (D:=D1'++D2')(E:=E')(dsubst:=dsubst)(gsubst:=gsubst) (Env:=Env) (lEnv:=lEnv1++lEnv2); auto. 

              apply red_abs.
                apply expr_abs with (L:=cv_ec (close_ec C1 y) `union` cv_ec C1).
                   apply type_from_wf_typ in WFTV; assumption.

                   intros.
                   assert (disjdom (fv_ee x0 `union` fv_te x0) (cv_ec (close_ec C1 y))) as Disj0'.
                     eapply disjdom_app_l.
                     split.
                       clear - H.
                       apply disjdom_one_2; auto.
                       simpl. apply disjdom_nil_1.
                   rewrite open_ee_plug; auto.
                   rewrite close_open_ec__subst_ec; auto.
                   rewrite close_open_ee__subst_ee; auto.
                  assert (disjdom (union {{y}} (fv_ee x0 `union` fv_te x0)) (cv_ec C1)) as Disj1'.
                     eapply disjdom_app_l.
                     split.
                       clear - H1.
                       apply disjdom_one_2; auto.
                     eapply disjdom_app_l.
                     split.
                       clear - H.
                       apply disjdom_one_2; auto.
                       simpl. apply disjdom_nil_1.
                   rewrite <- subst_ee_plug; auto.
               apply F_Related_ovalues_inversion in Harrow_left.
               decompose [prod] Harrow_left; auto.
         split; auto.
           SSSCase "norm".
           split; auto.
           apply bigstep_red_trans with (e':=(apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst (lgsubst1'++lgsubst2') (subst_ee y x' (plug C1 e')))))); auto.
              assert (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst (lgsubst1'++lgsubst2') x')) =x') as Heq1'.
                 assert (disjdom (fv_te x') (dom dsubst')) as Disj03.
                   assert (disjdom (dom E') (fv_env Env)) as Disj001.
                     apply disjdom_sym_1 in Disj00.
                     apply disjdom_sub with (D2:=dom E') in Disj00.
                       apply disjdom_sym_1 in Disj00; auto.
                       clear. simpl_env. fsetdec.
                   clear Disj00 Disj01.
                   split; intros x0 x0notin.
                     apply dom_delta_osubst in Hwfd'.
                     rewrite <- Hwfd'.
                     clear - Htyping' x0notin Disj001.
                     apply in_fv_te_typing with (X:=x0) in Htyping'; auto.
                       destruct Disj001 as [J1 J2].
                       apply free_dom__free_env in Htyping'.
                       apply J2 in Htyping'; auto.

                     apply dom_delta_osubst in Hwfd'.
                     rewrite <- Hwfd' in x0notin. 
                     clear - Htyping' x0notin Disj001.
                     apply notin_fv_te_typing with (X:=x0) in Htyping'; auto.
                       destruct Disj001 as [J1 J2].
                       apply free_env__free_dom.
                       apply J1.
                       apply ddom__dom; simpl_env; auto.
                 assert (disjdom (fv_ee x') (dom (lgsubst1'++lgsubst2'))) as Disj04.
                   assert (disjdom (dom (D1'++D2')) (fv_env Env)) as Disj001.
                     apply disjdom_sym_1 in Disj00.
                     apply disjdom_sub with (D2:=dom (D1'++D2')) in Disj00.
                       apply disjdom_sym_1 in Disj00; auto.
                       clear. simpl_env. fsetdec.
                   assert (disjdom (dom (D1'++D2')) (dom lEnv)) as Disj002.
                     apply disjdom_sym_1 in Disj'.
                     apply disjdom_sub with (D2:=dom (D1'++D2')) in Disj'.
                       apply disjdom_sym_1 in Disj'; auto.
                       clear. simpl_env. fsetdec.
                   clear Disj00 Disj01.
                   split; intros x0 x0notin.
                     simpl_env. rewrite <- gEQ5. rewrite <- gEQ6.
                     clear - Htyping' x0notin Disj001 Disj002.
                     apply in_fv_ee_typing with (x:=x0) in Htyping'; auto.
                     assert (x0 `in` dom Env \/ x0 `in` dom lEnv) as J.
                       clear - Htyping'.  fsetdec.
                     destruct J as [J | J].
                       destruct Disj001 as [J1 J2].
                       apply free_dom__free_env in J.
                       apply J2 in J. simpl_env in J. auto.

                       destruct Disj002 as [J1 J2].
                       apply J2 in J. simpl_env in J. auto.

                     simpl_env in x0notin. rewrite <- gEQ5 in x0notin. rewrite <- gEQ6 in x0notin.
                     clear - Htyping' x0notin Disj001 Disj002.
                     apply notin_fv_ee_typing with (y:=x0) in Htyping'; auto.
                     assert (x0 `in` dom (D1'++D2')) as J. 
                       clear - x0notin. simpl_env. fsetdec.
                     assert (J':=J).
                     destruct Disj001 as [J1 J2].
                     apply J1 in J.
                     apply free_env__free_dom in J.

                     destruct Disj002 as [J3 J4].
                     apply J3 in J'.
                     auto.
                 assert (disjdom (fv_ee x') (dom gsubst')) as Disj05.
                   assert (disjdom (dom E') (fv_env Env)) as Disj001.
                     apply disjdom_sym_1 in Disj00.
                     apply disjdom_sub with (D2:=dom E') in Disj00.
                       apply disjdom_sym_1 in Disj00; auto.
                       clear. simpl_env. fsetdec.
                   assert (disjdom (dom E') (dom lEnv)) as Disj002.
                     apply disjdom_sym_1 in Disj'.
                     apply disjdom_sub with (D2:=dom E') in Disj'.
                       apply disjdom_sym_1 in Disj'; auto.
                       clear. simpl_env. fsetdec.
                   clear Disj00 Disj01.
                   split; intros x0 x0notin.
                     apply dom_lgamma_osubst in Hwflg'.
                     decompose [and] Hwflg'.
                     rewrite <- H4.
                     clear - Htyping' x0notin Disj001 Disj002.
                     apply in_fv_ee_typing with (x:=x0) in Htyping'; auto.
                     assert (x0 `in` dom Env \/ x0 `in` dom lEnv) as J.
                       clear - Htyping'.  fsetdec.
                     destruct J as [J | J].
                       destruct Disj001 as [J1 J2].
                       apply free_dom__free_env in J.
                       apply J2 in J.
                       apply dom__gdom in J; auto.

                       destruct Disj002 as [J1 J2].
                       apply J2 in J.
                       apply dom__gdom in J; auto.

                     apply dom_lgamma_osubst in Hwflg'.
                     decompose [and] Hwflg'.
                     rewrite <- H4 in x0notin.
                     clear - Htyping' x0notin Disj001 Disj002.
                     apply notin_fv_ee_typing with (y:=x0) in Htyping'; auto.
                     assert (J:=x0notin).
                     destruct Disj001 as [J1 J2].
                     apply gdom__dom in J.                
                     apply J1 in J.
                     apply free_env__free_dom in J.
                     destruct Disj002 as [J3 J4].
                     apply gdom__dom in x0notin.                
                     apply J3 in x0notin. auto.
                 clear Disj00 Disj01.
                 rewrite gamma_osubst_closed_exp; auto.
                 rewrite gamma_osubst_closed_exp; auto.
                 rewrite delta_osubst_closed_exp; auto.
                 rewrite gamma_osubst_closed_exp; auto.
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
                 clear - H1.
                 apply disjdom_one_2; auto.
               eapply disjdom_app_l.
               split.
                  clear - Htyping' Disj00 Disj'.
                  apply typing_fv_ee_upper in Htyping'.
                  apply disjdom_sym_1.
                  simpl in Htyping'.
                  apply disjdom_sub with (D1:= dom Env `union` dom lEnv); auto.
                  apply disjdom_sub with (D1:= fv_env Env `union` dom lEnv).
                    eapply disjdom_app_r.
                    split.
                      clear - Disj00.
                      assert (J:=@close_ec_fv_ec_eq C1 y).
                      apply disjdom_sub with (D1:=L0 `union` ({{y}} `union` (cv_ec (close_ec C1 y))) `union` (fv_ec (close_ec C1 y)) `union` dom E `union` dom D `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2') `union` (dom E') `union` dom ((D1'++D2'))).
                        apply disjdom_sym_1; auto.
                        simpl_env. rewrite J. clear. fsetdec.                                       

                      clear - Disj'.
                      apply disjdom_sym_1 in Disj'.
                      apply disjdom_sub with (D2:=cv_ec C1) in Disj'; auto.
                        clear. fsetdec.                                       
                    assert (J:=@fv_env__includes__dom Env). clear - J. fsetdec.

                  clear - Htyping' Disj00.
                  apply typing_fv_te_upper in Htyping'.
                  apply disjdom_sym_1.
                  apply disjdom_sub with (D1:= dom Env `union` {}); auto.
                    apply disjdom_sub with (D1:= fv_env Env).
                      assert (J:=@close_ec_fv_ec_eq C1 y).
                      apply disjdom_sym_1.
                      apply disjdom_sub with (D1:=L0 `union` ({{y}} `union` (cv_ec (close_ec C1 y))) `union` (fv_ec (close_ec C1 y)) `union` dom E `union` dom D `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2') `union` (dom E') `union` dom (D1'++D2')).
                        apply disjdom_sym_1; auto.
                        simpl_env. rewrite J. clear. fsetdec.                                       
                      assert (J:=@fv_env__includes__dom Env). clear - J. fsetdec.
                    simpl_env. fsetdec.

              rewrite subst_ee_plug; auto.
              rewrite <- close_open_ee__subst_ee; auto.
              assert (context C1) as Context1.
                apply contexting__context in Hcontexting; auto.    
              rewrite <- close_open_ec__subst_ec; auto.
              assert (disjdom (fv_ee x' `union` fv_te x') (cv_ec (close_ec C1 y))) as Disj.
                eapply disjdom_app_l.
                split.
                  clear - Htyping' Disj00 Disj'.
                  apply typing_fv_ee_upper in Htyping'.
                  apply disjdom_sym_1.
                  simpl in Htyping'.
                  apply disjdom_sub with (D1:= dom Env `union` dom lEnv); auto.
                  apply disjdom_sub with (D1:= fv_env Env `union` dom lEnv).
                    eapply disjdom_app_r.
                    split.
                      clear - Disj00.
                      assert (J:=@close_ec_fv_ec_eq C1 y).
                      apply disjdom_sub with (D1:=L0 `union` ({{y}} `union` (cv_ec (close_ec C1 y))) `union` (fv_ec (close_ec C1 y)) `union` dom E `union` dom D `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2') `union` (dom E') `union` dom ((D1'++D2'))).
                        apply disjdom_sym_1; auto.
                        simpl_env. rewrite J. clear. fsetdec.                                       

                      clear - Disj'.
                      apply disjdom_sym_1 in Disj'.
                      assert (J:=@close_ec_fv_ec_eq C1 y).
                      apply disjdom_sub with (D2:=cv_ec (close_ec C1 y)) in Disj'; auto.
                        rewrite J. clear. fsetdec.                                       
                    assert (J:=@fv_env__includes__dom Env). clear - J. fsetdec.

                  clear - Htyping' Disj00.
                  apply typing_fv_te_upper in Htyping'.
                  apply disjdom_sym_1.
                  apply disjdom_sub with (D1:= dom Env `union` {}); auto.
                    apply disjdom_sub with (D1:= fv_env Env).
                      assert (J:=@close_ec_fv_ec_eq C1 y).
                      apply disjdom_sym_1.
                      apply disjdom_sub with (D1:=L0 `union` ({{y}} `union` (cv_ec (close_ec C1 y))) `union` (fv_ec (close_ec C1 y)) `union` dom E `union` dom D `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2') `union` (dom E') `union` dom (D1'++D2')).
                        apply disjdom_sym_1; auto.
                        simpl_env. rewrite J. clear. fsetdec.                                       
                      assert (J:=@fv_env__includes__dom Env). clear - J. fsetdec.
                    simpl_env. fsetdec.

              rewrite <- open_ee_plug; auto.
              rewrite commut_lgamma_osubst_open_ee with (D:=D1'++D2')(E:=E')(dsubst:=dsubst')(gsubst:=gsubst') (Env:=Env) (lEnv:=lEnv1++lEnv2); auto.
              rewrite commut_gamma_osubst_open_ee with (D:=D1'++D2')(E:=E')(dsubst:=dsubst')(lgsubst:=lgsubst1'++lgsubst2') (Env:=Env) (lEnv:=lEnv1++lEnv2); auto.
              rewrite <- shift_ee_expr; auto.
              apply red_abs_preserved_under_delta_osubst with (dE:=E') (Env:=Env); auto.

              rewrite <- commut_gamma_subst_abs; auto.
              rewrite <- commut_gamma_osubst_open_ee with (D:=D1'++D2') (dsubst:=dsubst') (E:=E') (lgsubst:=lgsubst1'++lgsubst2') (Env:=Env) (lEnv:=lEnv1++lEnv2); auto.
              apply red_abs_preserved_under_gamma_osubst with (D:=D1'++D2') (dsubst:=dsubst') (E:=E')(lgsubst:=lgsubst1'++lgsubst2') (Env:=Env) (lEnv:=lEnv1++lEnv2); auto.

              rewrite <- commut_gamma_subst_abs; auto.
              rewrite <- commut_lgamma_osubst_open_ee with (D:=D1'++D2')(E:=E')(dsubst:=dsubst')(gsubst:=gsubst') (Env:=Env) (lEnv:=lEnv1++lEnv2); auto.
              apply red_abs_preserved_under_lgamma_osubst with (D:=D1'++D2')(E:=E')(dsubst:=dsubst')(gsubst:=gsubst') (Env:=Env) (lEnv:=lEnv1++lEnv2); auto. 

              apply red_abs.
                apply expr_abs with (L:=cv_ec (close_ec C1 y) `union` cv_ec C1).
                   apply type_from_wf_typ in WFTV; assumption.

                   intros.
                   assert (disjdom (fv_ee x0 `union` fv_te x0) (cv_ec (close_ec C1 y))) as Disj0.
                     eapply disjdom_app_l.
                     split.
                       clear - H.
                       apply disjdom_one_2; auto.
                       simpl. apply disjdom_nil_1.
                   rewrite open_ee_plug; auto.
                   rewrite close_open_ec__subst_ec; auto.
                   rewrite close_open_ee__subst_ee; auto.
                  assert (disjdom (union {{y}} (fv_ee x0 `union` fv_te x0)) (cv_ec C1)) as Disj1'.
                     eapply disjdom_app_l.
                     split.
                       clear - H1.
                       apply disjdom_one_2; auto.
                     eapply disjdom_app_l.
                     split.
                       clear - H.
                       apply disjdom_one_2; auto.
                       simpl. apply disjdom_nil_1.
                   rewrite <- subst_ee_plug; auto.
               apply F_Related_ovalues_inversion in Harrow_left.
               decompose [prod] Harrow_left; auto.
           SSSCase "Rel".
             apply Forel_lin_domeq with (lEnv:=lEnv1++lEnv++lEnv2); auto.
               clear. simpl_env. fsetdec.
Qed.

Lemma F_ological_related_congruence__app1 :
  forall e e' E D T,
  typing E D e T ->
  typing E D e' T ->
  forall L0,
  (forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
   disjdom L0 (fv_env Env) ->
   disjdom L0 (fv_lenv lEnv) ->
   F_Related_osubst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
   F_Rosubst E rsubst dsubst dsubst' Env ->
   F_Related_oterms T rsubst dsubst dsubst' 
     (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
     (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e')))
     Env lEnv
  ) ->
  forall T1' K  E' D1' D2' D3' C1 e2 T2',
  contexting E D T C1 E' D1' (typ_arrow K T1' T2') ->
  typing E' D2' e2 T1' ->
  lenv_split E' D1' D2' D3' ->
  disjdom (fv_ee e2) (dom D) ->
  (typing E D e T ->
   typing E D e' T ->
    (forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
     disjdom L0 (fv_env Env) ->
     disjdom L0 (fv_lenv lEnv) ->
     F_Related_osubst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
     F_Rosubst E rsubst dsubst dsubst' Env ->
     F_Related_oterms T rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e')))
      Env lEnv
    ) ->
   forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
     disjdom (L0 `union` cv_ec C1 `union` fv_ec C1 `union` dom E `union` dom D `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2') `union` dom E' `union` dom D1') (fv_env Env) ->
     disjdom (L0 `union` cv_ec C1 `union` fv_ec C1 `union` dom E `union` dom D `union` fv_tt T `union` (fv_tt T1' `union` fv_tt T2')  `union` dom E' `union` dom D1') (fv_lenv lEnv) ->
     F_Related_osubst E' D1' gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
     F_Rosubst E' rsubst dsubst dsubst' Env ->
     F_Related_oterms (typ_arrow K T1' T2') rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (plug C1 e))))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (plug C1 e'))))
      Env lEnv
  ) ->
  forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
  disjdom (L0 `union` cv_ec C1 `union` (fv_ec C1 `union` fv_ee e2) `union` dom E `union` dom D `union` fv_tt T `union` fv_tt T2' `union` dom E' `union` dom D3') (fv_env Env) ->
  disjdom (L0 `union` cv_ec C1 `union` (fv_ec C1 `union` fv_ee e2) `union` dom E `union` dom D `union` fv_tt T `union` fv_tt T2' `union` dom E' `union` dom D3') (fv_lenv lEnv) ->
  F_Related_osubst E' D3' gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
  F_Rosubst E' rsubst dsubst dsubst' Env  ->
  F_Related_oterms T2' rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_app (plug C1 e) e2))))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_app (plug C1 e') e2))))
      Env lEnv.
Proof.
    intros e e' E D T Htyp Htyp' L0 Hlr T1' K E' D1' D2' D3' C1 e2 T2' Hcontexting H H0 H1 IHHcontexting dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv Disj00 Disj01 Hrel_sub HRsub.  
   assert (J:=Hrel_sub). apply F_Related_osubst__inversion in J. 
   destruct J as [[[[[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe] Hwfe'] HwfEnv] HwflEnv].
   apply F_Related_osubst_split with (lE1:=D1') (lE2:=D2') in Hrel_sub; auto.
   destruct Hrel_sub as [lgsubst1 [lgsubst1' [lgsubst2 [lgsubst2' [lEnv1 [lEnv2 [J1 [J2 [J3 J4]]]]]]]]].

   assert (
      F_Related_oterms (typ_arrow K T1' T2') rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst1 (plug C1 e))))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst1' (plug C1 e'))))
         Env lEnv1
     ) as FR_ArrowType.
    apply IHHcontexting; auto.
      clear - Disj00 H0 H.
      apply dom_lenv_split in H0.
      apply typing_regular in H.
      destruct H as [_ [_ [_ H]]].
      apply wft_fv_tt_sub in H.
      apply disjdom_sym_1.
      apply disjdom_sub with (D1:=L0 `union` cv_ec C1 `union` (fv_ec C1 `union` fv_ee e2) `union` dom E `union` dom D `union` fv_tt T  `union` fv_tt T2' `union` dom E' `union` dom D3').
        apply disjdom_sym_1; auto.
        clear Disj00. rewrite H0. clear H0. fsetdec.        

      clear - Disj01 H0 J1 H.
      apply dom_lenv_split in H0.
      apply lgamma_osubst_split__lenv_split in J1.
      apply fv_lenv_split in J1.
      apply typing_regular in H.
      destruct H as [_ [_ [_ H]]].
      apply wft_fv_tt_sub in H.
      apply disjdom_sym_1.
      apply disjdom_sub with (D1:=L0 `union` cv_ec C1 `union` (fv_ec C1 `union` fv_ee e2) `union` dom E `union` dom D `union` fv_tt T `union` fv_tt T2' `union` dom E' `union` dom D3').
        apply disjdom_sym_1.
        apply disjdom_sub with (D1:=fv_lenv lEnv); auto.
          rewrite J1. clear. fsetdec.
        clear Disj01. rewrite H0. clear H0 J1. fsetdec.        
   destruct FR_ArrowType as [v [v' [Ht [Ht' [Hn [Hn' Hrel]]]]]].

   clear Disj00 Disj01.

   apply F_Related_ovalues_arrow_leq in Hrel.
   destruct Hrel as [Hv [Hv' [L Harrow]]]; subst.

   assert (
      F_Related_oterms T1' rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst2 e2)))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst'(apply_gamma_subst lgsubst2' e2)))
         Env lEnv2
     ) as FR_T1.
    apply oparametricity with (E:=E') (lE:=D2'); auto.
   destruct FR_T1 as [v0 [v'0 [Ht1 [Ht1' [Hn1 [Hn1' Hrel_wft1]]]]]].

   assert (lenv_split Env lEnv1 lEnv2 lEnv) as Split.
     apply lgamma_osubst_split__lenv_split in J1. auto.

   assert (uniq lEnv2) as Uniq2.
     apply typing_regular in Ht1. destruct Ht1 as [JJ1 [JJ2 [JJ3 JJ4]]].
     apply uniq_from_wf_lenv in JJ2; auto.
   assert (JJ:=@pick_lenv (L `union` dom lEnv2 `union` dom lEnv `union` dom lEnv1 `union` dom Env `union` dom E' `union` dom D1' `union` dom D2' `union` dom D3' `union` dom E `union` dom D) lEnv2 Uniq2).
   destruct JJ as [asubst [Wfa [lEnv2_eq_asubst Disj]]].
   assert (disjoint asubst Env) as Disj1.
     apply disjoint_split_right in Split.
     apply disjoint_eq with (D1:=lEnv2); auto.
   assert (disjdom (atom_subst_codom asubst) (union (dom Env) (dom lEnv2))) as Disj2.
     apply disjdom_sym_1 in Disj.
     apply disjdom_sub with (D2:=union (dom Env) (dom lEnv2)) in Disj; try solve [assumption].
     clear. fsetdec.
   destruct (@Harrow (subst_atoms_lenv asubst lEnv2) (subst_atoms_exp asubst v0) (subst_atoms_exp asubst v'0)) as [u [u' [Hnorm_vxu [Hnorm_v'x'u' Hrel_wft2]]]]; auto.
     apply typing_lin_renamings; auto.
       eapply preservation_normalization; eauto.
     apply typing_lin_renamings; auto.
       eapply preservation_normalization; eauto.
     apply wf_lenv_merge; auto.
       apply wf_lenv_renamings; auto.

       assert (disjdom (atom_subst_codom asubst) (dom lEnv2)) as Disj3.
         apply disjdom_app_r in Disj2. destruct Disj2.
         apply disjdom_sym_1; auto.
       assert (J:=@subst_atoms_lenv__dom_upper asubst lEnv2 Wfa Uniq2 Disj3).
       apply disjdom__disjoint.
       apply disjdom_sym_1.
       apply disjdom_sub with (D1:=union (dom lEnv2) (atom_subst_codom asubst)); auto.
       eapply disjdom_app_r.
         split.
           apply disjoint__disjdom.
           apply disjoint_lenv_split' in Split.
           apply disjoint_sym_1; auto.
            
           apply disjdom_sym_1 in Disj.
           apply disjdom_sub with (D2:=(dom lEnv1)) in Disj; auto.
             clear. fsetdec.

     assert (J:=@subst_atoms_lenv__dom_eq asubst lEnv2 Wfa Uniq2 lEnv2_eq_asubst).
     apply disjdom_sym_1 in Disj.
     apply disjdom_sub with (D2:=L) in Disj; auto.
       apply disjdom_sym_1.
       apply disjdom_eq with (D1:=atom_subst_codom asubst); auto.
          rewrite J. clear. fsetdec.       
       clear. fsetdec.
     apply Forel_lin_renamings with (E:=E'); auto.
       eapply preservation_normalization; eauto.
       eapply preservation_normalization; eauto.

   assert (F_Related_ovalues T2' rsubst dsubst dsubst' (rev_subst_atoms_exp asubst u) (rev_subst_atoms_exp asubst u') Env (lEnv2++lEnv1)) as Hrel_wft2'.
     assert (lEnv2++lEnv1 = rev_subst_atoms_lenv asubst ((subst_atoms_lenv asubst lEnv2)++ lEnv1)) as Eq1.
       rewrite rev_subst_atoms_lenv_app.
       rewrite <- id_rev_subst_atoms_lenv; auto.
         rewrite <- rev_subst_atoms_lenv_notin_inv; auto.
           apply disjdom_sym_1 in Disj.
           apply disjdom_sub with (D2:=dom lEnv1) in Disj; auto.
             clear. fsetdec.
         rewrite lEnv2_eq_asubst. clear. fsetdec.

         apply disjdom_sym_1 in Disj.
         apply disjdom_sub with (D2:=dom lEnv2) in Disj; auto.
           clear. fsetdec.
     rewrite Eq1.
     apply Forel_lin_rev_renamings with (E:=E'); auto.
       apply preservation_normalization with (e:=exp_app v (subst_atoms_exp asubst v0)); auto.
         apply typing_app with (T1:=apply_delta_subst_typ dsubst T1') (K:=K) (D1:=lEnv1) (D2:=subst_atoms_lenv asubst lEnv2).
           simpl_commut_subst in Ht.
           apply preservation_normalization with (v:=v) in Ht; auto.

           apply preservation_normalization with (v:=v0) in Ht1; auto.
           apply typing_lin_renamings; auto.

           apply lenv_split_commute.
           apply disjoint__lenv_split; auto.
             apply wf_lenv_renamings; auto.

             assert (J:=@subst_atoms_lenv__dom_eq asubst lEnv2 Wfa Uniq2 lEnv2_eq_asubst).
             apply disjdom_sym_1 in Disj.
             apply disjdom_sub with (D2:=dom lEnv1) in Disj; auto.
               apply disjdom__disjoint.
               apply disjdom_eq with (D1:=atom_subst_codom asubst); auto.
                 rewrite J. clear. fsetdec.             
               clear. fsetdec.

       apply preservation_normalization with (e:=exp_app v' (subst_atoms_exp asubst v'0)); auto.
         apply typing_app with (T1:=apply_delta_subst_typ dsubst' T1') (K:=K) (D1:=lEnv1) (D2:=subst_atoms_lenv asubst lEnv2).
           simpl_commut_subst in Ht'.
           apply preservation_normalization with (v:=v') in Ht'; auto.

           apply preservation_normalization with (v:=v'0) in Ht1'; auto.
           apply typing_lin_renamings; auto.

           apply lenv_split_commute.
           apply disjoint__lenv_split; auto.
             apply wf_lenv_renamings; auto.

             assert (J:=@subst_atoms_lenv__dom_eq asubst lEnv2 Wfa Uniq2 lEnv2_eq_asubst).
             apply disjdom_sym_1 in Disj.
             apply disjdom_sub with (D2:=dom lEnv1) in Disj; auto.
               apply disjdom__disjoint.
               apply disjdom_eq with (D1:=atom_subst_codom asubst); auto.
                 rewrite J. clear. fsetdec.             
               clear. fsetdec.

       apply disjdom_sym_1 in Disj.
       apply disjdom_sub with (D2:=dom Env) in Disj; auto.
         clear. fsetdec.

       apply disjdom_eq with (D1:=dom lEnv2); auto.
       eapply disjdom_app_r.
       split.
         apply disjoint__disjdom.
         apply disjoint_split_right in Split; auto.
       
         apply disjoint__disjdom.
         eapply disjoint_app_l.
         split.
           assert (J:=@subst_atoms_lenv__dom_eq asubst lEnv2 Wfa Uniq2 lEnv2_eq_asubst).
           apply disjdom__disjoint.
           apply disjdom_eq with (D1:=atom_subst_codom asubst); auto.
             apply disjdom_sym_1 in Disj.
             apply disjdom_sub with (D2:=dom lEnv2) in Disj; auto.
               clear. fsetdec.             
             rewrite J. clear. fsetdec.

           apply disjoint_lenv_split' in Split; auto.
   assert (normalize (exp_app v v0) (rev_subst_atoms_exp asubst u)) as Hnorm'_vxu.
     apply normalize_rev_renamings with (asubst:=asubst) in Hnorm_vxu; auto.
     rewrite rev_subst_atoms_exp__app in Hnorm_vxu.
     rewrite <- id_rev_subst_atoms_exp with (asubst:=asubst) in Hnorm_vxu; auto.
       rewrite <- rev_wf_asubst_id with (asubst:=asubst) (e:=v) in Hnorm_vxu; auto.
       apply disjdom_sub with (D1:=dom Env `union` dom lEnv1).
         eapply disjdom_app_r.
         split.
           apply disjdom_sym_1.
           apply disjdom_sym_1 in Disj.
           apply disjdom_sub with (D2:=dom Env) in Disj; auto.
             clear. fsetdec.             
           apply disjdom_sym_1.
           apply disjdom_sym_1 in Disj.
           apply disjdom_sub with (D2:=dom lEnv1) in Disj; auto.
             clear. fsetdec.             
         apply preservation_normalization with (v:=v) in Ht; auto.
         apply typing_fv_ee_upper in Ht; auto.
      apply preservation_normalization with (v:=v0) in Ht1; auto.      
      apply typing_fv_ee_lower in Ht1; auto.
      rewrite <- lEnv2_eq_asubst. assumption.

      apply preservation_normalization with (v:=v0) in Ht1; auto.
      apply typing_fv_ee_upper in Ht1; auto.
      apply disjdom_sub with (D1:=union (dom Env) (dom lEnv2)); auto.  

   assert (normalize (exp_app v' v'0) (rev_subst_atoms_exp asubst u')) as Hnorm'_v'x'u'.
     apply normalize_rev_renamings with (asubst:=asubst) in Hnorm_v'x'u'; auto.
     rewrite rev_subst_atoms_exp__app in Hnorm_v'x'u'.
     rewrite <- id_rev_subst_atoms_exp with (asubst:=asubst) in Hnorm_v'x'u'; auto.
       rewrite <- rev_wf_asubst_id with (asubst:=asubst) (e:=v') in Hnorm_v'x'u'; auto.
       apply disjdom_sub with (D1:=dom Env `union` dom lEnv1).
         eapply disjdom_app_r.
         split.
           apply disjdom_sym_1.
           apply disjdom_sym_1 in Disj.
           apply disjdom_sub with (D2:=dom Env) in Disj; auto.
             clear.  fsetdec.             
           apply disjdom_sym_1.
           apply disjdom_sym_1 in Disj.
           apply disjdom_sub with (D2:=dom lEnv1) in Disj; auto.
             clear.  fsetdec.             
         apply preservation_normalization with (v:=v') in Ht'; auto.
         apply typing_fv_ee_upper in Ht'; auto.
      apply preservation_normalization with (v:=v'0) in Ht1'; auto.
      apply typing_fv_ee_lower in Ht1'; auto.
      rewrite <- lEnv2_eq_asubst. assumption.

      apply preservation_normalization with (v:=v'0) in Ht1'; auto.
      apply typing_fv_ee_upper in Ht1'; auto.
      apply disjdom_sub with (D1:=union (dom Env) (dom lEnv2)); auto.  

   exists(rev_subst_atoms_exp asubst u). exists(rev_subst_atoms_exp asubst u').
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
     rewrite lgamma_subst_split_osubst' with (lgsubst1:=lgsubst1) (lgsubst2:=lgsubst2) (E:=E') (lE:=D3') (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst) (Env:=Env) (lEnv1:=lEnv1) (lEnv2:=lEnv2) (lEnv:=lEnv); auto.
     rewrite lgamma_subst_split_osubst with (lgsubst1:=lgsubst1) (lgsubst2:=lgsubst2) (E:=E') (lE:=D3') (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst) (Env:=Env) (lEnv1:=lEnv1) (lEnv2:=lEnv2) (lEnv:=lEnv); auto.
     apply F_Related_osubst__inversion in J3.
     decompose [prod] J3; auto.
     apply F_Related_osubst__inversion in J4.
     decompose [prod] J4; auto.
     rewrite lgamma_osubst_split_shuffle2 with (lgsubst:=lgsubst) (lgsubst1:=lgsubst1) (E:=E') (lE:=D3') (Env:=Env) (lEnv1:=lEnv1) (lEnv2:=lEnv2) (lEnv:=lEnv) ; auto.
     erewrite gamma_osubst_closed_exp; eauto.
       rewrite lgamma_osubst_split_shuffle1 with (lgsubst:=lgsubst) (lgsubst2:=lgsubst2) (E:=E') (lE:=D3') (e:=apply_gamma_subst lgsubst2 e2) (Env:=Env) (lEnv1:=lEnv1) (lEnv2:=lEnv2) (lEnv:=lEnv) ; auto.
       erewrite gamma_osubst_closed_exp with 
         (e:=apply_delta_subst dsubst
            (apply_gamma_subst gsubst
              (apply_gamma_subst lgsubst2 e2))
          ); eauto.
         unfold disjdom.
         split; intros x xnotin.
           apply in_fv_ee_typing with (x:=x) in Ht1; try solve [assumption].
           assert (x `in` dom Env \/ x `in` dom lEnv2) as J. 
             clear - Ht1. fsetdec.
           destruct J as [J | J].
             apply disjoint_lgamma_osubst in b5.
             decompose [and] b5. clear b5.
             clear - J H6.
             apply disjoint_innotin2 with (x:=x) in H6; auto.

             assert (x `in` dom lEnv)as J'.
               apply dom_lenv_split in Split.
               rewrite Split. auto.
             assert (dom D1' [=] dom lgsubst1) as DomEq.
               apply dom_lgamma_osubst in b5.
               decompose [and] b5; auto.
             rewrite <- DomEq.
             assert (x `notin` dom D3')as J''.            
               apply lgamma_osubst_split__wf_lgamma_osubst in J1.
               apply disjoint_lgamma_osubst in J1.
               decompose [and] J1. clear J1.       
             clear - J' H8.
             apply disjoint_innotin2 with (x:=x) in H8; auto.
             apply dom_lenv_split in H0.
             rewrite H0 in J''. auto.

           apply notin_fv_ee_typing with (y:=x) in Ht1; try solve [assumption].
           assert (x `notin` dom Env) as J'.
             apply disjoint_lgamma_osubst in b5.
             decompose [and] b5. clear b5.
             clear - xnotin H6.
             apply disjoint_innotin1 with (x:=x) in H6; auto.

           assert ( x `notin` dom lEnv2) as J''.
             assert (dom D1' [=] dom lgsubst1) as DomEq.
               apply dom_lgamma_osubst in b5.
               decompose [and] b5; auto.
             rewrite <- DomEq in xnotin.
             assert (x `in` dom D3')as J'''.            
               apply dom_lenv_split in H0.
               rewrite H0. auto.
             assert (x `notin` dom lEnv)as JJ'.
               apply lgamma_osubst_split__wf_lgamma_osubst in J1.
               apply disjoint_lgamma_osubst in J1.
               decompose [and] J1. clear J1.
             clear - J''' H8.
             apply disjoint_innotin1 with (x:=x) in H8; auto.
             apply dom_lenv_split in Split.
             rewrite Split in JJ'. auto.
           clear - J' J''. auto.

       unfold disjdom.
       split; intros x xnotin.
         apply in_fv_ee_typing with (x:=x) in Ht; try solve [assumption].
         assert (x `in` dom Env \/ x `in` dom lEnv1) as J. clear - Ht. fsetdec.
         destruct J as [J | J].
           apply disjoint_lgamma_osubst in b13.
           decompose [and] b13. clear b13.
           clear - J H6.
           apply disjoint_innotin2 with (x:=x) in H6; auto.

           assert (x `in` dom lEnv)as J'.
             apply dom_lenv_split in Split.
             rewrite Split. auto.
           assert (dom D2' [=] dom lgsubst2) as DomEq.
             apply dom_lgamma_osubst in b13.
             decompose [and] b13; auto.
           rewrite <- DomEq.
           assert (x `notin` dom D3')as J''.            
             apply lgamma_osubst_split__wf_lgamma_osubst in J1.
             apply disjoint_lgamma_osubst in J1.
             decompose [and] J1. clear J1.             
             clear - J' H8.
             apply disjoint_innotin2 with (x:=x) in H8; auto.
           apply dom_lenv_split in H0.
           rewrite H0 in J''. auto.
         apply notin_fv_ee_typing with (y:=x) in Ht; try solve [assumption].
         assert (x `notin` dom Env) as J'.
           apply disjoint_lgamma_osubst in b13.
           decompose [and] b13. clear b13.
           clear - xnotin H6.
           apply disjoint_innotin1 with (x:=x) in H6; auto.

         assert ( x `notin` dom lEnv1) as J''.
           assert (dom D2' [=] dom lgsubst2) as DomEq.
             apply dom_lgamma_osubst in b13.
             decompose [and] b13; auto.
           rewrite <- DomEq in xnotin.
           assert (x `in` dom D3')as J'''.            
             apply dom_lenv_split in H0.
             rewrite H0. auto.
           assert (x `notin` dom lEnv)as JJ'.
             apply lgamma_osubst_split__wf_lgamma_osubst in J1.
             apply disjoint_lgamma_osubst in J1.
             decompose [and] J1. clear J1.             
           clear - J''' H8.
           apply disjoint_innotin1 with (x:=x) in H8; auto.
           apply dom_lenv_split in Split.
           rewrite Split in JJ'. auto.
         clear - J' J''. auto.   
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
     rewrite lgamma_subst_split_osubst' with (lgsubst1:=lgsubst1') (lgsubst2:=lgsubst2') (E:=E') (lE:=D3') (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst') (Env:=Env) (lEnv1:=lEnv1) (lEnv2:=lEnv2) (lEnv:=lEnv); auto.
     rewrite lgamma_subst_split_osubst with (lgsubst1:=lgsubst1') (lgsubst2:=lgsubst2') (E:=E') (lE:=D3') (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst') (Env:=Env) (lEnv1:=lEnv1) (lEnv2:=lEnv2) (lEnv:=lEnv); auto.
     apply F_Related_osubst__inversion in J3.
     decompose [prod] J3; auto.
     apply F_Related_osubst__inversion in J4.
     decompose [prod] J4; auto.
     rewrite lgamma_osubst_split_shuffle2 with (lgsubst:=lgsubst') (lgsubst1:=lgsubst1') (E:=E') (lE:=D3')  (Env:=Env) (lEnv1:=lEnv1) (lEnv2:=lEnv2) (lEnv:=lEnv); auto.
     erewrite gamma_osubst_closed_exp; eauto.
       rewrite lgamma_osubst_split_shuffle1 with (lgsubst:=lgsubst') (lgsubst2:=lgsubst2') (E:=E') (lE:=D3') (e:=apply_gamma_subst lgsubst2' e2)  (Env:=Env) (lEnv1:=lEnv1) (lEnv2:=lEnv2) (lEnv:=lEnv); auto.
       erewrite gamma_osubst_closed_exp with 
         (e:=apply_delta_subst dsubst'
            (apply_gamma_subst gsubst'
              (apply_gamma_subst lgsubst2' e2))
          ); eauto.
         unfold disjdom.
         split; intros x xnotin.
           apply in_fv_ee_typing with (x:=x) in Ht1'; try solve [assumption].
           assert (x `in` dom Env \/ x `in` dom lEnv2) as J. clear - Ht1'. fsetdec.
           destruct J as [J | J].
             apply disjoint_lgamma_osubst in b4.
             decompose [and] b4. clear b4.
             clear - J H6.
             apply disjoint_innotin2 with (x:=x) in H6; auto.

             assert (x `in` dom lEnv)as J'.
               apply dom_lenv_split in Split.
               rewrite Split. auto.
             assert (dom D1' [=] dom lgsubst1') as DomEq.
               apply dom_lgamma_osubst in b4.
               decompose [and] b4; auto.
             rewrite <- DomEq.
             assert (x `notin` dom D3')as J''.            
               apply lgamma_osubst_split__wf_lgamma_osubst in J2.
               apply disjoint_lgamma_osubst in J2.
               decompose [and] J2. clear J2.             
             clear - J' H8.
             apply disjoint_innotin2 with (x:=x) in H8; auto.
             apply dom_lenv_split in H0.
             rewrite H0 in J''. auto.

           apply notin_fv_ee_typing with (y:=x) in Ht1'; try solve [assumption].
           assert (x `notin` dom Env) as J'.
             apply disjoint_lgamma_osubst in b4.
             decompose [and] b4. clear b4.
             clear - xnotin H6.
             apply disjoint_innotin1 with (x:=x) in H6; auto.

           assert ( x `notin` dom lEnv2) as J''.
             assert (dom D1' [=] dom lgsubst1') as DomEq.
               apply dom_lgamma_osubst in b4.
               decompose [and] b4; auto.
             rewrite <- DomEq in xnotin.
             assert (x `in` dom D3')as J'''.            
               apply dom_lenv_split in H0.
               rewrite H0. auto.
             assert (x `notin` dom lEnv)as JJ'.
               apply lgamma_osubst_split__wf_lgamma_osubst in J2.
               apply disjoint_lgamma_osubst in J2.
               decompose [and] J2. clear J2.             
               clear - J''' H8.
               apply disjoint_innotin1 with (x:=x) in H8; auto.
             apply dom_lenv_split in Split.
             rewrite Split in JJ'. auto.
           clear - J' J''. auto.

       unfold disjdom.
       split; intros x xnotin.
         apply in_fv_ee_typing with (x:=x) in Ht'; try solve [assumption].
         assert (x `in` dom Env \/ x `in` dom lEnv1) as J. clear - Ht'. fsetdec.
         destruct J as [J | J].
           apply disjoint_lgamma_osubst in b12.
           decompose [and] b12. clear b12.
           clear - J H6.
           apply disjoint_innotin2 with (x:=x) in H6; auto.

           assert (x `in` dom lEnv)as J'.
             apply dom_lenv_split in Split.
             rewrite Split. auto.
           assert (dom D2' [=] dom lgsubst2') as DomEq.
             apply dom_lgamma_osubst in b12.
             decompose [and] b12; auto.
           rewrite <- DomEq.
           assert (x `notin` dom D3')as J''.            
             apply lgamma_osubst_split__wf_lgamma_osubst in J2.
             apply disjoint_lgamma_osubst in J2.
             decompose [and] J2. clear J2.           
             clear - H8 J'.
             apply disjoint_innotin2 with (x:=x) in H8; auto.
           apply dom_lenv_split in H0.
           rewrite H0 in J''. auto.
         apply notin_fv_ee_typing with (y:=x) in Ht'; try solve [assumption].
         assert (x `notin` dom Env) as J'.
           apply disjoint_lgamma_osubst in b12.
           decompose [and] b12. clear b12.
           clear - xnotin H6.
           apply disjoint_innotin1 with (x:=x) in H6; auto.
         assert ( x `notin` dom lEnv1) as J''.
           assert (dom D2' [=] dom lgsubst2') as DomEq.
             apply dom_lgamma_osubst in b12.
             decompose [and] b12; auto.
           rewrite <- DomEq in xnotin.
           assert (x `in` dom D3')as J'''.            
             apply dom_lenv_split in H0.
             rewrite H0. auto.
           assert (x `notin` dom lEnv)as JJ'.
             apply lgamma_osubst_split__wf_lgamma_osubst in J2.
             apply disjoint_lgamma_osubst in J2.
             decompose [and] J2. clear J2.             
             clear - J''' H8.
             apply disjoint_innotin1 with (x:=x) in H8; auto.
           apply dom_lenv_split in Split.
           rewrite Split in JJ'. auto.
         clear - J' J''. auto.   
   repeat(rewrite EQ). clear EQ.
   repeat(split; try solve [simpl_commut_subst in *; eauto |
                                              simpl_commut_subst; apply congr_app with (v1:=v) (v2:=v0); auto |
                                              simpl_commut_subst; apply congr_app with (v1:=v') (v2:=v'0); auto]).
    apply Forel_lin_domeq with (lEnv:=lEnv2++lEnv1); auto.
      apply wf_lenv_merge; auto.
        apply disjoint_lenv_split' in Split; auto.
      apply dom_lenv_split in Split.
        rewrite Split. simpl_env. clear. fsetdec.
Qed.

Lemma F_ological_related_congruence__app2 :
  forall e e' E D T,
  typing E D e T ->
  typing E D e' T ->
  forall L0,
  (forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
   disjdom L0 (fv_env Env) ->
   disjdom L0 (fv_lenv lEnv) ->
   F_Related_osubst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
   F_Rosubst E rsubst dsubst dsubst' Env ->
   F_Related_oterms T rsubst dsubst dsubst' 
     (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
     (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e')))
     Env lEnv
  ) ->
  forall T1' K  E' D1' D2' D3' e1 C2 T2',
  typing E' D1' e1 (typ_arrow K T1' T2') ->
  contexting E D T C2 E' D2' T1' ->
  disjdom (fv_ee e1) (dom D) ->
  lenv_split E' D1' D2' D3' ->
  (typing E D e T ->
   typing E D e' T ->
    (forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
     disjdom L0 (fv_env Env) ->
     disjdom L0 (fv_lenv lEnv) ->
     F_Related_osubst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
     F_Rosubst E rsubst dsubst dsubst' Env ->
     F_Related_oterms T rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e')))
      Env lEnv
    ) ->
   forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
     disjdom (L0 `union` cv_ec C2 `union` fv_ec C2 `union` dom E `union` dom D `union` fv_tt T `union` fv_tt T1' `union` dom E' `union` dom D2') (fv_env Env) ->
     disjdom (L0 `union` cv_ec C2 `union` fv_ec C2 `union` dom E `union` dom D `union` fv_tt T `union` fv_tt T1'  `union` dom E' `union` dom D2') (fv_lenv lEnv) ->
     F_Related_osubst E' D2' gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
     F_Rosubst E' rsubst dsubst dsubst' Env ->
     F_Related_oterms T1' rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (plug C2 e))))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (plug C2 e'))))
      Env lEnv
  ) ->
  forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
  disjdom (L0 `union` cv_ec C2 `union` (fv_ee e1 `union` fv_ec C2) `union` dom E `union` dom D `union` fv_tt T `union` fv_tt T2' `union` dom E' `union` dom D3') (fv_env Env) ->
  disjdom (L0 `union` cv_ec C2 `union` (fv_ee e1 `union` fv_ec C2) `union` dom E `union` dom D `union` fv_tt T `union` fv_tt T2' `union` dom E' `union` dom D3') (fv_lenv lEnv) ->
  F_Related_osubst E' D3' gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
  F_Rosubst E' rsubst dsubst dsubst' Env  ->
  F_Related_oterms T2' rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_app e1 (plug C2 e)))))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_app e1 (plug C2 e')))))
      Env lEnv.
Proof.
   intros e e' E D T Htyp Htyp' L0 Hlr T1' K E' D1' D2' D3' e1 C2 T2' H Hcontexting H0 H1 IHHcontexting dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv Disj00 Disj01 Hrel_sub HRsub.  
   assert (J:=Hrel_sub). apply F_Related_osubst__inversion in J. 
   destruct J as [[[[[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe] Hwfe'] HwfEnv] HwflEnv].
   apply F_Related_osubst_split with (lE1:=D1') (lE2:=D2') in Hrel_sub; auto.
   destruct Hrel_sub as [lgsubst1 [lgsubst1' [lgsubst2 [lgsubst2' [lEnv1 [lEnv2 [J1 [J2 [J3 J4]]]]]]]]].

   assert (
      F_Related_oterms (typ_arrow K T1' T2') rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst1 e1)))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst1' e1)))
         Env lEnv1
     ) as FR_ArrowType.
    apply oparametricity with (E:=E') (lE:=D1'); auto.
   destruct FR_ArrowType as [v [v' [Ht [Ht' [Hn [Hn' Hrel]]]]]].

   apply F_Related_ovalues_arrow_leq in Hrel.
   destruct Hrel as [Hv [Hv' [L Harrow]]]; subst.

   assert (
      F_Related_oterms T1' rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst2 (plug C2 e))))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst'(apply_gamma_subst lgsubst2' (plug C2 e'))))
         Env lEnv2
     ) as FR_T1.
    apply IHHcontexting; auto.
      clear - Disj00 H1 H.
      apply dom_lenv_split in H1.
      apply typing_regular in H.
      destruct H as [_ [_ [_ H]]].
      apply wft_fv_tt_sub in H.
      apply disjdom_sym_1.
      apply disjdom_sub with (D1:=L0 `union` cv_ec C2 `union` (fv_ee e1 `union` fv_ec C2) `union` dom E `union` dom D `union` fv_tt T  `union` fv_tt T2' `union` dom E' `union` dom D3').
        apply disjdom_sym_1; auto.
        clear Disj00. rewrite H1. clear H1. simpl in H. fsetdec.        

      clear - Disj01 H1 J1 H.
      apply dom_lenv_split in H1.
      apply lgamma_osubst_split__lenv_split in J1.
      apply fv_lenv_split in J1.
      apply typing_regular in H.
      destruct H as [_ [_ [_ H]]].
      apply wft_fv_tt_sub in H.
      apply disjdom_sym_1.
      apply disjdom_sub with (D1:=L0 `union` cv_ec C2 `union` (fv_ee e1 `union` fv_ec C2) `union` dom E `union` dom D `union` fv_tt T `union` fv_tt T2' `union` dom E' `union` dom D3').
        apply disjdom_sym_1.
        apply disjdom_sub with (D1:=fv_lenv lEnv); auto.
          rewrite J1. clear. fsetdec.
        clear Disj01. rewrite H1. clear H1 J1. simpl in H. fsetdec.        
   destruct FR_T1 as [v0 [v'0 [Ht1 [Ht1' [Hn1 [Hn1' Hrel_wft1]]]]]].

   clear Disj00 Disj01.

   assert (lenv_split Env lEnv1 lEnv2 lEnv) as Split.
     apply lgamma_osubst_split__lenv_split in J1. auto.

   assert (uniq lEnv2) as Uniq2.
     apply typing_regular in Ht1. destruct Ht1 as [JJ1 [JJ2 [JJ3 JJ4]]].
     apply uniq_from_wf_lenv in JJ2; auto.
   assert (JJ:=@pick_lenv (L `union` dom lEnv2 `union` dom lEnv `union` dom lEnv1 `union` dom Env `union` dom E' `union` dom D1' `union` dom D2' `union` dom D3' `union` dom E `union` dom D) lEnv2 Uniq2).
   destruct JJ as [asubst [Wfa [lEnv2_eq_asubst Disj]]].
   assert (disjoint asubst Env) as Disj1.
     apply disjoint_split_right in Split.
     apply disjoint_eq with (D1:=lEnv2); auto.
   assert (disjdom (atom_subst_codom asubst) (union (dom Env) (dom lEnv2))) as Disj2.
     apply disjdom_sym_1 in Disj.
     apply disjdom_sub with (D2:=union (dom Env) (dom lEnv2)) in Disj; try solve [assumption].
     clear. fsetdec.
   destruct (@Harrow (subst_atoms_lenv asubst lEnv2) (subst_atoms_exp asubst v0) (subst_atoms_exp asubst v'0)) as [u [u' [Hnorm_vxu [Hnorm_v'x'u' Hrel_wft2]]]]; auto.
     apply typing_lin_renamings; auto.
       eapply preservation_normalization; eauto.
     apply typing_lin_renamings; auto.
       eapply preservation_normalization; eauto.
     apply wf_lenv_merge; auto.
       apply wf_lenv_renamings; auto.

       assert (disjdom (atom_subst_codom asubst) (dom lEnv2)) as Disj3.
         apply disjdom_app_r in Disj2. destruct Disj2.
         apply disjdom_sym_1; auto.
       assert (J:=@subst_atoms_lenv__dom_upper asubst lEnv2 Wfa Uniq2 Disj3).
       apply disjdom__disjoint.
       apply disjdom_sym_1.
       apply disjdom_sub with (D1:=union (dom lEnv2) (atom_subst_codom asubst)); auto.
       eapply disjdom_app_r.
         split.
           apply disjoint__disjdom.
           apply disjoint_lenv_split' in Split.
           apply disjoint_sym_1; auto.
            
           apply disjdom_sym_1 in Disj.
           apply disjdom_sub with (D2:=(dom lEnv1)) in Disj; auto.
             clear. fsetdec.

     assert (J:=@subst_atoms_lenv__dom_eq asubst lEnv2 Wfa Uniq2 lEnv2_eq_asubst).
     apply disjdom_sym_1 in Disj.
     apply disjdom_sub with (D2:=L) in Disj; auto.
       apply disjdom_sym_1.
       apply disjdom_eq with (D1:=atom_subst_codom asubst); auto.
          rewrite J. clear. fsetdec.       
       clear. fsetdec.
     apply Forel_lin_renamings with (E:=E'); auto.
       eapply preservation_normalization; eauto.
       eapply preservation_normalization; eauto.

   assert (F_Related_ovalues T2' rsubst dsubst dsubst' (rev_subst_atoms_exp asubst u) (rev_subst_atoms_exp asubst u') Env (lEnv2++lEnv1)) as Hrel_wft2'.
     assert (lEnv2++lEnv1 = rev_subst_atoms_lenv asubst ((subst_atoms_lenv asubst lEnv2)++ lEnv1)) as Eq1.
       rewrite rev_subst_atoms_lenv_app.
       rewrite <- id_rev_subst_atoms_lenv; auto.
         rewrite <- rev_subst_atoms_lenv_notin_inv; auto.
           apply disjdom_sym_1 in Disj.
           apply disjdom_sub with (D2:=dom lEnv1) in Disj; auto.
             clear. fsetdec.
         rewrite lEnv2_eq_asubst. clear. fsetdec.

         apply disjdom_sym_1 in Disj.
         apply disjdom_sub with (D2:=dom lEnv2) in Disj; auto.
           clear. fsetdec.
     rewrite Eq1.
     apply Forel_lin_rev_renamings with (E:=E'); auto.
       apply preservation_normalization with (e:=exp_app v (subst_atoms_exp asubst v0)); auto.
         apply typing_app with (T1:=apply_delta_subst_typ dsubst T1') (K:=K) (D1:=lEnv1) (D2:=subst_atoms_lenv asubst lEnv2).
           simpl_commut_subst in Ht.
           apply preservation_normalization with (v:=v) in Ht; auto.

           apply preservation_normalization with (v:=v0) in Ht1; auto.
           apply typing_lin_renamings; auto.

           apply lenv_split_commute.
           apply disjoint__lenv_split; auto.
             apply wf_lenv_renamings; auto.

             assert (J:=@subst_atoms_lenv__dom_eq asubst lEnv2 Wfa Uniq2 lEnv2_eq_asubst).
             apply disjdom_sym_1 in Disj.
             apply disjdom_sub with (D2:=dom lEnv1) in Disj; auto.
               apply disjdom__disjoint.
               apply disjdom_eq with (D1:=atom_subst_codom asubst); auto.
                 rewrite J. clear. fsetdec.             
               clear. fsetdec.

       apply preservation_normalization with (e:=exp_app v' (subst_atoms_exp asubst v'0)); auto.
         apply typing_app with (T1:=apply_delta_subst_typ dsubst' T1') (K:=K) (D1:=lEnv1) (D2:=subst_atoms_lenv asubst lEnv2).
           simpl_commut_subst in Ht'.
           apply preservation_normalization with (v:=v') in Ht'; auto.

           apply preservation_normalization with (v:=v'0) in Ht1'; auto.
           apply typing_lin_renamings; auto.

           apply lenv_split_commute.
           apply disjoint__lenv_split; auto.
             apply wf_lenv_renamings; auto.

             assert (J:=@subst_atoms_lenv__dom_eq asubst lEnv2 Wfa Uniq2 lEnv2_eq_asubst).
             apply disjdom_sym_1 in Disj.
             apply disjdom_sub with (D2:=dom lEnv1) in Disj; auto.
               apply disjdom__disjoint.
               apply disjdom_eq with (D1:=atom_subst_codom asubst); auto.
                 rewrite J. clear. fsetdec.             
               clear. fsetdec.

       apply disjdom_sym_1 in Disj.
       apply disjdom_sub with (D2:=dom Env) in Disj; auto.
         clear. fsetdec.

       apply disjdom_eq with (D1:=dom lEnv2); auto.
       eapply disjdom_app_r.
       split.
         apply disjoint__disjdom.
         apply disjoint_split_right in Split; auto.
       
         apply disjoint__disjdom.
         eapply disjoint_app_l.
         split.
           assert (J:=@subst_atoms_lenv__dom_eq asubst lEnv2 Wfa Uniq2 lEnv2_eq_asubst).
           apply disjdom__disjoint.
           apply disjdom_eq with (D1:=atom_subst_codom asubst); auto.
             apply disjdom_sym_1 in Disj.
             apply disjdom_sub with (D2:=dom lEnv2) in Disj; auto.
               clear. fsetdec.             
             rewrite J. clear. fsetdec.

           apply disjoint_lenv_split' in Split; auto.
   assert (normalize (exp_app v v0) (rev_subst_atoms_exp asubst u)) as Hnorm'_vxu.
     apply normalize_rev_renamings with (asubst:=asubst) in Hnorm_vxu; auto.
     rewrite rev_subst_atoms_exp__app in Hnorm_vxu.
     rewrite <- id_rev_subst_atoms_exp with (asubst:=asubst) in Hnorm_vxu; auto.
       rewrite <- rev_wf_asubst_id with (asubst:=asubst) (e:=v) in Hnorm_vxu; auto.
       apply disjdom_sub with (D1:=dom Env `union` dom lEnv1).
         eapply disjdom_app_r.
         split.
           apply disjdom_sym_1.
           apply disjdom_sym_1 in Disj.
           apply disjdom_sub with (D2:=dom Env) in Disj; auto.
             clear. fsetdec.             
           apply disjdom_sym_1.
           apply disjdom_sym_1 in Disj.
           apply disjdom_sub with (D2:=dom lEnv1) in Disj; auto.
             clear. fsetdec.             
         apply preservation_normalization with (v:=v) in Ht; auto.
         apply typing_fv_ee_upper in Ht; auto.
      apply preservation_normalization with (v:=v0) in Ht1; auto.      
      apply typing_fv_ee_lower in Ht1; auto.
      rewrite <- lEnv2_eq_asubst. assumption.

      apply preservation_normalization with (v:=v0) in Ht1; auto.
      apply typing_fv_ee_upper in Ht1; auto.
      apply disjdom_sub with (D1:=union (dom Env) (dom lEnv2)); auto.  

   assert (normalize (exp_app v' v'0) (rev_subst_atoms_exp asubst u')) as Hnorm'_v'x'u'.
     apply normalize_rev_renamings with (asubst:=asubst) in Hnorm_v'x'u'; auto.
     rewrite rev_subst_atoms_exp__app in Hnorm_v'x'u'.
     rewrite <- id_rev_subst_atoms_exp with (asubst:=asubst) in Hnorm_v'x'u'; auto.
       rewrite <- rev_wf_asubst_id with (asubst:=asubst) (e:=v') in Hnorm_v'x'u'; auto.
       apply disjdom_sub with (D1:=dom Env `union` dom lEnv1).
         eapply disjdom_app_r.
         split.
           apply disjdom_sym_1.
           apply disjdom_sym_1 in Disj.
           apply disjdom_sub with (D2:=dom Env) in Disj; auto.
             clear. fsetdec.             
           apply disjdom_sym_1.
           apply disjdom_sym_1 in Disj.
           apply disjdom_sub with (D2:=dom lEnv1) in Disj; auto.
             clear. fsetdec.             
         apply preservation_normalization with (v:=v') in Ht'; auto.
         apply typing_fv_ee_upper in Ht'; auto.
      apply preservation_normalization with (v:=v'0) in Ht1'; auto.
      apply typing_fv_ee_lower in Ht1'; auto.
      rewrite <- lEnv2_eq_asubst. assumption.

      apply preservation_normalization with (v:=v'0) in Ht1'; auto.
      apply typing_fv_ee_upper in Ht1'; auto.
      apply disjdom_sub with (D1:=union (dom Env) (dom lEnv2)); auto.  

   exists(rev_subst_atoms_exp asubst u). exists(rev_subst_atoms_exp asubst u').
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
     rewrite lgamma_subst_split_osubst' with (lgsubst1:=lgsubst1) (lgsubst2:=lgsubst2) (E:=E') (lE:=D3') (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst) (Env:=Env) (lEnv1:=lEnv1) (lEnv2:=lEnv2) (lEnv:=lEnv); auto.
     rewrite lgamma_subst_split_osubst with (lgsubst1:=lgsubst1) (lgsubst2:=lgsubst2) (E:=E') (lE:=D3') (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst) (Env:=Env) (lEnv1:=lEnv1) (lEnv2:=lEnv2) (lEnv:=lEnv); auto.
     apply F_Related_osubst__inversion in J3.
     decompose [prod] J3; auto.
     apply F_Related_osubst__inversion in J4.
     decompose [prod] J4; auto.
     rewrite lgamma_osubst_split_shuffle2 with (lgsubst:=lgsubst) (lgsubst1:=lgsubst1) (E:=E') (lE:=D3') (Env:=Env) (lEnv1:=lEnv1) (lEnv2:=lEnv2) (lEnv:=lEnv) ; auto.
     erewrite gamma_osubst_closed_exp; eauto.
     rewrite lgamma_osubst_split_shuffle1 with (lgsubst:=lgsubst) (lgsubst2:=lgsubst2) (E:=E') (lE:=D3') (e:=apply_gamma_subst lgsubst2 (plug C2 e)) (Env:=Env) (lEnv1:=lEnv1) (lEnv2:=lEnv2) (lEnv:=lEnv) ; auto.
     erewrite gamma_osubst_closed_exp with 
         (e:=apply_delta_subst dsubst
            (apply_gamma_subst gsubst
              (apply_gamma_subst lgsubst2 (plug C2 e)))
          ); eauto.
         unfold disjdom.
         split; intros x xnotin.
           apply in_fv_ee_typing with (x:=x) in Ht1; try solve [assumption].
           assert (x `in` dom Env \/ x `in` dom lEnv2) as J. clear - Ht1. fsetdec.
           destruct J as [J | J].
             apply disjoint_lgamma_osubst in b5.
             decompose [and] b5. clear b5.
             clear - J H6.
             apply disjoint_innotin2 with (x:=x) in H6; auto.

             assert (x `in` dom lEnv)as J'.
               apply dom_lenv_split in Split.
               rewrite Split. auto.
             assert (dom D1' [=] dom lgsubst1) as DomEq.
               apply dom_lgamma_osubst in b5.
               decompose [and] b5; auto.
             rewrite <- DomEq.
             assert (x `notin` dom D3')as J''.            
               apply lgamma_osubst_split__wf_lgamma_osubst in J1.
               apply disjoint_lgamma_osubst in J1.
               decompose [and] J1. clear J1.             
               clear - J' H8.
               apply disjoint_innotin2 with (x:=x) in H8; auto.
             apply dom_lenv_split in H1.
             rewrite H1 in J''. auto.

           assert (x `notin` dom Env) as J'.
             apply disjoint_lgamma_osubst in b5.
             decompose [and] b5. clear b5.
             clear - xnotin H6.
             apply disjoint_innotin1 with (x:=x) in H6; auto.

           assert ( x `notin` dom lEnv2) as J''.
             assert (dom D1' [=] dom lgsubst1) as DomEq.
               apply dom_lgamma_osubst in b5.
               decompose [and] b5; auto.
             rewrite <- DomEq in xnotin.
             assert (x `in` dom D3')as J'''.            
               apply dom_lenv_split in H1.
               rewrite H1. auto.
             assert (x `notin` dom lEnv)as JJ'.
               apply lgamma_osubst_split__wf_lgamma_osubst in J1.
               apply disjoint_lgamma_osubst in J1.
               decompose [and] J1. clear J1.             
               clear - J''' H8.
               apply disjoint_innotin1 with (x:=x) in H8; auto.
           apply dom_lenv_split in Split.
             rewrite Split in JJ'. auto.
           apply notin_fv_ee_typing with (y:=x) in Ht1; auto.

       unfold disjdom.
       split; intros x xnotin.
         apply in_fv_ee_typing with (x:=x) in Ht; try solve [assumption].
         assert (x `in` dom Env \/ x `in` dom lEnv1) as J. 
           clear - Ht.
           fsetdec.
         destruct J as [J | J].
           apply disjoint_lgamma_osubst in b13.
           decompose [and] b13. clear b13.
           clear - J H6.
           apply disjoint_innotin2 with (x:=x) in H6; auto.

           assert (x `in` dom lEnv)as J'.
             apply dom_lenv_split in Split.
             rewrite Split. auto.
           assert (dom D2' [=] dom lgsubst2) as DomEq.
             apply dom_lgamma_osubst in b13.
             decompose [and] b13; auto.
           rewrite <- DomEq.
           assert (x `notin` dom D3')as J''.            
             apply lgamma_osubst_split__wf_lgamma_osubst in J1.
             apply disjoint_lgamma_osubst in J1.
             decompose [and] J1. clear J1.             
             clear - J' H8.
             apply disjoint_innotin2 with (x:=x) in H8; auto.
           apply dom_lenv_split in H1.
           rewrite H1 in J''. auto.
         assert (x `notin` dom Env) as J'.
           apply disjoint_lgamma_osubst in b13.
           decompose [and] b13. clear b13.
           clear - xnotin H6.
           apply disjoint_innotin1 with (x:=x) in H6; auto.
         assert ( x `notin` dom lEnv1) as J''.
           assert (dom D2' [=] dom lgsubst2) as DomEq.
             apply dom_lgamma_osubst in b13.
             decompose [and] b13; auto.
           rewrite <- DomEq in xnotin.
           assert (x `in` dom D3')as J'''.            
             apply dom_lenv_split in H1.
             rewrite H1. auto.
           assert (x `notin` dom lEnv)as JJ'.
             apply lgamma_osubst_split__wf_lgamma_osubst in J1.
             apply disjoint_lgamma_osubst in J1.
             decompose [and] J1. clear J1.             
             clear - J''' H8.
             apply disjoint_innotin1 with (x:=x) in H8; auto.
           apply dom_lenv_split in Split.
           rewrite Split in JJ'. auto.
         apply notin_fv_ee_typing with (y:=x) in Ht; auto.
   repeat(rewrite EQ). clear EQ.
   assert (apply_delta_subst dsubst'
            (apply_gamma_subst gsubst'
              (apply_gamma_subst lgsubst' (exp_app e1 (plug C2 e'))) 
            ) =
            apply_delta_subst dsubst'
            (apply_gamma_subst gsubst'
              (exp_app 
                (apply_gamma_subst lgsubst1' e1)
                (apply_gamma_subst lgsubst2' (plug C2 e'))
              )               
            )
          ) as EQ.
     simpl_commut_subst in *.
     rewrite lgamma_subst_split_osubst' with (lgsubst1:=lgsubst1') (lgsubst2:=lgsubst2') (E:=E') (lE:=D3') (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst') (Env:=Env) (lEnv1:=lEnv1) (lEnv2:=lEnv2) (lEnv:=lEnv); auto.
     rewrite lgamma_subst_split_osubst with (lgsubst1:=lgsubst1') (lgsubst2:=lgsubst2') (E:=E') (lE:=D3') (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst') (Env:=Env) (lEnv1:=lEnv1) (lEnv2:=lEnv2) (lEnv:=lEnv); auto.
     apply F_Related_osubst__inversion in J3.
     decompose [prod] J3; auto.
     apply F_Related_osubst__inversion in J4.
     decompose [prod] J4; auto.
     rewrite lgamma_osubst_split_shuffle2 with (lgsubst:=lgsubst') (lgsubst1:=lgsubst1') (E:=E') (lE:=D3')  (Env:=Env) (lEnv1:=lEnv1) (lEnv2:=lEnv2) (lEnv:=lEnv); auto.
     erewrite gamma_osubst_closed_exp; eauto.
     rewrite lgamma_osubst_split_shuffle1 with (lgsubst:=lgsubst') (lgsubst2:=lgsubst2') (E:=E') (lE:=D3') (e:=apply_gamma_subst lgsubst2' (plug C2 e'))  (Env:=Env) (lEnv1:=lEnv1) (lEnv2:=lEnv2) (lEnv:=lEnv); auto.
     erewrite gamma_osubst_closed_exp with 
         (e:=apply_delta_subst dsubst'
            (apply_gamma_subst gsubst'
              (apply_gamma_subst lgsubst2' (plug C2 e')))
          ); eauto.
         unfold disjdom.
         split; intros x xnotin.
           apply in_fv_ee_typing with (x:=x) in Ht1'; try solve [assumption].
           assert (x `in` dom Env \/ x `in` dom lEnv2) as J. 
             clear - Ht1'.
             fsetdec.
           destruct J as [J | J].
             apply disjoint_lgamma_osubst in b4.
             decompose [and] b4. clear b4.
             clear - J H6.
             apply disjoint_innotin2 with (x:=x) in H6; auto.

             assert (x `in` dom lEnv)as J'.
               apply dom_lenv_split in Split.
               rewrite Split. auto.
             assert (dom D1' [=] dom lgsubst1') as DomEq.
               apply dom_lgamma_osubst in b4.
               decompose [and] b4; auto.
             rewrite <- DomEq.
             assert (x `notin` dom D3')as J''.            
               apply lgamma_osubst_split__wf_lgamma_osubst in J2.
               apply disjoint_lgamma_osubst in J2.
               decompose [and] J2. clear J2.             
               clear - J' H8.
               apply disjoint_innotin2 with (x:=x) in H8; auto.
           apply dom_lenv_split in H1.
             rewrite H1 in J''. auto.

           assert (x `notin` dom Env) as J'.
             apply disjoint_lgamma_osubst in b4.
             decompose [and] b4. clear b4.
             clear - xnotin H6.
             apply disjoint_innotin1 with (x:=x) in H6; auto.

           assert ( x `notin` dom lEnv2) as J''.
             assert (dom D1' [=] dom lgsubst1') as DomEq.
               apply dom_lgamma_osubst in b4.
               decompose [and] b4; auto.
             rewrite <- DomEq in xnotin.
             assert (x `in` dom D3')as J'''.            
               apply dom_lenv_split in H1.
               rewrite H1. auto.
             assert (x `notin` dom lEnv)as JJ'.
               apply lgamma_osubst_split__wf_lgamma_osubst in J2.
               apply disjoint_lgamma_osubst in J2.
               decompose [and] J2. clear J2.             
               clear - J''' H8.
               apply disjoint_innotin1 with (x:=x) in H8; auto.
           apply dom_lenv_split in Split.
             rewrite Split in JJ'. auto.
           apply notin_fv_ee_typing with (y:=x) in Ht1'; auto.

       unfold disjdom.
       split; intros x xnotin.
         apply in_fv_ee_typing with (x:=x) in Ht'; try solve [assumption].
         assert (x `in` dom Env \/ x `in` dom lEnv1) as J. 
           clear - Ht'.
           fsetdec.
         destruct J as [J | J].
           apply disjoint_lgamma_osubst in b12.
           decompose [and] b12. clear b12.
           clear - J H6.
           apply disjoint_innotin2 with (x:=x) in H6; auto.

           assert (x `in` dom lEnv)as J'.
             apply dom_lenv_split in Split.
             rewrite Split. auto.
           assert (dom D2' [=] dom lgsubst2') as DomEq.
             apply dom_lgamma_osubst in b12.
             decompose [and] b12; auto.
           rewrite <- DomEq.
           assert (x `notin` dom D3')as J''.            
             apply lgamma_osubst_split__wf_lgamma_osubst in J2.
             apply disjoint_lgamma_osubst in J2.
             decompose [and] J2. clear J2.             
             clear - J' H8.
             apply disjoint_innotin2 with (x:=x) in H8; auto.
           apply dom_lenv_split in H1.
           rewrite H1 in J''. auto.
         assert (x `notin` dom Env) as J'.
           apply disjoint_lgamma_osubst in b12.
           decompose [and] b12. clear b12.
           clear - xnotin H6.
           apply disjoint_innotin1 with (x:=x) in H6; auto.
        assert ( x `notin` dom lEnv1) as J''.
           assert (dom D2' [=] dom lgsubst2') as DomEq.
             apply dom_lgamma_osubst in b12.
             decompose [and] b12; auto.
           rewrite <- DomEq in xnotin.
           assert (x `in` dom D3')as J'''.            
             apply dom_lenv_split in H1.
             rewrite H1. auto.
           assert (x `notin` dom lEnv)as JJ'.
             apply lgamma_osubst_split__wf_lgamma_osubst in J2.
             apply disjoint_lgamma_osubst in J2.
             decompose [and] J2. clear J2.             
             clear - J''' H8.
             apply disjoint_innotin1 with (x:=x) in H8; auto.
           apply dom_lenv_split in Split.
           rewrite Split in JJ'. auto.
         apply notin_fv_ee_typing with (y:=x) in Ht'; auto.
   repeat(rewrite EQ). clear EQ.
   repeat(split; try solve [simpl_commut_subst in *; eauto |
                                              simpl_commut_subst; apply congr_app with (v1:=v) (v2:=v0); auto |
                                              simpl_commut_subst; apply congr_app with (v1:=v') (v2:=v'0); auto]).
    apply Forel_lin_domeq with (lEnv:=lEnv2++lEnv1); auto.
      apply wf_lenv_merge; auto.
        apply disjoint_lenv_split' in Split; auto.
      apply dom_lenv_split in Split.
        rewrite Split. simpl_env. clear. fsetdec.
Qed.

Lemma F_ological_related_congruence__tabs_free :
  forall e e' E D T,
  typing E D e T ->
  typing E D e' T ->
  forall L0,
  (forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
   disjdom L0 (fv_env Env) ->
   disjdom L0 (fv_lenv lEnv) ->
   F_Related_osubst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
   F_Rosubst E rsubst dsubst dsubst' Env ->
   F_Related_oterms T rsubst dsubst dsubst' 
     (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
     (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e')))
     Env lEnv
  ) ->
  forall L K C1 T1' E' D',
  (forall X, X `notin` L -> vcontext (open_tc C1 X)) ->
  (forall X,
    X `notin` L ->
    contexting E D T (open_tc C1 X) ((X, bind_kn K)::E') D' (open_tt T1' X)
  ) ->
  (forall X,
   X `notin` L ->
   typing E D e T ->
   typing E D e' T ->
    (forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
     disjdom L0 (fv_env Env) ->
     disjdom L0 (fv_lenv lEnv) ->
     F_Related_osubst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
     F_Rosubst E rsubst dsubst dsubst' Env ->
     F_Related_oterms T rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e')))
      Env lEnv
    ) ->
   forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
     disjdom (L0 `union` cv_ec (open_tc C1 X) `union` fv_ec (open_tc C1 X) `union` dom E `union` dom D `union` fv_tt T `union` fv_tt (open_tt T1' X) `union` (add X (dom E')) `union` dom D') (fv_env Env) ->
     disjdom (L0 `union` cv_ec (open_tc C1 X) `union` fv_ec (open_tc C1 X) `union` dom E `union` dom D `union` fv_tt T `union` fv_tt (open_tt T1' X) `union` (add X (dom E')) `union` dom D') (fv_lenv lEnv) ->
     F_Related_osubst ((X, bind_kn K)::E') D' gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
     F_Rosubst ((X, bind_kn K)::E') rsubst dsubst dsubst' Env ->
     F_Related_oterms (open_tt T1' X) rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (plug (open_tc C1 X) e))))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (plug (open_tc C1 X) e'))))
      Env lEnv
  ) ->
  forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
  disjdom (L0 `union` cv_ec C1 `union` fv_ec C1 `union` dom E `union` dom D `union` fv_tt T `union` fv_tt T1'  `union` dom E' `union` dom D') (fv_env Env) ->
  disjdom (L0 `union` cv_ec C1 `union` fv_ec C1 `union` dom E `union` dom D `union` fv_tt T `union` fv_tt T1'  `union` dom E' `union` dom D') (fv_lenv lEnv) ->
  F_Related_osubst E' D' gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
  F_Rosubst E' rsubst dsubst dsubst' Env  ->
  F_Related_oterms (typ_all K T1') rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_tabs K (plug C1 (shift_te e))))))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_tabs K (plug C1 (shift_te e'))))))
      Env lEnv.
Proof.
  intros e e' E D T Htyp Htyp' L0 Hlr L K C1 T1' E' D' H0 H1 H2 dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv Disj00 Disj01 Hrel_sub HRsub.
  assert (J:=Hrel_sub). apply F_Related_osubst__inversion in J.
  destruct J as [[[[[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe] Hwfe'] HwfEnv] HwflEnv].
  assert (value (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_tabs K (plug C1 (shift_te e))))))) as Value.
    clear Disj00 Disj01.
    apply delta_gamma_lgamma_osubst_value with (E:=E') (D:=D') (Env:=Env) (lEnv:=lEnv); auto.
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
  assert (value (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_tabs K (plug C1 (shift_te e'))))))) as Value'.
    clear Disj00 Disj01.
    apply delta_gamma_lgamma_osubst_value with (E:=E') (D:=D')(Env:=Env) (lEnv:=lEnv); auto.
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
    
  exists (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_tabs K (plug C1 (shift_te e)))))).
  exists (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_tabs K (plug C1 (shift_te e')))))).
    split.
      assert (typing E' D' (plug (ctx_tabs_free K C1) e) (typ_all K T1')) as Hptyp.
        apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.
           apply contexting_tabs_free with (L:=L); auto.
      apply typing_osubst with (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst) (Env:=Env) (lEnv:=lEnv)in Hptyp; auto.
    split.
      assert (typing E' D' (plug (ctx_tabs_free K C1) e') (typ_all K T1')) as Hptyp'.
        apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.
           apply contexting_tabs_free with (L:=L); auto.
      apply typing_osubst with (dsubst:=dsubst') (gsubst:=gsubst') (lgsubst:=lgsubst')(Env:=Env) (lEnv:=lEnv) in Hptyp'; auto.
    split. split; auto.
    split. split; auto.
      SCase "Frel".
      apply F_Related_ovalues_all_req.
      split; auto.
      split; auto.
        SSCase "Frel".
        exists (L `union` fv_te e `union` dom E `union` fv_env E `union` fv_lenv D `union` fv_env E' `union` fv_lenv D' `union` cv_ec C1 `union` fv_te (plug C1 e) `union` fv_te (plug C1 e') `union` fv_env Env `union` fv_lenv lEnv).
        intros X t2 t2' R Fr HwfR Hfv.
        assert (X `notin` L) as FryL. auto.
        assert (wf_typ ([(X,bind_kn K)]++E') (open_tt T1' X) kn_lin) as WFT'.
          apply H1 in FryL.
          apply contexting_regular in FryL.
          decompose [and] FryL; auto.
        apply H2 with (dsubst:=[(X, t2)]++dsubst) 
                         (dsubst':=[(X, t2')]++dsubst') 
                         (gsubst:=gsubst)
                         (gsubst':=gsubst') 
                         (lgsubst:=lgsubst)
                         (lgsubst':=lgsubst') (Env:=Env) (lEnv:=lEnv)
                         (rsubst:=[(X,R)]++rsubst)in FryL; auto.
        simpl in FryL. simpl_env in FryL.
        clear Disj00 Disj01.
        erewrite swap_subst_te_ogsubst with (E:=E') (dsubst:=dsubst) (Env:=Env) (lEnv:=lEnv)in FryL; eauto using wfor_left_inv. 
        erewrite swap_subst_te_olgsubst with (E:=E') (dsubst:=dsubst) (Env:=Env) (lEnv:=lEnv)in FryL; eauto using wfor_left_inv. 
        erewrite swap_subst_te_ogsubst with  (E:=E')  (dsubst:=dsubst') (Env:=Env) (lEnv:=lEnv)in FryL; eauto using wfor_right_inv.
        erewrite swap_subst_te_olgsubst with  (E:=E')  (dsubst:=dsubst') (Env:=Env) (lEnv:=lEnv)in FryL; eauto using wfor_right_inv.
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
             eapply m_red_tabs_osubst with (T1:=T1') (L:=L `union` cv_ec C1); eauto.
               apply wfor_left_inv in HwfR; auto.

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
             eapply m_red_tabs_osubst with (T1:=T1') (L:=L `union` cv_ec C1); eauto.
               apply wfor_right_inv in HwfR; auto.

               intros X0 X0dom.
               assert (X0 `notin` L) as X0n. auto.
               apply H1 in X0n.
               assert (disjdom (fv_tt X0) (cv_ec C1)) as Disj.
                 apply disjdom_one_2; auto.
               rewrite open_te_plug; auto.
               rewrite <- open_te_expr'; auto.
               apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.       

          clear - Fr Disj00.
          assert (J:=@open_tc_fv_ec_eq C1 X).
          assert (J':=@cv_ec_open_tc_rec C1 0 X).
          assert (J'':=@open_tt_fv_tt_upper T1' X).
          unfold open_tc in *.
          apply disjdom_sym_1.
          apply disjdom_sub with (D1:={{X}} `union` L0 `union` cv_ec C1 `union` fv_ec C1 `union` dom E `union` dom D `union` fv_tt T `union` fv_tt T1' `union` dom E' `union` dom D').
          eapply disjdom_app_r.
          split; auto.
            destruct_notin.
            clear - NotInTac8.
            apply disjdom_one_2; auto.
           
            rewrite J'. rewrite J.
            clear - J''.  simpl in J''.  fsetdec.

          clear - Fr Disj01.
          assert (J:=@open_tc_fv_ec_eq C1 X).
          assert (J':=@cv_ec_open_tc_rec C1 0 X).
          assert (J'':=@open_tt_fv_tt_upper T1' X).
          unfold open_tc in *.
          apply disjdom_sym_1.
          apply disjdom_sub with (D1:={{X}} `union` L0 `union` cv_ec C1 `union` fv_ec C1 `union` dom E `union` dom D `union` fv_tt T `union` fv_tt T1' `union` dom E' `union` dom D').
          eapply disjdom_app_r.
          split; auto.
            destruct_notin.
            clear - NotInTac9.
            apply disjdom_one_2; auto.
           
            rewrite J'. rewrite J.
            clear - J''.  simpl in J''.  fsetdec.

          SSSCase "Fsubst".
          simpl_env.
          apply F_Related_osubst_kind; auto.
          SSSCase "FRsubst".
          simpl_env.
          apply F_Rosubst_rel; auto.
Qed.

Lemma F_ological_related_congruence__tabs_capture :
  forall e e' E D T,
  typing E D e T ->
  typing E D e' T ->
  forall L0,
  (forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
   disjdom L0 (fv_env Env) ->
   disjdom L0 (fv_lenv lEnv) ->
   F_Related_osubst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
   F_Rosubst E rsubst dsubst dsubst' Env ->
   F_Related_oterms T rsubst dsubst dsubst' 
     (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
     (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e')))
     Env lEnv
  ) ->
  forall Y K C1 T1' E' D',
  binds Y (bind_kn K) E' ->
  Y `notin` cv_ec C1 ->
  vcontext C1 ->
  contexting E D T C1 E' D' T1' ->
  wf_lenv (env_remove (Y, bind_kn K) E') D' ->
  (typing E D e T ->
   typing E D e' T ->
    (forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
     disjdom L0 (fv_env Env) ->
     disjdom L0 (fv_lenv lEnv) ->
     F_Related_osubst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
     F_Rosubst E rsubst dsubst dsubst' Env ->
     F_Related_oterms T rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e')))
      Env lEnv
    ) ->
   forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
     disjdom (L0 `union` cv_ec C1 `union` fv_ec C1 `union` dom E `union` dom D `union` fv_tt T `union` fv_tt T1' `union` dom E' `union` dom D') (fv_env Env) ->
     disjdom (L0 `union` cv_ec C1 `union` fv_ec C1 `union` dom E `union` dom D `union` fv_tt T `union` fv_tt T1' `union` dom E' `union` dom D') (fv_lenv lEnv) ->
     F_Related_osubst E' D' gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
     F_Rosubst E' rsubst dsubst dsubst' Env ->
     F_Related_oterms T1' rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (plug C1 e))))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (plug C1 e'))))
      Env lEnv
  ) ->
  forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
  disjdom (L0 `union` ({{Y}} `union` cv_ec (close_tc C1 Y)) `union` fv_ec  (close_tc C1 Y) `union` dom E `union` dom D `union` fv_tt T `union` fv_tt (close_tt T1' Y)  `union` dom (env_remove (Y, bind_kn K) E') `union` dom D') (fv_env Env) ->
  disjdom (L0 `union` ({{Y}} `union` cv_ec  (close_tc C1 Y)) `union` fv_ec  (close_tc C1 Y) `union` dom E `union` dom D `union` fv_tt T `union` fv_tt (close_tt T1' Y)  `union` dom (env_remove (Y, bind_kn K) E')  `union` dom D') (fv_lenv lEnv) ->
  F_Related_osubst (env_remove (Y, bind_kn K) E') D' gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
  F_Rosubst (env_remove (Y, bind_kn K) E') rsubst dsubst dsubst' Env  ->
  F_Related_oterms (typ_all K (close_tt T1' Y)) rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_tabs K (plug (close_tc C1 Y) (close_te (shift_te e) Y))))))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_tabs K (plug (close_tc C1 Y) (close_te (shift_te e') Y))))))
      Env lEnv.
Proof.
    intros e e' E D T Htyp Htyp' L0 Hlr Y K C1 T1' E' D' H H0 H1 Hcontexting H2 IHHcontexting dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv Disj00 Disj01 Hrel_sub HRsub.
    assert (J:=Hrel_sub). apply F_Related_osubst__inversion in J. 
    destruct J as [[[[[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe] Hwfe'] HwfEnv] HwflEnv].

    assert (Fry := @IHHcontexting Htyp Htyp' Hlr).
    assert (wf_env E') as Wfe'.
      apply contexting_regular in Hcontexting.
      decompose [and] Hcontexting; auto.
    assert (EQ1:=@env_remove_inv E' Y (bind_kn K)  Wfe' H).
    destruct EQ1 as [E1' [E2' [EQ1' EQ2']]]; subst.
    rewrite EQ1' in *.

    assert (EQ:=Hwflg).
    apply wf_olgsubst_app_inv in EQ.
    destruct EQ as [dsubst1 [dsubst2 [gsubst1 [gsubst2 [dEQ1 [dEQ2 [dEQ3 [gEQ1 [gEQ2 gEQ3]]]]]]]]]; subst.

    assert (EQ:=Hwflg').
    apply wf_olgsubst_app_inv in EQ.
    destruct EQ as [dsubst1' [dsubst2' [gsubst1' [gsubst2' [dEQ1' [dEQ2' [dEQ3' [gEQ1' [gEQ2' gEQ3']]]]]]]]]; subst.
       
    assert (EQ:=Hwfr).
    apply wf_rsubst_app_inv in EQ.
    destruct EQ as [rsubst1 [rsubst2 [rEQ1 [rEQ2 rEQ3]]]]; subst.

    assert (value (apply_delta_subst (dsubst1++dsubst2) (apply_gamma_subst (gsubst1++gsubst2) (apply_gamma_subst lgsubst (exp_tabs K (plug (close_tc C1 Y) (close_te (shift_te e) Y))))))) as Value.
      clear Disj00 Disj01.
      apply delta_gamma_lgamma_osubst_value with (E:=E1'++E2') (D:=D')(Env:=Env)(lEnv:=lEnv); auto.
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
              clear - H0.
              apply disjdom_one_2; auto.
              clear - XnFv.
              apply disjdom_one_2; auto.
          rewrite <- subst_te_plug; auto. 
          assert (typing (E1'++[(Y, bind_kn K)]++E2') D' (plug C1 e) T1') as Htyp2.
            apply contexting_plug_typing with (e:=e) in Hcontexting; auto.
          apply subst_te_expr; auto.

    assert (value (apply_delta_subst (dsubst1'++dsubst2') (apply_gamma_subst (gsubst1'++gsubst2') (apply_gamma_subst lgsubst' (exp_tabs K (plug (close_tc C1 Y)  (close_te (shift_te e') Y))))))) as Value'.
      clear Disj00 Disj01.
      apply delta_gamma_lgamma_osubst_value with (E:=E1'++E2') (D:=D')(Env:=Env)(lEnv:=lEnv); auto.
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
              clear - H0.
              apply disjdom_one_2; auto.
              clear - XnFv.
              apply disjdom_one_2; auto.
          rewrite <- subst_te_plug; auto. 
          assert (typing (E1'++[(Y, bind_kn K)]++E2') D' (plug C1 e') T1') as Htyp2'.
            apply contexting_plug_typing with (e:=e') in Hcontexting; auto.
          apply subst_te_expr; auto.

    exists (apply_delta_subst (dsubst1++dsubst2) (apply_gamma_subst (gsubst1++gsubst2) (apply_gamma_subst lgsubst (exp_tabs K (plug (close_tc C1 Y) (close_te (shift_te e) Y)))))).
    exists (apply_delta_subst (dsubst1'++dsubst2') (apply_gamma_subst (gsubst1'++gsubst2') (apply_gamma_subst lgsubst' (exp_tabs K (plug (close_tc C1 Y) (close_te (shift_te e') Y)))))).
    split.
      assert (typing (E1'++E2') D' (plug (ctx_tabs_capture Y K (close_tc C1 Y)) e) (typ_all K (close_tt T1' Y))) as Hptyp.
        clear Disj00 Disj01.
        destruct (in_dec Y (fv_te e)) as [yine | ynine].
          simpl.
          apply typing_tabs with (L:=dom (E1'++E2') `union` dom D' `union` dom E `union` dom D `union` {{Y}} `union` cv_ec C1 `union` cv_ec (close_tc C1 Y)); auto.
            intros X Xn.
            rewrite <- shift_te_expr; auto.
            rewrite open_te_plug; auto.
              rewrite close_open_te__subst_te; auto.
              rewrite close_open_tc__subst_tc; auto.
                apply plug_vcontext__value.
                  apply vcontext_through_subst_tc; auto.
                  apply plug_context__expr.
                    apply context_through_subst_tc; auto.
                      apply vcontext__context in H1; auto.
                    apply subst_te_expr; auto.             
                apply vcontext__context in H1; auto.
              clear - Xn.
              apply disjdom_one_2; auto.        

            intros X Xn.
            rewrite <- shift_te_expr; auto.
            assert (disjdom (fv_tt X) (cv_ec (close_tc C1 Y))) as Disj.
              apply disjdom_one_2; auto.
            rewrite open_te_plug; auto.
            assert (Y `in` ddom_env E) as J.
              apply in_fv_te_typing' with (X:=Y) in Htyp; auto.
            rewrite close_open_te__subst_te; auto.
            assert (context C1) as Ctx1.
              apply contexting__context in Hcontexting; auto.
            rewrite close_open_tc__subst_tc; auto.
            apply dbinds_In_inv in J.
            destruct J as [k Binds].
            assert (wf_env E) as Wfe. auto.
            assert (J:=@env_remove2_inv E Y (bind_kn k) Wfe Binds).
            destruct J as [E1 [E2 [EQ1 EQ2]]]; subst.

            apply typing_typ_permute; auto. 
            assert (J:=Hcontexting).
            apply contexting_typ_renaming_one with (Y:=X) in Hcontexting; auto.
            assert (Y `notin` fv_env E1' `union` fv_env E2' `union` fv_lenv D') as YnE1'E2'D'.
              apply wf_lenv_notin_fv_env with (K:=K); auto.          
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
            apply contexting_plug_typing with (E:=map (subst_tb Y X) E1++[(X, bind_kn k)]++E2) (D:=map (subst_tlb Y X) D) (T:=subst_tt Y X T); auto.
              rewrite close_open_tt__subst_tt; auto.
                apply contexting_regular in J.
                decompose [and] J.
                apply type_from_wf_typ in H9; auto.

              simpl_env in Xn.
              apply typing_typ_renaming_one with (Y:=X) in Htyp; auto.

          rewrite <- EQ1'.
          apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.
            apply contexting_tabs_capture; auto.
              rewrite EQ1'. auto.
      apply typing_osubst with (dsubst:=dsubst1++dsubst2) (gsubst:=gsubst1++gsubst2) (lgsubst:=lgsubst)(Env:=Env)(lEnv:=lEnv) in Hptyp; auto.
    split.
      assert (typing (E1'++E2') D' (plug (ctx_tabs_capture Y K (close_tc C1 Y)) e') (typ_all K (close_tt T1' Y))) as Hptyp'.
        clear Disj00 Disj01.
        destruct (in_dec Y (fv_te e')) as [yine' | ynine'].
          simpl.
          apply typing_tabs with (L:=dom (E1'++E2') `union` dom D' `union` dom E `union` dom D `union` {{Y}} `union` cv_ec C1 `union` cv_ec (close_tc C1 Y)); auto.
            intros X Xn.
            rewrite <- shift_te_expr; auto.
            rewrite open_te_plug; auto.
              rewrite close_open_te__subst_te; auto.
              rewrite close_open_tc__subst_tc; auto.
                apply plug_vcontext__value.
                  apply vcontext_through_subst_tc; auto.
                  apply plug_context__expr.
                    apply context_through_subst_tc; auto.
                      apply vcontext__context in H1; auto.
                    apply subst_te_expr; auto.             
                apply vcontext__context in H1; auto.
              apply disjdom_one_2; auto.        

            intros X Xn.
            rewrite <- shift_te_expr; auto.
            assert (disjdom (fv_tt X) (cv_ec (close_tc C1 Y))) as Disj.
              apply disjdom_one_2; auto.
            rewrite open_te_plug; auto.
            assert (Y `in` ddom_env E) as J.
              apply in_fv_te_typing' with (X:=Y) in Htyp'; auto.
            rewrite close_open_te__subst_te; auto.
            assert (context C1) as Ctx1.
              apply contexting__context in Hcontexting; auto.
            rewrite close_open_tc__subst_tc; auto.
            apply dbinds_In_inv in J.
            destruct J as [k Binds].
            assert (wf_env E) as Wfe. auto.
            assert (J:=@env_remove2_inv E Y (bind_kn k) Wfe Binds).
            destruct J as [E1 [E2 [EQ1 EQ2]]]; subst.

            apply typing_typ_permute; auto. 
            assert (J:=Hcontexting).
            apply contexting_typ_renaming_one with (Y:=X) in Hcontexting; auto.
            assert (Y `notin` fv_env E1' `union` fv_env E2' `union` fv_lenv D') as YnE1'E2'D'.
              apply wf_lenv_notin_fv_env with (K:=K); auto.          
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
            apply contexting_plug_typing with (E:=map (subst_tb Y X) E1++[(X, bind_kn k)]++E2) (D:=map (subst_tlb Y X) D) (T:=subst_tt Y X T); auto.
              rewrite close_open_tt__subst_tt; auto.
                apply contexting_regular in J.
                decompose [and] J.
                apply type_from_wf_typ in H9; auto.

              simpl_env in Xn.
              apply typing_typ_renaming_one with (Y:=X) in Htyp'; auto.

          rewrite <- EQ1'.
          apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.
            apply contexting_tabs_capture; auto.
              rewrite EQ1'. auto.
      apply typing_osubst with (dsubst:=dsubst1'++dsubst2') (gsubst:=gsubst1'++gsubst2') (lgsubst:=lgsubst')(Env:=Env)(lEnv:=lEnv) in Hptyp'; auto.
    split. split; auto.
    split. split; auto.
      SCase "Frel".
      apply F_Related_ovalues_all_req.
      split; auto.
      split; auto.

        SSCase "Frel".
        exists (fv_te e `union` dom E `union` fv_env E `union` fv_lenv D `union` {{Y}} `union` fv_env E1' `union` fv_lenv D' `union` cv_ec C1 `union` fv_te (plug C1 e) `union` fv_te (plug C1 e') `union` dom E1' `union` dom E2' `union` fv_tt T1' `union` fv_env Env `union` fv_lenv lEnv).
        intros X t2 t2' R Fr HwfR Hfv.

        assert (F_Related_osubst (E1'++[(Y, bind_kn K)]++E2') D' (gsubst1++gsubst2) (gsubst1'++gsubst2') lgsubst lgsubst' (rsubst1++[(Y,R)]++rsubst2) (dsubst1++[(Y,t2)]++dsubst2) (dsubst1'++[(Y,t2')]++dsubst2') Env lEnv) as Hrel_sub'.
          assert (Y `notin` dom E1') as YnE1'.
            apply fresh_mid_head with (E:=E2') (a:=bind_kn K); auto.
          assert (Y `notin` dom E2') as YnE2'.
             apply fresh_mid_tail with (F:=E1') (a:=bind_kn K); auto.
          assert (Y `notin` dom D') as YnD'.
            apply contexting_regular in Hcontexting.
            decompose [and] Hcontexting.
            clear - H7 Hwfe'.
            apply wf_lenv_notin_fv_env with (E1:=E1') (E2:=E2') (X:=Y) (K:=K) in H7; auto.
          assert (Y `notin` fv_env Env) as YnEnv.
            clear - Disj00.
            apply disjdom_app_2 in Disj00.
            apply disjdom_app_1 in Disj00.
            apply disjdom_app_1 in Disj00.
            destruct Disj00 as [J1 J2].
            apply J1; auto.
          assert (Y `notin` fv_lenv lEnv) as YnlEnv.
            clear - Disj01.
            apply disjdom_app_2 in Disj01.
            apply disjdom_app_1 in Disj01.
            apply disjdom_app_1 in Disj01.
            destruct Disj01 as [J1 J2].
            apply J1; auto.
          clear Disj00 Disj01.
          apply F_Related_osubst_dweaken; auto.

        assert (F_Rosubst (E1'++[(Y, bind_kn K)] ++E2') (rsubst1++[(Y, R)]++rsubst2) (dsubst1++[(Y, t2)] ++dsubst2) (dsubst1'++[(Y, t2')] ++dsubst2') Env) as HRsub'. 
          assert (Y `notin` dom E1') as ynE1'.
             apply fresh_mid_head with (E:=E2') (a:=bind_kn K); auto.
          assert (Y `notin` dom E2') as ynE2'.
             apply fresh_mid_tail with (F:=E1') (a:=bind_kn K); auto.
          assert (Y `notin` fv_env Env) as YnEnv.
            clear - Disj00.
            apply disjdom_app_2 in Disj00.
            apply disjdom_app_1 in Disj00.
            apply disjdom_app_1 in Disj00.
            destruct Disj00 as [J1 J2].
            apply J1; auto.
          clear Disj00 Disj01.
          apply F_Rosubst_dweaken; auto.       

       assert (
       disjdom
         (union L0
            (union (cv_ec C1)
               (union (fv_ec C1)
                  (union (dom E)
                     (union (dom D)
                        (union (fv_tt T)
                           (union (fv_tt T1')
                              (union (dom (E1' ++ [(Y, bind_kn K)] ++ E2')) (dom D')))))))))
         (fv_env Env)) as Disj00'.

           clear - Disj00.
           assert (J:=@close_tc_fv_ec_eq C1 Y).
           assert (J':=@close_tc_cv_ec_eq C1 Y).
           assert (J'':=@close_tt_fv_tt_lower T1' Y).
           apply disjdom_sym_1.
           apply disjdom_sub with (D1:=L0 `union` ({{Y}} `union` (cv_ec (close_tc C1 Y))) `union` (fv_ec (close_tc C1 Y)) `union` dom E `union` dom D `union` fv_tt T `union` (fv_tt (close_tt T1' Y)) `union` (dom (E1'++E2')) `union` dom D').
             apply disjdom_sym_1; auto.
             simpl_env. rewrite <- J.  rewrite <- J'.  clear - J''. fsetdec.

       assert (
       disjdom
         (union L0
            (union (cv_ec C1)
               (union (fv_ec C1)
                  (union (dom E)
                     (union (dom D)
                        (union (fv_tt T)
                           (union (fv_tt T1')
                              (union (dom (E1' ++ [(Y, bind_kn K)] ++ E2')) (dom D')))))))))
         (fv_lenv lEnv)) as Disj01'.
           clear - Disj01.
           assert (J:=@close_tc_fv_ec_eq C1 Y).
           assert (J':=@close_tc_cv_ec_eq C1 Y).
           assert (J'':=@close_tt_fv_tt_lower T1' Y).
           apply disjdom_sym_1.
           apply disjdom_sub with (D1:=L0 `union` ({{Y}} `union` (cv_ec (close_tc C1 Y))) `union` (fv_ec (close_tc C1 Y)) `union` dom E `union` dom D `union` fv_tt T `union` (fv_tt (close_tt T1' Y)) `union` (dom (E1'++E2')) `union` dom D').
             apply disjdom_sym_1; auto.
             simpl_env. rewrite <- J.  rewrite <- J'.  clear - J''. fsetdec.

        assert (J:=@Fry (dsubst1++[(Y, t2)]++dsubst2) (dsubst1'++[(Y, t2')]++dsubst2') (gsubst1++gsubst2) (gsubst1'++gsubst2') lgsubst lgsubst' (rsubst1++[(Y, R)]++rsubst2) Env lEnv Disj00' Disj01' Hrel_sub' HRsub').

        assert (
            apply_delta_subst (dsubst1++[(Y, t2)]++dsubst2) (apply_gamma_subst (gsubst1++gsubst2) (apply_gamma_subst lgsubst (plug C1 e))) =
            apply_delta_subst (dsubst1++dsubst2) (apply_gamma_subst (gsubst1++gsubst2) (apply_gamma_subst lgsubst (subst_te Y t2 (plug C1 e))))
                  ) as Heq1. simpl.
           simpl_env.
           assert (wf_typ Env t2 K) as Wft2. apply wfor_left_inv in HwfR; auto.
           apply F_Related_osubst__inversion in Hrel_sub'.
           decompose [prod] Hrel_sub'; auto.
           apply F_Related_osubst__inversion in Hrel_sub.
           decompose [prod] Hrel_sub; auto.
           rewrite delta_osubst_opt' with (Env:=Env) (E':=E1') (E:=E2') (k:=K); auto.
           assert (Y `notin` dom Env) as YnE. 
             clear - Disj00.
             apply disjdom_app_2 in Disj00.
             apply disjdom_app_1 in Disj00.
             apply disjdom_app_1 in Disj00.
             destruct Disj00 as [J1 J2].
             apply free_env__free_dom.
             apply J1; auto.
           rewrite swap_subst_te_ogsubst with (Env:=Env) (lEnv:=lEnv) (D:=D') (E:=E1'++E2') (dsubst:=dsubst1++dsubst2) (K:=K) (lgsubst:=lgsubst); auto.
           rewrite swap_subst_te_olgsubst with (Env:=Env) (lEnv:=lEnv) (D:=D') (E:=E1'++E2') (dsubst:=dsubst1++dsubst2) (K:=K) (gsubst:=gsubst1++gsubst2); auto.

         assert (
            apply_delta_subst (dsubst1'++[(Y,t2')]++dsubst2') (apply_gamma_subst (gsubst1'++gsubst2') (apply_gamma_subst lgsubst' (plug C1 e'))) =
            apply_delta_subst (dsubst1'++dsubst2') (apply_gamma_subst (gsubst1'++gsubst2') (apply_gamma_subst lgsubst' (subst_te Y t2' (plug C1 e'))))
                  ) as Heq2.  simpl.
           simpl_env.
           assert (wf_typ Env t2' K) as Wft2. apply wfor_right_inv in HwfR; auto.
           apply F_Related_osubst__inversion in Hrel_sub'.
           decompose [prod] Hrel_sub'; auto.
           apply F_Related_osubst__inversion in Hrel_sub.
           decompose [prod] Hrel_sub; auto.
           rewrite delta_osubst_opt' with (E':=E1') (E:=E2') (k:=K)  (Env:=Env); auto.
           assert (Y `notin` dom Env) as YnE. 
             clear - Disj00.
             apply disjdom_app_2 in Disj00.
             apply disjdom_app_1 in Disj00.
             apply disjdom_app_1 in Disj00.
             destruct Disj00 as [J1 J2].
             apply free_env__free_dom.
             apply J1; auto.
           rewrite swap_subst_te_ogsubst with  (Env:=Env) (lEnv:=lEnv)  (D:=D') (E:=E1'++E2') (dsubst:=dsubst1'++dsubst2') (K:=K) (lgsubst:=lgsubst'); auto.
           rewrite swap_subst_te_olgsubst with  (Env:=Env) (lEnv:=lEnv)  (D:=D') (E:=E1'++E2') (dsubst:=dsubst1'++dsubst2') (K:=K) (gsubst:=gsubst1'++gsubst2'); auto.

         rewrite Heq1 in J. rewrite Heq2 in J. clear Heq1 Heq2.
         destruct J as [v [v' [Ht [Ht' [[Hbrc Hv] [[Hbrc' Hv'] Hrel]]]]]].
         exists (v). exists (v').
         split.
           SSSCase "norm".
           split; auto.
           apply bigstep_red_trans with (e':=(apply_delta_subst (dsubst1++dsubst2) (apply_gamma_subst (gsubst1++gsubst2)  (apply_gamma_subst lgsubst (subst_te Y t2 (plug C1 e)))))); auto.
              assert (apply_delta_subst_typ (dsubst1++dsubst2) t2 = t2) as Heq1.
                 rewrite delta_osubst_closed_typ; auto.
                   assert (disjdom (dom (E1'++E2')) (fv_env Env)) as Disj001.
                     apply disjdom_sym_1 in Disj00.
                     apply disjdom_sub with (D2:=dom (E1'++E2')) in Disj00.
                       apply disjdom_sym_1 in Disj00; auto.
                       clear. simpl_env. fsetdec.
                   clear Disj00 Disj01.
                   split; intros x0 x0notin.
                     simpl_env. rewrite <- dEQ2. rewrite <- dEQ3.
                     clear - HwfR x0notin Disj001.
                     apply wfor_left_inv in HwfR.
                     apply in_fv_wf with (X:=x0) in HwfR; auto.
                       destruct Disj001 as [J1 J2].
                       apply free_dom__free_env in HwfR.
                       apply J2 in HwfR; auto.

                     simpl_env in x0notin. rewrite <- dEQ2 in x0notin. rewrite <- dEQ3 in x0notin.
                     clear - HwfR x0notin Disj001.
                     apply wfor_left_inv in HwfR.
                     apply notin_fv_wf with (X:=x0) in HwfR; auto.
                       destruct Disj001 as [J1 J2].
                       apply free_env__free_dom.
                       apply J1.
                       apply ddom__dom; simpl_env; auto.
              rewrite <- Heq1.
              rewrite commut_gamma_subst_tabs.
              rewrite commut_gamma_subst_tabs.
              assert (subst_te Y (apply_delta_subst_typ  (dsubst1++dsubst2) t2) (plug C1 e) = subst_te Y t2 (plug C1 e)) as Heq2. 
                 rewrite Heq1. auto. 
              rewrite Heq2.
              assert (typing (E1'++[(Y, bind_kn K)]++E2') D' (plug C1 e) T1') as Typinge.
                apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.
             assert (disjdom (union {{Y}} (fv_tt t2)) (cv_ec C1)) as Disj0.
               eapply disjdom_app_l.
               split.
                 clear - H0.
                 apply disjdom_one_2; auto.

                  clear - HwfR Disj00.
                  apply wfor_left_inv in HwfR.
                  apply wft_fv_tt_sub in HwfR.
                  apply disjdom_sym_1.
                  apply disjdom_sub with (D1:= dom Env); auto.
                  apply disjdom_sub with (D1:= fv_env Env).
                      clear - Disj00.
                      assert (J:=@close_tc_cv_ec_eq C1 Y).
                      apply disjdom_sym_1.
                      apply disjdom_sub with (D1:=L0 `union` ({{Y}} `union` (cv_ec (close_tc C1 Y))) `union` (fv_ec (close_tc C1 Y)) `union` dom E `union` dom D `union` fv_tt T `union` (fv_tt (close_tt T1' Y)) `union` (dom (E1'++E2')) `union` dom D').
                        apply disjdom_sym_1; auto.
                        simpl_env. rewrite <- J. clear. fsetdec.                                       

                    apply fv_env__includes__dom.

             assert (type t2) as Type2.
               apply wfor_left_inv in HwfR.
               apply type_from_wf_typ in HwfR; auto. 
              rewrite subst_te_plug; auto.
              rewrite <- close_open_te__subst_te; auto.
              assert (context C1) as Context1.
                apply contexting__context in Hcontexting; auto.    
              rewrite <- close_open_tc__subst_tc; auto.
              assert (disjdom (fv_tt t2) (cv_ec (close_tc C1 Y))) as Disj.
                clear - Disj00 HwfR.
                apply disjdom_sym_1 in Disj00.
                apply disjdom_sub with (D2:=cv_ec (close_tc C1 Y)) in Disj00.
                  apply disjdom_sym_1.
                  apply disjdom_sub with (D1:=dom Env).
                    apply disjdom_sub with (D1:=fv_env Env).
                      apply disjdom_sym_1; auto.
                        apply fv_env__includes__dom.
                      apply wft_fv_tt_sub with (K:=K).
                        apply wfor_left_inv in HwfR; auto.
                    clear. fsetdec.
              rewrite <- open_te_plug; auto.
              rewrite commut_lgamma_osubst_open_te with (Env:=Env) (lEnv:=lEnv) (E:=E1'++E2')(D:=D')(dsubst:=dsubst1++dsubst2)(gsubst:=gsubst1++gsubst2); auto.
              rewrite commut_gamma_osubst_open_te with (Env:=Env) (lEnv:=lEnv) (E:=E1'++E2')(D:=D')(dsubst:=dsubst1++dsubst2)(lgsubst:=lgsubst); auto.
              rewrite <- shift_te_expr; auto.
              apply red_tabs_preserved_under_delta_osubst with (Env:=Env) (dE:=E1'++E2'); auto.

              rewrite <- commut_gamma_subst_tabs; auto.
              rewrite <- commut_gamma_osubst_open_te with (Env:=Env) (lEnv:=lEnv) (E:=E1'++E2') (dsubst:=dsubst1++dsubst2) (D:=D') (lgsubst:=lgsubst); auto.
              apply red_tabs_preserved_under_gamma_osubst with(Env:=Env) (lEnv:=lEnv)  (E:=E1'++E2') (dsubst:=dsubst1++dsubst2) (D:=D') (lgsubst:=lgsubst); auto. 

              rewrite <- commut_gamma_subst_tabs; auto.
              rewrite <- commut_lgamma_osubst_open_te with (Env:=Env) (lEnv:=lEnv) (E:=E1'++E2')(D:=D')(dsubst:=dsubst1++dsubst2)(gsubst:=gsubst1++gsubst2); auto.
              apply red_tabs_preserved_under_lgamma_osubst with (Env:=Env) (lEnv:=lEnv) (E:=E1'++E2')(D:=D')(dsubst:=dsubst1++dsubst2)(gsubst:=gsubst1++gsubst2); auto. 

              apply red_tabs; auto.
                apply expr_tabs with (L:=(cv_ec (close_tc C1 Y)) `union` cv_ec C1).
                   intros.
                   assert (disjdom (fv_tt X0) (cv_ec (close_tc C1 Y))) as Disj'.
                     simpl. clear - H3.
                     apply disjdom_one_2; auto.
                   rewrite open_te_plug; auto.
                   rewrite close_open_tc__subst_tc; auto.
                   rewrite close_open_te__subst_te; auto.
                  assert (disjdom (union {{Y}} (fv_tt X0)) (cv_ec C1)) as Disj0'.
                     eapply disjdom_app_l.
                     split.
                       clear - H0.
                       apply disjdom_one_2; auto.

                       clear - H3.
                       apply disjdom_one_2; auto.
                   rewrite <- subst_te_plug; auto.

         split; auto.
           SSSCase "norm".
           split; auto.
           apply bigstep_red_trans with (e':=(apply_delta_subst (dsubst1'++dsubst2') (apply_gamma_subst (gsubst1'++gsubst2')  (apply_gamma_subst lgsubst' (subst_te Y t2' (plug C1 e')))))); auto.
              assert (apply_delta_subst_typ (dsubst1'++dsubst2') t2' = t2') as Heq1.
                 rewrite delta_osubst_closed_typ; auto.
                   assert (disjdom (dom (E1'++E2')) (fv_env Env)) as Disj001.
                     apply disjdom_sym_1 in Disj00.
                     apply disjdom_sub with (D2:=dom (E1'++E2')) in Disj00.
                       apply disjdom_sym_1 in Disj00; auto.
                       clear. simpl_env. fsetdec.
                   clear Disj00 Disj01.
                   split; intros x0 x0notin.
                     simpl_env. rewrite <- dEQ2'. rewrite <- dEQ3'.
                     clear - HwfR x0notin Disj001.
                     apply wfor_right_inv in HwfR.
                     apply in_fv_wf with (X:=x0) in HwfR; auto.
                       destruct Disj001 as [J1 J2].
                       apply free_dom__free_env in HwfR.
                       apply J2 in HwfR; auto.

                     simpl_env in x0notin. rewrite <- dEQ2' in x0notin. rewrite <- dEQ3' in x0notin.
                     clear - HwfR x0notin Disj001.
                     apply wfor_right_inv in HwfR.
                     apply notin_fv_wf with (X:=x0) in HwfR; auto.
                       destruct Disj001 as [J1 J2].
                       apply free_env__free_dom.
                       apply J1.
                       apply ddom__dom; simpl_env; auto.
              rewrite <- Heq1.
              rewrite commut_gamma_subst_tabs.
              rewrite commut_gamma_subst_tabs.
              assert (subst_te Y (apply_delta_subst_typ  (dsubst1'++dsubst2') t2') (plug C1 e') = subst_te Y t2' (plug C1 e')) as Heq2. 
                 rewrite Heq1. auto. 
              rewrite Heq2.
              assert (typing (E1'++[(Y, bind_kn K)]++E2') D' (plug C1 e') T1') as Typinge'.
                apply contexting_plug_typing with (E:=E) (D:=D) (T:=T); auto.
             assert (disjdom (union {{Y}} (fv_tt t2')) (cv_ec C1)) as Disj0.
               eapply disjdom_app_l.
               split.
                 clear - H0.
                 apply disjdom_one_2; auto.

                  clear - HwfR Disj00.
                  apply wfor_right_inv in HwfR.
                  apply wft_fv_tt_sub in HwfR.
                  apply disjdom_sym_1.
                  apply disjdom_sub with (D1:= dom Env); auto.
                  apply disjdom_sub with (D1:= fv_env Env).
                      clear - Disj00.
                      assert (J:=@close_tc_cv_ec_eq C1 Y).
                      apply disjdom_sym_1.
                      apply disjdom_sub with (D1:=L0 `union` ({{Y}} `union` (cv_ec (close_tc C1 Y))) `union` (fv_ec (close_tc C1 Y)) `union` dom E `union` dom D `union` fv_tt T `union` (fv_tt (close_tt T1' Y)) `union` (dom (E1'++E2')) `union` dom D').
                        apply disjdom_sym_1; auto.
                        simpl_env. rewrite <- J. clear. fsetdec.                                       

                    apply fv_env__includes__dom.
             assert (type t2') as Type2'.
               apply wfor_right_inv in HwfR.
               apply type_from_wf_typ in HwfR; auto. 
              rewrite subst_te_plug; auto.
              rewrite <- close_open_te__subst_te; auto.
              assert (context C1) as Context1.
                apply contexting__context in Hcontexting; auto.    
              rewrite <- close_open_tc__subst_tc; auto.
              assert (disjdom (fv_tt t2') (cv_ec (close_tc C1 Y))) as Disj.
                clear - Disj00 HwfR.
                apply disjdom_sym_1 in Disj00.
                apply disjdom_sub with (D2:=cv_ec (close_tc C1 Y)) in Disj00.
                  apply disjdom_sym_1.
                  apply disjdom_sub with (D1:=dom Env).
                    apply disjdom_sub with (D1:=fv_env Env).
                      apply disjdom_sym_1; auto.
                        apply fv_env__includes__dom.
                      apply wft_fv_tt_sub with (K:=K).
                        apply wfor_right_inv in HwfR; auto.
                    clear. fsetdec.
              rewrite <- open_te_plug; auto.
              rewrite commut_lgamma_osubst_open_te with (Env:=Env) (lEnv:=lEnv) (E:=E1'++E2')(D:=D')(dsubst:=dsubst1'++dsubst2')(gsubst:=gsubst1'++gsubst2'); auto.
              rewrite commut_gamma_osubst_open_te with (Env:=Env) (lEnv:=lEnv) (E:=E1'++E2')(D:=D')(dsubst:=dsubst1'++dsubst2')(lgsubst:=lgsubst'); auto.
              rewrite <- shift_te_expr; auto.
              apply red_tabs_preserved_under_delta_osubst with(Env:=Env) (dE:=E1'++E2'); auto.

              rewrite <- commut_gamma_subst_tabs; auto.
              rewrite <- commut_gamma_osubst_open_te with(Env:=Env) (lEnv:=lEnv)  (E:=E1'++E2') (dsubst:=dsubst1'++dsubst2') (D:=D') (lgsubst:=lgsubst'); auto.
              apply red_tabs_preserved_under_gamma_osubst with (Env:=Env) (lEnv:=lEnv) (E:=E1'++E2') (dsubst:=dsubst1'++dsubst2') (D:=D') (lgsubst:=lgsubst'); auto. 

              rewrite <- commut_gamma_subst_tabs; auto.
              rewrite <- commut_lgamma_osubst_open_te with (Env:=Env) (lEnv:=lEnv) (E:=E1'++E2')(D:=D')(dsubst:=dsubst1'++dsubst2')(gsubst:=gsubst1'++gsubst2'); auto.
              apply red_tabs_preserved_under_lgamma_osubst with (Env:=Env) (lEnv:=lEnv) (E:=E1'++E2')(D:=D')(dsubst:=dsubst1'++dsubst2')(gsubst:=gsubst1'++gsubst2'); auto. 

              apply red_tabs; auto.
                apply expr_tabs with (L:=(cv_ec (close_tc C1 Y)) `union` cv_ec C1).
                   intros.
                   assert (disjdom (fv_tt X0) (cv_ec (close_tc C1 Y))) as Disj'.
                     clear - H3.
                     apply disjdom_one_2; auto.
                   rewrite open_te_plug; auto.
                   rewrite close_open_tc__subst_tc; auto.
                   rewrite close_open_te__subst_te; auto.
                  assert (disjdom (union {{Y}} (fv_tt X0)) (cv_ec C1)) as Disj0'.
                     eapply disjdom_app_l.
                     split.
                       clear - H0.
                       apply disjdom_one_2; auto.

                       clear - H3.  
                       apply disjdom_one_2; auto.
                   rewrite <- subst_te_plug; auto.

               simpl_env.
               rewrite close_open_tt__subst_tt; auto.
                 assert (wf_delta_osubst ([(X, bind_kn K)]++E1'++E2') ([(X, t2)]++dsubst1++dsubst2) Env) as Wfd.
                   apply F_Rosubst__wf_osubst in HRsub.
                   decompose [prod] HRsub.
                   clear - a0 HwfR Fr dEQ2 dEQ3.
                   eapply odsubst_weaken_head; simpl_env; eauto using wfor_left_inv.

                 assert (wf_delta_osubst ([(X, bind_kn K)]++E1'++E2') ([(X, t2')]++dsubst1'++dsubst2') Env) as Wfd'.
                   apply F_Rosubst__wf_osubst in HRsub.
                   decompose [prod] HRsub.
                   clear - b0 HwfR Fr dEQ2' dEQ3'.
                   eapply odsubst_weaken_head; simpl_env; eauto using wfor_right_inv.

                 apply F_Rosubst__wf_osubst in HRsub'.
                 decompose [prod] HRsub'; auto.
                 clear - Hrel Wfd Wfd' b a0 b0 Hwfd Hwfd' Fr rEQ2 rEQ3 dEQ2 dEQ3 dEQ2' dEQ3' HwfR.
                 apply Forel_typ_permute_renaming_one with (E1:=E1')(E2:=E2')(K:=K) (X:=Y); auto.
               
                 apply contexting_regular in Hcontexting.
                 decompose [and] Hcontexting.
                 apply type_from_wf_typ in H9; auto.
Qed.

Lemma F_ological_related_congruence__tapp :
  forall e e' E D T,
  typing E D e T ->
  typing E D e' T ->
  forall L0,
  (forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
   disjdom L0 (fv_env Env) ->
   disjdom L0 (fv_lenv lEnv) ->
   F_Related_osubst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
   F_Rosubst E rsubst dsubst dsubst' Env ->
   F_Related_oterms T rsubst dsubst dsubst' 
     (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
     (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e')))
     Env lEnv
  ) ->
  forall K  C1 T' T2' E' D',
  contexting E D T C1 E' D' (typ_all K T2') ->
  wf_typ E' T' K ->
  (typing E D e T ->
   typing E D e' T ->
    (forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
     disjdom L0 (fv_env Env) ->
     disjdom L0 (fv_lenv lEnv) ->
     F_Related_osubst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
     F_Rosubst E rsubst dsubst dsubst' Env ->
     F_Related_oterms T rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e')))
      Env lEnv
    ) ->
   forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
     disjdom (L0 `union` cv_ec C1 `union` fv_ec C1 `union` dom E `union` dom D `union` fv_tt T `union` fv_tt T2' `union` dom E' `union` dom D') (fv_env Env) ->
     disjdom (L0 `union` cv_ec C1 `union` fv_ec C1 `union` dom E `union` dom D `union` fv_tt T `union` fv_tt T2'  `union` dom E' `union` dom D') (fv_lenv lEnv) ->
     F_Related_osubst E' D' gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
     F_Rosubst E' rsubst dsubst dsubst' Env ->
     F_Related_oterms (typ_all K T2') rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (plug C1 e))))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (plug C1 e'))))
      Env lEnv
  ) ->
  forall dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
  disjdom (L0 `union` cv_ec C1 `union` fv_ec C1 `union` dom E `union` dom D `union` fv_tt T `union` fv_tt (open_tt T2' T') `union` dom E' `union` dom D') (fv_env Env) ->
  disjdom (L0 `union` cv_ec C1 `union` fv_ec C1 `union` dom E `union` dom D `union` fv_tt T `union` fv_tt (open_tt T2' T') `union` dom E' `union` dom D') (fv_lenv lEnv) ->
  F_Related_osubst E' D' gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
  F_Rosubst E' rsubst dsubst dsubst' Env  ->
  F_Related_oterms (open_tt T2' T') rsubst dsubst dsubst' 
      (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_tapp (plug C1 e) T'))))
      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_tapp (plug C1 e') T'))))
      Env lEnv.
Proof.
   intros e e' E D T Htyp Htyp' L0 Hlr K C1 T' T2' E' D' Hcontexting H IHHcontexting dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv Disj00 Disj01 Hrel_sub HRsub.  
   assert (J:=Hrel_sub). apply F_Related_osubst__inversion in J. 
   destruct J as [[[[[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe] Hwfe'] HwfEnv] HwflEnv].
   assert (
      F_Related_oterms (typ_all K T2') rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (plug C1 e))))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (plug C1 e'))))
         Env lEnv
     ) as FR_AllType.
      apply IHHcontexting; auto.
        clear - Disj00.
        apply disjdom_sym_1.
        apply disjdom_sub with (D1:=L0 `union` cv_ec C1 `union` fv_ec C1 `union` dom E `union` dom D `union` fv_tt T  `union` fv_tt (open_tt T2' T') `union` dom E' `union` dom D').
          apply disjdom_sym_1; auto.

          assert (J:=@open_tt_fv_tt_lower T2' T').
          clear Disj00.  fsetdec.        

        clear - Disj01.
        apply disjdom_sym_1.
        apply disjdom_sub with (D1:=L0 `union` cv_ec C1 `union` fv_ec C1 `union` dom E `union` dom D `union` fv_tt T  `union` fv_tt (open_tt T2' T') `union` dom E' `union` dom D').
          apply disjdom_sym_1; auto.

          assert (J:=@open_tt_fv_tt_lower T2' T').
          clear Disj01.  fsetdec.        
   destruct FR_AllType as [v [v' [Ht [Ht' [Hn [Hn' Hrel]]]]]].

   clear Disj00 Disj01.

   apply F_Related_ovalues_all_leq in Hrel.
   destruct Hrel as [Hv [Hv' [L Hall]]]; subst.
   unfold open_tt in Hall.

   assert (forall X,
     X `notin` dom (E') `union` fv_tt T2' ->
     wf_typ ([(X, bind_kn K)]++E') (open_tt T2' X) kn_lin) as w.
     apply contexting_regular in Hcontexting.
     destruct Hcontexting as [J1 [J2 [J3 [J4 [J5 J6]]]]].
     eapply wft_all_inv; eauto.

   pick fresh y.
   assert (y `notin` L) as Fr'. auto.
   destruct (@Hall y (apply_delta_subst_typ dsubst T') (apply_delta_subst_typ dsubst' T') 
                                (F_FORel T' (rho_nil++rsubst) (delta_nil++dsubst) (delta_nil++dsubst') Env)
                                Fr'
                   ) as [u [u' [Hn_vt2u [Hn_v't2'u' Hrel_wft]]]]; auto.
          apply F_FORel__R__wfor with (E:=E') (rsubst:=rsubst); auto.
             simpl_env. split; auto.  

              assert (ddom_env E' [=] dom rsubst) as EQ.
                apply dom_rho_subst; auto.
              assert (y `notin` ddom_env E') as Fv.
                 apply dom__ddom; auto.
              rewrite EQ in Fv. auto.

   exists(u). exists (u').
       split. simpl_commut_subst in *; rewrite commut_delta_osubst_open_tt with (dE:=E') (Env:=Env); auto.
                eapply typing_tapp; eauto using wft_osubst.
       split. simpl_commut_subst in *; rewrite commut_delta_osubst_open_tt with (dE:=E') (Env:=Env); auto.
                eapply typing_tapp; eauto using wft_osubst.
       split.
       SCase "Norm".
       simpl_commut_subst.
       eapply m_ocongr_tapp; eauto.

      split.
      SCase "Norm".
      simpl_commut_subst.
      eapply m_ocongr_tapp; eauto.

      SCase "Frel".
      unfold open_tt.
      assert (F_Related_ovalues (open_tt_rec 0 T' T2') (rho_nil++rsubst) (delta_nil++dsubst) (delta_nil++dsubst') u u' Env lEnv =
                  F_Related_ovalues (open_tt_rec 0 T' T2') rsubst dsubst dsubst' u u' Env lEnv).
         simpl. reflexivity.
      rewrite <- H0.
      apply oparametricity_subst_value with
                (E:=E') (E':=@nil (atom*binding))
                (rsubst:=rsubst) (rsubst':=rho_nil)
                (k:=0) (Env:=Env) (lEnv:=lEnv)
                (t:=T2') (t2:=T') (K:=kn_lin) (Q:=K)
                (X:=y) (R:=(F_FORel T' (rho_nil++rsubst) (delta_nil++dsubst) (delta_nil++dsubst') Env))
                ; auto.
        SSCase "wft".
          simpl_env. unfold open_tt in w. apply w; auto.

        SSCase "wft".
          simpl_env. rewrite subst_tt_intro_rec with (X:=y); auto.
          rewrite_env (map (subst_tb y T') nil ++ E').
          eapply wf_typ_subst_tb with (Q:=K); auto.
          apply w; auto.

        SSCase "Rel__R".
        unfold F_FORel__R. split; auto.

        SSCase "fv".
        eapply m_tapp_ofv with (dsubst:=dsubst) (dsubst':=dsubst') (v:=v) (v':=v'); 
           eauto using notin_fv_te_typing.

        SSCase "eq".
        apply dom_delta_osubst with (Env:=Env); auto.
        apply dom_delta_osubst with (Env:=Env); auto.
        apply dom_rho_subst; auto.

        SSCase "typing".
        simpl_env. simpl.
        apply preservation_normalization with (e:=(exp_tapp (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (plug C1 e))))
                                                            (apply_delta_subst_typ dsubst (apply_gamma_subst_typ gsubst (apply_gamma_subst_typ lgsubst T'))))); auto.
          rewrite swap_subst_tt_odsubst with (E:=E')(Env:=Env)(K:=K); auto.
          rewrite subst_tt_open_tt_rec; eauto using type_from_wf_typ.
            rewrite <- subst_tt_fresh with (T:=T2'); auto.
            simpl. destruct (y == y); subst; try solve [contradict n; auto].
              rewrite commut_delta_osubst_open_tt_rec with (dE:=E')(Env:=Env); auto.
              apply typing_tapp with (K:=K); eauto using wft_osubst.
                simpl_commut_subst in Ht. auto.

          apply m_ocongr_tapp with(E:=E')(lE:=D')(Env:=Env)(lEnv:=lEnv)(v:=v)(K:=K); auto.

        SSCase "typing".
        simpl_env. simpl.
        apply preservation_normalization with (e:=(exp_tapp (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (plug C1 e'))))
                                                            (apply_delta_subst_typ dsubst' (apply_gamma_subst_typ gsubst' (apply_gamma_subst_typ lgsubst' T'))))); auto.
          rewrite swap_subst_tt_odsubst with (E:=E')(Env:=Env)(K:=K); auto.
          rewrite subst_tt_open_tt_rec; eauto using type_from_wf_typ.
            rewrite <- subst_tt_fresh with (T:=T2'); auto.
            simpl. destruct (y == y); subst; try solve [contradict n; auto].
              rewrite commut_delta_osubst_open_tt_rec with (dE:=E')(Env:=Env); auto.
              apply typing_tapp with (K:=K); eauto using wft_osubst.
                simpl_commut_subst in Ht'. auto.

          apply m_ocongr_tapp with(E:=E')(lE:=D')(Env:=Env)(lEnv:=lEnv)(v:=v')(K:=K); auto.

        SSCase "rsubst".
        eapply rsubst_weaken with (X:=y) (rsubst:=rsubst) (rsubst':=rho_nil); eauto.
          apply dom_rho_subst; auto.
        SSCase "dsubst".   
        apply odsubst_weaken with (X:=y) (K:=K) (dsubst:=dsubst) (dsubst':=delta_nil) (t:=(apply_delta_subst_typ dsubst T')); auto.
          apply wft_osubst_closed with (E:=E') (E':=@nil (atom*binding)) (dsubst:=dsubst) (Env:=Env) ; auto.
          apply dom_delta_osubst in Hwfd; auto.
        SSCase "dsubst'".
        apply odsubst_weaken with (X:=y) (K:=K) (dsubst:=dsubst') (dsubst':=delta_nil) (t:=(apply_delta_subst_typ dsubst' T')); auto.
          apply wft_osubst_closed with (E:=E') (E':=@nil (atom*binding)) (dsubst:=dsubst') (Env:=Env); auto.
          apply dom_delta_osubst in Hwfd'; auto.
Qed.

Lemma F_ological_related_congruence : forall E lE e e' t C E' lE' t',
  F_ological_related E lE e e' t ->
  contexting E lE t C E' lE' t' ->
  F_ological_related E' lE' (plug C e) (plug C e') t'.
Proof.
  intros E lE e e' t C E' lE' t' Hlr Hcontexting.
  destruct Hlr as [Htyp [Htyp' [L0 Hlr]]]. 
  split. apply contexting_plug_typing with (e:=e) in Hcontexting; auto.
  split. apply contexting_plug_typing with (e:=e') in Hcontexting; auto.
  exists (L0 `union` 
                 cv_ec C `union` fv_ec C `union` 
                 dom E `union` dom lE `union` 
                 fv_tt t `union`  fv_tt t' `union` 
                dom E' `union` dom lE').
  (contexting_cases (induction Hcontexting) Case); 
    intros dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv Disj00 Disj01 Hrel_sub HRsub; simpl in *; auto.
  Case "contexting_hole".
    remember (L0 `union` 
                 {} `union` {} `union` 
                 dom E `union` dom D `union` 
                 fv_tt T `union`  fv_tt T `union` 
                dom E `union` dom D) as L1.
    apply Hlr; auto.
      apply disjdom_sym_1.
      apply disjdom_sub with (D1:=L1); subst.
        apply disjdom_sym_1; auto.
        clear. fsetdec.

      apply disjdom_sym_1.
      apply disjdom_sub with (D1:=L1); subst.
        apply disjdom_sym_1; auto.
        clear. fsetdec.

  Case "contexting_abs_free".
    apply F_ological_related_congruence__abs_free with 
     (e:=e) (e':=e') (E:=E) (D:=D) (T:=T) (L0:=L0) (L:=L) (K:=K) (T1':=T1') (C1:=C1) (T2':=T2') (E':=E') (D':=D') 
     (dsubst:=dsubst) (dsubst':=dsubst') (gsubst:=gsubst) (gsubst':=gsubst') (lgsubst:=lgsubst) (lgsubst':=lgsubst') (rsubst:=rsubst) (Env:=Env) (lEnv:=lEnv); assumption.

  Case "contexting_labs_free". 
    apply F_ological_related_congruence__labs_free with 
     (e:=e) (e':=e') (E:=E) (D:=D) (T:=T) (L0:=L0) (L:=L) (K:=K) (T1':=T1') (C1:=C1) (T2':=T2') (E':=E') (D':=D') 
     (dsubst:=dsubst) (dsubst':=dsubst') (gsubst:=gsubst) (gsubst':=gsubst') (lgsubst:=lgsubst) (lgsubst':=lgsubst') (rsubst:=rsubst) (Env:=Env) (lEnv:=lEnv); assumption.

  Case "contexting_abs_capture".
    apply F_ological_related_congruence__abs_capture with 
     (e:=e) (e':=e') (E:=E) (D:=D) (T:=T) (L0:=L0) (K:=K) (y:=y) (T1':=T1') (C1:=C1) (T2':=T2') (E':=E') (D':=D') 
     (dsubst:=dsubst) (dsubst':=dsubst') (gsubst:=gsubst) (gsubst':=gsubst') (lgsubst:=lgsubst) (lgsubst':=lgsubst') (rsubst:=rsubst) (Env:=Env) (lEnv:=lEnv); assumption.

  Case "contexting_labs_capture".
    apply F_ological_related_congruence__labs_capture with 
     (e:=e) (e':=e') (E:=E) (D:=D) (T:=T) (L0:=L0) (K:=K) (y:=y) (T1':=T1') (C1:=C1) (T2':=T2') (E':=E') (D':=D') 
     (dsubst:=dsubst) (dsubst':=dsubst') (gsubst:=gsubst) (gsubst':=gsubst') (lgsubst:=lgsubst) (lgsubst':=lgsubst') (rsubst:=rsubst) (Env:=Env) (lEnv:=lEnv); assumption.

  Case "contexting_app1". 
    apply F_ological_related_congruence__app1 with 
     (e:=e) (e':=e') (E:=E) (D:=D) (T:=T) (L0:=L0) (K:=K) (T1':=T1') (C1:=C1) (T2':=T2') (E':=E') (D1':=D1')  (D2':=D2')  (D3':=D3') 
     (dsubst:=dsubst) (dsubst':=dsubst') (gsubst:=gsubst) (gsubst':=gsubst') (lgsubst:=lgsubst) (lgsubst':=lgsubst') (rsubst:=rsubst) (Env:=Env) (lEnv:=lEnv); assumption.

  Case "contexting_app2". 
    apply F_ological_related_congruence__app2 with 
     (e:=e) (e':=e') (E:=E) (D:=D) (T:=T) (L0:=L0) (K:=K) (T1':=T1') (C2:=C2) (T2':=T2') (E':=E') (D1':=D1')  (D2':=D2')  (D3':=D3') 
     (dsubst:=dsubst) (dsubst':=dsubst') (gsubst:=gsubst) (gsubst':=gsubst') (lgsubst:=lgsubst) (lgsubst':=lgsubst') (rsubst:=rsubst) (Env:=Env) (lEnv:=lEnv); assumption.

   Case "contexting_tabs_free".
    apply F_ological_related_congruence__tabs_free with 
     (e:=e) (e':=e') (E:=E) (D:=D) (T:=T) (L0:=L0) (K:=K) (L:=L) (T1':=T1') (C1:=C1) (E':=E') (D':=D')
     (dsubst:=dsubst) (dsubst':=dsubst') (gsubst:=gsubst) (gsubst':=gsubst') (lgsubst:=lgsubst) (lgsubst':=lgsubst') (rsubst:=rsubst) (Env:=Env) (lEnv:=lEnv); assumption.

   Case "contexting_tabs_capture".
    apply F_ological_related_congruence__tabs_capture with 
     (e:=e) (e':=e') (E:=E) (D:=D) (T:=T) (L0:=L0) (K:=K) (T1':=T1') (C1:=C1) (E':=E') (D':=D')
     (dsubst:=dsubst) (dsubst':=dsubst') (gsubst:=gsubst) (gsubst':=gsubst') (lgsubst:=lgsubst) (lgsubst':=lgsubst') (rsubst:=rsubst) (Env:=Env) (lEnv:=lEnv); assumption.

   Case "contexting_tapp".
    apply F_ological_related_congruence__tapp with 
     (e:=e) (e':=e') (E:=E) (D:=D) (T:=T) (L0:=L0) (K:=K) (T':=T') (C1:=C1) (E':=E') (D':=D')
     (dsubst:=dsubst) (dsubst':=dsubst') (gsubst:=gsubst) (gsubst':=gsubst') (lgsubst:=lgsubst) (lgsubst':=lgsubst') (rsubst:=rsubst) (Env:=Env) (lEnv:=lEnv); assumption.

    Case "contexting_apair1".
    assert (J:=Hrel_sub). apply F_Related_osubst__inversion in J. decompose [prod] J. clear J.

    assert (
      F_Related_oterms T1' rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (plug C1 e))))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (plug C1 e'))))
         Env lEnv
     ) as FR_T1.
     apply IHHcontexting; auto.
      clear - Disj00.
      apply disjdom_sym_1.
      apply disjdom_sub with (D1:=L0 `union` cv_ec C1 `union` (fv_ec C1 `union` fv_ee e2) `union` dom E `union` dom D `union` fv_tt T  `union` (fv_tt T1' `union` fv_tt T2') `union` dom E' `union` dom D').
        apply disjdom_sym_1; auto.
        clear Disj00. fsetdec.        

      clear - Disj01.
      apply disjdom_sym_1.
      apply disjdom_sub with (D1:=L0 `union` cv_ec C1 `union` (fv_ec C1 `union` fv_ee e2) `union` dom E `union` dom D `union` fv_tt T  `union` (fv_tt T1' `union` fv_tt T2') `union` dom E' `union` dom D').
        apply disjdom_sym_1; auto.
        clear Disj01. fsetdec.        
    destruct FR_T1 as [v [v' [Ht1 [Ht1' [Hn1 [Hn1' Hrel1]]]]]].

    clear Disj00 Disj01.

    assert (
      F_Related_oterms T2' rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e2)))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e2)))
         Env lEnv
     ) as FR_T2.
       apply oparametricity with (E:=E') (lE:=D'); auto.
    destruct FR_T2 as [v0 [v'0 [Ht2 [Ht2' [Hn2 [Hn2' Hrel2]]]]]].

    exists (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_apair (plug C1 e)  e2)))).
    exists (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_apair (plug C1 e') e2)))).
    split; simpl_commut_subst; auto.
    split; simpl_commut_subst; auto.
    split. split; simpl_commut_subst; auto.
    split. split; simpl_commut_subst; auto.
      SCase "Frel".
        SSCase "Frel".
        apply F_Related_ovalues_with_req.
        repeat (split; simpl_commut_subst; auto).
        exists (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (plug C1 e)))).
        exists (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e2))).
        exists (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (plug C1 e')))).
        exists (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e2))).
        repeat(split; auto).
          exists (v). exists (v'). split; auto.
          exists (v0). exists (v'0). split; auto.

    Case "contexting_apair2".
    assert (J:=Hrel_sub). apply F_Related_osubst__inversion in J. decompose [prod] J. clear J.

    assert (
      F_Related_oterms T1' rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e1)))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e1)))
         Env lEnv
     ) as FR_T1.
       apply oparametricity with (E:=E') (lE:=D'); auto.
    destruct FR_T1 as [v [v' [Ht1 [Ht1' [Hn1 [Hn1' Hrel1]]]]]].

    assert (
      F_Related_oterms T2' rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (plug C2 e))))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (plug C2 e'))))
         Env lEnv
     ) as FR_T2.
     apply IHHcontexting; auto.
      clear - Disj00.
      apply disjdom_sym_1.
      apply disjdom_sub with (D1:=L0 `union` cv_ec C2 `union` (fv_ee e1 `union` fv_ec C2) `union` dom E `union` dom D `union` fv_tt T  `union` (fv_tt T1' `union` fv_tt T2') `union` dom E' `union` dom D').
        apply disjdom_sym_1; auto.
        clear Disj00. fsetdec.        

      clear - Disj01.
      apply disjdom_sym_1.
      apply disjdom_sub with (D1:=L0 `union` cv_ec C2 `union` (fv_ee e1 `union` fv_ec C2) `union` dom E `union` dom D `union` fv_tt T  `union` (fv_tt T1' `union` fv_tt T2') `union` dom E' `union` dom D').
        apply disjdom_sym_1; auto.
        clear Disj01. fsetdec.        
    destruct FR_T2 as [v0 [v'0 [Ht2 [Ht2' [Hn2 [Hn2' Hrel2]]]]]].

    clear Disj00 Disj01.

    exists (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_apair e1 (plug C2 e))))).
    exists (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_apair e1 (plug C2 e'))))).
    split; simpl_commut_subst; auto.
    split; simpl_commut_subst; auto.
    split. split; simpl_commut_subst; auto.
    split. split; simpl_commut_subst; auto.
      SCase "Frel".
        SSCase "Frel".
        apply F_Related_ovalues_with_req.
        repeat (split; simpl_commut_subst; auto).
        exists (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e1))).
        exists (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (plug C2 e)))).
        exists (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e1))).
        exists (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (plug C2 e')))).
        repeat(split; auto).
          exists (v). exists (v'). split; auto.
          exists (v0). exists (v'0). split; auto.

    Case "contexting_fst".
    assert (J:=Hrel_sub). apply F_Related_osubst__inversion in J.
    destruct J as [[[[[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe] Hwfe'] HwfEnv] HwflEnv].
    assert (wf_typ E' (typ_with T1' T2') kn_lin) as WFTwith.
      apply contexting_regular in Hcontexting.
      decompose [and] Hcontexting; auto.
    assert (
      F_Related_oterms (typ_with T1' T2') rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (plug C1 e))))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (plug C1 e'))))
         Env lEnv
     ) as FR_With.
      apply IHHcontexting; auto.
       clear - Disj00 WFTwith.
       apply disjdom_sym_1.
       apply disjdom_sub with (D1:=L0 `union` cv_ec C1 `union` fv_ec C1 `union` dom E `union` dom D `union` fv_tt T  `union` fv_tt T1' `union` dom E' `union` dom D').
         apply disjdom_sym_1; auto.

         apply wft_fv_tt_sub in WFTwith.
         clear Disj00. simpl in WFTwith. fsetdec.        

       clear - Disj01 WFTwith.
       apply disjdom_sym_1.
       apply disjdom_sub with (D1:=L0 `union` cv_ec C1 `union` fv_ec C1 `union` dom E `union` dom D `union` fv_tt T  `union` fv_tt T1' `union` dom E' `union` dom D').
         apply disjdom_sym_1; auto.

         apply wft_fv_tt_sub in WFTwith.
         clear Disj01. simpl in WFTwith. fsetdec.        
    destruct FR_With as [ee1 [ee1' [Ht [Ht' [Hn [Hn' FR_With]]]]]].

    clear Disj00 Disj01.

    simpl_commut_subst in Ht. simpl_commut_subst in Ht'. 
    apply congr_fst with (T1:=apply_delta_subst_typ dsubst T1') (T2:=apply_delta_subst_typ dsubst T2') (Env:=Env) (lEnv:=lEnv) in Hn; auto.
    apply congr_fst with (T1:=apply_delta_subst_typ dsubst' T1') (T2:=apply_delta_subst_typ dsubst' T2') (Env:=Env) (lEnv:=lEnv) in Hn'; auto.
    destruct Hn as [e1 [e2 [Hbrc Heq]]].
    destruct Hn' as [e1' [e2' [Hbrc' Heq']]].
    apply F_Related_ovalues_with_leq in FR_With.
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
    assert (J:=Hrel_sub). apply F_Related_osubst__inversion in J.
    destruct J as [[[[[[[[Hwfd Hwfd'] Hwflg] Hwflg'] Hwfr] Hwfe] Hwfe'] HwfEnv] HwflEnv].
    assert (wf_typ E' (typ_with T1' T2') kn_lin) as WFTwith.
      apply contexting_regular in Hcontexting.
      decompose [and] Hcontexting; auto.
    assert (
      F_Related_oterms (typ_with T1' T2') rsubst dsubst dsubst'
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (plug C1 e))))
         (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (plug C1 e'))))
         Env lEnv
     ) as FR_With.
      apply IHHcontexting; auto.
       clear - Disj00 WFTwith.
       apply disjdom_sym_1.
       apply disjdom_sub with (D1:=L0 `union` cv_ec C1 `union` fv_ec C1 `union` dom E `union` dom D `union` fv_tt T  `union` fv_tt T2' `union` dom E' `union` dom D').
         apply disjdom_sym_1; auto.

         apply wft_fv_tt_sub in WFTwith.
         clear Disj00. simpl in WFTwith. fsetdec.        

       clear - Disj01 WFTwith.
       apply disjdom_sym_1.
       apply disjdom_sub with (D1:=L0 `union` cv_ec C1 `union` fv_ec C1 `union` dom E `union` dom D `union` fv_tt T  `union` fv_tt T2' `union` dom E' `union` dom D').
         apply disjdom_sym_1; auto.

         apply wft_fv_tt_sub in WFTwith.
         clear Disj01. simpl in WFTwith. fsetdec.        
    destruct FR_With as [ee2 [ee2' [Ht [Ht' [Hn [Hn' FR_With]]]]]].

    clear Disj00 Disj01.

    simpl_commut_subst in Ht. simpl_commut_subst in Ht'. 
    apply congr_snd with (T1:=apply_delta_subst_typ dsubst T1') (T2:=apply_delta_subst_typ dsubst T2') (Env:=Env) (lEnv:=lEnv) in Hn; auto.
    apply congr_snd with (T1:=apply_delta_subst_typ dsubst' T1') (T2:=apply_delta_subst_typ dsubst' T2') (Env:=Env) (lEnv:=lEnv) in Hn'; auto.
    destruct Hn as [e1 [e2 [Hbrc Heq]]].
    destruct Hn' as [e1' [e2' [Hbrc' Heq']]].
    apply F_Related_ovalues_with_leq in FR_With.
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

Axiom F_Related_ovalues__consistent : forall v v',
  F_Related_ovalues Two nil nil nil v v' nil nil->
  ((v = tt /\ v' =tt) \/ (v = ff /\ v' =ff)).

Lemma F_ological_related__sound : forall E lE e e' t,
  F_ological_related E lE e e' t ->
  F_observational_eq E lE e e' t.
Proof.
  intros E lE e e' t Hlr.
  assert (J:=Hlr).
  destruct J as [Htyp [Htyp' [L J]]].
  split; auto.
  split; auto.
    intros C Hcontext.
    apply F_ological_related_congruence with (C:=C) (E':=nil) (lE':=nil) (t':=Two) in Hlr; auto.
    split. eapply contexting_plug_typing; eauto.
    split. eapply contexting_plug_typing; eauto.
      assert (F_Rosubst nil nil nil nil nil) as J1. auto.
      assert (F_Related_osubst nil nil nil nil nil nil nil nil nil nil nil) as J2. auto.
      destruct Hlr as [Htyp1 [Htyp1' [L' Hlr]]].
      assert (disjdom L' (dom (@nil (atom*binding)))) as Disj1.
        simpl. apply disjdom_sym_1. apply disjdom_nil_1.
      assert (disjdom L' (dom (@nil (atom*lbinding)))) as Disj2.
        simpl. apply disjdom_sym_1. apply disjdom_nil_1.
      assert (Hrel:=@Hlr nil nil nil nil nil nil nil nil nil Disj1 Disj2 J2 J1).
      destruct Hrel as [v [v' [Htypv [Htypv' [Hn [Hn' Hrel]]]]]].
      simpl in *.
      assert (JJ:=@F_Related_ovalues__consistent v v' Hrel).
      destruct JJ as [[EQ EQ'] | [EQ EQ']]; subst; auto.
Qed.
