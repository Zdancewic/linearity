(** Authors: Jianzhou Zhao. *)

Require Import Bang_Parametricity.
Require Import Bang_OParametricity_App.
Require Import Bang_ContextualEq_Def.
Require Import Bang_ContextualEq_Infrastructure.
Require Import Bang_ContextualEq_Sound.

Export Parametricity.

Lemma exists_wf_delta_subst : forall E,
  wf_env E ->
  exists dsubst, wf_delta_subst E dsubst.
Proof.
  intros E Wfe.
  induction Wfe.
    exists nil. auto.

    destruct IHWfe as [dsubst EQ].
    exists ([(X, typ_all 0)]++dsubst).
    apply wf_delta_subst_styp; auto.
      apply wf_typ_all with {}; auto.
        intros X0 X0n.
        unfold open_tt. simpl. 
        apply wf_typ_var; auto.

    destruct IHWfe as [dsubst EQ].
    exists dsubst.
    apply wf_delta_subst_skip; auto.
Qed.   

Lemma exists_wf_delta_subst' : forall E E' dsubst,
  wf_delta_subst E dsubst ->
  wf_env (E'++E) ->
  exists dsubst', wf_delta_subst (E'++E) (dsubst'++dsubst).
Proof.
  intros E E' dsubst Wfd Wfe.
  remember (E'++E) as EE.
  generalize dependent E'.
  induction Wfe; intros; subst.
    symmetry in HeqEE.
    apply app_eq_nil in HeqEE.
    destruct HeqEE; subst.
    inversion Wfd; subst.
    exists nil. auto.

    apply one_eq_app in HeqEE. 
    destruct HeqEE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
      destruct IHWfe with (E':=E0') as [dsubst' EQ]; auto.
      exists ([(X, typ_all 0)]++dsubst'). simpl_env.
      apply wf_delta_subst_styp; auto.
        apply wf_typ_all with {}; auto.
          intros X0 X0n.
          unfold open_tt. simpl. 
          apply wf_typ_var; auto.

      exists nil. simpl_env. auto.

    apply one_eq_app in HeqEE. 
    destruct HeqEE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
      destruct IHWfe with (E':=E0') as [dsubst' EQ]; auto.
      exists dsubst'.
      apply wf_delta_subst_skip; auto.

      exists nil. auto.
Qed.   

Lemma wf_delta_subst__remove_gdom : forall E dsubst,
  wf_delta_subst E dsubst ->
  wf_delta_subst (remove_gdom E) dsubst.
Proof.
  intros E dsubst Wfd.
  induction Wfd; simpl; auto.
    simpl_env.
    apply wf_delta_subst_styp; auto. 
      apply remove_gdom_sub; auto.
Qed.

Lemma F_observational_eq__refl : forall E lE e t,
  typing E lE e t ->
  F_observational_eq E lE e e t.
Proof.
  intros E lE e t Typ.
  apply F_logical_related__sound; auto.
  split; auto.
  split; auto.
  intros dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst H_relsubst H_Rsubst.
  apply parametricity with (E:=E) (lE:=lE); auto.
Qed.

Lemma Kleene_eq__sym  : forall e e',
  Kleene_eq  e e' ->
  Kleene_eq  e' e.
Proof.
  intros e e' Hkleene.
  destruct Hkleene as [Typ [Typ' Hkleene]].
  split; auto.
  split; auto.
    destruct Hkleene as [[H1 H2] | [H1 H2]]; auto.
Qed.

Lemma F_observational_eq__sym : forall E lE e e' t,
  F_observational_eq E lE e e' t ->
  F_observational_eq E lE e' e t.
Proof.
  intros E lE e e' t Hobservation.
  destruct Hobservation as [Typ [Typ' Hkleene]].
  split; auto.
  split; auto.
    intros C Hcontexting.
    apply Kleene_eq__sym; auto.
Qed.

Lemma Kleene_eq__trans  : forall e e' e'',
  Kleene_eq  e e' ->
  Kleene_eq  e' e'' ->
  Kleene_eq  e e''.
Proof.
  intros e e' e'' Hkleene Hkleene'.
  destruct Hkleene as [Typ [Typ' Hkleene]].
  destruct Hkleene' as [_ [Typ'' Hkleene']].
  split; auto.
  split; auto.
    destruct Hkleene as [[H1 H2] | [H1 H2]].
      destruct Hkleene' as [[H2' H3] | [H2' H3]]; auto.
        assert (tt = ff) as EQ.
          apply unique_normal_form with (u:=e'); auto.
        inversion EQ.
      destruct Hkleene' as [[H2' H3] | [H2' H3]]; auto.
        assert (tt = ff) as EQ.
          apply unique_normal_form with (u:=e'); auto.
        inversion EQ.
Qed.

Lemma F_observational_eq__trans : forall E lE e e' e'' t,
  F_observational_eq E lE e e' t ->
  F_observational_eq E lE e' e'' t ->
  F_observational_eq E lE e e'' t.
Proof.
  intros E lE e e' e'' t Hobservation Hobservation'.
  destruct Hobservation as [Typ [Typ' Hkleene]].
  destruct Hobservation' as [_ [Typ'' Hkleene']].
  split; auto.
  split; auto.
    intros C Hcontexting.
    apply Kleene_eq__trans with (e':=plug C e'); auto.
Qed.

Lemma red_preserved_under_delta_subst: forall E dsubst e e',
   wf_delta_subst E dsubst ->
   red e e' ->
   red (apply_delta_subst dsubst e) (apply_delta_subst dsubst e').
Proof.
  intros E dsubst e e' Wfd Red.
  (red_cases (induction Red) Case); simpl_commut_subst; auto.
  Case "red_app". 
    apply red_app; auto.
      eapply expr_preserved_under_delta_subst; eauto.
   Case "red_tapp".
    apply red_tapp; auto.
      eapply type_preserved_under_delta_subst; eauto.
  Case "red_abs".
    rewrite <- commut_delta_subst_abs.
    eapply red_abs_preserved_under_delta_subst; eauto.
  Case "red_tabs".
    rewrite <- commut_delta_subst_tabs.
    eapply red_tabs_preserved_under_delta_subst; eauto.
  Case "red_let_cong". 
    apply red_let_cong; auto.
      rewrite <- commut_delta_subst_let.
      eapply expr_preserved_under_delta_subst; eauto.
  Case "red_let_beta". 
    rewrite <- commut_delta_subst_ebang.
    eapply red_bang_preserved_under_delta_subst; eauto.
  Case "red_fst_beta". 
    apply red_fst_beta; eauto using expr_preserved_under_delta_subst.
  Case "red_snd_beta". 
    apply red_snd_beta; eauto using expr_preserved_under_delta_subst.
Qed.

Lemma red_preserved_under_gamma_subst: forall E D dsubst gsubst lgsubst e e',
   wf_lgamma_subst E D dsubst gsubst lgsubst ->
   red e e' ->
   red (apply_gamma_subst gsubst e) (apply_gamma_subst gsubst e').
Proof.
  intros E D dsubst gsubst lgsubst e e' Wflg Red.
  (red_cases (induction Red) Case); simpl_commut_subst; auto.
  Case "red_app". 
    apply red_app; auto.
      eapply expr_preserved_under_gamma_subst; eauto.
  Case "red_abs".
    rewrite <- commut_gamma_subst_abs.
    eapply red_abs_preserved_under_gamma_subst; eauto.
  Case "red_tabs".
    rewrite <- commut_gamma_subst_tabs.
    eapply red_tabs_preserved_under_gamma_subst; eauto.
  Case "red_let_cong". 
    apply red_let_cong; auto.
      rewrite <- commut_gamma_subst_let.
      eapply expr_preserved_under_gamma_subst; eauto.
  Case "red_let_beta". 
    rewrite <- commut_gamma_subst_bang.
    eapply red_bang_preserved_under_gamma_subst; eauto.
  Case "red_fst_beta". 
    apply red_fst_beta; eauto using expr_preserved_under_gamma_subst.
  Case "red_snd_beta". 
    apply red_snd_beta; eauto using expr_preserved_under_gamma_subst.
Qed.

Lemma red_preserved_under_lgamma_subst: forall E D dsubst gsubst lgsubst e e',
   wf_lgamma_subst E D dsubst gsubst lgsubst ->
   red e e' ->
   red (apply_gamma_subst lgsubst e) (apply_gamma_subst lgsubst e').
Proof.
  intros E D dsubst gsubst lgsubst e e' Wflg Red.
  (red_cases (induction Red) Case); simpl_commut_subst; auto.
  Case "red_app". 
    apply red_app; auto.
      eapply expr_preserved_under_lgamma_subst; eauto.
  Case "red_abs".
    rewrite <- commut_gamma_subst_abs.
    eapply red_abs_preserved_under_lgamma_subst; eauto.
  Case "red_tabs".
    rewrite <- commut_gamma_subst_tabs.
    eapply red_tabs_preserved_under_lgamma_subst; eauto.
  Case "red_let_cong". 
    apply red_let_cong; auto.
      rewrite <- commut_gamma_subst_let.
      eapply expr_preserved_under_lgamma_subst; eauto.
  Case "red_let_beta". 
    rewrite <- commut_gamma_subst_bang.
    eapply red_bang_preserved_under_lgamma_subst; eauto.
  Case "red_fst_beta". 
    apply red_fst_beta; eauto using expr_preserved_under_lgamma_subst.
  Case "red_snd_beta". 
    apply red_snd_beta; eauto using expr_preserved_under_lgamma_subst.
Qed.

Lemma red_preserved_under_subst: forall E D dsubst gsubst lgsubst e e',
   wf_lgamma_subst E D dsubst gsubst lgsubst ->
   red e e' ->
   red (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
           (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e'))).
Proof.
  intros E D dsubst gsubst lgsubst e e' Wflg Red.
  eapply red_preserved_under_delta_subst; eauto.
    apply wf_lgamma_subst__wf_subst in Wflg.
    destruct Wflg; eauto.
    eapply red_preserved_under_gamma_subst; eauto.
    eapply red_preserved_under_lgamma_subst; eauto.
Qed.

Lemma confluent_normalization: forall u u' u'' t,
  typing nil nil u t ->
  bigstep_red u u' -> 
  bigstep_red u u'' -> 
  exists v, 
    normalize u' v /\
    normalize u'' v.
Proof.
  intros u u' u'' t Typ Mred Mred'.
  generalize dependent u''.
  generalize dependent t.
  induction Mred; intros.
    assert (J:=Typ).
    apply strong_normalization in J.
    destruct J as [v Norm].
    exists v.
    split; auto.
      apply preservation_bigstep_red with (e':=u'') in Typ; auto.
      apply strong_normalization in Typ.
      destruct Typ as [v' Norm'].
      assert (v = v') as EQ.
        apply unique_normal_form with (u:=e); auto.
          destruct Norm' as [H1 H2].
          split; auto.
            apply bigstep_red__trans with (e':=u''); auto.
      subst. auto.

    assert (J:=Typ).
    apply preservation with (e':=e') in J; auto.
    apply IHMred with (u'':=e'') in J; auto.
    destruct J as [v [H1 H2]].
    exists v.
    split; auto.
      apply preservation_bigstep_red with (e':=u'') in Typ; auto.
      apply strong_normalization in Typ.
      destruct Typ as [v' Norm'].
      assert (v = v') as EQ.
        apply unique_normal_form with (u:=e); auto.
          destruct H1 as [J1 J2].
          split; auto.
            apply bigstep_red__trans with (e':=e''); auto.
              apply bigstep_red__trans with (e':=e'); auto.
                apply bigstep_red_trans with (e':=e'); auto.

          destruct Norm' as [J1 J2].
          split; auto.
            apply bigstep_red__trans with (e':=u''); auto.
      subst. auto.
Qed.

Lemma bigstep_red_normalization: forall u u' v t,
  typing nil nil u t ->
  normalize u v ->
  bigstep_red u u' ->
  normalize u' v.
Proof.
  intros u u' v t Typ Norm Red.
  assert (J:=Norm).
  destruct J as [H1 H2].
  split; auto.
    assert(exists v0, normalize u' v0 /\ normalize v v0) as J.
      apply confluent_normalization with (u:=u) (t:=t); auto.
    destruct J as [v0 [Norm1 Norm2]].
    apply red_value__eq_value in Norm2; auto.
    subst.
    destruct Norm1; auto.
Qed.    

Lemma red_normalization: forall u u' v t,
  typing nil nil u t ->
  normalize u v ->
  red u u' ->
  normalize u' v.
Proof.
  intros u u' v t Typ Norm Red.
  apply bigstep_red_normalization with (t:=t) (u:=u); auto.
    apply bigstep_red_trans with (e':=u'); auto.
Qed.    

Lemma F_observational_eq__beta : forall E lE e e' t,
  typing E lE e t ->
  red e e' ->
  F_observational_eq E lE e e' t.
Proof.
  intros E lE e e' t Typ Red.
  apply F_logical_related__sound; auto.
  split; auto.
  split. apply preservation with (e':=e') in Typ; auto.
    intros dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst H_relsubst H_Rsubst.
    apply parametricity with (dsubst:=dsubst) (dsubst':=dsubst')  
                                                         (gsubst:=gsubst) (gsubst':=gsubst')
                                                         (lgsubst:=lgsubst) (lgsubst':=lgsubst') (rsubst:=rsubst) in Typ; auto.
    destruct Typ as [v [v' [Typ [Typ' [Hn [Hn' Hrel ]]]]]].
    exists v. exists v'.
    split; auto.
    split. apply preservation with (e':=apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e'))) in Typ'; auto.
      apply red_preserved_under_subst with (E:=E) (D:=lE); auto.
        apply F_related_subst__inversion in H_relsubst.
        decompose [prod] H_relsubst; auto.
    split; auto.
    split; auto.
      apply red_normalization with (u:=apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e)))
                                                                     (t:=apply_delta_subst_typ dsubst' t); auto.
        apply red_preserved_under_subst with (E:=E) (D:=lE); auto.
          apply F_related_subst__inversion in H_relsubst.
          decompose [prod] H_relsubst; auto.
Qed.

Lemma F_observational_eq__mbeta : forall E lE e e' t,
  typing E lE e t ->
  bigstep_red e e' ->
  F_observational_eq E lE e e' t.
Proof.
  intros E lE e e' t Typ Red.
  induction Red.
    apply F_observational_eq__refl; auto.
    apply F_observational_eq__trans with (e':=e').
      apply F_observational_eq__beta; auto.
      apply IHRed.
        apply preservation with (e':=e') in Typ; auto.
Qed.

Lemma typing_eta_abs : forall E e t1 t2,
  typing E nil e (typ_arrow t1 t2) ->
  typing E nil (exp_abs t1 (exp_app e 0)) (typ_arrow t1 t2).
Proof.
  intros E e t1 t2 Typ.
  assert (J:=Typ).
  apply typing_regular in J.
  destruct J as [J1 [J2 [J3 J4]]].
  apply wft_arrow_inv in J4.
  destruct J4 as [J4 J5].
  apply typing_abs with (L:=dom E); auto.
    intros x xn.
    unfold open_ee. simpl. simpl_env.
    apply typing_app with (T1:=t1) (D1:=nil) (D2:=[(x, lbind_typ t1)]); auto.
      rewrite <- open_ee_rec_expr; auto.
     apply typing_lvar; auto.
       rewrite_env ([(x, lbind_typ t1)]++nil).
       apply wf_lenv_typ; auto.
    rewrite_env ([(x, lbind_typ t1)]++nil).
    apply lenv_split_right; auto.
Qed.

Lemma bigstep_red_app : forall e1 e1' e2,
  bigstep_red e1 e1' ->
  expr e2 ->
  bigstep_red (exp_app e1 e2) (exp_app e1' e2).
Proof.
  intros e1 e1' e2 Hrel Expr.
  induction Hrel; auto.
    apply bigstep_red_trans with (e':=exp_app e' e2); auto.
Qed.    

Lemma F_observational_eq__eta_abs : forall E e t1 t2,
  typing E nil e (typ_arrow t1 t2) ->
  F_observational_eq E nil e (exp_abs t1 (exp_app e 0)) (typ_arrow t1 t2).
Proof.
  intros E e t1 t2 Typ.
  apply F_logical_related__sound; auto.
  assert (typing E nil (exp_abs t1 (exp_app e 0)) (typ_arrow t1 t2)) as Typ'.
    apply typing_eta_abs; auto.
  split; auto.
  split; auto.
    intros dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst H_relsubst H_Rsubst.
    assert (J:=Typ).
    apply parametricity with (dsubst:=dsubst) (dsubst':=dsubst')  
                                                         (gsubst:=gsubst) (gsubst':=gsubst')
                                                         (lgsubst:=lgsubst) (lgsubst':=lgsubst') (rsubst:=rsubst) in J; auto.
    destruct J as [v [v' [Typing [Typing' [Hn [Hn' Hrel ]]]]]].
    exists v. exists (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_abs t1 (exp_app e 0))))).
    split; auto.
    split.
      apply typing_subst with (E:=E) (D:=nil); auto.
        apply F_related_subst__inversion in H_relsubst.
        decompose [prod] H_relsubst; auto.
    split; auto.
    split. 
      split; auto.
        apply F_related_subst__inversion in H_relsubst.
        decompose [prod] H_relsubst.
        apply delta_gamma_lgamma_subst_value with (E:=E) (D:=nil); auto.

      apply F_related_values_arrow_leq in Hrel.
      destruct Hrel as [Hv [Hv' Hrel]].
      apply F_related_values_arrow_req.
      split; auto.
      split.
        apply F_related_subst__inversion in H_relsubst.
        decompose [prod] H_relsubst.
        apply delta_gamma_lgamma_subst_value with (E:=E) (D:=nil); auto.

      intros x x' Typingx Typingx' Hrelx.
      assert (J:=@Hrel x x' Typingx Typingx' Hrelx).
      destruct J as [u [u' [Hnu [Hnu' J]]]].
      exists u. exists u'.
      split; auto.
      split; auto.
        simpl_commut_subst.
        assert (disjdom (fv_ee 0) (dom lgsubst')) as Disj1.
           simpl. apply disjdom_nil_1.
        assert (disjdom (fv_ee 0) (dom gsubst')) as Disj2.
           simpl. apply disjdom_nil_1.
        assert (disjdom (fv_ee 0) (dom dsubst')) as Disj3.
           simpl. apply disjdom_nil_1.
        rewrite gamma_osubst_closed_exp with (e:=0); auto.
        rewrite gamma_osubst_closed_exp with (e:=0); auto.
        rewrite delta_osubst_closed_exp with (e:=0); auto.
        destruct Hnu' as [H1 H2].
        split; auto.
          apply bigstep_red__trans with (e':=exp_app v' x'); auto.
            apply bigstep_red_trans with (e':=exp_app  (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e))) x'); auto.
               assert (exp_app  (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e))) x' =
                              open_ee (exp_app  (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e))) 0) x') as EQ.
                 unfold open_ee.
                 simpl.
                 rewrite <- open_ee_rec_expr; auto.
              rewrite EQ.
              apply red_abs; auto.
                apply typing_subst with (E:=E) (D:=nil) (dsubst:=dsubst') (lgsubst:=lgsubst') (gsubst:=gsubst') in Typ'; auto.
                   simpl_commut_subst in Typ'.
                   rewrite gamma_osubst_closed_exp with (e:=0) in Typ'; auto.
                   rewrite gamma_osubst_closed_exp with (e:=0) in Typ'; auto.
                   rewrite delta_osubst_closed_exp with (e:=0) in Typ'; auto.

                  apply F_related_subst__inversion in H_relsubst.
                  decompose [prod] H_relsubst; auto.
          apply bigstep_red_app; auto.
            destruct Hn'; auto.
Qed.

Lemma typing_eta_bang : forall E e t,
  typing E nil e (typ_bang t) ->
  typing E nil (exp_let e (exp_bang 0)) (typ_bang t).
Proof.
  intros E e t Typ.
  assert (J:=Typ).
  apply typing_regular in J.
  destruct J as [J1 [J2 [J3 J4]]].
  apply wft_bang_inv in J4.
  apply typing_let with (L:=dom E) (D1:=lempty) (D2:=lempty) (T1:=t); auto.
    intros x xn.
    unfold open_ee. simpl. simpl_env.
    apply typing_bang; auto.
Qed.

Lemma apply_gamma_subst_bv: forall gsubst n,
  apply_gamma_subst gsubst (exp_bvar n) = (exp_bvar n).
Proof.
  induction gsubst; intros; simpl; auto.
  destruct a. auto.
Qed.

Lemma apply_delta_subst_bv: forall dsubst n,
  apply_delta_subst dsubst (exp_bvar n) = (exp_bvar n).
Proof.
  induction dsubst; intros; simpl; auto.
  destruct a. auto.
Qed.

Lemma F_observational_eq__eta_bang : forall E e t,
  typing E nil e (typ_bang t) ->
  F_observational_eq E nil e (exp_let e (exp_bang 0)) (typ_bang t).
Proof.
  intros E e t Typ.
  apply F_logical_related__sound; auto.
  assert (typing E nil (exp_let e (exp_bang 0)) (typ_bang t)) as Typ'.
    apply typing_eta_bang; auto.
  split; auto.
  split; auto.
    intros dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst H_relsubst H_Rsubst.
    assert (J:=Typ).
    apply parametricity with (dsubst:=dsubst) (dsubst':=dsubst')  
                                                         (gsubst:=gsubst) (gsubst':=gsubst')
                                                         (lgsubst:=lgsubst) (lgsubst':=lgsubst') (rsubst:=rsubst) in J; auto.
    destruct J as [v [v' [Typing [Typing' [Hn [Hn' Hrel ]]]]]].
    exists v. exists v'.
    split; auto.
    split.
      apply typing_subst with (E:=E) (D:=nil); auto.
        apply F_related_subst__inversion in H_relsubst.
        decompose [prod] H_relsubst; auto.
    split; auto.
    split.
      assert (J:=Hn').
      destruct J as [Hbrc' Hv'].
      split; auto.
        assert (J:=Typing').
        apply preservation_normalization with (v:=v') in J; auto.
        simpl_commut_subst in J.
        apply canonical_form_bang in J; auto.
        destruct J as [e1' EQ1']; subst.
        simpl_commut_subst.
        rewrite apply_gamma_subst_bv.
        rewrite apply_gamma_subst_bv.
        rewrite apply_delta_subst_bv.
        apply bigstep_red__trans with (e':=exp_let (exp_bang e1') (exp_bang 0)).
          apply _congr_let_arg; auto.
            apply expr_let with (L:={}); auto.
              intros x xn.
              unfold open_ee. simpl. auto.
          apply bigstep_red_trans with (e':=exp_bang e1'); auto.
            apply red_let_beta; auto.
              apply expr_let with (L:={}); auto.
                intros x xn.
                unfold open_ee. simpl. auto.

      apply F_related_values_bang_leq in Hrel.
      destruct Hrel as [Hv [Hv' Hrel]].
      apply F_related_values_bang_req.
      split; auto.
Qed.

Lemma typing_eta_tabs_abs : forall E e t1 t2,
  typing E nil e (typ_all (typ_arrow t1 t2)) ->
  typing E nil (exp_tabs (exp_abs t1 (exp_app (exp_tapp e 0) 0))) (typ_all (typ_arrow t1 t2)).
Proof.
  intros E e t1 t2 Typ.
  apply typing_tabs with (L:=dom E `union` fv_tt (typ_arrow t1 t2)); auto.
    intros X Xn.
    assert (J:=Typ).
    apply typing_regular in J.
    destruct J as [J1 [J2 [J3 J4]]].
    apply wft_all_inv with (X:=X) in J4; auto.
    unfold open_tt in J4. simpl in J4.
    apply wft_arrow_inv in J4.
    destruct J4 as [J4 J5].
    simpl_env in *.
    unfold open_te. unfold open_tt. simpl. simpl_env.
    apply typing_abs with (L:=dom E `union` {{X}}); auto.
      intros x xn.
      unfold open_ee. simpl. simpl_env.
      apply typing_app with (T1:=(open_tt_rec 0 X t1)) (D1:=nil) (D2:=[(x, lbind_typ (open_tt_rec 0 X t1))]); auto.
        rewrite <- open_te_rec_expr; auto.
        rewrite <- open_ee_rec_expr; auto.
        assert (typ_arrow (open_tt_rec 0 X t1) (open_tt_rec 0 X t2) =
                        (open_tt (typ_arrow t1 t2) X)) as EQ. auto.
        rewrite EQ.
        apply typing_tapp; auto.
          rewrite_env (nil ++ [(X, bind_kn)] ++ E).
          apply typing_weakening; auto.
            simpl_env. auto.
        apply typing_lvar; auto.
          rewrite_env ([(x, lbind_typ (open_tt_rec 0 X t1))]++nil).
          apply wf_lenv_typ; auto.
        rewrite_env ([(x, lbind_typ (open_tt_rec 0 X t1))]++nil).
        apply lenv_split_right; auto.
Qed.

Lemma bigstep_red_tapp : forall e1 e1' t2,
  bigstep_red e1 e1' ->
  type t2 ->
  bigstep_red (exp_tapp e1 t2) (exp_tapp e1' t2).
Proof.
  intros e1 e1' t2 Hrel Htype.
  induction Hrel; auto.
    apply bigstep_red_trans with (e':=exp_tapp e' t2); auto.
Qed.    

Lemma F_observational_eq__eta_tabs_abs : forall E e t1 t2,
  typing E nil e (typ_all (typ_arrow t1 t2)) ->
  F_observational_eq E nil e (exp_tabs (exp_abs t1 (exp_app (exp_tapp e 0) 0))) (typ_all (typ_arrow t1 t2)).
Proof.
  intros E e t1 t2 Typ.
  apply F_logical_related__sound; auto.
  assert (typing E nil (exp_tabs (exp_abs t1 (exp_app (exp_tapp e 0) 0))) (typ_all (typ_arrow t1 t2))) as Typ'.
    apply typing_eta_tabs_abs; auto.
  split; auto.
  split; auto.
    intros dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst H_relsubst H_Rsubst.
    assert (J:=Typ).
    apply parametricity with (dsubst:=dsubst) (dsubst':=dsubst')  
                                                         (gsubst:=gsubst) (gsubst':=gsubst')
                                                         (lgsubst:=lgsubst) (lgsubst':=lgsubst') (rsubst:=rsubst) in J; auto.
    destruct J as [v [v' [Typing [Typing' [Hn [Hn' Hrel ]]]]]].
    exists v. exists (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_tabs (exp_abs t1 (exp_app (exp_tapp e 0) 0)))))).
    split; auto.
    split.
      apply typing_subst with (E:=E) (D:=nil); auto.
        apply F_related_subst__inversion in H_relsubst.
        decompose [prod] H_relsubst; auto.
    split; auto.
    split. 
      split; auto.
        apply F_related_subst__inversion in H_relsubst.
        decompose [prod] H_relsubst.
        apply delta_gamma_lgamma_subst_value with (E:=E) (D:=nil); auto.

      apply F_related_values_all_leq in Hrel.
      destruct Hrel as [Hv [Hv' [L Hrel]]].
      apply F_related_values_all_req.
      split; auto.
      split.
        apply F_related_subst__inversion in H_relsubst.
        decompose [prod] H_relsubst.
        apply delta_gamma_lgamma_subst_value with (E:=E) (D:=nil); auto.

        exists (L `union` fv_tt (typ_arrow (apply_delta_subst_typ dsubst' t1) (apply_delta_subst_typ dsubst' t2))).
        intros X t3 t2' R Xn WfR Xn'.
        assert (X `notin` L) as XnL. auto.
        assert (J:=@Hrel X t3 t2' R XnL WfR Xn').
        destruct J as [w [w' [Hnw [Hnw' J]]]].
        unfold open_tt in J. simpl in J.
        apply F_related_values_arrow_leq in J.       
        destruct J as [Hw [Hw' J]].
        exists w. exists (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_abs (open_tt t1 t2') (exp_app (exp_tapp e t2') 0))))).
        split; auto.
        split.
        Case "norm".
          simpl_commut_subst.
          assert (disjdom (fv_ee 0) (dom lgsubst')) as Disj1.
            simpl. apply disjdom_nil_1.
          assert (disjdom (fv_ee 0) (dom gsubst')) as Disj2.
            simpl. apply disjdom_nil_1.
          assert (disjdom (fv_ee 0) (dom dsubst')) as Disj3.
            simpl. apply disjdom_nil_1.
          rewrite gamma_osubst_closed_exp with (e:=0); auto.
          rewrite gamma_osubst_closed_exp with (e:=0); auto.
          rewrite delta_osubst_closed_exp with (e:=0); auto.
          rewrite gamma_osubst_closed_typ with (t:=0); auto.
          rewrite delta_osubst_closed_typ with (t:=0); auto.
          rewrite gamma_subst_closed_typ with (t:=t2'); eauto using wfr_right_inv.
          rewrite delta_subst_closed_typ with (t:=t2'); eauto using wfr_right_inv.
          assert (exp_abs
                           (apply_delta_subst_typ dsubst' (apply_gamma_subst_typ gsubst' (apply_gamma_subst_typ lgsubst' (open_tt t1 t2'))))
                           (exp_app 
                               (exp_tapp
                                  (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e)))
                                  t2')
                                0) =
                          open_te
                              (exp_abs  
                                 (apply_delta_subst_typ dsubst' (apply_gamma_subst_typ gsubst' (apply_gamma_subst_typ lgsubst' t1)))
                                 (exp_app 
                                    (exp_tapp
                                      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e)))
                                      0)
                                   0))
                               t2') as EQ.
                 unfold open_te.
                 simpl.
                 rewrite <- open_te_rec_expr; auto.
                 rewrite commut_gamma_subst_open_tt.
                 rewrite commut_gamma_subst_open_tt.
                 rewrite commut_delta_subst_open_tt with (dE:=E); auto.
                   rewrite gamma_subst_closed_typ with (t:=t2'); eauto using wfr_right_inv.
                   rewrite delta_subst_closed_typ with (t:=t2'); eauto using wfr_right_inv.

                   apply F_related_subst__inversion in H_relsubst.
                   decompose [prod] H_relsubst; auto.
          rewrite EQ.
          split; auto.
            apply bigstep_red_trans with (e':=
                          open_te
                              (exp_abs  
                                 (apply_delta_subst_typ dsubst' (apply_gamma_subst_typ gsubst' (apply_gamma_subst_typ lgsubst' t1)))
                                 (exp_app 
                                    (exp_tapp
                                      (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e)))
                                      0)
                                   0))
                               t2'); auto.
               apply red_tabs; auto.
                 apply typing_subst with (E:=E) (D:=nil) (dsubst:=dsubst') (lgsubst:=lgsubst') (gsubst:=gsubst') in Typ'; auto.
                    simpl_commut_subst in Typ'.
                    rewrite gamma_osubst_closed_exp with (e:=0) in Typ'; auto.
                    rewrite gamma_osubst_closed_exp with (e:=0) in Typ'; auto.
                    rewrite delta_osubst_closed_exp with (e:=0) in Typ'; auto. 
                    rewrite gamma_osubst_closed_typ with (t:=0) in Typ'; auto.
                    rewrite delta_osubst_closed_typ with (t:=0) in Typ'; auto.

                    apply F_related_subst__inversion in H_relsubst.
                    decompose [prod] H_relsubst; auto.

                  apply wfr_right_inv in WfR.
                  apply type_from_wf_typ in WfR; auto.

          apply F_related_subst__inversion in H_relsubst.
          decompose [prod] H_relsubst; auto.
          unfold open_te. simpl.
          unfold apply_gamma_subst_typ.
          apply typing_subst with (E:=E) (D:=nil) (dsubst:=dsubst') (lgsubst:=lgsubst') (gsubst:=gsubst') in Typ'; auto.
             simpl_commut_subst in Typ'.
             rewrite gamma_osubst_closed_exp with (e:=0) in Typ'; auto.
             rewrite gamma_osubst_closed_exp with (e:=0) in Typ'; auto.
             rewrite delta_osubst_closed_exp with (e:=0) in Typ'; auto. 
             rewrite gamma_osubst_closed_typ with (t:=0) in Typ'; auto.
             rewrite delta_osubst_closed_typ with (t:=0) in Typ'; auto.
          apply value_abs.
          apply expr_abs with (L:={}); auto.
            apply typing_regular in Typ'.
            decompose [and] Typ'.
            apply wft_all_inv with (X:=X) in H3; auto.
               unfold open_tt in H3. simpl in H3.
               apply wft_arrow_inv in H3.
               destruct H3 as [H4 H5].
               assert (subst_tt X t2' (open_tt_rec 0 X (apply_delta_subst_typ dsubst' t1)) = (open_tt_rec 0 t2' (apply_delta_subst_typ dsubst' t1))) as EQ'.
                 simpl in Xn.
                 rewrite subst_tt_open_tt_rec; auto.
                   rewrite <- subst_tt_fresh with (T:=apply_delta_subst_typ dsubst' t1); auto.
                   simpl.
                   destruct (X==X); auto.
                     contradict n; auto.

                   apply wfr_right_inv in WfR.
                   apply type_from_wf_typ in WfR; auto.
               rewrite <- EQ'.
               apply type_from_wf_typ in H4.
               apply subst_tt_type; auto.
                 apply wfr_right_inv in WfR.
                 apply type_from_wf_typ in WfR; auto.

            intros x xn.
            unfold open_ee. simpl.
            apply expr_app; auto.
            apply expr_tapp; auto.
              assert (JJ:=Typ').
              apply typing_regular in Typ'.
              decompose [and] Typ'.
              inversion H0; subst.
              pick fresh Y.
              assert (Y `notin` L0) as YnL0. auto.
              apply H4 in YnL0; auto.
              unfold open_te in YnL0. simpl in YnL0.
              inversion YnL0; subst.
              pick fresh y.
              assert (y `notin` L1) as ynL1. auto.
              apply H7 in ynL1; auto.
              unfold open_ee in ynL1. simpl in ynL1.
              inversion ynL1; subst.
              inversion H8; subst.
              assert (subst_ee y x (open_ee_rec 0 y (open_te_rec 0 t2' (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e))))) = 
                            (open_ee_rec 0 x (open_te_rec 0 t2' (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e)))))) as EQ0.
                 simpl in Xn.
                 rewrite subst_ee_open_ee_rec; auto.
                 simpl.
                 destruct (y==y); subst; auto.
                   rewrite <- subst_ee_fresh; auto.
                     apply notin_fv_ee_open_te_exp_rec.
                     apply typing_subst with (E:=E) (D:=nil) (dsubst:=dsubst') (lgsubst:=lgsubst') (gsubst:=gsubst') in Typ; auto.
                     apply notin_fv_ee_typing with (y:=y) in Typ; auto.

                   contradict n; auto.
               rewrite <- EQ0.
               apply subst_ee_expr; auto.
              assert (subst_te Y t2' (open_ee_rec 0 y (open_te_rec 0 Y (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e))))) = 
                            (open_ee_rec 0 y (open_te_rec 0 t2' (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e)))))) as EQ1.
                 simpl in Xn.
                 rewrite subst_te_open_ee_rec; auto.
                 simpl.
                 rewrite subst_te_open_te_rec; auto.
                   simpl.
                   destruct (Y==Y); subst; auto.
                     rewrite <- subst_te_fresh; auto.
                     apply typing_subst with (E:=E) (D:=nil) (dsubst:=dsubst') (lgsubst:=lgsubst') (gsubst:=gsubst') in Typ; auto.
                     apply notin_fv_te_typing with (X:=Y) in Typ; auto.

                     contradict n; auto.

                   apply wfr_right_inv in WfR.
                   apply type_from_wf_typ in WfR; auto.

               rewrite <- EQ1.
              apply subst_te_expr; auto.
                apply wfr_right_inv in WfR.
                apply type_from_wf_typ in WfR; auto.

                apply wfr_right_inv in WfR.
                apply type_from_wf_typ in WfR; auto.

        Case "Rel".
          unfold open_tt. simpl. simpl_env.       
          apply F_related_values_arrow_req.
          split; auto.
          split.
          SCase "Value".
            apply F_related_subst__inversion in H_relsubst.
            decompose [prod] H_relsubst; auto.
            unfold open_te. simpl.
            unfold apply_gamma_subst_typ.
            apply typing_subst with (E:=E) (D:=nil) (dsubst:=dsubst') (lgsubst:=lgsubst') (gsubst:=gsubst') in Typ'; auto.
              simpl_commut_subst in Typ'.
              assert (disjdom (fv_ee 0) (dom lgsubst')) as Disj1.
                simpl. apply disjdom_nil_1.
              assert (disjdom (fv_ee 0) (dom gsubst')) as Disj2.
                simpl. apply disjdom_nil_1.
              assert (disjdom (fv_ee 0) (dom dsubst')) as Disj3.
                simpl. apply disjdom_nil_1.
              rewrite gamma_osubst_closed_exp with (e:=0) in Typ'; auto.
              rewrite gamma_osubst_closed_exp with (e:=0) in Typ'; auto.
              rewrite delta_osubst_closed_exp with (e:=0) in Typ'; auto. 
              rewrite gamma_osubst_closed_typ with (t:=0) in Typ'; auto.
              rewrite delta_osubst_closed_typ with (t:=0) in Typ'; auto.
            simpl_commut_subst.
            apply value_abs.
            apply expr_abs with (L:={}); auto.
              apply typing_regular in Typ'.
              decompose [and] Typ'.
              apply wft_all_inv with (X:=X) in H3; auto.
              unfold open_tt in H3. simpl in H3.
              apply wft_arrow_inv in H3.
              destruct H3 as [H4 H5].
              unfold apply_gamma_subst_typ.
              assert (subst_tt X t2' (open_tt_rec 0 X (apply_delta_subst_typ dsubst' t1)) = (open_tt_rec 0 t2' (apply_delta_subst_typ dsubst' t1))) as EQ'.
                  simpl in Xn.
                  rewrite subst_tt_open_tt_rec; auto.
                    rewrite <- subst_tt_fresh with (T:=apply_delta_subst_typ dsubst' t1); auto.
                    simpl.
                    destruct (X==X); auto.
                      contradict n; auto.

                    apply wfr_right_inv in WfR.
                    apply type_from_wf_typ in WfR; auto.
              assert (open_tt_rec 0 t2' t1 = open_tt t1 t2') as EQ1. 
                unfold open_tt. auto.
              rewrite EQ1.
              rewrite commut_delta_subst_open_tt with (dE:=E); auto.
              rewrite delta_osubst_closed_typ with (t:=t2') ; auto. 
                unfold open_tt.
                rewrite <- EQ'.
                apply type_from_wf_typ in H4.
                apply subst_tt_type; auto.  
                  apply wfr_right_inv in WfR.
                  apply type_from_wf_typ in WfR; auto.

                  apply empty_wft_disjdom; eauto using wfr_right_inv.

            intros x xn.
            unfold open_ee. simpl.
            rewrite gamma_osubst_closed_exp with (e:=0); auto.
            rewrite gamma_osubst_closed_exp with (e:=0); auto.
            rewrite delta_osubst_closed_exp with (e:=0); auto. 
            simpl.
            apply expr_app; auto.
            unfold apply_gamma_subst_typ.
            rewrite delta_osubst_closed_typ with (t:=t2') ; auto. 
              apply expr_tapp; auto.
                rewrite <- open_ee_rec_expr; auto.                

                apply wfr_right_inv in WfR.
                apply type_from_wf_typ in WfR; auto.

              apply empty_wft_disjdom; eauto using wfr_right_inv.

          SCase "Rel".
          intros x x' Typingx Typingx' Hrelx.
          assert (J':=@J x x' Typingx Typingx' Hrelx).
          destruct J' as [u [u' [Hnu [Hnu' J']]]].
          exists u. exists u'.
          split; auto.
          split; auto.
            simpl_commut_subst.
            assert (disjdom (fv_ee 0) (dom lgsubst')) as Disj1.
              simpl. apply disjdom_nil_1.
            assert (disjdom (fv_ee 0) (dom gsubst')) as Disj2.
              simpl. apply disjdom_nil_1.
            assert (disjdom (fv_ee 0) (dom dsubst')) as Disj3.
              simpl. apply disjdom_nil_1.
             rewrite gamma_osubst_closed_exp with (e:=0); auto.
             rewrite gamma_osubst_closed_exp with (e:=0); auto.
             rewrite delta_osubst_closed_exp with (e:=0); auto.
             unfold apply_gamma_subst_typ.
             assert (disjdom (fv_tt t2') (dom dsubst')) as Disj4.
               apply empty_wft_disjdom; eauto using wfr_right_inv.
             rewrite delta_osubst_closed_typ with (t:=t2'); auto.
             destruct Hnu' as [H1 H2].
             split; auto.
               apply bigstep_red__trans with (e':=exp_app w' x'); auto.
                 apply bigstep_red_trans with (e':=exp_app (exp_tapp  (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e))) t2') x'); auto.
                    assert (exp_app (exp_tapp (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e))) t2') x' =
                                      open_ee (exp_app (exp_tapp (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e))) t2') 0) x') as EQ.
                      unfold open_ee.
                      simpl.
                      rewrite <- open_ee_rec_expr; auto.
              rewrite EQ.
              apply red_abs; auto.
                apply typing_subst with (E:=E) (D:=nil) (dsubst:=dsubst') (lgsubst:=lgsubst') (gsubst:=gsubst') in Typ'; auto.
                   simpl_commut_subst in Typ'.
                   rewrite gamma_osubst_closed_exp with (e:=0) in Typ'; auto.
                   rewrite gamma_osubst_closed_exp with (e:=0) in Typ'; auto.
                   rewrite delta_osubst_closed_exp with (e:=0) in Typ'; auto.
                   rewrite gamma_osubst_closed_typ with (t:=0) in Typ'; auto.
                   rewrite delta_osubst_closed_typ with (t:=0) in Typ'; auto.

                   apply expr_abs with (L:={}); auto.
                     apply typing_regular in Typ'.
                     decompose [and] Typ'.
                      apply wft_all_inv with (X:=X) in H5; auto.
                     unfold open_tt in H5. simpl in H5.
                      apply wft_arrow_inv in H5.
                     destruct H5 as [H4 H5].
                      unfold apply_gamma_subst_typ.
                      assert (subst_tt X t2' (open_tt_rec 0 X (apply_delta_subst_typ dsubst' t1)) = (open_tt_rec 0 t2' (apply_delta_subst_typ dsubst' t1))) as EQ'.
                        simpl in Xn.
                        rewrite subst_tt_open_tt_rec; auto.
                          rewrite <- subst_tt_fresh with (T:=apply_delta_subst_typ dsubst' t1); auto.
                          simpl.
                          destruct (X==X); auto.
                            contradict n; auto.

                          apply wfr_right_inv in WfR.
                          apply type_from_wf_typ in WfR; auto.
                    assert (open_tt_rec 0 t2' t1 = open_tt t1 t2') as EQ1. 
                      unfold open_tt. auto.
                    rewrite EQ1.
                    rewrite commut_delta_subst_open_tt with (dE:=E); auto.
                    rewrite delta_osubst_closed_typ with (t:=t2') ; auto. 
                      unfold open_tt.
                      rewrite <- EQ'.
                      apply type_from_wf_typ in H4.
                      apply subst_tt_type; auto.  
                        apply wfr_right_inv in WfR.
                        apply type_from_wf_typ in WfR; auto.

                      apply F_related_subst__inversion in H_relsubst.
                      decompose [prod] H_relsubst; auto.

               intros x0 x0n.
               unfold open_ee. simpl.
               apply expr_app; auto.
               apply expr_tapp; auto.
                 rewrite <- open_ee_rec_expr; auto.                

                  apply wfr_right_inv in WfR.
                  apply type_from_wf_typ in WfR; auto.

                  apply F_related_subst__inversion in H_relsubst.
                  decompose [prod] H_relsubst; auto.

          apply bigstep_red_app; auto.
          apply bigstep_red__trans with (e':=exp_tapp v' t2'); auto.
            apply bigstep_red_tapp; auto.
              destruct Hn'; auto.

              apply wfr_right_inv in WfR.
              apply type_from_wf_typ in WfR; auto.
            destruct Hnw'; auto.
Qed.

Lemma typing_eta_tabs : forall E e t1,
  typing E nil e (typ_all t1) ->
  typing E nil (exp_tabs (exp_tapp e 0)) (typ_all t1).
Proof.
  intros E e t1 Typ.
  apply typing_tabs with (L:=dom E `union` fv_tt t1); auto.
    intros X Xn.
    assert (J:=Typ).
    apply typing_regular in J.
    destruct J as [J1 [J2 [J3 J4]]].
    apply wft_all_inv with (X:=X) in J4; auto.
    unfold open_tt in J4. simpl in J4.
    simpl_env in *.
    unfold open_te. unfold open_tt. simpl. simpl_env.
    apply typing_tapp; auto.
        rewrite_env (nil ++ [(X, bind_kn)] ++ E).
        apply typing_weakening; auto.
        simpl_env. 
        rewrite <- open_te_rec_expr; auto.
 
        rewrite_env ([(X, bind_kn)] ++ E). auto.
Qed.

Lemma F_observational_eq__eta_tabs : forall E e t1,
  typing E nil e (typ_all t1) ->
  F_observational_eq E nil e (exp_tabs (exp_tapp e 0)) (typ_all t1).
Proof.
  intros E e t1 Typ.
  apply F_logical_related__sound; auto.
  assert (typing E nil (exp_tabs (exp_tapp e 0)) (typ_all t1)) as Typ'.
    apply typing_eta_tabs; auto.
  split; auto.
  split; auto.
    intros dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst H_relsubst H_Rsubst.
    assert (J:=Typ).
    apply parametricity with (dsubst:=dsubst) (dsubst':=dsubst')  
                                                         (gsubst:=gsubst) (gsubst':=gsubst')
                                                         (lgsubst:=lgsubst) (lgsubst':=lgsubst') (rsubst:=rsubst) in J; auto.
    destruct J as [v [v' [Typing [Typing' [Hn [Hn' Hrel ]]]]]].
    exists v. exists (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' (exp_tabs (exp_tapp e 0))))).
    split; auto.
    split.
      apply typing_subst with (E:=E) (D:=nil); auto.
        apply F_related_subst__inversion in H_relsubst.
        decompose [prod] H_relsubst; auto.
    split; auto.
    split. 
      split; auto.
        apply F_related_subst__inversion in H_relsubst.
        decompose [prod] H_relsubst.
        apply delta_gamma_lgamma_subst_value with (E:=E) (D:=nil); auto.

      apply F_related_values_all_leq in Hrel.
      destruct Hrel as [Hv [Hv' [L Hrel]]].
      apply F_related_values_all_req.
      split; auto.
      split.
        apply F_related_subst__inversion in H_relsubst.
        decompose [prod] H_relsubst.
        apply delta_gamma_lgamma_subst_value with (E:=E) (D:=nil); auto.

        exists (L `union` fv_tt (apply_delta_subst_typ dsubst' t1)).
        intros X t3 t2' R Xn WfR Xn'.
        assert (X `notin` L) as XnL. auto.
        assert (J:=@Hrel X t3 t2' R XnL WfR Xn').
        destruct J as [w [w' [Hnw [Hnw' J]]]].
        unfold open_tt in J. simpl in J.
        exists w. exists w'.
        split; auto.
        split; auto.
        Case "norm".
        simpl_commut_subst.
        assert (disjdom (fv_tt 0) (dom dsubst')) as Disj.
            simpl. apply disjdom_nil_1.
        rewrite gamma_osubst_closed_typ with (t:=0); auto.
        rewrite delta_osubst_closed_typ with (t:=0); auto.
        destruct Hnw' as [H1 H2].
        split; auto.
          apply bigstep_red__trans with (e':=exp_tapp v' t2'); auto.
           apply bigstep_red_trans with (e':=exp_tapp  (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e))) t2'); auto.
             assert (exp_tapp  (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e))) t2' =
                              open_te (exp_tapp  (apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e))) 0) t2') as EQ.
                 unfold open_te.
                 simpl.
                 rewrite <- open_te_rec_expr; auto.
              rewrite EQ.
              apply red_tabs.
                apply typing_subst with (E:=E) (D:=nil) (dsubst:=dsubst') (lgsubst:=lgsubst') (gsubst:=gsubst') in Typ'; auto.
                   simpl_commut_subst in Typ'.
                   rewrite gamma_osubst_closed_typ with (t:=0) in Typ'; auto.
                   rewrite delta_osubst_closed_typ with (t:=0) in Typ'; auto.

                  apply F_related_subst__inversion in H_relsubst.
                  decompose [prod] H_relsubst; auto.
               apply wfr_right_inv in WfR. apply type_from_wf_typ in WfR; auto.
            destruct Hn'.
            apply wfr_right_inv in WfR. apply type_from_wf_typ in WfR.
            apply bigstep_red_tapp; auto. 
Qed.

Lemma contexting_nonlin_sub : forall E D T C E' D' T',
  contexting E D T C E' D' T' ->
  AtomSetImpl.diff (dom E) (cv_ec C) [<=] dom E'.
Proof.
  intros E D T C E' D' T' Hctx.
  (contexting_cases (induction Hctx) Case); intros; simpl in *.
  Case "contexting_hole".
    fsetdec.
  Case "contexting_abs_free".
    pick fresh x.
    assert (x `notin` L) as J. auto.
    apply H1 in J. 
    unfold open_ec in J.
    rewrite cv_ec_open_ec_rec in J.
    assert (AtomSetImpl.diff (dom E) (cv_ec C1) [=] AtomSetImpl.diff (dom E) (cv_ec C1)) as EQ.
      clear - H0. fsetdec.
    rewrite EQ.  clear EQ.
    assert (x `notin` dom E) as Sub. auto.
    clear - J Sub. fsetdec.
  Case "contexting_abs_capture".
    unfold close_ec. rewrite cv_ec_close_ec_rec.
    clear - H1 IHHctx. fsetdec.
  Case "contexting_app1".
    fsetdec.
  Case "contexting_app2".
    fsetdec.
  Case "contexting_tabs_free".
    pick fresh X.
    assert (X `notin` L) as J. auto.
    apply H0 in J. 
    unfold open_tc in J.
    rewrite cv_ec_open_tc_rec in J.
    assert (AtomSetImpl.diff (dom E) (cv_ec C1) [=] AtomSetImpl.diff (dom E) (cv_ec C1)) as EQ.
      clear - H. fsetdec.
    rewrite EQ.  clear EQ.
    assert (X `notin` dom E) as Sub. auto.
    clear - J Sub. fsetdec.
  Case "contexting_tabs_capture".
    unfold close_tc. rewrite cv_ec_close_tc_rec.
    rewrite env_remove_binds_dom; auto.
      clear - H0 IHHctx. fsetdec.
      apply contexting_regular in Hctx. decompose [and] Hctx; auto.
  Case "contexting_tapp".
    fsetdec.
  Case "contexting_bang".
    fsetdec.
  Case "contexting_let1".
    fsetdec.
  Case "contexting_let2_free".
    pick fresh x.
    assert (x `notin` L) as J. auto.
    apply H1 in J. 
    unfold open_ec in J.
    rewrite cv_ec_open_ec_rec in J.
    assert (AtomSetImpl.diff (dom E) (cv_ec C2) [=] AtomSetImpl.diff (dom E) (cv_ec C2)) as EQ.
      clear - H0. fsetdec.
    rewrite EQ.  clear EQ.
    assert (x `notin` dom E) as Sub. auto.
    clear - J Sub. fsetdec.
  Case "contexting_let2_capture".
    unfold close_ec. rewrite cv_ec_close_ec_rec.
    rewrite env_remove_binds_dom; auto.
      clear - H1 IHHctx. fsetdec.
      apply contexting_regular in Hctx. decompose [and] Hctx; auto.
  Case "contexting_apair1".
    fsetdec.
  Case "contexting_apair2".
    fsetdec.
  Case "contexting_fst".
    fsetdec.
  Case "contexting_snd".
    fsetdec.
Qed.

Lemma contexting_lin_sub : forall E D T C E' D' T',
  contexting E D T C E' D' T' ->
  AtomSetImpl.diff (dom D) (cv_ec C) [<=] dom D'.
Proof.
  intros E D T C E' D' T' Hctx.
  (contexting_cases (induction Hctx) Case); intros; simpl in *.
  Case "contexting_hole".
    fsetdec.
  Case "contexting_abs_free".
    pick fresh x.
    assert (x `notin` L) as J. auto.
    apply H1 in J. 
    unfold open_ec in J.
    rewrite cv_ec_open_ec_rec in J.
    assert (AtomSetImpl.diff (dom D) (cv_ec C1) [=] AtomSetImpl.diff (dom D) (cv_ec C1)) as EQ.
      clear - H0. fsetdec.
    rewrite EQ.  clear EQ.
    assert (x `notin` dom D) as Sub. auto.
    clear - J Sub. fsetdec.
  Case "contexting_abs_capture".
    unfold close_ec. rewrite cv_ec_close_ec_rec.
    rewrite lenv_remove_binds_dom; auto.
      clear - H1 IHHctx. fsetdec.
      apply contexting_regular in Hctx. decompose [and] Hctx; eauto.
  Case "contexting_app1".
    apply dom_lenv_split in H0. 
    rewrite H0. fsetdec.
  Case "contexting_app2".
    apply dom_lenv_split in H0. 
    rewrite H0. fsetdec.
  Case "contexting_tabs_free".
    pick fresh X.
    assert (X `notin` L) as J. auto.
    apply H0 in J. 
    unfold open_tc in J.
    rewrite cv_ec_open_tc_rec in J.
    assert (AtomSetImpl.diff (dom D) (cv_ec C1) [=] AtomSetImpl.diff (dom D) (cv_ec C1)) as EQ.
      clear - H. fsetdec.
    rewrite EQ.  clear EQ.
    assert (X `notin` dom D) as Sub. auto.
    clear - J Sub. fsetdec.
  Case "contexting_tabs_capture".
    unfold close_tc. rewrite cv_ec_close_tc_rec.
    clear - H0 IHHctx. fsetdec.
  Case "contexting_tapp".
    fsetdec.
  Case "contexting_bang".
    fsetdec.
  Case "contexting_let1".
    apply dom_lenv_split in H0. 
    rewrite H0. fsetdec.
  Case "contexting_let2_free".
    apply dom_lenv_split in H2. 
    rewrite H2.
    pick fresh x.
    assert (x `notin` L) as J. auto.
    apply H1 in J. 
    unfold open_ec in J.
    rewrite cv_ec_open_ec_rec in J.
    assert (AtomSetImpl.diff (dom D) (cv_ec C2) [=] AtomSetImpl.diff (dom D) (cv_ec C2)) as EQ.
      clear - H0. fsetdec.
    rewrite EQ.  clear EQ.
    assert (x `notin` dom D) as Sub. auto.
    clear - J Sub. fsetdec.
  Case "contexting_let2_capture".
    apply dom_lenv_split in H2. 
    rewrite H2.
    unfold close_ec. rewrite cv_ec_close_ec_rec.
    clear - H1 IHHctx. fsetdec.
  Case "contexting_apair1".
    fsetdec.
  Case "contexting_apair2".
    fsetdec.
  Case "contexting_fst".
    fsetdec.
  Case "contexting_snd".
    fsetdec.
Qed.

Lemma contexting_sub : forall E D T C E' D' T',
  contexting E D T C E' D' T' ->
  AtomSetImpl.diff (dom E `union` dom D) (cv_ec C) [<=] dom E' `union` dom D'.
Proof.
  intros E D T C E' D' T' Hctx.
  (contexting_cases (induction Hctx) Case); intros; simpl in *.
  Case "contexting_hole".
    fsetdec.
  Case "contexting_abs_free".
    pick fresh x.
    assert (x `notin` L) as J. auto.
    apply H1 in J. 
    unfold open_ec in J.
    rewrite cv_ec_open_ec_rec in J.
    assert (AtomSetImpl.diff (dom E `union` dom D) (cv_ec C1) [=] AtomSetImpl.diff (dom E `union` dom D) (cv_ec C1)) as EQ.
      clear - H0. fsetdec.
    rewrite EQ.  clear EQ.
    assert (x `notin` dom E `union` dom D) as Sub. auto.
    clear - J Sub. fsetdec.
  Case "contexting_abs_capture".
    unfold close_ec. rewrite cv_ec_close_ec_rec.
    rewrite lenv_remove_binds_dom; auto.
      clear - H1 IHHctx. fsetdec.
      apply contexting_regular in Hctx. decompose [and] Hctx; eauto.
  Case "contexting_app1".
    apply dom_lenv_split in H0. 
    rewrite H0. fsetdec.
  Case "contexting_app2".
    apply dom_lenv_split in H0. 
    rewrite H0. fsetdec.
  Case "contexting_tabs_free".
    pick fresh X.
    assert (X `notin` L) as J. auto.
    apply H0 in J. 
    unfold open_tc in J.
    rewrite cv_ec_open_tc_rec in J.
    assert (AtomSetImpl.diff (dom E `union` dom D) (cv_ec C1) [=] AtomSetImpl.diff (dom E `union` dom D) (cv_ec C1)) as EQ.
      clear - H. fsetdec.
    rewrite EQ.  clear EQ.
    assert (X `notin` dom E `union` dom D) as Sub. auto.
    clear - J Sub. fsetdec.
  Case "contexting_tabs_capture".
    unfold close_tc. rewrite cv_ec_close_tc_rec.
    rewrite env_remove_binds_dom; auto.
      clear - H0 IHHctx. fsetdec.
      apply contexting_regular in Hctx. decompose [and] Hctx; auto.
  Case "contexting_tapp".
    fsetdec.
  Case "contexting_bang".
    fsetdec.
  Case "contexting_let1".
    apply dom_lenv_split in H0. 
    rewrite H0. fsetdec.
  Case "contexting_let2_free".
    apply dom_lenv_split in H2. 
    rewrite H2. 
    pick fresh x.
    assert (x `notin` L) as J. auto.
    apply H1 in J. 
    unfold open_ec in J.
    rewrite cv_ec_open_ec_rec in J.
    assert (AtomSetImpl.diff (dom E `union` dom D) (cv_ec C2) [=] AtomSetImpl.diff (dom E `union` dom D) (cv_ec C2)) as EQ.
      clear - H0. fsetdec.
    rewrite EQ.  clear EQ.
    assert (x `notin` dom E `union` dom D) as Sub. auto.
    clear - J Sub. fsetdec.
  Case "contexting_let2_capture".
    apply dom_lenv_split in H2. 
    rewrite H2. 
    unfold close_ec. rewrite cv_ec_close_ec_rec.
    rewrite env_remove_binds_dom; auto.
      clear - H1 IHHctx. fsetdec.
      apply contexting_regular in Hctx. decompose [and] Hctx; auto.
  Case "contexting_apair1".
    fsetdec.
  Case "contexting_apair2".
    fsetdec.
  Case "contexting_fst".
    fsetdec.
  Case "contexting_snd".
    fsetdec.
Qed.

Hint Extern 1 (context ?C) =>
  match goal with
  | H: contexting _ _ _ C _ _ _ |- _ => apply (contexting__context _ _ _ _ _ _ _ H)
  end.

Lemma _env_remove_bind_typ_gdom : forall E y t,
  uniq E ->
  (binds y (bind_typ t) E -> gdom_env (env_remove (y, bind_typ t) E) [=] AtomSetImpl.diff (gdom_env E) {{y}}) /\
  (~binds y (bind_typ t) E -> gdom_env (env_remove (y, bind_typ t) E) [=] gdom_env E).
Proof.
  intros E y t Uniq.
  generalize dependent y.
  generalize dependent t.
  induction Uniq; intros; simpl.
    split; auto.
      intros J. contradict J; auto.

    split; intro J.
      destruct (eq_binding_dec (y,bind_typ t)  (x, a)); simpl.
        inversion e; subst. 
        destruct (IHUniq t x) as [J1 J2].
        rewrite J2; auto. 
          rewrite dom__ddom_gdom in H. fsetdec.
          intros JJ. apply binds_In in JJ. contradict JJ; auto.

        analyze_binds J.
        destruct (IHUniq t y) as [J1 J2].
        destruct a.
          rewrite J1; auto.
          destruct (x == y); subst.
            apply binds_In in BindsTac. contradict BindsTac; auto.                 
            fsetdec.
      
          rewrite J1; auto.
          destruct (x == y); subst.
            apply binds_In in BindsTac. contradict BindsTac; auto.                 
            fsetdec.

      destruct (eq_binding_dec (y,bind_typ t)  (x, a)); simpl.
        inversion e; subst.
        contradict J; auto.
 
        destruct (IHUniq t y) as [J1 J2].
        destruct a.
          rewrite J2; auto. 
          fsetdec.

          rewrite J2; auto. 
          fsetdec.
Qed.

Lemma env_remove_bind_typ_gdom : forall E y t,
  uniq E ->
  binds y (bind_typ t) E -> 
  gdom_env (env_remove (y, bind_typ t) E) [=] AtomSetImpl.diff (gdom_env E) {{y}}.
Proof.
  intros E y t H1 H2.
  destruct (@_env_remove_bind_typ_gdom E y t H1); auto.
Qed.

Lemma env_remove_bind_kn_gdom : forall E Y,
  uniq E ->
  gdom_env (env_remove (Y, bind_kn) E) [=] (gdom_env E).
Proof.
  intros E Y Uniq.
  generalize dependent Y.
  induction Uniq; intros; simpl.
    split; auto.
      destruct (eq_binding_dec (Y,bind_kn)  (x, a)); simpl.
        inversion e; subst. 
        rewrite (IHUniq x).
        fsetdec.

        destruct a.
          rewrite (IHUniq Y). fsetdec.

          rewrite (IHUniq Y). fsetdec.
Qed.

Lemma notin_fv_ec_contexting : forall E D T C E' D' T' (y : atom),
  contexting E D T C E' D' T' ->
  y `notin` gdom_env E' `union` dom D' ->
  y `notin` fv_ec C.
Proof.
  intros E D T C E' D' T' y Hctx.
  generalize dependent y.
  (contexting_cases (induction Hctx) Case); intros; simpl in *.
  Case "contexting_hole".
    fsetdec.

  Case "contexting_abs_free".
    pick fresh x.
    assert (x `notin` L ) as J. auto.
    apply H1 with (y:=y) in J; auto.
    assert (J1:=@open_ec_fv_ec_lower C1 x).
    clear - J J1. fsetdec.

  Case "contexting_abs_capture".
    destruct (y0==y); subst.
      apply close_ec_fv_ec_notin.

      assert (y0 `notin` gdom_env E' `union` dom D') as J.
        rewrite lenv_remove_binds_dom in H2; auto.
          clear - n H2. fsetdec.
          apply contexting_regular in Hctx. decompose [and] Hctx; eauto.
      apply IHHctx in J.
      assert (J':=@close_ec_fv_ec_upper C1 y).
      clear - J J'. fsetdec.

  Case "contexting_app1".
    apply dom_lenv_split in H0. 
    rewrite H0 in H2.
    apply typing_ldom in H.
    assert (y `notin` fv_ec C1) as J.
      apply IHHctx; auto.
    clear - J H2 H J. fsetdec.

  Case "contexting_app2".
    apply dom_lenv_split in H0. 
    rewrite H0 in H2.
    apply typing_ldom in H.
    assert (y `notin` fv_ec C2) as J.
      apply IHHctx; auto.
    clear - J H2 H J. fsetdec.

  Case "contexting_tabs_free".
    pick fresh X.
    assert (X `notin` L) as J. auto.
    apply H0 with (y:=y) in J; auto.
    rewrite open_tc_fv_ec_eq in J. assumption.

  Case "contexting_tabs_capture".
    rewrite <- fv_ec_close_tc.
    apply IHHctx.
      rewrite env_remove_bind_kn_gdom in H2; auto.
        apply contexting_regular in Hctx. decompose [and] Hctx; auto.

  Case "contexting_tapp".
    apply IHHctx; auto.

  Case "contexting_bang".
    apply IHHctx; auto.

  Case "contexting_let1".
    apply dom_lenv_split in H0. 
    rewrite H0 in H2.
    pick fresh x.
    assert (x `notin` L) as J. auto.
    apply H in J.
    apply typing_ldom in J.
    assert (y `notin` fv_ee (open_ee e2 x)) as yne2x.
      simpl in J. destruct_notin. 
      clear - J NotInTac H2 NotInTac22. 
      fsetdec.
    apply notin_fv_ee_open_ee_inv in yne2x.
    assert (y `notin` fv_ec C1) as J'.
      apply IHHctx; auto.
    clear - yne2x J'. fsetdec.

  Case "contexting_let2_free".
    apply dom_lenv_split in H2. 
    rewrite H2 in H4.
    apply typing_ldom in H.
    pick fresh x.
    assert (x `notin` L) as J. auto.
    apply H1 with (y:=y) in J; auto. 
    assert (J1:=@open_ec_fv_ec_lower C2 x).
    clear - J H J1 H4 H0. fsetdec.

  Case "contexting_let2_capture".
    apply dom_lenv_split in H2. 
    rewrite H2 in H4.
    apply typing_ldom in H.
    assert (y0 `notin` fv_ee e1) as y0ne1. fsetdec.
    destruct (y0==y); subst.
      assert (y `notin` fv_ec (close_ec C2 y)) as y0nC2. 
        apply close_ec_fv_ec_notin.
      auto.

      assert (y0 `notin` gdom_env E' `union` dom D2') as J.
        rewrite env_remove_bind_typ_gdom in H4; auto.
          clear - n H4. fsetdec.
          apply contexting_regular in Hctx. decompose [and] Hctx; auto.
      apply IHHctx in J.
      assert (J':=@close_ec_fv_ec_upper C2 y).
      clear - y0ne1 J J'. fsetdec.
     
  Case "contexting_apair1".
    apply typing_ldom in H.
    assert (y `notin` fv_ec C1) as J.
      apply IHHctx; auto.
    clear - J H H0. fsetdec.

  Case "contexting_apair2".
    apply typing_ldom in H.
    assert (y `notin` fv_ec C2) as J.
      apply IHHctx; auto.
    clear - J H H0. fsetdec.

  Case "contexting_fst".
    apply IHHctx; auto.

  Case "contexting_snd".
    apply IHHctx; auto.
Qed.

Lemma fv_ec_contexting_sub : forall E D T C E' D' T',
  contexting E D T C E' D' T' ->
  fv_ec C [<=] gdom_env E' `union` dom D'.
Proof.
  intros E D T C E' D' T' Hctx.
  (contexting_cases (induction Hctx) Case); intros; simpl in *; auto.
  Case "contexting_hole".
    fsetdec.

  Case "contexting_abs_free".
    pick fresh x.
    assert (x `notin` L) as J. auto.
    apply H1 in J; auto.
    assert (J1:=@open_ec_fv_ec_lower C1 x).
    destruct_notin.
    clear - J  J1 NotInTac11 NotInTac3 NotInTac7.
    apply dom__gdom in NotInTac3.
    fsetdec.

  Case "contexting_abs_capture".
    rewrite lenv_remove_binds_dom; auto.
      assert (fv_ec (close_ec C1 y) [=] AtomSetImpl.diff (fv_ec C1) {{y}}) as J.
        apply close_ec_fv_ec_eq'.
      rewrite J.
      destruct_notin.
      clear - H1 IHHctx NotInTac. fsetdec.

      apply contexting_regular in Hctx. decompose [and] Hctx; eauto.

  Case "contexting_app1".
    apply dom_lenv_split in H0. 
    rewrite H0.
    apply typing_ldom in H.
    clear - H IHHctx. fsetdec.

  Case "contexting_app2".
    apply dom_lenv_split in H0. 
    rewrite H0.
    apply typing_ldom in H.
    clear - H IHHctx. fsetdec.

  Case "contexting_tabs_free".
    pick fresh X.
    assert (X `notin` L) as J. auto.
    apply H0 in J; auto.
    rewrite (@open_tc_fv_ec_eq C1 X) in J. auto.

  Case "contexting_tabs_capture".
    rewrite env_remove_bind_kn_gdom; auto.
      rewrite <- fv_ec_close_tc; auto.
      apply contexting_regular in Hctx. decompose [and] Hctx; auto.

  Case "contexting_let1".
    apply dom_lenv_split in H0. 
    rewrite H0.
    pick fresh x.
    assert (x `notin` L) as J. auto.
    apply H in J.
    apply typing_ldom in J.
    assert (fv_ee (open_ee e2 x) [<=] gdom_env ((x, bind_typ T1')::E') `union` dom D2') as J2.
      simpl in J. simpl. clear - J. fsetdec.
    assert (J1:=@open_ee_fv_ee_lower e2 x).
    assert (fv_ee e2 [<=] gdom_env E' `union` dom D2') as J3.
      destruct_notin. 
      clear - J1 J2 NotInTac5 NotInTac10 NotInTac0.
      apply dom__gdom in NotInTac5.
      simpl in J2. fsetdec.
    clear - J3 IHHctx. fsetdec.

  Case "contexting_let2_free".
    apply dom_lenv_split in H2. 
    rewrite H2.
    apply typing_ldom in H.
    pick fresh x.
    assert (x `notin` L) as J. auto.
    apply H1 in J; auto. 
    assert (J1:=@open_ec_fv_ec_lower C2 x).
    destruct_notin.
    clear - J H J1 NotInTac10 NotInTac5 NotInTac17.
    apply dom__gdom in NotInTac5.
    assert (fv_ee e1 [<=] gdom_env E' `union` dom D1') as J3.
      fsetdec.
    fsetdec.

  Case "contexting_let2_capture".
    apply dom_lenv_split in H2. 
    rewrite H2.
    apply typing_ldom in H.
    assert (fv_ee e1 [<=] gdom_env (env_remove (y,bind_typ T1') E') `union` dom D1') as J3.
      fsetdec.
    assert (uniq E') as UniqE'.
      apply contexting_regular in Hctx. decompose [and] Hctx; auto.
    rewrite env_remove_bind_typ_gdom in J3; auto.
    rewrite env_remove_bind_typ_gdom; auto.
    assert (fv_ec (close_ec C2 y) [=] AtomSetImpl.diff (fv_ec C2) {{y}}) as J.
      apply close_ec_fv_ec_eq'.
    rewrite J.
    destruct_notin.
    clear - J3 H1 IHHctx NotInTac. fsetdec.

  Case "contexting_apair1".
    apply typing_ldom in H.
    clear - H IHHctx. fsetdec.

  Case "contexting_apair2".
    apply typing_ldom in H.
    clear - H IHHctx. fsetdec.
Qed.
            
Lemma plug_plugC: forall C1 C2 e,
  disjdom (cv_ec C1) (cv_ec C2) ->
  plug (plugC C1 C2) e = plug C1 (plug C2 e).
Proof.
  induction C1; intros C2 ee Disj; simpl; 
    try solve [auto | rewrite IHC1; auto].
    simpl in Disj.
    rewrite IHC1. 
      unfold shift_ee. rewrite  shift_ee_rec_plug. auto.
      
      apply disjdom_sym_1.
      apply disjdom_sub with (D1:=cv_ec C1).
        apply disjdom_eq with (D1:=cv_ec C2).
          apply disjdom_sym_1; auto.
          
          unfold shift_ec.
          rewrite <- cv_ec_shift_ec_rec. 
          fsetdec.
        fsetdec.

    simpl in Disj.
    rewrite IHC1. 
      unfold shift_ee. rewrite  shift_ee_rec_plug.
      unfold close_ee. rewrite  close_ee_rec_plug; auto.
        rewrite <- cv_ec_shift_ec_rec.
        apply disjdom_one_1.
        apply disjdom_sym_1.
        apply disjdom_sub with (D1:={{a}} `union` cv_ec C1).
          apply disjdom_sym_1; auto.
          fsetdec.
      
      apply disjdom_sym_1.
      apply disjdom_sub with (D1:={{a}} `union` cv_ec C1).
        apply disjdom_eq with (D1:=cv_ec C2).
          apply disjdom_sym_1; auto.
          
          unfold close_ec.
          rewrite cv_ec_close_ec_rec.
          unfold shift_ec.
          rewrite <- cv_ec_shift_ec_rec. 
          fsetdec.
        fsetdec.
    
    simpl in Disj.
    rewrite IHC1. 
      unfold shift_te. rewrite  shift_te_rec_plug. auto.
      
      apply disjdom_sym_1.
      apply disjdom_sub with (D1:=cv_ec C1).
        apply disjdom_eq with (D1:=cv_ec C2).
          apply disjdom_sym_1; auto.
          
          unfold shift_tc.
          rewrite <- cv_ec_shift_tc_rec. 
          fsetdec.
        fsetdec.

    simpl in Disj.
    rewrite IHC1. 
      unfold shift_te. rewrite  shift_te_rec_plug.
      unfold close_te. rewrite  close_te_rec_plug; auto.
        rewrite <- cv_ec_shift_tc_rec.
        apply disjdom_one_1.
        apply disjdom_sym_1.
        apply disjdom_sub with (D1:={{a}} `union` cv_ec C1).
          apply disjdom_sym_1; auto.
          fsetdec.
      
      apply disjdom_sym_1.
      apply disjdom_sub with (D1:={{a}} `union` cv_ec C1).
        apply disjdom_eq with (D1:=cv_ec C2).
          apply disjdom_sym_1; auto.
          
          unfold close_tc.
          rewrite cv_ec_close_tc_rec.
          unfold shift_tc.
          rewrite <- cv_ec_shift_tc_rec. 
          fsetdec.
        fsetdec.

    simpl in Disj.
    rewrite IHC1. 
      unfold shift_ee. rewrite  shift_ee_rec_plug. auto.
      
      apply disjdom_sym_1.
      apply disjdom_sub with (D1:=cv_ec C1).
        apply disjdom_eq with (D1:=cv_ec C2).
          apply disjdom_sym_1; auto.
          
          unfold shift_ec.
          rewrite <- cv_ec_shift_ec_rec. 
          fsetdec.
        fsetdec.

    simpl in Disj.
    rewrite IHC1. 
      unfold shift_ee. rewrite  shift_ee_rec_plug.
      unfold close_ee. rewrite  close_ee_rec_plug; auto.
        rewrite <- cv_ec_shift_ec_rec.
        apply disjdom_one_1.
        apply disjdom_sym_1.
        apply disjdom_sub with (D1:={{a}} `union` cv_ec C1).
          apply disjdom_sym_1; auto.
          fsetdec.
      
      apply disjdom_sym_1.
      apply disjdom_sub with (D1:={{a}} `union` cv_ec C1).
        apply disjdom_eq with (D1:=cv_ec C2).
          apply disjdom_sym_1; auto.
          
          unfold close_ec.
          rewrite cv_ec_close_ec_rec.
          unfold shift_ec.
          rewrite <- cv_ec_shift_ec_rec. 
          fsetdec.
        fsetdec.
Qed.

Lemma plugC_context : forall C C',
  context C ->
  context C' ->
  disjdom (cv_ec C) (cv_ec C') ->
  context (plugC C C').
Proof.
  intros C C' HC HC' Disj.
  generalize dependent C'.
  induction HC; simpl; intros; auto.
    apply context_abs_free with (L:=L `union` cv_ec C1); auto.
      intros x xn.
      unfold shift_ec.
      rewrite <- shift_ec_rec_context; auto.
      rewrite open_ec_plugC; auto.
        apply H1; auto.
        rewrite <- open_ec_context; auto.

        apply disjdom_sym_1.
        apply disjdom_sub with (D1:=cv_ec C1).
          apply disjdom_eq with (D1:=cv_ec C').
            apply disjdom_sym_1; auto.
            unfold open_ec.
            rewrite cv_ec_open_ec_rec. fsetdec.
          unfold open_ec. rewrite cv_ec_open_ec_rec. fsetdec.

        simpl. 
        apply disjdom_eq with (D1:={{x}}).
          apply disjdom_one_2; auto.
          fsetdec.

    apply context_abs_capture with (L:=L `union` cv_ec C1); auto.
      intros x xn.
      unfold shift_ec.
      rewrite <- shift_ec_rec_context; auto.
      rewrite open_ec_plugC; auto.
        rewrite close_open_ec__subst_ec; auto.
        apply H1; auto.
          apply subst_ec_context; auto.

        apply disjdom_sym_1.
        apply disjdom_sub with (D1:={{y}} `union` cv_ec C1).
          apply disjdom_eq with (D1:=cv_ec C').
            apply disjdom_sym_1; auto.
            rewrite cv_ec_subst_ec_rec. fsetdec.
          unfold open_ec. rewrite cv_ec_open_ec_rec. fsetdec.

        simpl. 
        apply disjdom_eq with (D1:={{x}}).
          apply disjdom_one_2; auto.
          fsetdec.

    apply context_tabs_free with (L:=L `union` cv_ec C1); auto.
      intros X Xn.
      unfold shift_tc.
      rewrite <- shift_tc_rec_context; auto.
      rewrite open_tc_plugC; auto.
        apply H0; auto.
        rewrite <- open_tc_context; auto.

        apply disjdom_sym_1.
        apply disjdom_sub with (D1:=cv_ec C1).
          apply disjdom_eq with (D1:=cv_ec C').
            apply disjdom_sym_1; auto.
            unfold open_tc.
            rewrite cv_ec_open_tc_rec. fsetdec.
          unfold open_tc. rewrite cv_ec_open_tc_rec. fsetdec.

        simpl. 
        apply disjdom_eq with (D1:={{X}}).
          apply disjdom_one_2; auto.
          fsetdec.

    apply context_tabs_capture with (L:=L `union` cv_ec C1); auto.
      intros X Xn.
      unfold shift_tc.
      rewrite <- shift_tc_rec_context; auto.
      rewrite open_tc_plugC; auto.
        rewrite close_open_tc__subst_tc; auto.
        apply H0; auto.
          apply subst_tc_context; auto.

        apply disjdom_sym_1.
        apply disjdom_sub with (D1:={{Y}} `union` cv_ec C1).
          apply disjdom_eq with (D1:=cv_ec C').
            apply disjdom_sym_1; auto.
            rewrite cv_ec_subst_tc_rec. fsetdec.
          unfold open_tc. rewrite cv_ec_open_tc_rec. fsetdec.

        simpl. 
        apply disjdom_eq with (D1:={{X}}).
          apply disjdom_one_2; auto.
          fsetdec.

    apply context_let1 with (L:=L `union` cv_ec C1); auto.

    apply context_let2_free with (L:=L `union` cv_ec C2); auto.
      intros x xn.
      unfold shift_ec.
      rewrite <- shift_ec_rec_context; auto.
      rewrite open_ec_plugC; auto.
        apply H1; auto.
        rewrite <- open_ec_context; auto.

        apply disjdom_sym_1.
        apply disjdom_sub with (D1:=cv_ec C2).
          apply disjdom_eq with (D1:=cv_ec C').
            apply disjdom_sym_1; auto.
            unfold open_ec.
            rewrite cv_ec_open_ec_rec. fsetdec.
          unfold open_ec. rewrite cv_ec_open_ec_rec. fsetdec.

        simpl. 
        apply disjdom_eq with (D1:={{x}}).
          apply disjdom_one_2; auto.
          fsetdec.

    apply context_let2_capture with (L:=L `union` cv_ec C2); auto.
      intros x xn.
      unfold shift_ec.
      rewrite <- shift_ec_rec_context; auto.
      rewrite open_ec_plugC; auto.
        rewrite close_open_ec__subst_ec; auto.
        apply H1; auto.
          apply subst_ec_context; auto.

        apply disjdom_sym_1.
        apply disjdom_sub with (D1:={{y}} `union` cv_ec C2).
          apply disjdom_eq with (D1:=cv_ec C').
            apply disjdom_sym_1; auto.
            rewrite cv_ec_subst_ec_rec. fsetdec.
          unfold open_ec. rewrite cv_ec_open_ec_rec. fsetdec.

        simpl. 
        apply disjdom_eq with (D1:={{x}}).
          apply disjdom_one_2; auto.
          fsetdec.
Qed.

Lemma plugC_vcontext__value : forall C C',
  vcontext C ->
  context C' ->
  disjdom (cv_ec C) (cv_ec C') ->
  vcontext (plugC C C').
Proof.
  intros C C' VC HC' Disj.
  generalize dependent C'.
  induction VC; simpl; intros; auto.
    apply vcontext_abs_free.
      apply plugC_context with (C':=C') in H; auto.
    apply vcontext_abs_capture.
      apply plugC_context with (C':=C') in H; auto.
    apply vcontext_tabs_free.
      apply plugC_context with (C':=C') in H; auto.
    apply vcontext_tabs_capture.
      apply plugC_context with (C':=C') in H; auto.
    apply vcontext_bang.
      apply plugC_context with (C':=C') in H; auto.
    apply vcontext_apair1.
      apply plugC_context with (C':=C') in H; auto.
    apply vcontext_apair2.
      apply plugC_context with (C':=C') in H; auto.
Qed.

Lemma env_remove_bind_typ_ddom : forall E y t,
  uniq E ->
  ddom_env (env_remove (y, bind_typ t) E) [=] (ddom_env E).
Proof.
  intros E y t Uniq.
  generalize dependent y.
  generalize dependent t.
  induction Uniq; intros; simpl.
    split; auto.
      destruct (eq_binding_dec (y,bind_typ t)  (x, a)); simpl.
        inversion e; subst. 
        rewrite (IHUniq t x).
        fsetdec.

        destruct a.
          rewrite (IHUniq t y). fsetdec.

          rewrite (IHUniq t y). fsetdec.
Qed.

Lemma typing_fv_te_upper' : forall E lE e t,
  typing E lE e t ->
  fv_te e [<=] ddom_env E.
Proof.
  intros E lE e t Typing.
  (typing_cases (induction Typing) Case); intros; subst; simpl.
  Case "typing_var".
    apply binds_In in H0.
    fsetdec.
  Case "typing_lvar".
    fsetdec.
  Case "typing_abs".
    pick fresh x.
    assert (x `notin` L) as xnL. auto.
    apply H1 in xnL.
    assert (J:=@fv_te_open_ee_eq e1 x).
    rewrite J in xnL.
    assert (J':=@wft_fv_tt_dsub E T1 H).
    clear - J' xnL. fsetdec.
  Case "typing_app".
    fsetdec.
  Case "typing_tabs".
    pick fresh X.
    assert (X `notin` L) as XnL. auto.
    apply H0 in XnL.
    assert (J:=@open_te_fv_te_lower e1 X).
    simpl in XnL.
    assert (fv_te e1 [<=] add X (ddom_env E)) as JJ.
      clear - XnL J. fsetdec.
    destruct_notin.
    clear - JJ NotInTac.
    fsetdec.
  Case "typing_tapp".
    assert (J':=@wft_fv_tt_dsub E T H).
     fsetdec.
  Case "typing_bang". auto.
  Case "typing_let".
    pick fresh x.
    assert (x `notin` L) as xnL. auto.
    apply H0 in xnL.
    assert (J:=@fv_te_open_ee_eq e2 x).
    rewrite J in xnL.
    destruct_notin.
    clear - IHTyping xnL NotInTac0. simpl in xnL. fsetdec.
  Case "typing_apair". fsetdec.
  Case "typing_fst". auto.
  Case "typing_snd". auto.
Qed.

Lemma _env_remove_bind_kn_ddom : forall E Y,
  uniq E ->
  (binds Y (bind_kn) E -> ddom_env (env_remove (Y, bind_kn) E) [=] AtomSetImpl.diff (ddom_env E) {{Y}}) /\
  (~binds Y (bind_kn) E -> ddom_env (env_remove (Y, bind_kn) E) [=] ddom_env E).
Proof.
  intros E Y Uniq.
  generalize dependent Y.
  induction Uniq; intros; simpl.
    split; auto.
      intros J. contradict J; auto.

    split; intro J.
      destruct (eq_binding_dec (Y,bind_kn)  (x, a)); simpl.
        inversion e; subst. 
        destruct (IHUniq x) as [J1 J2].
        rewrite J2; auto. 
          rewrite dom__ddom_gdom in H. fsetdec.
          intros JJ. apply binds_In in JJ. contradict JJ; auto.

        analyze_binds J.
        destruct (IHUniq Y) as [J1 J2].
        destruct a.
          rewrite J1; auto.
          destruct (x == Y); subst.
            apply binds_In in BindsTac. contradict BindsTac; auto.                 
            fsetdec.
      
          rewrite J1; auto.
          destruct (x == Y); subst.
            apply binds_In in BindsTac. contradict BindsTac; auto.                 
            fsetdec.

      destruct (eq_binding_dec (Y,bind_kn)  (x, a)); simpl.
        inversion e; subst.
        contradict J; auto.
 
        destruct (IHUniq Y) as [J1 J2].
        destruct a.
          rewrite J2; auto. 
          fsetdec.

          rewrite J2; auto. 
          fsetdec.
Qed.

Lemma env_remove_bind_kn_ddom : forall E Y,
  uniq E ->
  binds Y (bind_kn) E -> 
  ddom_env (env_remove (Y, bind_kn) E) [=] AtomSetImpl.diff (ddom_env E) {{Y}}.
Proof.
  intros E Y H1 H2.
  destruct (@_env_remove_bind_kn_ddom E Y H1); auto.
Qed.

Lemma notin_fv_tc_contexting : forall E D T C E' D' T' (X : atom),
  contexting E D T C E' D' T' ->
  X `notin` ddom_env E' ->
  X `notin` fv_tc C.
Proof.
  intros E D T C E' D' T' X Hctx.
  generalize dependent X.
  (contexting_cases (induction Hctx) Case); intros; simpl in *.
  Case "contexting_hole".
    fsetdec.

  Case "contexting_abs_free".
    pick fresh x.
    assert (x `notin` L) as J. auto.
    apply H1 with (X:=X) in J; auto.
    rewrite (open_ec_fv_tc_eq C1 x) in J.
    apply dnotin_fv_wf with (X:=X) in H; auto.

  Case "contexting_abs_capture".
    rewrite <- fv_tc_close_ec.
    apply dnotin_fv_wf with (X:=X) in H; auto.

  Case "contexting_app1".
    apply typing_fv_te_upper' in H; auto.

  Case "contexting_app2".
    apply typing_fv_te_upper' in H; auto.

  Case "contexting_tabs_free".
    pick fresh X'.
    assert (X' `notin` L) as J. auto.
    apply H0 with (X0:=X) in J; auto.
    assert (J1:=@open_tc_fv_tc_lower C1 X').
    clear - J J1. fsetdec.

  Case "contexting_tabs_capture".
    destruct (X==Y); subst.
      apply close_tc_fv_tc_notin.

      assert (X `notin` ddom_env E') as J.
        rewrite env_remove_bind_kn_ddom in H2; auto.
          apply contexting_regular in Hctx. decompose [and] Hctx; auto.
      apply IHHctx in J.
      assert (J':=@close_tc_fv_tc_upper C1 Y).
      clear - J J'. fsetdec.
     
  Case "contexting_tapp".
    apply dnotin_fv_wf with (X:=X) in H; auto.

  Case "contexting_bang".
    apply IHHctx; auto.

  Case "contexting_let1".
    pick fresh x.
    assert (x `notin` L) as J. auto.
    apply H in J.
    apply typing_fv_te_upper' in J; auto.
    rewrite <- (open_ee_fv_te_eq e2 x) in J.
    simpl in J. auto.

  Case "contexting_let2_free".
    pick fresh x.
    assert (x `notin` L) as J. auto.
    apply H1 with (X:=X) in J; auto.
    rewrite (open_ec_fv_tc_eq C2 x) in J.
    apply typing_fv_te_upper' in H; auto.

  Case "contexting_let2_capture".
    rewrite <- fv_tc_close_ec.
    apply typing_fv_te_upper' in H; auto.
    assert (uniq E') as UniqE'.
      apply contexting_regular in Hctx. decompose [and] Hctx; auto.
    rewrite env_remove_bind_typ_ddom in H; auto.
    rewrite env_remove_bind_typ_ddom in H4; auto.

  Case "contexting_apair1".
    apply typing_fv_te_upper' in H; auto.

  Case "contexting_apair2".
    apply typing_fv_te_upper' in H; auto.

  Case "contexting_fst".
    apply IHHctx; auto.

  Case "contexting_snd".
    apply IHHctx; auto.
Qed.

Lemma contexting_gdom_sub : forall E D T C E' D' T',
  contexting E D T C E' D' T' ->
  AtomSetImpl.diff (gdom_env E) (cv_ec C) [<=] gdom_env E'.
Proof.
  intros E D T C E' D' T' Hctx.
  (contexting_cases (induction Hctx) Case); intros; simpl in *.
  Case "contexting_hole".
    fsetdec.
  Case "contexting_abs_free".
    pick fresh x.
    assert (x `notin` L) as J. auto.
    apply H1 in J. 
    unfold open_ec in J.
    rewrite cv_ec_open_ec_rec in J.
    assert (x `notin` gdom_env E) as Sub. 
      apply dom__gdom; auto.
    clear - J Sub. fsetdec.
  Case "contexting_abs_capture".
    unfold close_ec. rewrite cv_ec_close_ec_rec.
    clear - H1 IHHctx. fsetdec.
  Case "contexting_app1".
    fsetdec.
  Case "contexting_app2".
    fsetdec.
  Case "contexting_tabs_free".
    pick fresh X.
    assert (X `notin` L) as J. auto.
    apply H0 in J. 
    unfold open_tc in J.
    rewrite cv_ec_open_tc_rec in J.
    assert (X `notin` gdom_env E) as Sub.
      apply dom__gdom; auto.
    clear - J Sub. fsetdec.
  Case "contexting_tabs_capture".
    unfold close_tc. rewrite cv_ec_close_tc_rec.
    rewrite env_remove_bind_kn_gdom; auto.
      clear - H0 IHHctx. fsetdec.
      apply contexting_regular in Hctx. decompose [and] Hctx; auto.
  Case "contexting_tapp".
    fsetdec.
  Case "contexting_bang".
    fsetdec.
  Case "contexting_let1".
    fsetdec.
  Case "contexting_let2_free".
    pick fresh x.
    assert (x `notin` L) as J. auto.
    apply H1 in J. 
    unfold open_ec in J.
    rewrite cv_ec_open_ec_rec in J.
    assert (x `notin` gdom_env E) as Sub. 
      apply dom__gdom; auto.
    clear - J Sub. fsetdec.
  Case "contexting_let2_capture".
    unfold close_ec. rewrite cv_ec_close_ec_rec.
    rewrite env_remove_bind_typ_gdom; auto.
      clear - H1 IHHctx. fsetdec.
      apply contexting_regular in Hctx. decompose [and] Hctx; auto.
  Case "contexting_apair1".
    fsetdec.
  Case "contexting_apair2".
    fsetdec.
  Case "contexting_fst".
    fsetdec.
  Case "contexting_snd".
    fsetdec.
Qed.

Lemma contexting_plugC_contexting : forall E D T C1 E' D' T' C2 E'' D'' T'',
  contexting E D T C1 E' D' T' ->
  contexting E' D' T' C2 E'' D'' T'' ->
  disjdom (cv_ec C1) (cv_ec C2 `union` fv_ec C2) ->
  contexting E D T (plugC C2 C1) E'' D'' T''.
Proof.
  intros E D T C1 E' D' T' C2 E'' D'' T'' Hcontexting1 Hcontexting2 Disj.
  generalize dependent C1.
  generalize dependent E.
  generalize dependent D.
  generalize dependent T.
  (contexting_cases (induction Hcontexting2) Case); intros; simpl in *; eauto.
  Case "contexting_abs_free".
    apply contexting_abs_free with (L:=L `union` cv_ec C1 `union` cv_ec C0); auto.
      intros x xn.
      assert (x `notin` L) as xnL. auto.
      apply H1 with (C2:=open_ec (shift_ec C0) x) (D0:=D0) (E0:=E0) (T0:=T0) in xnL; auto.
        rewrite open_ec_plugC; auto.
          eapply disjdom_app_l; auto.
          split; simpl.
            apply disjdom_one_2; auto.
            apply disjdom_nil_1.

        unfold shift_ec.
        rewrite <- shift_ec_rec_context; auto.
          unfold open_ec.
          rewrite <- open_ec_rec_context; auto.

        apply disjdom_app_r in Disj. destruct Disj as [Disj1 Disj2].
        eapply disjdom_app_r.
        split.
          apply disjdom_sym_1.
          apply disjdom_eq with (D1:=cv_ec C0).
            apply disjdom_sub with (D1:=cv_ec C1).
              apply disjdom_sym_1; auto.
              unfold open_ec. rewrite cv_ec_open_ec_rec. fsetdec. 
            unfold open_ec. rewrite cv_ec_open_ec_rec. 
            unfold shift_ec. rewrite <- cv_ec_shift_ec_rec. fsetdec.

          apply disjdom_sym_1.
          apply disjdom_sub with (D1:= {{x}} `union`  fv_ec C1).
            apply disjdom_eq with (D1:=cv_ec C0).
              eapply disjdom_app_r.
              split; auto.
                apply disjdom_one_2; auto.
              unfold open_ec. rewrite cv_ec_open_ec_rec. 
              unfold shift_ec. rewrite <- cv_ec_shift_ec_rec. fsetdec.
            assert (J:=@open_ec_fv_ec_upper C1 x).
            simpl in J. clear - J. fsetdec.

  Case "contexting_abs_capture".
    unfold close_ec.
    rewrite <- close_ec_rec_plugC; auto.
    apply contexting_abs_capture; auto.
      rewrite cv_ec_plugC.
      unfold shift_ec. rewrite <- cv_ec_shift_ec_rec.
      assert (y `notin` cv_ec C0) as ynC0.
        apply disjdom_one_1.
        apply disjdom_sym_1.
        apply disjdom_sub with (D1:=({{y}} `union` cv_ec (close_ec C1 y)) `union` fv_ec (close_ec C1 y)); auto.
          fsetdec.
      apply contexting_gdom_sub in Hcontexting1.
      clear - Hcontexting1 ynC0 H1.  
      fsetdec.
 
      apply IHHcontexting2 with (C2:=shift_ec C0) (D0:=D0) (E0:=E0) (T0:=T0); auto.
        unfold shift_ec.
        rewrite <- shift_ec_rec_context; auto.

        apply disjdom_app_r in Disj. destruct Disj as [Disj1 Disj2].
        eapply disjdom_app_r.
        unfold shift_ec. rewrite <- shift_ec_rec_context; auto. 
        split.
          apply disjdom_sym_1.
          apply disjdom_sub with (D1:=union {{y}} (cv_ec (close_ec C1 y))); auto.
            apply disjdom_sym_1; auto.
            unfold close_ec. rewrite cv_ec_close_ec_rec. fsetdec.
          apply disjdom_sym_1.
          apply disjdom_sub with (D1:=fv_ec (close_ec C1 y) `union` {{y}}).
            eapply disjdom_app_r.
            split; auto.
             apply disjdom_sym_1.
             apply disjdom_sub with (D1:= {{y}} `union` cv_ec (close_ec C1 y)).
               apply disjdom_sym_1; auto.
               fsetdec.
            apply close_ec_fv_ec_lower.

  Case "contexting_app1".
    apply contexting_app1 with (T1':=T1') (D1':=D1') (D2':=D2'); auto.
      apply IHHcontexting2; auto.
        apply disjdom_sub with (D1:=union (cv_ec C1) (union (fv_ec C1) (fv_ee e2))); auto.
          fsetdec.

      apply contexting_lin_sub in Hcontexting1.
      assert (disjdom (cv_ec C0) (fv_ee e2)) as J. 
        clear - Disj.
        apply disjdom_sub with (D1:=union (cv_ec C1) (union (fv_ec C1) (fv_ee e2))); auto.
          fsetdec.
      clear - Hcontexting1 J H1.
      destruct J as [J1 J2].
      destruct H1 as [J3 J4].
      split; intros x J.
        assert (J':=J).
        apply J2 in J.
        apply J3 in J'.
        clear - Hcontexting1 J J'.
        fsetdec.
        
        destruct (in_dec x (cv_ec C0)) as [J5 | J5]; auto.

  Case "contexting_app2".
    apply contexting_app2 with (T1':=T1') (D1':=D1') (D2':=D2'); auto.
      apply IHHcontexting2; auto.
        apply disjdom_sub with (D1:=union (cv_ec C2) (union (fv_ee e1) (fv_ec C2))); auto.
          fsetdec.

      apply contexting_lin_sub in Hcontexting1.
      assert (disjdom (cv_ec C1) (fv_ee e1)) as J. 
        clear - Disj.
        apply disjdom_sub with (D1:=union (cv_ec C2) (union (fv_ee e1) (fv_ec C2))); auto.
          fsetdec.
      clear - Hcontexting1 J H1.
      destruct J as [J1 J2].
      destruct H1 as [J3 J4].
      split; intros x J.
        assert (J':=J).
        apply J2 in J.
        apply J3 in J'.
        clear - Hcontexting1 J J'.
        fsetdec.
        
        destruct (in_dec x (cv_ec C1)) as [J5 | J5]; auto.

  Case "contexting_tabs_free".
    apply contexting_tabs_free with (L:=L `union` cv_ec C1); auto.
      intros X Xn.
      assert (X `notin` L) as XnL. auto.
      apply H0 with (C2:=open_tc (shift_tc C0) X) (D0:=D0) (E0:=E0) (T0:=T0) in XnL; auto.
        rewrite open_tc_plugC; auto.
          apply disjdom_one_2; auto.
        unfold shift_tc. rewrite <- shift_tc_rec_context; auto.
        unfold open_tc. rewrite <- open_tc_rec_context; auto.
        
        apply disjdom_eq with (D1:=cv_ec C0).
          apply disjdom_sub with (D1:=cv_ec C1 `union` fv_ec C1); auto.
            unfold open_tc. rewrite cv_ec_open_tc_rec. rewrite open_tc_rec_fv_ec_eq.  fsetdec.
          unfold open_tc. rewrite cv_ec_open_tc_rec. 
          unfold shift_tc. rewrite <- cv_ec_shift_tc_rec. fsetdec.

  Case "contexting_tabs_capture".
    unfold close_tc.
    rewrite <- close_tc_rec_plugC; auto.
    apply contexting_tabs_capture; auto.
      rewrite cv_ec_plugC.
      unfold shift_tc. rewrite <- cv_ec_shift_tc_rec.
      assert (Y `notin` cv_ec C0) as YnC0.
        apply disjdom_one_1.
        apply disjdom_sym_1.
        apply disjdom_sub with (D1:=({{Y}} `union` cv_ec (close_tc C1 Y)) `union` fv_ec (close_tc C1 Y)); auto.
          fsetdec.
      auto.
     
      apply IHHcontexting2 with (C2:=shift_tc C0) (D0:=D0) (E0:=E0) (T0:=T0); auto.
        unfold shift_tc.
        rewrite <- shift_tc_rec_context; auto.

        apply disjdom_eq with (D1:=cv_ec C0).
          apply disjdom_sub with (D1:=({{Y}} `union` cv_ec (close_tc C1 Y)) `union` fv_ec (close_tc C1 Y)); auto.
            unfold close_tc. rewrite cv_ec_close_tc_rec. 
            rewrite <- fv_ec_close_tc_rec. fsetdec.
          unfold shift_tc. rewrite <- cv_ec_shift_tc_rec. fsetdec.

  Case "contexting_bang".
    apply contexting_bang; auto.

  Case "contexting_let1".
    apply contexting_let1 with (L:=L `union` cv_ec C1 `union` cv_ec C0) (T1':=T1') (D1':=D1') (D2':=D2'); auto.
      apply IHHcontexting2; auto.
        apply disjdom_sub with (D1:=union (cv_ec C1) (union (fv_ec C1) (fv_ee e2))); auto.
          fsetdec.

      intros x xn. 
      assert (x `notin` L) as xnL. auto.
      apply H in xnL. auto.

      apply contexting_lin_sub in Hcontexting1.
      assert (disjdom (cv_ec C0) (fv_ee e2)) as J. 
        clear - Disj.
        apply disjdom_sub with (D1:=union (cv_ec C1) (union (fv_ec C1) (fv_ee e2))); auto.
          fsetdec.
      clear - Hcontexting1 J H1.
      destruct J as [J1 J2].
      destruct H1 as [J3 J4].
      split; intros x J.
        assert (J':=J).
        apply J2 in J.
        apply J3 in J'.
        clear - Hcontexting1 J J'.
        fsetdec.
        
        destruct (in_dec x (cv_ec C0)) as [J5 | J5]; auto.

  Case "contexting_let2_free".
    apply contexting_let2_free with (L:=L `union` cv_ec C1 `union` cv_ec C2) (T1':=T1') (D1':=D1') (D2':=D2'); auto.
      intros x xn.
      assert (x `notin` L) as xnL. auto.
      apply H1 with (C1:=open_ec (shift_ec C1) x) (D0:=D0) (E0:=E0) (T0:=T0) in xnL; auto.
        rewrite open_ec_plugC; auto.
          eapply disjdom_app_l; auto.
          split; simpl.
            apply disjdom_one_2; auto.
            apply disjdom_nil_1.

        unfold shift_ec.
        rewrite <- shift_ec_rec_context; auto.
        unfold open_ec.
        rewrite <- open_ec_rec_context; auto.

        apply disjdom_app_r in Disj. destruct Disj as [Disj1 Disj2].
        eapply disjdom_app_r.
        split.
          apply disjdom_sym_1.
          apply disjdom_eq with (D1:=cv_ec C1).
            apply disjdom_sub with (D1:=cv_ec C2).
              apply disjdom_sym_1; auto.
              unfold open_ec. rewrite cv_ec_open_ec_rec. fsetdec. 
            unfold open_ec. rewrite cv_ec_open_ec_rec. 
            unfold shift_ec. rewrite <- cv_ec_shift_ec_rec. fsetdec.

          apply disjdom_sym_1.
          apply disjdom_sub with (D1:= {{x}} `union`  fv_ec C2).
            apply disjdom_eq with (D1:=cv_ec C1).
              eapply disjdom_app_r.
              split.
                apply disjdom_one_2; auto.

                apply disjdom_sym_1.
                apply disjdom_sub with (D1:= fv_ee e1 `union`  fv_ec C2).
                  apply disjdom_sym_1; auto.
                   fsetdec.
              unfold open_ec. rewrite cv_ec_open_ec_rec. 
              unfold shift_ec. rewrite <- cv_ec_shift_ec_rec. fsetdec.
            assert (J:=@open_ec_fv_ec_upper C2 x).
            simpl in J. clear - J. fsetdec.

      apply contexting_lin_sub in Hcontexting1.
      assert (disjdom (cv_ec C1) (fv_ee e1)) as J. 
        clear - Disj.
        apply disjdom_sub with (D1:=union (cv_ec C2) (union (fv_ee e1) (fv_ec C2))); auto.
          fsetdec.
      clear - Hcontexting1 J H3.
      destruct J as [J1 J2].
      destruct H3 as [J3 J4].
      split; intros x J.
        assert (J':=J).
        apply J2 in J.
        apply J3 in J'.
        clear - Hcontexting1 J J'.
        fsetdec.
        
        destruct (in_dec x (cv_ec C1)) as [J5 | J5]; auto.

  Case "contexting_let2_capture".
    unfold close_ec.
    rewrite <- close_ec_rec_plugC; auto.
    apply contexting_let2_capture with (T1':=T1') (D1':=D1') (D2':=D2'); auto.
      rewrite cv_ec_plugC.
      unfold shift_ec. rewrite <- cv_ec_shift_ec_rec.
      assert (y `notin` cv_ec C1) as ynC1.
        apply disjdom_one_1.
        apply disjdom_sym_1.
        apply disjdom_sub with (D1:=({{y}} `union` cv_ec (close_ec C2 y)) `union` fv_ee e1 `union` fv_ec (close_ec C2 y)); auto.
          fsetdec.
      apply contexting_lin_sub in Hcontexting1.
      clear - Hcontexting1 ynC1 H1. 
      fsetdec.
     
      apply IHHcontexting2 with (C1:=shift_ec C1) (D0:=D0) (E0:=E0) (T0:=T0); auto.
        unfold shift_ec.
        rewrite <- shift_ec_rec_context; auto.

        apply disjdom_app_r in Disj. destruct Disj as [Disj1 Disj2].
        eapply disjdom_app_r.
        unfold shift_ec. rewrite <- shift_ec_rec_context; auto. 
        split.
          apply disjdom_sym_1.
          apply disjdom_sub with (D1:=union {{y}} (cv_ec (close_ec C2 y))); auto.
            apply disjdom_sym_1; auto.
            unfold close_ec. rewrite cv_ec_close_ec_rec. fsetdec.
          apply disjdom_sym_1.
          apply disjdom_sub with (D1:={{y}} `union` fv_ee e1 `union` fv_ec (close_ec C2 y)).
            eapply disjdom_app_r.
            split; auto.
             apply disjdom_sym_1.
             apply disjdom_sub with (D1:= {{y}} `union` cv_ec (close_ec C2 y)).
               apply disjdom_sym_1; auto.
               fsetdec.
            assert (J:=@close_ec_fv_ec_lower C2 y). fsetdec.

      apply contexting_lin_sub in Hcontexting1.
      assert (disjdom (cv_ec C1) (fv_ee e1)) as J. 
        clear - Disj.
        apply disjdom_sub with (D1:=union (union {{y}} (cv_ec (close_ec C2 y))) (union (fv_ee e1) (fv_ec (close_ec C2 y)))); auto.
          fsetdec.
      clear - Hcontexting1 J H3.
      destruct J as [J1 J2].
      destruct H3 as [J3 J4].
      split; intros x J.
        assert (J':=J).
        apply J2 in J.
        apply J3 in J'.
        clear - Hcontexting1 J J'.
        fsetdec.
        
        destruct (in_dec x (cv_ec C1)) as [J5 | J5]; auto.

  Case "contexting_apair1".
    apply contexting_apair1; auto.
      apply IHHcontexting2; auto.
        apply disjdom_sub with (D1:=union (cv_ec C1) (union (fv_ec C1) (fv_ee e2))); auto.
          fsetdec.

  Case "contexting_apair2".
    apply contexting_apair2; auto.
      apply IHHcontexting2; auto.
        apply disjdom_sub with (D1:=union (cv_ec C2) (union (fv_ee e1) (fv_ec C2))); auto.
          fsetdec.
Qed.

Lemma F_observational_eq__congr_app : forall E lE1 lE2 lE e1 e1' e2 e2' t1 t2,
   F_observational_eq E lE1 e1 e1' (typ_arrow t1 t2) ->
   F_observational_eq E lE2 e2 e2' t1 -> 
   lenv_split E lE1 lE2 lE ->
   F_observational_eq E lE (exp_app e1 e2) (exp_app e1' e2') t2.
Proof.
  intros E lE1 lE2 lE e1 e1' e2 e2' t1 t2 Heq1 Heq2 Split.
  destruct Heq1 as [Typ1 [Typ1' Heq1]].
  destruct Heq2 as [Typ2 [Typ2' Heq2]].
  split; eauto.
  split; eauto.
    intros C Hcontext.

    assert (contexting E lE1 (typ_arrow t1 t2) (plugC C (ctx_app1 ctx_hole e2)) nil nil Two) as Hcontexting1.
      apply contexting_plugC_contexting with (E':=E) (D':=lE) (T':=t2); auto.
        apply contexting_app1 with (T1':=t1) (D1':=lE1) (D2':=lE2); auto.
          assert (J:=Typ2).
          apply typing_fv_ee_upper in Typ2.
          apply disjdom_sym_1.
          apply disjdom_sub with (D1:=union (dom E) (dom lE2)); auto.
          eapply disjdom_app_r.
          split.
            apply disjoint__disjdom.
            apply disjoint_split_left in Split; auto.

            apply disjoint__disjdom.
            apply disjoint_lenv_split' in Split. auto.
        simpl. apply disjdom_nil_1.
    apply Heq1 in Hcontexting1.
    rewrite plug_plugC in Hcontexting1; try solve [simpl; apply disjdom_sym_1; apply disjdom_nil_1].
    rewrite plug_plugC in Hcontexting1; try solve [simpl; apply disjdom_sym_1; apply disjdom_nil_1].
    simpl in Hcontexting1.

    assert (contexting E lE2 t1 (plugC C (ctx_app2 e1' ctx_hole)) nil nil Two) as Hcontexting2.
      apply contexting_plugC_contexting with (E':=E) (D':=lE) (T':=t2); auto.
        apply contexting_app2 with (T1':=t1) (D1':=lE1) (D2':=lE2); auto.
          assert (J:=Typ1').
          apply typing_fv_ee_upper in Typ1'.
          apply disjdom_sym_1.
          apply disjdom_sub with (D1:=union (dom E) (dom lE1)); auto.
          eapply disjdom_app_r.
          split.
            apply disjoint__disjdom.
            apply disjoint_split_right in Split; auto.

            apply disjoint__disjdom.
            apply disjoint_lenv_split' in Split. auto.
        simpl. apply disjdom_nil_1.
    apply Heq2 in Hcontexting2.
    rewrite plug_plugC in Hcontexting2; try solve [simpl; apply disjdom_sym_1; apply disjdom_nil_1].
    rewrite plug_plugC in Hcontexting2; try solve [simpl; apply disjdom_sym_1; apply disjdom_nil_1].
    simpl in Hcontexting2.

    apply Kleene_eq__trans with (e':=plug C (exp_app e1' e2)); auto.
Qed.

Lemma F_observational_eq__congr_tapp : forall E lE e1 e1' t2 t,
   F_observational_eq E lE e1 e1' (typ_all t) ->
   wf_typ E t2 ->
   F_observational_eq E lE (exp_tapp e1 t2) (exp_tapp e1' t2) (open_tt t t2).
Proof.
  intros E lE e1 e1' t2 t Heq Wft2.
  destruct Heq as [Typ [Typ' Heq]].
  split; eauto.
  split; eauto.
    intros C Hcontext.
    assert (contexting E lE (typ_all t) (plugC C (ctx_tapp ctx_hole t2)) nil nil Two) as Hcontexting1.
      apply contexting_plugC_contexting with (E':=E) (D':=lE) (T':=open_tt t t2); auto.
        simpl. apply disjdom_nil_1.
    apply Heq in Hcontexting1.
    rewrite plug_plugC in Hcontexting1; try solve [simpl; apply disjdom_sym_1; apply disjdom_nil_1].
    rewrite plug_plugC in Hcontexting1; try solve [simpl; apply disjdom_sym_1; apply disjdom_nil_1].
    simpl in Hcontexting1. auto.
Qed.

Lemma F_observational_eq__congr_abs : forall E lE e1 e1' t1 t2 L,
   wf_typ E t1 ->
   (forall x, x `notin` L ->  F_observational_eq E ([(x, lbind_typ t1)]++lE) (open_ee e1 x) (open_ee e1' x) t2) ->
   F_observational_eq E lE (exp_abs t1 e1) (exp_abs t1 e1') (typ_arrow t1 t2).
Proof.
  intros E lE e1 e1' t1 t2 L Wft H1.
  split.
    apply typing_abs with (L:=L `union` dom E `union` dom lE); auto.
    intros x xn.
    assert (x `notin` L) as xnL. auto.
    apply H1 in xnL.
    destruct xnL as [Typ [Typ' Heq]]. auto.
  split.
    apply typing_abs with (L:=L  `union` dom E `union` dom lE); auto.
    intros x xn.
    assert (x `notin` L) as xnL. auto.
    apply H1 in xnL.
    destruct xnL as [Typ [Typ' Heq]]. auto.
    
    intros C Hcontexting.
    pick fresh x.
    assert (x `notin` L) as xnL. auto.
    apply H1 in xnL.
    destruct xnL as [Typ [Typ' Heq]].
    assert (contexting E ([(x, lbind_typ t1)]++lE) t2 (plugC C (ctx_abs_capture x t1 ctx_hole)) nil nil Two) as Hcontexting1.
      apply contexting_plugC_contexting with (E':=E) (D':=lE) (T':=typ_arrow t1 t2); auto.     
        assert (
          contexting E ([(x, lbind_typ t1)]++lE) t2 (ctx_abs_capture x t1 (close_ec ctx_hole x)) E (lenv_remove (x, lbind_typ t1) ([(x, lbind_typ t1)]++lE)) (typ_arrow t1 t2) =
          contexting E ([(x, lbind_typ t1)]++lE) t2 (ctx_abs_capture x t1 ctx_hole) E lE (typ_arrow t1 t2)
          ) as EQ.
          simpl.
          destruct (eq_lbinding_dec (x, lbind_typ t1) (x, lbind_typ t1)).
             rewrite lenv_remove_kind_notin; auto.
             contradict n; auto.
        rewrite <- EQ.
        apply contexting_abs_capture; auto.
          rewrite dom__ddom_gdom in Fr. auto.

        simpl. apply disjdom_eq with (D1:={{x}}). 
          apply disjdom_one_2; auto.
           clear. fsetdec.

    apply Heq in Hcontexting1.
    rewrite plug_plugC in Hcontexting1;
      try solve [simpl; eapply disjdom_app_r; 
        split; [apply disjdom_one_2; auto | apply disjdom_nil_1]].
    rewrite plug_plugC in Hcontexting1;
      try solve [simpl; eapply disjdom_app_r; 
        split; [apply disjdom_one_2; auto | apply disjdom_nil_1]].
    simpl in Hcontexting1.
    rewrite <- shift_ee_expr in Hcontexting1; auto.
    rewrite <- shift_ee_expr in Hcontexting1; auto.
    rewrite open_close_ee__id in Hcontexting1; auto.
    rewrite open_close_ee__id in Hcontexting1; auto.
Qed.

Lemma F_observational_eq__congr_tabs : forall E lE e1 e1' t1 L,
   (forall X, X `notin` L ->  wf_typ ([(X, bind_kn)]++E) (open_tt t1 X)) ->
   (forall X, 
     X `notin` L ->  
     F_observational_eq ([(X, bind_kn)]++E) lE 
       (open_te e1 X) (open_te e1' X) (open_tt t1 X)
   ) ->
   F_observational_eq E lE
     (exp_tabs e1) 
     (exp_tabs e1')
     (typ_all t1).
Proof.
  intros E lE e1 e1' t1 L Wft H1.
  split.
    apply typing_tabs with (L:=L `union` dom E `union` dom lE); auto.
      intros X0 X0n.
      unfold open_te. unfold open_tt.
      assert (X0 `notin` L) as X0nL. auto.
      assert (J1 := @H1 X0 X0nL).
      destruct J1 as [Typ0 [Typ0' Heq0]].
      unfold open_tt in Typ0. unfold open_te in Typ0.
      auto.

  split.
    apply typing_tabs with (L:=L `union` dom E `union` dom lE); auto.
      intros X0 X0n.
      unfold open_te. unfold open_tt. 
     assert (X0 `notin` L) as X0nL. auto.
     assert (J1 := @H1 X0 X0nL).
     destruct J1 as [Typ0 [Typ0' Heq0]].
     unfold open_tt in Typ0. unfold open_te in Typ0.
     auto.

    intros C Hcontexting.
    pick fresh X.
    assert (X `notin` L) as XnL. auto.
    assert (J1 := @H1 X XnL).
    destruct J1 as [Typ [Typ' Heq]].
    assert (contexting ([(X, bind_kn)]++E) lE 
                     (open_tt t1 X)
                     (plugC C (ctx_tabs_capture X ctx_hole)) nil nil Two) as Hcontexting1.
      apply contexting_plugC_contexting with (E':=E) (D':=lE) (T':=typ_all t1); auto.     
        assert (
          contexting ([(X, bind_kn)]++E) lE (open_tt t1 X) (ctx_tabs_capture X (close_tc ctx_hole X)) (env_remove (X, bind_kn) ([(X, bind_kn)]++E)) lE (typ_all (close_tt (open_tt t1 X) X)) =
          contexting ([(X, bind_kn)]++E) lE (open_tt t1 X )(ctx_tabs_capture X ctx_hole) E lE (typ_all t1)
          ) as EQ.
          unfold close_tc. unfold close_tt. simpl.
          destruct (eq_binding_dec (X, bind_kn) (X, bind_kn)).
             rewrite env_remove_notin; auto.
             unfold open_tt.
             rewrite open_close_tt_rec__id; auto. 

             contradict n; auto.
        rewrite <- EQ. clear EQ.
        apply contexting_tabs_capture; auto.
          simpl.
          destruct (eq_binding_dec (X, bind_kn) (X, bind_kn)).
            rewrite env_remove_notin; auto.
            apply contexting_regular in Hcontexting.
            decompose [and] Hcontexting; auto.

            contradict n; auto.

        simpl. 
        apply disjdom_eq with (D1:={{X}}). 
            eapply disjdom_app_r.
            split.
              apply disjdom_sym_1.
              apply disjdom_one_2; auto.

              apply disjdom_sym_1.
              apply disjdom_one_2; auto.
           clear. fsetdec.

    apply Heq in Hcontexting1.
    rewrite plug_plugC in Hcontexting1;
      try solve [simpl; eapply disjdom_app_r; 
        split; [apply disjdom_one_2; auto | 
                     apply disjdom_nil_1]
        ].
    rewrite plug_plugC in Hcontexting1;
      try solve [simpl; eapply disjdom_app_r; 
        split; [apply disjdom_one_2; auto | 
                     apply disjdom_nil_1]
        ].
    simpl in Hcontexting1.
    rewrite <- shift_te_expr in Hcontexting1; auto.
    rewrite <- shift_te_expr in Hcontexting1; auto.
    unfold close_te in Hcontexting1.
    unfold open_te in Hcontexting1.
    rewrite open_close_te_rec__id in Hcontexting1; auto.
    rewrite open_close_te_rec__id in Hcontexting1; auto.
Qed.

Lemma F_observational_eq__congr_tabs_abs : forall E lE e1 e1' t1 t2 L,
   (forall X, X `notin` L ->  wf_typ ([(X, bind_kn)]++E) (open_tt t1 X)) ->
   (forall X x, 
     X `notin` L ->  
     x `notin` L `union` {{X}} ->  
     F_observational_eq ([(X, bind_kn)]++E) ([(x, lbind_typ (open_tt t1 X))]++lE) 
       (open_ee (open_te e1 X) x) (open_ee (open_te e1' X) x) (open_tt t2 X)
   ) ->
   F_observational_eq E lE
     (exp_tabs (exp_abs t1 e1)) 
     (exp_tabs (exp_abs t1 e1')) 
     (typ_all (typ_arrow t1 t2)).
Proof.
  intros E lE e1 e1' t1 t2 L Wft H1.
  split.
    apply typing_tabs with (L:=L `union` dom E `union` dom lE); auto.
      intros X0 X0n.
      unfold open_te. unfold open_tt. simpl. simpl_env.
      apply typing_abs with (L:=L `union` dom E `union` dom lE `union` {{X0}}); auto.
        assert (X0 `notin` L) as X0nL. auto.
        assert (J2 := @Wft X0 X0nL). auto.

        intros x0 x0n.
        assert (X0 `notin` L) as X0nL. auto.
        assert (x0 `notin` L `union` {{X0}}) as x0nL. auto.
        assert (J1 := @H1 X0 x0 X0nL x0nL).
        destruct J1 as [Typ0 [Typ0' Heq0]].
        unfold open_tt in Typ0. unfold open_te in Typ0. unfold open_ee in Typ0. 
        simpl in Typ0. simpl_env in Typ0. unfold open_ee. auto.

  split.
    apply typing_tabs with (L:=L `union` dom E `union` dom lE); auto.
      intros X0 X0n.
      unfold open_te. unfold open_tt. simpl. simpl_env.
      apply typing_abs with (L:=L `union` dom E `union` dom lE `union` {{X0}}); auto.
        assert (X0 `notin` L) as X0nL. auto.
        assert (J2 := @Wft X0 X0nL). auto.

        intros x0 x0n.
        assert (X0 `notin` L) as X0nL. auto.
        assert (x0 `notin` L `union` {{X0}}) as x0nL. auto.
        assert (J1 := @H1 X0 x0 X0nL x0nL).
        destruct J1 as [Typ0 [Typ0' Heq0]].
        unfold open_tt in Typ0. unfold open_te in Typ0. unfold open_ee in Typ0. 
        simpl in Typ0. simpl_env in Typ0. unfold open_ee. auto.

    intros C Hcontexting.
    pick fresh X.
    pick fresh x.
    assert (X `notin` L) as XnL. auto.
    assert (x `notin` L `union` {{X}}) as xnL. auto.
    assert (J1 := @H1 X x XnL xnL).
    destruct J1 as [Typ [Typ' Heq]].
    assert (contexting ([(X, bind_kn)]++E) ([(x, lbind_typ (open_tt t1 X))]++lE)
                     (open_tt t2 X)
                     (plugC C (ctx_tabs_capture X (ctx_abs_capture x (close_tt (open_tt t1 X) X) ctx_hole))) nil nil Two) as Hcontexting1.
      apply contexting_plugC_contexting with (E':=E) (D':=lE) (T':=typ_all (typ_arrow t1 t2)); auto.     
        assert (
          contexting ([(X, bind_kn)]++E) ([(x, lbind_typ (open_tt t1 X))]++lE) (open_tt t2 X) (ctx_tabs_capture X (close_tc (ctx_abs_capture x (open_tt t1 X) ctx_hole) X)) (env_remove (X, bind_kn) ([(X, bind_kn)]++E)) lE (typ_all (close_tt (open_tt (typ_arrow t1 t2) X) X)) =
          contexting ([(X, bind_kn)]++E) ([(x, lbind_typ (open_tt t1 X))]++lE) (open_tt t2 X )(ctx_tabs_capture X (ctx_abs_capture x (close_tt (open_tt t1 X) X) ctx_hole)) E lE (typ_all (typ_arrow t1 t2))
          ) as EQ.
          unfold close_tc. unfold close_tt. simpl.
          destruct (eq_binding_dec (X, bind_kn) (X, bind_kn)).
             rewrite env_remove_notin; auto.
             rewrite open_close_tt_rec__id; auto. 
             rewrite open_close_tt_rec__id; auto.
             rewrite <- close_tt_rec_typ; auto.

             contradict n; auto.
        rewrite <- EQ. clear EQ.
        apply contexting_tabs_capture; auto.
          assert (
            contexting ([(X, bind_kn)]++E) ([(x, lbind_typ (open_tt t1 X))]++lE) (open_tt t2 X) (ctx_abs_capture x (open_tt t1 X) (close_ec ctx_hole x)) ([(X, bind_kn)]++E) (lenv_remove (x, lbind_typ  (open_tt t1 X)) ([(x, lbind_typ (open_tt t1 X))]++lE)) (typ_arrow (open_tt t1 X) (open_tt t2 X)) =
            contexting ([(X, bind_kn)]++E) ([(x, lbind_typ (open_tt t1 X))]++lE) (open_tt t2 X) (ctx_abs_capture x (open_tt t1 X) ctx_hole) ([(X, bind_kn)]++E) lE (open_tt (typ_arrow t1 t2) X)
            ) as EQ.
            simpl.        
            destruct (eq_lbinding_dec (x, lbind_typ (open_tt t1 X)) (x, lbind_typ (open_tt t1 X))).
              rewrite lenv_remove_kind_notin; auto.
              contradict n; auto.
          rewrite <- EQ. clear EQ.
          apply contexting_abs_capture; auto.
            rewrite dom__ddom_gdom in Fr0. auto.

            simpl.
            destruct (eq_binding_dec (X, bind_kn) (X, bind_kn)).
              rewrite env_remove_notin; auto.
              apply contexting_regular in Hcontexting.
              decompose [and] Hcontexting; auto.

              contradict n; auto.

        simpl. apply disjdom_eq with (D1:={{X}} `union` {{x}}). 
          eapply disjdom_app_l.
          split.
            eapply disjdom_app_r.
            split.
              apply disjdom_sym_1.
              apply disjdom_one_2; auto.

              apply disjdom_sym_1.
              apply disjdom_one_2; auto.
            eapply disjdom_app_r.
            split.
              apply disjdom_sym_1.
              apply disjdom_one_2; auto.

              apply disjdom_sym_1.
              apply disjdom_one_2; auto.
           clear. fsetdec.

    apply Heq in Hcontexting1.
    rewrite plug_plugC in Hcontexting1;
      try solve [simpl; eapply disjdom_app_r; 
        split; [apply disjdom_one_2; auto | 
                     eapply disjdom_app_l;
                     split; [apply disjdom_one_2; auto | 
                                 apply disjdom_nil_1]]
        ].
    rewrite plug_plugC in Hcontexting1;
      try solve [simpl; eapply disjdom_app_r; 
        split; [apply disjdom_one_2; auto | 
                     eapply disjdom_app_l;
                     split; [apply disjdom_one_2; auto | 
                                 apply disjdom_nil_1]]
        ].
    simpl in Hcontexting1.
    rewrite <- shift_te_expr in Hcontexting1; auto.
    rewrite <- shift_te_expr in Hcontexting1; auto.
    unfold shift_ee in Hcontexting1.
    unfold close_te in Hcontexting1.
    rewrite shift_ee_rec__close_te_rec in Hcontexting1; auto.
    rewrite shift_ee_rec__close_te_rec in Hcontexting1; auto.
    rewrite <- shift_ee_rec_expr in Hcontexting1; auto.
    rewrite <- shift_ee_rec_expr in Hcontexting1; auto.
    unfold open_ee in Hcontexting1.
    rewrite close_te_open_ee_rec_commut in Hcontexting1; auto.
    rewrite close_te_open_ee_rec_commut in Hcontexting1; auto.
    unfold open_te in Hcontexting1.
    rewrite open_close_te_rec__id in Hcontexting1; auto.
    rewrite open_close_te_rec__id in Hcontexting1; auto.
    unfold close_ee in Hcontexting1.
    rewrite open_close_ee_rec__id in Hcontexting1; auto.
    rewrite open_close_ee_rec__id in Hcontexting1; auto.
    rewrite open_close_tt__id in Hcontexting1; auto.
Qed.

Lemma F_observational_eq__congr_bang : forall E e1 e1' t1,
   F_observational_eq E lempty e1 e1' t1 ->
   F_observational_eq E lempty (exp_bang e1) (exp_bang e1') (typ_bang t1).
Proof.
  intros E e1 e1' t1 H1.
  destruct H1 as [Typ [Typ' Heq]].
  split; auto.
  split; auto.
    intros C Hcontexting.
    assert (contexting E lempty t1 (plugC C (ctx_bang ctx_hole)) nil nil Two) as Hcontexting1.
      apply contexting_plugC_contexting with (E':=E) (D':=lempty) (T':=typ_bang t1); auto.     
        apply contexting_bang; auto.
          simpl. apply disjdom_nil_1; auto.

    apply Heq in Hcontexting1.
    rewrite plug_plugC in Hcontexting1; 
      try solve [simpl; apply disjdom_sym_1; apply disjdom_nil_1].
    rewrite plug_plugC in Hcontexting1; 
      try solve [simpl; apply disjdom_sym_1; apply disjdom_nil_1].
    simpl in Hcontexting1. auto.
Qed.

Lemma F_observational_eq__congr_fst : forall E lE e1 e1' e2 e2' t1 t2,
   F_observational_eq E lE (exp_apair e1 e2) (exp_apair e1' e2') (typ_with t1 t2) ->
   F_observational_eq E lE e1 e1' t1.
Proof.
  intros E lE e1 e1' e2 e2' t1 t2 Heq.
  destruct Heq as [Typ [Typ' Heq]].
  split.
    inversion Typ; subst; auto.
  split.
    inversion Typ'; subst; auto.

    intros C Hcontext.
    assert (contexting E lE (typ_with t1 t2) (plugC C (ctx_fst ctx_hole)) nil nil Two) as Hcontexting1.
      apply contexting_plugC_contexting with (E':=E) (D':=lE) (T':=t1); auto.
        apply contexting_fst with (T2':=t2); auto.
        simpl. apply disjdom_nil_1.
    apply Heq in Hcontexting1.
    rewrite plug_plugC in Hcontexting1; try solve [simpl; apply disjdom_sym_1; apply disjdom_nil_1].
    rewrite plug_plugC in Hcontexting1; try solve [simpl; apply disjdom_sym_1; apply disjdom_nil_1].
    simpl in Hcontexting1.

    assert (F_observational_eq E lE (exp_fst (exp_apair e1 e2)) e1 t1) as Hctx1.
      apply F_observational_eq__beta.
        apply typing_fst with (T2:=t2); auto.

        inversion Typ; subst.
        apply red_fst_beta; auto.
      
    assert (F_observational_eq E lE (exp_fst (exp_apair e1' e2')) e1' t1) as Hctx1'.
      apply F_observational_eq__beta.
        apply typing_fst with (T2:=t2); auto.

        inversion Typ'; subst.
        apply red_fst_beta; auto.

  destruct Hctx1 as [Typ1 [Typ2 Heq1]].
  destruct Hctx1' as [Typ1' [Typ2' Heq1']].
  
  apply Kleene_eq__trans with (e':=plug C (exp_fst (exp_apair e1 e2))); auto.
    apply Kleene_eq__sym.
    apply Heq1 in Hcontext. auto.

  apply Kleene_eq__trans with (e':=plug C (exp_fst (exp_apair e1' e2'))); auto.
Qed.

Lemma F_observational_eq__congr_snd : forall E lE e1 e1' e2 e2' t1 t2,
   F_observational_eq E lE (exp_apair e1 e2) (exp_apair e1' e2') (typ_with t1 t2) ->
   F_observational_eq E lE e2 e2' t2.
Proof.
  intros E lE e1 e1' e2 e2' t1 t2 Heq.
  destruct Heq as [Typ [Typ' Heq]].
  split.
    inversion Typ; subst; auto.
  split.
    inversion Typ'; subst; auto.

    intros C Hcontext.
    assert (contexting E lE (typ_with t1 t2) (plugC C (ctx_snd ctx_hole)) nil nil Two) as Hcontexting1.
      apply contexting_plugC_contexting with (E':=E) (D':=lE) (T':=t2); auto.
        apply contexting_snd with (T1':=t1); auto.
        simpl. apply disjdom_nil_1.
    apply Heq in Hcontexting1.
    rewrite plug_plugC in Hcontexting1; try solve [simpl; apply disjdom_sym_1; apply disjdom_nil_1].
    rewrite plug_plugC in Hcontexting1; try solve [simpl; apply disjdom_sym_1; apply disjdom_nil_1].
    simpl in Hcontexting1.

    assert (F_observational_eq E lE (exp_snd (exp_apair e1 e2)) e2 t2) as Hctx2.
      apply F_observational_eq__beta.
        apply typing_snd with (T1:=t1); auto.

        inversion Typ; subst.
        apply red_snd_beta; auto.
      
    assert (F_observational_eq E lE (exp_snd (exp_apair e1' e2')) e2' t2) as Hctx2'.
      apply F_observational_eq__beta.
        apply typing_snd with (T1:=t1); auto.

        inversion Typ'; subst.
        apply red_snd_beta; auto.

  destruct Hctx2 as [Typ1 [Typ2 Heq2]].
  destruct Hctx2' as [Typ1' [Typ2' Heq2']].
  
  apply Kleene_eq__trans with (e':=plug C (exp_snd (exp_apair e1 e2))); auto.
    apply Kleene_eq__sym.
    apply Heq2 in Hcontext. auto.

  apply Kleene_eq__trans with (e':=plug C (exp_snd (exp_apair e1' e2'))); auto.
Qed.

Definition F_nobservational_eq E lE e e' t : Prop :=
  typing E lE e t /\
  typing E lE e' t /\
  forall C,
   contexting E lE t C nil nil Two ->
   cbn_ctx C ->
   Kleene_eq (plug C e) (plug C e').

Lemma F_observational_eq__F_nobservational_eq : forall E lE e e' t,
  F_observational_eq E lE e e' t ->
  F_nobservational_eq E lE e e' t.
Proof.
  intros E lE e e' t Hctx.
  destruct Hctx as [Htyp [Htyp' J]].
  split; auto.
Qed.

Lemma F_nobservational_eq__sym : forall E lE e e' t,
  F_nobservational_eq E lE e e' t ->
  F_nobservational_eq E lE e' e t.
Proof.
  intros E lE e e' t Hobservation.
  destruct Hobservation as [Typ [Typ' Hkleene]].
  split; auto.
  split; auto.
    intros C Hcontexting HvC.
    apply Kleene_eq__sym; auto.
Qed.

Lemma F_nobservational_eq__trans : forall E lE e e' e'' t,
  F_nobservational_eq E lE e e' t ->
  F_nobservational_eq E lE e' e'' t ->
  F_nobservational_eq E lE e e'' t.
Proof.
  intros E lE e e' e'' t Hobservation Hobservation'.
  destruct Hobservation as [Typ [Typ' Hkleene]].
  destruct Hobservation' as [_ [Typ'' Hkleene']].
  split; auto.
  split; auto.
    intros C Hcontexting HvC.
    apply Kleene_eq__trans with (e':=plug C e'); auto.
Qed.

Lemma cbn_ctx_plug : forall C C',
  cbn_ctx C ->
  cbn_ctx C' ->
  cbn_ctx (plugC C C').
Proof.
  induction C; intros C' H1 H2; simpl;
    try solve [auto | inversion H1; eauto].
Qed.

Lemma F_nobservational_eq__congr_app : forall E lE1 lE2 lE e1 e1' e2 t1 t2,
   F_nobservational_eq E lE1 e1 e1' (typ_arrow t1 t2) ->
   value e1' ->
   lenv_split E lE1 lE2 lE ->
   typing E lE2 e2 t1 ->
   F_nobservational_eq E lE (exp_app e1 e2) (exp_app e1' e2) t2.
Proof.
  intros E lE1 lE2 lE e1 e1' e2 t1 t2 Heq1 Hv1' Split Typ2.
  destruct Heq1 as [Typ1 [Typ1' Heq1]].
  split; eauto.
  split; eauto.
    intros C Hcontext HvC.

    assert (contexting E lE1 (typ_arrow t1 t2) (plugC C (ctx_app1 ctx_hole e2)) nil nil Two) as Hcontexting1.
      apply contexting_plugC_contexting with (E':=E) (D':=lE) (T':=t2); auto.
        apply contexting_app1 with (T1':=t1) (D1':=lE1) (D2':=lE2); auto.
          assert (J:=Typ2).
          apply typing_fv_ee_upper in Typ2.
          apply disjdom_sym_1.
          apply disjdom_sub with (D1:=union (dom E) (dom lE2)); auto.
          eapply disjdom_app_r.
          split.
            apply disjoint__disjdom.
            apply disjoint_split_left in Split; auto.

            apply disjoint__disjdom.
            apply disjoint_lenv_split' in Split. auto.
        simpl. apply disjdom_nil_1.

    apply Heq1 in Hcontexting1; try solve [apply cbn_ctx_plug; simpl; auto].
    rewrite plug_plugC in Hcontexting1; try solve [simpl; apply disjdom_sym_1; apply disjdom_nil_1].
    rewrite plug_plugC in Hcontexting1; try solve [simpl; apply disjdom_sym_1; apply disjdom_nil_1].
    simpl in Hcontexting1. auto.
Qed.

Lemma F_nobservational_eq__congr_tapp : forall E lE e1 e1' t2 t,
   F_nobservational_eq E lE e1 e1' (typ_all t) ->
   wf_typ E t2 ->
   F_nobservational_eq E lE (exp_tapp e1 t2) (exp_tapp e1' t2) (open_tt t t2).
Proof.
  intros E lE e1 e1' t2 t Heq Wft2.
  destruct Heq as [Typ [Typ' Heq]].
  split; eauto.
  split; eauto.
    intros C Hcontext HvC.
    assert (contexting E lE (typ_all t) (plugC C (ctx_tapp ctx_hole t2)) nil nil Two) as Hcontexting1.
      apply contexting_plugC_contexting with (E':=E) (D':=lE) (T':=open_tt t t2); auto.
        simpl. apply disjdom_nil_1.

    apply Heq in Hcontexting1; try solve [apply cbn_ctx_plug; simpl; eauto using type_from_wf_typ].
    rewrite plug_plugC in Hcontexting1; try solve [simpl; apply disjdom_sym_1; apply disjdom_nil_1].
    rewrite plug_plugC in Hcontexting1; try solve [simpl; apply disjdom_sym_1; apply disjdom_nil_1].
    simpl in Hcontexting1. auto.
Qed.

Lemma F_nobservational_eq__congr_fst : forall E lE e1 e1' e2 e2' t1 t2,
   F_nobservational_eq E lE (exp_apair e1 e2) (exp_apair e1' e2') (typ_with t1 t2) ->
   F_nobservational_eq E lE e1 e1' t1.
Proof.
  intros E lE e1 e1' e2 e2' t1 t2 Heq.
  destruct Heq as [Typ [Typ' Heq]].
  split.
    inversion Typ; subst; auto.
  split.
    inversion Typ'; subst; auto.

    intros C Hcontext HvC.
    assert (contexting E lE (typ_with t1 t2) (plugC C (ctx_fst ctx_hole)) nil nil Two) as Hcontexting1.
      apply contexting_plugC_contexting with (E':=E) (D':=lE) (T':=t1); auto.
        apply contexting_fst with (T2':=t2); auto.
        simpl. apply disjdom_nil_1.

    apply Heq in Hcontexting1; try solve [apply cbn_ctx_plug; simpl; auto].
    rewrite plug_plugC in Hcontexting1; try solve [simpl; apply disjdom_sym_1; apply disjdom_nil_1].
    rewrite plug_plugC in Hcontexting1; try solve [simpl; apply disjdom_sym_1; apply disjdom_nil_1].
    simpl in Hcontexting1.

    assert (F_nobservational_eq E lE (exp_fst (exp_apair e1 e2)) e1 t1) as Hctx1.
      apply F_observational_eq__F_nobservational_eq.
      apply F_observational_eq__beta.
        apply typing_fst with (T2:=t2); auto.

        inversion Typ; subst.
        apply red_fst_beta; auto.
      
    assert (F_nobservational_eq E lE (exp_fst (exp_apair e1' e2')) e1' t1) as Hctx1'.
      apply F_observational_eq__F_nobservational_eq.
      apply F_observational_eq__beta.
        apply typing_fst with (T2:=t2); auto.

        inversion Typ'; subst.
        apply red_fst_beta; auto.

  destruct Hctx1 as [Typ1 [Typ2 Heq1]].
  destruct Hctx1' as [Typ1' [Typ2' Heq1']].
  
  apply Kleene_eq__trans with (e':=plug C (exp_fst (exp_apair e1 e2))); auto.
    apply Kleene_eq__sym.
    apply Heq1 in Hcontext; auto.

  apply Kleene_eq__trans with (e':=plug C (exp_fst (exp_apair e1' e2'))); auto.
Qed.

Lemma F_observational_eq__congr_let : forall E lE1 lE2 lE e1 e1' e2 e2' t1 t2 L,
   F_nobservational_eq E lE1 e1 e1' (typ_bang t1) ->
   (forall x, x `notin` L ->  F_observational_eq ([(x, bind_typ t1)]++E) lE2 (open_ee e2 x) (open_ee e2' x) t2) ->
   lenv_split E lE1 lE2 lE ->
   F_nobservational_eq E lE (exp_let e1 e2) (exp_let e1' e2') t2.
Proof.
  intros E lE1 lE2 lE e1 e1' e2 e2' t1 t2 L Heq1 Heq2 Hsplit.
  destruct Heq1 as [Typ1 [Typ1' Heq1]].
  split.
    apply typing_let with (L:=L `union` dom E `union` dom lE)(D1:=lE1)(D2:=lE2)(T1:=t1); auto.
    intros x xn.
    assert (x `notin` L) as xnL. auto.
    apply Heq2 in xnL.
    destruct xnL as [Typ2 [Typ2' Heq2']]. auto.
  split.
    apply typing_let with (L:=L `union` dom E `union` dom lE)(D1:=lE1)(D2:=lE2)(T1:=t1); auto.
    intros x xn.
    assert (x `notin` L) as xnL. auto.
    apply Heq2 in xnL.
    destruct xnL as [Typ2 [Typ2' Heq2']]. auto.
    
    intros C Hcontexting HnC.

    assert (contexting E lE1 (typ_bang t1) (plugC C (ctx_let1 ctx_hole e2)) nil nil Two) as Hcontexting1.
      apply contexting_plugC_contexting with (E':=E) (D':=lE) (T':=t2); auto.
        apply contexting_let1 with (L:=L `union` dom E `union` dom lE) (T1':=t1) (D1':=lE1) (D2':=lE2); auto.
          intros x0 x0n.
          assert (x0 `notin` L) as x0nL. auto.
          apply Heq2 in x0nL.
          destruct x0nL as [Typ2 [Typ2' Heq2']]; auto.          

          pick fresh x.
          assert (x `notin` L) as xnL. auto.
          apply Heq2 in xnL.
          destruct xnL as [Typ2 [Typ2' Heq2']]; auto.          
          assert (J:=Typ2).
          apply typing_fv_ee_upper in Typ2.
          assert (J1:=@open_ee_fv_ee_lower e2 x).
          assert (fv_ee e2 [<=] dom E `union` dom lE2) as J2.
            simpl in Typ2. destruct_notin.
            clear - Typ2 NotInTac5 NotInTac12 NotInTac9 J1.
            fsetdec.
          apply disjdom_sym_1.
          apply disjdom_sub with (D1:=union (dom E) (dom lE2)); auto.
          eapply disjdom_app_r.
          split.
            apply disjoint__disjdom.
            apply disjoint_split_left in Hsplit; auto.

            apply disjoint__disjdom.
            apply disjoint_lenv_split' in Hsplit. auto.
        simpl. apply disjdom_nil_1.

    apply Heq1 in Hcontexting1; try solve [apply cbn_ctx_plug; simpl; auto].
    rewrite plug_plugC in Hcontexting1; try solve [simpl; apply disjdom_sym_1; apply disjdom_nil_1].
    rewrite plug_plugC in Hcontexting1; try solve [simpl; apply disjdom_sym_1; apply disjdom_nil_1].
    simpl in Hcontexting1.

    pick fresh x.
    assert (x `notin` L) as xnL. auto.
    apply Heq2 in xnL.
    destruct xnL as [Typ2 [Typ2' Heq2']].
    assert (contexting ([(x, bind_typ t1)]++E) lE2 t2 (plugC C (ctx_let2_capture e1' x ctx_hole)) nil nil Two) as Hcontexting2.
      apply contexting_plugC_contexting with (E':=E) (D':=lE) (T':=t2); auto.
        assert (
          contexting ([(x, bind_typ t1)]++E) lE2 t2 (ctx_let2_capture e1' x (close_ec ctx_hole x)) (env_remove (x, bind_typ t1) ([(x, bind_typ t1)]++E)) lE t2 =
          contexting ([(x, bind_typ t1)]++E) lE2 t2 (ctx_let2_capture e1' x ctx_hole) E lE t2
          ) as EQ.
          unfold close_ec. simpl.
          destruct (eq_binding_dec (x, bind_typ t1) (x, bind_typ t1)).
             rewrite env_remove_notin; auto.  
             contradict n; auto.
        rewrite <- EQ.
        apply contexting_let2_capture with (T1':=t1) (D1':=lE1) (D2':=lE2); auto.
          simpl.
          destruct (eq_binding_dec (x, bind_typ t1) (x, bind_typ t1)); try solve [contradict n; auto].
          rewrite env_remove_notin; auto.

          simpl.
          destruct (eq_binding_dec (x, bind_typ t1) (x, bind_typ t1)); try solve [contradict n; auto].
          rewrite env_remove_notin; auto.

          assert (J:=Typ1').
          apply typing_fv_ee_upper in Typ1'.
          apply disjdom_sym_1.
          apply disjdom_sub with (D1:=union (dom E) (dom lE1)); auto.
          eapply disjdom_app_r.
          split.
            apply disjoint__disjdom.
            apply disjoint_split_right in Hsplit; auto.

            apply disjoint__disjdom.
            apply disjoint_lenv_split' in Hsplit. auto.
        simpl. apply disjdom_eq with (D1:={{x}}).
          eapply disjdom_app_r.
          split.
            apply disjdom_sym_1.
            apply disjdom_one_2; auto.

            apply disjdom_sym_1.
            apply disjdom_one_2; auto.
          clear. fsetdec.

    apply Heq2' in Hcontexting2; try solve [apply cbn_ctx_plug; simpl; auto].
    rewrite plug_plugC in Hcontexting2; try solve [simpl;eapply disjdom_app_r;split; try solve [apply disjdom_one_2; auto | apply disjdom_nil_1]].
    rewrite plug_plugC in Hcontexting2; try solve [simpl;eapply disjdom_app_r;split; try solve [apply disjdom_one_2; auto | apply disjdom_nil_1]].
    simpl in Hcontexting2.
    rewrite <- shift_ee_expr in Hcontexting2; auto.
    rewrite <- shift_ee_expr in Hcontexting2; auto.
    rewrite open_close_ee__id in Hcontexting2; auto.
    rewrite open_close_ee__id in Hcontexting2; auto.
    apply Kleene_eq__trans with (e':=plug C (exp_let e1' e2)); auto.
Qed.

Lemma F_nobservational_eq__congr_bang : forall E lE e1 e1' t1,
   F_nobservational_eq E lE (exp_bang e1) (exp_bang e1') (typ_bang t1) ->
   F_nobservational_eq E lE e1 e1' t1.
Proof.
  intros E lE e1 e1' t1 Heq.
  destruct Heq as [Typ [Typ' Heq]].
  inversion Typ; subst.
  inversion Typ'; subst.
  split; auto.
  split; auto.
    intros C Hcontext HvC.
    assert (contexting E lempty (typ_bang t1) (plugC C (ctx_let1 ctx_hole 0)) nil nil Two) as Hcontexting1.
      apply contexting_plugC_contexting with (E':=E) (D':=lempty) (T':=t1); auto.
        apply contexting_let1 with (T1':=t1)(L:=dom E)(D1':=lempty)(D2':=lempty); auto.
          intros x xn. unfold open_ee. simpl. simpl_env. apply typing_var; auto.
          simpl. apply disjdom_nil_1.
        simpl. apply disjdom_nil_1.

    apply Heq in Hcontexting1; try solve [apply cbn_ctx_plug; simpl; auto].
    rewrite plug_plugC in Hcontexting1; try solve [simpl; apply disjdom_sym_1; apply disjdom_nil_1].
    rewrite plug_plugC in Hcontexting1; try solve [simpl; apply disjdom_sym_1; apply disjdom_nil_1].
    simpl in Hcontexting1.

    assert (F_nobservational_eq E lempty (exp_let (exp_bang e1) 0) e1 t1) as Hctx1.
      apply F_observational_eq__F_nobservational_eq.
      apply F_observational_eq__beta.
        apply typing_let with (T1:=t1)(L:=dom E)(D1:=lempty)(D2:=lempty); auto.
          intros x xn. unfold open_ee. simpl. simpl_env. apply typing_var; auto.

        apply red_let_beta; auto.
          apply expr_let with (L:={}); auto.
            intros x xn. unfold open_ee. simpl. auto. 
      
    assert (F_nobservational_eq E lempty (exp_let (exp_bang e1') 0) e1' t1) as Hctx1'.
      apply F_observational_eq__F_nobservational_eq.
      apply F_observational_eq__beta.
        apply typing_let with (T1:=t1)(L:=dom E)(D1:=lempty)(D2:=lempty); auto.
          intros x xn. unfold open_ee. simpl. simpl_env. apply typing_var; auto.

        apply red_let_beta; auto.
          apply expr_let with (L:={}); auto.
            intros x xn. unfold open_ee. simpl. auto. 

  destruct Hctx1 as [Typ1 [Typ2 Heq1]].
  destruct Hctx1' as [Typ1' [Typ2' Heq1']].
  
  apply Kleene_eq__trans with (e':=plug C (exp_let (exp_bang e1) 0)); auto.
    apply Kleene_eq__sym.
    apply Heq1 in Hcontext; auto.

  apply Kleene_eq__trans with (e':=plug C (exp_let (exp_bang e1') 0)); auto.
Qed.

Lemma F_nobservational_eq__congr_snd : forall E lE e1 e1' e2 e2' t1 t2,
   F_nobservational_eq E lE (exp_apair e1 e2) (exp_apair e1' e2') (typ_with t1 t2) ->
   F_nobservational_eq E lE e2 e2' t2.
Proof.
  intros E lE e1 e1' e2 e2' t1 t2 Heq.
  destruct Heq as [Typ [Typ' Heq]].
  split.
    inversion Typ; subst; auto.
  split.
    inversion Typ'; subst; auto.

    intros C Hcontext HvC.
    assert (contexting E lE (typ_with t1 t2) (plugC C (ctx_snd ctx_hole)) nil nil Two) as Hcontexting1.
      apply contexting_plugC_contexting with (E':=E) (D':=lE) (T':=t2); auto.
        apply contexting_snd with (T1':=t1); auto.
        simpl. apply disjdom_nil_1.

    apply Heq in Hcontexting1; try solve [apply cbn_ctx_plug; simpl; auto].
    rewrite plug_plugC in Hcontexting1; try solve [simpl; apply disjdom_sym_1; apply disjdom_nil_1].
    rewrite plug_plugC in Hcontexting1; try solve [simpl; apply disjdom_sym_1; apply disjdom_nil_1].
    simpl in Hcontexting1.

    assert (F_nobservational_eq E lE (exp_snd (exp_apair e1 e2)) e2 t2) as Hctx2.
      apply F_observational_eq__F_nobservational_eq.
      apply F_observational_eq__beta.
        apply typing_snd with (T1:=t1); auto.

        inversion Typ; subst.
        apply red_snd_beta; auto.
      
    assert (F_nobservational_eq E lE (exp_snd (exp_apair e1' e2')) e2' t2) as Hctx2'.
      apply F_observational_eq__F_nobservational_eq.
      apply F_observational_eq__beta.
        apply typing_snd with (T1:=t1); auto.

        inversion Typ'; subst.
        apply red_snd_beta; auto.

  destruct Hctx2 as [Typ1 [Typ2 Heq2]].
  destruct Hctx2' as [Typ1' [Typ2' Heq2']].
  
  apply Kleene_eq__trans with (e':=plug C (exp_snd (exp_apair e1 e2))); auto.
    apply Kleene_eq__sym.
    apply Heq2 in Hcontext; auto.

  apply Kleene_eq__trans with (e':=plug C (exp_snd (exp_apair e1' e2'))); auto.
Qed.

