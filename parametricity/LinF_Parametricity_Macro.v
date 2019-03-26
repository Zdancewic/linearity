(** Authors: Jianzhou Zhao. *)

Require Export LinF_Parametricity_Pre.

(******************************************************************)
(*                                      Macro                     *)
(******************************************************************)
Lemma m_delta_gamma_subst_var : 
  forall E lE (gsubst lgsubst: gamma_subst) (dsubst : delta_subst) (x : atom) (t : typ) (e : exp),
  wf_lgamma_subst E lE dsubst gsubst lgsubst ->
  binds x e gsubst -> 
  typing nil nil e t -> 
  apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst x)) = e.
Proof.
  intros E lE gsubst lgsubst dsubst x t e Hwfg Hbinds Htyping.
  assert (H:=Hwfg).
  apply wf_lgamma_subst__uniq in H.
  decompose [and] H.
  assert (x `notin` dom lgsubst) as J.
    apply wf_lgamma_subst_disjoint in Hwfg.
    decompose [and] Hwfg.
    apply binds_In in Hbinds.
    unfold disjoint in H5. fsetdec.
  rewrite apply_gamma_subst_nfv; auto.
  rewrite gamma_subst_var with (x:=x) (gsubst:=gsubst) (t:=t) (e:=e); auto.
  rewrite delta_subst_closed_exp with (t:=t); auto.
Qed.

Lemma m_delta_lgamma_subst_var : 
  forall E lE (gsubst lgsubst: gamma_subst) (dsubst : delta_subst) (x : atom) (t : typ) (e : exp),
  wf_lgamma_subst E lE dsubst gsubst lgsubst ->
  binds x e lgsubst -> 
  typing nil nil e t -> 
  apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst x)) = e.
Proof.
  intros E lE gsubst lgsubst dsubst x t e Hwfg Hbinds Htyping.
  assert (H:=Hwfg).
  apply wf_lgamma_subst__uniq in H.
  decompose [and] H.
  assert (x `notin` dom gsubst) as J.
    apply wf_lgamma_subst_disjoint in Hwfg.
    decompose [and] Hwfg.
    apply binds_In in Hbinds.
    unfold disjoint in H5. fsetdec.
  rewrite gamma_subst_var with (x:=x) (gsubst:=lgsubst) (t:=t) (e:=e); auto.
  rewrite gamma_subst_closed_exp with (t:=t); auto.
  rewrite delta_subst_closed_exp with (t:=t); auto.
Qed.

Lemma m_commut_subst_open_ee: forall E lE dsubst gsubst lgsubst e1 (x:atom),
  wf_lgamma_subst E lE dsubst gsubst lgsubst ->
  x `notin` dom gsubst ->
  x `notin` dom lgsubst ->
  apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (open_ee e1 x))) =
  open_ee (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e1))) x.
Proof.
  intros.
  rewrite commut_lgamma_subst_open_ee with (E:=E) (dsubst:=dsubst) (D:=lE) (gsubst:=gsubst); auto.
  rewrite commut_gamma_subst_open_ee with (E:=E) (dsubst:=dsubst) (D:=lE) (lgsubst:=lgsubst); auto.
  rewrite commut_delta_subst_open_ee with (dE:=E); auto.
    rewrite apply_gamma_subst_nfv; auto.
    rewrite apply_gamma_subst_nfv; auto.
    rewrite apply_delta_subst_nfv; auto.
    apply wf_lgamma_subst__wf_subst in H. destruct H; auto.
Qed.

Lemma m_commut_subst_open_te: forall E lE dsubst gsubst lgsubst e1 (X:atom),
  wf_lgamma_subst E lE dsubst gsubst lgsubst ->
  X `notin` dom dsubst ->
  (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (open_te e1 X)))) =
  open_te (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e1))) X.
Proof.
  intros.
  rewrite commut_lgamma_subst_open_te with (E:=E) (dsubst:=dsubst) (D:=lE) (gsubst:=gsubst); auto.
  rewrite commut_gamma_subst_open_te with (E:=E) (dsubst:=dsubst)(D:=lE) (lgsubst:=lgsubst); auto.
    rewrite commut_delta_subst_open_te with (dE:=E); auto.
    rewrite apply_gamma_subst_typ_nfv; auto.
    rewrite apply_gamma_subst_typ_nfv; auto.
    rewrite apply_delta_subst_typ_nfv; auto.
    apply wf_lgamma_subst__wf_subst in H. destruct H; auto.
Qed.

Lemma m_commut_subst_typ_open_tt: forall E lE dsubst gsubst lgsubst T1 (X:atom),
  wf_lgamma_subst E lE dsubst gsubst lgsubst ->
  X `notin` dom dsubst ->
  (apply_delta_subst_typ dsubst (open_tt T1 X)) =
  open_tt (apply_delta_subst_typ dsubst T1) X.
Proof.
  intros.
  rewrite commut_delta_subst_open_tt with (dE:=E); auto.
    rewrite apply_delta_subst_typ_nfv; auto.
    apply wf_lgamma_subst__wf_subst in H. destruct H; auto.
Qed.

Lemma m_type_preserved_under_delta_gamma_subst : 
  forall (E : env) lE (dsubst : delta_subst) (gsubst lgsubst: gamma_subst) (t : typ) K,
  wf_lgamma_subst E lE dsubst gsubst lgsubst ->
  wf_typ E t K ->
  type (apply_delta_subst_typ dsubst (apply_gamma_subst_typ gsubst (apply_gamma_subst_typ lgsubst t))).
Proof.
  intros E lE dsubst gsubst lgsubst t K Hwfg Hwft.
  apply type_preserved_under_delta_subst with (E:=E); auto.
    apply wf_lgamma_subst__wf_subst in Hwfg.
    destruct Hwfg; auto.
  apply type_preserved_under_gamma_subst with  (E:=E) (dsubst:=dsubst) (D:=lE) (lgsubst:=lgsubst); auto.
  apply type_preserved_under_lgamma_subst with  (E:=E)(D:=lE)(gsubst:=gsubst)(dsubst:=dsubst); auto.
    apply type_from_wf_typ in Hwft. assumption.
Qed.

Lemma m_red_abs_subst : forall E lE dsubst gsubst lgsubst V e1 x (y:atom) L T1 Q,
  wf_lgamma_subst E lE dsubst gsubst lgsubst ->
  wf_typ E V kn_nonlin ->
  value x -> 
  typing nil nil x (apply_delta_subst_typ dsubst V) ->
  y `notin` fv_ee e1 ->
  (forall x : atom, x `notin` L -> typing ([(x, bind_typ V)] ++ E) lE (open_ee e1 x) T1) ->
  red (exp_app
                  (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_abs Q V e1)))) x)
                  (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (subst_ee y x (open_ee e1 y))))).
Proof.
  intros E lE dsubst gsubst lgsubst V e1 x y L T1 Q Hwfg Hwft Hvalue Htyping Hfvy Hfr.
  rewrite <- subst_ee_intro; auto.
  assert (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst x)) =x) as Heq1.
     rewrite gamma_subst_closed_exp with (t:= apply_delta_subst_typ dsubst V); auto.
     rewrite gamma_subst_closed_exp with (t:= apply_delta_subst_typ dsubst V); auto.
     rewrite delta_subst_closed_exp with (t:= apply_delta_subst_typ dsubst V); auto.
     rewrite gamma_subst_closed_exp with (t:= apply_delta_subst_typ dsubst V); auto.
  rewrite <- Heq1.
  rewrite commut_gamma_subst_abs.
  rewrite commut_gamma_subst_abs.
  assert (open_ee e1 (apply_delta_subst dsubst (apply_gamma_subst gsubst  (apply_gamma_subst lgsubst x))) = open_ee e1 x) as Heq2. 
     rewrite Heq1. auto. 
  rewrite Heq2.
  rewrite commut_lgamma_subst_open_ee with (E:=E)(D:=lE)(dsubst:=dsubst)(gsubst:=gsubst); auto.
  rewrite commut_gamma_subst_open_ee with (E:=E) (dsubst:=dsubst) (D:=lE) (lgsubst:=lgsubst); auto.
  apply red_abs_preserved_under_delta_subst with (dE:=E); auto.
    apply wf_lgamma_subst__wf_subst in Hwfg. destruct Hwfg; auto.
  rewrite <- commut_gamma_subst_abs; auto.
  rewrite <- commut_gamma_subst_open_ee with (E:=E) (dsubst:=dsubst) (D:=lE) (lgsubst:=lgsubst); auto.
  apply red_abs_preserved_under_gamma_subst with (E:=E) (dsubst:=dsubst) (D:=lE) (lgsubst:=lgsubst); auto. 

  rewrite <- commut_gamma_subst_abs; auto.
  rewrite <- commut_lgamma_subst_open_ee with (E:=E)(D:=lE)(dsubst:=dsubst)(gsubst:=gsubst); auto.
  apply red_abs_preserved_under_lgamma_subst with (E:=E)(D:=lE)(dsubst:=dsubst)(gsubst:=gsubst); auto. 

  apply red_abs.
    apply expr_abs with (L:=L).
       assert (wf_typ E V kn_nonlin); auto.
       apply type_from_wf_typ in H; assumption.

       intros. apply Hfr in H.
       apply typing_regular in H. decompose [and] H. assumption.
   apply typing_regular in Htyping. decompose [and] Htyping. assumption.
Qed.

Lemma m_red_labs_subst : forall E lE dsubst gsubst lgsubst V e1 x (y:atom) L T1 Q,
  wf_lgamma_subst E lE dsubst gsubst lgsubst ->
  wf_typ E V kn_lin ->
  value x -> 
  typing nil nil x (apply_delta_subst_typ dsubst V) ->
  y `notin` fv_ee e1 ->
  (forall x : atom, x `notin` L -> typing E ([(x, lbind_typ V)] ++ lE) (open_ee e1 x) T1) ->
  red (exp_app
                  (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_abs Q V e1)))) x)
                  (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (subst_ee y x (open_ee e1 y))))).
Proof.
  intros E lE dsubst gsubst lgsubst V e1 x y L T1 Q Hwfg Hwft Hvalue Htyping Hfvy Hfr.
  rewrite <- subst_ee_intro; auto.
  assert (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst x)) =x) as Heq1.
     rewrite gamma_subst_closed_exp with (t:= apply_delta_subst_typ dsubst V); auto.
     rewrite gamma_subst_closed_exp with (t:= apply_delta_subst_typ dsubst V); auto.
     rewrite delta_subst_closed_exp with (t:= apply_delta_subst_typ dsubst V); auto.
     rewrite gamma_subst_closed_exp with (t:= apply_delta_subst_typ dsubst V); auto.
  rewrite <- Heq1.
  rewrite commut_gamma_subst_abs.
  rewrite commut_gamma_subst_abs.
  assert (open_ee e1 (apply_delta_subst dsubst (apply_gamma_subst gsubst  (apply_gamma_subst lgsubst x))) = open_ee e1 x) as Heq2. 
     rewrite Heq1. auto. 
  rewrite Heq2.
  rewrite commut_lgamma_subst_open_ee with (E:=E)(D:=lE)(dsubst:=dsubst)(gsubst:=gsubst); auto.
  rewrite commut_gamma_subst_open_ee with (E:=E) (dsubst:=dsubst) (D:=lE) (lgsubst:=lgsubst); auto.
  apply red_abs_preserved_under_delta_subst with (dE:=E); auto.
    apply wf_lgamma_subst__wf_subst in Hwfg. destruct Hwfg; auto.
  rewrite <- commut_gamma_subst_abs; auto.
  rewrite <- commut_gamma_subst_open_ee with (E:=E) (dsubst:=dsubst) (D:=lE) (lgsubst:=lgsubst); auto.
  apply red_abs_preserved_under_gamma_subst with (E:=E) (dsubst:=dsubst) (D:=lE) (lgsubst:=lgsubst); auto. 

  rewrite <- commut_gamma_subst_abs; auto.
  rewrite <- commut_lgamma_subst_open_ee with (E:=E)(D:=lE)(dsubst:=dsubst)(gsubst:=gsubst); auto.
  apply red_abs_preserved_under_lgamma_subst with (E:=E)(D:=lE)(dsubst:=dsubst)(gsubst:=gsubst); auto. 

  apply red_abs.
    apply expr_abs with (L:=L).
       assert (wf_typ E V kn_lin); auto.
       apply type_from_wf_typ in H; assumption.

       intros. apply Hfr in H.
       apply typing_regular in H. decompose [and] H. assumption.
   apply typing_regular in Htyping. decompose [and] Htyping. assumption.
Qed.

Lemma m_red_tabs_subst : forall E lE dsubst gsubst lgsubst e1 (X:atom) t2 L T1 K,
  wf_lgamma_subst E lE dsubst gsubst lgsubst ->
  wf_typ nil t2 K ->
  X `notin` fv_te e1 ->
  (forall X : atom,  X `notin` L -> typing ([(X, bind_kn K)] ++ E) lE (open_te e1 X) (open_tt T1 X)) ->
  red (exp_tapp
                 (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_tabs K e1)))) t2)
                 (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (subst_te X t2 (open_te e1 X))))). 
Proof.
  intros E lE dsubst gsubst lgsubst e1 X t2 L K T1 Hwfg Hwfr Hfv Hfr.
  rewrite <- subst_te_intro; auto.
  assert (apply_delta_subst_typ dsubst (apply_gamma_subst_typ gsubst (apply_gamma_subst_typ lgsubst t2)) =t2) as Heq1.
     erewrite gamma_subst_closed_typ; eauto.
     erewrite gamma_subst_closed_typ; eauto.
     erewrite delta_subst_closed_typ; eauto.
  rewrite <- Heq1.
  rewrite commut_gamma_subst_tabs.
  rewrite commut_gamma_subst_tabs.
  assert (open_te e1 (apply_delta_subst_typ dsubst (apply_gamma_subst_typ gsubst (apply_gamma_subst_typ lgsubst t2))) = open_te e1 t2) as Heq2.
     rewrite Heq1. auto. 
  rewrite Heq2.
  rewrite commut_lgamma_subst_open_te with (E:=E)(D:=lE)(dsubst:=dsubst)(gsubst:=gsubst); auto.
  rewrite commut_gamma_subst_open_te with  (E:=E) (dsubst:=dsubst)(D:=lE) (lgsubst:=lgsubst); auto.
  apply red_tabs_preserved_under_delta_subst with (dE:=E); auto.
    apply wf_lgamma_subst__wf_subst in Hwfg. destruct Hwfg; auto.
  rewrite <- commut_gamma_subst_tabs.
  rewrite <- commut_gamma_subst_open_te with  (E:=E) (dsubst:=dsubst)(D:=lE) (lgsubst:=lgsubst); auto.
  apply red_tabs_preserved_under_gamma_subst with  (E:=E) (dsubst:=dsubst)(D:=lE) (lgsubst:=lgsubst); auto.

  rewrite <- commut_gamma_subst_tabs; auto.
  rewrite <- commut_lgamma_subst_open_te with (E:=E)(D:=lE)(dsubst:=dsubst)(gsubst:=gsubst); auto.
  apply red_tabs_preserved_under_lgamma_subst with (E:=E)(D:=lE)(dsubst:=dsubst)(gsubst:=gsubst); auto. 

  apply red_tabs.
      apply expr_tabs with (L:=L).
          intros. apply Hfr in H.
          apply typing_regular in H. decompose [and] H. assumption.
      eapply type_from_wf_typ with (E:=@nil (atom*binding)); eauto.
Qed.

Lemma m_typing_arrow_stronger : 
  forall (E E' : env) (dsubst : delta_subst) (X : atom) e k t1 t2 t3 (dsubst' : delta_subst) K Q,
  wf_delta_subst (E' ++ [(X, bind_kn K)] ++ E) (dsubst' ++ [(X, (apply_delta_subst_typ (dsubst' ++ dsubst) t2))]  ++ dsubst) ->
  X `notin` union (fv_env E) (fv_env E') ->
  X `notin` fv_tt t1 ->
  X `notin` fv_tt t3 ->
  ddom_env E[=]dom dsubst ->
  ddom_env E'[=]dom dsubst' ->
  wf_typ nil (apply_delta_subst_typ (dsubst' ++ dsubst) t2) K ->
  wf_typ (E'++E) t2 K ->
  typing nil nil e
         (apply_delta_subst_typ
            (dsubst' ++
             [(X, apply_delta_subst_typ (dsubst' ++ dsubst) t2)] ++ dsubst)
            (typ_arrow Q (open_tt_rec k X t1) (open_tt_rec k X t3))) ->
  typing nil nil e (apply_delta_subst_typ (dsubst'++dsubst) (typ_arrow Q (open_tt_rec k t2 t1) (open_tt_rec k t2 t3))).
Proof. 
  intros E E' dsubst X e k t1 t2 t3 dsubst' K Q Hwfd Hfv Hfvt1 Hfvt3 Heq Heq' Hwft2 Hwft Htyping.
  rewrite subst_tt_intro_rec with (X:=X) (T2:=t1); auto.
  rewrite subst_tt_intro_rec with (X:=X) (T2:=t3); auto.
  erewrite delta_subst_opt with (E:=E) (E':=E') in Htyping; eauto.
  erewrite swap_subst_tt_dsubst with (E:=E'++E) in Htyping; simpl_env; eauto.
     apply dsubst_stronger in Hwfd; eauto.
     eapply notin_fv_wf with (E:=E'++E); simpl_env; eauto.
Qed.

Lemma m_typing_arrow_weaken : 
  forall (E E' : env) (dsubst : delta_subst) (X : atom) e k t1 t2 t3 (dsubst' : delta_subst) K Q,
  wf_delta_subst (E' ++ E) (dsubst' ++ dsubst) ->
  X `notin` union (fv_env E) (fv_env E') ->
  X `notin` fv_tt t1 ->
  X `notin` fv_tt t3 ->
  ddom_env E[=]dom dsubst ->
  ddom_env E'[=]dom dsubst' ->
  wf_typ nil (apply_delta_subst_typ (dsubst' ++ dsubst) t2) K ->
  wf_typ (E'++E) t2 K ->
  typing nil nil e
         (apply_delta_subst_typ
            (dsubst' ++ dsubst)
            (typ_arrow Q (open_tt_rec k t2 t1) (open_tt_rec k t2 t3))) ->
  typing nil nil e (apply_delta_subst_typ (dsubst'++[(X, apply_delta_subst_typ (dsubst' ++ dsubst) t2)]++dsubst) (typ_arrow Q (open_tt_rec k X t1) (open_tt_rec k X t3))).
Proof.
  intros E E' dsubst X e k t1 t2 t3 dsubst' K Q Hwfd Hfv Hfvt1 Hfvt3 Heq Heq' Hwft2 Hwft Htyping.
  rewrite subst_tt_intro_rec with (X:=X) (T2:=t1) in Htyping; auto.
  rewrite subst_tt_intro_rec with (X:=X) (T2:=t3) in Htyping; auto.
  erewrite delta_subst_opt with (E:=E) (E':=E'); eauto.
      erewrite swap_subst_tt_dsubst with (E:=E'++E); simpl_env; eauto.
          eapply notin_fv_wf with (E:=E'++E); simpl_env; eauto.
      apply dsubst_weaken; eauto.
Qed.

Lemma m_typing_var_stronger : 
  forall (E E' : env) (dsubst : delta_subst) (X : atom) x k t1 t2 (dsubst' : delta_subst) K,
  wf_delta_subst (E' ++ [(X, bind_kn K)] ++ E) (dsubst' ++ [(X, (apply_delta_subst_typ (dsubst' ++ dsubst) t2))]  ++ dsubst) ->
  X `notin` union (fv_env E) (fv_env E') ->
  X `notin` fv_tt t1 ->
  ddom_env E[=]dom dsubst ->
  ddom_env E'[=]dom dsubst' ->
  wf_typ nil (apply_delta_subst_typ (dsubst' ++ dsubst) t2) K ->
  wf_typ (E'++E) t2 K ->
  typing nil nil x (apply_delta_subst_typ (dsubst'++dsubst) (open_tt_rec k t2 t1)) ->
  typing nil nil x
         (apply_delta_subst_typ
            (dsubst' ++
             [(X, apply_delta_subst_typ (dsubst' ++ dsubst) t2)] ++ dsubst)
            (open_tt_rec k X t1)).
Proof.
  intros E E' dsubst X e k t1 t2 dsubst' K Hwfd Hfv Hfvt1 Heq Heq' Hwft2 Hwft Htyping.
  erewrite delta_subst_opt with (E:=E) (E':=E'); eauto.
  erewrite swap_subst_tt_dsubst with (E:=E'++E); simpl_env; eauto.
    simpl in Hfv; rewrite <- subst_tt_intro_rec; auto.
    apply dsubst_stronger in Hwfd; eauto.
    eapply notin_fv_wf with (E:=E'++E); simpl_env; eauto.
Qed.

Lemma m_typing_var_weaken : 
  forall (E E' : env) (dsubst : delta_subst) (X : atom) x k t1 t2 (dsubst' : delta_subst) K,
  wf_delta_subst (E' ++ E) (dsubst' ++ dsubst) ->
  X `notin` union (dom E) (dom E') ->
  X `notin` fv_tt t1 ->
  ddom_env E[=]dom dsubst ->
  ddom_env E'[=]dom dsubst' ->
  wf_typ nil (apply_delta_subst_typ (dsubst' ++ dsubst) t2) K ->
  wf_typ (E'++E) t2 K ->
  typing nil nil x (apply_delta_subst_typ (dsubst'++[(X, apply_delta_subst_typ (dsubst' ++ dsubst) t2)]++dsubst) (open_tt_rec k X t1)) ->
  typing nil nil x (apply_delta_subst_typ (dsubst' ++ dsubst) (open_tt_rec k t2 t1)).
Proof.
  intros E E' dsubst X e k t1 t2 dsubst' K Hwfd Hfv Hfvt1 Heq Heq' Hwft2 Hwft Htyping.
  erewrite delta_subst_opt with (E:=E) (E':=E') in Htyping; eauto.
  erewrite swap_subst_tt_dsubst with (E:=E'++E) in Htyping; simpl_env; eauto.
    rewrite <- subst_tt_intro_rec in Htyping; auto.
    eapply notin_fv_wf with (E:=E'++E); simpl_env; eauto.
    apply dsubst_weaken; eauto.
Qed.

Lemma m_typing_all_stronger : 
  forall (E E' : env) (dsubst : delta_subst) (X : atom) e k t t2 (dsubst' : delta_subst) K Q,
  wf_delta_subst (E' ++ [(X, bind_kn K)] ++ E) (dsubst' ++ [(X, (apply_delta_subst_typ (dsubst' ++ dsubst) t2))]  ++ dsubst) ->
  X `notin` union (fv_env E) (fv_env E') ->
  X `notin` fv_tt t ->
  ddom_env E[=]dom dsubst ->
  ddom_env E'[=]dom dsubst' ->
  wf_typ nil (apply_delta_subst_typ (dsubst' ++ dsubst) t2) K ->
  wf_typ (E'++E) t2 K ->
  typing nil nil e
         (apply_delta_subst_typ
            (dsubst' ++
             [(X, apply_delta_subst_typ (dsubst' ++ dsubst) t2)] ++ dsubst)
            (typ_all Q (open_tt_rec (S k) X t))) ->
  typing nil nil e (apply_delta_subst_typ (dsubst'++dsubst) (typ_all Q (open_tt_rec (S k) t2 t))).
Proof.
  intros E E' dsubst X e k t t2 dsubst' K Q Hwfd Hfv Hfvt Heq Heq' Hwft2 Hwft Htyping.
  rewrite subst_tt_intro_rec with (X:=X); auto.
  erewrite delta_subst_opt with (E:=E) (E':=E') in Htyping; eauto.
  erewrite swap_subst_tt_dsubst with (E:=E'++E) in Htyping; simpl_env; eauto.
      apply dsubst_stronger in Hwfd; eauto.
      eapply notin_fv_wf with (E:=E'++E); simpl_env; eauto.
Qed.

Lemma m_typing_normalization_fv : forall (e v : exp) (T : typ) X,
  typing nil nil e T -> 
  normalize e v -> 
  X `notin` fv_te v.
Proof.
  intros e v T X Htypinge Hnorm.
  apply preservation_normalization with (v:=v) in Htypinge; auto.
  apply empty_typing__empty_fv with (X:=X) in Htypinge. 
  decompose [and] Htypinge. auto.
Qed.

Lemma m_typing_normalization_arrow_fv_stronger :
  forall (E E' : env) (dsubst : delta_subst) (X : atom) e x k t1 t2 (dsubst' : delta_subst) u,
  X `notin` fv_te e ->
  typing nil nil x
         (apply_delta_subst_typ
            (dsubst' ++ dsubst)
            (open_tt_rec k t2 t1)) ->
  normalize (exp_app e x) u ->
  X `notin` fv_te u.
Proof.
  intros E E' dsubst X e x k t1 t2 dsubst' u Hfv Htypingx Hnorm_exu.
  apply notin_fv_te_mred with (e:=exp_app e x).
       destruct Hnorm_exu; auto.
       simpl. eauto using notin_fv_te_typing.
Qed.

Lemma m_typing_normalization_arrow_fv_weaken :
  forall (E E' : env) (dsubst : delta_subst) (X : atom) e x k t1 t2 (dsubst' : delta_subst) u,
  X `notin` fv_te e ->
  typing nil nil x
         (apply_delta_subst_typ
            (dsubst' ++ [(X, apply_delta_subst_typ (dsubst' ++ dsubst) t2)] ++ dsubst)
            (open_tt_rec k X t1)) ->
  normalize (exp_app e x) u ->
  X `notin` fv_te u.
Proof.
  intros E E' dsubst X e x k t1 t2 dsubst' u Hfv Htypingx Hnorm_exu.
  apply notin_fv_te_mred with (e:=exp_app e x).
       destruct Hnorm_exu; auto.
       simpl. eauto using notin_fv_te_typing.
Qed.

Lemma m_typing_subst_typ_closed : forall E lE dsubst gsubst lgsubst V e1 (x:atom) T1,
  wf_delta_subst E dsubst ->
  wf_lgamma_subst E lE dsubst gsubst lgsubst ->
  wf_typ E V kn_nonlin ->
  x `notin` dom gsubst ->
  x `notin` dom lgsubst ->
  wf_env E ->
  typing ([(x, bind_typ V)] ++ E) lE (open_ee e1 x) T1 ->
  typing ([(x, bind_typ (apply_delta_subst_typ dsubst V))] ++ nil) nil
             (open_ee (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e1))) x) 
             (apply_delta_subst_typ dsubst T1).
Proof.
  intros E lE dsubst gsubst lgsubst V e1 x T1 Hwfd Hwfg HWFTV Hfv Hfv' Henv Htyping.
  rewrite_env (nil++lE) in Htyping.
  apply typing_subst_closed with (E:=E) (E':=[(x, bind_typ V)]) (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst) in Htyping; auto.
     rewrite m_commut_subst_open_ee with (E:=E) (lE:=lE) (dsubst:=dsubst) in Htyping; auto.

     apply wft_subst_closed with (E:=E) (E':=@nil (atom*binding)) (dsubst:=dsubst) in HWFTV; auto.
     apply wf_lenv_empty.
       apply wf_env_typ with (x:=x) in HWFTV; auto.
Qed.

Lemma m_typing_subst_ltyp_closed : forall E lE dsubst gsubst lgsubst V e1 (x:atom) T1,
  wf_delta_subst E dsubst ->
  wf_lgamma_subst E lE dsubst gsubst lgsubst ->
  wf_typ E V kn_lin ->
  x `notin` dom gsubst ->
  x `notin` dom lgsubst ->
  wf_env E ->
  typing E ([(x, lbind_typ V)] ++ lE) (open_ee e1 x) T1 ->
  typing nil ([(x, lbind_typ (apply_delta_subst_typ dsubst V))])
             (open_ee (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e1))) x) 
             (apply_delta_subst_typ dsubst T1).
Proof.
  intros E lE dsubst gsubst lgsubst V e1 x T1 Hwfd Hwfg HWFTV Hfv Hfv' Henv Htyping.
  rewrite_env (nil++E) in Htyping.
  apply typing_subst_closed with (D:=lE) (D':=[(x, lbind_typ V)]) (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst) in Htyping; auto.
     rewrite m_commut_subst_open_ee with (E:=E) (lE:=lE) (dsubst:=dsubst) in Htyping; auto.

     apply wft_subst_closed with (E:=E) (E':=@nil (atom*binding)) (dsubst:=dsubst) in HWFTV; auto.
     apply wf_lenv_typ with (x:=x) (D:=nil) in HWFTV; auto.
Qed.

Lemma m_typing_subst_kind_closed : forall E lE dsubst gsubst lgsubst e1 (X:atom) T1 K,
  wf_delta_subst E dsubst ->
  wf_lgamma_subst E lE dsubst gsubst lgsubst ->
  X `notin` dom dsubst ->
  wf_env E ->
  typing ([(X, bind_kn K)] ++ E) lE (open_te e1 X) (open_tt T1 X) ->
  typing ([(X, bind_kn K)] ++ nil) nil
             (open_te (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e1))) X) 
             (open_tt (apply_delta_subst_typ dsubst T1) X).
Proof.
  intros E lE dsubst gsubst lgsubst e1 X T1 K Hwfd Hwfg Hfv Henv Htyping.
  rewrite_env (nil++lE) in Htyping.
  apply typing_subst_closed with (E:=E) (E':=[(X, bind_kn K)]) (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst)in Htyping; auto.
      rewrite m_commut_subst_open_te with (E:=E) (dsubst:=dsubst) (lE:=lE) (lgsubst:=lgsubst) in Htyping; eauto.
      rewrite m_commut_subst_typ_open_tt with (E:=E) (gsubst:=gsubst)(lE:=lE) (lgsubst:=lgsubst) in Htyping; eauto.
        apply wf_lgamma_subst__wf_subst in Hwfg.
        destruct Hwfg; auto.
       
      simpl. simpl_env.
      apply wf_lenv_empty.
        rewrite_env ([(X, bind_kn K)]++nil).
        apply wf_env_kn; auto.
Qed.

Lemma m_congr_tapp : forall E lE dsubst gsubst lgsubst T2 e1 v u K, 
   wf_delta_subst E dsubst ->
   wf_lgamma_subst E lE dsubst gsubst lgsubst ->
   wf_typ E T2 K ->
   normalize (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e1)))  v ->
   normalize (exp_tapp v (apply_delta_subst_typ dsubst T2)) u ->
   normalize (exp_tapp (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e1)))
                              (apply_delta_subst_typ dsubst (apply_gamma_subst_typ gsubst (apply_gamma_subst_typ lgsubst T2)))) u.
Proof.
   intros E lE dsubst gsubst lgsubst T2 e1 v u K Hwfd Hwfg Hwft He1_v Hvt1_u.
   apply congr_tapp with (v1:=v); auto.
      apply type_preserved_under_delta_subst with (E:=E); auto.
         apply type_preserved_under_gamma_subst with  (E:=E) (dsubst:=dsubst)(D:=lE) (lgsubst:=lgsubst); auto.
           apply wf_lgamma_subst__wf_subst in Hwfg.
           destruct Hwfg; auto.

           apply type_from_wf_typ in Hwft. assumption.
Qed.

Lemma m_tapp_fv : forall E dsubst dsubst' T2 e e' v v' u u' T1 y K,
   wf_env E ->
   wf_delta_subst E dsubst ->
   wf_delta_subst E dsubst' ->
   wf_typ E T2 K ->
   normalize e v ->
   normalize e' v' ->
   normalize (exp_tapp v (apply_delta_subst_typ dsubst T2)) u ->
   normalize (exp_tapp v' (apply_delta_subst_typ dsubst' T2)) u' ->
   y `notin` union (fv_env E) (union (fv_tt T1) (union (fv_te e) (fv_te e')))->
   y `notin` union (fv_env E) (union (fv_env nil) (union (fv_tt T1) (union (fv_te u) (fv_te u')))).
Proof.
  intros E dsubst dsubst' T2 e e' v v' u u' T1 y K Hwfe Hwfd Hwfd' Hwft He_v He'_v' Hvt2_u Hv't2_u' Hfv.
  assert (y `notin` fv_te v).  
    apply notin_fv_te_mred with (e:=e).
      destruct He_v; auto.
      simpl. eauto using notin_fv_wf.
  assert (y `notin` fv_te v').  
    apply notin_fv_te_mred with (e:=e').
      destruct He'_v'; auto.
      simpl. eauto using notin_fv_wf.
  assert (y `notin` fv_te u).
    apply notin_fv_te_mred with (e:=(exp_tapp v (apply_delta_subst_typ dsubst T2))).
      destruct Hvt2_u; auto.
      apply wft_subst_closed with (E:=E) (E':=@nil (atom*binding)) (dsubst:=dsubst) in Hwft; auto.
      simpl. eauto using notin_fv_wf.
  assert (y `notin` fv_te u').
    apply notin_fv_te_mred with (e:=(exp_tapp v' (apply_delta_subst_typ dsubst' T2))).
      destruct Hv't2_u'; auto.
      apply wft_subst_closed with (E:=E) (E':=@nil (atom*binding)) (dsubst:=dsubst') in Hwft; auto.
      simpl. eauto using notin_fv_wf.
   auto.
Qed.

Lemma m_all_left_fv : forall t3 t2' e e' X t v v' (X4:atom) E E' K,
  wf_typ nil t3 K ->
  wf_typ nil t2' K->
  normalize (exp_tapp e t3) v ->
  normalize (exp_tapp e' t2') v' ->
  X `notin` union (fv_te e) (union (fv_te e')  (union (fv_tt t) (union (fv_env E) (union (fv_env E') (singleton X4))))) ->
  X `notin` union (fv_env E) 
                (union (union (union (singleton X4) {}) (fv_env E'))
                    (union (fv_tt (open_tt t X4)) (union (fv_te v) (fv_te v')))).
Proof.
  intros t3 t2' e e' X t v v' X4 E E' K Hwft3 Hwft2' Het3_v He't2'_v' Hfv.
  assert (X `notin` fv_te v).  
    apply notin_fv_te_mred with (e:=exp_tapp e t3).
      destruct Het3_v; auto.
      simpl. eauto using notin_fv_wf.
  assert (X `notin` fv_te v').
    apply notin_fv_te_mred with (e:=exp_tapp e' t2').
      destruct He't2'_v'; auto.
      simpl. eauto using notin_fv_wf.
  assert (X `notin` fv_tt (open_tt t X4)).
     unfold open_tt. unfold open_tt. destruct_notin.
     apply notin_fv_tt_open_tt_rec; auto.
  simpl_env. auto.
Qed.

Lemma m_all_right_fv : forall t3 t2' e e' X t v v' (X2:atom) E E' K,
  wf_typ nil t3 K ->
  wf_typ nil t2' K ->
  normalize (exp_tapp e t3) v ->
  normalize (exp_tapp e' t2') v' ->
  X `notin` union (fv_te e) (union (fv_te e')  (union (fv_tt t) (union (fv_env E) (union (fv_env E') (singleton X2))))) ->
  X `notin` union (fv_env E) 
                (union (union (union (singleton X2) {}) (fv_env E'))
                    (union (fv_tt (open_tt t X2)) (union (fv_te v) (fv_te v')))).
Proof.
  intros t3 t2' e e' X t v v' X2 E E' K Hwft3 Hwft2' Het3_v He't2'_v' Hfv.
  assert (X `notin` fv_te v).
    apply notin_fv_te_mred with (e:=exp_tapp e t3).
      destruct Het3_v; auto.
      simpl. eauto using notin_fv_wf.
  assert (X `notin` fv_te v').
    apply notin_fv_te_mred with (e:=exp_tapp e' t2').
      destruct He't2'_v'; auto.
      simpl. eauto using notin_fv_wf.
   destruct_notin; auto using notin_fv_tt_open_tt.
Qed.

Lemma m_with1_fv : forall e1 e1' X t1 u1 u1' E E',
  normalize e1 u1 ->
  normalize e1' u1' ->
  X `notin` union (fv_te e1) (union (fv_te e1') (union (fv_tt t1) (union (fv_env E) (fv_env E')))) ->
  X `notin` union (fv_env E) 
                (union (fv_env E')
                    (union (fv_tt t1) (union (fv_te u1) (fv_te u1')))).
Proof.
  intros e1 e1' X t1 u1 u1' E E' He1_u1 He1'_u1' Hfv.
  assert (X `notin` fv_te u1).
    apply notin_fv_te_mred with (e:=e1); auto.
      destruct He1_u1; auto.
  assert (X `notin` fv_te u1').
    apply notin_fv_te_mred with (e:=e1'); auto.
      destruct He1'_u1'; auto.
   destruct_notin. auto.
Qed.

Lemma m_with2_fv : forall e2 e2' X  t3 u2 u2' E E',
  normalize e2 u2 ->
  normalize e2' u2' ->
  X `notin` union (fv_te e2) (union (fv_te e2') (union (fv_tt t3) (union (fv_env E) (fv_env E')))) ->
  X `notin` union (fv_env E) 
                (union (fv_env E')
                    (union (fv_tt t3) (union (fv_te u2) (fv_te u2')))).
Proof.
  intros e2 e2' X t3 u2 u2' E E' He2_u2 He2'_u2' Hfv.
  assert (X `notin` fv_te u2).
    apply notin_fv_te_mred with (e:=e2); auto.
      destruct He2_u2; auto.
  assert (X `notin` fv_te u2').
    apply notin_fv_te_mred with (e:=e2'); auto.
      destruct He2'_u2'; auto.
  destruct_notin. auto.
Qed.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../../../metatheory" "-I" "../linf") ***
*** End: ***
 *)
