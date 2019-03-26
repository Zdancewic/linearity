(** Authors: Jianzhou Zhao. *)

Require Export LinF_OParametricity_Pre.

(******************************************************************)
(*                                      Macro                     *)
(******************************************************************)
Lemma m_delta_gamma_osubst_var : 
  forall E lE (gsubst lgsubst: gamma_subst) (dsubst : delta_subst) Env lEnv (x : atom) (t : typ) (e : exp),
  wf_lgamma_osubst E lE dsubst gsubst lgsubst Env lEnv ->
  binds x e gsubst -> 
  typing Env lEnv  e t -> 
  apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst x)) = e.
Proof.
  intros E lE gsubst lgsubst dsubst Env lEnv x t e Hwfg Hbinds Htyping.
  assert (H:=Hwfg).
  apply wf_lgamma_osubst__uniq in H.
  decompose [and] H.
  assert (x `notin` dom lgsubst) as J.
    apply wf_lgamma_osubst_disjoint in Hwfg.
    decompose [and] Hwfg.
    apply binds_In in Hbinds.
    unfold disjoint in H7. fsetdec.
  rewrite apply_gamma_subst_nfv; auto.
  apply disjoint_lgamma_osubst in Hwfg.
  decompose [and] Hwfg. clear Hwfg.
  rewrite gamma_osubst_var with (x:=x) (gsubst:=gsubst)(e:=e); auto.
    rewrite delta_osubst_closed_exp; auto.
      split; intros x0 x0notin.
        apply in_fv_te_typing with (X:=x0) in Htyping; auto.
        clear H0 H1 H2 H3 H4 H6 H5 H8 H9 H10 H11 H12 H13 H14 H16. solve_uniq.

        apply notin_fv_te_typing with (X:=x0) in Htyping; auto.
        clear H0 H1 H2 H3 H4 H6 H5 H8 H9 H10 H11 H12 H13 H14 H16. solve_uniq.
    split; intros x0 x0notin.
      apply in_fv_ee_typing with (x:=x0) in Htyping; auto.
      assert (x0 `in` dom Env \/ x0 `in` dom lEnv) as JJ. fsetdec.
      destruct JJ as [JJ | JJ].
        clear H0 H1 H2 H3 H4 H6 H5 H8 H7 H10 H11 H12 H13 H14 H16. solve_uniq.
        clear H0 H1 H2 H3 H4 H6 H5 H8 H7 H10 H11 H12 H13 H14 H9. solve_uniq.

      apply notin_fv_ee_typing with (y:=x0) in Htyping; auto.
      assert (x0 `notin` dom Env) as x0notinEnv.
        clear H0 H1 H2 H3 H4 H6 H5 H8 H7 H10 H11 H12 H13 H14 H16. solve_uniq.
      assert (x0 `notin` dom lEnv) as x0notinlEnv.
        clear H0 H1 H2 H3 H4 H6 H5 H8 H7 H10 H11 H12 H13 H14 H9. solve_uniq.
      auto.
Qed.

Lemma m_delta_lgamma_osubst_var : 
  forall E lE (gsubst lgsubst: gamma_subst) (dsubst : delta_subst) Env lEnv  (x : atom) (t : typ) (e : exp),
  wf_lgamma_osubst E lE dsubst gsubst lgsubst Env lEnv ->
  binds x e lgsubst -> 
  typing Env lEnv e t -> 
  apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst x)) = e.
Proof.
  intros E lE gsubst lgsubst dsubst Env lEnv x t e Hwfg Hbinds Htyping.
  assert (H:=Hwfg).
  apply wf_lgamma_osubst__uniq in H.
  decompose [and] H.
  assert (x `notin` dom gsubst) as J.
    apply wf_lgamma_osubst_disjoint in Hwfg.
    decompose [and] Hwfg.
    apply binds_In in Hbinds.
    unfold disjoint in H7. fsetdec.
  apply disjoint_lgamma_osubst in Hwfg.
  decompose [and] Hwfg. clear Hwfg.
  rewrite gamma_osubst_var with (x:=x) (gsubst:=lgsubst) (e:=e); auto.
    rewrite gamma_osubst_closed_exp; auto.
      rewrite delta_osubst_closed_exp; auto.
        split; intros x0 x0notin.
          apply in_fv_te_typing with (X:=x0) in Htyping; auto.
          clear H0 H1 H2 H3 H4 H6 H5 H8 H9 H10 H11 H12 H13 H14 H16. solve_uniq.

          apply notin_fv_te_typing with (X:=x0) in Htyping; auto.
          clear H0 H1 H2 H3 H4 H6 H5 H8 H9 H10 H11 H12 H13 H14 H16. solve_uniq.
      split; intros x0 x0notin.
        apply in_fv_ee_typing with (x:=x0) in Htyping; auto.
        assert (x0 `in` dom Env \/ x0 `in` dom lEnv) as JJ. fsetdec.
        destruct JJ as [JJ | JJ].
          clear H0 H1 H2 H3 H4 H6 H5 H8 H7 H10 H11 H12 H13 H14 H16. solve_uniq.
          clear H0 H1 H2 H3 H4 H6 H5 H8 H7 H10 H11 H12 H13 H14 H9. solve_uniq.

        apply notin_fv_ee_typing with (y:=x0) in Htyping; auto.
        assert (x0 `notin` dom Env) as x0notinEnv.
          clear H0 H1 H2 H3 H4 H6 H5 H8 H7 H10 H11 H12 H13 H14 H16. solve_uniq.
        assert (x0 `notin` dom lEnv) as x0notinlEnv.
          clear H0 H1 H2 H3 H4 H6 H5 H8 H7 H10 H11 H12 H13 H14 H9. solve_uniq.
        auto.
    split; intros x0 x0notin.
      apply in_fv_ee_typing with (x:=x0) in Htyping; auto.
      assert (x0 `in` dom Env \/ x0 `in` dom lEnv) as JJ. fsetdec.
      destruct JJ as [JJ | JJ].
        clear H0 H1 H2 H3 H4 H6 H5 H8 H7 H9 H11 H12 H13 H14 H16. solve_uniq.
        clear H0 H1 H2 H3 H4 H6 H5 H8 H7 H10 H11 H12 H13 H10 H9. solve_uniq.

      apply notin_fv_ee_typing with (y:=x0) in Htyping; auto.
      assert (x0 `notin` dom Env) as x0notinEnv.
        clear H0 H1 H2 H3 H4 H6 H5 H8 H7 H9 H11 H12 H13 H14 H16. solve_uniq.
      assert (x0 `notin` dom lEnv) as x0notinlEnv.
        clear H0 H1 H2 H3 H4 H6 H5 H8 H7 H10 H11 H12 H13 H10 H9. solve_uniq.
      auto.
Qed.

Lemma m_commut_osubst_open_ee: forall E lE dsubst gsubst lgsubst Env lEnv e1 (x:atom),
  wf_lgamma_osubst E lE dsubst gsubst lgsubst Env lEnv ->
  x `notin` dom gsubst ->
  x `notin` dom lgsubst ->
  apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (open_ee e1 x))) =
  open_ee (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e1))) x.
Proof.
  intros.
  rewrite commut_lgamma_osubst_open_ee with (E:=E) (dsubst:=dsubst) (D:=lE) (gsubst:=gsubst) (Env:=Env) (lEnv:=lEnv); auto.
  rewrite commut_gamma_osubst_open_ee with (E:=E) (dsubst:=dsubst) (D:=lE) (lgsubst:=lgsubst) (Env:=Env) (lEnv:=lEnv); auto.
  rewrite commut_delta_osubst_open_ee with (dE:=E) (Env:=Env); auto.
    rewrite apply_gamma_subst_nfv; auto.
    rewrite apply_gamma_subst_nfv; auto.
    rewrite apply_delta_subst_nfv; auto.
    apply wf_lgamma_osubst__wf_osubst in H. destruct H; auto.
Qed.

Lemma m_commut_osubst_open_te: forall E lE dsubst gsubst lgsubst Env lEnv e1 (X:atom),
  wf_lgamma_osubst E lE dsubst gsubst lgsubst Env lEnv ->
  X `notin` dom dsubst ->
  (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (open_te e1 X)))) =
  open_te (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e1))) X.
Proof.
  intros.
  rewrite commut_lgamma_osubst_open_te with (E:=E) (dsubst:=dsubst) (D:=lE) (gsubst:=gsubst) (Env:=Env) (lEnv:=lEnv); auto.
  rewrite commut_gamma_osubst_open_te with (E:=E) (dsubst:=dsubst)(D:=lE) (lgsubst:=lgsubst) (Env:=Env) (lEnv:=lEnv); auto.
    rewrite commut_delta_osubst_open_te with (dE:=E) (Env:=Env); auto.
    rewrite apply_gamma_subst_typ_nfv; auto.
    rewrite apply_gamma_subst_typ_nfv; auto.
    rewrite apply_delta_subst_typ_nfv; auto.
    apply wf_lgamma_osubst__wf_osubst in H. destruct H; auto.
Qed.

Lemma m_commut_osubst_typ_open_tt: forall E lE dsubst gsubst lgsubst Env lEnv T1 (X:atom),
  wf_lgamma_osubst E lE dsubst gsubst lgsubst Env lEnv ->
  X `notin` dom dsubst ->
  (apply_delta_subst_typ dsubst (open_tt T1 X)) =
  open_tt (apply_delta_subst_typ dsubst T1) X.
Proof.
  intros.
  rewrite commut_delta_osubst_open_tt with (dE:=E) (Env:=Env); auto.
    rewrite apply_delta_subst_typ_nfv; auto.
    apply wf_lgamma_osubst__wf_osubst in H. destruct H; auto.
Qed.

Lemma m_typing_osubst_typ_closed : forall E lE dsubst gsubst lgsubst Env lEnv V e1 (x:atom) T1,
  wf_delta_osubst E dsubst Env ->
  wf_lgamma_osubst E lE dsubst gsubst lgsubst Env lEnv ->
  wf_typ E V kn_nonlin ->
  x `notin` dom gsubst `union` dom lgsubst `union` dom Env `union` dom lEnv ->
  wf_env E ->
  typing ([(x, bind_typ V)] ++ E) lE (open_ee e1 x) T1 ->
  typing ([(x, bind_typ (apply_delta_subst_typ dsubst V))] ++ Env) lEnv
             (open_ee (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e1))) x) 
             (apply_delta_subst_typ dsubst T1).
Proof.
  intros E lE dsubst gsubst lgsubst Env lEnv V e1 x T1 Hwfd Hwfg HWFTV Hfv Henv Htyping.
  rewrite_env (nil++lE) in Htyping.
  assert (wf_env Env) as Wfe.
    apply wf_lgamma_osubst__wf_lenv in Hwfg. decompose [and] Hwfg; auto.
  assert (wf_lenv (apply_delta_subst_env dsubst [(x, bind_typ V)]++Env) lEnv) as wfle.
     simpl. simpl_env. 
     rewrite_env(nil ++ [(x, bind_typ (apply_delta_subst_typ dsubst V))]++Env). 
     apply wf_lenv_weakening; auto.
       apply wf_lgamma_osubst__wf_lenv in Hwfg. decompose [and] Hwfg; auto.
       simpl_env. apply wf_env_typ; auto.
         apply wft_osubst_closed with (E:=E) (E':=@nil (atom*binding)) (dsubst:=dsubst) (Env:=Env) in HWFTV; simpl_env; auto.
  apply typing_osubst_closed with (E:=E) (E':=[(x, bind_typ V)]) (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst) (Env:=Env) (lEnv:=lEnv) in Htyping; simpl_env; auto.
     rewrite m_commut_osubst_open_ee with (E:=E) (lE:=lE) (dsubst:=dsubst) (Env:=Env) (lEnv:=lEnv) in Htyping; simpl_env; auto.
Qed.

Lemma m_typing_osubst_ltyp_closed : forall E lE dsubst gsubst lgsubst Env lEnv V e1 (x:atom) T1,
  wf_delta_osubst E dsubst Env ->
  wf_lgamma_osubst E lE dsubst gsubst lgsubst Env lEnv ->
  wf_typ E V kn_lin ->
  x `notin` dom gsubst `union` dom lgsubst `union` dom Env `union` dom lEnv ->
  wf_env E ->
  typing E ([(x, lbind_typ V)] ++ lE) (open_ee e1 x) T1 ->
  typing Env ([(x, lbind_typ (apply_delta_subst_typ dsubst V))]++lEnv)
             (open_ee (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e1))) x) 
             (apply_delta_subst_typ dsubst T1).
Proof.
  intros E lE dsubst gsubst lgsubst Env lEnv V e1 x T1 Hwfd Hwfg HWFTV Hfv Henv Htyping.
  rewrite_env (nil++E) in Htyping.
  assert (wf_lenv Env lEnv) as Wfle.
    apply wf_lgamma_osubst__wf_lenv in Hwfg. decompose [and] Hwfg; auto.
  assert (wf_lenv Env (apply_delta_subst_lenv dsubst [(x, lbind_typ V)]++lEnv)) as wfle'.
     simpl. simpl_env. 
     apply wf_lenv_typ; auto.
       apply wft_osubst_closed with (E:=E) (E':=@nil (atom*binding)) (dsubst:=dsubst) (Env:=Env) in HWFTV; simpl_env; auto.
  apply typing_osubst_closed with (D:=lE) (D':=[(x, lbind_typ V)]) (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst) (Env:=Env) (lEnv:=lEnv) in Htyping; simpl_env; auto.
     rewrite m_commut_osubst_open_ee with (E:=E) (lE:=lE) (dsubst:=dsubst) (Env:=Env) (lEnv:=lEnv) in Htyping; simpl_env; auto.
Qed.

Lemma m_typing_osubst_kind_closed : forall E lE dsubst gsubst lgsubst Env lEnv e1 (X:atom) T1 K,
  wf_delta_osubst E dsubst Env ->
  wf_lgamma_osubst E lE dsubst gsubst lgsubst Env lEnv ->
  X `notin` dom dsubst `union` dom Env `union` dom lEnv ->
  wf_env E ->
  typing ([(X, bind_kn K)] ++ E) lE (open_te e1 X) (open_tt T1 X) ->
  typing ([(X, bind_kn K)] ++ Env) lEnv
             (open_te (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e1))) X) 
             (open_tt (apply_delta_subst_typ dsubst T1) X).
Proof.
  intros E lE dsubst gsubst lgsubst Env lEnv e1 X T1 K Hwfd Hwfg Hfv Henv Htyping.
  rewrite_env (nil++lE) in Htyping.
  assert (wf_lenv Env lEnv) as Wfle.
    apply wf_lgamma_osubst__wf_lenv in Hwfg. decompose [and] Hwfg; auto.
  assert (wf_lenv (apply_delta_subst_env dsubst [(X, bind_kn K)]++Env) lEnv) as wfle.
     simpl. simpl_env. 
     rewrite_env(nil ++ [(X, bind_kn K)]++Env). 
     apply wf_lenv_weakening; auto.
       simpl_env. apply wf_env_kn; auto.
  apply typing_osubst_closed with (E:=E) (E':=[(X, bind_kn K)]) (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst)(Env:=Env)(lEnv:=lEnv)in Htyping; auto.
      rewrite m_commut_osubst_open_te with (E:=E) (dsubst:=dsubst) (lE:=lE) (lgsubst:=lgsubst)(Env:=Env)(lEnv:=lEnv) in Htyping; eauto.
      rewrite m_commut_osubst_typ_open_tt with (E:=E) (gsubst:=gsubst)(lE:=lE) (lgsubst:=lgsubst)(Env:=Env)(lEnv:=lEnv) in Htyping; eauto.
Qed.

Lemma m_red_abs_osubst : forall E lE dsubst gsubst lgsubst Env lEnv V e1 x (y:atom) L T1 Q,
  wf_lgamma_osubst E lE dsubst gsubst lgsubst Env lEnv ->
  wf_typ E V kn_nonlin ->
  value x -> 
  typing Env lempty x (apply_delta_subst_typ dsubst V) ->
  y `notin` fv_ee e1 ->
  (forall x : atom, x `notin` L -> typing ([(x, bind_typ V)] ++ E) lE (open_ee e1 x) T1) ->
  red (exp_app
                  (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_abs Q V e1)))) x)
                  (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (subst_ee y x (open_ee e1 y))))).
Proof.
  intros E lE dsubst gsubst lgsubst Env lEnv V e1 x y L T1 Q Hwfg Hwft Hvalue Htyping Hfvy Hfr.
  rewrite <- subst_ee_intro; auto.
  assert (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst x)) =x) as Heq1.
     apply disjoint_lgamma_osubst in Hwfg. destruct Hwfg as [J1 [J2 [J3 [J4 [J5 [J6 [J7 [J8 [J9 J10]]]]]]]]].
     rewrite gamma_osubst_closed_exp; auto.
       rewrite gamma_osubst_closed_exp; auto.
         rewrite delta_osubst_closed_exp; auto.
           split;intros x0 x0notin.
             apply in_fv_te_typing with (X:=x0) in Htyping; auto.
             clear J1 J2 J4 J5 J6 J7 J8 J9 J10. solve_uniq.

             apply notin_fv_te_typing with (X:=x0) in Htyping; auto.
             clear J1 J2 J4 J5 J6 J7 J8 J9 J10. solve_uniq.         
         split; intros x0 x0notin.
           apply in_fv_ee_typing with (x:=x0) in Htyping; auto.
           assert (x0 `in` dom Env \/ x0 `in` dom lEnv) as JJ. fsetdec.
           destruct JJ as [JJ | JJ].
             clear J1 J2 J4 J3 J6 J7 J8 J9 J10. solve_uniq.
             clear J1 J2 J4 J3 J6 J7 J8 J10 J5. solve_uniq.

           apply notin_fv_ee_typing with (y:=x0) in Htyping; auto.
           assert (x0 `notin` dom Env) as x0notinEnv.
             clear J1 J2 J4 J3 J6 J7 J8 J9 J10. solve_uniq.
           assert (x0 `notin` dom lEnv) as x0notinlEnv.
             clear J1 J2 J4 J3 J6 J7 J8 J10 J5. solve_uniq.
           auto.
       rewrite gamma_osubst_closed_exp; auto.
         split; intros x0 x0notin.
           apply in_fv_ee_typing with (x:=x0) in Htyping; auto.
           assert (x0 `in` dom Env \/ x0 `in` dom lEnv) as JJ. fsetdec.
           destruct JJ as [JJ | JJ].
             clear J1 J2 J5 J3 J6 J7 J8 J9 J10. solve_uniq.
             clear J1 J2 J4 J3 J6 J7 J8 J9 J5. solve_uniq.

           apply notin_fv_ee_typing with (y:=x0) in Htyping; auto.
           assert (x0 `notin` dom Env) as x0notinEnv.
             clear J1 J2 J5 J3 J6 J7 J8 J9 J10. solve_uniq.
           assert (x0 `notin` dom lEnv) as x0notinlEnv.
             clear J1 J2 J4 J3 J6 J7 J8 J9 J5. solve_uniq.
           auto.

          split; intros x0 x0notin.
            apply in_fv_ee_typing with (x:=x0) in Htyping; auto.
            assert (x0 `in` dom Env \/ x0 `in` dom lEnv) as JJ. fsetdec.
            destruct JJ as [JJ | JJ].
              clear J1 J2 J4 J3 J6 J7 J8 J9 J10. solve_uniq.
              clear J1 J2 J4 J3 J6 J7 J8 J10 J5. solve_uniq.

            apply notin_fv_ee_typing with (y:=x0) in Htyping; auto.
            assert (x0 `notin` dom Env) as x0notinEnv.
              clear J1 J2 J4 J3 J6 J7 J8 J9 J10. solve_uniq.
            assert (x0 `notin` dom lEnv) as x0notinlEnv.
              clear J1 J2 J4 J3 J6 J7 J8 J10 J5. solve_uniq.
            auto.

  rewrite <- Heq1.
  rewrite commut_gamma_subst_abs.
  rewrite commut_gamma_subst_abs.
  assert (open_ee e1 (apply_delta_subst dsubst (apply_gamma_subst gsubst  (apply_gamma_subst lgsubst x))) = open_ee e1 x) as Heq2. 
     rewrite Heq1. auto. 
  rewrite Heq2.
  rewrite commut_lgamma_osubst_open_ee with (E:=E)(D:=lE)(dsubst:=dsubst)(gsubst:=gsubst)(Env:=Env)(lEnv:=lEnv); auto.
  rewrite commut_gamma_osubst_open_ee with (E:=E) (dsubst:=dsubst) (D:=lE) (lgsubst:=lgsubst)(Env:=Env)(lEnv:=lEnv); auto.
  apply red_abs_preserved_under_delta_osubst with (dE:=E)(Env:=Env); auto.
    apply wf_lgamma_osubst__wf_osubst in Hwfg. destruct Hwfg; auto.
  rewrite <- commut_gamma_subst_abs; auto.
  rewrite <- commut_gamma_osubst_open_ee with (E:=E) (dsubst:=dsubst) (D:=lE) (lgsubst:=lgsubst)(Env:=Env)(lEnv:=lEnv); auto.
  apply red_abs_preserved_under_gamma_osubst with (E:=E) (dsubst:=dsubst) (D:=lE) (lgsubst:=lgsubst)(Env:=Env)(lEnv:=lEnv); auto. 

  rewrite <- commut_gamma_subst_abs; auto.
  rewrite <- commut_lgamma_osubst_open_ee with (E:=E)(D:=lE)(dsubst:=dsubst)(gsubst:=gsubst)(Env:=Env)(lEnv:=lEnv); auto.
  apply red_abs_preserved_under_lgamma_osubst with (E:=E)(D:=lE)(dsubst:=dsubst)(gsubst:=gsubst)(Env:=Env)(lEnv:=lEnv); auto. 

  apply red_abs.
    apply expr_abs with (L:=L).
       assert (wf_typ E V kn_nonlin); auto.
       apply type_from_wf_typ in H; assumption.

       intros. apply Hfr in H.
       apply typing_regular in H. decompose [and] H. assumption.
   apply typing_regular in Htyping. decompose [and] Htyping. assumption.
Qed.

Lemma m_red_labs_osubst : forall E lE dsubst gsubst lgsubst Env lEnv lEnv' V e1 x (y:atom) L T1 Q,
  wf_lgamma_osubst E lE dsubst gsubst lgsubst Env lEnv ->
  wf_typ E V kn_lin ->
  value x -> 
  disjoint lEnv' lgsubst /\ disjoint lEnv' gsubst ->
  typing Env lEnv' x (apply_delta_subst_typ dsubst V) ->
  y `notin` fv_ee e1 ->
  (forall x : atom, x `notin` L -> typing E ([(x, lbind_typ V)] ++ lE) (open_ee e1 x) T1) ->
  red (exp_app
                  (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_abs Q V e1)))) x)
                  (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (subst_ee y x (open_ee e1 y))))).
Proof.
  intros E lE dsubst gsubst lgsubst Env lEnv lEnv' V e1 x y L T1 Q Hwfg Hwft Hvalue [Disj1 Disj2] Htyping Hfvy Hfr.
  rewrite <- subst_ee_intro; auto.
  assert (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst x)) =x) as Heq1.
    apply disjoint_lgamma_osubst in Hwfg. destruct Hwfg as [J1 [J2 [J3 [J4 [J5 [J6 [J7 [J8 [J9 J10]]]]]]]]].
     rewrite gamma_osubst_closed_exp; auto.
       rewrite gamma_osubst_closed_exp; auto.
         rewrite delta_osubst_closed_exp; auto.
           split;intros x0 x0notin.
             apply in_fv_te_typing with (X:=x0) in Htyping; auto.
             clear J1 J2 J4 J5 J6 J7 J8 J9 J10. solve_uniq.

             apply notin_fv_te_typing with (X:=x0) in Htyping; auto.
             clear J1 J2 J4 J5 J6 J7 J8 J9 J10. solve_uniq.         
         split; intros x0 x0notin.
           apply in_fv_ee_typing with (x:=x0) in Htyping; auto.
           assert (x0 `in` dom Env \/ x0 `in` dom lEnv') as JJ. fsetdec.
           destruct JJ as [JJ | JJ].
             clear J1 J2 J4 J3 J6 J7 J8 J9 J10. solve_uniq.
             clear J1 J2 J4 J3 J6 J7 J8 J10 J5. solve_uniq.

           apply notin_fv_ee_typing with (y:=x0) in Htyping; auto.
           assert (x0 `notin` dom Env) as x0notinEnv.
             clear J1 J2 J4 J3 J6 J7 J8 J9 J10. solve_uniq.
           assert (x0 `notin` dom lEnv') as x0notinlEnv.
             clear J1 J2 J4 J3 J6 J7 J8 J10 J5. solve_uniq.
           auto.
       rewrite gamma_osubst_closed_exp; auto.
         split; intros x0 x0notin.
           apply in_fv_ee_typing with (x:=x0) in Htyping; auto.
           assert (x0 `in` dom Env \/ x0 `in` dom lEnv') as JJ. fsetdec.
           destruct JJ as [JJ | JJ].
             clear J1 J2 J5 J3 J6 J7 J8 J9 J10. solve_uniq.
             clear J1 J2 J4 J3 J6 J7 J8 J9 J5. solve_uniq.

           apply notin_fv_ee_typing with (y:=x0) in Htyping; auto.
           assert (x0 `notin` dom Env) as x0notinEnv.
             clear J1 J2 J5 J3 J6 J7 J8 J9 J10. solve_uniq.
           assert (x0 `notin` dom lEnv') as x0notinlEnv.
             clear J1 J2 J4 J3 J6 J7 J8 J9 J5. solve_uniq.
           auto.

          split; intros x0 x0notin.
            apply in_fv_ee_typing with (x:=x0) in Htyping; auto.
            assert (x0 `in` dom Env \/ x0 `in` dom lEnv') as JJ. fsetdec.
            destruct JJ as [JJ | JJ].
              clear J1 J2 J4 J3 J6 J7 J8 J9 J10. solve_uniq.
              clear J1 J2 J4 J3 J6 J7 J8 J10 J5. solve_uniq.

            apply notin_fv_ee_typing with (y:=x0) in Htyping; auto.
            assert (x0 `notin` dom Env) as x0notinEnv.
              clear J1 J2 J4 J3 J6 J7 J8 J9 J10. solve_uniq.
            assert (x0 `notin` dom lEnv') as x0notinlEnv.
              clear J1 J2 J4 J3 J6 J7 J8 J10 J5. solve_uniq.
            auto.

  rewrite <- Heq1.
  rewrite commut_gamma_subst_abs.
  rewrite commut_gamma_subst_abs.
  assert (open_ee e1 (apply_delta_subst dsubst (apply_gamma_subst gsubst  (apply_gamma_subst lgsubst x))) = open_ee e1 x) as Heq2. 
     rewrite Heq1. auto. 
  rewrite Heq2.
  rewrite commut_lgamma_osubst_open_ee with (E:=E)(D:=lE)(dsubst:=dsubst)(gsubst:=gsubst)(Env:=Env)(lEnv:=lEnv); auto.
  rewrite commut_gamma_osubst_open_ee with (E:=E) (dsubst:=dsubst) (D:=lE) (lgsubst:=lgsubst)(Env:=Env)(lEnv:=lEnv); auto.
  apply red_abs_preserved_under_delta_osubst with (dE:=E)(Env:=Env); auto.
    apply wf_lgamma_osubst__wf_osubst in Hwfg. destruct Hwfg; auto.
  rewrite <- commut_gamma_subst_abs; auto.
  rewrite <- commut_gamma_osubst_open_ee with (E:=E) (dsubst:=dsubst) (D:=lE) (lgsubst:=lgsubst)(Env:=Env)(lEnv:=lEnv); auto.
  apply red_abs_preserved_under_gamma_osubst with (E:=E) (dsubst:=dsubst) (D:=lE) (lgsubst:=lgsubst)(Env:=Env)(lEnv:=lEnv); auto. 

  rewrite <- commut_gamma_subst_abs; auto.
  rewrite <- commut_lgamma_osubst_open_ee with (E:=E)(D:=lE)(dsubst:=dsubst)(gsubst:=gsubst)(Env:=Env)(lEnv:=lEnv); auto.
  apply red_abs_preserved_under_lgamma_osubst with (E:=E)(D:=lE)(dsubst:=dsubst)(gsubst:=gsubst)(Env:=Env)(lEnv:=lEnv); auto. 

  apply red_abs.
    apply expr_abs with (L:=L).
       assert (wf_typ E V kn_lin); auto.
       apply type_from_wf_typ in H; assumption.

       intros. apply Hfr in H.
       apply typing_regular in H. decompose [and] H. assumption.
   apply typing_regular in Htyping. decompose [and] Htyping. assumption.
Qed.

Lemma m_red_tabs_osubst : forall E lE dsubst gsubst lgsubst Env lEnv e1 (X:atom) t2 L T1 K,
  wf_lgamma_osubst E lE dsubst gsubst lgsubst Env lEnv ->
  wf_typ Env t2 K ->
  X `notin` fv_te e1 ->
  (forall X : atom,  X `notin` L -> typing ([(X, bind_kn K)] ++ E) lE (open_te e1 X) (open_tt T1 X)) ->
  red (exp_tapp
                 (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (exp_tabs K e1)))) t2)
                 (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst (subst_te X t2 (open_te e1 X))))). 
Proof.
  intros E lE dsubst gsubst lgsubst Env lEnv e1 X t2 L K T1 Hwfg Hwfor Hfv Hfr.
  rewrite <- subst_te_intro; auto.
  assert (apply_delta_subst_typ dsubst (apply_gamma_subst_typ gsubst (apply_gamma_subst_typ lgsubst t2)) =t2) as Heq1.
     erewrite gamma_osubst_closed_typ; eauto.
     erewrite gamma_osubst_closed_typ; eauto.
     erewrite delta_osubst_closed_typ; eauto.
       apply disjoint_lgamma_osubst in Hwfg. destruct Hwfg as [J1 [J2 [J3 [J4 [J5 [J6 [J7 [J8 [J9 J10]]]]]]]]].
       unfold disjdom. split; intros x xnotin.
         apply in_fv_wf with (X:=x) in Hwfor; auto. solve_uniq.
         apply notin_fv_wf with (X:=x) in Hwfor; auto. solve_uniq.
  rewrite <- Heq1.
  rewrite commut_gamma_subst_tabs.
  rewrite commut_gamma_subst_tabs.
  assert (open_te e1 (apply_delta_subst_typ dsubst (apply_gamma_subst_typ gsubst (apply_gamma_subst_typ lgsubst t2))) = open_te e1 t2) as Heq2.
     rewrite Heq1. auto. 
  rewrite Heq2.
  rewrite commut_lgamma_osubst_open_te with (E:=E)(D:=lE)(dsubst:=dsubst)(gsubst:=gsubst)(Env:=Env)(lEnv:=lEnv); auto.
  rewrite commut_gamma_osubst_open_te with  (E:=E) (dsubst:=dsubst)(D:=lE) (lgsubst:=lgsubst)(Env:=Env)(lEnv:=lEnv); auto.
  apply red_tabs_preserved_under_delta_osubst with (dE:=E)(Env:=Env); auto.
    apply wf_lgamma_osubst__wf_osubst in Hwfg. destruct Hwfg; auto.
  rewrite <- commut_gamma_subst_tabs.
  rewrite <- commut_gamma_osubst_open_te with  (E:=E) (dsubst:=dsubst)(D:=lE) (lgsubst:=lgsubst)(Env:=Env)(lEnv:=lEnv); auto.
  apply red_tabs_preserved_under_gamma_osubst with  (E:=E) (dsubst:=dsubst)(D:=lE) (lgsubst:=lgsubst)(Env:=Env)(lEnv:=lEnv); auto.

  rewrite <- commut_gamma_subst_tabs; auto.
  rewrite <- commut_lgamma_osubst_open_te with (E:=E)(D:=lE)(dsubst:=dsubst)(gsubst:=gsubst)(Env:=Env)(lEnv:=lEnv); auto.
  apply red_tabs_preserved_under_lgamma_osubst with (E:=E)(D:=lE)(dsubst:=dsubst)(gsubst:=gsubst)(Env:=Env)(lEnv:=lEnv); auto. 

  apply red_tabs.
      apply expr_tabs with (L:=L).
          intros. apply Hfr in H.
          apply typing_regular in H. decompose [and] H. assumption.
      eapply type_from_wf_typ with (E:=Env); eauto.
Qed.

Lemma m_typing_ovar_stronger : 
  forall (E E' : env) (dsubst : delta_subst) (X : atom) x k t1 t2 (dsubst' : delta_subst) K Env lEnv,
  wf_delta_osubst (E' ++ [(X, bind_kn K)] ++ E) (dsubst' ++ [(X, (apply_delta_subst_typ (dsubst' ++ dsubst) t2))]  ++ dsubst) Env ->
  X `notin` (fv_env E) `union` (fv_env E') `union` (fv_env Env)->
  X `notin` fv_tt t1 ->
  ddom_env E[=]dom dsubst ->
  ddom_env E'[=]dom dsubst' ->
  wf_typ Env (apply_delta_subst_typ (dsubst' ++ dsubst) t2) K ->
  wf_typ (E'++E) t2 K ->
  typing Env lEnv x (apply_delta_subst_typ (dsubst'++dsubst) (open_tt_rec k t2 t1)) ->
  typing Env lEnv x
         (apply_delta_subst_typ
            (dsubst' ++
             [(X, apply_delta_subst_typ (dsubst' ++ dsubst) t2)] ++ dsubst)
            (open_tt_rec k X t1)).
Proof.
  intros E E' dsubst X e k t1 t2 dsubst' K Env lEnv Hwfd Hfv Hfvt1 Heq Heq' Hwft2 Hwft Htyping.
  rewrite delta_osubst_opt with (E:=E) (E':=E')(Env:=Env)(K:=K); auto.
  rewrite swap_subst_tt_odsubst with (E:=E'++E)(Env:=Env)(K:=K); simpl_env; auto.
    simpl in Hfv; rewrite <- subst_tt_intro_rec; auto.
    apply odsubst_stronger in Hwfd; eauto.
    apply notin_fv_wf with (X:=X) in Hwft; simpl_env; auto.
Qed.

Lemma m_typing_ovar_weaken : 
  forall (E E' : env) (dsubst : delta_subst) (X : atom) x k t1 t2 (dsubst' : delta_subst) K Env lEnv,
  wf_delta_osubst (E' ++ E) (dsubst' ++ dsubst) Env->
  X `notin` (dom E) `union` (fv_env E') `union` (fv_env Env)->
  X `notin` fv_tt t1 ->
  ddom_env E[=]dom dsubst ->
  ddom_env E'[=]dom dsubst' ->
  wf_typ Env (apply_delta_subst_typ (dsubst' ++ dsubst) t2) K ->
  wf_typ (E'++E) t2 K ->
  typing Env lEnv x (apply_delta_subst_typ (dsubst'++[(X, apply_delta_subst_typ (dsubst' ++ dsubst) t2)]++dsubst) (open_tt_rec k X t1)) ->
  typing Env lEnv x (apply_delta_subst_typ (dsubst' ++ dsubst) (open_tt_rec k t2 t1)).
Proof.
  intros E E' dsubst X e k t1 t2 dsubst' K Env lEnv Hwfd Hfv Hfvt1 Heq Heq' Hwft2 Hwft Htyping.
  rewrite delta_osubst_opt with (E:=E) (E':=E') (Env:=Env) (K:=K) in Htyping; eauto.
  rewrite swap_subst_tt_odsubst with (E:=E'++E) (Env:=Env) (K:=K) in Htyping; simpl_env; eauto.
    rewrite <- subst_tt_intro_rec in Htyping; auto.
    apply notin_fv_wf with (X:=X) in Hwft; simpl_env; auto.
    apply odsubst_weaken; eauto.
Qed.

Lemma m_typing_onormalization_fv : forall (e v : exp) (T : typ) X Env lEnv,
  typing Env lEnv e T -> 
  normalize e v -> 
  X `notin` dom Env ->
  X `notin` fv_te v.
Proof.
  intros e v T X Env lEnv Htypinge Hnorm Hfv.
  apply preservation_normalization with (v:=v) in Htypinge; auto.
  apply notin_fv_te_typing with (X:=X) in Htypinge; auto.
Qed.

Lemma m_typing_onormalization_arrow_fv_stronger :
  forall (E E' : env) (dsubst : delta_subst) (X : atom) e x k t1 t2 (dsubst' : delta_subst) u Env lEnv,
  X `notin` fv_te e `union` dom Env ->
  typing Env lEnv x
         (apply_delta_subst_typ
            (dsubst' ++ dsubst)
            (open_tt_rec k t2 t1)) ->
  normalize (exp_app e x) u ->
  X `notin` fv_te u.
Proof.
  intros E E' dsubst X e x k t1 t2 dsubst' u Env lEnv Hfv Htypingx Hnorm_exu.
  apply notin_fv_te_mred with (e:=exp_app e x).
       destruct Hnorm_exu; auto.
       simpl. eauto using notin_fv_te_typing.
Qed.

Lemma m_typing_onormalization_arrow_fv_weaken :
  forall (E E' : env) (dsubst : delta_subst) (X : atom) e x k t1 t2 (dsubst' : delta_subst) u Env lEnv,
  X `notin` fv_te e `union` dom Env ->
  typing Env lEnv x
         (apply_delta_subst_typ
            (dsubst' ++ [(X, apply_delta_subst_typ (dsubst' ++ dsubst) t2)] ++ dsubst)
            (open_tt_rec k X t1)) ->
  normalize (exp_app e x) u ->
  X `notin` fv_te u.
Proof.
  intros E E' dsubst X e x k t1 t2 dsubst' u Env lEnv Hfv Htypingx Hnorm_exu.
  apply notin_fv_te_mred with (e:=exp_app e x).
       destruct Hnorm_exu; auto.
       simpl. eauto using notin_fv_te_typing.
Qed.

Lemma m_ocongr_tapp : forall E lE dsubst gsubst lgsubst Env lEnv T2 e1 v u K, 
   wf_delta_osubst E dsubst Env ->
   wf_lgamma_osubst E lE dsubst gsubst lgsubst Env lEnv ->
   wf_typ E T2 K ->
   normalize (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e1)))  v ->
   normalize (exp_tapp v (apply_delta_subst_typ dsubst T2)) u ->
   normalize (exp_tapp (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e1)))
                              (apply_delta_subst_typ dsubst (apply_gamma_subst_typ gsubst (apply_gamma_subst_typ lgsubst T2)))) u.
Proof.
   intros E lE dsubst gsubst lgsubst Env lEnv T2 e1 v u K Hwfd Hwfg Hwft He1_v Hvt1_u.
   apply congr_tapp with (v1:=v); auto.
      apply type_preserved_under_delta_osubst with (E:=E) (Env:=Env); auto.
         apply type_preserved_under_gamma_osubst with  (E:=E) (dsubst:=dsubst)(D:=lE) (lgsubst:=lgsubst) (Env:=Env) (lEnv:=lEnv); auto.
           apply type_from_wf_typ in Hwft. assumption.
Qed.

Lemma m_tapp_ofv : forall E dsubst dsubst' Env T2 e e' v v' u u' T1 y K lEnv,
   wf_env E ->
   wf_delta_osubst E dsubst Env ->
   wf_delta_osubst E dsubst' Env ->
   wf_typ E T2 K ->
   normalize e v ->
   normalize e' v' ->
   normalize (exp_tapp v (apply_delta_subst_typ dsubst T2)) u ->
   normalize (exp_tapp v' (apply_delta_subst_typ dsubst' T2)) u' ->
   y `notin` union (fv_env E) (union (fv_tt T1) (union (fv_te e) (union (fv_te e') (union (fv_env Env) (fv_lenv lEnv)))))->
   y `notin` union (fv_env E) (union (fv_env nil) (union (fv_tt T1) (union (fv_te u) (union (fv_te u') (union (fv_env Env) (fv_lenv lEnv)))))).
Proof.
  intros E dsubst dsubst' Env T2 e e' v v' u u' T1 y K lEnv Hwfe Hwfd Hwfd' Hwft He_v He'_v' Hvt2_u Hv't2_u' Hfv.
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
      apply wft_osubst with (E:=E) (Env:=Env) (dsubst:=dsubst) in Hwft; auto.
      simpl. eauto using notin_fv_wf.
  assert (y `notin` fv_te u').
    apply notin_fv_te_mred with (e:=(exp_tapp v' (apply_delta_subst_typ dsubst' T2))).
      destruct Hv't2_u'; auto.
      apply wft_osubst with (E:=E) (Env:=Env) (dsubst:=dsubst') in Hwft; auto.
      simpl. eauto using notin_fv_wf.
   auto.
Qed.

Lemma m_all_ofv : forall t3 t2' e e' X t v v' (X4:atom) E E' K Env lEnv, 
  wf_typ Env t3 K ->
  wf_typ Env t2' K->
  normalize (exp_tapp e t3) v ->
  normalize (exp_tapp e' t2') v' ->
  X `notin` union (fv_te e) (union (fv_te e')  (union (fv_tt t) (union (fv_env E) (union (fv_env E') (union (singleton X4) (union (fv_env Env) (fv_lenv lEnv))))))) ->
  X `notin` union (fv_env E) 
                (union (union (union (singleton X4) {}) (fv_env E'))
                    (union (fv_tt (open_tt t X4)) (union (fv_te v) (union (fv_te v') (union (fv_env Env) (fv_lenv lEnv)))))).
Proof.
  intros t3 t2' e e' X t v v' X4 E E' K Env lEnv Hwft3 Hwft2' Het3_v He't2'_v' Hfv.
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

Lemma m_with1_fv : forall e1 e1' X t1 u1 u1' E E' Env lEnv, 
  normalize e1 u1 ->
  normalize e1' u1' ->
  X `notin` union (fv_te e1) (union (fv_te e1') (union (fv_tt t1) (union (fv_env E) (union (fv_env E')  (union (fv_env Env) (fv_lenv lEnv)))))) ->
  X `notin` union (fv_env E) 
                (union (fv_env E')
                    (union (fv_tt t1) (union (fv_te u1) (union (fv_te u1')  (union (fv_env Env) (fv_lenv lEnv)))))).
Proof.
  intros e1 e1' X t1 u1 u1' E E' Env lEnv He1_u1 He1'_u1' Hfv.
  assert (X `notin` fv_te u1).
    apply notin_fv_te_mred with (e:=e1); auto.
      destruct He1_u1; auto.
  assert (X `notin` fv_te u1').
    apply notin_fv_te_mred with (e:=e1'); auto.
      destruct He1'_u1'; auto.
   destruct_notin. auto.
Qed.

Lemma m_with2_fv : forall e2 e2' X  t3 u2 u2' E E' Env lEnv,
  normalize e2 u2 ->
  normalize e2' u2' ->
  X `notin` union (fv_te e2) (union (fv_te e2') (union (fv_tt t3) (union (fv_env E) (union (fv_env E')  (union (fv_env Env) (fv_lenv lEnv)))))) ->
  X `notin` union (fv_env E) 
                (union (fv_env E')
                    (union (fv_tt t3) (union (fv_te u2) (union (fv_te u2')  (union (fv_env Env) (fv_lenv lEnv)))))).
Proof.
  intros e2 e2' X t3 u2 u2' E E' Env lEnv He2_u2 He2'_u2' Hfv.
  assert (X `notin` fv_te u2).
    apply notin_fv_te_mred with (e:=e2); auto.
      destruct He2_u2; auto.
  assert (X `notin` fv_te u2').
    apply notin_fv_te_mred with (e:=e2'); auto.
      destruct He2'_u2'; auto.
  destruct_notin. auto.
Qed.

Lemma m_delta_osubst_opt : forall (E E' : env) (dsubst : delta_subst) (X : atom)
         (t : delta_binding) (t' : typ) (dsubst' : delta_subst) Env lEnv e t2 K,
  wf_delta_osubst (E' ++ E) (dsubst' ++ dsubst) Env ->
  X `notin` (dom E) `union` (dom E') `union` dom Env `union` dom lEnv ->
  ddom_env E[=]dom dsubst ->
  ddom_env E'[=]dom dsubst' ->
  wf_typ Env (apply_delta_subst_typ (dsubst' ++ dsubst) t2) K ->
  typing Env lEnv e (apply_delta_subst_typ (dsubst' ++ dsubst) t2) ->
  typing Env lEnv e (apply_delta_subst_typ (dsubst' ++ X ~ apply_delta_subst_typ (dsubst' ++ dsubst) t2 ++ dsubst) X).
Proof.
  intros.
  rewrite delta_osubst_opt with (E:=E) (E':=E')(Env:=Env) (K:=K); eauto.
     simpl. destruct (X==X).
       rewrite delta_osubst_closed_typ; auto.
         unfold disjdom.
         apply disjoint_delta_osubst in H.
         destruct H as [J1 J2].
         split; intros x xnotin.
           apply in_fv_wf with (X:=x) in H3; auto.
             clear H0 xnotin. solve_uniq.
           apply notin_fv_wf with (X:=x) in H3; auto.
             clear H0 J1 H1 H2 e0. simpl_env in xnotin. solve_uniq.
       contradict n; auto.
     eapply odsubst_weaken; eauto.
Qed.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../../../metatheory" "-I" "../linf") ***
*** End: ***
 *)
