Require Export Soundness.

Fixpoint from_env_to_genv (G : env) {struct G} : genv :=
  match G with 
  | nil => gempty 
  | h :: t =>
    match h with 
    | (A, bind_kn K) => (A, gbind_kn K) :: (from_env_to_genv t)
    | (A, bind_typ T) => (A, gbind_typ T) :: (from_env_to_genv t)
    end
  end.

Lemma dom_G_remain_2 : forall G, 
  dom (from_env_to_genv G)  = dom G.
Proof with eauto.
  intros G. induction G...
   destruct a. simpl. destruct b; simpl; rewrite IHG...
Qed.

Lemma uniq_env_compl : forall G, 
  uniq G ->
  uniq (from_env_to_genv G).
Proof with eauto.
  intros G Uniq.
  induction G; simpl...
   destruct a. destruct b.
   apply uniq_cons. apply IHG. solve_uniq.
    rewrite dom_G_remain_2. solve_uniq.
   apply uniq_cons. apply IHG. solve_uniq.
    rewrite dom_G_remain_2. solve_uniq.
Qed.
    
Lemma uniq_denv_sound : forall D,
  uniq D ->
  uniq (from_denv_to_lenv D).
Proof with eauto.
  intros D Uniq.
  induction D; simpl...
   destruct a. 
    apply uniq_cons.
     apply IHD. solve_uniq. rewrite <- dom_D_remain; solve_uniq.
Qed.

Lemma binds_typ_compl : forall x T G,
  binds x (bind_typ T) G ->
  binds x (gbind_typ T) (from_env_to_genv G).
Proof with eauto.
  intros x T G H.
  induction G...
   destruct a.
    apply binds_cons_1 in H.
     destruct H.
      destruct H as [EQ Bind].
       subst. simpl...
      apply IHG in H.
       destruct b; simpl...
Qed.

Lemma binds_kn_compl : forall X K G,
  binds X (bind_kn K) G ->
  binds X (gbind_kn K) (from_env_to_genv G).
Proof with eauto.
  intros X K G Binds.
  induction G...
  destruct a.
   apply binds_cons_1 in Binds.
   destruct Binds.
    destruct H. subst. simpl...
     destruct b; simpl...
Qed.


Lemma wf_typ_compl : forall G T K K',
  wf_typ G T K ->
  kn_order K K' ->
  wf_atyp (from_env_to_genv G) T K'.
Proof with eauto.
  intros G T K K' Wft Ord.
  generalize dependent K'.
  (wf_typ_cases (induction Wft) Case); intros...
  Case "wf_typ_var".
   apply binds_kn_compl in H0.
   apply wf_atyp_var with K... 
    apply uniq_env_compl...
  Case "wf_typ_all".
   apply wf_atyp_all with L. simpl in H0.
   intros x Notin.  rewrite_env ((x, gbind_kn K1) :: from_env_to_genv E). 
   apply H0...
  Case "wf_typ_with".
   skip.
  Case "wf_typ_sub".
   apply IHWft. destruct K'...
Qed.
   
Lemma wf_env_compl : forall G, 
  wf_env G ->
  wf_genv (from_env_to_genv G).
Proof with eauto.
  intros G Wfe.
  induction G...
   destruct a.
   simpl. destruct b; simpl_env.
    apply wf_genv_kn...
     apply IHG. inversion Wfe...
     rewrite dom_G_remain_2. inversion Wfe...
    apply wf_genv_typ...
     apply IHG. inversion Wfe... inversion Wfe; subst...
     apply wf_typ_compl with kn_nonlin...
    rewrite dom_G_remain_2.
    inversion Wfe...
Qed.
      
Lemma wf_lenv_compl : forall G D,
  wf_lenv G D ->
  wf_denv (from_env_to_genv G) (from_lenv_to_denv D).
Proof with eauto.
  intros G D Wfl.
  induction Wfl; subst...
   simpl. apply wf_env_compl in H.
    apply wf_denv_empty...
   simpl. simpl_env.
    eapply wf_denv_typ. eauto.
    assert (wf_atyp (from_env_to_genv E) T kn_lin).
     apply wf_typ_compl with kn_lin...
    eauto.
    rewrite dom_G_remain_2. eauto.
    rewrite <- dom_D_remain_2. auto.
    rewrite  dom_D_remain_2 in H0.
    rewrite_env ((x, T) :: from_lenv_to_denv D). apply uniq_cons.
     eapply uniq_from_wf_denv_lin... auto.
   apply Equal_refl.
Qed.

Lemma permute_denv_weakening : forall D1L D1R D2L D2R D : denv,
  uniq (D1L ++ D ++ D1R) ->
  permute (D1L ++ D1R) (D2L ++ D2R) ->
  permute (D1L ++ D ++ D1R) (D2L ++ D ++ D2R).
Proof with eauto.
  intros D1L D1R D2L D2R D Uniq Perm.
  induction D...
  destruct a. simpl_env in *.
  apply permute_weakening...
   intros x0 y. decide equality.
  remember (beq_typ b t0) as e.
  destruct e.
   apply sym_eq in Heqe.
   apply beq_typ_iff_eq in Heqe; subst...
   right. unfold not. intros contra.
    apply beq_typ_iff_eq in contra. rewrite contra in Heqe. inversion Heqe.
Qed.

Lemma denv_refl : forall D,
  D = from_lenv_to_denv (from_denv_to_lenv D).
Proof with eauto.
  intros D.
  induction D...
  destruct a. simpl. rewrite <- IHD...
Qed.

Lemma binds_permute : forall x T ( D1 D2 : denv), 
  binds x T D1 ->
  permute D2 D1 ->
  binds x T D2.
Proof with eauto.
  intros x T D1 D2 H Perm.
  induction Perm; simpl_env...
   analyze_binds H.
Qed.

Lemma disjoint_sound : forall D1 D2,
  disjoint (from_lenv_to_denv D1) (from_lenv_to_denv D2) ->
  disjoint D1 D2.
Proof with eauto.
  intros D1 D2 Disj.
  generalize dependent D2.
  induction D1; intros; subst...
   destruct a... destruct l... simpl in *.
    assert (disjoint D1 D2).
     apply IHD1... solve_uniq.
     simpl_env.
     unfold disjoint in *. simpl_env in *.
     rewrite dom_D_remain_2. rewrite dom_D_remain_2. fsetdec.
Qed.

Lemma disjoint_compl : forall D1 D2, 
  disjoint D1 D2 ->
  disjoint (from_lenv_to_denv D1) (from_lenv_to_denv D2).
Proof with eauto.
  intros D1 D2 Disj.
  generalize dependent D2.
  induction D1; intros; subst; simpl...
  destruct a. destruct l.
   unfold disjoint in *. simpl_env in *.
   rewrite <- dom_D_remain_2. rewrite <- dom_D_remain_2. fsetdec.
Qed.

Lemma wf_lenv_lin_weakening_2 : forall E D1 D2 D3,
  wf_lenv E (D1 ++ D2) ->
  wf_lenv E D3 ->
  uniq (D1 ++ D3 ++ D2) ->
  wf_lenv E (D1 ++ D3 ++ D2).
Proof with eauto.
  intros E D1 D2 D3 Wfl12 Wfl3 Uniq.
  generalize dependent D1.
  generalize dependent D2.
  induction D3; intros; subst...
   destruct a. destruct l. simpl_env in *.
   apply wf_lenv_lin_weakening...
    inversion Wfl3...
    apply IHD3... inversion Wfl3...
    inversion Wfl3... solve_uniq.
Qed.

Lemma perm_conc_commu : forall D1 D2 : denv,
  uniq (D1 ++ D2) ->
  permute (D1 ++ D2) (D2 ++ D1).
Proof with eauto.
  intros D1 D2 Uniq.
  apply eq_uniq_implies_perm...
   rewrite_env (D1 ++ dempty ++ D2).
   rewrite_env (D2 ++ dempty ++ D1).
   apply disjoint_denv_cons_3commut_aux. simpl_env...
   solve_uniq.
Qed.

Theorem Completeness : forall E D1 e T D2 D3,
  typing E D1 e T ->
  wf_lenv E D3 ->
  permute D3 (D2 ++ D1) ->
  exists D2',
    permute D2 D2' /\
    atyping (from_env_to_genv E) (from_lenv_to_denv D3) e T (from_lenv_to_denv D2').
Proof with eauto.
  intros E D1 e T D2 D3 Typing WflenvD3 Perm.
  assert (uniq D3) as Uniq3.
   apply uniq_from_wf_lenv with E...
  assert (uniq (D2 ++ D1)) as Uniq21.
   apply uniq_env_permute with D3...
  assert (uniq D2) as Uniq2.
   solve_uniq.
  assert (uniq D1) as Uniq1.
   solve_uniq.
  assert (wf_lenv E (D2 ++ D1)) as Wflenv.
   eapply wf_lenv_permute...
  generalize dependent D3.
  generalize dependent D2.
  (typing_cases (induction Typing) Case); intros; subst; simpl_env in *.
  Case "typing_var". 
   apply binds_typ_compl in H0.

   exists D3.
   repeat split; simpl_env...
    apply permute_sym...
     apply eq_lbinding_dec.
   apply atyping_uvar...
      apply wf_lenv_compl...
  
  Case "typing_lvar".
   assert (uniq (from_lenv_to_denv (D2 ++ [(x, lbind_typ T)]))) as Uniq21'.
    apply uniq_lenv_compl...
   assert (uniq (from_lenv_to_denv D2 ++ from_lenv_to_denv [(x, lbind_typ T)])) as Uniq21D.
    rewrite lenv_to_denv_conc in Uniq21'...
    
   exists D2.
   repeat split; simpl; simpl_env...
    apply permute_refl.
    assert (permute (from_lenv_to_denv D3) (from_lenv_to_denv D2 ++ [(x, T)])) as Perm2.
      apply perm_lenv_to_denv_2 in Perm.
      rewrite lenv_to_denv_conc in Perm. simpl in Perm. simpl_env in Perm...

    apply atyping_lvar...
     assert (binds x T (from_lenv_to_denv D2 ++ [(x, T)]))...
     eapply binds_permute...

     apply wf_lenv_compl in WflenvD3...
     solve_uniq.
     eapply Equal_trans.
      apply dmap_remove_preserves_Equal.
      eapply perm_uniq_implies_eq...
       apply uniq_lenv_compl...
      rewrite_env (from_lenv_to_denv D2 ++ dempty).
      rewrite_env (from_lenv_to_denv D2 ++ [(x, T)] ++ dempty).
      apply denv_remove_mid.
       simpl_env. rewrite_env (from_lenv_to_denv [(x, lbind_typ T)]).
       rewrite <- lenv_to_denv_conc...
  
  Case "typing_abs".
   pick fresh x for (union L
                 (union (fv_te e1)
                    (union (fv_ee e1)
                       (union (fv_tt T1) (union (fv_tt T2) (union (dom D2) (union (dom D) (dom E)))))))).
   assert (wf_lenv ([(x, bind_typ T1)] ++ E) (D2 ++ D)) as WflWeak1.
     rewrite_env (empty ++ [(x, bind_typ T1)] ++ E).
     apply wf_lenv_weakening.
      simpl_env...
      simpl_env...
      apply in_notin_disjoint. 
      intros y InDom.
       destruct (x == y); subst.
        simpl_env.  auto. 
        simpl_env in InDom. fsetdec.
   assert (exists D2' : lenv,
         permute D2 D2' /\
         atyping (from_env_to_genv ([(x, bind_typ T1)] ++ E))
           (from_lenv_to_denv D3) (open_ee e1 x) T2 
           (from_lenv_to_denv D2')) as IH.

    eapply H1...
     eapply wf_lenv_permute...
      apply permute_sym... apply eq_lbinding_dec.
      
   destruct IH as [D2' [Perm2 ATyping]].
   exists D2'. 
   repeat split; simpl_env...
    apply atyping_uabs with (union L
                 (union (fv_te e1)
                    (union (fv_ee e1)
                       (union (fv_tt T1) (union (fv_tt T2) (union (dom E) (union (dom D3) (singleton x))))))))...
     apply wf_typ_compl with kn_nonlin...
     intros x0 Notin.
     apply atyping_nonlin_term_renaming_head with x. 
      rewrite dom_G_remain_2.
      assert (x `notin` dom (from_lenv_to_denv D3)).
       apply atyping_regular in ATyping.
       destruct ATyping as [Wfg [Wfd3 HH]].
       simpl in Wfd3.
       apply denv_dom_ginv with ((x, gbind_typ T1) :: from_env_to_genv E)...
        simpl_env. solve_notin. solve_notin.
       rewrite dom_G_remain_2. rewrite <- dom_D_remain_2. auto.
       auto.
    simpl in ATyping. simpl_env in ATyping...
    intros KEq.
     apply H2 in KEq.
     subst.
     simpl_env in Perm.
     assert (permute (from_lenv_to_denv D3) (from_lenv_to_denv D2')) as Perm3.
      apply atyping_regular in ATyping.
       destruct ATyping as [Wfg [Wfd3 [Wfd2' HH]]].
      apply perm_trans with (from_lenv_to_denv D2).
       eapply uniq_from_wf_denv_lin...
       apply uniq_lenv_compl. simpl_env in Uniq21...
      apply perm_lenv_to_denv_2...
      apply perm_lenv_to_denv_2...
     apply perm_uniq_implies_eq...
      apply atyping_regular in ATyping.
       destruct ATyping as [Wfg [Wfd3 HH]].
       eapply uniq_from_wf_denv_lin...

  Case "typing_labs".
   pick fresh x for (union L
                 (union (fv_te e1)
                    (union (fv_ee e1)
                       (union (fv_tt T1) (union (fv_tt T2) (union (dom D2) (union (dom D) (dom E)))))))).
    
    assert (dom D3 [=] dom (D2 ++ D)) as DomEq.
      apply dom_permute...
    simpl_env in DomEq.
    assert ( exists D2' : lenv,
         permute D2 D2' /\
         atyping (from_env_to_genv E) (from_lenv_to_denv ([(x, lbind_typ T1)] ++ D3))
           (open_ee e1 x) T2 (from_lenv_to_denv D2')) as IH. 
     apply H1. auto. solve_uniq. solve_uniq. auto.
     apply wf_lenv_lin_weakening...
     rewrite_env (lempty ++ [(x, lbind_typ T1)] ++ D3).
     apply wf_lenv_lin_weakening... simpl_env.
      rewrite DomEq...
     apply permute_cons...
     simpl. apply uniq_cons... rewrite DomEq...
     
    destruct IH as [D2' [Perm2 ATyping]].
   
    assert (uniq (from_lenv_to_denv D3)) as UniqD3.
     apply atyping_regular in ATyping.
     destruct ATyping as [Wfg [Wfd HH]].
     apply uniq_from_wf_denv_lin in Wfd. rewrite lenv_to_denv_conc in Wfd. solve_uniq.

    assert (uniq (D2 ++ [(x, lbind_typ T1)] ++ D)) as UniqD31.
      solve_uniq.
    
    exists D2'.
    repeat split...
    apply atyping_labs with (union L
                 (union (fv_te e1)
                    (union (fv_ee e1)
                       (union (fv_tt T1) (union (fv_tt T2) (union (dom E) (union (dom D2) (union (dom D) (singleton x))))))))) kn_lin...
     apply wf_typ_compl with kn_lin...
     intros x0 Notin.
     apply atyping_lin_term_renaming_head_in with x.
      rewrite dom_G_remain_2. rewrite <- dom_D_remain_2. rewrite DomEq. auto.
      rewrite dom_G_remain_2. rewrite <- dom_D_remain_2. rewrite DomEq. auto.
      auto.
      assert ((x `in` fv_ee (open_ee e1 x) /\ x `notin` dom (from_lenv_to_denv D2')) 
        \/  (x `notin` fv_ee (open_ee e1 x) /\ x `in` dom (from_lenv_to_denv D2'))) as InorNot.
       eapply denv_mono_aux.
        apply ATyping.
        rewrite <- dom_D_remain_2. simpl_env...
      rewrite <- dom_D_remain_2 in InorNot.
      assert (dom D2 [=] dom D2') as DomEq2.
       apply dom_permute...
      rewrite <- DomEq2 in InorNot.
      assert (x `notin` dom D2) as xNotin.
       solve_uniq.
      destruct InorNot.
       inversion H3...
       destruct H3.
        solve_uniq.
     auto.
     intros KEq.
     apply H2 in KEq.
     subst. 
     simpl_env in *.
     apply perm_lenv_to_denv_2 in Perm.
     apply perm_lenv_to_denv_2 in Perm2.
     assert (permute (from_lenv_to_denv D3) (from_lenv_to_denv D2')) as Perm32'.
      apply perm_trans with (from_lenv_to_denv D2)...
       apply uniq_lenv_compl...
     apply perm_uniq_implies_eq...

  Case "typing_app".
   assert (wf_lenv E D1) as WflD1.
    eapply wf_lenv_split_left...
   assert (wf_lenv E D2) as WflD2.
    eapply wf_lenv_split_right...
   assert (permute D3 (D1 ++ D2)) as Perm3.
    eapply lenv_split_permute...
   assert (uniq (D0 ++ D1 ++ D2)) as Uniq012.
    apply uniq_app_4...
     apply uniq_env_permute with D3...
     apply disjoint_sound.
     apply disjoint_sym_1.
      apply dmap_denv_disjoint.
       eapply dmap_Equal_preserves_disjoint_left.
        destruct_uniq.
        apply denv_dmap_disjoint.
         apply disjoint_sym_1.
          eapply disjoint_compl...
        apply Equal_sym.
        apply perm_uniq_implies_eq...
         apply perm_lenv_to_denv_2...
         apply uniq_lenv_compl...   
       
   assert (exists D2' : lenv,
                permute (D0 ++ D2) D2' /\
                atyping (from_env_to_genv E) (from_lenv_to_denv (D0 ++ D3)) e1
                  (typ_arrow K T1 T2) (from_lenv_to_denv D2')) as IH1.
    apply IHTyping1...
     simpl_env... solve_uniq.
     assert (wf_lenv E (D1 ++ D2)) as Wfl12.
      eapply wf_lenv_split_both...
     rewrite_env(lempty ++ D0 ++ (D2++ D1)). 
     apply wf_lenv_lin_weakening_2. simpl_env.
     eapply wf_lenv_permute. apply Wfl12. 
     apply perm_lenv_to_denv. rewrite lenv_to_denv_conc. 
     rewrite lenv_to_denv_conc. apply perm_conc_commu.
     rewrite <- lenv_to_denv_conc. apply uniq_lenv_compl. solve_uniq.
     rewrite_env (lempty ++ D0 ++ D3) in Wflenv.
      eapply wf_lenv_lin_strengthening...
      simpl_env. solve_uniq.
     simpl_env. 
     apply perm_lenv_to_denv.
      rewrite lenv_to_denv_conc. rewrite lenv_to_denv_conc.  rewrite lenv_to_denv_conc.
     apply eq_uniq_implies_perm...
     apply denv_conc_preserves_Equal_1...
      apply perm_uniq_implies_eq...
       rewrite <- lenv_to_denv_conc. apply perm_lenv_to_denv_2...
      apply perm_lenv_to_denv. rewrite lenv_to_denv_conc.
      apply perm_lenv_to_denv_2 in Perm3. rewrite lenv_to_denv_conc in Perm3.
      apply perm_trans with (from_lenv_to_denv D1 ++ from_lenv_to_denv D2)...
       apply uniq_lenv_compl... rewrite <- lenv_to_denv_conc. apply uniq_lenv_compl. solve_uniq.
      apply perm_conc_commu... rewrite <- lenv_to_denv_conc . apply uniq_lenv_compl. solve_uniq.
      apply uniq_lenv_compl... rewrite <- lenv_to_denv_conc. apply uniq_lenv_compl...
      rewrite <- lenv_to_denv_conc. rewrite <- lenv_to_denv_conc. apply uniq_lenv_compl... solve_uniq.

   destruct IH1 as [D02 [Perm02 ATypingPre]].
   assert (exists D2', 
     atyping (from_env_to_genv E) (from_lenv_to_denv D4) e1 (typ_arrow K T1 T2) D2' 
     /\ (from_lenv_to_denv D02) ~~~ D2') as Mid.
   apply atyping_permutation with (from_lenv_to_denv (D0 ++ D3))...
    apply uniq_lenv_compl. eapply uniq_from_wf_lenv...
    apply Equal_sym.
    apply perm_uniq_implies_eq.
     apply perm_lenv_to_denv_2...
     apply uniq_lenv_compl. eapply uniq_from_wf_lenv...
   
   destruct Mid as [D42 [ATyping1 EQ]].
   assert (wf_lenv E D0) as Wfl0.
    rewrite_env (lempty ++ D0 ++ D3) in Wflenv.
      eapply wf_lenv_lin_strengthening. apply Wflenv.
   assert (wf_lenv E (D0 ++ D2)) as Wfl02.
    rewrite_env (lempty ++ D0 ++ D2).
     apply wf_lenv_lin_weakening_2...
   assert (wf_lenv E D02) as WflD02.
    eapply wf_lenv_permute...
   assert (uniq D42) as Uniq42.
    apply atyping_regular in ATyping1.
        destruct ATyping1 as [Wfg [Wfd4 [Wfd42 HH]]].
         eapply uniq_from_wf_denv_lin...
   assert (exists D2' : lenv,
                permute D0 D2' /\
                atyping (from_env_to_genv E) (from_lenv_to_denv (from_denv_to_lenv D42)) e2 T1
                  (from_lenv_to_denv D2')) as IH2. 
    apply IHTyping2...
     eapply wf_lenv_permute.
      apply WflD02.
      apply perm_lenv_to_denv. rewrite <- denv_refl.
      apply eq_uniq_implies_perm... 
       apply uniq_lenv_compl. eapply uniq_from_wf_lenv...
     apply perm_lenv_to_denv. rewrite <- denv_refl.
      apply eq_uniq_implies_perm...
       apply Equal_sym.
        apply Equal_trans with (<# from_lenv_to_denv D02 #>).
         apply perm_uniq_implies_eq.
          apply perm_lenv_to_denv_2... apply uniq_lenv_compl...
         auto. 
       apply uniq_lenv_compl. eapply uniq_from_wf_lenv...
      apply uniq_denv_sound...
    destruct IH2 as [D2' [Perm02' ATyping2]].
    exists D2'.
    repeat split...
    apply atyping_app with T1 K D42...
    rewrite <- denv_refl in ATyping2...

  Case "typing_tabs".
   pick fresh X for (union L
                 (union (fv_te e1)
                    (union (fv_ee e1) (union (fv_tt T1) (union (dom D2) (union (dom D) (union (dom D3) (union  (denv_fv_tt (from_lenv_to_denv D3)) (dom E))))))))).
   assert (exists D2' : lenv,
         permute D2 D2' /\
         atyping (from_env_to_genv ([(X, bind_kn K)] ++ E))
           (from_lenv_to_denv D3) (open_te e1 X) (open_tt T1 X)
           (from_lenv_to_denv D2')) as IH.
    apply H1...
     rewrite_env (empty ++ [(X, bind_kn K)] ++ E).
     apply wf_lenv_weakening. simpl_env...
      simpl_env. apply wf_env_kn. eapply wf_env_from_wf_lenv...
      auto.
      auto.
    rewrite_env (empty ++ [(X, bind_kn K)] ++ E).
     apply wf_lenv_weakening. simpl_env...
      simpl_env. apply wf_env_kn. eapply wf_env_from_wf_lenv...
      auto.
      auto.
   destruct IH as [D2' [Perm22 ATyping]].
   exists D2'.
   repeat split...
   apply atyping_tabs with ( union L
                 (union (fv_te e1)
                    (union (fv_ee e1)
                       (union (fv_tt T1)
                          (union (dom D2)
                             (union (dom D) (union (dom D3) (union (singleton X) (union  (denv_fv_tt (from_lenv_to_denv D3)) (dom E))))))))))...
     intros X0 Notin...
     apply atyping_nonlin_typ_renaming with X.
      rewrite  dom_G_remain_2. rewrite <- dom_D_remain_2...
      rewrite dom_G_remain_2.  rewrite <- dom_D_remain_2...
      auto.
      auto.

  Case "typing_tapp".
   assert (exists D2' : lenv,
               permute D2 D2' /\
               atyping (from_env_to_genv E) (from_lenv_to_denv D3) e1
                 (typ_all K T2) (from_lenv_to_denv D2')) as IH.
    apply IHTyping...
   destruct IH as [D2' [Perm22 ATyping]].
   exists D2'.
   repeat split...
   apply atyping_tapp with K K...
    apply wf_typ_compl with K...
  
  Case "typing_apair".
   skip.
  Case "typing_fst".
   skip.
  Case "typing_snd".
   skip.
Qed.
