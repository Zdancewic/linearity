(** Authors: Jianzhou Zhao. *)

Require Import Bang_PreLib.
Require Import Bang_Renaming.
Require Import Bang_ContextualEq_Def.
Require Import Bang_ContextualEq_Infrastructure.

Lemma _env_remove_dom : forall E y b,
  uniq E ->
  (binds y b E -> dom (env_remove (y, b) E) [=] AtomSetImpl.diff (dom E) {{y}}) /\
  (~binds y b E -> dom (env_remove (y, b) E) [=] dom E).
Proof.
  intros E y b Uniq.
  generalize dependent y.
  generalize dependent b.
  induction Uniq; intros; simpl.
    split; auto.
      intros J. contradict J; auto.

    split; intro J.
      destruct (eq_binding_dec (y,b)  (x, a)); simpl.
        inversion e; subst. 
        destruct (IHUniq a x) as [J1 J2].
        rewrite J2; auto. 
          fsetdec.
          intros JJ. apply binds_In in JJ. contradict JJ; auto.

        analyze_binds J.
        destruct (IHUniq b y) as [J1 J2].
        rewrite J1; auto.
        destruct (x == y); subst.
          apply binds_In in BindsTac. contradict BindsTac; auto.                 
          fsetdec.
      
      destruct (eq_binding_dec (y,b)  (x, a)); simpl.
        inversion e; subst.
        contradict J; auto.
 
        destruct (IHUniq b y) as [J1 J2].
        rewrite J2; auto. 
          fsetdec.
Qed.

Lemma env_remove_binds_dom : forall E y b,
  uniq E ->
  binds y b E -> 
  dom (env_remove (y, b) E) [=] AtomSetImpl.diff (dom E) {{y}}.
Proof.
  intros E y b H1 H2.
  destruct (@_env_remove_dom E y b H1); auto.
Qed.

Lemma _lenv_remove_dom : forall E y b,
  uniq E ->
  (binds y b E -> dom (lenv_remove (y, b) E) [=] AtomSetImpl.diff (dom E) {{y}}) /\
  (~binds y b E -> dom (lenv_remove (y, b) E) [=] dom E).
Proof.
  intros E y b Uniq.
  generalize dependent y.
  generalize dependent b.
  induction Uniq; intros; simpl.
    split; auto.
      intros J. contradict J; auto.

    split; intro J.
      destruct (eq_lbinding_dec (y,b)  (x, a)); simpl.
        inversion e; subst. 
        destruct (IHUniq a x) as [J1 J2].
        rewrite J2; auto. 
          fsetdec.
          intros JJ. apply binds_In in JJ. contradict JJ; auto.

        analyze_binds J.
        destruct (IHUniq b y) as [J1 J2].
        rewrite J1; auto.
        destruct (x == y); subst.
          apply binds_In in BindsTac. contradict BindsTac; auto.                 
          fsetdec.
      
      destruct (eq_lbinding_dec (y,b)  (x, a)); simpl.
        inversion e; subst.
        contradict J; auto.
 
        destruct (IHUniq b y) as [J1 J2].
        rewrite J2; auto. 
          fsetdec.
Qed.

Lemma lenv_remove_binds_dom : forall E y b,
  uniq E ->
  binds y b E -> 
  dom (lenv_remove (y, b) E) [=] AtomSetImpl.diff (dom E) {{y}}.
Proof.
  intros E y b H1 H2.
  destruct (@_lenv_remove_dom E y b H1); auto.
Qed.

Lemma contexting__context : forall E D T C E' D' T',
  contexting E D T C E' D' T' ->
  context C.
Proof.
  intros E D T C E' D' T' Hcontexting.
  induction Hcontexting; auto.
    apply context_abs_free with (L:=L); auto.
      apply type_from_wf_typ in H; auto.

    apply context_abs_capture with (L:={}); auto.
      apply type_from_wf_typ in H; auto.

      intros x xnL.
      rewrite close_open_ec__subst_ec; auto.
      apply subst_ec_context; auto.

    apply context_tabs_free with (L:=L); auto.

    apply context_tabs_capture with (L:={}); auto.
      intros X XnL.
      rewrite close_open_tc__subst_tc; auto.
      apply subst_tc_context; auto.

    apply context_tapp; auto.
      apply type_from_wf_typ in H; auto.

    apply context_let1 with (L:=L); auto.
      intros x xnL.
      apply H in xnL; auto.

    apply context_let2_free with (L:=L); auto.

    apply context_let2_capture with (L:={{y}}); auto.
      intros x xnL.
      rewrite close_open_ec__subst_ec; auto.
      apply subst_ec_context; auto.
Qed.

Lemma plug_context__expr : forall C e,
  context C ->
  expr e ->
  expr (plug C e).
Proof.
  intros C e HC.
  generalize dependent e.
  induction HC; simpl; intros; auto.
    apply expr_abs with (L:=L `union` cv_ec C1); auto.
      intros x xnL.
      rewrite <- shift_ee_expr; auto.
      rewrite open_ee_plug; auto.
         assert (x `notin` L) as FV. auto.
         apply H1 with (e:=open_ee e x) in FV; auto.
            rewrite <- open_ee_expr; auto.
         
         eapply disjdom_app_l.
         split.
           apply disjdom_one_2; auto.
           simpl. apply disjdom_nil_1.

    apply expr_abs with (L:=L `union` cv_ec C1); auto.
      intros x xnL.
      rewrite <- shift_ee_expr; auto.
      rewrite open_ee_plug; auto.
         assert (x `notin` L) as FV. auto.
         apply H1 with (e:=open_ee (close_ee e y) x) in FV; auto.
            apply open_close_ee_rec__expr; auto.
         
         eapply disjdom_app_l.
         split.
           apply disjdom_one_2; auto.
           simpl. apply disjdom_nil_1.
         
    apply expr_tabs with (L:=L `union` cv_ec C1); auto.
      intros X XnL.
      rewrite <- shift_te_expr; auto.
      rewrite open_te_plug; auto.
         assert (X `notin` L) as FV. auto.
         apply H0 with (e:=open_te e X) in FV; auto.
            apply open_te_expr; auto.
         
         apply disjdom_one_2; auto.

    apply expr_tabs with (L:=L `union` cv_ec C1); auto.
      intros X XnL.
      rewrite <- shift_te_expr; auto.
      rewrite open_te_plug; auto.
         assert (X `notin` L) as FV. auto.
         apply H0 with (e:=open_te (close_te e Y) X) in FV; auto.
            apply open_close_te_rec__expr; auto.
         
         apply disjdom_one_2; auto.

    apply expr_let with (L:=L `union` cv_ec C1); auto.

    apply expr_let with (L:=L `union` cv_ec C2); auto.
      intros x xnL.
      rewrite <- shift_ee_expr; auto.
      rewrite open_ee_plug; auto.
         assert (x `notin` L) as FV. auto.
         apply H1 with (e:=open_ee e x) in FV; auto.
            rewrite <- open_ee_expr; auto.
         
         eapply disjdom_app_l.
         split.
           apply disjdom_one_2; auto.
           simpl. apply disjdom_nil_1.

    apply expr_let with (L:=L `union` cv_ec C2); auto.
      intros x xnL.
      rewrite <- shift_ee_expr; auto.
      rewrite open_ee_plug; auto.
         assert (x `notin` L) as FV. auto.
         apply H1 with (e:=open_ee (close_ee e y) x) in FV; auto.
            apply open_close_ee_rec__expr; auto.
         
         eapply disjdom_app_l.
         split.
           apply disjdom_one_2; auto.
           simpl. apply disjdom_nil_1.
Qed.

Lemma context_through_subst_ec : forall C x e,
  context C ->
  expr e ->
  context (subst_ec x e C).       
Proof.
  intros C x e HC.
  induction HC; simpl; intros; auto.
    apply context_abs_free with (L:=L `union` {{x}}); auto.
      intros x0 x0nL.
      assert (x0 `notin` L) as FV. auto.
      apply H1 in FV; auto.
      rewrite subst_ec_open_ec_var; auto.

    apply context_abs_capture with (L:=L `union` {{x}}); auto.
      intros x0 x0nL.
      assert (x0 `notin` L) as FV. auto.
      apply H1 in FV; auto.
      rewrite subst_ec_open_ec_var; auto.

    apply context_tabs_free with (L:=L `union` {{x}}); auto.
      intros X0 X0nL.
      assert (X0 `notin` L) as FV. auto.
      apply H in FV; auto.
      rewrite subst_ec_open_tc_var; auto.

    apply context_tabs_capture with (L:=L `union` {{x}}); auto.
      intros X0 X0nL.
      assert (X0 `notin` L) as FV. auto.
      apply H0 in FV; auto.
      rewrite subst_ec_open_tc_var; auto.

    apply context_let1 with (L:=L `union` {{x}}); auto.
      intros x0 x0nL.
      assert (x0 `notin` L) as FV. auto.
      apply H in FV; auto.
      rewrite subst_ee_open_ee_var; auto.

    apply context_let2_free with (L:=L `union` {{x}}); auto.
      intros x0 x0nL.
      assert (x0 `notin` L) as FV. auto.
      apply H0 in FV; auto.
      rewrite subst_ec_open_ec_var; auto.

    apply context_let2_capture with (L:=L `union` {{x}}); auto.
      intros x0 x0nL.
      assert (x0 `notin` L) as FV. auto.
      apply H1 in FV; auto.
      rewrite subst_ec_open_ec_var; auto.
Qed.

Lemma context_through_subst_tc : forall C x t,
  context C ->
  type t ->
  context (subst_tc x t C).       
Proof.
  intros C x t HC.
  induction HC; simpl; intros; auto.
    apply context_abs_free with (L:=L `union` {{x}}); auto.
      intros x0 x0nL.
      assert (x0 `notin` L) as FV. auto.
      apply H1 in FV; auto.
      rewrite subst_tc_open_ec_var; auto.

    apply context_abs_capture with (L:=L `union` {{x}}); auto.
      intros x0 x0nL.
      assert (x0 `notin` L) as FV. auto.
      apply H1 in FV; auto.
      rewrite subst_tc_open_ec_var; auto.

    apply context_tabs_free with (L:=L `union` {{x}}); auto.
      intros X0 X0nL.
      assert (X0 `notin` L) as FV. auto.
      apply H in FV; auto.
      rewrite subst_tc_open_tc_var; auto.

    apply context_tabs_capture with (L:=L `union` {{x}}); auto.
      intros X0 X0nL.
      assert (X0 `notin` L) as FV. auto.
      apply H0 in FV; auto.
      rewrite subst_tc_open_tc_var; auto.

    apply context_let1 with (L:=L `union` {{x}}); auto.
      intros x0 x0nL.
      assert (x0 `notin` L) as FV. auto.
      apply H in FV; auto.
      rewrite subst_te_open_ee_var; auto.

    apply context_let2_free with (L:=L `union` {{x}}); auto.
      intros x0 x0nL.
      assert (x0 `notin` L) as FV. auto.
      apply H0 in FV; auto.
      rewrite subst_tc_open_ec_var; auto.

    apply context_let2_capture with (L:=L `union` {{x}}); auto.
      intros x0 x0nL.
      assert (x0 `notin` L) as FV. auto.
      apply H1 in FV; auto.
      rewrite subst_tc_open_ec_var; auto.
Qed.

Lemma vcontext_through_subst_ec : forall C x e,
  vcontext C ->
  expr e ->
  vcontext (subst_ec x e C).       
Proof.
  intros C x e VC.
  induction VC; intros; simpl; auto.
    apply vcontext_abs_free.
      apply context_through_subst_ec with (x:=x) (e:=e) in H; auto.
    apply vcontext_abs_capture.
      apply context_through_subst_ec with (x:=x) (e:=e) in H; auto.
    apply vcontext_tabs_free.
      apply context_through_subst_ec with (x:=x) (e:=e) in H; auto.
    apply vcontext_tabs_capture.
      apply context_through_subst_ec with (x:=x) (e:=e) in H; auto.
    apply vcontext_bang.
      apply context_through_subst_ec with (x:=x) (e:=e) in H; auto.
    apply vcontext_apair1.
      apply context_through_subst_ec with (x:=x) (e:=e) in H; auto.
    apply vcontext_apair2.
      apply context_through_subst_ec with (x:=x) (e:=e) in H; auto.
Qed.

Lemma vcontext_through_subst_tc : forall C x t,
  vcontext C ->
  type t ->
  vcontext (subst_tc x t C).       
Proof.
  intros C x t VC.
  induction VC; intros; simpl; auto.
    apply vcontext_abs_free.
      apply context_through_subst_tc with (x:=x) (t:=t) in H; auto.
    apply vcontext_abs_capture.
      apply context_through_subst_tc with (x:=x) (t:=t) in H; auto.
    apply vcontext_tabs_free.
      apply context_through_subst_tc with (x:=x) (t:=t) in H; auto.
    apply vcontext_tabs_capture.
      apply context_through_subst_tc with (x:=x) (t:=t) in H; auto.
    apply vcontext_bang.
      apply context_through_subst_tc with (x:=x) (t:=t) in H; auto.
    apply vcontext_apair1.
      apply context_through_subst_tc with (x:=x) (t:=t) in H; auto.
    apply vcontext_apair2.
      apply context_through_subst_tc with (x:=x) (t:=t) in H; auto.
Qed.
         
Lemma wf_typ_permute: forall F E1 x t' E2 T,
  wf_env (F++E1++[(x, bind_typ t')]++E2) ->
  wf_typ (F++E1++[(x, bind_typ t')]++E2) T ->
  wf_typ (F++[(x, bind_typ t')]++E1++E2) T.
Proof.
  intros F E1 x t' E2 T Wfe Wft.
  apply wf_typ_weakening; auto.
    rewrite_env ((F++E1)++[(x, bind_typ t')]++E2) in Wft.
    apply wf_typ_strengthening in Wft.
    simpl_env in Wft. auto.

    apply uniq_from_wf_env in Wfe; auto.
    solve_uniq.
Qed.  

Lemma wf_env_permute: forall F E1 x t' E2,
  wf_env (F++E1++[(x, bind_typ t')]++E2)->
  wf_env (F++[(x, bind_typ t')]++E1++E2).
Proof.
  intros F E1 x t' E2 Wfe.
  apply wf_env_weakening; auto.
    rewrite_env ((F  ++ E1) ++ [(x, bind_typ t')] ++ E2) in Wfe.
    apply wf_env_strengthening in Wfe.
    simpl_env in Wfe. auto.

    apply wf_env_typ; auto.
      rewrite_env ((F  ++ E1) ++ [(x, bind_typ t')] ++ E2) in Wfe.
      apply wf_env_strengthening in Wfe.
      simpl_env in Wfe.
      apply wf_env_strengthening_tail in Wfe; auto.

      apply wf_env_strengthening_tail in Wfe.
      assert (J:=Wfe).
      apply wf_env_strengthening_tail in Wfe.
      inversion Wfe; subst.
      apply wf_typ_weaken_head; auto.
        apply uniq_from_wf_env in J.
        solve_uniq.

      apply uniq_from_wf_env in Wfe.
      solve_uniq.

    apply uniq_from_wf_env in Wfe.
    solve_uniq.
Qed.

Lemma wf_lenv_nonlin_permute: forall F E1 x t' E2 D,
  wf_lenv (F++E1++[(x, bind_typ t')]++E2) D ->
  wf_lenv (F++[(x, bind_typ t')]++E1++E2) D.
Proof.
  intros F E1 x t' E2 D Wfle.
  apply wf_lenv_weakening; auto.
    rewrite_env ((F  ++ E1) ++ [(x, bind_typ t')] ++ E2) in Wfle.
    apply wf_lenv_strengthening in Wfle.
    simpl_env in Wfle. auto.

    apply wf_env_permute; auto.

    apply disjoint_wf_lenv in Wfle.
    solve_uniq.
Qed.

Lemma lenv_split_nonlin_permute: forall F E1 x t' E2 D1 D2 D,
  lenv_split (F++E1++[(x, bind_typ t')]++E2) D1 D2 D ->
  lenv_split (F++[(x, bind_typ t')]++E1++E2) D1 D2 D.
Proof.
  intros F E1 x t' E2 D1 D2 D Split.
  apply lenv_split_weakening; auto.
    rewrite_env ((F  ++ E1) ++ [(x, bind_typ t')] ++ E2) in Split.
    apply lenv_split_strengthening in Split.
    simpl_env in Split. auto.

    apply wf_env_permute; auto.
      apply wf_lenv_split in Split. auto.

    apply wf_lenv_split in Split. 
    apply disjoint_wf_lenv in Split.
    solve_uniq.
Qed.

Lemma _typing_nonlin_permute: forall F E1 x t' E2 D e t,
  typing (F++E1++[(x, bind_typ t')]++E2) D e t ->
  typing (F++[(x, bind_typ t')]++E1++E2) D e t.
Proof.
  intros F E1 x t' E2 D e t TYP.
  remember (F++E1++[(x, bind_typ t')]++E2) as E.
  generalize dependent F.
  generalize dependent E1.
  generalize dependent x.
  generalize dependent t'.
  (typing_cases (induction TYP) Case); intros; subst; eauto.
  Case "typing_var".
    apply typing_var; auto.
      apply wf_env_permute; auto.
      
      apply uniq_from_wf_env in H.
      analyze_binds H0; auto.
  Case "typing_lvar".
    apply typing_lvar; auto.
      apply wf_lenv_nonlin_permute; auto.
  Case "typing_abs".
    pick fresh y and apply typing_abs; auto.
      apply wf_typ_permute; auto.
        pick fresh y.
        assert (y `notin` L) as ynL. auto.
        apply H0 in ynL.
        apply typing_regular in ynL.
        decompose [and] ynL.
        inversion H3; subst; auto.
  Case "typing_app".
    apply typing_app with (D1:=D1) (D2:=D2) (T1:=T1); auto.
      apply lenv_split_nonlin_permute; auto.
  Case "typing_tabs".
    pick fresh X and apply typing_tabs; eauto.
      rewrite_env (([(X, bind_kn)]++F)++[(x, bind_typ t')]++E1++E2).
      apply H0; auto.
  Case "typing_tapp".
    apply typing_tapp; auto.
      apply wf_typ_permute; auto.
  Case "typing_let".
    apply typing_let with (L:=L)(D1:=D1) (D2:=D2) (T1:=T1); auto.
      intros x0 x0n.
      apply H0 with (t'0:=t')(x1:=x)(E3:=E1)(F0:=[(x0, bind_typ T1)]++F) in x0n; auto.

      apply lenv_split_nonlin_permute; auto.
Qed.

Lemma wf_typ_renaming_one: forall E1 x y t' E2 T,
  wf_env (E1++[(x, bind_typ t')]++E2) ->
  wf_typ (E1++[(x, bind_typ t')]++E2) T->
  y `notin` dom E1 `union` dom E2 ->
  wf_typ (E1++[(y, bind_typ t')]++E2) T.
Proof.
  intros E1 x y t' E2 T Wfe Wft yn.
  apply wf_typ_weakening; auto.
    apply wf_typ_strengthening in Wft. auto.

    apply uniq_from_wf_env in Wfe; auto.
    solve_uniq.
Qed.  

Lemma wf_env_renaming_one: forall E1 x y t' E2,
  wf_env (E1++[(x, bind_typ t')]++E2)->
  y `notin` dom E1 `union` dom E2 ->
  wf_env (E1++[(y, bind_typ t')]++E2).
Proof.
  intros E1 x y t' E2 Wfe yn.
  apply wf_env_weakening; auto.
    apply wf_env_strengthening in Wfe. auto.

    apply wf_env_typ; auto.
      apply wf_env_strengthening in Wfe.
      apply wf_env_strengthening_tail in Wfe; auto.

      apply wf_env_strengthening_tail in Wfe.
      inversion Wfe; subst. auto.

    apply uniq_from_wf_env in Wfe.
    solve_uniq.
Qed.

Lemma wf_lenv_nonlin_renaming_one: forall E1 x y t' E2 D,
  wf_lenv (E1++[(x, bind_typ t')]++E2) D ->
  y `notin` dom E1 `union` dom E2 `union` dom D ->
  wf_lenv (E1++[(y, bind_typ t')]++E2) D.
Proof.
  intros E1 x y t' E2 D Wfle yn.
  apply wf_lenv_weakening; auto.
    apply wf_lenv_strengthening in Wfle. auto.

    apply wf_env_renaming_one with (x:=x) ; auto.
Qed.

Lemma lenv_split_nonlin_renaming_one: forall E1 x y t' E2 D1 D2 D,
  lenv_split (E1++[(x, bind_typ t')]++E2) D1 D2 D ->
  y `notin` dom E1 `union` dom E2 `union` dom D ->
  lenv_split (E1++[(y, bind_typ t')]++E2) D1 D2 D.
Proof.
  intros E1 x y t' E2 D1 D2 D Split yn.
  apply lenv_split_weakening; auto.
    apply lenv_split_strengthening in Split. auto.

    apply wf_env_renaming_one with (x:=x); auto.
      apply wf_lenv_split in Split. auto.
Qed.

Lemma typing_nonlin_renaming_one: forall E1 x y t' E2 D e t,
  typing (E1++[(x, bind_typ t')]++E2) D e t ->
  y `notin` dom E1 `union` dom E2 `union` dom D ->
  typing (E1++[(y, bind_typ t')]++E2) D (subst_ee x y e) t.
Proof.
  intros E1 x y t' E2 D e t TYP yn.
  remember (E1++[(x, bind_typ t')]++E2) as E.
  generalize dependent E1.
  generalize dependent x.
  generalize dependent t'.
  (typing_cases (induction TYP) Case); intros; subst; simpl; simpl_env; eauto.
  Case "typing_var".    
    assert (J:=H).
    apply uniq_from_wf_env in H.
    destruct (x==x0); subst.
      analyze_binds_uniq H0.
      inversion BindsTacVal; subst.
      apply typing_var; auto.      
        apply wf_env_renaming_one with (x:=x0); auto.
   
      apply wf_env_renaming_one with (y:=y) in J; auto.
      apply typing_var; auto.      
      analyze_binds_uniq H0; auto.       
  Case "typing_lvar".
    destruct (x==x0); subst.
      inversion H; subst.
      simpl_env in H5.
      destruct_notin.
      contradict NotInTac1; auto.

      apply typing_lvar; auto.
        apply wf_lenv_nonlin_renaming_one with (x:=x0); auto.
  Case "typing_abs".
    pick fresh z and apply typing_abs; auto.
      apply wf_typ_renaming_one with (x:=x); auto.
        pick fresh z.
        assert (z `notin` L) as znL. auto.
        apply H0 in znL.
        apply typing_regular in znL.
        decompose [and] znL.
        inversion H3; subst; auto.

      rewrite subst_ee_fresh with (e:=z) (u:=y) (x:=x); auto.
      rewrite <- subst_ee_open_ee; auto.
  Case "typing_app".
    assert (J:=H).
    apply dom_lenv_split in J.
    rewrite J in yn.
    apply typing_app with (D1:=D1) (D2:=D2) (T1:=T1); eauto.
      apply lenv_split_nonlin_renaming_one with (x:=x); auto.
         rewrite J. auto.
  Case "typing_tabs".
    pick fresh X and apply typing_tabs; eauto.
      rewrite_env (([(X, bind_kn)]++E1)++[(y, bind_typ t')]++E2).
      rewrite <- subst_ee_open_te; auto.
  Case "typing_tapp".
    apply typing_tapp; auto.
      apply wf_typ_renaming_one with (x:=x); auto.
  Case "typing_let".
    assert (J:=H1).
    apply dom_lenv_split in J.
    rewrite J in yn.
    apply typing_let with (L:=L `union` {{x}} `union` {{y}})(D1:=D1) (D2:=D2) (T1:=T1); auto.
      intros x0 x0n.
      assert (x0 `notin` L) as x0nL. auto.
      apply H0 with (t'0:=t')(x1:=x)(E3:=[(x0, bind_typ T1)]++E1) in x0nL; auto.
      rewrite_env (([(x0, bind_typ T1)]++E1)++[(y, bind_typ t')]++E2).
      rewrite subst_ee_fresh with (e:=x0) (u:=y) (x:=x); auto.
      rewrite <- subst_ee_open_ee; auto.

      apply lenv_split_nonlin_renaming_one with (x:=x); auto.
         rewrite J. auto.
Qed.

Lemma swap_typing_nonlin : forall E' E D e1 x y T1 T2, 
  x `notin` (fv_ee e1) -> 
  y `notin` (dom E' `union` dom E `union` dom D) -> 
  typing (E'++[(x, bind_typ T1)]++E) D (open_ee e1 x) T2 ->
  typing (E'++[(y, bind_typ T1)]++E) D (open_ee e1 y) T2.
intros E' E D e1 x y T1 T2 Hxn Hyn Htypx.
destruct (x==y); subst; auto.
  rewrite (@subst_ee_intro x); auto.  
  unfold open_ee in *.
  apply typing_nonlin_renaming_one; auto.
Qed.

Lemma swap_typing_nonlin_head : forall E D e1 x y T1 T2, 
  x `notin` (fv_ee e1) -> 
  y `notin` (dom E `union` dom D) -> 
  typing ([(x, bind_typ T1)]++E) D (open_ee e1 x) T2 ->
  typing ([(y, bind_typ T1)]++E) D (open_ee e1 y) T2.
intros E D e1 x y T1 T2 Hxn Hyn Htypx.
  rewrite_env (nil ++ [(y,bind_typ T1)] ++ E).
  apply swap_typing_nonlin with (x:=x); auto.
Qed.

Lemma typing_nonlin_permute: forall E1 x t' E2 D e t,
  typing (E1++[(x, bind_typ t')]++E2) D e t ->
  typing ([(x, bind_typ t')]++E1++E2) D e t.
Proof.
  intros E1 x t' E2 D e t TYP.
  rewrite_env (nil++E1++[(x, bind_typ t')]++E2) in TYP.
  apply _typing_nonlin_permute in TYP; auto.
Qed.

Lemma typing_nonlin_renaming_permute : forall E' E D e t (x y:atom) T,
  typing (E'++[(x,bind_typ T)]++E) D e t ->
  y `notin` dom E `union` dom E' `union` dom D ->
  typing ([(y,bind_typ T)]++E'++E) D (subst_ee x y e) t.
Proof.
  intros E' E D e t x y T Typ yndom.
  apply typing_nonlin_renaming_one with (y:=y) in Typ; auto.
  apply typing_nonlin_permute  in Typ; auto.
Qed.

Lemma typing_lin_renaming_permute : forall E D' D e t (x y:atom) T,
  typing E (D'++[(x,lbind_typ T)]++D) e t ->
  y `notin` dom D `union` dom D' `union` dom E ->
  typing E ([(y,lbind_typ T)]++D'++D) (subst_ee x y e) t.
Proof.
  intros E D' D e t x y T Typ yndom.
  apply typing_lin_renaming_one with (y:=y) in Typ; auto.
  apply typing_permute with (D2:=[(y,lbind_typ T)]++D'++D) in Typ; auto.
    apply permute_sym; auto.
      apply eq_lbinding_dec.

      assert (uniq (D'++[(y,lbind_typ T)]++D)) as Uniq.
        apply typing_regular in Typ.
        decompose [and] Typ.
        apply uniq_from_wf_lenv in H1; auto.
      clear Typ.
      solve_uniq.

      apply permute_cons.
        apply permute_refl.
Qed.

Lemma _wf_typ_typ_permute: forall F E1 X E2 T,
  wf_env (F++E1++[(X, bind_kn)]++E2) ->
  wf_env (E1++E2) ->
  wf_typ (F++E1++[(X, bind_kn)]++E2) T->
  wf_typ (F++[(X, bind_kn)]++E1++E2) T.
Proof.
  intros F E1 X E2 T Wfe Wfe' Wft.
  remember (F++E1++[(X, bind_kn)]++E2) as E.
  generalize dependent F.
  generalize dependent E1.
  induction Wft; intros; subst.
    apply uniq_from_wf_env in Wfe; auto.
    apply wf_typ_var; auto.
      solve_uniq.
      analyze_binds_uniq H0; auto.
        solve_uniq.

    apply wf_typ_arrow; auto.

    apply wf_typ_all with (L:=L `union` {{X}} `union` dom (F++E1++E2)); auto.
      intros X0 X0nL.
      rewrite_env (([(X0, bind_kn)]++F)++[(X, bind_kn)]++E1++E2).
      apply H0; simpl_env; auto.

    apply wf_typ_bang; auto.

    apply wf_typ_with; auto.
Qed.

Lemma wf_typ_typ_permute: forall E1 X E2 T,
  wf_env (E1++[(X, bind_kn)]++E2) ->
  wf_env (E1++E2) ->
  wf_typ (E1++[(X, bind_kn)]++E2) T->
  wf_typ ([(X, bind_kn)]++E1++E2) T.
Proof.
  intros E1 X E2 T Wfe Wfe' Wft.
  rewrite_env (nil++E1++[(X, bind_kn)]++E2) in Wft.
  apply _wf_typ_typ_permute in Wft; auto.
Qed.

Lemma _wf_env_typ_permute: forall F E1 X E2,
  wf_env (F++E1++[(X, bind_kn)]++E2) ->
  wf_env (E1++E2) ->
  wf_env (F++[(X, bind_kn)]++E1++E2).
Proof.
  intros F E1 X E2 Wfe.
  remember (F++E1++[(X, bind_kn)]++E2) as E.
  generalize dependent F.
  generalize dependent E1.
  induction Wfe; intros; subst.
    symmetry in HeqE.
    contradict HeqE.
    simpl. rewrite_env ((F++E1)++(X, bind_kn)::E2).
    apply app_cons_not_nil.

    apply one_eq_app in HeqE. destruct HeqE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
      simpl_env.
      apply wf_env_kn; auto.

      simpl_env.
      symmetry in eEQ2'.
      simpl_env in eEQ2'.
      apply one_eq_app in eEQ2'. 
      destruct eEQ2' as [[F0' [fEQ1' fEQ2']] | [fEQ1' fEQ2']]; subst.
        simpl_env.
        apply wf_env_kn; simpl_env; auto.
          apply uniq_from_wf_env in Wfe. solve_uniq.

        simpl_env.
        simpl_env in fEQ2'.
        inversion fEQ2'; subst.
        apply wf_env_kn; simpl_env; auto.

    apply one_eq_app in HeqE. destruct HeqE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
      simpl_env.
      apply wf_env_typ; auto.
        apply _wf_typ_typ_permute; auto.

      simpl_env.
      symmetry in eEQ2'.
      simpl_env in eEQ2'.
      apply one_eq_app in eEQ2'. 
      destruct eEQ2' as [[F0' [fEQ1' fEQ2']] | [fEQ1' fEQ2']]; subst.
        simpl_env.
        apply wf_env_kn; simpl_env; auto.
          apply uniq_from_wf_env in Wfe. solve_uniq.

        simpl_env.
        simpl_env in fEQ2'.
        inversion fEQ2'; subst.
Qed.     

Lemma wf_env_typ_permute: forall E1 X E2,
  wf_env (E1++[(X, bind_kn)]++E2) ->
  wf_env (E1++E2) ->
  wf_env ([(X, bind_kn)]++E1++E2).
Proof.
  intros E1 X E2 Wfe Wfe'.
  rewrite_env (nil++E1++[(X, bind_kn)]++E2) in Wfe.
  apply _wf_env_typ_permute with (X:=X) (F:=nil) (E1:=E1) (E2:=E2) in Wfe; auto.
Qed.

Lemma wf_typ_typ_renaming_one: forall E1 X Y E2 T,
  wf_env (E1++[(X, bind_kn)]++E2) ->
  wf_typ (E1++[(X, bind_kn)]++E2) T->
  Y `notin` dom E1 `union` dom E2 ->
  wf_typ (E1++[(Y, bind_kn)]++E2) (subst_tt X Y T).
Proof.
  intros E1 X Y E2 T Wfe Wft Yn.
  remember (E1++[(X, bind_kn)]++E2) as E.
  generalize dependent E1.
  induction Wft; intros; subst; simpl; simpl_env.
    apply uniq_from_wf_env in Wfe; auto.
    destruct (X0==X); subst.
      analyze_binds_uniq H0.
      inversion BindsTacVal; subst. 
      apply wf_typ_var; auto.
        apply uniq_remove_mid in Wfe.
        apply uniq_insert_mid; auto.
   
      apply wf_typ_var; auto.
        apply uniq_remove_mid in Wfe.
        apply uniq_insert_mid; auto.

        analyze_binds_uniq H0.

    apply wf_typ_arrow; auto.

    apply wf_typ_all with (L:=L `union` {{X}} `union` {{Y}} `union` dom E1 `union` dom E2); auto.
      intros X0 X0nL.
      rewrite_env (([(X0, bind_kn)]++E1)++[(Y, bind_kn)]++E2).
      
      rewrite subst_tt_fresh with (T:=X0) (Z:=X) (U:=Y); auto.
      unfold open_tt.
      rewrite <- subst_tt_open_tt_rec; auto.
      apply H0; auto.

    apply wf_typ_bang; auto.

    apply wf_typ_with; auto.
Qed.         

Lemma typing_lin_permute : forall E D1 y T1 D2 e T2,
  typing E (D1++[(y, lbind_typ T1)]++D2) e T2 ->
  typing E ([(y, lbind_typ T1)]++D1++D2) e T2.
Proof.
  intros E D1 y T1 D2 e T2 Typ.
  apply typing_permute with (D2:=[(y,lbind_typ T1)]++D1++D2) in Typ; auto.
    apply permute_sym; auto.
      apply eq_lbinding_dec.

      assert (uniq (D1++[(y,lbind_typ T1)]++D2)) as Uniq.
        apply typing_regular in Typ.
        decompose [and] Typ.
        apply uniq_from_wf_lenv in H1; auto.
      clear Typ.
      solve_uniq.

      apply permute_cons.
        apply permute_refl.
Qed.

Lemma wf_typ_typ_renaming_one': forall E1 X Y E2 T,
  wf_env (E1++[(X, bind_kn)]++E2) ->
  wf_typ (E1++[(X, bind_kn)]++E2) T ->
  Y `notin` dom E1 `union` dom E2 ->
  wf_typ (map (subst_tb X Y) E1 ++[(Y, bind_kn)]++E2) (subst_tt X Y T).
Proof.
  intros E1 X Y E2 T Wfe Wft Yn.
  remember (E1++[(X, bind_kn)]++E2) as E.
  generalize dependent E1.
  induction Wft; intros; subst; simpl; simpl_env.
    apply uniq_from_wf_env in Wfe; auto.
    destruct (X0==X); subst.
      analyze_binds_uniq H0.
      inversion BindsTacVal; subst. 
      apply wf_typ_var; auto.
        apply uniq_remove_mid in Wfe.
        apply uniq_insert_mid; auto.
   
      apply wf_typ_var; auto.
        apply uniq_remove_mid in Wfe.
        apply uniq_insert_mid; auto.

        analyze_binds_uniq H0.
           apply binds_map_2 with (f:=subst_tb X Y) in BindsTac.
           simpl in BindsTac.
           auto.

    apply wf_typ_arrow; auto.

    apply wf_typ_all with (L:=L `union` {{X}} `union` {{Y}} `union` dom E1 `union` dom E2); auto.
      intros X0 X0nL.
      rewrite_env ((map (subst_tb X Y) ([(X0, bind_kn)]++E1))++[(Y, bind_kn)]++E2).    
      rewrite subst_tt_fresh with (T:=X0) (Z:=X) (U:=Y); auto.
      unfold open_tt.
      rewrite <- subst_tt_open_tt_rec; auto.
      apply H0; auto.

    apply wf_typ_bang; auto.

    apply wf_typ_with; auto.
Qed.         

Lemma wf_env_typ_renaming_one: forall E1 X Y E2,
  wf_env (E1++[(X, bind_kn)]++E2) ->
  Y `notin` dom E1 `union` dom E2 ->
  wf_env (map (subst_tb X Y) E1 ++[(Y, bind_kn)]++E2).
Proof.
  intros E1 X Y E2 Wfe.
  remember (E1++[(X, bind_kn)]++E2) as E.
  generalize dependent E1.
  induction Wfe; intros; subst.
    symmetry in HeqE.
    contradict HeqE.
    simpl. 
    apply app_cons_not_nil.

    apply one_eq_app in HeqE. destruct HeqE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
      simpl_env.
      apply wf_env_kn; auto.

      simpl_env.
      simpl_env in eEQ2'.
      inversion eEQ2'; subst.
      apply wf_env_kn; simpl_env; auto.

    apply one_eq_app in HeqE. destruct HeqE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
      simpl_env.
      apply wf_env_typ; auto.
        apply wf_typ_typ_renaming_one'; auto.

      simpl_env.
      simpl_env in eEQ2'.
      inversion eEQ2'; subst.
Qed.     

Lemma wf_lenv_typ_renaming_one: forall E1 X Y E2 D,
  wf_lenv (E1++[(X, bind_kn)]++E2) D ->
  Y `notin` dom E1 `union` dom E2 `union` dom D ->
  wf_lenv (map (subst_tb X Y) E1 ++[(Y, bind_kn)]++E2) (map (subst_tlb X Y) D).
Proof.
  intros E1 X Y E2 D Wfle.
  remember (E1++[(X, bind_kn)]++E2) as E.
  generalize dependent E1.
  induction Wfle; intros; subst; simpl; simpl_env.
    apply wf_lenv_empty; auto.
      apply wf_env_typ_renaming_one; auto.

    apply wf_lenv_typ; auto.
    apply wf_typ_typ_renaming_one'; auto.
Qed.     

Lemma lenv_split_typ_renaming_one: forall E1 X (Y:atom) E2 D1 D2 D,
  lenv_split (E1++[(X, bind_kn)]++E2) D1 D2 D ->
  Y `notin` dom E1 `union` dom E2 `union` dom D ->
  lenv_split (map (subst_tb X Y) E1++[(Y, bind_kn)]++E2) (map (subst_tlb X Y) D1) (map (subst_tlb X Y) D2) (map (subst_tlb X Y) D).
Proof.
  intros E1 X Y E2 D1 D2 D Split yn.
  remember (E1++[(X, bind_kn)]++E2) as E.
  generalize dependent E1.
  generalize dependent X.
  induction Split; intros; subst; simpl; simpl_env.
    apply lenv_split_empty.
      apply wf_env_typ_renaming_one; auto.

    apply lenv_split_left; auto.
      apply wf_typ_typ_renaming_one'; auto.
         apply wf_lenv_split in Split; auto.

    apply lenv_split_right; auto.
      apply wf_typ_typ_renaming_one'; auto.
         apply wf_lenv_split in Split; auto.
Qed.

Lemma typing_typ_renaming_one: forall E1 X Y E2 D e t,
  typing (E1++[(X, bind_kn)]++E2) D e t ->
  Y `notin` dom E1 `union` dom E2 `union` dom D ->
  typing (map (subst_tb X Y) E1 ++[(Y, bind_kn)]++E2) (map (subst_tlb X Y) D) (subst_te X Y e) (subst_tt X Y t).
Proof.
  intros E1 X Y E2 D e t TYP yn.
  remember (E1++[(X, bind_kn)]++E2) as E.
  generalize dependent E1.
  generalize dependent X.
  (typing_cases (induction TYP) Case); intros; subst; simpl; simpl_env; eauto.
  Case "typing_var".    
    assert (J:=H).
    apply uniq_from_wf_env in H.
    apply typing_var; auto.      
      apply wf_env_typ_renaming_one with (X:=X); auto.

      analyze_binds_uniq H0.
      apply binds_map_2 with (f:=subst_tb X Y) in BindsTac0.
      rewrite <- map_subst_tb_id in BindsTac0; auto.
        rewrite_env ((E1++[(X, bind_kn)])++E2) in J.
        apply wf_env_strengthening_tail in J; auto.

        solve_uniq.
  Case "typing_lvar".
    apply typing_lvar; auto.
       rewrite_env (map (subst_tlb X Y) [(x, lbind_typ T)]).
       apply wf_lenv_typ_renaming_one with (X:=X); auto.
  Case "typing_abs".
    pick fresh z and apply typing_abs; auto.
      apply wf_typ_typ_renaming_one' with (X:=X); auto.
        pick fresh z.
        assert (z `notin` L) as znL. auto.
        apply H0 in znL.
        apply typing_regular in znL.
        decompose [and] znL.
        inversion H3; subst; auto.

      rewrite_env (map (subst_tlb X Y) ([(z, lbind_typ T1)]++D)).
      rewrite subst_te_fresh with (e:=z) (U:=Y) (X:=X); auto.
      rewrite <- subst_te_open_ee; auto.
  Case "typing_app".
    assert (J:=H).
    apply dom_lenv_split in J.
    rewrite J in yn.   
    apply typing_app with (D1:=map (subst_tlb X Y) D1) (D2:=map (subst_tlb X Y) D2) (T1:=subst_tt X Y T1); eauto.
      assert (typ_arrow (subst_tt X Y T1) (subst_tt X Y T2) =  subst_tt X Y (typ_arrow T1 T2)) as EQ. auto.
      rewrite EQ.
      apply IHTYP1; auto.

      apply lenv_split_typ_renaming_one with (X:=X); auto.
         rewrite J. auto.
  Case "typing_tabs".
    pick fresh Z and apply typing_tabs; eauto.
      rewrite_env ((map (subst_tb X Y) ([(Z, bind_kn)]++E1))++[(Y, bind_kn)]++E2).
      rewrite subst_tt_fresh with (T:=Z) (U:=Y) (Z:=X); auto.
      rewrite <- subst_te_open_te; auto.
      rewrite <- subst_tt_open_tt; auto.
  Case "typing_tapp".
    rewrite subst_tt_open_tt; auto.
    apply typing_tapp; auto.
      assert (typ_all (subst_tt X Y T1) =  subst_tt X Y (typ_all T1)) as EQ. auto.
      rewrite EQ.
      apply IHTYP; auto.

      apply wf_typ_typ_renaming_one' with (X:=X); auto.
  Case "typing_bang".
    apply typing_bang; auto.
      apply IHTYP; auto.
  Case "typing_let".
    assert (J:=H1).
    apply dom_lenv_split in J.
    rewrite J in yn.   
    apply typing_let with (L:=L `union` {{X}} `union` {{Y}})(D1:=map (subst_tlb X Y) D1) (D2:=map (subst_tlb X Y) D2) (T1:=subst_tt X Y T1); eauto.
      assert (typ_bang (subst_tt X Y T1) =  subst_tt X Y (typ_bang T1)) as EQ. auto.
      rewrite EQ.
      apply IHTYP; auto.

      intros x xn.
      assert (x `notin` L) as xnL. auto.
      apply H0 with (X0:=X)(E3:=[(x, bind_typ T1)]++E1) in xnL; auto.
       rewrite_env ((map (subst_tb X Y) ([(x, bind_typ T1)]++E1))++[(Y, bind_kn)]++E2).
       rewrite subst_te_fresh with (e:=x) (U:=Y) (X:=X); auto.
       rewrite <- subst_te_open_ee; auto.

      apply lenv_split_typ_renaming_one with (X:=X); auto.
         rewrite J. auto.
  Case "typing_fst".
    apply typing_fst with (T2:=subst_tt X Y T2); eauto.
      assert (typ_with(subst_tt X Y T1) (subst_tt X Y T2) =  subst_tt X Y (typ_with T1 T2)) as EQ. auto.
      rewrite EQ.
      apply IHTYP; auto.
  Case "typing_snd".
    apply typing_snd with (T1:=subst_tt X Y T1); eauto.
      assert (typ_with(subst_tt X Y T1) (subst_tt X Y T2) =  subst_tt X Y (typ_with T1 T2)) as EQ. auto.
      rewrite EQ.
      apply IHTYP; auto.
Qed.

Lemma _wf_lenv_typ_permute: forall F E1 X E2 D,
  wf_lenv (F++E1++[(X, bind_kn)]++E2) D ->
  wf_env (E1++E2) ->
  wf_lenv (F++[(X, bind_kn)]++E1++E2) D.
Proof.
  intros F E1 X E2 D Wfle.
  remember (F++E1++[(X, bind_kn)]++E2) as E.
  generalize dependent F.
  generalize dependent E1.
  induction Wfle; intros; subst.
    apply wf_lenv_empty.
      apply _wf_env_typ_permute; auto.

    apply wf_lenv_typ; auto.
      apply _wf_typ_typ_permute; auto.
Qed.     

Lemma wf_lenv_typ_permute: forall E1 X E2 D,
  wf_lenv (E1++[(X, bind_kn)]++E2) D->
  wf_env (E1++E2) ->
  wf_lenv ([(X, bind_kn)]++E1++E2) D.
Proof.
  intros E1 X E2 D Wfle Wfle'.
  rewrite_env (nil++E1++[(X, bind_kn)]++E2) in Wfle.
  apply _wf_lenv_typ_permute with (X:=X) (F:=nil) (E1:=E1) (E2:=E2) in Wfle; auto.
Qed.

Lemma _lenv_split_typ_permute: forall F E1 X E2 D1 D2 D,
  lenv_split (F++E1++[(X, bind_kn)]++E2) D1 D2 D ->
  wf_env (E1++E2) ->
  lenv_split (F++ [(X, bind_kn)]++E1++E2)D1 D2 D.
Proof.
  intros F E1 X E2 D1 D2 D Split Wfe.
  remember (F++E1++[(X, bind_kn)]++E2) as E.
  generalize dependent F.
  generalize dependent E1.
  generalize dependent X.
  induction Split; intros; subst; simpl; simpl_env.
    apply lenv_split_empty.
      apply _wf_env_typ_permute; auto.

    apply lenv_split_left; auto.
      apply _wf_typ_typ_permute; auto.
         apply wf_lenv_split in Split; auto.

    apply lenv_split_right; auto.
      apply _wf_typ_typ_permute; auto.
         apply wf_lenv_split in Split; auto.
Qed.

Lemma _typing_typ_permute: forall F E1 X E2 D e t,
  typing (F++E1++[(X, bind_kn)]++E2) D e t ->
  wf_env (E1++E2) ->
  typing (F++[(X, bind_kn)]++E1++E2) D e t.
Proof.
  intros F E1 X E2 D e t TYP.
  remember (F++E1++[(X, bind_kn)]++E2) as E.
  generalize dependent F.
  generalize dependent E1.
  generalize dependent X.
  (typing_cases (induction TYP) Case); intros; subst; eauto.
  Case "typing_var".
    apply typing_var; auto.
      apply _wf_env_typ_permute; auto.
      
      apply uniq_from_wf_env in H.
      analyze_binds H0; auto.
  Case "typing_lvar".
    apply typing_lvar; auto.
      apply _wf_lenv_typ_permute with (F:=F) (E1:=E1) (E2:=E2) in H; auto.
  Case "typing_abs".
    pick fresh y and apply typing_abs; auto.
      apply _wf_typ_typ_permute; auto.
        pick fresh y.
        assert (y `notin` L) as ynL. auto.
        apply H0 in ynL.
        apply typing_regular in ynL.
        decompose [and] ynL.
        inversion H4; subst; auto.
  Case "typing_app".
    apply typing_app with (D1:=D1) (D2:=D2) (T1:=T1); auto.
      apply _lenv_split_typ_permute; auto.
  Case "typing_tabs".
    pick fresh Z and apply typing_tabs; eauto.
      rewrite_env (([(Z, bind_kn)]++F)++[(X, bind_kn)]++E1++E2).
      apply H0; auto.
  Case "typing_tapp".
    apply typing_tapp; auto.
      apply _wf_typ_typ_permute; auto.
  Case "typing_let".
    apply typing_let with (L:=L)(D1:=D1) (D2:=D2) (T1:=T1); auto.
      intros x xn.
      apply H0 with (X0:=X)(E3:=E1)(F0:=[(x, bind_typ T1)]++F) in xn; auto.

      apply _lenv_split_typ_permute; auto.
Qed.

Lemma typing_typ_permute: forall E1 X E2 D e t,
  typing (E1++[(X, bind_kn)]++E2) D e t ->
  wf_env (E1++E2) ->
  typing ([(X, bind_kn)]++E1++E2) D e t.
Proof.
  intros E1 X E2 D e t TYP Wfe.
  rewrite_env (nil++E1++[(X, bind_kn)]++E2) in TYP.
  apply _typing_typ_permute in TYP; auto.
Qed.

Lemma typing_typ_renaming_permute : forall E' E D e t (X Y:atom),
  typing (E'++[(X,bind_kn)]++E) D e t ->
  wf_lenv (E'++E) D ->
  Y `notin` dom E `union` dom E' `union` dom D ->
  typing ([(Y,bind_kn)]++E'++E) D (subst_te X Y e) (subst_tt X Y t).
Proof.
  intros E' E D e t X Y Typ Wfle yndom.
  assert (X `notin` fv_env E' `union` fv_env E `union` fv_lenv D) as J.
    apply wf_lenv_notin_fv_env; auto.
  apply typing_typ_renaming_one with (Y:=Y) in Typ; auto.
  rewrite <- map_subst_tlb_id with (G:=E'++E) in Typ; auto.
  rewrite <- map_subst_tb_id' with (G':=E) in Typ; auto.
  apply typing_typ_permute  in Typ; auto.  
Qed.

Require Export Bang_Parametricity.
Require Import Bang_Parametricity_Macro.

Export Parametricity.

Lemma wf_dsubst_app_inv : forall E1 E2 dsubst,
  wf_delta_subst (E1++E2) dsubst ->
  exists dsubst1, exists dsubst2, 
    dsubst = dsubst1 ++ dsubst2 /\
    ddom_env E1 [=] dom dsubst1 /\
    ddom_env E2 [=] dom dsubst2.
Proof.
  intros E1 E2 dsubst Wfd.
  remember (E1++E2) as E.
  generalize dependent E1.        
  generalize dependent E2.
  induction Wfd; intros; subst.
    symmetry in HeqE.
    apply app_eq_nil in HeqE.
    destruct HeqE; subst.
    exists nil. exists nil. simpl. auto.

    apply one_eq_app in HeqE.
    destruct HeqE as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      assert (E''++E2=E''++E2) as EQ. auto.
      apply IHWfd in EQ.
      destruct EQ as [dsubst1 [dsubst2 [EQ1 [EQ2 EQ3]]]]; subst.
      exists ([(X, T)]++dsubst1). exists dsubst2.
      simpl. split; auto. split; auto. fsetdec.
 
      assert (E=nil++E) as EQ. auto.
      apply IHWfd in EQ.
      destruct EQ as [dsubst1 [dsubst2 [EQ1 [EQ2 EQ3]]]]; subst.
      exists nil. exists ([(X, T)]++dsubst1++dsubst2).
      simpl. split; auto. split; auto. simpl_env. fsetdec.

    apply one_eq_app in HeqE.
    destruct HeqE as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      assert (E''++E2=E''++E2) as EQ. auto.
      apply IHWfd in EQ.
      destruct EQ as [dsubst1 [dsubst2 [EQ1 [EQ2 EQ3]]]]; subst.
      exists (dsubst1). exists dsubst2.
      simpl. split; auto.
 
      assert (E=nil++E) as EQ. auto.
      apply IHWfd in EQ.
      destruct EQ as [dsubst1 [dsubst2 [EQ1 [EQ2 EQ3]]]]; subst.
      exists nil. exists (dsubst1++dsubst2).
      simpl. split; auto. split; auto. simpl_env. fsetdec.
Qed.

Lemma wf_rsubst_app_inv : forall E1 E2 rsubst,
  wf_rho_subst (E1++E2) rsubst ->
  exists rsubst1, exists rsubst2, 
    rsubst = rsubst1 ++ rsubst2 /\
    ddom_env E1 [=] dom rsubst1 /\
    ddom_env E2 [=] dom rsubst2.
Proof.
  intros E1 E2 rsubst Wfr.
  remember (E1++E2) as E.
  generalize dependent E1.        
  generalize dependent E2.
  induction Wfr; intros; subst.
    symmetry in HeqE.
    apply app_eq_nil in HeqE.
    destruct HeqE; subst.
    exists nil. exists nil. simpl. auto.

    apply one_eq_app in HeqE.
    destruct HeqE as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      assert (E''++E2=E''++E2) as EQ. auto.
      apply IHWfr in EQ.
      destruct EQ as [rsubst1 [rsubst2 [EQ1 [EQ2 EQ3]]]]; subst.
      exists ([(X, R)]++rsubst1). exists rsubst2.
      simpl. split; auto. split; auto. fsetdec.
 
      assert (E=nil++E) as EQ. auto.
      apply IHWfr in EQ.
      destruct EQ as [rsubst1 [rsubst2 [EQ1 [EQ2 EQ3]]]]; subst.
      exists nil. exists ([(X, R)]++rsubst1++rsubst2).
      simpl. split; auto. split; auto. simpl_env. fsetdec.

    apply one_eq_app in HeqE.
    destruct HeqE as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      assert (E''++E2=E''++E2) as EQ. auto.
      apply IHWfr in EQ.
      destruct EQ as [rsubst1 [rsubst2 [EQ1 [EQ2 EQ3]]]]; subst.
      exists (rsubst1). exists rsubst2.
      simpl. split; auto.
 
      assert (E=nil++E) as EQ. auto.
      apply IHWfr in EQ.
      destruct EQ as [rsubst1 [rsubst2 [EQ1 [EQ2 EQ3]]]]; subst.
      exists nil. exists (rsubst1++rsubst2).
      simpl. split; auto. split; auto. simpl_env. fsetdec.
Qed.

Lemma wf_lgsubst_app_inv : forall E1 E2 D dsubst gsubst lgsubst,
  wf_lgamma_subst (E1++E2) D dsubst gsubst lgsubst ->
  exists dsubst1, exists dsubst2, exists gsubst1, exists gsubst2,
    dsubst = dsubst1 ++ dsubst2 /\
    ddom_env E1 [=] dom dsubst1 /\
    ddom_env E2 [=] dom dsubst2 /\
    gsubst = gsubst1 ++ gsubst2 /\
    gdom_env E1 [=] dom gsubst1 /\
    gdom_env E2 [=] dom gsubst2.
Proof.
  intros E1 E2 D dsubst gsubst lgsubst Wflg.
  remember (E1++E2) as E.
  generalize dependent E1.        
  generalize dependent E2.
  induction Wflg; intros; subst.
    symmetry in HeqE.
    apply app_eq_nil in HeqE.
    destruct HeqE; subst.
    exists nil. exists nil. exists nil. exists nil. simpl. split; auto.

    apply one_eq_app in HeqE.
    destruct HeqE as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      assert (E''++E2=E''++E2) as EQ. auto.
      apply IHWflg in EQ.
      destruct EQ as [dsubst1 [dsubst2 [gsubst1 [gsubst2 [EQ1 [EQ2 [EQ3 [EQ4 [EQ5 EQ6]]]]]]]]]; subst.
      exists dsubst1. exists dsubst2.
      exists ([(x, e)]++gsubst1). exists gsubst2.
      simpl. split; auto. split; auto. split; auto. split; auto. split; auto. fsetdec.
 
      assert (E=nil++E) as EQ. auto.
      apply IHWflg in EQ.
      destruct EQ as [dsubst1 [dsubst2 [gsubst1 [gsubst2 [EQ1 [EQ2 [EQ3 [EQ4 [EQ5 EQ6]]]]]]]]]; subst.
      exists nil. exists (dsubst1++dsubst2).
      exists nil. exists ([(x, e)]++gsubst1++gsubst2).
      simpl. simpl_env.  split; auto. split; auto. split; auto. fsetdec. split; auto. split; auto. fsetdec.

    assert (E1++E2=E1++E2) as EQ. auto.
    apply IHWflg in EQ.
    destruct EQ as [dsubst1 [dsubst2 [gsubst1 [gsubst2 [EQ1 [EQ2 [EQ3 [EQ4 [EQ5 EQ6]]]]]]]]]; subst.
    exists dsubst1. exists dsubst2.
    exists (gsubst1). exists gsubst2.
    split; auto.

    apply one_eq_app in HeqE.
    destruct HeqE as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      assert (E''++E2=E''++E2) as EQ. auto.
      apply IHWflg in EQ.
      destruct EQ as [dsubst1 [dsubst2 [gsubst1 [gsubst2 [EQ1 [EQ2 [EQ3 [EQ4 [EQ5 EQ6]]]]]]]]]; subst.
      exists ([(X, T)]++dsubst1). exists dsubst2.
      exists gsubst1. exists gsubst2.
      simpl. split; auto. split; auto. fsetdec.
 
      assert (E=nil++E) as EQ. auto.
      apply IHWflg in EQ.
      destruct EQ as [dsubst1 [dsubst2 [gsubst1 [gsubst2 [EQ1 [EQ2 [EQ3 [EQ4 [EQ5 EQ6]]]]]]]]]; subst.
      exists nil. exists ([(X, T)]++dsubst1++dsubst2).
      exists gsubst1. exists gsubst2.
      simpl. split; auto. split; auto. split; auto. simpl_env. fsetdec.
Qed.

Lemma wf_lgsubst_lapp_inv : forall E D1 D2 dsubst gsubst lgsubst,
  wf_lgamma_subst E (D1++D2) dsubst gsubst lgsubst ->
  exists lgsubst1, exists lgsubst2,
    lgsubst = lgsubst1 ++ lgsubst2 /\
    dom D1 [=] dom lgsubst1 /\
    dom D2 [=] dom lgsubst2.
Proof.
  intros E D1 D2 dsubst gsubst lgsubst Wflg.
  remember (D1++D2) as D.
  generalize dependent D1.        
  generalize dependent D2.
  induction Wflg; intros; subst.
    symmetry in HeqD.
    apply app_eq_nil in HeqD.
    destruct HeqD; subst.
    exists nil. exists nil. simpl. split; auto.

    assert (D1++D2=D1++D2) as EQ. auto.
    apply IHWflg in EQ.
    destruct EQ as [lgsubst1 [lgsubst2 [EQ1 [EQ2 EQ3]]]]; subst.
    exists (lgsubst1). exists lgsubst2.
    split; auto.

    apply one_eq_app in HeqD.
    destruct HeqD as [[D'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      assert (D''++D2=D''++D2) as EQ. auto.
      apply IHWflg in EQ.
      destruct EQ as [lgsubst1 [lgsubst2 [EQ1 [EQ2 EQ3]]]]; subst.
      exists ([(x, e)]++lgsubst1). exists lgsubst2.
      simpl. split; auto. split; auto. fsetdec.
 
      assert (lE=nil++lE) as EQ. auto.
      apply IHWflg in EQ.
      destruct EQ as [lgsubst1 [lgsubst2 [EQ1 [EQ2 EQ3]]]]; subst.
      exists nil. exists ([(x, e)]++lgsubst1++lgsubst2).
      simpl. simpl_env.  split; auto. split; auto. fsetdec.

    assert (D1++D2=D1++D2) as EQ. auto.
    apply IHWflg in EQ.
    destruct EQ as [lgsubst1 [lgsubst2 [EQ1 [EQ2 EQ3]]]]; subst.
    exists (lgsubst1). exists lgsubst2.
    split; auto.
Qed.

Lemma dom_F_related_subst : forall E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst',
  F_related_subst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
  ddom_env E [=] dom dsubst /\
  ddom_env E [=] dom dsubst' /\
  ddom_env E [=] dom rsubst /\
  gdom_env E [=] dom gsubst /\
  gdom_env E [=] dom gsubst' /\
  dom D [=] dom lgsubst /\
  dom D [=] dom lgsubst'.
Proof.
  induction 1; simpl.
    split; auto. split; auto.

    destruct IHF_related_subst as [J1 [J2 [J3 [J4 [J5 [J6 J7]]]]]].
    rewrite <- J1. rewrite <- J2. rewrite <- J3. rewrite <- J4.
    rewrite <- J5. rewrite <- J6. rewrite <- J7.  
    split; auto. fsetdec.
    split. clear. fsetdec.
    split. clear. fsetdec.
    split. clear. fsetdec.
    split. clear. fsetdec.
    split. clear. fsetdec.
               clear. fsetdec.

    destruct IHF_related_subst as [J1 [J2 [J3 [J4 [J5 [J6 J7]]]]]].
    rewrite <- J1. rewrite <- J2. rewrite <- J3. rewrite <- J4.
    rewrite <- J5. rewrite <- J6. rewrite <- J7.  
    split; auto. fsetdec.
    split. clear. fsetdec.
    split. clear. fsetdec.
    split. clear. fsetdec.
    split. clear. fsetdec.
    split. clear. fsetdec.
               clear. fsetdec.

    destruct IHF_related_subst as [J1 [J2 [J3 [J4 [J5 [J6 J7]]]]]].
    rewrite <- J1. rewrite <- J2. rewrite <- J3. rewrite <- J4.
    rewrite <- J5. rewrite <- J6. rewrite <- J7.  
    split; auto. fsetdec.
    split. clear. fsetdec.
    split. clear. fsetdec.
    split. clear. fsetdec.
    split. clear. fsetdec.
    split. clear. fsetdec.
               clear. fsetdec.
Qed.

Lemma dom_lgamma_subst : forall E D dsubst gsubst lgsubst,
  wf_lgamma_subst E D dsubst gsubst lgsubst -> 
  ddom_env E [=] dom dsubst /\
  gdom_env E [=] dom gsubst /\
  dom D [=] dom lgsubst.
Proof.
  intros E D dsubst gsubst lgsubst Wflg.
  induction Wflg; simpl_env; simpl.
    split; auto.

    destruct IHWflg as [J1 [J2 J3]].
    rewrite <- J1. rewrite <- J2. rewrite <- J3.
    split; auto. fsetdec.
    split. clear. fsetdec.
               clear. fsetdec.

    destruct IHWflg as [J1 [J2 J3]].
    rewrite <- J1. rewrite <- J2. rewrite <- J3.
    split; auto. fsetdec.
    split. clear. fsetdec.
               clear. fsetdec.

    destruct IHWflg as [J1 [J2 J3]].
    rewrite <- J1. rewrite <- J2. rewrite <- J3.
    split; auto. fsetdec.
    split. clear. fsetdec.
               clear. fsetdec.
Qed.

Lemma wf_lgsubst_lcons_inv : forall E x T D dsubst gsubst lgsubst,
  wf_lgamma_subst E ([(x, lbind_typ T)]++D) dsubst gsubst lgsubst ->
  exists e, exists lgsubst',
    lgsubst = [(x, e)] ++ lgsubst' /\
    dom D [=] dom lgsubst' /\
    wf_typ E T /\
    typing nil nil e (apply_delta_subst_typ dsubst T).
Proof.
  intros E x T D dsubst gsubst lgsubst Wflg.
  remember ([(x, lbind_typ T)]++D) as DD.
  generalize dependent D.        
  generalize dependent x.
  generalize dependent T.
  induction Wflg; intros; subst.
    inversion HeqDD.

    assert ([(x0, lbind_typ T0)]++D=[(x0, lbind_typ T0)]++D) as EQ. auto.
    apply IHWflg in EQ.
    destruct EQ as [e0 [lgsubst' [EQ1 [EQ2 [Wft Typ]]]]]; subst.
    exists e0. exists lgsubst'.
    split; auto.
    split; auto.
    split; auto.
      apply wf_typ_weaken_head; auto.
        apply wf_lgamma_subst__wf_lenv in Wflg.
        destruct Wflg; auto.        

    inversion HeqDD; subst. clear HeqDD.
    exists e. exists lgsE.
    split; auto.
    split; auto.
      apply dom_lgamma_subst in Wflg.
      decompose [and] Wflg; auto.

    assert ([(x, lbind_typ T0)]++D=[(x, lbind_typ T0)]++D) as EQ. auto.
    apply IHWflg in EQ.
    destruct EQ as [e [lgsubst' [EQ1 [EQ2 [Wft Typ]]]]]; subst.
    exists e. exists lgsubst'.
    split; auto.
    split; auto.
    split.
      apply wf_typ_weaken_head; auto.
        apply wf_lgamma_subst__wf_lenv in Wflg.
        destruct Wflg; auto.              

      simpl. simpl in H0.
      rewrite <- subst_tt_fresh; auto.
        apply notin_fv_wf with (X:=X) in Wft; auto.
Qed.

Lemma F_related_subst_lcons_inv : forall E x T D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst',
  F_related_subst E ([(x, lbind_typ T)]++D) gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
  exists e, exists lgsubst0,
    exists e', exists lgsubst0',
      lgsubst = [(x, e)] ++ lgsubst0 /\
      lgsubst' = [(x, e')] ++ lgsubst0' /\
      dom D [=] dom lgsubst0 /\
      dom D [=] dom lgsubst0' /\
      wf_typ E T /\
      typing nil nil e (apply_delta_subst_typ dsubst T) /\
      typing nil nil e' (apply_delta_subst_typ dsubst' T) /\
      F_related_terms T rsubst dsubst dsubst' e e' /\
      F_related_subst E D gsubst gsubst' lgsubst0 lgsubst0' rsubst dsubst dsubst'.
Proof.
  intros E x T D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Hrel_subst.
  remember ([(x, lbind_typ T)]++D) as DD.
  generalize dependent D.        
  generalize dependent x.
  generalize dependent T.
  induction Hrel_subst; intros; subst.
    inversion HeqDD.

    assert ([(x, lbind_typ T)]++D=[(x, lbind_typ T)]++D) as EQ. auto.
    apply IHHrel_subst in EQ.
    destruct EQ as [e [lgsubst0 [e' [lgsubst0' [EQ1 [EQ2 [EQ3 [EQ4 [Wft [Typ [Typ' [Hrel Sub]]]]]]]]]]]]; subst.
    exists e. exists lgsubst0.
    exists e'. exists lgsubst0'.
    simpl_env.
    split; auto.
    split; auto.
    split; auto.
    split; auto.
    split.
      apply wf_typ_weaken_head; auto.
        apply F_related_subst__inversion in Hrel_subst.
        decompose [prod] Hrel_subst. auto.
    split.
      simpl.
      rewrite <- subst_tt_fresh; auto.
        apply notin_fv_wf with (X:=X) in Wft; auto.
    split.
      simpl.
      rewrite <- subst_tt_fresh; auto.
        apply notin_fv_wf with (X:=X) in Wft; auto.
    split.
      apply F_related_subst__inversion in Hrel_subst.
      decompose [prod] Hrel_subst.
      destruct Hrel as [v [v' [Htv [Htv' [Henv [He'nv' Hrel]]]]]].
      exists v. exists v'.
      split.
        simpl. rewrite <- subst_tt_fresh; auto.
          apply notin_fv_wf with (X:=X) in Wft; auto.
      split.
        simpl. rewrite <- subst_tt_fresh; auto.
          apply notin_fv_wf with (X:=X) in Wft; auto.
      split; auto.
      split; auto.
        apply Frel_weaken_head with (E:=E); auto.
          apply dom_delta_subst in a; auto.
          apply dom_delta_subst in b3; auto.
          apply dom_rho_subst in b0; auto.
          apply notin_fv_wf with (X:=X) in Wft; auto.

      simpl_env in H.
      apply F_related_subst_kind; auto.

    assert ([(x0, lbind_typ T)]++D=[(x0, lbind_typ T)]++D) as EQ. auto.
    apply IHHrel_subst in EQ.
    destruct EQ as [e0 [lgsubst0 [e'0 [lgsubst0' [EQ1 [EQ2 [EQ3 [EQ4 [Wft [Typ [Typ' [Hrel Sub]]]]]]]]]]]]; subst.
    exists e0. exists lgsubst0.
    exists e'0. exists lgsubst0'.
    simpl_env.
    split; auto.
    split; auto.
    split; auto.
    split; auto.
    split.
      apply wf_typ_weaken_head; auto.
        apply F_related_subst__inversion in Hrel_subst.
        decompose [prod] Hrel_subst. auto.
    split; auto.
    split; auto.
    split; auto.
      simpl_env in H2. simpl in H2.
      apply F_related_subst_typ; auto.

    simpl_env in HeqDD.
    inversion HeqDD; subst.
    exists e. exists lgsubst.
    exists e'. exists lgsubst'.
    simpl_env.
    assert (J:=Hrel_subst).
    apply F_related_subst__inversion in J.
    decompose [prod] J.
    split; auto.
    split; auto.
    split.
        apply dom_lgamma_subst in b2.
        decompose [and] b2; auto.
    split.
        apply dom_lgamma_subst in b1.
        decompose [and] b1; auto.
    split; auto.
Qed.

Lemma Frel_stronger_head:  forall t E v v' rsubst dsubst dsubst' X R t2 t2',
  F_related_values t ([(X, R)]++rsubst) ([(X, t2)]++dsubst) ([(X, t2')]++dsubst') v v' ->
  X `notin` (fv_env E `union` (fv_tt t))->
  wfr R t2 t2' ->
  wf_rho_subst ([(X, bind_kn)]++E) ([(X, R)]++rsubst) ->
  wf_delta_subst ([(X, bind_kn)]++E) ([(X, t2)]++dsubst) ->
  wf_delta_subst ([(X, bind_kn)]++E) ([(X, t2')]++dsubst') ->
  F_related_values t rsubst dsubst dsubst' v v'
  .
Proof.
  intros t E v v' rsubst dsubst dsubst' X R t2 t2' Hrel HX Hwfr Rsubst Dsubst Dsubst'.
  rewrite_env (nil ++ [(X, R)] ++ rsubst) in Hrel.
  rewrite_env (nil ++ [(X, t2)] ++ dsubst) in Hrel.
  rewrite_env (nil ++ [(X, t2')] ++ dsubst') in Hrel.
  apply Frel_stronger with (E:=E) (E':=nil) in Hrel; auto.
    inversion Dsubst; subst.
    apply dom_delta_subst in H3. auto.

    inversion Dsubst'; subst.
    apply dom_delta_subst in H3. auto.

    inversion Rsubst; subst.
    apply dom_rho_subst in H2. auto.
Qed.

Lemma  Frel_stronger_heads:  forall t E' E v v' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0,
  F_related_values t (rsubst'++rsubst) (dsubst0++dsubst) (dsubst'0++dsubst') v v' ->
  ddom_env E [=] dom dsubst ->
  ddom_env E [=] dom dsubst' ->
  ddom_env E' [=] dom dsubst0 ->
  ddom_env E' [=] dom dsubst'0 ->
  ddom_env E [=] dom rsubst ->
  ddom_env E' [=] dom rsubst' ->
  fv_tt t [<=] ddom_env E ->
  wf_rho_subst (E'++E) (rsubst'++rsubst) ->
  wf_delta_subst (E'++E) (dsubst0++dsubst) ->
  wf_delta_subst (E'++E) (dsubst'0++dsubst') ->
  F_related_values t rsubst dsubst dsubst' v v'
  .
Proof.
  intros t E' E v v' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 Hrel
    Hdomd Hdomd' Hdomd0 Hdomd0' Hdomr Hdomr' Hsub Hwfr Hwfd Hwfd'.         
  remember (E'++E)  as EE.
  remember (rsubst'++rsubst) as rS.
  generalize dependent E'.
  generalize dependent rsubst'.
  generalize dependent dsubst0.
  generalize dependent dsubst'0.
  (wf_rho_subst_cases (induction Hwfr) Case); intros; subst.
  Case "wf_rho_subst_empty".
    symmetry in HeqrS.
    apply app_eq_nil in HeqrS.
    destruct HeqrS; subst.

    symmetry in HeqEE.
    apply app_eq_nil in HeqEE.
    destruct HeqEE; subst.
    
    inversion Hwfd; subst.
    inversion Hwfd'; subst.

    symmetry in H.
    apply app_eq_nil in H.
    destruct H; subst.

    symmetry in H0.
    apply app_eq_nil in H0.
    destruct H0; subst.

    auto.
  Case "wf_rho_subst_srel".
    inversion Hwfd; subst.
    inversion Hwfd'; subst.    
    simpl_env in *.
    apply one_eq_app in HeqrS. destruct HeqrS as [[rS0 [rEQ1 rEQ2]] | [rEQ1 rEQ2]]; subst.
      apply one_eq_app in H2. destruct H2 as [[dsubst1 [dEQ1 dEQ2]] | [dEQ1 dEQ2]]; subst.
        apply one_eq_app in H6. destruct H6 as [[dsubst1' [dEQ1' dEQ2']] | [dEQ1' dEQ2']]; subst.
          apply one_eq_app in HeqEE. destruct HeqEE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
            simpl_env in Hrel.
            assert (X `notin` fv_env (E0'++E)) as XnE.
              apply wfe_dom_fv_env; auto.
              apply wf_rho_subst__uniq in Hwfr.
              decompose [and] Hwfr; auto.
            apply Frel_stronger_head with (E:=E0'++E) in Hrel; auto.
               apply IHHwfr with (dsubst'0:=dsubst1') (dsubst0:=dsubst1) (rsubst':=rS0) (E':=E0'); auto.
                 apply ddom_dom__inv with (X:=X)(b:=T); auto.
                   destruct_notin.
                   apply dom_delta_subst in H3.
                   apply free_env__free_ddom in XnE.
                    rewrite H3 in XnE. simpl_env in XnE. auto.

                 apply ddom_dom__inv with (X:=X)(b:=T0); auto.
                   destruct_notin.
                   apply dom_delta_subst in H7.
                   apply free_env__free_ddom in XnE.
                    rewrite H7 in XnE. simpl_env in XnE. auto.
 
                 apply ddom_dom__inv with (X:=X)(b:=R); auto.
                   destruct_notin.
                   apply dom_rho_subst in Hwfr.
                   apply free_env__free_ddom in XnE.
                    rewrite Hwfr in XnE. simpl_env in XnE. auto.

                 assert (X `notin` fv_tt t) as Xnt.
                   apply free_env__free_ddom in XnE.
                   clear Hrel H H5 H9 Hwfr IHHwfr H4 Hwfd H8 Hwfd' Hdomr' Hdomd0 Hdomd0'.
                   simpl_env in XnE.
                   fsetdec.
                 auto.

                 split; auto.

            simpl_env in Hdomr'.
            assert (X `notin` (singleton X `union` dom rS0) -> False) as J.
              intro. destruct_notin. contradict NotInTac0; auto.
            rewrite <- Hdomr' in J.
            contradict J; auto.

          apply one_eq_app in HeqEE. destruct HeqEE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
            simpl_env in Hdomd0'.
            assert (X `notin` (singleton X `union` ddom_env E0') -> False) as J.
              intro. destruct_notin. contradict NotInTac0; auto.
            rewrite Hdomd0' in J.
            contradict J; auto.

            simpl_env in Hdomd0.
            assert (X `notin` (singleton X `union` dom dsubst1) -> False) as J.
              intro. destruct_notin. contradict NotInTac0; auto.
            rewrite <- Hdomd0 in J.
            contradict J; auto.

        apply one_eq_app in HeqEE. destruct HeqEE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
          simpl_env in Hdomd0.
          assert (X `notin` (singleton X `union` ddom_env E0') -> False) as J.
            intro. destruct_notin. contradict NotInTac0; auto.
          rewrite Hdomd0 in J.
          contradict J; auto.

          simpl_env in Hdomr'.
          assert (X `notin` (singleton X `union` dom rS0) -> False) as J.
            intro. destruct_notin. contradict NotInTac0; auto.
          rewrite <- Hdomr' in J.
          contradict J; auto.

      apply one_eq_app in HeqEE. destruct HeqEE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
        simpl_env in Hdomr'.
        assert (X `notin` (singleton X `union` ddom_env E0') -> False) as J.
          intro. destruct_notin. contradict NotInTac0; auto.
        rewrite Hdomr' in J.
        contradict J; auto.

        simpl in Hdomd0. symmetry in Hdomd0.  apply dom_empty_inv in Hdomd0.
        simpl in Hdomd0'. symmetry in Hdomd0'.  apply dom_empty_inv in Hdomd0'.
        subst. 
        simpl_env in H7. simpl_env in H3.
        subst.
        simpl_env. auto.

  Case "wf_rho_subst_skip".
    inversion Hwfd; subst.
    inversion Hwfd'; subst.    
    simpl_env in *.
    apply one_eq_app in HeqEE. destruct HeqEE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
      apply IHHwfr with (dsubst'0:=dsubst'0) (dsubst0:=dsubst0) (rsubst'0:=rsubst') (E':=E0'); auto.

      simpl in Hdomd0. symmetry in Hdomd0.  apply dom_empty_inv in Hdomd0.
      simpl in Hdomd0'. symmetry in Hdomd0'.  apply dom_empty_inv in Hdomd0'.
      simpl in Hdomr'. symmetry in Hdomr'.  apply dom_empty_inv in Hdomr'.
      subst. auto.
Qed.

Lemma  Frel_weaken_heads:  forall t E' E v v' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0,
  F_related_values t rsubst dsubst dsubst' v v' ->
  ddom_env E [=] dom dsubst ->
  ddom_env E [=] dom dsubst' ->
  ddom_env E' [=] dom dsubst0 ->
  ddom_env E' [=] dom dsubst'0 ->
  ddom_env E [=] dom rsubst ->
  ddom_env E' [=] dom rsubst' ->
  fv_tt t [<=] ddom_env E ->
  wf_rho_subst (E'++E) (rsubst'++rsubst) ->
  wf_delta_subst (E'++E) (dsubst0++dsubst) ->
  wf_delta_subst (E'++E) (dsubst'0++dsubst') ->
  F_related_values t (rsubst'++rsubst) (dsubst0++dsubst) (dsubst'0++dsubst') v v'
  .
Proof.
  intros t E' E v v' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 Hrel
    Hdomd Hdomd' Hdomd0 Hdomd0' Hdomr Hdomr' Hsub Hwfr Hwfd Hwfd'.         
  remember (E'++E)  as EE.
  remember (rsubst'++rsubst) as rS.
  generalize dependent E'.
  generalize dependent rsubst'.
  generalize dependent dsubst0.
  generalize dependent dsubst'0.
  (wf_rho_subst_cases (induction Hwfr) Case); intros; subst.
  Case "wf_rho_subst_empty".
    symmetry in HeqrS.
    apply app_eq_nil in HeqrS.
    destruct HeqrS; subst.

    symmetry in HeqEE.
    apply app_eq_nil in HeqEE.
    destruct HeqEE; subst.
    
    inversion Hwfd; subst.
    inversion Hwfd'; subst.

    symmetry in H.
    apply app_eq_nil in H.
    destruct H; subst.

    symmetry in H0.
    apply app_eq_nil in H0.
    destruct H0; subst.

    auto.
  Case "wf_rho_subst_srel".
    inversion Hwfd; subst.
    inversion Hwfd'; subst.    
    simpl_env in *.
    apply one_eq_app in HeqrS. destruct HeqrS as [[rS0 [rEQ1 rEQ2]] | [rEQ1 rEQ2]]; subst.
      apply one_eq_app in H2. destruct H2 as [[dsubst1 [dEQ1 dEQ2]] | [dEQ1 dEQ2]]; subst.
        apply one_eq_app in H6. destruct H6 as [[dsubst1' [dEQ1' dEQ2']] | [dEQ1' dEQ2']]; subst.
          apply one_eq_app in HeqEE. destruct HeqEE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
            assert (X `notin` fv_env (E0'++E)) as XnE.
              apply wfe_dom_fv_env; auto.
              apply wf_rho_subst__uniq in Hwfr.
              decompose [and] Hwfr; auto.
            apply Frel_weaken_head with (E:=E0'++E); auto.
               apply IHHwfr with (dsubst'0:=dsubst1') (dsubst0:=dsubst1) (rsubst':=rS0) (E':=E0'); auto.
                 apply ddom_dom__inv with (X:=X)(b:=T); auto.
                   destruct_notin.
                   apply dom_delta_subst in H3.
                   apply free_env__free_ddom in XnE.
                    rewrite H3 in XnE. simpl_env in XnE. auto.

                 apply ddom_dom__inv with (X:=X)(b:=T0); auto.
                   destruct_notin.
                   apply dom_delta_subst in H7.
                   apply free_env__free_ddom in XnE.
                    rewrite H7 in XnE. simpl_env in XnE. auto.
 
                 apply ddom_dom__inv with (X:=X)(b:=R); auto.
                   destruct_notin.
                   apply dom_rho_subst in Hwfr.
                   apply free_env__free_ddom in XnE.
                    rewrite Hwfr in XnE. simpl_env in XnE. auto.

               apply dom_delta_subst in H3. auto.

               apply dom_delta_subst in H7. auto.

               apply dom_rho_subst in Hwfr. auto.

               assert (X `notin` fv_tt t) as Xnt.
                 apply free_env__free_ddom in XnE.
                 clear Hrel H H5 H9 Hwfr IHHwfr H4 Hwfd H8 Hwfd' Hdomr' Hdomd0 Hdomd0'.
                 simpl_env in XnE.
                  fsetdec.
               auto.

               split; auto.

            simpl_env in Hdomr'.
            assert (X `notin` (singleton X `union` dom rS0) -> False) as J.
              intro. destruct_notin. contradict NotInTac0; auto.
            rewrite <- Hdomr' in J.
            contradict J; auto.

          apply one_eq_app in HeqEE. destruct HeqEE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
            simpl_env in Hdomd0'.
            assert (X `notin` (singleton X `union` ddom_env E0') -> False) as J.
              intro. destruct_notin. contradict NotInTac0; auto.
            rewrite Hdomd0' in J.
            contradict J; auto.

            simpl_env in Hdomd0.
            assert (X `notin` (singleton X `union` dom dsubst1) -> False) as J.
              intro. destruct_notin. contradict NotInTac0; auto.
            rewrite <- Hdomd0 in J.
            contradict J; auto.

        apply one_eq_app in HeqEE. destruct HeqEE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
          simpl_env in Hdomd0.
          assert (X `notin` (singleton X `union` ddom_env E0') -> False) as J.
            intro. destruct_notin. contradict NotInTac0; auto.
          rewrite Hdomd0 in J.
          contradict J; auto.

          simpl_env in Hdomr'.
          assert (X `notin` (singleton X `union` dom rS0) -> False) as J.
            intro. destruct_notin. contradict NotInTac0; auto.
          rewrite <- Hdomr' in J.
          contradict J; auto.

      apply one_eq_app in HeqEE. destruct HeqEE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
        simpl_env in Hdomr'.
        assert (X `notin` (singleton X `union` ddom_env E0') -> False) as J.
          intro. destruct_notin. contradict NotInTac0; auto.
        rewrite Hdomr' in J.
        contradict J; auto.

        simpl in Hdomd0. symmetry in Hdomd0.  apply dom_empty_inv in Hdomd0.
        simpl in Hdomd0'. symmetry in Hdomd0'.  apply dom_empty_inv in Hdomd0'.
        subst. 
        simpl_env in H6. simpl_env in H2.
        subst.
        simpl_env. auto.

  Case "wf_rho_subst_skip".
    inversion Hwfd; subst.
    inversion Hwfd'; subst.    
    simpl_env in *.
    apply one_eq_app in HeqEE. destruct HeqEE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
      apply IHHwfr with (dsubst'0:=dsubst'0) (dsubst0:=dsubst0) (rsubst'0:=rsubst') (E':=E0'); auto.

      simpl in Hdomd0. symmetry in Hdomd0.  apply dom_empty_inv in Hdomd0.
      simpl in Hdomd0'. symmetry in Hdomd0'.  apply dom_empty_inv in Hdomd0'.
      simpl in Hdomr'. symmetry in Hdomr'.  apply dom_empty_inv in Hdomr'.
      subst. auto.
Qed.

Lemma apply_delta_subst_typ_strenghen : forall E1 E2 dsubst1 dsubst2 T,
  wf_delta_subst (E1++E2) (dsubst1++dsubst2) ->
  ddom_env E1 [=] dom dsubst1 ->
  ddom_env E2 [=] dom dsubst2 ->
  fv_tt T [<=] ddom_env E2 ->
  apply_delta_subst_typ (dsubst1++dsubst2) T = apply_delta_subst_typ dsubst2 T.
Proof.
  intros E1 E2 dsubst1 dsubst2 T Hwfd Hdom1 Hdom2 Hsub.
  remember (E1++E2) as E.
  remember (dsubst1++dsubst2) as dsubst.
  generalize dependent E1.
  generalize dependent dsubst1.
  (wf_delta_subst_cases (induction Hwfd) Case); intros; subst.
  Case "wf_delta_subst_empty".
    symmetry in HeqE.
    apply app_eq_nil in HeqE.
    destruct HeqE; subst.

    symmetry in Heqdsubst.
    apply app_eq_nil in Heqdsubst.
    destruct Heqdsubst; subst.
    
    simpl. auto.
  Case "wf_delta_subst_styp".
    apply one_eq_app in HeqE. destruct HeqE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
      apply one_eq_app in Heqdsubst. destruct Heqdsubst as [[dsubst0' [dEQ1' dEQ2']] | [dEQ1' dEQ2']]; subst; auto.
        simpl.
        assert (X `notin` fv_env (E0'++E2)) as XnE.
          apply wfe_dom_fv_env; auto.
          apply  wf_delta_subst__uniq in Hwfd.
          decompose [and] Hwfd; auto.
          apply free_env__free_ddom in XnE.
        rewrite <- subst_tt_fresh; auto.
          eapply IHHwfd; eauto.
            apply ddom_dom__inv with (X:=X)(b:=T0); auto.
            apply dom_delta_subst in Hwfd.
            rewrite Hwfd in XnE.
            simpl_env in XnE. auto.
          simpl_env in XnE.  fsetdec.
            
        simpl in Hdom1. symmetry in Hdom1.  apply dom_empty_inv in Hdom1.
        subst. 
        simpl_env in Heqdsubst.
        subst. auto.
  Case "wf_delta_subst_skip".
    apply one_eq_app in HeqE. destruct HeqE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
      eapply IHHwfd; eauto.

      simpl in Hdom1. symmetry in Hdom1.  apply dom_empty_inv in Hdom1.
      subst. auto. 
Qed.

Lemma gamma_subst_opt :  forall E E' D dsubst x t gsubst gsubst' v lgsubst e,
   wf_lgamma_subst (E'++[(x, bind_typ t)]++E) D dsubst (gsubst'++[(x, v)]++gsubst) lgsubst ->
   gdom_env E [=] dom gsubst ->
   gdom_env E' [=] dom gsubst' ->
   typing nil nil v (apply_delta_subst_typ dsubst t) ->
   apply_gamma_subst (gsubst'++[(x, v)]++gsubst) e =
    apply_gamma_subst (gsubst'++gsubst) (subst_ee x v e).
Proof.
  intros E E' D dsubst x t gsubst gsubst' v lgsubst e Hwf_lgamma_subst Heq Heq' Typ.
  remember (E'++[(x, bind_typ t)]++E) as G.
  remember (gsubst'++[(x, v)]++gsubst) as Gsubst.
  generalize dependent e.
  generalize dependent gsubst'.
  generalize dependent E'.
  (wf_lgamma_subst_cases (induction Hwf_lgamma_subst) Case); intros; subst.
  Case "wf_lgamma_subst_empty".
    contradict HeqG; auto.    
  Case "wf_lgamma_subst_sval".
    destruct (one_eq_app _ _ _ _ _ HeqG) as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
    SCase "exists E'', E'=E&X0'' /\ E0=E&X&E'' ".
      destruct (one_eq_app _ _ _ _ _ HeqGsubst) as [[gsubst'' [GEQ1 GEQ2]] | [GEQ1 GEQ2]]; subst.
      SSCase "exists GS'',GS'=GS&X0'' /\ GS0=GS&X&GS'' ".
        simpl. simpl_env. 
        rewrite <- subst_ee_commute; auto.
           apply IHHwf_lgamma_subst with (E':=E'') (gsubst':=gsubst''); auto.
             apply gdom_dom__inv with (x:=x0)(b:= e)(t:=T); auto.
               apply dom__gdom in H.
               simpl_env in H. auto.

               apply dom_lgamma_subst in Hwf_lgamma_subst.
               destruct Hwf_lgamma_subst as [J1 [J2 J3]].
               apply dom__gdom in H.
               rewrite J2 in H. simpl_env in *. auto.
          eauto using notin_fv_ee_typing.
          eauto using notin_fv_ee_typing.
      SSCase "GS'=nil /\ GS&X = GS0&X0 ".
        inversion GEQ2. subst.
        simpl_env in *. destruct_notin.
        auto.
    SCase "E'=nil /\ E&X = E0&X0 ".
      inversion EQ2; subst.
      destruct (one_eq_app _ _ _ _ _ HeqGsubst) as [[gsubst'' [GEQ1 GEQ2]] | [GEQ1 GEQ2]]; subst.
      SSCase "exists GS'',GS'=GS&X0'' /\ GS0=GS&X&GS'' ".
        simpl_env in Heq'.
        assert (x0 `notin` (singleton x0 `union` dom gsubst'') -> False) as J.
            intro. destruct_notin. apply NotInTac0; auto.
        rewrite <- Heq' in J.
        contradict J; auto.
     SSCase "GS'=nil /\ GS&X = GS0&X0 ".
        inversion GEQ2; subst; auto.
  Case "wf_lgamma_subst_slval".
    apply IHHwf_lgamma_subst with (E'0:=E') (gsubst'0:=gsubst'); auto.
  Case "wf_lgamma_subst_skind".
    destruct (one_eq_app _ _ _ _ _ HeqG) as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      apply IHHwf_lgamma_subst with (E':=E'') (gsubst'0:=gsubst'); auto.
        simpl in Typ.
        apply wf_lgamma_subst__wf_lenv in Hwf_lgamma_subst.
        destruct Hwf_lgamma_subst as [J1 J2].
        apply wfe_dom_fv_env with (x:=X) in J1; auto.
        simpl_env in J1. simpl in J1.
        rewrite <- subst_tt_fresh in Typ; auto.

      simpl_env in HeqG.
      inversion HeqG.
Qed.

Lemma lgamma_subst_opt :  forall E D D' dsubst x t gsubst lgsubst lgsubst' v e,
   wf_lgamma_subst E (D'++[(x, lbind_typ t)]++D) dsubst gsubst (lgsubst'++[(x, v)]++lgsubst) ->
   dom D [=] dom lgsubst ->
   dom D' [=] dom lgsubst' ->
   typing nil nil v (apply_delta_subst_typ dsubst t) ->
   apply_gamma_subst (lgsubst'++[(x, v)]++lgsubst) e =
    apply_gamma_subst (lgsubst'++lgsubst) (subst_ee x v e).
Proof.
  intros E D D' dsubst x t gsubst lgsubst lgsubst' v e Hwf_lgamma_subst Heq Heq' Typ.
  remember (D'++[(x, lbind_typ t)]++D) as G.
  remember (lgsubst'++[(x, v)]++lgsubst) as Gsubst.
  generalize dependent e.
  generalize dependent lgsubst'.
  generalize dependent D'.
  (wf_lgamma_subst_cases (induction Hwf_lgamma_subst) Case); intros; subst.
  Case "wf_lgamma_subst_empty".
    contradict HeqG; auto.    
  Case "wf_lgamma_subst_sval".
    apply IHHwf_lgamma_subst with (D'0:=D') (lgsubst'0:=lgsubst'); auto.
  Case "wf_lgamma_subst_slval".
    destruct (one_eq_app _ _ _ _ _ HeqG) as [[D'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
    SCase "exists D'', D'=D&X0'' /\ D0=D&X&D'' ".
      destruct (one_eq_app _ _ _ _ _ HeqGsubst) as [[lgsubst'' [GEQ1 GEQ2]] | [GEQ1 GEQ2]]; subst.
      SSCase "exists GS'',GS'=GS&X0'' /\ GS0=GS&X&GS'' ".
        simpl. simpl_env. 
        rewrite <- subst_ee_commute; auto.
           apply IHHwf_lgamma_subst with (D':=D'') (lgsubst':=lgsubst''); auto.
             apply dom_dom__inv with (x:=x0)(b':= e)(b:=lbind_typ T); auto.
               apply dom_lgamma_subst in Hwf_lgamma_subst.
               destruct Hwf_lgamma_subst as [J1 [J2 J3]].
               rewrite J3 in H0. simpl_env in *. auto.
          eauto using notin_fv_ee_typing.
          eauto using notin_fv_ee_typing.
      SSCase "GS'=nil /\ GS&X = GS0&X0 ".
        inversion GEQ2. subst.
        simpl_env in *. destruct_notin.
        auto.
    SCase "E'=nil /\ E&X = E0&X0 ".
      inversion EQ2; subst.
      destruct (one_eq_app _ _ _ _ _ HeqGsubst) as [[lgsubst'' [GEQ1 GEQ2]] | [GEQ1 GEQ2]]; subst.
      SSCase "exists GS'',GS'=GS&X0'' /\ GS0=GS&X&GS'' ".
        simpl_env in Heq'.
        assert (x0 `notin` (singleton x0 `union` dom lgsubst'') -> False) as J.
            intro. destruct_notin. apply NotInTac0; auto.
        rewrite <- Heq' in J.
        contradict J; auto.
     SSCase "GS'=nil /\ GS&X = GS0&X0 ".
        inversion GEQ2; subst; auto.
  Case "wf_lgamma_subst_skind".
    apply IHHwf_lgamma_subst with (D'0:=D') (lgsubst'0:=lgsubst'); auto.
      simpl in Typ.
      apply wf_lgamma_subst__wf_lenv in Hwf_lgamma_subst.
      destruct Hwf_lgamma_subst as [J1 J2].
      apply notin_fv_lenv_wfle with (X:=X) in J2; auto.
      simpl_env in J2. simpl in J2.
      rewrite <- subst_tt_fresh in Typ; auto.
Qed.

Lemma dom_F_Rsubst : forall E rsubst dsubst dsubst',
  F_Rsubst E rsubst dsubst dsubst' ->
  ddom_env E [=] dom dsubst /\
  ddom_env E [=] dom dsubst' /\
  ddom_env E [=] dom rsubst.
Proof.
  induction 1; simpl.
    split; auto.

    destruct IHF_Rsubst as [J1 [J2 J3]].
    rewrite <- J1. rewrite <- J2. rewrite <- J3.  
    split; auto. fsetdec.
    split. clear. fsetdec.
               clear. fsetdec.

    destruct IHF_Rsubst as [J1 [J2 J3]].
    rewrite <- J1. rewrite <- J2. rewrite <- J3.  
    split; auto. fsetdec.
    split. clear. fsetdec.
               clear. fsetdec.
Qed.

Lemma delta_subst_opt' :  forall E E' dsubst dsubst' X t e,
   wf_delta_subst (E'++[(X, bind_kn)]++E) (dsubst'++[(X, t)]++dsubst) ->
   ddom_env E [=] dom dsubst ->
   ddom_env E' [=] dom dsubst' ->
   wf_typ nil t ->
   apply_delta_subst (dsubst'++[(X, t)]++dsubst) e =
    apply_delta_subst (dsubst'++dsubst) (subst_te X t e).
Proof.
  intros E E' dsubst dsubst' X t e Hwf_delta_subst Heq Heq' Typ.
  remember (E'++[(X, bind_kn)]++E) as G.
  remember (dsubst'++[(X, t)]++dsubst) as Dsubst.
  generalize dependent e.
  generalize dependent dsubst'.
  generalize dependent E'.
  (wf_delta_subst_cases (induction Hwf_delta_subst) Case); intros; subst.
  Case "wf_delta_subst_empty".
    contradict HeqG; auto.    
  Case "wf_delta_subst_styp".
    destruct (one_eq_app _ _ _ _ _ HeqG) as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
    SCase "exists E'', E'=E&X0'' /\ E0=E&X&E'' ".
      destruct (one_eq_app _ _ _ _ _ HeqDsubst) as [[dsubst'' [DEQ1 DEQ2]] | [DEQ1 DEQ2]]; subst.
      SSCase "exists DS'',DS'=DS&X0'' /\ DS0=DS&X&DS'' ".
        simpl. simpl_env. 
        rewrite <- subst_te_commute; auto.
           apply IHHwf_delta_subst with (E':=E'') (dsubst':=dsubst''); auto.
             apply ddom_dom__inv with (X:=X0)(b:= T); auto.
               apply dom_delta_subst in Hwf_delta_subst.
               apply dom__ddom in H.
               rewrite Hwf_delta_subst in H. simpl_env in *. auto.
          eauto using notin_fv_wf.
          eauto using notin_fv_wf.
      SSCase "DS'=nil /\ DS&X = DS0&X0 ".
        inversion DEQ2. subst.
        simpl_env in *. destruct_notin.
        auto.
    SCase "E'=nil /\ E&X = E0&X0 ".
      inversion EQ2; subst.
      destruct (one_eq_app _ _ _ _ _ HeqDsubst) as [[dsubst'' [DEQ1 DEQ2]] | [DEQ1 DEQ2]]; subst.
      SSCase "exists DS'',DS'=DS&X0'' /\ DS0=DS&X&DS'' ".
        simpl_env in Heq'.
        assert (X0 `notin` (singleton X0 `union` dom dsubst'') -> False) as J.
            intro. destruct_notin. apply NotInTac0; auto.
        rewrite <- Heq' in J.
        contradict J; auto.
     SSCase "DS'=nil /\ DS&X = DS0&X0 ".
        inversion DEQ2; subst; auto.
  Case "wf_delta_subst_skip".
    destruct (one_eq_app _ _ _ _ _ HeqG) as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      apply IHHwf_delta_subst with (E':=E'') (dsubst'0:=dsubst'); auto.

      simpl_env in HeqG.
      inversion HeqG.
Qed.

Definition P_Frel_typ_permute_renaming_one (n:nat) := 
  ((forall t v v' E1 E2 E3 rsubst1 rsubst2 rsubst3 dsubst1 dsubst2 dsubst3 dsubst1' dsubst2' dsubst3' X R t2 t2' Y,
  typ_size t = n ->
  (F_related_values t (rsubst1++rsubst2++[(X, R)]++rsubst3) (dsubst1++dsubst2++[(X, t2)]++dsubst3) (dsubst1'++dsubst2'++[(X, t2')]++dsubst3') v v' ->
  ddom_env E1 [=] dom rsubst1 ->
  ddom_env E1 [=] dom dsubst1 ->
  ddom_env E1 [=] dom dsubst1' ->
  ddom_env E2 [=] dom rsubst2 ->
  ddom_env E2 [=] dom dsubst2 ->
  ddom_env E2 [=] dom dsubst2' ->
  ddom_env E3 [=] dom rsubst3 ->
  ddom_env E3 [=] dom dsubst3 ->
  ddom_env E3 [=] dom dsubst3' ->
  wfr R t2 t2' ->
  wf_rho_subst (E1++E2++[(X, bind_kn)]++E3) (rsubst1++rsubst2++[(X, R)]++rsubst3) ->
  wf_delta_subst (E1++E2++[(X, bind_kn)]++E3) (dsubst1++dsubst2++[(X, t2)]++dsubst3) ->
  wf_delta_subst (E1++E2++[(X, bind_kn)]++E3) (dsubst1'++dsubst2'++[(X, t2')]++dsubst3') ->
  wf_delta_subst (E1++[(Y, bind_kn)]++E2++E3) (dsubst1++[(Y, t2)]++dsubst2++dsubst3) ->
  wf_delta_subst (E1++[(Y, bind_kn)]++E2++E3) (dsubst1'++[(Y, t2')]++dsubst2'++dsubst3') ->
  Y `notin` (dom E1 `union` dom E2 `union` dom E3 `union` (fv_tt t))->
  F_related_values (subst_tt X Y t) (rsubst1++[(Y, R)]++rsubst2++rsubst3) (dsubst1++[(Y, t2)]++dsubst2++dsubst3) (dsubst1'++[(Y, t2')]++dsubst2'++dsubst3') v v'))
  *
  (forall t v v' E1 E2 E3 (rsubst1 rsubst2 rsubst3:rho_subst) dsubst1 dsubst2 dsubst3 dsubst1' dsubst2' dsubst3' (X:atom) (R:rel) t2 t2' (Y:atom),
  typ_size t = n ->
  (F_related_values (subst_tt X Y t) (rsubst1++[(Y, R)]++rsubst2++rsubst3) (dsubst1++[(Y, t2)]++dsubst2++dsubst3) (dsubst1'++[(Y, t2')]++dsubst2'++dsubst3') v v' ->
  ddom_env E1 [=] dom rsubst1 ->
  ddom_env E1 [=] dom dsubst1 ->
  ddom_env E1 [=] dom dsubst1' ->
  ddom_env E2 [=] dom rsubst2 ->
  ddom_env E2 [=] dom dsubst2 ->
  ddom_env E2 [=] dom dsubst2' ->
  ddom_env E3 [=] dom rsubst3 ->
  ddom_env E3 [=] dom dsubst3 ->
  ddom_env E3 [=] dom dsubst3' ->
  wfr R t2 t2' ->
  wf_rho_subst (E1++E2++[(X, bind_kn)]++E3) (rsubst1++rsubst2++[(X, R)]++rsubst3) ->
  wf_delta_subst (E1++E2++[(X, bind_kn)]++E3) (dsubst1++dsubst2++[(X, t2)]++dsubst3) ->
  wf_delta_subst (E1++E2++[(X, bind_kn)]++E3) (dsubst1'++dsubst2'++[(X, t2')]++dsubst3') ->
  wf_delta_subst (E1++[(Y, bind_kn)]++E2++E3) (dsubst1++[(Y, t2)]++dsubst2++dsubst3) ->
  wf_delta_subst (E1++[(Y, bind_kn)]++E2++E3) (dsubst1'++[(Y, t2')]++dsubst2'++dsubst3') ->
  Y `notin` (dom E1 `union` dom E2 `union` dom E3 `union` (fv_tt t))->
  F_related_values t (rsubst1++rsubst2++[(X, R)]++rsubst3) (dsubst1++dsubst2++[(X, t2)]++dsubst3) (dsubst1'++dsubst2'++[(X, t2')]++dsubst3') v v'))) % type
  .

Lemma _Frel_typ_permute_renaming_one:  forall n, P_Frel_typ_permute_renaming_one n.
Proof.
  intro n.
  apply lt_wf_ind. clear n.
  intros n H.
  unfold P_Frel_typ_permute_renaming_one in *.
  split.
  (* -> *)
  intros t v v' E1 E2 E3 rsubst1 rsubst2 rsubst3 dsubst1 dsubst2 dsubst3 dsubst1' dsubst2' dsubst3' X R t2 t2' Y
     Htsize Hrel Heqr1 Heqd1 Heqd1' Heqr2 Heqd2 Heqd2' Heqr3 Heqd3 Heqd3' WfR Wfr Wfd Wfd' Wfd0 Wfd0' Hfv.
  (typ_cases (destruct t) Case).

  Case "typ_bvar". (*bvar*)
  apply F_related_values_bvar_leq in Hrel; auto.

  Case "typ_fvar". (* fvar *)
  apply F_related_values_fvar_leq in Hrel.
  unfold In_rel in Hrel.  
  destruct Hrel as [R0 [Hb [Hv [Hv' Hr]]]]; subst; simpl.
  simpl. simpl_env.
  destruct (a==X); subst.
    apply F_related_values_fvar_req.
    apply wf_rho_subst__uniq in Wfr.
    decompose [and] Wfr.
    analyze_binds_uniq Hb.
      exists (R).
      simpl_env.
      repeat(split; auto).

    apply F_related_values_fvar_req.
    apply wf_rho_subst__uniq in Wfr.
    decompose [and] Wfr.
    analyze_binds_uniq Hb.
      exists (R0).
      simpl_env.
      repeat(split; auto).

      exists (R0).
      simpl_env.
      repeat(split; auto).

      exists (R0).
      simpl_env.
      repeat(split; auto).

  Case "typ_arrow". (* arrow *)
  apply F_related_values_arrow_leq in Hrel.
  simpl. simpl_env.
  apply F_related_values_arrow_req.
  destruct Hrel as [Hv [Hv' Harrow]]; subst.
  repeat(split; simpl_env; auto).
     SCase "arrow".
     intros x x' Htypingx Htypingx' Harrow'.
     destruct Harrow' as [w [w' [Hnorm_xw [Hnorm_x'w' Hrel_wft1']]]].
     simpl_env in *.

     assert (typ_size t1 < typ_size (typ_arrow t1 t3)) as G1. simpl. omega.
     apply H in G1; auto.
     destruct G1 as [Hrel_wft1_wft1' Hrel_wft1'_wft1].
     simpl in Hfv.
     apply Hrel_wft1'_wft1 with (E1:=E1) (E2:=E2) (E3:=E3) in Hrel_wft1'; auto; simpl_env.
       SSCase "arrow".
       destruct (@Harrow x x') as [u [u' [Hnorm_vxu [Hnorm_v'x'u' Hrel_wft1]]]]; auto.
         assert (ddom_env (E2++E3) [=] dom (dsubst2++dsubst3)) as EQ1.
           simpl_env. rewrite Heqd2. rewrite Heqd3. 
           clear. fsetdec.
         assert (wf_typ nil t2) as Wft2.
           apply wfr_left_inv in WfR; auto.
         rewrite delta_subst_opt with (E:=E2++E3) (E':=E1) in Htypingx; auto.
         assert (ddom_env (E1++E2) [=] dom (dsubst1++dsubst2)) as EQ2.
           simpl_env. rewrite Heqd1. rewrite Heqd2. 
           clear. fsetdec.
         rewrite_env ((dsubst1++dsubst2)++[(X, t2)]++dsubst3).
         rewrite_env ((dsubst1++dsubst2)++[(X, t2)]++dsubst3) in Wfd.
         rewrite_env ((E1++E2)++[(X, bind_kn)]++E3) in Wfd.
         assert (X `notin` dom (E1++E2) `union` dom E3) as Xn.
           apply wf_rho_subst__uniq in Wfr.
           decompose [and] Wfr.
           solve_uniq.
         rewrite delta_subst_opt with (E:=E3) (E':=E1++E2); auto.

         simpl_env.
         rewrite subst_tt_tt in Htypingx; auto.

         assert (ddom_env (E2++E3) [=] dom (dsubst2'++dsubst3')) as EQ1.
           simpl_env. rewrite Heqd2'. rewrite Heqd3'. 
           clear. fsetdec.
         assert (wf_typ nil t2') as Wft2'.
           apply wfr_right_inv in WfR; auto.
         rewrite delta_subst_opt with (E:=E2++E3) (E':=E1) in Htypingx'; auto.
         assert (ddom_env (E1++E2) [=] dom (dsubst1'++dsubst2')) as EQ2.
           simpl_env. rewrite Heqd1'. rewrite Heqd2'. 
           clear. fsetdec.
         rewrite_env ((dsubst1'++dsubst2')++[(X, t2')]++dsubst3').
         rewrite_env ((dsubst1'++dsubst2')++[(X, t2')]++dsubst3') in Wfd'.
         rewrite_env ((E1++E2)++[(X, bind_kn)]++E3) in Wfd'.
         assert (X `notin` dom (E1++E2) `union` dom E3) as Xn.
           apply wf_rho_subst__uniq in Wfr.
           decompose [and] Wfr.
           solve_uniq.
         rewrite delta_subst_opt with (E:=E3) (E':=E1++E2); auto.
         simpl_env.
         rewrite subst_tt_tt  in Htypingx'; auto.

         exists w. exists w'. repeat(split; auto).

       exists (u). exists (u'). repeat(split; auto).
       assert (typ_size t3 < typ_size (typ_arrow t1 t3)) as G2. simpl. omega.
       apply H in G2. destruct G2 as [Hrel_wft2_wft2' Hrel_wft2'_wft2].
       simpl in Hfv.
       apply Hrel_wft2_wft2' with (E1:=E1) (E2:=E2) (E3:=E3); auto.

  Case "typ_all". (* all *)
  apply F_related_values_all_leq in Hrel.
  simpl. simpl_env.
  apply F_related_values_all_req.
  destruct Hrel as [Hv [Hv' [L' Hall]]]; subst.
  repeat(split; simpl_env; auto).
     SCase "all".
     exists (L' `union` singleton X `union` singleton Y `union` dom E1 `union` dom E2 `union` dom E3 `union` fv_tt t).
      intros X1 t3 t2'0 R0 Fr Hwfr' Hfv'.
      assert (X1 `notin` L') as Fr''. auto.
      destruct (@Hall X1 t3 t2'0 R0 Fr'') as [w0 [w'0 [Hnorm_vt2w0 [Hnorm_v't2'w'0 Hrel_wft]]]]; auto.
      exists (w0). exists (w'0). repeat(split; auto).
      assert (typ_size (open_tt t X1) < typ_size (typ_all t)) as G. 
        simpl. rewrite open_tt_typ_size_eq. omega.
      apply H in G. destruct G as [Hrel_wft_wft' Hrel_wft'_wft].
      simpl_env in Hrel_wft_wft'. clear H Hrel_wft'_wft.
      simpl_env.
      rewrite subst_tt_fresh with (T:=X1) (Z:=X) (U:=Y); auto.
      rewrite <- subst_tt_open_tt; auto.  
      apply Hrel_wft_wft' with (t0:=(open_tt t X1)) 
                               (E1:=[(X1, bind_kn)]++E1)(E2:=E2)(E3:=E3)
                               (rsubst1:=[(X1,R0)]++rsubst1)(rsubst2:=rsubst2)(rsubst3:=rsubst3)
                               (dsubst1:=[(X1,t3)]++dsubst1)(dsubst2:=dsubst2)(dsubst3:=dsubst3)
                               (dsubst1':=[(X1,t2'0)]++dsubst1')(dsubst2':=dsubst2')(dsubst3':=dsubst3')
                               (v:=w0) (v':=w'0)
                               (X:=X) (R:=R) 
                               (t2:=t2) (t2':=t2')
                               ; simpl_env; auto; clear Hrel_wft_wft'.
          eapply dsubst_weaken_head; simpl_env; eauto using wfr_left_inv.
          eapply dsubst_weaken_head; simpl_env; eauto using wfr_right_inv.
          eapply dsubst_weaken_head; simpl_env; eauto using wfr_left_inv.
          eapply dsubst_weaken_head; simpl_env; eauto using wfr_right_inv.
          SSCase "fv".
          destruct_notin.
          simpl in *. auto using notin_fv_tt_open_tt.

  Case "typ_bang". (* bang *)
  apply F_related_values_bang_leq in Hrel.
  simpl. simpl_env.
  apply F_related_values_bang_req.
  destruct Hrel as [Hv [Hv' [e1 [e1' [Heq [Heq' 
                                [u1 [u1' [Hnorm_e1u1 [Hnorm_e1'u1' Hrel_wft1]]]
                              ]]]]]]]; subst.
  repeat(split; auto; simpl_env in * ).
     simpl in Hfv.
     exists (e1). exists (e1'). repeat(split; auto).
       exists (u1). exists (u1').  repeat(split;auto).
       simpl_env in *.
       assert (typ_size t < typ_size (typ_bang t)) as G1. simpl. omega.
       apply H in G1. destruct G1 as [Hrel_wft1_wft1' Hrel_wft1'_wft1].
       simpl in Hfv.
       apply Hrel_wft1_wft1' with (E1:=E1) (E2:=E2) (E3:=E3); auto.

  Case "typ_with". (* with *)
  apply F_related_values_with_leq in Hrel.
  simpl. simpl_env.
  apply F_related_values_with_req.
  destruct Hrel as [Hv [Hv' [e1 [e2 [e1' [e2' [Heq [Heq' 
                                [[u1 [u1' [Hnorm_e1u1 [Hnorm_e1'u1' Hrel_wft1]]]] 
                                 [u2 [u2' [Hnorm_e2u2 [Hnorm_e2'u2' Hrel_wft2]]]]]
                              ]]]]]]]]; subst.
  repeat(split; auto; simpl_env in * ).
     SCase "with".
     simpl in Hfv.
     exists (e1). exists (e2). exists (e1'). exists (e2'). repeat(split; auto).
       SSCase "with1".
       exists (u1). exists (u1').  repeat(split;auto).
       simpl_env in *.
       assert (typ_size t1 < typ_size (typ_with t1 t3)) as G1. simpl. omega.
       apply H in G1. destruct G1 as [Hrel_wft1_wft1' Hrel_wft1'_wft1].
       simpl in Hfv.
       apply Hrel_wft1_wft1' with (E1:=E1) (E2:=E2) (E3:=E3); auto.
       SSCase "with2".
       exists (u2). exists (u2').  repeat(split; auto).
       assert (typ_size t3 < typ_size (typ_with t1 t3)) as G2. simpl. omega.
       apply H in G2. destruct G2 as [Hrel_wft2_wft2' Hrel_wft2'_wft2].
      simpl in Hfv.
      apply Hrel_wft2_wft2' with (E1:=E1) (E2:=E2) (E3:=E3) ; auto.

  (* <- *)
  intros t v v' E1 E2 E3 rsubst1 rsubst2 rsubst3 dsubst1 dsubst2 dsubst3 dsubst1' dsubst2' dsubst3' X R t2 t2' Y
     Htsize Hrel Heqr1 Heqd1 Heqd1' Heqr2 Heqd2 Heqd2' Heqr3 Heqd3 Heqd3' WfR Wfr Wfd Wfd' Wfd0 Wfd0' Hfv.
  (typ_cases (destruct t) Case).

  Case "typ_bvar". (*bvar*)
  apply F_related_values_bvar_leq in Hrel; auto.

  Case "typ_fvar". (* fvar *)
  apply F_related_values_fvar_req.
  simpl in Hrel. simpl_env in Hrel.
  destruct (a==X); subst.
    apply F_related_values_fvar_leq in Hrel.
    unfold In_rel in Hrel.  
    destruct Hrel as [R0 [Hb [Hv [Hv' Hr]]]]; subst.
    exists R.
    repeat(split; auto).
    apply wf_rho_subst__uniq in Wfr.
    decompose [and] Wfr.
    destruct_notin.
    apply dom__ddom in Hfv.
    rewrite Heqr1 in Hfv.
    apply dom__ddom in NotInTac.
    rewrite Heqr2 in NotInTac.
    apply dom__ddom in NotInTac0.
    rewrite Heqr3 in NotInTac0.
    analyze_binds_uniq Hb.

    apply F_related_values_fvar_leq in Hrel.
    unfold In_rel in Hrel.  
    destruct Hrel as [R0 [Hb [Hv [Hv' Hr]]]]; subst.
    apply wf_rho_subst__uniq in Wfr.
    decompose [and] Wfr.
    destruct_notin.
    apply dom__ddom in Hfv.
    rewrite Heqr1 in Hfv.
    apply dom__ddom in NotInTac.
    rewrite Heqr2 in NotInTac.
    apply dom__ddom in NotInTac0.
    rewrite Heqr3 in NotInTac0.
    analyze_binds_uniq Hb.
      exists R0.
      repeat(split; auto).

      simpl. auto.

      exists (R0).
      repeat(split; auto).

      exists (R0).
      repeat(split; auto).

  Case "typ_arrow". (* arrow *)
  simpl in Hrel. simpl_env in Hrel.
  apply F_related_values_arrow_leq in Hrel.
  apply F_related_values_arrow_req.
  destruct Hrel as [Hv [Hv' Harrow]]; subst.
  repeat(split; simpl_env in *; auto).
     SCase "arrow".
     intros x x' Htypingx Htypingx' Harrow'.
     destruct Harrow' as [w [w' [Hnorm_xw [Hnorm_x'w' Hrel_wft1]]]].
 
     assert (typ_size t1 < typ_size (typ_arrow t1 t3)) as G1. simpl. omega.
     apply H in G1. destruct G1 as [Hrel_wft1_wft1' Hrel_wft1'_wft1].
     simpl in Hfv.
     apply Hrel_wft1_wft1' with (X:=X)(Y:=Y)(R:=R)(t2:=t2)(t2':=t2')(E1:=E1)(E2:=E2)(E3:=E3) in Hrel_wft1; auto; simpl_env.
       SSCase "arrow".
       destruct (@Harrow x x') as [u [u' [Hnorm_vxu [Hnorm_v'x'u' Hrel_wft1']]]]; auto.
         assert (ddom_env (E2++E3) [=] dom (dsubst2++dsubst3)) as EQ1.
           simpl_env. rewrite Heqd2. rewrite Heqd3. 
           clear. fsetdec.
         assert (wf_typ nil t2) as Wft2.
           apply wfr_left_inv in WfR; auto.
         rewrite delta_subst_opt with (E:=E2++E3) (E':=E1); auto.
         assert (ddom_env (E1++E2) [=] dom (dsubst1++dsubst2)) as EQ2.
           simpl_env. rewrite Heqd1. rewrite Heqd2. 
           clear. fsetdec.
         rewrite_env ((dsubst1++dsubst2)++[(X, t2)]++dsubst3) in Htypingx.
         rewrite_env ((dsubst1++dsubst2)++[(X, t2)]++dsubst3) in Wfd.
         rewrite_env ((E1++E2)++[(X, bind_kn)]++E3) in Wfd.
         assert (X `notin` dom (E1++E2) `union` dom E3) as Xn.
           apply wf_rho_subst__uniq in Wfr.
           decompose [and] Wfr.
           solve_uniq.
         rewrite delta_subst_opt with (E:=E3) (E':=E1++E2) in Htypingx; auto.
         simpl_env  in Htypingx.
         rewrite subst_tt_tt; auto.

         assert (ddom_env (E2++E3) [=] dom (dsubst2'++dsubst3')) as EQ1.
           simpl_env. rewrite Heqd2'. rewrite Heqd3'. 
           clear. fsetdec.
         assert (wf_typ nil t2') as Wft2'.
           apply wfr_right_inv in WfR; auto.
         rewrite delta_subst_opt with (E:=E2++E3) (E':=E1); auto.
         assert (ddom_env (E1++E2) [=] dom (dsubst1'++dsubst2')) as EQ2.
           simpl_env. rewrite Heqd1'. rewrite Heqd2'. 
           clear. fsetdec.
         rewrite_env ((dsubst1'++dsubst2')++[(X, t2')]++dsubst3') in Htypingx'.
         rewrite_env ((dsubst1'++dsubst2')++[(X, t2')]++dsubst3') in Wfd'.
         rewrite_env ((E1++E2)++[(X, bind_kn)]++E3) in Wfd'.
         assert (X `notin` dom (E1++E2) `union` dom E3) as Xn.
           apply wf_rho_subst__uniq in Wfr.
           decompose [and] Wfr.
           solve_uniq.
         rewrite delta_subst_opt with (E:=E3) (E':=E1++E2) in Htypingx'; auto.
         simpl_env  in Htypingx'.
         rewrite subst_tt_tt; auto.

         exists (w). exists (w'). repeat(split; auto).

       exists (u). exists (u'). repeat(split; auto).
       assert (typ_size t3 < typ_size (typ_arrow t1 t3)) as G2. simpl. omega.
       apply H in G2. destruct G2 as [Hrel_wft2_wft2' Hrel_wft2'_wft2].
       simpl in Hfv.
       apply Hrel_wft2'_wft2 with (X:=X)(Y:=Y)(R:=R)(t2:=t2)(t2':=t2')(E1:=E1)(E2:=E2)(E3:=E3); auto.

  Case "typ_all". (* all *)
  simpl in Hrel. simpl_env in Hrel.
  apply F_related_values_all_leq in Hrel.
  apply F_related_values_all_req.
  destruct Hrel as [Hv [Hv' [L' Hall]]]; subst.
  repeat(split; auto; simpl_env in *).
     SCase "all".
      exists (L' `union` singleton X `union` singleton Y `union` dom E1 `union` dom E2 `union` dom E3 `union` fv_tt (subst_tt X Y t)).
      intros X1 t3 t2'0 R0 Fr Hwfr' Hfv'.
      assert (X1 `notin` L') as Fr''. auto.
      destruct (@Hall X1 t3 t2'0 R0 Fr'') as [w0 [w'0 [Hnorm_vt2w0 [Hnorm_v't2'w'0 Hrel_wft]]]]; auto.
          destruct_notin. simpl_env. simpl. auto.
      exists (w0). exists (w'0). repeat(split; auto).
      assert (typ_size (open_tt t X1) < typ_size (typ_all t)) as G. 
        simpl. rewrite open_tt_typ_size_eq. omega.
      apply H in G. destruct G as [Hrel_wft_wft' Hrel_wft'_wft].
      simpl_env in Hrel_wft'_wft. clear H Hrel_wft_wft'.
      simpl_env. simpl_env in Hrel_wft.
      rewrite subst_tt_fresh with (T:=X1) (Z:=X) (U:=Y) in Hrel_wft; auto.
      rewrite <- subst_tt_open_tt in Hrel_wft; auto.  
      apply Hrel_wft'_wft with (t0:=(open_tt t X1)) 
                               (E1:=[(X1, bind_kn)]++E1)(E2:=E2)(E3:=E3)
                               (rsubst1:=[(X1,R0)]++rsubst1)(rsubst2:=rsubst2)(rsubst3:=rsubst3)
                               (dsubst1:=[(X1,t3)]++dsubst1)(dsubst2:=dsubst2)(dsubst3:=dsubst3)
                               (dsubst1':=[(X1,t2'0)]++dsubst1')(dsubst2':=dsubst2')(dsubst3':=dsubst3')
                               (v:=w0) (v':=w'0)
                               (X:=X) (R:=R) (Y:=Y)
                               (t2:=t2) (t2':=t2')
                               ; simpl_env; auto; clear Hrel_wft'_wft.
          eapply dsubst_weaken_head; simpl_env; eauto using wfr_left_inv.
          eapply dsubst_weaken_head; simpl_env; eauto using wfr_right_inv.
          eapply dsubst_weaken_head; simpl_env; eauto using wfr_left_inv.
          eapply dsubst_weaken_head; simpl_env; eauto using wfr_right_inv.
          SSCase "fv".
          destruct_notin. simpl in NotInTac5. simpl.
          auto using notin_fv_tt_open_tt.

  Case "typ_bang". (* bang *)
  simpl in Hrel. simpl_env in Hrel.
  apply F_related_values_bang_leq in Hrel.
  apply F_related_values_bang_req.
  destruct Hrel as [Hv [Hv' [e1 [e1' [Heq [Heq' 
                                [u1 [u1' [Hnorm_e1u1 [Hnorm_e1'u1' Hrel_wft1]]]
                              ]]]]]]]; subst.
  repeat(split; auto; simpl_env in *).
     simpl in Hfv.
     exists (e1). exists (e1').  repeat(split; auto).
       exists (u1). exists (u1'). repeat(split; auto).
       simpl_env in *.
       assert (typ_size t < typ_size (typ_bang t)) as G1. simpl. omega.
       apply H in G1. destruct G1 as [Hrel_wft1_wft1' Hrel_wft1'_wft1].
       simpl in Hfv.
       eapply Hrel_wft1'_wft1; eauto.

  Case "typ_with". (* with *)
  simpl in Hrel. simpl_env in Hrel.
  apply F_related_values_with_leq in Hrel.
  apply F_related_values_with_req.
  destruct Hrel as [Hv [Hv' [e1 [e2 [e1' [e2' [Heq [Heq' 
                                [[u1 [u1' [Hnorm_e1u1 [Hnorm_e1'u1' Hrel_wft1]]]] 
                                 [u2 [u2' [Hnorm_e2u2 [Hnorm_e2'u2' Hrel_wft2]]]]]
                              ]]]]]]]]; subst.
  repeat(split; auto; simpl_env in *).
     SCase "with".
     simpl in Hfv.
     exists (e1). exists (e2). exists (e1'). exists (e2'). repeat(split; auto).
       SSCase "with1".
       exists (u1). exists (u1'). repeat(split; auto).
       simpl_env in *.
       assert (typ_size t1 < typ_size (typ_with t1 t3)) as G1. simpl. omega.
       apply H in G1. destruct G1 as [Hrel_wft1_wft1' Hrel_wft1'_wft1].
       simpl in Hfv.
       eapply Hrel_wft1'_wft1; eauto.
       SSCase "with2".
       exists (u2). exists (u2'). repeat(split; auto).
       assert (typ_size t3 < typ_size (typ_with t1 t3)) as G2. simpl. omega.
       apply H in G2. destruct G2 as [Hrel_wft2_wft2' Hrel_wft2'_wft2].
       simpl in Hfv.
       eapply Hrel_wft2'_wft2; eauto.
Qed.

Lemma Frel_typ_permute_renaming_one': forall t v v' E1 E2 E3 rsubst1 rsubst2 rsubst3 dsubst1 dsubst2 dsubst3 dsubst1' dsubst2' dsubst3' X R t2 t2' Y,
  F_related_values t (rsubst1++rsubst2++[(X, R)]++rsubst3) (dsubst1++dsubst2++[(X, t2)]++dsubst3) (dsubst1'++dsubst2'++[(X, t2')]++dsubst3') v v' ->
  ddom_env E1 [=] dom rsubst1 ->
  ddom_env E1 [=] dom dsubst1 ->
  ddom_env E1 [=] dom dsubst1' ->
  ddom_env E2 [=] dom rsubst2 ->
  ddom_env E2 [=] dom dsubst2 ->
  ddom_env E2 [=] dom dsubst2' ->
  ddom_env E3 [=] dom rsubst3 ->
  ddom_env E3 [=] dom dsubst3 ->
  ddom_env E3 [=] dom dsubst3' ->
  wfr R t2 t2' ->
  wf_rho_subst (E1++E2++[(X, bind_kn)]++E3) (rsubst1++rsubst2++[(X, R)]++rsubst3) ->
  wf_delta_subst (E1++E2++[(X, bind_kn)]++E3) (dsubst1++dsubst2++[(X, t2)]++dsubst3) ->
  wf_delta_subst (E1++E2++[(X, bind_kn)]++E3) (dsubst1'++dsubst2'++[(X, t2')]++dsubst3') ->
  wf_delta_subst (E1++[(Y, bind_kn)]++E2++E3) (dsubst1++[(Y, t2)]++dsubst2++dsubst3) ->
  wf_delta_subst (E1++[(Y, bind_kn)]++E2++E3) (dsubst1'++[(Y, t2')]++dsubst2'++dsubst3') ->
  Y `notin` (dom E1 `union` dom E2 `union` dom E3 `union` (fv_tt t))->
  F_related_values (subst_tt X Y t) (rsubst1++[(Y, R)]++rsubst2++rsubst3) (dsubst1++[(Y, t2)]++dsubst2++dsubst3) (dsubst1'++[(Y, t2')]++dsubst2'++dsubst3') v v'
  .
Proof.
  intros.
  assert (P_Frel_typ_permute_renaming_one (typ_size t)) as J.
    apply (@_Frel_typ_permute_renaming_one (typ_size t)).
  unfold P_Frel_typ_permute_renaming_one in J.
  destruct J. eauto.
Qed.

Lemma Frel_typ_permute_renaming_one: forall t v v' E1 E2 rsubst1 rsubst2 dsubst1 dsubst2 dsubst1' dsubst2' X R t2 t2' Y,
  F_related_values t (rsubst1++[(X, R)]++rsubst2) (dsubst1++[(X, t2)]++dsubst2) (dsubst1'++[(X, t2')]++dsubst2') v v' ->
  ddom_env E1 [=] dom rsubst1 ->
  ddom_env E1 [=] dom dsubst1 ->
  ddom_env E1 [=] dom dsubst1' ->
  ddom_env E2 [=] dom rsubst2 ->
  ddom_env E2 [=] dom dsubst2 ->
  ddom_env E2 [=] dom dsubst2' ->
  wfr R t2 t2' ->
  wf_rho_subst (E1++[(X, bind_kn)]++E2) (rsubst1++[(X, R)]++rsubst2) ->
  wf_delta_subst (E1++[(X, bind_kn)]++E2) (dsubst1++[(X, t2)]++dsubst2) ->
  wf_delta_subst (E1++[(X, bind_kn)]++E2) (dsubst1'++[(X, t2')]++dsubst2') ->
  wf_delta_subst ([(Y, bind_kn)]++E1++E2) ([(Y, t2)]++dsubst1++dsubst2) ->
  wf_delta_subst ([(Y, bind_kn)]++E1++E2) ([(Y, t2')]++dsubst1'++dsubst2') ->
  Y `notin` (dom E1 `union` dom E2 `union` (fv_tt t))->
  F_related_values (subst_tt X Y t) ([(Y, R)]++rsubst1++rsubst2) ([(Y, t2)]++dsubst1++dsubst2) ([(Y, t2')]++dsubst1'++dsubst2') v v'
  .
Proof.
  intros.
  rewrite_env (nil++[(Y, R)]++rsubst1++rsubst2).
  rewrite_env (nil++[(Y, t2)]++dsubst1++dsubst2).
  rewrite_env (nil++[(Y, t2')]++dsubst1'++dsubst2').
  apply Frel_typ_permute_renaming_one' with (E1:=nil) (E2:=E1) (E3:=E2); auto.
Qed.

Lemma F_related_subst_lgweaken : forall D1 E D2 gsubst gsubst' lgsubst1 lgsubst2 lgsubst1' lgsubst2' rsubst dsubst dsubst' x T e e',
  F_related_subst E (D1++D2) gsubst gsubst' (lgsubst1++lgsubst2) (lgsubst1'++lgsubst2') rsubst dsubst dsubst' ->
  dom D1 [=] dom lgsubst1 ->
  dom D1 [=] dom lgsubst1' ->
  dom D2 [=] dom lgsubst2 ->
  dom D2 [=] dom lgsubst2' ->
  x `notin` (dom D1 `union` dom D2 `union` dom E)->
  wf_typ E T ->
  typing nil nil e (apply_delta_subst_typ dsubst T) ->
  typing nil nil e' (apply_delta_subst_typ dsubst' T) ->
  F_related_terms T rsubst dsubst dsubst' e e' ->
  F_related_subst E (D1++[(x, lbind_typ T)]++D2) gsubst gsubst' (lgsubst1++[(x, e)]++lgsubst2) (lgsubst1'++[(x, e')]++lgsubst2') rsubst dsubst dsubst'.
Proof.
  induction D1; intros E D2 gsubst gsubst' lgsubst1 lgsubst2 lgsubst1' lgsubst2' rsubst dsubst dsubst' x T e e'
                Hrel_subst Hdomlg1 Hdomlg1' Hdomlg2 Hdomlg2' Hx Hwft Htyp Htyp' Hrel.
    simpl in Hdomlg1. symmetry in Hdomlg1.  apply dom_empty_inv in Hdomlg1.
    simpl in Hdomlg1'. symmetry in Hdomlg1'.  apply dom_empty_inv in Hdomlg1'.
    subst.
    simpl_env.
    apply F_related_subst_ltyp; auto.
      apply F_related_subst__inversion in Hrel_subst.
      decompose [prod] Hrel_subst.
      assert (x `notin` fv_env E) as xnE.
        apply wfe_dom_fv_env; auto.
      assert (x `notin` fv_lenv D2) as xnlE.
        apply notin_fv_lenv_wfle with (E:=E); auto.
          apply wf_lgamma_subst__wf_lenv in b1.
          destruct b1; auto.
      assert (x `notin` fv_tt T) as xnT.
        apply notin_fv_wf with (X:=x) in Hwft; auto.
      auto.
    
    destruct a.
    destruct l.
    assert (J:=Hrel_subst). simpl_env in J.
    apply F_related_subst_lcons_inv in J.
    destruct J as [v [lgsubst [v' [lgsubts' [EQ1 [EQ2 [EQ3 [EQ4 [Wft [Typ [Typ' [Hrel' Hrel_subst']]]]]]]]]]]]; subst.
    symmetry in EQ1.
    symmetry in EQ2.
    apply one_eq_app in EQ1. destruct EQ1 as [[lgsubst0 [lgEQ1 lgEQ2]] | [lgEQ1 lgEQ2]]; subst.
      apply one_eq_app in EQ2. destruct EQ2 as [[lgsubst0' [lgEQ1' lgEQ2']] | [lgEQ1' lgEQ2']]; subst.
        simpl_env.
        simpl_env in Hrel_subst.
        apply F_related_subst__inversion in Hrel_subst.
        decompose [prod] Hrel_subst.
        apply F_related_subst_ltyp; auto.
          apply IHD1; auto.
            apply wf_lgamma_subst__uniq in b2.
            decompose [and] b2.
            apply dom_dom__inv with (x:=a)(b:=lbind_typ t)(b':=v); auto.
              inversion H3; subst.
              simpl_env in H7. auto.

              inversion H1; subst.
              simpl_env in H7. auto.

            apply wf_lgamma_subst__uniq in b1.
            decompose [and] b1.
            apply dom_dom__inv with (x:=a)(b:=lbind_typ t)(b':=v'); auto.
              inversion H3; subst.
              simpl_env in H7. auto.

              inversion H1; subst.
              simpl_env in H7. auto.

            assert (a `notin` fv_env E) as anE.
              apply wfe_dom_fv_env; auto.
                apply wf_lgamma_subst__wf_lenv in b1.
                decompose [and] b1.
                inversion H0; subst; auto.
            assert (a `notin` fv_lenv (D1++D2)) as anD.
              apply notin_fv_lenv_wfle with (E:=E); auto.
                apply wf_lgamma_subst__wf_lenv in b1.
                decompose [and] b1.
                inversion H0; subst; auto.

                apply wf_lgamma_subst__uniq in b2.
                decompose [and] b2.
                inversion H3; subst.
                simpl_env in H7. auto.
           simpl_env. simpl.
           apply notin_fv_wf with (X:=a) in Hwft; auto.
           apply notin_fv_wf with (X:=a) in Wft; auto.
           simpl_env in anD. auto.

        simpl_env in Hdomlg1'.
        assert (a `notin` (singleton a `union` dom D1) -> False) as J.
          intro. destruct_notin. contradict NotInTac0; auto.
        rewrite Hdomlg1' in J.
        contradict J; auto.

      simpl_env in Hdomlg1.
      assert (a `notin` (singleton a `union` dom D1) -> False) as J.
        intro. destruct_notin. contradict NotInTac0; auto.
      rewrite Hdomlg1 in J.
      contradict J; auto.
Qed.

Lemma F_related_subst_dweaken : forall E1 E2 D gsubst gsubst' lgsubst lgsubst' rsubst1 rsubst2 dsubst1 dsubst2 dsubst1' dsubst2' X t t' R,
  F_related_subst (E1++E2) D gsubst gsubst' lgsubst lgsubst' (rsubst1++rsubst2) (dsubst1++dsubst2) (dsubst1'++dsubst2') ->
  ddom_env E1 [=] dom dsubst1 ->
  ddom_env E1 [=] dom dsubst1' ->
  ddom_env E1 [=] dom rsubst1 ->
  ddom_env E2 [=] dom dsubst2 ->
  ddom_env E2 [=] dom dsubst2' ->
  ddom_env E2 [=] dom rsubst2 ->
  X `notin` (dom E1 `union` dom E2 `union` dom D)->
  wfr R t t' ->
  F_related_subst (E1++[(X, bind_kn)]++E2) D gsubst gsubst' lgsubst lgsubst' (rsubst1++[(X, R)]++rsubst2) (dsubst1++[(X, t)]++dsubst2) (dsubst1'++[(X, t')]++dsubst2').
Proof.
  intros E1 E2 D gsubst gsubst' lgsubst lgsubst' rsubst1 rsubst2 dsubst1 dsubst2 dsubst1' dsubst2' X t t' R
                Hrel_subst Hdomd1 Hdomd1' Hdomr1 Hdomd2 Hdomd2' Hdomr2 HX Hwfr.
  remember (E1++E2) as E.
  remember (rsubst1++rsubst2) as rsubst.
  remember (dsubst1++dsubst2) as dsubst.
  remember (dsubst1'++dsubst2') as dsubst'.
  generalize dependent E1.
  generalize dependent dsubst1.
  generalize dependent dsubst1'.
  generalize dependent rsubst1.  
  (F_related_subst_cases (induction Hrel_subst) Case); intros; subst.
  Case "F_related_subst_empty".
    symmetry in Heqdsubst.
    apply app_eq_nil in Heqdsubst.
    destruct Heqdsubst; subst.

    symmetry in Heqdsubst'.
    apply app_eq_nil in Heqdsubst'.
    destruct Heqdsubst'; subst.

    symmetry in Heqrsubst.
    apply app_eq_nil in Heqrsubst.
    destruct Heqrsubst; subst.

    symmetry in HeqE.
    apply app_eq_nil in HeqE.
    destruct HeqE; subst.
    rewrite_env ([(X, R)]++nil).
    rewrite_env ([(X, t)]++nil).
    rewrite_env ([(X, t')]++nil).
    apply F_related_subst_kind; auto.

  Case "F_related_subst_kind".
    simpl_env in *.
    apply one_eq_app in Heqrsubst. destruct Heqrsubst as [[rsubst0 [rEQ1 rEQ2]] | [rEQ1 rEQ2]]; subst.
      apply one_eq_app in Heqdsubst. destruct Heqdsubst as [[dsubst0 [dEQ1 dEQ2]] | [dEQ1 dEQ2]]; subst.
        apply one_eq_app in Heqdsubst'. destruct Heqdsubst' as [[dsubst0' [dEQ1' dEQ2']] | [dEQ1' dEQ2']]; subst.
          apply one_eq_app in HeqE. destruct HeqE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
            simpl_env.
            apply F_related_subst_kind; auto.
              apply IHHrel_subst with (rsubst1:=rsubst0) (dsubst1:=dsubst0) (dsubst1':=dsubst0'); auto.
                apply ddom_dom__inv with (X:=X0)(b:=t0); auto.
                  simpl_env in H. destruct_notin.
                  apply free_env__free_ddom in H; auto.
                   
                  destruct_notin.
                  apply free_env__free_ddom in H.
                  apply dom_F_related_subst in Hrel_subst.
                  destruct Hrel_subst as [J1 [J2 [J3 [J4 [J5 [J6 J7]]]]]].
                  rewrite J1 in H.
                  simpl_env in H. auto.
                apply ddom_dom__inv with (X:=X0)(b:=t'0); auto.
                  simpl_env in H. destruct_notin.
                  apply free_env__free_ddom in H; auto.
                   
                  destruct_notin.
                  apply free_env__free_ddom in H.
                  apply dom_F_related_subst in Hrel_subst.
                  destruct Hrel_subst as [J1 [J2 [J3 [J4 [J5 [J6 J7]]]]]].
                  rewrite J2 in H.
                  simpl_env in H. auto.
                apply ddom_dom__inv with (X:=X0)(b:=R0); auto.
                  simpl_env in H. destruct_notin.
                  apply free_env__free_ddom in H; auto.
                   
                  destruct_notin.
                  apply free_env__free_ddom in H.
                  apply dom_F_related_subst in Hrel_subst.
                  destruct Hrel_subst as [J1 [J2 [J3 [J4 [J5 [J6 J7]]]]]].
                  rewrite J3 in H.
                  simpl_env in H. auto.
                simpl_env. simpl. simpl_env in HX. simpl in HX.
                simpl_env in H. auto. 

            simpl_env in Hdomd1.
            assert (X0 `notin` (singleton X0 `union` dom dsubst0) -> False) as J.
              intro. destruct_notin. contradict NotInTac0; auto.
            rewrite <- Hdomd1 in J.
            contradict J; auto.

          simpl_env in Hdomd1'.
          simpl_env in Hdomd1.
          assert (X0 `notin` (singleton X0 `union` dom dsubst0) -> False) as J.
            intro. destruct_notin. contradict NotInTac0; auto.
          rewrite <- Hdomd1 in J.
          rewrite Hdomd1' in J.
          contradict J; auto.
        simpl_env in Hdomd1.
        simpl_env in Hdomr1.
        assert (X0 `notin` (singleton X0 `union` dom rsubst0) -> False) as J.
          intro. destruct_notin. contradict NotInTac0; auto.
        rewrite <- Hdomr1 in J.
        rewrite Hdomd1 in J.
        contradict J; auto.
      apply one_eq_app in HeqE. destruct HeqE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
        simpl in Hdomr1.
        assert (X0 `notin` (singleton X0 `union` ddom_env E0') -> False) as J.
          intro. destruct_notin. contradict NotInTac0; auto.
        rewrite Hdomr1 in J.
        contradict J; auto.

        simpl in Hdomd1. symmetry in Hdomd1.  apply dom_empty_inv in Hdomd1.
        simpl in Hdomd1'. symmetry in Hdomd1'.  apply dom_empty_inv in Hdomd1'.
        subst. 
        simpl_env in Heqdsubst. simpl_env in Heqdsubst'.
        subst. simpl_env.
        apply F_related_subst_kind; auto.
          apply F_related_subst_kind; auto. 

          assert (X `notin` fv_env E) as XnE.
            apply wfe_dom_fv_env; auto.
              apply F_related_subst__inversion in Hrel_subst.
              decompose [prod] Hrel_subst; auto. 
          assert (X `notin` fv_lenv lE) as XnlE.
            apply notin_fv_lenv_wfle with (E:=E); auto.
              apply F_related_subst__inversion in Hrel_subst.
              decompose [prod] Hrel_subst.
              apply wf_lgamma_subst__wf_lenv in b1.
              destruct b1; auto.
          simpl_env. simpl in HX. simpl. auto.
          
  Case "F_related_subst_typ".
    simpl_env in *.
    apply one_eq_app in HeqE. destruct HeqE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
      simpl in Hdomd1. simpl in Hdomd1'. simpl in Hdomr1.
      simpl_env.
      apply F_related_subst_typ; auto.
        erewrite delta_subst_opt with (E:=E2) (E':=E0'); eauto.
          rewrite <- subst_tt_fresh; auto.
            apply notin_fv_wf with (X:=X) in H3; auto.
         
          apply F_related_subst__inversion in Hrel_subst.
          decompose [prod] Hrel_subst.
          apply dsubst_weaken; auto.
            apply wfr_left_inv in Hwfr; auto.

          apply wfr_left_inv in Hwfr; auto.

        erewrite delta_subst_opt with (E:=E2) (E':=E0'); eauto.
          rewrite <- subst_tt_fresh; auto.
            apply notin_fv_wf with (X:=X) in H3; auto.
         
          apply F_related_subst__inversion in Hrel_subst.
          decompose [prod] Hrel_subst.
          apply dsubst_weaken; auto.
            apply wfr_right_inv in Hwfr; auto.

          apply wfr_right_inv in Hwfr; auto.

        destruct H1 as [v [v' [Htv [Htv' [Henv [He'nv' H1]]]]]].
        exists v. exists v'.
        split.
         erewrite delta_subst_opt with (E:=E2) (E':=E0'); eauto.
          rewrite <- subst_tt_fresh; auto.
            apply notin_fv_wf with (X:=X) in H3; auto.
         
          apply F_related_subst__inversion in Hrel_subst.
          decompose [prod] Hrel_subst.
          apply dsubst_weaken; auto.
            apply wfr_left_inv in Hwfr; auto.

          apply wfr_left_inv in Hwfr; auto.
        split.
         erewrite delta_subst_opt with (E:=E2) (E':=E0'); eauto.
          rewrite <- subst_tt_fresh; auto.
            apply notin_fv_wf with (X:=X) in H3; auto.
         
          apply F_related_subst__inversion in Hrel_subst.
          decompose [prod] Hrel_subst.
          apply dsubst_weaken; auto.
            apply wfr_right_inv in Hwfr; auto.

          apply wfr_right_inv in Hwfr; auto.
        split; auto.
        split; auto.
         apply F_related_subst__inversion in Hrel_subst.
         decompose [prod] Hrel_subst.
         apply Frel_weaken with (E:=E2) (E':=E0'); auto.
          assert (X `notin` fv_env (E0'++E2)) as XnE.
            apply wfe_dom_fv_env; auto.
          assert (X `notin` fv_tt t0) as Xnt0.
            apply notin_fv_wf with (X:=X) in H3; auto.
          simpl_env in XnE. auto.

        assert (x `notin` fv_tt t0) as xnt0.
          apply notin_fv_wf with (X:=x) in H3; auto.
        simpl_env. simpl. simpl in HX. simpl_env in H2. simpl in H2. auto.

        apply wf_typ_weakening; auto.
          apply F_related_subst__inversion in Hrel_subst.
          decompose [prod] Hrel_subst.
          simpl in HX. 
          apply uniq_insert_mid; auto.

      simpl in Hdomd1. symmetry in Hdomd1.  apply dom_empty_inv in Hdomd1.
      simpl in Hdomd1'. symmetry in Hdomd1'.  apply dom_empty_inv in Hdomd1'.
      simpl in Hdomr1. symmetry in Hdomr1.  apply dom_empty_inv in Hdomr1.
      subst. simpl_env. 
      apply F_related_subst_kind; auto.
        apply F_related_subst_typ; auto.

        assert (X `notin` fv_env E) as XnE.
          apply wfe_dom_fv_env; auto.
            apply F_related_subst__inversion in Hrel_subst.
            decompose [prod] Hrel_subst; auto. 
        assert (X `notin` fv_lenv lE) as XnlE.
          apply notin_fv_lenv_wfle with (E:=E); auto.
            apply F_related_subst__inversion in Hrel_subst.
            decompose [prod] Hrel_subst.
            apply wf_lgamma_subst__wf_lenv in b1.
            destruct b1; auto.
        assert (X `notin` fv_tt t0) as Xnt0.
          apply notin_fv_wf with (X:=X) in H3; auto.
        simpl_env. simpl. simpl in HX. auto.
          
  Case "F_related_subst_ltyp".
    simpl_env in *.
    apply F_related_subst_ltyp; auto.
      erewrite delta_subst_opt with (E:=E2) (E':=E1); eauto.
        rewrite <- subst_tt_fresh; auto.
          apply notin_fv_wf with (X:=X) in H3; auto.
         
        apply F_related_subst__inversion in Hrel_subst.
        decompose [prod] Hrel_subst.
        apply dsubst_weaken; auto.
          apply wfr_left_inv in Hwfr; auto.

        apply wfr_left_inv in Hwfr; auto.

      erewrite delta_subst_opt with (E:=E2) (E':=E1); eauto.
        rewrite <- subst_tt_fresh; auto.
          apply notin_fv_wf with (X:=X) in H3; auto.
         
        apply F_related_subst__inversion in Hrel_subst.
        decompose [prod] Hrel_subst.
        apply dsubst_weaken; auto.
          apply wfr_right_inv in Hwfr; auto.

        apply wfr_right_inv in Hwfr; auto.

        destruct H1 as [v [v' [Htv [Htv' [Henv [He'nv' H1]]]]]].
        exists v. exists v'.
        split.
          erewrite delta_subst_opt with (E:=E2) (E':=E1); eauto.
            rewrite <- subst_tt_fresh; auto.
              apply notin_fv_wf with (X:=X) in H3; auto.
         
            apply F_related_subst__inversion in Hrel_subst.
             decompose [prod] Hrel_subst.
             apply dsubst_weaken; auto.
             apply wfr_left_inv in Hwfr; auto.

            apply wfr_left_inv in Hwfr; auto.
        split.
          erewrite delta_subst_opt with (E:=E2) (E':=E1); eauto.
            rewrite <- subst_tt_fresh; auto.
              apply notin_fv_wf with (X:=X) in H3; auto.
         
            apply F_related_subst__inversion in Hrel_subst.
            decompose [prod] Hrel_subst.
            apply dsubst_weaken; auto.
             apply wfr_right_inv in Hwfr; auto.

            apply wfr_right_inv in Hwfr; auto.
        split; auto.
        split; auto.
          apply F_related_subst__inversion in Hrel_subst.
          decompose [prod] Hrel_subst.
          apply Frel_weaken with (E:=E2) (E':=E1); auto.
            assert (X `notin` fv_env (E1++E2)) as XnE.
              apply wfe_dom_fv_env; auto.
            assert (X `notin` fv_tt t0) as Xnt0.
              apply notin_fv_wf with (X:=X) in H3; auto.
            simpl_env in XnE. auto.

      assert (x `notin` fv_tt t0) as xnt0.
        apply notin_fv_wf with (X:=x) in H3; auto.
      simpl_env. simpl. auto.

      apply wf_typ_weakening; auto.
        apply F_related_subst__inversion in Hrel_subst.
        decompose [prod] Hrel_subst.
        simpl in HX. 
        apply uniq_insert_mid; auto.
Qed.

Lemma F_related_subst_gweaken : forall E1 E2 D gsubst1 gsubst2 gsubst1' gsubst2' lgsubst lgsubst' rsubst1 rsubst2 dsubst1 dsubst2 dsubst1' dsubst2' x T e e',
  F_related_subst (E1++E2) D (gsubst1++gsubst2) (gsubst1'++gsubst2') lgsubst lgsubst' (rsubst1++rsubst2) (dsubst1++dsubst2) (dsubst1'++dsubst2') ->
  gdom_env E1 [=] dom gsubst1 ->
  gdom_env E1 [=] dom gsubst1' ->
  gdom_env E2 [=] dom gsubst2 ->
  gdom_env E2 [=] dom gsubst2' ->
  ddom_env E1 [=] dom dsubst1 ->
  ddom_env E1 [=] dom dsubst1' ->
  ddom_env E1 [=] dom rsubst1 ->
  ddom_env E2 [=] dom dsubst2 ->
  ddom_env E2 [=] dom dsubst2' ->
  ddom_env E2 [=] dom rsubst2 ->
  x `notin` (dom E1 `union` dom E2 `union` dom D)->
  wf_typ E2 T ->
  typing nil nil e (apply_delta_subst_typ dsubst2 T) ->
  typing nil nil e' (apply_delta_subst_typ dsubst2' T) ->
  F_related_terms T rsubst2 dsubst2 dsubst2' e e' ->
  F_related_subst (E1++[(x, bind_typ T)]++E2) D (gsubst1++[(x, e)]++gsubst2) (gsubst1'++[(x, e')]++gsubst2') lgsubst lgsubst' (rsubst1++rsubst2) (dsubst1++dsubst2) (dsubst1'++dsubst2').
Proof.
  intros E1 E2 D gsubst1 gsubst2 gsubst1' gsubst2' lgsubst lgsubst' rsubst1 rsubst2 dsubst1 dsubst2 dsubst1' dsubst2' x T e e'
                Hrel_subst Hdomg1 Hdomg1' Hdomg2 Hdomg2' Hdomd1 Hdomd1' Hdomr1 Hdomd2 Hdomd2' Hdomr2 Hx Hwft Htyp Htyp' Hrel.
  remember (E1++E2) as E.
  remember (gsubst1++gsubst2) as gsubst.
  remember (gsubst1'++gsubst2') as gsubst'.
  remember (rsubst1++rsubst2) as rsubst.
  remember (dsubst1++dsubst2) as dsubst.
  remember (dsubst1'++dsubst2') as dsubst'.
  generalize dependent E1.
  generalize dependent dsubst1.
  generalize dependent dsubst1'.
  generalize dependent rsubst1.  
  generalize dependent gsubst1.
  generalize dependent gsubst1'.
  (F_related_subst_cases (induction Hrel_subst) Case); intros; subst.
  Case "F_related_subst_empty".
    symmetry in Heqdsubst.
    apply app_eq_nil in Heqdsubst.
    destruct Heqdsubst; subst.

    symmetry in Heqdsubst'.
    apply app_eq_nil in Heqdsubst'.
    destruct Heqdsubst'; subst.

    symmetry in Heqrsubst.
    apply app_eq_nil in Heqrsubst.
    destruct Heqrsubst; subst.

    symmetry in Heqgsubst.
    apply app_eq_nil in Heqgsubst.
    destruct Heqgsubst; subst.

    symmetry in Heqgsubst'.
    apply app_eq_nil in Heqgsubst'.
    destruct Heqgsubst'; subst.

    symmetry in HeqE.
    apply app_eq_nil in HeqE.
    destruct HeqE; subst.
    rewrite_env ([(x, bind_typ T)]++empty).
    rewrite_env ([(x, e)]++gamma_nil).
    rewrite_env ([(x, e')]++gamma_nil).
    apply F_related_subst_typ; auto.
       simpl. eauto using notin_fv_wf.

  Case "F_related_subst_kind".
    simpl_env in *.
    apply one_eq_app in Heqrsubst. destruct Heqrsubst as [[rsubst0 [rEQ1 rEQ2]] | [rEQ1 rEQ2]]; subst.
      apply one_eq_app in Heqdsubst. destruct Heqdsubst as [[dsubst0 [dEQ1 dEQ2]] | [dEQ1 dEQ2]]; subst.
        apply one_eq_app in Heqdsubst'. destruct Heqdsubst' as [[dsubst0' [dEQ1' dEQ2']] | [dEQ1' dEQ2']]; subst.
          apply one_eq_app in HeqE. destruct HeqE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
            simpl_env.
            apply F_related_subst_kind; auto.
              apply IHHrel_subst with (rsubst1:=rsubst0) (dsubst1:=dsubst0) (dsubst1':=dsubst0') (gsubst1'0:=gsubst1'); auto.
                apply ddom_dom__inv with (X:=X)(b:=t); auto.
                  simpl_env in H. destruct_notin.
                  apply free_env__free_ddom in H; auto.
                   
                  destruct_notin.
                  apply free_env__free_ddom in H.
                  apply dom_F_related_subst in Hrel_subst.
                  destruct Hrel_subst as [J1 [J2 [J3 [J4 [J5 [J6 J7]]]]]].
                  rewrite J1 in H.
                  simpl_env in H. auto.
                apply ddom_dom__inv with (X:=X)(b:=t'); auto.
                  simpl_env in H. destruct_notin.
                  apply free_env__free_ddom in H; auto.
                   
                  destruct_notin.
                  apply free_env__free_ddom in H.
                  apply dom_F_related_subst in Hrel_subst.
                  destruct Hrel_subst as [J1 [J2 [J3 [J4 [J5 [J6 J7]]]]]].
                  rewrite J2 in H.
                  simpl_env in H. auto.
                apply ddom_dom__inv with (X:=X)(b:=R); auto.
                  simpl_env in H. destruct_notin.
                  apply free_env__free_ddom in H; auto.
                   
                  destruct_notin.
                  apply free_env__free_ddom in H.
                  apply dom_F_related_subst in Hrel_subst.
                  destruct Hrel_subst as [J1 [J2 [J3 [J4 [J5 [J6 J7]]]]]].
                  rewrite J3 in H.
                  simpl_env in H. auto.
                simpl_env. simpl. simpl_env in Hx. simpl in Hx.
                simpl_env in H. 
                assert (X `notin` fv_tt T) as XnT.
                  apply notin_fv_wf with (X:=X) in Hwft; auto.
                auto.

            simpl_env in Hdomd1.
            assert (X `notin` (singleton X `union` dom dsubst0) -> False) as J.
              intro. destruct_notin. contradict NotInTac0; auto.
            rewrite <- Hdomd1 in J.
            contradict J; auto.

          simpl_env in Hdomd1'.
          simpl_env in Hdomd1.
          assert (X `notin` (singleton X `union` dom dsubst0) -> False) as J.
            intro. destruct_notin. contradict NotInTac0; auto.
          rewrite <- Hdomd1 in J.
          rewrite Hdomd1' in J.
          contradict J; auto.
        simpl_env in Hdomd1.
        simpl_env in Hdomr1.
        assert (X `notin` (singleton X `union` dom rsubst0) -> False) as J.
          intro. destruct_notin. contradict NotInTac0; auto.
        rewrite <- Hdomr1 in J.
        rewrite Hdomd1 in J.
        contradict J; auto.
      apply one_eq_app in HeqE. destruct HeqE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
        simpl in Hdomr1.
        assert (X `notin` (singleton X `union` ddom_env E0') -> False) as J.
          intro. destruct_notin. contradict NotInTac0; auto.
        rewrite Hdomr1 in J.
        contradict J; auto.

        simpl in Hdomg1. symmetry in Hdomg1.  apply dom_empty_inv in Hdomg1.
        simpl in Hdomg1'. symmetry in Hdomg1'.  apply dom_empty_inv in Hdomg1'.
        simpl in Hdomd1. symmetry in Hdomd1.  apply dom_empty_inv in Hdomd1.
        simpl in Hdomd1'. symmetry in Hdomd1'.  apply dom_empty_inv in Hdomd1'.
        subst. 
        simpl_env in Heqdsubst. simpl_env in Heqdsubst'.
        subst.
        simpl_env.

        assert (J:=Hrel_subst).
        apply F_related_subst__inversion in J.
        decompose [prod] J.
        assert (x `notin` fv_env E) as xnE.
          apply wfe_dom_fv_env; auto.
        assert (x `notin` fv_lenv lE) as xnlE.
          apply notin_fv_lenv_wfle with (E:=E); auto.
            apply wf_lgamma_subst__wf_lenv in b1.
            destruct b1; auto.
        assert (x `notin` fv_tt T) as xnT.
          apply notin_fv_wf with (X:=x) in Hwft; auto.

        apply F_related_subst_typ; simpl; auto.
          simpl_env.
          apply F_related_subst_kind; simpl; auto.

  Case "F_related_subst_typ".
    simpl_env in *.
    apply one_eq_app in Heqgsubst. destruct Heqgsubst as [[gsubst0 [gEQ1 gEQ2]] | [gEQ1 gEQ2]]; subst.
      apply one_eq_app in Heqgsubst'. destruct Heqgsubst' as [[gsubst0' [gEQ1' gEQ2']] | [gEQ1' gEQ2']]; subst.
        apply one_eq_app in HeqE. destruct HeqE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
          simpl_env.
          apply F_related_subst_typ; auto.
              apply IHHrel_subst with (rsubst3:=rsubst1) (dsubst3:=dsubst1) (dsubst1'0:=dsubst1') (gsubst1:=gsubst0) (gsubst1':=gsubst0'); auto.
                apply gdom_dom__inv with (x:=x0)(b:=e)(t:=t); auto.
                  simpl_env in H2. destruct_notin.
                  apply free_env__free_gdom in H2; auto.

                  destruct_notin.
                  apply free_env__free_gdom in H2.
                  apply dom_F_related_subst in Hrel_subst.
                  destruct Hrel_subst as [J1 [J2 [J3 [J4 [J5 [J6 J7]]]]]].
                  rewrite J4 in H2.
                  simpl_env in H2. auto.
                apply gdom_dom__inv with (x:=x0)(b:=e')(t:=t); auto.
                  simpl_env in H2. destruct_notin.
                  apply free_env__free_gdom in H2; auto.
                   
                  destruct_notin.
                  apply free_env__free_gdom in H2.
                  apply dom_F_related_subst in Hrel_subst.
                  destruct Hrel_subst as [J1 [J2 [J3 [J4 [J5 [J6 J7]]]]]].
                  rewrite J5 in H2.
                  simpl_env in H2. auto.

                simpl_env. simpl. simpl_env in Hx. simpl in Hx.
                simpl_env in H2. 
                assert (x0 `notin` fv_tt T) as x0nT.
                  apply notin_fv_wf with (X:=x0) in Hwft; auto.
                auto.

                apply wf_typ_weakening; auto.
                  apply F_related_subst__inversion in Hrel_subst.
                  decompose [prod] Hrel_subst.
                  simpl in Hx. 
                  apply uniq_insert_mid; auto.

            simpl_env in Hdomg1.
            assert (x0 `notin` (singleton x0 `union` dom gsubst0) -> False) as J.
              intro. destruct_notin. contradict NotInTac0; auto.
            rewrite <- Hdomg1 in J.
            contradict J; auto.

          simpl_env in Hdomg1'.
          simpl_env in Hdomg1.
          assert (x0 `notin` (singleton x0 `union` dom gsubst0) -> False) as J.
            intro. destruct_notin. contradict NotInTac0; auto.
          rewrite <- Hdomg1 in J.
          rewrite Hdomg1' in J.
          contradict J; auto.
      apply one_eq_app in HeqE. destruct HeqE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
        simpl in Hdomg1.
        assert (x0 `notin` (singleton x0 `union` gdom_env E0') -> False) as J.
          intro. destruct_notin. contradict NotInTac0; auto.
        rewrite Hdomg1 in J.
        contradict J; auto.

        simpl in Hdomg1'. symmetry in Hdomg1'.  apply dom_empty_inv in Hdomg1'.
        simpl in Hdomd1. symmetry in Hdomd1.  apply dom_empty_inv in Hdomd1.
        simpl in Hdomd1'. symmetry in Hdomd1'.  apply dom_empty_inv in Hdomd1'.
        simpl in Hdomr1. symmetry in Hdomr1.  apply dom_empty_inv in Hdomr1.
        subst. 
        simpl_env in Heqgsubst'.
        subst.
        simpl_env.

        assert (J:=Hrel_subst).
        apply F_related_subst__inversion in J.
        decompose [prod] J.
        assert (x `notin` fv_env E) as xnE.
          apply wfe_dom_fv_env; auto.
        assert (x `notin` fv_lenv lE) as xnlE.
          apply notin_fv_lenv_wfle with (E:=E); auto.
            apply wf_lgamma_subst__wf_lenv in b1.
            destruct b1; auto.
        assert (x `notin` fv_tt T) as xnT.
          apply notin_fv_wf with (X:=x) in Hwft; auto.
        assert (x `notin` fv_tt t) as xnt.
          apply notin_fv_wf with (X:=x) in H3; auto.
        simpl in Hx. auto.
        apply F_related_subst_typ; simpl; auto.
          simpl_env.
          apply F_related_subst_typ; simpl; auto.

  Case "F_related_subst_ltyp".
    simpl_env in *.
    apply F_related_subst_ltyp; auto.
      apply IHHrel_subst with (rsubst3:=rsubst1) (dsubst3:=dsubst1) (dsubst1'0:=dsubst1') (gsubst3:=gsubst1) (gsubst1'0:=gsubst1'); auto.

      assert (x0 `notin` fv_tt T) as x0nT.
        apply notin_fv_wf with (X:=x0) in Hwft; auto.
      assert (x0 `notin` fv_tt t) as x0nt.
        apply notin_fv_wf with (X:=x0) in H3; auto.
      simpl_env. simpl. auto.

      apply wf_typ_weakening; auto.
        apply F_related_subst__inversion in Hrel_subst.
        decompose [prod] Hrel_subst.
        simpl in Hx. 
        apply uniq_insert_mid; auto.
Qed.
    
Lemma F_Rsubst_gweaken : forall E1 E2 rsubst dsubst dsubst' x T,
  F_Rsubst (E1++E2) rsubst dsubst dsubst' ->
  x `notin` (dom E1 `union` dom E2)->
  wf_typ E2 T ->
  F_Rsubst (E1++[(x, bind_typ T)]++E2) rsubst dsubst dsubst'.
Proof.
  intros E1 E2 rsubst dsubst dsubst' x T HRsubst Hx Wft.
  remember (E1++E2) as EE.
  generalize dependent E1.
  (F_Rsubst_cases (induction HRsubst) Case); intros; subst.
  Case "F_Rsubst_empty".
    symmetry in HeqEE.
    apply app_eq_nil in HeqEE.
    destruct HeqEE; subst.
    simpl_env.
    rewrite_env ([(x, bind_typ T)]++nil). rewrite_env (nil++rho_nil).
    rewrite_env (nil++delta_nil).  rewrite_env (nil++delta_nil).
    apply F_Rsubst_typ; auto.
 
  Case "F_Rsubst_rel".
    simpl_env in *.
    apply one_eq_app in HeqEE. destruct HeqEE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
      simpl_env.
      apply F_Rsubst_rel; auto.
        assert (X `notin` fv_tt T) as XnT.
          apply notin_fv_wf with (X:=X) in Wft; auto.
            apply free_env__free_dom in H0. 
            simpl_env in H0. auto.
        simpl_env in H0. simpl_env. simpl. auto.

      simpl_env.
      apply F_Rsubst_typ; auto.
        apply F_Rsubst_rel; auto.

        assert (x `notin` fv_env E) as XnE.
          apply wfe_dom_fv_env; auto.
          apply F_Rsubst__wf_subst in HRsubst.
          decompose [prod] HRsubst.
          apply  wf_rho_subst__uniq in b. 
          decompose [and] b; auto.
        simpl. auto.
 
  Case "F_Rsubst_typ".
    simpl_env in *.
    apply one_eq_app in HeqEE. destruct HeqEE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
      simpl_env.
      apply F_Rsubst_typ; auto.
        apply wf_typ_weakening; auto.
          apply F_Rsubst__wf_subst in HRsubst.
          decompose [prod] HRsubst.
          apply  wf_rho_subst__uniq in b. 
          decompose [and] b; auto.
      
          assert (x0 `notin` fv_tt T) as x0nT.
            apply notin_fv_wf with (X:=x0) in Wft; auto.
              apply free_env__free_dom in H0. 
              simpl_env in H0. auto.
          simpl_env in H0. simpl_env. simpl. auto.

      simpl_env.
      apply F_Rsubst_typ; auto.
        apply F_Rsubst_typ; auto.

        assert (x `notin` fv_env E) as XnE.
          apply wfe_dom_fv_env; auto.
          apply F_Rsubst__wf_subst in HRsubst.
          decompose [prod] HRsubst.
          apply  wf_rho_subst__uniq in b. 
          decompose [and] b; auto.
        assert (x `notin` fv_tt T0) as xnT.
          apply notin_fv_wf with (X:=x) in H; auto.
        simpl. auto.
Qed.

Lemma F_Rsubst_dweaken : forall E1 E2 rsubst1 rsubst2 dsubst1 dsubst2 dsubst1' dsubst2' X R t2 t2',
  F_Rsubst (E1++E2) (rsubst1++rsubst2) (dsubst1++dsubst2) (dsubst1'++dsubst2') ->
  ddom_env E1 [=] dom dsubst1 ->
  ddom_env E1 [=] dom dsubst1' ->
  ddom_env E1 [=] dom rsubst1 ->
  ddom_env E2 [=] dom dsubst2 ->
  ddom_env E2 [=] dom dsubst2' ->
  ddom_env E2 [=] dom rsubst2 ->
  X `notin` (dom E1 `union` dom E2)->
  wfr R t2 t2' ->
  F_Rsubst (E1++[(X, bind_kn)]++E2) (rsubst1++[(X, R)]++rsubst2) (dsubst1++[(X, t2)]++dsubst2) (dsubst1'++[(X, t2')]++dsubst2').
Proof.
  intros E1 E2 rsubst1 rsubst2 dsubst1 dsubst2 dsubst1' dsubst2' X R t2 t2' HRsubst 
    Hdomd1 Hdomd1' Hdomr1 Hdomd2 Hdomd2' Hdomr2 HX Hwfr.
  remember (E1++E2) as E.
  remember (rsubst1++rsubst2) as rsubst.
  remember (dsubst1++dsubst2) as dsubst.
  remember (dsubst1'++dsubst2') as dsubst'.
  generalize dependent E1.
  generalize dependent dsubst1.
  generalize dependent dsubst1'.
  generalize dependent rsubst1.  
  (F_Rsubst_cases (induction HRsubst) Case); intros; subst.
  Case "F_Rsubst_empty".
    symmetry in HeqE.
    apply app_eq_nil in HeqE.
    destruct HeqE; subst.

    symmetry in Heqdsubst.
    apply app_eq_nil in Heqdsubst.
    destruct Heqdsubst; subst.

    symmetry in Heqdsubst'.
    apply app_eq_nil in Heqdsubst'.
    destruct Heqdsubst'; subst.

    symmetry in Heqrsubst.
    apply app_eq_nil in Heqrsubst.
    destruct Heqrsubst; subst.

    simpl_env.
    rewrite_env ([(X, bind_kn)]++nil). 
    rewrite_env ([(X, R)]++rho_nil).
    rewrite_env ([(X, t2)]++delta_nil).  
    rewrite_env ([(X, t2')]++delta_nil).
    apply F_Rsubst_rel; auto.
 
  Case "F_Rsubst_rel".
    simpl_env in *.
    apply one_eq_app in Heqrsubst. destruct Heqrsubst as [[rsubst0 [rEQ1 rEQ2]] | [rEQ1 rEQ2]]; subst.
      apply one_eq_app in Heqdsubst. destruct Heqdsubst as [[dsubst0 [dEQ1 dEQ2]] | [dEQ1 dEQ2]]; subst.
        apply one_eq_app in Heqdsubst'. destruct Heqdsubst' as [[dsubst0' [dEQ1' dEQ2']] | [dEQ1' dEQ2']]; subst.
          apply one_eq_app in HeqE. destruct HeqE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
            simpl_env.
            apply F_Rsubst_rel; auto.
              apply IHHRsubst with (rsubst1:=rsubst0) (dsubst1:=dsubst0) (dsubst1':=dsubst0'); auto.
                apply ddom_dom__inv with (X:=X0)(b:=t); auto.
                  simpl_env in H0. destruct_notin.
                  apply free_env__free_ddom in H0; auto.
                   
                  destruct_notin.
                  apply free_env__free_ddom in H0.
                  apply dom_F_Rsubst in HRsubst.
                  destruct HRsubst as [J1 [J2 J3]].
                  rewrite J1 in H0.
                  simpl_env in H0. auto.
                apply ddom_dom__inv with (X:=X0)(b:=t'); auto.
                  simpl_env in H0. destruct_notin.
                  apply free_env__free_ddom in H0; auto.
                   
                  destruct_notin.
                  apply free_env__free_ddom in H0.
                  apply dom_F_Rsubst in HRsubst.
                  destruct HRsubst as [J1 [J2 J3]].
                  rewrite J2 in H0.
                  simpl_env in H0. auto.
                apply ddom_dom__inv with (X:=X0)(b:=R); auto.
                  simpl_env in H0. destruct_notin.
                  apply free_env__free_ddom in H0; auto.
                   
                  destruct_notin.
                  apply free_env__free_ddom in H0.
                  apply dom_F_Rsubst in HRsubst.
                  destruct HRsubst as [J1 [J2 J3]].
                  rewrite J3 in H0.
                  simpl_env in H0. auto.
                simpl_env. simpl. simpl_env in HX. simpl in HX.
                simpl_env in H0. 
                auto.

            simpl_env in Hdomd1.
            assert (X0 `notin` (singleton X0 `union` dom dsubst0) -> False) as J.
              intro. destruct_notin. contradict NotInTac0; auto.
            rewrite <- Hdomd1 in J.
            contradict J; auto.

          simpl_env in Hdomd1'.
          simpl_env in Hdomd1.
          assert (X0 `notin` (singleton X0 `union` dom dsubst0) -> False) as J.
            intro. destruct_notin. contradict NotInTac0; auto.
          rewrite <- Hdomd1 in J.
          rewrite Hdomd1' in J.
          contradict J; auto.
        simpl_env in Hdomd1.
        simpl_env in Hdomr1.
        assert (X0 `notin` (singleton X0 `union` dom rsubst0) -> False) as J.
          intro. destruct_notin. contradict NotInTac0; auto.
        rewrite <- Hdomr1 in J.
        rewrite Hdomd1 in J.
        contradict J; auto.
      apply one_eq_app in HeqE. destruct HeqE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
        simpl in Hdomr1.
        assert (X0 `notin` (singleton X0 `union` ddom_env E0') -> False) as J.
          intro. destruct_notin. contradict NotInTac0; auto.
        rewrite Hdomr1 in J.
        contradict J; auto.

        simpl in Hdomd1. symmetry in Hdomd1.  apply dom_empty_inv in Hdomd1.
        simpl in Hdomd1'. symmetry in Hdomd1'.  apply dom_empty_inv in Hdomd1'.
        subst. 
        simpl_env in Heqdsubst. simpl_env in Heqdsubst'.
        subst.
        simpl_env.

        assert (J:=HRsubst).
        apply F_Rsubst__wf_subst in J.
        decompose [prod] J.
        apply wf_rho_subst__uniq in b.
        decompose [and] b.
        assert (X `notin` fv_env E) as XnE.
          apply wfe_dom_fv_env; auto.
        apply F_Rsubst_rel; simpl; auto.
          simpl_env.
          apply F_Rsubst_rel; simpl; auto.
 
  Case "F_Rsubst_typ".
    simpl_env in *.
    apply one_eq_app in HeqE. destruct HeqE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
      simpl_env.
      apply F_Rsubst_typ; auto.
        apply wf_typ_weakening; auto.
          apply F_Rsubst__wf_subst in HRsubst.
          decompose [prod] HRsubst.
          apply  wf_rho_subst__uniq in b. 
          decompose [and] b; auto.       
        simpl_env in H0. simpl_env. simpl. auto.

      simpl in Hdomd1. symmetry in Hdomd1.  apply dom_empty_inv in Hdomd1.
      simpl in Hdomd1'. symmetry in Hdomd1'.  apply dom_empty_inv in Hdomd1'.
      simpl in Hdomr1. symmetry in Hdomr1.  apply dom_empty_inv in Hdomr1.
      subst. 
      simpl_env.
      apply F_Rsubst_rel; auto.
        apply F_Rsubst_typ; auto.

        assert (X `notin` fv_env E) as XnE.
          apply wfe_dom_fv_env; auto.
          apply F_Rsubst__wf_subst in HRsubst.
          decompose [prod] HRsubst.
          apply  wf_rho_subst__uniq in b. 
          decompose [and] b; auto.
        assert (X `notin` fv_tt T) as XnT.
          apply notin_fv_wf with (X:=X) in H; auto.
        simpl. auto.
Qed.


