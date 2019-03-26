(** Administrative lemmas for ?.

    Table of contents:
      - #<a href="##wft">Properties of wf_typ</a>#
      - #<a href="##oktwft">Properties of wf_env and wf_typ</a>#
      - #<a href="##okt">Properties of wf_env</a>#
      - #<a href="##subst">Properties of substitution</a>#
      - #<a href="##regularity">Regularity lemmas</a>#
      - #<a href="##auto">Automation</a># *)

Require Export Concur_LemmasInit.

Lemma ni_helper0 : forall X0 Y L X QX PX, 
X0
       `notin` union L
                 (union (singleton Y)
                    (union (singleton X)
                       (union Metatheory.empty (union (fv_cp QX) (fv_cp PX)))))
->
  Y `notin` singleton X0.
Proof.
  intros.
  fsetdec.
Qed.

Lemma ni_helper1 : forall Y0 Y X0 L X QX PX,
 Y0  `notin` union (singleton X0)
                 (union L
                    (union (singleton Y)
                       (union (singleton X)
                          (union Metatheory.empty
                             (union (fv_cp QX) (fv_cp PX))))))
->
  Y `notin` singleton Y0.
Proof.
  intros.
  fsetdec.
Qed.

Lemma ni_helper2 : forall Y PX QX,
 Y `notin` union (fv_cp PX) (fv_cp QX) 
->
  Y `notin` fv_cp PX.
Proof.
  intros.
  fsetdec.
Qed.

Lemma ni_helper3 : forall Y PX QX,
 Y `notin` union (fv_cp PX) (fv_cp QX) 
->
  Y `notin` fv_cp QX.
Proof.
  intros.
  fsetdec.
Qed.

Lemma ni_helper4 : forall Y0 X0 L Y X QX PX,
Y0
       `notin` union (singleton X0)
                 (union L
                    (union (singleton Y)
                       (union (singleton X)
                          (union Metatheory.empty
                             (union (fv_cp QX) (fv_cp PX))))))
->
Y0 `notin` union (singleton X0) L.
Proof.
 intros.
 fsetdec.
Qed.

Lemma dom_cenv_helper: forall (Q1 Q2 Q3 : cenv),
  dom Q1 [=] union (dom Q2) (dom Q3) ->
  dom Q3 [<=] dom Q1.
Proof.
  intros. fsetdec.
Qed.

Lemma disjoint_cenv_distrib_left: forall (Q1L Q1R Q2 : cenv),
  disjoint (Q1L ++ Q1R) Q2 <-> (disjoint Q1L Q2 /\ disjoint Q1R Q2).
Proof.
  repeat split; intros; unfold disjoint in *; simpl_env in *; fsetdec.
Qed.

Lemma disjoint_cenv_distrib_right: forall (Q1 Q2L Q2R : cenv),
  disjoint Q1 (Q2L ++ Q2R) <-> (disjoint Q1 Q2L /\ disjoint Q1 Q2R).
Proof.
  repeat split; intros; unfold disjoint in *; simpl_env in *; fsetdec.
Qed.

Lemma disjoint_cenv_srcsnk_helper: forall E X d T Q Q1L Q1R Q2L Q2R
                                                                                    Q3L Q3R Q4L Q4R d',
  cenv_split_exp E Q (Q1L ++ [(X, cbind_proto d T)] ++ Q1R)
                                 (Q2L ++ [(X, cbind_proto d T)] ++ Q2R) ->
  cenv_split_proc E (Q3L ++ [(X, cbind_proto cdir_src T)] ++ Q3R)
                               (Q2L ++ [(X, cbind_proto cdir_snk T)] ++ Q2R)
                               (Q4L ++ [(X, cbind_proto cdir_both T)] ++ Q4R)
                               (Some X) ->
  disjoint (Q3L ++ Q3R) (Q1L ++ [(X, cbind_proto d' T)] ++ Q1R).
Proof.
  intros. assert (uniq (Q3L ++ [(X, cbind_proto cdir_src T)] ++ Q3R)).
    apply wf_cenv_split_proc_left in H0.
    apply uniq_from_wf_cenv in H0. auto.
  apply cenv_split_proc_srcsnk_exp in H0.
  apply cenv_split_exp_disjoint in H0.
  apply dom_cenv_split_exp in H.
  apply dom_cenv_helper in H. simpl_env in H.
  apply disjoint_cenv_distrib_left in H0. destruct H0 as [H2 H3].
  apply <- disjoint_cenv_distrib_left. split.
    clear H3. unfold disjoint in *. simpl_env in *. solve_uniq.
    clear H2. unfold disjoint in *. simpl_env in *. solve_uniq.
Qed.

Lemma eq_open_cc_rename: forall (X Y:atom) i j c1 c2,
  X `notin` union (fv_cc c1) (fv_cc c2) ->
  Y `notin` union (fv_cc c1) (fv_cc c2) ->
  open_cc_rec i X c1 = open_cc_rec j X c2 ->
  open_cc_rec i Y c1 = open_cc_rec j Y c2.
Proof.
  intros.
  induction c1; induction c2; subst; simpl in *; auto.
  destruct (i == n).
  destruct (j == n0). auto. inversion H1.
  destruct (j == n0). inversion H1. auto.
  destruct (i == n). subst. inversion H1. subst. fsetdec. auto.
  destruct (j == n). subst. inversion H1. subst. fsetdec. auto.
Qed.

Lemma eq_open_ce_rename: forall (X Y:atom) e1 e2 i j ,
  X `notin` union (fv_ce e1) (fv_ce e2) ->
  Y `notin` union (fv_ce e1) (fv_ce e2) ->
  open_ce_rec i X e1 = open_ce_rec j X e2 ->
  open_ce_rec i Y e1 = open_ce_rec j Y e2.
Proof.
  intros X Y e1. 
  induction e1; intros e2; destruct e2; simpl in *; intros i j NI1 NI2 EQ; inversion EQ; clear EQ; subst; simpl in *; (
  try (rewrite (IHe1 e2 i j); auto);
  try (rewrite (IHe1_1 e2_1 i j); auto);
  try (rewrite (IHe1_2 e2_2 i j); auto);
  try (rewrite (IHe1_3 e2_3 i j); auto);
  try (rewrite (eq_open_cc_rename X Y i j c c0)); auto
 ); auto.
Qed.

Lemma eq_open_cp_rename: forall (X Y:atom) P Q i j ,
  X `notin` union (fv_cp P) (fv_cp Q) ->
  Y `notin` union (fv_cp P) (fv_cp Q) ->
  open_cp_rec i X P = open_cp_rec j X Q ->
  open_cp_rec i Y P = open_cp_rec j Y Q.
Proof.
  intros X Y P.
  induction P; intros Q; induction Q; intros i j NI1 NI2 EQ; simpl in *; inversion EQ; clear EQ; subst; simpl in *; auto.
  rewrite (eq_open_ce_rename X Y e e0 i j); auto.
  rewrite (IHP1 Q1 i j); auto.
  rewrite (IHP2 Q2 i j); auto.

  rewrite (IHP Q (S i) (S j)); auto.
Qed.

Lemma proc_eq1_rename : forall P Q (X Y:atom) i,
  Y `notin` union (fv_cp P) (fv_cp Q) ->
  X `notin` union (fv_cp P) (fv_cp Q) ->
  proc_eq1 (open_cp_rec i Y P) (open_cp_rec i Y Q) ->
  proc_eq1 (open_cp_rec i X P) (open_cp_rec i X Q).
Proof.
  intros P Q X Y i NI1 NI2 EQ.
  remember (open_cp_rec i Y P) as P1.
  remember (open_cp_rec i Y Q) as Q1.
  generalize dependent P. generalize dependent Q.
  generalize dependent i. generalize dependent X. generalize dependent Y.
  (proc_eq1_cases (induction EQ) Case); intros Y X i QX EQQ PX NI1 NI2 EQP; destruct QX; destruct PX; inversion EQQ; inversion EQP; subst; simpl in *; auto.

  Case "proc_eq1_parl".
    assert (PX2 = QX2).
    apply (open_cp_aux_inj i Y); auto.
    rewrite H.
    apply proc_eq1_parl.
    apply (IHEQ Y X); auto.
  
  Case "proc_eq1_new".
  subst.
  pick fresh Z and apply proc_eq1_new.
  unfold open_cp.
  rewrite open_cp_open_cp_comm; auto.
  rewrite (open_cp_open_cp_comm QX); auto.
  eapply (H0 Z); auto.
  unfold open_cp.
  rewrite (open_cp_open_cp_comm); auto.
  assert (Y `notin` (fv_cp (open_cp_rec 0 Z PX))). apply fv_cp_notin_open; auto.
  assert (Y `notin` (fv_cp (open_cp_rec 0 Z QX))). apply fv_cp_notin_open; auto.
  apply notin_union; auto.  

  assert (X `notin` (fv_cp (open_cp_rec 0 Z PX))). apply fv_cp_notin_open; auto.
  assert (X `notin` (fv_cp (open_cp_rec 0 Z QX))). apply fv_cp_notin_open; auto.
  apply notin_union; auto.
  
  unfold open_cp.
  rewrite open_cp_open_cp_comm; auto.

  Case "proc_eq1_comm".
  assert (QX1 = PX2). apply (open_cp_aux_inj i Y); auto.
  assert (QX2 = PX1). apply (open_cp_aux_inj i Y); auto.
  subst.
  apply proc_eq1_comm.

  Case "proc_eq1_assoc".
  destruct QX2; inversion H1; subst; simpl in *; auto.
  destruct PX1; inversion H2; subst; simpl in *; auto.
  assert (QX1 = PX1_1). apply (open_cp_aux_inj i Y); auto.
  assert (QX2_1 = PX1_2). apply (open_cp_aux_inj i Y); auto.
  subst; auto.
  assert (PX2 = QX2_2). apply (open_cp_aux_inj i Y); auto.
  subst.
  apply proc_eq1_assoc.

  Case "proc_eq1_swap".
  destruct QX; inversion H2; subst; simpl in *; auto.
  destruct PX; inversion H4; subst; simpl in *; auto.

  let LL := gather_atoms in (apply (proc_eq1_swap LL)).
  intros.
  unfold open_cp in *.
  lapply (H X0 Y0); auto. intros.
  lapply H3. intros.

  rewrite (open_cp_open_cp_comm PX) in *; auto.
  rewrite (open_cp_open_cp_comm QX) in *; auto.
  rewrite (open_cp_open_cp_comm (open_cp_rec 1 Y0 PX)) in *; auto.
  rewrite (open_cp_open_cp_comm (open_cp_rec 1 X0 QX)) in *; auto.
  assert ((open_cp_rec 0 X0 (open_cp_rec 1 Y0 PX)) = (open_cp_rec 0 Y0 (open_cp_rec 1 X0 QX))).
  apply (open_cp_aux_inj (S (S (i))) Y). 
  assert (Y `notin` (fv_cp (open_cp_rec 0 X0 (open_cp_rec 1 Y0 PX)))).
  apply fv_cp_notin_open. simpl. 
  clear H3. clear EQP. clear EQQ. clear H2. clear H4.
  eapply (ni_helper0 X0 Y). apply H0.
  apply fv_cp_notin_open. simpl.
  eapply (ni_helper1 Y0 Y). apply H1.
  apply (ni_helper2 Y PX QX). apply NI1.

  assert (Y `notin` (fv_cp (open_cp_rec 0 Y0 (open_cp_rec 1 X0 QX)))).
  apply fv_cp_notin_open. simpl. 
  clear H3. clear EQP. clear EQQ. clear H2. clear H4.
  eapply (ni_helper1 Y0 Y). apply H1.
  apply fv_cp_notin_open. simpl.
  eapply (ni_helper0 X0 Y). apply H0.
  apply (ni_helper3 Y PX QX). apply NI1.
  apply notin_union. auto. auto.

  auto.

  rewrite H6.  
  auto.
  eapply ni_helper4. apply H1.

  Case "proc_eq1_extrude".
  destruct QX1; inversion H1; clear H1; subst; simpl in *; auto.
  destruct PX; inversion H4; clear H4; subst; simpl in *; auto.

  assert (QX1 = PX1).
  apply (open_cp_aux_inj (S i) Y); auto.
  subst.
  clear EQQ. clear H1.
  rewrite (eq_open_cp_rename Y X QX2 PX2 i (S i)); auto.
  apply proc_eq1_extrude.
  rewrite <- (eq_open_cp_rename Y X QX2 PX2 i (S i)); auto.
  eapply process_rename. apply H.
Qed.

Lemma channel_renumber: forall i j (Y:atom) C,
  channel (open_cc_rec i Y C) ->
  exists D, (open_cc_rec i Y C) = (open_cc_rec j Y D) /\ (forall Z, Z `notin` fv_cc C -> Z `notin` fv_cc D).
Proof.
  intros i j Y C CHAN.
  destruct C. simpl in *.
  destruct (i == n).
   exists j. simpl. destruct (j == j). 
    split; auto.
    tauto.
  inversion CHAN. 

  simpl in *. exists a. simpl; split; auto.
Qed.

Lemma expr_renumber: forall e i j (Y:atom),
  expr (open_ce_rec i Y e) ->
  exists f, open_ce_rec i Y e = open_ce_rec j Y f /\ (forall Z, (Z `notin` fv_ce e -> Z `notin` fv_ce f)).
Proof.
  intros e i j Y EXPR.
  remember (open_ce_rec i Y e) as EX.
  generalize dependent Y. generalize dependent j. generalize dependent i.
  generalize dependent e.
  (expr_cases (induction EXPR) Case); intros e i j Y EQ; destruct e; simpl in *; inversion EQ; clear EQ; subst.

  exists a; simpl; split; auto.
  exists exp_unit; simpl; split; auto.

  destruct (IHEXPR1 e3 i j Y) as [f1 [EQ1 NI1]]; auto.
  destruct (IHEXPR2 e4 i j Y) as [f2 [EQ2 NI2]]; auto.
  exists (exp_seq f1 f2); simpl in *; split; auto. rewrite EQ1. rewrite EQ2. auto.

  pick fresh Z.
  lapply (H1 Z); auto. intros; auto.
  destruct (H2 (open_ee e Z) i j Y) as [f1 [EQ1 NI]]; auto.
  unfold open_ee. rewrite <- open_ee_open_ce_comm; auto.
  exists (exp_abs t (close_ee_rec 0 Z f1)).
  simpl; split.
  rewrite (open_ce_close_ee_comm). rewrite <- EQ1.
  unfold open_ee. rewrite close_open_ee; auto.
  rewrite fv_ee_open_ce. fsetdec.
  intros; auto. rewrite fv_ce_close_ee. apply NI; auto. 
  unfold open_ee. rewrite fv_ce_open_ee. auto.

  destruct (IHEXPR1 e3 i j Y) as [f1 [EQ1 NI1]]; auto.
  destruct (IHEXPR2 e4 i j Y) as [f2 [EQ2 NI2]]; auto.
  exists (exp_app f1 f2); simpl in *; split; auto. rewrite EQ1. rewrite EQ2. auto.

  destruct (IHEXPR1 e3 i j Y) as [f1 [EQ1 NI1]]; auto.
  destruct (IHEXPR2 e4 i j Y) as [f2 [EQ2 NI2]]; auto.
  exists (exp_apair f1 f2); simpl in *; split; auto. rewrite EQ1. rewrite EQ2. auto.

  destruct (IHEXPR e i j Y) as [f1 [EQ1 NI1]]; auto.
  exists (exp_fst f1); simpl in *; split; auto. rewrite EQ1. auto.

  destruct (IHEXPR e i j Y) as [f1 [EQ1 NI1]]; auto.
  exists (exp_snd f1); simpl in *; split; auto. rewrite EQ1. auto.

  destruct (IHEXPR1 e3 i j Y) as [f1 [EQ1 NI1]]; auto.
  destruct (IHEXPR2 e4 i j Y) as [f2 [EQ2 NI2]]; auto.
  exists (exp_mpair f1 f2); simpl in *; split; auto. rewrite EQ1. rewrite EQ2. auto.

  destruct (IHEXPR1 e3 i j Y) as [f1 [EQ1 NI1]]; auto.
  destruct (IHEXPR2 e4 i j Y) as [f2 [EQ2 NI2]]; auto.
  exists (exp_let f1 f2); simpl in *; split; auto. rewrite EQ1. rewrite EQ2. auto.

  destruct (IHEXPR e i j Y) as [f1 [EQ1 NI1]]; auto.
  exists (exp_inl t f1); simpl in *; split; auto. rewrite EQ1. auto.

  destruct (IHEXPR e i j Y) as [f1 [EQ1 NI1]]; auto.
  exists (exp_inr t f1); simpl in *; split; auto. rewrite EQ1. auto.

  destruct (IHEXPR1 e4 i j Y) as [f1 [EQ1 NI1]]; auto.
  destruct (IHEXPR2 e5 i j Y) as [f2 [EQ2 NI2]]; auto.
  destruct (IHEXPR3 e6 i j Y) as [f3 [EQ3 NI3]]; auto.
  exists (exp_case f1 f2 f3); simpl in *; split; auto. rewrite EQ1. rewrite EQ2. rewrite EQ3. auto.

  destruct (IHEXPR e i j Y) as [f1 [EQ1 NI1]]; auto.
  exists (exp_go t f1); simpl in *; split; auto. rewrite EQ1. auto.

  destruct (IHEXPR e i j Y) as [f1 [EQ1 NI1]]; auto.
  exists (exp_yield f1); simpl in *; split; auto. rewrite EQ1. auto.

  destruct (channel_renumber i j Y c) as [D [EQ1 NI1]]; auto.
  exists (exp_snk D t). split. rewrite EQ1. simpl. auto. intros. auto.

  destruct (channel_renumber i j Y c) as [D [EQ1 NI1]]; auto.
  exists (exp_src D t). split. rewrite EQ1. simpl. auto. intros. auto.

  destruct (channel_renumber i j Y c) as [D [EQ1 NI1]]; auto.
  exists (exp_done D). split. rewrite EQ1. simpl. auto. intros. auto.
Qed.

Lemma process_renumber: forall i j (Y:atom) P,
  process (open_cp_rec i Y P) ->
  exists Q, open_cp_rec i Y P = open_cp_rec j Y Q /\ (forall Z, (Z `notin` (fv_cp P) -> Z `notin` fv_cp Q)).
Proof.
  intros i j Y P PROC.
  remember (open_cp_rec i Y P) as P0.
  generalize dependent i. generalize dependent Y. generalize dependent j. generalize dependent P.
  induction PROC; intros P j Y i EQ; destruct P; simpl in *; inversion EQ; subst; eauto.

  destruct (expr_renumber e0 i j Y) as [f [EQ1 NI]]; auto.
  exists (proc_exp f). simpl; split. rewrite EQ1. auto. intros; auto.

  destruct (IHPROC1 P3 j Y i) as [P1' [EQ1 NI1]]; auto.
  destruct (IHPROC2 P4 j Y i) as [P2' [EQ2 NI2]]; auto.
  exists (proc_par P1' P2'); auto. simpl; split. rewrite EQ1. rewrite EQ2. auto. 
  intros; auto.  

  pick fresh X.
  lapply (H1 X); auto; intros.
  destruct (H2 (open_cp P X) (S j) Y (S i)) as [P' [EQ1 NI1]]; auto.
  unfold open_cp. 
  rewrite open_cp_open_cp_comm; auto.
  exists (proc_new t (close_cp_rec 0 X P')). 
  simpl. split. rewrite <- close_cp_open_cp_comm; auto.
  rewrite <- EQ1. unfold open_cp. 
  rewrite close_open_cp; auto.
  apply fv_cp_notin_open. simpl. fsetdec. fsetdec.

  intros.
  destruct (Z === X).
    subst. apply fv_close_cp_aux.
  apply notin_close_cp. apply NI1.
  unfold open_cp. apply fv_cp_notin_open. simpl. fsetdec. fsetdec.
Qed.

Lemma channel_switch: forall C (X Y:atom) i j,
  i <> j -> X <> Y ->
  channel (open_cc_rec i X (open_cc_rec j Y C)) ->
  channel (open_cc_rec i Y (open_cc_rec j X C)).
Proof.
  induction C; intros X Y i j NI1 NI2 Chan; inversion Chan; subst; auto.
  destruct (j == n). simpl in *. destruct (j == n). subst.
  simpl. simpl in Chan. auto. simpl in *.
  destruct (i == n); simpl in *. auto. inversion Chan.
  simpl in *.
  destruct (j == n). simpl in *. auto.
  simpl. destruct (i == n). auto. simpl in Chan. destruct (i == n).
  subst. tauto. inversion Chan.
Qed.

Lemma expr_switch: forall e (X Y:atom) i j,
  i <> j -> X <> Y ->
  expr (open_ce_rec i X (open_ce_rec j Y e)) ->
  expr (open_ce_rec i Y (open_ce_rec j X e)).
Proof.
  intros e X Y i j NI1 NI2 EXP.
  remember (open_ce_rec i X (open_ce_rec j Y e)) as e1.
  generalize dependent e. generalize dependent X. generalize dependent Y.
  generalize dependent i. generalize dependent j.
  induction EXP; intros j i NI1 Y X NI2 e EQ; destruct e; simpl in *; inversion EQ; subst; auto.

  pick fresh Z and apply expr_abs; auto.
  unfold open_ee.
  assert (exp_fvar Z = open_ce_rec i Y Z). simpl. auto.
  rewrite H2.
  rewrite open_ee_open_ce_comm.
  assert (exp_fvar Z = open_ce_rec j X Z). simpl. auto.
  rewrite H3. 
  rewrite open_ee_open_ce_comm.
  apply (H1 Z); auto. 
  unfold open_ee.
  assert (exp_fvar Z = open_ce_rec i X Z). simpl; auto.
  rewrite H4.
  rewrite open_ee_open_ce_comm.
  assert (exp_fvar Z = open_ce_rec j Y Z); simpl; auto.
  rewrite H5.
  rewrite open_ee_open_ce_comm. rewrite <- H5. auto.

  apply expr_snk; auto. apply channel_switch; auto.
  apply expr_src; auto. apply channel_switch; auto.
  apply expr_done. apply channel_switch; auto.
Qed.


Lemma process_switch : forall P (X Y:atom) i j,
  i <> j -> X <> Y -> 
  process (open_cp_rec i X (open_cp_rec j Y P)) ->
  process (open_cp_rec i Y (open_cp_rec j X P)).
Proof.
  intros P X Y i j NI1 NI2 Proc.
  remember (open_cp_rec i X (open_cp_rec j Y P)) as Q.
  generalize dependent P. generalize dependent Y. generalize dependent X.
  generalize dependent j. generalize dependent i.
  induction Proc; intros i j NI1 X Y NI2 P EQ; destruct P; inversion EQ; subst; simpl in *; auto.

  apply process_exp. apply expr_switch; auto.

  pick fresh Z and apply process_new. auto.
  unfold open_cp.
  rewrite open_cp_open_cp_comm; auto.
  rewrite (open_cp_open_cp_comm P); auto.
  apply (H1 Z); auto.
  unfold open_cp.
  rewrite open_cp_open_cp_comm; auto.
  rewrite (open_cp_open_cp_comm P); auto.
Qed.

Lemma proc_eq1_trans : forall (Y:atom) P i Q,
  proc_eq1 (open_cp_rec i Y P) Q ->
  exists Q', Q = (open_cp_rec i Y Q') /\ (forall Z, (Z `notin` (fv_cp P) -> Z `notin` fv_cp Q')).
Proof.
  intros Y P i Q PEQ.
  remember (open_cp_rec i Y P) as P1.
  generalize dependent i. generalize dependent P. generalize dependent Y.
  (proc_eq1_cases (induction PEQ) Case); intros Y P i EQ; destruct P; simpl in *; inversion EQ; subst; auto.

  Case "proc_eq1_parl".
  destruct (IHPEQ Y P3 i) as [Q1' [EQ1 NI]]; auto.
  subst.
  exists (proc_par Q1' P4); simpl; split; auto.

  Case "proc_eq1_new".
  pick fresh X.
  lapply (H0 X); intros; auto.
  destruct (H1 Y (open_cp_rec 0 X P) (S i)) as [Q1' [EQ1 NI]]; auto.
  unfold open_cp. rewrite open_cp_open_cp_comm; auto.
  unfold open_cp in EQ1.
  exists (proc_new t (close_cp_rec 0 X Q1')).
  simpl; split. rewrite <- close_cp_open_cp_comm; auto.
  rewrite <- EQ1. rewrite close_open_cp_rec; auto.
  intros.
  destruct (Z === X). subst.
  apply fv_close_cp_aux.
  apply notin_close_cp; auto.  apply NI; auto.
  apply fv_cp_notin_open; auto.

  Case "proc_eq1_comm".
  exists (proc_par P4 P3); split; simpl; auto. 

  Case "proc_eq1_assoc".
  destruct P4; simpl in H0; inversion H0; subst.
  exists (proc_par P4_1 (proc_par P4_2 P5));
  simpl; split; auto.

  Case "proc_eq1_swap".
  pick fresh X.
  pick fresh Z.
  lapply (H X Z); intros; auto.
  lapply H0; intros; auto.
  unfold open_cp in H1.
  destruct P; simpl in H2; inversion H2; subst; auto. clear H2. clear EQ.
  exists (proc_new t0 (close_cp_rec 0 X (proc_new t (close_cp_rec 0 Z (open_cp_rec 0 X (open_cp_rec 1 Z P)))))). 
  simpl. split.
  rewrite <- close_cp_open_cp_comm; auto.
  rewrite <- close_cp_open_cp_comm; auto.
  rewrite <- (open_cp_open_cp_comm (open_cp_rec 1 Z P)); auto.
  rewrite <- (open_cp_open_cp_comm P); auto.
  rewrite H1.
  rewrite close_open_cp_rec; auto.
  rewrite close_open_cp_rec; auto.
  apply fv_cp_notin_open; auto.

  intros. 
  destruct (Z0 === X). subst.
    apply fv_close_cp_aux.
  apply notin_close_cp. 
  destruct (Z0 === Z).  subst.
    apply fv_close_cp_aux.
  apply notin_close_cp. apply fv_cp_notin_open; auto.
  apply fv_cp_notin_open; auto.

  Case "proc_eq1_extrude".
  destruct P; simpl in H2; inversion H2; subst.
  destruct (process_renumber (S i) i Y P4) as [P4' [EQ1 NI]]. auto.
  exists (proc_par (proc_new t P3) P4').
  simpl; split.
  rewrite <- EQ1. auto.
  intros. apply notin_union. auto.
  apply NI; auto.
Qed.

Lemma proc_eq1_trans2 : forall (Y:atom) P i Q,
  proc_eq1 Q (open_cp_rec i Y P) ->
  exists Q', Q = (open_cp_rec i Y Q') /\ (forall Z, (Z `notin` (fv_cp P) -> Z `notin` fv_cp Q')).
Proof.
  intros Y P i Q PEQ.
  remember (open_cp_rec i Y P) as P1.
  generalize dependent i. generalize dependent P. generalize dependent Y.
  (proc_eq1_cases (induction PEQ) Case); intros Y P i EQ; destruct P; simpl in *; inversion EQ; subst; auto.

  Case "proc_eq1_parl".
  destruct (IHPEQ Y P3 i) as [Q1' [EQ1 NI]]; auto.
  subst.
  exists (proc_par Q1' P4); simpl; split; auto.

  Case "proc_eq1_new".
  pick fresh X.
  lapply (H0 X); intros; auto.
  destruct (H1 Y (open_cp_rec 0 X P) (S i)) as [Q1' [EQ1 NI]]; auto.
  unfold open_cp. rewrite open_cp_open_cp_comm; auto.
  unfold open_cp in EQ1.
  exists (proc_new t (close_cp_rec 0 X Q1')).
  simpl; split. rewrite <- close_cp_open_cp_comm; auto.
  rewrite <- EQ1. rewrite close_open_cp_rec; auto.
  intros.
  destruct (Z === X). subst.
  apply fv_close_cp_aux.
  apply notin_close_cp; auto.  apply NI; auto.
  apply fv_cp_notin_open; auto.

  Case "proc_eq1_comm".
  exists (proc_par P4 P3); split; simpl; auto. 

  Case "proc_eq1_assoc".
  destruct P5; simpl in H1; inversion H1; subst.
  exists (proc_par (proc_par P4 P5_1) P5_2);
  simpl; split; auto.

  Case "proc_eq1_swap".
  pick fresh X.
  pick fresh Z.
  lapply (H X Z); intros; auto.
  lapply H0; intros; auto.
  unfold open_cp in H1.
  destruct P; simpl in H2; inversion H2; subst; auto. clear H2. clear EQ.
  exists (proc_new t0 (close_cp_rec 0 Z (proc_new t (close_cp_rec 0 X (open_cp_rec 0 Z (open_cp_rec 1 X P)))))). 
  simpl. split.
  rewrite <- close_cp_open_cp_comm; auto.
  rewrite <- close_cp_open_cp_comm; auto.
  rewrite <- (open_cp_open_cp_comm (open_cp_rec 1 X P)); auto.
  rewrite <- (open_cp_open_cp_comm P); auto.
  rewrite <- H1.
  rewrite close_open_cp_rec; auto.
  rewrite close_open_cp_rec; auto.
  apply fv_cp_notin_open; auto.

  intros. 
  destruct (Z0 === Z). subst.
    apply fv_close_cp_aux.
  apply notin_close_cp. 
  destruct (Z0 === X).  subst.
    apply fv_close_cp_aux.
  apply notin_close_cp. apply fv_cp_notin_open; auto.
  apply fv_cp_notin_open; auto.

  Case "proc_eq1_extrude".
  destruct P3; simpl in H1; inversion H1; subst. simpl in EQ.
  exists (proc_new t (proc_par P3 (close_cp_rec (S i) Y (open_cp_rec i Y P4)))).
  simpl; split. simpl in EQ.
  rewrite open_close_cp_rec; auto.

  intros. apply notin_union. auto.
  destruct (Z === Y).
  subst.
  apply fv_close_cp_aux; auto.
  apply notin_close_cp.
  apply fv_cp_notin_open; auto.
Qed.

Lemma proc_eqm_rename: forall P Q (X Y:atom) i,
  Y `notin` union (fv_cp P) (fv_cp Q) ->
  X `notin` union (fv_cp P) (fv_cp Q) ->
  proc_eqm (open_cp_rec i Y P) (open_cp_rec i Y Q) ->
  proc_eqm (open_cp_rec i X P) (open_cp_rec i X Q).
Proof.
  intros P Q X Y i NI1 NI2 EQM.
  remember (open_cp_rec i Y P) as P1.
  remember (open_cp_rec i Y Q) as Q1.
  generalize dependent Q. generalize dependent P. generalize dependent i.
  induction EQM; intros i Px EQ1 Qx NI1 NI2 EQ2; simpl in *; subst; auto.
  rewrite (open_cp_aux_inj i Y Px Qx); auto.

  destruct (proc_eq1_trans Y Px i P2) as [P2' [EQ2 NI3]]; auto.
  subst.
  apply (proc_eqm_left _ (open_cp_rec i X P2')); auto.
  apply (proc_eq1_rename _ _ X Y); auto.

  destruct (proc_eq1_trans2 Y Px i P2) as [P2' [EQ2 NI3]]; auto.
  subst.
  apply (proc_eqm_right _ (open_cp_rec i X P2')); auto.
  apply (proc_eq1_rename _ _ X Y); auto.
Qed.
  
Lemma proc_eqm_new : forall L P1 P1' T,
  (forall X, X `notin` L -> proc_eqm (open_cp P1 X) (open_cp P1' X)) ->
  process (proc_new T P1) ->
  proc_eqm (proc_new T P1) (proc_new T P1').
Proof.
  intros L P1 P1' T PEQM PROC.
  pick fresh X.
  lapply (PEQM X); try fsetdec; intros EQ.
  remember (open_cp P1 X) as P11.
  remember (open_cp P1' X) as P11'.
  generalize dependent P1. generalize dependent P1'. generalize dependent X.
  generalize dependent L.
  (proc_eqm_cases (induction EQ) Case); intros L X Px' EQ1 Px EQH PR NI EQ2; auto.
  
  Case "proc_eqm_refl".
  assert (Px = Px').
    apply (open_cp_inj X). fsetdec. subst. auto.
  subst. auto.
 
  Case "proc_eqm_left".
  subst.
  assert (exists Q, P2 = open_cp_rec 0 X Q /\ (forall Z, (Z `notin` (fv_cp Px) -> Z `notin` fv_cp Q))).
  apply proc_eq1_trans. unfold open_cp in H. apply H.
  destruct H0 as [Q [EQ2 NI2]].
  subst P2.
  apply (proc_eqm_left (proc_new T Px) (proc_new T Q)).
  apply (proc_eq1_new (union L (union (fv_cp Px) (union (fv_cp Px') (singleton X))))).
  intros.
  unfold open_cp.
  apply (proc_eq1_rename Px Q X0 X 0); auto.
  eapply (IHEQ (union L (union (fv_cp Px) (fv_cp Px')))); eauto.
  intros.  
  unfold open_cp.
  apply (proc_eqm_rename Q Px' X0 X). 
  apply notin_union. apply NI2. fsetdec. fsetdec.
  apply notin_union. apply NI2. fsetdec. fsetdec. 
  auto.
  
  apply (process_new (union L (union (fv_cp Px) (fv_cp Px')))); auto.
  intros.
  unfold open_cp in *. 
  assert ((process (open_cp_rec 0 X Px) -> process (open_cp_rec 0 X Q)) /\
          (process (open_cp_rec 0 X Q) -> process (open_cp_rec 0 X Px))).
  apply proc_eq1_regular. apply H.
  apply (process_rename Q 0 X X0). 
  destruct H1. apply H1.
  inversion PR. subst. unfold open_cp in H6.
  pick fresh Z. lapply (H6 Z). intros.
  apply (process_rename Px 0 Z X). auto. fsetdec.

  Case "proc_eqm_right".
  subst. 
  assert (exists Q, P2 = open_cp_rec 0 X Q /\ (forall Z, (Z `notin` (fv_cp Px) -> Z `notin` fv_cp Q))).
  apply proc_eq1_trans2. unfold open_cp in H. apply H.
  destruct H0 as [Q [EQ2 NI2]].
  subst P2.
  apply (proc_eqm_right (proc_new T Px) (proc_new T Q)).
  apply (proc_eq1_new (union L (union (fv_cp Px) (union (fv_cp Px') (singleton X))))).
  intros.
  unfold open_cp.
  apply (proc_eq1_rename Q Px X0 X 0); auto.
  eapply (IHEQ (union L (union (fv_cp Px) (fv_cp Px')))); eauto.
  intros.  
  unfold open_cp.
  apply (proc_eqm_rename Q Px' X0 X). 
  apply notin_union. apply NI2. fsetdec. fsetdec.
  apply notin_union. apply NI2. fsetdec. fsetdec. 
  auto.
  
  apply (process_new (union L (union (fv_cp Px) (fv_cp Px')))); auto.
  intros.
  unfold open_cp in *. 
  assert ((process (open_cp_rec 0 X Q) -> process (open_cp_rec 0 X Px)) /\
          (process (open_cp_rec 0 X Px) -> process (open_cp_rec 0 X Q))).
  apply proc_eq1_regular. apply H.
  apply (process_rename Q 0 X X0). 
  destruct H1. apply H2.
  inversion PR. subst. unfold open_cp in H6.
  pick fresh Z. lapply (H6 Z). intros.
  apply (process_rename Px 0 Z X). auto. fsetdec.
Qed.

Lemma proc_eq_fv : forall P1 P2,
  proc_eq P1 P2 -> forall X, (X `in` fv_cp P1) -> (X `in` fv_cp P2) /\
                             (X `in` fv_cp P2) -> (X `in` fv_cp P1).
Proof.
  induction P1; auto.
Qed.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop.opt" ***
*** coq-prog-args: ("-impredicative-set" "-emacs-U" "-I" "../../../metatheory") ***
*** End: ***
 *)
