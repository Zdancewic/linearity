(**  Authors: Steve Zdancewic and Karl Mazurak. *)

Require Export LinF_Soundness.
Require Import Omega.
Require Import Tactics.

(* Decidability results: *)
Lemma eq_bnd_dec: forall (a b:binding), {a = b}+{~a=b}.
Proof.
  decide equality. apply eq_kn_dec. apply eq_typ_dec.
Qed.

Lemma eq_binding_dec: forall (x y:(atom * binding)%type), {x = y}+{~x = y}.
Proof.
  decide equality. apply eq_bnd_dec.
Qed.

Lemma binds_dec: forall x b (E:env),
  {binds x b E} + {~binds x b E}.
Proof.
  intros. unfold binds. apply List.In_dec.
  decide equality.
  apply eq_bnd_dec.
Qed.

Lemma wf_typ_rename : forall G T (x y:atom) K1 K2, 
  uniq G ->
  y `notin` (singleton x `union` fv_tt T `union` dom G)  ->
  x `notin` (fv_tt T `union` dom G) ->
  wf_typ ([(x, bind_kn K1)] ++ G) (open_tt T x) K2 ->
  wf_typ ([(y, bind_kn K1)] ++ G) (open_tt T y) K2.
Proof.
  intros. 
  rewrite (subst_tt_intro x).
  rewrite_env (nil ++ [(y, bind_kn K1)] ++ G).
  assert (nil = map (subst_tb x y) nil).
  simpl. auto.
  rewrite H3.
  eapply wf_typ_subst_tb. simpl_env. 
  eapply wf_typ_weakening. eauto. 
    simpl. apply uniq_cons; auto. simpl. 
  apply wf_typ_var. apply uniq_cons. auto. solve_notin.
  rewrite_env ([(y, bind_kn K1)] ++ G).
  apply binds_app_l. apply binds_one; auto. solve_notin.
Qed.

Lemma wf_all_exists : forall T (x:atom) K1 G K2,
  uniq G ->
  x `notin` (fv_tt T `union` dom G) ->
  wf_typ ([(x, bind_kn K1)] ++ G) (open_tt T x) K2 ->
  wf_typ G (typ_all K1 T) K2.
Proof.
  intros.
  pick fresh y and apply wf_typ_all.
  apply (wf_typ_rename G T x). auto. solve_notin. auto. auto.
Qed.

Lemma wf_typ_dec: forall G T K,
  uniq G ->
  type T ->
  (wf_typ G T K) \/ (~wf_typ G T K).
Proof.
  intros G T K Uniq Hyp. generalize dependent G. generalize dependent K.
  induction Hyp; intros K0 G Uniq; auto.

  Case "fvar".
    destruct (binds_dec X (bind_kn K0) G).
    left. apply wf_typ_var; auto. destruct K0. 
       destruct (binds_dec X (bind_kn kn_nonlin) G).
       left. apply wf_typ_sub. apply wf_typ_var; auto.
       right. unfold not; intros. inversion H. apply n; auto. inversion H0. apply n0; auto.
       right. unfold not; intros. inversion H. apply n; auto.

  Case "arrow".
    destruct (eq_kn_dec K0 K). subst.
    destruct (IHHyp1 kn_lin G Uniq); destruct (IHHyp1 kn_nonlin G Uniq); 
    destruct (IHHyp2 kn_lin G Uniq); destruct (IHHyp2 kn_nonlin G Uniq); 
    try eapply wf_typ_arrow; eauto.
      right. unfold not; intros. inversion H3. subst. 
         destruct K2. apply H1; auto. apply H2; auto. inversion H4.
      right. unfold not; intros. inversion H3. subst. 
         destruct K2. apply H1; auto. apply H2; auto. inversion H4.
      right. unfold not; intros. inversion H3. subst. 
         destruct K1. apply H; auto. apply H0; auto. inversion H4.
      right. unfold not; intros. inversion H3. subst. 
         destruct K1. apply H; auto. apply H0; auto. inversion H4.
      right. unfold not; intros. inversion H3. subst. 
         destruct K1. apply H; auto. apply H0; auto. inversion H4.
      destruct K. destruct K0. unfold not in n. assert False. apply n; auto. tauto.
        right. unfold not; intros. inversion H. 

    destruct (IHHyp1 kn_lin G Uniq); destruct (IHHyp1 kn_nonlin G Uniq); 
    destruct (IHHyp2 kn_lin G Uniq); destruct (IHHyp2 kn_nonlin G Uniq);
    try (left; destruct K0;[ apply wf_typ_sub| ]; eapply wf_typ_arrow; eauto; 
    try (assert False; apply n; auto); tauto).
      right. unfold not; intros. inversion H3. subst. apply n; auto.  
        subst.  inversion H4.  subst. destruct K2. apply H1. auto. apply H2; auto.
      right. unfold not; intros. inversion H3. subst. apply n; auto.  
        subst.  inversion H4.  subst. destruct K2. apply H1. auto. apply H2; auto.
      right. unfold not; intros. inversion H3. subst. apply n; auto.  
        subst.  inversion H4.  subst. destruct K2. apply H1. auto. apply H2; auto.
      right. unfold not; intros. inversion H3. subst. apply n; auto.  
        subst.  inversion H4.  subst. destruct K1. apply H. auto. apply H0; auto.
      right. unfold not; intros. inversion H3. subst. apply n; auto.  
        subst.  inversion H4.  subst. destruct K1. apply H. auto. apply H0; auto.
      right. unfold not; intros. inversion H3. subst. apply n; auto.  
        subst.  inversion H4.  subst. destruct K1. apply H. auto. apply H0; auto.
      right. unfold not; intros. inversion H3. subst. apply n; auto.  
        subst.  inversion H4.  subst. destruct K1. apply H. auto. apply H0; auto.

  Case "all". 
      pick fresh y.
      assert  (FR: y `notin` L).
      solve_notin.
      destruct (H0 y FR K0 ([(y, bind_kn K)] ++ G)). 
      simpl. apply uniq_cons. auto. solve_notin.
      left. apply (wf_all_exists T2 y). auto. solve_notin. auto. 
      right. unfold not. intros. inversion H2. subst. 
      pick fresh z. lapply (H7 z). intros. 
      apply H1. apply (wf_typ_rename G T2 z y). auto. solve_notin. 
        solve_notin. auto. solve_notin.
      inversion H3. subst.
      pick fresh z. lapply (H11 z). intros. 
      apply H1. apply (wf_typ_rename G T2 z y). auto. solve_notin. 
        solve_notin. auto. solve_notin.

  Case "with".
    destruct K0.
      destruct (IHHyp1 kn_lin G Uniq); destruct (IHHyp1 kn_nonlin G Uniq); 
      destruct (IHHyp2 kn_lin G Uniq); destruct (IHHyp2 kn_nonlin G Uniq); 
      try eapply wf_typ_with; eauto.
        right. unfold not; intros. inversion H3. subst. 
         destruct K2. apply H1; auto. apply H2; auto. inversion H4.
        right. unfold not; intros. inversion H3. subst. 
         destruct K2. apply H1; auto. apply H2; auto. inversion H4.
        right. unfold not; intros. inversion H3. subst. 
         destruct K1. apply H; auto. apply H0; auto. inversion H4.
        right. unfold not; intros. inversion H3. subst. 
         destruct K1. apply H; auto. apply H0; auto. inversion H4.
        right. unfold not; intros. inversion H3. subst. 
         destruct K1. apply H; auto. apply H0; auto. inversion H4.

      right. intro J. inversion J.
Qed.

Lemma wf_env_inversion: forall E2 E1 x T,
  wf_env (E2 ++ [(x, bind_typ T)] ++ E1) ->
  wf_typ E1 T kn_nonlin.
Proof.
  induction E2; intros E1 x T WF.
  simpl_env in WF. inversion WF.  auto.
  eapply IHE2. rewrite_env ([a] ++ E2 ++ [(x, bind_typ T)] ++ E1) in WF.
  inversion WF. simpl_env in H1. apply H1. apply H1.
Qed.

Lemma fv_tt_in_open: forall X Y T n,
  X `in` fv_tt T -> X `in` fv_tt (open_tt_rec n (typ_fvar Y) T).
Proof.
  intros X Y T.
  induction T; intros; unfold open_tt in *; simpl in *; try (simpl; subst; fsetdec; auto).
  assert (X `in` (fv_tt T1) \/ X `in` (fv_tt T2)).
    fsetdec.
  destruct H0. 
    assert (X `in` (fv_tt (open_tt_rec n Y T1))). 
      apply IHT1; auto. 
    fsetdec.
    assert (X `in` fv_tt (open_tt_rec n Y T2)). 
      apply IHT2; auto. 
    fsetdec. 
  apply IHT; auto.
  assert (X `in` (fv_tt T1) \/ X `in` (fv_tt T2)).
    fsetdec.
  destruct H0. 
    assert (X `in` (fv_tt (open_tt_rec n Y T1))). 
      apply IHT1; auto. 
    fsetdec.
    assert (X `in` fv_tt (open_tt_rec n Y T2)). 
      apply IHT2; auto. 
    fsetdec. 
Qed.

Lemma fv_tt_in_wf_typ: forall E T K,
  wf_typ E T K ->
  (forall x, x `in` fv_tt T -> x `in` dom E).
Proof.
  intros E T K H.
  induction H; intros.
  Case "var".
  simpl in H1. assert (x = X). fsetdec.
  subst x. eapply binds_In. apply H0.
  Case "arrow". 
  simpl in H1. assert ((x `in` fv_tt T1) \/ (x `in` fv_tt T2)).
  fsetdec. destruct H2. apply IHwf_typ1; auto. apply IHwf_typ2; auto.
  Case "all".
  pick fresh Y.  
  lapply (H0 Y). intros.  lapply (H2 x). intros.
  destruct (x == Y).
    subst. assert False. apply Fr. fsetdec. tauto.
    rewrite dom_app in H3. simpl in H3. fsetdec. 
    simpl in H1. unfold open_tt.  apply fv_tt_in_open. auto.
    solve_notin.
  Case "with". 
  simpl in H1. assert ((x `in` fv_tt T1) \/ (x `in` fv_tt T2)).
  fsetdec. destruct H2. apply IHwf_typ1; auto. apply IHwf_typ2; auto.
  Case "sub".
    apply IHwf_typ; auto.
Qed.

Lemma uniq_from_wf_typ:  forall E T K,
  wf_typ E T K ->
  uniq E
.
Proof.
  intros E T K Hyp.
  induction Hyp; auto.
  pick fresh Y. lapply (H0 Y). intros. eapply uniq_app_2; auto. eauto.
Qed.

Lemma disjoint_dom: forall E1 E2 E3 T K1 K2,
  wf_typ (E1 ++ E2 ++ E3) T K1 ->
  wf_typ (E1 ++ E3) T K2 ->
  (forall x, x `in` (dom E2) -> x `notin` fv_tt T).
Proof.
  intros E1 E2 E3 T K1 K2 H1 H2.
  intros.
  assert (x `in` fv_tt T -> x `in` dom (E1 ++ E2 ++ E3)).
  intros.  eapply fv_tt_in_wf_typ; eauto.
  rewrite dom_app in H0. rewrite dom_app in H0. unfold not. intros. 
  assert (uniq (E1 ++ E2 ++ E3)). eapply uniq_from_wf_typ; eauto.
  lapply H0. intros. assert (x `in` dom E1 \/ x `in` dom E2 \/ x `in` dom E3).
  fsetdec. destruct H6. assert (x `notin` dom E2). solve_uniq.
  apply H7; auto.
  destruct H6.
  assert (x `notin` dom E1).  solve_uniq.
  assert (x `in` dom (E1 ++ E3)). eapply fv_tt_in_wf_typ with (T:=T) (K:=K2); auto.
  assert (x `notin` dom E3).  solve_uniq. 
  rewrite dom_app in H8. fsetdec. 

  assert (x `notin` dom E3).  solve_uniq. auto.

  auto.
Qed.
  
Lemma wf_typ_strengthening_sub: forall F E1 E2 T K,
  wf_typ (E2 ++ F ++ E1) T K ->
  (forall x, x `in` dom F -> x `notin` fv_tt T) ->
  wf_typ (E2 ++ E1) T K.
Proof.
  induction F; intros.
  simpl in H. auto.
  apply IHF. destruct a. destruct b. 
    eapply (wf_typ_strengthening_typ (F ++ E1) E2 a k). 
    simpl. rewrite_env (E2 ++ ((a, bind_kn k) :: F) ++ E1). apply H.
    apply H0. simpl. fsetdec. 
    eapply (wf_typ_strengthening (F ++ E1) E2 a t). apply H. 
    intros. lapply (H0 x). intros. auto. rewrite_env ([a] ++ F). rewrite dom_app. fsetdec.
Qed.

Lemma wf_typ_strengthening_head:  forall E1 E2 T K1 K2,
  wf_typ (E1 ++ E2) T K1 ->
  wf_typ E1 T K2 ->
  wf_typ E1 T K1.
Proof.
  intros E1 E2. generalize dependent E1.
  induction E2; intros E1 T K1 K2 H1 H2.
  simpl_env in H1. auto.
  destruct a.  assert (forall x, x `in` dom ((a,b) :: E2) -> x `notin` fv_tt T).
  intros. eapply disjoint_dom. rewrite_env (E1 ++ ((a,b)::E2) ++ nil) in H1. apply H1. 
  simpl_env. apply H2. auto. 
  eapply IHE2. eapply wf_typ_strengthening_sub. rewrite_env (E1 ++ [(a,b)] ++ E2) in H1.
  apply H1. intros. apply H. simpl. simpl in H0. fsetdec. apply H2.
Qed.

Lemma wf_typ_strengthening_sub2: forall E1 E2 E3 T K1 K2,
  wf_typ (E1 ++ E2 ++ E3) T K1 ->
  wf_typ (E1 ++ E3) T K2 ->
  wf_typ (E1 ++ E3) T K1.
Proof.
  intros.
  eapply wf_typ_strengthening_sub. apply H.
  intros. eapply disjoint_dom.
  eapply H. eapply H0. auto.
Qed.

Lemma not_wf_env: forall E1 E2 E3 x T U,
  ~ wf_env (E1 ++ [(x, bind_typ T)] ++ E2 ++ [(x, bind_typ U)] ++ E3).
Proof.
  intros. unfold not. intros.
  assert (uniq (E1 ++ [(x, bind_typ T)] ++ E2 ++ [(x, bind_typ U)] ++ E3)).
  apply uniq_from_wf_env; auto.
  assert (~ x `in` dom ([(x, bind_typ U)] ++ E3)).
  eapply fresh_mid_tail_In.
  rewrite_env  (E1 ++ ([(x, bind_typ T)] ++ E2) ++ [(x, bind_typ U)] ++ E3) in H0.
  apply H0.
  rewrite dom_app. simpl. fsetdec.
  apply H1. 
  rewrite dom_app. simpl. fsetdec.
Qed.

Lemma notin_fv_tail: forall F X T E K KT,
 wf_env (F ++ [(X, bind_kn K)] ++ E) ->
 wf_typ E T KT ->
 X `notin` fv_tt T.
Proof.
  intros.
  assert (forall Y, Y `in` fv_tt T -> Y `in` dom E).  intros.
  eapply fv_tt_in_wf_typ. apply H0.  auto.
  unfold not. intros.
  lapply (H1 X). intros. 
  assert (uniq (F ++ [(X, bind_kn K)] ++ E)). auto. 
  assert (uniq (E ++ F ++ [(X, bind_kn K)])). apply uniq_commute. simpl_env. auto.
  assert (X `notin` dom (F ++ [(X, bind_kn K)])).
  eapply fresh_tail_In. apply H5. auto. rewrite dom_app in H6. simpl in H6. fsetdec. auto.
Qed.

Lemma in_fv_tt_dec: forall X T,
 {X `in` fv_tt T}+{~ X `in` fv_tt T}.
Proof.
  intros X T.
  induction T; simpl.
    right. fsetdec.
    destruct (X == a). 
      subst. left. simpl. fsetdec. 
      right. simpl. fsetdec.
    destruct IHT1. 
      left. fsetdec.
      destruct IHT2. 
        left. fsetdec. 
        right. fsetdec.
    destruct IHT; simpl; auto.
    destruct IHT1. 
      left. fsetdec.
      destruct IHT2. 
        left. fsetdec. 
        right. fsetdec.
Qed.

Lemma wf_lenv_uniq_lin: forall G D,
  wf_lenv G D ->
  uniq D.
Proof.
  induction D; auto.
  intros. destruct a. apply uniq_cons.
  inversion H. apply IHD; auto.
  inversion H; auto.
Qed.

Lemma map_subst_tb_id_tail : forall E G Z P,
  wf_env (E ++ G) ->
  Z `notin` dom (E ++ G) ->
  (E ++ G) = (map (subst_tb Z P) E ++ G).
Proof with auto.
  intros.
  induction E; simpl_env in *.
  auto.
  simpl. destruct a. destruct b; simpl in *.
  rewrite IHE. auto. eapply wf_env_strengthening_tail. simpl_env in H. apply H.
  fsetdec.
  rewrite <- subst_tt_fresh. rewrite IHE; auto.
  eapply wf_env_strengthening_tail. simpl_env in H. apply H.
  inversion H. subst. eapply notin_fv_wf. apply H5. rewrite dom_app.
  fsetdec.
Qed.

Lemma uniq_from_lenv_split: forall G D1 D2 D3,
  lenv_split G D1 D2 D3 ->
  uniq D3.
Proof.
  intros.
  induction H; auto.
Qed.

Lemma open_tt_type: forall T U,
  type T ->
  type (open_tt T U).
Proof.
  intros.  unfold open_tt. rewrite <- open_tt_rec_type. auto. auto.
Qed.

Lemma open_te_expr: forall e1 T,
  expr e1 ->
  expr (open_te e1 T).
Proof.
  intros. unfold open_te. rewrite <- open_te_rec_expr.
  auto. auto.
Qed.


(* The following lemma is false:
   counterexample: D1 = [] D2 = [x,y] D3 = [x,y]
                   DL = x  DR = y    
   it is not the case that lenv_split E [] [x,y] [y,x] 

Lemma lenv_split_exchange: forall E D1 D2 DL DR D3,
  lenv_split E D1 D2 D3 ->
  lenv_split E DL DR D3 ->
  lenv_split E D1 D2 (DR ++ DL).
Proof.
  intros E D1 D2 DL DR D3 S1.
  generalize dependent DR. generalize dependent DL.
  induction S1; intros DL DR S2.
  Case "empty".
    inversion S2; subst. simpl_env. apply lenv_split_empty.
    auto.
  Case "left".
    inversion S2; subst. 
*)

Lemma wf_lenv_trivial_split: forall E D,
  wf_lenv E D ->
  lenv_split E lempty D D.
Proof.
  intros E D.
  induction D; intros.
  Case "empty".
    apply lenv_split_empty.
    inversion H; auto.
  Case "cons".
    destruct a. simpl_env in *. 
    inversion H.
    apply lenv_split_right; auto.
Qed.

(*
Lemma lenv_split_exchange2: forall E D3M D1L D1M D2L D2M D3L D3R x TX,
  lenv_split E D1L D2L D3L ->
  lenv_split E D1M D2M (D3M ++ D3R) ->
  lenv_split E (D1L ++ [(x, lbind_typ TX)] ++ D1M) 
               (D2L ++ D2M) 
               (D3L ++ [(x, lbind_typ TX)] ++ D3M ++ D3R) ->
  lenv_split E (D1L ++ D1M ++ [(x, lbind_typ TX)]) 
               (D2L ++ D2M) 
               (D3L ++ D3M ++ [(x, lbind_typ TX)] ++ D3R).
Proof. 
  intros E D3M.
  induction D3M; intros; simpl_env in *.
*)  

Lemma disjoint_split_left: forall G D1 D2 D3,
  lenv_split G D1 D2 D3 ->
  disjoint G D1.
Proof.
  intros.
  apply wf_lenv_disjoint.
  eapply wf_lenv_split_left; eauto.
Qed.
  
Lemma disjoint_split_right: forall G D1 D2 D3,
  lenv_split G D1 D2 D3 ->
  disjoint G D2.
Proof.
  intros.
  apply wf_lenv_disjoint.
  eapply wf_lenv_split_right; eauto.
Qed.  
  
Lemma lenv_split_exchange_left: forall E D1L D1M D2L D2M D3L D3M x TX,
  lenv_split E D1L D2L D3L ->
  lenv_split E D1M D2M D3M ->
  lenv_split E (D1L ++ [(x, lbind_typ TX)] ++ D1M) 
               (D2L ++ D2M) 
               (D3L ++ [(x, lbind_typ TX)] ++ D3M) ->
  lenv_split E (D1L ++ D1M ++ [(x, lbind_typ TX)]) 
               (D2L ++ D2M) 
               (D3L ++ D3M ++ [(x, lbind_typ TX)]).
Proof.
  intros E D1L D1M D2L D2M D3L D3M x TX S1.
  intros S2 S3.
  remember (D1L ++ [(x, lbind_typ TX)] ++ D1M) as D1.
  remember (D2L ++ D2M) as D2.
  remember (D3L ++ [(x, lbind_typ TX)] ++ D3M) as D3.
  generalize dependent D1M. generalize dependent D1L.
  generalize dependent D2M. generalize dependent D2L.
  generalize dependent D3M. generalize dependent D3L.
  induction S3; intros D3L D3M EQ3 D2L D2M EQ2 D1L SL D1M SM EQ1; simpl_env in *.
  Case "empty".
    destruct D3L; destruct D3M; inversion EQ3.
  Case "left".
    subst.  
    destruct D1L; inversion EQ1; subst; simpl_env in *.
    destruct D3L; inversion EQ3; subst; simpl_env in *.
    inversion SL. subst.
    simpl_env in *.
    rewrite_env (D1M ++ [(x, lbind_typ TX)] ++ nil).
    rewrite_env (D2M ++ nil).
    rewrite_env (D3M ++ [(x, lbind_typ TX)] ++ nil).
    apply lenv_split_weakening_left. simpl_env. auto. auto. auto.
    eapply wf_lenv_lin_weakening. auto. simpl_env. 
    eapply wf_lenv_split. apply SM. auto. simpl_env. fsetdec.
    assert False. fsetdec. tauto.
    destruct D3L; inversion EQ3; subst; simpl_env in *.
    rewrite (dom_lenv_split E (D1L ++ [(x, lbind_typ TX)] ++ D1M) (D2L ++ D2M) D3M) in H0.
    simpl_env in H0. assert False. fsetdec. tauto.
    auto.
    apply lenv_split_left; auto. eapply IHS3; auto.
    inversion SL; auto. subst. 
    rewrite (dom_lenv_split E ([(x0, lbind_typ T)] ++ D1L) D2 D3L) in H10; auto.
    simpl in H10. assert False. fsetdec. tauto.
  Case "right".
    destruct D2L; inversion EQ2; subst; simpl_env in *.
    destruct D3L; inversion EQ3; subst; simpl_env in *.
    rewrite (dom_lenv_split E D1M ([(x, lbind_typ TX)] ++ D2) D3M) in H0.
    simpl in H0. assert False. fsetdec. tauto.
    rewrite (dom_lenv_split E (D1L ++ [(x, lbind_typ TX)] ++ D1M) D2 D3M) in H0.
    simpl in H0. assert False. rewrite dom_app in H0. simpl in H0. fsetdec. tauto.
    auto.
    rewrite (dom_lenv_split E D1M ([(x0, lbind_typ T)] ++ D2) D3M) in H0.
    simpl in H0. assert False. fsetdec. tauto. auto.
    destruct D3L; inversion EQ3; subst; simpl_env in *.
    inversion SL.
    apply lenv_split_right; auto. eapply IHS3; auto.
    inversion SL; auto. subst.
    rewrite (dom_lenv_split E D1 ([(x0, lbind_typ T)] ++ D2L) D3L) in H10.
    simpl in H10. assert False. fsetdec. tauto. auto.
Qed.
      
Lemma lenv_split_join: forall E D1 D2 D3 F1 F2 F3,
  lenv_split E D1 D2 D3 ->
  lenv_split E F1 F2 F3 ->
  wf_lenv E (D3 ++ F3) ->
  lenv_split E (D1 ++ F1) (D2 ++ F2) (D3 ++ F3).
Proof.
  intros E D1 D2 D3 F1 F2 F3 S1.
  induction S1; intros S2 WFL; auto.
  Case "left".
    simpl_env in *.
    apply lenv_split_left; auto. apply IHS1; auto.
    inversion WFL; auto. inversion WFL; auto.
  Case "right".
    simpl_env in *.
    apply lenv_split_right; auto. apply IHS1; auto.
    inversion WFL; auto. inversion WFL; auto.
Qed.

Lemma wf_lenv_exchange: forall E x TX DL DR,
  wf_lenv E ([(x, lbind_typ TX)] ++ DL ++ DR) ->
  wf_lenv E (DL ++ [(x, lbind_typ TX)] ++ DR).
Proof.
  intros.
  inversion H.
  apply wf_lenv_lin_weakening; auto.
Qed.

Lemma wf_lenv_exchange_mid: forall E x TX DL DM DR,
  wf_lenv E (DL ++ [(x, lbind_typ TX)] ++ DM ++ DR) ->
  wf_lenv E (DL ++ DM ++ [(x, lbind_typ TX)] ++ DR).
Proof.
  induction DL; intros.
  simpl_env in *. apply wf_lenv_exchange; auto.
  simpl_env in *.
  destruct a. simpl_env in *.
  inversion H.
  apply wf_lenv_typ. apply IHDL; auto. auto.
  repeat rewrite dom_app in *. simpl in *. 
  rewrite dom_app in H6. fsetdec.
  auto.
Qed.

Lemma wf_lenv_from_lenv_split_left: forall E D1 D2 DL DR,
  lenv_split E D1 D2 (DL ++ DR) ->
  wf_lenv E DL.
Proof.
  intros. eapply wf_lenv_lin_strengthening.
  rewrite_env (nil ++ DL ++ DR) in H.
  eapply wf_lenv_split. apply H.
Qed.

Lemma wf_lenv_from_lenv_split_right: forall E D1 D2 DL DR,
  lenv_split E D1 D2 (DL ++ DR) ->
  wf_lenv E DR.
Proof.
  intros. eapply wf_lenv_lin_strengthening.
  rewrite_env (DL ++ DR ++ nil) in H.
  eapply wf_lenv_split. apply H.
Qed.

Lemma typing_exchange: forall E D1 D2 D3 x TX e T,
  typing E (D1 ++ [(x, lbind_typ TX)] ++ D2 ++ D3) e T ->
  typing E (D1 ++ D2 ++ [(x, lbind_typ TX)] ++ D3) e T.
Proof.
  intros E D1 D2 D3 x TX e T TYP.
  remember (D1 ++ [(x, lbind_typ TX)] ++ D2 ++ D3) as D.
  generalize dependent D3. generalize dependent D2. generalize dependent D1.
  induction TYP; intros DL DM DR EQ; eauto.
  Case "var".
    destruct DL; simpl in EQ; inversion EQ.
  Case "lvar".
    destruct DL; simpl in EQ; inversion EQ; subst.
    destruct DM; simpl in EQ; inversion EQ; subst.
    simpl_env in *. apply typing_lvar. auto.
    destruct DL; simpl in EQ; inversion EQ.
  Case "abs".
    pick fresh y and apply typing_abs.
    auto. apply (H1 y); auto. 
    intros. subst D. lapply H2; intros; auto.
    destruct DL; inversion H4.
  Case "labs".
    pick fresh y and apply typing_labs.
    auto. 
    rewrite_env (([(y, lbind_typ T1)] ++ DL) ++ DM ++ [(x, lbind_typ TX)] ++ DR).
    apply (H1 y); auto.
    subst. simpl_env. auto.
    intros. subst D. lapply H2; intros; auto.
    destruct DL; destruct DM; inversion H4.
  Case "app".
    subst. 
    lapply (lenv_split_cases_mid E D1 D2 DL x TX (DM ++ DR)); auto.
    intros CASES.
    destruct CASES as [LEFT | RIGHT].
    destruct LEFT as [D1L [D1R [D2L [D2R [EQ1 [EQ2 [S1 S2]]]]]]].
    subst.
    lapply (lenv_split_cases_app E DM D1R D2R DR); auto.
    intros EX.
    destruct EX as [D1RM [D1RR [D2RM [D2RR [S3 [S4 [EQ1 EQ2]]]]]]].
    lapply (IHTYP1 D1L D1RM D1RR); auto.
    intros TYPE1.
    assert (lenv_split E (D1L ++ D1RM ++ [(x, lbind_typ TX)] ++ D1RR)
                         (D2L ++ D2RM ++ D2RR)
                         (DL  ++ DM ++ [(x, lbind_typ TX)] ++ DR)).
    apply lenv_split_join. auto.
    apply lenv_split_weakening_left. subst; auto. auto. auto.
    apply wf_lenv_exchange.
    eapply wf_lenv_from_lenv_split_right. apply H.
    apply wf_lenv_exchange_mid.
    eapply wf_lenv_split. apply H.
    apply (typing_app T1 K E 
            (D1L ++ D1RM ++ [(x, lbind_typ TX)] ++ D1RR) 
            (D2L ++ D2RM ++ D2RR) 
            (DL ++ DM ++ [(x, lbind_typ TX)] ++ DR)); auto.
    subst; auto. subst; auto.

    destruct RIGHT as [D1L [D1R [D2L [D2R [EQ1 [EQ2 [S1 S2]]]]]]].
    subst.
    lapply (lenv_split_cases_app E DM D1R D2R DR); auto.
    intros EX.
    destruct EX as [D1RM [D1RR [D2RM [D2RR [S3 [S4 [EQ1 EQ2]]]]]]].
    lapply (IHTYP2 D2L D2RM D2RR); auto.
    intros TYPE2.
    assert (lenv_split E (D1L ++ D1RM ++ D1RR)
                         (D2L ++ D2RM ++ [(x, lbind_typ TX)] ++ D2RR)
                         (DL  ++ DM ++ [(x, lbind_typ TX)] ++ DR)).
    apply lenv_split_join; auto.
    apply lenv_split_weakening_right; subst; auto.
    apply wf_lenv_exchange.
    eapply wf_lenv_from_lenv_split_right. apply H.
    apply wf_lenv_exchange_mid.
    eapply wf_lenv_split. apply H.
    apply (typing_app T1 K E 
            (D1L ++ D1RM ++ D1RR) 
            (D2L ++ D2RM ++ [(x, lbind_typ TX)] ++ D2RR) 
            (DL ++ DM ++ [(x, lbind_typ TX)] ++ DR)); auto.
    subst; auto. subst; auto.
    
  Case "tabs".
    pick fresh X and apply typing_tabs.
    auto. 
    apply (H1 X); auto.
Qed.

(*    
Lemma exchange: forall E D1 D2 e T,
  typing E (D1 ++ D2) e T ->
  typing E (D2 ++ D1) e T.  
Proof.
  intros E D1 D2 e T Typ.
  remember (D1 ++ D2) as D.
  generalize dependent D2. generalize dependent D1.
  induction Typ; intros DL DR EQ.
  Case "var".
    destruct DL; destruct DR; inversion EQ; subst; simpl_env in *. 
    apply typing_var; auto.
  Case "lvar".
    destruct DL; destruct DR; inversion EQ; subst; simpl_env in *.
    apply typing_lvar; auto.
    subst DL. simpl_env. apply typing_lvar; auto.
    destruct DL; inversion H2.
  Case "abs".
    pick fresh x and apply typing_abs.
    auto. apply (H1 x); auto. intros. subst. 
    lapply H2; auto; intros. 
    destruct DL; destruct DR; inversion H3. simpl_env. auto.
  Case "labs".
    pick fresh x and apply typing_labs.
    auto. rewrite_env (([(x, lbind_typ T1)] ++ DR) ++ DL).
    apply (H1 x); auto.

*)

(*
This lemma is false:

Lemma lenv_split_cases_left_tail: forall E DL D1 D2 DR,
  lenv_split E D1 D2 (DL ++ DR) ->
  exists D1L, exists D1R, exists D2L, exists D2R,
    lenv_split E D1L D1R DL /\
    lenv_split E D2L D2R DR /\
    D1L ++ D1R = D1 /\
    D2L ++ D2R = D2.

Counterexample: let DL = lempty and pick D1 <> lempty
  then D1L = D1R = lempty but D1L ++ D1R = lempty <> D1
*)    

(* This lemma is false:  
Lemma lenv_splice: forall E DL DR DX D1 D2,
  lenv_split E D1 D2 (DL ++ DR) ->
  lenv_split E DL DR DX ->
  lenv_split E D1 D2 DX.
Proof.
Counterexample: 
[x y] U [z w] =  [x z] ++ [y w]
[x z] U [y w] =  [y x] ++ [w z]
[x y] U [z w] <> [y x] ++ [w z]
*)


Lemma lenv_split_cases_left_tail: forall E D1 D2 D3 x T,
  lenv_split E ([(x, lbind_typ T)] ++ D1) D2 D3 ->
  exists DL, exists D2R, exists D3R,
    D2 = DL ++ D2R /\
    D3 = DL ++ [(x, lbind_typ T)] ++ D3R /\
    lenv_split E D1 D2R D3R.
Proof.
  intros E D1 D2 D3 x T S.
  remember ([(x, lbind_typ T)] ++ D1) as D0.
  generalize dependent D1.
  induction S; intros D1R EQ; simpl_env in *.
  Case "empty".
    inversion EQ.
  Case "left".
    inversion EQ; subst.
    exists lempty. exists D2. exists D3.
    simpl_env in *. repeat split; auto.
  Case "right".
    lapply (IHS D1R); intros; auto.
    destruct H2 as [DL [D2R [D3R [Q1 [Q2 S2]]]]].
    exists ([(x0, lbind_typ T0)] ++ DL).
    exists D2R.
    exists D3R.
    subst. simpl_env in *. repeat split; auto.
Qed.

Lemma lenv_split_cases_right_tail: forall E D1 D2 D3 x T,
  lenv_split E D1 ([(x, lbind_typ T)] ++ D2) D3 ->
  exists DL, exists D1R, exists D3R,
    D1 = DL ++ D1R /\
    D3 = DL ++ [(x, lbind_typ T)] ++ D3R /\
    lenv_split E D1R D2 D3R.
Proof.
  intros. 
  lapply (lenv_split_cases_left_tail E D2 D1 D3 x T).
  intros. 
  destruct H0 as [DL [D2R [D3R [Q1 [Q2 S2]]]]].
  exists DL. exists D2R. exists D3R.
  repeat split; auto.
  apply lenv_split_commute; auto.
  apply lenv_split_commute; auto.
Qed.

Lemma wf_env_weakening: forall E F G,
  wf_env (G ++ E) ->
  wf_env (F ++ E) ->
  uniq (G ++ F ++ E) ->
  wf_env (G ++ F ++ E).
Proof.
  intros E F G. 
  generalize dependent F.
  induction G; intros F H1 H2 Uniq.
  Case "empty".
    simpl_env. auto.
  rewrite_env ([a] ++ (G ++ E)) in H1.
  rewrite_env ([a] ++ (G ++ F ++ E)).
  rewrite_env ([a] ++ (G ++ F ++ E)) in Uniq.
  inversion H1.
  Case "kn".
    apply wf_env_kn. apply IHG. auto. auto. eapply uniq_app_2. 
    eauto. subst. inversion Uniq. auto.
  Case "typ".
    eapply wf_env_typ. apply IHG; auto. eapply uniq_app_2. 
    eauto. eapply wf_typ_weakening. eapply H4.
    eapply uniq_app_2. eauto. subst. inversion Uniq. auto.
Qed.

Lemma wf_env_weakening_tail: forall E F,
  wf_env E ->
  wf_env F ->
  uniq (F ++ E) ->
  wf_env (F ++ E).
Proof.
  intros E F.
  generalize dependent E.
  induction F; intros E WF1 WF2 Uniq.
  simpl. auto.
  inversion WF2. 
  rewrite_env ([(X, bind_kn K)] ++ F ++ E).
  eapply wf_env_kn. apply IHF; auto. rewrite_env ([a] ++ (F ++ E)) in Uniq. eapply uniq_app_2. eapply Uniq. subst a.
  inversion Uniq.  auto.
  rewrite_env ([(x, bind_typ T)] ++ F ++ E).
  eapply wf_env_typ. apply IHF; auto. rewrite_env ([a] ++ (F ++ E)) in Uniq. eapply uniq_app_2. eapply Uniq. 
  rewrite_env (F ++ E ++ nil). apply wf_typ_weakening. rewrite <- app_nil_end. eapply H2.
  rewrite <- app_nil_end. rewrite_env ([a] ++ (F ++ E)) in Uniq. eapply uniq_app_2. eapply Uniq. 
  subst a. inversion Uniq.  auto.
Qed.

Lemma open_kn: forall L K1 K2 E T,
  (forall (Y: atom), Y `notin` L -> wf_typ ([(Y, bind_kn K1)] ++ E) (open_tt T Y) K2) ->
  wf_typ E (typ_all K1 T) K2.
Proof.
  intros L K1 K2 E T H.
  induction T; pick fresh Z and apply wf_typ_all; 
    try solve [apply (H Z); auto].
Qed.

Lemma wf_typ_from_wf_lenv: forall x T E D1 D2,
  wf_lenv E (D1 ++ [(x, lbind_typ T)] ++ D2) ->
  wf_typ E T kn_lin.
Proof.
  intros x T E D1 D2 WFL.
  remember (D1 ++ [(x, lbind_typ T)] ++ D2) as D.
  generalize dependent D1.
  induction WFL; intros D1 EQ.
     assert False. eapply nil_eq_one_mid_false. eapply EQ. tauto.
  destruct D1; inversion EQ; subst.
    auto.
  apply (IHWFL D1); auto.
Qed.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../../../metatheory") ***
*** End: ***
 *)




