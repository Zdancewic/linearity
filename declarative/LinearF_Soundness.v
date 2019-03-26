(** Type-safety proofs for Fsub.

    Authors: Brian Aydemir and Arthur Charguéraud, with help from
    Aaron Bohannon, Jeffrey Vaughan, and Dimitrios Vytiniotis.

    In parentheses are given the label of the corresponding lemma in
    the appendix (informal proofs) of the POPLmark Challenge.

    Table of contents:
      - #<a href="##subtyping">Properties of subtyping</a>#
      - #<a href="##typing">Properties of typing</a>#
      - #<a href="##preservation">Preservation</a>#
      - #<a href="##progress">Progress</a># *)

Require Export LinearF_Lemmas.
Require Import Omega.
Require Import Tactics.

  
Lemma notin_open_tt_rec_fv : forall (Y X : atom) T n,
  X `notin` fv_tt T ->
  X <> Y ->
  X `notin` fv_tt (open_tt_rec n Y T).
Proof.
  intros. 
  generalize dependent n. generalize dependent X.
  induction T; simpl; intros X Nin Neq n0. 
    destruct (n0 === n); simpl; auto. 
  simpl; auto. 
  assert (X `notin` fv_tt (open_tt_rec n0 Y T1)). apply IHT1; auto.
  simpl in H. assert (X `notin` fv_tt T1). fsetdec.
  assert (X `notin` fv_tt (open_tt_rec n0 Y T2)). apply IHT2; auto.
  fsetdec.

  apply IHT. auto. auto.
Qed.
  
Lemma notin_open_tt_fv : forall (Y X : atom) T,
  X `notin` fv_tt T ->
  X <> Y ->
  X `notin` fv_tt (open_tt T Y).
Proof.
  intros. unfold open_tt. apply (notin_open_tt_rec_fv Y X T 0).
  auto. auto.
Qed.


Lemma wf_typ_strengthening2 : forall E F X K1 T K,
 wf_typ (F ++ [(X, bind_kn K1)] ++ E) T K ->
 X `notin` (fv_tt T) ->
 ok (F ++ E) ->
 wf_typ (F ++ E) T K.
Proof with simpl_env; eauto.
  intros E F X K1 T K H.
  remember (F ++ [(X, bind_kn K1)] ++ E) as G.
  generalize dependent F.
  induction H; intros F Heq Nin OK; subst...
  Case "wf_typ_var".
    binds_cases H0... simpl in Nin. assert False. apply Nin. fsetdec. tauto.
  Case "wf_typ_arrow".
    simpl in Nin. eapply wf_typ_arrow. eapply IHwf_typ1; eauto. 
    eapply IHwf_typ2; eauto.  
  Case "wf_typ_all".
    pick fresh Y and apply wf_typ_all.  
    rewrite <- concat_assoc.
    eapply H0... simpl in Nin. apply notin_open_tt_fv. auto. auto.
Qed.    


Lemma wf_typ_strengthening3: forall F E1 E2 T K,
  wf_typ (E2 ++ F ++ E1) T K ->
  (forall x, x `in` dom F -> x `notin` fv_tt T) ->
  wf_typ (E2 ++ E1) T K.
Proof.
  induction F; intros.
  simpl in H. auto.
  apply IHF. destruct a. destruct b. 
    eapply (wf_typ_strengthening2 (F ++ E1) E2 a k). 
    simpl. rewrite_env (E2 ++ ((a, bind_kn k) :: F) ++ E1). apply H.
    apply H0. simpl. fsetdec. eapply ok_remove_mid. rewrite_env (E2 ++ [(a, bind_kn k)] ++ F ++ E1) in H.
    eapply ok_from_wf_typ. apply H.
    eapply (wf_typ_strengthening (F ++ E1) E2 a t). apply H. 
    intros. lapply (H0 x). intros. auto. rewrite_env ([a] ++ F). rewrite dom_concat. fsetdec.
Qed.


Lemma fv_tt_in_open: forall X Y T n,
  X `in` fv_tt T -> X `in` fv_tt (open_tt_rec n (typ_fvar Y) T).
Proof.
  intros X Y T.
  induction T; intros; unfold open_tt in *; simpl in *; try (simpl; subst; fsetdec; auto).
  assert (X `in` (fv_tt T1) \/ X `in` (fv_tt T2)). fsetdec.
  destruct H0. assert (X `in` (fv_tt (open_tt_rec n Y T1))). apply IHT1; auto. fsetdec.
  assert (X `in` fv_tt (open_tt_rec n Y T2)). apply IHT2; auto. fsetdec. apply IHT; auto.
Qed.

Lemma fv_tt_in_wf_typ: forall E T K,
  wf_typ E T K ->
  (forall x, x `in` fv_tt T -> x `in` dom E).
Proof.
  intros E T K H.
  induction H; intros.
  Case "var".
  simpl in H1. assert (x = X). fsetdec.
  subst x. eapply binds_in_dom. apply H0.
  Case "arrow". 
  simpl in H1. assert ((x `in` fv_tt T1) \/ (x `in` fv_tt T2)).
  fsetdec. destruct H2. apply IHwf_typ1; auto. apply IHwf_typ2; auto.
  Case "all".
  pick fresh Y.  
  lapply (H0 Y). intros.  lapply (H2 x). intros.
  destruct (x == Y).
    subst. assert False. apply Fr. fsetdec. tauto.
    rewrite dom_concat in H3. simpl in H3. fsetdec. 
    simpl in H1. unfold open_tt.  apply fv_tt_in_open. auto.
    notin_solve.
  Case "sub".
    apply IHwf_typ; auto.
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
  rewrite dom_concat in H0. rewrite dom_concat in H0. unfold not. intros. 
  assert (ok (E1 ++ E2 ++ E3)). eapply ok_from_wf_typ; eauto.
  lapply H0. intros. assert (x `in` dom E1 \/ x `in` dom E2 \/ x `in` dom E3).
  fsetdec. destruct H6. assert (x `notin` dom E2). eapply fresh_tail_In. 
  eapply ok_remove_tail. rewrite_env ((E1 ++ E2) ++ E3) in H4. apply H4. auto. tauto.
  destruct H6.
  assert (x `notin` dom E1).  eapply fresh_mid_head_In. apply H4. auto. 
  assert (x `in` dom (E1 ++ E3)). eapply fv_tt_in_wf_typ. 
  apply H2. auto. 
  assert (x `notin` dom E3).  eapply fresh_mid_tail_In. apply H4. auto. 
  rewrite dom_concat in H8. fsetdec. 
  assert (x `notin` dom E3).  eapply fresh_mid_tail_In. apply H4. auto.  tauto.
  auto.
Qed.
  
Lemma wf_typ_strengthening4:  forall E1 E2 T K1 K2,
  wf_typ (E1 ++ E2) T K1 ->
  wf_typ E1 T K2 ->
  wf_typ E1 T K1.
Proof.
  intros E1 E2. generalize dependent E1.
  induction E2; intros E1 T K1 K2 H1 H2.
  simpl_env in H1. auto.
  destruct a.  assert (forall x, x `in` dom ((a,b) :: E2) -> x `notin` fv_tt T).
  intros. eapply disjoint_dom. rewrite_env (E1 ++ ((a,b)::E2) ++ empty) in H1. apply H1. 
  simpl_env. apply H2. auto. 
  eapply IHE2. eapply wf_typ_strengthening3. rewrite_env (E1 ++ [(a,b)] ++ E2) in H1.
  apply H1. intros. apply H. simpl. simpl in H0. fsetdec. apply H2.
Qed.

Lemma wf_typ_strengthening5: forall E1 E2 E3 T K1 K2,
  wf_typ (E1 ++ E2 ++ E3) T K1 ->
  wf_typ (E1 ++ E3) T K2 ->
  wf_typ (E1 ++ E3) T K1.
Proof.
  intros.
  eapply wf_typ_strengthening3. apply H.
  intros. eapply disjoint_dom.
  eapply H. eapply H0. auto.
Qed.

(* ********************************************************************** *)
(** ** Weakening (5) *)


Lemma XXX_FIX_OK: forall (e:env), ok e.
Admitted.

Lemma SKIP: forall a, a.
Proof.
Admitted.

Lemma env_below_kn_weakening3: forall E1 E2 F K G,
  env_below_kn G (E1 ++ E2) K ->
  env_below_kn G (F ++ E2) K ->
  ok (E1 ++ F ++ E2) ->
  env_below_kn G (E1 ++ F ++ E2) K.
Proof with simpl_env; eauto.
  intros E1.
  induction E1; intros E2 F K G H1 H2 OK.
  Case "nil".
    simpl_env. auto.
  Case "cons".
  rewrite_env ([a] ++ E1 ++ F ++ E2).
  rewrite_env ([a] ++ E1 ++ E2) in H1.
  inversion H1.
   SCase "kn".
    apply env_below_bind_kn. apply IHE1; auto. rewrite_env ([a] ++ E1 ++ F ++ E2) in OK.
    eapply ok_remove_head. apply OK.
    rewrite_env (([(X, bind_kn K1)] ++ E1) ++ F ++ (E2 ++ G)).
    apply wf_env_weakening2. simpl_env. simpl_env in H6. auto.
    rewrite_env ((F ++ E2) ++ G). eapply wf_env_from_env_below1. apply H2.
    subst. apply ok_join. apply ok_from_wf_env. rewrite_env ((F ++ E2) ++ G).
    eapply wf_env_from_env_below1. apply H2. simpl_env. apply ok_from_wf_env.
    simpl_env in H6. apply H6. simpl_env. eapply ok_remove_tail. 
    rewrite_env (([(X, bind_kn K1)] ++ E1 ++ F) ++ E2) in OK. apply OK.
   SCase "typ".
    apply env_below_bind_typ. apply IHE1; auto. rewrite_env ([a] ++ E1 ++ F ++ E2) in OK.
    eapply ok_remove_head. apply OK.
    rewrite_env (([(x, bind_typ T)] ++ E1) ++ F ++ (E2 ++ G)).
    apply wf_env_weakening2. simpl_env. simpl_env in H5. auto.
    rewrite_env ((F ++ E2) ++ G). eapply wf_env_from_env_below1. apply H2.
    apply ok_join. apply ok_from_wf_env. rewrite_env ((F ++ E2) ++ G).
    eapply wf_env_from_env_below1. apply H2. simpl_env. apply ok_from_wf_env.
    simpl_env in H5. apply H5. simpl_env. subst a. eapply ok_remove_tail. 
    rewrite_env (([(x, bind_typ T)] ++ E1 ++ F) ++ E2) in OK. apply OK.

    rewrite_env (E1 ++ F ++ E2 ++ G). apply wf_typ_weakening. simpl_env in H7. auto.
    apply ok_join. apply ok_from_wf_env. rewrite_env ((F ++ E2) ++ G).
    eapply wf_env_from_env_below1. apply H2. simpl_env. apply ok_from_wf_env.
    simpl_env in H5.  eapply wf_env_strengthening2. apply H5.  
    eapply ok_remove_head. eapply ok_remove_tail.
    rewrite_env (([a] ++ E1 ++ F) ++ E2) in OK. apply OK.
Qed.
    
Lemma split_weakening1: forall E1 E2 E3 F1 F2 F3 G,
  env_split E1 E2 E3 G ->
  env_split F1 F2 F3 G ->
  ok (E3 ++ F3) ->
  env_split (E1 ++ F1) (E2 ++ F2) (E3 ++ F3) G.
Proof.
  intros E1 E2 E3 F1 F2 F3 G H1.
  generalize dependent F1.  generalize dependent F2.  generalize dependent F3.
  induction H1; intros F3 F2 F1 S OK.
  Case "empty".
    simpl_env. auto.
  Case "bind_kn".
    repeat (rewrite app_ass).
    apply env_split_kn; auto. apply IHenv_split. auto. 
    simpl_env in OK. eapply ok_remove_head. eauto.
    simpl_env in OK. inversion OK. auto.
  Case "bind_typ".
    repeat (rewrite app_ass).
    apply env_split_nonlin; auto. apply IHenv_split. auto.
    rewrite_env (E3 ++ F3 ++ empty).
    simpl_env. simpl_env in OK. eapply ok_remove_head. eauto.
    rewrite_env (E3 ++ F3 ++ G).
    apply wf_typ_weakening. auto.
    apply ok_join. apply ok_from_wf_env. eapply wf_env_split0. apply S.
    apply ok_from_wf_env. eapply wf_env_split0. apply H1. 
    simpl_env in OK. eapply ok_remove_head. apply OK.
    simpl_env in OK. inversion OK. auto.
  Case "left".
    repeat (rewrite app_ass).
    apply env_split_lin_left. apply IHenv_split. auto.
    simpl_env. simpl_env in OK. eapply ok_remove_head. eauto.
    simpl_env.
    apply wf_typ_weakening. apply H.
    apply ok_join. 
      apply ok_from_wf_env. eapply wf_env_split0. apply S.
      apply ok_from_wf_env. eapply wf_env_split0. apply H1. 
      simpl_env in OK. eapply ok_remove_head. apply OK.
    simpl_env in OK. inversion OK.
    rewrite dom_concat. rewrite dom_concat in H8.
    rewrite (dom_env_split E1 E2 E3 G) in H8.
    rewrite (dom_env_split F1 F2 F3 G) in H8.
    fsetdec. auto. auto.
    simpl_env in OK. inversion OK; auto. auto.
  Case "right".
    repeat (rewrite app_ass).
    apply env_split_lin_right. apply IHenv_split. auto.
    simpl_env. simpl_env in OK. eapply ok_remove_head. eauto.
    simpl_env.
    apply wf_typ_weakening. apply H.
    apply ok_join. 
      apply ok_from_wf_env. eapply wf_env_split0. apply S.
      apply ok_from_wf_env. eapply wf_env_split0. apply H1. 
      simpl_env in OK. eapply ok_remove_head. apply OK.
    simpl_env in OK. inversion OK. 
    rewrite dom_concat in H8.
    rewrite (dom_env_split E1 E2 E3 G) in H8.
    rewrite (dom_env_split F1 F2 F3 G) in H8.
    rewrite dom_concat. fsetdec. auto. auto.
    simpl_env in OK. inversion OK; auto. auto.
Qed.

(*
Example:

G ++ H  ==   (x1 X y1 c Z W) ++ (z2 a w2 b A)

E == x1 X y1 c Z W _  a _  b A
F == _  X  _ c Z W z2 a w2 b A

E1 ++ E2 = (x1 X y1 c Z W) ++ (_  a  _ b A)
F1 ++ F2 = (_  X _  c Z W) ++ (z2 a w2 b A)

G1 = (x1 X y1 c Z W)
G2 = (_  X _  c Z W)   
*)

Hint Constructors env_split.

Lemma empty_noteq_concat: forall E X G,
 empty = E ++ [X] ++ G -> False.
Proof.
  induction E; intros.
  simpl. unfold not; intros. inversion H.
  simpl. unfold not; intros. inversion H.
Qed.

Lemma split_weakening2 : forall E F G H EE,
  env_split E F (G ++ H) EE ->
  exists E1, exists F1, exists E2, exists F2,
  (env_split E2 F2 H EE /\
   E1 ++ E2 = E /\
   F1 ++ F2 = F /\
   env_split E1 F1 G (H ++ EE)).
Proof with simpl_env; auto.
  intros E F G H EE S.
  remember (G ++ H) as GG.
  generalize dependent G. generalize dependent H.
  induction S; intros HN GN EQ.
  Case "empty".
    exists empty. exists empty. exists empty. exists empty.
    simpl_env. repeat split; auto. 
    destruct HN. auto. assert False.  eapply empty_noteq_concat.
    simpl_env in EQ. rewrite_env (GN ++ [p] ++ HN) in EQ. apply EQ. tauto.
    destruct GN. apply env_split_empty. destruct HN. simpl_env. auto.
    rewrite_env (empty ++ [p] ++ HN) in EQ. assert False.  eapply empty_noteq_concat. 
    apply EQ. tauto.
    rewrite_env (p :: GN ++ HN) in EQ. inversion EQ.
  Case "kn".
    destruct GN. destruct HN; simpl in EQ; inversion EQ; subst.
    lapply (IHS HN empty). intros.
    destruct H1 as [E11 [E21 [E12 [E22 [S2 [Q1 [Q2 S3]]]]]]].
    exists empty.
    exists empty.
    exists ([(X, bind_kn K)] ++ E1). 
    exists ([(X, bind_kn K)] ++ E2).
    simpl_env; repeat split; auto.
    apply env_split_empty.
    apply wf_env_kn. rewrite_env (empty ++ HN ++ G).
    eapply wf_env_split0. apply S3. rewrite dom_concat. fsetdec. 
    simpl_env. auto.
    
    simpl_env in EQ. rewrite_env ([p] ++ GN ++ HN) in EQ.
    inversion EQ; subst. 
    lapply (IHS HN GN); intros; auto.
    destruct H1 as [E11 [E21 [E12 [E22 [S2 [Q1 [Q2 S3]]]]]]].
    exists ([(X, bind_kn K)] ++ E11).
    exists ([(X, bind_kn K)] ++ E21).
    exists E12.
    exists E22.
    simpl_env. subst. repeat split; auto.
    apply env_split_kn. auto. rewrite dom_concat in H. fsetdec.
    rewrite dom_concat in H. rewrite dom_concat. fsetdec.
  Case "nonlin".
    destruct GN. destruct HN; simpl in EQ; inversion EQ; subst.
    lapply (IHS HN empty). intros.
    destruct H2 as [E11 [E21 [E12 [E22 [S2 [Q1 [Q2 S3]]]]]]].
    exists empty.
    exists empty.
    exists ([(x, bind_typ T)] ++ E1). 
    exists ([(x, bind_typ T)] ++ E2).
    simpl_env; repeat split; auto. 
    apply env_split_empty.
    eapply wf_env_typ. rewrite_env (empty ++ HN ++ G).
    eapply wf_env_split0. apply S3. apply H. rewrite dom_concat. fsetdec. 
    simpl_env. auto.
    
    simpl_env in EQ. rewrite_env ([p] ++ GN ++ HN) in EQ.
    inversion EQ; subst. 
    lapply (IHS HN GN); intros; auto.
    destruct H2 as [E11 [E21 [E12 [E22 [S2 [Q1 [Q2 S3]]]]]]].
    exists ([(x, bind_typ T)] ++ E11).
    exists ([(x, bind_typ T)] ++ E21).
    exists E12.
    exists E22.
    simpl_env. subst. repeat split; auto.
    apply env_split_nonlin. auto. simpl_env in H. auto. 
    rewrite dom_concat in H0. fsetdec.
    rewrite dom_concat in H0. rewrite dom_concat. fsetdec.
  Case "left".
    destruct GN. destruct HN; simpl in EQ; inversion EQ; subst.
    lapply (IHS HN empty). intros.
    auto.
    destruct H3 as [E11 [E21 [E12 [E22 [S2 [Q1 [Q2 S3]]]]]]].
    exists empty.
    exists empty.
    exists ([(x, bind_typ T)] ++ E1). 
    exists E2.
    simpl_env; repeat split; auto. simpl_env. auto.
    apply env_split_empty.
    eapply wf_env_typ. rewrite_env (empty ++ HN ++ G).
    eapply wf_env_split0. apply S3. apply H. rewrite dom_concat. fsetdec. 
    simpl_env. auto.

    simpl_env in EQ. rewrite_env ([p] ++ GN ++ HN) in EQ.
    inversion EQ; subst. 
    lapply (IHS HN GN); intros; auto.
    destruct H3 as [E11 [E21 [E12 [E22 [S2 [Q1 [Q2 S3]]]]]]].
    exists ([(x, bind_typ T)] ++ E11).
    exists E21.
    exists E12.
    exists E22.
    simpl_env. subst. repeat split; auto.
    apply env_split_lin_left; auto. simpl_env in H. auto. 
    simpl_env in H0. fsetdec.
    rewrite dom_concat in H1. fsetdec.
    rewrite dom_concat in H1. rewrite dom_concat. fsetdec.

  Case "right".
    destruct GN. destruct HN; simpl in EQ; inversion EQ; subst.
    lapply (IHS HN empty). intros.
    destruct H3 as [E11 [E21 [E12 [E22 [S2 [Q1 [Q2 S3]]]]]]].
    exists empty.
    exists empty.
    exists E1.
    exists ([(x, bind_typ T)] ++ E2). 
    simpl_env; repeat split; auto. simpl_env. auto.
    apply env_split_empty.
    eapply wf_env_typ. rewrite_env (empty ++ HN ++ G).
    eapply wf_env_split0. apply S3. apply H. rewrite dom_concat. fsetdec. 
    simpl_env. auto.

    simpl_env in EQ. rewrite_env ([p] ++ GN ++ HN) in EQ.
    inversion EQ; subst. 
    lapply (IHS HN GN); intros; auto.
    destruct H3 as [E11 [E21 [E12 [E22 [S2 [Q1 [Q2 S3]]]]]]].
    exists E11.
    exists ([(x, bind_typ T)] ++ E21).
    exists E12.
    exists E22.
    simpl_env. subst. repeat split; auto.
    apply env_split_lin_right; auto. simpl_env in H. auto. 
    simpl_env in H0. fsetdec.
    rewrite dom_concat in H1. fsetdec.
    rewrite dom_concat in H1. rewrite dom_concat. fsetdec.
Qed.
   
Lemma split_destruct2: forall E F G H EE Z K,
    env_split E F (G ++ [(Z, bind_kn K)] ++ H) EE ->
    exists E1, exists F1, exists E2, exists F2,
    (env_split E2 F2 H EE /\
     E1 ++ [(Z, bind_kn K)] ++ E2 = E /\
     F1 ++ [(Z, bind_kn K)] ++ F2 = F /\
     env_split E1 F1 G ([(Z, bind_kn K)] ++ H ++ EE))
.
Proof.
  intros E F G H EE Z K Hyp.
  lapply (split_weakening2 E F G ([(Z, bind_kn K)] ++ H) EE). intros.
  destruct H0 as [E1 [F1 [E2 [F2 [S2 [EQ1 [EQ2 S3]]]]]]].
  exists E1. exists F1. 
  inversion S2. subst. exists E0. exists E3. repeat split; auto.
  auto.
Qed.

Lemma env_below_kn_sub: forall E G,
  env_below_kn G E kn_nonlin ->
  env_below_kn G E kn_lin.
Proof.
  intros E G H.  
  induction H; intros; auto.
  apply env_below_bind_typ. auto.
  auto. 
  destruct K.
  auto.
  apply wf_typ_sub. auto.
Qed.

Lemma env_split_weakening1: forall M E1 E2 E3 G,
  env_split E1 E2 E3 G ->
  env_below_kn (E3 ++ G) M kn_nonlin ->
  env_split (M ++ E1) (M ++ E2) (M ++ E3) G
.
Proof.
  induction M; intros E1 E2 E3 G H1 H2. 
  Case "nil".
  simpl_env; auto.
  Case "cons".
    rewrite_env ([a] ++ M ++ E1).
    rewrite_env ([a] ++ M ++ E2).
    rewrite_env ([a] ++ M ++ E3).
    inversion H2; subst.
    apply env_split_kn.
    apply IHM; auto.
    inversion H6. rewrite dom_concat in H7. rewrite dom_concat in H7.
    rewrite dom_concat. fsetdec. 
    inversion H6. rewrite dom_concat in H7. rewrite dom_concat in H7.
    fsetdec. 

    apply env_split_nonlin.
    apply IHM; auto.
    simpl_env; auto.
    inversion H5. rewrite dom_concat in H9. rewrite dom_concat in H9.
    rewrite dom_concat. fsetdec. 
    inversion H5. rewrite dom_concat in H9. rewrite dom_concat in H9.
    fsetdec. 
Qed.


Lemma split_below1: forall M E F G EE,
  env_split F G E EE ->
  env_below_kn (E ++ EE) M kn_nonlin ->
  env_below_kn (F ++ EE) M kn_nonlin
.
Proof.
  induction M; intros E F G EE S B.
  Case "empty".
    apply env_below_empty. 
    eapply wf_split_env1. auto. apply S. 
  rewrite_env ([a] ++ M) in B.
  inversion B; subst.
  Case "kn".
    simpl_env. apply env_below_bind_kn. eapply IHM.
    apply S. apply H2.
    apply wf_env_kn. inversion H4. subst.
    rewrite_env ((M ++ F) ++ EE).
    eapply wf_split_env1. eapply env_split_weakening1. apply S. apply H2.
    rewrite dom_concat. inversion H4. subst. rewrite dom_concat in H5.
    rewrite dom_concat in H5.
    rewrite (dom_env_split F G E EE) in H5. 
    rewrite dom_concat.
    fsetdec. apply S.
  Case "typ".
    simpl_env. apply env_below_bind_typ. eapply IHM.
    apply S. apply H1. 
    eapply wf_env_typ. inversion H3. subst.
    rewrite_env ((M ++ F) ++ EE).
    eapply wf_split_env1. eapply env_split_weakening1. apply S. apply H1.
    rewrite_env ((M ++ F) ++ EE).
    eapply wf_split_typ1. rewrite_env ((M ++ E) ++ EE) in H5. apply H5.
    eapply env_split_weakening1. apply S. apply H1. 
    repeat rewrite dom_concat. inversion H3. subst. repeat rewrite dom_concat in H7.
    rewrite (dom_env_split F G E EE) in H7. fsetdec. apply S.
    rewrite_env ((M ++ F) ++ EE).
    eapply wf_split_typ1. rewrite_env ((M ++ E) ++ EE) in H5. apply H5.
    eapply env_split_weakening1. apply S. apply H1. 
Qed.

Lemma split_below2: forall M E F G EE,
  env_split F G E EE ->
  env_below_kn (E ++ EE) M kn_nonlin ->
  env_below_kn (G ++ EE) M kn_nonlin
.
Proof.
  intros. eapply split_below1. eapply env_split_commute. apply H.
  auto.
Qed.

Lemma wf_env_from_typing: forall E e T,
  typing E e T ->
  wf_env E.
Proof.
  intros.
  lapply (typing_regular E e T); intros; tauto.
Qed.


Lemma not_wf_env: forall E1 E2 E3 x T U,
  ~ wf_env (E1 ++ [(x, bind_typ T)] ++ E2 ++ [(x, bind_typ U)] ++ E3).
Proof.
  intros. unfold not. intros.
  assert (ok (E1 ++ [(x, bind_typ T)] ++ E2 ++ [(x, bind_typ U)] ++ E3)).
  apply ok_from_wf_env; auto.
  assert (~ x `in` dom ([(x, bind_typ U)] ++ E3)).
  eapply fresh_mid_tail_In.
  rewrite_env  (E1 ++ ([(x, bind_typ T)] ++ E2) ++ [(x, bind_typ U)] ++ E3) in H0.
  apply H0.
  rewrite dom_concat. simpl. fsetdec.
  apply H1. 
  rewrite dom_concat. simpl. fsetdec.
Qed.

Lemma not_wf_env2: forall E1 E2 E3 x T U,
  ~ wf_env (E1 ++ [(x, bind_kn T)] ++ E2 ++ [(x, bind_kn U)] ++ E3).
Proof.
  intros. unfold not. intros.
  assert (ok (E1 ++ [(x, bind_kn T)] ++ E2 ++ [(x, bind_kn U)] ++ E3)).
  apply ok_from_wf_env; auto.
  assert (~ x `in` dom ([(x, bind_kn U)] ++ E3)).
  eapply fresh_mid_tail_In.
  rewrite_env  (E1 ++ ([(x, bind_kn T)] ++ E2) ++ [(x, bind_kn U)] ++ E3) in H0.
  apply H0.
  rewrite dom_concat. simpl. fsetdec.
  apply H1. 
  rewrite dom_concat. simpl. fsetdec.
Qed.

(*
Lemma env_split_weakening2: forall G F E M,
  env_split G F E ->
  wf_env (M ++ E) ->
  exists F1, env_split (M ++ G) F1 (M ++ E).
Proof.
  intros G F E M S.
  generalize dependent M.
  induction S; intros M WFE.
  Case "emtpy".
    induction M.
    exists empty. simpl_env. auto.
    destruct IHM as [F1 S].
    simpl_env. rewrite_env ([a] ++ M) in WFE. eapply wf_env_strengthening2. simpl_env in WFE.
    apply WFE.
    destruct a; destruct b.
    exists ([(a, bind_kn k)] ++ F1).
    simpl_env. apply env_split_kn. simpl_env in S. auto.
    destruct (wf_typ_dec M t kn_nonlin).
    eapply ok_from_wf_env. eapply wf_env_strengthening2. simpl_env in WFE. apply WFE.
    simpl_env in WFE. inversion WFE. eapply type_from_wf_typ. apply H3.
    exists ((a, bind_typ t) :: F1). 
    simpl_env. apply env_split_nonlin. simpl_env in S. auto. auto.
    assert (exists K, wf_typ M t K).
    apply (wf_env_inversion empty M a t). simpl_env. simpl_env in WFE. apply WFE.
    destruct H0 as [K WFT].
    destruct K.
    exists F1. simpl_env. apply env_split_lin_left. simpl_env in S. apply S. auto.
    simpl_env in WFE. inversion WFE. simpl_env. subst.
    simpl_env in S. rewrite (dom_env_split M F1 M) in H5. fsetdec. auto. auto.
    assert False. apply H. auto. tauto.
  Case "kn".
    lapply (IHS (M ++ [(X, bind_kn K)])).
    intros H. destruct H as [F1 S1].
    exists F1. simpl_env in S1. apply S1. simpl_env. apply WFE.
  Case "nonlin".
    lapply (IHS (M ++ [(x, bind_typ T)])).
    intros H1. destruct H1 as [F1 S1].
    exists F1. simpl_env in S1. apply S1. simpl_env. apply WFE.
  Case "left".
    lapply (IHS (M ++ [(x, bind_typ T)])).
    intros H2. destruct H2 as [F1 S1].
    exists F1. simpl_env in S1. apply S1. simpl_env. apply WFE.
  Case "right".
    induction M.
    exists ([(x, bind_typ T)] ++ E2). simpl_env. apply env_split_lin_right. apply S. apply H.
    auto. auto.
    destruct IHM as [F1 S1].
    simpl_env. rewrite_env ([a] ++ M) in WFE. eapply wf_env_strengthening2. simpl_env in WFE.
    apply WFE.
    destruct a; destruct b.
    exists ([(a, bind_kn k)] ++ F1).
    simpl_env. apply env_split_kn. simpl_env in S. auto.
    destruct (wf_typ_dec (M ++ [(x, bind_typ T)] ++ E3) t kn_nonlin).
    eapply ok_from_wf_env. eapply wf_env_strengthening2. simpl_env in WFE. apply WFE.
    simpl_env in WFE. inversion WFE. eapply type_from_wf_typ. apply H6.
    exists ((a, bind_typ t) :: F1). 
    simpl_env. apply env_split_nonlin. simpl_env in S. auto. auto.
    assert (exists K, wf_typ (M ++ [(x, bind_typ T)] ++ E3) t K).
    apply (wf_env_inversion empty (M ++ [(x, bind_typ T)] ++ E3) a t). 
    simpl_env. simpl_env in WFE. apply WFE.
    destruct H3 as [K WFT].
    destruct K.
    exists F1. simpl_env. apply env_split_lin_left. apply S1. auto.
    simpl_env in WFE. inversion WFE. simpl_env. subst.
    rewrite_env (M ++ [(x, bind_typ T)] ++ E3) in H8.
    rewrite (dom_env_split (M ++ E1) F1 (M ++ [(x, bind_typ T)] ++ E3)) in H8. 
    fsetdec. auto. auto. contradiction.
Qed.

Lemma env_split_weakening3: forall G F E M,
  env_split G F E ->
  wf_env (M ++ E) ->
  exists G1, env_split G1 (M ++ F) (M ++ E).
Proof.
  intros.
  assert (exists G1, env_split (M ++ F) G1 (M ++ E)).
  eapply env_split_weakening2. eapply split_env_commute. apply H. auto.
  destruct H1 as [G1 S1].
  exists G1. apply split_env_commute. apply S1.
Qed.
*)

Lemma env_split_weakening4: forall G F E EE M,
  env_split G F E EE ->
  wf_env (E ++ M ++ EE) ->
  env_below_kn EE M kn_nonlin ->
  env_split (G ++ M) (F ++ M) (E ++ M) EE.
Proof.
  intros G F E EE M S. generalize dependent M.
  induction S; intros M WFE B.
  Case "empty".
    simpl_env. apply env_split_below_nonlin. auto.
  Case "kn".
    simpl_env. apply env_split_kn. apply IHS; auto.
    eapply wf_env_strengthening2. simpl_env in WFE. apply WFE.
    inversion WFE. rewrite dom_concat. repeat rewrite dom_concat in H5. fsetdec. auto.
  Case "nonlin".
    simpl_env. apply env_split_nonlin; auto. apply IHS; auto.
    eapply wf_env_strengthening2. simpl_env in WFE. apply WFE.
    simpl_env.
    eapply wf_typ_weakening. apply H.
    apply ok_from_wf_env. eapply wf_env_strengthening2. simpl_env in WFE.
    apply WFE.
    inversion WFE. rewrite dom_concat. repeat rewrite dom_concat in H7. fsetdec.
  Case "left".
    simpl_env. apply env_split_lin_left. apply IHS; auto.
    eapply wf_env_strengthening2. simpl_env in WFE. apply WFE.
    simpl_env.
    eapply wf_typ_weakening. simpl_env. apply H.
    apply ok_from_wf_env. eapply wf_env_strengthening2. simpl_env in WFE.
    apply WFE.
    rewrite dom_concat. inversion WFE. 
    repeat rewrite dom_concat in H8. fsetdec.
    inversion WFE. 
    repeat rewrite dom_concat in H8. rewrite dom_concat. fsetdec. auto.
  Case "right".
    simpl_env. apply env_split_lin_right. apply IHS; auto.
    eapply wf_env_strengthening2. simpl_env in WFE. apply WFE.
    simpl_env.
    eapply wf_typ_weakening. simpl_env. apply H.
    apply ok_from_wf_env. eapply wf_env_strengthening2. simpl_env in WFE.
    apply WFE.
    inversion WFE. 
    repeat rewrite dom_concat in H8. rewrite dom_concat. fsetdec.
    inversion WFE. 
    repeat rewrite dom_concat in H8. rewrite dom_concat. fsetdec. auto.
Qed.

Lemma env_split_weakening: forall M G1 G2 F1 F2 E1 E2 EE,
  env_split (G1 ++ G2) (F1 ++ F2) (E1 ++ E2) EE->
  env_split G2 F2 E2 EE ->
  env_split G1 F1 E1 (E2 ++ EE) ->
  wf_env (E1 ++ M ++ E2 ++ EE) ->
  env_below_kn (E2 ++ EE) M kn_nonlin ->
  env_split (G1 ++ M ++ G2) (F1 ++ M ++ F2) (E1 ++ M ++ E2) EE.
Proof.
  intros M G1 G2 F1 F2 E1 E2 EE S1 S2 S3 WFE B.
  remember (E2 ++ EE) as G.
  generalize dependent E2. generalize dependent F2. generalize dependent G2.
  induction S3; intros GR FR ER S1 S2 Q1; subst G; simpl_env in *.
  Case "empty".
    apply env_split_weakening1; auto.
  Case "kn".
    apply env_split_kn. apply IHS3; auto.
    eapply wf_env_strengthening2. apply WFE.
    inversion S1; auto.
    inversion WFE. repeat rewrite dom_concat in H5. repeat rewrite dom_concat.
    fsetdec. fsetdec.
  Case "nonlin".
    apply env_split_nonlin. apply IHS3; auto.
    eapply wf_env_strengthening2. apply WFE.
    inversion S1; subst; auto. 
    simpl in H9. assert False. apply H9. fsetdec. tauto.
    simpl in H9. assert False. apply H9. fsetdec. tauto.
    simpl_env. auto. eapply wf_typ_weakening. auto.
    eapply ok_from_wf_env. eapply wf_env_strengthening2. apply WFE.
    inversion WFE. repeat rewrite dom_concat in H7. repeat rewrite dom_concat.
    fsetdec. fsetdec.
  Case "left".
    apply env_split_lin_left. apply IHS3; auto.
    eapply wf_env_strengthening2. apply WFE.
    inversion S1; subst; auto. 
      destruct E2; inversion H6; subst. simpl_env in H3.
      rewrite (dom_env_split GR FR ER EE) in H2. subst FR.
      simpl in H2. assert False. fsetdec. tauto. auto.
      simpl in H0. assert False. fsetdec. tauto.
      simpl in H10. assert False. fsetdec. tauto.

    simpl_env. eapply wf_typ_weakening. auto.
    eapply ok_from_wf_env. eapply wf_env_strengthening2. apply WFE.
    repeat rewrite dom_concat.
    inversion WFE. repeat rewrite dom_concat in H8.
    rewrite (dom_env_split GR FR ER EE) in H8; auto.
    inversion WFE. repeat rewrite dom_concat in H8.
    repeat rewrite dom_concat. auto. auto.
  Case "right".
    apply env_split_lin_right. apply IHS3; auto.
    eapply wf_env_strengthening2. apply WFE.
    inversion S1; subst; auto. 
      destruct E1; inversion H3; subst. simpl_env in H3.
      rewrite dom_concat in H11.
      rewrite (dom_env_split GR FR ER EE) in H11. subst GR.
      simpl in H11. assert False. fsetdec. tauto. auto.
      simpl in H0. assert False. fsetdec. tauto. auto.
      simpl in H10. assert False. fsetdec. tauto. auto.

    simpl_env. eapply wf_typ_weakening. auto.
    eapply ok_from_wf_env. eapply wf_env_strengthening2. apply WFE.
    repeat rewrite dom_concat.
    inversion WFE. repeat rewrite dom_concat in H8.
    rewrite (dom_env_split GR FR ER EE) in H8; auto.
    inversion WFE. repeat rewrite dom_concat in H8.
    repeat rewrite dom_concat. auto. auto.
Qed.


Lemma env_below_kn_subst_tb: forall E F Z K P K0,
  env_below_kn empty (F ++ [(Z, bind_kn K)] ++ E) K0 ->
  wf_typ E P K ->
  env_below_kn empty (map (subst_tb Z P) F ++ E) K0.
Proof.
  intros E F Z K P K0 H1 H2.
  generalize dependent E.
  induction F; intros.
    simpl. simpl in H1. inversion H1. auto.
  inversion H1; subst; simpl;simpl_env. apply env_below_bind_kn. apply IHF. auto. auto. simpl_env.
  inversion H6. apply wf_env_kn. eapply wf_env_subst_tb. simpl_env in H3. apply H3. auto. rewrite dom_concat.
  simpl_env in H7. rewrite dom_map. notin_solve.
  apply env_below_bind_typ. apply IHF. auto. auto. simpl_env.
  inversion H5; subst; simpl; simpl_env.  rewrite_env ((map (subst_tb Z P) ([(x, bind_typ T)] ++ F)) ++ E).
  eapply wf_env_subst_tb. simpl_env in H5. simpl_env. apply H5. auto. simpl_env. eapply wf_typ_subst_tb. simpl_env in H7. apply H7.
  auto.
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
  assert (ok (F ++ [(X, bind_kn K)] ++ E)). auto. 
  assert (ok (E ++ F ++ [(X, bind_kn K)])). apply ok_commute. simpl_env. auto.
  assert (X `notin` dom (F ++ [(X, bind_kn K)])).
  eapply fresh_tail_In. apply H5. auto. rewrite dom_concat in H6. simpl in H6. fsetdec. auto.
Qed.


Lemma in_fv_tt_dec: forall X T,
 {X `in` fv_tt T}+{~ X `in` fv_tt T}.
Proof.
  intros X T.
  induction T.
  simpl. right. fsetdec.
  destruct (X == a). subst. left. simpl. fsetdec. right. simpl. fsetdec.
  simpl. destruct IHT1. left. fsetdec. destruct IHT2. left. fsetdec. right. fsetdec.
  destruct IHT. simpl. left. auto.
  simpl. right. auto.
Qed.

Lemma ok_strengthening: forall G (E:env) x a,
  ok (G ++ E) ->
  x `notin` dom G ->
  x `notin` dom E ->
  ok (G ++ [(x, a)] ++ E).
Proof.
  induction G; intros.
  simpl. apply ok_cons. simpl_env in H. auto.
  auto.
  destruct a. simpl. apply ok_cons. simpl_env. apply IHG. 
  eapply ok_remove_head. simpl_env in H. apply H. 
  simpl in H0. fsetdec. auto. simpl in H0. rewrite dom_concat. simpl. 
  assert (x <> a). unfold not. intros. apply H0. subst . fsetdec. 
  assert (a `notin` singleton x).
  fsetdec. inversion H. rewrite dom_concat in H8. fsetdec.
Qed.


Lemma ok_split_splice: forall E F G G0 G1,
  ok (G1 ++ E) ->
  ok (G1 ++ F) ->
  env_split E F G G0 ->
  ok (G1 ++ G).
Proof.
  intros E F G G0 G1 OK1 OK2 S.
  generalize dependent G1. 
  induction S; intros G2 OK1 OK2.
  Case "empty".
    auto.
  Case "kn".
    apply ok_strengthening. apply IHS.
    eapply ok_remove_mid; eauto.
    eapply ok_remove_mid; eauto.
    eapply fresh_mid_head. apply OK1. 
    rewrite (dom_env_split E1 E2 E3 G). 
    assert (X `notin` dom E1). eapply fresh_mid_tail. apply OK1.
    assert (X `notin` dom E2). eapply fresh_mid_tail. apply OK2. fsetdec. auto.
  Case "nonlin".
    apply ok_strengthening. apply IHS.
    eapply ok_remove_mid; eauto.
    eapply ok_remove_mid; eauto.
    eapply fresh_mid_head. apply OK1. 
    rewrite (dom_env_split E1 E2 E3 G). 
    assert (x `notin` dom E1). eapply fresh_mid_tail. apply OK1.
    assert (x `notin` dom E2). eapply fresh_mid_tail. apply OK2. fsetdec. auto.
  Case "left".
    apply ok_strengthening. apply IHS.
    eapply ok_remove_mid; eauto. auto.
    eapply fresh_mid_head. apply OK1. 
    rewrite (dom_env_split E1 E2 E3 G). 
    assert (x `notin` dom E1). eapply fresh_mid_tail. apply OK1. fsetdec. auto.
  Case "right".
    apply ok_strengthening. apply IHS. auto.
    eapply ok_remove_mid; eauto. 
    eapply fresh_mid_head. apply OK2. 
    rewrite (dom_env_split E1 E2 E3 G). 
    assert (x `notin` dom E2). eapply fresh_mid_tail. apply OK2. fsetdec. auto.
Qed.

Lemma env_split_splice_ok1: forall E1 E2 E3 G F,
  ok (F ++ E3) ->
  env_split E1 E2 E3 G ->
  ok (F ++ E1).
Proof.
  intros E1 E2 E3 G F OK S.
  induction S; auto.
  apply ok_join. simpl. apply ok_cons. eapply ok_remove_tail. 
  eapply ok_env_split1. apply S. rewrite (dom_env_split E1 E2 E3 G) in H.
  fsetdec. auto. apply IHS. eapply ok_remove_mid. apply OK.
  eapply ok_remove_tail. rewrite_env ((F ++ [(X, bind_kn K)]) ++ E3) in OK.
  apply OK.
  apply ok_join. simpl. apply ok_cons. eapply ok_remove_tail. 
  eapply ok_env_split1. apply S. rewrite (dom_env_split E1 E2 E3 G) in H0.
  fsetdec. auto. apply IHS. eapply ok_remove_mid. apply OK.
  eapply ok_remove_tail. rewrite_env ((F ++ [(x, bind_typ T)]) ++ E3) in OK.
  apply OK.
  apply ok_join. simpl. apply ok_cons. eapply ok_remove_tail. 
  eapply ok_env_split1. apply S. rewrite (dom_env_split E1 E2 E3 G) in H1.
  fsetdec. auto.
  apply IHS. eapply ok_remove_mid. apply OK.
  eapply ok_remove_tail. rewrite_env ((F ++ [(x, bind_typ T)]) ++ E3) in OK.
  apply OK.
  apply IHS; auto. eapply ok_remove_mid. apply OK.
Qed.

Lemma env_split_splice_ok2: forall E1 E2 E3 G F,
  ok (F ++ E3) ->
  env_split E1 E2 E3 G ->
  ok (F ++ E2).
Proof.
  intros. eapply env_split_splice_ok1. apply H.
  eapply env_split_commute. apply H0.
Qed.
  
Lemma wf_typ_split_splice: forall H G F E T K GX,
  wf_typ (H ++ G ++ GX) T K ->
  env_split G F E GX ->
  ok (H ++ E ++ GX) ->
  wf_typ (H ++ E ++ GX) T K.
Proof.
  intros H G F E T K GX WF S OK.
  assert (ok E). eapply ok_remove_head. eapply ok_remove_tail. 
  rewrite_env ((H ++ E) ++ GX) in OK. eapply  OK.
  remember (H ++ G ++ GX) as G0. generalize dependent H. generalize dependent E.
  induction WF; intros E0 S OKE HE OK EQ; subst; auto.
  binds_cases H0. eapply wf_typ_weaken_head. apply wf_typ_var. auto. 
  eapply ok_remove_head. apply OK. 
  eapply binds_concat_ok. auto. eapply ok_remove_head. apply OK. auto.
  apply wf_typ_var. auto.
  eapply binds_tail. eapply binds_head. 
  eapply binds_env_split1. apply H2. apply S. auto.
  apply wf_typ_var. auto. apply binds_head. auto.
  eapply wf_typ_arrow. eapply IHWF1; auto. eapply IHWF2; auto.
  pick fresh Y and apply wf_typ_all. 
  rewrite <- concat_assoc. apply (H0 Y). 
  fsetdec. auto. auto. simpl. apply ok_cons. auto. 
  rewrite dom_concat. rewrite dom_concat. fsetdec. auto.
Qed.

Lemma wf_env_split_splice1: forall H E F G GX,
  ok (H ++ E ++ GX) ->
  env_split G F E GX ->
  wf_env (H ++ G ++ GX) ->
  wf_env (H ++ E ++ GX).
Proof.
  induction H; intros E F G GX OK S WF.
  simpl_env; auto. eapply wf_env_split0. apply S.
  rewrite_env ([a] ++ H ++ G ++ GX) in WF.
  rewrite_env ([a] ++ H ++ E ++ GX).
  inversion WF; subst.
    apply wf_env_kn. eapply IHlist; eauto. 
    rewrite_env ([(X, bind_kn K)] ++ H ++ E ++ GX) in OK.
    eapply ok_remove_head. apply OK.
    rewrite_env ([(X, bind_kn K)] ++ H ++ E ++ GX) in OK.
    inversion OK. auto.

    eapply wf_env_typ. eapply IHlist; eauto. 
    rewrite_env ([(x, bind_typ T)] ++ H ++ E ++ GX) in OK.
    eapply ok_remove_head. apply OK.
    rewrite_env ([(x, bind_typ T)] ++ H ++ E ++ GX) in OK.
    eapply wf_typ_split_splice. apply H3. apply S.
    eapply ok_remove_head. apply OK.
    rewrite_env ([(x, bind_typ T)] ++ H ++ E ++ GX) in OK.
    inversion OK. auto.
Qed.
   
Lemma typing_weakening: forall E F G e T,
  typing (G ++ E) e T ->
  env_below_kn E F kn_nonlin ->
  wf_env (G ++ F ++ E) ->
  typing (G ++ F ++ E) e T.
Proof with simpl_env;
           eauto using wf_typ_weakening,
                       wf_typ_from_wf_env_typ.
  intros E F G e T Typ.
  remember (G ++ E) as H.
  generalize dependent G. generalize dependent E.
  induction Typ; intros E0 G EQ B WF.
  Case "var".
    lapply (env_mid_two E2 (x, bind_typ T) E1 G E0). intros.
    destruct H1. auto.
    destruct H1 as [F12 [Q1 Q2]].
    rewrite Q1.
    rewrite_env (E2 ++ [(x, bind_typ T)] ++ (F12 ++ F ++E0)).
    apply typing_var. rewrite Q2 in H. simpl_env.
    rewrite Q1 in WF.  simpl_env in WF. auto.
    subst E1.  
      assert (env_below_kn empty E0 kn_nonlin).
      rewrite_env ((E2 ++ F12) ++ E0) in H0.
      eapply env_below_kn_strengthening1. eapply H0.
      assert (env_below_kn empty (F ++ E0) kn_nonlin).
      apply env_below_kn_assoc2. simpl_env; auto. auto.
      rewrite_env ((E2 ++ F12) ++ F ++ E0).
      apply env_below_kn_weakening3. simpl_env. auto.
      auto.
      subst G. 
      apply ok_join. apply ok_from_wf_env. eapply wf_env_strengthening2. apply WF.
      simpl_env. eapply ok_remove_mid. eapply ok_from_wf_env. apply H.
      simpl_env. eapply ok_remove_mid. eapply ok_remove_tail.
      rewrite_env ((E2 ++ [(x, bind_typ T)] ++ F12 ++ F) ++ E0) in WF. 
      apply ok_from_wf_env. apply WF.
    
    destruct H1 as [F12 [Q1 Q2]].
    subst E2. subst E0.
    rewrite_env ((G ++ F ++ F12) ++ [(x, bind_typ T)] ++ E1).
    apply typing_var. simpl_env. simpl_env in WF. auto.
    rewrite_env ((G ++ F) ++ (F12 ++ E1)).
    apply env_below_kn_assoc2. simpl_env. 
    rewrite_env (G ++ F ++ empty).
    assert (env_below_kn (F12 ++ E1) F kn_nonlin).
    eapply env_below_kn_strengthening2. apply B.
    apply env_below_kn_weakening3. simpl_env.
    rewrite_env (G ++ (F12 ++ E1)) in H0.
    rewrite_env ((F12 ++ E1) ++ empty). apply env_below_kn_assoc1. auto.
    simpl_env. apply env_below_kn_assoc1. apply env_below_kn_assoc2. auto.
    eapply env_below_kn_strengthening1. rewrite_env (E1 ++ empty).
    apply env_below_kn_assoc1. eauto.
    simpl_env. eapply ok_remove_tail. eapply ok_from_wf_env.
    rewrite_env ((G ++ F) ++ F12 ++ [(x, bind_typ T)] ++ E1) in WF. apply WF.
    eapply env_below_kn_strengthening1. simpl_env in H0. eauto.
    apply ok_from_wf_env. auto.
     
  Case "abs".
    pick fresh x and apply typing_abs.
    subst E.
    destruct K. 
       apply env_below_kn_weakening3. auto. 
       apply env_below_kn_assoc2. simpl_env. apply env_below_kn_sub. auto.
       eapply env_below_kn_strengthening1. apply H. apply ok_from_wf_env. auto.

       apply env_below_kn_weakening3. auto. apply env_below_kn_assoc2. simpl_env. auto. 
       eapply env_below_kn_strengthening1. apply H; auto. apply ok_from_wf_env; auto.

    subst E.  apply wf_typ_weakening. apply H0. apply ok_from_wf_env. auto.
    lapply (H2 x); [intros Q | auto].
    rewrite <- concat_assoc.
    apply (H2 x)... subst E; auto.
    eapply wf_env_typ. auto. subst E. apply wf_typ_weakening. eauto.
    apply ok_from_wf_env; auto...
    rewrite dom_concat. rewrite dom_concat. fsetdec.
 
  Case "app".
    subst E3.
    lapply (split_weakening2 E1 E2 G E0 empty).    
    intros. destruct H0 as [E3 [F1 [E4 [ F2 [S2 [Q1 [Q2 S3]]]]]]].
    eapply typing_app. 
    eapply (IHTyp1 E4 E3); auto. 
    subst E1.  subst E2.
    rewrite_env (E4 ++ empty).
    eapply split_below1. apply S2.   auto. simpl_env. auto.
    assert (wf_env (G ++ E0)).
    rewrite_env ((G ++ E0) ++ empty).
    eapply wf_env_split0. apply H.
    apply wf_env_weakening2. 
    rewrite_env ((E3 ++ E4) ++ empty).
    apply (wf_split_env1 (E3 ++ E4) (F1++F2) (G ++ E0) empty). 
    subst. auto.  assert (env_below_kn E4 F kn_nonlin).
    rewrite_env (E4 ++ empty).
    eapply split_below1. eapply S2. simpl_env. auto. 
    eapply wf_env_from_env_below1. apply H1.
    subst. 
    apply ok_join. 
    eapply env_split_splice_ok1. eapply ok_remove_head. eapply ok_from_wf_env. apply WF.
    apply S2. rewrite_env ((E3 ++ E4) ++ empty).
    eapply ok_env_split1. apply H.
    apply ok_commute. eapply env_split_splice_ok2.
    eapply ok_commute. eapply ok_remove_tail. rewrite_env ((G ++ F) ++ E0) in WF.
    eapply ok_from_wf_env. apply WF. eapply env_split_commute. apply S3.
    eapply (IHTyp2 F2 F1); auto.
    subst E1. subst E2. 
    rewrite_env (F2 ++ empty).
    eapply split_below2. apply S2. simpl_env. auto.
    
    apply wf_env_weakening2.
    eapply wf_env_from_typing. subst E2. apply Typ2.
    rewrite_env ((F ++ F2) ++ empty).
    eapply wf_split_env1. eapply env_split_commute. 
    eapply env_split_weakening1. apply S2. simpl_env. auto.
    apply ok_join. 
    eapply env_split_splice_ok2. eapply ok_remove_head. eapply ok_from_wf_env. apply WF.
    apply S2. rewrite_env ((F1 ++ F2) ++ empty).
    eapply ok_env_split1. eapply env_split_commute. subst E2. apply H.
    apply ok_commute. eapply env_split_splice_ok2.
    eapply ok_commute. eapply ok_remove_tail. rewrite_env ((G ++ F) ++ E0) in WF.
    eapply ok_from_wf_env. apply WF. apply S3.
  
    subst. apply env_split_weakening; simpl_env in *; auto. 

    auto.

  Case "tabs".
    pick fresh X and apply typing_tabs.
    auto.
    lapply (H1 X); [intros Q | auto].
    rewrite <- concat_assoc.
    apply H1... rewrite EQ. auto.

  Case "tapp".
    subst E.  eapply typing_tapp. apply IHTyp. auto. auto. auto. 
    apply wf_typ_weakening. auto. auto.
Qed.


(************************************************************************ *)
(** ** Type substitution preserves typing (11) *)

Lemma env_split_below_kn1: forall H G F E GX,
  env_split G F E GX ->
  env_below_kn (G ++ GX) H kn_nonlin ->
  ok (H ++ E ++ GX) ->
  env_below_kn (E ++ GX) H kn_nonlin.
Proof.
  induction H; intros G F E GX S K OK.
  Case "empty".
   apply env_below_empty. eapply wf_env_split0. apply S.
  Case "cons".
   inversion K; subst; simpl_env in *.
   apply env_below_bind_kn. eapply IHlist; eauto.
   eapply ok_remove_head. apply OK.
   rewrite_env (([(X, bind_kn K1)] ++ H) ++ E ++ GX).
   eapply wf_env_split_splice1. simpl_env. apply OK. apply S.
   simpl_env. auto.
   apply env_below_bind_typ. eapply IHlist; eauto.
   eapply ok_remove_head. apply OK.
   rewrite_env (([(x, bind_typ T)] ++ H) ++ E ++ GX).
   eapply wf_env_split_splice1. simpl_env. apply OK. apply S.
   simpl_env. auto.
   eapply wf_typ_split_splice. apply H6. apply S.
   eapply ok_remove_head. apply OK.
Qed.
   
Lemma ok_map_app_l_inv : forall (E:env) F f,
  ok (map f F ++ E) -> ok (F ++ E).
Proof with auto.
  intros. induction F as [|(y,a)]; simpl...
  apply ok_cons. apply IHF; auto.
  simpl in H. eapply ok_remove_head. simpl_env in H. apply H.
  simpl in H. inversion H. rewrite dom_concat in H4. rewrite dom_map in H4.
  rewrite dom_concat. fsetdec.
Qed.

Lemma map_subst_tb_id2 : forall E G Z P,
  wf_env (E ++ G) ->
  Z `notin` dom (E ++ G) ->
  (E ++ G) = (map (subst_tb Z P) E ++ G).
Proof with auto.
  intros.
  induction E; simpl_env in *.
  auto.
  simpl. destruct a. destruct b; simpl in *.
  rewrite IHE. auto. eapply wf_env_strengthening2. simpl_env in H. apply H.
  fsetdec.
  rewrite <- subst_tt_fresh. rewrite IHE; auto.
  eapply wf_env_strengthening2. simpl_env in H. apply H.
  inversion H. subst. eapply notin_fv_wf. apply H5. rewrite dom_concat.
  fsetdec.
Qed.

(*
Lemma wf_typ_unsubst: forall E G X P T K1 K2,
  type T ->
  wf_typ G P K1 ->
  wf_env (E ++ [(X, bind_kn K1)] ++ G) ->
  wf_typ (map (subst_tb X P) E ++ G) (subst_tt X P T) K2 -> 
  wf_typ (E ++ [(X, bind_kn K1)] ++ G) T K2.
Proof.
  intros E G X P T K1 K2 TYPE WFT1 WFE WFT2.
  induction TYPE; simpl_env in *; auto.
  simpl in WFT2.
  destruct (X0 == X); subst.
*)  
  
    
(* The following lemma is false with the
   "determinized" version of env_split. 

   Why?  Because substitution doesn't preserve the 
   negated clause in env_split_lin_left or env_split_lin_right.

   That is,  It is possible for these to hold:
      wf_typ G X kn_lin
     ~wf_typ G X kn_nonlin
     
      wf_typ G P kn_lin
      wf_typ G P kn_nonlin

    so when you substitute P for X, the kn_nonlin kinding 
    derivation becomes possible.  

    :-(
*)
Lemma env_split_subst_tb : forall E1 E2 F1 F2 G1 G2 GX X K P,
  env_split (E1 ++ [(X, bind_kn K)] ++ E2) 
            (F1 ++ [(X, bind_kn K)] ++ F2) 
            (G1 ++ [(X, bind_kn K)] ++ G2)
            GX ->
  wf_typ (G2 ++ GX) P K ->
  env_split (map (subst_tb X P) E1 ++ E2) 
            (map (subst_tb X P) F1 ++ F2) 
            (map (subst_tb X P) G1 ++ G2)
            GX.
Proof.
  intros E1 E2 F1 F2 G1 G2 GX X K P S TYP.
  remember (E1 ++ [(X, bind_kn K)] ++ E2) as E.
  remember (F1 ++ [(X, bind_kn K)] ++ F2) as F.
  remember (G1 ++ [(X, bind_kn K)] ++ G2) as G.
  generalize dependent G1. generalize dependent G2.
  generalize dependent F1. generalize dependent F2. 
  generalize dependent E1. generalize dependent E2.
  induction S; intros ER EL Q1 FR FL Q2 GR WFT GL Q3; simpl_env in *.
  Case "empty".
    assert False. eapply empty_noteq_concat. apply Q1. tauto.
  Case "kn".
    destruct EL; simpl in Q1; inversion Q1; subst; simpl_env in *.
    destruct FL; simpl in Q2; inversion Q2; subst; simpl_env in *.
    destruct GL; simpl in Q3; inversion Q3; subst; simpl_env in *.
    auto.
    assert False. fsetdec. tauto.
    
    destruct GL; simpl in Q3; inversion Q3; subst; simpl_env in *.
    assert (env_split ([(X, bind_kn K)] ++ ER) 
                      ([(X, bind_kn K)] ++ FL ++ [(X, bind_kn K)] ++ FR) 
                      ([(X, bind_kn K)] ++ GR) G    ).
    apply env_split_weakening1. apply S.
    rewrite_env ([(X, bind_kn K)] ++ empty).
    apply env_below_bind_kn. apply env_below_empty.
    eapply wf_env_split0. apply S. simpl_env. 
    apply wf_env_kn. eapply wf_env_split0. apply S. 
    rewrite dom_concat. fsetdec.
    assert False.
    apply (not_wf_env2 empty FL (FR ++ G) X K K). simpl_env.
    rewrite_env (([(X, bind_kn K)] ++ FL ++ [(X, bind_kn K)] ++ FR) ++ G).
    eapply wf_env_split2. apply H1. tauto.
    assert False.
    fsetdec. tauto.

    destruct FL; simpl in Q2; inversion Q2; subst; simpl_env in *.
    assert (env_split ([(X, bind_kn K)] ++ EL ++ [(X, bind_kn K)] ++ ER) 
                      ([(X, bind_kn K)] ++ FR) 
                      ([(X, bind_kn K)] ++ E3) G    ).
    apply env_split_weakening1. apply S.
    rewrite_env ([(X, bind_kn K)] ++ empty).
    apply env_below_bind_kn. apply env_below_empty.
    eapply wf_env_split0. apply S. simpl_env. 
    apply wf_env_kn. eapply wf_env_split0. apply S. 
    rewrite dom_concat. fsetdec.
    assert False.
    apply (not_wf_env2 empty EL (ER ++ G) X K K). simpl_env.
    rewrite_env (([(X, bind_kn K)] ++ EL ++ [(X, bind_kn K)] ++ ER) ++ G).
    eapply wf_env_split1. apply H1. tauto.

    destruct GL; simpl in Q3; inversion Q3; subst; simpl_env in *.
    assert (env_split ([(X, bind_kn K)] ++ EL ++ [(X, bind_kn K)] ++ ER) 
                      ([(X, bind_kn K)] ++ FL ++ [(X, bind_kn K)] ++ FR) 
                      ([(X, bind_kn K)] ++ GR) G    ).
    apply env_split_weakening1. apply S.
    rewrite_env ([(X, bind_kn K)] ++ empty).
    apply env_below_bind_kn. apply env_below_empty.
    eapply wf_env_split0. apply S. simpl_env. 
    apply wf_env_kn. eapply wf_env_split0. apply S. 
    rewrite dom_concat. fsetdec.
    assert False.
    apply (not_wf_env2 empty EL (ER ++ G) X K K). simpl_env.
    rewrite_env (([(X, bind_kn K)] ++ EL ++ [(X, bind_kn K)] ++ ER) ++ G).
    eapply wf_env_split1. apply H1. tauto.    
    simpl. simpl_env. apply env_split_kn.
    apply IHS; auto. rewrite dom_concat.
    rewrite dom_map. fsetdec. auto.

  Case "nonlin".    
    destruct EL; simpl in Q1; inversion Q1; subst; simpl_env in *.
    destruct FL; simpl in Q2; inversion Q2; subst; simpl_env in *.
    destruct GL; simpl in Q3; inversion Q3; subst; simpl_env in *.
    simpl. simpl_env. 
    apply env_split_nonlin. 
    apply IHS; auto.
    simpl_env. eapply wf_typ_subst_tb.
    simpl_env in H. apply H. auto.
    rewrite dom_concat. rewrite dom_map. fsetdec. auto.


  Case "left".
    destruct EL; simpl in Q1; inversion Q1; subst; simpl_env in *.
    destruct GL; simpl in Q3; inversion Q3; subst; simpl_env in *.
    simpl. simpl_env.
    apply env_split_lin_left.
    apply IHS; auto.
    simpl_env. eapply wf_typ_subst_tb.
    simpl_env in H. apply H. auto.
    rewrite dom_concat. rewrite dom_map. fsetdec.
    rewrite dom_concat. rewrite dom_map. fsetdec.
    auto.

  Case "right".
    destruct FL; simpl in Q2; inversion Q2; subst; simpl_env in *.
    destruct GL; simpl in Q3; inversion Q3; subst; simpl_env in *.
    simpl. simpl_env.
    apply env_split_lin_right.
    apply IHS; auto.
    simpl_env. eapply wf_typ_subst_tb.
    simpl_env in H. apply H. auto.
    rewrite dom_concat. rewrite dom_map. fsetdec.
    rewrite dom_concat. rewrite dom_map. fsetdec.
    auto.
Qed.
    
    
Lemma value_through_subst_te : forall e Z P,
  type P ->
  value e ->
  value (subst_te Z P e).
Proof.
  intros e Z P Typ H.
  induction H. 
  assert (expr (subst_te Z P (exp_abs K T e1))).
  apply subst_te_expr. auto. auto.
  simpl. apply value_abs. simpl in H0. auto.
  assert (expr (subst_te Z P (exp_tabs K e1))).
  apply subst_te_expr; auto.
  simpl. apply value_tabs. simpl in H0. auto.
Qed.

Lemma typing_through_subst_te : forall K E F Z e T P,
  typing (F ++ [(Z, bind_kn K)] ++ E) e T ->
  wf_typ E P K ->
  typing (map (subst_tb Z P) F ++ E) (subst_te Z P e) (subst_tt Z P T).
Proof with simpl_env;
           eauto 6 using wf_env_subst_tb,
                         wf_typ_subst_tb.

  intros K E F Z e T P Typ PsubK.
  remember (F ++ [(Z, bind_kn K)] ++ E) as G.
  generalize dependent F. generalize dependent E.
  induction Typ; intros E0 WFT F EQ; subst;
    simpl subst_te in *; simpl subst_tt in *...
  Case "typing_var".
    lapply (env_cases E2 E1 F E0 (x, bind_typ T) (Z, bind_kn K)).
    intros. destruct H1 as [[M [EQL EQR]] | [M [EQL EQR]]]; auto.
    rewrite <- EQ; auto.
    subst. simpl_env. simpl subst_tb. apply typing_var. 
    rewrite_env (map (subst_tb Z P) (E2 ++ [(x, bind_typ T)] ++ M) ++ E0). eapply wf_env_subst_tb. simpl_env. apply H. auto.
    rewrite_env (map (subst_tb Z P) (E2 ++ M) ++ E0). eapply env_below_kn_subst_tb. simpl_env. apply H0. auto.
    subst. rewrite_env ((map (subst_tb Z P) F ++ M) ++ [(x, bind_typ T)] ++ E1). 
    assert (exists K, wf_typ E1 T K). eapply wf_typ_from_wf_env_typ.  eapply wf_env_strengthening2. apply H. destruct H1 as [K2 WF2]. 
    rewrite <- subst_tt_fresh. apply typing_var.
    simpl_env. eapply wf_env_subst_tb. simpl_env in H. apply H. auto. simpl_env. eapply env_below_kn_subst_tb. simpl_env in H0. apply H0.
    eapply wf_typ_strengthening. eapply WFT. eapply notin_fv_tail. simpl_env in H. apply H.
    rewrite_env (empty ++ (M ++ [(x, bind_typ T)]) ++ E1). eapply wf_typ_weakening. simpl_env. apply WF2.
    simpl_env. eapply ok_from_wf_typ. eauto. unfold not; intros. inversion H1.
    
  Case "typing_abs".
    pick fresh y and apply typing_abs.
    eapply env_below_kn_subst_tb. apply H. auto.
    eapply wf_typ_subst_tb. apply H0. auto.
    rewrite subst_te_open_ee_var...
    rewrite_env (map (subst_tb Z P) ([(y, bind_typ V)] ++ F) ++ E0).
    apply H2...

  Case "typing_app".
    lapply (split_destruct2 E1 E2 F E0 empty Z K). 
    intros H0. destruct H0 as [F1 [F2 [E01 [E02 [S2 [EQ1 [EQ2 S3]]]]]]].
    eapply typing_app. 
    lapply (IHTyp1 E01). intros. lapply (H0 F1); intros; auto. apply H1.
    rewrite_env (E01 ++ empty).
    eapply wf_split_typ1.  rewrite_env (E0 ++ empty) in WFT. apply WFT. apply S2.
    lapply (IHTyp2 E02). intros. lapply (H0 F2); intros; auto. apply H1.
    rewrite_env (E02 ++ empty).
    eapply wf_split_typ2. rewrite_env (E0 ++ empty) in WFT. apply WFT. apply S2.
    subst.
    eapply env_split_subst_tb. assert (wf_env (F1 ++ [(Z, bind_kn K)] ++ E01)). eapply wf_env_from_typing. apply Typ1.
    apply H.
    simpl_env. auto. auto.

  Case "typing_tabs".
    pick fresh Y and apply typing_tabs.
    apply value_through_subst_te. eapply type_from_wf_typ. apply WFT. auto.
    rewrite subst_te_open_te_var...
    rewrite subst_tt_open_tt_var...
    rewrite_env (map (subst_tb Z P) ([(Y, bind_kn K0)] ++ F) ++ E0).
    apply H1... eapply type_from_wf_typ. eauto. eapply type_from_wf_typ; eauto.

  Case "typing_tapp".
    rewrite subst_tt_open_tt... eapply type_from_wf_typ. eauto.
Qed.

(************************************************************************ *)
(** ** Substitution preserves typing (8) *)


Lemma env_below_kn_weakening_left: forall E G K x T,
  env_below_kn E G K ->
  wf_env (G ++ [(x, bind_typ T)] ++ E) ->
  env_below_kn ([(x, bind_typ T)] ++ E) G K.
Proof.
  intros E G K x T Hyp.
  induction Hyp; intros WF.
  apply env_below_empty.  auto.
  apply env_below_bind_kn. apply IHHyp. auto. 
  simpl_env in WF. inversion WF. simpl. auto.
  simpl_env in WF. auto.
  apply env_below_bind_typ. apply IHHyp.  auto.
  simpl_env in WF. inversion WF. simpl. auto.
  simpl_env in WF. auto.
  eapply wf_typ_weakening. auto. eapply ok_remove_head. simpl_env in WF. 
  apply ok_from_wf_env. apply WF. 
Qed.

(* I'm not sure I need this *)
(*
Lemma env_split_below_kn: forall F E G1 G2 GG,
  env_split G1 E F GG ->
  env_below_kn empty (G2 ++ G1) kn_nonlin ->
  wf_env (G2 ++ F) ->
  env_below_kn F G2 kn_nonlin
.
Proof.
  intros F E G1 G2 S.
  generalize dependent G2.
  induction S; intros G2 Hy WF.
  Case "empty".
    simpl_env in Hy. auto.
  Case "bind_kn".
    apply env_below_kn_assoc1. apply IHS. simpl_env. auto. simpl_env. auto.
  Case "bind_typ".
    apply env_below_kn_assoc1. apply IHS. simpl_env. auto. simpl_env. auto.
  Case "bind_typ".
    apply env_below_kn_assoc1. apply IHS. simpl_env. auto. simpl_env. auto.
  Case "bind_typ".
    eapply env_below_kn_weakening_left. apply IHS; auto. 
    eapply wf_env_strengthening. apply WF. auto.
Qed.

*)

Lemma env_below_weakening_head: forall E F G K,
  env_below_kn G (F ++ E) K ->
  wf_env G -> 
  ok (F ++ E) ->
  env_below_kn G E K
.
Proof.
  intros E F G K Hyp.
  generalize dependent E.
  induction F; intros E B WF OK.
  simpl_env in B. auto.
  apply IHF. simpl in B. inversion B. auto. auto. auto.
  eapply ok_remove_head. rewrite_env ([a] ++ F ++ E) in OK. apply OK.
Qed.


(*
Lemma wf_typ_nonlin_strengthening: forall E2 E1 x T,
  wf_env (E2 ++ [(x, bind_typ T)] ++ E1) -> 
  wf_typ (E2 ++ [(x, bind_typ T)] ++ E1) T kn_nonlin ->
  wf_typ E1 T kn_nonlin.
Proof.
  induction E2; intros E1 x T WF TYP.
  simpl_env in WF. inversion WF. 
*)

(* The following lemmas is false:  Counterexample:
     a:kn_nonlin, f : a -lin> a, x:a |- f x : a

Lemma typing_nonlin_env: forall E e T,
  typing E e T ->
  wf_typ E T kn_nonlin ->
  env_below_kn empty E kn_nonlin.
Proof.
  intros E e T TYP WF.
  induction TYP.
  eapply env_below_kn_weakening3. auto. 
  apply env_below_bind_typ.
  eapply env_below_weakening_head.  apply H0. auto. eapply ok_remove_mid. eapply ok_from_wf_env. apply H.
  simpl_env. eapply wf_env_strengthening2. apply H. simpl_env. 
*)  


(*
a:non, f:a -lin> a, y:a |-  (f y):a
a:non, g: a -> a -> a, x:a |- g x x : a

G1 |- U : K
env_below_kn empty E K
*)

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

Lemma value_through_open_te: forall e1 T,
  value e1 ->
  value (open_te e1 T).
Proof.
  intros.
  unfold open_te. rewrite <- open_te_rec_expr. auto. inversion H. auto. auto.
Qed.

Lemma value_env_below_kn: forall E u U K,
  typing E u U ->
  wf_typ E U K ->
  value u ->
  env_below_kn empty E K.
Proof.
  intros E u U K Typ WFT V.
  induction Typ; inversion V.
  destruct K0. destruct K. auto. 
  inversion WFT. destruct K. apply env_below_kn_sub. auto. auto.

  destruct K.
  inversion WFT. subst.
  pick fresh X. 
  lapply (H1 X). intros. lapply (H0 X). intros. 
  assert (env_below_kn empty ([(X, bind_kn K0)] ++ E) kn_lin).
  apply H2. apply H9.  fsetdec.
  apply value_through_open_te. auto.
  eapply env_below_kn_strengthening1. apply H5.
  fsetdec. fsetdec. subst. inversion H5. 
  subst.   pick fresh X. 
  lapply (H1 X). intros. lapply (H0 X). intros. 
  assert (env_below_kn empty ([(X, bind_kn K0)] ++ E) kn_lin).
  apply H2. apply wf_typ_sub.  apply H8.  fsetdec.
  apply value_through_open_te. auto.
  eapply env_below_kn_strengthening1. apply H6.
  fsetdec. fsetdec. subst. 
  inversion WFT. subst.
  pick fresh X. 
  lapply (H1 X). intros. lapply (H0 X). intros.
  assert (env_below_kn empty ([(X, bind_kn K0)] ++ E) kn_nonlin).
  apply H2. apply H7. fsetdec.
  apply value_through_open_te. auto.
  eapply env_below_kn_strengthening1. apply H5.
  fsetdec. fsetdec. 
Qed.

Lemma env_below_kn_inversion:  forall G2 x U G1 E K, 
  env_below_kn E (G2 ++ [(x, bind_typ U)] ++ G1) K ->
  wf_typ (G1 ++ E) U K.
Proof.
  intros. assert (env_below_kn E ([(x, bind_typ U)]++G1) K).
  eapply env_below_kn_strengthening1. apply H.
  inversion H0. auto.
Qed.

(* This lemma doesn't hold with the nondeterministic treatment
   of nonlinear variables.  It needs more cases. *)
(*
Lemma split_destruct3: forall G1 G2 x0 T E F GG,
  env_split (G1 ++ [(x0, bind_typ T)] ++ G2) E F GG ->
  wf_typ (G2 ++ GG) T kn_nonlin ->
  exists F1, exists F2, exists E1, exists E2,
    F = F1 ++ [(x0, bind_typ T)] ++ F2 /\
    E = E1 ++ [(x0, bind_typ T)] ++ E2 /\   
    env_split G2 E2 F2 GG /\
    env_split G1 F1 E1 ([(x0, bind_typ T)] ++ F2 ++ GG).
Proof.
  intros G1 G2 x0 T E F GG S.
  remember (G1 ++ [(x0, bind_typ T)] ++ G2) as G.
  generalize dependent G1.
  induction S; intros G1 EQ WFT.
  Case "empty".
    assert False. eapply empty_noteq_concat. apply EQ. tauto.
  Case "kn".
    destruct G1. simpl in EQ. inversion EQ.
    simpl in EQ. inversion EQ. 
    destruct (IHS G1) as [F1 [F2 [EL [ER [Q1 [Q2 [S1 S2]]]]]]]. 
    simpl. auto. auto.
    exists ([(X, bind_kn K)] ++ F1).
    exists F2.
    exists ([(X, bind_kn K)] ++ EL).
    exists ER. subst. repeat split; auto.
    simpl_env. apply env_split_kn. apply S2.
    rewrite (dom_env_split G1 F1 EL ([(x0, bind_typ T)] ++ F2 ++ G)).
    assert (X `notin` dom F1). repeat rewrite dom_concat in H. fsetdec.
    rewrite (dom_env_split (G1 ++ (x0, bind_typ T) :: G2)
        (EL ++ [(x0, bind_typ T)] ++ ER) (F1 ++ [(x0, bind_typ T)] ++ F2) G) in H.
    repeat rewrite dom_concat in H. fsetdec. auto. auto.
    repeat rewrite dom_concat. repeat rewrite dom_concat in H. fsetdec.

  Case "nonlin".
    destruct G1. simpl in EQ. inversion EQ.
    subst. 
    exists empty. exists E3. exists empty. exists E2.
    repeat split; auto.
    apply env_split_empty.
    eapply wf_env_typ. eapply wf_env_split0. apply S. apply H. 
    rewrite dom_concat. fsetdec.
    
    simpl in EQ. inversion EQ; subst.
    destruct (IHS G1) as [F1 [F2 [EL [ER [Q1 [Q2 [S1 S2]]]]]]]. 
    simpl. auto. auto.
    exists ([(x, bind_typ T0)] ++ F1).  
    exists F2.
    exists ([(x, bind_typ T0)] ++ EL).
    exists ER.
    subst. repeat split; auto. 
    simpl_env. apply env_split_nonlin. auto.
    simpl_env in H. auto.
    eapply wf_typ_split2. apply H. apply S2.
    rewrite (dom_env_split (G1 ++ (x0, bind_typ T) :: G2)
        (EL ++ [(x0, bind_typ T)] ++ ER) (F1 ++ [(x0, bind_typ T)] ++ F2) G) in H0.
    repeat rewrite dom_concat in H0. fsetdec. auto.
    rewrite dom_concat. simpl. rewrite dom_concat.
    repeat rewrite dom_concat in H0. simpl in H0. fsetdec.

  Case "left".
   destruct G1; simpl in EQ; inversion EQ. 
   subst.  assert (wf_typ E3 T kn_nonlin). eapply wf_typ_split1. 
   apply XXX_FIX_OK. apply WFT. apply S. contradiction.
   simpl in EQ. inversion EQ. subst.
   destruct (IHS G1) as [F1 [F2 [EL [ER [Q1 [Q2 S1]]]]]]. 
   simpl.  auto. auto.
   exists ([(x, bind_typ T0)] ++ F1).
   exists F2.
   exists EL.
   exists ER.
   subst. repeat split; auto.
  Case "right".
   destruct G1. simpl in EQ. inversion EQ.
   subst.  
   destruct (IHS empty) as [F1 [F2 [EL [ER [Q1 [Q2 S1]]]]]]. 
   simpl.  auto. auto.
   exists ([(x, bind_typ T0)] ++ F1).
   exists F2.  
   exists ([(x, bind_typ T0)] ++ EL).
   exists ER.
   subst. repeat split; auto.
  
   destruct (IHS ([p] ++ G1)) as [F1 [F2 [EL [ER [Q1 [Q2 S1]]]]]]. 
   simpl. auto. auto.
   exists ([(x, bind_typ T0)] ++ F1).
   exists F2.
   exists ([(x, bind_typ T0)] ++ EL).
   exists ER.
   subst. simpl. repeat split; auto.
Qed.
*)

Lemma wf_env_weaken_split: forall E1 E2 E3 G x T,
  wf_env ([(x, bind_typ T)] ++ E3 ++ G) ->
  env_split E1 E2 E3 G ->
  wf_env ([(x, bind_typ T)] ++ E1 ++ G).
Proof.
  intros.
  assert (exists K, wf_typ (E3 ++ G) T K).
  eapply wf_env_inversion. rewrite_env (empty ++ [(x, bind_typ T)] ++ E3 ++ G) in H.
  apply H.
  destruct H1.
  eapply wf_env_typ.
  eapply wf_split_env1. apply H0. 
  eapply wf_split_typ1. apply H1. apply H0. 
  inversion H. rewrite dom_concat in H7. rewrite (dom_env_split E1 E2 E3 G) in H7. 
  rewrite dom_concat. fsetdec. auto.
Qed.

(* Need to combine this with split_destruct3, probably. *)  
(*
Lemma split_destruct4: forall G1 G2 x0 T E F, 
  env_split (G1 ++ [(x0, bind_typ T)] ++ G2) E F ->
  ~ wf_typ G2 T kn_nonlin ->
  exists F1, exists F2, exists E1, exists E2,
    F = F1 ++ [(x0, bind_typ T)] ++ F2 /\
    E = E1 ++ E2 /\   
    env_split G2 E2 F2.
Proof.
  intros G1 G2 x0 T E F S.
  remember (G1 ++ [(x0, bind_typ T)] ++ G2) as G.
  generalize dependent G1.
  induction S; intros G1 EQ NWFT.
  Case "empty".
    assert False. eapply empty_noteq_concat. apply EQ. tauto.
  Case "kn".
    destruct G1. simpl in EQ. inversion EQ.
    simpl in EQ. inversion EQ. 
    destruct (IHS G1) as [F1 [F2 [EL [ER [Q1 [Q2 S1]]]]]]. 
    simpl. auto. auto. auto.
    exists ([(X, bind_kn K)] ++ F1).
    exists F2.
    exists ([(X, bind_kn K)] ++ EL).
    exists ER. subst. repeat split; auto.
  Case "nonlin".
    destruct G1. simpl in EQ. inversion EQ.
    subst. 
    exists empty. exists E3. exists [(x0, bind_typ T)]. exists E2.
    repeat split; auto.
    simpl in EQ. inversion EQ; subst.
    destruct (IHS G1) as [F1 [F2 [EL [ER [Q1 [Q2 S1]]]]]]. 
    simpl. auto. auto. auto.
    exists ([(x, bind_typ T0)] ++ F1).  
    exists F2.
    exists ([(x, bind_typ T0)] ++ EL).
    exists ER.
    subst. repeat split; auto. 
  Case "left".
   destruct G1. simpl in EQ. inversion EQ.
   subst.  exists empty. exists E3. exists empty. exists E2.
   simpl. repeat split;auto.
   simpl in EQ. inversion EQ. subst.
   destruct (IHS G1) as [F1 [F2 [EL [ER [Q1 [Q2 S1]]]]]]. 
   simpl.  auto. auto. auto.
   exists ([(x, bind_typ T0)] ++ F1).
   exists F2.
   exists EL.
   exists ER.
   subst. repeat split; auto.
  Case "right".
   destruct (IHS G1) as [F1 [F2 [EL [ER [Q1 [Q2 S1]]]]]]. 
   auto. auto. auto. 
   exists ([(x, bind_typ T0)] ++ F1).
   exists F2.  
   exists ([(x, bind_typ T0)] ++ EL).
   exists ER.
   subst. simpl. repeat split; auto.
Qed.
*)

(*
Lemma split_destruct5: forall G1 G2 x0 T E F, 
  env_split E F (G1 ++ [(x0, bind_typ T)] ++ G2) ->
  wf_typ G2 T kn_nonlin ->
  exists E1, exists E2, exists F1, exists F2,
    E = E1 ++ [(x0, bind_typ T)] ++ E2 /\ 
    F = F1 ++ [(x0, bind_typ T)] ++ F2 /\ 
    env_split E2 F2 G2.
Proof.
  intros G1 G2 x0 T E F S WFT.
  remember (G1 ++ [(x0, bind_typ T)] ++ G2) as G.
  generalize dependent G1.
  induction S; intros G1 EQ.
  Case "empty".
    assert False. eapply empty_noteq_concat. eauto. tauto.
  Case "kn".
    destruct G1. simpl in EQ. inversion EQ.
    simpl in EQ. inversion EQ; subst.
    lapply (IHS G1). intros. 
    destruct H as [E3 [E4 [F1 [F2 [Q1 [Q2 S2]]]]]].
    exists ([(X, bind_kn K)] ++ E3).
    exists E4.
    exists ([(X, bind_kn K)] ++ F1).
    exists F2.
    subst. simpl. repeat split;auto. simpl. auto.
  Case "nonlin".
    destruct G1. simpl in EQ. inversion EQ. subst.
    exists empty. exists E1. exists empty. exists E2.
    simpl_env. repeat split; auto.
    simpl in EQ. inversion EQ. subst.
    lapply (IHS G1). intros.
    destruct H0 as [E3 [E4 [F1 [F2 [Q1 [Q2 S2]]]]]].
    exists ([(x, bind_typ T0)] ++ E3).
    exists E4.
    exists ([(x, bind_typ T0)] ++ F1).
    exists F2.
    subst. simpl. repeat split;auto. simpl. auto.
  Case "left".
    destruct G1. simpl in EQ. inversion EQ. subst. contradiction.
    simpl in EQ. inversion EQ. subst.
    lapply (IHS G1). intros.
    destruct H2 as [E3 [E4 [F1 [F2 [Q1 [Q2 S2]]]]]].
    exists ([(x, bind_typ T0)] ++ E3).
    exists E4.
    exists F1.
    exists F2.
    subst. simpl. repeat split;auto. simpl. auto.
  Case "right".
    destruct G1. simpl in EQ. inversion EQ. subst. contradiction.
    simpl in EQ. inversion EQ. subst.
    lapply (IHS G1). intros.
    destruct H2 as [E3 [E4 [F1 [F2 [Q1 [Q2 S2]]]]]].
    exists E3.
    exists E4.
    exists ([(x, bind_typ T0)] ++ F1).
    exists F2.
    subst. simpl. repeat split;auto. simpl. auto.
Qed.
    
Lemma split_destruct6: forall G1 G2 x0 T E F,
  wf_env (G1 ++ [(x0, bind_typ T)] ++ G2) ->
  env_split E F (G1 ++ [(x0, bind_typ T)] ++ G2) ->
  ~ wf_typ G2 T kn_nonlin ->
  (exists E1, exists E2, exists F1, exists F2,
    E = E1 ++ [(x0, bind_typ T)] ++ E2 /\ 
    F = F1 ++ F2 /\
    env_split E2 F2 G2 /\
    x0 `notin` dom F
  ) \/
  (exists E1, exists E2, exists F1, exists F2,
    E = E1 ++ E2 /\
    F = F1 ++ [(x0, bind_typ T)] ++ F2 /\ 
    env_split E2 F2 G2 /\
    x0 `notin` dom E
  ).
Proof.
  intros G1 G2 x0 T E F WFE S WFT.
  remember (G1 ++ [(x0, bind_typ T)] ++ G2) as G.
  generalize dependent G1.
  induction S; intros G1 EQ.
  Case "empty".
    assert False. eapply empty_noteq_concat. eauto. tauto.
  Case "kn".
    destruct G1. simpl in EQ. inversion EQ.
    simpl in EQ. inversion EQ; subst.
    assert (wf_env (G1 ++ (x0, bind_typ T) :: G2)) as WFE2.
    eapply wf_env_strengthening2. apply WFE.
    lapply (IHS WFE2 G1). intros. 
    destruct H.
    left. destruct H as [E3 [E4 [F1 [F2 [Q1 [Q2 [S2 NI]]]]]]]. 
    exists ([(X, bind_kn K)] ++ E3).
    exists E4.
    exists ([(X, bind_kn K)] ++ F1).
    exists F2.
    subst. simpl. repeat split;auto. destruct (x0 == X).  subst X.
    assert False. assert (x0 `notin` dom [(x0, bind_kn K)]).
    eapply fresh_mid_head_In. 
    eapply ok_from_wf_env. 
    rewrite_env ([(x0, bind_kn K)] ++ (G1 ++ [(x0, bind_typ T)] ++ G2) ++ empty) in WFE.
    apply WFE. rewrite dom_concat. rewrite dom_concat. simpl. fsetdec. 
    apply H. simpl. fsetdec. tauto. fsetdec.

    right. destruct H as [E3 [E4 [F1 [F2 [Q1 [Q2 [S2 NI]]]]]]]. 
    exists ([(X, bind_kn K)] ++ E3).
    exists E4.
    exists ([(X, bind_kn K)] ++ F1).
    exists F2.
    subst. simpl. repeat split;auto.
    destruct (x0 == X).  subst X.
    assert False. assert (x0 `notin` dom [(x0, bind_kn K)]).
    eapply fresh_mid_head_In. 
    eapply ok_from_wf_env. 
    rewrite_env ([(x0, bind_kn K)] ++ (G1 ++ [(x0, bind_typ T)] ++ G2) ++ empty) in WFE.
    apply WFE. rewrite dom_concat. rewrite dom_concat. simpl. fsetdec. 
    apply H. simpl. fsetdec. tauto. fsetdec.

    simpl. auto.

  Case "nonlin".
    destruct G1. simpl in EQ. inversion EQ. subst. contradiction.
    simpl in EQ. inversion EQ. subst.
    assert (wf_env (G1 ++ (x0, bind_typ T) :: G2)) as WFE2.
    eapply wf_env_strengthening2. apply WFE.
    lapply (IHS WFE2 G1). intros.
    destruct H0.

    left. destruct H0 as [E3 [E4 [F1 [F2 [Q1 [Q2 [S2 NI]]]]]]].
    exists ([(x, bind_typ T0)] ++ E3).
    exists E4.
    exists ([(x, bind_typ T0)] ++ F1).
    exists F2.
    subst. simpl. repeat split;auto. simpl. auto.
    destruct (x == x0). subst x.
    assert False.
    apply (not_wf_env empty G1 G2 x0 T0 T). simpl_env. simpl_env in WFE. apply WFE.
    fsetdec. fsetdec.

    right. destruct H0 as [E3 [E4 [F1 [F2 [Q1 [Q2 [S2 NI]]]]]]].
    exists ([(x, bind_typ T0)] ++ E3).
    exists E4.
    exists ([(x, bind_typ T0)] ++ F1).
    exists F2.
    subst. simpl. repeat split;auto. simpl. auto.
    destruct (x == x0). subst x.
    assert False.
    apply (not_wf_env empty G1 G2 x0 T0 T). simpl_env. simpl_env in WFE. apply WFE.
    fsetdec. fsetdec.
    auto.

  Case "left".
    destruct G1. simpl in EQ. inversion EQ. subst. 
    left. exists empty. exists E1. exists empty. exists E2. simpl_env. 
    repeat split; auto.

    simpl in EQ. inversion EQ. subst.
    assert (wf_env (G1 ++ (x0, bind_typ T) :: G2)) as WFE2.
    eapply wf_env_strengthening2. apply WFE.

    lapply (IHS WFE2 G1). intros.
    destruct H2.

    left. destruct H2 as [E3 [E4 [F1 [F2 [Q1 [Q2 [S2 NI]]]]]]].
    exists ([(x, bind_typ T0)] ++ E3).
    exists E4.
    exists F1.
    exists F2.
    subst. simpl. repeat split;auto. simpl. auto.

    right. destruct H2 as [E3 [E4 [F1 [F2 [Q1 [Q2 [S2 NI]]]]]]].
    exists ([(x, bind_typ T0)] ++ E3).
    exists E4.
    exists F1.
    exists F2.
    subst. simpl. repeat split;auto. simpl. auto.
    destruct (x == x0). subst x.
    assert False.
    apply (not_wf_env empty G1 G2 x0 T0 T). simpl_env. simpl_env in WFE. apply WFE.
    fsetdec. fsetdec.
    auto.

  Case "right".
    destruct G1. simpl in EQ. inversion EQ. subst. 
    right. exists empty. exists E1. exists empty. exists E2. simpl_env. 
    repeat split; auto.

    simpl in EQ. inversion EQ. subst.
    assert (wf_env (G1 ++ (x0, bind_typ T) :: G2)) as WFE2.
    eapply wf_env_strengthening2. apply WFE.

    lapply (IHS WFE2 G1). intros.
    destruct H2.

    left. destruct H2 as [E3 [E4 [F1 [F2 [Q1 [Q2 [S2 NI]]]]]]].
    exists E3.
    exists E4.
    exists ([(x, bind_typ T0)] ++ F1).
    exists F2.
    subst. simpl. repeat split;auto. simpl. auto.
    destruct (x == x0). subst x.
    assert False.
    apply (not_wf_env empty G1 G2 x0 T0 T). simpl_env. simpl_env in WFE. apply WFE.
    fsetdec. fsetdec.
    auto.


    right. destruct H2 as [E3 [E4 [F1 [F2 [Q1 [Q2 [S2 NI]]]]]]].
    exists E3.
    exists E4.
    exists ([(x, bind_typ T0)] ++ F1).
    exists F2.
    subst. simpl. repeat split;auto. simpl. auto.
Qed.

*)

Lemma split_env_below_kn_weakening1:  forall G E1 E2 E3 GG K,
  env_below_kn GG (G ++ E1) K ->
  env_below_kn GG E3 K ->
  env_split E1 E2 E3 GG ->
  wf_env (G ++ E3 ++ GG) ->
  env_below_kn GG (G ++ E3) K.
Proof.
  induction G; intros E1 E2 E3 GG K H1 H2 S WF.
  simpl_env. auto.
  rewrite_env ([a] ++ G ++ E1) in H1.
  rewrite_env ([a] ++ G ++ E3).
  inversion H1; subst.
  apply env_below_bind_kn. eapply IHG; eauto. 
  simpl_env in WF. inversion WF. auto. simpl_env. simpl_env in WF. auto.
  apply env_below_bind_typ. eapply IHG; eauto.
  simpl_env in WF. inversion WF. auto. simpl_env. simpl_env in WF. auto.
  simpl_env. eapply wf_typ_split_splice. simpl_env in H7. apply H7. apply S.
  eapply ok_remove_head. eapply ok_from_wf_env. simpl_env in WF. apply WF.
Qed.

Lemma split_destruct3: forall E1 E2 F G1 G2 GG x0 T,
  env_split (E2 ++ [(x0, bind_typ T)] ++ E1) F (G2 ++ [(x0, bind_typ T)] ++ G1) GG ->
  exists F1,
    env_split E1 F1 G1 GG.
Proof.
  intros E1 E2 F G1 G2 GG x0 T S.
  remember (E2 ++ [(x0, bind_typ T)] ++ E1) as E.
  remember (G2 ++ [(x0, bind_typ T)] ++ G1) as G.
  generalize dependent E2. generalize dependent E1.
  generalize dependent G2. generalize dependent G1.
  induction S; intros GR GL EQ1 ER EL EQ2.
  Case "empty".
    assert False. eapply empty_noteq_concat. apply EQ1. tauto.
  Case "kn".
    destruct GL; inversion EQ1; subst.
    destruct EL; inversion EQ2; subst.
    lapply (IHS GR GL); auto. intros.
    lapply (H1 ER EL); auto.
  Case "nonlin".
    destruct GL; inversion EQ1; subst.
    destruct EL; inversion EQ2; subst.
    exists E2. auto.
    rewrite (dom_env_split (EL ++ (x0, bind_typ T) :: ER) E2 GR G) in H0.
    rewrite dom_concat in H0. simpl in H0.
    assert False. apply H0. fsetdec. tauto.
    simpl_env. simpl_env in S. apply S.

    destruct EL; inversion EQ2; subst.
    assert False. apply H0. rewrite dom_concat. simpl. fsetdec. tauto.

    eapply IHS; eauto.

  Case "left".
    destruct GL; inversion EQ1; subst.
    destruct EL; inversion EQ2; subst.
    exists E2; auto.
    rewrite (dom_env_split (EL ++ (x0, bind_typ T) :: ER) E2 GR G) in H1.
    rewrite dom_concat in H1. simpl in H1.
    assert False. apply H1. fsetdec. tauto.
    simpl_env in S. simpl_env. apply S.

    destruct EL; inversion EQ2; subst.
    assert False. apply H1. rewrite dom_concat. simpl. fsetdec. tauto.

    eapply IHS; eauto.

  Case "right".
    destruct GL; inversion EQ1; subst.
    assert False. apply H0. rewrite dom_concat. simpl. fsetdec. tauto.
    eapply IHS; eauto.
Qed.

Lemma binds_split1: forall E1 E2 E3 G X K,
  binds X (bind_kn K) (E1 ++ G) ->
  env_split E1 E2 E3 G ->
  binds X (bind_kn K) (E3 ++ G).
Proof.
  intros E1 E2 E3 G X K B S.
  induction S; simpl_env in *; auto.
  remember (E1 ++ G) as H.
  binds_cases B.
    apply binds_tail. apply IHS. auto. auto.
    inversion H4; subst.
    apply binds_head. auto.
  Case "nonlin".
  remember (E1 ++ G) as H.
  binds_cases B.
    apply binds_tail. apply IHS. auto. auto.

  Case "left".    
  remember (E1 ++ G) as H.
  binds_cases B.
    apply binds_tail. apply IHS. auto. auto.

  Case "right".
  destruct (X == x). subst.
    assert (x `in` dom (E1 ++ G)).
    eapply binds_in_dom. apply B. assert False. rewrite dom_concat in H3. fsetdec. 
     tauto.
    apply binds_tail. apply IHS. auto. auto.
Qed.    

Lemma binds_split2: forall E1 E2 E3 G X K,
  binds X (bind_kn K) (E2 ++ G) ->
  env_split E1 E2 E3 G ->
  binds X (bind_kn K) (E3 ++ G).
Proof.  
  intros. eapply binds_split1. apply H.
  eapply env_split_commute. apply H0.
Qed.

Lemma env_split_wf_typ1: forall E1 E2 F G1 G2 GG x0 T K,
  wf_typ (E1 ++ GG) T K ->
  env_split (E2 ++ [(x0, bind_typ T)] ++ E1) F (G2 ++ [(x0, bind_typ T)] ++ G1) GG ->
  wf_typ (G1 ++ GG) T K.
Proof.
  intros E1 E2 F G1 G2 GG x0 T K WFT S.
  assert (exists F1, env_split E1 F1 G1 GG).
  eapply split_destruct3. apply S. destruct H. 
  eapply wf_typ_split1. apply WFT.
  apply H.
Qed.
  

Lemma wf_typ_inversion: forall E2 E1 x0 T K,
  wf_env (E2 ++ [(x0, bind_typ T)] ++ E1) ->
  wf_typ (E2 ++ [(x0, bind_typ T)] ++ E1) T K ->
  wf_typ E1 T K.
Proof.
  intros E2 E1 x0 T K WFE WFT.
  remember (E2 ++ [(x0, bind_typ T)] ++ E1) as E.
  generalize dependent E2.
  induction WFE; intros E2 EQ.
  Case "empty".
    assert False. eapply empty_noteq_concat; eauto. tauto.
  Case "kn".
   destruct E2. simpl in EQ. inversion EQ.
   simpl in EQ. inversion EQ; subst.
   eapply IHWFE. rewrite_env (empty ++ E2 ++ [(x0, bind_typ T)] ++ E1).
   eapply wf_typ_strengthening2. simpl_env. simpl_env in WFT. apply WFT.
   assert (exists K1, wf_typ E1 T K1).   
   eapply wf_env_inversion. simpl_env in WFE. apply WFE. destruct H0.
   unfold not. intros.
   assert (X `in` dom E1).
   eapply fv_tt_in_wf_typ. apply H0.  auto. rewrite dom_concat in H. simpl in H.
   fsetdec.
   simpl_env. simpl_env in WFE. apply ok_from_wf_env. auto. eauto.
   Case "typ".
   destruct E2. simpl in EQ. inversion EQ. subst.
   rewrite_env (empty ++ E1). 
   eapply wf_typ_strengthening. simpl_env. apply WFT.
   simpl in EQ. inversion EQ; subst.
   eapply IHWFE.  simpl_env. 
   rewrite_env (empty ++ (E2 ++ [(x0, bind_typ T)] ++ E1)).
   eapply wf_typ_strengthening. simpl_env. simpl_env in WFT. apply WFT.
   eauto.
Qed.

Lemma env_split_strengthening1: forall  E1 E2 F G1 G2 GG x0 T,
  wf_typ (E1 ++ GG) T kn_lin ->
  ~ wf_typ (E1 ++ GG) T kn_nonlin ->
  env_split (E2 ++ [(x0, bind_typ T)] ++ E1) F (G2 ++ [(x0, bind_typ T)] ++ G1) GG ->
  env_split (E2 ++ E1) F (G2 ++ G1) GG.
Proof.
  intros E1 E2 F G1 G2 GG x0 T WFT NWFT S.
  remember (E2 ++ [(x0, bind_typ T)] ++ E1) as E.
  remember (G2 ++ [(x0, bind_typ T)] ++ G1) as G.
  generalize dependent G2. generalize dependent E2.
  induction S; intros EN EQ1 GN EQ2.
  Case "empty".
    assert False. eapply empty_noteq_concat; eauto. tauto.
  Case "kn".
    destruct EN. simpl in EQ1. inversion EQ1.
    destruct GN. simpl in EQ2. inversion EQ2.
      simpl in *. inversion EQ1; inversion EQ2; subst.
    simpl_env. apply env_split_kn. 
    eapply IHS; eauto.
    rewrite dom_concat. simpl_env in H. fsetdec. auto.

  Case "nonlin".
    destruct EN. simpl in EQ1. 
    destruct GN. simpl in EQ2. 
    inversion EQ1; inversion EQ2; subst.
    assert (wf_typ (E1 ++ G) T kn_nonlin).
    eapply wf_split_typ1. apply H. apply S. contradiction.
    inversion EQ1; inversion EQ2; subst.  
    assert (wf_typ (E1 ++ G) T kn_nonlin).
    eapply wf_split_typ1. apply H. apply S. contradiction.
    destruct GN. simpl in EQ2. simpl in EQ1.
    inversion EQ1; inversion EQ2; subst.   
    rewrite (dom_env_split (EN ++ (x0, bind_typ T) :: E1) E2 G1 G) in H0; auto.
    simpl_env in H0. assert False. fsetdec. tauto.
    simpl in EQ2. simpl in EQ1.
    inversion EQ1; inversion EQ2; subst.
    simpl_env. apply env_split_nonlin. 
    eapply IHS; simpl_env in *; auto. simpl_env.
    eapply wf_typ_strengthening. simpl_env in H. apply H.
    simpl_env. simpl_env in *. fsetdec. auto.

  Case "left".
    destruct EN; simpl in EQ1; destruct GN; simpl in EQ2.
    inversion EQ1; inversion EQ2; subst.
    simpl_env. auto.
    inversion EQ1; inversion EQ2; subst. 
    assert False. simpl_env in H1. fsetdec. tauto.
    inversion EQ2; subst. inversion EQ1. subst.
    rewrite (dom_env_split (EN ++ (x0, bind_typ T) :: E1) E2 G1 G) in H1; auto.
    simpl_env in H1. assert False. fsetdec. tauto.

    inversion EQ1; inversion EQ2; subst.
    simpl_env.
    apply env_split_lin_left; auto.
    simpl_env in *.
    eapply wf_typ_strengthening. apply H.
    simpl_env in *. fsetdec.

  Case "right".
    destruct GN.
    simpl in EQ2. inversion EQ2; subst. 

    assert False. simpl_env in H0. fsetdec. tauto.
    simpl in EQ2. inversion EQ2; subst.
    simpl_env. apply env_split_lin_right.
    eapply IHS; auto. 
    simpl_env.
    eapply wf_typ_strengthening. simpl_env in H. apply H.
    simpl_env in *. fsetdec.
    simpl_env in *. fsetdec. auto.
Qed.

Lemma env_split_strengthening2: forall  x0 T E1 E2 F1 F2 G1 G2 GG,
  env_split (E2 ++ [(x0, bind_typ T)] ++ E1) 
            (F2 ++ [(x0, bind_typ T)] ++ F1) 
            (G2 ++ [(x0, bind_typ T)] ++ G1) GG ->
  env_split (E2 ++ E1) (F2 ++ F1) (G2 ++ G1) GG.
Proof.
  intros x0 T E1 E2 F1 F2 G1 G2 GG S.
  remember (E2 ++ [(x0, bind_typ T)] ++ E1) as E.
  remember (F2 ++ [(x0, bind_typ T)] ++ F1) as F.
  remember (G2 ++ [(x0, bind_typ T)] ++ G1) as G.
  generalize dependent G2. generalize dependent F2. generalize dependent E2.
  generalize dependent G1. generalize dependent F1. generalize dependent E1.
  induction S; intros ER FR GR EN EQ1 FN EQ2 GN EQ3.
  Case "empty". 
    assert False. eapply empty_noteq_concat; eauto. tauto.
  Case "kn".
    destruct EN. simpl in EQ1. inversion EQ1.
    destruct FN. simpl in EQ2. inversion EQ2.
    destruct GN. simpl in EQ3. inversion EQ3.
      simpl in *. inversion EQ1; inversion EQ2; inversion EQ3; subst.
    simpl_env. apply env_split_kn; simpl_env in *; try fsetdec; auto.

  Case "nonlin".
    destruct EN; simpl in EQ1; inversion EQ1; subst.
    destruct FN; simpl in EQ2; inversion EQ2; subst.
    destruct GN; simpl in EQ3; inversion EQ3; subst. 
      simpl_env; auto.
      simpl_env in *. assert False. fsetdec. tauto.

      rewrite (dom_env_split ER (FN ++ (x0, bind_typ T) :: FR) E3 G) in H0; auto.
      simpl_env in *. assert False. fsetdec. tauto.

    destruct FN; simpl in EQ2; inversion EQ2; subst.
    destruct GN; simpl in EQ3; inversion EQ3; subst.

      rewrite (dom_env_split (EN ++ (x0, bind_typ T) :: ER) FR GR G) in H0; auto.
        simpl_env in *. assert False. fsetdec. tauto.

      simpl_env in *. assert False. fsetdec. tauto.

    destruct GN; simpl in EQ3; inversion EQ3; subst.
      rewrite (dom_env_split (EN ++ (x0, bind_typ T) :: ER) 
                             (FN ++ (x0, bind_typ T) :: FR) GR G) in H0; auto.
        simpl_env in *. assert False. fsetdec. tauto.

    simpl_env in *. apply env_split_nonlin; auto.
    simpl_env. eapply wf_typ_strengthening. apply H.

  Case "left".
    destruct EN; simpl in EQ1; inversion EQ1; subst.    
    destruct GN; simpl in EQ3; inversion EQ3; subst.
    simpl_env in *. assert False. fsetdec. tauto. 
    simpl_env in *. assert False. fsetdec. tauto. 
    destruct GN; simpl in EQ3; inversion EQ3; subst.
    simpl_env in *. assert False. fsetdec. tauto. 
    simpl_env. apply env_split_lin_left; auto. 
    simpl_env.
    eapply wf_typ_strengthening. simpl_env in H. apply H.  
    simpl_env in *. fsetdec. simpl_env in *. fsetdec.

  Case "right".
    destruct FN; simpl in EQ2; inversion EQ2; subst.
    simpl_env in *. assert False. fsetdec. tauto.
    destruct GN; simpl in EQ3; inversion EQ3; subst.
    simpl_env in *. assert False. fsetdec. tauto.
    simpl_env. apply env_split_lin_right; auto. 
    simpl_env.
    eapply wf_typ_strengthening. simpl_env in H. apply H.  
    simpl_env in *. fsetdec. simpl_env in *. fsetdec.
Qed.

(*
Lemma env_split_strengthening3: forall x0 T E1 E2 F G1 G2,
  wf_env (G2 ++ [(x0, bind_typ T)] ++ G1) ->
  wf_typ G1 T kn_lin ->
  ~ wf_typ G1 T kn_nonlin ->
  env_split (E2 ++ [(x0, bind_typ T)] ++ E1) 
            F 
            (G2 ++ [(x0, bind_typ T)] ++ G1) ->
  env_split (E2 ++ E1) F (G2 ++ G1).
Proof.
  intros x0 T E1 E2 F G1 G2 WFE WFT NWFT S.
  remember (E2 ++ [(x0, bind_typ T)] ++ E1) as E.
  remember (G2 ++ [(x0, bind_typ T)] ++ G1) as G.
  generalize dependent G2. generalize dependent E2.
  generalize dependent G1. generalize dependent E1.
  induction S; intros ER GR WFT NWFT EN EQ1 GN EQ3.
  Case "empty". 
    assert False. eapply empty_noteq_concat; eauto. tauto.
  Case "kn".
    destruct EN. simpl in EQ1. inversion EQ1.
    destruct GN. simpl in EQ3. inversion EQ3.
      simpl in *. inversion EQ1; inversion EQ3; subst.
    simpl_env. apply env_split_kn. 
    eapply IHS; eauto. 
    simpl_env. eapply wf_env_strengthening2. simpl_env in WFE. apply WFE.
  Case "nonlin".  
    destruct EN; simpl in EQ1; inversion EQ1; subst.
    destruct GN; simpl in EQ3; inversion EQ3; subst. tauto.
    assert (wf_typ GR T kn_nonlin). eapply wf_typ_inversion. simpl_env in H.
    eapply wf_env_strengthening2. simpl_env in WFE. apply WFE. apply H. tauto.
    destruct GN; simpl in EQ3; inversion EQ3; subst. tauto.
    simpl_env. apply env_split_nonlin. apply IHS; auto.
    eapply wf_env_strengthening2. simpl_env in WFE. apply WFE. 
    eapply wf_typ_strengthening. simpl_env in H. apply H.
  Case "left".
    destruct EN; simpl in EQ1; inversion EQ1; subst.
    destruct GN; simpl in EQ3; inversion EQ3; subst. 
    simpl_env. auto.
    assert False. apply (not_wf_env empty GN GR x0 T T). simpl_env. simpl_env in WFE. apply WFE.
    tauto.
    destruct GN; simpl in EQ3; inversion EQ3; subst. 
    assert (env_split ([(x0, bind_typ T)] ++ EN ++ [(x0, bind_typ T)] ++ ER)
                      E2
                      ([(x0, bind_typ T)] ++ GR)).
    apply env_split_lin_left. simpl_env in S. auto. auto. auto. auto.
    assert (wf_env ([(x0, bind_typ T)] ++ EN ++ [(x0, bind_typ T)] ++ ER)).    
    eapply wf_split_env1. apply WFE. apply H2. assert False.
    apply (not_wf_env empty EN ER x0 T T). simpl_env. auto. tauto.
    simpl_env. apply env_split_lin_left. apply IHS; auto.
    simpl_env. eapply wf_env_strengthening2. simpl_env in WFE. apply WFE. 
    eapply wf_typ_strengthening. simpl_env in H. apply H. auto.
    unfold not. intros. apply H1. simpl_env. eapply wf_typ_weakening. auto.
    eapply ok_from_wf_typ. simpl_env in H. apply H.
  Case "right".
    destruct GN; simpl in EQ3; inversion EQ3; subst.
    assert False. apply H0. rewrite dom_concat. rewrite dom_concat. simpl. fsetdec. tauto.
    simpl_env. apply env_split_lin_right; auto. apply IHS; auto.
    simpl_env. eapply wf_env_strengthening2. simpl_env in WFE. apply WFE.
    eapply wf_typ_strengthening. simpl_env in H. apply H. rewrite dom_concat.
    repeat rewrite dom_concat in H0. fsetdec.
    unfold not. intros. apply H1. simpl_env. eapply wf_typ_weakening. apply H2.
    simpl_env in H. eapply ok_from_wf_typ. apply H.
Qed.

Lemma env_split_strengthening4: forall x0 T E1 E2 F G1 G2,
  wf_env (G2 ++ [(x0, bind_typ T)] ++ G1) ->
  wf_typ G1 T kn_lin ->
  ~ wf_typ G1 T kn_nonlin ->
  env_split F 
            (E2 ++ [(x0, bind_typ T)] ++ E1) 
            (G2 ++ [(x0, bind_typ T)] ++ G1) ->
  env_split F (E2 ++ E1) (G2 ++ G1).
Proof.
  intros.
  apply split_env_commute. eapply env_split_strengthening3; eauto.
  apply split_env_commute. auto.
Qed.
*)  
  
Lemma env_split_below_kn2: forall E1 E2 E3 G K,
  env_below_kn G E1 K ->
  env_below_kn G E2 K ->
  env_split E1 E2 E3 G ->
  env_below_kn G E3 K.    
Proof.
  intros E1 E2 E3 G K B1 B2 S.
  induction S.
  Case "empty".
    apply env_below_empty. auto.

  Case "kn".
    inversion B1. inversion B2.
    subst. simpl_env in *. inversion H7. inversion H14. subst.
    apply env_below_bind_kn. apply IHS; auto. 
    apply wf_env_kn. eapply wf_env_split0. apply S. simpl_env. fsetdec.

  Case "typ".
    inversion B1. inversion B2.
    subst. simpl_env in *. inversion H8. inversion H16. subst.
    apply env_below_bind_typ. apply IHS; auto. 
    eapply wf_env_typ. eapply wf_env_split0; eauto.
    eapply wf_typ_split1. apply H9. apply S.
    simpl_env. fsetdec.
    destruct K. apply wf_typ_sub. auto. auto.

  Case "left".
    inversion B1.   
    subst. apply env_below_bind_typ. apply IHS; auto.
    eapply wf_env_typ.  eapply wf_env_split0. apply S. 
    apply H. simpl_env. fsetdec.
    eapply wf_typ_split1. apply H10. apply S.

  Case "right".
  inversion B2. subst.
    apply env_below_bind_typ. apply IHS; auto. 
    eapply wf_env_typ.  eapply wf_env_split0.  apply S. 
    apply H. simpl_env. fsetdec.
    eapply wf_typ_split2. apply H10. apply S.
Qed.

Lemma expr_from_typing: forall E u T,
  typing E u T ->
  expr u.
Proof.
  intros.
  lapply (typing_regular E u T). intro. tauto. auto.
Qed.

(*
Lemma exists_env_split1: forall E1 F1 G F2,
  wf_env G ->
  env_split E1 F1 G ->
  env_split G F2 G ->
  exists G2, env_split E1 F2 G2.
Proof.
  intros E1 F1 G F2 WFE S1 S2.
  generalize dependent F2.
  induction S1; intros F2 S2.
  Case "empty".
  inversion S2; subst. exists empty; auto.
  Case "bind_kn".
  inversion S2; subst. 
  assert (exists G2, env_split E1 E4 G2) as EX.
  apply IHS1; auto. eapply wf_env_strengthening2. apply WFE.
  destruct EX as [G2 S3].
  exists ([(X, bind_kn K)] ++ G2).
  apply env_split_kn. auto.
  Case "nonlin".
  inversion S2; subst.
  assert (exists G2, env_split E1 E4 G2) as EX.
  apply IHS1; auto. 
  eapply wf_env_strengthening2. apply WFE.
  destruct EX as [G2 S3].
  exists ([(x, bind_typ T)] ++ G2).
  apply env_split_nonlin. auto. eapply wf_typ_split1.
  apply (split_ok E1 E4 G2).  eapply ok_split1. eapply ok_from_wf_typ. apply H.
  apply S1. eapply ok_split2. eapply ok_from_wf_typ. apply H. apply H4. apply S3.
  eapply wf_split_typ1. apply H. apply S1. apply S3.
  assert False. apply H8. apply H. tauto.
  tauto.
  Case "left".
  inversion S2; subst.
  tauto. 
   assert (exists G2, env_split E1 F2 G2) as EX.
   apply IHS1; auto. eapply wf_env_strengthening2. apply WFE.
   destruct EX as [G2 S3].
   exists ([(x, bind_typ T)] ++ G2); auto. apply env_split_lin_left. auto.
   eapply wf_typ_split1. apply (split_ok E1 F2 G2). eapply ok_split1. 
   eapply ok_from_wf_typ. apply H. apply S1. eapply ok_split2.
   eapply ok_from_wf_typ. apply H.  apply H6. auto.
   eapply wf_split_typ1. apply H. apply S1. apply S3. auto.
   unfold not. intros WFT2. apply H1. eapply wf_typ_split1. 
   eapply ok_from_wf_typ. apply H. eapply wf_split_typ1. 
   apply WFT2. apply S3. apply S1. 
   rewrite dom_concat in H9. simpl in H9. fsetdec.
  Case "right". 
   inversion S2; subst.
   assert (exists G2, env_split E1 E4 G2) as EX.
   apply IHS1; auto. eapply wf_env_strengthening2. apply WFE.
   destruct EX as [G2 S3].
   exists ([(x, bind_typ T)] ++ G2); auto. apply env_split_lin_right. auto.
   eapply wf_typ_split1. apply (split_ok E1 E4 G2). eapply ok_split1. 
   eapply ok_from_wf_typ. apply H. apply S1. eapply ok_split2.
   eapply ok_from_wf_typ. apply H.  apply H6. auto.
   eapply wf_split_typ1. apply H. apply S1. apply S3. auto.
   unfold not. intros WFT2. apply H1. eapply wf_typ_split1. 
   eapply ok_from_wf_typ. apply H. eapply wf_split_typ1. 
   apply WFT2. apply S3. apply S1. apply IHS1. 
   eapply wf_env_strengthening2. apply WFE. auto.
   rewrite dom_concat in H9. simpl in H9. fsetdec.
Qed.
*)

Lemma notin_env_split1: forall E2 E1 F G2 G1 GG x U Y,
  env_split (E2 ++ [(x, bind_typ U)] ++ E1)
            F
            (G2 ++ [(x, bind_typ U)] ++ G1) GG ->
  Y `notin` dom G2 ->
  Y `notin` dom E2.
Proof.
  intros E2 E1 F G2 G1 GG x U Y S NIN.
  remember (E2 ++ [(x, bind_typ U)] ++ E1) as E.
  remember (G2 ++ [(x, bind_typ U)] ++ G1) as G.
  generalize dependent E2. generalize dependent G2.
  induction S; intros GL NIN EQ1 EL EQ2.
  Case "empty".
    assert False. eapply empty_noteq_concat. apply EQ1. tauto.
  Case "kn".
    destruct GL; simpl in EQ1; inversion EQ1. 
    destruct EL; simpl in EQ2; inversion EQ2; subst.
    simpl. assert (Y `notin` dom EL).
    eapply (IHS GL). simpl in *. fsetdec. auto. auto. simpl in *.
    fsetdec.
  Case "nonlin".
    destruct GL; simpl in EQ1; inversion EQ1; subst.
    destruct EL; simpl in EQ2; inversion EQ2; subst.
    fsetdec.
    simpl. 
    rewrite (dom_env_split (EL ++ (x, bind_typ U) :: E1) E2 G1 G) in H0; auto.
    assert False. simpl in H0. simpl_env in H0. fsetdec. tauto.
    destruct EL; simpl in EQ1; inversion EQ2; subst. fsetdec.
    simpl.  assert (Y `notin` dom EL).
    eapply (IHS GL); try fsetdec; auto. simpl_env in *. fsetdec.
    simpl_env in *. fsetdec.
  Case "left".
    destruct GL; simpl in EQ1; inversion EQ1; subst.
    destruct EL; simpl in EQ2; inversion EQ2; subst.
    fsetdec. 
    rewrite (dom_env_split (EL ++ (x, bind_typ U) :: E1) E2 G1 G) in H1; auto.
    assert False. simpl in H1. simpl_env in H1. fsetdec. tauto.
    destruct EL; simpl in EQ2; inversion EQ2; subst.
    fsetdec.
    simpl_env in *.
    assert (Y `notin` dom EL).
    eapply (IHS GL); try fsetdec; auto. fsetdec.
  Case "right".
    destruct GL; simpl in EQ1; inversion EQ1; subst.
    simpl_env in H0. assert False. fsetdec. tauto.
    eapply (IHS GL); try fsetdec; auto. 
    simpl_env in NIN. fsetdec.
Qed.
    
(*
Lemma ok_split_splice2: forall E2 E1 F G2 G1 E0 x U,
  wf_env (G2 ++ [(x, bind_typ U)] ++ G1) ->
  env_split (E2 ++ [(x, bind_typ U)] ++ E1)
            F
            (G2 ++ [(x, bind_typ U)] ++ G1) ->
  ok (G2 ++ E0) ->
  ok (E2 ++ E0).
Proof.
  intros E2 E1 F G2 G1 E0 x U WFE S.
  remember (E2 ++ [(x, bind_typ U)] ++ E1) as E.
  remember (G2 ++ [(x, bind_typ U)] ++ G1) as G.
  generalize dependent E2. generalize dependent G2.
  induction S; intros GL EQ1 EL EQ2 OK.
  Case "empty".
     assert False. eapply empty_noteq_concat. apply EQ1. tauto.
  Case "bind_kn".
    destruct GL; simpl in EQ1; inversion EQ1; subst.
    destruct EL; simpl in EQ2; inversion EQ2; subst.
    simpl_env. simpl. apply ok_cons.
    assert (wf_env (GL ++ (x, bind_typ U) :: G1)) as WFE2.
    eapply wf_env_strengthening2. apply WFE. 
    eapply (IHS WFE2 GL); auto. eapply ok_remove_head. simpl_env in OK. apply OK.
    simpl_env in OK. simpl in OK. inversion OK. subst.
    assert (X `notin` dom EL) as NIN2.
    apply (notin_env_split1 EL E1 E3 GL G1 x U X).
    eapply wf_env_strengthening2. apply WFE. 
    apply S. rewrite dom_concat in H3. fsetdec.
    rewrite dom_concat. rewrite dom_concat in H3. fsetdec.
  Case "nonlin".
    destruct GL; simpl in EQ1; inversion EQ1; subst.
    destruct EL; simpl in EQ2; inversion EQ2; subst.
    auto.
    simpl_env. simpl. apply ok_cons.
    assert (wf_env ([(x, bind_typ U)] ++ EL ++ (x, bind_typ U) :: E1)) as WFE2.
    eapply wf_split_env1. apply WFE.
    eapply env_split_weakening1. apply S.
    rewrite_env ([(x, bind_typ U)] ++ empty).
    apply env_below_bind_typ. apply env_below_empty. 
    eapply wf_env_strengthening2. apply WFE.  simpl_env. auto. simpl_env. auto.
    assert False. 
    apply (not_wf_env empty EL E1 x U U). simpl_env. simpl_env in WFE2. auto. tauto.
    assert (wf_env ([(x, bind_typ U)] ++ EL ++ (x, bind_typ U) :: E1)) as WFE2.
    eapply wf_split_env1. apply WFE.
    eapply env_split_weakening1. apply S.
    rewrite_env ([(x, bind_typ U)] ++ empty).
    apply env_below_bind_typ. apply env_below_empty. 
    eapply wf_env_strengthening2. apply WFE.  simpl_env. auto. simpl_env. auto.
    assert False. 
    apply (not_wf_env empty EL E1 x U U). simpl_env. simpl_env in WFE2. auto. tauto.
    assert (wf_env (GL ++ (x, bind_typ U) :: G1)) as WFE2.
    eapply wf_env_strengthening2. apply WFE.
    destruct EL; simpl in EQ2; inversion EQ2; subst.     
    simpl_env. eapply ok_remove_head. apply OK.
    simpl_env. simpl. apply ok_cons.
    eapply (IHS WFE2 GL); auto. eapply ok_remove_head. simpl_env in OK. apply OK.
    assert (x0 `notin` dom EL) as NIN2.
    apply (notin_env_split1 EL E1 E3 GL G1 x U x0). auto.
    apply S. simpl_env in OK. simpl in OK. inversion OK; subst.
    rewrite dom_concat in H4. fsetdec.
    simpl_env in OK. simpl in OK. inversion OK; subst.
    rewrite dom_concat in H4. rewrite dom_concat. fsetdec.
  Case "left".
    destruct GL; simpl in EQ1; inversion EQ1; subst.
    destruct EL; simpl in EQ2; inversion EQ2; subst. auto.
    assert (wf_env ([(x, bind_typ U)] ++ EL ++ (x, bind_typ U) :: E1)) as WFE2.
    eapply wf_split_env1. apply WFE. eapply env_split_lin_left; eauto.
    assert False.
    apply (not_wf_env empty EL E1 x U U). simpl_env. simpl_env in WFE2. auto. tauto.
    destruct EL; simpl in EQ2; inversion EQ2; subst.
    simpl_env. eapply ok_remove_head. apply OK.
    simpl_env. simpl. apply ok_cons.
    assert (wf_env (GL ++ (x, bind_typ U) :: G1)) as WFE2.
    eapply wf_env_strengthening2. apply WFE.
    eapply (IHS WFE2 GL); auto. eapply ok_remove_head. simpl_env in OK. apply OK.
    assert (x0 `notin` dom EL) as NIN2.
    apply (notin_env_split1 EL E1 E3 GL G1 x U x0). auto.
    eapply wf_env_strengthening2. apply WFE.
    apply S. simpl_env in OK. simpl in OK. inversion OK; subst.
    rewrite dom_concat in H6. fsetdec.
    simpl_env in OK. simpl in OK. inversion OK; subst.
    simpl_env in OK. simpl in OK. inversion OK; subst.
    rewrite dom_concat in H6. rewrite dom_concat. fsetdec.
  Case "right".
    destruct GL; simpl in EQ1; inversion EQ1; subst.
    assert False. rewrite dom_concat in H0. rewrite dom_concat in H0. simpl in H0.
    fsetdec. tauto.
    assert (wf_env (GL ++ (x, bind_typ U) :: G1)).
    eapply wf_env_strengthening2. apply WFE.
    rewrite dom_concat in H0. rewrite dom_concat in H0. simpl in H0.
    eapply (IHS H2 GL); try fsetdec; auto. 
    eapply ok_remove_head. simpl_env in OK. apply OK.
Qed.
*)

Lemma fv_in_open_ee:  forall x e1 e2 k,
   x `in` fv_ee e1 -> 
   x `in` fv_ee (open_ee_rec k e2 e1).
Proof.
  intros x. induction e1; intros e2 k1 IN; simpl in IN; simpl; try fsetdec.
  apply IHe1. auto.
  assert ((x `in` fv_ee e1_1) \/ (x `in` fv_ee e1_2)).
  fsetdec. destruct H.
  assert (x `in` fv_ee (open_ee_rec k1 e2 e1_1)).
  apply IHe1_1; auto. fsetdec.
  assert (x `in` fv_ee (open_ee_rec k1 e2 e1_2)).
  apply IHe1_2; auto. fsetdec.
  apply IHe1; auto.
  apply IHe1; auto.
Qed.

Lemma fv_in_open_te:  forall x e1 e2 k,
   x `in` fv_ee e1 -> 
   x `in` fv_ee (open_te_rec k e2 e1).
Proof.
  intros x. induction e1; intros e2 k1 IN; simpl in IN; simpl; try fsetdec.
  apply IHe1. auto.
  assert ((x `in` fv_ee e1_1) \/ (x `in` fv_ee e1_2)).
  fsetdec. destruct H.
  assert (x `in` fv_ee (open_te_rec k1 e2 e1_1)).
  apply IHe1_1; auto. fsetdec.
  assert (x `in` fv_ee (open_te_rec k1 e2 e1_2)).
  apply IHe1_2; auto. fsetdec.
  apply IHe1; auto.
  apply IHe1; auto.
Qed.

Lemma typing_fv: forall E e T x,
  typing E e T ->
  x `notin` dom E ->
  x `notin` fv_ee e.
Proof.
  intros E e T x H.
  induction H; intros NI.
  Case "var".
  rewrite dom_concat in NI. rewrite dom_concat in NI. simpl in NI. simpl.
  fsetdec.
  Case "abs".
  simpl. pick fresh y. lapply (H2 y); intros; auto.
  simpl in H3. unfold not.  intros. apply H3. fsetdec. 
  unfold open_ee. apply fv_in_open_ee; auto.
  Case "app".
  simpl. assert (x `notin` fv_ee e1). apply IHtyping1; auto.
  rewrite (dom_env_split E1 E2 E3 empty) in NI. fsetdec. auto.
  simpl. assert (x `notin` fv_ee e2). apply IHtyping2; auto.
  rewrite (dom_env_split E1 E2 E3 empty) in NI. fsetdec. auto.
  fsetdec.
  Case "tabs".
  simpl. pick fresh y. lapply (H1 y); intros; auto.
  unfold not. intros. apply H2. simpl. fsetdec.
  unfold open_te. apply fv_in_open_te. auto.
  Case "tapp".
  simpl. apply IHtyping; auto.
Qed.

Lemma non_subst: forall E e T x u,
  typing E e T ->
  x `notin` dom E ->
  e = subst_ee x u e.
Proof.
  intros.
  apply subst_ee_fresh.
  eapply typing_fv. apply H. apply H0.
Qed.

(*
Lemma typing_weakening2: forall G E1 E2 GG F e T,
  wf_env (E1 ++ G ++ GG) ->
  typing (E1 ++ E2 ++ GG) e T ->
  env_split E2 F G GG ->
  env_below_kn GG F kn_nonlin ->
  typing (E1 ++ G ++ GG) e T.
Proof.
  intros G E1 E2 GG F e T WFE Typ S B.
  assert (E2 = G).
  eapply env_split_below_eq1. eapply split_env_commute. apply S. auto.
  subst. auto.
Qed.
*)

Lemma env_split_cases: forall E F G2 G1 x T GG,
  env_split E F (G2 ++ [(x, bind_typ T)] ++ G1) GG ->
  (exists E1, exists F1, exists E2, exists F2,
    E = E2 ++ [(x, bind_typ T)] ++ E1 /\
    F = F2 ++ [(x, bind_typ T)] ++ F1 /\
    env_split E1 F1 G1 GG /\
    env_split E2 F2 G2 (G1 ++ GG) /\
    wf_typ (G1 ++ GG) T kn_nonlin)
   \/
  (exists E1, exists F1, exists E2, exists F2,
    E = E2 ++ [(x, bind_typ T)] ++ E1 /\
    F = F2 ++ F1 /\
    env_split E1 F1 G1 GG /\
    env_split E2 F2 G2 (G1 ++ GG) /\ 
    x `notin` dom F)
   \/
  (exists E1, exists F1, exists E2, exists F2,
    E = E2 ++ E1 /\
    F = F2 ++ [(x, bind_typ T)] ++ F1 /\
    env_split E1 F1 G1 GG /\
    env_split E2 F2 G2 (G1 ++ GG) /\ 
    x `notin` dom E).
Proof.
  intros E F G2 G1 x T GG S.
  remember (G2 ++ [(x, bind_typ T)] ++ G1) as G.
  generalize dependent G2. generalize dependent G1.
  induction S; intros G1 G2 EQ; simpl_env in *; auto.
  Case "empty".
     assert False. eapply empty_noteq_concat. apply EQ. tauto.
  Case "kn".
    destruct G2; inversion EQ; subst; simpl_env in *.
    destruct (IHS G1 G2); auto.
    destruct H1 as [ER [FR [EL [FL [Q1 [Q2 [S1 [S2 WFT]]]]]]]].
    left. 
    exists ER. exists FR. exists ([(X, bind_kn K)] ++ EL).
    exists ([(X, bind_kn K)] ++ FL).
    repeat split; simpl_env in *; subst; auto.
    destruct H1.
    destruct H1 as [ER [FR [EL [FL [Q1 [Q2 [S1 [S2 NIN]]]]]]]].
    right. left.
    exists ER. exists FR. exists ([(X, bind_kn K)] ++ EL).
    exists ([(X, bind_kn K)] ++ FL).
    repeat split; simpl_env in *; subst; auto.
    destruct H1 as [ER [FR [EL [FL [Q1 [Q2 [S1 [S2 NIN]]]]]]]].
    right. right.
    exists ER. exists FR. exists ([(X, bind_kn K)] ++ EL).
    exists ([(X, bind_kn K)] ++ FL).
    repeat split; simpl_env in *; subst; auto.

  Case "nonlin".
    destruct G2; inversion EQ; subst; simpl_env in *.
    left.
    exists E1. exists E2. exists empty. exists empty.
    repeat split; simpl_env in *; subst ;auto. 
    apply env_split_empty. eapply wf_env_split0. apply S.
    destruct (IHS G1 G2) as [X1 | [X2 | X3]]; auto.
    destruct X1 as [ER [FR [EL [FL [Q1 [Q2 [S1 [S2 WFT]]]]]]]].
    left. 
    exists ER. exists FR. exists ([(x0, bind_typ T0)] ++ EL).
    exists ([(x0, bind_typ T0)] ++ FL).
    repeat split; simpl_env in *; subst; auto.
    apply env_split_nonlin. auto. eapply wf_typ_strengthening. apply H.
    fsetdec. simpl_env. fsetdec.

    destruct X2 as [ER [FR [EL [FL [Q1 [Q2 [S1 [S2 NIN]]]]]]]].
    right. left.
    exists ER. exists FR. exists ([(x0, bind_typ T0)] ++ EL).
    exists ([(x0, bind_typ T0)] ++ FL).
    repeat split; simpl_env in *; subst; auto.
    apply env_split_nonlin. auto. eapply wf_typ_strengthening. apply H.
    fsetdec. simpl_env. fsetdec.

    destruct X3 as [ER [FR [EL [FL [Q1 [Q2 [S1 [S2 NIN]]]]]]]].
    right. right.
    exists ER. exists FR. exists ([(x0, bind_typ T0)] ++ EL).
    exists ([(x0, bind_typ T0)] ++ FL).
    repeat split; simpl_env in *; subst; auto.
    apply env_split_nonlin. auto. eapply wf_typ_strengthening. apply H.
    fsetdec. simpl_env. fsetdec.

  Case "left".
    destruct G2; inversion EQ; subst; simpl_env in *.
    right. left.
    exists E1. exists E2. exists empty. exists empty.
    repeat split; simpl_env in *; subst ;auto. 
    apply env_split_empty. eapply wf_env_split0. apply S.
    
    destruct (IHS G1 G2) as [X1 | [X2 | X3]]; auto.
    destruct X1 as [ER [FR [EL [FL [Q1 [Q2 [S1 [S2 WFT]]]]]]]].
    left.
    exists ER. exists FR. exists ([(x0, bind_typ T0)] ++ EL).
    exists FL.
    repeat split; simpl_env in *; subst ;auto. 
    apply env_split_lin_left. auto. 
    eapply wf_typ_strengthening. apply H.
    simpl_env in *. fsetdec. 
    simpl_env in *. fsetdec.
    simpl_env in *. fsetdec.
    
    destruct X2 as [ER [FR [EL [FL [Q1 [Q2 [S1 [S2 NIN]]]]]]]].
    right. left.
    exists ER. exists FR. exists ([(x0, bind_typ T0)] ++ EL).
    exists FL.
    repeat split; simpl_env in *; subst; auto.
    apply env_split_lin_left; try (simpl_env in *; fsetdec); auto.
    eapply wf_typ_strengthening. apply H.

    destruct X3 as [ER [FR [EL [FL [Q1 [Q2 [S1 [S2 NIN]]]]]]]].
    right. right.
    exists ER. exists FR. exists ([(x0, bind_typ T0)] ++ EL).
    exists FL.
    repeat split; simpl_env in *; subst; auto.
    apply env_split_lin_left; try (simpl_env in *; fsetdec); auto.
    eapply wf_typ_strengthening. apply H.

  Case "right".
    destruct G2; inversion EQ; subst; simpl_env in *.
    right. right.
    exists E1. exists E2. exists empty. exists empty.
    repeat split; simpl_env in *; subst; auto.
    apply env_split_empty. eapply wf_env_split0. apply S.

    destruct (IHS G1 G2) as [X1 | [X2 | X3]]; auto.
    destruct X1 as [ER [FR [EL [FL [Q1 [Q2 [S1 [S2 WFT]]]]]]]].
    left.
    exists ER. exists FR. exists EL.
    exists ([(x0, bind_typ T0)] ++ FL).
    repeat split; simpl_env in *; subst ;auto. 
    apply env_split_lin_right; try (simpl_env in *; fsetdec); auto.
    eapply wf_typ_strengthening. apply H.

    destruct X2 as [ER [FR [EL [FL [Q1 [Q2 [S1 [S2 NIN]]]]]]]].
    right. left.
    exists ER. exists FR. exists EL.
    exists ([(x0, bind_typ T0)] ++ FL).
    repeat split; simpl_env in *; subst; auto.
    apply env_split_lin_right; try (simpl_env in *; fsetdec); auto.
    eapply wf_typ_strengthening. apply H.

  destruct X3 as [ER [FR [EL [FL [Q1 [Q2 [S1 [S2 NIN]]]]]]]].
    right. right.
    exists ER. exists FR. exists EL.
    exists ([(x0, bind_typ T0)] ++ FL).
    repeat split; simpl_env in *; subst; auto.
    apply env_split_lin_right; try (simpl_env in *; fsetdec); auto.
    eapply wf_typ_strengthening. apply H.
Qed.

Lemma typing_split_splice: forall H E F G GG e T,
  env_split E F G GG ->
  typing (H ++ E ++ GG) e T ->
  env_below_kn GG F kn_nonlin ->
  ok (H ++ G ++ GG) ->
  typing (H ++ G ++ GG) e T.
Proof.
  intros H E F G GG e T S.
  generalize dependent H. generalize dependent e. generalize dependent T.
  induction S; intros U0 e0 E0 Typ B OK.
  Case "empty".
    auto.
  Case "kn".
    rewrite_env ((E0 ++ [(X, bind_kn K)]) ++ E3 ++ G).
    eapply IHS; simpl_env in *; auto.
    eapply env_below_kn_strengthening1. apply B.
  Case "nonlin".
    rewrite_env ((E0 ++ [(x, bind_typ T)]) ++ E3 ++ G).
    eapply IHS; simpl_env in *; auto.
    inversion B. auto.
  Case "left".
    rewrite_env ((E0 ++ [(x, bind_typ T)]) ++ E3 ++ G).
    eapply IHS; simpl_env in *; auto. auto.
  Case "right".
    rewrite_env ((E0 ++ [(x, bind_typ T)]) ++ E3 ++ G).
    eapply IHS; simpl_env in *; auto.
    eapply typing_weakening. auto.
    eapply split_below1. apply S.
    eapply env_split_below_kn1. eapply env_split_commute. apply S.
    apply env_below_kn_assoc1. auto.
    eapply ok_remove_head. apply OK.
    apply wf_env_weakening2. 
    eapply wf_env_from_typing. apply Typ.
    eapply wf_env_typ. eapply wf_env_split1. apply S.
    eapply wf_split_typ1. apply H. apply S. simpl_env. fsetdec.
    apply ok_join.
    simpl. apply ok_cons. eapply ok_from_wf_env. eapply wf_env_split1. apply S.
    simpl_env. fsetdec. apply ok_from_wf_env. eapply wf_env_from_typing. apply Typ.
    apply ok_commute. simpl. apply ok_cons. eapply ok_remove_tail. apply OK.
    eapply fresh_mid_head_In. apply OK. simpl. fsetdec.
    inversion B. auto.
Qed.
    
Lemma exists_env_split1: forall G1 E0 F ER FR GG,
  env_split G1 E0 F GG ->
  env_split ER FR G1 empty ->
  exists F0, env_split ER E0 F0 GG.
Proof.
  intros G1 E0 F ER FR GG S1.
  intros S2. 
  generalize dependent ER. generalize dependent FR.
  induction S1; intros FR ER S2; simpl_env in *.
  Case "empty".
    inversion S2. subst.
    exists empty. apply env_split_empty. auto.
  Case "kn".
    inversion S2; subst.
    lapply (IHS1 E4 E0).
    intros EX. destruct EX as [F0 S3].
    exists ([(X, bind_kn K)] ++ F0).
    apply env_split_kn. auto. rewrite (dom_env_split E0 E2 F0 G).
    rewrite (dom_env_split E0 E4 E1 empty) in H8.
    rewrite (dom_env_split E1 E2 E3 G) in H; auto. auto. auto.
    auto. auto.
  Case "nonlin".
    inversion S2; simpl_env in *.
    subst.  
    lapply (IHS1 E4 E0); auto.
    intros EX. destruct EX as [F0 S3].
    exists ([(x, bind_typ T)] ++ F0).
    apply env_split_nonlin. auto.


(* BEFORE *)
Lemma typing_through_subst_ee : forall U0 E0 x G1 G2 F0 T e u,
  typing (G2 ++ [(x, bind_typ U0)] ++ G1) e T ->
  typing E0 u U0 ->
  value u ->
  env_split G1 E0 F0 empty->
  ok (G2 ++ E0) ->
  typing (G2 ++ F0) (subst_ee x u e) T.
Proof with simpl_env.
  intros U0 E0 x G1 G2 F0 T e u TypT TypU V S OK.

  (* set up IH *)
  remember (G2 ++ [(x, bind_typ U0)] ++ G1) as G.

  generalize dependent G2. generalize dependent G1. generalize dependent F0.
  generalize dependent E0.
  induction TypT; intros E0 TypU F G1 S G2 OK EQ; subst; simpl subst_ee...

Focus 3.
(*
  Case "typing_var".
    destruct (x0 == x).

    SCase "x0 = x".
    subst x.
      assert (E2 = G2 /\ E1 = G1 /\ (bind_typ T) = (bind_typ U)). 
      eapply eq_list_mid2.        
        eapply ok_from_wf_env. eapply H0. auto.
        destruct H2 as [Q1 [Q2 Q3]]. inversion Q3. subst.
        assert (E = F). eapply env_split_below_eq1. apply S.
        eapply env_below_kn_strengthening1. apply H1.
        rewrite_env (empty ++ G2 ++ F).
        apply typing_weakening... subst E. auto.
        subst E. eapply env_split_below_kn. apply S. auto. 
        eapply wf_env_split_splice1. auto. auto. apply S.
        eapply wf_env_strengthening. apply H0. subst. 
        eapply wf_env_split_splice1. auto. auto. apply S. 
        eapply wf_env_strengthening. apply H0.

    (** In the case where x0<>x, the result follows by an exhaustive
        case analysis on exactly where x0 is bound in the environment.
        We perform this case analysis by using the binds_cases tactic,
        described in the Environment library. *)

    SCase "x0 <> x".
      lapply (env_cases E2 E1 G2 G1 (x0, bind_typ T) (x, bind_typ U)).
      intros.  assert (ok (E2 ++ [(x0, bind_typ T)] ++ E1)). auto.
      assert (ok (G2 ++ [(x, bind_typ U)] ++ G1)).
      rewrite <- EQ. auto. destruct H2; auto.
      destruct H2 as [M [Q1 Q2]].
      subst G2. simpl_env. apply typing_var. 
      rewrite_env ((E2 ++ [(x0, bind_typ T)] ++ M) ++ F).
      eapply (wf_env_strengthening x U).
      rewrite_env ((E2 ++ [(x0, bind_typ T)] ++ M ++ [(x, bind_typ U)]) ++ F).
      eapply wf_env_split_splice1. 
      eapply wf_env_split. assert (wf_env G1).  eapply wf_env_strengthening2.
      subst E1.
      rewrite_env ((E2 ++ [(x0, bind_typ T)] ++ M ++ [(x, bind_typ U)]) ++ G1) in H0.
      apply H0. apply H2. eapply wf_env_from_typing. apply TypU. apply S.
      apply XXX_FIX_OK. 
           (* x is bound to a nonlinear type and it's not in G1, so it's also not in F *)
      apply S. simpl_env. subst E1. apply H0.
      rewrite_env ((E2 ++ M) ++ F). 
      eapply (env_below_kn_strengthening empty (E2 ++ M) x U).
      simpl_env.  subst. assert (wf_typ (G1 ++ empty) U kn_nonlin). 
      eapply env_below_kn_inversion. 
      rewrite_env ((E2 ++ M) ++ [(x, bind_typ U)] ++ G1) in H1.
      apply H1.  simpl_env in H2. assert (wf_typ F U kn_nonlin).
      eapply wf_typ_split1. eapply ok_remove_head. apply OK2. apply H2. apply S.
      assert (E = F). eapply env_split_below_eq1. apply S. 
      eapply env_below_kn_strengthening1.
      rewrite_env ((E2 ++ M ++ [(x, bind_typ U)]) ++ G1) in H1.
      apply H1. subst E.
      assert (env_below_kn empty F kn_nonlin).
      eapply value_env_below_kn. apply TypU. apply H5. auto.
      rewrite_env ((E2 ++ M ++ [(x, bind_typ U)]) ++ F).
      eapply env_below_kn_assoc2. simpl_env. 
      eapply env_split_below_kn. apply S. simpl_env. apply H1. 
      eapply wf_env_split_splice1. auto. 
      apply XXX_FIX_OK. apply S. 
      simpl_env. eapply wf_env_strengthening. apply H0. auto.

      (* Now for the case where the variable is on the right *)
      destruct H2 as [M [Q1 Q2]]. subst. 
      assert (exists K, wf_typ E1 T K).
      eapply wf_env_inversion. 
      rewrite_env ((G2 ++ [(x, bind_typ U)] ++ M) ++ [(x0, bind_typ T)] ++ E1) in H0. 
      apply H0.
      destruct H2 as [K WFT].
      destruct K.    
(* Case K = kn_lin *)
      destruct (wf_typ_dec E1 T kn_nonlin).
      eapply ok_from_wf_typ. apply WFT. eapply type_from_wf_typ. eapply WFT.
(* Case wf_typ E1 T kn_nonlin *)
      lapply (split_destruct3 M E1 x0 T E F); auto.
      intros. destruct H5 as [F1 [F2 [EL [ER [Q1 [Q2 S1]]]]]]; auto.
      subst. rewrite_env ((G2 ++ F1) ++ [(x0, bind_typ T)] ++ F2).
      apply typing_var. 
      (* Prove the enviroment well formed *)
      rewrite_env (G2 ++ F1 ++ [(x0, bind_typ T)] ++ F2).
      eapply wf_env_split_splice1. eapply wf_env_split.
      assert (wf_env (M ++ [(x0, bind_typ T)] ++ E1)).
      eapply wf_env_strengthening2. 
      rewrite_env ((G2 ++ [(x, bind_typ U)]) ++ M ++ [(x0, bind_typ T)] ++ E1) in H0.
      apply H0. apply H5.
      eapply wf_env_from_typing. apply TypU. auto. auto. apply S.
      eapply wf_env_strengthening. simpl_env in H0. apply H0.
      (* Prove the env_below_kn thing *)
      apply (env_below_kn_strengthening empty (G2 ++ F1) x0 T F2 kn_nonlin).
      simpl_env.
      eapply (split_env_below_kn_weakening1 G2 (M ++ [(x0, bind_typ T)] ++ E1)).
      rewrite_env ((G2 ++ M) ++ [(x0, bind_typ T)] ++ E1).
      apply env_below_kn_weakening3. 
      simpl_env. 
      eapply env_below_kn_strengthening. simpl_env in H1. apply H1.
      apply env_below_bind_typ. 
      eapply env_below_kn_strengthening1. apply H1. simpl_env.
      eapply wf_env_strengthening2. apply H0.
      simpl_env. apply H2.
      simpl_env. eapply ok_remove_mid. apply H4.

      (* prove env_below_kn empty (F1 ++ [(x0, bind_typ T)] ++ F2) kn_nonlin *)
      assert ((EL ++ [(x0, bind_typ T)] ++ ER) = (F1 ++ [(x0, bind_typ T)] ++ F2)).
      eapply env_split_below_eq1. apply S.
      eapply env_below_kn_weakening3.  eapply env_below_kn_strengthening1. 
      simpl_env in H1. rewrite_env ((G2 ++ [(x, bind_typ U)]) ++ M ++ E1) in H1.
      apply H1. apply env_below_bind_typ. 
      eapply env_below_kn_strengthening1. 
      rewrite_env ((G2 ++ [(x, bind_typ U)] ++ M) ++ E1) in H1. apply H1. simpl_env.
      eapply wf_env_strengthening2. apply H0. simpl_env. auto.
      eapply ok_remove_head. 
      rewrite_env ((G2 ++ [(x, bind_typ U)]) ++ M ++ [(x0, bind_typ T)] ++ E1) in H4.
      apply H4.
  
      rewrite H5 in TypU.
      eapply value_env_below_kn. apply TypU.
      eapply (wf_typ_split1 (M ++ [(x0, bind_typ T)] ++ E1)). 
      eapply ok_from_wf_env. eapply wf_env_from_typing. apply TypU.
      apply wf_typ_weakening.
      eapply env_below_kn_inversion.
      lapply (env_below_kn_assoc1 empty E1 (G2 ++ [(x, bind_typ U)] ++ M) kn_nonlin).
      intros. simpl_env in H6. apply H6. apply H1.
      eapply ok_remove_head. 
      rewrite_env ((G2 ++ [(x, bind_typ U)]) ++ M ++ [(x0, bind_typ T)] ++ E1) in H4.
      apply H4. apply S. auto. apply S.

      (* Prove the enviroment well formed again *)
      rewrite_env (G2 ++ F1 ++ [(x0, bind_typ T)] ++ F2).
      eapply wf_env_split_splice1. eapply wf_env_split.
      assert (wf_env (M ++ [(x0, bind_typ T)] ++ E1)).
      eapply wf_env_strengthening2. 
      rewrite_env ((G2 ++ [(x, bind_typ U)]) ++ M ++ [(x0, bind_typ T)] ++ E1) in H0.
      apply H0. apply H5.
      eapply wf_env_from_typing. apply TypU. auto. auto. apply S.
      eapply wf_env_strengthening. simpl_env in H0. apply H0.

(* Case ~ wf_typ_E1 T kn_nonlin *)
      lapply (split_destruct4 M E1 x0 T E F); auto.
      intros. destruct H5 as [F1 [F2 [EL [ER [Q1 [Q2 S1]]]]]]; auto.
      subst. rewrite_env ((G2 ++ F1) ++ [(x0, bind_typ T)] ++ F2).
      apply typing_var. 
      (* Prove the enviroment well formed *)
      rewrite_env (G2 ++ F1 ++ [(x0, bind_typ T)] ++ F2).
      eapply wf_env_split_splice1. eapply wf_env_split.
      assert (wf_env (M ++ [(x0, bind_typ T)] ++ E1)).
      eapply wf_env_strengthening2. 
      rewrite_env ((G2 ++ [(x, bind_typ U)]) ++ M ++ [(x0, bind_typ T)] ++ E1) in H0.
      apply H0. apply H5.
      eapply wf_env_from_typing. apply TypU. apply S. auto. apply S.
      eapply wf_env_strengthening. simpl_env in H0. apply H0.
      (* Prove the env_below_kn thing *)
      rewrite_env (G2 ++ (F1 ++ F2)).
(** Need different proof here *)
      assert (env_split (M ++ E1) (EL ++ ER) (F1 ++ F2)).
      eapply env_split_strengthening1. apply WFT. apply H2.
      apply (wf_env_split (M ++ [(x0, bind_typ T)] ++ E1) (EL ++ ER)).
      eapply wf_env_strengthening2. 
      rewrite_env ((G2 ++ [(x, bind_typ U)]) ++ M ++ [(x0, bind_typ T)] ++ E1) in H0.
      apply H0.
      eapply wf_env_from_typing. apply TypU. 
      apply S. apply S.
      assert (env_below_kn empty (F1 ++ F2) kn_nonlin).
      assert (env_below_kn empty (M ++ E1) kn_nonlin).
      eapply env_below_kn_strengthening1.  
      rewrite_env ((G2 ++ [(x, bind_typ U)]) ++ M ++ E1) in H1.
      apply H1.
      assert (env_below_kn empty (EL ++ ER) kn_nonlin).
      eapply value_env_below_kn; eauto.
      assert (wf_typ ((M ++ E1) ++ empty) U kn_nonlin).
      eapply env_below_kn_inversion.  simpl_env in H1. apply H1.
      simpl_env in H7.
      assert (wf_typ (F1 ++ F2) U kn_nonlin).
      eapply wf_typ_split1. eapply split_ok. eapply ok_from_wf_typ. apply H7. 
      eapply ok_from_wf_env. eapply wf_env_from_typing. apply TypU. apply H5.
      apply H7. apply H5.
      eapply wf_split_typ2. apply H8. apply H5.
      eapply env_split_below_kn2. apply H6. apply H7. apply H5.
      apply (split_env_below_kn_weakening1 G2 (M ++ E1) (EL ++ ER) (F1 ++ F2)).
      eapply env_below_kn_strengthening. simpl_env in H1. apply H1.
      apply H6. apply H5. 
      (* environment again *)
      assert (wf_env (G2 ++ F1 ++ [(x0, bind_typ T)] ++ F2)).
      eapply wf_env_split_splice1. eapply wf_env_split.
      assert (wf_env (M ++ [(x0, bind_typ T)] ++ E1)).
      eapply wf_env_strengthening2. 
      rewrite_env ((G2 ++ [(x, bind_typ U)]) ++ M ++ [(x0, bind_typ T)] ++ E1) in H0.
      apply H0. apply H7.
      eapply wf_env_from_typing. apply TypU. apply S. auto. apply S.
      eapply wf_env_strengthening. simpl_env in H0. apply H0.
      rewrite_env ((G2 ++ F1) ++ F2).
      eapply wf_env_strengthening. simpl_env. apply H7.
      
(* Case wf_typ_E1 T kn_nonlin *)
      lapply (split_destruct3 M E1 x0 T E F); auto.
      intros. destruct H2 as [F1 [F2 [EL [ER [Q1 [Q2 S1]]]]]]; auto.
      subst. rewrite_env ((G2 ++ F1) ++ [(x0, bind_typ T)] ++ F2).
      apply typing_var. 

      (* Prove the enviroment well formed *)
      rewrite_env (G2 ++ F1 ++ [(x0, bind_typ T)] ++ F2).
      eapply wf_env_split_splice1. eapply wf_env_split.
      assert (wf_env (M ++ [(x0, bind_typ T)] ++ E1)).
      eapply wf_env_strengthening2. 
      rewrite_env ((G2 ++ [(x, bind_typ U)]) ++ M ++ [(x0, bind_typ T)] ++ E1) in H0.
      apply H0. apply H2.
      eapply wf_env_from_typing. apply TypU. auto. auto. apply S.
      eapply wf_env_strengthening. simpl_env in H0. apply H0.
      (* Prove the env_below_kn thing *)
      apply (env_below_kn_strengthening empty (G2 ++ F1) x0 T F2 kn_nonlin).
      simpl_env.
      eapply (split_env_below_kn_weakening1 G2 (M ++ [(x0, bind_typ T)] ++ E1)).
      rewrite_env ((G2 ++ M) ++ [(x0, bind_typ T)] ++ E1).
      apply env_below_kn_weakening3. 
      simpl_env. 
      eapply env_below_kn_strengthening. simpl_env in H1. apply H1.
      apply env_below_bind_typ. 
      eapply env_below_kn_strengthening1. apply H1. simpl_env.
      eapply wf_env_strengthening2. apply H0.
      simpl_env. apply WFT.
      simpl_env. eapply ok_remove_mid. apply H4.

      (* prove env_below_kn empty (F1 ++ [(x0, bind_typ T)] ++ F2) kn_nonlin *)
      assert ((EL ++ [(x0, bind_typ T)] ++ ER) = (F1 ++ [(x0, bind_typ T)] ++ F2)).
      eapply env_split_below_eq1. apply S.
      eapply env_below_kn_weakening3.  eapply env_below_kn_strengthening1. 
      simpl_env in H1. rewrite_env ((G2 ++ [(x, bind_typ U)]) ++ M ++ E1) in H1.
      apply H1. apply env_below_bind_typ. 
      eapply env_below_kn_strengthening1. 
      rewrite_env ((G2 ++ [(x, bind_typ U)] ++ M) ++ E1) in H1. apply H1. simpl_env.
      eapply wf_env_strengthening2. apply H0. simpl_env. auto.
      eapply ok_remove_head. 
      rewrite_env ((G2 ++ [(x, bind_typ U)]) ++ M ++ [(x0, bind_typ T)] ++ E1) in H4.
      apply H4.
  
      rewrite H2 in TypU.
      eapply value_env_below_kn. apply TypU.
      eapply (wf_typ_split1 (M ++ [(x0, bind_typ T)] ++ E1)). 
      eapply ok_from_wf_env. eapply wf_env_from_typing. apply TypU.
      apply wf_typ_weakening.
      eapply env_below_kn_inversion.
      lapply (env_below_kn_assoc1 empty E1 (G2 ++ [(x, bind_typ U)] ++ M) kn_nonlin).
      intros. simpl_env in H5. apply H5. apply H1.
      eapply ok_remove_head. 
      rewrite_env ((G2 ++ [(x, bind_typ U)]) ++ M ++ [(x0, bind_typ T)] ++ E1) in H4.
      apply H4. apply S. auto. apply S.

      (* Prove the enviroment well formed again *)
      rewrite_env (G2 ++ F1 ++ [(x0, bind_typ T)] ++ F2).
      eapply wf_env_split_splice1. eapply wf_env_split.
      assert (wf_env (M ++ [(x0, bind_typ T)] ++ E1)).
      eapply wf_env_strengthening2. 
      rewrite_env ((G2 ++ [(x, bind_typ U)]) ++ M ++ [(x0, bind_typ T)] ++ E1) in H0.
      apply H0. apply H2.
      eapply wf_env_from_typing. apply TypU. auto. auto. apply S.
      eapply wf_env_strengthening. simpl_env in H0. apply H0.
      
      unfold not. intros. apply n. inversion H2. auto.

  (** Informally, the typing_abs case is a straightforward application
      of the induction hypothesis, which is called H0 here. *)

  Case "typing_abs".

    (** We use the "pick fresh and apply" tactic to apply the rule
        typing_abs without having to calculate the appropriate finite
        set of atoms. *)

    pick fresh y and apply typing_abs.
    (* env_below *)
    eapply split_env_below_kn_weakening1.
    assert (env_below_kn empty (G2 ++ G1) K).
    eapply env_below_kn_strengthening. apply H0.
    apply H4.
    eapply (env_split_below_kn2 G1 E F).
    eapply env_below_kn_strengthening1. 
    rewrite_env ((G2 ++ [(x, bind_typ U)]) ++ G1) in H0.
    apply H0.
    eapply value_env_below_kn. apply TypU.
    eapply (wf_split_typ2 G1 E F).
    eapply (wf_typ_split1 G1 E F).
    eapply ok_remove_head. apply OK2.
    rewrite_env (G1 ++ empty).
    eapply env_below_kn_inversion. eapply H0.
    apply S. apply S. apply V. apply S. apply S.
    eapply (wf_env_split_splice1 G2 F E G1).
    apply (wf_env_split G1 E F).
    eapply wf_env_strengthening2. eapply wf_env_from_typing.
    rewrite_env ((G2 ++ [(x, bind_typ U)]) ++ G1) in H. apply H.
    eapply wf_env_from_typing. apply TypU. 
    apply S.
    apply OK2. apply S.
    eapply wf_env_strengthening. eapply wf_env_from_typing. apply H.
    
    (* check wf_typ (G2 ++ F) V0 K1 *)
    eapply (wf_typ_split_splice G2 G1 E F V0 K1). 
    eapply wf_typ_strengthening. apply H1. apply S. auto.

    (* Need to apply the IH. *)
    rewrite subst_ee_open_ee_var...
    rewrite <- concat_assoc.
    apply H3; auto.

    (* Clean up IH preconditions *)
    simpl. apply ok_cons. auto. rewrite dom_concat. fsetdec.
    simpl. apply ok_cons. auto. rewrite dom_concat. fsetdec.
    fsetdec. eapply expr_from_typing.  apply TypU.
*)
  Case "typing_app".
  
    destruct (env_split_cases E1 E2 G2 G1 x U0 empty); auto.
    SCase "nonlin".
      destruct H0 as [ER [FR [EL [FL [EQ1 [EQ2 [S1 [S2 WFT]]]]]]]].
      rewrite_env (G2 ++ F ++ empty).
      eapply (typing_split_splice G2 G1 E0 F empty). auto.
      simpl_env in *. 
      eapply (typing_app T1 K (EL ++ ER) (FL ++ FR) (G2 ++ G1)).
      eapply IHTypT1.


    (* There are several cases:
       Case 1: wf_typ G1 U kn_nonlin
           then E1 = E11 ++ [(x, bind_typ U)] ++ E12 and
                E2 = E21 ++ [(x, bind_typ U)] ++ E21 
           and the result follows by IH.
       Case 2: ~wf_typ G1 U kn_nonlin /\ wf_typ G1 u kn_lin
           There are two subcases:
          SC1:  E1 = E11 ++ [(x, bind_typ U)] ++ E12 and
                x `notin` dom E2
           
            Need to show that x `notin` dom E2 -> x `notin` fv_ee e2 and
            thus (subst_ee x u e2) = e2.
            Result follows by TypT2 and IHTypT1.

        or SC2: x `notin` dom E1 and
                E2 = E21 ++ [(x, bind_typ U)] ++ E21 
            Similar to SC1 above *)

    assert (exists K0, wf_typ G1 U0 K0) as EX.
    eapply wf_env_inversion. apply WFE.
    destruct EX as [K0 WFT]. 
    assert (ok F) as OKF. eapply ok_remove_head. apply OK2.
    assert (wf_typ F U0 K0) as WFT2. eapply wf_typ_split1; eauto.
    assert (ok G1) as OKG1. eapply ok_from_wf_typ. apply WFT.
    destruct K0.
    destruct (wf_typ_dec G1 U0 kn_nonlin) as [WFUnon | NWFUnon]; auto. 
    eapply type_from_wf_typ. apply WFT.
    
    SCase "nonlin".
      assert (wf_typ F U0 kn_nonlin).
      eapply wf_typ_split1; auto. apply WFUnon. apply S.
      assert (wf_typ E0 U0 kn_nonlin).
      eapply wf_split_typ2; auto. apply H0. apply S.
      assert (env_below_kn empty E0 kn_nonlin).
      eapply value_env_below_kn. apply TypU. apply H1. auto.  
      assert (G1 = F). eapply env_split_below_eq1. eapply split_env_commute.
      apply S; auto. auto.
      subst F.

(* 
   env_split G1 E0 F
   env_split E1 E2 (G2 ++ [(x, bind_typ U0)] ++ G1)
       E1 == E11 ++ [(x, bind_typ U0)] ++ E12
       E2 == E21 ++ [(x, bind_typ U0)] ++ E22
       env_split E12 E22 G1          typing (E12 ++ G1) (subst_ee u e1) 

                                     typing (
   env_split A B (G2 ++ F)
*)
      lapply (split_destruct5 G2 G1 x U0 E1 E2); auto.
      intros N. destruct N as [E11 [E12 [E21 [E22 [Q1 [Q2 S1]]]]]]; auto.

      (* Prepare to use IHTypT1 *)
      assert (exists G, env_split E12 E0 G) as EX.
      eapply exists_env_split1. eapply wf_env_strengthening2.
      rewrite_env ((G2 ++ [(x, bind_typ U0)]) ++ G1) in WFE. apply WFE.
      apply S1. apply S.
      destruct EX as [GG S2].
      assert (E12 = GG).  eapply env_split_below_eq1. 
      eapply split_env_commute. apply S2. auto.
      subst GG. 

      lapply (IHTypT1); clear IHTypT1; auto. intros IH1. 
      lapply (IH1 E0); clear IH1; auto. intros IH1. 
      lapply (IH1 E12 E12); clear IH1; auto. intros IH1. 
      lapply (IH1 E11); clear IH1; auto. intros IH1.

      (* Prepare to use IHTypT2 *)
      assert (exists G, env_split E22 E0 G) as EX.
      eapply exists_env_split1. eapply wf_env_strengthening2.
      rewrite_env ((G2 ++ [(x, bind_typ U0)]) ++ G1) in WFE. apply WFE.
      eapply split_env_commute. apply S1. apply S.
      destruct EX as [GG S3].
      assert (E22 = GG). eapply env_split_below_eq1.
      eapply split_env_commute. apply S3. auto.
      subst GG.

      lapply (IHTypT2); clear IHTypT2; auto. intros IH2. 
      lapply (IH2 E0); clear IH2; auto. intros IH2. 
      lapply (IH2 E22 E22); clear IH2; auto. intros IH2. 
      lapply (IH2 E21); clear IH2; auto. intros IH2.

      eapply (typing_app T1 K (E11 ++ E12) (E21 ++ E22) (G2 ++ G1)).
      apply IH1; auto. eapply ok_remove_mid. eapply ok_from_wf_env.
      eapply wf_env_from_typing. rewrite Q1 in TypT1. apply TypT1.
      apply IH2; auto. eapply ok_remove_mid. eapply ok_from_wf_env.
      eapply wf_env_from_typing. rewrite Q2 in TypT2. apply TypT2.
      rewrite Q1 in H. rewrite Q2 in H. 
      eapply env_split_strengthening2. apply WFE. apply H.
      
      eapply ok_split_splice2. apply WFE. subst E1. subst E2.
      eapply split_env_commute. apply H. auto. 
      eapply ok_split_splice2. apply WFE. subst E1. subst E2.
      apply H. auto.

  SCase "lin".
    lapply (split_destruct6 G2 G1 x U0 E1 E2 WFE); auto.
    intros HX. destruct HX as [C1 | C2]; auto.

    (* var is in the function *)
    destruct C1 as [E11 [E12 [E21 [E22 [Q1 [Q2 [S1 NI]]]]]]].
    rewrite <- (non_subst E2 e2 T1 x); auto.

(*  S :  env_split G1 E0 F
    H :  env_split E1 E2 (G2 ++ [(x, bind_typ U0)] ++ G1)
    S1 : env_split E12 E22 G1
    WFT: wf_typ G1 U0 kn_lin
    WFT2: wf_typ F U0 kn_lin
    E1 = E11 ++ [(x, bind_typ U0)] ++ E12
    E2 = E21 ++ E22

    env_split E12 E0 F
    E1 = E11 ++ [(x, bind_typ U0)] ++ E12
    typing (E11 ++ E12) (subst_ee x u e1) (typ_arrow K T1 T2)

    typing (E21 ++ E22) e2 T1

    exists FN, env_split F FN F  /\  env_below_kn empty FN kn_nonlin
    env_split E2 FN YY -> typing (E2 ++ FN) 

    typing XX (subst_ee x u e1) (typ_arrow K T1 T2)
    typing YY e2 T1
    env_split XX YY (G2 ++ F)
   -------------------------------------------------
    typing (G2 ++ F) tm_app (subst_ee x u e1) e2 T2
*)
    (* Use IHTypT1 *)    
    lapply (IHTypT1); clear IHTypT1; auto. intros IH1. 
    lapply (IH1 E0); clear IH1; auto. intros IH1. 
    lapply (IH1 E12 E12); clear IH1; auto. intros IH1. 
    lapply (IH1 E11); clear IH1; auto. intros IH1.
 
    
    
      
(* HERE *)                       




  Case "typing_tabs".
    pick fresh Y and apply typing_tabs.
    rewrite subst_ee_open_te_var...
    rewrite <- concat_assoc.
    apply H0...
Qed.
(* end show *)




(* ********************************************************************** *)
(** * #<a name="preservation"></a># Preservation *)

(*
Lemma typing_inv_abs : forall E S1 e1 T,
  typing E (exp_abs S1 e1) T ->
  forall U1 U2, sub E T (typ_arrow U1 U2) ->
     sub E U1 S1
  /\ exists S2, exists L, forall x, x `notin` L ->
     typing ([(x, bind_typ S1)] ++ E) (open_ee e1 x) S2 /\ sub E S2 U2.
Proof with auto.
  intros E S1 e1 T Typ.
  remember (exp_abs S1 e1) as e.
  generalize dependent e1.
  generalize dependent S1.
  induction Typ; intros S1 b1 EQ U1 U2 Sub; inversion EQ; subst.
  Case "typing_abs".
    inversion Sub; subst.
    split...
    exists T1. exists L...
  Case "typing_sub".
    auto using (sub_transitivity T).
Qed.

Lemma typing_inv_tabs : forall E S1 e1 T,
  typing E (exp_tabs S1 e1) T ->
  forall U1 U2, sub E T (typ_all U1 U2) ->
     sub E U1 S1
  /\ exists S2, exists L, forall X, X `notin` L ->
     typing ([(X, bind_sub U1)] ++ E) (open_te e1 X) (open_tt S2 X)
     /\ sub ([(X, bind_sub U1)] ++ E) (open_tt S2 X) (open_tt U2 X).
Proof with simpl_env; auto.
  intros E S1 e1 T Typ.
  remember (exp_tabs S1 e1) as e.
  generalize dependent e1.
  generalize dependent S1.
  induction Typ; intros S1 e0 EQ U1 U2 Sub; inversion EQ; subst.
  Case "typing_tabs".
    inversion Sub; subst.
    split...
    exists T1.
    exists (L0 `union` L).
    intros Y Fr.
    split...
    rewrite_env (empty ++ [(Y, bind_sub U1)] ++ E).
    apply (typing_narrowing S1)...
  Case "typing_sub".
    auto using (sub_transitivity T).
Qed.
*)


(* ********************************************************************** *)
(** ** Preservation (20) *)

Lemma preservation : forall e e' T,
  typing empty e T ->
  red e e' ->
  typing empty e' T.
Proof with simpl_env; eauto.
  intros e e' T Typ. remember empty as E. generalize dependent e'.
  induction Typ; intros e' Red; try solve [ inversion Red; subst; eauto ].
  Case "typing_app".
    inversion Red; subst...
    eapply typing_app. apply IHTyp1. inversion H. auto. auto. eauto. auto.
    eapply typing_app. apply Typ1. apply IHTyp2. inversion H. auto. auto. auto.

    SCase "red_abs".
      inversion H. 
      inversion Typ1; subst. 
      pick fresh x.
      lapply (H13 x). intros.
      rewrite (subst_ee_intro x)...
      rewrite_env (empty ++ empty).
      eapply (typing_through_subst_ee T1 empty x empty empty).  simpl_env. simpl_env in H0. auto.
      auto. intros. apply env_below_empty. auto. auto. simpl. auto. fsetdec.
  Case "typing_tapp".
    inversion Red; subst...
    SCase "red_tabs".
      inversion Typ. subst.
      pick fresh X.
      lapply (H3 X). intros.
      rewrite (subst_te_intro X)...
      rewrite (subst_tt_intro X)...
      rewrite_env (map (subst_tb X T) empty ++ empty).
      apply (typing_through_subst_te K)...
      fsetdec.
Qed.


(*
Lemma preservation : forall E e e' T,
  typing E e T ->
  red e e' ->
  typing E e' T.
Proof with simpl_env; eauto.
  intros E e e' T Typ. generalize dependent e'.
  induction Typ; intros e' Red; try solve [ inversion Red; subst; eauto ].
  Case "typing_app".
    inversion Red; subst...
    SCase "red_abs".
      inversion Typ1. subst.
      pick fresh x.
      lapply (H11 x). intros.
      rewrite (subst_ee_intro x)...
      rewrite_env (empty ++ E3).
      eapply (typing_through_subst_ee T1 E2 x E1 empty).  simpl_env. apply H0. apply Typ2.
      intros.      

  Case "typing_tapp".
    inversion Red; subst...
    SCase "red_tabs".
      destruct (typing_inv_tabs _ _ _ _ Typ T1 T2) as [P1 [S2 [L P2]]].
        apply sub_reflexivity...
      pick fresh X.
      destruct (P2 X) as [? ?]...
      rewrite (subst_te_intro X)...
      rewrite (subst_tt_intro X)...
      rewrite_env (map (subst_tb X T) empty ++ E).
      apply (typing_through_subst_te T1)...
Qed.
*)

(* ********************************************************************** *)
(** * #<a name="progress"></a># Progress *)


(* ********************************************************************** *)
(** ** Canonical forms (14) *)

Lemma canonical_form_abs : forall e U1 U2,
  value e ->
  typing empty e (typ_arrow U1 U2) ->
  exists V, exists e1, e = exp_abs V e1.
Proof.
  intros e U1 U2 Val Typ.
  remember empty as E.
  remember (typ_arrow U1 U2) as T.
  revert U1 U2 HeqT HeqE.
  induction Typ; intros U1 U2 EQT EQE; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
  Case "typing_sub".
    inversion H; subst; eauto.
    inversion H0.
Qed.

Lemma canonical_form_tabs : forall e U1 U2,
  value e ->
  typing empty e (typ_all U1 U2) ->
  exists V, exists e1, e = exp_tabs V e1.
Proof.
  intros e U1 U2 Val Typ.
  remember empty as E.
  remember (typ_all U1 U2) as T.
  revert U1 U2 HeqT HeqT.
  induction Typ; intros U1 U2 EQT EQE; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
  Case "typing_sub".
    inversion H; subst; eauto.
    inversion H0.
Qed.



(* ********************************************************************** *)
(** ** Progress (16) *)

Lemma progress : forall e T,
  typing empty e T ->
  value e \/ exists e', red e e'.
Proof with eauto.
  intros e T Typ.
  remember empty as E. generalize dependent HeqE.
  assert (Typ' : typing E e T)...
  induction Typ; intros EQ; subst...
  Case "typing_var".
    inversion H0.
  Case "typing_app".
    right.
    destruct IHTyp1 as [Val1 | [e1' Rede1']]...
    SCase "Val1".
      destruct IHTyp2 as [Val2 | [e2' Rede2']]...
      SSCase "Val2".
        destruct (canonical_form_abs _ _ _ Val1 Typ1) as [S [e3 EQ]].
        subst.
        exists (open_ee e3 e2)...
  Case "typing_tapp".
    right.
    destruct IHTyp as [Val1 | [e1' Rede1']]...
    SCase "Val1".
      destruct (canonical_form_tabs _ _ _ Val1 Typ) as [S [e3 EQ]].
      subst.
      exists (open_te e3 T)...
    SCase "e1' Rede1'".
      exists (exp_tapp e1' T)...
Qed.
