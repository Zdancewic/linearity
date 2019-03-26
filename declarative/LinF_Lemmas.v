(** Administrative lemmas for Fsub.

    Table of contents:
      - #<a href="##wft">Properties of wf_typ</a>#
      - #<a href="##oktwft">Properties of wf_env and wf_typ</a>#
      - #<a href="##okt">Properties of wf_env</a>#
      - #<a href="##subst">Properties of substitution</a>#
      - #<a href="##regularity">Regularity lemmas</a>#
      - #<a href="##auto">Automation</a># *)

Require Export LinF_Infrastructure.
Require Import Omega.


Lemma list_empty: forall (E:env), E ++ empty = E.
Proof.
  induction E; simpl; auto.
  rewrite IHE. auto.
Qed.


Lemma eq_env_head: forall (E1:env) F1 Y,
  E1 ++ [Y] = F1 ++ [Y] ->
  E1 = F1.
Proof.
  intros. assert (E1 = F1 /\ Y = Y).
  apply app_inj_tail. auto.
  tauto.
Qed.

Lemma eq_env_tail: forall (E2:env) F2 Y,
  [Y] ++ E2 = [Y] ++ F2 ->
  E2 = F2.
Proof.
  induction E2; intros.
  simpl in H. inversion H. auto.
  destruct F2.
  simpl in H. inversion H.
  simpl in H. inversion H. subst. auto.
Qed.


Lemma eq_env_concat1: forall (E1 :env) E2 F1 F2,
  E1 = F1 -> 
  E1 ++ E2 = F1 ++ F2 ->
  E2 = F2.
Proof.
  intros. subst.
  induction F1. simpl in H0. auto.
  apply IHF1. rewrite_env ([a]++(F1 ++ E2)) in H0.
  rewrite_env ([a]++(F1 ++ F2)) in H0.
  eapply eq_env_tail. apply H0.
Qed.

Lemma eq_env_concat2: forall (E1 :env) E2 F1 F2,
  E2 = F2 -> 
  E1 ++ E2 = F1 ++ F2 ->
  E1 = F1.
Proof.
  intros.
  assert (rev (E1 ++ E2) = rev (F1 ++ F2)).
  rewrite H0. auto.
  rewrite distr_rev in H1. rewrite distr_rev in H1.
  assert (rev E1 = rev F1).
  eapply eq_env_concat1. assert (rev E2 = rev F2). rewrite H. auto.
  eapply H2. auto. rewrite <- rev_involutive. rewrite <- (rev_involutive E1).
  rewrite H2. auto.
Qed.

Lemma eq_list_mid: forall (E1:env) E2 F1 F2 Y,
  ok (E1 ++ [Y] ++ E2) ->
  E1 ++ [Y] ++ E2 = F1 ++ [Y] ++ F2 ->
   E1 = F1 /\ E2 = F2
.
Proof.
  induction E1; intros; auto.
  destruct F1.   simpl in *. split; auto. eapply eq_env_tail. simpl. eapply H0.
  rewrite H0 in H. simpl in H0. inversion H0. subst.
    simpl in H. inversion H. rewrite dom_concat in H4. assert False. apply H4. simpl. fsetdec. tauto.
  destruct F1. simpl in H0. inversion H0. subst.
     simpl in H. inversion H. rewrite dom_concat in H4. assert False. apply H4. simpl. fsetdec. tauto.
  rewrite_env (a :: (E1 ++ [Y] ++ E2)) in H0.
  rewrite_env (p :: (F1 ++ [Y] ++ F2)) in H0.
  inversion H0. subst a. assert (E1 = F1 /\ E2 = F2). apply (IHE1 E2 F1 F2 Y).
  rewrite_env ([p] ++ E1 ++ [Y] ++ E2) in H. eapply ok_remove_head. eapply H.
  auto. destruct H1; subst; auto.
Qed.

  
Lemma eq_list_mid2: forall (E1:env) x a E2 F1 F2 b,
  ok (E1 ++ [(x, a)] ++ E2) ->
  E1 ++ [(x, a)] ++ E2 = F1 ++ [(x, b)] ++ F2 ->
   E1 = F1 /\ E2 = F2 /\ a = b
.
Proof.
  intros E1 x a E2.
  remember (E1 ++ [(x, a)] ++ E2) as G.
  generalize dependent G. generalize dependent E2. generalize dependent a. generalize dependent x.
  induction E1; intros x a1 E2 G EQG F1 F2 b OK EQ; auto.
  subst.
    destruct F1. simpl in *. inversion EQ; subst. repeat split; auto.
    simpl in *. inversion EQ. rewrite EQ in OK. subst p. simpl_env in OK.  
    assert (x `notin` dom [(x, a1)]). eapply fresh_mid_head_In.  rewrite_env ([(x, a1)] ++ (F1 ++ [(x, b)]) ++ F2) in OK.
    apply OK. rewrite dom_concat. simpl. fsetdec. simpl in H. assert False. apply H. fsetdec. tauto.

    destruct F1. subst. simpl in EQ.  inversion EQ. subst a.
    assert (x `notin` dom [(x, b)]). eapply fresh_mid_head_In.  rewrite_env ([(x, b)] ++ (E1 ++ [(x, a1)]) ++ E2) in OK.
    apply OK. rewrite dom_concat. simpl. fsetdec. simpl in H. assert False. apply H. fsetdec. tauto.
    subst.
    rewrite_env (a :: (E1 ++ [(x, a1)] ++ E2)) in EQ.
    rewrite_env (p :: (F1 ++ [(x, b)] ++ F2)) in EQ.
    inversion EQ. subst a.
    assert (E1 = F1 /\ E2 = F2 /\ a1 = b). apply (IHE1 x a1 E2 (E1 ++ [(x, a1)] ++ E2)). auto.
    eapply ok_remove_head. rewrite_env ([p] ++ E1 ++ [(x, a1)] ++ E2) in OK. eauto. auto.
    destruct H as [Q1 [Q2 Q3]]. subst. repeat split; auto.
Qed.
    
Lemma ok_distinct: forall A (E1:env) X E2,
  ok ((A :: E1) ++ [X] ++ E2) ->
  A <> X.
Proof.
  intros.
  inversion H. destruct X.
  rewrite dom_concat in H3. simpl in H3. unfold not. intros. inversion H4. subst. unfold not in H3. apply H3. fsetdec.
Qed.

Lemma ok_join: forall (E:env) F G,
  ok (F ++ E) ->
  ok (G ++ E) ->
  ok (G ++ F) ->
  ok (G ++ F ++ E).
Proof.
  intros E F G.
  generalize dependent E. generalize dependent F.
  induction G; intros F E OK1 OK2 OK3.
  Case "nil".
    simpl_env.  auto.
  Case "cons".
    rewrite_env ([a] ++ G ++ F ++ E).
    rewrite_env ([a] ++ G ++ F) in OK3.
    rewrite_env ([a] ++ G ++ E) in OK2.
    inversion OK2. inversion OK3.
    simpl. apply ok_cons.
    apply IHG; auto.
    rewrite dom_concat. rewrite dom_concat.
    rewrite dom_concat in H6. rewrite dom_concat in H2. 
    notin_solve.
Qed.
  
Lemma ok_commute: forall (E:env) G,
  ok (E ++ G) ->
  ok (G ++ E).
Proof.
  intros E G; generalize dependent E.
  induction G; intros E H.
  Case "nil".
    simpl_env. simpl_env in H. auto.
  Case "cons".
    rewrite_env (E ++ [a] ++ G) in H.
    simpl. destruct a. apply ok_cons. 
    apply IHG; auto.
    eapply ok_remove_mid. eauto.
    assert (a `notin` dom E). eapply fresh_mid_head; eauto.
    assert (a `notin` dom G). eapply fresh_mid_tail; eauto.
    rewrite dom_concat. notin_solve.
Qed.

Lemma binds_weaken_at_tail : forall (x:atom) (a:binding) F G,
  binds x a F ->
  ok (F ++ G) ->
  binds x a (F ++ G).
Proof.
  intros x a F G H J.
  rewrite_env (F ++ G ++ nil).
  apply binds_weaken; simpl_env; trivial.
Qed.

Lemma type_from_wf_typ : forall E T K,
  wf_typ E T K -> type T.
Proof.
  intros E T K H; induction H; eauto.
Qed.

Lemma wf_typ_weakening : forall T E F G K,
  wf_typ (G ++ E) T K ->
  ok (G ++ F ++ E) ->
  wf_typ (G ++ F ++ E) T K.
Proof with simpl_env; eauto.
  intros T E F G K Hwf_typ Hk.
  remember (G ++ E) as F.
  generalize dependent G.
  induction Hwf_typ; intros G Hok Heq; subst...
  Case "type_all".
    pick fresh Y and apply wf_typ_all...
    rewrite <- concat_assoc.
    apply H0...
Qed.

Lemma wf_typ_weaken_head : forall T E F K,
  wf_typ E T K ->
  ok (F ++ E) ->
  wf_typ (F ++ E) T K.
Proof.
  intros.
  rewrite_env (empty ++ F++ E).
  auto using wf_typ_weakening.
Qed.

Lemma wf_typ_subst_tb : forall F Q E Z P T K,
  wf_typ (F ++ [(Z, bind_kn Q)] ++ E) T K ->
  wf_typ E P Q->
  wf_typ (map (subst_tb Z P) F ++ E) (subst_tt Z P T) K.
Proof with simpl_env; eauto using wf_typ_weaken_head, type_from_wf_typ.
  intros F Q E Z P T K WT WP.
  remember (F ++ [(Z, bind_kn Q)] ++ E) as G.
  generalize dependent F.
  induction WT; intros F EQ; subst; simpl subst_tt...
  Case "wf_typ_var".
    destruct (X == Z).  subst...
      binds_get H0.
      inversion H2. subst...
      binds_cases H0... 
      apply wf_typ_var. assert ((subst_tb Z P (bind_kn K)) = (bind_kn K)).
      simpl. auto. apply ok_map_app_l. 
      eapply ok_remove_mid. eapply H.
      apply binds_weaken_at_tail.
      assert (bind_kn K = (subst_tb Z P (bind_kn K))).
      simpl; auto. rewrite H0.
      apply binds_map. auto. apply ok_map_app_l.
      apply (@ok_remove_mid binding [(Z, bind_kn Q)]). auto.
  Case "wf_typ_all".
    pick fresh Y and apply wf_typ_all...
    rewrite subst_tt_open_tt_var...
    rewrite_env (map (subst_tb Z P) ([(Y, bind_kn K1)] ++ F) ++ E).
    apply H0...
Qed.


Lemma wf_typ_rename : forall G T x y K1 K2, 
  ok G ->
  y `notin` (singleton x `union` fv_tt T `union` dom G)  ->
  x `notin` (fv_tt T `union` dom G) ->
  wf_typ ([(x, bind_kn K1)] ++ G) (open_tt T x) K2 ->
  wf_typ ([(y, bind_kn K1)] ++ G) (open_tt T y) K2.
Proof.
  intros. 
  rewrite (subst_tt_intro x).
  rewrite_env (empty ++ [(y, bind_kn K1)] ++ G).
  assert (empty = map (subst_tb x y) empty).
  simpl. auto.
  rewrite H3.
  eapply wf_typ_subst_tb. simpl_env. 
  eapply wf_typ_weakening. eauto. 
    simpl. apply ok_cons; auto. simpl. 
  apply wf_typ_var. apply ok_cons. auto. notin_solve.
  rewrite_env ([(y, bind_kn K1)] ++ G).
  apply binds_head. apply binds_singleton. notin_solve.
Qed.

Lemma wf_all_exists : forall T x K1 G K2,
  ok G ->
  x `notin` (fv_tt T `union` dom G) ->
  wf_typ ([(x, bind_kn K1)] ++ G) (open_tt T x) K2 ->
  wf_typ G (typ_all K1 T) K2.
Proof.
  intros.
  pick fresh y and apply wf_typ_all.
  apply (wf_typ_rename G T x). auto. notin_solve. auto. auto.
Qed.


(* Decidability results: *)
Lemma in_dom_dec: forall x (E:env),
  {x `in` dom E} + {~ x `in` dom E}.
Proof.
  intros x; induction E.
  right. fsetdec.
  destruct a. destruct IHE.
    left. rewrite_env ([(a, b)] ++ E). rewrite dom_concat. simpl. fsetdec.
    destruct (x == a).
    subst. left. simpl. fsetdec. right. simpl. fsetdec.
Qed.

Lemma ok_dec: forall (E:env),
  {ok E} + {~ok E}.
Proof.
  induction E; auto.
  destruct a.
  destruct (in_dom_dec a E).
  destruct IHE. right. unfold not. intros. inversion H. contradiction.
  right. unfold not; intros; inversion H; contradiction.
  destruct IHE. left. apply ok_cons; auto.
  right. unfold not. intros; inversion H; contradiction.
Qed.

Lemma eq_kn_dec: forall (k1 k2:kn), {k1 = k2} + {~k1 = k2}.
Proof.
  decide equality.
Qed.

Lemma eq_typ_dec: forall (t1 t2:typ), {t1 = t2} + {~t1 = t2}.
Proof.
  decide equality. apply eq_nat_dec. apply eq_atom_dec.
  apply eq_kn_dec. apply eq_kn_dec.
Qed.

Lemma eq_bnd_dec: forall (a b:binding), {a = b}+{~a=b}.
Proof.
  decide equality. apply eq_kn_dec. apply eq_typ_dec.
Qed.
  
Lemma eq_binding_dec: forall (x y:(atom * binding)%type), {x = y}+{~x = y}.
Proof.
  decide equality. apply eq_bnd_dec. apply eq_atom_dec.
Qed.


Lemma binds_dec: forall x b (E:env),
  {binds x b E} + {~binds x b E}.
Proof.
  intros. induction E.
  unfold binds. right. unfold get. unfold not. intros. inversion H.
  destruct a. 
    destruct (x == a). subst. destruct (eq_bnd_dec b b0). subst.
    left. unfold binds. simpl. destruct (a == a). auto. destruct n. auto.
    right. unfold not. intros. inversion H. destruct (a == a). 
      inversion H1. apply n; auto. apply n0. auto.
    destruct IHE. left. unfold binds. simpl get. destruct (x == a). destruct n. auto. auto.
    right. unfold not. intros. unfold binds in H. simpl in H. 
      destruct (x == a). apply n; auto. apply n0. auto.
Qed.

Lemma wf_typ_dec: forall G T K,
  ok G ->
  type T ->
  (wf_typ G T K) \/ (~wf_typ G T K).
Proof.
  intros G T K OK Hyp. generalize dependent G. generalize dependent K.
  induction Hyp; intros K0 G OK; auto.

  Case "fvar".
    destruct (binds_dec X (bind_kn K0) G).
    left. apply wf_typ_var; auto. destruct K0. 
       destruct (binds_dec X (bind_kn kn_nonlin) G).
       left. apply wf_typ_sub. apply wf_typ_var; auto.
       right. unfold not; intros. inversion H. apply n; auto. inversion H0. apply n0; auto.
       right. unfold not; intros. inversion H. apply n; auto.

  Case "arrow".
    destruct (eq_kn_dec K0 K). subst.
    destruct (IHHyp1 kn_lin G OK); destruct (IHHyp1 kn_nonlin G OK); 
    destruct (IHHyp2 kn_lin G OK); destruct (IHHyp2 kn_nonlin G OK); 
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

    destruct (IHHyp1 kn_lin G OK); destruct (IHHyp1 kn_nonlin G OK); 
    destruct (IHHyp2 kn_lin G OK); destruct (IHHyp2 kn_nonlin G OK);
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
      notin_solve.
      destruct (H0 y FR K0 ([(y, bind_kn K)] ++ G)). 
      simpl. apply ok_cons. auto. notin_solve.
      left. apply (wf_all_exists T2 y). auto. notin_solve. auto. 
      right. unfold not. intros. inversion H2. subst. 
      pick fresh z. lapply (H7 z). intros. 
      apply H1. apply (wf_typ_rename G T2 z y). auto. notin_solve. 
        notin_solve. auto. notin_solve.
      inversion H3. subst.
      pick fresh z. lapply (H11 z). intros. 
      apply H1. apply (wf_typ_rename G T2 z y). auto. notin_solve. 
        notin_solve. auto. notin_solve.
Qed.


Lemma env_cases: forall (E1:env) E2 F1 F2 X Y,
  X <> Y ->
  ok (E1 ++ [X] ++ E2) ->
  ok (F1 ++ [Y] ++ F2) ->
  E1 ++ [X] ++ E2 = F1 ++ [Y] ++ F2 ->
  (exists M,
    (E2 =  M ++ [Y] ++ F2  /\ 
     F1 = E1 ++ [X] ++ M))
  \/
  (exists M,
    (E1 = F1 ++ [Y] ++ M /\
     F2 = M ++ [X] ++ E2))
.    
Proof.
  intros E1.
  induction E1. intros.
    destruct F1. simpl in *. inversion H2. contradiction.
       simpl in H2.  inversion H2. subst p. left. exists F1. simpl. auto.
    (* cons case *)
    intros.
    destruct F1. simpl in *. inversion H2. subst a. right. exists E1. auto.
    (* hard case. *)
    assert (a <> X).  
    eapply ok_distinct. eapply H0.
    assert (p <> Y).
    eapply ok_distinct. eapply H1.
    inversion H2.
    subst a.
    assert (ok (E1 ++ [X] ++ E2)).
    rewrite_env ([p] ++ (E1 ++ [X] ++ E2)) in H0.
    eapply  ok_remove_head. eapply H0.
    rewrite_env ([p] ++ (F1 ++ [Y] ++ F2)) in H1.
    assert (ok (F1 ++ [Y] ++ F2)).
    eapply ok_remove_head. eapply H1.
    destruct (IHE1 E2 F1 F2 X Y H H5 H6 H7).
    left. destruct H8. exists x. destruct H8. subst. auto.
    right. destruct H8. exists x. destruct H8. subst. auto.
Qed.


Lemma env_mid_two: forall (E1:env) X E2 F1 F2,
   ok (E1 ++ [X] ++ E2) -> 
   E1 ++ [X] ++ E2 = F1 ++ F2 ->
      (* X is in F1 *)
   (exists F12, F1 = E1 ++ [X] ++ F12 /\ E2 = F12 ++ F2) \/
      (* X is in F2 *)
   (exists F21, E1 = F1 ++ F21 /\ F2 = F21 ++ [X] ++ E2).
Proof with try rewrite list_empty; auto.
  intros E1 X E2 F1 F2 OK EQ.
  destruct F2.
  left. exists E2. simpl in *. rewrite <- app_nil_end. rewrite <- app_nil_end in EQ. auto.
  destruct (eq_binding_dec X p).
  subst p. rewrite_env (F1 ++ [X] ++ F2) in EQ.
  right. exists empty. rewrite <- app_nil_end. rewrite_env ([X] ++ E2).
  assert (E1 = F1 /\ E2 = F2).
  eapply eq_list_mid. eapply OK.
  auto. destruct H. subst; auto.
  rewrite_env (F1 ++ [p] ++ F2) in EQ.
  lapply (env_cases E1 E2 F1 F2 X p n OK).  intros.
  destruct (H EQ).
  left. destruct H0. exists x. tauto.
  right. destruct H0. exists ([p] ++ x). simpl in H0. simpl. destruct H0. subst. tauto.
  rewrite <- EQ. auto.
Qed.


(* ********************************************************************** *)
(** * #<a name="wft"></a># Properties of [wf_typ] *)

Lemma wf_typ_strengthening : forall E F x U T K,
 wf_typ (F ++ [(x, bind_typ U)] ++ E) T K ->
 wf_typ (F ++ E) T K.
Proof with simpl_env; eauto.
  intros E F x U T K H.
  remember (F ++ [(x, bind_typ U)] ++ E) as G.
  generalize dependent F.
  induction H; intros F Heq; subst...
  Case "wf_typ_var".
    binds_cases H0...
  Case "wf_typ_all".
    pick fresh Y and apply wf_typ_all...
    rewrite <- concat_assoc.
    apply H0...
Qed.




(* ********************************************************************** *)
(** * #<a name="oktwft"></a># Properties of [wf_env] and [wf_typ] *)

Lemma wf_env_inversion: forall E2 E1 x T,
  wf_env (E2 ++ [(x, bind_typ T)] ++ E1) ->
  wf_typ E1 T kn_nonlin.
Proof.
  induction E2; intros E1 x T WF.
  simpl_env in WF. inversion WF.  auto.
  eapply IHE2. rewrite_env ([a] ++ E2 ++ [(x, bind_typ T)] ++ E1) in WF.
  inversion WF. simpl_env in H1. apply H1. apply H1.
Qed.

Lemma ok_from_wf_env : forall E,
  wf_env E ->
  ok E.
Proof.
  intros E H; induction H; auto.
Qed.

Lemma ok_from_wf_typ:  forall E T K,
  wf_typ E T K ->
  ok E
.
Proof.
  intros E T K Hyp.
  induction Hyp; auto.
  pick fresh Y. lapply (H0 Y). intros. eapply ok_remove_head; auto. eauto.
  notin_solve.
Qed.

Lemma ok_remove_tail : forall (E:env) F,
  ok (E ++ F) ->
  ok E.
Proof.
  intros.
  rewrite_env (E ++ nil).
  rewrite_env (E ++ F ++ nil) in H.
  eauto using ok_remove_mid.
Qed.

Lemma binds_in_dom: forall x P (E:env),
  binds x P E -> x `in` (dom E).
Proof.
  induction E; intros.
  Case "nil".
  unfold binds in H. simpl in H. inversion H.
  Case "cons".
  unfold binds in H. simpl in H. destruct a.
  destruct (x == a).
    subst. rewrite_env ([(a, b)] ++ E).
    rewrite dom_concat. simpl. fsetdec.
    rewrite_env ([(a, b)] ++ E). simpl. 
    assert (x `in` dom E). apply IHE. unfold binds. auto. fsetdec.
Qed.
  
Lemma in_singleton_id: forall (x:atom) y,
  forall x, x `in` singleton y -> x = y.
Proof.
  intros.
  fsetdec.
Qed.

(** We add [ok_from_wf_env] as a hint here since it helps blur the
    distinction between [wf_env] and [ok] in proofs.  The lemmas in
    the [Environment] library use [ok], whereas here we naturally have
    (or can easily show) the stronger [wf_env].  Thus,
    [ok_from_wf_env] serves as a bridge that allows us to use the
    environments library. *)

Hint Resolve ok_from_wf_env.

Lemma wf_typ_from_binds_typ : forall x U E,
  wf_env E ->
  binds x (bind_typ U) E ->
  wf_typ E U kn_nonlin.
Proof with auto using wf_typ_weaken_head.
  induction 1; intros J; binds_cases J...
  inversion H4. subst...
Qed.

Lemma wf_typ_from_wf_env_typ : forall x T E,
  wf_env ([(x, bind_typ T)] ++ E) ->
  wf_typ E T kn_nonlin.
Proof.
  intros x T E H. inversion H; auto.
Qed.

Lemma lempty_noteq_concat: forall D1 X D2,
  (lempty = D1 ++ [X] ++ D2) -> False.
Proof.
  intros.
  destruct D1; simpl; intros; inversion H.  
Qed.

Lemma wf_typ_from_wf_lenv: forall x T E D1 D2,
  wf_lenv E (D1 ++ [(x, lbind_typ T)] ++ D2) ->
  wf_typ E T kn_lin.
Proof.
  intros x T E D1 D2 WFL.
  remember (D1 ++ [(x, lbind_typ T)] ++ D2) as D.
  generalize dependent D1.
  induction WFL; intros D1 EQ.
     assert False. eapply lempty_noteq_concat. eapply EQ. tauto.
  destruct D1; inversion EQ; subst.
    auto.
  apply (IHWFL D1); auto.
Qed.

(* ********************************************************************** *)
(** * #<a name="okt"></a># Properties of [wf_env] *)

(** These properties are analogous to the properties that we need to
    show for the subtyping and typing relations. *)

Lemma wf_env_strengthening : forall x T E F,
  wf_env (F ++ [(x, bind_typ T)] ++ E) ->
  wf_env (F ++ E).
Proof with eauto using wf_typ_strengthening.
  induction F; intros Wf_env; inversion Wf_env; subst; simpl_env in *...
Qed.

Lemma wf_lenv_strengthening: forall x T E F D,
  wf_lenv (F ++ [(x, bind_typ T)] ++ E) D ->
  wf_lenv (F ++ E) D.
Proof.
  intros x T E F D WFL.
  remember (F ++ [(x, bind_typ T)] ++ E) as E0.
  generalize dependent F.
  induction WFL; intros F EQ.
    apply wf_lenv_empty. eapply wf_env_strengthening. subst. auto. eauto.
    apply wf_lenv_typ. apply IHWFL; auto. rewrite dom_concat. subst.
    repeat rewrite dom_concat in H. fsetdec. auto.
    eapply wf_typ_strengthening.  subst. auto. eauto.
Qed.

Lemma wf_env_subst_tb : forall K Z P E F,
  wf_env (F ++ [(Z, bind_kn K)] ++ E) ->
  wf_typ E P K ->
  wf_env (map (subst_tb Z P) F ++ E).
Proof with eauto 6 using wf_typ_subst_tb.
  induction F; intros Wf_env WP; simpl_env;
    inversion Wf_env; simpl_env in *; simpl subst_tb...
Qed.

Lemma wf_lenv_subst_tb: forall K Z P E F D,
  wf_lenv (F ++ [(Z, bind_kn K)] ++ E) D ->
  wf_typ E P K ->
  wf_lenv (map (subst_tb Z P) F ++ E) (map (subst_tlb Z P) D).
Proof.
  intros K Z P E F D WFL.
  remember (F ++[(Z, bind_kn K)] ++ E) as E0.
  generalize dependent F.
  induction WFL; intros F EQ WFT; subst; simpl_env in *.
    apply wf_lenv_empty. eapply wf_env_subst_tb; eauto.
    simpl. simpl_env.
    apply wf_lenv_typ. apply IHWFL; auto.
    repeat rewrite dom_concat in *. rewrite dom_map. fsetdec.
    rewrite dom_map. auto.
    eapply wf_typ_subst_tb; eauto.
Qed.



(* ********************************************************************** *)
(** * #<a name="subst"></a># Environment is unchanged by substitution for a fresh name *)

Lemma notin_fv_tt_open : forall (Y X : atom) T,
  X `notin` fv_tt (open_tt T Y) ->
  X `notin` fv_tt T.
Proof.
 intros Y X T. unfold open_tt.
 generalize 0.
 induction T; simpl; intros K Fr; notin_simpl; try apply notin_union; eauto.
Qed.

Lemma notin_fv_wf : forall E (X : atom) T K,
  wf_typ E T K ->
  X `notin` dom E ->
  X `notin` fv_tt T.
Proof with auto.
  intros E X T K Wf_typ.
  induction Wf_typ; intros Fr; simpl...
  Case "wf_typ_var".
    assert (X0 `in` (dom E))...
    eapply binds_In; eauto.
  Case "wf_typ_all".
    pick fresh Y.
    apply (notin_fv_tt_open Y)...
Qed.

Lemma map_subst_tb_id : forall G Z P,
  wf_env G ->
  Z `notin` dom G ->
  G = map (subst_tb Z P) G.
Proof with auto.
  intros G Z P H.
  induction H; simpl; intros Fr; simpl_env...
  rewrite <- IHwf_env...
  rewrite <- IHwf_env...
    rewrite <- subst_tt_fresh... eapply notin_fv_wf; eauto.
Qed.

Lemma open_kn: forall L K1 K2 E T,
  (forall Y, Y `notin` L -> wf_typ ([(Y, bind_kn K1)] ++ E) (open_tt T Y) K2) ->
  wf_typ E (typ_all K1 T) K2.
Proof.
  intros L K1 K2 E T H.
  induction T;
  pick fresh Z and apply wf_typ_all.
  destruct (n === 0). subst. simpl. unfold open_tt. simpl.
  lapply (H Z). intros.
  simpl in H0. unfold open_tt in H0. simpl in H0. auto. auto.
  apply (H Z). auto.
  apply (H Z). auto.
  unfold open_tt. simpl.
  lapply (H Z). intros. inversion H0. subst.
  eapply wf_typ_arrow. eauto. eauto.
  auto. auto.
  apply (H Z). auto.
Qed.

(* Basic properties of the env_split relation *)

Lemma dom_lenv_split: forall G E1 E2 E3,
  lenv_split G E1 E2 E3  -> dom E3 = dom E1 `union` dom E2.
Proof.
  intros E1 E2 E3 G S.
  induction S; simpl; try fsetdec. 
  rewrite IHS. fsetdec.
  rewrite IHS. fsetdec.
Qed.

Lemma lenv_split_commute: forall G E1 E2 E3,
  lenv_split G E1 E2 E3 ->
  lenv_split G E2 E1 E3.
Proof.
  intros G E1 E2 E3 S.
  induction S; auto.
  apply lenv_split_empty. auto.
  apply lenv_split_right; auto.
  apply lenv_split_left; auto.
Qed.

Lemma lenv_split_empty1: forall G E F,
  lenv_split G lempty E F ->
  E = F
.
Proof.
  induction E; intros F H; inversion H; auto.
  rewrite (IHE D3). auto. auto.
Qed.

Lemma lenv_split_empty2: forall G E F,
  lenv_split G E lempty F ->
  E = F
.
Proof.
  intros. eapply lenv_split_empty1. eapply lenv_split_commute. eauto.
Qed.

Lemma wf_env_split0: forall E1 E2 E3 G,
  lenv_split G E1 E2 E3  ->
  wf_lenv G E3.
Proof.
  intros G E1 E2 E3 S.
  induction S; simpl_env in *. 
  auto.
  eapply wf_lenv_typ. auto. eauto. auto. auto.
  eapply wf_lenv_typ. auto. eauto. auto. auto.
Qed.

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
 wf_typ (F ++ E) T K.
Proof with simpl_env; eauto.
  intros E F X K1 T K H.
  remember (F ++ [(X, bind_kn K1)] ++ E) as G.
  generalize dependent F.
  induction H; intros F Heq Nin; subst...
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

Lemma wf_lenv_strengthening2: forall G D X K, 
  wf_lenv ([(X, bind_kn K)] ++ G) D ->
  X `notin` fv_lenv D ->
  wf_lenv G D.
Proof.
  induction D; intros X K WFL NIN.
  apply wf_lenv_empty.
  inversion WFL. inversion H. auto.
  destruct a. destruct l. simpl in NIN.
  inversion WFL. subst.
  simpl_env in *.
  apply wf_lenv_typ.
  eapply IHD; eauto.
  fsetdec. fsetdec.
  rewrite_env (empty ++ G).
  eapply wf_typ_strengthening2. simpl_env. apply H6.
  fsetdec.
Qed.

(* requires the kind to be kn_lin!! *)
Lemma typing_regular : forall E D e T,
  typing E D e T ->
  wf_env E /\ wf_lenv E D /\ expr e /\ wf_typ E T kn_lin.
Proof with simpl_env; auto*.
  intros E D e T H; induction H...
  Case "typing_var".
    repeat split...
    eauto using wf_typ_from_binds_typ.
  Case "typing_lvar".
    repeat split...
    inversion H; auto. inversion H3; auto.
    inversion H; auto.
  Case "typing_abs".
    pick fresh y.
    destruct (H1 y)...
    repeat split...
    rewrite_env (empty ++ E). 
    eapply wf_env_strengthening. simpl_env. eapply H3.
    destruct H4 as [WFL [EXP WFT]].
    rewrite_env (empty ++ E). 
    eapply wf_lenv_strengthening. simpl_env. apply WFL.
    pick fresh x and apply expr_abs.
    eapply type_from_wf_typ. eauto.
    lapply (H1 x). auto... fsetdec.
    destruct K.
    eapply wf_typ_arrow. eauto.
    rewrite_env (empty ++ E).
    eapply wf_typ_strengthening; simpl_env; eauto.
    destruct H4 as [WFL [EXP WFT]].
    apply WFT.
    eapply wf_typ_sub.
    eapply wf_typ_arrow. eauto.
    rewrite_env (empty ++ E).
    eapply wf_typ_strengthening; simpl_env; eauto.
    destruct H4 as [WFL [EXP WFT]].
    apply WFT.
  Case "typing_labs".
    pick fresh y.
    destruct (H1 y)...
    repeat split...
    destruct H4. destruct H5.
    inversion H4. auto.
    pick fresh x and apply expr_abs.
    eapply type_from_wf_typ. eauto.
    lapply (H1 x). auto... fsetdec.
    destruct H4 as [WFL [EXP WFT]].
    inversion WFL. subst.
    destruct K.
    eapply wf_typ_arrow. eauto.
    eauto.
    eapply wf_typ_sub; eauto.
  Case "typing_app".
    destruct IHtyping1 as [WF1 [WFL1 [EX1 J1]]]...
    destruct IHtyping2 as [WF2 [WFL2 [EX2 J2]]]...
    repeat split...
      eapply wf_env_split0. apply H1.
    inversion J1; subst; auto.
    destruct K2. auto. apply wf_typ_sub. auto.
    inversion H2; subst; auto.
    destruct K2. auto. apply wf_typ_sub. auto.
  Case "typing_tabs".
    pick fresh Y.
    destruct (H1 Y) as [HWF [WFL [EX WT]]]...
    inversion HWF; subst.
    repeat split...
    inversion WFL; subst; auto.
    eapply wf_lenv_strengthening2. apply WFL.
    fsetdec.
    pick fresh X and apply expr_tabs.
    destruct (H1 X) as [A [B [C CC]]]...
    pick fresh X and apply wf_typ_all.
    destruct (H1 X) as [A [B [C CC]]]...
  Case "type_tapp".
    repeat split...
    apply (expr_tapp).
    tauto.
    eapply type_from_wf_typ. eapply H0.
    destruct IHtyping as [_ [_ [_ WF]]].
    inversion WF; subst... 
    pick fresh Y.
    rewrite (subst_tt_intro Y).
    rewrite_env ((map (subst_tb Y T) empty) ++ E).
    eapply (wf_typ_subst_tb empty K).
    rewrite_env ([(Y, bind_kn K)] ++ E).
    apply H5. auto. auto. auto.
    apply wf_typ_sub.
    inversion H1; subst...
    pick fresh Y.
    rewrite (subst_tt_intro Y).
    rewrite_env ((map (subst_tb Y T) empty) ++ E).
    eapply (wf_typ_subst_tb empty K).
    rewrite_env ([(Y, bind_kn K)] ++ E).
    apply H6. auto. auto. auto.
Qed.
    
Lemma value_regular : forall e,
  value e ->
  expr e.
Proof.
  intros e H. induction H; auto.
Qed.

Lemma red_regular : forall e e',
  red e e' ->
  expr e /\ expr e'.
Proof with auto*.
  intros e e' H.
  induction H; assert(J := value_regular); split...
  Case "red_abs".
    inversion H. pick fresh y. rewrite (subst_ee_intro y)...
  Case "red_tabs".
    inversion H. pick fresh Y. rewrite (subst_te_intro Y)...
Qed.

Lemma wf_env_weakening: forall E F,
  wf_env E ->
  wf_env F ->
  ok (F ++ E) ->
  wf_env (F ++ E).
Proof.
  intros E F.
  generalize dependent E.
  induction F; intros E WF1 WF2 OK.
  simpl. auto.
  inversion WF2. 
  rewrite_env ([(X, bind_kn K)] ++ F ++ E).
  eapply wf_env_kn. apply IHF; auto. rewrite_env ([a] ++ (F ++ E)) in OK. eapply ok_remove_head. eapply OK. subst a.
  inversion OK.  auto.
  rewrite_env ([(x, bind_typ T)] ++ F ++ E).
  eapply wf_env_typ. apply IHF; auto. rewrite_env ([a] ++ (F ++ E)) in OK. eapply ok_remove_head. eapply OK. 
  rewrite_env (F ++ E ++ empty). apply wf_typ_weakening. rewrite <- app_nil_end. eapply H2.
  rewrite <- app_nil_end. rewrite_env ([a] ++ (F ++ E)) in OK. eapply ok_remove_head. eapply OK. 
  subst a. inversion OK.  auto.
Qed.

Lemma wf_env_strengthening2: forall E F,
  wf_env (F ++ E) ->
  wf_env E.
Proof.
  intros E F H.
  induction F; auto.
  rewrite_env ([a] ++ (F ++ E)) in H.
  apply IHF.
  inversion H; auto.
Qed.

Lemma wf_env_weakening2: forall E F G,
  wf_env (G ++ E) ->
  wf_env (F ++ E) ->
  ok (G ++ F ++ E) ->
  wf_env (G ++ F ++ E).
Proof.
  intros E F G. 
  generalize dependent F.
  induction G; intros F H1 H2 OK.
  Case "empty".
    simpl_env. auto.
  rewrite_env ([a] ++ (G ++ E)) in H1.
  rewrite_env ([a] ++ (G ++ F ++ E)).
  rewrite_env ([a] ++ (G ++ F ++ E)) in OK.
  inversion H1.
  Case "kn".
    apply wf_env_kn. apply IHG. auto. auto. eapply ok_remove_head. 
    eauto. subst. inversion OK. auto.
  Case "typ".
    eapply wf_env_typ. apply IHG; auto. eapply ok_remove_head. 
    eauto. eapply wf_typ_weakening. eapply H4.
    eapply ok_remove_head. eauto. subst. inversion OK. auto.
Qed.



(* *********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

(** The lemma [ok_from_wf_env] was already added above as a hint since it
    helps blur the distinction between [wf_env] and [ok] in proofs.

    As currently stated, the regularity lemmas are ill-suited to be
    used with [auto] and [eauto] since they end in conjunctions.  Even
    if we were, for example, to split [sub_regularity] into three
    separate lemmas, the resulting lemmas would be usable only by
    [eauto] and there is no guarantee that [eauto] would be able to
    find proofs effectively.  Thus, the hints below apply the
    regularity lemmas and [type_from_wf_typ] to discharge goals about
    local closure and well-formedness, but in such a way as to
    minimize proof search.

    The first hint introduces an [wf_env] fact into the context.  It
    works well when combined with the lemmas relating [wf_env] and
    [wf_typ].  We choose to use those lemmas explicitly via [(auto
    using ...)] tactics rather than add them as hints.  When used this
    way, the explicitness makes the proof more informative rather than
    more cluttered (with useless details).

    The other three hints try outright to solve their respective
    goals. *)

Hint Extern 1 (wf_env ?E) =>
  match goal with
  | H: typing _ _ _ |- _ => apply (proj1 (typing_regular _ _ _ H))
  end.

Hint Extern 1 (wf_typ ?E ?T) =>
  match goal with
  | H: typing E _ T |- _ => apply (proj2 (proj2 (typing_regular _ _ _ H)))
  end.

Hint Extern 1 (type ?T) =>
  let go E := apply (type_from_wf_typ E); auto in
  match goal with
  | H: typing ?E _ T |- _ => go E
  end.

Hint Extern 1 (expr ?e) =>
  match goal with
  | H: typing _ ?e _ |- _ => apply (proj1 (proj2 (typing_regular _ _ _ H)))
  | H: red ?e _ |- _ => apply (proj1 (red_regular _ _ H))
  | H: red _ ?e |- _ => apply (proj2 (red_regular _ _ H))
  end.
