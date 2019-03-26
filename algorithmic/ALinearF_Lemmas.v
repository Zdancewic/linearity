 (** Administrative lemmas for Algorithmic Lightweight Linear F

    Table of contents:
      - #<a href="##wft">Properties of wf_typ</a>#
      - #<a href="##oktwft">Properties of wf_env and wf_typ</a>#
      - #<a href="##okt">Properties of wf_env</a>#
      - #<a href="##subst">Properties of substitution</a>#
      - #<a href="##regularity">Regularity lemmas</a>#
      - #<a href="##auto">Automation</a># *)
Require Export LinearF_Lemmas.
Require Export ALinearF_Infrastructure.
Require Import Omega.

(* ********************************************************************** *)
(** * #<a name="wft"></a># Properties of [wf_typ] *)

(** If a type is well-formed in an environment, then it is locally
    closed. *)

Lemma type_from_wf_atyp : forall G T K,
  wf_atyp G T K -> type T.
Proof.
  intros G T K H; induction H; eauto.
Qed.

Lemma wf_genv_from_wf_denv : forall G D,
  wf_denv G D ->
  wf_genv G.
Proof. intros. induction H; eauto.
Qed.


Lemma ok_from_wf_genv : forall G,
  wf_genv G ->
  ok G.
Proof with simpl_env; eauto.
  intros. induction H...
Qed.

Lemma ok_from_wf_denv : forall G D,
  wf_denv G D ->
  ok D.
Proof with simpl_env; eauto.
  intros. induction H...
Qed.

Lemma ok_from_wf_atyp:  forall E T K,
  wf_atyp E T K ->
  ok E. 
Proof.
  intros E T K Hyp.
  induction Hyp; auto.
  pick fresh Y. lapply (H0 Y). intros. eapply ok_remove_head; auto. eauto.
  notin_solve.
Qed.

(**  Free Variables. *)
Lemma denv_dom_ginv : forall G D x,
  wf_denv G D ->
  x `in` dom G ->
  x `notin` dom D.
Proof with simpl_env; eauto.
  intros G D x H1 H2. generalize dependent x.  
  induction H1; intros. fsetdec. destruct (x0 == x).
   Case "x0 = x". subst...
   Case "x0 <> x". simpl. auto.
Qed.
  
Lemma denv_dom_dinv : forall G D x,
  wf_denv G D ->
  x `in` dom D ->
  x `notin` dom G.Proof with simpl_env; eauto.
  intros G D x H1 H2. generalize dependent x. induction H1; intros.
  fsetdec. destruct (x0 == x). 
  Case "x0 = x". subst...
  Case "x0 <> x". simpl in H3. assert (x0 `notin` AtomSet.F.singleton x). auto.
   apply IHwf_denv. fsetdec.
Qed.

Lemma denv_fv_ginv : forall G D x b,
  wf_denv G D ->
  binds x b G ->
  x `notin` dom D.
Proof.
  intros. eapply denv_dom_ginv. eauto. eapply binds_In. eauto.
Qed.

Lemma denv_fv_dinv : forall G D x b,
  wf_denv G D ->
  binds x b D ->
  x `notin` dom G.
Proof.
  intros. eapply denv_dom_dinv. eauto. eapply binds_In. eauto.
Qed.

(** Context Monotonicity*)

Lemma dom_dminus_var_notin : forall x D,
  x `notin` dom (D [-] x).
Proof with simpl_env; eauto.
  intros. induction D... destruct a... simpl. destruct (x == a)...
Qed.

Hint Resolve dom_dminus_var_notin.

Lemma dom_dminus_var_in : forall x D x0,
  x `in` dom D ->
  x0 <> x ->
  x `in` dom (D [-] x0).
Proof with simpl_env; eauto.
  intros. induction D.
  Case "empty". simpl in H. assert (x `notin` {})...
  Case "nonempty". 
  destruct a. simpl.  destruct (x0 == a); subst; simpl in H; try fsetdec.
    destruct (x == a); simpl;  subst;  try fsetdec.
Qed.
Hint Resolve dom_dminus_var_in.

Lemma dom_dminus_var_in_rev : forall x D x0,
  x0 <> x ->
  x `in` dom (D [-] x0) ->
  x `in` dom D.
Proof with eauto.
  intros. induction D. simpl in H0. fsetdec.
  destruct a. simpl. destruct (x == a).  subst.  fsetdec.
  simpl in H0 .  destruct (x0 ==a ). subst. apply IHD in H0. auto.
  simpl in H0. assert (x `notin` AtomSet.F.singleton a). fsetdec.
  assert (x `in` dom (D [-] x0)). fsetdec. apply IHD in H2. auto.
Qed.
 

Lemma dom_dminus_var_in2 : forall x D x0,
 x0 <> x ->
  x `notin` dom (D [-] x0) ->
  x `notin` dom D.
Proof. intros. assert (x `in` dom D -> False). intros.
 assert (x `in` dom (D [-] x0)). apply dom_dminus_var_in... auto. auto. fsetdec.
 fsetdec.
Qed.

Lemma dom_dminus_var_in_rev2 : forall x D x0,
  x `notin` dom D ->
  x0 <> x ->
  x `notin` dom (D [-] x0).
Proof. intros. assert (x `in` dom (D [-] x0) -> False). intros.
 assert (x `in` dom D ). eapply dom_dminus_var_in_rev. eauto. auto. fsetdec.
 fsetdec.
Qed.

Definition D'_leq_D := 
 fun (D' : denv) =>
  fun (D : denv) =>
   (forall x, x `in` dom D' -> x `in` dom D) .  

Notation "D' <<= D" := (D'_leq_D D' D) (at level 70, no associativity).

Lemma denv_mono : forall G D1 e T D2,
  atyping G D1 e T D2 ->
  D2 <<= D1.
Proof with simpl_env; eauto.
  intros. induction H; unfold D'_leq_D; intros;  auto. 
  Case "atyping_lvar". destruct (x0 == x).  subst. assert (x `notin` dom (D [-] x))...
   eapply dom_dminus_var_in_rev. eauto. auto. 
  Case "atyping_uabs". unfold D'_leq_D in H1. pick fresh y. apply H1 with y. auto. auto.
  Case "atyping_labs". unfold D'_leq_D in H1. pick fresh y. 
   assert (x `in` dom ([(y, dbind_typ V)] ++D)).  apply H1. auto. auto.
   simpl in H4. assert (x `notin` AtomSet.F.singleton y). auto.
    clear H0 H1 H2 H3 Fr. fsetdec.
  Case "atyping_tabs". pick fresh y. unfold D'_leq_D in H2. apply H2 with y. auto.
   auto.
Qed.

Hint Resolve denv_mono.
Lemma denv_mono2 : forall G D1 e T D2 x,
  atyping G D1 e T D2 ->
  x `in` dom D2 ->
  x `in` dom D1.
Proof with eauto.
  intros.  apply denv_mono in H. unfold D'_leq_D in H. auto.
Qed.

Hint Resolve denv_mono. 

Lemma denv_mono3 : forall G D1 e T D2 x,
  atyping G D1 e T D2 ->
  x `notin` dom D1 ->
  x `notin` dom D2.
Proof with eauto.
 intros. apply denv_mono in H. unfold D'_leq_D in H. auto.
Qed.

Corollary denv_mono_empty : forall G e T D2,
  atyping G dempty e T D2 ->
  D2 = dempty.
Proof with eauto.
  intros. apply denv_mono in H. destruct D2... 
  unfold D'_leq_D in H. destruct p. assert (a `in` dom dempty). eapply H. 
  simpl_env. fsetdec. fsetdec.
Qed.

Lemma minus_var_mono : forall D x x0,
  x0 `in` dom (D [-] x ) -> x0 `in` dom D.
Proof with simpl_env; eauto.
  intros. destruct (x0 == x). subst. 
  assert (x `notin` dom (D [-] x))... eapply dom_dminus_var_in_rev. eauto. auto. 
Qed.

Lemma minus_var_mono2 :  forall D x x0,
  x0 `notin` dom D -> x0 `notin` dom (D [-] x).
Proof with simpl_env; eauto.
  intros. destruct (x0 == x). subst. 
  assert (x `notin` dom (D [-] x))... apply dom_dminus_var_in_rev2...
Qed.

Lemma minus_mono : forall D1 D2 x,
  x `in` dom (D1 -- D2) -> x `in` dom D1.
Proof with simpl_env; eauto.
  intros. generalize dependent D1. generalize dependent x.
  induction D2; intros. simpl in H... destruct a.  simpl in H.
  apply IHD2 in H. eapply minus_var_mono. eauto.
Qed.

Lemma minus_mono2 :  forall D1 D2 x,
  x `notin` dom D1 -> x `notin` dom (D1--D2).
Proof with simpl_env; eauto.
  intros. generalize dependent D1. generalize dependent x.
  induction D2; intros. simpl in H... destruct a.  simpl.
  assert (x `notin` dom (D1 [-] a)). apply minus_var_mono2...
  apply IHD2 in H0...
Qed.

Lemma dom_dminus : forall D D' x,
  x `in` dom D' ->
  x `notin` dom (D -- D').
Proof with simpl_env; eauto.
 intros.  generalize dependent D. generalize dependent x. induction D'; intros. fsetdec. 
 destruct a. simpl. simpl_env in H. 
 assert (x `in` dom D' \/ x `notin` dom D'). fsetdec. destruct H0.
 Case "x `in` dom D'". apply IHD'...
 Case "x `notin` dom D'". assert (x `in` AtomSet.F.singleton a). fsetdec.
  assert (x = a). fsetdec. subst. apply minus_mono2...Qed.

Hint Resolve dom_dminus.
(** 
Lemma denv_mono_aux : forall G D1 e T D2 x, 
  atyping G D1 e T D2 ->
  x `in` dom D1 ->
  (x `in` fv_ee e /\ x `notin` dom D2) \/
  (x `notin` fv_ee e /\ x `in` dom D2).
Proof with simpl_env; eauto.
 intros. induction H; subst... 
 Case "atyping_uvar". destruct (x0 == x)...
  SCase "x0 = x". subst. assert (x `notin` dom D) as contra. eapply denv_fv_ginv .
   eauto. eauto. destruct contra...
  SCase "x0 <> x". right. split. simpl fv_ee... auto.
 Case "atyping_lvar". destruct (x0 == x)...
   SCase "x0 = x". subst. left. split. simpl fv_ee. fsetdec. auto.
   SCase "x0 <> x". right. split. simpl fv_ee... auto.
 Case "atyping_uabs". simpl fv_ee. pick fresh x0. 
  assert (x `in` fv_ee (open_ee e1 x0) /\ x `notin` dom D' \/ 
     x `notin` fv_ee (open_ee e1 x0) /\ x `in` dom D'). auto. destruct H4.
   SCase "left". left. destruct H4. split. assert (x0 <> x). auto.
    eapply in_open_ee_fv_ee. eauto. auto. auto.
   SCase "right". right. split. destruct H4. eapply notin_open_ee_fv_ee.
    eauto. destruct H4. auto.
  Case "atyping_labs". simpl fv_ee. pick fresh x0.
  assert (x `in` fv_ee (open_ee e1 x0) /\ x `notin` dom D' \/ 
     x `notin` fv_ee (open_ee e1 x0) /\ x `in` dom D'). apply H2. auto. simpl. auto. destruct H4.
   SCase "left". left. destruct H4. split. assert (x0 <> x). auto.
    eapply in_open_ee_fv_ee. eauto. auto. auto.
   SCase "right". right. split. destruct H4. eapply notin_open_ee_fv_ee.
    eauto. destruct H4. auto.
  Case "atyping_app". simpl fv_ee. apply IHatyping1 in H0. destruct H0.
    SCase "left". left. split. destruct H0. auto. destruct H0. eapply denv_mono3. eauto. auto.
    SCase "right". destruct H0. apply IHatyping2 in H2. destruct H2. 
      SSCase "left". left. split. fsetdec. auto.
      SSCase "right". right. split. auto. destruct H2... 
  Case "atyping_tabs". simpl fv_ee. pick fresh X.  
    assert (x `in` fv_ee (open_te e1 X) /\ x `notin` dom D' \/ 
     x `notin` fv_ee (open_te e1 X) /\ x `in` dom D'). auto. destruct H3.
     SCase "left". left.  split. destruct H3. eapply in_open_te_fv_ee. eauto. auto. auto.
     SCase "right". right. split. destruct H3. eapply notin_open_te_fv_ee. eauto. auto.
      destruct H3...
 Qed.
Hint Resolve denv_mono_aux.
*)
(** Regularity *)
Lemma denv_regular : forall G D,
  wf_denv G D ->
  wf_genv G.
Proof. intros. induction H; eauto.
Qed.

Lemma empty_minus : forall D,
  dempty -- D = dempty.
Proof with eauto.
  intros. induction D... destruct a...
Qed.

Hint Resolve empty_minus.

Lemma minus_distr : forall D1 D2 x,
 D1 ++ D2 [-] x = (D1 [-] x) ++ (D2 [-] x).
Proof with simpl_env; eauto.
  intros.  generalize dependent D2.  generalize dependent x. induction D1; intros... 
  destruct a... simpl. destruct (x == a)... rewrite IHD1...
Qed.

Lemma minus_var_regularity : forall G D x,
  wf_denv G D ->
  wf_denv G (D [-] x).
Proof with simpl_env; eauto.
  intros. generalize dependent x. generalize dependent G. induction D; intros...
  destruct a...  simpl_env in H. inversion H; subst... rewrite minus_distr... simpl. destruct (x == a); subst...
  eapply wf_denv_typ. auto. auto. auto. apply  dom_dminus_var_in_rev2. auto. auto.
Qed.

Hint Resolve minus_var_regularity .

Lemma minus_regularity : forall G D D',
  wf_denv G D ->
  (wf_denv G (D -- D')    /\
  (forall x, x `in` dom D' -> x `notin` dom (D -- D'))).
Proof with simpl_env; eauto.
  intros. generalize dependent D. generalize dependent G. induction D'; intros; split; auto.
   destruct a... simpl.  assert (wf_denv G (D [-] a))... 
   assert (wf_denv G ((D [-] a) -- D') /\ (forall x, x `in` dom D' -> x `notin` dom ((D [-] a) -- D')))...
   destruct H1...
Qed.

Lemma minus_assoc : forall D1 D2 x,
  x `notin` dom D1 ->
  D1 ++ (D2 [-] x) = ((D1 ++ D2) [-] x).
Proof with simpl_env; eauto.
  intros. generalize dependent x. generalize dependent D2. induction D1; intros; subst...
  destruct a... simpl_env in H. rewrite minus_distr . simpl. 
  destruct (x == a)... assert (x <> a). fsetdec. fsetdec. assert (D1 ++ (D2 [-] x) = (D1 ++ D2 [-] x))...
  rewrite H0...
Qed.

Lemma minus_notin : forall D x,
  x `notin` dom D ->
  D = (D [-] x).
Proof with simpl_env; eauto. 
  intros. generalize dependent x. induction D; intros; subst... destruct a. simpl_env.
  rewrite <- minus_assoc. assert ( D = (D [-] x)). simpl_env in H.  apply IHD...
  rewrite <- H0... simpl_env in H. simpl. fsetdec.
Qed.

Lemma minus_assoc2 : forall D1 D2 x,
  x `notin` dom D2 ->
  (D1[-]x)  ++ D2  = ((D1 ++ D2) [-] x).
Proof with simpl_env; eauto.
 intros. generalize dependent x. generalize dependent D1. induction D2; intros; subst...
 destruct a. simpl_env. simpl_env in H.
 assert ([(a,d)]  = ([(a,d)] [-] x)). apply minus_notin. simpl_env. fsetdec.
 assert (D2 = (D2 [-] x)). apply minus_notin. fsetdec. 
 rewrite minus_distr. rewrite minus_distr. rewrite <- H0. rewrite <- H1...
Qed.
 
(**    
Lemma kn_regular : forall G T K,
  wf_atyp G T K ->
  wf_genv G.
Proof with simpl_env; eauto.
 intros.  induction H...
Admitted.

Lemma typ_regular : forall G D1 e T D2,
  atyping G D1 e T D2 ->
  (wf_genv G  /\ wf_denv G D1 /\ wf_denv G D2 /\ exists K, wf_atyp G T K).
Proof with simpl_env; eauto.
Admitted.
*)

(** The remaining properties are analogous to the properties that we
    need to show for the subtyping and typing relations. *)

Lemma wf_atyp_weakening : forall T E F G K,
  wf_atyp (G ++ E) T K ->
  ok (G ++ F ++ E) ->
  wf_atyp (G ++ F ++ E) T K.
Proof with simpl_env; eauto.
  intros T E F G K Hwf_atyp Hk.
  remember (G ++ E) as F.
  generalize dependent G.
  induction Hwf_atyp; intros GG Hok Heq; subst...
  Case "type_all".
    pick fresh Y and apply wf_atyp_all...
    rewrite <- concat_assoc.
    assert (forall G, ok (G ++ F ++ E) -> [(Y, gbind_kn K1)] ++ GG ++ E = G ++ E ->
     wf_atyp (G ++ F ++ E) (open_tt T2 Y) K2). apply H0... apply H1.
    simpl_env. apply ok_push... auto.
Qed.

Lemma wf_atyp_weaken_head : forall T E F K,
  wf_atyp E T K ->
  ok (F ++ E) ->
  wf_atyp (F ++ E) T K.
Proof.
  intros.
  rewrite_env (gempty ++ F++ E).
  auto using wf_atyp_weakening.
Qed.

Hint Resolve wf_atyp_weaken_head .

Lemma wf_atyp_strengthening : forall E F x U T K,
 wf_atyp (F ++ [(x, gbind_typ U)] ++ E) T K ->
 wf_atyp (F ++ E) T K.
Proof with simpl_env; eauto.
  intros E F x U T K H.
  remember (F ++ [(x, gbind_typ U)] ++ E) as G.
  generalize dependent F.
  induction H; intros F Heq; subst...
  Case "wf_atyp_var".
    binds_cases H0...
  Case "wf_atyp_all".
    pick fresh Y and apply wf_atyp_all...
    rewrite <- concat_assoc.
    apply H0...
Qed.

Lemma wf_atyp_strengthening2 : forall E x U T K,
  wf_atyp ([(x, gbind_typ U)] ++ E) T K ->
 wf_atyp E T K.
Proof with simpl_env; eauto.
 intros. rewrite_env (gempty ++ E). rewrite_env (gempty ++ [(x, gbind_typ U)] ++ E) in H.
  eapply wf_atyp_strengthening. eauto.
Qed.

Lemma gbinds_weaken_at_tail : forall (x:atom) (a:gbinding) F G,
  binds x a F ->
  ok (F ++ G) ->
  binds x a (F ++ G).
Proof.
  intros x a F G H J.
  rewrite_env (F ++ G ++ nil).
  apply binds_weaken; simpl_env; trivial.
Qed.

Lemma wf_atyp_subst_tgb : forall F Q E Z P T K,
  wf_atyp (F ++ [(Z, gbind_kn Q)] ++ E) T K ->
  wf_atyp E P Q->
  wf_atyp (map (subst_tgb Z P) F ++ E) (subst_tt Z P T) K.
Proof with simpl_env; eauto using wf_atyp_weaken_head, type_from_wf_atyp.
  intros F Q E Z P T K WT WP.
  remember (F ++ [(Z, gbind_kn Q)] ++ E) as G.
  generalize dependent F.
  induction WT; intros F EQ; subst; simpl subst_tt...
  Case "wf_atyp_var".
    destruct (X == Z).  subst...
      binds_get H0.
      inversion H2. subst...
      binds_cases H0...
      apply wf_atyp_var. assert ((subst_tgb Z P (gbind_kn K)) = (gbind_kn K)).
      simpl. auto. apply ok_map_app_l. 
      eapply ok_remove_mid. eapply H.
      apply gbinds_weaken_at_tail.
      assert (gbind_kn K = (subst_tgb Z P (gbind_kn K))).
      simpl; auto. rewrite H0.
      apply binds_map. auto. apply ok_map_app_l.
      apply (@ok_remove_mid gbinding [(Z, gbind_kn Q)]). auto.
  Case "wf_atyp_all".
    pick fresh Y and apply wf_atyp_all...
    rewrite subst_tt_open_tt_var...
    rewrite_env (map (subst_tgb Z P) ([(Y, gbind_kn K1)] ++ F) ++ E).
    apply H0...
Qed.

(* ********************************************************************** *)
(** * #<a name="oktwft"></a># Properties of [wf_env] and [wf_typ] *)

(* ********************************************************************** *)
(** * #<a name="okt"></a># Properties of [wf_env] *)

(** These properties are analogous to the properties that we need to
    show for the subtyping and typing relations. *)

Lemma wf_genv_strengthening : forall x T E F,
  wf_genv (F ++ [(x, gbind_typ T)] ++ E) ->
  wf_genv (F ++ E).
Proof with eauto using wf_atyp_strengthening.
  induction F; intros Wf_env; inversion Wf_env; subst; simpl_env in *...
Qed.

Lemma wf_genv_subst_tgb : forall K Z P E F,
  wf_genv (F ++ [(Z, gbind_kn K)] ++ E) ->
  wf_atyp E P K ->
  wf_genv (map (subst_tgb Z P) F ++ E).
Proof with eauto 6 using wf_atyp_subst_tgb.
  induction F; intros Wf_env WP; simpl_env;
    inversion Wf_env; simpl_env in *; simpl subst_tgb...
Qed.

Lemma wf_denv_subst_tdb : forall G1 Z K G2 D K' T,
 wf_denv (G2 ++ [(Z, gbind_kn K)] ++ G1) D ->
 wf_atyp G1 T K' ->
 kn_order K' K ->
 wf_denv (map (subst_tgb Z T) G2 ++ G1) (map (subst_tdb Z T) D).
Proof with eauto 6 using wf_atyp_subst_tgb.
Admitted.

Lemma wf_atyp_from_gbinds_typ : forall x U E,
  wf_genv E ->
  binds x (gbind_typ U) E ->
  exists K, wf_atyp E U K.
Proof with auto using wf_atyp_weaken_head. intros. generalize dependent x. generalize dependent U.
  induction H; intros U xx J; binds_cases J...
  assert (exists K, wf_atyp G U K).
  eapply IHwf_genv. eauto. inversion H2. exists x. eapply wf_atyp_weaken_head . 
  auto. apply ok_push... apply ok_from_wf_genv ...
  assert (exists K, wf_atyp G U K).
  eapply IHwf_genv. eauto. inversion H3. exists x0. eapply wf_atyp_weaken_head...
  apply ok_push... apply ok_from_wf_genv...
  inversion H4; subst... exists kn_nonlin... eapply wf_atyp_weaken_head...
  apply ok_push... apply ok_from_wf_genv...
Qed.

Lemma wf_atyp_from_wf_genv_typ : forall x T G,
  wf_genv ([(x, gbind_typ T)] ++ G) ->
  wf_atyp G T kn_nonlin.
Proof.
  intros x T G H. inversion H; auto.
Qed.

Lemma wf_atyp_from_dbinds_typ : forall x U G E,
  wf_denv G E ->
  binds x (dbind_typ U) E ->
  wf_atyp G U kn_lin.
Proof with simpl_env; eauto.
  intros. generalize dependent x. generalize dependent U.
  induction H; intros U xx J; binds_cases J... inversion H5; subst...
Qed.

Lemma atyping_fv_inv : forall G D1 e T D2 x,
  atyping G D1 e T D2 ->
  x `notin` dom G ->
  x `notin` dom D1 ->
  x  `notin` fv_ee e /\ x `notin` fv_te e /\ x `notin` fv_tt T /\ x `notin` dom D2.
Proof with simpl_env; eauto.
 intros. induction H; simpl fv_ee; simpl fv_te; simpl fv_tt; subst.
 Case "atyping_uvar". split. destruct (x == x0). eauto. subst. apply binds_In in H. fsetdec.
    fsetdec. split. 
Admitted.
 

Lemma wf_atyp_fv_inv : forall G T K x,
  wf_atyp G T K ->
  x `notin` dom G ->
  x `notin` fv_tt T.
Proof with simpl_env; eauto.
Admitted.


(* ********************************************************************** *)
(** * #<a name="subst"></a># Environment is unchanged by substitution for a fresh name *)

Lemma notin_fv_awf : forall G (X : atom) T K,
  wf_atyp G T K ->
  X `notin` dom G ->
  X `notin` fv_tt T.
Proof with auto.
  intros G X T K Wf_atyp.
  induction Wf_atyp; intros Fr; simpl...
  Case "wf_atyp_var".
    assert (X0 `in` (dom G))...
    eapply binds_In; eauto.
  Case "wf_atyp_all".
    pick fresh Y.
    apply (notin_fv_tt_open Y)...
Qed.

Lemma map_subst_tb_id : forall G Z P,
  wf_genv G ->
  Z `notin` dom G ->
  G = map (subst_tgb Z P) G.
Proof with auto.
  intros G Z P H.
  induction H; simpl; intros Fr; simpl_env...
  rewrite <- IHwf_genv...
  rewrite <- IHwf_genv...
    rewrite <- subst_tt_fresh... eapply notin_fv_awf; eauto.
Qed.

Lemma wf_genv_weakening: forall E F,
  wf_genv E ->
  wf_genv F ->
  ok (F ++ E) ->
  wf_genv (F ++ E).
Proof.
  intros E F.
  generalize dependent E.
  induction F; intros E WF1 WF2 OK.
  simpl. auto.
  inversion WF2. 
  rewrite_env ([(X, gbind_kn K)] ++ F ++ E).
  eapply wf_genv_kn. apply IHF; auto. rewrite_env ([a] ++ (F ++ E)) in OK. eapply ok_remove_head. eapply OK. subst a.
  inversion OK.  auto.
  rewrite_env ([(x, gbind_typ T)] ++ F ++ E).
  eapply wf_genv_typ. apply IHF; auto. rewrite_env ([a] ++ (F ++ E)) in OK. eapply ok_remove_head. eapply OK. 
  rewrite_env (F ++ E ++ gempty). apply wf_atyp_weakening. rewrite <- app_nil_end. eapply H2.
  rewrite <- app_nil_end. rewrite_env ([a] ++ (F ++ E)) in OK. eapply ok_remove_head. eapply OK. 
  subst a. inversion OK.  auto.
Qed.

Lemma wf_genv_strengthening2: forall E F,
  wf_genv (F ++ E) ->
  wf_genv E.
Proof.
  intros E F H.
  induction F; auto.
  rewrite_env ([a] ++ (F ++ E)) in H.
  apply IHF.
  inversion H; auto.
Qed.

Lemma wf_genv_weakening2: forall E F G,
  wf_genv (G ++ E) ->
  wf_genv (F ++ E) ->
  ok (G ++ F ++ E) ->
  wf_genv (G ++ F ++ E).
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
    apply wf_genv_kn. apply IHG. auto. auto. eapply ok_remove_head. eauto. subst. inversion OK. auto.
  Case "typ".
    eapply wf_genv_typ. apply IHG; auto. eapply ok_remove_head. eauto. eapply wf_atyp_weakening. eapply H4.
    eapply ok_remove_head. eauto. subst. inversion OK. auto.
Qed.

Lemma wf_denv_nonlin_strengthening : forall x T E F D,
  wf_denv (F ++ [(x, gbind_typ T)] ++ E) D ->
  wf_denv (F ++ E) D.Proof with simpl_env; eauto.
  intros x T E F D H. remember (F ++ [(x, gbind_typ T)] ++E) as G. 
  generalize dependent x.  induction H; intros xx EQ; subst; simpl_env in * ...
  apply wf_denv_empty. eapply wf_genv_strengthening. eauto.
  apply wf_denv_typ. apply (IHwf_denv xx)... eapply wf_atyp_strengthening. eauto.
  simpl_env. fsetdec. auto.
Qed.

 Lemma wf_denv_nonlin_strengthening2 : forall x T E D,
  wf_denv ([(x, gbind_typ T)] ++ E) D ->
  wf_denv E D.
Proof with eauto.
  intros. rewrite_env (gempty ++ E). rewrite_env (gempty ++ [(x, gbind_typ T)]  ++ E) in H.
  eapply wf_denv_nonlin_strengthening. eauto.
Qed.

Lemma wf_atyp_kn_strengthening : forall X K E F T K0,
  wf_atyp (F ++ [(X, gbind_kn K)] ++ E) T K0->
  X `notin` genv_fv_tt F ->
  X `notin` fv_tt T ->
  wf_atyp (F ++ E) T K0.
Proof with simpl_env; eauto.
  intros X K E F T K0 Wft H1 H2. remember (F ++ [(X, gbind_kn K)] ++E) as G. 
  generalize dependent X.  generalize dependent F. generalize dependent E. generalize dependent K.
  induction Wft; intros KK E F XX Q1 Q2 EQ; subst; simpl_env in * .
  destruct (X == XX); subst; simpl in *... fsetdec.
  eapply wf_atyp_arrow. eapply IHWft1. apply Q1. simpl in *. fsetdec. eauto. eapply IHWft2. eauto. simpl in Q2. fsetdec. eauto.
  eapply wf_atyp_all with L. auto.  intros. rewrite <- concat_assoc. pick fresh Y. eapply (H0 X H1). simpl. eauto. simpl in *. 
  apply notin_fv_tt_open_tt. auto. assert (wf_atyp ((X, gbind_kn K1) :: F ++ (XX, gbind_kn KK) :: E) (open_tt T2 X) K2).
  apply H... simpl_env in H1. apply ok_from_wf_atyp in H2. inversion H2; subst. simpl_env in H7. notin_solve. 
  rewrite concat_assoc. eauto.
Qed.
  

Lemma wf_atyp_kn_strengthening2 : forall X K E T K0,
  wf_atyp ([(X, gbind_kn K)] ++ E) T K0->
  X `notin` fv_tt T ->
  wf_atyp E T K0.
Proof with eauto.
  intros. rewrite_env (gempty ++ E). rewrite_env (gempty ++ [(X, gbind_kn K)]  ++ E) in H.
  eapply wf_atyp_kn_strengthening. eauto. auto. auto.
Qed.

Lemma wf_genv_kn_strengthening : forall X K E F,
 wf_genv (F ++ [(X, gbind_kn K)] ++ E) ->
 X `notin` genv_fv_tt F ->
 wf_genv (F ++ E).
Proof with simpl_env; eauto.
 intros X K E F H. remember (F ++ [(X, gbind_kn K)] ++E) as G. 
  generalize dependent X.  generalize dependent F. generalize dependent E. generalize dependent K.
  induction H; intros KK E F XX EQ Q1; subst; simpl_env in * ...
  destruct F; simpl_env in *... inversion EQ. inversion EQ.
  destruct F; simpl_env in *... destruct (X == XX);  subst... inversion EQ; subst... inversion EQ; subst. fsetdec.
  destruct p. simpl_env in *. inversion EQ; subst... assert (wf_genv (F ++ E)). eapply IHwf_genv. simpl_env...
   simpl in Q1... apply wf_genv_kn. auto. simpl_env in *. fsetdec.
  destruct F; simpl_env in *... destruct (x == XX); subst... inversion EQ; subst... inversion EQ; subst...
   destruct p. simpl_env in *. inversion EQ; subst... assert (wf_genv (F ++E)). eapply IHwf_genv. simpl_env...
   simpl in Q1. fsetdec. apply wf_genv_typ. auto. simpl_env in *. eapply wf_atyp_kn_strengthening. eauto.
   simpl in Q1. fsetdec. simpl in Q1. fsetdec. simpl_env in *. fsetdec.
Qed.

Lemma wf_denv_kn_strengthening : forall X K E F D,
 wf_denv (F ++ [(X, gbind_kn K)] ++ E) D ->
 X `notin` denv_fv_tt D ->
 X `notin` genv_fv_tt F ->
 wf_denv (F ++ E) D.
Proof with simpl_env; eauto.
   intros X K E F D H. remember (F ++ [(X, gbind_kn K)] ++E) as G. 
  generalize dependent X.  induction H; intros XX EQ Q1 Q2; subst; simpl_env in * ...
  apply wf_denv_empty. eapply wf_genv_kn_strengthening. eauto. auto.
  assert (wf_denv (F ++ E) D). eapply IHwf_denv. eauto. simpl in Q1. fsetdec. auto.
  apply wf_denv_typ... eapply wf_atyp_kn_strengthening. eauto. auto. simpl in Q1. fsetdec.
Qed.

Lemma wf_denv_kn_strengthening2 : forall X K E D,
 wf_denv ([(X, gbind_kn K)] ++ E) D ->
 X `notin` denv_fv_tt D ->
 wf_denv  E D.
Proof with simpl_env; eauto.
   intros. rewrite_env (gempty ++ E). rewrite_env (gempty ++ [(X, gbind_kn K)] ++ E) in H.
  eapply wf_denv_kn_strengthening. eauto. auto. auto.
Qed.

(**  
Lemma wf_denv_weakening : forall E F G D,
  wf_denv (F ++ E) D ->
  wf_genv (F ++ G ++ E) ->
  wf_denv (F ++ G ++ E) D.
Proof with simpl_env; eauto.
  intros E F G D Wfd Wfg. generalize dependent G.
  induction Wfd; intros; simpl_env in *...
  destruct a. simpl_env in *.
  assert (wf_denv (F ++ E) D). inversion Wfd... apply IHD in H.
  destruct d... apply wf_denv_typ. auto.
  assert (wf_atyp (F ++ E) t kn_lin). eapply wf_atyp_from_dbinds_typ. eauto.
  assert (binds a (dbind_typ t) ([(a, dbind_typ t)] ++ D))... apply wf_atyp_weakening...
  apply ok_from_wf_genv...  

Lemma wf_denv_weakening2 : forall E G D,
  wf_denv  E D ->
  wf_genv (G ++ E) ->
  wf_denv (G ++ E) D.
Proof.
  intros. rewrite_env (gempty ++ G ++ E). rewrite_env (gempty ++ G ++ E) in H0.
  apply wf_denv_weakening. auto. auto.
Qed.
*)
Lemma wf_denv_lin_strengthening : forall x T G E F,
  wf_denv G (F ++ [(x, dbind_typ T)] ++ E) ->
  wf_denv G (F ++ E).Proof with simpl_env; eauto.
  induction F; intros; simpl_env in *... inversion H...
  destruct a. simpl_env in *. assert (wf_denv G (F ++ [(x, dbind_typ T)] ++ E)).
  inversion H... apply IHF in H0. destruct d... apply wf_denv_typ. auto.
  eapply wf_atyp_from_dbinds_typ. apply H. 
  assert (binds a (dbind_typ t) ([(a, dbind_typ t)] ++ F ++ [(x, dbind_typ T)] ++ E))...
  assert (a `in` dom ([(a, dbind_typ t)] ++ F ++ [(x, dbind_typ T)] ++ E)). simpl_env. fsetdec.
  eapply denv_dom_dinv. apply H. auto. simpl_env.
  assert (a `notin` dom (F ++ [(x, dbind_typ T)] ++ E)). inversion H. auto. simpl_env in H1. fsetdec.
Qed.

Lemma wf_denv_lin_strengthening2 : forall G E D F,
  wf_denv G (F ++ D ++ E) ->
  wf_denv G (F ++ E).
Proof with simpl_env; eauto.
  induction D; intros; simpl_env in *... destruct a... destruct d. simpl_env in H.
  apply wf_denv_lin_strengthening in H. apply IHD...
Qed.

Lemma wf_denv_lin_strengthening3 : forall G E D,
  wf_denv G (D ++ E) ->
  wf_denv G E.
Proof with simpl_env; eauto.
  intros. rewrite_env (dempty ++ E). rewrite_env (dempty ++ D ++ E) in H.
  eapply wf_denv_lin_strengthening2. eauto.
Qed.

Lemma wf_denv_fv_disj : forall G D1 D2 x,
  wf_denv G (D1 ++ D2) ->
  x `in` dom D2 ->
  x `notin` dom D1.
Proof with eauto; simpl_env.
   intros. generalize dependent x. generalize dependent D2. induction D1; intros; subst.
   fsetdec. destruct a. simpl_env in H. simpl. assert (wf_denv G (D1 ++ D2)).
  eapply wf_denv_lin_strengthening3. eauto.  assert (x `notin` dom D1).
  eapply IHD1. eauto. auto. assert (wf_denv G ([(a, d)] ++ D2)).
  eapply wf_denv_lin_strengthening2.  eauto. assert ( x `notin` AtomSet.F.singleton a).
  destruct (x == a). subst. inversion H3; subst. fsetdec. fsetdec. fsetdec.
Qed.

Lemma wf_denv_fv_disj2 : forall G D1 D2 x,
  wf_denv G (D1 ++ D2) ->
  x `in` dom D1 ->
  x `notin` dom D2.
Proof with eauto; simpl_env.
   intros. generalize dependent x. generalize dependent D2. induction D1; intros; subst.
   fsetdec. destruct a. simpl_env in H. assert (wf_denv G (D1 ++ D2)).
  eapply wf_denv_lin_strengthening3. eauto. simpl in H0. destruct (x == a). subst.
  assert (wf_denv G ([(a, d)] ++ D2)).
  eapply wf_denv_lin_strengthening2.  eauto. inversion H2; subst...
  assert (x `in` dom D1). fsetdec.
  eapply IHD1. eauto. auto.
Qed.

Lemma wf_denv_fv_disj3 : forall G D1 D2 D x,
  wf_denv G (D1 ++D ++ D2) ->
  x `in` dom D ->
  x `notin` dom D2 /\ x `notin` dom D1.
Proof with eauto; simpl_env.
  intros. assert (x `in` dom (D1 ++ D)). simpl_env. fsetdec.
  assert (x `in` dom (D ++ D2)). simpl_env. fsetdec. 
  split. eapply wf_denv_fv_disj2.  rewrite_env ((D1 ++ D) ++ D2) in H. eauto.
  auto.  eapply wf_denv_fv_disj. eauto. auto.
Qed.


(* ********************************************************************** *)
(** * #<a name="regularity"></a># Regularity of relations *)


Lemma wf_atyp_open : forall E U M T K1 K2 K1',
  wf_genv E ->
  wf_atyp E M K2 ->
  (M = (typ_all K1 T)) ->
  wf_atyp E U K1' ->
  kn_order K1' K1 ->
  wf_atyp E (open_tt T U) K2.
Proof with simpl_env; eauto.
  intros E U M T K1 K2 K1' Ok WA.
  intros H.  rewrite H in WA. inversion WA; subst; intros...
  pick fresh Y.
  rewrite (subst_tt_intro Y)...
  rewrite_env (map (subst_tgb Y U) gempty ++ E).
  apply wf_atyp_subst_tgb with K1'...
Admitted.
(*
Lemma subst_tt_same : forall Z T,
  subst_tt Z Z T = T.
Proof with eauto.
  intros. induction T; simpl subst_tt... destruct (a == Z)... rewrite e...
  rewrite IHT1. rewrite IHT2... rewrite IHT...
Qed.
Lemma wf_atyp_subst : forall E Z U T K1 K2,
  wf_atyp E U K1->
  binds Z (gbind_kn K1) E ->
  wf_atyp E T K2->
  wf_atyp E (subst_tt Z U T) K2.
Proof with eauto using type_from_wf_atyp, wf_atyp_weaken_head.
  intros. generalize dependent K2. generalize dependent Z. generalize dependent T.
  induction H; intros; simpl subst_tt...
  Case "wf_atyp_var".
    destruct (X == Z)... subst.  rewrite subst_tt_same...
  Case "wf_atyp_arrow". eapply wf_atyp_arrow. apply IHwf_atyp1. auto.
  Case "wf_atyp_all".
    pick fresh Y and apply wf_typ_all.
    rewrite subst_tt_open_tt_var...
Qed.

Lemma wf_typ_rename : forall (X Y : atom) E T K1 K2,
  X `notin` (fv_tt T `union` dom E) ->
  Y `notin` (fv_tt T `union` dom E) ->
  wf_atyp ([(X, gbind_kn K1)] ++ E) (open_tt T X) K2->
  wf_atyp ([(Y, gbind_kn K1)] ++ E) (open_tt T Y) K2.
Proof with auto.
  intros.
  destruct (X == Y); subst...
  rewrite (@subst_tt_intro X)...
  eapply (@wf_atyp_kn_strengthening2 X).
  apply wf_typ_subst...
  apply wf_typ_weaken_head...
  apply notin_fv_tt_subst_tt_var. simpl...
Qed.
****************************************)


Lemma atyping_regular : forall G D e T D',
  atyping G D e T D' ->
  wf_genv G /\ wf_denv G D /\ wf_denv G D' /\ expr e /\ exists K, wf_atyp G T K.
Proof with simpl_env; auto*.
  intros G D e T D' H; induction H...
  Case "atyping_uvar".
    assert (wf_genv G). eapply wf_genv_from_wf_denv. eauto.
    repeat split...  eapply wf_atyp_from_gbinds_typ... eauto.  
  Case "atyping_lvar".   assert (wf_genv G). eapply wf_genv_from_wf_denv. eauto.
   repeat split... exists (kn_lin). eapply wf_atyp_from_dbinds_typ. eauto. eauto.
  Case "atyping_uabs".
    pick fresh y.
    assert (wf_genv ([(y, gbind_typ V)] ++ G) /\ 
      wf_denv ([(y, gbind_typ V)] ++ G)  D /\ 
      wf_denv ([(y, gbind_typ V)] ++ G)  D' /\ 
      expr (open_ee e1 y) /\ exists K, wf_atyp ([(y, gbind_typ V)] ++ G)  T1 K) as HE. apply H1...
    destruct HE  as [E1 [E2 [E3 [ E4 E5]]]]...
    repeat split... inversion E1...  eapply wf_denv_nonlin_strengthening2. eauto.
    eapply wf_denv_nonlin_strengthening2. eauto. apply expr_abs with L. 
    eapply type_from_wf_atyp. eauto. intros. lapply (H1 x). intros. destruct H4 as [A1 [A2 [A3 [A4 A5]]]]... auto.
    destruct E5 as [KK Wft]. apply wf_atyp_strengthening2 in Wft. exists K. eapply wf_atyp_arrow. eauto. eauto.
  Case "atyping_labs". 
    pick fresh y.
    assert (wf_genv G /\ 
      wf_denv G ([(y, dbind_typ V)] ++ D) /\ 
      wf_denv G  D' /\ 
      expr (open_ee e1 y) /\ exists K, wf_atyp G  T1 K) as HE. apply H1...
      destruct HE  as [E1 [E2 [E3 [ E4 E5]]]]...
    repeat split... inversion E2... apply expr_abs with L. eapply type_from_wf_atyp. eauto. 
    intros. lapply (H1 x). intros. destruct H4 as [A1 [A2 [A3 [A4 A5]]]]... auto.
    destruct E5 as [KK Wft]. exists K. eapply wf_atyp_arrow. eauto. eauto.
  Case "atyping_app". 
    destruct IHatyping1  as [IH1 [IH2 [IH3 [IH4 IH5]]]]... destruct IHatyping2  as [IH1' [IH2' [IH3' [IH4' IH5']]]]...
    repeat split... destruct IH5 as [K0 Wf]. inversion Wf; subst... exists K2...
  Case "atyping_tabs".
    pick fresh Y.
     assert (wf_genv ([(Y, gbind_kn K)] ++ G) /\ 
      wf_denv ([(Y, gbind_kn K)] ++ G)  D /\ 
      wf_denv ([(Y, gbind_kn K)] ++ G)  D' /\ 
      expr (open_te e1 Y) /\ exists K0, wf_atyp ([(Y, gbind_kn K)] ++ G)  (open_tt T1 Y) K0) as HE. apply H2...
      destruct HE  as [E1 [E2 [E3 [ E4 E5]]]]... repeat split... inversion E1... eapply wf_denv_kn_strengthening2 . eauto.
      notin_solve. eapply wf_denv_kn_strengthening2 . eauto.  notin_solve. 
      apply expr_tabs with L. intros. lapply (H2 X). intros. destruct H4 as [A1 [A2 [A3 [A4 A5]]]]... auto.
      exists K'. apply wf_atyp_all with L. intros. apply H0... 
  Case "atyping_tapp". 
    destruct IHatyping as [IH1 [IH2 [IH3 [IH4 IH5]]]]... repeat split...
    apply expr_tapp... eapply type_from_wf_atyp. eauto. destruct IH5 as [K0 Wf]. inversion Wf; subst...
    inversion H1; subst... exists K0.
Admitted.
     
(** 
    rewrite_env (empty ++ E). 
    eapply wf_env_strengthening. simpl_env. eapply H3.
    pick fresh x and apply expr_abs.
    eapply type_from_wf_typ. eauto.
    lapply (H2 x). auto... fsetdec.
    inversion H3. subst. inversion H4. 
    destruct K.
    eapply wf_typ_arrow. eauto.
    rewrite_env (empty ++ E).
    eapply wf_typ_strengthening; simpl_env; eauto.
    eapply wf_typ_sub.
    eapply wf_typ_arrow. eauto.
    rewrite_env (empty ++ E).
    eapply wf_typ_strengthening; simpl_env; eauto.
  Case "typing_app".
    destruct IHtyping1 as [WF1 [EX1 J1]]...
    destruct IHtyping2 as [WF2 [EX2 J2]]...
    repeat split...
    apply (wf_env_split E1 E2 E3)...
    destruct K.
    inversion J1; subst; auto.
    destruct K2.
      eapply (wf_typ_split1 E1 E2 E3).
      apply (split_ok E1 E2 E3); auto. auto. auto.
      apply wf_typ_sub.
      eapply (wf_typ_split1 E1 E2 E3).
      apply (split_ok E1 E2 E3); auto. auto. auto.
    inversion H2.
    inversion J1; subst; auto.
    inversion H2; subst; auto.
    destruct K2.
      eapply (wf_typ_split1 E1 E2 E3).
      apply (split_ok E1 E2 E3); auto. auto. auto.
      apply wf_typ_sub.
      eapply (wf_typ_split1 E1 E2 E3).
      apply (split_ok E1 E2 E3); auto. auto. auto.
  Case "typing_tabs".
    pick fresh Y.
    destruct (H1 Y) as [HWF [EX WT]]...
    inversion HWF; subst.
    repeat split...
    pick fresh X and apply expr_tabs.
    destruct (H1 X) as [A [B C]]...
    pick fresh X and apply wf_typ_all.
    destruct (H1 X) as [A [B C]]...
  Case "type_tapp".
    repeat split...
    apply (expr_tapp).
    tauto. eapply type_from_wf_typ. eapply H0.
    destruct IHtyping as [_ [_ WF]].
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
*)



Corollary denv_mono_app : forall G D1 e1 e2 T D2 x,
  atyping G D1 (exp_app e1 e2) T D2  ->
  x `in` dom D1 ->
  (x `in` fv_ee e1 /\ x `notin` fv_ee e2 /\ x `notin` dom D2) \/
  (x `notin` fv_ee e1 /\ x `in` fv_ee e2 /\ x `notin` dom D2) \/
  (x `notin` fv_ee e1 /\ x `notin` fv_ee e2 /\ x `in` dom D2).
Proof with simpl_env; eauto.
  intros. inversion H; subst. 
  assert ( (x `in` fv_ee e1 /\ x `notin` dom D3) \/
  (x `notin` fv_ee e1 /\ x `in` dom D3))...
  assert ((x `in` fv_ee (exp_app e1 e2) /\ x `notin` dom D2) \/
  (x `notin` fv_ee (exp_app e1 e2) /\ x `in` dom D2)). eapply denv_mono_aux.
  eauto. auto.  destruct H1.
  Case "left". left. split. destruct H1. auto. 
  destruct H2. 
   SCase "left". split. destruct H1. destruct H2. apply atyping_regular in H5. destruct H5 as [E1 [E2 [E3 [E4 E5]]]].
    assert (x `notin` dom G). eapply denv_dom_dinv. apply E2. auto. 
    assert  (x  `notin` fv_ee e2 /\ x `notin` fv_te e2 /\ x `notin` fv_tt T1 /\ x `notin` dom D2). eapply atyping_fv_inv.
    eauto. auto. auto. auto. auto.
   SCase "right". destruct H2. destruct H1. assert (x `notin` dom D2).  eapply denv_mono3. eauto. auto. fsetdec.
  Case "right". right. destruct H2. 
    SCase "left". left. destruct H1. split. auto. split. simpl fv_ee in H2. destruct H2. fsetdec. destruct H2. auto.
    SCase "right". right. destruct H1. split. auto. split. simpl fv_ee in H2. destruct H2. auto. destruct H2...Qed.

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

Hint Extern 1 (wf_genv ?E) =>
  match goal with
  | H: atyping _ _ _ _ _ |- _ => apply (proj1 (atyping_regular _ _ _ _ _ H))
  end.

Hint Extern 1 (wf_atyp ?G ?T) =>
  match goal with
  | H: atyping G _ _ T _ |- _ => apply (proj2 (proj2 (atyping_regular _ _ _ _ _ H)))
  end.

Hint Extern 1 (type ?T) =>
let go E := apply (type_from_wf_atyp E); auto in
  match goal with
  | H: atyping ?E _ _ T _ |- _ => go E
  end.

Hint Extern 1 (expr ?e) =>
  match goal with
  | H: atyping _ _ ?e _ _ |- _ => apply (proj1 (proj2 (atyping_regular _ _ _ _ _ H)))
  | H: red ?e _ |- _ => apply (proj1 (red_regular _ _ _ _ H))
  | H: red _ ?e |- _ => apply (proj2 (red_regular _ _ _ _ H))
  end.



