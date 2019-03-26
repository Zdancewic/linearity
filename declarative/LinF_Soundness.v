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

Require Export LinF_Lemmas.
Require Import Omega.
Require Import Tactics.


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
    apply H0. simpl. fsetdec. 
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


Lemma empty_noteq_concat: forall E X G,
 empty = E ++ [X] ++ G -> False.
Proof.
  induction E; intros.
  simpl. unfold not; intros. inversion H.
  simpl. unfold not; intros. inversion H.
Qed.

   

Lemma wf_env_from_typing: forall E D e T,
  typing E D e T ->
  wf_env E.
Proof.
  intros.
  lapply (typing_regular E D e T); intros; tauto.
Qed.

Lemma wf_lenv_from_typing: forall E D e T,
  typing E D e T ->
  wf_lenv E D.
Proof.
  intros.
  lapply (typing_regular E D e T); intros; tauto.
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

Lemma wf_env_from_wf_lenv: forall E D,
  wf_lenv E D ->
  wf_env E.
Proof.
  intros E D WFL.
  induction WFL; auto.
Qed.  

Lemma wf_lenv_split1: forall G D1 D2 D3,
  lenv_split G D1 D2 D3 ->
  wf_lenv G D1.
Proof.
  intros G D1 D2 D3 S.
  induction S; auto.
  apply wf_lenv_typ. auto. auto. 
  rewrite (dom_lenv_split E D1 D2 D3) in H0. fsetdec.
  auto. auto.
Qed.

Lemma wf_lenv_split2: forall G D1 D2 D3,
  lenv_split G D1 D2 D3 ->
  wf_lenv G D2.
Proof.
  intros. eapply wf_lenv_split1. eapply lenv_split_commute. apply H.
Qed.

Definition disjoint (F:env) (D:lenv) :=
  (forall x, x `in` dom F -> x `notin` dom D) /\
  (forall x, x `in` dom D -> x `notin` dom F).

Lemma disjoint_strengthening1: forall G F D,
  ok (G ++ F) ->
  ok D ->
  disjoint (G ++ F) D ->
  disjoint F D.
Proof.
  intros.
  unfold disjoint in H1. destruct H1 as [NIN1 NIN2].
  unfold disjoint.
  split; intros.
  apply NIN1. rewrite dom_concat. fsetdec.
  lapply (NIN2 x); intros. rewrite dom_concat in H2. fsetdec.  auto.
Qed.

Lemma disjoint_strengthening2: forall G D1 D2,
  disjoint G (D1 ++ D2) ->
  disjoint G D2.
Proof.
  intros.
  destruct H.
  unfold disjoint.
  rewrite dom_concat in *.
  split; intros.
  lapply (H x); intros. fsetdec. auto.
  apply (H0 x); auto. 
Qed.

Lemma disjoint_commute1: forall G F D,
  disjoint (G ++ F) D ->
  disjoint (F ++ G) D.
Proof.
  intros.
  destruct H. 
  unfold disjoint.
  split; intros.
  rewrite dom_concat in *.
  eapply H. fsetdec.
  rewrite dom_concat in *.
  lapply (H0 x); intros; fsetdec.
Qed.

Lemma disjoint_strengthening3: forall E F G D,
  disjoint (E ++ F ++ G) D ->
  disjoint (E ++ G) D.
Proof.
  intros.
  destruct H.
  unfold disjoint. 
  repeat rewrite dom_concat in *.
  split; intros.
  apply H. fsetdec.
  lapply (H0 x); intros. fsetdec. auto.
Qed.
  
Lemma wf_lenv_disjoint: forall G D,
  wf_lenv G D ->
  disjoint G D.
Proof.
  induction D; intros.
  unfold disjoint. 
  split; intros. simpl. fsetdec. simpl in H0. fsetdec.
  destruct a. unfold disjoint. simpl.
  split; intros. unfold disjoint in IHD.
  inversion H. subst. 
  lapply IHD; intros. destruct H1.
  lapply (H1 x); intros; auto. auto.
  destruct (x == a). subst.
    inversion H. auto.
  assert (x `in` dom D).
  fsetdec.
  inversion H; subst.
  unfold disjoint in IHD.
  lapply IHD; intros. destruct H2.
  lapply (H3 x); intros; auto.  auto.
Qed.

Lemma wf_lenv_ok1: forall G D,
  wf_lenv G D ->
  ok D.
Proof.
  induction D; auto.
  intros. destruct a. apply ok_cons.
  inversion H. apply IHD; auto.
  inversion H; auto.
Qed.

Lemma disjoint_inversion1: forall G D x,
  disjoint G D ->
  x `in` dom D ->
  x `notin` dom G.
Proof.
  intros. unfold disjoint in H. destruct H.
  apply H1; auto.
Qed.

Lemma wf_lenv_weakening: forall E F G D,
  wf_lenv (G ++ E) D ->
  wf_env (G ++ F ++ E) ->
  disjoint F D ->
  wf_lenv (G ++ F ++ E) D.
Proof.
  intros E F G D WFL.
  remember (G ++ E) as G0.
  generalize dependent G. 
  induction WFL; intros G EQ WFE NIN; subst; simpl_env in *; auto.
  apply wf_lenv_typ.
  apply IHWFL; auto.
  intros. auto.
  apply (disjoint_strengthening2 F [(x, lbind_typ T)]).  auto.
  repeat rewrite dom_concat.
  assert (x `notin` dom F).  eapply disjoint_inversion1. apply NIN.
  simpl. fsetdec. fsetdec. auto.
  eapply wf_typ_weakening. auto. apply ok_from_wf_env. apply WFE.
Qed.

Lemma disjoint_split1: forall G D1 D2 D3,
  lenv_split G D1 D2 D3 ->
  disjoint G D1.
Proof.
  intros.
  apply wf_lenv_disjoint.
  eapply wf_lenv_split1; eauto.
Qed.

Lemma disjoint_split2: forall G D1 D2 D3,
  lenv_split G D1 D2 D3 ->
  disjoint G D2.
Proof.
  intros.
  apply wf_lenv_disjoint.
  eapply wf_lenv_split2; eauto.
Qed.

Lemma ok_from_lenv_split0: forall G D1 D2 D3,
  lenv_split G D1 D2 D3 ->
  ok D3.
Proof.
  intros.
  induction H; auto.
Qed.

Lemma lenv_split_weakening: forall E F G D1 D2 D3,
  lenv_split (E ++ G) D1 D2 D3 ->
  wf_env (E ++ F ++ G) ->
  disjoint F D3 ->
  lenv_split (E ++ F ++ G) D1 D2 D3.
Proof.
 intros E F G D1 D2 D3 S.
  remember (E ++ G) as G0.
  generalize dependent E. generalize dependent G. generalize dependent F.
  induction S; intros F1 G1 E1 EQ WFE NIN.
  apply lenv_split_empty. auto.
  apply lenv_split_left; auto. apply IHS; auto. eapply disjoint_strengthening2.
  apply NIN.
  subst. assert (x `notin` dom F1). eapply disjoint_inversion1. apply NIN.
  simpl; auto. fsetdec. 
  repeat rewrite dom_concat in *. fsetdec.
  subst. apply wf_typ_weakening. auto. apply ok_from_wf_env. apply WFE.
 
  apply lenv_split_right; auto. apply IHS; auto. eapply disjoint_strengthening2.
  apply NIN.
  subst. assert (x `notin` dom F1). eapply disjoint_inversion1. apply NIN.
  simpl; auto. fsetdec. 
  repeat rewrite dom_concat in *. fsetdec.
  subst. apply wf_typ_weakening. auto. apply ok_from_wf_env. apply WFE.
Qed.

Lemma disjoint_strengthening4: forall E F G D,
  disjoint (E ++ F ++ G) D ->
  disjoint F D.
Proof.
  intros.
  destruct H.
  unfold disjoint.
  repeat rewrite dom_concat in *.
  split; intros.
  apply H. fsetdec.
  lapply (H0 x); intros; auto.
Qed.

Lemma disjoint_dom1: forall x b D,
  x `notin` dom D ->
  disjoint [(x, b)] D.
Proof.
  intros.
  unfold disjoint.
  split; intros.
  simpl in H0. assert (x = x0). apply in_singleton_id. auto. fsetdec. subst. auto.
  simpl.
  fsetdec.
Qed.
  
Lemma typing_weakening: forall E F G D e T,
  typing (G ++ E) D e T ->
  wf_lenv (G ++ F ++ E) D ->
  typing (G ++ F ++ E) D e T.
Proof with simpl_env;
           eauto using wf_typ_weakening,
                       wf_typ_from_wf_env_typ.
  intros E F G D e T Typ.
  remember (G ++ E) as H.
  generalize dependent G. generalize dependent E.
  induction Typ; intros E0 G EQ WFL...
  Case "var".
    subst.
    apply typing_var. eapply wf_env_from_wf_lenv.  apply WFL.
    eapply binds_weaken. apply H0. 
    apply ok_from_wf_env. eapply wf_env_from_wf_lenv; auto. eauto.
  Case "lvar".
    subst.
    apply typing_lvar. auto.
  Case "abs".
    pick fresh x and apply typing_abs.
    subst.
    apply wf_typ_weakening. auto.
    apply ok_from_wf_env. eapply wf_env_from_wf_lenv; eauto.
    subst.
    lapply (H1 x); intros; auto.
    rewrite <- concat_assoc.
    eapply H3; eauto.
    simpl_env. rewrite_env (empty ++ [(x, bind_typ T1)] ++ G ++ F ++ E0).
    eapply wf_lenv_weakening. simpl_env. auto.
    simpl_env. apply wf_env_typ. eapply wf_env_from_wf_lenv; eauto.
    apply wf_typ_weakening; eauto. 
    apply ok_from_wf_env; auto... eapply wf_env_from_wf_lenv; eauto.
    repeat rewrite dom_concat. fsetdec.
    apply disjoint_dom1. fsetdec. auto.
  Case "absl".
    pick fresh x and apply typing_labs.
    subst.
    apply wf_typ_weakening. auto.
    apply ok_from_wf_env. eapply wf_env_from_wf_lenv; eauto.
    eapply (H1 x). fsetdec. auto.
    apply wf_lenv_typ. auto. repeat rewrite dom_concat. fsetdec. fsetdec.
    subst.
    apply wf_typ_weakening. auto.
    apply ok_from_wf_env. eapply wf_env_from_wf_lenv; eauto. auto.
  Case "app".
    eapply typing_app.
    eapply IHTyp1; eauto.
    eapply wf_lenv_split1.
    subst. apply lenv_split_weakening; auto. apply H.
    eapply wf_env_from_wf_lenv. apply WFL.
    eapply disjoint_strengthening4. eapply wf_lenv_disjoint. apply WFL.
    eapply IHTyp2; eauto.
    eapply wf_lenv_split2.
    subst. apply lenv_split_weakening; auto. apply H.
    eapply wf_env_from_wf_lenv. apply WFL.
    eapply disjoint_strengthening4. eapply wf_lenv_disjoint. apply WFL.
    subst. eapply lenv_split_weakening. auto.
    eapply wf_env_from_wf_lenv. apply WFL.
    eapply disjoint_strengthening4. eapply wf_lenv_disjoint. apply WFL.
  Case "tabs".
    pick fresh X and apply typing_tabs.
    auto.
    lapply (H1 X); [intros Q | auto].
    rewrite <- concat_assoc.
    apply H1... rewrite EQ. auto.
    rewrite_env (empty ++ [(X, bind_kn K)] ++ G ++ F ++ E0).
    apply wf_lenv_weakening. simpl_env. auto.
    simpl_env. apply wf_env_kn. eapply wf_env_from_wf_lenv. apply WFL.
    repeat rewrite dom_concat. fsetdec.
    apply disjoint_dom1. fsetdec.
  Case "tapp".
    subst E.  eapply typing_tapp. apply IHTyp. auto. auto. auto. 
    apply wf_typ_weakening. auto. auto.
    apply ok_from_wf_env. eapply wf_env_from_wf_lenv. eauto.
Qed.


(************************************************************************ *)
(** ** Type substitution preserves typing (11) *)

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

    
Lemma lenv_split_subst_tb : forall G1 G2 D1 D2 D3 X K P,
  lenv_split (G1 ++ [(X, bind_kn K)] ++ G2) D1 D2 D3 ->
  wf_typ G2 P K ->
  lenv_split (map (subst_tb X P) G1 ++ G2)
             (map (subst_tlb X P) D1)
             (map (subst_tlb X P) D2)
             (map (subst_tlb X P) D3).
Proof.
  intros G1 G2 D1 D2 D3 X K P S.
  remember (G1 ++ [(X, bind_kn K)] ++ G2) as G.
  generalize dependent G1. generalize dependent G2.
  induction S; intros G2 G1 EQ WFT; subst; simpl_env in *.
  Case "empty".
    apply lenv_split_empty. auto.
    eapply wf_env_subst_tb; eauto.
  Case "left".
    simpl. simpl_env.
    apply lenv_split_left.
    apply IHS; auto. rewrite dom_concat. rewrite dom_map. fsetdec.
    rewrite dom_map. auto.
    eapply wf_typ_subst_tb; eauto.
  Case "right".
    simpl. simpl_env.
    apply lenv_split_right.
    apply IHS; auto. rewrite dom_concat. rewrite dom_map. fsetdec.
    rewrite dom_map. auto.
    eapply wf_typ_subst_tb; eauto.
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

Lemma typing_through_subst_te : forall K E F D Z e T P,
  typing (F ++ [(Z, bind_kn K)] ++ E) D e T ->
  wf_typ E P K ->
  typing (map (subst_tb Z P) F ++ E) (map (subst_tlb Z P) D) (subst_te Z P e) (subst_tt Z P T).
Proof with simpl_env;
           eauto 6 using wf_env_subst_tb,
                         wf_typ_subst_tb.

  intros K E F D Z e T P Typ PsubK.
  remember (F ++ [(Z, bind_kn K)] ++ E) as G.
  generalize dependent F. generalize dependent E.
  induction Typ; intros E0 WFT F EQ; subst;
    simpl subst_te in *; simpl subst_tt in *...
  Case "typing_var".
    apply typing_var...
    rewrite (map_subst_tb_id E0 Z P).
    binds_cases H0... 
    eapply wf_env_strengthening2.
    eapply wf_env_strengthening2. apply H.
    assert (wf_env ([(Z, bind_kn K)] ++ E0)).
          eapply wf_env_strengthening2. apply H.
       inversion H1. auto.
   Case "typing_lvar".
     simpl. apply typing_lvar. 
     assert ([(x, lbind_typ (subst_tt Z P T))] = 
             map (subst_tlb Z P) [(x, lbind_typ T)]).
     simpl. auto. rewrite H0.
     eapply wf_lenv_subst_tb. apply H. auto.
  Case "typing_abs".
    pick fresh y and apply typing_abs...
    rewrite subst_te_open_ee_var...
    rewrite_env (map (subst_tb Z P) ([(y, bind_typ T1)] ++ F) ++ E0).
    simpl in H1.
    apply H1...
    intros. rewrite H2. simpl. auto. auto.
  Case "typing_labs".
    pick fresh y and apply typing_labs...
    rewrite subst_te_open_ee_var...
    rewrite_env (map (subst_tlb Z P) ([(y, lbind_typ T1)] ++ D)).
    apply H1...
    intros. rewrite H2. simpl; auto. auto.
  Case "typing_app".
    eapply typing_app. eapply IHTyp1. auto. auto.
    eapply IHTyp2. auto. auto. eapply lenv_split_subst_tb. apply H. auto.
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


  
Lemma expr_from_typing: forall E D u T,
  typing E D u T ->
  expr u.
Proof.
  intros.
  lapply (typing_regular E D u T). intro. tauto. auto.
Qed.

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


Lemma binds_in: forall x p (E:env),
  binds x p E ->
  x `in` dom E.
Proof.
  intros. induction E.
  inversion H.
  destruct a.  simpl_env in*.
  binds_cases H.
  assert (x `in` dom E). apply IHE; auto. fsetdec.
  fsetdec.
Qed.

Lemma typing_fv: forall E D e T x,
  typing E D e T ->
  x `notin` dom E ->
  x `notin` dom D ->
  x `notin` fv_ee e.
Proof.
  intros E D e T x H.
  induction H; intros NIE NID.
  Case "var".
    simpl. assert (x0 `in` dom E). eapply binds_in; eauto. fsetdec.
  Case "lvar".
    simpl. simpl_env in *. auto.
  Case "abs".
    simpl. pick fresh y. lapply (H1 y); intros; auto.
    simpl in H3. unfold not.  intros. apply H3. assert (x `notin` singleton y). fsetdec.
    clear Fr. fsetdec. fsetdec.
    unfold open_ee. apply fv_in_open_ee; auto.
  Case "labs".
    simpl. pick fresh y. lapply (H1 y); intros; auto.
    simpl in H3. unfold not. intros. apply H3. auto. assert (x `notin` singleton y). fsetdec.
    clear Fr. fsetdec.  
    unfold open_ee. apply fv_in_open_ee; auto.
  Case "app".
    simpl. assert (x `notin` fv_ee e1). apply IHtyping1; auto.
    rewrite (dom_lenv_split E D1 D2 D3) in NID. fsetdec. auto.
    simpl. assert (x `notin` fv_ee e2). apply IHtyping2; auto.
    rewrite (dom_lenv_split E D1 D2 D3) in NID. fsetdec. auto.
    fsetdec.
  Case "tabs".
    simpl. pick fresh y. lapply (H1 y); intros; auto.
    unfold not. intros. apply H2. simpl. fsetdec. auto.
    unfold open_te. apply fv_in_open_te. auto.
  Case "tapp".
    simpl. apply IHtyping; auto.
Qed.

Lemma non_subst: forall E D e T x u,
  typing E D e T ->
  x `notin` dom E ->
  x `notin` dom D ->
  e = subst_ee x u e.
Proof.
  intros.
  apply subst_ee_fresh.
  eapply typing_fv. apply H. apply H0. apply H1.
Qed.

Lemma lenv_split_strengthening: forall G2 G1 x T D1 D2 D3,
  lenv_split (G2 ++ [(x, bind_typ T)] ++ G1) D1 D2 D3 ->
  lenv_split (G2 ++ G1) D1 D2 D3.
Proof.
  intros G2 G1 x T D1 D2 D3 S.
  remember (G2 ++ [(x, bind_typ T)] ++ G1) as G.
  generalize dependent G1. generalize dependent G2.
  induction S; intros G2 G1 EQ; simpl_env in *; auto.
  apply lenv_split_empty. subst. eapply wf_env_strengthening; eauto.
  subst. apply lenv_split_left; auto. simpl_env in *. fsetdec.
  eapply wf_typ_strengthening. apply H1.
  subst. apply lenv_split_right; auto. simpl_env in *. fsetdec.
  eapply wf_typ_strengthening. apply H1.
Qed.

Lemma value_through_subst_ee: forall e1 x u,
  expr u ->
  value e1 ->
  value (subst_ee x u e1).
Proof.
  intros e1 x u EX V.
  induction V; simpl; auto.
  inversion H. subst.
  apply value_abs. 
  pick fresh z and apply expr_abs. auto.
  rewrite subst_ee_open_ee_var. 
  apply subst_ee_expr. apply H4. fsetdec. auto.
  fsetdec. auto.
  inversion H; subst.
  apply value_tabs.
  pick fresh X and apply expr_tabs.
  rewrite subst_ee_open_te_var.
  apply subst_ee_expr. apply H1; auto.  auto. auto.
Qed.
  
Lemma typing_through_subst_ee1: forall G2 G1 x U0 D e T u,
  typing (G2 ++ [(x, bind_typ U0)] ++ G1) D e T ->
  typing G1 lempty u U0 ->
  value u ->
  typing (G2 ++ G1) D (subst_ee x u e) T.
Proof.
  intros G2 G1 x U0 D e T u Typ.
  remember (G2 ++ [(x, bind_typ U0)] ++ G1) as G.
  generalize dependent G2. generalize dependent G1.
  induction Typ; intros G1 G2 EQ TYP V; simpl_env in *; auto.
  Case "var".
    simpl; subst.
    destruct (x0 == x).
    rewrite_env (empty ++ G2 ++ G1).
    apply typing_weakening. simpl_env. subst. 
    assert (bind_typ T = bind_typ U0).
    eapply binds_mid_eq_cons. simpl in H0. apply H0.
    simpl_env. apply ok_from_wf_env; auto.
    inversion H1. subst. auto.
    simpl_env. apply wf_lenv_empty. eapply wf_env_strengthening. apply H.
    apply typing_var.
    eapply wf_env_strengthening. apply H.
    binds_cases H0. apply binds_tail; auto. apply binds_head; auto.
  Case "lvar".
    simpl. destruct (x0 == x); subst.
    inversion H. assert False. apply H5. repeat rewrite dom_concat. simpl. fsetdec. tauto.
    apply typing_lvar. eapply wf_lenv_strengthening. apply H.
  Case "abs".
    simpl. 
    pick fresh y and apply typing_abs.
    subst. eapply wf_typ_strengthening. apply H.
    rewrite_env (([(y, bind_typ T1)] ++ G2) ++ G1).
    rewrite subst_ee_open_ee_var.
    apply H1; auto. subst. simpl_env. auto.
    fsetdec. eapply expr_from_typing. apply TYP. auto.
  Case "labs".
    simpl.
    pick fresh y and apply typing_labs.
    subst. eapply wf_typ_strengthening. apply H.
    rewrite subst_ee_open_ee_var.
    apply H1; subst; auto.
    fsetdec. eapply expr_from_typing. apply TYP. auto.
  Case "app".
    simpl; subst.
    eapply typing_app.
    eapply IHTyp1; eauto.
    eapply IHTyp2; eauto.
    eapply lenv_split_strengthening.
    eapply H.
  Case "tabs".
    simpl. 
    pick fresh X and apply typing_tabs.
    apply value_through_subst_ee. eapply expr_from_typing. apply TYP. auto.
    rewrite_env (([(X, bind_kn K)] ++ G2) ++ G1).
    rewrite subst_ee_open_te_var.
    apply H1; subst; auto. eapply expr_from_typing. apply TYP.
  Case "tapp".
    simpl.
    eapply typing_tapp. eapply IHTyp; auto.
    subst. eapply wf_typ_strengthening. apply H.
Qed.


Lemma lenv_split_cases: forall G D1 D2 DL x T DR,
  lenv_split G D1 D2 (DL ++ [(x, lbind_typ T)] ++ DR) ->
  (exists D1L, exists D1R, exists D2L, exists D2R,
    D1 = D1L ++ [(x, lbind_typ T)] ++ D1R /\
    D2 = D2L ++ D2R /\
    lenv_split G D1L D2L DL /\
    lenv_split G D1R D2R DR) \/
  (exists D1L, exists D1R, exists D2L, exists D2R,
    D1 = D1L ++ D1R /\
    D2 = D2L ++ [(x, lbind_typ T)] ++ D2R /\
    lenv_split G D1L D2L DL /\
    lenv_split G D1R D2R DR).
Proof.
  intros G D1 D2 DL x T DR S.
  remember (DL ++ [(x, lbind_typ T)] ++ DR) as D3.
  generalize dependent DR. generalize dependent DL.
  induction S; intros DL DR EQ; subst; simpl_env in *.
  Case "empty".
    destruct DL; inversion EQ.
  Case "left".
    destruct DL; simpl in *; inversion EQ; subst; simpl_env in *.
    left. 
    exists lempty. exists D1. exists lempty. exists D2.
    simpl_env. repeat split; auto. apply lenv_split_empty.
    eapply wf_env_from_wf_lenv. eapply wf_lenv_split1. apply S.
    lapply (IHS DL DR).
    intros.
    destruct H2.
    destruct H2 as [D1L [D1R [D2L [D2R [Q1 [Q2 [S1 S2]]]]]]].
    left. exists ([(x0, lbind_typ T0)] ++ D1L).
    exists D1R. exists D2L. exists D2R.
    simpl_env in *. repeat split; auto. subst. auto.
    apply lenv_split_left. auto. auto. fsetdec. auto.
    
    destruct H2 as [D1L [D1R [D2L [D2R [Q1 [Q2 [S1 S2]]]]]]].
    right. exists ([(x0, lbind_typ T0)] ++ D1L).
    exists D1R. exists D2L. exists D2R.
    subst. simpl_env in *. repeat split; auto.
    apply lenv_split_left; auto. simpl_env. auto.
  Case "right".
    destruct DL; simpl in *; inversion EQ; subst; simpl_env in *.
    right.
    exists lempty. exists D1. exists lempty. exists D2.
    simpl_env in *. repeat split; auto. apply lenv_split_empty.
    eapply wf_env_from_wf_lenv. eapply wf_lenv_split1. apply S.
    lapply (IHS DL DR).
    intros.
    destruct H2.
    destruct H2 as [D1L [D1R [D2L [D2R [Q1 [Q2 [S1 S2]]]]]]].
    left. exists D1L. 
    exists D1R. exists ([(x0, lbind_typ T0)] ++ D2L). exists D2R.
    simpl_env in *. repeat split; auto. subst. auto.
    apply lenv_split_right. auto. auto. fsetdec. auto.
    
    destruct H2 as [D1L [D1R [D2L [D2R [Q1 [Q2 [S1 S2]]]]]]].
    right. exists D1L. 
    exists D1R. exists ([(x0, lbind_typ T0)] ++ D2L). exists D2R.
    subst. simpl_env in *. repeat split; auto.
    apply lenv_split_right; auto. simpl_env. auto.
Qed.

Lemma lenv_split_not_in1: forall G D1 D2 D3 x,
  lenv_split G D1 D2 D3 ->
  x `in` dom D1 ->
  x `notin` (dom D2 `union` dom G).
Proof.
  intros G D1 D2 D3 x S.
  induction S; intros; simpl_env in *; try fsetdec.
  rewrite (dom_lenv_split E D1 D2 D3) in H0.
  fsetdec. auto.
  rewrite (dom_lenv_split E D1 D2 D3) in H0.
  fsetdec. auto.
Qed.

Lemma lenv_split_not_in2: forall G D1 D2 D3 x,
  lenv_split G D1 D2 D3 ->
  x `in` dom D2 ->
  x `notin` (dom D1 `union` dom G).
Proof.
  intros.
  eapply lenv_split_not_in1. eapply lenv_split_commute. apply H. auto.
Qed.

Lemma lenv_split_lin_weakening1: forall E F D1 D2 D3,
  lenv_split E D1 D2 D3 ->
  wf_lenv E (F ++ D3) ->
  lenv_split E (F ++ D1) D2 (F ++ D3).
Proof.
  intros E F. 
  induction F; intros D1 D2 D3 S WFL; simpl_env in *; auto.
  destruct a. simpl_env in *.
  inversion WFL.
  apply lenv_split_left; auto.
Qed.

Lemma lenv_split_sub1: forall E D1L D1R D2 DL DR x U F,
   lenv_split E 
        (D1L ++ [(x, lbind_typ U)] ++ D1R) 
        D2 
        (DL ++ [(x, lbind_typ U)] ++ DR) ->
   wf_lenv E (DL ++ F ++ DR) ->
   lenv_split E
        (D1L ++ F ++ D1R) 
        D2
        (DL ++ F ++ DR).
Proof.
  intros E D1L D1R D2 DL DR x U F S.
  remember (D1L ++ [(x, lbind_typ U)] ++ D1R) as D1.
  remember (DL ++ [(x, lbind_typ U)] ++ DR) as D3.
  generalize dependent D1R. generalize dependent D1L.
  generalize dependent DR. generalize dependent DL.
  induction S; intros DL DR EQ1 D1L D1R EQ2 WFL; subst; auto.
  Case "empty".
    destruct DL; inversion EQ1.
  Case "left".
    destruct DL; inversion EQ1; subst.
    destruct D1L; inversion EQ2; subst.
    simpl_env in *. apply lenv_split_lin_weakening1. apply S. auto.
    simpl_env in *.
    rewrite (dom_lenv_split E (D1L ++ [(x, lbind_typ U)] ++ D1R) D2 DR) in H0.
    simpl_env in *. assert False. fsetdec. tauto. auto.
    destruct D1L; inversion EQ2; subst.        
    simpl_env in *. assert False. fsetdec. tauto. 
    simpl_env in *. apply lenv_split_left. apply IHS; auto.
    inversion WFL; auto. auto. inversion WFL; auto. auto.
  Case "right".
    destruct DL; inversion EQ1; subst.
    rewrite (dom_lenv_split E (D1L ++ [(x, lbind_typ U)] ++ D1R) D2 DR) in H0.
    simpl_env in *. assert False. fsetdec. tauto. auto.
    simpl_env in *. apply lenv_split_right. apply IHS; auto.
    inversion WFL; auto. auto. inversion WFL; auto. auto.
Qed.

Lemma lenv_split_sub2: forall E D1 D2L D2R DL DR x U F,
   lenv_split E 
        D1
        (D2L ++ [(x, lbind_typ U)] ++ D2R) 
        (DL ++ [(x, lbind_typ U)] ++ DR) ->
   wf_lenv E (DL ++ F ++ DR) ->
   lenv_split E
        D1
        (D2L ++ F ++ D2R) 
        (DL ++ F ++ DR).
Proof.
  intros.
  apply lenv_split_commute. eapply lenv_split_sub1.
  apply lenv_split_commute. apply H. auto.
Qed.
  
Lemma wf_lenv_lin_strengthening: forall G D1 D2 D3,
  wf_lenv G (D1 ++ D2 ++ D3) ->
  wf_lenv G D2.
Proof.
  intros.
  remember (D1 ++ D2 ++ D3) as D.
  generalize dependent D1. generalize dependent D2. generalize dependent D3.
  induction H; intros D3 D2 D1 EQ.
  Case "empty".
    destruct D1; destruct D2; destruct D3; inversion EQ; auto.
  Case "nonempty".
    destruct D1; destruct D2; simpl_env in *; inversion EQ; subst; auto.
    apply wf_lenv_empty. eapply wf_env_from_wf_lenv. apply H.
    simpl_env. apply wf_lenv_typ; auto. apply (IHwf_lenv D3 D2 lempty); auto.
    simpl_env in *. fsetdec. 
    apply wf_lenv_empty. eapply wf_env_from_wf_lenv. apply H.
    apply (IHwf_lenv D3 (p0 :: D2) D1); auto.
Qed.

Lemma typing_through_subst_ee2: forall G D2 x U D1 e T F u,
  typing G (D2 ++ [(x, lbind_typ U)] ++ D1) e T ->
  typing G F u U ->
  wf_lenv G (D2 ++ F ++ D1) ->
  typing G (D2 ++ F ++ D1) (subst_ee x u e) T.
Proof.
  intros G D2 x U D1 e T F u TYP.
  remember (D2 ++ [(x, lbind_typ U)] ++ D1) as D.
  generalize dependent D2. generalize dependent D1.
  induction TYP; intros DR DL EQ TYPU WFL; subst; simpl_env in *; auto.
  Case "var".
    destruct DL; inversion EQ.
  Case "lvar".
    destruct DL; inversion EQ. subst. simpl_env in *. simpl.
    destruct (x == x). auto. tauto.
    destruct DL; inversion EQ.
  Case "abs".
    simpl.
    pick fresh y and apply typing_abs; auto.
    rewrite subst_ee_open_ee_var.
    apply H1; auto. rewrite_env (empty ++ [(y, bind_typ T1)] ++ E).
    apply typing_weakening. simpl_env. auto. 
    apply wf_lenv_weakening. simpl_env. 
    eapply wf_lenv_lin_strengthening. apply WFL.
    simpl_env. apply wf_env_typ. eapply wf_env_from_typing. apply TYPU. auto.
    fsetdec. apply disjoint_dom1. fsetdec.
    rewrite_env (empty ++ [(y, bind_typ T1)] ++ E). 
    apply wf_lenv_weakening. simpl_env.  auto.
    simpl_env. apply wf_env_typ. eapply wf_env_from_typing. apply TYPU. auto.
    fsetdec. apply disjoint_dom1. repeat rewrite dom_concat. fsetdec. fsetdec.
    eapply expr_from_typing. apply TYPU. 
    intros. lapply H2; auto. intros. destruct DL; inversion H4.
  Case "labs".
    simpl.
    pick fresh y and apply typing_labs. auto.
    rewrite_env (([(y, lbind_typ T1)] ++ DL) ++ F ++ DR).
    rewrite subst_ee_open_ee_var.
    apply H1; auto. simpl_env. apply wf_lenv_typ. auto. 
    fsetdec. simpl_env. fsetdec. auto. fsetdec.
    eapply expr_from_typing. apply TYPU.
    intros. lapply H2; auto. intros. destruct DL; inversion H4.
  Case "app".
    simpl.
    lapply (lenv_split_cases E D1 D2 DL x U DR).
    intros C.
    destruct C as [LEFT | RIGHT].
    destruct LEFT as [D1L [D1R [D2L [D2R [Q1 [Q2 [S1 S2]]]]]]].
    lapply (IHTYP1 D1R D1L); auto. intros I.
    lapply I; auto. intros TYPE1. 
    rewrite <- (non_subst E D2 e2 T1 x u); auto.
    subst.
    apply (typing_app T1 K E (D1L ++ F ++ D1R) (D2L ++ D2R)).
    assert (wf_lenv E (D1L ++ F ++ D1R)).
    eapply wf_lenv_split1. eapply lenv_split_sub1. apply H. auto.
    apply TYPE1.  auto. auto.
    eapply lenv_split_sub1. apply H. auto.
    assert (x `notin` (dom D2 `union` dom E)).
    eapply lenv_split_not_in1. apply H. subst.
    simpl_env. fsetdec. fsetdec.
    assert (x `notin` (dom D2 `union` dom E)).
    eapply lenv_split_not_in1. apply H. subst.
    simpl_env. fsetdec. fsetdec.

    destruct RIGHT as [D1L [D1R [D2L [D2R [Q1 [Q2 [S1 S2]]]]]]].
    lapply (IHTYP2 D2R D2L); auto. intros I.
    lapply I; auto. intros TYPE2. 
    rewrite <- (non_subst E D1 e1 (typ_arrow K T1 T2) x u); auto.
    subst.
    apply (typing_app T1 K E (D1L ++ D1R) (D2L ++ F ++ D2R)).
    assert (wf_lenv E (D2L ++ F ++ D2R)).
    eapply wf_lenv_split2. eapply lenv_split_sub2. apply H. auto.
    auto.
    apply TYPE2.  auto. 
    eapply wf_lenv_split2. eapply lenv_split_sub2. apply H. auto. 
    eapply lenv_split_sub2. apply H. auto.
    assert (x `notin` (dom D1 `union` dom E)).
    eapply lenv_split_not_in2. apply H. subst.
    simpl_env. fsetdec. fsetdec.
    assert (x `notin` (dom D1 `union` dom E)).
    eapply lenv_split_not_in2. apply H. subst.
    simpl_env. fsetdec. fsetdec. auto.

  Case "tabs".
    simpl.
    pick fresh X and apply typing_tabs.
    apply value_through_subst_ee. eapply expr_from_typing. apply TYPU. auto.
    rewrite subst_ee_open_te_var. 
    apply H1; auto. 
    rewrite_env (empty ++ [(X, bind_kn K)] ++ E). apply typing_weakening. 
    simpl_env. auto. eapply wf_lenv_weakening. simpl_env. eapply wf_lenv_from_typing. 
    apply TYPU. simpl_env. eapply wf_env_kn. eapply wf_env_from_typing. apply TYPU. fsetdec.
    apply disjoint_dom1. fsetdec.
    rewrite_env (empty ++ [(X, bind_kn K)] ++ E). apply wf_lenv_weakening. 
    simpl_env. auto. simpl_env. apply wf_env_kn. eapply wf_env_from_typing. apply TYPU. 
    fsetdec. apply disjoint_dom1. repeat rewrite dom_concat. fsetdec.
    eapply expr_from_typing. apply TYPU.
  Case "tapp".
    simpl. 
    eapply typing_tapp. apply IHTYP; auto. auto.
Qed.

    
(* ********************************************************************** *)
(* ********************************************************************** *)
(** ** Preservation (20) *)

Lemma value_nonlin_inversion: forall E D e T,
  typing E D e T ->
  value e ->
  wf_typ E T kn_nonlin ->
  D = lempty.
Proof.
  intros E D e T Typ.
  induction Typ; intros V WFT; auto.
  Case "lvar".
    inversion V.
  Case "abs".
    inversion WFT; subst. apply H2; auto.
  Case "labs".
    inversion WFT; subst. apply H2; auto.
  Case "app".
    inversion V.
  Case "tabs".
    inversion V. subst. 
    inversion WFT. subst.
    pick fresh X.
    apply (H1 X). fsetdec.
    apply value_through_open_te; auto.
    apply (H7 X). fsetdec.
  Case "tapp".
    inversion V.
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

Lemma lenv_split_weakening1: forall E D1L D1R D2L D2R D3L D3R x T,
  lenv_split E (D1L ++ D1R) (D2L ++ D2R) (D3L ++ D3R) ->
  lenv_split E D1L D2L D3L ->
  lenv_split E D1R D2R D3R ->
  wf_lenv E (D3L ++ [(x, lbind_typ T)] ++ D3R) ->
  lenv_split E (D1L ++ [(x, lbind_typ T)] ++ D1R) (D2L ++ D2R) (D3L ++ [(x, lbind_typ T)]++ D3R).
Proof.
  intros E D1L D1R D2L D2R D3L D3R x T S.
  remember (D1L ++ D1R) as D1.
  remember (D2L ++ D2R) as D2.
  remember (D3L ++ D3R) as D3.
  generalize dependent D1L. generalize dependent D1R.
  generalize dependent D2L. generalize dependent D2R.
  generalize dependent D3L. generalize dependent D3R.
  induction S; intros D3R D3L EQ3 D2R D2L EQ2 D1R D1L EQ1 SL SR WFL; subst; simpl_env in *.
  Case "empty".
    destruct D3L; destruct D3R; inversion EQ3; subst; simpl_env.
    destruct D2L; destruct D2R; inversion EQ2; subst; simpl_env.
    destruct D1L; destruct D1R; inversion EQ1; subst; simpl_env.
    rewrite_env ([(x, lbind_typ T)] ++ lempty).
    apply lenv_split_left. apply lenv_split_empty. auto. 
    simpl_env in WFL. inversion WFL. auto. simpl. fsetdec.
    simpl_env in WFL. inversion WFL. auto.
  Case "left".
    destruct D3L; inversion EQ3.
    destruct D1L; inversion EQ1.
      destruct D3R; simpl_env in EQ3; inversion EQ3.
      destruct D1R; simpl_env in EQ1; inversion EQ1.
      subst; simpl_env in *.
      apply lenv_split_left.  apply lenv_split_left; auto.
      inversion WFL; auto. inversion WFL; auto. inversion WFL; auto.
      inversion SL.
      destruct D1R; simpl_env in EQ1; inversion EQ1.
      subst. simpl_env in *. apply lenv_split_left; auto.
      rewrite_env (D1 ++ [(x, lbind_typ T)] ++ lempty).
      eapply IHS; auto. simpl_env; auto. 
        inversion SL; auto. subst.
        rewrite (dom_lenv_split E ([(x0, lbind_typ T0)] ++ D1) D2 D3L) in H0; auto.
        simpl in H0. assert False. fsetdec. tauto.
        inversion WFL; auto.
        inversion WFL; auto.
      subst.
      inversion SL; subst; simpl_env in *.
      apply lenv_split_left. eapply IHS; auto. inversion EQ1; auto.
      inversion WFL; auto. auto. inversion WFL; auto. auto.
      assert (dom (D3L ++ D3R) = dom D3L `union` dom D3R).
      rewrite dom_concat; auto.
      rewrite <- H2 in H0.
      rewrite (dom_lenv_split E D1 ([(x0, lbind_typ T0)] ++ D2 ++ D2R) (D3L ++ D3R)) in H0.
      simpl in H0. assert False. fsetdec. tauto. auto.
  Case "right".
    destruct D3L; inversion EQ3.
    destruct D2L; inversion EQ2.
    destruct D3R; inversion EQ3.
    destruct D2R; inversion EQ2.
    subst; simpl_env in *.
    inversion SL; simpl_env in *.
    apply lenv_split_left; auto. inversion WFL; auto. inversion WFL; auto. auto.
    inversion WFL; auto.
    subst. inversion SL.
    subst. simpl_env in *.
    destruct D2L; inversion EQ2.
      destruct D2R; inversion EQ2. subst.  simpl_env in *.
      rewrite (dom_lenv_split E D1R ([(x0, lbind_typ T0)] ++ D2R) D3R) in H0; auto.
      simpl in H0. assert False. fsetdec. tauto.
    apply lenv_split_right; auto.  subst. eapply IHS; auto.  
      inversion SL; subst; simpl_env in *.
      assert (dom (D3L ++ D3R) = dom D3L `union` dom D3R).
      rewrite dom_concat; auto.
      rewrite <- H2 in H0.
      rewrite (dom_lenv_split E ([(x0, lbind_typ T0)] ++ D1 ++ D1R) 
        (D2L ++ D2R) (D3L ++ D3R)) in H0; auto.
      simpl in H0. assert False. fsetdec. tauto. auto.
      inversion WFL; auto. inversion WFL; auto.
Qed.
      
Lemma lenv_split_weakening2: forall E D1L D1R D2L D2R D3L D3R x T,
  lenv_split E (D1L ++ D1R) (D2L ++ D2R) (D3L ++ D3R) ->
  lenv_split E D1L D2L D3L ->
  lenv_split E D1R D2R D3R ->
  wf_lenv E (D3L ++ [(x, lbind_typ T)] ++ D3R) ->
  lenv_split E (D1L ++ D1R) (D2L ++ [(x, lbind_typ T)] ++ D2R) (D3L ++ [(x, lbind_typ T)]++ D3R). Proof.   
  intros. apply lenv_split_commute. apply lenv_split_weakening1; try (apply lenv_split_commute; auto); auto.
Qed.

Lemma wf_lenv_trivial_split1: forall E D,
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

Lemma wf_lenv_from_lenv_split1: forall E D1 D2 DL DR,
  lenv_split E D1 D2 (DL ++ DR) ->
  wf_lenv E DL.
Proof.
  intros. eapply wf_lenv_lin_strengthening.
  rewrite_env (lempty ++ DL ++ DR) in H.
  eapply wf_env_split0. apply H.
Qed.

Lemma wf_lenv_from_lenv_split2: forall E D1 D2 DL DR,
  lenv_split E D1 D2 (DL ++ DR) ->
  wf_lenv E DR.
Proof.
  intros. eapply wf_lenv_lin_strengthening.
  rewrite_env (DL ++ DR ++ lempty) in H.
  eapply wf_env_split0. apply H.
Qed.

Lemma wf_lenv_lin_weakening: forall E D1 D2 x TX,
  wf_typ E TX kn_lin ->
  wf_lenv E (D1 ++ D2) ->
  x `notin` dom E ->
  x `notin` dom (D1 ++ D2) ->
  wf_lenv E (D1 ++ [(x, lbind_typ TX)] ++ D2).
Proof.
  intros E D1 D2 x TX WFT WFL.
  remember (D1 ++ D2) as D.
  generalize dependent D1. generalize dependent D2.
  induction WFL; intros D2 D1 EQ NIN1 NIN2.
  Case "empty".
   destruct D1; destruct D2; inversion EQ; subst; simpl_env in *.
   rewrite_env ([(x, lbind_typ TX)] ++ lempty).
   apply wf_lenv_typ; auto.
  Case "cons".
    destruct D1; destruct D2; inversion EQ; subst; simpl_env in *.
    apply wf_lenv_typ; auto. 
    apply wf_lenv_typ; auto.  rewrite_env (D1 ++ [(x, lbind_typ TX)] ++ lempty).
    apply IHWFL; auto. simpl_env; auto.
    apply wf_lenv_typ; auto. 
Qed.

Lemma lenv_split_exchange1: forall E D1L D1M D2L D2M D3L D3M x TX,
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
    rewrite_env (D1M ++ [(x, lbind_typ TX)] ++ lempty).
    rewrite_env (D2M ++ lempty).
    rewrite_env (D3M ++ [(x, lbind_typ TX)] ++ lempty).
    apply lenv_split_weakening1. simpl_env. auto. auto. auto.
    eapply wf_lenv_lin_weakening. auto. simpl_env. 
    eapply wf_env_split0. apply SM. auto. simpl_env. fsetdec.
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
    simpl in H0. assert False. rewrite dom_concat in H0. simpl in H0. fsetdec. tauto.
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

Lemma lenv_split_cases2: forall E DL D1 D2 DR,
  lenv_split E D1 D2 (DL ++ DR) ->
  exists D1L, exists D1R, exists D2L, exists D2R,
    lenv_split E D1L D2L DL /\
    lenv_split E D1R D2R DR /\
    D1L ++ D1R = D1 /\
    D2L ++ D2R = D2.
Proof.
  intros E DL.
  induction DL; intros D1 D2 DR S.
  Case "empty".
    exists lempty. exists D1. exists lempty. exists D2.
    simpl_env in *; repeat split; auto. apply lenv_split_empty.
    eapply wf_env_from_wf_lenv. eapply wf_env_split0. apply S.
  Case "cons".
    destruct a. simpl_env in S.
    inversion S.
    SCase "left".
      subst.
      lapply (IHDL D0 D2 DR); auto.
      intros.
      destruct H as [D1L [D1R [D2L [D2R [S2 [S3 [Q1 Q2]]]]]]].
      exists ([(a, lbind_typ T)] ++ D1L).
      exists D1R.
      exists D2L.
      exists D2R.
      subst; simpl_env in *; repeat split; auto.
      apply lenv_split_left; auto.
    SCase "right".
      subst.
      lapply (IHDL D1 D3 DR); auto.
      intros.
      destruct H as [D1L [D1R [D2L [D2R [S2 [S3 [Q1 Q2]]]]]]].
      exists D1L.
      exists D1R.
      exists ([(a, lbind_typ T)] ++ D2L).
      exists D2R.
      subst; simpl_env in *; repeat split; auto.
      apply lenv_split_right; auto.
Qed.

Lemma wf_lenv_exchange: forall E x TX DL DR,
  wf_lenv E ([(x, lbind_typ TX)] ++ DL ++ DR) ->
  wf_lenv E (DL ++ [(x, lbind_typ TX)] ++ DR).
Proof.
  intros.
  inversion H.
  apply wf_lenv_lin_weakening; auto.
Qed.

Lemma wf_lenv_exchange2: forall E x TX DL DM DR,
  wf_lenv E (DL ++ [(x, lbind_typ TX)] ++ DM ++ DR) ->
  wf_lenv E (DL ++ DM ++ [(x, lbind_typ TX)] ++ DR).
Proof.
  induction DL; intros.
  simpl_env in *. apply wf_lenv_exchange; auto.
  simpl_env in *.
  destruct a. simpl_env in *.
  inversion H.
  apply wf_lenv_typ. apply IHDL; auto. auto.
  repeat rewrite dom_concat in *. simpl in *. 
  rewrite dom_concat in H6. fsetdec.
  auto.
Qed.

Lemma typing_exchange1: forall E D1 D2 D3 x TX e T,
  typing E (D1 ++ [(x, lbind_typ TX)] ++ D2 ++ D3) e T ->
  typing E (D1 ++ D2 ++ [(x, lbind_typ TX)] ++ D3) e T.
Proof.
  intros E D1 D2 D3 x TX e T TYP.
  remember (D1 ++ [(x, lbind_typ TX)] ++ D2 ++ D3) as D.
  generalize dependent D3. generalize dependent D2. generalize dependent D1.
  induction TYP; intros DL DM DR EQ.
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
    lapply (lenv_split_cases E D1 D2 DL x TX (DM ++ DR)); auto.
    intros CASES.
    destruct CASES as [LEFT | RIGHT].
    destruct LEFT as [D1L [D1R [D2L [D2R [EQ1 [EQ2 [S1 S2]]]]]]].
    subst.
    lapply (lenv_split_cases2 E DM D1R D2R DR); auto.
    intros EX.
    destruct EX as [D1RM [D1RR [D2RM [D2RR [S3 [S4 [EQ1 EQ2]]]]]]].
    lapply (IHTYP1 D1L D1RM D1RR); auto.
    intros TYPE1.
    assert (lenv_split E (D1L ++ D1RM ++ [(x, lbind_typ TX)] ++ D1RR)
                         (D2L ++ D2RM ++ D2RR)
                         (DL  ++ DM ++ [(x, lbind_typ TX)] ++ DR)).
    apply lenv_split_join. auto.
    apply lenv_split_weakening1. subst; auto. auto. auto.
    apply wf_lenv_exchange.
    eapply wf_lenv_from_lenv_split2. apply H.
    apply wf_lenv_exchange2.
    eapply wf_env_split0. apply H.
    apply (typing_app T1 K E 
            (D1L ++ D1RM ++ [(x, lbind_typ TX)] ++ D1RR) 
            (D2L ++ D2RM ++ D2RR) 
            (DL ++ DM ++ [(x, lbind_typ TX)] ++ DR)); auto.
    subst; auto. subst; auto.

    destruct RIGHT as [D1L [D1R [D2L [D2R [EQ1 [EQ2 [S1 S2]]]]]]].
    subst.
    lapply (lenv_split_cases2 E DM D1R D2R DR); auto.
    intros EX.
    destruct EX as [D1RM [D1RR [D2RM [D2RR [S3 [S4 [EQ1 EQ2]]]]]]].
    lapply (IHTYP2 D2L D2RM D2RR); auto.
    intros TYPE2.
    assert (lenv_split E (D1L ++ D1RM ++ D1RR)
                         (D2L ++ D2RM ++ [(x, lbind_typ TX)] ++ D2RR)
                         (DL  ++ DM ++ [(x, lbind_typ TX)] ++ DR)).
    apply lenv_split_join; auto.
    apply lenv_split_weakening2; subst; auto.
    apply wf_lenv_exchange.
    eapply wf_lenv_from_lenv_split2. apply H.
    apply wf_lenv_exchange2.
    eapply wf_env_split0. apply H.
    apply (typing_app T1 K E 
            (D1L ++ D1RM ++ D1RR) 
            (D2L ++ D2RM ++ [(x, lbind_typ TX)] ++ D2RR) 
            (DL ++ DM ++ [(x, lbind_typ TX)] ++ DR)); auto.
    subst; auto. subst; auto.
    
  Case "tabs".
    pick fresh X and apply typing_tabs.
    auto. 
    apply (H1 X); auto.

  Case "tapp".
    eapply typing_tapp; auto.
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

Lemma lenv_split_cases3: forall E DL D1 D2 DR,
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

Lemma lenv_split_cases3: forall E D1 D2 D3 x T,
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

Lemma lenv_split_cases4: forall E D1 D2 D3 x T,
  lenv_split E D1 ([(x, lbind_typ T)] ++ D2) D3 ->
  exists DL, exists D1R, exists D3R,
    D1 = DL ++ D1R /\
    D3 = DL ++ [(x, lbind_typ T)] ++ D3R /\
    lenv_split E D1R D2 D3R.
Proof.
  intros. 
  lapply (lenv_split_cases3 E D2 D1 D3 x T).
  intros. 
  destruct H0 as [DL [D2R [D3R [Q1 [Q2 S2]]]]].
  exists DL. exists D2R. exists D3R.
  repeat split; auto.
  apply lenv_split_commute; auto.
  apply lenv_split_commute; auto.
Qed.

(* Auxilliary definitions to add enough structure about permutations! *)

Inductive permute : lenv -> lenv -> Prop :=
| permute_empty: permute lempty lempty
| permute_cons: forall D DL DR x T,
    permute D (DL ++ DR) ->
    permute ([(x, lbind_typ T)] ++ D) (DL ++ [(x, lbind_typ T)] ++ DR).

Lemma permute_refl: forall D,
  permute D D.
Proof.
  induction D.
  apply permute_empty.
  destruct a. destruct l. 
  assert ((permute ((a, lbind_typ t)::D) 
                  ((a, lbind_typ t)::D)) = 
         (permute ([(a, lbind_typ t)] ++ D) 
                  (lempty ++ [(a, lbind_typ t)] ++ D))).
  simpl_env; auto.
  rewrite -> H.
  apply permute_cons. simpl_env. auto.
Qed.

Lemma eq_lbnd_dec: forall (a b:lbinding), {a = b}+{~a=b}.
Proof.
  decide equality. apply eq_typ_dec.
Qed.
  
Lemma eq_lbinding_dec: forall (x y:(atom * lbinding)%type), {x = y}+{~x = y}.
Proof.
  decide equality. apply eq_lbnd_dec. apply eq_atom_dec.
Qed.

Lemma eq_lenv_tail: forall (E2:lenv) F2 Y,
  [Y] ++ E2 = [Y] ++ F2 ->
  E2 = F2.
Proof.
  induction E2; intros.
  simpl in H. inversion H. auto.
  destruct F2.
  simpl in H. inversion H.
  simpl in H. inversion H. subst. auto.
Qed.

Lemma eq_lenv_mid: forall (E1:lenv) E2 F1 F2 Y,
  ok (E1 ++ [Y] ++ E2) ->
  E1 ++ [Y] ++ E2 = F1 ++ [Y] ++ F2 ->
   E1 = F1 /\ E2 = F2
.
Proof.
  induction E1; intros; auto.
  destruct F1.   simpl in *. split; auto. eapply eq_lenv_tail. simpl. eapply H0.
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

Lemma lok_distinct: forall A (E1:lenv) X E2,
  ok ((A :: E1) ++ [X] ++ E2) ->
  A <> X.
Proof.
  intros.
  inversion H. destruct X.
  rewrite dom_concat in H3. simpl in H3. unfold not. intros. inversion H4. subst. unfold not in H3. apply H3. fsetdec.
Qed.


Lemma lenv_cases: forall (E1:lenv) E2 F1 F2 X Y,
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
    eapply lok_distinct. eapply H0.
    assert (p <> Y).
    eapply lok_distinct. eapply H1.
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


Lemma lenv_mid_two: forall (E1:lenv) X E2 F1 F2,
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
  destruct (eq_lbinding_dec X p).
  subst p. rewrite_env (F1 ++ [X] ++ F2) in EQ.
  right. exists lempty. rewrite <- app_nil_end. rewrite_env ([X] ++ E2).
  assert (E1 = F1 /\ E2 = F2).
  eapply eq_lenv_mid. eapply OK.
  auto. destruct H. subst; auto.
  rewrite_env (F1 ++ [p] ++ F2) in EQ.
  lapply (lenv_cases E1 E2 F1 F2 X p n OK).  intros.
  destruct (H EQ).
  left. destruct H0. exists x. tauto.
  right. destruct H0. exists ([p] ++ x). simpl in H0. simpl. destruct H0. subst. tauto.
  rewrite <- EQ. auto.
Qed.

Lemma dom_permute: forall D1 D2,
  permute D1 D2 ->
  dom D1 = dom D2.
Proof.
  induction D1.
  intros.
  inversion H. simpl_env in *. auto.
  intros.
  inversion H. subst. simpl_env in *.
  rewrite (IHD1 (DL ++ DR)). rewrite dom_concat. fsetdec. auto.
Qed.

Lemma ok_exchange: forall D1 D2 x T,
  ok ([(x, lbind_typ T)] ++ D1 ++ D2) ->
  ok (D1 ++ [(x, lbind_typ T)] ++ D2).
Proof.
  induction D1; intros; simpl_env in *.
  auto.
  simpl_env. destruct a. destruct l.
  simpl_env in *. simpl. apply ok_cons; auto.
  simpl_env. apply IHD1; auto.
  eapply ok_remove_mid. apply H.
  inversion H. inversion H2. rewrite dom_concat in *.
  simpl_env in *. fsetdec.
Qed.

Lemma ok_lenv_permute: forall D1 D2,
  ok D1 ->
  permute D1 D2 ->
  ok D2.
Proof.
  induction D1; intros D2 OK P.
  inversion P. auto.
  inversion P. subst.
  apply ok_exchange. simpl. apply ok_cons. apply IHD1; auto.
  inversion OK; auto. rewrite <- (dom_permute D1). 
  inversion OK; auto. auto.
Qed.

Lemma permute_weakening: forall D1L D1R D2L D2R x T,
  ok (D1L ++ [(x, lbind_typ T)] ++ D1R) ->
  permute (D1L ++ D1R) (D2L ++ D2R) ->
  permute (D1L ++ [(x, lbind_typ T)] ++ D1R) (D2L ++ [(x, lbind_typ T)] ++ D2R).
Proof.
  induction D1L; intros D1R D2L D2R x T OK P; simpl_env in *; auto.
  Case "emtpy".
    apply permute_cons; auto.
  Case "cons".
  destruct a. destruct l. simpl_env in *.
  inversion P.
  subst.
  lapply (lenv_mid_two DL (a, lbind_typ t) DR D2L D2R). intros.
  destruct H as [LEFT | RIGHT]. simpl_env in H3. auto.
  destruct LEFT as [F12 [Q1 Q2]].
  subst.  simpl_env in *.
  apply permute_cons. rewrite_env ((DL ++ F12) ++ [(x, lbind_typ T)] ++ D2R).
  apply IHD1L; auto. simpl_env. auto.
  eapply ok_remove_head. apply OK. simpl_env. auto.
  destruct RIGHT as [F21 [Q1 Q2]].
  subst. simpl_env in *.
  rewrite_env ((D2L ++ [(x, lbind_typ T)] ++ F21) ++ [(a, lbind_typ t)] ++ DR).
  apply permute_cons. simpl_env. apply IHD1L; auto.
  eapply ok_remove_head. apply OK.
  inversion OK. subst.
  apply ok_exchange. simpl. apply ok_cons. apply (ok_lenv_permute (D1L ++ D1R)).
  eapply ok_remove_mid. simpl_env in H2. apply H2. auto.
  rewrite <- (dom_permute (D1L ++ D1R)).
  rewrite dom_concat in *. simpl_env  in *. fsetdec. auto.
Qed.

Lemma permute_sym: forall D1 D2,
  ok D1 ->
  permute D1 D2 ->
  permute D2 D1.
Proof.
  induction D1; intros D2 OK PERM.
  inversion PERM. apply permute_empty.
  inversion PERM. subst. 
  rewrite_env (lempty ++ [(x, lbind_typ T)] ++ D1).
  apply permute_weakening; auto. inversion OK.
  subst. apply ok_exchange. simpl. apply ok_cons. apply (ok_lenv_permute D1); auto.
  rewrite <- (dom_permute D1). auto. auto. 
  simpl_env. apply IHD1. auto. inversion OK; auto. auto.
Qed.


Lemma lenv_split_permute: forall E D1 D2 D3,
  lenv_split E D1 D2 D3 ->
  permute D3 (D1 ++ D2).
Proof.
  intros E D1 D2 D3 S.
  induction S; auto.
  simpl_env. apply permute_empty.
  rewrite_env (lempty ++ [(x, lbind_typ T)] ++ (D1 ++ D2)).
  apply permute_cons. simpl_env. auto.
  apply permute_cons. auto.
Qed.


Lemma lenv_split_exists_permute: forall E D1 D2 D3 DX,
  lenv_split E D1 D2 D3 ->
  permute D3 DX ->
  exists D1P, exists D2P,
    permute D1 D1P /\
    permute D2 D2P /\
    lenv_split E D1P D2P DX.
Proof.
  intros E D1 D2 D3 DX.
  intros S.
  generalize dependent DX.
  induction S; intros DX PERM.
  Case "emtpy".
    inversion PERM.
    exists lempty. exists lempty.
    repeat split; try apply permute_empty; try apply lenv_split_empty. auto.
  Case "left".
    inversion PERM.
    subst.  
    lapply (IHS (DL ++ DR)); auto.
    intros EX.
    destruct EX as [D1P [D2P [PERM1 [PERM2 S2]]]].
    lapply (lenv_split_cases2 E DL D1P D2P DR); intros; auto.
    destruct H2 as [D1l [D1R [D2L [D2R [S3 [S4 [Q1 Q2]]]]]]].
    subst.  
    exists (D1l ++ [(x, lbind_typ T)] ++ D1R).
    exists (D2L ++ D2R).
    repeat split; auto.
    apply permute_cons. auto.
    apply lenv_split_weakening1. auto. auto. auto.
    apply wf_lenv_lin_weakening. auto. eapply wf_env_split0. apply S2. auto.
    rewrite (dom_permute D3 (DL ++ DR)) in H0. auto. auto.
  Case "right".
    inversion PERM.
    subst.
    lapply (IHS (DL ++ DR)); auto.
    intros EX.
    destruct EX as [D1P [D2P [PERM1 [PERM2 S2]]]].
    lapply (lenv_split_cases2 E DL D1P D2P DR); intros; auto.
    destruct H2 as [D1l [D1R [D2L [D2R [S3 [S4 [Q1 Q2]]]]]]].
    subst.
    exists (D1l ++ D1R).
    exists (D2L ++ [(x, lbind_typ T)] ++ D2R).
    repeat split; auto.
    apply permute_cons; auto.
    apply lenv_split_weakening2; auto.
    apply wf_lenv_lin_weakening; auto. eapply wf_env_split0; eauto.
    rewrite (dom_permute D3 (DL ++ DR)) in H0; auto.
Qed.
    
Lemma typing_permute: forall E D1 D2 e t,
  typing E D1 e t ->
  permute D1 D2 ->
  typing E D2 e t.
Proof.
  intros E D1 D2 e t TYP PERM.
  generalize dependent D2.
  induction TYP; intros DX PERM.
  inversion PERM. subst.
  apply typing_var; auto.
  inversion PERM. inversion H4. subst.
  destruct DL; destruct DR; subst; simpl_env in *.
  apply typing_lvar; auto.
  inversion H5. inversion H5.
  inversion H5.
  Case "abs".
    pick fresh x and apply typing_abs.
    auto. apply H1; auto. intros. lapply H2; intros; auto. subst.
    inversion PERM; auto.
  Case "labs".
    pick fresh x and apply typing_labs.
    auto.
    apply (H1 x); auto.
    rewrite_env (lempty ++ [(x, lbind_typ T1)] ++ DX).
    apply permute_cons. simpl_env. auto.
    intros. lapply H2. intros. subst. inversion PERM. auto. auto.
  Case "app".
    assert (exists D1P, exists D2P,
    permute D1 D1P /\
    permute D2 D2P /\
    lenv_split E D1P D2P DX).
    eapply lenv_split_exists_permute; auto. apply H. auto.
    destruct H0 as [D1P [D2P [PERM2 [PERM3 S]]]].
    apply (typing_app T1 K E D1P D2P DX); auto.
  Case "tabs".
    pick fresh X and apply typing_tabs.
    auto.
    apply (H1 X); auto.
  Case "tapp".
    eapply typing_tapp; eauto.
Qed.

Lemma ok_from_wf_lenv: forall E D,
  wf_lenv E D ->
  ok D.
Proof.
  induction D; intros; auto.
  destruct a.
  inversion H; auto.
Qed.

Lemma typing_split: forall E D3 e T D1 D2,
  typing E (D1 ++ D2) e T ->
  lenv_split E D1 D2 D3 ->
  typing E D3 e T.
Proof.
  intros.
  apply (typing_permute E (D1 ++ D2) D3).
  auto.
  apply permute_sym. eapply ok_from_wf_lenv. eapply wf_env_split0. apply H0.
  eapply lenv_split_permute. apply H0.
Qed.
  
Lemma wf_lenv_split_both: forall E D1 D2 D3,
  lenv_split E D1 D2 D3 ->
  wf_lenv E (D1 ++ D2).
Proof.
  intros E D1 D2 D3 S.
  induction S; simpl_env in *; auto.
  Case "left".
    apply wf_lenv_typ; auto. rewrite (dom_lenv_split E D1 D2 D3) in H0. auto. auto.
  Case "right".
    apply wf_lenv_lin_weakening; auto.
    rewrite (dom_lenv_split E D1 D2 D3) in H0. auto. auto.
Qed.

Lemma subst_tlb_identity: forall D X T,
  X `notin` fv_lenv D ->
  D = (map (subst_tlb X T) D).
Proof.
  intros. induction D.
  simpl. auto.
  destruct a. destruct l.
  simpl. simpl in H. rewrite <- IHD. 
  rewrite <- subst_tt_fresh. auto.
  fsetdec. fsetdec.
Qed.

Lemma preservation : forall E D e e' T,
  typing E D e T ->
  red e e' ->
  typing E D e' T.
Proof with simpl_env; eauto.
  intros E D e e' T Typ. 
  generalize dependent e'.
  induction Typ; intros e' Red; try solve [ inversion Red; subst; eauto ].
  Case "typing_app".
    inversion Red; subst...
    inversion Typ1. subst.
    pick fresh x.
    rewrite (subst_ee_intro x).
    assert (D2 = lempty).
    apply (value_nonlin_inversion E D2 e2 T1); auto.
    subst D2.
      lapply (H11 x). intros.
      assert (D1 = D3).
      apply (lenv_split_empty2 E D1 D3). auto. subst D1.
      rewrite_env (empty ++ E).
      eapply typing_through_subst_ee1. simpl_env. apply (H11 x). fsetdec.
      auto. auto. fsetdec. fsetdec.

    subst.
    pick fresh x.
    rewrite (subst_ee_intro x).
    apply (typing_split E D3 (subst_ee x e2 (open_ee e0 x)) T2 D2 D1).
    rewrite_env (lempty ++ D2 ++ D1).
    apply (typing_through_subst_ee2 E lempty x T1 D1).
    simpl_env. apply H11; auto. auto.
    simpl_env. eapply wf_lenv_split_both. eapply lenv_split_commute. apply H. 
    auto. apply lenv_split_commute. auto. fsetdec.
  Case "typing_tapp".
    inversion Red; subst...
      inversion Typ. subst.
      pick fresh X.
      lapply (H9 X). intros.
      rewrite (subst_te_intro X)...
      rewrite (subst_tt_intro X)...
      rewrite_env (map (subst_tb X T) empty ++ E).
      rewrite (subst_tlb_identity D X T).
      apply (typing_through_subst_te K)...
      fsetdec. fsetdec.
Qed.


(* ********************************************************************** *)
(** * #<a name="progress"></a># Progress *)


(* ********************************************************************** *)
(** ** Canonical forms (14) *)

Lemma canonical_form_abs : forall e K U1 U2,
  value e ->
  typing empty lempty e (typ_arrow K U1 U2) ->
  exists K1, exists V, exists e1, (e = exp_abs K1 V e1) /\ (K = kn_nonlin -> K1 = kn_nonlin).
Proof.
  intros e K U1 U2 Val Typ.
  remember empty as E.
  remember lempty as D.
  remember (typ_arrow K U1 U2) as T.
  revert U1 U2 HeqT HeqE HeqD.
  induction Typ; intros U1 U2 EQT EQE EQD; subst.
    inversion Val.
    inversion Val.
    inversion EQT. subst. inversion Val. subst. 
    exists K. exists U1. exists e1. tauto.
    inversion EQT. subst. inversion Val. subst.
    exists K. exists U1. exists e1. tauto.
    inversion Val.
    inversion EQT.
    inversion Val.
Qed.

Lemma canonical_form_tabs : forall e U1 U2,
  value e ->
  typing empty lempty e (typ_all U1 U2) ->
  exists V, exists e1, e = exp_tabs V e1.
Proof.
  intros e U1 U2 Val Typ.
  remember empty as E.
  remember (typ_all U1 U2) as T.
  revert U1 U2 HeqT HeqT.
  induction Typ; intros U1 U2 EQT EQE; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
Qed.

(* ********************************************************************** *)
(** ** Progress (16) *)

Lemma progress : forall e T,
  typing empty lempty e T ->
  value e \/ exists e', red e e'.
Proof with eauto.
  intros e T Typ.
  remember empty as E. remember lempty as D. generalize dependent HeqE.
  generalize dependent HeqD.
  assert (Typ' : typing E D e T)...
  induction Typ; intros EQD EQE; subst...
  Case "typing_var".
    inversion H0.
  Case "typing_lvar".
    inversion EQD.
  Case "typing_abs".
    left. apply value_abs. eapply expr_from_typing. apply Typ'.
  Case "typing_labs".
    left. apply value_abs. eapply expr_from_typing. apply Typ'.
  Case "typing_app".
    right.
    inversion H; subst.
    destruct IHTyp1 as [Val1 | [e1' Rede1']]...
    SCase "Val1".
      destruct IHTyp2 as [Val2 | [e2' Rede2']]...
      SSCase "Val2".
        destruct (canonical_form_abs _ _ _ _ Val1 Typ1) as [K1 [S [e3 [EQE EQK]]]].
        subst.
        exists (open_ee e3 e2)...
        auto.  apply red_abs. eapply expr_from_typing. apply Typ1. auto.
    exists (exp_app e1' e2).
    apply red_app_1; auto. eapply expr_from_typing. apply Typ2.
  Case "typing_tabs".
    left. apply value_tabs. eapply expr_from_typing. apply Typ'.
  Case "typing_tapp".
    right.
    destruct IHTyp as [Val1 | [e1' Rede1']]...
    SCase "Val1".
      destruct (canonical_form_tabs _ _ _ Val1 Typ) as [S [e3 EQ]].
      subst.
      exists (open_te e3 T)...
      apply red_tabs; auto. eapply expr_from_typing. apply Typ. 
      eapply type_from_wf_typ. apply H.
    SCase "e1' Rede1'".
      exists (exp_tapp e1' T)...
      apply red_tapp. eapply type_from_wf_typ. apply H. auto.
Qed.

