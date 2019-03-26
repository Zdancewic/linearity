(** Administrative lemmas for ?.

    Table of contents:
      - #<a href="##wft">Properties of wf_typ</a>#
      - #<a href="##oktwft">Properties of wf_env and wf_typ</a>#
      - #<a href="##okt">Properties of wf_env</a>#
      - #<a href="##subst">Properties of substitution</a>#
      - #<a href="##regularity">Regularity lemmas</a>#
      - #<a href="##auto">Automation</a># *)

Require Export Concur_Infrastructure.
Require Export Extra.
Require Import Omega.

(*Axiom skip : False.
Ltac skip := assert False; [ apply skip | contradiction ].*)

(* ********************************************************************** *)
(** * #<a name="wft"></a># Properties of [wf_typ] and [wf_proto] *)

(* These are all going to be trivial for now... *)

Lemma type_from_wf_typ : forall E T,
  wf_typ E T -> type T.
Proof.
  auto.
Qed.

Lemma wf_typ_weakening : forall T E F G,
  wf_typ (G ++ E) T ->
  uniq (G ++ F ++ E) ->
  wf_typ (G ++ F ++ E) T.
Proof with simpl_env; eauto.
  auto.
Qed.

Lemma wf_typ_weaken_head : forall T E F,
  wf_typ E T ->
  uniq (F ++ E) ->
  wf_typ (F ++ E) T.
Proof.
  auto.
Qed.

(*Lemma wf_typ_rebind_chan : forall E T C T',
  wf_typ E T ->
  wf_proto E T' ->
  wf_typ (List.map (rebind_chan C T') E) T.
Proof with simpl_env; eauto using wf_typ_weaken_head, type_from_wf_typ.
  intros E T Z T' Hwft Hwfp.
  induction Hwft...
Qed.*)

Lemma wf_typ_strengthening : forall E F x T,
 wf_typ (F ++ [(x, bind_kn)] ++ E) T ->
 wf_typ (F ++ E) T.
Proof with simpl_env; eauto.
  auto.
Qed.

Lemma wf_typ_from_wf_proto : forall E T,
  wf_proto E T -> wf_typ E T.
Proof.
  auto.
Qed.

Lemma type_from_wf_proto : forall E T,
  wf_proto E T -> type T.
Proof.
  intros.
  apply type_from_wf_typ with (E := E).
  apply wf_typ_from_wf_proto.
  auto.
Qed.

Lemma wf_proto_weakening : forall T E F G,
  wf_proto (G ++ E) T ->
  uniq (G ++ F ++ E) ->
  wf_proto (G ++ F ++ E) T.
Proof with simpl_env; eauto.
  intros. induction H; auto.
Qed.

Lemma wf_proto_weaken_head : forall T E F,
  wf_proto E T ->
  uniq (F ++ E) ->
  wf_proto (F ++ E) T.
Proof.
  intros. induction H; auto.
Qed.

Lemma wf_proto_strengthening : forall E F x T,
 wf_proto (F ++ [(x, bind_kn)] ++ E) T ->
 wf_proto (F ++ E) T.
Proof with simpl_env; eauto.
  intros. induction H; auto.
Qed.


(* ********************************************************************** *)
(** * #<a name="oktwft"></a># Properties of [wf_env] and [wf_typ] *)

Lemma uniq_from_wf_env : forall E,
  wf_env E ->
  uniq E.
Proof.
  intros E H; induction H; auto.
Qed.

Lemma uniq_from_wf_lenv : forall E D,
  wf_lenv E D ->
  uniq D.
Proof.
  induction D; intros; auto.
  destruct a.
  inversion H; auto.
Qed.

Lemma uniq_from_wf_cenv : forall E Q,
  wf_cenv E Q ->
  uniq Q.
Proof.
  induction Q; intros; auto.
  destruct a.
  inversion H; auto.
Qed.

(** We add [uniq_from_wf_env] as a hint here since it helps blur the
    distinction between [wf_env] and [uniq] in proofs.  The lemmas in
    the [Environment] library use [uniq], whereas here we naturally have
    (or can easily show) the stronger [wf_env].  Thus,
    [uniq_from_wf_env] serves as a bridge that allows us to use the
    environments library. *)

Hint Resolve uniq_from_wf_env.
Hint Resolve uniq_from_wf_lenv.
Hint Resolve uniq_from_wf_cenv.

Lemma wf_proto_from_wf_cenv : forall E Q1 Q2 X d T,
  wf_cenv E (Q1 ++ [(X, cbind_proto d T)] ++ Q2) ->
  wf_proto E T.
Proof with auto.
  intros. induction Q1; simpl_env in *.
  inversion H; subst...
  destruct a as [Y [d0 T0]]. inversion H; subst.
  simpl_env in *. apply IHQ1...
Qed.

(* ********************************************************************** *)
(** * #<a name="uniqt"></a># Properties of [wf_env] and [wf_lenv] *)

(** These properties are analogous to the properties that we need to
    show for the subtyping and typing relations. *)

Lemma wf_env_strengthening : forall x E F,
  wf_env (F ++ [(x, bind_kn)] ++ E) ->
  wf_env (F ++ E).
Proof with eauto using wf_proto_strengthening.
  induction F; intros Wf_env; inversion Wf_env; subst; simpl_env in *...
Qed.

Lemma wf_env_strengthening_tail : forall E F,
  wf_env (F ++ E) ->
  wf_env E.
Proof.
  intros E F H.
  induction F; auto.
    rewrite_env ([a] ++ (F ++ E)) in H.
    apply IHF.
      inversion H; auto.
Qed.

Lemma wf_env_from_wf_lenv : forall E D,
  wf_lenv E D ->
  wf_env E.
Proof.
  intros E D WFL.
  induction WFL; auto.
Qed.

Lemma wf_env_from_wf_cenv : forall E Q,
  wf_cenv E Q ->
  wf_env E.
Proof.
  intros E Q WFL.
  induction WFL; auto.
Qed.

(*Lemma wf_env_from_wf_cenv_acc: forall E Q1 Q2 Q3,
  wf_cenv_acc E Q1 Q2 Q3 ->
  wf_env E.
Proof with auto.
  intros. induction H...
Qed.

Lemma wf_cenv_acc_wf_left: forall E Q1 Q2 Q3,
  wf_cenv_acc E Q1 Q2 Q3 ->
  wf_cenv E Q1.
Proof with auto.
  intros. induction H...
    constructor... apply dom_wf_cenv_acc in H. fsetdec.
Qed.

Lemma wf_cenv_acc_wf_right: forall E Q1 Q2 Q3,
  wf_cenv_acc E Q1 Q2 Q3 ->
  wf_cenv E Q2.
Proof with auto.
  intros. induction H...
Qed.

Lemma wf_cenv_acc_wf: forall E Q1 Q2 Q3,
  wf_cenv_acc E Q1 Q2 Q3 ->
  wf_cenv E Q3.
Proof with auto.
  intros E Q1. induction Q1; intros; inversion H; subst...
    constructor... apply IHQ1 with (Q2 := Q2)...
    apply IHQ1 in H2. eapply wf_cenv_rebind_chan; eauto.
    apply IHQ1 in H2. eapply wf_cenv_rebind_chan; eauto.
Qed.*)

Lemma wf_env_from_wf_cenvs : forall E Qs,
  wf_cenvs E Qs ->
  wf_env E.
Proof with auto.
  intros E Q WFC. inversion WFC; subst...
  induction H...
    apply wf_env_from_wf_cenv in H...
    apply IHcenv_split_multi1. econstructor. eauto.
Qed.

Lemma wf_env_from_vwf_envs : forall E Q D,
  vwf_envs E Q D ->
  wf_env E.
Proof.
  intros E Q D VWF.
  induction VWF; auto.
    eapply wf_env_from_wf_cenv; eauto.
Qed.

Lemma wf_lenv_from_vwf_envs : forall E Q D,
  vwf_envs E Q D ->
  wf_lenv E D.
Proof.
  intros E Q D VWF.
  induction VWF; auto.
    constructor. eapply wf_env_from_wf_cenv; eauto.
Qed.

Lemma wf_cenv_from_vwf_envs : forall E Q D,
  vwf_envs E Q D ->
  wf_cenv E Q.
Proof.
  intros E Q D VWF.
  induction VWF; auto.
Qed.

Lemma wf_cenv_eq_app: forall E Q1 Q2 Q1' Q2' X d T,
  wf_cenv E (Q1 ++ [(X, cbind_proto d T)] ++ Q2) ->
  wf_cenv E (Q1' ++ [(X, cbind_proto d T)] ++ Q2') ->
  Q1 ++ [(X, cbind_proto d T)] ++ Q2 = Q1' ++ [(X, cbind_proto d T)] ++ Q2' ->
  Q1 = Q1' /\ Q2 = Q2'.
Proof with auto.
  intros E Q1.
  induction Q1; intros; destruct Q1';
      simpl_env in *; simpl in H1; inversion H1; subst.
    split...
    inversion H0; subst. simpl_env in H9. fsetdec.
    inversion H; subst. simpl_env in H9. fsetdec.
    inversion H0. inversion H. subst. simpl_env in *.
      lapply (IHQ1 Q2 Q1' Q2' X d T H12 H5)... intros.
      intuition. subst...
Qed.

Lemma wf_lenv_strengthening : forall x E F D,
  wf_lenv (F ++ [(x, bind_kn)] ++ E) D ->
  wf_lenv (F ++ E) D.
Proof.
  intros x E F D WFL.
  remember (F ++ [(x, bind_kn)] ++ E) as E0.
  generalize dependent F.
  (wf_lenv_cases (induction WFL) Case); intros F EQ; subst.
  Case "wf_lenv_empty".
    apply wf_lenv_empty; auto. 
      eapply wf_env_strengthening; eauto.
  Case "wf_lenv_typ".
    apply wf_lenv_typ; auto.
Qed.

Lemma wf_cenv_strengthening : forall x E F Q,
  wf_cenv (F ++ [(x, bind_kn)] ++ E) Q ->
  wf_cenv (F ++ E) Q.
Proof.
  intros x E F Q WFL.
  remember (F ++ [(x, bind_kn)] ++ E) as E0.
  generalize dependent F.
  (wf_cenv_cases (induction WFL) Case); intros F EQ; subst.
  Case "wf_cenv_empty".
    apply wf_cenv_empty; auto. 
      eapply wf_env_strengthening; eauto.
  Case "wf_cenv_proto".
    apply wf_cenv_proto; auto.
    eapply wf_proto_strengthening; eauto.
Qed.

Lemma vwf_envs_strengthening : forall x E F Q D,
  vwf_envs (F ++ [(x, bind_kn)] ++ E) Q D ->
  vwf_envs (F ++ E) Q D.
Proof.
  intros x E F Q D VWF.
  remember (F ++ [(x, bind_kn)] ++ E) as E0.
  generalize dependent F.
  (vwf_envs_cases (induction VWF) Case); intros F EQ; subst.
  Case "vwf_envs_empty".
    apply vwf_envs_empty; auto. 
      eapply wf_cenv_strengthening; eauto.
  Case "vwf_envs_typ".
    apply vwf_envs_typ; auto.
Qed.

Lemma wf_lenv_disjoint: forall G D,
  wf_lenv G D ->
  disjoint G D.
Proof.
  induction D; simpl_env; intros.
  SCase "nil".
    unfold disjoint. fsetdec.
  SCase "con".
    inversion H; subst.
    solve_uniq.
Qed.

Lemma wf_cenv_disjoint: forall G Q,
  wf_cenv G Q ->
  disjoint G Q.
Proof.
  induction Q; simpl_env; intros.
  SCase "nil".
    unfold disjoint. fsetdec.
  SCase "con".
    inversion H; subst.
    solve_uniq.
Qed.

Lemma vwf_envs_pack : forall E Q D,
  wf_lenv E D ->
  wf_cenv E Q ->
  disjoint D Q ->
  vwf_envs E Q D.
Proof with auto.
  intros E Q D WFL WFC DJ.
  induction D...
  simpl_env in *. destruct a. destruct l.
  constructor; inversion WFL; subst...
    apply IHD...
      unfold disjoint in *. simpl_env in DJ. fsetdec.
    unfold disjoint in DJ. simpl_env in DJ. fsetdec.
Qed.

Lemma vwf_envs_unpack : forall E Q D,
  vwf_envs E Q D ->
  wf_lenv E D /\ wf_cenv E Q /\ disjoint D Q.
Proof with auto.
  intros. induction D; repeat split; inversion H; subst; simpl_env in *...
    constructor. apply wf_env_from_wf_cenv with (Q := Q)...
    apply IHD in H2. destruct H2 as [H0 [H1 H2]]. constructor...
    apply IHD in H2. destruct H2 as [H0 [H1 H2]]...
    apply IHD in H2. destruct H2 as [H0 [H1 H2]].
      unfold disjoint in *. simpl_env. fsetdec.
Qed.    

Lemma wf_lenv_strengthen_lenv : forall E D1 D2,
  wf_lenv E (D1 ++ D2) ->
  wf_lenv E D1 /\ wf_lenv E D2.
Proof with auto.
  intros. induction D1; split.
    inversion H; constructor...
    eapply wf_env_from_wf_lenv; eauto.
    inversion H; subst; simpl_env in *...
    simpl_env in *... destruct a as [X b].
    inversion H; subst; constructor...
    inversion H; subst; simpl_env in *.
    apply IHD1 in H3; intuition.
    inversion H; subst. apply IHD1 in H2.
    destruct H2...
Qed.

Lemma vwf_envs_strengthen_lenv : forall E Q D1 D2,
  vwf_envs E Q (D1 ++ D2) ->
  vwf_envs E Q D1 /\ vwf_envs E Q D2.
Proof.
  intros. apply vwf_envs_unpack in H. destruct H as [WFL [WFC DJ]].
  apply wf_lenv_strengthen_lenv in WFL. destruct WFL as [WFL1 WFL2].
  split; apply vwf_envs_pack; auto;
    unfold disjoint in *; simpl_env in DJ; fsetdec.
Qed.

Lemma wf_cenv_rebind_chan : forall E Q1 Q2 X d1 T1 d2 T2,
  wf_cenv E (Q1 ++ [(X, cbind_proto d1 T1)] ++ Q2) ->
  wf_proto E T2 ->
  wf_cenv E (Q1 ++ [(X, cbind_proto d2 T2)] ++ Q2).
Proof with auto.
  intros E Q1 Q2 X d1 T1 d2 T2 Hwfl Hwfp.
  induction Q1; simpl_env in *.
    inversion Hwfl. constructor...
    destruct a as [Y [d T]]. inversion Hwfl; subst.
    simpl_env in *. apply IHQ1 in H4.
    constructor...
Qed.

Lemma vwf_envs_rebind_chan : forall E Q1 Q2 X d1 T1 d2 T2 D,
  vwf_envs E (Q1 ++ [(X, cbind_proto d1 T1)] ++ Q2) D ->
  wf_proto E T2 ->
  vwf_envs E (Q1 ++ [(X, cbind_proto d2 T2)] ++ Q2) D.
Proof with auto.
  intros. apply vwf_envs_unpack in H. destruct H as [WFL [WFC DJ]].
  apply wf_cenv_rebind_chan with (d2 := d2) (T2 := T2) in WFC...
  apply vwf_envs_pack... unfold disjoint in *. simpl_env in *. fsetdec.
Qed.


(* ********************************************************************** *)
(** * #<a name="subst"></a># Environment is unchanged by substitution for a fresh name *)

(* Nothing here at present... *)

(* Basic properties of the env_split relations *)

Lemma dom_lenv_split: forall G Q E1 E2 E3,
  lenv_split G Q E1 E2 E3  -> 
  dom E3 [=] dom E1 `union` dom E2.
Proof.
  intros G Q E1 E2 E3 S.
  induction S; simpl; try fsetdec. 
Qed.

Lemma dom_cenv_split_exp: forall G E1 E2 E3,
  cenv_split_exp G E1 E2 E3  -> 
  dom E3 [=] dom E1 `union` dom E2.
Proof.
  intros E1 E2 E3 G S.
  induction S; simpl; try fsetdec. 
Qed.

Lemma dom_cenv_split_proc: forall G E1 E2 E3 Z,
  cenv_split_proc G E1 E2 E3 Z -> 
  dom E3 [=] dom E1 `union` dom E2.
Proof.
  intros G E1 E2 E3 Z S.
  induction S; try apply dom_cenv_split_exp in H; simpl; try fsetdec. 
Qed.

Lemma dom_cenv_split_proc_some: forall G E1 E2 E3 X,
  cenv_split_proc G E1 E2 E3 (Some X) ->
  X `in` dom E1 /\ X `in` dom E2.
Proof with auto.
  intros. remember (Some X) as Z.
  induction H; inversion HeqZ; subst...
    apply IHcenv_split_proc in H3. simpl_env. fsetdec.
    apply IHcenv_split_proc in H3. simpl_env. fsetdec.
    simpl_env. fsetdec.
    simpl_env. fsetdec.
Qed.

Lemma doms_append: forall A L1 L2,
  doms A (L1 ++ L2) [=] doms A L1 `union` doms A L2.
Proof.
  intros. induction L1. simpl. fsetdec.
  rewrite_env (a :: (L1 ++ L2)). simpl. rewrite IHL1. fsetdec.
Qed.

Lemma dom_cenv_split_multi: forall G Qs Q Z,
  cenv_split_multi G Qs Q Z ->
  dom Q [=] doms cbinding Qs.
Proof.
  intros. induction H.
    simpl. fsetdec.
    simpl. fsetdec.
    rewrite doms_append. apply dom_cenv_split_proc in H1.
      rewrite <- IHcenv_split_multi1.
      rewrite <- IHcenv_split_multi2.
      fsetdec.
Qed.

Lemma lenv_split_commute: forall G Q E1 E2 E3,
  lenv_split G Q E1 E2 E3 ->
  lenv_split G Q E2 E1 E3.
Proof.
  intros G Q E1 E2 E3 S.
  induction S; auto.
Qed.

Lemma lenv_agree_commute: forall G Q E1 E2,
  lenv_agree G Q E1 E2 ->
  lenv_agree G Q E2 E1.
Proof.
  intros. induction H; auto.
Qed.

Lemma lenv_split_left_id: forall E Q D,
  vwf_envs E Q D ->
  lenv_split E Q lempty D D.
Proof with auto.
  intros. induction D...
    constructor... apply vwf_envs_unpack in H. intuition...
    simpl_env in *. destruct a as [x b]. destruct b.
      inversion H; subst.
      constructor...
Qed.

Lemma lenv_split_right_id: forall E Q D,
  vwf_envs E Q D ->
  lenv_split E Q D lempty D.
Proof with auto.
  intros. apply lenv_split_commute.
  apply lenv_split_left_id...
Qed.

Lemma cenv_split_exp_commute: forall G E1 E2 E3,
  cenv_split_exp G E1 E2 E3 ->
  cenv_split_exp G E2 E1 E3.
Proof.
  intros G E1 E2 E3 S.
  induction S; auto.
Qed.

Lemma cenv_split_proc_commute: forall G E1 E2 E3 Z,
  cenv_split_proc G E1 E2 E3 Z ->
  cenv_split_proc G E2 E1 E3 Z.
Proof.
  intros G E1 E2 E3 Z S.
  induction S; try apply cenv_split_exp_commute in H; auto.
Qed.

Lemma cenv_agree_commute: forall G E1 E2,
  cenv_agree G E1 E2 ->
  cenv_agree G E2 E1.
Proof.
  intros. induction H; auto.
Qed.

Lemma cenv_split_exp_left_id: forall E Q,
  wf_cenv E Q ->
  cenv_split_exp E cempty Q Q.
Proof with auto.
  intros. induction Q...
    constructor... apply wf_env_from_wf_cenv in H...
    simpl_env in *. destruct a as [x b]. destruct b.
      inversion H; subst.
      constructor...
Qed.

Lemma cenv_split_exp_right_id: forall E Q,
  wf_cenv E Q ->
  cenv_split_exp E Q cempty Q.
Proof with auto.
  intros. apply cenv_split_exp_commute.
  apply cenv_split_exp_left_id...
Qed.

Lemma cenv_split_proc_left_id: forall E Q,
  wf_cenv E Q ->
  cenv_split_proc E cempty Q Q None.
Proof with auto.
  intros. induction Q...
    constructor... apply wf_env_from_wf_cenv in H...
    simpl_env in *. destruct a as [x b]. destruct b.
      inversion H; subst.
      constructor...
Qed.

Lemma cenv_split_proc_right_id: forall E Q,
  wf_cenv E Q ->
  cenv_split_proc E Q cempty Q None.
Proof with auto.
  intros. apply cenv_split_proc_commute.
  apply cenv_split_proc_left_id...
Qed.

Lemma lenv_split_empty_left: forall G Q E F,
  lenv_split G Q lempty E F ->
  E = F.
Proof.
  induction E; intros F H; inversion H; auto.
  Case "con".
    rewrite (IHE D3); auto.
Qed.

Lemma lenv_split_empty_right: forall G Q E F,
  lenv_split G Q E lempty F ->
  E = F.
Proof.
  intros. 
  eapply lenv_split_empty_left. 
  eapply lenv_split_commute; eauto.
Qed.

Lemma cenv_split_exp_empty_left: forall G E F,
  cenv_split_exp G cempty E F ->
  E = F.
Proof.
  induction E; intros F H; inversion H; auto.
  Case "con".
    rewrite (IHE Q3); auto.
Qed.

Lemma cenv_split_exp_empty_right: forall G E F,
  cenv_split_exp G E cempty F ->
  E = F.
Proof.
  intros. 
  eapply cenv_split_exp_empty_left. 
  eapply cenv_split_exp_commute; eauto.
Qed.

Lemma cenv_split_proc_empty_left: forall G E F Z,
  cenv_split_proc G cempty E F Z ->
  E = F /\ Z = None.
Proof with auto.
  induction E; intros F Z H; inversion H; auto.
  Case "con".
    lapply (IHE Q3 Z)... intros. intuition. subst...
Qed.

Lemma cenv_split_proc_empty_right: forall G E F Z,
  cenv_split_proc G E cempty F Z ->
  E = F /\ Z = None.
Proof.
  intros. 
  eapply cenv_split_proc_empty_left. 
  eapply cenv_split_proc_commute; eauto.
Qed.

Lemma cenvs_split_simple_commute: forall G E1 E2 E3,
  cenvs_split_simple G E1 E2 E3 ->
  cenvs_split_simple G E2 E1 E3.
Proof with auto.
  intros. induction H...
Qed.

Lemma cenvs_split_commute: forall G E1 E2 E3,
  cenvs_split G E1 E2 E3 ->
  cenvs_split G E2 E1 E3.
Proof with auto.
  intros. induction H...
    econstructor; eauto.
      apply cenvs_split_simple_commute...
Qed.

Lemma cenv_split_multi_empty: forall E Q Z,
  cenv_split_multi E lcempty Q Z ->
  Q = cempty.
Proof with auto.
  intros. remember lcempty as Qs. induction H; subst...
    symmetry in HeqQs. apply nil_cons in HeqQs. intuition.
    apply app_eq_nil in HeqQs. intuition. subst. inversion H1...
Qed.

(* No longer true - could be a string of cemptys
Lemma cenvs_split_multi_empty: forall E Qs,
  cenvs_split_multi E lcempty Qs ->
  Qs = lcempty.
Proof with auto.
  intros. inversion H; subst...
    apply app_eq_nil in H0. intuition. subst.
      apply cenv_split_multi_not_empty in H2. intuition.
Qed.*)

Lemma cenv_split_multi_single: forall E Q1 Q2 Z,
  cenv_split_multi E [Q1] Q2 Z->
  Q1 = Q2 /\ Z = None.
Proof with auto.
  intros. remember [Q1] as Qs. induction H...
    inversion HeqQs...
    inversion HeqQs...
    apply app_eq_unit in HeqQs.
      destruct HeqQs as [[Eq1 Eq2] | [Eq1 Eq2]]; subst.
        apply cenv_split_multi_empty in H. subst.
          lapply IHcenv_split_multi2... intros. destruct H. subst.
          apply cenv_split_proc_empty_left in H1...
        apply cenv_split_multi_empty in H0. subst.
          lapply IHcenv_split_multi1... intros. destruct H0. subst.
          apply cenv_split_proc_empty_right in H1...
Qed.

Lemma cenvs_split_simple_empty_left: forall G E F,
  cenvs_split_simple G lcempty E F ->
  E = F.
Proof with auto.
  induction E; intros; inversion H...
    rewrite (IHE Qs3)...
Qed.

Lemma cenvs_split_simple_empty_right: forall G E F,
  cenvs_split_simple G E lcempty F ->
  E = F.
Proof with auto.
  induction E; intros; inversion H...
    rewrite (IHE Qs3)...
Qed.

(* Also no longer true - do we need "list of cempty" predicate?
Lemma cenvs_split_empty_both: forall E Qs,
  cenvs_split E lcempty lcempty Qs ->
  Qs = lcempty.
Proof with auto.
  intros. inversion H; subst...
    apply cenvs_split_simple_empty_left in H1. subst.
      apply cenvs_split_multi_empty in H0...
Qed.

Lemma cenvs_split_empty_left: forall E Qs Q,
  cenvs_split E lcempty [Q] Qs ->
  Qs = [Q].
Proof with auto.
  intros E Qs. induction Qs; intros; inversion H; subst...
    absurd (Qs' = lcempty).
      apply cenvs_split_simple_empty_left in H1; intuition; subst.
        apply symmetry in H2. apply nil_cons in H2...
      inversion H0...
    apply cenvs_split_simple_empty_left in H1; subst.
      inversion H0; subst. apply app_eq_unit in H1. intuition; subst.
        apply cenv_split_multi_not_empty in H6. intuition.
        simpl. apply cenv_split_multi_single in H6. intuition. subst.
          apply cenvs_split_multi_empty in H5. subst...
Qed.

Lemma cenvs_split_empty_right: forall E Qs Q,
  cenvs_split E [Q] lcempty Qs ->
  Qs = [Q].
Proof.
  intros. apply cenvs_split_commute in H.
  apply cenvs_split_empty_left in H. auto.
Qed.*)

Lemma wf_lenv_split: forall G Q D1 D2 D3,
  lenv_split G Q D1 D2 D3  ->
  vwf_envs G Q D3.
Proof.
  intros G Q D1 D2 D3 S.
  (lenv_split_cases (induction S) Case); simpl_env in *; eauto.
Qed.

Lemma wf_lenv_split_left: forall G Q D1 D2 D3,
  lenv_split G Q D1 D2 D3 ->
  vwf_envs G Q D1.
Proof.
  intros G Q D1 D2 D3 S.
  (lenv_split_cases (induction S) Case); auto.
  Case "lenv_split_left".
    apply vwf_envs_typ; auto.
      rewrite (dom_lenv_split E Q D1 D2 D3) in H1; auto.
Qed.

Lemma wf_lenv_split_right: forall G Q D1 D2 D3,
  lenv_split G Q D1 D2 D3 ->
  vwf_envs G Q D2.
Proof.
  intros. 
  eapply wf_lenv_split_left. 
  eapply lenv_split_commute; eauto.
Qed.

Lemma wf_lenv_agree_left: forall G Q D1 D2,
  lenv_agree G Q D1 D2 ->
  vwf_envs G Q D1.
Proof.
  intros. induction H; auto.
Qed.

Lemma wf_lenv_agree_right: forall G Q D1 D2,
  lenv_agree G Q D1 D2 ->
  vwf_envs G Q D2.
Proof.
  intros. induction H; auto.
Qed.

Lemma wf_cenv_split_exp: forall G Q1 Q2 Q3,
  cenv_split_exp G Q1 Q2 Q3  ->
  wf_cenv G Q3.
Proof.
  intros G Q1 Q2 Q3 S.
  (cenv_split_exp_cases (induction S) Case); simpl_env in *; 
    try solve [ eauto | eapply wf_cenv_cbind; eauto ].
Qed.

Lemma wf_cenv_split_exp_left: forall G Q1 Q2 Q3,
  cenv_split_exp G Q1 Q2 Q3 ->
  wf_cenv G Q1.
Proof.
  intros G Q1 Q2 Q3 S.
  (cenv_split_exp_cases (induction S) Case); auto.
  Case "cenv_split_exp_left".
    apply wf_cenv_proto; auto.
      rewrite (dom_cenv_split_exp E Q1 Q2 Q3) in H0; auto.
Qed.

Lemma wf_cenv_split_exp_right: forall G Q1 Q2 Q3,
  cenv_split_exp G Q1 Q2 Q3 ->
  wf_cenv G Q2.
Proof.
  intros. 
  eapply wf_cenv_split_exp_left. 
  eapply cenv_split_exp_commute; eauto.
Qed.

Lemma wf_cenv_split_proc: forall G Q1 Q2 Q3 Z,
  cenv_split_proc G Q1 Q2 Q3 Z ->
  wf_cenv G Q3.
Proof.
  intros G Q1 Q2 Q3 Z S.
  (cenv_split_proc_cases (induction S) Case); simpl_env in *;
    try apply wf_cenv_split_exp in H;
    try solve [ eauto | eapply wf_cenv_cbind; eauto ].
Qed.

Lemma wf_cenv_split_proc_left: forall G Q1 Q2 Q3 Z,
  cenv_split_proc G Q1 Q2 Q3 Z ->
  wf_cenv G Q1.
Proof.
  intros G Q1 Q2 Q3 Z S.
  (cenv_split_proc_cases (induction S) Case); auto.
  Case "cenv_split_proc_left".
    apply wf_cenv_proto; auto.
      rewrite (dom_cenv_split_proc E Q1 Q2 Q3 Z) in H0; auto.
  Case "cenv_split_proc_snksrc".
    apply wf_cenv_proto; auto.
      apply wf_cenv_split_exp_left in H; auto.
      apply dom_cenv_split_exp in H; fsetdec.
  Case "cenv_split_proc_srcsnk".
    apply wf_cenv_proto; auto.
      apply wf_cenv_split_exp_left in H; auto.
      apply dom_cenv_split_exp in H; fsetdec.
Qed.

Lemma wf_cenv_split_proc_right: forall G Q1 Q2 Q3 Z,
  cenv_split_proc G Q1 Q2 Q3 Z ->
  wf_cenv G Q2.
Proof.
  intros. 
  eapply wf_cenv_split_proc_left. 
  eapply cenv_split_proc_commute; eauto.
Qed.

Lemma wf_cenv_split_multi: forall G Qs Q Z,
  cenv_split_multi G Qs Q Z ->
  wf_cenv G Q.
Proof.
  intros. inversion H; subst; auto.
    eapply wf_cenv_split_proc. eauto.
Qed.

Lemma wf_cenvs_split_multi: forall G Qs1 Qs2,
  cenvs_split_multi G Qs1 Qs2 ->
  wf_cenvs G Qs2.
Proof.
  intros. inversion H; subst.
    econstructor; eauto.
    auto.
Qed.

Lemma wf_cenvs_from_single: forall E Q,
  wf_cenv E Q ->
  wf_cenvs E [Q].
Proof with auto.
  intros. econstructor. constructor...
Qed.

Lemma wf_cenvs_to_single: forall E Q,
  wf_cenvs E [Q] ->
  wf_cenv E Q.
Proof with auto.
  intros. inversion H. subst.
  assert (Q = Q0).
    apply cenv_split_multi_single in H0... intuition.
   subst. apply wf_cenv_split_multi in H0...
Qed.

Lemma wf_cenvs_split: forall G Qs1 Qs2 Qs3,
  cenvs_split G Qs1 Qs2 Qs3 ->
  wf_cenvs G Qs3.
Proof.
  intros. inversion H. subst.
  eapply wf_cenvs_split_multi. eauto.
Qed.

Lemma wf_cenv_agree_left: forall G Q1 Q2,
  cenv_agree G Q1 Q2 ->
  wf_cenv G Q1.
Proof.
  intros. induction H; auto.
Qed.

Lemma wf_cenv_agree_right: forall G Q1 Q2,
  cenv_agree G Q1 Q2 ->
  wf_cenv G Q2.
Proof.
  intros. induction H; auto.
Qed.

Lemma lenv_split_agree: forall G Q D1 D2 D3,
  lenv_split G Q D1 D2 D3 ->
  lenv_agree G Q D1 D2.
Proof.
  intros. (lenv_split_cases (induction H) Case);
  try solve [ auto
                 | apply dom_lenv_split in H;
                   constructor; try fsetdec; auto ].
Qed.

Lemma lenv_split_agree_left: forall G Q D1 D2 D3,
  lenv_split G Q D1 D2 D3 ->
  lenv_agree G Q D1 D3.
Proof.
  intros. (lenv_split_cases (induction H) Case);
  try solve [ auto
                 | apply dom_lenv_split in H;
                   constructor; try fsetdec; auto ].
Qed.

Lemma lenv_split_agree_right: forall G Q D1 D2 D3,
  lenv_split G Q D1 D2 D3 ->
  lenv_agree G Q D2 D3.
Proof.
  intros. (lenv_split_cases (induction H) Case);
  try solve [ auto
                 | apply dom_lenv_split in H;
                   constructor; try fsetdec; auto ].
Qed.

Lemma cenv_split_exp_agree: forall G Q1 Q2 Q3,
  cenv_split_exp G Q1 Q2 Q3 ->
  cenv_agree G Q1 Q2.
Proof.
  intros. (cenv_split_exp_cases (induction H) Case);
  try solve [ auto
                 | apply dom_cenv_split_exp in H;
                   constructor; try fsetdec; auto ].
Qed.

Lemma cenv_split_exp_agree_left: forall G Q1 Q2 Q3,
  cenv_split_exp G Q1 Q2 Q3 ->
  cenv_agree G Q1 Q3.
Proof.
  intros. (cenv_split_exp_cases (induction H) Case);
  try solve [ auto
                 | apply dom_cenv_split_exp in H;
                   constructor; try fsetdec; auto ].
Qed.

Lemma cenv_split_exp_agree_right: forall G Q1 Q2 Q3,
  cenv_split_exp G Q1 Q2 Q3 ->
  cenv_agree G Q2 Q3.
Proof.
  intros. (cenv_split_exp_cases (induction H) Case);
  try solve [ auto
                 | apply dom_cenv_split_exp in H;
                   constructor; try fsetdec; auto ].
Qed.

(* These are no longer true!  But I don't think we need them. *)
(*Lemma cenv_split_proc_agree: forall G Q1 Q2 Q3,
  cenv_split_proc G Q1 Q2 Q3 ->
  cenv_agree G Q1 Q2.
Proof with auto.
  intros. (cenv_split_proc_cases (induction H) Case);
  try solve [ auto
                 | apply dom_cenv_split_proc in H;
                   constructor; try fsetdec; auto ].
  constructor; try (apply dom_cenv_split_exp in H; fsetdec)...
    apply cenv_split_exp_agree in H...
  constructor; try (apply dom_cenv_split_exp in H; fsetdec)...
    apply cenv_split_exp_agree in H...
Qed.

Lemma cenv_split_proc_agree_left: forall G Q1 Q2 Q3,
  cenv_split_proc G Q1 Q2 Q3 ->
  cenv_agree G Q1 Q3.
Proof with auto.
  intros. (cenv_split_proc_cases (induction H) Case);
  try solve [ auto
                 | apply dom_cenv_split_proc in H;
                   constructor; try fsetdec; auto ].
  constructor; try (apply dom_cenv_split_exp in H; fsetdec)...
    apply cenv_split_exp_agree_left in H...
  constructor; try (apply dom_cenv_split_exp in H; fsetdec)...
    apply cenv_split_exp_agree_left in H...
Qed.

Lemma cenv_split_proc_agree_right: forall G Q1 Q2 Q3,
  cenv_split_proc G Q1 Q2 Q3 ->
  cenv_agree G Q2 Q3.
Proof with auto.
  intros. (cenv_split_proc_cases (induction H) Case);
  try solve [ auto
                 | apply dom_cenv_split_proc in H;
                   constructor; try fsetdec; auto ].
  constructor; try (apply dom_cenv_split_exp in H; fsetdec)...
    apply cenv_split_exp_agree_right in H...
  constructor; try (apply dom_cenv_split_exp in H; fsetdec)...
    apply cenv_split_exp_agree_right in H...
Qed.*)

Lemma cenv_split_exp_proc: forall G Q1 Q2 Q3,
  cenv_split_exp G Q1 Q2 Q3 ->
  cenv_split_proc G Q1 Q2 Q3 None.
Proof with auto.
  intros. induction H...
Qed.

Lemma cenv_split_proc_exp: forall E Q1 Q2 Q3,
  cenv_split_proc E Q1 Q2 Q3 None ->
  cenv_split_exp E Q1 Q2 Q3.
Proof with auto.
  intros. remember (None:option atom) as Z.
  induction H; inversion HeqZ...
Qed.

Lemma cenv_split_proc_snksrc_exp : forall E X T Q1L Q1R Q2L Q2R Q3L Q3R,
  cenv_split_proc E (Q1L ++ [(X, cbind_proto cdir_snk T)] ++ Q1R)
                              (Q2L ++ [(X, cbind_proto cdir_src T)] ++ Q2R)
                              (Q3L ++ [(X, cbind_proto cdir_both T)] ++ Q3R)
                              (Some X) ->
  cenv_split_exp E (Q1L ++ Q1R) (Q2L ++ Q2R) (Q3L ++ Q3R).
Proof with auto.
  intros. remember (Some X) as Z.
  remember (Q1L ++ [(X, cbind_proto cdir_snk T)] ++ Q1R) as Q1.
  remember (Q2L ++ [(X, cbind_proto cdir_src T)] ++ Q2R) as Q2.
  remember (Q3L ++ [(X, cbind_proto cdir_both T)] ++ Q3R) as Q3.
  generalize dependent Q3R. revert Q3L.
  generalize dependent Q2R. revert Q2L.
  generalize dependent Q1R. revert Q1L.
  generalize dependent X. revert T.
  (cenv_split_proc_cases (induction H) Case); intros; subst.
    Case "cenv_split_proc_empty".
      discriminate HeqZ.
    Case "cenv_split_proc_left".
      destruct Q1L as [ | [X1 [d1 T1]] Q1L ];
          destruct Q3L as [ | [X3 [d3 T3]] Q3L ];
          inversion HeqQ1; inversion HeqQ3; repeat subst;
          simpl_env in *; clear HeqQ1 HeqQ3.
        discriminate H9.
        fsetdec.
        apply dom_cenv_split_proc in H.
          simpl_env in H. fsetdec.
        constructor...
          apply IHcenv_split_proc with (X := X0) (T := T0)...
    Case "cenv_split_proc_right".
      destruct Q2L as [ | [X2 [d2 T2]] Q2L ];
          destruct Q3L as [ | [X3 [d3 T3]] Q3L ];
          inversion HeqQ2; inversion HeqQ3; repeat subst;
          simpl_env in *; clear HeqQ2 HeqQ3.
        discriminate H9.
        fsetdec.
        apply dom_cenv_split_proc in H.
          simpl_env in H. fsetdec.
        constructor...
          apply IHcenv_split_proc with (X := X0) (T := T0)...
    Case "cenv_split_proc_snksrc".
      inversion HeqZ. subst. clear HeqZ.
      destruct Q1L as [ | [X1 [d1 T1]] Q1L ];
          destruct Q2L as [ | [X2 [d2 T2]] Q2L ];
          destruct Q3L as [ | [X3 [d3 T3]] Q3L ];
          inversion HeqQ1; inversion HeqQ2; inversion HeqQ3;
          repeat subst; simpl_env in *;
          clear HeqQ1 HeqQ2 HeqQ3; try solve
            [ auto
            | fsetdec
            | apply dom_cenv_split_exp in H; simpl_env in H; fsetdec ].
    Case "cenv_split_proc_srcsnk".
      inversion HeqZ. subst. clear HeqZ.
      destruct Q1L as [ | [X1 [d1 T1]] Q1L ];
          destruct Q2L as [ | [X2 [d2 T2]] Q2L ];
          destruct Q3L as [ | [X3 [d3 T3]] Q3L ];
          inversion HeqQ1; inversion HeqQ2; inversion HeqQ3;
          repeat subst; simpl_env in *;
          clear HeqQ1 HeqQ2 HeqQ3; try solve
            [ auto
            | fsetdec
            | apply dom_cenv_split_exp in H; simpl_env in H; fsetdec ].
Qed.

Lemma cenv_split_proc_srcsnk_exp : forall E X T Q1L Q1R Q2L Q2R Q3L Q3R,
  cenv_split_proc E (Q1L ++ [(X, cbind_proto cdir_src T)] ++ Q1R)
                              (Q2L ++ [(X, cbind_proto cdir_snk T)] ++ Q2R)
                              (Q3L ++ [(X, cbind_proto cdir_both T)] ++ Q3R)
                              (Some X) ->
  cenv_split_exp E (Q1L ++ Q1R) (Q2L ++ Q2R) (Q3L ++ Q3R).
Proof.
  intros. apply cenv_split_exp_commute.
  apply cenv_split_proc_commute in H.
  apply cenv_split_proc_snksrc_exp in H. auto.
Qed.

Lemma vwf_envs_strengthen_cenv_left: forall G Q1 Q2 Q3 D Z,
  vwf_envs G Q3 D ->
  cenv_split_proc G Q1 Q2 Q3 Z ->
  vwf_envs G Q1 D.
Proof with auto.
  intros G Q1 Q2 Q3 D Z VWF CS.
  apply vwf_envs_unpack in VWF. destruct VWF as [WFL [WFC DJ]].
  apply vwf_envs_pack...
    eapply wf_cenv_split_proc_left; eauto.
  assert (dom Q3 [=] dom Q1 `union` dom Q2).
    apply dom_cenv_split_proc with (G := G) (Z := Z)...
  unfold disjoint in *. fsetdec.
Qed.

Lemma vwf_envs_strengthen_cenv_right: forall G Q1 Q2 Q3 D Z,
  vwf_envs G Q3 D ->
  cenv_split_proc G Q1 Q2 Q3 Z ->
  vwf_envs G Q2 D.
Proof.
  intros G Q1 Q2 Q3 D Z VWF CS.
  apply cenv_split_proc_commute in CS.
  eapply vwf_envs_strengthen_cenv_left; eauto.
Qed.
  
Lemma vwf_envs_lenv_strengthening: forall G Q D1 D2 D3,
  vwf_envs G Q (D1 ++ D2 ++ D3) ->
  vwf_envs G Q D2.
Proof.
  intros.
  remember (D1 ++ D2 ++ D3) as D.
  generalize dependent D1. generalize dependent D2. generalize dependent D3.
  (wf_lenv_cases (induction H) Case);  
    intros D3 D2 D1 EQ.
  Case "wf_lenv_empty".
    destruct D1; destruct D2; destruct D3; inversion EQ; auto.
  Case "wf_lenv_typ".
    destruct D1; destruct D2; simpl_env in *; inversion EQ; subst; auto.
    SCase "D1=nil, D2=nil".
      constructor. eapply wf_cenv_from_vwf_envs; eauto.
    SCase "D1=nil, D2=con".
      apply vwf_envs_typ; auto. 
        apply (IHvwf_envs D3 D2 lempty); auto.
        constructor. eapply wf_cenv_from_vwf_envs; eauto.
    SCase "D1=con, D2=con".
      apply (IHvwf_envs D3 (p0 :: D2) D1); auto.
Qed.

Lemma lenv_split_strengthen_cenv_left: forall E Q1 Q2 Q3 D1 D2 D3 Z,
  lenv_split E Q3 D1 D2 D3 ->
  cenv_split_proc E Q1 Q2 Q3 Z ->
  lenv_split E Q1 D1 D2 D3.
Proof with auto.
  intros E Q1 Q2 Q3 D1 D2 D3 Z Hl Hc. induction Hl.
  constructor... eapply wf_cenv_split_proc_left; eauto.
    assert (dom Q [=] dom Q1 `union` dom Q2).
      apply dom_cenv_split_proc with
          (G := E) (E1 := Q1) (E2 := Q2) (E3 := Q) (Z := Z)...
      constructor... fsetdec.
    assert (dom Q [=] dom Q1 `union` dom Q2).
      apply dom_cenv_split_proc with
          (G := E) (E1 := Q1) (E2 := Q2) (E3 := Q) (Z := Z)...
      constructor... fsetdec.
Qed.

Lemma lenv_split_strengthen_cenv_right: forall E Q1 Q2 Q3 D1 D2 D3 Z,
  lenv_split E Q3 D1 D2 D3 ->
  cenv_split_proc E Q1 Q2 Q3 Z ->
  lenv_split E Q2 D1 D2 D3.
Proof.
  intros E Q1 Q2 Q3 D1 D2 D3 Z Hl Hc.
  apply cenv_split_proc_commute in Hc.
  eapply lenv_split_strengthen_cenv_left; eauto.
Qed.

Lemma cenv_split_exp_disjoint: forall E Q1 Q2 Q3,
  cenv_split_exp E Q1 Q2 Q3 ->
  disjoint Q1 Q2.
Proof with auto.
  intros. induction H...
    unfold disjoint. simpl_env.
      apply dom_cenv_split_exp in H. solve_uniq.
    unfold disjoint. simpl_env.
      apply dom_cenv_split_exp in H. solve_uniq.
Qed.

Lemma cenv_split_exp_exists_disjoint: forall E Q1 Q2,
  wf_cenv E Q1 ->
  wf_cenv E Q2 ->
  disjoint Q1 Q2 ->
  exists Q3, cenv_split_exp E Q1 Q2 Q3.
Proof with auto.
  induction Q1; simpl_env in *.
    induction Q2; intros; simpl_env in *.
      exists cempty... constructor.
        apply wf_env_from_wf_cenv in H...
      inversion H0. subst. apply IHQ2 in H...
        destruct H as [Q3 CS].
        exists ([(X, cbind_proto d T)] ++ Q3). constructor...
          apply dom_cenv_split_exp in CS. fsetdec.
    intros. inversion H. subst.
      unfold disjoint in H1. simpl_env in H1.
      lapply (IHQ1 Q2 H4 H0)...
        intros. destruct H2 as [Q3 CS].
          exists ([(X, cbind_proto d T)] ++ Q3). constructor...
            apply dom_cenv_split_exp in CS. fsetdec.
        unfold disjoint. fsetdec.
Qed.

Hint Extern 1 (cenv_split_proc ?G ?Q1 ?Q2 ?Q3 ?Z) =>
  match goal with
  | H: cenv_split_exp _ _ _ _ |- _ => apply (cenv_split_exp_proc _ _ _ _ _ H)
  end.

Hint Extern 1 (wf_env ?E) =>
  match goal with
  | H: wf_lenv _ _ |- _ => apply (wf_env_from_wf_lenv _ _ H)
  | H: wf_cenv _ _ |- _ => apply (wf_env_from_wf_cenv _ _ H)
  | H: wf_cenvs _ _ |- _ => apply (wf_env_from_wf_cenvs _ _ H)
  end.

Hint Extern 1 (wf_lenv ?G ?D) =>
  match goal with
  | H: lenv_split _ _ _ _ |- _ => apply (wf_lenv_split _ _ _ _ H)
  | H: lenv_split _ _ _ _ |- _ => apply (wf_lenv_split_left _ _ _ _ H)
  | H: lenv_split _ _ _ _ |- _ => apply (wf_lenv_split_right _ _ _ _ H)
  | H: vwf_envs _ _ _ |- _ => apply (proj1 (vwf_envs_unpack _ _ _ H))
  end.

Hint Extern 1 (wf_cenv ?G ?Q) =>
  match goal with
  | H: cenv_split_exp _ _ _ _ |- _ => apply (wf_cenv_split_exp _ _ _ _ H)
  | H: cenv_split_exp _ _ _ _ |- _ => apply (wf_cenv_split_exp_left _ _ _ _ H)
  | H: cenv_split_exp _ _ _ _ |- _ => apply (wf_cenv_split_exp_right _ _ _ _ H)
  | H: cenv_split_proc _ _ _ _ |- _ => apply (wf_cenv_split_proc _ _ _ _ H)
  | H: cenv_split_proc _ _ _ _ |- _ => apply (wf_cenv_split_proc_left _ _ _ _ H)
  | H: cenv_split_proc _ _ _ _ |- _ => apply (wf_cenv_split_proc_right _ _ _ _ H)
  | H: vwf_envs _ _ _ |- _ => apply (proj1 (proj2 (vwf_envs_unpack _ _ _ H)))
  end.

(*Lemma wf_cenv_acc_right_empty : forall E Q,
  wf_cenv E Q ->
  wf_cenv_acc E Q cempty Q.
Proof with auto.
  intros. induction H; constructor...
Qed.*)

(*Lemma wf_cenv_acc_empty : forall E Q1 Q2,
  wf_cenv_acc E Q1 Q2 cempty ->
  Q1 = cempty /\ Q2 = cempty.
Proof with auto.
  intros. remember cempty as Q3. induction H...
    absurd (cempty = (X, cbind_proto d T) :: Q'')...
      apply nil_cons.
    absurd (QL ++ (X, cbind_proto cdir_both T) :: QR = cempty)...
      apply app_cons_not_nil.
    absurd (QL ++ (X, cbind_proto cdir_both T) :: QR = cempty)...
      apply app_cons_not_nil.
Qed.

Lemma wf_cenv_acc_right_id : forall E Q1 Q2,
  wf_cenv_acc E Q1 cempty Q2 ->
  Q1 = Q2.
Proof with auto.
  intros E Q1 Q3 WFC. remember cempty as Q2.
  induction WFC; subst...
    rewrite IHWFC...
    rewrite IHWFC in H0... simpl_env in H0. fsetdec.
    rewrite IHWFC in H0... simpl_env in H0. fsetdec.
Qed.

Lemma wf_prepend_aux : forall E Q Qs Qs' Q'',
  wf_cenvs_aux E Qs' Q'' ->
  nd_prepend_list Q Qs Qs' ->
  exists Q', wf_cenv_acc E Q Q' Q'' /\ wf_cenvs_aux E Qs Q'.
Proof with auto.
  intros E Q Qs Qs' Q'' WFC Prep.
  generalize dependent Qs. revert Q.
  induction WFC; intros; inversion Prep; subst.
    inversion WFC; subst.
      assert (Q = Q'').
        eapply wf_cenv_acc_right_id; eauto.
      subst. exists cempty. split...
    exists (Q1 ++ Q').

Lemma wf_cenv_acc_assoc : forall E Q1 Q2 Q3 Q4,
  wf_cenv_acc E (Q1 ++ Q2) Q3 Q4 ->
  wf_cenv_acc E Q1 (Q2 ++ Q3) Q4.
Proof with auto.
  intros E Q1 Q2. revert Q1. induction Q2; intros.
    simpl_env in *...
    destruct a as [X [d T]]. simpl_env in *.
      rewrite_env ((Q1 ++ [(X, cbind_proto d T)]) ++ Q2) in H.
      apply IHQ2 in H.


(*  induction Qs'.
    inversion Prep.
    inversion WFC; subst. rename a into Q0.*)
    

Lemma wf_prepend_right : forall E X d T Qs Qs',
  wf_cenvs E Qs' ->
  nd_prepend_list [(X, cbind_proto d T)] Qs Qs' ->
  wf_cenvs E Qs.
Proof with auto.
  intros. remember [(X, cbind_proto d T)] as Q.
  induction H0; inversion H; subst.
    apply wf_cenvs_wfca with (Q := cempty). constructor...
    inversion H0; inversion H6; subst;
      econstructor; econstructor; eauto.
    assert (wf_cenvs E Qs').
      inversion H; inversion H2; subst. econstructor; eauto.
    apply IHnd_prepend_list in H2...
      inversion H2; subst.*)

(* Lemma wf_typ_rename : forall G T (x y:atom) K1 K2,  *)
(*   uniq G -> *)
(*   y `notin` (singleton x `union` fv_tt T `union` dom G)  -> *)
(*   x `notin` (fv_tt T `union` dom G) -> *)
(*   wf_typ ([(x, bind_kn K1)] ++ G) (open_tt T x) K2 -> *)
(*   wf_typ ([(y, bind_kn K1)] ++ G) (open_tt T y) K2. *)
(* Proof. *)
(*   intros.  *)
(*   rewrite (subst_tt_intro x). *)
(*   rewrite_env (nil ++ [(y, bind_kn K1)] ++ G). *)
(*   assert (nil = map (subst_tb x y) nil). *)
(*   simpl. auto. *)
(*   rewrite H3. *)
(*   eapply wf_typ_subst_tb. simpl_env.  *)
(*   eapply wf_typ_weakening. eauto.  *)
(*     simpl. apply uniq_cons; auto. simpl.  *)
(*   apply wf_typ_var. apply uniq_cons. auto. solve_notin. *)
(*   rewrite_env ([(y, bind_kn K1)] ++ G). *)
(*   apply binds_app_l. apply binds_one; auto. solve_notin. *)
(* Qed. *)

Lemma channel_swap : forall c X Y,
  channel c -> channel (swap_cc X Y c).
Proof.
  intros.  induction c.
  simpl.  auto. 
  simpl. destruct (a == Y). auto. destruct (a == X). auto.  auto.
Qed.

Lemma swap_cc_eq: forall c X Y,
  X `notin` fv_cc c ->
  Y `notin` fv_cc c ->
  swap_cc X Y c = c.
Proof.
  induction c; intros; simpl in *; auto.
  destruct (a == Y).
    subst. fsetdec.
  destruct (a == X).
    subst. fsetdec.
  auto.
Qed.

Lemma swap_ce_eq:  forall u X Y,
  X `notin` fv_ce u ->
  Y `notin` fv_ce u ->
  swap_ce X Y u = u.
Proof.
  induction u; intros; simpl in *; (
    try rewrite IHu;
    try rewrite IHu1;
    try rewrite IHu2;
    try rewrite IHu3;
    try rewrite swap_cc_eq
  ); auto.
Qed.  

Lemma swap_open_ee : forall e u X Y k,
  X `notin` fv_ce u ->
  Y `notin` fv_ce u ->
  swap_ce X Y (open_ee_rec k u e) = open_ee_rec k u (swap_ce X Y e).
Proof.
  induction e; intros; simpl in *; (
    try rewrite IHe;
    try rewrite IHe1;
    try rewrite IHe2;
    try rewrite IHe3
  ); auto.
  destruct (k == n).
    rewrite swap_ce_eq; auto.
  simpl. auto.
Qed.

Lemma swap_open_cc : forall c Z X Y k,
  X `notin` fv_cc Z ->
  Y `notin` fv_cc Z ->
  swap_cc X Y (open_cc_rec k Z c) = open_cc_rec k Z (swap_cc X Y c).
Proof.
  induction c; intros; simpl in *; auto.
  destruct (k == n). rewrite swap_cc_eq; auto.
  simpl. auto.
  destruct (a == Y).
   subst. simpl. auto.
  destruct (a == X).
   simpl. auto.
  simpl. auto.
Qed.

Lemma swap_open_ce : forall e Z X Y k,
  X `notin` fv_cc Z ->
  Y `notin` fv_cc Z ->
  swap_ce X Y (open_ce_rec k Z e) = open_ce_rec k Z (swap_ce X Y e).
Proof.
  induction e; intros; simpl in *; (
    try rewrite IHe;
    try rewrite IHe1;
    try rewrite IHe2;
    try rewrite IHe3;
    try rewrite <- swap_open_cc
  ); auto.
Qed.

Lemma expr_swap : forall e X Y,
  expr e -> expr (swap_ce X Y e).
Proof.
  intros e X Y H.
  induction H; intros; simpl in *; auto.
  pick fresh Z and apply expr_abs; auto.
    simpl.  unfold open_ee. rewrite <- swap_open_ee; auto. 
    unfold open_ee in H1. apply H1; auto.
  apply expr_snk. apply channel_swap; auto. auto.
  apply expr_src. apply channel_swap; auto. auto.
  apply expr_done. apply channel_swap; auto.
Qed.

Lemma swap_open_cp : forall P k X Y Z,
  X `notin` fv_cc Z ->
  Y `notin` fv_cc Z ->
  swap_cp X Y (open_cp_rec k Z P) = open_cp_rec k Z (swap_cp X Y P).
Proof.
  induction P; intros; simpl in *; auto.
  rewrite swap_open_ce; auto.
  rewrite IHP1; auto.
  rewrite IHP2; auto.
  rewrite IHP; auto.
Qed.

Lemma process_swap : forall P X Y,
  process P -> process (swap_cp X Y P).
Proof.
  intros P X Y H.
  induction H; intros; simpl in *; auto.
  apply process_exp. apply expr_swap. auto.

  pick fresh Z and apply process_new. auto.
  unfold open_cp. rewrite <- swap_open_cp; auto.
  unfold open_cp in H1. apply H1; auto.
Qed.

Lemma chan_rename : forall c k (X Y:atom),
  channel (open_cc_rec k X c) ->
  channel (open_cc_rec k Y c).
Proof.
  induction c; intros; simpl in *; auto.
  destruct (k == n).  auto. auto.
Qed.

Lemma swap_open_cc2 : forall c k X Y,
  X `notin` fv_cc c ->
  Y `notin` fv_cc c ->
  swap_cc X Y (open_cc_rec k X c) = open_cc_rec k Y c.
Proof.
  induction c; intros k X Y NI1 NI2; simpl in *; auto.
  destruct (k == n).
  simpl. destruct (X == Y). subst. auto.
  destruct (X == X). auto. tauto.
  simpl. auto.
  destruct (a ==  Y). subst. fsetdec.
  destruct (a == X). subst. fsetdec. auto.
Qed.

Lemma swap_open_ce2 : forall e k X Y,
  X `notin` fv_ce e ->
  Y `notin` fv_ce e -> 
  swap_ce X Y (open_ce_rec k X e) = open_ce_rec k Y e.
Proof.
  induction e; intros k X Y NI1 NI2; simpl in *; (
    try rewrite IHe;
    try rewrite IHe1;
    try rewrite IHe2;
    try rewrite IHe3;
    try rewrite swap_open_cc2
  ); auto.
Qed.

(*
(open_ce_rec i X e) = subst_ee X Z (open_ce_rec i Z e)
(open_ce_rec i Y e) = subst_ee Y Z (open_ce_rec i Z e)
*)

Lemma channel_subst: forall Z (X:atom) c,
  channel (subst_cc Z X c) -> channel c.
Proof.
  induction c; simpl in *; auto.
Qed.

Lemma expr_subst : forall Z (X : atom) e,
  expr (subst_ce Z X e) -> expr e.
Proof.
  intros Z X e H.
  remember (subst_ce Z X e) as e'.
  generalize dependent e.
  induction H; intros ex EQ; destruct ex; simpl in *; inversion EQ; subst; auto.

  pick fresh Y and apply expr_abs; auto.
  apply (H1 Y); auto.
  rewrite subst_ce_open_ee_var. auto.
  
  apply expr_snk; auto. eapply channel_subst; eauto.
  apply expr_src; auto. eapply channel_subst; eauto.
  apply expr_done. eapply channel_subst; eauto.
Qed.

Lemma expr_rename : forall e i (X Y:atom),
  expr (open_ce_rec i X e) ->
  expr (open_ce_rec i Y e).
Proof.
  intros e i X Y H.
  remember (open_ce_rec i X e) as e'.
  generalize dependent e.  
  generalize dependent i.
  induction H; intros i ex EQ; destruct ex; inversion EQ; subst; simpl in *; auto.

  pick fresh Z and apply expr_abs; auto.
  unfold open_ee.
  rewrite (open_ce_rec_expr Z Y i).
  rewrite open_ee_open_ce_comm.
  apply (H1 Z); auto.
  unfold open_ee.
  rewrite <- open_ee_open_ce_comm.
  rewrite <- (open_ce_rec_expr Z X i). auto.
  auto. auto.

  apply expr_snk; auto. eapply chan_rename; eauto.
  apply expr_src; auto. eapply chan_rename; eauto.
  apply expr_done. eapply chan_rename; eauto.
Qed.

Lemma process_rename : forall P i (X Y:atom),
  process (open_cp_rec i X P) ->
  process (open_cp_rec i Y P).
Proof.
  intros P i X Y H.
  remember (open_cp_rec i X P) as Q.
  generalize dependent P. generalize dependent i.
  induction H; intros k Qx EQ; destruct Qx; inversion EQ; subst; simpl in *; auto.
  apply process_exp. 
  apply (expr_rename e0 k X Y). auto.

  pick fresh Z and apply process_new. auto.
  unfold open_cp.
  rewrite open_cp_open_cp_comm; auto.
  apply (H1 Z); auto.
  unfold open_cp.
  rewrite open_cp_open_cp_comm; auto.
Qed.
  
Lemma proc_eq1_regular : forall P1 P2,
  proc_eq1 P1 P2 ->
  (process P1 -> process P2) /\ (process P2 -> process P1).
Proof with auto.
  intros P1 P2 Heq.
  (proc_eq1_cases (induction Heq) Case)...
  Case "proc_eq1_parl".
    destruct IHHeq as [IH1 IH2].
    split; intros HP; inversion HP; subst...
  Case "proc_eq1_new".
    split; intros HP; inversion HP; subst; auto;
    apply process_new with (L := L `union` L0); auto;
    intros X NI; lapply (H0 X); auto;
    intros H'; destruct H' as [IH1 IH2]; auto.
  Case "proc_eq1_comm".
    split; intros HP; inversion HP; subst...
  Case "proc_eq1_assoc".
    split; intros HP; inversion HP; subst.
      inversion H1; subst...
      inversion H2; subst...
  Case "proc_eq1_swap".
    split; intros HP; inversion HP; subst.
      pick fresh X and apply process_new...
        unfold open_cp. simpl.
        pick fresh Y and apply process_new... 
        rewrite <- H...
        lapply (H3 Y)... intros. 
        inversion H0. subst.
        pick fresh Z. lapply (H6 Z). intros.
        unfold open_cp.
        apply (process_rename (open_cp_rec 1 Y P1) 0 Z X).
        unfold open_cp in H1. auto. auto.

      pick fresh X and apply process_new...
        unfold open_cp. simpl.
        pick fresh Y and apply process_new... 
        rewrite H...
        lapply (H3 Y)... intros. 
        inversion H0. subst.
        pick fresh Z. lapply (H6 Z). intros.
        unfold open_cp.
        apply (process_rename (open_cp_rec 1 Y P1') 0 Z X).
        unfold open_cp in H1. auto. auto.
  Case "proc_eq1_extrude".
    split; intros HP; inversion HP; subst.
      constructor... apply process_new with (L := L)...
        intros X NI. lapply (H3 X)... intros. inversion H0; subst...
      inversion H2; subst. apply process_new with (L := L)...
        intros X NI. constructor; fold open_cp_rec...
          lapply (H5 X)...
          rewrite <- open_cp_rec_process...
Qed.

Lemma proc_eq_sym : forall P1 P2,
  proc_eq P1 P2 ->
  proc_eq P2 P1.
Proof with auto.
  intros. (proc_eq_cases (induction H) Case)...
  Case "eq_trans".
    apply eq_trans with (P2 := P2)...
  Case "eq_new".
    pick fresh X and apply eq_new...
  Case "eq_swap".
    pick fresh X. 
    pick fresh Y and apply eq_swap.
    auto. auto. intros. rewrite H1. auto. fsetdec. fsetdec.
  Case "eq_extrude".
    apply eq_sym.  
    apply eq_extrude. auto. auto.
Qed.

Lemma proc_eqm_trans: forall P1 P2 P3,
  proc_eqm P1 P2 ->
  proc_eqm P2 P3 ->
  proc_eqm P1 P3.
Proof.
  intros P1 P2 P3 PEQ1.
  revert P3.
  induction PEQ1; intros; auto.
  eapply proc_eqm_left. apply H. apply IHPEQ1. auto.
  eapply proc_eqm_right. apply H. apply IHPEQ1. auto.
Qed.

Lemma proc_eqm_sym : forall P1 P2,
  proc_eqm P1 P2 ->
  proc_eqm P2 P1.
Proof.
  intros P1 P2 PEQM.  
  induction PEQM; intros; auto.
  generalize dependent P1.
  induction IHPEQM; intros.
    eapply proc_eqm_right. apply H. apply proc_eqm_refl.
    eapply proc_eqm_left. apply H. apply IHIHPEQM. 
    assert (proc_eqm P1 P2).  eapply proc_eqm_left. apply H. apply proc_eqm_refl.
    eapply proc_eqm_trans. apply PEQM. apply H1. apply H0.
    
    eapply proc_eqm_right. apply H. apply IHIHPEQM. 
    assert (proc_eqm P1 P2).  eapply proc_eqm_right. apply H. apply proc_eqm_refl.
    eapply proc_eqm_trans. apply PEQM. apply H1. apply H0.

    assert (proc_eqm P2 P1). eapply proc_eqm_left. apply H. apply proc_eqm_refl.
    eapply proc_eqm_trans. apply IHPEQM. auto.
Qed.

(* Conversion between more/less declarative process equalities *)

Lemma proc_eqm_parl : forall P1 P2 P1',
  proc_eqm P1 P1' ->
  proc_eqm (proc_par P1 P2) (proc_par P1' P2).
Proof.
  intros P1 P2 P1' PEQM.
  revert P2.
  induction PEQM; intros P2'; auto.
  
  apply proc_eqm_left with (P2:=(proc_par P2 P2')).
  apply proc_eq1_parl. auto. apply IHPEQM; auto.

  apply proc_eqm_right with (P2:=(proc_par P2 P2')).
  apply proc_eq1_parl. auto. apply IHPEQM; auto.
Qed.

Lemma proc_eqm_par : forall P1 P2 P1' P2',
  proc_eqm P1 P1' ->
  proc_eqm P2 P2' ->
  proc_eqm (proc_par P1 P2) (proc_par P1' P2').
Proof.
  intros P1 P2 P1' P2' PEQM1 PEQM2.
  assert (proc_eqm (proc_par P1 P2) (proc_par P1' P2)).
  eapply proc_eqm_parl. tauto. 
  assert (proc_eqm (proc_par P1' P2) (proc_par P2 P1')).
  apply proc_eqm_left with (P2:=(proc_par P2 P1')).
  apply proc_eq1_comm. apply proc_eqm_refl.
  assert (proc_eqm (proc_par P2 P1') (proc_par P2' P1')).
  eapply proc_eqm_parl. tauto.
  assert (proc_eqm (proc_par P2' P1') (proc_par P1' P2')). 
  apply proc_eqm_left with (P2:=(proc_par P1' P2')).
  apply proc_eq1_comm. apply proc_eqm_refl.
  eapply proc_eqm_trans. apply H.
  eapply proc_eqm_trans. apply H0.
  eapply proc_eqm_trans. apply H1.
  eapply proc_eqm_trans. apply H2.
  apply proc_eqm_refl.
Qed.

(*
Lemma proc_eqm_ex: forall P1 P2 (X:atom),
  proc_eq1 P2 (open_cp P1 X)  ->
  X `notin` (fv_cp P1) ->
  exists P3, P2 = (open_cp P3 X) /\ (X `notin` (fv_cp P3)).
Proof.
  intros P1 P2 X PEQ.
  remember (open_cp P1 X) as P1'.
  generalize dependent X. generalize dependent P1.
  induction PEQ; intros Px X EQ NI; subst; destruct Px; simpl in EQ; inversion EQ; subst; auto.
  unfold open_cp in *. 
  destruct (IHPEQ Px1 X) as [P3 [EQ3 NI3]]; auto.
  simpl in NI. fsetdec.
  subst P1. 
  exists (proc_par P3 Px2). 
  split. simpl. auto. simpl. simpl in NI. fsetdec.
  

  induction P1; intros P2 X PEQ NI; inversion PEQ; subst; auto.
  unfold open_cp in *.
  destruct (IHP1_1 P1 X) as [P3 [EQ3 NI3]]; auto. simpl in NI. fsetdec.
  subst. exists (proc_par P3 P1_2).
  simpl. split; auto. simpl in NI. fsetdec.

  exists (proc_par P1_2 P1_1). unfold open_cp. simpl.
  split; auto. simpl in NI. fsetdec.

  unfold open_cp in PEQ. simpl in PEQ. 
  rewrite <- H2 in PEQ.
  inversion PEQ. 
*)

Lemma notin_union : forall X S T,
  X `notin` S ->
  X `notin` T ->
  X `notin` union S T.
Proof.
  intros.
  fsetdec.
Qed.


(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../../../metatheory") ***
*** End: ***
 *)
