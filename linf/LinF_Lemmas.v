(** Administrative lemmas.

    Authors: Steve Zdancewic and Karl Mazurak.
    
    Table of contents:
      - #<a href="##wft">Properties of wf_typ</a>#
      - #<a href="##oktwft">Properties of wf_env and wf_typ</a>#
      - #<a href="##okt">Properties of wf_env</a>#
      - #<a href="##subst">Properties of substitution</a>#
      - #<a href="##regularity">Regularity lemmas</a>#
      - #<a href="##auto">Automation</a># *)

Require Export LinF_Infrastructure.
Require Export Extra.
Require Import Omega.

(* ********************************************************************** *)
(** * #<a name="wft"></a># Properties of [wf_typ] *)

Lemma type_from_wf_typ : forall E T K,
  wf_typ E T K -> type T.
Proof.
  intros E T K H; induction H; eauto.
Qed.

Lemma wf_typ_weakening : forall T E F G K,
  wf_typ (G ++ E) T K ->
  uniq (G ++ F ++ E) ->
  wf_typ (G ++ F ++ E) T K.
Proof with simpl_env; eauto.
  intros T E F G K Hwf_typ Hk.
  remember (G ++ E) as FF.
  generalize dependent G.
  (wf_typ_cases (induction Hwf_typ) Case); intros G Huniq Heq; subst...
  Case "wf_typ_all".
    pick fresh Y and apply wf_typ_all...
    rewrite <- app_assoc.
    apply H0...
Qed.

Lemma wf_typ_weaken_head : forall T E F K,
  wf_typ E T K ->
  uniq (F ++ E) ->
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
  (wf_typ_cases (induction WT) Case); intros F EQ; subst; simpl subst_tt...
  Case "wf_typ_var".
    destruct (X == Z).  subst...
      apply binds_mid_eq in H0; auto.
      inversion H0. subst...

      analyze_binds_uniq H0... 
        apply wf_typ_var.
          assert ((subst_tb Z P (bind_kn K)) = (bind_kn K)) as J; auto.
            solve_uniq.
          apply binds_weaken_at_tail.

          assert (bind_kn K = (subst_tb Z P (bind_kn K))) as J; auto.
          rewrite J.
          apply binds_map; auto.
  Case "wf_typ_all".
    pick fresh Y and apply wf_typ_all...
    rewrite subst_tt_open_tt_var...
    rewrite_env (map (subst_tb Z P) ([(Y, bind_kn K1)] ++ F) ++ E).
    apply H0...
Qed.

Lemma wf_typ_strengthening : forall E F x U T K,
 wf_typ (F ++ [(x, bind_typ U)] ++ E) T K ->
 wf_typ (F ++ E) T K.
Proof with simpl_env; eauto.
  intros E F x U T K H.
  remember (F ++ [(x, bind_typ U)] ++ E) as G.
  generalize dependent F.
  (wf_typ_cases (induction H) Case); intros F Heq; subst...
  Case "wf_typ_var".
    analyze_binds_uniq H0...
  Case "wf_typ_all".
    pick fresh Y and apply wf_typ_all...
    rewrite <- app_assoc.
    apply H0...
Qed.

Lemma wf_typ_strengthening_typ : forall E F X K1 T K,
 wf_typ (F ++ [(X, bind_kn K1)] ++ E) T K ->
 X `notin` (fv_tt T) ->
 wf_typ (F ++ E) T K.
Proof with simpl_env; eauto.
  intros E F X K1 T K H.
  remember (F ++ [(X, bind_kn K1)] ++ E) as G.
  generalize dependent F.
  (wf_typ_cases (induction H) Case); 
     intros F Heq Nin; simpl in Nin; subst...
  Case "wf_typ_var".
    analyze_binds_uniq H0; subst... 
  Case "wf_typ_all".
    pick fresh Y and apply wf_typ_all.  
    rewrite <- app_assoc.
    eapply H0... 
      apply notin_open_tt_fv; auto.
Qed.    

(* ********************************************************************** *)
(** * #<a name="oktwft"></a># Properties of [wf_env] and [wf_typ] *)

Lemma uniq_from_wf_env : forall E,
  wf_env E ->
  uniq E.
Proof.
  intros E H; induction H; auto.
Qed.

Lemma uniq_from_wf_lenv: forall E D,
  wf_lenv E D ->
  uniq D.
Proof.
  induction D; intros; auto.
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

Lemma wf_typ_from_binds_typ : forall x U E,
  wf_env E ->
  binds x (bind_typ U) E ->
  wf_typ E U kn_nonlin.
Proof with auto using wf_typ_weaken_head.
  induction 1; intros J; analyze_binds_uniq J...
  inversion BindsTacVal. subst...
Qed.

Lemma wf_typ_from_wf_env_typ : forall x T E,
  wf_env ([(x, bind_typ T)] ++ E) ->
  wf_typ E T kn_nonlin.
Proof.
  intros x T E H. inversion H; auto.
Qed.

(* ********************************************************************** *)
(** * #<a name="uniqt"></a># Properties of [wf_env] and [wf_lenv] *)

(** These properties are analogous to the properties that we need to
    show for the subtyping and typing relations. *)

Lemma wf_env_strengthening : forall x T E F,
  wf_env (F ++ [(x, bind_typ T)] ++ E) ->
  wf_env (F ++ E).
Proof with eauto using wf_typ_strengthening.
  induction F; intros Wf_env; inversion Wf_env; subst; simpl_env in *...
Qed.

Lemma wf_env_strengthening_tail: forall E F,
  wf_env (F ++ E) ->
  wf_env E.
Proof.
  intros E F H.
  induction F; auto.
    rewrite_env ([a] ++ (F ++ E)) in H.
    apply IHF.
      inversion H; auto.
Qed.

Lemma wf_env_from_wf_lenv: forall E D,
  wf_lenv E D ->
  wf_env E.
Proof.
  intros E D WFL.
  induction WFL; auto.
Qed.  

Lemma wf_lenv_strengthening: forall x T E F D,
  wf_lenv (F ++ [(x, bind_typ T)] ++ E) D ->
  wf_lenv (F ++ E) D.
Proof.
  intros x T E F D WFL.
  remember (F ++ [(x, bind_typ T)] ++ E) as E0.
  generalize dependent F.
  (wf_lenv_cases (induction WFL) Case); intros F EQ; subst.
  Case "wf_lenv_empty".
    apply wf_lenv_empty; auto. 
      eapply wf_env_strengthening; eauto.
  Case "wf_lenv_typ".
    apply wf_lenv_typ; auto.
      eapply wf_typ_strengthening; eauto.
Qed.

Lemma wf_lenv_strengthening_typ: forall G D X K, 
  wf_lenv ([(X, bind_kn K)] ++ G) D ->
  X `notin` fv_lenv D ->
  wf_lenv G D.
Proof.
  induction D; intros X K WFL NIN.
  Case "nil".
    apply wf_lenv_empty.
      inversion WFL; subst. 
      inversion H; subst.
      auto.
  Case "con".
    destruct a. destruct l. simpl in NIN.
    inversion WFL; subst.
    simpl_env in *.
    apply wf_lenv_typ; auto.
      eapply IHD; eauto.

      rewrite_env (empty ++ G).
      eapply wf_typ_strengthening_typ.
        simpl_env. apply H6.
        fsetdec.
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
  (wf_lenv_cases (induction WFL) Case); intros F EQ WFT; subst; simpl_env in *.
  Case "wf_lenv_empty".
    apply wf_lenv_empty. 
      eapply wf_env_subst_tb; eauto.
  Case "wf_lenv_typ".
    apply wf_lenv_typ; auto.
      eapply wf_typ_subst_tb; eauto.
Qed.

(* ********************************************************************** *)
(** * #<a name="subst"></a># Environment is unchanged by substitution for a fresh name *)

Lemma notin_fv_wf : forall E (X : atom) T K,
  wf_typ E T K ->
  X `notin` dom E ->
  X `notin` fv_tt T.
Proof with auto.
  intros E X T K Wf_typ.
  (wf_typ_cases (induction Wf_typ) Case); intros Fr; simpl...
  Case "wf_typ_var".
    assert (X0 `in` (dom E))...
    eapply binds_In; eauto. assert (X <> X0)... fsetdec.
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
  (wf_env_cases (induction H) Case); simpl; intros Fr; simpl_env...
  Case "wf_env_kn".
    rewrite <- IHwf_env...
  Case "wf_env_typ".
    rewrite <- IHwf_env...
    rewrite <- subst_tt_fresh... 
    eapply notin_fv_wf; eauto.
Qed.

(* Basic properties of the env_split relation *)

Lemma dom_lenv_split: forall G E1 E2 E3,
  lenv_split G E1 E2 E3  -> 
  dom E3 [=] dom E1 `union` dom E2.
Proof.
  intros E1 E2 E3 G S.
  induction S; simpl; try fsetdec. 
Qed.

Lemma lenv_split_commute: forall G E1 E2 E3,
  lenv_split G E1 E2 E3 ->
  lenv_split G E2 E1 E3.
Proof.
  intros G E1 E2 E3 S.
  induction S; auto.
Qed.

Lemma lenv_split_empty_left: forall G E F,
  lenv_split G lempty E F ->
  E = F.
Proof.
  induction E; intros F H; inversion H; auto.
  Case "con".
    rewrite (IHE D3); auto.
Qed.

Lemma lenv_split_empty_right: forall G E F,
  lenv_split G E lempty F ->
  E = F.
Proof.
  intros. 
  eapply lenv_split_empty_left. 
  eapply lenv_split_commute; eauto.
Qed.

Lemma wf_lenv_split: forall D1 D2 D3 G,
  lenv_split G D1 D2 D3  ->
  wf_lenv G D3.
Proof.
  intros G D1 D2 D3 S.
  (lenv_split_cases (induction S) Case); simpl_env in *; 
    try solve [ eauto | eapply wf_lenv_typ; eauto ].
Qed.

Lemma wf_lenv_split_left: forall G D1 D2 D3,
  lenv_split G D1 D2 D3 ->
  wf_lenv G D1.
Proof.
  intros G D1 D2 D3 S.
  (lenv_split_cases (induction S) Case); auto.
  Case "lenv_split_left".
    apply wf_lenv_typ; auto.
      rewrite (dom_lenv_split E D1 D2 D3) in H0; auto.
Qed.

Lemma wf_lenv_split_right: forall G D1 D2 D3,
  lenv_split G D1 D2 D3 ->
  wf_lenv G D2.
Proof.
  intros. 
  eapply wf_lenv_split_left. 
  eapply lenv_split_commute; eauto.
Qed.

Hint Extern 1 (wf_env ?E) =>
  match goal with
  | H: wf_lenv _ _ |- _ => apply (wf_env_from_wf_lenv _ _ H)
  end.

Hint Extern 1 (wf_lenv ?G ?D) =>
  match goal with
  | H: lenv_split _ _ _ _ |- _ => apply (wf_lenv_split _ _ _ _ H)
  | H: lenv_split _ _ _ _ |- _ => apply (wf_lenv_split_left _ _ _ _ H)
  | H: lenv_split _ _ _ _ |- _ => apply (wf_lenv_split_right _ _ _ _ H)
  end.

(* requires the kind to be kn_lin!! *)
Lemma typing_regular : forall E D e T,
  typing E D e T ->
  wf_env E /\ wf_lenv E D /\ expr e /\ wf_typ E T kn_lin.
Proof with simpl_env; try solve [intuition].
  intros E D e T H; (typing_cases (induction H) Case)...
  Case "typing_var".
    repeat split...
    eauto using wf_typ_from_binds_typ.
  Case "typing_lvar".
    repeat split...
    inversion H; auto. 
  Case "typing_abs".
    pick fresh y.
    destruct (H1 y)...
    destruct H4 as [WFL [EXP WFT]].
    repeat split...
    SCase "wf_env".
      rewrite_env (empty ++ E). 
      eapply wf_env_strengthening; eauto.
    SCase "wf_lenv".
      rewrite_env (empty ++ E). 
      eapply wf_lenv_strengthening; eauto.
    SCase "expr".
      pick fresh x and apply expr_abs.
        eapply type_from_wf_typ; eauto.
        lapply (H1 x); auto...
    SCase "wf_typ".
      destruct K.
      SSCase "K=lin".
        eapply wf_typ_arrow; eauto.
          rewrite_env (empty ++ E).
          eapply wf_typ_strengthening; eauto.
      SSCase "K=nonlin".
        eapply wf_typ_sub.
         eapply wf_typ_arrow; eauto.
            rewrite_env (empty ++ E).
            eapply wf_typ_strengthening; eauto.
  Case "typing_labs".
    pick fresh y.
    destruct (H1 y)...
    destruct H4 as [WFL [EXP WFT]].
    repeat split...
    SCase "wf_lenv".
      inversion WFL; auto.
    SCase "expr".
      pick fresh x and apply expr_abs.
      eapply type_from_wf_typ; eauto.
      lapply (H1 x); auto...
    SCase "wf_typ".
      destruct K.
      SSCase "K=lin".
        eapply wf_typ_arrow; eauto.
      SSCase "K=nonlin".
        eapply wf_typ_sub; eauto.
  Case "typing_app".
    destruct IHtyping1 as [WF1 [WFL1 [EX1 J1]]]...
    destruct IHtyping2 as [WF2 [WFL2 [EX2 J2]]]...
    repeat split...
    SCase "wf_typ".
      inversion J1; subst; auto.
      SSCase "K=lin".
        destruct K2; auto. 
      SSCase "K=nonlin".
        inversion H2; subst; auto.
        destruct K2; auto. 
  Case "typing_tabs".
    pick fresh Y.
    destruct (H1 Y) as [HWF [WFL [EX WT]]]...
    inversion HWF; subst.
    repeat split...
    SCase "wf_lenv".
      inversion WFL; subst; auto.
      eapply wf_lenv_strengthening_typ; eauto.
    SCase "expr".
      pick fresh X and apply expr_tabs.
      destruct (H1 X) as [A [B [C CC]]]...
    SCase "wf_typ".
      pick fresh X and apply wf_typ_all.
      destruct (H1 X) as [A [B [C CC]]]...
  Case "typing_tapp".
    repeat split...
    SCase "expr".
      apply (expr_tapp).
        tauto.
        eapply type_from_wf_typ; eauto.
    SCase "wf_typ".
      destruct IHtyping as [_ [_ [_ WF]]].
      inversion WF; subst... 
      SSCase "wf_typ_all".
        pick fresh Y.
        rewrite (subst_tt_intro Y); auto.
        rewrite_env ((map (subst_tb Y T) empty) ++ E); auto.
        eapply (wf_typ_subst_tb empty K); auto.
        rewrite_env ([(Y, bind_kn K)] ++ E); auto.
      SSCase "wf_typ_sub".
        apply wf_typ_sub.
          inversion H1; subst...
          pick fresh Y.
          rewrite (subst_tt_intro Y); auto.
          rewrite_env ((map (subst_tb Y T) empty) ++ E); auto.
          eapply (wf_typ_subst_tb empty K); auto.
          rewrite_env ([(Y, bind_kn K)] ++ E); auto.
  Case "typing_apair".
    destruct IHtyping1 as [WF1 [WFL1 [EX1 J1]]]...
    destruct IHtyping2 as [WF2 [WFL2 [EX2 J2]]]...
    repeat split...
      eapply wf_typ_with; eauto.
  Case "typing_fst".
    destruct IHtyping as [WF [WFL1 [EX J]]]...
    repeat split...
    SCase "wf_typ".
      inversion J; subst; auto.
      SSCase "wf_typ_with".
        destruct K1; auto. 
      SSCase "wf_typ_sub".
        inversion H0; subst; auto.
  Case "typing_snd".
    destruct IHtyping as [WF [WFL1 [EX J]]]...
    repeat split...
    SCase "wf_typ".
      inversion J; subst; auto.
      SSCase "wf_typ_with".
        destruct K2; auto. 
      SSCase "wf_typ_sub".
        inversion H0; subst; auto.
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
Proof with try solve [solve_notin | intuition].
  intros e e' H.
  induction H; assert(J := value_regular); split...
  Case "red_abs".
    inversion H. pick fresh y. rewrite (subst_ee_intro y)...
  Case "red_tabs".
    inversion H. pick fresh Y. rewrite (subst_te_intro Y)...
Qed.

(* *********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

(** The lemma [uniq_from_wf_env] was already added above as a hint since it
    helps blur the distinction between [wf_env] and [uniq] in proofs.

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
  | H: typing _ _ _ _ |- _ => apply (proj1 (typing_regular _ _ _ _ H))
  end.

Hint Extern 1 (wf_lenv ?G ?D) =>
  match goal with
  | H: typing _ _ _ _ |- _ => apply (proj1 (proj2 (typing_regular _ _ _ _ H)))
  end.

Hint Extern 1 (wf_typ ?E ?T kn_lin) =>
  match goal with
  | H: typing E _ _ T |- _ => apply (proj2 (proj2 (proj2 (typing_regular _ _ _ _ H))))
  end.

Hint Extern 1 (type ?T) =>
  let go E := apply (type_from_wf_typ E); auto in
  match goal with
  | H: typing ?E _ _ T |- _ => go E
  end.

Hint Extern 1 (expr ?e) =>
  match goal with
  | H: typing _ _ ?e _ |- _ => apply (proj1 (proj2 (proj2 (typing_regular _ _ _ _ H))))
  | H: red ?e _ |- _ => apply (proj1 (red_regular _ _ H))
  | H: red _ ?e |- _ => apply (proj2 (red_regular _ _ H))
  | H: value ?e |- _ => apply (value_regular _ H)
  end.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../../../metatheory") ***
*** End: ***
 *)
