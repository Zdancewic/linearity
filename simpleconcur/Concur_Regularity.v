(** Regularity lemmas

     For space reasons and because dependencies are getting tricky. *)

Require Export Concur_Environments.

Axiom skip : False.
Ltac skip := assert False; [ apply skip | contradiction ].


(* Regularity lemmas *)

Lemma dual_regular: forall E T T',
  dual E T T' ->
  wf_env E /\ wf_proto E T /\ wf_typ E T'.
Proof with auto.
  intros. induction H; split; intuition...
Qed.

Lemma value_regular : forall e,
  value e ->
  expr e.
Proof.
  intros e H. induction H; auto.
Qed.

(*Lemma snk_regular : forall E T C v,
  type T ->
  channel C ->
  snk E T C v ->
  wf_chan E C /\ wf_proto E T /\ value v.
Proof with auto.
  intros E T C v Ht Hc Hs.
  induction Hs.
    repeat split...
    assert (wf_chan E C /\ wf_proto E T2 /\ value e2).
      apply IHHs...
    destruct H as [WFE [WFP Val]].
    repeat split...
      repeat constructor... apply value_regular...
    assert (wf_chan E C /\ wf_proto E T1 /\ value e1).
      apply IHHs1...
    destruct H as [WFE1 [WFP1 Val1]]. 
    assert (wf_chan E C /\ wf_proto E T2 /\ value e2).
      apply IHHs2...
    destruct H as [WFE2 [WFP2 Val2]].
    repeat split...
      repeat constructor; auto; apply value_regular...
Qed.

Lemma src_regular : forall E T C v,
  type T ->
  channel C ->
  src E T C v ->
  wf_chan E C /\ wf_proto E T /\ value v.
Proof with auto.
  intros E T C v Ht Hc Hs.
  induction Hs.
    repeat split...
    assert (wf_chan E C /\ wf_proto E T2 /\ value e2).
      apply IHHs...
    destruct H0 as [WFE [WFP Val]].
    repeat split...
      repeat constructor... pick fresh x and apply expr_abs...
      constructor; fold open_ee_rec.
        compute...
        assert (expr e2). apply value_regular...
        rewrite <- open_ee_rec_expr...
    assert (wf_chan E C /\ wf_proto E T1 /\ value e1).
      apply IHHs1...
    destruct H1 as [WFE1 [WFP1 Val1]]. 
    assert (wf_chan E C /\ wf_proto E T2 /\ value e2).
      apply IHHs2...
    destruct H1 as [WFE2 [WFP2 Val2]].
    repeat split...
      repeat constructor; auto; apply value_regular...
Qed.*)

Lemma typing_regular : forall E D Q e T,
  typing E D Q e T ->
  vwf_envs E Q D /\ expr e /\ wf_typ E T.
Proof with simpl_env; try solve [intuition; eapply wf_lenv_split; eauto].
  intros E D Q e T H; (typing_cases (induction H) Case)...
  Case "typing_var".
    split... rewrite_env ([(x, lbind_typ T)] ++ lempty).
    constructor; try fsetdec.
      repeat constructor; auto.
      apply wf_lenv_disjoint in H. solve_uniq.
  Case "typing_abs".
    pick fresh y.
    destruct (H1 y) as [WFL H3]...
    destruct H3 as [EXP WFT].
    repeat split...
    SCase "vwf_envs".
      inversion WFL; auto.
    SCase "expr".
      pick fresh x and apply expr_abs.
      eapply type_from_wf_typ; eauto.
      lapply (H1 x); auto...
Qed.

Lemma wf_cenvs_strengthen_cenv_left: forall E Q1 Q2 Q3 QsL QsR Z,
  wf_cenvs E (QsL ++ [Q3] ++ QsR) ->
  cenv_split_proc E Q1 Q2 Q3 Z ->
  wf_cenvs E (QsL ++ [Q1] ++ QsR).
Proof with auto.
  intros. inversion H; subst.
    assert (lcempty = Q3 :: QsR).
      symmetry in H1. apply app_eq_nil in H1. intuition.
      apply nil_cons in H2. intuition.
    remember (QsL ++ [Q3] ++ QsR) as Qs.
    generalize dependent Z. generalize dependent Q3.
    revert QsL QsR Q1 Q2.
    induction H1; intros; subst.
      assert (lcempty = Q3 :: QsR).
        symmetry in HeqQs. apply app_eq_nil in HeqQs. intuition.
        apply nil_cons in H2. intuition.
      symmetry in HeqQs. apply app_eq_unit in HeqQs.
        destruct HeqQs as [[H2 H3] | [H2 H3]]; subst.
          inversion H3. subst. simpl_env in *.
            apply wf_cenvs_from_single. apply wf_cenv_split_proc_left in H1...
          symmetry in H3. simpl in H3. apply nil_cons in H3. intuition.
      apply app_eq_cases_mid in HeqQs.
        (* Needs disjointness / append lemma, maybe? *)
        destruct HeqQs as [Qs' [[Eq Eq'] | [Eq Eq']]]; subst.
          apply wf_cenvs_append_wf in H. destruct H as [H H'].
            (* But are they really disjoint...? *)
Admitted.

Lemma nd_cons_cenvs_regular : forall E X T Qs FQs,
  nd_cons_cenvs Qs FQs ->
  X `notin` dom E ->
  X `notin` doms cbinding Qs ->
  wf_proto E T ->
  (wf_cenvs E Qs <-> wf_cenvs E (FQs X T)).
Proof with auto.
  intros. inversion H; subst; split; intros.
    skip. (* Waiting to see if we prove these lemmas elsewhere... *)
    apply wf_cenvs_strengthen_cenvs with
        (Qs2 := [[(X, cbind_proto cdir_both T)]])...
    skip. (* Same as above. *)
    apply wf_cenvs_strengthen_cenv_left with (Z := None)
         (Q2 := [(X, cbind_proto cdir_both T)])
         (Q3 := [(X, cbind_proto cdir_both T)] ++ Q)...
      rewrite_env ([(X, cbind_proto cdir_both T)] ++ cempty).
      rewrite_env ([(X, cbind_proto cdir_both T)] ++ Q).
      constructor...
        apply cenv_split_proc_right_id...
          apply wf_cenvs_append_wf in H3. intuition.
          apply wf_cenvs_append_wf in H5. intuition.
          apply wf_cenvs_to_single in H3. inversion H3...
        assert (doms cbinding (QsL ++ [Q] ++ QsR) [=]
                    union (doms cbinding QsL) (doms cbinding ([Q] ++ QsR))).
            apply doms_append...
          simpl in H4. fsetdec.
Qed.

Lemma proc_typing_regular : forall Qs P T,
  proc_typing Qs P T ->
  wf_cenvs empty Qs /\ process P /\ wf_typ empty T.
Proof with auto.
  intros Qs P T H. (proc_typing_cases (induction H) Case).
  Case "typing_exp".
    assert (vwf_envs empty Q lempty /\ expr e /\ wf_typ empty T).
      apply typing_regular...
    destruct H1 as [Hvwf [He Ht]]. split...
      apply wf_cenvs_split_multi in H0...
  Case "typing_parl".
    destruct IHproc_typing1 as [Hwfe1 [Hp1 Ht1]].
    destruct IHproc_typing2 as [Hwfe2 [Hp2 Ht2]].
    repeat split... apply wf_cenvs_split in H1...
  Case "typing_parr".
    destruct IHproc_typing1 as [Hwfe1 [Hp1 Ht1]].
    destruct IHproc_typing2 as [Hwfe2 [Hp2 Ht2]].
    repeat split... apply wf_cenvs_split in H1...
  Case "typing_new".
    pick fresh Y.
    lapply (H1 Y)... lapply (H2 Y)... intros IH PTyp.
    destruct IH as [Hwf [Hp Ht]]. repeat split...
      apply nd_cons_cenvs_regular in Hwf... intuition.
      pick fresh Z and apply process_new...
        lapply (H2 Z)... intros. intuition.
Qed.

Lemma plug_regular : forall M e f,
  expr e ->
  plug M e f ->
  expr f.
Proof with auto.
  intros M e f He Hp. induction Hp...
  constructor... apply value_regular...
  constructor... apply value_regular...
Qed.

Lemma open_ce_plug_regular : forall M e f Y,
  expr (open_ce e Y) ->
  plug M e f ->
  expr (open_ce f Y).
Proof.
  intros M e f Y He Hp. generalize dependent Y.
  (plug_cases (induction Hp) Case); intros Y He; unfold open_ce in *;
  try solve [ auto;
                   constructor; fold open_ce_rec; auto;
                   try rewrite <- open_ce_rec_expr; auto;
                   try apply value_regular; auto ].
Qed.

Lemma plug_open_ce_rec: forall M e f K C f',
  plug M e f ->
  plug M (open_ce_rec K C e) f' ->
  f' = open_ce_rec K C f.
Proof with auto.
  (ectx_cases (induction M) Case); intros;
  inversion H; inversion H0; subst; simpl...
  Case "ectx_seq".
    rewrite <- (open_ce_rec_expr e)...
    rewrite <- (IHM e1 e4 K C e7)...
  Case "ectx_appl".
    rewrite <- (open_ce_rec_expr e)...
    rewrite <- (IHM e1 e4 K C e7)...
  Case "ectx_appr".
    apply value_regular in Hv0.
    rewrite <- (open_ce_rec_expr v)...
    rewrite <- (IHM e e2 K C e3)...
  Case "ectx_fst".
    rewrite <- (IHM e e1 K C e3)...
  Case "ectx_snd".
    rewrite <- (IHM e e1 K C e3)...
  Case "ectx_mpairl".
    rewrite <- (open_ce_rec_expr e)...
    rewrite <- (IHM e1 e4 K C e7)...
  Case "ectx_mpairr".
    apply value_regular in Hv0.
    rewrite <- (open_ce_rec_expr v)...
    rewrite <- (IHM e e2 K C e3)...
  Case "ectx_let".
    rewrite <- (open_ce_rec_expr e)...
    rewrite <- (IHM e1 e4 K C e7)...
  Case "ectx_inl".
    rewrite <- (IHM e e1 K C e3)...
  Case "ectx_inr".
    rewrite <- (IHM e e1 K C e3)...
  Case "ectx_case".
    rewrite <- (open_ce_rec_expr e2)...
    rewrite <- (open_ce_rec_expr e3)...
    rewrite <- (IHM e1 e7 K C e11)...
  Case "ectx_go".
    rewrite <- (IHM e e1 K C e3)...
  Case "ectx_yield".
    rewrite <- (IHM e e1 K C e3)...
Qed.

Lemma ectx_typing_regular: forall E D Q M T T',
  ectx_typing E D Q M T T' ->
  vwf_envs E Q D /\ wf_typ E T /\ wf_typ E T'.
Proof with simpl_env; try solve [intuition; eapply wf_lenv_split; eauto].
  intros E D Q M T T' ETyp.
  induction ETyp...
Qed.

Lemma red_regular : forall e e',
  red e e' ->
  expr e /\ expr e'.
Proof with try solve [solve_notin | intuition].
  intros e e' H.
  induction H; assert(J := value_regular); split...
  Case "red_seq".
    inversion H; auto.
  Case "red_app".
    inversion H. inversion H2. pick fresh y. rewrite (subst_ee_intro y)...
  Case "red_apairl".
    inversion H. inversion H1. auto.
  Case "red_apairr".
    inversion H. inversion H1. auto.
  Case "red_let".
    inversion H. constructor. constructor; auto. auto.
  Case "red_inl".
    inversion H. constructor; auto.
  Case "red_inr".
    inversion H. constructor; auto.
  Case "red_yield_abs".
    inversion H. subst. inversion H1. subst. inversion H3. subst.
    repeat constructor; auto.
      pick fresh y and apply expr_abs; auto.
      constructor; simpl; auto.
      pick fresh z and apply expr_abs; simpl; auto.
      pick fresh w and apply expr_abs; simpl; auto.
      constructor; simpl; intuition.
  Case "red_yield_snk".
    inversion H. subst. inversion H1. subst. constructor...
    repeat constructor; auto.
      remember empty as E.
      pick fresh y and apply expr_abs; auto.
      constructor; simpl; auto.
      pick fresh z and apply expr_abs; simpl; auto.
      pick fresh w and apply expr_abs; simpl; auto.
      constructor; simpl; intuition.
    inversion H. inversion H1...
Qed.

(*Lemma open_snk: forall E T v X,
  snk E T 0 v ->
  X `notin` fv_ce v ->
  X `notin` fv_ee v -> 
  snk E T X (open_ce v X).
Proof with auto.
  intros E T v X. revert v.
  induction T; intros v Snk NI1 NI2; inversion Snk; inversion H; subst.
    compute...
    constructor; fold open_ce_rec.
      apply IHT2...
        compute in NI1; fsetdec.
    constructor; fold open_ce_rec.
      apply IHT1...
        compute in NI1; fsetdec.
        compute in NI2; fsetdec.
      apply IHT2...
        compute in NI1; fsetdec.
        compute in NI2; fsetdec.
Qed.

Lemma open_src: forall E T v X,
  src E T 0 v ->
  X `notin` fv_ce v ->
  X `notin` fv_ee v -> 
  src E T X (open_ce v X).
Proof with auto.
  intros E T v X. revert v.
  induction T; intros v Src NI1 NI2; inversion Src; inversion H; subst.
    compute...
    unfold open_ce; unfold open_ce_rec;
    pick fresh x and apply src_arrow; fold open_ce_rec...
      apply IHT2...
        compute in NI1; fsetdec.
        compute in NI2; fsetdec.
      unfold open_ee in H5. unfold open_ee.
      lapply (H5 x). intros. inversion H. rewrite H1. simpl.
      assert (open_ce_rec 0 X x = x). simpl. auto.
      rewrite <- H0.
      rewrite open_ee_open_ce_comm. rewrite H1. auto.
      fsetdec.
    unfold open_ce; unfold open_ce_rec; constructor; fold open_ce_rec...
      apply IHT1...
        compute in NI1; fsetdec.
        compute in NI2; fsetdec.
      apply IHT2...
        compute in NI1; fsetdec.
        compute in NI2; fsetdec.
Qed.

Lemma open_ce_snk_regular : forall E T J Y v,
  snk E T (bchan J) v ->
  value (open_ce_rec J (fchan Y) v).
Proof.
  intros. remember (bchan J) as C. induction H; try rewrite HeqC in *;
  auto; repeat constructor; fold open_ce_rec;
  try solve [ unfold open_cc_rec; destruct (J == J); intuition; auto
                 | apply value_regular; auto ].
Qed.

Lemma open_ce_src_regular : forall E T J Y v,
  src E T (bchan J) v ->
  value (open_ce_rec J (fchan Y) v).
Proof with auto.
  intros. remember (bchan J) as C. induction H; try rewrite HeqC in *;
  auto; repeat constructor; fold open_ce_rec;
    try solve [ unfold open_cc_rec; destruct (J == J); intuition; auto
                   | apply value_regular; auto ].
  Case "src_arrow".
    pick fresh Z and apply expr_abs... constructor; fold open_ee_rec.
    destruct (0 == 0); intuition...
    assert (expr (open_ce_rec J Y e2)). apply value_regular...
    rewrite <- open_ee_rec_expr...
Qed.*)

Lemma dual_unique_src: forall E T T1 T2,
  dual E T T1 ->
  dual E T T2 ->
  T1 = T2.
Proof with auto. 
  intros E T.
  induction T; intros  T'1 T'2 Dual1 Dual2;
  inversion Dual1; inversion Dual2; subst...
    rewrite (IHT2 T2' T2'0)...
    rewrite (IHT1 T1' T1'0)... rewrite (IHT2 T2' T2'0)...
Qed.

(*Lemma typing_snk: forall E T X v,
  snk E T (fchan X) v ->
  X `notin` dom E ->
  typing E lempty [(X, cbind_proto cdir_snk T)] v T.
Proof with auto.
  intros E T X v Snk NI.
  inversion Snk; subst; constructor...
  rewrite_env ([(X, cbind_proto cdir_snk typ_answer)] ++ cempty).
  inversion H; subst. constructor...
Qed.

Lemma typing_src: forall E T X v T',
  src E T (fchan X) v ->
  X `notin` dom E ->
  dual E T T' ->
  typing E lempty [(X, cbind_proto cdir_src T)] v T'.
Proof with auto.
  intros E T X v T' Src NI Dual.
  inversion Src; inversion Dual; subst;
  try solve [ inversion H6
                 | inversion H7
                 | constructor; auto ].
    constructor. inversion H; subst.
    rewrite_env ([(X, cbind_proto cdir_src typ_answer)] ++ cempty).
    constructor...
Qed.*)

Lemma canon_inner_regular: forall P,
  canon_inner P ->
  process P.
Proof with auto.
  intros. induction H...
Qed.

Lemma canon_outer_regular: forall P,
  canon_outer P ->
  process P.
Proof with auto.
  intros. induction H...
    apply canon_inner_regular...
    pick fresh X and apply process_new...
Qed.


Lemma proc_eq_regular : forall P1 P2,
  proc_eq P1 P2 ->
  process P1 /\ process P2.
Proof with auto.
  intros P1 P2 He. (proc_eq_cases (induction He) Case); split;
  try destruct IHHe as [IH1 IH2]; try destruct IHHe1 as [IH1 IH2];
  try destruct IHHe2 as [IH3 IH4]; try destruct IHHe3 as [IH5 IH6];
  try solve [ repeat constructor; auto
                 | inversion H; repeat constructor; auto
                 | inversion H; inversion H2; repeat constructor; auto
                 | pick fresh Y and apply process_new; auto;
                   lapply (H0 Y); auto; intros Hp; destruct Hp as [Hp1 Hp2]; auto ].
(*
  Case "eq_swap".
    pick fresh Z and apply process_new...
    pick fresh Z' and apply process_new...
    fold open_cp_rec; unfold open_cp in *.
    assert (process (open_cp_rec 0 Z' (open_cp_rec 1 Z P1)) /\
                process (open_cp_rec 0 Z (open_cp_rec 1 Z' P1'))).
    apply H0... destruct H1...
    pick fresh W and apply process_new...
    pick fresh W' and apply process_new...
    fold open_cp_rec; unfold open_cp in *.
    assert (process (open_cp_rec 0 W (open_cp_rec 1 W' P1)) /\
                process (open_cp_rec 0 W' (open_cp_rec 1 W P1'))).
    apply H0... destruct H1...
*)
  Case "eq_extrude".
    constructor.
    inversion H0. subst.
    pick fresh Y and apply process_new...
    lapply (H4 Y); intros... unfold open_cp in *. simpl in *. 
    inversion H1. auto. auto.
Qed.

Lemma proc_eqm_regular : forall P1 P2,
  proc_eqm P1 P2 ->
  (process P1 -> process P2) /\ (process P2 -> process P1).
Proof.
  intros P1 P2 Heq.
  induction Heq; auto; destruct IHHeq as [IH1 IH2];
    apply proc_eq1_regular in H; destruct H as [H1 H2]; auto.
Qed.

Lemma proc_red_regular : forall P1 P2,
  proc_red P1 P2 ->
  process P1 /\ process P2.
Proof with auto.
  intros P1 P2 Hr. (proc_red_cases (induction Hr) Case); split...
  Case "red_ectx".
    apply process_exp.
    assert (expr e1 /\ expr e2). apply red_regular...
    destruct H2 as [H2 H3]...
    apply plug_regular with (M := M) (e := e1)...
    apply process_exp.
    assert (expr e1 /\ expr e2). apply red_regular...
    destruct H2 as [H2 H3]...
    apply plug_regular with (M := M) (e := e2)...
  Case "red_done".
    inversion H...
  Case "red_par".
    inversion H. destruct IHHr as [IH1 IH2]. constructor...
  Case "red_new".
    pick fresh Y and apply process_new...
    lapply (H1 Y)... intros. destruct H2 as [Hp Hp']...
  Case "red_go".
    constructor... apply plug_regular with (M := M) (e := (exp_go T v))...
    constructor... apply value_regular...
    pick fresh Y and apply process_new... constructor...
    constructor... apply open_ce_plug_regular with (M := M) (e := exp_src O T)...
    unfold open_ce. apply value_regular.
    repeat constructor. simpl...
    constructor. apply value_regular in H.
    constructor; fold open_ce_rec...
      rewrite <- open_ce_rec_expr...
      constructor... simpl...
  Case "red_pass".
    pick fresh Y and apply process_new...
    repeat constructor.
    apply open_ce_plug_regular
      with (M := M1) (e := exp_yield (exp_src O (typ_arrow T1 T2)))...
      unfold open_ce. apply expr_yield; fold open_ce_rec.
      constructor... simpl...
    apply open_ce_plug_regular
      with (M := M2) (e := exp_app (exp_snk O (typ_arrow T1 T2)) v)...
      unfold open_ce. apply expr_app; fold open_ce_rec.
      constructor... simpl...
      rewrite <- open_ce_rec_expr; apply value_regular...
    pick fresh Y and apply process_new...
    repeat constructor.
    apply open_ce_plug_regular
      with (M := M1) (e := exp_mpair v (exp_src O T2))...
      unfold open_ce. apply expr_mpair; fold open_ce_rec...
        rewrite <- open_ce_rec_expr; apply value_regular...
      constructor... simpl...
    apply open_ce_plug_regular
      with (M := M2) (e := exp_snk O T2)...
      unfold open_ce... constructor... simpl...
  Case "red_left".
    pick fresh Y and apply process_new...
    repeat constructor.
    apply open_ce_plug_regular
      with (M := M1) (e := exp_yield (exp_src O (typ_with T1 T2)))...
      unfold open_ce. simpl. apply expr_yield; fold open_ce_rec.
      constructor...
    apply open_ce_plug_regular
      with (M := M2) (e := exp_fst (exp_snk O (typ_with T1 T2)))...
      unfold open_ce. apply expr_fst; fold open_ce_rec.
      constructor... compute...
    pick fresh Y and apply process_new...
    repeat constructor.
    apply open_ce_plug_regular
        with (M := M1) (e := exp_inl T' (exp_src O T1))...
      unfold open_ce. apply expr_inl; fold open_ce_rec...
      constructor... simpl...
    apply open_ce_plug_regular
      with (M := M2) (e := exp_snk O T1)...
      constructor... simpl...
  Case "red_right".
    pick fresh Y and apply process_new...
    repeat constructor.
    apply open_ce_plug_regular
      with (M := M1) (e := exp_yield (exp_src O (typ_with T1 T2)))...
      unfold open_ce. simpl. apply expr_yield; fold open_ce_rec.
      constructor...
    apply open_ce_plug_regular
      with (M := M2) (e := exp_snd (exp_snk O (typ_with T1 T2)))...
      unfold open_ce. apply expr_snd; fold open_ce_rec.
      constructor... compute...
    pick fresh Y and apply process_new...
    repeat constructor.
    apply open_ce_plug_regular
      with (M := M1) (e := exp_inr T' (exp_src O T2))...
      unfold open_ce. apply expr_inr; fold open_ce_rec...
      constructor... simpl...
    apply open_ce_plug_regular
      with (M := M2) (e := exp_snk O T2)...
      constructor... simpl...
  Case "red_close".
    pick fresh Y and apply process_new... repeat constructor.
    apply open_ce_plug_regular
      with (M := M1) (e := exp_src (bchan 0) typ_answer)...
      unfold open_ce. apply expr_src... compute...
    apply open_ce_plug_regular
      with (M := M2) (e := exp_snk (bchan 0) typ_answer)...
      unfold open_ce. apply expr_snk... compute...
    pick fresh Y and apply process_new... repeat constructor.
    apply open_ce_plug_regular
      with (M := M1) (e := exp_unit)...
    apply open_ce_plug_regular
      with (M := M2) (e := exp_done (bchan 0))...
      unfold open_ce. apply expr_done. compute...
Qed.

Lemma proc_eq_proc_eqm : forall P1 P2,
  proc_eq P1 P2 -> proc_eqm P1 P2  /\ proc_eqm P2 P1.
Proof with try tauto.
  intros P1 P2 PEQ.
  (proc_eq_cases (induction PEQ) Case); split; auto...

  apply proc_eqm_trans with (P2:=P2); tauto.
  apply proc_eqm_trans with (P2:=P2); tauto.
  
  apply proc_eqm_par; tauto.

  apply proc_eqm_par; tauto.

  apply (proc_eqm_new L). 
  intros. lapply (H0 X); intros; auto. tauto.
  pick fresh X and apply process_new; auto.
  assert (process (open_cp P1 X) /\ process (open_cp P1' X)).
  apply proc_eq_regular. apply H; auto. tauto.

  apply (proc_eqm_new L). 
  intros. lapply (H0 X); intros; auto. tauto.
  pick fresh X and apply process_new; auto.
  assert (process (open_cp P1 X) /\ process (open_cp P1' X)).
  apply proc_eq_regular. apply H; auto. tauto.

  eapply proc_eqm_left. apply proc_eq1_comm.
  assert (proc_eqm (proc_par P2 P1) (proc_par P2' P1)).
  apply proc_eqm_parl. tauto.
  assert (proc_eqm (proc_par P2' P1) (proc_par P1 P2')).
  eapply proc_eqm_left. apply proc_eq1_comm. apply proc_eqm_refl.
  assert (proc_eqm (proc_par P1 P2') (proc_par P1' P2')).
  apply proc_eqm_parl. tauto.
  eapply proc_eqm_trans. apply H.
  eapply proc_eqm_trans. apply H0.
  eapply proc_eqm_trans. apply H1.
  eapply proc_eqm_left. apply proc_eq1_comm. apply proc_eqm_refl.

  assert (proc_eqm (proc_par P2' P1') (proc_par P2 P1')).
  apply proc_eqm_parl. tauto.
  assert (proc_eqm (proc_par P2 P1') (proc_par P1' P2)).
  eapply proc_eqm_left. apply proc_eq1_comm. apply proc_eqm_refl.
  assert (proc_eqm (proc_par P1' P2) (proc_par P1 P2)).
  apply proc_eqm_parl. tauto.
  eapply proc_eqm_trans. apply H.
  eapply proc_eqm_trans. apply H0.
  eapply proc_eqm_trans. apply H1. apply proc_eqm_refl.

  eapply proc_eqm_left.  apply proc_eq1_assoc.
  apply (proc_eqm_par P1 (proc_par P2 P3) P1' (proc_par P2' P3')).
  tauto.
  apply (proc_eqm_par P2 P3 P2' P3'); tauto.

  eapply proc_eqm_right.  apply proc_eq1_assoc.
  apply (proc_eqm_par (proc_par P1' P2') P3' (proc_par P1 P2) P3).
  apply (proc_eqm_par P1' P2' P1 P2); tauto.
  tauto.

  eapply proc_eqm_left. eapply proc_eq1_swap with (L := L). intros.
  rewrite H1.  auto. fsetdec. fsetdec.
  apply proc_eqm_refl.

  eapply proc_eqm_left. eapply proc_eq1_swap with (L := L). intros.
  rewrite H1.  auto. fsetdec. fsetdec.
  apply proc_eqm_refl.

  eapply proc_eqm_left. apply proc_eq1_extrude. auto. 
  apply proc_eqm_refl.

  eapply proc_eqm_right. apply proc_eq1_extrude. auto. 
  apply proc_eqm_refl.
Qed.

Lemma proc_eq1_proc_eq : forall P1 P2,
  process P1 ->
  proc_eq1 P1 P2 ->
  proc_eq P1 P2.
Proof with auto.
  intros P1 P2 HP PEQ1.
  (proc_eq1_cases (induction PEQ1) Case); inversion HP; subst...
  Case "proc_eq1_new".
    apply eq_new with (L := L `union` L0)...
  Case "proc_eq1_assoc".
    inversion H1; subst...
  Case "proc_eq1_swap".
    apply eq_swap with (L := L `union` L0)...
    apply process_new with (L := L `union` L0)...
    intros. lapply (H3 X)... intros. inversion H1; subst.
    apply process_new with
      (L := (singleton X) `union` L `union` L0 `union` L1)...
    intros Y NI. fold open_cp_rec.
    lapply (H7 Y)... intros. rewrite <- H...
    unfold open_cp in *.
    apply process_switch; auto.
  Case "proc_eq1_extrude".
    apply eq_extrude...
Qed.

Lemma proc_eqm_proc_eq : forall P1 P2,
  process P1 ->
  process P2 ->
  proc_eqm P1 P2 ->
  proc_eq P1 P2.
Proof.
  intros P1 P2 HP1 HP2 PEQM.
  induction PEQM; intros.
  apply eq_refl; auto.

  apply (eq_trans P1 P2 P3).
  apply proc_eq1_proc_eq. auto. auto. apply IHPEQM; auto.

  apply proc_eq1_regular in H. intuition.
  
  apply (eq_trans P1 P2 P3).
  apply eq_sym.
  apply proc_eq1_proc_eq; auto.
  apply proc_eq1_regular in H. intuition.
  apply IHPEQM; auto.
  apply proc_eq1_regular in H. intuition.
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

    The other hints try outright to solve their respective subgoals *)

(* Some hints removed thanks to vwf conversion. *)

(*Hint Extern 1 (wf_chan ?E ?C) =>
  match goal with
  | H: snk _ _ _ _ |- _ => apply (proj1 (snk_regular _ _ _ _ _ _ H))
  | H: src _ _ _ _ |- _ => apply (proj1 (src_regular _ _ _ _ _ _ H))
  end.*)

Hint Extern 1 (wf_env ?E) =>
  match goal with
  | H: dual _ _ _ |- _ => apply (proj1 (dual_regular _ _ _ H))
  end.

(*Hint Extern 1 (wf_lenv ?G ?D) =>
  match goal with
  | H: typing _ _ _ _ _ |- _ => apply (proj1 (proj2 (typing_regular _ _ _ _ _ H)))
  end.*)

Hint Extern 1 (vwf_envs ?E ?Q ?D) =>
  match goal with
  | H: typing _ _ _ _ _ |- _ => apply (proj1 (typing_regular _ _ _ _ _ H))
  end.

Hint Extern 1 (wf_cenv ?G ?Q) =>
  match goal with
(* | H: typing _ _ _ _ _ |- _ => apply (proj1 (proj2 (proj2 (typing_regular _ _ _ _ _ H)))) *)
  | H: proc_typing _ _ _ |- _ => apply (proj1 (proc_typing_regular _ _ _ H))
  end.

Hint Extern 1 (wf_typ ?E ?T) =>
  match goal with
  | H: typing E _ _ _ T |- _ => apply (proj2 (proj2 (typing_regular _ _ _ _ _ H)))
  | H: proc_typing E _ T |- _ => apply (proj2 (proj2 (proc_typing_regular _ _ _ H)))
  end.

Hint Extern 1 (wf_proto ?E ?T) =>
  match goal with
  | H: dual _ _ _ |- _ => apply (proj1 (proj2 (dual_regular _ _ _ H)))
(*  | H: snk _ _ _ _ |- _ => apply (proj1 (proj2 (snk_regular _ _ _ _ _ _ H)))
  | H: src _ _ _ _ |- _ => apply (proj1 (proj2 (src_regular _ _ _ _ _ _ H)))*)
  end.

Hint Extern 1 (type ?T) =>
  let go E := apply (type_from_wf_typ E); auto in
  match goal with
  | H: typing ?E _ _ _ T |- _ => go E
  end.

Hint Extern 1 (expr ?e) =>
  match goal with
  | H: typing _ _ _ ?e _ |- _ => apply (proj1 (proj2 (typing_regular _ _ _ _ _ H)))
  | H: red ?e _ |- _ => apply (proj1 (red_regular _ _ H))
  | H: red _ ?e |- _ => apply (proj2 (red_regular _ _ H))
  | H: value ?e |- _ => apply (value_regular _ H)
  end.

Hint Extern 1 (process ?P) =>
  match goal with
  | H: proc_typing _ ?P _ |- _ => apply (proj1 (proj2 (proc_typing_regular _ _ _ H)))
  | H: proc_eq ?P _ |- _ => apply (proj1 (proc_eq_regular _ _ H))
  | H: proc_eq _ ?P |- _ => apply (proj2 (proc_eq_regular _ _ H))
  | H: proc_red ?P _ |- _ => apply (proj1 (proc_red_regular _ _ H))
  | H: proc_red _ ?P |- _ => apply (proj2 (proc_red_regular _ _ H))
  | H: canon_inner ?P |- _ => apply (canon_inner_regular _ H)
  | H: canon_outer ?P |- _ => apply (canon_outer_regular _ H)
  end.