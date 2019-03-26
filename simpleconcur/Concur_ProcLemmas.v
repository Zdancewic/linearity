(** Lemmas about evaluation contexts, proc_eq, proc_eq1, and proc_eqm *)

Require Export Concur_ExpSoundness.

Axiom skip : False.
Ltac skip := assert False; [ apply skip | contradiction ].

(* ********************************************************************** *)
(** These shoud probably be in the Infrastructure or LemmasInit file... *)

Lemma fv_cc_open_cc_rec: forall X J C,
  fv_cc (open_cc_rec J (fchan X) C) [<=] (fv_cc C) `union` (singleton X) /\
  fv_cc C [<=] fv_cc (open_cc_rec J (fchan X) C).
Proof with simpl; auto; try fsetdec.
  intros. induction C...
    destruct (J == n); split...
Qed.

Lemma fv_ce_open_ce_rec: forall X J e,
  fv_ce (open_ce_rec J (fchan X) e) [<=] (fv_ce e) `union` (singleton X) /\
  fv_ce e [<=] fv_ce (open_ce_rec J (fchan X) e).
Proof with simpl; auto; try fsetdec.
  intros. induction e; try solve [ split; simpl; auto; try fsetdec ]...
    apply fv_cc_open_cc_rec...
    apply fv_cc_open_cc_rec...
    apply fv_cc_open_cc_rec...
Qed.

Lemma fv_cp_open_cp_rec: forall X J P,
  fv_cp (open_cp_rec J (fchan X) P) [<=] (fv_cp P) `union` (singleton X) /\
  fv_cp P [<=] fv_cp (open_cp_rec J (fchan X) P).
Proof with simpl; auto; try fsetdec.
  intros. revert J. induction P; intros; try solve [ split; simpl; auto; try fsetdec ]...
    apply fv_ce_open_ce_rec...
    assert (fv_cp (open_cp_rec J X P1)[<=]union (fv_cp P1) (singleton X) /\
                fv_cp P1[<=]fv_cp (open_cp_rec J X P1))...
      assert (fv_cp (open_cp_rec J X P2)[<=]union (fv_cp P2) (singleton X) /\
                  fv_cp P2[<=]fv_cp (open_cp_rec J X P2))...
      intuition...
Qed.

Lemma fv_cc_open_cc: forall C X,
  fv_cc (open_cc C (fchan X)) [<=] (fv_cc C) `union` (singleton X) /\
  fv_cc C [<=] fv_cc (open_cc C (fchan X)).
Proof.
  intros. unfold open_cc. apply fv_cc_open_cc_rec.
Qed.

Lemma fv_ce_open_ce: forall e X,
  fv_ce (open_ce e (fchan X)) [<=] (fv_ce e) `union` (singleton X) /\
  fv_ce e [<=] fv_ce (open_ce e (fchan X)).
Proof.
  intros. unfold open_ce. apply fv_ce_open_ce_rec.
Qed.

Lemma fv_cp_open_cp: forall P X,
  fv_cp (open_cp P (fchan X)) [<=] (fv_cp P) `union` (singleton X) /\
  fv_cp P [<=] fv_cp (open_cp P (fchan X)).
Proof.
  intros. unfold open_cp. apply fv_cp_open_cp_rec.
Qed.

Lemma fv_cp_proc_eq: forall P1 P2,
  proc_eq P1 P2 ->
  fv_cp P1 [=] fv_cp P2.
Proof with auto; try fsetdec.
  intros. induction H...
    simpl...
    simpl. pick fresh X. lapply (H0 X)... intros.
      assert (fv_cp (open_cp P1 (fchan X)) [<=] (fv_cp P1) `union` (singleton X) /\
                  fv_cp P1 [<=] fv_cp (open_cp P1 (fchan X))).
        apply fv_cp_open_cp...
      assert (fv_cp (open_cp P1' (fchan X)) [<=] (fv_cp P1') `union` (singleton X) /\
                  fv_cp P1' [<=] fv_cp (open_cp P1' (fchan X))).
        apply fv_cp_open_cp...
      intuition. fsetdec.
    simpl...
    simpl...
    simpl. pick fresh X. pick fresh Y. assert (X `notin` L)...
      lapply (H1 X Y H2)... intros.
      skip.
Qed.

Lemma value_swap : forall v X Y,
  value v -> value (swap_ce X Y v).
Proof.
  intros.
  induction H; intros; simpl in *; constructor;
      try eapply expr_swap in H; eauto.
Qed.

Fixpoint swap_ectx (X : atom) (Y : atom) (M : ectx) {struct M} : ectx :=
  match M with
  | ectx_hole => ectx_hole
  | ectx_seq e M H => ectx_seq (swap_ce X Y e) (swap_ectx X Y M)
                                      (expr_swap e X Y H)
  | ectx_appl e M H => ectx_appl (swap_ce X Y e) (swap_ectx X Y M)
                                       (expr_swap e X Y H)
  | ectx_appr v H M => ectx_appr (swap_ce X Y v) (value_swap v X Y H)
                                       (swap_ectx X Y M)
  | ectx_fst M => ectx_fst (swap_ectx X Y M)
  | ectx_snd M => ectx_snd (swap_ectx X Y M)
  | ectx_mpairl e M H => ectx_mpairl (swap_ce X Y e) (swap_ectx X Y M)
                                          (expr_swap e X Y H)
  | ectx_mpairr v H M => ectx_mpairr (swap_ce X Y v) (value_swap v X Y H)
                                          (swap_ectx X Y M)
  | ectx_let e M H => ectx_let (swap_ce X Y e) (swap_ectx X Y M)
                                    (expr_swap e X Y H)
  | ectx_inl T H M => ectx_inl T H (swap_ectx X Y M)
  | ectx_inr T H M => ectx_inr T H (swap_ectx X Y M)
  | ectx_case e2 e3 M H2 H3 => ectx_case (swap_ce X Y e2)
                                                     (swap_ce X Y e3) (swap_ectx X Y M)
                                                     (expr_swap e2 X Y H2) (expr_swap e3 X Y H3)
  | ectx_go T H M => ectx_go T H (swap_ectx X Y M)
  | ectx_yield M => ectx_yield (swap_ectx X Y M)
  end.

Lemma open_cp_exp_eq_open_ce: forall e i X P,
  proc_exp e = open_cp_rec i X P ->
  exists e', e = open_ce_rec i X e' /\ P = proc_exp e'.
Proof with auto.
  intros. induction P.
    exists e0. split... simpl in H. inversion H...
    simpl in H. inversion H.
    simpl in H. inversion H.
Qed.

Lemma swap_open_close_ce : forall e X Y i,
  expr e ->
  Y `notin` fv_ce e ->
  swap_ce X Y e = open_ce_rec i Y (close_ce_rec i X e).
Proof with auto.
  intros. rewrite <- (open_close_ce_rec X e i) at 1...
  apply swap_open_ce2...
    apply fv_close_ce_aux.
    apply notin_close_ce...
Qed.

Lemma swap_open_cp2 : forall P k X Y,
  X `notin` fv_cp P ->
  Y `notin` fv_cp P -> 
  swap_cp X Y (open_cp_rec k X P) = open_cp_rec k Y P.
Proof.
  induction P; intros k X Y NI1 NI2; simpl in *; (
    try rewrite IHP;
    try rewrite IHP1;
    try rewrite IHP2;
    try rewrite swap_open_ce2
  ); auto.
Qed.

Lemma swap_open_close_cp : forall P X Y i,
  process P ->
  Y `notin` fv_cp P ->
  swap_cp X Y P = open_cp_rec i Y (close_cp_rec i X P).
Proof with auto.
  intros. rewrite <- (open_close_cp_rec X P i) at 1...
  apply swap_open_cp2...
    apply fv_close_cp_aux.
    apply notin_close_cp...
Qed.

Lemma plug_swap_ce : forall M e f X Y,
  expr e ->
  plug M e f ->
  plug (swap_ectx X Y M) (swap_ce X Y e) (swap_ce X Y f).
Proof with auto.
  intros M e f X Y Expr Plug.
  assert (expr f). eapply plug_regular; eauto.
  generalize dependent f.
  induction M; intros; inversion Plug; subst; try solve
      [ auto
      | inversion H; subst; simpl in *; constructor; apply IHM; auto ].
Qed.

Lemma swap_open_ee1 : forall e u X Y k,
  swap_ce X Y (open_ee_rec k u e) = open_ee_rec k (swap_ce X Y u) (swap_ce X Y e).
Proof.
  induction e; intros; simpl in *; (
    try rewrite IHe;
    try rewrite IHe1;
    try rewrite IHe2;
    try rewrite IHe3
  ); auto.
  destruct (k == n); auto.
Qed.

Lemma red_swap_ce : forall e1 e2 X Y,
  red e1 e2 ->
  red (swap_ce X Y e1) (swap_ce X Y e2).
Proof with auto using expr_swap.
  intros. (red_cases (induction H) Case); simpl; try solve
      [ constructor; auto; apply value_swap with (X := X) (Y := Y) in H;
          auto using expr_swap ].
    Case "red_seq".
      constructor...
      apply expr_swap with (X := X) (Y := Y) in H...
    Case "red_app".
      unfold open_ee. rewrite swap_open_ee1...
      fold (open_ee (swap_ce X Y e1) (swap_ce X Y v2)).
      apply red_app...
        apply value_swap with (X := X) (Y := Y) in H...
        apply value_swap...
    Case "red_app_src".
      constructor...
        apply value_swap with (X := X) (Y := Y) in H...
        apply value_swap with (X := X) (Y := Y) in H0...
Qed.

(* ********************************************************************** *)
(** Evaluation contexts *)

Lemma typing_unique_typ: forall E e D1 D2 Q1 Q2 T1 T2,
  cenv_agree E Q1 Q2 ->
  lenv_agree E Q1 D1 D2 ->
  lenv_agree E Q2 D1 D2 ->
  typing E D1 Q1 e T1 ->
  typing E D2 Q2 e T2 ->
  T1 = T2.
Proof with auto.
  intros E e D1 D2 Q1 Q2 T1 T2 CA LA1 LA2 Typ1 Typ2.
  generalize dependent T2.
  generalize dependent D2. generalize dependent Q2.
  (typing_cases (induction Typ1) Case); intros; inversion Typ2; subst...
  Case "typing_var".
    inversion LA2; subst; simpl_env in *; try fsetdec...
  Case "typing_seq".
    assert (cenv_agree E Q2 Q5 /\ lenv_agree E Q2 D2 D5 /\ lenv_agree E Q5 D2 D5).
      eapply agree_regular_right; eauto.
    intuition. apply IHTyp1_2 with (D3 := D5) (Q3 := Q5)...
  Case "typing_abs".
    f_equal. pick fresh x.
    apply H1 with (x := x) (Q2 := Q2) (D2 := [(x, lbind_typ T1)] ++ D2)...
  Case "typing_app".
    assert (cenv_agree E Q1 Q4 /\ lenv_agree E Q1 D1 D4 /\ lenv_agree E Q4 D1 D4).
      eapply agree_regular_left; eauto.
    intuition. assert (typ_arrow T1 T2 = typ_arrow T3 T0).
      apply IHTyp1_1 with (Q2 := Q4) (D2 := D4)...
    inversion H5...
  Case "typing_apair".
    f_equal.
      eapply IHTyp1_1; eauto.
      eapply IHTyp1_2; eauto.
  Case "typing_fst".
    assert (typ_with T1 T2 = typ_with T0 T4).
      apply IHTyp1 with (Q2 := Q2) (D2 := D2)...
    inversion H...
  Case "typing_snd".
    assert (typ_with T1 T2 = typ_with T3 T0).
      apply IHTyp1 with (Q2 := Q2) (D2 := D2)...
    inversion H...
  Case "typing_mpair".
    assert (cenv_agree E Q1 Q4 /\ lenv_agree E Q1 D1 D4 /\ lenv_agree E Q4 D1 D4).
      eapply agree_regular_left; eauto.
    assert (cenv_agree E Q2 Q5 /\ lenv_agree E Q2 D2 D5 /\ lenv_agree E Q5 D2 D5).
      eapply agree_regular_right; eauto.
    intuition. f_equal.
      apply IHTyp1_1 with (Q2 := Q4) (D2 := D4)...
      apply IHTyp1_2 with (Q3 := Q5) (D3 := D5)...
  Case "typing_let".
    assert (cenv_agree E Q2 Q5 /\ lenv_agree E Q2 D2 D5 /\ lenv_agree E Q5 D2 D5).
      eapply agree_regular_right; eauto.
    intuition.
    assert (typ_arrow T1 (typ_arrow T2 T3) = typ_arrow T4 (typ_arrow T5 T0)).
      apply IHTyp1_2 with (Q3 := Q5) (D3 := D5)...
    inversion H5...
  Case "typing_case".
    assert (cenv_agree E Q2 Q5 /\ lenv_agree E Q2 D2 D5 /\ lenv_agree E Q5 D2 D5).
      eapply agree_regular_right; eauto.
    intuition. assert (typ_arrow T1 T3 = typ_arrow T4 T0).
      apply IHTyp1_2 with (Q3 := Q5) (D3 := D5)...
    inversion H3...
  Case "typing_go".
    eapply dual_unique_src; eauto.
  Case "typing_yield".
    assert (typ_src T1 = typ_src T2).
      apply IHTyp1 with (Q2 := Q2) (D2 := D2)...
    inversion H...
  Case "typing_src".
    apply dual_unique_src with (T1 := T') in H8...
Qed.

Lemma plug_exists: forall M e,
  exists f, plug M e f.
Proof with auto.
  intros. (ectx_cases (induction M) Case).
  Case "ectx_hole".
    exists e...
  Case "ectx_seq".
    destruct IHM as [f H].
    exists (exp_seq f e0)...
  Case "ectx_appl".
    destruct IHM as [f H].
    exists (exp_app f e0)...
  Case "ectx_appr".
    destruct IHM as [f H].
    exists (exp_app v f)...
  Case "ectx_fst".
    destruct IHM as [f H].
    exists (exp_fst f)...
  Case "ectx_snd".
    destruct IHM as [f H].
    exists (exp_snd f)...
  Case "ectx_mpairl".
    destruct IHM as [f H].
    exists (exp_mpair f e0)...
  Case "ectx_mpairr".
    destruct IHM as [f H].
    exists (exp_mpair v f)...
  Case "ectx_let".
    destruct IHM as [f H].
    exists (exp_let f e0)...
  Case "ectx_inl".
    destruct IHM as [f H].
    exists (exp_inl T f)...
  Case "ectx_inr".
    destruct IHM as [f H].
    exists (exp_inr T f)...
  Case "ectx_case".
    destruct IHM as [f H].
    exists (exp_case f e2 e3)...
  Case "ectx_go".
    destruct IHM as [f H].
    exists (exp_go T f)...
  Case "ectx_yield".
    destruct IHM as [f H].
    exists (exp_yield f)...
Qed.

Lemma plug_typing: forall E Df Qf M e f Tf,
  plug M e f ->
  typing E Df Qf f Tf ->
  exists Dm, exists De, exists Qm, exists Qe, exists Te,
    cenv_split_exp E Qm Qe Qf /\ lenv_split E Qf Dm De Df /\
    typing E De Qe e Te /\ ectx_typing E Dm Qm M Te Tf.
Proof with auto.
  intros E Df Qf M e f Tf Plug Typ.
  generalize dependent Tf. generalize dependent Qf.
  generalize dependent Df. generalize dependent E.
  (plug_cases (induction Plug) Case); intros.
  Case "plug_hole".
    exists lempty. exists Df. exists cempty. exists Qf. exists Tf.
    repeat split...
      apply cenv_split_exp_left_id. apply typing_regular in Typ; intuition...
      apply lenv_split_left_id. apply typing_regular in Typ; intuition...
      constructor... apply typing_regular in Typ. intuition.
        apply vwf_envs_unpack in H. intuition.
  Case "plug_seq".
    inversion Typ; subst. apply IHPlug in H1.
    destruct H1 as [Dm [De [Qm [Qe [Te [CS [LS [Typ' ETyp']]]]]]]].
    apply lenv_split_commute in LS.
    apply lenv_split_disjoint_cenv with (Q' := Qf) in LS.
    apply lenv_split_assoc with (D11 := De) (D12 := Dm) in H6...
    destruct H6 as [Dm' [LS' LS'']].
    apply cenv_split_exp_commute in CS.
    apply cenv_split_exp_assoc with (Q11 := Qe) (Q12 := Qm) in H8...
    destruct H8 as [Qm' [CS' CS'']].
    exists Dm'. exists De. exists Qm'. exists Qe. exists Te.
    repeat split...
      apply cenv_split_exp_commute...
      apply lenv_split_commute...
    econstructor; eauto.
      apply lenv_split_disjoint_cenv with (Q := Qf)...
        apply wf_lenv_split in LS'. apply vwf_envs_unpack in LS'.
        apply vwf_envs_pack; intuition.
          apply dom_cenv_split_exp in CS''. unfold disjoint in *. fsetdec.
    eapply wf_lenv_split_left; eauto.
  Case "plug_appl".
    inversion Typ; subst. apply IHPlug in H1.
    destruct H1 as [Dm [De [Qm [Qe [Te [CS [LS [Typ' ETyp']]]]]]]].
    apply lenv_split_commute in LS.
    apply lenv_split_disjoint_cenv with (Q' := Qf) in LS.
    apply lenv_split_assoc with (D11 := De) (D12 := Dm) in H6...
    destruct H6 as [Dm' [LS' LS'']].
    apply cenv_split_exp_commute in CS.
    apply cenv_split_exp_assoc with (Q11 := Qe) (Q12 := Qm) in H8...
    destruct H8 as [Qm' [CS' CS'']].
    exists Dm'. exists De. exists Qm'. exists Qe. exists Te.
    repeat split...
      apply cenv_split_exp_commute...
      apply lenv_split_commute...
    econstructor; eauto.
      apply lenv_split_disjoint_cenv with (Q := Qf)...
        apply wf_lenv_split in LS'. apply vwf_envs_unpack in LS'.
        apply vwf_envs_pack; intuition.
          apply dom_cenv_split_exp in CS''. unfold disjoint in *. fsetdec.
    eapply wf_lenv_split_left; eauto.
  Case "plug_appr".
    inversion Typ; subst. apply IHPlug in H2.
    destruct H2 as [Dm [De [Qm [Qe [Te [CS [LS [Typ' ETyp']]]]]]]].
    apply lenv_split_commute in LS.
    apply lenv_split_commute in H6.
    apply lenv_split_disjoint_cenv with (Q' := Qf) in LS.
    apply lenv_split_assoc with (D11 := De) (D12 := Dm) in H6...
    destruct H6 as [Dm' [LS' LS'']].
    apply cenv_split_exp_commute in CS.
    apply cenv_split_exp_commute in H8.
    apply cenv_split_exp_assoc with (Q11 := Qe) (Q12 := Qm) in H8...
    destruct H8 as [Qm' [CS' CS'']].
    exists Dm'. exists De. exists Qm'. exists Qe. exists Te.
    repeat split...
      apply cenv_split_exp_commute...
      apply lenv_split_commute...
    econstructor; eauto.
      apply lenv_split_commute.
      apply lenv_split_disjoint_cenv with (Q := Qf)...
        apply wf_lenv_split in LS'. apply vwf_envs_unpack in LS'.
        apply vwf_envs_pack; intuition.
          apply dom_cenv_split_exp in CS''. unfold disjoint in *. fsetdec.
      apply cenv_split_exp_commute...
    eapply wf_lenv_split_left; eauto.
  Case "plug_fst".
    inversion Typ; subst. apply IHPlug in H3.
    destruct H3 as [Dm [De [Qm [Qe [Te [CS [LS [Typ' ETyp']]]]]]]].
    exists Dm. exists De. exists Qm. exists Qe. exists Te. intuition.
    econstructor; eauto.
  Case "plug_snd".
    inversion Typ; subst. apply IHPlug in H3.
    destruct H3 as [Dm [De [Qm [Qe [Te [CS [LS [Typ' ETyp']]]]]]]].
    exists Dm. exists De. exists Qm. exists Qe. exists Te. intuition.
    econstructor; eauto.
  Case "plug_mpairl".
    inversion Typ; subst. apply IHPlug in H1.
    destruct H1 as [Dm [De [Qm [Qe [Te [CS [LS [Typ' ETyp']]]]]]]].
    apply lenv_split_commute in LS.
    apply lenv_split_disjoint_cenv with (Q' := Qf) in LS.
    apply lenv_split_assoc with (D11 := De) (D12 := Dm) in H6...
    destruct H6 as [Dm' [LS' LS'']].
    apply cenv_split_exp_commute in CS.
    apply cenv_split_exp_assoc with (Q11 := Qe) (Q12 := Qm) in H8...
    destruct H8 as [Qm' [CS' CS'']].
    exists Dm'. exists De. exists Qm'. exists Qe. exists Te.
    repeat split...
      apply cenv_split_exp_commute...
      apply lenv_split_commute...
    econstructor; eauto.
      apply lenv_split_disjoint_cenv with (Q := Qf)...
        apply wf_lenv_split in LS'. apply vwf_envs_unpack in LS'.
        apply vwf_envs_pack; intuition.
          apply dom_cenv_split_exp in CS''. unfold disjoint in *. fsetdec.
    eapply wf_lenv_split_left; eauto.
  Case "plug_mpairr".
    inversion Typ; subst. apply IHPlug in H2.
    destruct H2 as [Dm [De [Qm [Qe [Te [CS [LS [Typ' ETyp']]]]]]]].
    apply lenv_split_commute in LS.
    apply lenv_split_commute in H6.
    apply lenv_split_disjoint_cenv with (Q' := Qf) in LS.
    apply lenv_split_assoc with (D11 := De) (D12 := Dm) in H6...
    destruct H6 as [Dm' [LS' LS'']].
    apply cenv_split_exp_commute in CS.
    apply cenv_split_exp_commute in H8.
    apply cenv_split_exp_assoc with (Q11 := Qe) (Q12 := Qm) in H8...
    destruct H8 as [Qm' [CS' CS'']].
    exists Dm'. exists De. exists Qm'. exists Qe. exists Te.
    repeat split...
      apply cenv_split_exp_commute...
      apply lenv_split_commute...
    econstructor; eauto.
      apply lenv_split_commute.
      apply lenv_split_disjoint_cenv with (Q := Qf)...
        apply wf_lenv_split in LS'. apply vwf_envs_unpack in LS'.
        apply vwf_envs_pack; intuition.
          apply dom_cenv_split_exp in CS''. unfold disjoint in *. fsetdec.
      apply cenv_split_exp_commute...
    eapply wf_lenv_split_left; eauto.
  Case "plug_let".
    inversion Typ; subst. apply IHPlug in H1.
    destruct H1 as [Dm [De [Qm [Qe [Te [CS [LS [Typ' ETyp']]]]]]]].
    apply lenv_split_commute in LS.
    apply lenv_split_disjoint_cenv with (Q' := Qf) in LS.
    apply lenv_split_assoc with (D11 := De) (D12 := Dm) in H6...
    destruct H6 as [Dm' [LS' LS'']].
    apply cenv_split_exp_commute in CS.
    apply cenv_split_exp_assoc with (Q11 := Qe) (Q12 := Qm) in H8...
    destruct H8 as [Qm' [CS' CS'']].
    exists Dm'. exists De. exists Qm'. exists Qe. exists Te.
    repeat split...
      apply cenv_split_exp_commute...
      apply lenv_split_commute...
    econstructor; eauto.
      apply lenv_split_disjoint_cenv with (Q := Qf)...
        apply wf_lenv_split in LS'. apply vwf_envs_unpack in LS'.
        apply vwf_envs_pack; intuition.
          apply dom_cenv_split_exp in CS''. unfold disjoint in *. fsetdec.
    eapply wf_lenv_split_left; eauto.
  Case "plug_inl".
    inversion Typ; subst. apply IHPlug in H5.
    destruct H5 as [Dm [De [Qm [Qe [Te [CS [LS [Typ' ETyp']]]]]]]].
    exists Dm. exists De. exists Qm. exists Qe. exists Te. intuition.
    econstructor; eauto.
  Case "plug_inr".
    inversion Typ; subst. apply IHPlug in H5.
    destruct H5 as [Dm [De [Qm [Qe [Te [CS [LS [Typ' ETyp']]]]]]]].
    exists Dm. exists De. exists Qm. exists Qe. exists Te. intuition.
    econstructor; eauto.
  Case "plug_case".
    inversion Typ; subst. apply IHPlug in H2.
    destruct H2 as [Dm [De [Qm [Qe [Te [CS [LS [Typ' ETyp']]]]]]]].
    apply lenv_split_commute in LS.
    apply lenv_split_disjoint_cenv with (Q' := Qf) in LS.
    apply lenv_split_assoc with (D11 := De) (D12 := Dm) in H9...
    destruct H9 as [Dm' [LS' LS'']].
    apply cenv_split_exp_commute in CS.
    apply cenv_split_exp_assoc with (Q11 := Qe) (Q12 := Qm) in H10...
    destruct H10 as [Qm' [CS' CS'']].
    exists Dm'. exists De. exists Qm'. exists Qe. exists Te.
    repeat split...
      apply cenv_split_exp_commute...
      apply lenv_split_commute...
    econstructor; eauto.
      apply lenv_split_disjoint_cenv with (Q := Qf)...
        apply wf_lenv_split in LS'. apply vwf_envs_unpack in LS'.
        apply vwf_envs_pack; intuition.
          apply dom_cenv_split_exp in CS''. unfold disjoint in *. fsetdec.
    eapply wf_lenv_split_left; eauto.
  Case "plug_go".
    inversion Typ; subst. apply IHPlug in H4.
    destruct H4 as [Dm [De [Qm [Qe [Te [CS [LS [Typ' ETyp']]]]]]]].
    exists Dm. exists De. exists Qm. exists Qe. exists Te. intuition.
    econstructor; eauto.
  Case "plug_yield".
    inversion Typ; subst. apply IHPlug in H3.
    destruct H3 as [Dm [De [Qm [Qe [Te [CS [LS [Typ' ETyp']]]]]]]].
    exists Dm. exists De. exists Qm. exists Qe. exists Te. intuition.
    econstructor; eauto.
Qed.

Lemma ectx_typing_plug: forall E D1 D2 D3 Q1 Q2 Q3 M e f T T',
  ectx_typing E D1 Q1 M T T' ->
  typing E D2 Q2 e T ->
  plug M e f ->
  cenv_split_exp E Q1 Q2 Q3 ->
  lenv_split E Q3 D1 D2 D3 ->
  typing E D3 Q3 f T'.
Proof with auto.
  intros E D1 D2 D3 Q1 Q2 Q3 M e f T T'. revert D1 D2 D3 Q1 Q2 Q3 f T'.
  (ectx_cases (induction M) Case);
      intros D1 D2 D3 Q1 Q2 Q3 f T' ETyp Typ' Plug CS LS;
      inversion ETyp; inversion Plug; subst; try solve [econstructor; eauto].
    Case "ectx_hole".
      apply cenv_split_exp_empty_left in CS.
      apply lenv_split_empty_left in LS. subst...
    Case "ectx_seq".
      assert (exists Q', cenv_split_exp E Q0 Q2 Q' /\ cenv_split_exp E Q4 Q' Q3).
        apply cenv_split_exp_assoc with (Q13 := Q1)...
          apply cenv_split_exp_commute...
      destruct H as [Q' [CS1 CS2]].
      assert (exists D', lenv_split E Q3 D0 D2 D' /\ lenv_split E Q3 D4 D' D3).
        apply lenv_split_assoc with (D13 := D1)...
        apply lenv_split_commute. apply lenv_split_disjoint_cenv with (Q := Q1)...
          apply wf_lenv_split_left in LS...
      destruct H as [D' [LS1 LS2]].
      apply typing_seq with (D1 := D') (D2 := D4) (Q1 := Q') (Q2 := Q4)...
        eapply IHM; eauto.
          eapply lenv_split_strengthen_cenv_right; eauto.
          apply cenv_split_exp_proc; eauto.
        apply lenv_split_commute...
        apply cenv_split_exp_commute...
    Case "ectx_appl".
      assert (exists Q', cenv_split_exp E Q0 Q2 Q' /\ cenv_split_exp E Q4 Q' Q3).
        apply cenv_split_exp_assoc with (Q13 := Q1)...
          apply cenv_split_exp_commute...
      destruct H as [Q' [CS1 CS2]].
      assert (exists D', lenv_split E Q3 D0 D2 D' /\ lenv_split E Q3 D4 D' D3).
        apply lenv_split_assoc with (D13 := D1)...
        apply lenv_split_commute. apply lenv_split_disjoint_cenv with (Q := Q1)...
          apply wf_lenv_split_left in LS...
      destruct H as [D' [LS1 LS2]].
      apply typing_app with (D1 := D') (D2 := D4) (Q1 := Q') (Q2 := Q4) (T1 := T1)...
        eapply IHM; eauto.
          eapply lenv_split_strengthen_cenv_right; eauto.
          apply cenv_split_exp_proc; eauto.
        apply lenv_split_commute...
        apply cenv_split_exp_commute...
    Case "ectx_appr".
      assert (exists Q', cenv_split_exp E Q4 Q2 Q' /\ cenv_split_exp E Q0 Q' Q3).
        apply cenv_split_exp_assoc with (Q13 := Q1)...
      destruct H as [Q' [CS1 CS2]].
      assert (exists D', lenv_split E Q3 D4 D2 D' /\ lenv_split E Q3 D0 D' D3).
        apply lenv_split_assoc with (D13 := D1)...
        apply lenv_split_disjoint_cenv with (Q := Q1)...
          apply wf_lenv_split_left in LS...
      destruct H as [D' [LS1 LS2]].
      apply typing_app with (D1 := D0) (D2 := D') (Q1 := Q0) (Q2 := Q') (T1 := T1)...
        eapply IHM; eauto.
          eapply lenv_split_strengthen_cenv_right; eauto.
          apply cenv_split_exp_proc; eauto.
    Case "ectx_mpairl".
      assert (exists Q', cenv_split_exp E Q0 Q2 Q' /\ cenv_split_exp E Q4 Q' Q3).
        apply cenv_split_exp_assoc with (Q13 := Q1)...
          apply cenv_split_exp_commute...
      destruct H as [Q' [CS1 CS2]].
      assert (exists D', lenv_split E Q3 D0 D2 D' /\ lenv_split E Q3 D4 D' D3).
        apply lenv_split_assoc with (D13 := D1)...
        apply lenv_split_commute. apply lenv_split_disjoint_cenv with (Q := Q1)...
          apply wf_lenv_split_left in LS...
      destruct H as [D' [LS1 LS2]].
      apply typing_mpair with (D1 := D') (D2 := D4) (Q1 := Q') (Q2 := Q4)...
        eapply IHM; eauto.
          eapply lenv_split_strengthen_cenv_right; eauto.
          apply cenv_split_exp_proc; eauto.
        apply lenv_split_commute...
        apply cenv_split_exp_commute...
    Case "ectx_mpairr".
      assert (exists Q', cenv_split_exp E Q4 Q2 Q' /\ cenv_split_exp E Q0 Q' Q3).
        apply cenv_split_exp_assoc with (Q13 := Q1)...
      destruct H as [Q' [CS1 CS2]].
      assert (exists D', lenv_split E Q3 D4 D2 D' /\ lenv_split E Q3 D0 D' D3).
        apply lenv_split_assoc with (D13 := D1)...
        apply lenv_split_disjoint_cenv with (Q := Q1)...
          apply wf_lenv_split_left in LS...
      destruct H as [D' [LS1 LS2]].
      apply typing_mpair with (D1 := D0) (D2 := D') (Q1 := Q0) (Q2 := Q')...
        eapply IHM; eauto.
          eapply lenv_split_strengthen_cenv_right; eauto.
          apply cenv_split_exp_proc; eauto.
    Case "ectx_let".
      assert (exists Q', cenv_split_exp E Q0 Q2 Q' /\ cenv_split_exp E Q4 Q' Q3).
        apply cenv_split_exp_assoc with (Q13 := Q1)...
          apply cenv_split_exp_commute...
      destruct H as [Q' [CS1 CS2]].
      assert (exists D', lenv_split E Q3 D0 D2 D' /\ lenv_split E Q3 D4 D' D3).
        apply lenv_split_assoc with (D13 := D1)...
        apply lenv_split_commute. apply lenv_split_disjoint_cenv with (Q := Q1)...
          apply wf_lenv_split_left in LS...
      destruct H as [D' [LS1 LS2]].
      apply typing_let with (D1 := D') (D2 := D4) (Q1 := Q') (Q2 := Q4) (T1 := T1) (T2 := T2)...
        eapply IHM; eauto.
          eapply lenv_split_strengthen_cenv_right; eauto.
          apply cenv_split_exp_proc; eauto.
        apply lenv_split_commute...
        apply cenv_split_exp_commute...
    Case "ectx_case".
      assert (exists Q', cenv_split_exp E Q0 Q2 Q' /\ cenv_split_exp E Q4 Q' Q3).
        apply cenv_split_exp_assoc with (Q13 := Q1)...
          apply cenv_split_exp_commute...
      destruct H as [Q' [CS1 CS2]].
      assert (exists D', lenv_split E Q3 D0 D2 D' /\ lenv_split E Q3 D4 D' D3).
        apply lenv_split_assoc with (D13 := D1)...
        apply lenv_split_commute. apply lenv_split_disjoint_cenv with (Q := Q1)...
          apply wf_lenv_split_left in LS...
      destruct H as [D' [LS1 LS2]].
      apply typing_case with (D1 := D') (D2 := D4) (Q1 := Q') (Q2 := Q4) (T1 := T1) (T2 := T2)...
        eapply IHM; eauto.
          eapply lenv_split_strengthen_cenv_right; eauto.
          apply cenv_split_exp_proc; eauto.
        apply lenv_split_commute...
        apply cenv_split_exp_commute...
Qed.

Lemma plug_preservation: forall M E D Q e e' f f' T,
  plug M e f ->
  plug M e' f' ->
  typing E D Q f T ->
  red e e' ->
  typing E D Q f' T.
Proof.
  induction M; intros; inversion H; inversion H0; subst;
  try solve
    [ eapply preservation; eauto
    | inversion H1; subst; econstructor; eauto; eapply IHM; eauto ].
Qed.

(* ********************************************************************** *)
(** Onto the eq* relations... *)

Lemma proc_eq_rename : forall P Q (X Y:atom) i,
  process (open_cp_rec i Y P) ->
  Y `notin` union (fv_cp P) (fv_cp Q) ->
  X `notin` union (fv_cp P) (fv_cp Q) ->
  proc_eq (open_cp_rec i Y P) (open_cp_rec i Y Q) ->
  proc_eq (open_cp_rec i X P) (open_cp_rec i X Q).
Proof.
  intros.
  destruct (proc_eq_proc_eqm (open_cp_rec i Y P) (open_cp_rec i Y Q)) as [EQM1 EQM2]; auto.
  apply proc_eqm_proc_eq; auto. 
  destruct (proc_eqm_regular (open_cp_rec i Y P) (open_cp_rec i Y Q)) as [R1 R2]; auto.
  apply (process_rename P i Y X); auto.
  apply (process_rename Q i Y X); auto.
  apply (proc_eqm_rename P Q X Y); auto.
Qed.

Lemma proc_eqm_exp: forall e P,
  proc_eqm (proc_exp e) P ->
  P = proc_exp e.
Proof with auto.
  intros. remember (proc_exp e) as P'. generalize dependent e.
  induction H; intros; subst; try inversion H...
Qed.

Lemma proc_eq_exp: forall e P,
  proc_eq (proc_exp e) P ->
  P = proc_exp e.
Proof.
  intros. apply proc_eq_proc_eqm in H. intuition.
  apply proc_eqm_exp. auto.
Qed.

(* So we can use "pick fresh and apply" more liberally... *)
Lemma typing_new': forall L Qs FQs T1 P1 T2,
  wf_proto empty T1 ->
  (forall X : atom, X `notin` L -> 
    proc_typing (FQs X T1) (open_cp P1 X) T2 /\
    nd_cons_cenvs Qs FQs) ->
  proc_typing Qs (proc_new T1 P1) T2.
Proof with intuition; auto.
  intros. pick fresh X and apply typing_new...
    instantiate (1 := FQs). pick fresh X.
      lapply (H0 X)...
    lapply (H0 X)...
Qed.

Lemma typing_new'': forall L Qs FQs FQs' X T T1 P1 T2,
  wf_proto empty T1 ->
  (forall Y : atom, Y `notin` L ->
    proc_typing (FQs' Y T1) (open_cp P1 Y) T2 /\
    nd_cons_cenvs Qs FQs /\
    nd_cons_cenvs (FQs X T) FQs') ->
  proc_typing (FQs X T) (proc_new T1 P1) T2 /\
  nd_cons_cenvs Qs FQs.
Proof with intuition; auto.
  intros. split.
    pick fresh Y and apply typing_new...
      instantiate (1 := FQs'). pick fresh Y.
        lapply (H0 Y)...
      lapply (H0 Y)...
    pick fresh Y. lapply (H0 Y)...
Qed.

Lemma typing_par_notin_right: forall QsL QsR Q X d T Qs1 Qs2 P1 P2 T1 T2,
  cenvs_split empty Qs1 Qs2 (QsL ++ [[(X, cbind_proto d T)] ++ Q] ++ QsR) ->
  proc_typing Qs1 P1 T1 ->
  proc_typing Qs2 P2 T2 ->
  X `notin` fv_cp P2 ->
  exists QsL1, exists QsR1, Qs1 = QsL1 ++ [[(X, cbind_proto d T)] ++ Q] ++ QsR1.
Proof with auto.
  intros. 
Admitted.


(* These are not going to be fun to prove... *)
Lemma typing_rename: forall E D QL QR (X Y : atom) d T e T' i,
  typing E D (QL ++ [(X, cbind_proto d T)] ++ QR) (open_ce_rec i X e) T' ->
  X `notin` fv_ce e ->
  Y `notin` union (fv_ce e)
                           (union (dom E)
                                      (union (dom D)
                                                 (union (dom QL) (dom QR)))) ->
  typing E D (QL ++ [(Y, cbind_proto d T)] ++ QR) (open_ce_rec i Y e) T'.
Proof.
Admitted.

Lemma proc_typing_rename_snk: forall QsL QsR QL QR (X Y : atom) T P T' i,
  proc_typing (QsL ++ [QL ++ [(X, cbind_proto cdir_snk T)] ++ QR] ++ QsR) 
                      (open_cp_rec i X P) T' ->
  X `notin` union (fv_cp P)
                           (union (doms cbinding QsL)
                                      (union (doms cbinding QsR)
                                                 (union (dom QL) (dom QR)))) ->
  Y `notin` union (fv_cp P)
                           (union (doms cbinding QsL)
                                      (union (doms cbinding QsR)
                                                 (union (dom QL) (dom QR)))) ->
  proc_typing (QsL ++ [QL ++ [(Y, cbind_proto cdir_snk T)] ++ QR] ++ QsR) 
                      (open_cp_rec i Y P) T'.
Proof.
Admitted.

Lemma proc_typing_rename_src: forall QsL QsR QL QR (X Y : atom) T P T' i,
  proc_typing (QsL ++ [QL ++ [(X, cbind_proto cdir_src T)] ++ QR] ++ QsR) 
                      (open_cp_rec i X P) T' ->
  X `notin` union (fv_cp P)
                           (union (doms cbinding QsL)
                                      (union (doms cbinding QsR)
                                                 (union (dom QL) (dom QR)))) ->
  Y `notin` union (fv_cp P)
                           (union (doms cbinding QsL)
                                      (union (doms cbinding QsR)
                                                 (union (dom QL) (dom QR)))) ->
  proc_typing (QsL ++ [QL ++ [(Y, cbind_proto cdir_src T)] ++ QR] ++ QsR) 
                      (open_cp_rec i Y P) T'.
Proof.
Admitted.

Lemma proc_typing_rename_snksrc: forall QsL QsM QsR QL1 QR1 QL2 QR2
                                                                     (X Y : atom) T P T' i,
  proc_typing (QsL ++ [QL1 ++ [(X, cbind_proto cdir_snk T)] ++ QR1] ++ QsM
                              ++ [QL2 ++ [(X, cbind_proto cdir_src T)] ++ QR2] ++ QsR) 
                      (open_cp_rec i X P) T' ->
  X `notin` fv_cp P ->
  Y `notin` union (fv_cp P)
                           (union (doms cbinding QsL)
                                      (union (doms cbinding QsM)
                                                 (union (doms cbinding QsR)
                                                            (union (dom QL1)
                                                                       (union (dom QR1)
                                                                                  (union (dom QL2) (dom QR2))))))) ->
  proc_typing (QsL ++ [QL1 ++ [(Y, cbind_proto cdir_snk T)] ++ QR1] ++ QsM
                              ++ [QL2 ++ [(Y, cbind_proto cdir_src T)] ++ QR2] ++ QsR) 
                      (open_cp_rec i Y P) T'.
Proof.
Admitted.

Lemma proc_typing_rename_srcsnk: forall QsL QsM QsR QL1 QR1 QL2 QR2
                                                                     (X Y : atom) T P T' i,
  proc_typing (QsL ++ [QL1 ++ [(X, cbind_proto cdir_src T)] ++ QR1] ++ QsM
                              ++ [QL2 ++ [(X, cbind_proto cdir_snk T)] ++ QR2] ++ QsR) 
                      (open_cp_rec i X P) T' ->
  X `notin` fv_cp P ->
  Y `notin` union (fv_cp P)
                           (union (doms cbinding QsL)
                                      (union (doms cbinding QsM)
                                                 (union (doms cbinding QsR)
                                                            (union (dom QL1)
                                                                       (union (dom QR1)
                                                                                  (union (dom QL2) (dom QR2))))))) ->
  proc_typing (QsL ++ [QL1 ++ [(Y, cbind_proto cdir_src T)] ++ QR1] ++ QsM
                              ++ [QL2 ++ [(Y, cbind_proto cdir_snk T)] ++ QR2] ++ QsR) 
                      (open_cp_rec i Y P) T'.
Proof.
Admitted.

Lemma proc_typing_rename_both: forall QsL QsR QL QR (X Y : atom) T P T' i,
  proc_typing (QsL ++ [QL ++ [(X, cbind_proto cdir_both T)] ++ QR] ++ QsR) 
                      (open_cp_rec i X P) T' ->
  X `notin` fv_cp P ->
  Y `notin` union (fv_cp P)
                           (union (doms cbinding QsL)
                                      (union (doms cbinding QsR)
                                                 (union (dom QL) (dom QR)))) ->
  proc_typing (QsL ++ [QL ++ [(Y, cbind_proto cdir_both T)] ++ QR] ++ QsR) 
                      (open_cp_rec i Y P) T'.
Proof.
Admitted.

Lemma cenvs_split_strengthen_cenvs_left: forall E QsL1 QsR1 Qs2 QsL QsR QsM,
  cenvs_split E (QsL1 ++ QsM ++ QsR1) Qs2 (QsL ++ QsM ++ QsR) ->
  cenvs_split E (QsL1 ++ QsR1) Qs2 (QsL ++ QsR).
Proof with auto.
  intros.
Admitted.

Lemma cenvs_split_strengthen_cenvs_right: forall E Qs1 QsL2 QsR2 QsL QsR QsM,
  cenvs_split E Qs1 (QsL2 ++ QsM ++ QsR2) (QsL ++ QsM ++ QsR) ->
  cenvs_split E Qs1 (QsL2 ++ QsR2) (QsL ++ QsR).
Proof.
  intros. apply cenvs_split_commute.
  apply cenvs_split_commute in H.
  apply cenvs_split_strengthen_cenvs_left in H; auto.
Qed.

Lemma cenvs_split_strengthen_cenv_left: forall E QsL1 QsR1 Qs2 QsL QsR QL QM QR,
  cenvs_split E (QsL1 ++ [QL ++ QM ++ QR] ++ QsR1) Qs2 (QsL ++ [QL ++ QM ++ QR] ++ QsR) ->
  cenvs_split E (QsL1 ++ [QL ++ QR] ++ QsR1) Qs2 (QsL ++ [QL ++ QR] ++ QsR).
Proof with auto.
  intros.
Admitted.

Lemma cenvs_split_strengthen_cenv_right: forall E Qs1 QsL2 QsR2 QsL QsR QL QM QR,
  cenvs_split E Qs1 (QsL2 ++ [QL ++ QM ++ QR] ++ QsR2) (QsL ++ [QL ++ QM ++ QR] ++ QsR) ->
  cenvs_split E Qs1 (QsL2 ++ [QL ++ QR] ++ QsR2) (QsL ++ [QL ++ QR] ++ QsR).
Proof.
  intros. apply cenvs_split_commute.
  apply cenvs_split_commute in H.
  apply cenvs_split_strengthen_cenv_left in H; auto.
Qed.

Inductive pw_permute: cenvs -> cenvs -> Prop :=
  | pw_permute_nil: pw_permute lcempty lcempty
  | pw_permute_cons: forall Q1 Q2 Qs1 Qs2,
      pw_permute Qs1 Qs2 ->
      permute Q1 Q2 ->
      pw_permute (Q1::Qs1) (Q2::Qs2)
.

Hint Constructors pw_permute.

Lemma pw_permute_refl: forall Qs,
  pw_permute Qs Qs.
Proof with auto.
  intros. induction Qs...
    constructor... apply permute_refl.
Qed.

Lemma cenvs_split_multi_exists_permute: forall E Qs1 Qs2 Qs2P,
  cenvs_split_multi E Qs1 Qs2 ->
  pw_permute Qs2 Qs2P ->
  exists Qs1P, pw_permute Qs1 Qs1P /\ cenvs_split_multi E Qs1P Qs2P.
Proof with auto.
  intros E Qs1 Qs2. revert Qs1.
  induction Qs2; intros Qs1 Qs2P CS Perm;
      inversion Perm; inversion CS; subst.
    exists lcempty. split...
    destruct Qs.
      simpl in *. lapply (IHQs2 Qs4 Qs3 H6)... intros.
        destruct H as [Qs1P [Perm' CS']].
        (* I don't really know how to proceed here... *)
Admitted.

Lemma cenvs_split_exists_permute: forall E Qs1 Qs2 Qs QsP,
  cenvs_split E Qs1 Qs2 Qs ->
  pw_permute Qs QsP ->
  exists Qs1P, exists Qs2P,
    pw_permute Qs1 Qs1P /\
    pw_permute Qs2 Qs2P /\
    cenvs_split E Qs1P Qs2P QsP.
Proof with auto.
Admitted.

Lemma append_permute: forall Qs1 Qs2 Qs1P Qs2P,
  pw_permute Qs1 Qs1P ->
  pw_permute Qs2 Qs2P ->
  pw_permute (Qs1 ++ Qs2) (Qs1P ++ Qs2P).
Proof with auto.
  induction Qs1; intros; inversion H; subst; simpl...
Qed.

Lemma append_exists_permute: forall Qs1 Qs2 QsP,
  pw_permute (Qs1 ++ Qs2) QsP ->
  exists Qs1P, exists Qs2P,
    pw_permute Qs1 Qs1P /\
    pw_permute Qs2 Qs2P /\
    Qs1P ++ Qs2P = QsP.
Proof with auto.
  induction Qs1; intros; simpl in *.
    exists lcempty. exists QsP. repeat split...
    inversion H. subst. lapply (IHQs1 Qs2 Qs3)... intros.
      destruct H0 as [Qs1P [Qs2P [Perm1 [Perm2 Eq]]]]. subst.
      exists (Q2 :: Qs1P). exists Qs2P. repeat split...
Qed.

Lemma nd_cons_cenvs_exists_permute: forall Qs FQs QsP,
  nd_cons_cenvs Qs FQs ->
  pw_permute Qs QsP ->
  exists FQsP,
    (forall X T, pw_permute (FQs X T) (FQsP X T)) /\
    nd_cons_cenvs QsP FQsP.
Proof with auto.
  intros. generalize dependent QsP.
  induction H; intros QsP Perm.
    destruct (append_exists_permute QsL QsR QsP)
        as [QsLP [QsRP [PermL [PermR Eq]]]]; subst...
      exists (fun X T => QsLP ++ [[(X, cbind_proto cdir_both T)]] ++ QsRP).
      split.
        intros. apply append_permute... apply append_permute...
          constructor... apply permute_refl...
        constructor...
    destruct (append_exists_permute QsL ([Q] ++ QsR) QsP)
        as [QsLP [QsP' [PermL [Perm' Eq]]]]; subst...
      destruct (append_exists_permute [Q] QsR QsP')
          as [QsP'' [QsRP [Perm'' [PermR Eq]]]]; subst...
      inversion Perm''. inversion H1. subst. simpl_env in *.
      exists (fun X T => QsLP ++ [[(X, cbind_proto cdir_both T)] ++ Q2] ++ QsRP).
      split.
        intros. apply append_permute... apply append_permute...
          rewrite_env (cempty ++ [(X, cbind_proto cdir_both T)] ++ Q2)...
          repeat constructor...
        constructor...
Qed.

Lemma proc_typing_permute_cenvs: forall Qs1 Qs2 P T,
  proc_typing Qs1 P T ->
  pw_permute Qs1 Qs2 ->
  proc_typing Qs2 P T.
Proof with auto.
  intros. generalize dependent Qs2.
  (proc_typing_cases (induction H) Case); intros QsP Perm.
    Case "typing_exp".
      apply cenvs_split_multi_exists_permute with (Qs2P := QsP) in H0...
      destruct H0 as [Qs1P [Perm' CSM']].
      inversion Perm'. inversion H2. subst. simpl_env in *.
      apply typing_exp with (Q := Q2)...
        apply typing_permute_cenv with (Q1 := Q)...
    Case "typing_parl".
      apply cenvs_split_exists_permute with (QsP := QsP) in H1...
      destruct H1 as [Qs1P [Qs2P [Perm1 [Perm2 CS]]]].
      lapply (IHproc_typing1 Qs1P)... lapply (IHproc_typing2 Qs2P)...
      intros. apply typing_parl with (Qs1 := Qs1P) (Qs2 := Qs2P)...
    Case "typing_parr".
      apply cenvs_split_exists_permute with (QsP := QsP) in H1...
      destruct H1 as [Qs1P [Qs2P [Perm1 [Perm2 CS]]]].
      lapply (IHproc_typing1 Qs1P)... lapply (IHproc_typing2 Qs2P)...
      intros. apply typing_parr with (Qs1 := Qs1P) (Qs2 := Qs2P)...
    Case "typing_new".
      destruct (nd_cons_cenvs_exists_permute Qs FQs QsP)
          as [FQsP [FPerm Cons]]...
        apply typing_new with (L := L) (FQs := FQsP)...
Qed.

Lemma eq1_preservation_right: forall Qs P1 P2 T,
  proc_typing Qs P1 T ->
  proc_eq1 P1 P2 ->
  proc_typing Qs P2 T.
Proof with auto.
  intros Qs P1 P2 T Typ. revert P2.
  (proc_typing_cases (induction Typ) Case); intros P0 Eq; inversion Eq; subst.
    Case "typing_parl".
      apply typing_parl with (Qs1 := Qs1) (Qs2 := Qs2)...
      apply typing_parr with (Qs1 := Qs2) (Qs2 := Qs1)...
        apply cenvs_split_commute...
      inversion Typ1; subst;
          (assert (exists Qs', cenvs_split empty Qs4 Qs2 Qs' /\
                                        cenvs_split empty Qs0 Qs' Qs3);
           [ apply cenvs_split_assoc with (Qs13 := Qs1); auto
           | destruct H0 as [Qs' [H1 H3]]]).
        apply typing_parl with (Qs1 := Qs0) (Qs2 := Qs')...
          apply typing_parl with (Qs1 := Qs4) (Qs2 := Qs2)...
        apply typing_parr with (Qs1 := Qs0) (Qs2 := Qs')...
          apply typing_parl with (Qs1 := Qs4) (Qs2 := Qs2)...
    Case "typing_parr".
      apply typing_parr with (Qs1 := Qs1) (Qs2 := Qs2)...
      apply typing_parl with (Qs1 := Qs2) (Qs2 := Qs1)...
        apply cenvs_split_commute...
      inversion Typ1; subst;
          (assert (exists Qs', cenvs_split empty Qs4 Qs2 Qs' /\
                                        cenvs_split empty Qs0 Qs' Qs3);
           [ apply cenvs_split_assoc with (Qs13 := Qs1); auto
           | destruct H0 as [Qs' [H1 H3]]]).
        apply typing_parr with (Qs1 := Qs0) (Qs2 := Qs')...
          apply typing_parr with (Qs1 := Qs4) (Qs2 := Qs2)...
        apply typing_parr with (Qs1 := Qs0) (Qs2 := Qs')...
          apply typing_parr with (Qs1 := Qs4) (Qs2 := Qs2)...
    Case "typing_new".
      pick fresh X and apply typing_new... auto.

     SCase "eq_swap".
      inversion H0; pick fresh Z; lapply (H1 Z); auto;
          intros; inversion H5; inversion H11; subst;
          apply app_eq_cases_mid in H15;
          destruct H15 as [Qs' [[Eq1 Eq2] | [Eq1 Eq2]]]; subst.
        pick fresh X and apply typing_new'...
          lapply (H1 X)... intros. inversion H3; subst.
          pick fresh Y and apply typing_new''...
            fold open_cp_rec. repeat split.
              rewrite <- H6... lapply (H13 X)... intros. simpl_env in H4.
                rewrite_env (cempty ++ [(Z, cbind_proto cdir_both T1)] ++ cempty) in H4.
                unfold open_cp in H4. rewrite open_cp_open_cp_comm in H4...
                apply proc_typing_rename_both with (Y := Y) in H4...
                  instantiate (1 := fun Y T => QsL ++
                                               [[(Y, cbind_proto cdir_both T)]] ++ Qs' ++
                                               [[(X, cbind_proto cdir_both T3)]] ++ QsR0).
                    simpl in *. simpl_env in *.
                    unfold open_cp. rewrite open_cp_open_cp_comm...
                  apply fv_cp_notin_open...
                  apply notin_union.
                    apply fv_cp_notin_open...
                    repeat rewrite doms_append. simpl...
              instantiate (1 := fun X T => (QsL ++ Qs') ++
                                           [[(X, cbind_proto cdir_both T)]] ++ QsR0).
                rewrite_env ((QsL ++ Qs') ++ QsR0).
                constructor...
              lazy beta. simpl_env. constructor...
        pick fresh X and apply typing_new'...
          lapply (H1 X)... intros. inversion H3; subst.
          pick fresh Y and apply typing_new''...
            fold open_cp_rec. repeat split.
              rewrite <- H6... lapply (H13 X)... intros. simpl_env in H4.
                rewrite_env ((QsL0 ++ [[(X, cbind_proto cdir_both T3)]] ++ Qs') ++
                                     [cempty ++ [(Z, cbind_proto cdir_both T1)] ++ cempty] ++
                                     QsR) in H4.
                unfold open_cp in H4. rewrite open_cp_open_cp_comm in H4...
                apply proc_typing_rename_both with (Y := Y) in H4...
                  instantiate (1 := fun Y T => (QsL0 ++
                                               [[(X, cbind_proto cdir_both T3)]] ++ Qs') ++
                                               [[(Y, cbind_proto cdir_both T)]] ++ QsR).
                    simpl in *. simpl_env in *.
                    unfold open_cp. rewrite open_cp_open_cp_comm...
                  apply fv_cp_notin_open...
                  apply notin_union.
                    apply fv_cp_notin_open...
                    repeat rewrite doms_append. simpl...
              instantiate (1 := fun X T => QsL0 ++
                                           [[(X, cbind_proto cdir_both T)]] ++ Qs' ++ QsR).
                simpl_env. constructor...
              lazy beta.
                rewrite_env ((QsL0 ++ [[(X, cbind_proto cdir_both T3)]] ++ Qs') ++ QsR).
                constructor...
        pick fresh X and apply typing_new'...
          lapply (H1 X)... intros. inversion H3; subst.
          pick fresh Y and apply typing_new''...
            fold open_cp_rec. repeat split.
              rewrite <- H6... lapply (H13 X)... intros. simpl_env in H4.
                rewrite_env (cempty ++ [(Z, cbind_proto cdir_both T1)] ++ cempty) in H4.
                unfold open_cp in H4. rewrite open_cp_open_cp_comm in H4...
                apply proc_typing_rename_both with (Y := Y) in H4...
                  instantiate (1 := fun Y T => QsL ++
                                               [[(Y, cbind_proto cdir_both T)]] ++ Qs' ++
                                               [[(X, cbind_proto cdir_both T3)] ++ Q] ++ QsR0).
                    simpl in *. simpl_env in *.
                    unfold open_cp. rewrite open_cp_open_cp_comm...
                  apply fv_cp_notin_open...
                  apply notin_union.
                    apply fv_cp_notin_open...
                    repeat rewrite doms_append. simpl...
              instantiate (1 := fun X T => (QsL ++ Qs') ++
                                           [[(X, cbind_proto cdir_both T)] ++ Q] ++ QsR0).
                rewrite_env ((QsL ++ Qs') ++ [Q] ++ QsR0).
                constructor...
              lazy beta. simpl_env. constructor...
        destruct Qs'; simpl_env in *; inversion Eq1; subst.
          pick fresh X and apply typing_new'...
            lapply (H1 X)... intros. inversion H3; subst.
            pick fresh Y and apply typing_new''...
              fold open_cp_rec. repeat split.
                rewrite <- H6... lapply (H13 X)... intros.
                  rewrite_env ([(X, cbind_proto cdir_both T3)] ++
                                       [(Z, cbind_proto cdir_both T1)] ++ cempty) in H4.
                  unfold open_cp in H4. rewrite open_cp_open_cp_comm in H4...
                  apply proc_typing_rename_both with (Y := Y) in H4...
                    instantiate (1 := fun Y T => QsL0 ++
                                                 [[(Y, cbind_proto cdir_both T)] ++
                                                  [(X, cbind_proto cdir_both T3)]] ++ QsR).
                      simpl in *. simpl_env in *.
                      unfold open_cp. rewrite open_cp_open_cp_comm...
                      apply proc_typing_permute_cenvs with
                          (Qs1 := QsL0 ++ [[(X, cbind_proto cdir_both T3)] ++
                                                       [(Y, cbind_proto cdir_both T1)]] ++ QsR)...
                        apply append_permute.
                          apply pw_permute_refl.
                          apply append_permute.
                            constructor...
                              rewrite_env ([(Y, cbind_proto cdir_both T1)] ++
                                                   [(X, cbind_proto cdir_both T3)] ++ cempty).
                              constructor. simpl_env. apply permute_refl.
                            apply pw_permute_refl.
                    apply fv_cp_notin_open...
                    apply notin_union.
                      apply fv_cp_notin_open...
                      repeat rewrite doms_append. simpl...
                instantiate (1 := fun X T => QsL0 ++
                                             [[(X, cbind_proto cdir_both T)]] ++ QsR).
                  simpl_env. constructor...
                lazy beta. constructor...
          pick fresh X and apply typing_new'...
            lapply (H1 X)... intros. inversion H3; subst.
            pick fresh Y and apply typing_new''...
              fold open_cp_rec. repeat split.
                rewrite <- H6... lapply (H13 X)... intros. simpl_env in H4.
                  rewrite_env ((QsL0 ++ [[(X, cbind_proto cdir_both T3)] ++ l] ++ Qs') ++
                                       [cempty ++ [(Z, cbind_proto cdir_both T1)] ++ cempty] ++
                                       QsR) in H4.
                  unfold open_cp in H4. rewrite open_cp_open_cp_comm in H4...
                  apply proc_typing_rename_both with (Y := Y) in H4...
                    instantiate (1 := fun Y T => (QsL0 ++
                                                 [[(X, cbind_proto cdir_both T3)] ++ l] ++ Qs') ++
                                                 [[(Y, cbind_proto cdir_both T)]] ++ QsR).
                      simpl in *. simpl_env in *.
                      unfold open_cp. rewrite open_cp_open_cp_comm...
                    apply fv_cp_notin_open...
                    apply notin_union.
                      apply fv_cp_notin_open...
                      repeat rewrite doms_append. simpl...
                instantiate (1 := fun X T => QsL0 ++
                                             [[(X, cbind_proto cdir_both T)] ++ l] ++ Qs' ++ QsR).
                  simpl_env. constructor...
                lazy beta.
                  rewrite_env ((QsL0 ++ [[(X, cbind_proto cdir_both T3)] ++ l] ++ Qs') ++ QsR).
                  constructor...
        pick fresh X and apply typing_new'...
          lapply (H1 X)... intros. inversion H3; subst.
          pick fresh Y and apply typing_new''...
            fold open_cp_rec. repeat split.
              rewrite <- H6... lapply (H13 X)... intros. simpl_env in H4.
                rewrite_env (cempty ++ [(Z, cbind_proto cdir_both T1)] ++ Q) in H4.
                unfold open_cp in H4. rewrite open_cp_open_cp_comm in H4...
                apply proc_typing_rename_both with (Y := Y) in H4...
                  instantiate (1 := fun Y T => QsL ++
                                               [[(Y, cbind_proto cdir_both T)] ++ Q] ++ Qs' ++
                                               [[(X, cbind_proto cdir_both T3)]] ++ QsR0).
                    simpl in *. simpl_env in *.
                    unfold open_cp. rewrite open_cp_open_cp_comm...
                  apply fv_cp_notin_open...
                  apply notin_union.
                    apply fv_cp_notin_open...
                    repeat rewrite doms_append. simpl...
              instantiate (1 := fun X T => (QsL ++ [Q] ++ Qs') ++
                                           [[(X, cbind_proto cdir_both T)]] ++ QsR0).
                rewrite_env ((QsL ++ [Q] ++ Qs') ++ QsR0).
                constructor...
              lazy beta. simpl_env. constructor...
        pick fresh X and apply typing_new'...
          lapply (H1 X)... intros. inversion H3; subst.
          pick fresh Y and apply typing_new''...
            fold open_cp_rec. repeat split.
              rewrite <- H6... lapply (H13 X)... intros. simpl_env in H4.
                rewrite_env ((QsL0 ++ [[(X, cbind_proto cdir_both T3)]] ++ Qs') ++
                                     [cempty ++ [(Z, cbind_proto cdir_both T1)] ++ Q] ++
                                     QsR) in H4.
                unfold open_cp in H4. rewrite open_cp_open_cp_comm in H4...
                apply proc_typing_rename_both with (Y := Y) in H4...
                  instantiate (1 := fun Y T => (QsL0 ++
                                               [[(X, cbind_proto cdir_both T3)]] ++ Qs') ++
                                               [[(Y, cbind_proto cdir_both T)] ++ Q] ++ QsR).
                    simpl in *. simpl_env in *.
                    unfold open_cp. rewrite open_cp_open_cp_comm...
                  apply fv_cp_notin_open...
                  apply notin_union.
                    apply fv_cp_notin_open...
                    repeat rewrite doms_append. simpl...
              instantiate (1 := fun X T => QsL0 ++
                                           [[(X, cbind_proto cdir_both T)]] ++ Qs' ++ [Q] ++ QsR).
                simpl_env. constructor...
              lazy beta.
                rewrite_env ((QsL0 ++ [[(X, cbind_proto cdir_both T3)]] ++ Qs') ++ [Q] ++ QsR).
                constructor...
        pick fresh X and apply typing_new'...
          lapply (H1 X)... intros. inversion H3; subst.
          pick fresh Y and apply typing_new''...
            fold open_cp_rec. repeat split.
              rewrite <- H6... lapply (H13 X)... intros. simpl_env in H4.
                rewrite_env (cempty ++ [(Z, cbind_proto cdir_both T1)] ++ Q) in H4.
                unfold open_cp in H4. rewrite open_cp_open_cp_comm in H4...
                apply proc_typing_rename_both with (Y := Y) in H4...
                  instantiate (1 := fun Y T => QsL ++
                                               [[(Y, cbind_proto cdir_both T)] ++ Q] ++ Qs' ++
                                               [[(X, cbind_proto cdir_both T3)] ++ Q0] ++ QsR0).
                    simpl in *. simpl_env in *.
                    unfold open_cp. rewrite open_cp_open_cp_comm...
                  apply fv_cp_notin_open...
                  apply notin_union.
                    apply fv_cp_notin_open...
                    repeat rewrite doms_append. simpl...
              instantiate (1 := fun X T => (QsL ++ [Q] ++ Qs') ++
                                           [[(X, cbind_proto cdir_both T)] ++ Q0] ++ QsR0).
                rewrite_env ((QsL ++ [Q] ++ Qs') ++ [Q0] ++ QsR0).
                constructor...
              lazy beta. simpl_env. constructor...
        destruct Qs'; simpl_env in *; inversion Eq1; subst.
          pick fresh X and apply typing_new'...
            lapply (H1 X)... intros. inversion H3; subst.
            pick fresh Y and apply typing_new''...
              fold open_cp_rec. repeat split.
                rewrite <- H6... lapply (H13 X)... intros. simpl_env in H4.
                  unfold open_cp in H4. rewrite open_cp_open_cp_comm in H4...
                  apply proc_typing_rename_both with (Y := Y) in H4...
                    instantiate (1 := fun Y T => QsL0 ++
                                                 [[(Y, cbind_proto cdir_both T)] ++
                                                  [(X, cbind_proto cdir_both T3)] ++ Q] ++ QsR).
                      simpl in *. simpl_env in *.
                      unfold open_cp. rewrite open_cp_open_cp_comm...
                      apply proc_typing_permute_cenvs with
                          (Qs1 := QsL0 ++ [[(X, cbind_proto cdir_both T3)] ++
                                                       [(Y, cbind_proto cdir_both T1)] ++ Q] ++
                                                       QsR)...
                        apply append_permute.
                          apply pw_permute_refl.
                          apply append_permute.
                            repeat constructor... apply permute_refl.
                            apply pw_permute_refl.
                    apply fv_cp_notin_open...
                    apply notin_union.
                      apply fv_cp_notin_open...
                      repeat rewrite doms_append. simpl...
                instantiate (1 := fun X T => QsL0 ++
                                             [[(X, cbind_proto cdir_both T)] ++ Q] ++ QsR).
                  simpl_env. constructor...
                lazy beta. constructor...
          pick fresh X and apply typing_new'...
            lapply (H1 X)... intros. inversion H3; subst.
            pick fresh Y and apply typing_new''...
              fold open_cp_rec. repeat split.
                rewrite <- H6... lapply (H13 X)... intros. simpl_env in H4.
                  rewrite_env ((QsL0 ++ [[(X, cbind_proto cdir_both T3)] ++ l] ++ Qs') ++
                                       [cempty ++ [(Z, cbind_proto cdir_both T1)] ++ Q] ++
                                       QsR) in H4.
                  unfold open_cp in H4. rewrite open_cp_open_cp_comm in H4...
                  apply proc_typing_rename_both with (Y := Y) in H4...
                    instantiate (1 := fun Y T => (QsL0 ++
                                                 [[(X, cbind_proto cdir_both T3)] ++ l] ++ Qs') ++
                                                 [[(Y, cbind_proto cdir_both T)] ++ Q] ++ QsR).
                      simpl in *. simpl_env in *.
                      unfold open_cp. rewrite open_cp_open_cp_comm...
                    apply fv_cp_notin_open...
                    apply notin_union.
                      apply fv_cp_notin_open...
                      repeat rewrite doms_append. simpl...
                instantiate (1 := fun X T => QsL0 ++
                                             [[(X, cbind_proto cdir_both T)] ++ l] ++ Qs' ++ [Q] ++ QsR).
                  simpl_env. constructor...
                lazy beta.
                  rewrite_env ((QsL0 ++ [[(X, cbind_proto cdir_both T3)] ++ l] ++ Qs') ++ [Q] ++ QsR).
                  constructor...

     SCase "eq_extrude".
      unfold open_cp in H1. simpl in H1. pick fresh X. lapply (H1 X)...
        intros. rewrite <- (open_cp_rec_process P3 X 0) in H3...
        inversion H0; inversion H3; subst.
          destruct (typing_par_notin_right QsL QsR cempty X cdir_both T1 Qs1 Qs2
                           (open_cp_rec 0 X P2) P3 T2 typ_answer) as
              [QsL1 [QsR1 Eq1]]; simpl_env in *; subst...
            apply typing_parl with (Qs1 := QsL1 ++ QsR1) (Qs2 := Qs2)...
              pick fresh Y and apply typing_new...
                instantiate (1 := fun Y T => (QsL1 ++ [[(Y, cbind_proto cdir_both T)]] ++ QsR1)).
                  constructor...
                rewrite_env (cempty ++ [(X, cbind_proto cdir_both T1)] ++ cempty) in H9.
                  apply proc_typing_rename_both with (Y := Y) in H9...
              apply cenvs_split_strengthen_cenvs_left in H13...
          destruct (typing_par_notin_right QsL QsR cempty X cdir_both T1 Qs1 Qs2
                           (open_cp_rec 0 X P2) P3 typ_answer T2) as
              [QsL1 [QsR1 Eq1]]; simpl_env in *; subst...
            apply typing_parr with (Qs1 := QsL1 ++ QsR1) (Qs2 := Qs2)...
              pick fresh Y and apply typing_new...
                instantiate (1 := fun Y T => (QsL1 ++ [[(Y, cbind_proto cdir_both T)]] ++ QsR1)).
                  constructor...
                rewrite_env (cempty ++ [(X, cbind_proto cdir_both T1)] ++ cempty) in H9.
                  apply proc_typing_rename_both with (Y := Y) in H9...
              apply cenvs_split_strengthen_cenvs_left in H13...
          destruct (typing_par_notin_right QsL QsR Q X cdir_both T1 Qs1 Qs2
                           (open_cp_rec 0 X P2) P3 T2 typ_answer) as
              [QsL1 [QsR1 Eq1]]; simpl_env in *; subst...
            apply typing_parl with (Qs1 := QsL1 ++ [Q] ++ QsR1) (Qs2 := Qs2)...
              pick fresh Y and apply typing_new...
                instantiate (1 := fun Y T => (QsL1 ++ [[(Y, cbind_proto cdir_both T)] ++ Q] ++ QsR1)).
                  constructor...
                rewrite_env (cempty ++ [(X, cbind_proto cdir_both T1)] ++ Q) in H9.
                  apply proc_typing_rename_both with (Y := Y) in H9...
              rewrite_env (cempty ++ [(X, cbind_proto cdir_both T1)] ++ Q) in H13.
                apply cenvs_split_strengthen_cenv_left in H13...
          destruct (typing_par_notin_right QsL QsR Q X cdir_both T1 Qs1 Qs2
                           (open_cp_rec 0 X P2) P3 typ_answer T2) as
              [QsL1 [QsR1 Eq1]]; simpl_env in *; subst...
            apply typing_parr with (Qs1 := QsL1 ++ [Q] ++ QsR1) (Qs2 := Qs2)...
              pick fresh Y and apply typing_new...
                instantiate (1 := fun Y T => (QsL1 ++ [[(Y, cbind_proto cdir_both T)] ++ Q] ++ QsR1)).
                  constructor...
                rewrite_env (cempty ++ [(X, cbind_proto cdir_both T1)] ++ Q) in H9.
                  apply proc_typing_rename_both with (Y := Y) in H9...
              rewrite_env (cempty ++ [(X, cbind_proto cdir_both T1)] ++ Q) in H13.
                apply cenvs_split_strengthen_cenv_left in H13...
Qed.

Lemma nd_cons_cenvs_with_right: forall E Qs1 FQs1 Qs2 Qs3,
  nd_cons_cenvs Qs1 FQs1 ->
  cenvs_split E Qs1 Qs2 Qs3 ->
  exists FQs3, exists L,
    nd_cons_cenvs Qs3 FQs3 /\
    forall X T, X `notin` L -> cenvs_split E (FQs1 X T) Qs2 (FQs3 X T).
Proof with auto.
  intros E Qs1 FQs1 Qs2 Qs3. revert Qs1 FQs1 Qs2.
  induction Qs3; intros Qs1 FQs1 Qs2 Cons CS.
    inversion CS. subst.
    (* This is going to be tricky, isn't it...? *)
Admitted.

Lemma eq1_preservation_left: forall Qs P1 P2 T,
  proc_typing Qs P2 T ->
  proc_eq1 P1 P2 ->
  proc_typing Qs P1 T.
Proof with auto.
  intros Qs P1 P2 T Typ. revert P1.
  (proc_typing_cases (induction Typ) Case); intros P0 Eq;
      inversion Eq; subst.
    Case "typing_parl".
      apply typing_parl with (Qs1 := Qs1) (Qs2 := Qs2)...
      apply typing_parr with (Qs1 := Qs2) (Qs2 := Qs1)...
        apply cenvs_split_commute...

      inversion Typ2; subst;
          (assert (exists Qs', cenvs_split empty Qs0 Qs1 Qs' /\
                                        cenvs_split empty Qs4 Qs' Qs3);
           [ apply cenvs_split_assoc with (Qs13 := Qs2); auto; 
             apply cenvs_split_commute; auto
           | destruct H0 as [Qs' [H1 H3]]]).
        apply typing_parl with (Qs1 := Qs') (Qs2 := Qs4)...
          apply typing_parl with (Qs1 := Qs1) (Qs2 := Qs0)...
            apply cenvs_split_commute...
          apply cenvs_split_commute...
        apply typing_parl with (Qs1 := Qs') (Qs2 := Qs4)...
          apply typing_parl with (Qs1 := Qs1) (Qs2 := Qs0)...
            apply cenvs_split_commute...
          apply cenvs_split_commute...

    SCase "eq_extrude".
      inversion Typ1. subst.
      destruct (nd_cons_cenvs_with_right empty Qs1 FQs Qs2 Qs3) as
          [FQs' [L' [Cons H0]]]...
      pick fresh X and apply typing_new...
        instantiate (1 := FQs')...
        lapply (H0 X T)... lapply (H7 X)... intros.
        apply typing_parl with (Qs1 := FQs X T) (Qs2 := Qs2)...
          fold open_cp_rec.
          rewrite <- open_cp_rec_process...

    Case "typing_parr".
      apply typing_parr with (Qs1 := Qs1) (Qs2 := Qs2)...
      apply typing_parl with (Qs1 := Qs2) (Qs2 := Qs1)...
        apply cenvs_split_commute...

      inversion Typ2; subst;
          (assert (exists Qs', cenvs_split empty Qs0 Qs1 Qs' /\
                                        cenvs_split empty Qs4 Qs' Qs3);
           [ apply cenvs_split_assoc with (Qs13 := Qs2); auto; 
             apply cenvs_split_commute; auto
           | destruct H0 as [Qs' [H1 H3]]]).
        apply typing_parl with (Qs1 := Qs') (Qs2 := Qs4)...
          apply typing_parr with (Qs1 := Qs1) (Qs2 := Qs0)...
            apply cenvs_split_commute...
          apply cenvs_split_commute...
        apply typing_parr with (Qs1 := Qs') (Qs2 := Qs4)...
          apply typing_parl with (Qs1 := Qs1) (Qs2 := Qs0)...
            apply cenvs_split_commute...
          apply cenvs_split_commute...

    SCase "eq_extrude".
      inversion Typ1. subst.
      destruct (nd_cons_cenvs_with_right empty Qs1 FQs Qs2 Qs3) as
          [FQs' [L' [Cons H0]]]...
      pick fresh X and apply typing_new...
        instantiate (1 := FQs')...
        lapply (H0 X T)... lapply (H7 X)... intros.
        apply typing_parr with (Qs1 := FQs X T) (Qs2 := Qs2)...
          fold open_cp_rec.
          rewrite <- open_cp_rec_process...

    Case "typing_new".
      pick fresh X and apply typing_new... auto.

     SCase "eq_swap".
      assert (proc_typing Qs (proc_new T1 (proc_new T0 P1')) T2)...
        econstructor; eauto.
      assert (proc_eq1 (proc_new T1 (proc_new T0 P1'))
                                  (proc_new T0 (proc_new T1 P2))).
        apply proc_eq1_swap with (L := L0)...
        intros. lapply (H5 Y X)... intros... symmetry...
      eapply eq1_preservation_right; eauto.
Qed.

Lemma eqm_preservation: forall Qs P1 P2 T,
  proc_typing Qs P1 T ->
  proc_eqm P1 P2 ->
  proc_typing Qs P2 T.
Proof.
  intros Qs P1 P2 T Typ Eq.
  induction Eq.
    auto.
    apply IHEq. eapply eq1_preservation_right in Typ; eauto.
    apply IHEq. eapply eq1_preservation_left in Typ; eauto.
Qed.

Lemma eq_preservation: forall Qs P1 P2 T,
  proc_typing Qs P1 T ->
  proc_eq P1 P2 ->
  proc_typing Qs P2 T.
Proof.
  intros Qs P1 P2 T Typ Eq.
  apply proc_eq_proc_eqm in Eq. destruct Eq as [Eq1 Eq2].
  eapply eqm_preservation in Eq1; eauto.
Qed.

Lemma proc_red_rename : forall P Q (X Y:atom) i,
  Y `notin` union (fv_cp P) (fv_cp Q) ->
  X `notin` union (fv_cp P) (fv_cp Q) ->
  proc_red (open_cp_rec i Y P) (open_cp_rec i Y Q) ->
  proc_red (open_cp_rec i X P) (open_cp_rec i X Q).
Proof with auto.
  intros P Q X Y i NI1 NI2 Red.
  remember (open_cp_rec i Y P) as P1.
  remember (open_cp_rec i Y Q) as Q1.
  destruct (proc_red_regular P1 Q1) as [ProcP ProcQ]...
  generalize dependent Q. generalize dependent P. revert i.
  (proc_red_cases (induction Red) Case);
      intros i Px EQ1 Qx NI1 NI2 EQ2; simpl in *; subst; auto.
    Case "red_ectx".
      apply open_cp_exp_eq_open_ce in EQ1.
      apply open_cp_exp_eq_open_ce in EQ2.
      destruct EQ1 as [f1' [EQ1 EQ1']].
      destruct EQ2 as [f2' [EQ2 EQ2']]. subst.
      apply red_ectx with (M := swap_ectx Y X M) (e1 := swap_ce Y X e1)
                                                     (e2 := swap_ce Y X e2)...
        apply red_swap_ce...
        rewrite <- swap_open_ce2 with (X := Y)...
          apply plug_swap_ce...
        rewrite <- swap_open_ce2 with (X := Y)...
          apply plug_swap_ce...
    Case "red_done".
      assert (open_cp_rec i Y (proc_par Qx
                                                            (proc_new typ_answer (exp_done O)))
                  = proc_par (open_cp_rec i Y Qx)
                                     (proc_new typ_answer (exp_done O))).
        simpl...
      rewrite <- H0 in EQ1.
      apply eq_open_cp_rename with (Y := X) in EQ1...
      rewrite <- EQ1. simpl. constructor...
      inversion H; subst. constructor...
      apply process_rename with (X := Y)...
    Case "red_par".
      rewrite <- (open_close_cp_rec Y (proc_par P1 P2) i) in EQ1...
      rewrite <- (open_close_cp_rec Y (proc_par P1 P2') i) in EQ2...
      assert (X `notin` union (fv_cp (close_cp_rec i Y (proc_par P1 P2'))) (fv_cp Qx)).
        apply notin_union...
        skip. (* Very stuck here. *)
      assert (X `notin` union (fv_cp (close_cp_rec i Y (proc_par P1 P2))) (fv_cp Px)).
        apply notin_union...
        skip. (* Same as above. *)
      apply eq_open_cp_rename with (Y := X) in EQ1...
         apply eq_open_cp_rename with (Y := X) in EQ2...
           rewrite <- EQ1. rewrite <- EQ2. simpl. constructor.
             inversion ProcP. subst. constructor.
               apply process_rename with (X := Y)...
                 rewrite open_close_cp_rec...
               apply process_rename with (X := Y)...
                 rewrite open_close_cp_rec...
             apply IHRed...
               rewrite open_close_cp_rec...
               apply notin_union; apply fv_close_cp_aux...
               apply open_cp_aux_inj in EQ1...
                 simpl in EQ1. apply open_cp_aux_inj in EQ2.
                   simpl in EQ2. subst. simpl in NI1. simpl in NI2.
                   apply notin_union; fsetdec...
                 apply notin_union; try fsetdec.
               rewrite open_close_cp_rec...
           apply notin_union...
             apply fv_close_cp_aux.
         apply notin_union...
           apply fv_close_cp_aux.
    Case "red_new".
      (* I need to work on something else for a while. *)
Admitted.