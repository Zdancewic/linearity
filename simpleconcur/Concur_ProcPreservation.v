(** Type-safety proofs.

    Based on work by: Brian Aydemir and Arthur Chargu\'eraud, with help from
    Aaron Bohannon, Jeffrey Vaughan, and Dimitrios Vytiniotis.

    In parentheses are given the label of the corresponding lemma in
    the appendix (informal proofs) of the POPLmark Challenge.

    Table of contents:
      - #<a href="##preservation">Preservation</a>#
*)
Require Export Concur_ProcLemmas.
Require Import Omega.

Axiom skip : False.
Ltac skip := assert False; [ apply skip | contradiction ].


(* ********************************************************************** *)
(** Preservation on processes *)

(*Lemma par_exists_plug : forall P1 P2,
  semi_canon P1 ->
  process P2 ->
  exists N, exists P', proc_plug N P2 P' /\ proc_eq P' (proc_par P1 P2).
Proof with auto.
  intros P1 P2 SC1 Proc2.
  (semi_canon_cases (induction SC1) Case); subst.
    Case "semi_canon_exp".
      exists (sctx_par e H sctx_hole). exists (proc_par e P2).
      split...
    Case "semi_canon_par".
      destruct IHSC1 as [N [P' [Plug Eq]]].
      exists (sctx_par e H N). exists (proc_par e P'). split...
      apply eq_trans with (P2 := (proc_par e (proc_par P P2)))...
      apply eq_sym. apply eq_assoc... apply eq_refl.
      apply semi_canon_regular...
    Case "semi_canon_new".
      pick fresh X. lapply (H1 X)... lapply (H0 X)...
      intros SC IH. destruct IH as [N [P' [Plug Eq]]].
      exists (sctx_new T H N). exists (proc_new T P'). split...
      apply eq_trans with (P2 := (proc_new T (proc_par P P2)))...
        skip. (* Want to apply eq_new, but with existing X... *)
        apply eq_extrude... skip. (* process_new with existing X *)
Qed.*)


(*Lemma cenv_split_multi_sub: forall E Q Qs Qs',
  cenv_split_multi E Qs Q ->
  cenvs_split E Qs' lcempty Qs ->
  cenv_split_multi E Qs' Q.
Proof with auto.
  intros. generalize dependent Qs'. induction H; intros.
    inversion H0; subst.*)

Lemma cenvs_split_simple_append: forall E Qs1 Qs2 Qs3 Qs1' Qs2' Qs3',
  cenvs_split_simple E Qs1 Qs2 Qs3 ->
  cenvs_split_simple E Qs1' Qs2' Qs3' ->
  cenvs_split_simple E (Qs1 ++ Qs1') (Qs2 ++ Qs2') (Qs3 ++ Qs3').
Proof.
  intros E Qs1 Qs2 Qs3. revert Qs1 Qs2.
  induction Qs3; intros; inversion H; subst; simpl; auto.
Qed.

Lemma cenv_split_multi_insert_empty: forall E Qs1 Qs2 Q Z,
  cenv_split_multi E (Qs1 ++ Qs2) Q Z ->
  cenv_split_multi E (Qs1 ++ [cempty] ++ Qs2) Q Z.
Proof with auto.
Admitted.

Lemma cenv_split_multi_drop_empty: forall E Qs1 Qs2 Q Z,
  cenv_split_multi E (Qs1 ++ [cempty] ++ Qs2) Q Z ->
  cenv_split_multi E (Qs1 ++ Qs2) Q Z.
Proof with auto.
Admitted.

Lemma cenvs_split_multi_insert_empty: forall E Qs1 Qs2 Qs3,
  cenvs_split_multi E (Qs1 ++ Qs2) Qs3 ->
  cenvs_split_multi E (Qs1 ++ [cempty] ++ Qs2) Qs3.
Proof with auto.
Admitted.

Lemma cenvs_split_multi_drop_empty: forall E Qs1 Qs2 Qs3,
  cenvs_split_multi E (Qs1 ++ [cempty] ++ Qs2) Qs3 ->
  cenvs_split_multi E (Qs1 ++ Qs2) Qs3.
Proof with auto.
Admitted.

Inductive lcempties : cenvs -> Prop :=
  | lcempties_nil :  lcempties lcempty
  | lcempties_cons : forall Qs,
      lcempties Qs ->
      lcempties (cempty :: Qs)
.

Hint Constructors lcempties.

Lemma lcempties_append: forall Qs1 Qs2,
  lcempties Qs1 ->
  lcempties Qs2 ->
  lcempties (Qs1 ++ Qs2).
Proof with auto.
  induction Qs1; intros.
    simpl...
    simpl. inversion H. subst. constructor. apply IHQs1...
Qed.

Lemma lcempties_divide: forall Qs1 Qs2,
  lcempties (Qs1 ++ Qs2) ->
  lcempties Qs1 /\ lcempties Qs2.
Proof with auto.
  induction Qs1; intros; split...
    simpl in H. inversion H. subst.
      apply IHQs1 in H1. intuition.
    simpl in H. inversion H. subst.
      apply IHQs1 in H1. intuition.
Qed.

Lemma cenv_split_multi_insert_empties: forall E Qs1 Qs2 Q Qs Z,
  cenv_split_multi E (Qs1 ++ Qs2) Q Z ->
  lcempties Qs ->
  cenv_split_multi E (Qs1 ++ Qs ++ Qs2) Q Z.
Proof with auto.
  intros E Qs1 Qs2 Q Qs. revert Qs1 Qs2 Q.
  induction Qs; intros.
    simpl...
    simpl_env in H0. apply lcempties_divide in H0. intuition.
      inversion H1. subst. apply IHQs in H...
      simpl_env. apply cenv_split_multi_insert_empty...
Qed.

Lemma cenv_split_multi_drop_empties: forall E Qs1 Qs2 Q Qs Z,
  cenv_split_multi E (Qs1 ++ Qs ++ Qs2) Q Z ->
  lcempties Qs ->
  cenv_split_multi E (Qs1 ++ Qs2) Q Z.
Proof with auto.
  intros E Qs1 Qs2 Q Qs. revert Qs1 Qs2 Q.
  induction Qs; intros.
    simpl...
    simpl_env in H0. apply lcempties_divide in H0. intuition.
      inversion H1. subst.
      rewrite_env ((Qs1 ++ [cempty]) ++ Qs ++ Qs2) in H.
      apply IHQs in H... simpl_env in H.
      apply cenv_split_multi_drop_empty...
Qed.

Lemma cenvs_split_multi_insert_empties: forall E Qs1 Qs2 Qs3 Qs,
  cenvs_split_multi E (Qs1 ++ Qs2) Qs3 ->
  lcempties Qs ->
  cenvs_split_multi E (Qs1 ++ Qs ++ Qs2) Qs3.
Proof with auto.
  intros E Qs1 Qs2 Qs3 Qs. revert Qs1 Qs2 Qs3.
  induction Qs; intros.
    simpl...
    simpl_env in H0. apply lcempties_divide in H0. intuition.
      inversion H1. subst. apply IHQs in H...
      simpl_env. apply cenvs_split_multi_insert_empty...
Qed.

Lemma cenvs_split_multi_drop_empties: forall E Qs1 Qs2 Qs3 Qs,
  cenvs_split_multi E (Qs1 ++ Qs ++ Qs2) Qs3 ->
  lcempties Qs ->
  cenvs_split_multi E (Qs1 ++ Qs2) Qs3.
Proof with auto.
  intros E Qs1 Qs2 Qs3 Qs. revert Qs1 Qs2 Qs3.
  induction Qs; intros.
    simpl...
    simpl_env in H0. apply lcempties_divide in H0. intuition.
      inversion H1. subst.
      rewrite_env ((Qs1 ++ [cempty]) ++ Qs ++ Qs2) in H.
      apply IHQs in H... simpl_env in H.
      apply cenvs_split_multi_drop_empty...
Qed.

Lemma cenvs_split_insert_empties_left: forall E Qs1L Qs1R Qs2 Qs3 Qs,
  cenvs_split E (Qs1L ++ Qs1R) Qs2 Qs3 ->
  lcempties Qs ->
  cenvs_split E (Qs1L ++ Qs ++ Qs1R) Qs2 Qs3.
Proof with auto.
  intros. inversion H; subst.
  generalize dependent Qs'. generalize dependent Qs3.
  revert Qs2. revert Qs1R.
  induction Qs1L; intros; simpl_env in *.
    rewrite_env (lcempty ++ Qs') in H1.
      apply cenvs_split_multi_insert_empties with (Qs := Qs) in H1...
      simpl_env in H1. apply cenvs_split_ms with (Qs' := Qs ++ Qs')...
        skip.
    inversion H2; subst; simpl_env in *.
Admitted.

Lemma cenvs_split_insert_empties_right: forall E Qs1 Qs2L Qs2R Qs3 Qs,
  cenvs_split E Qs1 (Qs2L ++ Qs2R) Qs3 ->
  lcempties Qs ->
  cenvs_split E Qs1 (Qs2L ++ Qs ++ Qs2R) Qs3.
Proof.  
  intros. apply cenvs_split_commute.
  apply cenvs_split_commute in H.
  apply cenvs_split_insert_empties_left; auto.
Qed.

Lemma cenvs_split_drop_empties_left: forall E Qs1L Qs1R Qs2 Qs3 Qs,
  cenvs_split E (Qs1L ++ Qs ++ Qs1R) Qs2 Qs3 ->
  lcempties Qs ->
  cenvs_split E (Qs1L ++ Qs1R) Qs2 Qs3.
Proof with auto.
  intros. inversion H; subst.
  generalize dependent Qs'. generalize dependent Qs3.
  revert Qs2. revert Qs1R.
  induction Qs1L; intros; simpl_env in *.
    rewrite_env (lcempty ++ Qs') in H1.
Admitted.

Lemma cenvs_split_drop_empties_right: forall E Qs1 Qs2L Qs2R Qs3 Qs,
  cenvs_split E Qs1 (Qs2L ++ Qs ++ Qs2R) Qs3 ->
  lcempties Qs ->
  cenvs_split E Qs1 (Qs2L ++ Qs2R) Qs3.
Proof.
  intros. apply cenvs_split_commute.
  apply cenvs_split_commute in H.
  apply cenvs_split_drop_empties_left with (Qs := Qs); auto.
Qed.

Lemma cenvs_split_pad_both: forall E Qs1 Qs2 Qs3 Qs1L Qs1R Qs2L Qs2R,
  cenvs_split E Qs1 Qs2 Qs3 ->
  lcempties Qs1L ->
  lcempties Qs1R ->
  lcempties Qs2L ->
  lcempties Qs2R ->
  cenvs_split E (Qs1L ++ Qs1 ++ Qs1R) (Qs2L ++ Qs2 ++ Qs2R) Qs3.
Proof with auto.
  intros E Qs1 Qs2 Qs3 Qs1L Qs1R Qs2L Qs2R CS Emp1L Emp1R Emp2L Emp2R.
  rewrite_env (lcempty ++ Qs1L ++ Qs1 ++ Qs1R).
  apply cenvs_split_insert_empties_left...
  rewrite_env (Qs1 ++ Qs1R ++ lcempty).
  apply cenvs_split_insert_empties_left...
  rewrite_env (lcempty ++ Qs2L ++ Qs2 ++ Qs2R).
  apply cenvs_split_insert_empties_right...
  rewrite_env (Qs2 ++ Qs2R ++ lcempty).
  apply cenvs_split_insert_empties_right...
  simpl_env...
Qed.

Lemma cenvs_split_unpad_both: forall E Qs1 Qs2 Qs3 Qs1L Qs1R Qs2L Qs2R,
  cenvs_split E (Qs1L ++ Qs1 ++ Qs1R) (Qs2L ++ Qs2 ++ Qs2R) Qs3 ->
  lcempties Qs1L ->
  lcempties Qs1R ->
  lcempties Qs2L ->
  lcempties Qs2R ->
  cenvs_split E Qs1 Qs2 Qs3.
Proof with auto.
  intros E Qs1 Qs2 Qs3 Qs1L Qs1R Qs2L Qs2R CS Emp1L Emp1R Emp2L Emp2R.
  rewrite_env (lcempty ++ Qs1L ++ Qs1 ++ Qs1R) in CS.
  apply cenvs_split_drop_empties_left in CS...
  rewrite_env (Qs1 ++ Qs1R ++ lcempty) in CS.
  apply cenvs_split_drop_empties_left in CS...
  rewrite_env (lcempty ++ Qs2L ++ Qs2 ++ Qs2R) in CS.
  apply cenvs_split_drop_empties_right in CS...
  rewrite_env (Qs2 ++ Qs2R ++ lcempty) in CS.
  apply cenvs_split_drop_empties_right in CS...
  simpl_env in CS...
Qed.

Lemma cenv_split_multi_empty: forall E Qs Z,
  cenv_split_multi E Qs cempty Z ->
  lcempties Qs /\ Z = None.
Proof with auto.
  intros. remember cempty as Q. induction H; subst.
    split...
    split... constructor...
    inversion H1. subst.
      lapply IHcenv_split_multi2... lapply IHcenv_split_multi1...
      intros. intuition. subst.
      apply lcempties_append...
Qed.

Lemma cenv_split_multi_empties: forall E Qs Q Z,
  cenv_split_multi E Qs Q Z ->
  lcempties Qs ->
  Q = cempty /\ Z = None.
Proof with auto.
  intros. induction H; intros...
    inversion H0; subst...
    apply lcempties_divide in H0. intuition; subst; inversion H2...
Qed.

Lemma cenvs_split_multi_empties: forall E Qs1 Qs2,
  cenvs_split_multi E Qs1 Qs2 ->
  (lcempties Qs1 <-> lcempties Qs2).
Proof with auto.
  intros. induction H; split; intros...
    apply lcempties_divide in H2. intuition.
      apply cenv_split_multi_empties in H0...
        intuition. subst. simpl_env in *. apply lcempties_append...
         constructor...
    inversion H2. subst. apply cenv_split_multi_empty in H0.
      intuition. subst. apply lcempties_append...
Qed.

Lemma cenvs_split_simple_empties: forall E Qs1 Qs2 Qs3,
  cenvs_split_simple E Qs1 Qs2 Qs3 ->
  lcempties Qs3 ->
  (lcempties Qs1 /\ lcempties Qs2).
Proof with auto.
  intros E Qs1 Qs2 Qs3 H. induction H; intros...
    simpl_env in H0. apply lcempties_divide in H0. intuition.
      inversion H1. subst. constructor...
    simpl_env in H0. apply lcempties_divide in H0. intuition.
      inversion H1. subst. constructor...
Qed.

Lemma cenvs_split_empties: forall E Qs1 Qs2 Qs3,
  cenvs_split E Qs1 Qs2 Qs3 ->
  lcempties Qs3 ->
  lcempties Qs1 /\ lcempties Qs2.
Proof with auto.
  intros E Qs1 Qs2 Qs3. revert Qs1 Qs2.
  induction Qs3; intros Qs1 Qs2 CS Emp; induction CS; subst.
    apply cenvs_split_multi_empties in H. apply H in Emp.
      apply cenvs_split_simple_empties in H0...
    apply cenvs_split_multi_empties in H. apply H in Emp.
      apply cenvs_split_simple_empties in H0...
Qed.

Lemma cenvs_split_simple_empties_left: forall E Qs1 Qs2 Qs3,
  cenvs_split_simple E Qs1 Qs2 Qs3 ->
  wf_cenvs E Qs3 ->
  lcempties Qs1 ->
  cenvs_split_multi E Qs2 Qs3.
Proof with auto.
  intros E Qs1 Qs2 Qs3 CS. induction CS; intros...
Admitted.

Lemma cenvs_split_simple_empties_right: forall E Qs1 Qs2 Qs3,
  cenvs_split_simple E Qs1 Qs2 Qs3 ->
  wf_cenvs E Qs3 ->
  lcempties Qs2 ->
  cenvs_split_multi E Qs1 Qs3.
Proof.
  intros. eapply cenvs_split_simple_empties_left; eauto.
    apply cenvs_split_simple_commute. auto.
Qed.

Lemma cenvs_split_empties_left: forall E Qs1 Qs2 Qs3,
  cenvs_split E Qs1 Qs2 Qs3 ->
  lcempties Qs1 ->
  cenvs_split_multi E Qs2 Qs3.
Proof with auto.
  intros E Qs1 Qs2 Qs3 CS Emp.
  generalize dependent Qs3. revert Qs2.
  induction Emp; intros; inversion CS; subst.
    apply cenvs_split_simple_empty_left in H0. subst...
    apply IHEmp. simpl_env in H0. inversion H0; subst.
      apply cenvs_split_ms with (Qs' := Qs4)...
        rewrite_env (lcempty ++ [cempty] ++ Qs4) in H.
        rewrite_env (lcempty ++ Qs4).
        apply cenvs_split_multi_drop_empty...
      (* More list messiness; skip for now. *)
Admitted.

Lemma cenvs_split_empties_right: forall E Qs1 Qs2 Qs3,
  cenvs_split E Qs1 Qs2 Qs3 ->
  lcempties Qs2 ->
  cenvs_split_multi E Qs1 Qs3.
Proof.
  intros. eapply cenvs_split_empties_left; eauto.
    apply cenvs_split_commute. auto.
Qed.

Lemma wf_empties: forall E Qs,
  wf_env E ->
  lcempties Qs ->
  wf_cenvs E Qs.
Proof with eauto.
  intros. induction H0.
    constructor...
    inversion IHlcempties; subst...
      econstructor. econstructor...
      eapply cenv_split_multi_empties in H0... intuition. subst.
        apply wf_cenvs_csm with (Q := cempty) (Z := None). simpl_env.
          econstructor...
Qed.

Lemma wf_cenvs_split_multi': forall G Qs1 Qs2,
  cenvs_split_multi G Qs1 Qs2 ->
  wf_cenvs G Qs1.
Proof with auto.
  intros. assert (wf_cenvs G Qs2).
    eapply wf_cenvs_split_multi; eauto.
    inversion H0; subst.
      inversion H. subst...
      eapply cenv_split_multi_trans in H1; eauto.
        destruct H1 as [Z' H1]. econstructor; eauto.
Qed.

Lemma cenvs_split_sub_right: forall E Qs1 Qs2 Qs3 Qs3' QsE,
  cenvs_split E Qs1 Qs2 Qs3 ->
  cenvs_split E Qs3 QsE Qs3' ->
  lcempties QsE ->
  cenvs_split E Qs1 Qs2 Qs3'.
Proof with eauto.
  intros. inversion H; inversion H0; subst.
  apply cenvs_split_simple_empties_right in H9...
    assert (cenvs_split_multi E Qs' Qs3').
        eapply cenvs_split_multi_trans...
        eapply cenvs_split_multi_trans...
      eapply cenvs_split_ms...
    eapply wf_cenvs_split_multi'...
Qed.

Lemma proc_typing_sub_right: forall Qs QsE Qs' P T,
  proc_typing Qs P T ->
  cenvs_split empty Qs QsE Qs' ->
  lcempties QsE ->
  proc_typing Qs' P T.
Proof with auto.
  intros Qs QsE Qs' P T PTyp. revert QsE Qs'.
  (proc_typing_cases (induction PTyp) Case); intros.
    Case "typing_exp".
      apply typing_exp with (Q := Q)...
        apply cenvs_split_empties_right in H1...
        apply cenvs_split_multi_trans with (Qs2 := Qs)...
    Case "typing_parl".
      apply typing_parl with (Qs1 := Qs1) (Qs2 := Qs2)...
        apply cenvs_split_sub_right with (Qs3 := Qs3) (QsE := QsE)...
    Case "typing_parr".
      apply typing_parr with (Qs1 := Qs1) (Qs2 := Qs2)...
        apply cenvs_split_sub_right with (Qs3 := Qs3) (QsE := QsE)...
    Case "typing_new".
      destruct (nd_cons_cenvs_with_right empty Qs FQs QsE Qs') as
          [FQs' [L' [Cons H']]]...
      pick fresh X and apply typing_new.
        auto.
        instantiate (1 := FQs')...
        lapply (H' X T1)... lapply (H2 X)... intros.
        apply H5 with (QsE := QsE)... 
Qed.

Lemma nd_cons_cenvs_not_empty: forall X T Qs FQs,
  nd_cons_cenvs Qs FQs ->
  lcempties (FQs X T) ->
  False.
Proof with auto.
  intros. inversion H; subst; simpl in H0.
    simpl_env in H0. apply lcempties_divide in H0. intuition.
      inversion H2.
    simpl_env in H0. apply lcempties_divide in H0. intuition.
      inversion H2.
Qed.

Lemma cenvs_split_multi_single: forall E Q Qs,
  cenvs_split_multi E [Q] Qs ->
  exists QsL, exists QsR, Qs = QsL ++ [Q] ++ QsR
    /\ lcempties QsL /\ lcempties QsR.
Proof with auto.
  intros E Q Qs. revert Q.
  induction Qs; intros; inversion H; subst. 
    apply app_eq_unit in H0. destruct H0 as [[H1 H2] | [H1 H2]]; subst.
      apply cenv_split_multi_empties in H5... intuition. subst. 
        apply IHQs in H4... destruct H4 as [QsL [QsR [H1 [H2 H3]]]]. subst.
        simpl_env in *. exists ([cempty] ++ QsL). exists QsR. repeat split...
          apply lcempties_append... constructor...
      simpl_env in *. apply cenv_split_multi_single in H5. intuition. subst.
        apply cenvs_split_multi_empties in H4.
        exists lcempty. exists Qs. repeat split...
          apply H4...
Qed.

Lemma nd_cons_cenvs_single: forall E X T Qs FQs,
  nd_cons_cenvs Qs FQs ->
  cenvs_split_multi E [[(X, cbind_proto cdir_both T)]] (FQs X T)->
  lcempties Qs.
Proof with auto.
  intros E X T Qs FQs Cons CSM.
  apply cenvs_split_multi_single in CSM.
  destruct CSM as [QsL [QsR [Eq [EmpL EmpR]]]].
  inversion Cons; subst;
      apply app_eq_cases_mid in Eq;
      destruct Eq as [Qs [[Eq1 Eq2] | [Eq1 Eq2]]]; subst.
    apply lcempties_divide in EmpR. intuition. inversion H0.
    apply app_eq_cases_mid in Eq1;
      destruct Eq1 as [Qs' [[Eq1 Eq2] | [Eq1 Eq2]]]; subst.
        apply lcempties_divide in EmpL. apply lcempties_divide in EmpR.
           intuition. apply lcempties_append...
        apply lcempties_divide in EmpL. intuition.
          apply lcempties_divide in H0. intuition.
          repeat apply lcempties_append...
    apply lcempties_divide in EmpR. intuition. inversion H0.
    apply app_eq_cases_mid in Eq1;
      destruct Eq1 as [Qs' [[Eq1 Eq2] | [Eq1 Eq2]]]; subst.
        apply lcempties_divide in EmpL. apply lcempties_divide in EmpR.
           intuition. symmetry in Eq1. apply app_eq_unit in Eq1.
           destruct Eq1 as [[Eq1 Eq2] | [Eq1 Eq2]]; subst...
             inversion Eq2; subst.
               repeat apply lcempties_append... constructor...
             inversion Eq2.
        apply lcempties_divide in EmpL. intuition.
          apply lcempties_divide in H0. intuition.
          inversion H1.
Qed.

Lemma cenv_split_multi_half_chan: forall E X d T QL QR QsL QsR Q Z,
  cenv_split_multi E (QsL ++ [QL ++ [(X, cbind_proto cdir_both T)] ++ QR] ++ QsR) Q Z ->
  exists Q', exists Z', cenv_split_multi E (QsL ++ [QL ++ [(X, cbind_proto d T)] ++ QR] ++ QsR) Q' Z'.
Proof with auto.
  intros. destruct d.
    remember (QsL ++ [QL ++ [(X, cbind_proto cdir_both T)] ++ QR] ++ QsR) as Qs.
    generalize dependent QsR. revert QL QR QsL.
    induction H; intros.
      symmetry in HeqQs. apply app_eq_nil in HeqQs. intuition.
        inversion H1.
      symmetry in HeqQs. apply app_eq_unit in HeqQs.
        destruct HeqQs as [[Eq1 Eq2] | [Eq1 Eq2]]; subst.
          inversion Eq2. subst. simpl_env in *.
            exists (QL ++ [(X, cbind_proto cdir_snk T)] ++ QR). exists None.
            constructor.
            apply wf_cenv_rebind_chan with (d1 := cdir_both) (T1 := T)...
              apply wf_proto_from_wf_cenv in H...
          inversion Eq2.
      skip.
    skip.
    exists Q. exists Z...
Qed.

Lemma wf_cenvs_half_chan: forall E X d T QL QR QsL QsR,
  wf_cenvs E (QsL ++ [QL ++ [(X, cbind_proto cdir_both T)] ++ QR] ++ QsR) ->
  wf_cenvs E (QsL ++ [QL ++ [(X, cbind_proto d T)] ++ QR] ++ QsR).
Proof with auto.
  intros.
  inversion H; subst.
    symmetry in H0. apply app_eq_nil in H0. intuition.
      inversion H3.
    apply cenv_split_multi_half_chan with (d := d) in H0.
      destruct H0 as [Q' [Z' CSM]].
      apply wf_cenvs_csm with (Q := Q') (Z := Z')...
Qed.

Lemma wf_cenvs_cons_fresh: forall E Q X d T QsL QsR,
  wf_cenvs E (QsL ++ [Q] ++ QsR) ->
  wf_proto E T ->
  X `notin` dom E ->
  X `notin` dom Q ->
  X `notin` doms cbinding QsL ->
  X `notin` doms cbinding QsR ->
  wf_cenvs E (QsL ++ [[(X, cbind_proto d T)] ++ Q] ++ QsR).
Proof with auto.
  intros.
  assert (wf_cenvs E (QsL ++ [[(X, cbind_proto cdir_both T)] ++ Q] ++ QsR)).
  apply -> (nd_cons_cenvs_regular E X T (QsL ++ [Q] ++ QsR) 
                    (fun X T =>
                       QsL ++ [[(X, cbind_proto cdir_both T)] ++ Q] ++ QsR)) in H...
    repeat rewrite doms_append. simpl. fsetdec.
    apply nd_cons_cenvs_cons.
  rewrite_env [cempty ++ [(X, cbind_proto cdir_both T)] ++ Q] in H5.
    rewrite_env  [cempty ++ [(X, cbind_proto d T)] ++ Q].
    apply wf_cenvs_half_chan...
Qed.

Lemma cenvs_split_proc_insert_left: forall E Q1 Q2 Q3 QsL QsR Z,
  cenv_split_proc E Q1 Q2 Q3 Z ->
  wf_cenvs E (QsL ++ [Q3] ++ QsR) ->
  cenvs_split E (QsL ++ [Q1] ++ QsR) [Q2] (QsL ++ [Q3] ++ QsR).
Proof with auto.
  intros E Q1 Q2 Q3 QsL. revert Q1 Q2 Q3.
  induction QsL; intros.
    simpl in *. inversion H0. subst. inversion H1; subst.
      rewrite_env ([Q1] ++ lcempty). rewrite_env ([Q2] ++ lcempty).
        apply cenvs_split_ms with (Qs' := ([Q1] ++ [Q2]) ++ lcempty).
          apply cenvs_split_multi_cons with (Z := Z)...
            apply cenv_split_multi_branch with
                (Q1 := Q1) (Q2 := Q2) (X := None) (Y := None)...
              constructor. eapply wf_cenv_split_proc_left; eauto.
              constructor. eapply wf_cenv_split_proc_right; eauto.
          simpl. apply cenvs_split_simple_left. apply cenvs_split_simple_right...
      simpl_env. rewrite_env ([Q2] ++ lcempty). rewrite H2.
        apply cenvs_split_ms with (Qs' := ([Q1] ++ [Q2]) ++ QsR).
          apply cenvs_split_multi_cons with (Z := Z)...
            apply cenvs_split_multi_id...
              simpl_env in H0. apply wf_cenvs_append_wf in H0. intuition.
            apply cenv_split_multi_branch with
                (Q1 := Q1) (Q2 := Q2) (X := None) (Y := None)...
              constructor. eapply wf_cenv_split_proc_left; eauto.
              constructor. eapply wf_cenv_split_proc_right; eauto.
          simpl. apply cenvs_split_simple_left. apply cenvs_split_simple_right.
            apply cenvs_split_simple_right_id.
    simpl_env in *. lapply (IHQsL Q1 Q2 Q3 QsR Z H). intros.
      inversion H1; subst. apply cenvs_split_ms with (Qs' := [a] ++ Qs')...
        rewrite_env (a :: QsL ++ [Q3] ++ QsR).
          apply cenvs_split_multi_cons with (Z := None)...
          apply cenv_split_multi_leaf...
            apply wf_cenvs_to_single. apply wf_cenvs_append_wf in H0. intuition.
        simpl. apply cenvs_split_simple_left...
      apply wf_cenvs_append_wf in H0. intuition.
Qed.

Lemma cenv_split_exp_insert_right: forall E X d T QL QR,
  wf_cenv E (QL ++ QR) ->
  X `notin` dom E ->
  X `notin` dom QL ->
  X `notin` dom QR ->
  wf_proto E T ->
  cenv_split_exp E (QL ++ QR) [(X, cbind_proto d T)]
                             (QL ++ [(X, cbind_proto d T)] ++ QR).
Proof with auto.
  intros E X d T QL. induction QL; intros QR WFCE NiE NiL NiR WFP.
    simpl_env in *. 
      rewrite_env ([(X, cbind_proto d T)] ++ cempty).
      rewrite_env ([(X, cbind_proto d T)] ++ QR).
      constructor...
        apply cenv_split_exp_right_id...
    destruct a as [X0 [d0 T0]]. simpl_env in *.
      inversion WFCE. subst.
      constructor...
Qed.

Lemma wf_cenv_mid_notin_dom: forall E X d T QL QR,
  wf_cenv E (QL ++ [(X, cbind_proto d T)] ++ QR) ->
  X `notin` dom QL /\ X `notin` dom QR.
Proof.
  intros. apply uniq_from_wf_cenv in H.
  destruct_uniq. fsetdec.
Qed.

Lemma wf_cenvs_pad: forall E Qs QsL QsR,
  wf_cenvs E Qs ->
  lcempties QsL ->
  lcempties QsR ->
  wf_cenvs E (QsL ++ Qs ++ QsR).
Proof with auto.
  intros. induction H.
    simpl_env. apply wf_empties... apply lcempties_append...
    rewrite_env (Qs ++ lcempty) in H.
      apply cenv_split_multi_insert_empties with (Qs := QsR) in H...
      rewrite_env (lcempty ++ Qs ++ QsR) in H.
      apply cenv_split_multi_insert_empties with (Qs := QsL) in H...
      simpl_env in H. econstructor; eauto.
Qed.

Lemma cenvs_split_multi_unpad: forall E Qs QsL QsR,
  wf_cenvs E Qs ->
  lcempties QsL ->
  lcempties QsR ->
  cenvs_split_multi E Qs (QsL ++ Qs ++ QsR).
Proof with simpl_env; auto.
  intros. apply cenvs_split_multi_trans with (Qs2 := Qs ++ QsR)...
    rewrite_env (Qs ++ QsR ++ lcempty).
      rewrite_env (Qs ++ lcempty).
      apply cenvs_split_multi_drop_empties with (Qs := QsR)...
      apply cenvs_split_multi_id...
        apply wf_cenvs_pad with (QsL := lcempty) (QsR := QsR) in H...
    rewrite_env (lcempty ++ QsL ++ Qs ++ QsR).
      rewrite_env (lcempty ++ Qs ++ QsR).
      apply cenvs_split_multi_drop_empties with (Qs := QsL)...
      apply cenvs_split_multi_id...
        apply wf_cenvs_pad...
Qed.

Lemma nd_cons_cenvs_shape: forall Qs FQs,
  nd_cons_cenvs Qs FQs ->
  exists Q, exists QsL, exists QsR, forall X T,
    (FQs X T) = QsL ++ [[(X, cbind_proto cdir_both T)] ++ Q] ++ QsR.
Proof with auto.
  intros. induction H.
    exists cempty. exists QsL. exists QsR. intros...
    exists Q. exists QsL. exists QsR. intros...
Qed.

Lemma eq_padded_single: forall QsL b1 Q1 QsR QsLE b2 Q2 QsRE,
  QsL ++ [[b1] ++ Q1] ++ QsR = QsLE ++ [[b2] ++ Q2] ++ QsRE ->
  lcempties QsLE ->
  lcempties QsRE ->
  QsL = QsLE /\ b1 = b2 /\ Q1 = Q2 /\ QsR = QsRE.
Proof with auto.
  induction QsL; intros;
      inversion H0; subst; inversion H; subst; simpl_env in *.
    split...
    apply lcempties_divide in H1. inversion H1. inversion H3.
    apply IHQsL in H5... intuition. subst...
Qed.

Lemma cenv_split_exp_single_right: forall E Q1 X d T Q3,
  cenv_split_exp E Q1 [(X, cbind_proto d T)] Q3 ->
  exists QL, exists QR,
    Q3 = QL ++ [(X, cbind_proto d T)] ++ QR /\
    Q1 = QL ++ QR.
Proof with auto.
  intros. remember [(X, cbind_proto d T)] as Q2.
  induction H; subst.
    inversion HeqQ2.
    assert ([(X, cbind_proto d T)] = [(X, cbind_proto d T)])...
      destruct (IHcenv_split_exp H3) as [QL [QR [Eq1 Eq2]]]. subst.
      exists ([(X0, cbind_proto d0 T0)] ++ QL). exists QR...
    inversion HeqQ2. subst. 
      apply cenv_split_exp_empty_right in H. subst.
      exists cempty. exists Q3...
Qed.

Lemma cenv_split_exp_single_left: forall E X d T Q2 Q3,
  cenv_split_exp E [(X, cbind_proto d T)] Q2 Q3 ->
  exists QL, exists QR,
    Q3 = QL ++ [(X, cbind_proto d T)] ++ QR /\
    Q2 = QL ++ QR.
Proof.
  intros. apply cenv_split_exp_commute in H.
  apply cenv_split_exp_single_right in H.
  destruct H as [QL [QR [Eq1 Eq2]]]. subst.
  exists QL. exists QR. auto.
Qed.

Lemma cenv_split_exp_focus_right: forall E Q1 Q2L X d T Q2R Q3,
  cenv_split_exp E Q1 (Q2L ++ [(X, cbind_proto d T)] ++ Q2R) Q3 ->
  exists Q1L, exists Q1R, exists Q3L, exists Q3R,
    Q3 = Q3L ++ [(X, cbind_proto d T)] ++ Q3R /\
    Q1 = Q1L ++ Q1R /\
    cenv_split_exp E Q1L Q2L Q3L /\
    cenv_split_exp E Q1R Q2R Q3R.
Proof with auto.
  intros. remember (Q2L ++ [(X, cbind_proto d T)] ++ Q2R) as Q2.
  generalize dependent Q2R. revert X d T Q2L.
  induction H; intros; subst.
    symmetry in HeqQ2. apply app_eq_nil in HeqQ2.
      intuition. discriminate H1.
    destruct (IHcenv_split_exp X0 d0 T0 Q2L Q2R)
        as [Q1L [Q1R [Q3L [Q3R [Eq1 [Eq2 [CS1 CS2]]]]]]]... subst.
      exists ([(X, cbind_proto d T)] ++ Q1L). exists Q1R.
      exists ([(X, cbind_proto d T)] ++ Q3L). exists Q3R...
    destruct Q2L; inversion HeqQ2; subst; simpl_env in *.
      exists cempty. exists Q1. exists cempty. exists Q3.
        repeat split... constructor. apply wf_cenv_split_exp in H...
      destruct (IHcenv_split_exp X0 d0 T0 Q2L Q2R)
          as [Q1L [Q1R [Q3L [Q3R [Eq1 [Eq2 [CS1 CS2]]]]]]]... subst.
        exists Q1L. exists Q1R.
        exists ([(X, cbind_proto d T)] ++ Q3L). exists Q3R.
        repeat split; simpl_env...
Qed.

Lemma cenv_split_exp_focus_left: forall E Q1L X d T Q1R Q2 Q3,
  cenv_split_exp E (Q1L ++ [(X, cbind_proto d T)] ++ Q1R) Q2 Q3 ->
  exists Q2L, exists Q2R, exists Q3L, exists Q3R,
    Q3 = Q3L ++ [(X, cbind_proto d T)] ++ Q3R /\
    Q2 = Q2L ++ Q2R /\
    cenv_split_exp E Q1L Q2L Q3L /\
    cenv_split_exp E Q1R Q2R Q3R.
Proof.
  intros. apply cenv_split_exp_commute in H.
  apply cenv_split_exp_focus_right in H.
  destruct H as [Q2L [Q2R [Q3L [Q3R [Eq1 [Eq2 [CS1 CS2]]]]]]].
  exists Q2L. exists Q2R. exists Q3L. exists Q3R.
  repeat split; try solve [auto | apply cenv_split_exp_commute; auto].
Qed.

Lemma cenv_split_multi_two: forall E Q1 Q2 Q3 Z,
  cenv_split_multi E (Q1 :: Q2 :: lcempty) Q3 Z ->
  exists Z', cenv_split_proc E Q1 Q2 Q3 Z'.
Proof with auto.
  intros. remember (Q1 :: Q2 :: lcempty) as Qs.
  generalize dependent Q2. revert Q1.
  induction H; intros; subst; try solve [ discriminate HeqQs ].
    destruct Qs1; simpl_env in *; subst.
      apply cenv_split_multi_empties in H... intuition. subst.
        apply cenv_split_proc_empty_left in H1. intuition. subst.
        lapply (IHcenv_split_multi2 Q0 Q4)...
      inversion HeqQs. subst. apply app_eq_unit in H4.
        destruct H4 as [[Eq1 Eq2] | [Eq1 Eq2]]; subst; simpl_env in *.
          exists Z. apply cenv_split_multi_single in H.
            apply cenv_split_multi_single in H0. intuition. subst...
          apply cenv_split_multi_empties in H0... intuition. subst.
            apply cenv_split_proc_empty_right in H1. intuition. subst.
            lapply (IHcenv_split_multi1 Q0 Q4)...
Qed.

Lemma cenvs_split_multi_two: forall E Q1 Q2 Q3,
  cenvs_split_multi E (Q1 :: Q2 :: lcempty) (Q3 :: lcempty) ->
  exists Z, cenv_split_proc E Q1 Q2 Q3 Z.
Proof with auto.
  intros. remember (Q3 :: lcempty) as Qs.
  remember (Q1 :: Q2 :: lcempty) as Qs'.
  generalize dependent Q3. generalize dependent Q2. revert Q1.
  induction H; intros; subst.
    discriminate HeqQs.
    inversion HeqQs. subst.
      apply cenvs_split_multi_empties in H.
      assert (lcempties lcempty)... apply H in H2.
      inversion H2; subst.
        simpl_env in HeqQs'. simpl in HeqQs'. subst.
          apply cenv_split_multi_two in H0...
        destruct Qs.
          simpl in HeqQs'. inversion HeqQs'. subst.
            inversion H3. subst.
            apply cenv_split_multi_empties in H0...
            destruct H0. subst. exists None...
          simpl in HeqQs'. inversion HeqQs'. subst.
            apply app_eq_unit in H6.
            destruct H6 as [[Eq1 Eq2] | [Eq1 Eq2]]; subst.
              inversion Eq2. subst.
                apply cenv_split_multi_single in H0.
                destruct H0. subst. exists None.
                apply cenv_split_proc_right_id.
                  apply wf_cenvs_to_single...
              discriminate Eq2.
Qed.

Lemma cenvs_split_two_proc: forall E Q1 Q2 Qs,
  cenvs_split E [Q1] [Q2] Qs ->
  exists Q, exists Z, cenv_split_proc E Q1 Q2 Q Z.
Proof with auto.
  intros. inversion H.
  inversion H1; inversion H11; inversion H17; subst;
      apply wf_cenvs_split_multi' in H0; inversion H0;
      simpl in *; subst; exists Q;
      apply cenv_split_multi_two in H2;
      destruct H2 as [Z' H2]; exists Z'...
    apply cenv_split_proc_commute...
Qed.

Lemma cenv_split_proc_mid_snksrc: forall E X T Q1L Q1R Q2L Q2R Q3 Z,
  cenv_split_proc E (Q1L ++ [(X, cbind_proto cdir_snk T)] ++ Q1R)
                              (Q2L ++ [(X, cbind_proto cdir_src T)] ++ Q2R) Q3 Z ->
  exists Q3L, exists Q3R,
    Q3 = Q3L ++ [(X, cbind_proto cdir_both T)] ++ Q3R /\
    cenv_split_exp E Q1L Q2L Q3L /\
    cenv_split_exp E Q1R Q2R Q3R /\
    Z = Some X.
Proof with auto.
  intros.
  remember (Q1L ++ [(X, cbind_proto cdir_snk T)] ++ Q1R) as Q1.
  remember (Q2L ++ [(X, cbind_proto cdir_src T)] ++ Q2R) as Q2.
  generalize dependent Q2R. revert Q2L.
  generalize dependent Q1R. revert X T Q1L.
  induction H; intros; subst; simpl_env in *.
    symmetry in HeqQ1. apply app_eq_nil in HeqQ1.
      intuition. simpl in H1. discriminate H1.
    destruct Q1L as [ | [X' [d' T']] Q1L ];
        simpl_env in *; inversion HeqQ1; subst.
      apply dom_cenv_split_proc in H. simpl_env in H. fsetdec.
      assert (Q1L ++ (X0, cbind_proto cdir_snk T0) :: Q1R =
                  Q1L ++ [(X0, cbind_proto cdir_snk T0)] ++ Q1R)...
        destruct (IHcenv_split_proc X0 T0 Q1L Q1R H3 Q2L Q2R) as
            [Q3L [Q3R [EqQ [CS1 [CS2 EqZ]]]]]; subst...
        exists ([(X', cbind_proto d' T')] ++ Q3L). exists Q3R...
    destruct Q2L as [ | [X' [d' T']] Q2L ];
        simpl_env in *; inversion HeqQ2; subst.
      apply dom_cenv_split_proc in H. simpl_env in H. fsetdec.
      assert (Q1L ++ [(X0, cbind_proto cdir_snk T0)] ++ Q1R =
                  Q1L ++ [(X0, cbind_proto cdir_snk T0)] ++ Q1R)...
        destruct (IHcenv_split_proc X0 T0 Q1L Q1R H3 Q2L Q2R) as
            [Q3L [Q3R [EqQ [CS1 [CS2 EqZ]]]]]; subst...
        exists ([(X', cbind_proto d' T')] ++ Q3L). exists Q3R...
    assert (wf_env E). apply wf_cenv_split_exp in H...
      destruct Q1L as [ | [X1 [d1 T1]] Q1L ];
          destruct Q2L as [ | [X2 [d2 T2]] Q2L ];
          inversion HeqQ1; inversion HeqQ2;
          repeat subst; simpl_env in *; try solve
            [ apply dom_cenv_split_exp in H; simpl_env in H; fsetdec ].
        exists cempty. exists Q3...
        apply cenv_split_exp_not_in_left with (X := X0) in H;
            simpl_env in *; fsetdec.
    assert (wf_env E). apply wf_cenv_split_exp in H...
      destruct Q1L as [ | [X1 [d1 T1]] Q1L ];
          destruct Q2L as [ | [X2 [d2 T2]] Q2L ];
          inversion HeqQ1; inversion HeqQ2;
          repeat subst; simpl_env in *; try solve
            [ apply dom_cenv_split_exp in H; simpl_env in H; fsetdec ].
        exists cempty. exists Q3...
        apply cenv_split_exp_not_in_left with (X := X0) in H;
            simpl_env in *; fsetdec.
Qed.

Lemma cenv_split_proc_mid_srcsnk: forall E X T Q1L Q1R Q2L Q2R Q3 Z,
  cenv_split_proc E (Q1L ++ [(X, cbind_proto cdir_src T)] ++ Q1R)
                              (Q2L ++ [(X, cbind_proto cdir_snk T)] ++ Q2R) Q3 Z ->
  exists Q3L, exists Q3R,
    Q3 = Q3L ++ [(X, cbind_proto cdir_both T)] ++ Q3R /\
    cenv_split_exp E Q1L Q2L Q3L /\
    cenv_split_exp E Q1R Q2R Q3R /\
    Z = Some X.
Proof.
  intros. apply cenv_split_proc_commute in H.
  apply cenv_split_proc_mid_snksrc in H.
  destruct H as [Q3L [Q3R [EqQ [CS1 [CS2 EqZ]]]]].
  exists Q3L. exists Q3R. repeat split;
      try apply cenv_split_exp_commute; auto.
Qed.

Lemma cenvs_split_single_srcsnk: forall E X T Q1L Q1R Q2L Q2R Q3L Q3R QsL QsR,
  cenvs_split E [Q1L ++ [(X, cbind_proto cdir_src T)] ++ Q1R]
                       [Q2L ++ [(X, cbind_proto cdir_snk T)] ++ Q2R]
         (QsL ++ [Q3L ++ [(X, cbind_proto cdir_both T)] ++ Q3R] ++ QsR) ->
  lcempties QsL /\ lcempties QsR.
Proof with auto.
  intros. (* Let's look at this again later... *)
Admitted.

Lemma cenvs_split_single_snksrc: forall E X T Q1L Q1R Q2L Q2R Q3L Q3R QsL QsR,
  cenvs_split E [Q1L ++ [(X, cbind_proto cdir_snk T)] ++ Q1R]
                       [Q2L ++ [(X, cbind_proto cdir_src T)] ++ Q2R]
         (QsL ++ [Q3L ++ [(X, cbind_proto cdir_both T)] ++ Q3R] ++ QsR) ->
  lcempties QsL /\ lcempties QsR.
Proof.
  intros. apply cenvs_split_commute in H.
  apply cenvs_split_single_srcsnk in H. auto.
Qed.

Lemma cenvs_split_from_proc: forall E Q1 Q2 Q3 Z,
  cenv_split_proc E Q1 Q2 Q3 Z ->
  cenvs_split E [Q1] [Q2] [Q3].
Proof with auto.
  intros. apply cenvs_split_ms with (Qs' := ([Q1] ++ [Q2])).
    rewrite_env (([Q1] ++ [Q2]) ++ lcempty).
      rewrite_env (Q3 :: lcempty).
      apply cenvs_split_multi_cons with (Z := Z).
        constructor. apply wf_cenv_split_proc in H...
        apply cenv_split_multi_branch with
            (Q1 := Q1) (Q2 := Q2) (X := None) (Y := None);
            try constructor...
          apply wf_cenv_split_proc_left in H...
          apply wf_cenv_split_proc_right in H...
        apply wf_cenvs_from_single.
          apply wf_cenv_split_proc in H...
    simpl. repeat constructor.
Qed.

Lemma cenvs_split_to_proc: forall E Q1 Q2 Q3,
  cenvs_split E [Q1] [Q2] [Q3] ->
  exists Z, cenv_split_proc E Q1 Q2 Q3 Z.
Proof with auto.
  intros. inversion H. subst. inversion H1; subst.
    apply cenvs_split_simple_empty_left in H7. subst.
      apply cenvs_split_multi_two in H0...
    apply cenvs_split_simple_empty_right in H7. subst.
      apply cenvs_split_multi_two in H0...
      destruct H0 as [Z H0]. exists Z.
      apply cenv_split_proc_commute...
Qed.

Lemma cenvs_split_multi_forget_empty: forall E Qs QsL QsR,
  cenvs_split_multi E Qs (QsL ++ [cempty] ++ QsR) ->
  cenvs_split_multi E Qs (QsL ++ QsR).
Proof with auto.
  intros E Qs QsL. revert Qs.
  induction QsL; intros; inversion H; subst; simpl_env in *.
    apply cenv_split_multi_empty in H5.
      destruct H5 as [Qs2 Eq]. subst.
      rewrite_env (lcempty ++ Qs0 ++ Qs1).
      apply cenvs_split_multi_insert_empties...
    apply IHQsL in H2.
      simpl. apply cenvs_split_multi_cons with (Z := Z)...
        simpl_env. inversion H6. subst.
          rewrite_env (([a] ++ QsL) ++ [cempty] ++ QsR) in H0.
          apply cenv_split_multi_drop_empty in H0.
          simpl_env in H0. econstructor. eauto.
Qed.

Lemma cenvs_split_multi_ignore_empty: forall E Qs QsL QsR,
  cenvs_split_multi E Qs (QsL ++ QsR) ->
  cenvs_split_multi E Qs (QsL ++ [cempty] ++ QsR).
Proof with auto.
  intros E Qs QsL. revert Qs.
  induction QsL; intros.
    simpl. rewrite_env (lcempty ++ Qs). simpl_env in H.
      assert (wf_cenvs E QsR). apply wf_cenvs_split_multi in H...
      apply cenvs_split_multi_cons with (Z := None)...
      inversion H0; subst.
        apply wf_cenvs_csm with (Q := cempty) (Z := None)...
          constructor...
        simpl_env. apply wf_cenvs_csm with (Q := Q) (Z := None).
          apply cenv_split_multi_branch with
              (Q1 := cempty) (Q2 := Q) (X := None) (Y := Z)...
            apply cenv_split_proc_left_id...
              apply wf_cenv_split_multi in H1...
    simpl. simpl in H. inversion H. subst.
      apply cenvs_split_multi_cons with (Z := Z)...
        simpl_env. apply IHQsL...
        inversion H6. subst.
          rewrite_env ((a :: QsL) ++ QsR) in H0.
          apply cenv_split_multi_insert_empty in H0.
          simpl in H0. apply wf_cenvs_csm with (Q := Q) (Z := Z0)...
Qed.

Lemma cenvs_split_forget_empty: forall E Qs1 Qs2 QsL QsR,
  cenvs_split E Qs1 Qs2 (QsL ++ [cempty] ++ QsR) ->
  cenvs_split E Qs1 Qs2 (QsL ++ QsR).
Proof.
  intros. inversion H. subst.
  apply cenvs_split_multi_forget_empty in H0.
  econstructor; eauto.
Qed.

Lemma cenvs_split_ignore_empty: forall E Qs1 Qs2 QsL QsR,
  cenvs_split E Qs1 Qs2 (QsL ++ QsR) ->
  cenvs_split E Qs1 Qs2 (QsL ++ [cempty] ++ QsR).
Proof.
  intros. inversion H. subst.
  apply cenvs_split_multi_ignore_empty in H0.
  econstructor; eauto.
Qed.

Lemma cenvs_split_forget_empties: forall E Qs1 Qs2 QsL QsR QsE,
  cenvs_split E Qs1 Qs2 (QsL ++ QsE ++ QsR) ->
  lcempties QsE ->
  cenvs_split E Qs1 Qs2 (QsL ++ QsR).
Proof with auto.
  induction QsE; intros; simpl_env in *...
    inversion H0; subst. apply cenvs_split_forget_empty in H.
      apply IHQsE in H...
Qed.

Lemma cenvs_split_ignore_empties: forall E Qs1 Qs2 QsL QsR QsE,
  cenvs_split E Qs1 Qs2 (QsL ++ QsR) ->
  lcempties QsE ->
  cenvs_split E Qs1 Qs2 (QsL ++ QsE ++ QsR).
Proof with auto.
  intros. generalize dependent QsR. revert Qs1 Qs2 QsL.
  induction QsE; intros; simpl_env in *...
    inversion H0; subst. apply cenvs_split_ignore_empty in H.
      rewrite_env ((QsL ++ [cempty]) ++ QsR) in H.
      apply IHQsE in H... simpl_env in H...
Qed.

Lemma cenvs_split_unpadded: forall E Qs1 Qs2 Qs3 QsL QsR,
  cenvs_split E Qs1 Qs2 (QsL ++ Qs3 ++ QsR) ->
  lcempties QsL ->
  lcempties QsR ->
  cenvs_split E Qs1 Qs2 Qs3.
Proof with auto.
  intros. rewrite_env (lcempty ++ QsL ++ Qs3 ++ QsR) in H.
  apply cenvs_split_forget_empties in H...
  rewrite_env (Qs3 ++ QsR ++ lcempty) in H.
  apply cenvs_split_forget_empties in H...
  simpl_env in H...
Qed.

Lemma cenvs_split_padded: forall E Qs1 Qs2 Qs3 QsL QsR,
  cenvs_split E Qs1 Qs2 Qs3 ->
  lcempties QsL ->
  lcempties QsR ->
  cenvs_split E Qs1 Qs2 (QsL ++ Qs3 ++ QsR).
Proof with auto.
  intros. rewrite_env (lcempty ++ QsL ++ Qs3 ++ QsR).
  apply cenvs_split_ignore_empties...
  rewrite_env (Qs3 ++ QsR ++ lcempty).
  apply cenvs_split_ignore_empties...
  simpl_env...
Qed.

Lemma cenv_split_exp_unright: forall E Q1 Q2 Q3 X d T,
  cenv_split_exp E Q1 ([(X, cbind_proto d T)] ++ Q2)
                                   ([(X, cbind_proto d T)] ++ Q3) ->
  cenv_split_exp E Q1 Q2 Q3.
Proof.
  intros. inversion H; subst.
    apply dom_cenv_split_exp in H7. simpl_env in H7.
      fsetdec.
    auto.
Qed.

Lemma cenv_split_exp_unleft: forall E Q1 Q2 Q3 X d T,
  cenv_split_exp E ([(X, cbind_proto d T)] ++ Q1) Q2
                             ([(X, cbind_proto d T)] ++ Q3) ->
  cenv_split_exp E Q1 Q2 Q3.
Proof.
  intros. apply cenv_split_exp_commute.
  apply cenv_split_exp_commute in H.
  apply cenv_split_exp_unright in H. auto.
Qed.

Lemma doms_single: forall A L,
  doms A [L] [=] dom L.
Proof.
  intros. simpl. fsetdec.
Qed.

Lemma cenv_split_exp_mid_right': forall E X d T Q1L Q1R Q2L Q2R Q3 Q3L Q3R,
  cenv_split_exp E (Q1L ++ Q1R) (Q2L ++ [(X, cbind_proto d T)] ++ Q2R) Q3 ->
  cenv_split_exp E Q1L Q2L Q3L ->
  cenv_split_exp E Q1R Q2R Q3R ->
  Q3 = Q3L ++ [(X, cbind_proto d T)] ++ Q3R.
Proof with auto.
  intros. (* may require uniqueness of last argument to split *)
Admitted.

Lemma cenv_split_proc_shift_src_right: forall E X T Q1L Q1R Q2L Q2R Q3L Q3R,
  cenv_split_proc E (Q1L ++ [(X, cbind_proto cdir_src T)] ++ Q1R)
                              (Q2L ++ [(X, cbind_proto cdir_snk T)] ++ Q2R)
                              (Q3L ++ [(X, cbind_proto cdir_both T)] ++ Q3R)
                              (Some X) ->
  cenv_split_proc E (Q1L ++ Q1R)
                              (Q2L ++ [(X, cbind_proto cdir_both T)] ++ Q2R)
                              (Q3L ++ [(X, cbind_proto cdir_both T)] ++ Q3R)
                              None.
Proof with auto.
  intros. induction Q3L; simpl_env in *.
(*
      inversion H; subst.
    destruct Q1L; simpl_env in *.
      inversion H0.

  remember (Q1L ++ [(X, cbind_proto cdir_src T)] ++ Q1R) as Q1.
  remember (Q2L ++ [(X, cbind_proto cdir_snk T)] ++ Q2R) as Q2.
  remember (Q3L ++ [(X, cbind_proto cdir_both T)] ++ Q3R) as Q3.
*)
Admitted.

Lemma proc_preservation: forall Qs P1 P2 T,
  proc_typing Qs P1 T ->
  proc_red P1 P2 ->
  proc_typing Qs P2 T.
Proof with simpl_env; auto.
  intros Qs P1 P2 T PTyp PRed.
  generalize dependent T. revert Qs.
  (proc_red_cases (induction PRed) Case); intros.
  Case "red_ectx".
    inversion PTyp; subst. apply typing_exp with (Q := Q)...
      eapply plug_typing in H0; eauto.
      destruct H0 as [Dm [De [Qm [Qe [Te [CS [LS [Typ Etyp]]]]]]]].
      eapply preservation in Typ; eauto.
      eapply ectx_typing_plug; eauto.
  Case "red_done".
    inversion PTyp; subst...
      inversion H4; subst... pick fresh X. lapply (H9 X)...
        intros. inversion H0. inversion H5. subst.
        assert (wf_proto empty typ_answer)...
        apply cenvs_split_multi_single in H10.
        destruct H10 as [QsL [QsR [Eq [Emp1 Emp2]]]].
        rewrite Eq in H0. inversion H7; rewrite <- H10 in Eq; subst.
          rewrite_env ([(X, cbind_proto cdir_both typ_answer)] ++ cempty) in Eq.
            apply eq_padded_single in Eq...
            destruct Eq as [EqL [_ [_ EqR]]]. subst.
            apply proc_typing_sub_right with (Qs := Qs1) (QsE := QsL ++ QsR)...
              apply lcempties_append...
          rewrite_env ([(X, cbind_proto cdir_both typ_answer)] ++ cempty) in Eq.
            rewrite_env ([(X, cbind_proto cdir_both typ_answer)] ++ Q) in Eq.
            apply eq_padded_single in Eq...
            destruct Eq as [EqL [_ [Eq EqR]]]. subst.
            apply proc_typing_sub_right with (Qs := Qs1) (QsE := QsL ++ [cempty] ++ QsR)...
              apply lcempties_append... apply lcempties_append...
              repeat constructor.
      inversion H4; subst... pick fresh X. lapply (H9 X)...
        intros. inversion H0. inversion H5. subst.
        assert (wf_proto empty typ_answer)...
        apply cenvs_split_multi_single in H10.
        destruct H10 as [QsL [QsR [Eq [Emp1 Emp2]]]].
        rewrite Eq in H0. inversion H7; rewrite <- H10 in Eq; subst.
          rewrite_env ([(X, cbind_proto cdir_both typ_answer)] ++ cempty) in Eq.
            apply eq_padded_single in Eq...
            destruct Eq as [EqL [_ [_ EqR]]]. subst.
            apply proc_typing_sub_right with (Qs := Qs1) (QsE := QsL ++ QsR)...
              apply lcempties_append...
          rewrite_env ([(X, cbind_proto cdir_both typ_answer)] ++ cempty) in Eq.
            rewrite_env ([(X, cbind_proto cdir_both typ_answer)] ++ Q) in Eq.
            apply eq_padded_single in Eq...
            destruct Eq as [EqL [_ [Eq EqR]]]. subst.
            apply proc_typing_sub_right with (Qs := Qs1) (QsE := QsL ++ [cempty] ++ QsR)...
              apply lcempties_append... apply lcempties_append...
              repeat constructor.
  Case "red_par".
    inversion PTyp; subst.
      apply typing_parl with (Qs1 := Qs1) (Qs2 := Qs2)...
      apply typing_parr with (Qs1 := Qs1) (Qs2 := Qs2)...
  Case "red_new".
    inversion PTyp; subst.
    pick fresh X and apply typing_new...
      auto.
  Case "red_go".
    inversion PTyp; subst. eapply plug_typing in H1; eauto.
      destruct H1 as [Dm [De [Qm [Qe [Te [CS [LS [Typ Etyp]]]]]]]].
      inversion Typ. inversion LS. subst.
      lapply (cenvs_split_multi_single empty Q Qs)... intros.
      destruct H1 as [QsL [QsR [Eq [EmpL EmpR]]]]. subst.
      pick fresh X and apply typing_new...
        intros.
          instantiate (1 := fun X T1 =>
                          QsL ++ [[(X, cbind_proto cdir_both T1)] ++ Q] ++ QsR).
          constructor.
        simpl. simpl_env. apply typing_parl with
            (Qs1 := QsL ++ [[(X, cbind_proto cdir_src T)] ++ Qm] ++ QsR)
            (Qs2 := [[(X, cbind_proto cdir_snk T)] ++ Qe]).
          assert (exists f', plug M (open_ce_rec 0 (fchan X) (exp_src O T)) f').
            apply plug_exists...
          destruct H1 as [f' H1].
          rewrite <- (plug_open_ce_rec M (exp_src O T) f1 0 (fchan X) f')...
          simpl in H1.
          apply typing_exp with (Q := [(X, cbind_proto cdir_src T)] ++ Qm)...
            apply ectx_typing_plug with (D1 := lempty) (D2 := lempty) (Q1 := Qm)
                                                         (Q2 := [(X, cbind_proto cdir_src T)]) (M := M)
                                                         (e := exp_src X T) (T := Te)...
              apply typing_src...
                rewrite_env ([(X, cbind_proto cdir_src T)] ++ cempty).
                constructor...
              rewrite_env ([(X, cbind_proto cdir_src T)] ++ cempty).
                constructor... apply cenv_split_exp_right_id...
            apply proc_typing_regular in PTyp. intuition.
              apply wf_cenvs_strengthen_cenv_left with
                  (Q1 := Qm) (Q2 := Qe) (Z := None) in H3...
                apply wf_cenvs_cons_fresh with
                    (X := X) (d := cdir_src) (T := T) in H3...
                  apply cenvs_split_multi_unpad...
                    apply wf_cenvs_append_wf in H3. intuition.
                    apply wf_cenvs_append_wf in H10. intuition.
                apply cenv_split_exp_proc...
          apply typing_exp with (Q := [(X, cbind_proto cdir_snk T)] ++ Qe)...
            apply typing_app with (D1 := lempty) (D2 := lempty) (Q1 := Qe)
                                                (Q2 := [(X, cbind_proto cdir_snk T)]) (T1 := T); fold open_ce_rec...
              rewrite <- open_ce_rec_expr...
              simpl. apply typing_snk...
                rewrite_env ([(X, cbind_proto cdir_snk T)] ++ cempty).
                constructor...
              rewrite_env ([(X, cbind_proto cdir_snk T)] ++ cempty).
                apply cenv_split_exp_right... apply cenv_split_exp_right_id...
            apply cenvs_split_multi_id... apply wf_cenvs_from_single...
          apply cenvs_split_proc_insert_left with (Z := Some X)...
            apply proc_typing_regular in PTyp. intuition.
            apply wf_cenvs_cons_fresh with
                (X := X) (d := cdir_both) (T := T) in H1...
  Case "red_pass".
    inversion PTyp; subst. inversion H7. subst.
    pick fresh X and apply typing_new...
      instantiate (1 := FQs)... (* Let's see if this is right... *)
      lapply (H11 X)... intros.
        assert (exists f1'', plug M1 (open_ce_rec 0 X (exp_yield (exp_src O (typ_arrow T1 T2)))) f1'').
          apply plug_exists...
        assert (exists f2'', plug M2 (open_ce_rec 0 X (exp_app (exp_snk O (typ_arrow T1 T2)) v)) f2'').
          apply plug_exists...
        destruct H6 as [f1'' Plug1]. destruct H8 as [f2'' Plug2].
        rewrite (plug_open_ce_rec M1 (exp_yield (exp_src O (typ_arrow T1 T2))) f1 0 X f1'') in Plug1...
        rewrite (plug_open_ce_rec M2 (exp_app (exp_snk O (typ_arrow T1 T2)) v) f2 0 X f2'') in Plug2...
        clear f1'' f2''. simpl in Plug1.
        simpl in Plug2. rewrite <- (open_ce_rec_expr v X 0) in Plug2...
        inversion H5; inversion H13; inversion H15; subst.

          SCase "typing_parl".
            lapply (plug_typing empty lempty Q M1
                          (exp_yield (exp_src X (typ_arrow T1 T2)))
                          (open_ce_rec 0 X f1) T Plug1)...
            lapply (plug_typing empty lempty Q0 M2
                          (exp_app (exp_snk X (typ_arrow T1 T2)) v)
                          (open_ce_rec 0 X f2) typ_answer Plug2)... intros.
            destruct H8 as [Dm1 [De1 [Qm1 [Qe1 [Te1 [CS1 [LS1 [Typ1 ETyp1]]]]]]]].
            destruct H6 as [Dm2 [De2 [Qm2 [Qe2 [Te2 [CS2 [LS2 [Typ2 ETyp2]]]]]]]].
            inversion Typ1. inversion Typ2. inversion H18. inversion H25.
            inversion LS1. inversion LS2. subst. inversion H31. subst.
            clear H31 LS1 LS2 H54.
            assert (exists f1'', plug M1 (open_ce_rec 0 X (exp_mpair v (exp_src O Te2))) f1'').
              apply plug_exists...
            assert (exists f2'', plug M2 (open_ce_rec 0 X (exp_snk O Te2)) f2'').
              apply plug_exists...
            destruct H8 as [f1'' Plug1']. destruct H14 as [f2'' Plug2'].
            rewrite (plug_open_ce_rec M1 (exp_mpair v (exp_src O Te2)) f1' 0 X f1'') in Plug1'...
            rewrite (plug_open_ce_rec M2 (exp_snk O Te2) f2' 0 X f2'') in Plug2'...
            clear f1'' f2''.
            apply cenvs_split_multi_single in H21.
            apply cenvs_split_multi_single in H26.
            destruct H21 as [QsL1 [QsR1 [QEq1 [EmpL1 EmpR1]]]].
            destruct H26 as [QsL2 [QsR2 [QEq2 [EmpL2 EmpR2]]]]. subst.
            inversion H41. subst.
            destruct (cenv_split_exp_single_right empty Qm1
                             X cdir_src (typ_arrow T3 Te2) Q) as
                [QL1 [QR1 [Eq1 Eq2]]]... subst.
            destruct (cenv_split_exp_single_left empty X cdir_snk (typ_arrow T3 Te2)
                             Q3 Qe2) as
                [QL2 [QR2 [Eq1 Eq2]]]... subst.
            destruct (cenv_split_exp_focus_right empty Qm2
                             QL2 X  cdir_snk (typ_arrow T3 Te2) QR2 Q0) as
                [QL0 [QR0 [QL0' [QR0' [Eq1 [Eq2 [CS3 CS4]]]]]]]... subst.
            assert (exists QL', exists QR',
                          cenv_split_proc empty
                            (QL1 ++ [(X, cbind_proto cdir_src (typ_arrow T3 Te2))] ++ QR1)
                            (QL0' ++ [(X, cbind_proto cdir_snk (typ_arrow T3 Te2))] ++ QR0')
                            (QL' ++ [(X, cbind_proto cdir_both (typ_arrow T3 Te2))] ++ QR')
                            (Some X) /\
                          cenv_split_exp empty QL1 QL0' QL' /\
                          cenv_split_exp empty QR1 QR0' QR').
              apply cenvs_split_unpad_both in H17...
              apply cenvs_split_two_proc in H17.
              destruct H17 as [Q' [Z' CS']].
              destruct (cenv_split_proc_mid_srcsnk empty X (typ_arrow T3 Te2)
                               QL1 QR1 QL0' QR0' Q' Z') as
                  [Q3L [Q3R [EqQ [CSL [CSR EqZ]]]]]...
              subst. exists Q3L. exists Q3R...
            destruct H8 as [QL' [QR' [CS' [CSL CSR]]]].
            rewrite_env (cempty ++ [(X, cbind_proto cdir_snk (typ_arrow T3 Te2))] ++ cempty) in H33.
            rewrite_env (QL2 ++ [(X, cbind_proto cdir_snk (typ_arrow T3 Te2))] ++ QR2) in H33.
            apply cenv_split_exp_rebind_chan_left with (T2 := Te2) (d2 := cdir_src) in H33...
            apply cenv_split_exp_rebind_chan_right with (T2 := Te2) (d2 := cdir_snk) in CS2...
            apply cenv_split_proc_rebind_chan_both with (T2 := Te2) in CS'...
            destruct (cenv_split_exp_exists_disjoint empty (QL1 ++ QR1)
                             (QL2 ++ [(X, cbind_proto cdir_src Te2)] ++ QR2)) as
                [Qf1' CS]...
                apply disjoint_cenv_srcsnk_helper with
                    (Q := QL0 ++ QR0) (Q1L := QL2) (Q1R := QR2)
                    (d := cdir_snk) (d' := cdir_src) in CS'...
            apply typing_parl with
                (Qs1 := QsL1 ++ [Qf1'] ++ QsR1)
                (Qs2 := QsL2 ++ [QL0 ++ [(X, cbind_proto cdir_snk Te2)] ++ QR0] ++ QsR2)...
              apply typing_exp with (Q := Qf1')...
                apply ectx_typing_plug with (D1 := lempty) (D2 := lempty)
                    (M := M1) (T := typ_tensor T3 T2')
                    (e := open_ce_rec 0 X (exp_mpair v (exp_src O Te2)))
                    (Q1 := QL1 ++ QR1)
                    (Q2 := QL2 ++ [(X, cbind_proto cdir_src Te2)] ++ QR2)...
                  simpl. simpl_env.
                    apply typing_mpair with (D1 := lempty) (D2 := lempty)
                        (Q2 := [(X, cbind_proto cdir_src Te2)]) (Q1 := QL2 ++ QR2)...
                      rewrite <- open_ce_rec_expr...
                      apply wf_cenv_mid_notin_dom in H55. destruct H55 as [NiL NiR].
                        apply cenv_split_exp_insert_right...
                          apply cenv_split_exp_notin_dom with (X := X) in CS3...
                          apply cenv_split_exp_notin_dom with (X := X) in CS4...
                apply cenvs_split_multi_unpad...
                  apply wf_cenvs_from_single...
              assert (cenv_split_exp empty (QL0 ++ QR0)
                              [(X, cbind_proto cdir_snk Te2)]
                              (QL0 ++ [(X, cbind_proto cdir_snk Te2)] ++ QR0)).
                  apply cenv_split_exp_insert_right...
                    apply cenv_split_exp_notin_dom with (X := X) in CS3...
                      apply wf_cenv_split_exp in CS2.
                      apply uniq_from_wf_cenv in CS2.
                      destruct_uniq...
                    apply cenv_split_exp_notin_dom with (X := X) in CS4...
                      apply wf_cenv_split_exp in CS2.
                      apply uniq_from_wf_cenv in CS2.
                      destruct_uniq...
                apply typing_exp with (Q := QL0 ++ [(X, cbind_proto cdir_snk Te2)] ++ QR0)...  
                  apply ectx_typing_plug with (D1 := lempty) (D2 := lempty)
                      (M := M2) (T := Te2)
                      (e := open_ce_rec 0 X (exp_snk O Te2))
                      (Q1 := QL0 ++ QR0) (Q2 := [(X, cbind_proto cdir_snk Te2)])...
                    constructor...
                apply cenvs_split_multi_unpad...
                  apply wf_cenvs_from_single...
              apply cenvs_split_unpad_both in H17...
                apply cenvs_split_pad_both...
                inversion H9; subst.
                  destruct (cenv_split_exp_mid_right empty (QL1 ++ QR1)
                                 X cdir_src Te2 QL2 QR2 Qf1') as
                      [QL'' [QR'' Eq]]... subst.
                    rewrite_env (cempty ++
                                       [(X, cbind_proto cdir_both (typ_arrow T3 Te2))] ++
                                       cempty) in H17.
                    destruct (cenvs_split_single_srcsnk empty X (typ_arrow T3 Te2)
                                      QL1 QR1 QL0' QR0' cempty cempty QsL QsR)...
                    apply cenvs_split_unpadded in H17... simpl_env in H17.
                    apply cenvs_split_to_proc in H17. destruct H17 as [Z H17].
                    apply cenv_split_proc_mid_srcsnk in H17.
                    destruct H17 as [QEL [QER [EqE [CSEL [CSER Eq]]]]]. subst.
                    symmetry in EqE. apply app_eq_unit in EqE.
                    destruct EqE as [[Eq1 Eq2] | [Eq1 Eq2]]; subst.
                      inversion Eq2. subst.
                        inversion CSEL. inversion CSER. subst.
                        inversion CSL. inversion CSR. subst.
                        inversion CS3. inversion CS4. subst.
                        rewrite_env cempty in CS.
                        apply cenv_split_exp_empty_left in CS.
                        simpl_env in *. symmetry in CS. apply app_eq_unit in CS.
                        destruct CS as [[Eq3 Eq4] | [Eq3 Eq4]]; subst.
                          inversion Eq4. subst. simpl_env.
                            apply cenvs_split_padded...
                            apply cenvs_split_from_proc with (Z := Some X).
                            rewrite_env ([(X, cbind_proto cdir_src Te2)] ++ cempty).
                            rewrite_env ([(X, cbind_proto cdir_snk Te2)] ++ cempty).
                            rewrite_env ([(X, cbind_proto cdir_both Te2)] ++ cempty).
                            constructor...
                          discriminate Eq4.
                      discriminate Eq2.
                  rewrite_env (cempty ++
                                       [(X, cbind_proto cdir_both (typ_arrow T3 Te2))] ++
                                       Q) in H17.
                    destruct (cenvs_split_single_srcsnk empty X (typ_arrow T3 Te2)
                                      QL1 QR1 QL0' QR0' cempty Q QsL QsR)...
                    apply cenvs_split_unpadded in H17... simpl_env in H17.
                    apply cenvs_split_to_proc in H17. destruct H17 as [Z H17].
                    apply cenv_split_proc_mid_srcsnk in H17.
                    destruct H17 as [QLL [QRR [Eq' [CSLL [CSRR Eq]]]]]. subst.
                    assert (exists QL3, cenv_split_exp empty QL2 QL1 QL3 /\
                                                  cenv_split_exp empty QL0 QL3 QLL).
                      apply cenv_split_exp_assoc with (Q13 := QL0')...
                      apply cenv_split_exp_commute...
                    destruct H17 as [QL3 [CSL' CSL'']].
                    apply cenv_split_exp_commute in CSL'.
                    assert (exists QR3, cenv_split_exp empty QR2 QR1 QR3 /\
                                                  cenv_split_exp empty QR0 QR3 QRR).
                      apply cenv_split_exp_assoc with (Q13 := QR0')...
                      apply cenv_split_exp_commute...
                    destruct H17 as [QR3 [CSR' CSR'']].
                    apply cenv_split_exp_commute in CSR'.
                    assert (Qf1' = QL3 ++ [(X, cbind_proto cdir_src Te2)] ++ QR3).
                      apply cenv_split_exp_mid_right' with (E := empty)
                          (Q1L := QL1) (Q1R := QR1) (Q2L := QL2) (Q2R := QR2)...
                    subst.
                    destruct QLL; simpl in Eq'; inversion Eq'; subst.
                      inversion CSLL. subst.
                        inversion CSL. inversion CS3. subst.
                        inversion CSL'. subst.
                        simpl_env in *. inversion CS'. subst.
                        apply cenv_split_exp_unright in CS2.
                        apply cenvs_split_padded...
                        apply cenvs_split_from_proc with (Z := Some X).
                        apply cenv_split_proc_srcsnk...
                          apply cenv_split_exp_commute...
                          apply dom_cenv_split_exp in CSR.
                            apply dom_cenv_split_exp in CSRR.
                            rewrite CSRR. rewrite <- CSR...
                      simpl_env in *. absurd (X `notin` singleton X)...
                        rewrite doms_append in Fr.
                        rewrite doms_append in Fr.
                        rewrite doms_single in Fr.
                        simpl_env in Fr. clear - Fr. fsetdec.

          SCase "typing_parr".
            lapply (plug_typing empty lempty Q M1
                          (exp_yield (exp_src X (typ_arrow T1 T2)))
                          (open_ce_rec 0 X f1) typ_answer Plug1)...
            lapply (plug_typing empty lempty Q0 M2
                          (exp_app (exp_snk X (typ_arrow T1 T2)) v)
                          (open_ce_rec 0 X f2) T Plug2)... intros.
            destruct H8 as [Dm1 [De1 [Qm1 [Qe1 [Te1 [CS1 [LS1 [Typ1 ETyp1]]]]]]]].
            destruct H6 as [Dm2 [De2 [Qm2 [Qe2 [Te2 [CS2 [LS2 [Typ2 ETyp2]]]]]]]].
            inversion Typ1. inversion Typ2. inversion H18. inversion H25.
            inversion LS1. inversion LS2. subst. inversion H31. subst.
            clear H31 LS1 LS2 H54.
            assert (exists f1'', plug M1 (open_ce_rec 0 X (exp_mpair v (exp_src O Te2))) f1'').
              apply plug_exists...
            assert (exists f2'', plug M2 (open_ce_rec 0 X (exp_snk O Te2)) f2'').
              apply plug_exists...
            destruct H8 as [f1'' Plug1']. destruct H14 as [f2'' Plug2'].
            rewrite (plug_open_ce_rec M1 (exp_mpair v (exp_src O Te2)) f1' 0 X f1'') in Plug1'...
            rewrite (plug_open_ce_rec M2 (exp_snk O Te2) f2' 0 X f2'') in Plug2'...
            clear f1'' f2''.
            apply cenvs_split_multi_single in H21.
            apply cenvs_split_multi_single in H26.
            destruct H21 as [QsL1 [QsR1 [QEq1 [EmpL1 EmpR1]]]].
            destruct H26 as [QsL2 [QsR2 [QEq2 [EmpL2 EmpR2]]]]. subst.
            inversion H41. subst.
            destruct (cenv_split_exp_single_right empty Qm1
                             X cdir_src (typ_arrow T3 Te2) Q) as
                [QL1 [QR1 [Eq1 Eq2]]]... subst.
            destruct (cenv_split_exp_single_left empty X cdir_snk (typ_arrow T3 Te2)
                             Q3 Qe2) as
                [QL2 [QR2 [Eq1 Eq2]]]... subst.
            destruct (cenv_split_exp_focus_right empty Qm2
                             QL2 X  cdir_snk (typ_arrow T3 Te2) QR2 Q0) as
                [QL0 [QR0 [QL0' [QR0' [Eq1 [Eq2 [CS3 CS4]]]]]]]... subst.
            assert (exists QL', exists QR',
                          cenv_split_proc empty
                            (QL1 ++ [(X, cbind_proto cdir_src (typ_arrow T3 Te2))] ++ QR1)
                            (QL0' ++ [(X, cbind_proto cdir_snk (typ_arrow T3 Te2))] ++ QR0')
                            (QL' ++ [(X, cbind_proto cdir_both (typ_arrow T3 Te2))] ++ QR')
                            (Some X) /\
                          cenv_split_exp empty QL1 QL0' QL' /\
                          cenv_split_exp empty QR1 QR0' QR').
              apply cenvs_split_unpad_both in H17...
              apply cenvs_split_two_proc in H17.
              destruct H17 as [Q' [Z' CS']].
              destruct (cenv_split_proc_mid_srcsnk empty X (typ_arrow T3 Te2)
                               QL1 QR1 QL0' QR0' Q' Z') as
                  [Q3L [Q3R [EqQ [CSL [CSR EqZ]]]]]...
              subst. exists Q3L. exists Q3R...
            destruct H8 as [QL' [QR' [CS' [CSL CSR]]]].
            rewrite_env (cempty ++ [(X, cbind_proto cdir_snk (typ_arrow T3 Te2))] ++ cempty) in H33.
            rewrite_env (QL2 ++ [(X, cbind_proto cdir_snk (typ_arrow T3 Te2))] ++ QR2) in H33.
            apply cenv_split_exp_rebind_chan_left with (T2 := Te2) (d2 := cdir_src) in H33...
            apply cenv_split_exp_rebind_chan_right with (T2 := Te2) (d2 := cdir_snk) in CS2...
            apply cenv_split_proc_rebind_chan_both with (T2 := Te2) in CS'...
            destruct (cenv_split_exp_exists_disjoint empty (QL1 ++ QR1)
                             (QL2 ++ [(X, cbind_proto cdir_src Te2)] ++ QR2)) as
                [Qf1' CS]...
                apply disjoint_cenv_srcsnk_helper with
                    (Q := QL0 ++ QR0) (Q1L := QL2) (Q1R := QR2)
                    (d := cdir_snk) (d' := cdir_src) in CS'...
            apply typing_parr with
                (Qs1 := QsL1 ++ [Qf1'] ++ QsR1)
                (Qs2 := QsL2 ++ [QL0 ++ [(X, cbind_proto cdir_snk Te2)] ++ QR0] ++ QsR2)...
              apply typing_exp with (Q := Qf1')...
                apply ectx_typing_plug with (D1 := lempty) (D2 := lempty)
                    (M := M1) (T := typ_tensor T3 T2')
                    (e := open_ce_rec 0 X (exp_mpair v (exp_src O Te2)))
                    (Q1 := QL1 ++ QR1)
                    (Q2 := QL2 ++ [(X, cbind_proto cdir_src Te2)] ++ QR2)...
                  simpl. simpl_env.
                    apply typing_mpair with (D1 := lempty) (D2 := lempty)
                        (Q2 := [(X, cbind_proto cdir_src Te2)]) (Q1 := QL2 ++ QR2)...
                      rewrite <- open_ce_rec_expr...
                      apply wf_cenv_mid_notin_dom in H55. destruct H55 as [NiL NiR].
                        apply cenv_split_exp_insert_right...
                          apply cenv_split_exp_notin_dom with (X := X) in CS3...
                          apply cenv_split_exp_notin_dom with (X := X) in CS4...
                apply cenvs_split_multi_unpad...
                  apply wf_cenvs_from_single...
              assert (cenv_split_exp empty (QL0 ++ QR0)
                              [(X, cbind_proto cdir_snk Te2)]
                              (QL0 ++ [(X, cbind_proto cdir_snk Te2)] ++ QR0)).
                  apply cenv_split_exp_insert_right...
                    apply cenv_split_exp_notin_dom with (X := X) in CS3...
                      apply wf_cenv_split_exp in CS2.
                      apply uniq_from_wf_cenv in CS2.
                      destruct_uniq...
                    apply cenv_split_exp_notin_dom with (X := X) in CS4...
                      apply wf_cenv_split_exp in CS2.
                      apply uniq_from_wf_cenv in CS2.
                      destruct_uniq...
                apply typing_exp with (Q := QL0 ++ [(X, cbind_proto cdir_snk Te2)] ++ QR0)...  
                  apply ectx_typing_plug with (D1 := lempty) (D2 := lempty)
                      (M := M2) (T := Te2)
                      (e := open_ce_rec 0 X (exp_snk O Te2))
                      (Q1 := QL0 ++ QR0) (Q2 := [(X, cbind_proto cdir_snk Te2)])...
                    constructor...
                apply cenvs_split_multi_unpad...
                  apply wf_cenvs_from_single...
              apply cenvs_split_unpad_both in H17...
                apply cenvs_split_pad_both...
                inversion H9; subst.
                  destruct (cenv_split_exp_mid_right empty (QL1 ++ QR1)
                                 X cdir_src Te2 QL2 QR2 Qf1') as
                      [QL'' [QR'' Eq]]... subst.
                    rewrite_env (cempty ++
                                       [(X, cbind_proto cdir_both (typ_arrow T3 Te2))] ++
                                       cempty) in H17.
                    destruct (cenvs_split_single_srcsnk empty X (typ_arrow T3 Te2)
                                      QL1 QR1 QL0' QR0' cempty cempty QsL QsR)...
                    apply cenvs_split_unpadded in H17... simpl_env in H17.
                    apply cenvs_split_to_proc in H17. destruct H17 as [Z H17].
                    apply cenv_split_proc_mid_srcsnk in H17.
                    destruct H17 as [QEL [QER [EqE [CSEL [CSER Eq]]]]]. subst.
                    symmetry in EqE. apply app_eq_unit in EqE.
                    destruct EqE as [[Eq1 Eq2] | [Eq1 Eq2]]; subst.
                      inversion Eq2. subst.
                        inversion CSEL. inversion CSER. subst.
                        inversion CSL. inversion CSR. subst.
                        inversion CS3. inversion CS4. subst.
                        rewrite_env cempty in CS.
                        apply cenv_split_exp_empty_left in CS.
                        simpl_env in *. symmetry in CS. apply app_eq_unit in CS.
                        destruct CS as [[Eq3 Eq4] | [Eq3 Eq4]]; subst.
                          inversion Eq4. subst. simpl_env.
                            apply cenvs_split_padded...
                            apply cenvs_split_from_proc with (Z := Some X).
                            rewrite_env ([(X, cbind_proto cdir_src Te2)] ++ cempty).
                            rewrite_env ([(X, cbind_proto cdir_snk Te2)] ++ cempty).
                            rewrite_env ([(X, cbind_proto cdir_both Te2)] ++ cempty).
                            constructor...
                          discriminate Eq4.
                      discriminate Eq2.
                  rewrite_env (cempty ++
                                       [(X, cbind_proto cdir_both (typ_arrow T3 Te2))] ++
                                       Q) in H17.
                    destruct (cenvs_split_single_srcsnk empty X (typ_arrow T3 Te2)
                                      QL1 QR1 QL0' QR0' cempty Q QsL QsR)...
                    apply cenvs_split_unpadded in H17... simpl_env in H17.
                    apply cenvs_split_to_proc in H17. destruct H17 as [Z H17].
                    apply cenv_split_proc_mid_srcsnk in H17.
                    destruct H17 as [QLL [QRR [Eq' [CSLL [CSRR Eq]]]]]. subst.
                    assert (exists QL3, cenv_split_exp empty QL2 QL1 QL3 /\
                                                  cenv_split_exp empty QL0 QL3 QLL).
                      apply cenv_split_exp_assoc with (Q13 := QL0')...
                      apply cenv_split_exp_commute...
                    destruct H17 as [QL3 [CSL' CSL'']].
                    apply cenv_split_exp_commute in CSL'.
                    assert (exists QR3, cenv_split_exp empty QR2 QR1 QR3 /\
                                                  cenv_split_exp empty QR0 QR3 QRR).
                      apply cenv_split_exp_assoc with (Q13 := QR0')...
                      apply cenv_split_exp_commute...
                    destruct H17 as [QR3 [CSR' CSR'']].
                    apply cenv_split_exp_commute in CSR'.
                    assert (Qf1' = QL3 ++ [(X, cbind_proto cdir_src Te2)] ++ QR3).
                      apply cenv_split_exp_mid_right' with (E := empty)
                          (Q1L := QL1) (Q1R := QR1) (Q2L := QL2) (Q2R := QR2)...
                    subst.
                    destruct QLL; simpl in Eq'; inversion Eq'; subst.
                      inversion CSLL. subst.
                        inversion CSL. inversion CS3. subst.
                        inversion CSL'. subst.
                        simpl_env in *. inversion CS'. subst.
                        apply cenv_split_exp_unright in CS2.
                        apply cenvs_split_padded...
                        apply cenvs_split_from_proc with (Z := Some X).
                        apply cenv_split_proc_srcsnk...
                          apply cenv_split_exp_commute...
                          apply dom_cenv_split_exp in CSR.
                            apply dom_cenv_split_exp in CSRR.
                            rewrite CSRR. rewrite <- CSR...
                      simpl_env in *. absurd (X `notin` singleton X)...
                        rewrite doms_append in Fr.
                        rewrite doms_append in Fr.
                        rewrite doms_single in Fr.
                        simpl_env in Fr. clear - Fr. fsetdec.

  Case "red_left".
    inversion PTyp; subst. inversion H7. subst.
    pick fresh X and apply typing_new...
      instantiate (1 := FQs)...
      lapply (H11 X)... intros.
        assert (exists f1'', plug M1 (open_ce_rec 0 X (exp_yield (exp_src O (typ_with T1 T2)))) f1'').
          apply plug_exists...
        assert (exists f2'', plug M2 (open_ce_rec 0 X (exp_fst (exp_snk O (typ_with T1 T2)))) f2'').
          apply plug_exists...
        destruct H6 as [f1'' Plug1]. destruct H8 as [f2'' Plug2].
        rewrite (plug_open_ce_rec M1 (exp_yield (exp_src O (typ_with T1 T2))) f1 0 X f1'') in Plug1...
        rewrite (plug_open_ce_rec M2 (exp_fst (exp_snk O (typ_with T1 T2))) f2 0 X f2'') in Plug2...
        clear f1'' f2''. simpl in Plug1. simpl in Plug2.
        inversion H5; inversion H13; inversion H15; subst.

          SCase "typing_parl".
            lapply (plug_typing empty lempty Q M1
                          (exp_yield (exp_src X (typ_with T1 T2)))
                          (open_ce_rec 0 X f1) T Plug1)...
            lapply (plug_typing empty lempty Q0 M2
                          (exp_fst (exp_snk X (typ_with T1 T2)))
                          (open_ce_rec 0 X f2) typ_answer Plug2)... intros.
            destruct H8 as [Dm1 [De1 [Qm1 [Qe1 [Te1 [CS1 [LS1 [Typ1 ETyp1]]]]]]]].
            destruct H6 as [Dm2 [De2 [Qm2 [Qe2 [Te2 [CS2 [LS2 [Typ2 ETyp2]]]]]]]].
            inversion Typ1. inversion Typ2. inversion H18. inversion H28.
            inversion LS1. inversion LS2. subst.
            clear LS1 LS2 H50 H55.
            inversion H37. subst.
            assert (exists f1'', plug M1 (open_ce_rec 0 X (exp_inl (typ_plus T1' T2') (exp_src O Te2))) f1'').
              apply plug_exists...
            assert (exists f2'', plug M2 (open_ce_rec 0 X (exp_snk O Te2)) f2'').
              apply plug_exists...
            destruct H6 as [f1'' Plug1']. destruct H8 as [f2'' Plug2'].
            simpl in Plug1'. simpl in Plug2'.
            inversion H0. subst.
            apply dual_unique_src with (T2 := T1') in H23...
            apply dual_unique_src with (T2 := T2') in H25...
            subst. clear H37.
            rewrite (plug_open_ce_rec M1 (exp_inl (typ_plus T1' T2') (exp_src O Te2)) f1' 0 X f1'') in Plug1'...
            rewrite (plug_open_ce_rec M2 (exp_snk O Te2) f2' 0 X f2'') in Plug2'...
            clear f1'' f2''.
            apply cenvs_split_multi_single in H21.
            apply cenvs_split_multi_single in H26.
            destruct H21 as [QsL1 [QsR1 [QEq1 [EmpL1 EmpR1]]]].
            destruct H26 as [QsL2 [QsR2 [QEq2 [EmpL2 EmpR2]]]]. subst.
            destruct (cenv_split_exp_single_right empty Qm1
                             X cdir_src (typ_with Te2 T4) Q) as
                [QL1 [QR1 [Eq1 Eq2]]]... subst.
            destruct (cenv_split_exp_single_right empty Qm2 
                             X cdir_snk (typ_with Te2 T4) Q0) as
                [QL2 [QR2 [Eq1 Eq2]]]... subst.
            assert (exists QL', exists QR',
                          cenv_split_proc empty
                            (QL1 ++ [(X, cbind_proto cdir_src (typ_with Te2 T4))] ++ QR1)
                            (QL2 ++ [(X, cbind_proto cdir_snk (typ_with Te2 T4))] ++ QR2)
                            (QL' ++ [(X, cbind_proto cdir_both (typ_with Te2 T4))] ++ QR')
                            (Some X) /\
                          cenv_split_exp empty QL1 QL2 QL' /\
                          cenv_split_exp empty QR1 QR2 QR').
              apply cenvs_split_unpad_both in H17...
              apply cenvs_split_two_proc in H17.
              destruct H17 as [Q' [Z' CS']].
              destruct (cenv_split_proc_mid_srcsnk empty X (typ_with Te2 T4)
                               QL1 QR1 QL2 QR2 Q' Z') as
                  [Q3L [Q3R [EqQ [CSL [CSR EqZ]]]]]...
              subst. exists Q3L. exists Q3R...
            destruct H6 as [QL' [QR' [CS' [CSL CSR]]]].
            rewrite_env (cempty ++ [(X, cbind_proto cdir_src (typ_with Te2 T4))] ++ cempty) in CS1.
            rewrite_env (cempty ++ [(X, cbind_proto cdir_snk (typ_with Te2 T4))] ++ cempty) in CS2.
            rewrite_env (QL1 ++ [(X, cbind_proto cdir_src (typ_with Te2 T4))] ++ QR1) in CS1.
            rewrite_env (QL2 ++ [(X, cbind_proto cdir_snk (typ_with Te2 T4))] ++ QR2) in CS2.
            apply cenv_split_exp_rebind_chan_right with (T2 := Te2) (d2 := cdir_src) in CS1...
            apply cenv_split_exp_rebind_chan_right with (T2 := Te2) (d2 := cdir_snk) in CS2...
            apply cenv_split_proc_rebind_chan_both with (T2 := Te2) in CS'...
            apply typing_parl with
                (Qs1 := QsL1 ++ [QL1 ++ [(X, cbind_proto cdir_src Te2)] ++ QR1] ++ QsR1)
                (Qs2 := QsL2 ++ [QL2 ++ [(X, cbind_proto cdir_snk Te2)] ++ QR2] ++ QsR2)...
              apply typing_exp with (Q := QL1 ++ [(X, cbind_proto cdir_src Te2)] ++ QR1)...
                apply ectx_typing_plug with (D1 := lempty) (D2 := lempty)
                    (M := M1) (T := typ_plus T1' T2')
                    (e := open_ce_rec 0 X (exp_inl (typ_plus T1' T2') (exp_src O Te2)))
                    (Q1 := QL1 ++ QR1)
                    (Q2 := [(X, cbind_proto cdir_src Te2)])...
                  simpl. constructor...
                apply cenvs_split_multi_unpad...
                  apply wf_cenvs_from_single...
              apply typing_exp with (Q := QL2 ++ [(X, cbind_proto cdir_snk Te2)] ++ QR2)...
                apply ectx_typing_plug with (D1 := lempty) (D2 := lempty)
                    (M := M2) (T := Te2)
                    (e := open_ce_rec 0 X (exp_snk O Te2))
                    (Q1 := QL2 ++ QR2) (Q2 := [(X, cbind_proto cdir_snk Te2)])...
                  constructor...
                apply cenvs_split_multi_unpad...
                  apply wf_cenvs_from_single...
              apply cenvs_split_unpad_both in H17...
                apply cenvs_split_pad_both...
                inversion H9; subst.
                  rewrite_env (cempty ++
                                       [(X, cbind_proto cdir_both (typ_with Te2 T4))] ++
                                       cempty) in H17.
                    destruct (cenvs_split_single_srcsnk empty X (typ_with Te2 T4)
                                      QL1 QR1 QL2 QR2 cempty cempty QsL QsR)...
                    apply cenvs_split_unpadded in H17... simpl_env in H17.
                    apply cenvs_split_to_proc in H17. destruct H17 as [Z H17].
                    apply cenv_split_proc_mid_srcsnk in H17.
                    destruct H17 as [QEL [QER [EqE [CSEL [CSER Eq]]]]]. subst.
                    symmetry in EqE. apply app_eq_unit in EqE.
                    destruct EqE as [[Eq1 Eq2] | [Eq1 Eq2]]; subst.
                      inversion Eq2. subst.
                        inversion CSEL. inversion CSER. subst.
                        inversion CSL. inversion CSR. subst.
                        simpl_env in *. apply cenvs_split_padded...
                        apply cenvs_split_from_proc with (Z := Some X).
                        rewrite_env ([(X, cbind_proto cdir_src Te2)] ++ cempty).
                        rewrite_env ([(X, cbind_proto cdir_snk Te2)] ++ cempty).
                        rewrite_env ([(X, cbind_proto cdir_both Te2)] ++ cempty).
                        constructor...
                      discriminate Eq2.
                  rewrite_env (cempty ++
                                       [(X, cbind_proto cdir_both (typ_with Te2 T4))] ++
                                       Q) in H17.
                    destruct (cenvs_split_single_srcsnk empty X (typ_with Te2 T4)
                                      QL1 QR1 QL2 QR2 cempty Q QsL QsR)...
                    apply cenvs_split_unpadded in H17... simpl_env in H17.
                    apply cenvs_split_to_proc in H17. destruct H17 as [Z H17].
                    apply cenv_split_proc_mid_srcsnk in H17.
                    destruct H17 as [QLL [QRR [Eq' [CSLL [CSRR Eq]]]]]. subst.
                    destruct QLL; simpl in Eq'; inversion Eq'; subst.
                      inversion CSLL. subst.
                        inversion CSL. subst.
                        simpl_env in *. inversion CS'. subst.
                        apply cenvs_split_padded...
                        apply cenvs_split_from_proc with (Z := Some X).
                        apply cenv_split_proc_srcsnk...
                          apply dom_cenv_split_exp in CSR.
                            apply dom_cenv_split_exp in CSRR.
                            rewrite CSRR. rewrite <- CSR...
                      simpl_env in *. absurd (X `notin` singleton X)...
                        rewrite doms_append in Fr.
                        rewrite doms_append in Fr.
                        rewrite doms_single in Fr.
                        simpl_env in Fr. clear - Fr. fsetdec.

          SCase "typing_parr".
            lapply (plug_typing empty lempty Q M1
                          (exp_yield (exp_src X (typ_with T1 T2)))
                          (open_ce_rec 0 X f1) typ_answer Plug1)...
            lapply (plug_typing empty lempty Q0 M2
                          (exp_fst (exp_snk X (typ_with T1 T2)))
                          (open_ce_rec 0 X f2) T Plug2)... intros.
            destruct H8 as [Dm1 [De1 [Qm1 [Qe1 [Te1 [CS1 [LS1 [Typ1 ETyp1]]]]]]]].
            destruct H6 as [Dm2 [De2 [Qm2 [Qe2 [Te2 [CS2 [LS2 [Typ2 ETyp2]]]]]]]].
            inversion Typ1. inversion Typ2. inversion H18. inversion H28.
            inversion LS1. inversion LS2. subst.
            clear LS1 LS2 H50 H55.
            inversion H37. subst.
            assert (exists f1'', plug M1 (open_ce_rec 0 X (exp_inl (typ_plus T1' T2') (exp_src O Te2))) f1'').
              apply plug_exists...
            assert (exists f2'', plug M2 (open_ce_rec 0 X (exp_snk O Te2)) f2'').
              apply plug_exists...
            destruct H6 as [f1'' Plug1']. destruct H8 as [f2'' Plug2'].
            simpl in Plug1'. simpl in Plug2'.
            inversion H0. subst.
            apply dual_unique_src with (T2 := T1') in H23...
            apply dual_unique_src with (T2 := T2') in H25...
            subst. clear H37.
            rewrite (plug_open_ce_rec M1 (exp_inl (typ_plus T1' T2') (exp_src O Te2)) f1' 0 X f1'') in Plug1'...
            rewrite (plug_open_ce_rec M2 (exp_snk O Te2) f2' 0 X f2'') in Plug2'...
            clear f1'' f2''.
            apply cenvs_split_multi_single in H21.
            apply cenvs_split_multi_single in H26.
            destruct H21 as [QsL1 [QsR1 [QEq1 [EmpL1 EmpR1]]]].
            destruct H26 as [QsL2 [QsR2 [QEq2 [EmpL2 EmpR2]]]]. subst.
            destruct (cenv_split_exp_single_right empty Qm1
                             X cdir_src (typ_with Te2 T4) Q) as
                [QL1 [QR1 [Eq1 Eq2]]]... subst.
            destruct (cenv_split_exp_single_right empty Qm2 
                             X cdir_snk (typ_with Te2 T4) Q0) as
                [QL2 [QR2 [Eq1 Eq2]]]... subst.
            assert (exists QL', exists QR',
                          cenv_split_proc empty
                            (QL1 ++ [(X, cbind_proto cdir_src (typ_with Te2 T4))] ++ QR1)
                            (QL2 ++ [(X, cbind_proto cdir_snk (typ_with Te2 T4))] ++ QR2)
                            (QL' ++ [(X, cbind_proto cdir_both (typ_with Te2 T4))] ++ QR')
                            (Some X) /\
                          cenv_split_exp empty QL1 QL2 QL' /\
                          cenv_split_exp empty QR1 QR2 QR').
              apply cenvs_split_unpad_both in H17...
              apply cenvs_split_two_proc in H17.
              destruct H17 as [Q' [Z' CS']].
              destruct (cenv_split_proc_mid_srcsnk empty X (typ_with Te2 T4)
                               QL1 QR1 QL2 QR2 Q' Z') as
                  [Q3L [Q3R [EqQ [CSL [CSR EqZ]]]]]...
              subst. exists Q3L. exists Q3R...
            destruct H6 as [QL' [QR' [CS' [CSL CSR]]]].
            rewrite_env (cempty ++ [(X, cbind_proto cdir_src (typ_with Te2 T4))] ++ cempty) in CS1.
            rewrite_env (cempty ++ [(X, cbind_proto cdir_snk (typ_with Te2 T4))] ++ cempty) in CS2.
            rewrite_env (QL1 ++ [(X, cbind_proto cdir_src (typ_with Te2 T4))] ++ QR1) in CS1.
            rewrite_env (QL2 ++ [(X, cbind_proto cdir_snk (typ_with Te2 T4))] ++ QR2) in CS2.
            apply cenv_split_exp_rebind_chan_right with (T2 := Te2) (d2 := cdir_src) in CS1...
            apply cenv_split_exp_rebind_chan_right with (T2 := Te2) (d2 := cdir_snk) in CS2...
            apply cenv_split_proc_rebind_chan_both with (T2 := Te2) in CS'...
            (*destruct (cenv_split_exp_exists_disjoint empty (QL1 ++ QR1)
                             (QL2 ++ [(X, cbind_proto cdir_src Te2)] ++ QR2)) as
                [Qf1' CS]...
                apply disjoint_cenv_srcsnk_helper with
                    (Q := QL0 ++ QR0) (Q1L := QL2) (Q1R := QR2)
                    (d := cdir_snk) (d' := cdir_src) in CS'...*)
            apply typing_parr with
                (Qs1 := QsL1 ++ [QL1 ++ [(X, cbind_proto cdir_src Te2)] ++ QR1] ++ QsR1)
                (Qs2 := QsL2 ++ [QL2 ++ [(X, cbind_proto cdir_snk Te2)] ++ QR2] ++ QsR2)...
              apply typing_exp with (Q := QL1 ++ [(X, cbind_proto cdir_src Te2)] ++ QR1)...
                apply ectx_typing_plug with (D1 := lempty) (D2 := lempty)
                    (M := M1) (T := typ_plus T1' T2')
                    (e := open_ce_rec 0 X (exp_inl (typ_plus T1' T2') (exp_src O Te2)))
                    (Q1 := QL1 ++ QR1)
                    (Q2 := [(X, cbind_proto cdir_src Te2)])...
                  simpl. constructor...
                apply cenvs_split_multi_unpad...
                  apply wf_cenvs_from_single...
              apply typing_exp with (Q := QL2 ++ [(X, cbind_proto cdir_snk Te2)] ++ QR2)...
                apply ectx_typing_plug with (D1 := lempty) (D2 := lempty)
                    (M := M2) (T := Te2)
                    (e := open_ce_rec 0 X (exp_snk O Te2))
                    (Q1 := QL2 ++ QR2) (Q2 := [(X, cbind_proto cdir_snk Te2)])...
                  constructor...
                apply cenvs_split_multi_unpad...
                  apply wf_cenvs_from_single...
              apply cenvs_split_unpad_both in H17...
                apply cenvs_split_pad_both...
                inversion H9; subst.
                  (*destruct (cenv_split_exp_mid_right empty (QL1 ++ QR1)
                                 X cdir_src Te2 QL2 QR2 Qf1') as
                      [QL'' [QR'' Eq]]... subst.*)
                  rewrite_env (cempty ++
                                       [(X, cbind_proto cdir_both (typ_with Te2 T4))] ++
                                       cempty) in H17.
                    destruct (cenvs_split_single_srcsnk empty X (typ_with Te2 T4)
                                      QL1 QR1 QL2 QR2 cempty cempty QsL QsR)...
                    apply cenvs_split_unpadded in H17... simpl_env in H17.
                    apply cenvs_split_to_proc in H17. destruct H17 as [Z H17].
                    apply cenv_split_proc_mid_srcsnk in H17.
                    destruct H17 as [QEL [QER [EqE [CSEL [CSER Eq]]]]]. subst.
                    symmetry in EqE. apply app_eq_unit in EqE.
                    destruct EqE as [[Eq1 Eq2] | [Eq1 Eq2]]; subst.
                      inversion Eq2. subst.
                        inversion CSEL. inversion CSER. subst.
                        inversion CSL. inversion CSR. subst.
                        simpl_env in *. apply cenvs_split_padded...
                        apply cenvs_split_from_proc with (Z := Some X).
                        rewrite_env ([(X, cbind_proto cdir_src Te2)] ++ cempty).
                        rewrite_env ([(X, cbind_proto cdir_snk Te2)] ++ cempty).
                        rewrite_env ([(X, cbind_proto cdir_both Te2)] ++ cempty).
                        constructor...
                      discriminate Eq2.
                  rewrite_env (cempty ++
                                       [(X, cbind_proto cdir_both (typ_with Te2 T4))] ++
                                       Q) in H17.
                    destruct (cenvs_split_single_srcsnk empty X (typ_with Te2 T4)
                                      QL1 QR1 QL2 QR2 cempty Q QsL QsR)...
                    apply cenvs_split_unpadded in H17... simpl_env in H17.
                    apply cenvs_split_to_proc in H17. destruct H17 as [Z H17].
                    apply cenv_split_proc_mid_srcsnk in H17.
                    destruct H17 as [QLL [QRR [Eq' [CSLL [CSRR Eq]]]]]. subst.
                    destruct QLL; simpl in Eq'; inversion Eq'; subst.
                      inversion CSLL. subst.
                        inversion CSL. subst.
                        simpl_env in *. inversion CS'. subst.
                        apply cenvs_split_padded...
                        apply cenvs_split_from_proc with (Z := Some X).
                        apply cenv_split_proc_srcsnk...
                          apply dom_cenv_split_exp in CSR.
                            apply dom_cenv_split_exp in CSRR.
                            rewrite CSRR. rewrite <- CSR...
                      simpl_env in *. absurd (X `notin` singleton X)...
                        rewrite doms_append in Fr.
                        rewrite doms_append in Fr.
                        rewrite doms_single in Fr.
                        simpl_env in Fr. clear - Fr. fsetdec.

  Case "red_right".
    inversion PTyp; subst. inversion H7. subst.
    pick fresh X and apply typing_new...
      instantiate (1 := FQs)...
      lapply (H11 X)... intros.
        assert (exists f1'', plug M1 (open_ce_rec 0 X (exp_yield (exp_src O (typ_with T1 T2)))) f1'').
          apply plug_exists...
        assert (exists f2'', plug M2 (open_ce_rec 0 X (exp_snd (exp_snk O (typ_with T1 T2)))) f2'').
          apply plug_exists...
        destruct H6 as [f1'' Plug1]. destruct H8 as [f2'' Plug2].
        rewrite (plug_open_ce_rec M1 (exp_yield (exp_src O (typ_with T1 T2))) f1 0 X f1'') in Plug1...
        rewrite (plug_open_ce_rec M2 (exp_snd (exp_snk O (typ_with T1 T2))) f2 0 X f2'') in Plug2...
        clear f1'' f2''. simpl in Plug1. simpl in Plug2.
        inversion H5; inversion H13; inversion H15; subst.

          SCase "typing_parl".
            lapply (plug_typing empty lempty Q M1
                          (exp_yield (exp_src X (typ_with T1 T2)))
                          (open_ce_rec 0 X f1) T Plug1)...
            lapply (plug_typing empty lempty Q0 M2
                          (exp_snd (exp_snk X (typ_with T1 T2)))
                          (open_ce_rec 0 X f2) typ_answer Plug2)... intros.
            destruct H8 as [Dm1 [De1 [Qm1 [Qe1 [Te1 [CS1 [LS1 [Typ1 ETyp1]]]]]]]].
            destruct H6 as [Dm2 [De2 [Qm2 [Qe2 [Te2 [CS2 [LS2 [Typ2 ETyp2]]]]]]]].
            inversion Typ1. inversion Typ2. inversion H18. inversion H28.
            inversion LS1. inversion LS2. subst.
            clear LS1 LS2 H50 H55.
            inversion H37. subst.
            assert (exists f1'', plug M1 (open_ce_rec 0 X (exp_inr (typ_plus T1' T2') (exp_src O Te2))) f1'').
              apply plug_exists...
            assert (exists f2'', plug M2 (open_ce_rec 0 X (exp_snk O Te2)) f2'').
              apply plug_exists...
            destruct H6 as [f1'' Plug1']. destruct H8 as [f2'' Plug2'].
            simpl in Plug1'. simpl in Plug2'.
            inversion H0. subst.
            apply dual_unique_src with (T2 := T1') in H23...
            apply dual_unique_src with (T2 := T2') in H25...
            subst. clear H37.
            rewrite (plug_open_ce_rec M1 (exp_inr (typ_plus T1' T2') (exp_src O Te2)) f1' 0 X f1'') in Plug1'...
            rewrite (plug_open_ce_rec M2 (exp_snk O Te2) f2' 0 X f2'') in Plug2'...
            clear f1'' f2''.
            apply cenvs_split_multi_single in H21.
            apply cenvs_split_multi_single in H26.
            destruct H21 as [QsL1 [QsR1 [QEq1 [EmpL1 EmpR1]]]].
            destruct H26 as [QsL2 [QsR2 [QEq2 [EmpL2 EmpR2]]]]. subst.
            destruct (cenv_split_exp_single_right empty Qm1
                             X cdir_src (typ_with T3 Te2) Q) as
                [QL1 [QR1 [Eq1 Eq2]]]... subst.
            destruct (cenv_split_exp_single_right empty Qm2 
                             X cdir_snk (typ_with T3 Te2) Q0) as
                [QL2 [QR2 [Eq1 Eq2]]]... subst.
            assert (exists QL', exists QR',
                          cenv_split_proc empty
                            (QL1 ++ [(X, cbind_proto cdir_src (typ_with T3 Te2))] ++ QR1)
                            (QL2 ++ [(X, cbind_proto cdir_snk (typ_with T3 Te2))] ++ QR2)
                            (QL' ++ [(X, cbind_proto cdir_both (typ_with T3 Te2))] ++ QR')
                            (Some X) /\
                          cenv_split_exp empty QL1 QL2 QL' /\
                          cenv_split_exp empty QR1 QR2 QR').
              apply cenvs_split_unpad_both in H17...
              apply cenvs_split_two_proc in H17.
              destruct H17 as [Q' [Z' CS']].
              destruct (cenv_split_proc_mid_srcsnk empty X (typ_with T3 Te2)
                               QL1 QR1 QL2 QR2 Q' Z') as
                  [Q3L [Q3R [EqQ [CSL [CSR EqZ]]]]]...
              subst. exists Q3L. exists Q3R...
            destruct H6 as [QL' [QR' [CS' [CSL CSR]]]].
            rewrite_env (cempty ++ [(X, cbind_proto cdir_src (typ_with T3 Te2))] ++ cempty) in CS1.
            rewrite_env (cempty ++ [(X, cbind_proto cdir_snk (typ_with T3 Te2))] ++ cempty) in CS2.
            rewrite_env (QL1 ++ [(X, cbind_proto cdir_src (typ_with T3 Te2))] ++ QR1) in CS1.
            rewrite_env (QL2 ++ [(X, cbind_proto cdir_snk (typ_with T3 Te2))] ++ QR2) in CS2.
            apply cenv_split_exp_rebind_chan_right with (T2 := Te2) (d2 := cdir_src) in CS1...
            apply cenv_split_exp_rebind_chan_right with (T2 := Te2) (d2 := cdir_snk) in CS2...
            apply cenv_split_proc_rebind_chan_both with (T2 := Te2) in CS'...
            apply typing_parl with
                (Qs1 := QsL1 ++ [QL1 ++ [(X, cbind_proto cdir_src Te2)] ++ QR1] ++ QsR1)
                (Qs2 := QsL2 ++ [QL2 ++ [(X, cbind_proto cdir_snk Te2)] ++ QR2] ++ QsR2)...
              apply typing_exp with (Q := QL1 ++ [(X, cbind_proto cdir_src Te2)] ++ QR1)...
                apply ectx_typing_plug with (D1 := lempty) (D2 := lempty)
                    (M := M1) (T := typ_plus T1' T2')
                    (e := open_ce_rec 0 X (exp_inr (typ_plus T1' T2') (exp_src O Te2)))
                    (Q1 := QL1 ++ QR1)
                    (Q2 := [(X, cbind_proto cdir_src Te2)])...
                  simpl. constructor...
                apply cenvs_split_multi_unpad...
                  apply wf_cenvs_from_single...
              apply typing_exp with (Q := QL2 ++ [(X, cbind_proto cdir_snk Te2)] ++ QR2)...
                apply ectx_typing_plug with (D1 := lempty) (D2 := lempty)
                    (M := M2) (T := Te2)
                    (e := open_ce_rec 0 X (exp_snk O Te2))
                    (Q1 := QL2 ++ QR2) (Q2 := [(X, cbind_proto cdir_snk Te2)])...
                  constructor...
                apply cenvs_split_multi_unpad...
                  apply wf_cenvs_from_single...
              apply cenvs_split_unpad_both in H17...
                apply cenvs_split_pad_both...
                inversion H9; subst.
                  rewrite_env (cempty ++
                                       [(X, cbind_proto cdir_both (typ_with T3 Te2))] ++
                                       cempty) in H17.
                    destruct (cenvs_split_single_srcsnk empty X (typ_with T3 Te2)
                                      QL1 QR1 QL2 QR2 cempty cempty QsL QsR)...
                    apply cenvs_split_unpadded in H17... simpl_env in H17.
                    apply cenvs_split_to_proc in H17. destruct H17 as [Z H17].
                    apply cenv_split_proc_mid_srcsnk in H17.
                    destruct H17 as [QEL [QER [EqE [CSEL [CSER Eq]]]]]. subst.
                    symmetry in EqE. apply app_eq_unit in EqE.
                    destruct EqE as [[Eq1 Eq2] | [Eq1 Eq2]]; subst.
                      inversion Eq2. subst.
                        inversion CSEL. inversion CSER. subst.
                        inversion CSL. inversion CSR. subst.
                        simpl_env in *. apply cenvs_split_padded...
                        apply cenvs_split_from_proc with (Z := Some X).
                        rewrite_env ([(X, cbind_proto cdir_src Te2)] ++ cempty).
                        rewrite_env ([(X, cbind_proto cdir_snk Te2)] ++ cempty).
                        rewrite_env ([(X, cbind_proto cdir_both Te2)] ++ cempty).
                        constructor...
                      discriminate Eq2.
                  rewrite_env (cempty ++
                                       [(X, cbind_proto cdir_both (typ_with T3 Te2))] ++
                                       Q) in H17.
                    destruct (cenvs_split_single_srcsnk empty X (typ_with T3 Te2)
                                      QL1 QR1 QL2 QR2 cempty Q QsL QsR)...
                    apply cenvs_split_unpadded in H17... simpl_env in H17.
                    apply cenvs_split_to_proc in H17. destruct H17 as [Z H17].
                    apply cenv_split_proc_mid_srcsnk in H17.
                    destruct H17 as [QLL [QRR [Eq' [CSLL [CSRR Eq]]]]]. subst.
                    destruct QLL; simpl in Eq'; inversion Eq'; subst.
                      inversion CSLL. subst.
                        inversion CSL. subst.
                        simpl_env in *. inversion CS'. subst.
                        apply cenvs_split_padded...
                        apply cenvs_split_from_proc with (Z := Some X).
                        apply cenv_split_proc_srcsnk...
                          apply dom_cenv_split_exp in CSR.
                            apply dom_cenv_split_exp in CSRR.
                            rewrite CSRR. rewrite <- CSR...
                      simpl_env in *. absurd (X `notin` singleton X)...
                        rewrite doms_append in Fr.
                        rewrite doms_append in Fr.
                        rewrite doms_single in Fr.
                        simpl_env in Fr. clear - Fr. fsetdec.

          SCase "typing_parr".
            lapply (plug_typing empty lempty Q M1
                          (exp_yield (exp_src X (typ_with T1 T2)))
                          (open_ce_rec 0 X f1) typ_answer Plug1)...
            lapply (plug_typing empty lempty Q0 M2
                          (exp_snd (exp_snk X (typ_with T1 T2)))
                          (open_ce_rec 0 X f2) T Plug2)... intros.
            destruct H8 as [Dm1 [De1 [Qm1 [Qe1 [Te1 [CS1 [LS1 [Typ1 ETyp1]]]]]]]].
            destruct H6 as [Dm2 [De2 [Qm2 [Qe2 [Te2 [CS2 [LS2 [Typ2 ETyp2]]]]]]]].
            inversion Typ1. inversion Typ2. inversion H18. inversion H28.
            inversion LS1. inversion LS2. subst.
            clear LS1 LS2 H50 H55.
            inversion H37. subst.
            assert (exists f1'', plug M1 (open_ce_rec 0 X (exp_inr (typ_plus T1' T2') (exp_src O Te2))) f1'').
              apply plug_exists...
            assert (exists f2'', plug M2 (open_ce_rec 0 X (exp_snk O Te2)) f2'').
              apply plug_exists...
            destruct H6 as [f1'' Plug1']. destruct H8 as [f2'' Plug2'].
            simpl in Plug1'. simpl in Plug2'.
            inversion H0. subst.
            apply dual_unique_src with (T2 := T1') in H23...
            apply dual_unique_src with (T2 := T2') in H25...
            subst. clear H37.
            rewrite (plug_open_ce_rec M1 (exp_inr (typ_plus T1' T2') (exp_src O Te2)) f1' 0 X f1'') in Plug1'...
            rewrite (plug_open_ce_rec M2 (exp_snk O Te2) f2' 0 X f2'') in Plug2'...
            clear f1'' f2''.
            apply cenvs_split_multi_single in H21.
            apply cenvs_split_multi_single in H26.
            destruct H21 as [QsL1 [QsR1 [QEq1 [EmpL1 EmpR1]]]].
            destruct H26 as [QsL2 [QsR2 [QEq2 [EmpL2 EmpR2]]]]. subst.
            destruct (cenv_split_exp_single_right empty Qm1
                             X cdir_src (typ_with T3 Te2) Q) as
                [QL1 [QR1 [Eq1 Eq2]]]... subst.
            destruct (cenv_split_exp_single_right empty Qm2 
                             X cdir_snk (typ_with T3 Te2) Q0) as
                [QL2 [QR2 [Eq1 Eq2]]]... subst.
            assert (exists QL', exists QR',
                          cenv_split_proc empty
                            (QL1 ++ [(X, cbind_proto cdir_src (typ_with T3 Te2))] ++ QR1)
                            (QL2 ++ [(X, cbind_proto cdir_snk (typ_with T3 Te2))] ++ QR2)
                            (QL' ++ [(X, cbind_proto cdir_both (typ_with T3 Te2))] ++ QR')
                            (Some X) /\
                          cenv_split_exp empty QL1 QL2 QL' /\
                          cenv_split_exp empty QR1 QR2 QR').
              apply cenvs_split_unpad_both in H17...
              apply cenvs_split_two_proc in H17.
              destruct H17 as [Q' [Z' CS']].
              destruct (cenv_split_proc_mid_srcsnk empty X (typ_with T3 Te2)
                               QL1 QR1 QL2 QR2 Q' Z') as
                  [Q3L [Q3R [EqQ [CSL [CSR EqZ]]]]]...
              subst. exists Q3L. exists Q3R...
            destruct H6 as [QL' [QR' [CS' [CSL CSR]]]].
            rewrite_env (cempty ++ [(X, cbind_proto cdir_src (typ_with T3 Te2))] ++ cempty) in CS1.
            rewrite_env (cempty ++ [(X, cbind_proto cdir_snk (typ_with T3 Te2))] ++ cempty) in CS2.
            rewrite_env (QL1 ++ [(X, cbind_proto cdir_src (typ_with T3 Te2))] ++ QR1) in CS1.
            rewrite_env (QL2 ++ [(X, cbind_proto cdir_snk (typ_with T3 Te2))] ++ QR2) in CS2.
            apply cenv_split_exp_rebind_chan_right with (T2 := Te2) (d2 := cdir_src) in CS1...
            apply cenv_split_exp_rebind_chan_right with (T2 := Te2) (d2 := cdir_snk) in CS2...
            apply cenv_split_proc_rebind_chan_both with (T2 := Te2) in CS'...
            apply typing_parr with
                (Qs1 := QsL1 ++ [QL1 ++ [(X, cbind_proto cdir_src Te2)] ++ QR1] ++ QsR1)
                (Qs2 := QsL2 ++ [QL2 ++ [(X, cbind_proto cdir_snk Te2)] ++ QR2] ++ QsR2)...
              apply typing_exp with (Q := QL1 ++ [(X, cbind_proto cdir_src Te2)] ++ QR1)...
                apply ectx_typing_plug with (D1 := lempty) (D2 := lempty)
                    (M := M1) (T := typ_plus T1' T2')
                    (e := open_ce_rec 0 X (exp_inr (typ_plus T1' T2') (exp_src O Te2)))
                    (Q1 := QL1 ++ QR1)
                    (Q2 := [(X, cbind_proto cdir_src Te2)])...
                  simpl. constructor...
                apply cenvs_split_multi_unpad...
                  apply wf_cenvs_from_single...
              apply typing_exp with (Q := QL2 ++ [(X, cbind_proto cdir_snk Te2)] ++ QR2)...
                apply ectx_typing_plug with (D1 := lempty) (D2 := lempty)
                    (M := M2) (T := Te2)
                    (e := open_ce_rec 0 X (exp_snk O Te2))
                    (Q1 := QL2 ++ QR2) (Q2 := [(X, cbind_proto cdir_snk Te2)])...
                  constructor...
                apply cenvs_split_multi_unpad...
                  apply wf_cenvs_from_single...
              apply cenvs_split_unpad_both in H17...
                apply cenvs_split_pad_both...
                inversion H9; subst.
                  rewrite_env (cempty ++
                                       [(X, cbind_proto cdir_both (typ_with T3 Te2))] ++
                                       cempty) in H17.
                    destruct (cenvs_split_single_srcsnk empty X (typ_with T3 Te2)
                                      QL1 QR1 QL2 QR2 cempty cempty QsL QsR)...
                    apply cenvs_split_unpadded in H17... simpl_env in H17.
                    apply cenvs_split_to_proc in H17. destruct H17 as [Z H17].
                    apply cenv_split_proc_mid_srcsnk in H17.
                    destruct H17 as [QEL [QER [EqE [CSEL [CSER Eq]]]]]. subst.
                    symmetry in EqE. apply app_eq_unit in EqE.
                    destruct EqE as [[Eq1 Eq2] | [Eq1 Eq2]]; subst.
                      inversion Eq2. subst.
                        inversion CSEL. inversion CSER. subst.
                        inversion CSL. inversion CSR. subst.
                        simpl_env in *. apply cenvs_split_padded...
                        apply cenvs_split_from_proc with (Z := Some X).
                        rewrite_env ([(X, cbind_proto cdir_src Te2)] ++ cempty).
                        rewrite_env ([(X, cbind_proto cdir_snk Te2)] ++ cempty).
                        rewrite_env ([(X, cbind_proto cdir_both Te2)] ++ cempty).
                        constructor...
                      discriminate Eq2.
                  rewrite_env (cempty ++
                                       [(X, cbind_proto cdir_both (typ_with T3 Te2))] ++
                                       Q) in H17.
                    destruct (cenvs_split_single_srcsnk empty X (typ_with T3 Te2)
                                      QL1 QR1 QL2 QR2 cempty Q QsL QsR)...
                    apply cenvs_split_unpadded in H17... simpl_env in H17.
                    apply cenvs_split_to_proc in H17. destruct H17 as [Z H17].
                    apply cenv_split_proc_mid_srcsnk in H17.
                    destruct H17 as [QLL [QRR [Eq' [CSLL [CSRR Eq]]]]]. subst.
                    destruct QLL; simpl in Eq'; inversion Eq'; subst.
                      inversion CSLL. subst.
                        inversion CSL. subst.
                        simpl_env in *. inversion CS'. subst.
                        apply cenvs_split_padded...
                        apply cenvs_split_from_proc with (Z := Some X).
                        apply cenv_split_proc_srcsnk...
                          apply dom_cenv_split_exp in CSR.
                            apply dom_cenv_split_exp in CSRR.
                            rewrite CSRR. rewrite <- CSR...
                      simpl_env in *. absurd (X `notin` singleton X)...
                        rewrite doms_append in Fr.
                        rewrite doms_append in Fr.
                        rewrite doms_single in Fr.
                        simpl_env in Fr. clear - Fr. fsetdec.

  Case "red_close".
    inversion PTyp; subst.
    pick fresh X and apply typing_new...
      instantiate (1 := FQs)...
      lapply (H9 X)... intros.
        assert (exists f1'', plug M1 (open_ce_rec 0 X (exp_src O typ_answer)) f1'').
          apply plug_exists...
        assert (exists f2'', plug M2 (open_ce_rec 0 X (exp_snk O typ_answer)) f2'').
          apply plug_exists...
        destruct H4 as [f1'' Plug1]. destruct H6 as [f2'' Plug2].
        rewrite (plug_open_ce_rec M1 (exp_src O typ_answer) f1 0 X f1'') in Plug1...
        rewrite (plug_open_ce_rec M2 (exp_snk O typ_answer) f2 0 X f2'') in Plug2...
        clear f1'' f2''. simpl in Plug1. simpl in Plug2.
        inversion H3; inversion H8; inversion H11; subst.

          SCase "typing_parl".
            lapply (plug_typing empty lempty Q M1
                          (exp_src X typ_answer)
                          (open_ce_rec 0 X f1) T Plug1)...
            lapply (plug_typing empty lempty Q0 M2
                          (exp_snk X typ_answer)
                          (open_ce_rec 0 X f2) typ_answer Plug2)... intros.
            destruct H6 as [Dm1 [De1 [Qm1 [Qe1 [Te1 [CS1 [LS1 [Typ1 ETyp1]]]]]]]].
            destruct H4 as [Dm2 [De2 [Qm2 [Qe2 [Te2 [CS2 [LS2 [Typ2 ETyp2]]]]]]]].
            inversion Typ1. inversion Typ2.
            inversion LS1. inversion LS2. subst.
            clear LS1 LS2 H33 H38.
            inversion H19. subst.
            assert (exists f1'', plug M1 (open_ce_rec 0 X exp_unit) f1'').
              apply plug_exists...
            assert (exists f2'', plug M2 (open_ce_rec 0 X (exp_done O)) f2'').
              apply plug_exists...
            destruct H6 as [f1'' Plug1']. destruct H10 as [f2'' Plug2'].
            simpl in Plug1'. simpl in Plug2'.
            rewrite (plug_open_ce_rec M1 exp_unit f1' 0 X f1'') in Plug1'...
            rewrite (plug_open_ce_rec M2 (exp_done O) f2' 0 X f2'') in Plug2'...
            clear f1'' f2''.
            apply cenvs_split_multi_single in H17.
            apply cenvs_split_multi_single in H22.
            destruct H17 as [QsL1 [QsR1 [QEq1 [EmpL1 EmpR1]]]].
            destruct H22 as [QsL2 [QsR2 [QEq2 [EmpL2 EmpR2]]]]. subst.
            destruct (cenv_split_exp_single_right empty Qm1
                             X cdir_src typ_answer Q) as
                [QL1 [QR1 [Eq1 Eq2]]]... subst.
            destruct (cenv_split_exp_single_right empty Qm2 
                             X cdir_snk typ_answer Q0) as
                [QL2 [QR2 [Eq1 Eq2]]]... subst.
            assert (exists QL', exists QR',
                          cenv_split_proc empty
                            (QL1 ++ [(X, cbind_proto cdir_src typ_answer)] ++ QR1)
                            (QL2 ++ [(X, cbind_proto cdir_snk typ_answer)] ++ QR2)
                            (QL' ++ [(X, cbind_proto cdir_both typ_answer)] ++ QR')
                            (Some X) /\
                          cenv_split_exp empty QL1 QL2 QL' /\
                          cenv_split_exp empty QR1 QR2 QR').
              apply cenvs_split_unpad_both in H13...
              apply cenvs_split_two_proc in H13.
              destruct H13 as [Q' [Z' CS']].
              destruct (cenv_split_proc_mid_srcsnk empty X typ_answer
                               QL1 QR1 QL2 QR2 Q' Z') as
                  [Q3L [Q3R [EqQ [CSL [CSR EqZ]]]]]...
              subst. exists Q3L. exists Q3R...
            destruct H6 as [QL' [QR' [CS' [CSL CSR]]]].
            rewrite_env (cempty ++ [(X, cbind_proto cdir_snk typ_answer)] ++ cempty) in CS2.
            rewrite_env (QL2 ++ [(X, cbind_proto cdir_snk typ_answer)] ++ QR2) in CS2.
            apply cenv_split_exp_rebind_chan_right with (T2 := typ_answer) (d2 := cdir_both) in CS2...
            apply cenv_split_proc_shift_src_right in CS'...
            apply typing_parl with
                (Qs1 := QsL1 ++ [QL1 ++ QR1] ++ QsR1)
                (Qs2 := QsL2 ++ [QL2 ++ [(X, cbind_proto cdir_both typ_answer)] ++ QR2] ++ QsR2)...
              apply typing_exp with (Q := QL1 ++ QR1)...
                apply ectx_typing_plug with (D1 := lempty) (D2 := lempty)
                    (M := M1) (T := typ_unit)
                    (e := open_ce_rec 0 X exp_unit)
                    (Q1 := QL1 ++ QR1)
                    (Q2 := cempty)...
                  apply cenv_split_exp_right_id...
                apply cenvs_split_multi_unpad...
                  apply wf_cenvs_from_single...
              apply typing_exp with (Q := QL2 ++ [(X, cbind_proto cdir_both typ_answer)] ++ QR2)...
                apply ectx_typing_plug with (D1 := lempty) (D2 := lempty)
                    (M := M2) (T := typ_answer)
                    (e := open_ce_rec 0 X (exp_done O))
                    (Q1 := QL2 ++ QR2) (Q2 := [(X, cbind_proto cdir_both typ_answer)])...
                  constructor...
                apply cenvs_split_multi_unpad...
                  apply wf_cenvs_from_single...
              apply cenvs_split_unpad_both in H13...
                apply cenvs_split_pad_both...
                inversion H7; subst.
                  rewrite_env (cempty ++
                                       [(X, cbind_proto cdir_both typ_answer)] ++
                                       cempty) in H13.
                    destruct (cenvs_split_single_srcsnk empty X typ_answer
                                      QL1 QR1 QL2 QR2 cempty cempty QsL QsR)...
                    apply cenvs_split_unpadded in H13... simpl_env in H13.
                    apply cenvs_split_to_proc in H13. destruct H13 as [Z H13].
                    apply cenv_split_proc_mid_srcsnk in H13.
                    destruct H13 as [QEL [QER [EqE [CSEL [CSER Eq]]]]]. subst.
                    symmetry in EqE. apply app_eq_unit in EqE.
                    destruct EqE as [[Eq1 Eq2] | [Eq1 Eq2]]; subst.
                      inversion Eq2. subst.
                        inversion CSEL. inversion CSER. subst.
                        inversion CSL. inversion CSR. subst.
                        simpl_env in *. apply cenvs_split_padded...
                        apply cenvs_split_from_proc with (Z := None).
                        apply cenv_split_proc_left_id...
                      discriminate Eq2.
                  rewrite_env (cempty ++
                                       [(X, cbind_proto cdir_both typ_answer)] ++
                                       Q) in H13.
                    destruct (cenvs_split_single_srcsnk empty X typ_answer
                                      QL1 QR1 QL2 QR2 cempty Q QsL QsR)...
                    apply cenvs_split_unpadded in H13... simpl_env in H13.
                    apply cenvs_split_to_proc in H13. destruct H13 as [Z H13].
                    apply cenv_split_proc_mid_srcsnk in H13.
                    destruct H13 as [QLL [QRR [Eq' [CSLL [CSRR Eq]]]]]. subst.
                    destruct QLL; simpl in Eq'; inversion Eq'; subst.
                      inversion CSLL. subst.
                        inversion CSL. subst.
                        simpl_env in *.
                        apply cenvs_split_padded...
                        apply cenvs_split_from_proc with (Z := None).
                        apply cenv_split_proc_right...
                          apply cenv_split_exp_proc...
                          rewrite doms_append in Fr.
                            rewrite doms_append in Fr.
                            rewrite doms_single in Fr.
                            simpl_env in Fr. clear - Fr. fsetdec.
                      simpl_env in *. absurd (X `notin` singleton X)...
                        rewrite doms_append in Fr.
                        rewrite doms_append in Fr.
                        rewrite doms_single in Fr.
                        simpl_env in Fr. clear - Fr. fsetdec.

          SCase "typing_parr".
            lapply (plug_typing empty lempty Q M1
                          (exp_src X typ_answer)
                          (open_ce_rec 0 X f1) typ_answer Plug1)...
            lapply (plug_typing empty lempty Q0 M2
                          (exp_snk X typ_answer)
                          (open_ce_rec 0 X f2) T Plug2)... intros.
            destruct H6 as [Dm1 [De1 [Qm1 [Qe1 [Te1 [CS1 [LS1 [Typ1 ETyp1]]]]]]]].
            destruct H4 as [Dm2 [De2 [Qm2 [Qe2 [Te2 [CS2 [LS2 [Typ2 ETyp2]]]]]]]].
            inversion Typ1. inversion Typ2.
            inversion LS1. inversion LS2. subst.
            clear LS1 LS2 H33 H38.
            inversion H19. subst.
            assert (exists f1'', plug M1 (open_ce_rec 0 X exp_unit) f1'').
              apply plug_exists...
            assert (exists f2'', plug M2 (open_ce_rec 0 X (exp_done O)) f2'').
              apply plug_exists...
            destruct H6 as [f1'' Plug1']. destruct H10 as [f2'' Plug2'].
            simpl in Plug1'. simpl in Plug2'.
            rewrite (plug_open_ce_rec M1 exp_unit f1' 0 X f1'') in Plug1'...
            rewrite (plug_open_ce_rec M2 (exp_done O) f2' 0 X f2'') in Plug2'...
            clear f1'' f2''.
            apply cenvs_split_multi_single in H17.
            apply cenvs_split_multi_single in H22.
            destruct H17 as [QsL1 [QsR1 [QEq1 [EmpL1 EmpR1]]]].
            destruct H22 as [QsL2 [QsR2 [QEq2 [EmpL2 EmpR2]]]]. subst.
            destruct (cenv_split_exp_single_right empty Qm1
                             X cdir_src typ_answer Q) as
                [QL1 [QR1 [Eq1 Eq2]]]... subst.
            destruct (cenv_split_exp_single_right empty Qm2 
                             X cdir_snk typ_answer Q0) as
                [QL2 [QR2 [Eq1 Eq2]]]... subst.
            assert (exists QL', exists QR',
                          cenv_split_proc empty
                            (QL1 ++ [(X, cbind_proto cdir_src typ_answer)] ++ QR1)
                            (QL2 ++ [(X, cbind_proto cdir_snk typ_answer)] ++ QR2)
                            (QL' ++ [(X, cbind_proto cdir_both typ_answer)] ++ QR')
                            (Some X) /\
                          cenv_split_exp empty QL1 QL2 QL' /\
                          cenv_split_exp empty QR1 QR2 QR').
              apply cenvs_split_unpad_both in H13...
              apply cenvs_split_two_proc in H13.
              destruct H13 as [Q' [Z' CS']].
              destruct (cenv_split_proc_mid_srcsnk empty X typ_answer
                               QL1 QR1 QL2 QR2 Q' Z') as
                  [Q3L [Q3R [EqQ [CSL [CSR EqZ]]]]]...
              subst. exists Q3L. exists Q3R...
            destruct H6 as [QL' [QR' [CS' [CSL CSR]]]].
            rewrite_env (cempty ++ [(X, cbind_proto cdir_snk typ_answer)] ++ cempty) in CS2.
            rewrite_env (QL2 ++ [(X, cbind_proto cdir_snk typ_answer)] ++ QR2) in CS2.
            apply cenv_split_exp_rebind_chan_right with (T2 := typ_answer) (d2 := cdir_both) in CS2...
            apply cenv_split_proc_shift_src_right in CS'...
            apply typing_parr with
                (Qs1 := QsL1 ++ [QL1 ++ QR1] ++ QsR1)
                (Qs2 := QsL2 ++ [QL2 ++ [(X, cbind_proto cdir_both typ_answer)] ++ QR2] ++ QsR2)...
              apply typing_exp with (Q := QL1 ++ QR1)...
                apply ectx_typing_plug with (D1 := lempty) (D2 := lempty)
                    (M := M1) (T := typ_unit)
                    (e := open_ce_rec 0 X exp_unit)
                    (Q1 := QL1 ++ QR1)
                    (Q2 := cempty)...
                  apply cenv_split_exp_right_id...
                apply cenvs_split_multi_unpad...
                  apply wf_cenvs_from_single...
              apply typing_exp with (Q := QL2 ++ [(X, cbind_proto cdir_both typ_answer)] ++ QR2)...
                apply ectx_typing_plug with (D1 := lempty) (D2 := lempty)
                    (M := M2) (T := typ_answer)
                    (e := open_ce_rec 0 X (exp_done O))
                    (Q1 := QL2 ++ QR2) (Q2 := [(X, cbind_proto cdir_both typ_answer)])...
                  constructor...
                apply cenvs_split_multi_unpad...
                  apply wf_cenvs_from_single...
              apply cenvs_split_unpad_both in H13...
                apply cenvs_split_pad_both...
                inversion H7; subst.
                  rewrite_env (cempty ++
                                       [(X, cbind_proto cdir_both typ_answer)] ++
                                       cempty) in H13.
                    destruct (cenvs_split_single_srcsnk empty X typ_answer
                                      QL1 QR1 QL2 QR2 cempty cempty QsL QsR)...
                    apply cenvs_split_unpadded in H13... simpl_env in H13.
                    apply cenvs_split_to_proc in H13. destruct H13 as [Z H13].
                    apply cenv_split_proc_mid_srcsnk in H13.
                    destruct H13 as [QEL [QER [EqE [CSEL [CSER Eq]]]]]. subst.
                    symmetry in EqE. apply app_eq_unit in EqE.
                    destruct EqE as [[Eq1 Eq2] | [Eq1 Eq2]]; subst.
                      inversion Eq2. subst.
                        inversion CSEL. inversion CSER. subst.
                        inversion CSL. inversion CSR. subst.
                        simpl_env in *. apply cenvs_split_padded...
                        apply cenvs_split_from_proc with (Z := None).
                        apply cenv_split_proc_left_id...
                      discriminate Eq2.
                  rewrite_env (cempty ++
                                       [(X, cbind_proto cdir_both typ_answer)] ++
                                       Q) in H13.
                    destruct (cenvs_split_single_srcsnk empty X typ_answer
                                      QL1 QR1 QL2 QR2 cempty Q QsL QsR)...
                    apply cenvs_split_unpadded in H13... simpl_env in H13.
                    apply cenvs_split_to_proc in H13. destruct H13 as [Z H13].
                    apply cenv_split_proc_mid_srcsnk in H13.
                    destruct H13 as [QLL [QRR [Eq' [CSLL [CSRR Eq]]]]]. subst.
                    destruct QLL; simpl in Eq'; inversion Eq'; subst.
                      inversion CSLL. subst.
                        inversion CSL. subst.
                        simpl_env in *.
                        apply cenvs_split_padded...
                        apply cenvs_split_from_proc with (Z := None).
                        apply cenv_split_proc_right...
                          apply cenv_split_exp_proc...
                          rewrite doms_append in Fr.
                            rewrite doms_append in Fr.
                            rewrite doms_single in Fr.
                            simpl_env in Fr. clear - Fr. fsetdec.
                      simpl_env in *. absurd (X `notin` singleton X)...
                        rewrite doms_append in Fr.
                        rewrite doms_append in Fr.
                        rewrite doms_single in Fr.
                        simpl_env in Fr. clear - Fr. fsetdec.
Qed.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop.opt" ***
*** coq-prog-args: ("-impredicative-set" "-emacs-U" "-I" "../../../metatheory") ***
*** End: ***
 *)
