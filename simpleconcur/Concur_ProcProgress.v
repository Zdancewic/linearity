(** Type-safety proofs.

    Based on work by: Brian Aydemir and Arthur Chargu\'eraud, with help from
    Aaron Bohannon, Jeffrey Vaughan, and Dimitrios Vytiniotis.

    In parentheses are given the label of the corresponding lemma in
    the appendix (informal proofs) of the POPLmark Challenge.

    Table of contents:
      - #<a href="##progress">Progress</a># *)

Require Export Concur_ProcLemmas.
Require Import Omega.

Axiom skip : False.
Ltac skip := assert False; [ apply skip | contradiction ].



(* ********************************************************************** *)
(** ** Canonical forms (14) *)

Lemma canonical_form_unit : forall Q e,
  value e ->
  typing empty lempty Q e typ_unit ->
  (e = exp_unit) \/ (exists X, e = exp_src (fchan X) typ_answer).
Proof.
  intros Q e Val Typ.
  remember Concur_Definitions.empty as E.
  remember (typ_unit) as T.
  revert HeqT HeqE.
  (typing_cases (induction Typ) Case); 
      intros EQT EQE; subst;
      try solve [ inversion Val | inversion EQT | inversion H0 | eauto ].
    rewrite_env (cempty ++ [(X, cbind_proto cdir_snk typ_unit)] ++ cempty) in H.
      apply wf_proto_from_wf_cenv in H. inversion H.
    inversion H0. subst. right. exists X. auto.
Qed.

Lemma canonical_form_answer : forall Q e,
  value e ->
  typing empty lempty Q e typ_answer ->
  (exists X, e = exp_snk (fchan X) typ_answer) \/ (exists X, e = exp_done (fchan X)).
Proof.
  intros Q e Val Typ.
  remember Concur_Definitions.empty as E.
  remember (typ_answer) as T.
  revert HeqT HeqE.
  (typing_cases (induction Typ) Case); 
    intros EQT EQE; subst;
    try solve [ inversion Val | inversion EQT | inversion H0 | eauto ].
Qed.

Lemma canonical_form_with : forall Q e U1 U2,
  value e ->
  typing empty lempty Q e (typ_with U1 U2) ->
  (exists e1, exists e2, e = exp_apair e1 e2) \/ exists X, e = exp_snk (fchan X) (typ_with U1 U2).
Proof.
  intros Q e U1 U2 Val Typ.
  remember Concur_Definitions.empty as E.
  remember (typ_with U1 U2) as T.
  revert U1 U2 HeqT HeqE.
  (typing_cases (induction Typ) Case); 
      intros U1 U2 EQT EQE; subst;
      try solve [ inversion Val | inversion EQT | inversion H0 | auto ].
    left. exists e1. exists e2. auto.
    right. exists X. auto.
Qed.

Lemma canonical_form_arrow : forall e Q T1 T2,
  value e ->
  typing empty lempty Q e (typ_arrow T1 T2) ->
  (exists e1, e = exp_abs T1 e1)  \/
  (exists X, e = exp_snk (fchan X) (typ_arrow T1 T2)) \/
  (exists X, exists T3, e = exp_src (fchan X) T3 
                              /\ dual empty T3 (typ_arrow T1 T2)).
Proof.
  intros e Q T1 T2 Val Typ.
  remember Concur_Definitions.empty as E.
  remember (typ_arrow T1 T2) as T.
  revert T1 T2 HeqT HeqE.
  (typing_cases (induction Typ) Case); 
      intros U1 U2 EQT EQE; subst;
      try solve [ inversion Val | inversion EQT | inversion H0 | eauto ].
    left. exists e1. inversion EQT. auto.
    right. right. exists X. exists T. auto.
Qed.

Lemma canonical_form_tensor : forall e Q T1 T2,
  value e ->
  typing empty lempty Q e (typ_tensor T1 T2) ->
  (exists e1, exists e2, e = exp_mpair e1 e2).
Proof.
  intros Q e T1 T2 Val Typ.
  remember Concur_Definitions.empty as E.
  remember (typ_tensor T1 T2) as T.
  revert T1 T2 HeqT HeqE.
  (typing_cases (induction Typ) Case); 
      intros T1' T2' EQT EQE; subst;
      try solve [ inversion Val | inversion EQT | inversion H0 | eauto ].
    rewrite_env (cempty ++ [(X, cbind_proto cdir_snk (typ_tensor T1' T2'))] ++ cempty) in H.
      apply wf_proto_from_wf_cenv in H. inversion H.
Qed.

Lemma canonical_form_plus : forall e Q T1 T2,
  value e ->
  typing empty lempty Q e (typ_plus T1 T2) ->
  (exists e1, e = (exp_inl (typ_plus T1 T2) e1)) \/ (exists e2, e = (exp_inr (typ_plus T1 T2) e2)).
Proof.
  intros Q e T1 T2 Val Typ.
  remember Concur_Definitions.empty as E.
  remember (typ_plus T1 T2) as T.
  revert T1 T2 HeqT HeqE.
  (typing_cases (induction Typ) Case); 
      intros T1' T2' EQT EQE; subst;
      try solve [ inversion Val | inversion EQT | inversion H0 | eauto ].
    rewrite_env (cempty ++ [(X, cbind_proto cdir_snk (typ_plus T1' T2'))] ++ cempty) in H.
      apply wf_proto_from_wf_cenv in H. inversion H.
Qed.


(* And now for processes, where things get harder... *)

Lemma canon_inner_par_inner : forall P1 P2,
  canon_inner P1 ->
  canon_inner P2 ->
  exists P3, proc_eq (proc_par P1 P2) P3 /\ canon_inner P3.
Proof with auto.
  intros P1 P2 CI1 CI2. induction CI1.
    exists (proc_par e P2). split...
    destruct IHCI1 as [P3 [PEq CI3]]. exists (proc_par e P3). split...
      apply proc_eqm_proc_eq...
        eapply proc_eqm_left.
          eapply proc_eq1_assoc.
          eapply proj1. apply proc_eq_proc_eqm.
          apply eq_par...
Qed.

Lemma canon_inner_rename : forall P X Y i,
  Y `notin` fv_cp P ->
  X `notin` fv_cp P ->
  canon_inner (open_cp_rec i X P) ->
  canon_inner (open_cp_rec i Y P).
Proof.
  intros P X Y i NI1 NI2 CI.
  remember (open_cp_rec i X P) as Q. generalize dependent P.
  generalize dependent i. generalize dependent X. generalize dependent Y.
  induction CI; intros Y X i P1 NI1 NI2 EQ; destruct P1; simpl in *; inversion EQ; subst; auto.
  apply canon_inner_exp. 
  apply (expr_rename e0 i X Y). auto.

  inversion EQ. destruct P1_1; inversion H2; subst.
  simpl in *.
  apply canon_inner_par. 
  apply (expr_rename e0 i X Y). auto.
  apply (IHCI Y X i P1_2). fsetdec. fsetdec. auto.
Qed.

Lemma canon_outer_rename : forall P X Y i,
  Y `notin` fv_cp P ->
  X `notin` fv_cp P ->
  canon_outer (open_cp_rec i X P) ->
  canon_outer (open_cp_rec i Y P).
Proof.
  intros P X Y i NI1 NI2 CO.
  remember (open_cp_rec i X P) as Q.
  generalize dependent P. generalize dependent i.   
  generalize dependent X. generalize dependent Y.
  induction CO; intros Y X i P1 NI1 NI2 EQ; destruct P1; simpl in EQ; inversion EQ; subst; auto.   
  apply canon_outer_par. apply (canon_inner_rename _ X Y i); auto.

  apply canon_outer_par. apply (canon_inner_rename _ X Y i); auto.

  inversion H.

  simpl. pick fresh Z and apply canon_outer_new.
  unfold open_cp. rewrite open_cp_open_cp_comm; auto.
  eapply (H0 Z); auto.
  apply fv_cp_notin_open; auto.
  assert (X `notin` fv_cp (open_cp_rec 0 Z P1)). 
  apply fv_cp_notin_open; auto. apply H1.
  unfold open_cp. 
  rewrite open_cp_open_cp_comm; auto.
Qed.
  
Lemma canon_outer_par_inner : forall P1 P2,
  canon_outer P1 ->
  canon_inner P2 ->
  exists P3, proc_eq (proc_par P1 P2) P3 /\ canon_outer P3.
Proof with auto.
  intros P1 P2 CO.
  revert P2.
  induction CO; intros P2 PI.
    lapply (canon_inner_par_inner P P2)... intros.
      lapply H0... intros.
      destruct H1 as [P3 [PEq CI]].
      exists P3...
    pick fresh X. 
      lapply (H0 X)... intros.
      lapply (H1 P2)... intros.
      destruct H2 as [P3 [PEq CN]].
      exists (proc_new T (close_cp P3 X)). split.
        apply eq_trans with (P2 := proc_new T (proc_par P P2)).
          apply proc_eq_regular in PEq. intuition.
            apply eq_sym. apply eq_extrude...
            pick fresh Y and apply process_new...
            unfold open_cp. simpl. inversion H2; subst.
            constructor...
              apply (process_rename P 0 X Y). unfold open_cp in H6; auto.
              rewrite <- open_cp_rec_process...
          pick fresh Y and apply eq_new...
            unfold open_cp.
            apply (proc_eq_rename _ _ Y X); auto.
            destruct (proc_eq_regular (proc_par (open_cp P X) P2) P3) as [R1 R2]; auto.
            simpl. inversion R1. unfold open_cp in H4. subst. apply process_par.
            auto. rewrite <- open_cp_rec_process. auto. auto.
            apply notin_union. simpl. auto. apply fv_close_cp.
            apply notin_union. simpl. auto. unfold close_cp. apply notin_close_cp. auto.
            simpl. rewrite <- (open_cp_rec_process P2); auto.
            unfold close_cp. rewrite open_close_cp_rec; auto.

        pick fresh Y and apply canon_outer_new.
          unfold open_cp.
          apply (canon_outer_rename _ X Y). 
          unfold close_cp. apply notin_close_cp. fsetdec.
          apply fv_close_cp.
          unfold close_cp. rewrite open_close_cp_rec; auto.
Qed.

(* I don't recall what this is for; does it help with the above holes? *)
(*Lemma canon_outer_exists :  forall P P2 P3 T X, 
  proc_eq (proc_par (open_cp P X) P2) P3 ->
  canon_outer P3 ->
  exists P4 : proc, proc_eq (proc_par (proc_new T P) P2) P4 /\ canon_outer P4.
Proof.
Admitted.*)

Lemma extrude_canon : forall P1 P2,
  canon_outer P1 ->
  canon_outer P2 ->
  exists P3, proc_eq (proc_par P1 P2) P3 /\ canon_outer P3.
Proof with auto.
  intros P1 P2 CO1 CO2.
  (canon_outer_cases (induction CO2) Case).
    Case "canon_outer_par".
      apply canon_outer_par_inner...
    Case "canon_outer_new".
      pick fresh X. lapply (H X)... lapply (H0 X)... intros.
      destruct H1 as [P3 [PEq CO3]].
      exists (proc_new T (close_cp P3 X)). split.
        apply eq_trans with (P2 := proc_new T (proc_par P1 P)).
          apply proc_eq_regular in PEq. intuition.
            apply eq_sym.
            apply eq_trans with (P2 := proc_new T (proc_par P P1)).
              pick fresh Y and apply eq_new. inversion H1; subst.
                unfold open_cp. simpl. apply eq_comm; apply eq_refl.
                  rewrite <- open_cp_rec_process; auto.
                  apply (process_rename P _ X Y).
                  unfold open_cp in H7; auto.
              apply eq_trans with (P2 := (proc_par (proc_new T P) P1)).
                apply eq_extrude... pick fresh Y and apply process_new...
                  unfold open_cp. simpl.
                  inversion H1; subst. constructor...
                    apply (process_rename P _ X Y). unfold open_cp in H7. auto.
                    rewrite <- open_cp_rec_process...
                apply eq_comm... apply eq_refl.
                  pick fresh Y and apply process_new...
                  inversion H1. subst. unfold open_cp in *.
                  apply (process_rename P _ X Y); auto.
          pick fresh Y and apply eq_new...
            unfold open_cp.
            apply (proc_eq_rename (proc_par P1 P) (close_cp P3 X) Y X 0).
            simpl. constructor... 
            rewrite <- open_cp_rec_process. 
            destruct (proc_eq_regular (proc_par P1 (open_cp P X)) P3) as [R1 R2]; auto.
            destruct (proc_eq_regular (proc_par P1 (open_cp P X)) P3) as [R1 R2]; auto.
            apply notin_union. simpl. fsetdec. apply fv_close_cp; auto.
            apply notin_union. simpl. fsetdec. apply fv_cp_close_cp; auto.
            unfold close_cp. rewrite open_close_cp_rec; auto.
            simpl. rewrite <- (open_cp_rec_process P1); auto.

        pick fresh Y and apply canon_outer_new.
          unfold open_cp. 
        apply (canon_outer_rename _ X Y).
        unfold close_cp. apply fv_cp_close_cp; auto.
        apply fv_close_cp; auto.
        unfold close_cp. rewrite open_close_cp_rec; auto.
Qed.
   
Lemma proc_canon : forall P,
  process P -> 
  exists P', proc_eq P P' /\ canon_outer P'.
Proof.
  intros P PROC.
  (process_cases (induction PROC) Case); intros; eauto.
  exists (proc_exp e). intros.
    split; auto.

  destruct IHPROC1 as [P1' [EQ1 CAN1]]; auto.
  destruct IHPROC2 as [P2' [EQ2 CAN2]]; auto.

  destruct (extrude_canon P1' P2'  CAN1 CAN2) as [P' [PEQ CAN']]. 
  exists P'; auto. split.  eapply (eq_trans (proc_par P1 P2) (proc_par P1' P2')). 
  apply eq_par. auto. auto. auto. auto.

  pick fresh X.
  lapply (H1 X); auto. intros.
  destruct H2 as [P' [PEQ CAN]].

  exists (proc_new T (close_cp P' X)). split.
    pick fresh Y and apply eq_new.
      unfold open_cp.
      apply (proc_eq_rename _ _ Y X); auto.
      apply notin_union. fsetdec.
      apply fv_close_cp.
      apply notin_union. fsetdec.
      apply fv_cp_close_cp; auto.
      unfold close_cp. rewrite (open_close_cp_rec X); auto.
    pick fresh Y and apply canon_outer_new.
      unfold open_cp.
      apply (canon_outer_rename _ X Y); auto.
      unfold close_cp. apply fv_cp_close_cp; auto.
      apply fv_close_cp.
      unfold close_cp. rewrite (open_close_cp_rec X); auto.
Qed.


(* Tentative graph-ish work *)

(* I'm not sure if we'll need something like this, but maybe? *)
Inductive exprs : list exp -> Prop :=
  | exprs_nil : exprs nil
  | exprs_cons : forall e es,
      expr e ->
      exprs es ->
      exprs (e :: es)
.

Inductive essence : proc -> cenv -> list exp -> Prop :=
  | essence_exp : forall e,
      expr e ->
      essence (proc_exp e) cempty [e]
  | essence_par : forall e P Q es,
      expr e ->
      process P ->
      essence P Q es ->
      essence (proc_par (proc_exp e) P) Q (e :: es)
  | essence_new : forall L T P Q es,
      type T ->
      (forall X : atom, X `notin` L ->
        essence (open_cp P X) Q (List.map (fun e => open_ce e X) es)) ->
      essence (proc_new T P) Q es
.

Inductive semi_canon : proc -> Prop :=
  | semi_canon_exp : forall e,
      expr e ->
      semi_canon (proc_exp e)
  | semi_canon_par : forall e P,
      expr e ->
      semi_canon P ->
      semi_canon (proc_par (proc_exp e) P)
  | semi_canon_new : forall L T P,
      type T ->
      (forall X, X `notin` L -> semi_canon (open_cp P X)) ->
      semi_canon (proc_new T P)
.



(* Is this all unnecessary now? 
Inductive canon_typing : tenv -> proc -> typ -> Prop :=
  | canon_typing_exp : forall R Q e T,
      typing empty lempty Q e T ->
      tenv_flatten R Q ->
      canon_typing R (proc_exp e) T
  | canon_typing_parl : forall Q1 R2 R3 e1 P2 T1,
      typing empty lempty Q1 e1 T1 ->
      canon_typing R2 P2 typ_answer ->
      tenv_split empty Q1 R2 R3 ->
      canon_typing R3 (proc_par (proc_exp e1) P2) T1
  | canon_typing_parr : forall Q1 R2 R3 e1 P2 T2,
      typing empty lempty Q1 e1 typ_answer ->
      canon_typing R2 P2 T2 ->
      tenv_split empty Q1 R2 R3 ->
      canon_typing R3 (proc_par (proc_exp e1) P2) T2
  | canon_typing_new : forall L S U T1 P1 T2,
      wf_proto empty T1 ->
      (forall X : atom, X `notin` L ->
        canon_typing (S, [(X, T1)]++U) (open_cp P1 X) T2) ->
      canon_typing (S, U) (proc_new T1 P1) T2
.

(* Let's hope this is strong enough in the new case... *)
Inductive sctx : Set :=
  | sctx_hole
  | sctx_par : forall e, expr e -> sctx -> sctx
  | sctx_new : forall T, type T -> sctx -> sctx
.

Inductive proc_plug : sctx -> proc -> proc -> Prop :=
  | proc_plug_hole : forall P,
      proc_plug sctx_hole P P
  | proc_plug_par : forall e1 N2 He1 P P2,
      proc_plug N2 P P2 ->
      proc_plug (sctx_par e1 He1 N2) P (proc_par e1 P2)
  | proc_plug_new : forall T HT N1 P P1,
      proc_plug N1 P P1 ->
      proc_plug (sctx_new T HT N1) P (proc_new T P1)
.

Inductive sctx_typing : cenvs -> sctx -> typ -> typ -> Prop :=
  | sctx_typing_hole : forall T,
      wf_typ empty T ->
      sctx_typing lcempty sctx_hole T T
  | sctx_typing_parl : forall Q1 R2 R3 e1 N2 T T1 He1,
      typing empty lempty Q1 e1 T1 ->
      sctx_typing R2 N2 T typ_answer ->
      tenv_split empty Q1 R2 R3 ->
      sctx_typing R3 (sctx_par e1 He1 N2) T T1
  | sctx_typing_parr : forall Q1 R2 R3 e1 N2 T T2 He1,
      typing empty lempty Q1 e1 typ_answer ->
      sctx_typing R2 N2 T T2 ->
      tenv_split empty Q1 R2 R3 ->
      sctx_typing R3 (sctx_par e1 He1 N2) T T2
  | sctx_typing_new : forall L S U N1 T T1 T0 HT0,
      wf_proto empty T0 ->
      (forall X : atom, X `notin` L ->
         sctx_typing (S, [(X, T0)]++U) N1 T T1) ->
      sctx_typing (S, U) (sctx_new T0 HT0 N1) T T1
.*)

Hint Constructors exprs essence.
Hint Resolve semi_canon_exp semi_canon_par.

Tactic Notation "semi_canon_cases" tactic(first) tactic(c) :=
  first;
  [ c "semi_canon_exp" | c "semi_canon_par" | c "semi_canon_new" ].

Lemma semi_canon_regular: forall P,
  semi_canon P ->
  process P.
Proof with auto.
  intros. induction H...
    pick fresh X and apply process_new...
Qed.

(*Lemma canon_typing_semi: forall R P T,
  canon_typing R P T ->
  semi_canon P.
Proof with auto.
  intros. induction H...
    pick fresh X and apply semi_canon_new...
Qed.*)

Lemma canon_inner_semi: forall P,
  canon_inner P ->
  semi_canon P.
Proof with auto.
  intros. induction H...
Qed.

Lemma canon_outer_semi: forall P,
  canon_outer P ->
  semi_canon P.
Proof with auto.
  intros. induction H...
    apply canon_inner_semi...
    pick fresh X and apply semi_canon_new...
Qed.

(* Is this necessary? *)
Lemma proc_eq_par: forall P1 P2 P,
  proc_eq (proc_par P1 P2) P ->
  exists P1', exists P2', semi_canon P1' /\ semi_canon P2' /\
                                    proc_eq P (proc_par P1' P2').
Proof with auto.
  intros P1 P2 P Eq.
  assert (process P1 /\ process P2).
    apply proc_eq_regular in Eq. destruct Eq as [Eq Eq'].
    inversion Eq; subst...
  destruct H as [Proc1 Proc2].
  assert (exists P1', proc_eq P1 P1' /\ canon_outer P1').
    apply proc_canon...
  destruct H as [P1' [Eq1 Co1]]. exists P1'.
  assert (exists P2', proc_eq P2 P2' /\ canon_outer P2').
    apply proc_canon...
  destruct H as [P2' [Eq2 Co2]]. exists P2'.
  repeat split...
    apply canon_outer_semi...
    apply canon_outer_semi...
    apply eq_trans with (P2 := proc_par P1 P2)...
Qed.


(*Lemma proc_plug_regular: forall N P P',
  process P ->
  proc_plug N P P' ->
  process P'.
Proof with auto.
  intros N P P' HP HPp. induction HPp...
    pick fresh X and apply process_new...
    apply IHHPp in HP. unfold open_cp.
    rewrite <- open_cp_rec_process...
Qed.

Lemma proc_plug_semi: forall N P P',
  semi_canon P ->
  proc_plug N P P' ->
  semi_canon P'.
Proof with auto.
  intros N P P' SC PP. induction PP...
    pick fresh X and apply semi_canon_new...
    apply IHPP in SC. unfold open_cp.
    rewrite <- open_cp_rec_process...
    apply semi_canon_regular...
Qed.

Lemma proc_plug_exists: forall N P,
  exists P', proc_plug N P P'.
Proof with auto.
  intros. (sctx_cases (induction N) Case).
    Case "sctx_hole".
      exists P...
    Case "sctx_par".
      destruct IHN as [P' H]. exists (proc_par e P')...
    Case "sctx_new".
      destruct IHN as [P' H]. exists (proc_new T P')...
Qed.*)

(* ********************************************************************** *)
(** ** Progress (16) *)


Inductive done : proc -> Prop :=
  | done_exp : forall v Q T,
      value v ->
      typing empty lempty Q v T ->
      T <> typ_answer ->
      done (proc_exp v)
  | done_parl : forall P1 P2,
      done P1 ->
      done (proc_par P1 P2)
  | done_parr : forall P1 P2,
      done P2 ->
      done (proc_par P1 P2)
  | done_new : forall L T P1,
      (forall X : atom, X `notin` L -> done (open_cp P1 X)) ->
      done (proc_new T P1)
.

Inductive stuck : exp -> atom -> Prop := 
  | stuck_app : forall X T v,
      value v ->
      stuck (exp_app (exp_snk (fchan X) T) v) X
  | stuck_fst : forall X T,
      stuck (exp_fst (exp_snk (fchan X) T)) X
  | stuck_snd : forall X T,
      stuck (exp_snd (exp_snk (fchan X) T)) X
  | stuck_yield : forall X T,
      stuck (exp_yield (exp_src (fchan X) T)) X
  | stuck_seq : forall X e,
      expr e ->
      stuck (exp_seq (exp_src (fchan X) typ_answer) e) X
.

Inductive exp_stuck : exp -> Prop := 
  | exp_stuck_base : forall M e X f,
      stuck e X ->
      plug M e f ->
      exp_stuck f
  | exp_stuck_go : forall M T v f,
      value v ->
      plug M (exp_go T v) f ->
      exp_stuck f
.

Inductive proc_stuck : proc -> Prop := 
  | proc_stuck_base : forall M e X f,
      stuck e X ->
      plug M e f ->
      proc_stuck (proc_exp f)
  | proc_stuck_snk : forall X,
      proc_stuck (proc_exp (exp_snk (fchan X) typ_answer))
  | proc_stuck_done : forall X,
      proc_stuck (proc_exp (exp_done (fchan X)))
  | proc_stuck_par : forall P1 P2,
      proc_stuck P1 ->
      proc_stuck P2 ->
      proc_stuck (proc_par P1 P2)
  | proc_stuck_new : forall L T P1,
      (forall X : atom, X `notin` L ->
         proc_stuck (open_cp P1 X)) ->
      proc_stuck (proc_new T P1)
.

Lemma plug_trans: forall M1 M2 e f g,
  plug M1 e f ->
  plug M2 f g ->
  exists M3, plug M3 e g.
Proof with auto.
  intros M1 M2.
  (ectx_cases (induction M2) Case); intros e' f g Plug1 Plug2;
      inversion Plug2; subst; try (apply IHM2 with (e := e') in H3;
                                                 [destruct H3 as [M3 Plug'] | auto]);
                                           try (apply IHM2 with (e := e') in H0;
                                                 [destruct H0 as [M3 Plug'] | auto]).
    exists M1...
    exists (ectx_seq e M3 He0)...
    exists (ectx_appl e M3 He0)...
    exists (ectx_appr v Hv0 M3)...
    exists (ectx_fst M3)...
    exists (ectx_snd M3)...
    exists (ectx_mpairl e M3 He0)...
    exists (ectx_mpairr v Hv0 M3)...
    exists (ectx_let e M3 He0)...
    exists (ectx_inl T HT0 M3)...
    exists (ectx_inr T HT0 M3)...
    Case "ectx_case".
      apply IHM2 with (e := e') in H4...
      destruct H4 as [M3 Plug'].
      exists (ectx_case e2 e3 M3 He0 He1)...
    exists (ectx_go T HT0 M3)...
    exists (ectx_yield M3)...
Qed.

Lemma simple_progress: forall Q f1 T,
  typing empty lempty Q f1 T  ->
  value f1 \/ exp_stuck f1 \/ exists M, exists e1, exists f2, exists e2,
                                             plug M e1 f1 /\ plug M e2 f2 /\ red e1 e2.
Proof with auto.
  intros.
  remember Concur_Definitions.empty as E.
  remember lempty as D.
  revert HeqE HeqD.
  assert (typing E D Q f1 T) as Typ...
  (typing_cases (induction H) Case); intros; subst...
    Case "typing_var".
      inversion HeqD.
    Case "typing_seq".
      right. inversion H1. subst.
      lapply (IHtyping1 H (reflexivity empty))...
      lapply (IHtyping2 H0 (reflexivity empty))...
      intros. destruct H5 as
          [Val1 | [Stuck1 | [M [e1' [f2 [e2' [Plug1 [Plug2 Red]]]]]]]].
        apply canonical_form_unit with (Q := Q1) in Val1...
          destruct Val1 as [Eq | [X Eq]]; subst...
            right. exists ectx_hole. exists (exp_seq exp_unit e2).
              exists e2. exists e2. repeat split...
            left. apply exp_stuck_base with (X := X)
                (M := ectx_hole) (e := exp_seq (exp_src X typ_answer) e2)...
              apply stuck_seq...
        left. assert (expr e2)... inversion Stuck1; subst.
          apply plug_trans with
              (M2 := ectx_seq e2 ectx_hole H5) (g := exp_seq e1 e2) in H7...
            destruct H7 as [M3 Plug]. apply exp_stuck_base with (X := X) in Plug ...
          apply plug_trans with
              (M2 := ectx_seq e2 ectx_hole H5) (g := exp_seq e1 e2) in H7...
            destruct H7 as [M3 Plug]. apply exp_stuck_go in Plug...
        right. assert (expr e2)... exists (ectx_seq e2 M H5).
          exists e1'. exists (exp_seq f2 e2). exists e2'...
    Case "typing_app".
      right. inversion H1. subst.
      lapply (IHtyping1 H (reflexivity empty))...
      lapply (IHtyping2 H0 (reflexivity empty))...
      intros. destruct H5 as
          [Val1 | [Stuck1 | [M [e1' [f2 [e2' [Plug1 [Plug2 Red]]]]]]]].
        destruct H4 as 
            [Val2 | [Stuck2 | [M [e2' [e3 [e3' [Plug2 [Plug3 Red]]]]]]]].
          apply canonical_form_arrow with
              (Q := Q1) (T1 := T1) (T2 := T2) in Val1...
            destruct Val1 as [[e1' Eq] | [[X Eq] | [X [T3 [Eq Dual]]]]]; subst.
              right. exists ectx_hole. exists (exp_app (exp_abs T1 e1') e2).
                exists (open_ee e1' e2). exists (open_ee e1' e2).
                repeat split...
              left. apply exp_stuck_base with (X := X)
                  (M := ectx_hole) (e := exp_app (exp_snk X (typ_arrow T1 T2)) e2)...
                constructor...
              right. exists ectx_hole. exists (exp_app (exp_src X T3) e2).
                exists (exp_app e2 (exp_yield (exp_src X T3))).
                exists (exp_app e2 (exp_yield (exp_src X T3))).
                repeat split...
          inversion Stuck2; subst.
            apply plug_trans with
                (M2 := ectx_appr e1 Val1 ectx_hole ) (g := exp_app e1 e2) in H5...
              destruct H5 as [M3 Plug]. apply exp_stuck_base with (X := X) in Plug...
            apply plug_trans with
                (M2 := ectx_appr e1 Val1 ectx_hole) (g := exp_app e1 e2) in H5...
              destruct H5 as [M3 Plug]. apply exp_stuck_go in Plug...
          right. exists (ectx_appr e1 Val1 M). exists e2'.
            exists (exp_app e1 e3). exists e3'...
        left. assert (expr e2)... inversion Stuck1; subst.
          apply plug_trans with
              (M2 := ectx_appl e2 ectx_hole H5) (g := exp_app e1 e2) in H7...
            destruct H7 as [M3 Plug]. apply exp_stuck_base with (X := X) in Plug...
          apply plug_trans with
              (M2 := ectx_appl e2 ectx_hole H5) (g := exp_app e1 e2) in H7...
            destruct H7 as [M3 Plug]. apply exp_stuck_go in Plug...
        right. assert (expr e2)... exists (ectx_appl e2 M H5).
          exists e1'. exists (exp_app f2 e2). exists e2'...
    Case "typing_fst".
      right. lapply (IHtyping H (reflexivity empty))... intros.
      destruct H0 as [Val | [Stuck | [M [e' [e2 [e2' [Plug1 [Plug2 Red]]]]]]]].
        apply canonical_form_with with
            (Q := Q) (U1 := T1) (U2 := T2) in Val...
          destruct Val as [[e1 [e2 Eq]] | [X Eq]]; subst.
            right. exists ectx_hole. exists (exp_fst (exp_apair e1 e2)).
              exists e1. exists e1. repeat split...
            left. apply exp_stuck_base with (X := X)
                (M := ectx_hole) (e := exp_fst (exp_snk X (typ_with T1 T2)))...
              constructor...
        left. inversion Stuck; subst.
          apply plug_trans with
              (M2 := ectx_fst ectx_hole) (g := exp_fst e) in H1...
            destruct H1 as [M3 Plug]. apply exp_stuck_base with (X := X) in Plug...
          apply plug_trans with
              (M2 := ectx_fst ectx_hole) (g := exp_fst e) in H1...
            destruct H1 as [M3 Plug]. apply exp_stuck_go in Plug...
        right. exists (ectx_fst M). exists e'. exists (exp_fst e2). exists e2'...
    Case "typing_snd".
      right. lapply (IHtyping H (reflexivity empty))... intros.
      destruct H0 as [Val | [Stuck | [M [e' [e2 [e2' [Plug1 [Plug2 Red]]]]]]]].
        apply canonical_form_with with
            (Q := Q) (U1 := T1) (U2 := T2) in Val...
          destruct Val as [[e1 [e2 Eq]] | [X Eq]]; subst.
            right. exists ectx_hole. exists (exp_snd (exp_apair e1 e2)).
              exists e2. exists e2. repeat split...
            left. apply exp_stuck_base with (X := X)
                (M := ectx_hole) (e := exp_snd (exp_snk X (typ_with T1 T2)))...
              constructor...
        left. inversion Stuck; subst.
          apply plug_trans with
              (M2 := ectx_snd ectx_hole) (g := exp_snd e) in H1...
            destruct H1 as [M3 Plug]. apply exp_stuck_base with (X := X) in Plug...
          apply plug_trans with
              (M2 := ectx_snd ectx_hole) (g := exp_snd e) in H1...
            destruct H1 as [M3 Plug]. apply exp_stuck_go in Plug...
        right. exists (ectx_snd M). exists e'. exists (exp_snd e2). exists e2'...
    Case "typing_mpair".
      inversion H1. subst.
      lapply (IHtyping1 H (reflexivity empty))...
      lapply (IHtyping2 H0 (reflexivity empty))...
      intros. destruct H5 as
          [Val1 | [Stuck1 | [M [e1' [f2 [e2' [Plug1 [Plug2 Red]]]]]]]].
        destruct H4 as 
            [Val2 | [Stuck2 | [M [e2' [e3 [e3' [Plug2 [Plug3 Red]]]]]]]].
          left...
          right. left. inversion Stuck2; subst.
            apply plug_trans with
                (M2 := ectx_mpairr e1 Val1 ectx_hole ) (g := exp_mpair e1 e2) in H5...
              destruct H5 as [M3 Plug]. apply exp_stuck_base with (X := X) in Plug...
            apply plug_trans with
                (M2 := ectx_mpairr e1 Val1 ectx_hole) (g := exp_mpair e1 e2) in H5...
              destruct H5 as [M3 Plug]. apply exp_stuck_go in Plug...
          right. right. exists (ectx_mpairr e1 Val1 M). exists e2'.
            exists (exp_mpair e1 e3). exists e3'...
        right. left. assert (expr e2)... inversion Stuck1; subst.
          apply plug_trans with
              (M2 := ectx_mpairl e2 ectx_hole H5) (g := exp_mpair e1 e2) in H7...
            destruct H7 as [M3 Plug]. apply exp_stuck_base with (X := X) in Plug...
          apply plug_trans with
              (M2 := ectx_mpairl e2 ectx_hole H5) (g := exp_mpair e1 e2) in H7...
            destruct H7 as [M3 Plug]. apply exp_stuck_go in Plug...
        right. right. assert (expr e2)... exists (ectx_mpairl e2 M H5).
          exists e1'. exists (exp_mpair f2 e2). exists e2'...
    Case "typing_let".
      right. inversion H1. subst.
      lapply (IHtyping1 H (reflexivity empty))...
      lapply (IHtyping2 H0 (reflexivity empty))...
      intros. destruct H5 as
          [Val1 | [Stuck1 | [M [e1' [f2 [e2' [Plug1 [Plug2 Red]]]]]]]].
        destruct (canonical_form_tensor e1 Q1 T1 T2) as [e3 [e4 Eq]]...
          subst. right. exists ectx_hole.
            exists (exp_let (exp_mpair e3 e4) e2).
            exists (exp_app (exp_app e2 e3) e4).
            exists (exp_app (exp_app e2 e3) e4).
            repeat split...
        left. assert (expr e2)... inversion Stuck1; subst.
          apply plug_trans with
              (M2 := ectx_let e2 ectx_hole H5) (g := exp_let e1 e2) in H7...
            destruct H7 as [M3 Plug]. apply exp_stuck_base with (X := X) in Plug...
          apply plug_trans with
              (M2 := ectx_let e2 ectx_hole H5) (g := exp_let e1 e2) in H7...
            destruct H7 as [M3 Plug]. apply exp_stuck_go in Plug...
        right. assert (expr e2)... exists (ectx_let e2 M H5).
          exists e1'. exists (exp_let f2 e2). exists e2'...
    Case "typing_inl".
      assert (type (typ_plus T1 T2))...
      lapply (IHtyping H (reflexivity empty))... intros.
      destruct H1 as [Val | [Stuck | [M [e' [e2 [e2' [Plug1 [Plug2 Red]]]]]]]].
        left...
        right. left. inversion Stuck; subst.
          apply plug_trans with
              (M2 := ectx_inl (typ_plus T1 T2) H0 ectx_hole)
              (g := exp_inl (typ_plus T1 T2) e1) in H2...
            destruct H2 as [M3 Plug]. apply exp_stuck_base with (X := X) in Plug...
          apply plug_trans with
              (M2 := ectx_inl (typ_plus T1 T2) H0 ectx_hole)
              (g := exp_inl (typ_plus T1 T2) e1) in H2...
            destruct H2 as [M3 Plug]. apply exp_stuck_go in Plug...
        right. right. exists (ectx_inl (typ_plus T1 T2) H0 M). exists e'.
          exists (exp_inl (typ_plus T1 T2) e2). exists e2'...
    Case "typing_inr".
      assert (type (typ_plus T1 T2))...
      lapply (IHtyping H (reflexivity empty))... intros.
      destruct H1 as [Val | [Stuck | [M [e' [e3 [e3' [Plug1 [Plug2 Red]]]]]]]].
        left...
        right. left. inversion Stuck; subst.
          apply plug_trans with
              (M2 := ectx_inr (typ_plus T1 T2) H0 ectx_hole)
              (g := exp_inr (typ_plus T1 T2) e2) in H2...
            destruct H2 as [M3 Plug]. apply exp_stuck_base with (X := X) in Plug...
          apply plug_trans with
              (M2 := ectx_inr (typ_plus T1 T2) H0 ectx_hole)
              (g := exp_inr (typ_plus T1 T2) e2) in H2...
            destruct H2 as [M3 Plug]. apply exp_stuck_go in Plug...
        right. right. exists (ectx_inr (typ_plus T1 T2) H0 M). exists e'.
          exists (exp_inr (typ_plus T1 T2) e3). exists e3'...
    Case "typing_case".
      right. inversion H2. subst.
      lapply (IHtyping1 H (reflexivity empty))...
      lapply (IHtyping2 H0 (reflexivity empty))...
      lapply (IHtyping3 H1 (reflexivity empty))...
      intros. destruct H7 as
          [Val1 | [Stuck1 | [M [e1' [f2 [e2' [Plug1 [Plug2 Red]]]]]]]].
        destruct (canonical_form_plus e1 Q1 T1 T2) as [[e4 Eq] | [e4 Eq]];
            auto; subst; right; exists ectx_hole.
          exists (exp_case (exp_inl (typ_plus T1 T2) e4) e2 e3).
            exists (exp_app e2 e4). exists (exp_app e2 e4). repeat split...
          exists (exp_case (exp_inr (typ_plus T1 T2) e4) e2 e3).
            exists (exp_app e3 e4). exists (exp_app e3 e4). repeat split...
        left. assert (expr e2)... assert (expr e3)... inversion Stuck1; subst.
          apply plug_trans with
              (M2 := ectx_case e2 e3 ectx_hole H7 H8)
              (g := exp_case e1 e2 e3) in H10...
            destruct H10 as [M3 Plug]. apply exp_stuck_base with (X := X) in Plug...
          apply plug_trans with
              (M2 := ectx_case e2 e3 ectx_hole H7 H8)
              (g := exp_case e1 e2 e3) in H10...
            destruct H10 as [M3 Plug]. apply exp_stuck_go in Plug...
        right. assert (expr e2)... assert (expr e3)... 
          exists (ectx_case e2 e3 M H7 H8).
          exists e1'. exists (exp_case f2 e2 e3). exists e2'...
    Case "typing_go".
      right. apply IHtyping in H...
      destruct H as [Val | [Stuck | [M [e1' [f2 [e2' [Plug1 [Plug2 Red]]]]]]]].
        left. apply exp_stuck_go with (M := ectx_hole) (T := T1) (v := e1)...
        left. assert (type T1)... inversion Stuck; subst.
          apply plug_trans with
              (M2 := ectx_go T1 H ectx_hole)
              (g := exp_go T1 e1) in H2...
            destruct H2 as [M3 Plug]. apply exp_stuck_base with (X := X) in Plug...
          apply plug_trans with
              (M2 := ectx_go T1 H ectx_hole)
              (g := exp_go T1 e1) in H2...
            destruct H2 as [M3 Plug]. apply exp_stuck_go in Plug...
      right. assert (type T1)... exists (ectx_go T1 H M). exists e1'.
        exists (exp_go T1 f2). exists e2'...
    Case "typing_yield".
      right. apply IHtyping in H...
      destruct H as [Val | [Stuck | [M [e1' [f2 [e2' [Plug1 [Plug2 Red]]]]]]]].
        inversion Typ; subst. apply canonical_form_arrow in H3...
          destruct H3 as [[e0 Eq] | [[X Eq] | [X [T [Eq Dual]]]]]; subst.
            right. exists ectx_hole.
              exists (exp_yield (exp_abs (typ_arrow T1 typ_answer) e0)).
              exists (exp_app
                           (exp_abs (typ_tensor T1 typ_unit) (exp_let (exp_bvar 0)
                              (exp_abs T1 (exp_abs typ_unit
                                 (exp_seq (exp_bvar 0) (exp_bvar 1))))))
                           (exp_yield (exp_go (typ_arrow T1 typ_answer)
                              (exp_abs (typ_arrow T1 typ_answer) e0)))).
              exists (exp_app
                           (exp_abs (typ_tensor T1 typ_unit) (exp_let (exp_bvar 0)
                              (exp_abs T1 (exp_abs typ_unit
                                 (exp_seq (exp_bvar 0) (exp_bvar 1))))))
                           (exp_yield (exp_go (typ_arrow T1 typ_answer)
                              (exp_abs (typ_arrow T1 typ_answer) e0))))...
            right. exists ectx_hole.
              exists (exp_yield (exp_snk X (typ_src T1))).
              exists (exp_app
                           (exp_abs (typ_tensor T1 typ_unit) (exp_let (exp_bvar 0)
                              (exp_abs T1 (exp_abs typ_unit
                                 (exp_seq (exp_bvar 0) (exp_bvar 1))))))
                           (exp_yield (exp_go (typ_arrow T1 typ_answer)
                              (exp_snk X (typ_src T1))))).
              exists (exp_app
                           (exp_abs (typ_tensor T1 typ_unit) (exp_let (exp_bvar 0)
                              (exp_abs T1 (exp_abs typ_unit
                                 (exp_seq (exp_bvar 0) (exp_bvar 1))))))
                           (exp_yield (exp_go (typ_arrow T1 typ_answer)
                              (exp_snk X (typ_src T1))))). repeat split...
            left. apply exp_stuck_base with (X := X) (M := ectx_hole)
                (e := exp_yield (exp_src X T))...
              constructor...
        left. inversion Stuck; subst.
          apply plug_trans with
              (M2 := ectx_yield ectx_hole)
              (g := exp_yield e1) in H0...
            destruct H0 as [M3 Plug]. apply exp_stuck_base with (X := X) in Plug...
          apply plug_trans with
              (M2 := ectx_yield ectx_hole)
              (g := exp_yield e1) in H0...
            destruct H0 as [M3 Plug]. apply exp_stuck_go in Plug...
      right. exists (ectx_yield M). exists e1'.
        exists (exp_yield f2). exists e2'...
Qed.

Lemma proc_simple_progress: forall Qs P1 T,
  proc_typing Qs P1 T  ->
  done P1 \/ proc_stuck P1 \/ exists P1', exists P2',
                                               proc_eq P1 P1' /\ proc_red P1' P2'.
Proof with auto.
  intros. assert (proc_typing Qs P1 T) as PTyp...
  (proc_typing_cases (induction H) Case).
    Case "typing_exp".
      lapply (simple_progress Q e T)... intros.
      destruct H1 as [Val | [Stuck | [M [e' [e2 [e2' [Plug1 [Plug2 Red]]]]]]]].
        remember T as T'. destruct T; try solve
            [ left; apply done_exp with (Q := Q) (T := T');
              subst; auto; intuition; inversion H1 ]; subst.
          right. left. inversion H; subst; inversion Val; subst.
            constructor...
            inversion H2.
            constructor...
        inversion Stuck; subst.
          right. left. apply proc_stuck_base with (X := X) in H2...
          right. right. exists e.
            assert (exists f, plug M (exp_src (bchan 0) T0) f).
              apply plug_exists...
            destruct H3 as [f Plug].
            exists (proc_new T0 (proc_par f (exp_app v (exp_snk (bchan 0) T0)))).
            split...
              apply red_go with (M := M)...
        right. right. exists e. exists e2. split...
          econstructor; eauto.
    Case "typing_parl".
      lapply IHproc_typing1... lapply IHproc_typing2... intros.
      destruct H3 as [Done1 | [Stuck1 | [P1' [P1'' [Eq1 Red1]]]]].
        left. apply done_parl...
        destruct H2 as [Done2 | [Stuck2 | [P2' [P2'' [Eq2 Red2]]]]].
          left. apply done_parr...
          right. left. apply proc_stuck_par...
          right. right. exists (proc_par P1 P2').
            exists (proc_par P1 P2'')...
        right. right. exists (proc_par P2 P1').
          exists (proc_par P2 P1'')...
    Case "typing_parr".
      lapply IHproc_typing1... lapply IHproc_typing2... intros.
      destruct H3 as [Done1 | [Stuck1 | [P1' [P1'' [Eq1 Red1]]]]].
        left. apply done_parl...
        destruct H2 as [Done2 | [Stuck2 | [P2' [P2'' [Eq2 Red2]]]]].
          left. apply done_parr...
          right. left. apply proc_stuck_par...
          right. right. exists (proc_par P1 P2').
            exists (proc_par P1 P2'')...
        right. right. exists (proc_par P2 P1').
          exists (proc_par P2 P1'')...
    Case "typing_new".
      pick fresh X. assert (X `notin` L)...
      lapply (H1 X)... lapply (H2 X H3)... intros.
      destruct H4 as [Done | [Stuck | [P1' [P2' [Eq Red]]]]].
        left. pick fresh Y and apply done_new... skip.
        right. left. pick fresh Y and apply proc_stuck_new... skip.
        right. right. exists (proc_new T1 (close_cp P1' X)).
          exists (proc_new T1 (close_cp P2' X)). split...
            pick fresh Y and apply eq_new...
              assert (fv_cp (open_cp P1 X)[=]fv_cp P1').
                apply fv_cp_proc_eq...
              apply proc_eq_rename with (Y := X)...
                apply notin_union...
                  apply fv_close_cp...
                apply notin_union...
                  unfold close_cp. apply notin_close_cp...
              fold (open_cp (close_cp P1' X) X). fold (open_cp P1 X).
                rewrite open_close_cp...
            pick fresh Y and apply red_new...
              pick fresh Y and apply process_new...
                unfold open_cp. apply process_rename with (X := X)...
                fold (open_cp (close_cp P1' X) X). rewrite open_close_cp...
              apply proc_red_rename with (Y := X)...
                apply notin_union; apply fv_close_cp.
                apply notin_union; apply notin_close_cp...
                unfold close_cp. repeat rewrite open_close_cp_rec...
Qed.


(*

Think about the pigeon hole principle...


X Y.    (?Y;!X  | ?X ) | !Y 

         [X, Y]
         
      [?Y,X ][!Y]
         
  [!X,?Y]  [?X] [!Y]
      

  (Stuck(?Y)  |X Stuck(?X)) |Y Stuck(!Y)


(e(X) | f(Y)) | (g(!A) | h(!B))
   A      B        !X      !Y


new X1 ... new Xn. ( e1 | (e2 | ( ... | en)))

push Z to right =>

new X ... new Z. (e1 | (e2 | (... | en)))   and eq_proc P this

L = (e1 | (e2 | (... | en)))


match L with
 | e1 -> impossible (contradicts typing)
 | e1 | (e2 | R) ->   if Z is in e1 then e1 | pull_Z_to_front R
                

new X ... newZ . (e1(Z) | (e2(Z) | R))

==reassoc

new X ... newZ . (e1(Z) | e2(Z)) | R 


canon P,  Z   --->  exists P', super_canon Z P' /\ eq_proc P P'

*)

Inductive balance : env -> cenv -> Prop := 
  | balance_empty : forall E,
      wf_env E ->
      balance E cempty
  | balance_both : forall E Q X T,
      balance E Q ->
      X `notin` dom E ->
      X `notin` dom Q ->
      wf_proto E T ->
      balance E ([(X, cbind_proto cdir_both T)] ++ Q)
.

Inductive balances : env -> cenvs -> Prop :=
  | balances_csm : forall E Qs Q Z,
      cenv_split_multi E Qs Q Z ->
      balance E Q ->
      balances E Qs
.

Lemma canon_inner_progress: forall Qs P T,
  proc_typing Qs P T ->
  balances empty Qs ->
  canon_inner P ->
  proc_stuck P ->
  exists P', exists P'', proc_eq P P' /\ proc_red P' P''.
Proof with auto.
Admitted.

Lemma canon_outer_progress: forall Qs P T,
  proc_typing Qs P T ->
  balances empty Qs ->
  canon_outer P ->
  proc_stuck P ->
  exists P', exists P'', proc_eq P P' /\ proc_red P' P''.
Proof with auto.
Admitted.

Lemma proc_stuck_rename: forall P X Y i,
  Y `notin` fv_cp P ->
  X `notin` fv_cp P ->
  proc_stuck (open_cp_rec i Y P) ->
  proc_stuck (open_cp_rec i X P).
Proof.
  intros P X Y i NI1 NI2 Stuck.
  remember (open_cp_rec i Y P) as P'. generalize dependent P.
  revert X Y i. induction Stuck; intros.
    (* Sub-lemma shouldn't be too hard, but maybe do this later? *)
Admitted.

Lemma eq1_stuck: forall P1 P2,
  proc_stuck P1 ->
  proc_eq1 P1 P2 ->
  proc_stuck P2.
Proof with auto.
  intros P1 P2 Stuck. revert P2.
  induction Stuck; intros P' Eq; inversion Eq; subst;
      try solve [constructor; auto].
    inversion Stuck1. subst. constructor...
      constructor...
    pick fresh X and apply proc_stuck_new.
      lapply (H X)... lapply (H4 X)... intros...
      apply H0 with (X := X)...
    pick fresh Z. lapply (H Z)... intros. inversion H1. subst.
      pick fresh X and apply proc_stuck_new.
      pick fresh Y and apply proc_stuck_new.
      fold open_cp_rec. rewrite <- H4...
      lapply (H3 X)... intros.
      unfold open_cp in H2. rewrite open_cp_open_cp_comm in H2...
      unfold open_cp. rewrite open_cp_open_cp_comm...
      apply proc_stuck_rename with (Y := Z)...
        

Lemma proc_stuck_progress: forall P T,
  proc_typing lcempty P T ->
  proc_stuck P ->
  exists P', exists P'', proc_eq P P' /\ proc_red P' P''.
Proof with auto.
  intros P T Typ Stuck.
  destruct (proc_canon P) as [P' [Eq Can]].
    apply proc_typing_regular in Typ. intuition...
  apply canon_outer_progress with (Qs := lcempty) (T := T) in Can...
    destruct Can as [P'' [P''' [Eq' Red]]].
      exists P''. exists P'''. split...
      apply eq_trans with (P2 := P')...
    apply eq_preservation with (P1 := P)...
    apply balances_csm with (Q := cempty) (Z := None)...
      apply balance_empty...
    
Admitted.

Lemma proc_progress: forall P T,
  proc_typing lcempty P T ->
  done P \/ exists P', exists P'', proc_eq P P' /\ proc_red P' P''.
Proof with auto.
  intros P T Typ.
  lapply (proc_simple_progress lcempty P T)... intros.
  destruct H as [Done | [Stuck | [P' [P'' [Eq Red]]]]].
    left...
    right. apply proc_stuck_progress in Typ...
    right. exists P'. exists P''...
Qed.