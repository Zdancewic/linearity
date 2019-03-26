(** Type-safety proofs for Algorithmic Lightweight Linear F

    Authors: Aileen Zhang, Jianzhou Zhao, and Steve Zdancewic.

    In parentheses are given the label of the corresponding lemma in
    the appendix (informal proofs) of the POPLmark Challenge.

    Table of contents:
      - #<a href="##typing">Properties of typing</a>#
      - #<a href="##preservation">Preservation</a>#
      - #<a href="##progress">Progress</a># *)

Require Export ALinearF_Lemmas.
Require Import Omega.
Require Import Tactics.


(* ********************************************************************** *)
(** ** Weakening *)

(**
Lemma atyping_lin_weakening: forall G D2 D1 e T D2' D1' D,
  atyping G (D2 ++ D1) e T (D2' ++ D1') ->
  wf_denv G (D2 ++ D ++ D1) ->
  atyping G (D2 ++ D++ D1) e T (D2' ++ D ++ D1').
Proof with simpl_env; eauto.
  intros G D2 D1 e T D2' D1' D TypT Wfd. remember (D2 ++ D1) as E1. remember (D2' ++ D1') as E2.
  generalize dependent D.
  induction TypT; intros DD Wfd; subst... Admitted. 
 Case "atyping_lvar".  assert (x `in` dom D). eapply binds_In. eauto. 
   assert (x `notin` dom E1 /\ x `notin` dom E2). eapply wf_denv_fv_disj3. eauto. auto. destruct H2.
   apply minus_notin in H2. apply minus_notin in H3. assert (E2 ++ (D [-] x) ++ E1 = (E2 [-]x) ++ (D [-] x) ++ (E1 [-]x)).
   rewrite <- H2. rewrite <-H3... rewrite H4. rewrite <- minus_distr. rewrite <- minus_distr. 
   apply atyping_lvar. apply binds_weaken_at_head... eapply ok_from_wf_denv. eauto. auto.
  Case "atyping_uabs". 
    pick fresh y and apply atyping_uabs... apply H1... eapply wf_denv_weakening2...
    assert (wf_genv G). eapply wf_genv_from_wf_denv. eauto. apply wf_genv_typ...
    intros. apply H2 in H3. rewrite H3...
  Case "atyping_labs". 
   assert (atyping G  (D ++ E1) (exp_abs K V e1) (typ_arrow K V T1)  ( D' ++ E1)).
   pick fresh y and apply atyping_labs... rewrite () 
 *)

Lemma eq_denv_tail: forall (E2:denv) F2 Y,
  [Y] ++ E2 = [Y] ++ F2 ->
  E2 = F2.
Proof.
  induction E2; intros.
  simpl in H. inversion H. auto.
  destruct F2.
  simpl in H. inversion H.
  simpl in H. inversion H. subst. auto.
Qed.
Lemma eq_denv_concat1: forall (E1 : denv)  E2 F1 F2,
  E1 = F1 -> 
  E1 ++ E2 = F1 ++ F2 ->
  E2 = F2.
Proof.
  intros. subst.
  induction F1. simpl in H0. auto.
  apply IHF1. rewrite_env ([a]++(F1 ++ E2)) in H0.
  rewrite_env ([a]++(F1 ++ F2)) in H0.
  eapply eq_denv_tail. apply H0.
Qed.

Lemma eq_denv_concat2: forall (E1 :denv) E2 F1 F2,
  E2 = F2 -> 
  E1 ++ E2 = F1 ++ F2 ->
  E1 = F1.
Proof.
  intros.
  assert (rev (E1 ++ E2) = rev (F1 ++ F2)).
  rewrite H0. auto.
  rewrite distr_rev in H1. rewrite distr_rev in H1.
  assert (rev E1 = rev F1).
  eapply eq_denv_concat1. assert (rev E2 = rev F2). rewrite H. auto.
  eapply H2. auto. rewrite <- rev_involutive. rewrite <- (rev_involutive E1).
  rewrite H2. auto.
Qed.

Lemma eq_minus_notin : forall G D2 D2' D1 x,
  wf_denv G (D2 ++ D1) ->
  (D2 ++ D1[-] x) = D2' ++ D1 ->
  x `notin` dom D1.
Proof with simpl_env; eauto.
 intros G D2 D2' D1 x Wfd EQ. generalize dependent D2'. generalize dependent x. generalize dependent D2.
 induction D1; intros; subst. fsetdec. destruct a. simpl_env in EQ. 
 destruct (x == a). subst. assert (a `in` dom (D2' ++ [(a,d)] ++ D1)). 
 simpl_env. fsetdec. rewrite <- EQ in H.  assert (a `notin` dom (D2++[(a,d)] ++ D1[-]a)). apply dom_dminus_var_notin .
 fsetdec. assert( x `notin` AtomSet.F.singleton a). fsetdec. 
 assert (x `notin` dom D1). eapply IHD1. simpl_env in Wfd. rewrite  <- concat_assoc in Wfd. eauto.
 rewrite  <- concat_assoc in EQ. rewrite  <- concat_assoc in EQ. eauto. simpl. fsetdec.
Qed.

Lemma eq_minus_notin2 : forall G D2 D1 D1' x,
  wf_denv G (D2 ++ D1) ->
  (D2 ++ D1 [-] x) = D2 ++ D1' ->
   x `notin` dom D2.
Proof with simpl_env; eauto.
 intros G D2 D1 D1' x Wfd EQ. generalize dependent D1'. generalize dependent x.
 induction D2; intros; subst. fsetdec. destruct a. simpl_env in EQ. simpl in EQ. 
 destruct (x == a). subst. simpl_env in EQ. assert (a `in` dom ([(a,d)] ++ D2 ++ D1')). 
 simpl_env. fsetdec. rewrite <- EQ in H.  assert (a `notin` dom (D2++D1[-]a)). apply dom_dminus_var_notin .
 fsetdec. simpl_env in EQ. apply eq_denv_tail in EQ. simpl. assert( x `notin` AtomSet.F.singleton a). fsetdec.
 assert (x `notin` dom D2). eapply IHD2. simpl_env in Wfd. inversion Wfd; subst... eauto. fsetdec.
Qed.

Lemma atyping_lin_post : forall G D2 D1 e T D,
  atyping G (D2 ++ D1) e T D ->
  exists D2', exists  D1', D = D2' ++ D1'.
Proof with simpl_env; eauto.
  intros G D2 D1 e T D TypT. remember (D2 ++ D1) as E1. generalize dependent D2.
  generalize dependent D1. induction TypT; intros; subst...
  Case "lvar". binds_cases H. exists D2. exists (D1[-]x). apply sym_eq. apply minus_assoc...
    exists (D2[-]x). exists D1. apply binds_In in H2. assert (x `notin` dom D1). eapply wf_denv_fv_disj2. eauto. auto.
    apply sym_eq. apply minus_assoc2...
  Case "uabs". pick fresh y. eapply (H1 y). fsetdec. eauto.
  Case "labs". pick fresh y. eapply (H1 y). fsetdec. eauto.
  Case "app". assert (exists D2', exists D1', D2 = D2' ++ D1'). eapply IHTypT1. eauto. destruct H as [D2' [D1' H1]].
   eapply IHTypT2. eauto.
  Case "tabs". pick fresh Y. eapply (H1 Y). fsetdec. eauto.
Qed.


Lemma atyping_lin_weakening: forall G D2 D1 e T D2' D1' D,
  atyping G (D2 ++ D1) e T (D2' ++ D1') ->
  wf_denv G (D2 ++ D ++ D1) ->
  atyping G (D2 ++ D++ D1) e T (D2' ++ D ++ D1').
Proof with simpl_env; eauto. Admitted. (*
  intros G D2 D1 e T D2' D1' D TypT Wfd.
  generalize dependent D. remember (D2 ++ D1) as E1. remember (D2' ++ D1') as E2. generalize dependent D2.
  generalize dependent D1. generalize dependent D2'. generalize dependent D1'.
  induction TypT; intros; subst... 
  Case "uvar".  assert (D1 = D1)... assert (D2' = D2). eapply eq_denv_concat2. apply H1. auto.
   rewrite H2. apply atyping_uvar...
Lemma atyping_lin_weakening1: forall G D2 D1 e T D2' D,
  atyping G (D2 ++ D1) e T (D2' ++ D1) ->
  wf_denv G (D2 ++ D ++ D1) ->
  atyping G (D2 ++ D++ D1) e T (D2' ++ D ++ D1).
Proof with simpl_env; eauto.
  intros G D2 D1 e T D2' D TypT Wfd.
  generalize dependent D. remember (D2 ++ D1) as E1. remember (D2' ++ D1) as E2. generalize dependent D2.
  generalize dependent D1. generalize dependent D2'.
  induction TypT; intros; subst... 
  Case "uvar". assert (D1 = D1)... assert (D2' = D2). eapply eq_denv_concat2. apply H1. auto.
   rewrite H2. apply atyping_uvar...
  Case "lvar".  assert (x `notin` dom D1). eapply eq_minus_notin. apply H0. eauto.
    rewrite  minus_distr in HeqE2. assert (D1 = (D1[-] x)). apply minus_notin... rewrite <- H2 in HeqE2.
    assert (D1 = D1)... assert ((D2[-] x) = D2'). eapply eq_denv_concat2. apply H3. auto. rewrite <- H4.
    assert (binds x (dbind_typ T) (D2 ++ D0 ++ D1)). apply binds_weaken. auto. eapply ok_from_wf_denv. eauto.
    binds_cases H... apply binds_In in H6. fsetdec.
    apply binds_In in H7.
    assert (x `notin` dom (D0 ++ D1)). eapply wf_denv_fv_disj2 . eauto. auto. assert (D0 ++ D1 = ((D0 ++ D1) [-]x)).
    apply minus_notin. auto. assert ((D2[-]x) ++ D0 ++ D1 = ((D2[-]x) ++ (D0 ++ D1 [-]x))). rewrite <- H6...
    rewrite H8. rewrite <- minus_distr. apply atyping_lvar...
  Case "uabs". pick fresh y and apply atyping_uabs... apply H1... apply wf_denv_weakening2... 
    apply wf_genv_typ. eapply wf_genv_from_wf_denv. eauto. auto. auto. intros. apply H2 in H3. 
    assert (D1 = D1)... assert (D2 = D2'). eapply eq_denv_concat2. apply H4. auto. rewrite H5...
  Case "labs".  pick fresh y and apply atyping_labs... rewrite_env (([(y, dbind_typ V)] ++ D2) ++ D0 ++ D1). apply H1...
   intros. apply H2 in H3. assert (D1 = D1)... assert (D2 = D2').  eapply eq_denv_concat2. apply H4. auto. rewrite H5...
  Case "app".  eapply atyping_app.  apply IHTypT1. *)
   



Lemma atyping_nonlin_weakening: forall G2 G1 D e T D' G,
  atyping (G2 ++ G1) D e T D' ->
  wf_denv (G2 ++ G ++ G1) D ->
  atyping (G2 ++ G++ G1) D e T D'.
Admitted.

Lemma atyping_nonlin_weakening2 : forall G1 G D e T D',
  atyping G1 D e T D' ->
  wf_denv (G ++ G1) D ->
  atyping (G ++ G1) D e T D'.
Proof.
  intros. rewrite_env (gempty ++ G ++ G1). rewrite_env (gempty ++ G ++ G1) in H0.
  apply atyping_nonlin_weakening. auto. auto.
Qed. 


(* ********************************************************************** *)
(** ** Strengthening *)

Lemma atyping_lin_strengthening: forall G D2 D1 x T1 e T2 D ,
  atyping G (D2 ++ [(x, dbind_typ T1)] ++ D1) e T2 D ->
  x `notin` fv_ee e ->
  atyping G (D2 ++  D1) e T2 (dminus_var x D).
Admitted.

(************************************************************************ *)
(** ** Type substitution preserves typing *)

Lemma value_through_subst_te : forall e Z P,
  type P ->
  value e ->
  value (subst_te Z P e).
Admitted.

Lemma atyping_through_subst_te : forall K K' E F D Z e T D' P,
  atyping (F ++ [(Z, gbind_kn K)] ++ E) D e T D' ->
  wf_atyp E P K' ->
  kn_order K' K ->
  atyping (map (subst_tgb Z P) F ++ E) 
               (map (subst_tdb Z P) D)
               (subst_te Z P e) 
               (subst_tt Z P T) 
               (map (subst_tdb Z P) D').
Admitted.
       
(************************************************************************ *)
(** ** Substitution preserves typing *)

Lemma value_through_open_te: forall e1 T,
  value e1 ->
  value (open_te e1 T).
Proof.
  intros.
  unfold open_te. rewrite <- open_te_rec_expr. auto. inversion H. auto. auto.
Qed.

Lemma value_through_subst_ee : forall e e' x,
  value e ->
  expr e' ->
  value (subst_ee x e' e).
Proof.
  intros e e' x Hv He.
  induction Hv; intros; simpl; auto.
    inversion H; subst.
    apply value_abs.
        apply expr_abs with (L:=L `union` singleton x); auto.
        intros. rewrite subst_ee_open_ee_var; auto.

    inversion H; subst.
    apply value_tabs.
        apply expr_tabs with (L:=L `union` singleton x); auto.
        intros. rewrite subst_ee_open_te_var; auto.
Qed.
(** 
Lemma atyping_denv_mono : forall G D1 D2 D3  u T,
  atyping G D1 u T D2 ->
  wf_denv G (D3 ++ D1) ->
  atyping G (D3 ++ D1) u T (D3 ++ D2).
Proof with simpl_env; eauto.
  intros G D1 D2 D3 u T TypT Wfd.
  generalize dependent D3. induction TypT; intros E3 Wfd; subst...
  Case "atyping_lvar".  assert (x `in` dom D). eapply binds_In. eauto. 
   assert (x `notin` dom E3). eapply wf_denv_fv_disj. eauto. auto. apply minus_notin in H2.
   assert (E3 ++ (D [-] x) = ((E3[-]x) ++(D[-]x))). rewrite <- H2... rewrite H3. rewrite <- minus_distr.
   apply atyping_lvar. apply binds_weaken_at_head... eapply ok_from_wf_denv. eauto. auto.
  Case "atyping_uabs". 
   pick fresh y and apply atyping_uabs... apply H1... eapply wf_denv_weakening2...
    assert (wf_genv G). eapply wf_genv_from_wf_denv. eauto. apply wf_genv_typ...
    intros. apply H2 in H3. rewrite H3...
  Case "atyping_labs". 
    
Lemma atyping_denv_mono2 : forall G D1 D2 D3 D4  u T,
  atyping G D1 u T D2 ->
  wf_denv G (D3 ++ D1 ++ D4) ->
  atyping G (D3 ++ D1++ D4) u T (D3 ++ D2 ++ D4).
Proof with simpl_env; eauto.
  intros G D1 D2 D3 D4 u T TypT Wfd. 
  generalize dependent D3. generalize dependent D4.
  induction TypT; intros E1 E2 Wfd; subst...
  Case "atyping_lvar".  assert (x `in` dom D). eapply binds_In. eauto. 
   assert (x `notin` dom E1 /\ x `notin` dom E2). eapply wf_denv_fv_disj3. eauto. auto. destruct H2.
   apply minus_notin in H2. apply minus_notin in H3. assert (E2 ++ (D [-] x) ++ E1 = (E2 [-]x) ++ (D [-] x) ++ (E1 [-]x)).
   rewrite <- H2. rewrite <-H3... rewrite H4. rewrite <- minus_distr. rewrite <- minus_distr. 
   apply atyping_lvar. apply binds_weaken_at_head... eapply ok_from_wf_denv. eauto. auto.
  Case "atyping_uabs". 
    pick fresh y and apply atyping_uabs... apply H1... eapply wf_denv_weakening2...
    assert (wf_genv G). eapply wf_genv_from_wf_denv. eauto. apply wf_genv_typ...
    intros. apply H2 in H3. rewrite H3...
  Case "atyping_labs". 
   assert (atyping G  (D ++ E1) (exp_abs K V e1) (typ_arrow K V T1)  ( D' ++ E1)).
   pick fresh y and apply atyping_labs... rewrite_env (dempty ++ ([(y, dbind_typ V)] ++ D) ++ E1).
    rewrite_env (dempty ++ D' ++ E1). apply H1... assert (wf_denv G (D ++ E1)).
    eapply wf_denv_lin_strengthening3. eauto. apply wf_denv_typ... intros. apply H2 in H3. rewrite H3...
   apply H1... assert (wf_denv G (D ++ E1)). eapply wf_denv_lin_strengthening3. eauto. apply wf_denv_typ...
   simpl_env 
    assert (atyping G (DD ++ D) (open_ee e1 y) T1 (DD ++ D')).
    apply H1 with  

Lemma atyping_dempty : forall G D1 D2 e T D,
  atyping G D1 e T D2 ->
  D1 = dempty ->
  D2 = dempty ->
  wf_denv G D ->
  atyping G D e T D.
Proof with simpl_env; eauto.
  intros G D1 D2 e T D TypT EQ1 EQ2 Wfd. generalize dependent D. generalize dependent G. generalize dependent T.
  induction e; intros; inversion TypT; subst...
  Case "lvar". binds_cases H0.
  Case "uabs". pick fresh x and apply atyping_uabs. auto. 
  induction TypT; intros; subst...
  Case "lvar". binds_cases H.
  Case "uabs". pick fresh x and apply atyping_uabs. auto. apply H1... apply wf_denv_weakening2. auto.
    apply wf_genv_typ. eapply wf_genv_from_wf_denv. eauto. auto. auto. intros...
  Case "labs". pick fresh x and apply atyping_labs. auto. 
*)
Lemma single_dbinds : forall G x U D ,
  wf_denv G D ->
  binds x U D ->
  (D [-] x) = dempty ->
  exists d, D = [(x, d)].
Proof with simpl_env; eauto.
  intros. generalize dependent x . generalize dependent U. generalize dependent G.
  induction D; intros; subst...
  binds_cases H0. destruct a. simpl_env in H0. simpl_env in H1. simpl in H1. destruct (x == a).
  subst. assert (a `notin` dom D). simpl_env in H.  eapply wf_denv_fv_disj2. eauto. simpl_env. fsetdec.
  destruct D... destruct p. simpl_env in H. destruct (a == a0)... subst. simpl_env in H2. fsetdec.
  simpl_env in H1. rewrite minus_distr in H1. simpl in H1. destruct (a == a0)... fsetdec. inversion H1.
  simpl_env in H1. inversion H1.
Qed.

Lemma empty_atyping_through_nonlin_subst_ee : forall G2 G1 U0 x T e u D1 D2,
  atyping  (G2 ++ [(x, gbind_typ U0)] ++ G1) D1 e T D2 ->
  atyping G1 dempty u U0 dempty ->
  atyping (G2 ++ G1) D1 (subst_ee x u e) T D2.
Proof with simpl_env; eauto.
  intros G2 G1 U0 x T e u D1 D2 TypT TypU.
  remember (G2 ++ [(x, gbind_typ U0)] ++ G1) as G.  generalize dependent G2.
  induction TypT; intros G2 EQ;  subst; simpl subst_ee... 
  Case "atyping_uvar". assert (wf_genv (G2 ++ [(x, gbind_typ U0)] ++ G1)).
  eapply wf_genv_from_wf_denv. eauto.  destruct (x0 == x).
    SCase "x0 = x". subst. assert (gbind_typ T = gbind_typ U0). eapply binds_mid_eq. apply H. 
     apply ok_from_wf_genv... inversion H2; subst... rewrite_env (dempty ++ D ++ dempty).
     apply atyping_lin_weakening... apply atyping_nonlin_weakening2... apply wf_denv_empty. 
     eapply wf_genv_strengthening. eauto. eapply wf_denv_nonlin_strengthening. eauto.
    SCase "x0 <> x". assert (binds x0 (gbind_typ T) (G2++G1)). eapply binds_remove_mid. eauto. auto. 
     apply atyping_uvar... eapply wf_denv_nonlin_strengthening. eauto.
   Case "atyping_lvar". assert (wf_genv (G2 ++ [(x, gbind_typ U0)] ++ G1)).
      eapply wf_genv_from_wf_denv. eauto.  destruct (x0 == x).
      SCase "x0 = x". subst. apply binds_In in H. assert (x `notin` dom (G2 ++ [(x, gbind_typ U0)] ++ G1)).
      eapply denv_dom_dinv. eauto. auto. simpl_env in H2. fsetdec.
      SCase "x0 <> x". apply atyping_lvar... eapply wf_denv_nonlin_strengthening. eauto.
   Case "atyping_uabs". pick fresh y and apply atyping_uabs. eapply wf_atyp_strengthening. eauto. 
     rewrite subst_ee_open_ee_var. rewrite <- concat_assoc. apply H1. auto. auto. auto. 
     apply atyping_regular in TypU. destruct TypU as [U1 [ U2 [U3 [ U4 [ U5 U6]]]]]. auto. auto.
   Case "atyping_labs". pick fresh y and apply atyping_labs. eapply wf_atyp_strengthening. eauto.
    rewrite subst_ee_open_ee_var. apply H1... auto. apply atyping_regular in TypU. destruct TypU as [U1 [ U2 [U3 [ U4 [ U5 U6]]]]]. auto. auto.
   Case "atyping_tabs". pick fresh Y and apply atyping_tabs. apply value_through_subst_ee. auto.   
      apply atyping_regular in TypU. destruct TypU as [U1 [ U2 [U3 [ U4 [ U5 U6]]]]]. auto. auto. 
       rewrite subst_ee_open_te_var. rewrite <- concat_assoc. apply H1. auto. auto. 
       apply atyping_regular in TypU. destruct TypU as [U1 [ U2 [U3 [ U4 [ U5 U6]]]]]. auto. auto.
   Case "atyping_tapp". eapply atyping_tapp. apply IHTypT. auto. assert (wf_atyp (G2 ++ G1) T K').
     eapply wf_atyp_strengthening. eauto. eauto. auto.
Qed.

Lemma empty_atyping_through_lin_subst_ee : forall U0 x G T e e' D1 D' D2,
  atyping G (D2 ++ [(x, dbind_typ U0)] ++ D1) e T D' ->
  atyping G dempty e' U0 dempty ->
  atyping G (D2 ++ D1) (subst_ee x e' e) T (dminus_var x D').
Admitted.


(* ********************************************************************** *)
(** * #<a name="preservation"></a># Preservation *)

(* ********************************************************************** *)
(** ** Preservation *)
(* 
  Lemma dempty_to_dempty : forall e T G D2,
  atyping G dempty e T D2 ->
  D2 = dempty.
  Proof with simpl_env; eauto.
  intros e T G D2 Typ. remember dempty as E.  induction Typ; subst...
  pick fresh x. eapply H1... 
 *)

Lemma preservation : forall e e' T G D1 D2,
  atyping G D1 e T D2  ->
  red e e' ->
  G = gempty ->
  D1 = dempty ->
  D2 = dempty ->
  atyping G D1  e' T D2 .
Proof with simpl_env; eauto.
  intros e e' T G D1 D2 Typ Red HG HD1 HD2. generalize  dependent e'. 
  induction Typ; intros e' Red;  try (inversion Red; subst; eauto).
  Case "typing_app". 
    SCase "red_app_1".  apply denv_mono_empty in Typ1. subst. eapply atyping_app. apply IHTyp1... auto.
    SCase "red_app_2". assert (D2 = dempty). eapply denv_mono_empty. eauto. subst. eapply atyping_app. eauto. auto.
    SCase "red_abs". assert (D2 = dempty). eapply denv_mono_empty. eauto. subst. inversion Typ1; subst. 
      pick fresh x. lapply (H11 x). intros. rewrite (subst_ee_intro x). 
Admitted.
(* Lemma preservation : forall e e' T,
  atyping gempty dempty e T dempty  ->
  red e e' ->
  atyping gempty dempty  e' T dempty .
Proof with simpl_env; eauto.
  intros e e' T Typ.  remember gempty as E. remember dempty as E'. remember E' as E''.
 generalize dependent e'.
  induction Typ; intros e' Red.
  try (inversion Red; subst; eauto).
   try (inversion Red; subst; eauto).
    try (inversion Red; subst; eauto).
     try (inversion Red; subst; eauto).
  induction Typ; intros e' Red; try solve [inversion Red; subst; eauto].
  Case "atyping_app". inversion Red; subst...
    SCase "red_app_1". eapply atyping_app.
Admitted.
*)

  
(* ********************************************************************** *)
(** * #<a name="progress"></a># Progress *)

(* ********************************************************************** *)
(** ** Canonical forms *)

Lemma canonical_form_abs : forall e K U1 U2,
  value e ->
  atyping gempty dempty e (typ_arrow K U1 U2) dempty ->
  exists V, exists e1, e = exp_abs K V e1.
Admitted.

Lemma canonical_form_tabs : forall e U1 U2,
  value e ->
  atyping gempty dempty e (typ_all U1 U2) dempty ->
  exists V, exists e1, e = exp_tabs V e1.
Admitted.

(* ********************************************************************** *)
(** ** Progress *)

Lemma progress : forall e T,
  atyping gempty dempty e T dempty ->
  value e \/ exists e', red e e'.
Admitted.
