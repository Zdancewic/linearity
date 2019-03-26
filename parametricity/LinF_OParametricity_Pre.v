(** Authors: Jianzhou Zhao. *)

Require Import Wf_nat.
Require Import JMeq.
Require Import Omega.

Require Export LinF_PreLib.

(* ********************************************************************** *)
(** * Substitutee
       1) Substitutee on Delta, maping typ vars into typ terms, delta_subst
       2) Substitutee on Gamma, maping expr vars into expr terms, gamma_subst
       3) Substitutee on lin context, maping expr vars into expr terms, lgamma_subst
       4) Substitutee on Rho, maping typ vars into relations, rho_subst
*)

(* Substitutee on Delta, map from typ vars to closed types *)

Inductive wf_delta_osubst : env -> delta_subst -> env -> Prop :=
  | wf_delta_osubst_empty : forall Env,
      wf_env Env ->
      wf_delta_osubst nil delta_nil Env
  | wf_delta_osubst_styp : forall E SE Env X T k,
      wf_delta_osubst E SE Env -> 
      X `notin` dom E  `union`  dom Env -> 
      wf_typ Env T k ->
      wf_delta_osubst ([(X, bind_kn k)] ++ E) ([(X, T)] ++ SE) Env 
  | wf_delta_osubst_skip : forall E SE Env x T,
      wf_delta_osubst E SE Env -> 
      x `notin` dom E `union` dom Env -> 
      wf_typ E T kn_nonlin ->
      wf_delta_osubst ([(x, bind_typ T)] ++ E) SE Env 
  .

Tactic Notation "wf_delta_osubst_cases" tactic(first) tactic(c) :=
  first;
  [ c "wf_delta_osubst_empty" |
    c "wf_delta_osubst_styp" |
    c "wf_delta_osubst_skip"].

(*  Substitutee on Gamma, map from exp vars to exprs(closed) *)

Inductive wf_gamma_osubst : env -> delta_subst -> gamma_subst -> env -> Prop :=
  | wf_gamma_osubst_empty : forall Env,
      wf_env Env ->
      wf_gamma_osubst nil delta_nil gamma_nil Env
  | wf_gamma_osubst_sval : forall x e T E dsE gsE Env,
      wf_gamma_osubst E dsE gsE Env -> 
      x `notin` dom E `union` dom Env ->
      typing Env nil e (apply_delta_subst_typ dsE T) -> 
      wf_typ E T kn_nonlin ->
      wf_gamma_osubst ([(x, bind_typ T)] ++ E) dsE ([(x, e)]++gsE) Env
  | wf_gamma_osubst_skind : forall X T E dsE gsE Env k,
      wf_gamma_osubst E dsE gsE Env -> 
      X `notin` dom E `union` dom Env ->
      wf_typ Env T k ->
      wf_gamma_osubst ([(X, bind_kn k)]++E) ([(X, T)]++dsE) gsE Env
  .

Tactic Notation "wf_gamma_osubst_cases" tactic(first) tactic(c) :=
  first;
  [ c "wf_gamma_osubst_empty" |
    c "wf_gamma_osubst_sval" |
    c "wf_gamma_osubst_skind"].

(*  Substitutee on lin Context, map from exp vars to exprs(closed) *)

Inductive wf_lgamma_osubst : env -> lenv -> delta_subst -> gamma_subst -> gamma_subst -> env -> lenv -> Prop :=
  | wf_lgamma_osubst_empty : forall Env,
      wf_env Env ->
      wf_lgamma_osubst nil nil nil nil nil Env nil
  | wf_lgamma_osubst_sval : forall x e T E lE dsE gsE lgsE Env lEnv,
      wf_lgamma_osubst E lE dsE gsE lgsE Env lEnv -> 
      x `notin` dom E `union` dom lE `union` dom Env `union` dom lEnv ->
      typing Env nil e (apply_delta_subst_typ dsE T) -> 
      wf_typ E T kn_nonlin ->
      wf_lgamma_osubst ([(x, bind_typ T)] ++ E) lE dsE ([(x, e)]++gsE) lgsE Env lEnv
  | wf_lgamma_osubst_slval : forall x e T E lE dsE gsE lgsE Env lEnv1 lEnv2,
      wf_lgamma_osubst E lE dsE gsE lgsE Env lEnv1 -> 
      x `notin` dom E `union` dom lE `union` dom Env `union` dom lEnv1 `union` dom lEnv2->
      disjoint E lEnv2 /\ disjoint lE lEnv2 ->
      wf_lenv Env (lEnv2++lEnv1) ->
      typing Env lEnv2 e (apply_delta_subst_typ dsE T) -> 
      wf_typ E T kn_lin ->
      wf_lgamma_osubst E ([(x, lbind_typ T)] ++ lE) dsE gsE ([(x, e)]++lgsE) Env (lEnv2++lEnv1)
  | wf_lgamma_osubst_skind : forall X T E lE dsE gsE lgsE Env lEnv k,
      wf_lgamma_osubst E lE dsE gsE lgsE Env lEnv -> 
      X `notin` dom E `union` dom lE `union` dom Env `union` dom lEnv ->
      wf_typ Env T k ->
      wf_lgamma_osubst ([(X, bind_kn k)]++E) lE ([(X, T)]++dsE) gsE lgsE Env lEnv
  .

Tactic Notation "wf_lgamma_osubst_cases" tactic(first) tactic(c) :=
  first;
  [ c "wf_lgamma_osubst_empty" |
    c "wf_lgamma_osubst_sval" |
    c "wf_lgamma_osubst_slval" |
    c "wf_lgamma_osubst_skind" ].

(* ********************************************************************** *)
(** * #<a name="split"></a># Linear Substitution Splitting *)

Inductive lgamma_osubst_split : env -> lenv -> delta_subst -> gamma_subst -> gamma_subst -> gamma_subst -> gamma_subst -> env -> lenv -> lenv -> lenv -> Prop :=
  | lgamma_osubst_split_empty: forall E dsE gsE Env, 
       wf_lgamma_osubst E nil dsE gsE nil Env nil -> 
       lgamma_osubst_split E nil dsE gsE nil nil nil Env nil nil nil
  | lgamma_osubst_split_left: forall E lE dsE gsE lgsE1 lgsE2 lgsE3 Env lEnv1 lEnv2 lEnv3 lEnv1' x e T,
       lgamma_osubst_split E lE dsE gsE lgsE1 lgsE2 lgsE3 Env lEnv1 lEnv2 lEnv3 ->
       x `notin` dom E `union` dom lE `union` 
                         dom Env `union` dom lEnv1 `union` dom lEnv2 `union` dom lEnv3 `union` 
                         dom lEnv1' ->
       disjoint E lEnv1' /\ disjoint lE lEnv1' /\ disjoint lEnv2 lEnv1' ->
       wf_lenv Env (lEnv1'++lEnv1) ->
       typing Env lEnv1' e (apply_delta_subst_typ dsE T) -> 
       wf_typ E T kn_lin ->
       lgamma_osubst_split E ([(x, lbind_typ T)]++lE) dsE gsE ([(x, e)]++lgsE1) lgsE2 ([(x, e)]++lgsE3) Env (lEnv1'++lEnv1) lEnv2 (lEnv1'++lEnv3)
  | lgamma_osubst_split_right: forall E lE dsE gsE lgsE1 lgsE2 lgsE3 Env lEnv1 lEnv2 lEnv3 lEnv2' x e T,
       lgamma_osubst_split E lE dsE gsE lgsE1 lgsE2 lgsE3 Env lEnv1 lEnv2 lEnv3 ->
       x `notin` dom E `union` dom lE `union` 
                         dom Env `union` dom lEnv1 `union` dom lEnv2 `union` dom lEnv3 `union` 
                         dom lEnv2' ->
       disjoint E lEnv2' /\ disjoint lE lEnv2' /\ disjoint lEnv1 lEnv2' ->
       wf_lenv Env (lEnv2'++lEnv2) -> 
       typing Env lEnv2' e (apply_delta_subst_typ dsE T) -> 
       wf_typ E T kn_lin ->
       lgamma_osubst_split E ([(x, lbind_typ T)]++lE) dsE gsE lgsE1 ([(x, e)]++lgsE2) ([(x, e)]++lgsE3) Env lEnv1 (lEnv2'++lEnv2) (lEnv2'++lEnv3)
  .

Tactic Notation "lgamma_osubst_split_cases" tactic(first) tactic(c) :=
  first;
  [ c "lgamma_osubst_split_empty" |
    c "lgamma_osubst_split_left" |
    c "lgamma_osubst_split_right"].

Hint Constructors wf_delta_osubst wf_gamma_osubst wf_lgamma_osubst lgamma_osubst_split.

(* ********************************************************************** *)
(*                                            Properties                                             *)
(* ********************************************************************** *)
(** * Properties about the free variables of terms *)

Lemma wf_lgamma_osubst__fv : forall E D dsubst gsubst lgsubst x Env lEnv,
  wf_lgamma_osubst E D dsubst gsubst lgsubst Env lEnv ->
  x `in` dom lgsubst ->
  x `in` dom D.
Proof.
  intros E D dsubst gsubst lgsubst x Env lEnv H1 H2.
  (wf_lgamma_osubst_cases (induction H1) Case); intros; simpl; auto.
  Case "wf_lgamma_osubst_slval".
    rewrite dom_app in H2. 
    assert (x `in` dom [(x0, e)] \/ x `in` dom lgsE) as J. fsetdec.
    destruct J as [J | J]; simpl in J; fsetdec.
Qed.    

(********************************************************)
(* well found subst give envs *)
Lemma dom_delta_osubst : forall E sD Env,
  wf_delta_osubst E sD Env-> ddom_env E [=] dom sD.
Proof.
  intros E sD Env Hwfd.
  induction Hwfd; simpl_env; fsetdec.
Qed.

Lemma dom_gamma_osubst : forall E sD sG Env,
  wf_gamma_osubst E sD sG  Env -> 
  ddom_env E [=] dom sD /\ gdom_env E [=] dom sG.
Proof.
  intros E sD sG  Env Hwfg.
  induction Hwfg; simpl_env; split; fsetdec.
Qed.

Lemma dom_lgamma_osubst : forall E lE sD sG slG Env lEnv,
  wf_lgamma_osubst E lE sD sG slG Env lEnv -> 
  ddom_env E [=] dom sD /\ gdom_env E [=] dom sG /\ dom lE [=] dom slG.
Proof.
  intros E lE sD sG slG Env lEnv Hwfg.
  induction Hwfg; simpl; simpl_env; auto.
    split. fsetdec.
    split; fsetdec.

    decompose [and] IHHwfg.
    split. fsetdec.
    split; fsetdec.

    decompose [and] IHHwfg.
    split. fsetdec.
    split; fsetdec.
Qed.

Lemma disjoint_delta_osubst : forall E sD Env,
  wf_delta_osubst E sD Env -> disjoint E Env  /\ disjoint sD Env .
Proof.
  intros E sD Env Hwfd.
  induction Hwfd; simpl_env; split; 
    try solve [solve_uniq |
                         destruct IHHwfd; solve_uniq].
Qed.

Lemma disjoint_gamma_osubst : forall E sD sG Env,
  wf_gamma_osubst E sD sG Env -> 
  disjoint E Env  /\ disjoint sD Env /\ disjoint sG Env.
Proof.
  intros E sD sG Env Hwfg.
  induction Hwfg; simpl_env; split; 
    try solve [solve_uniq |
                         decompose [and] IHHwfg; solve_uniq | 
                         decompose [and] IHHwfg; split; auto]. 
Qed.

Lemma wf_lgamma_osubst__wf_lenv : forall E D dsubst gsubst lgsubst Env lEnv,
  wf_lgamma_osubst E D dsubst gsubst lgsubst Env lEnv -> 
  wf_env E /\ wf_lenv E D /\ wf_env Env /\ wf_lenv Env lEnv.
Proof.
  intros.
  induction H; auto .
    destruct IHwf_lgamma_osubst as [J1 [J2 [J3 J4]]].
    split; auto.
    split; auto.
      rewrite_env (nil ++ [(x, bind_typ T)] ++ E).
      apply wf_lenv_weakening; auto.
        apply wf_env_typ; auto.

    destruct IHwf_lgamma_osubst as [J1 [J2 [J3 J4]]].
    split; auto.

    destruct IHwf_lgamma_osubst as [J1 [J2 [J3 J4]]].
    split; auto.
    split; auto.
      rewrite_env (nil ++ [(X, bind_kn k)] ++ E).
      apply wf_lenv_weakening; auto.
        apply wf_env_kn; auto.
Qed.

Lemma disjoint_lgamma_osubst : forall E lE sD sG slG  Env lEnv,
  wf_lgamma_osubst E lE sD sG slG Env lEnv -> 
  disjoint E Env  /\ disjoint lE Env /\ disjoint sD Env /\ disjoint sG Env /\ disjoint slG Env /\ 
  disjoint E lEnv /\  disjoint lE lEnv /\ disjoint sD lEnv /\ disjoint slG lEnv /\ disjoint sG lEnv.
Proof.
  intros E lE sD sG slG Env lEnv Hwfg.
  induction Hwfg; simpl_env.
    repeat(split; auto).

    decompose [and] IHHwfg.
    repeat(split; auto).

    decompose [and] IHHwfg.
    decompose [and] H0. clear H0 IHHwfg.
    repeat(split; auto).
      apply disjoint_lenv_split with (E:=Env) (D1:=lEnv2) (D2:=lEnv1); auto.
        apply disjoint__lenv_split; auto.
          apply wf_lgamma_osubst__wf_lenv in Hwfg; auto.
          decompose [and] Hwfg; auto.

      apply uniq_from_wf_lenv in H1.
      solve_uniq.
 
      assert (ddom_env E [=] dom dsE) as EQ.
        apply dom_lgamma_osubst in Hwfg.
        decompose [and] Hwfg; auto.
      assert (dom E [=] ddom_env E `union` gdom_env E) as EQ'.
        apply dom__ddom_gdom; auto.
      assert (dom dsE [<=] dom E) as J. fsetdec.
      apply disjoint_sub with (D1:=E); auto.

      assert (disjoint lgsE lEnv2) as Disj.
        assert (dom lE [=] dom lgsE) as EQ.
          apply dom_lgamma_osubst in Hwfg.
          decompose [and] Hwfg; auto.
        apply disjoint_eq with (D1:=lE); auto.
      solve_uniq.

      assert (disjoint gsE lEnv2) as Disj.
        assert (gdom_env E [=] dom gsE) as EQ.
          apply dom_lgamma_osubst in Hwfg.
          decompose [and] Hwfg; auto.
        assert (dom E [=] ddom_env E `union` gdom_env E) as EQ'.
          apply dom__ddom_gdom; auto.
        assert (dom gsE [<=] dom E) as J. fsetdec.
        apply disjoint_sub with (D1:=E); auto.
      solve_uniq.

    decompose [and] IHHwfg.
    repeat(split; auto).
Qed.

Lemma wf_delta_osubst__uniq : forall E dsubst Env,
  wf_delta_osubst E dsubst Env -> wf_env E /\ uniq E /\ uniq dsubst  /\ wf_env Env.
Proof.
  intros E dsubst Env H.
  (wf_delta_osubst_cases (induction H) Case); auto.
  Case "wf_delta_osubst_styp".
    decompose [and] IHwf_delta_osubst.
    split; auto.
    split; auto.
    split; auto.
      apply dom_delta_osubst in H.
      destruct_notin.
      apply dom__ddom in H0. 
      rewrite H in H0; auto.
  Case "wf_delta_osubst_skip".
    split; decompose [and] IHwf_delta_osubst; auto.
Qed.

Lemma swap_subst_ee_ogsubst: forall e' x E D dsubst gsubst lgsubst Env lEnv e t lEnv',
  wf_lgamma_osubst E D dsubst gsubst lgsubst Env lEnv ->
  typing Env lEnv' e' t ->
  disjoint E lEnv' ->
  x `notin` dom gsubst `union` dom Env `union` dom lEnv `union` dom lEnv' ->
  subst_ee x e' (apply_gamma_subst gsubst e) =
  apply_gamma_subst gsubst (subst_ee x e' e).
Proof.
  intros e' x E D dsubst gsubst lgsubst Env lEnv e t lEnv' Hwflg Typing Disj Fv.
  generalize dependent e.
  generalize dependent e'.
  generalize dependent t.
  generalize dependent lEnv'.
  induction Hwflg; intros lEnv' Disj Fv t e' Typing e0; simpl; auto.
    rewrite subst_ee_commute; auto.
      apply IHHwflg with (t:=t) (lEnv':=lEnv'); auto.
      solve_uniq.
      eauto using notin_fv_ee_typing.

      assert (x0 `notin` dom lEnv') as J. solve_uniq.
      eauto using notin_fv_ee_typing.

    apply IHHwflg with (t:=t) (lEnv':=lEnv'); auto.

    apply IHHwflg with (t:=t) (lEnv':=lEnv'); auto.
      solve_uniq.
Qed.

Lemma swap_subst_ee_olgsubst: forall e' x E D dsubst gsubst lgsubst Env lEnv lEnv' e t,
  wf_lgamma_osubst E D dsubst gsubst lgsubst Env lEnv ->
  typing Env lEnv' e' t ->
  disjoint D lEnv' ->
  x `notin` dom lgsubst `union` dom Env `union` dom lEnv `union` dom lEnv' ->
  subst_ee x e' (apply_gamma_subst lgsubst e) =
  apply_gamma_subst lgsubst (subst_ee x e' e).
Proof.
  intros e' x E D dsubst gsubst lgsubst Env lEnv lEnv' e t Hwflg Typing Disj Fv.
  generalize dependent e.
  generalize dependent e'.
  generalize dependent t.
  generalize dependent lEnv'.
  induction Hwflg; intros lEnv' Disj Fv t e' Typing e0; simpl; eauto.
    assert (x0 `notin` dom lEnv') as J1. solve_uniq.
    rewrite IHHwflg with (lEnv':=lEnv') (t:=t); auto.
    rewrite subst_ee_commute; eauto.
      eauto using typing_fv.
      eauto using typing_fv.
    solve_uniq.
Qed.

Lemma swap_subst_ee_odsubst: forall e' x E dsubst e t Env lEnv',
  wf_delta_osubst E dsubst Env ->
  typing Env lEnv' e' t ->
  x `notin` dom dsubst `union` dom Env `union` dom lEnv' ->
  subst_ee x e' (apply_delta_subst dsubst e) =
  apply_delta_subst dsubst (subst_ee x e' e).
Proof.
  intros e' x E dsubst e t Env lEnv' Hwfd Hwft xndsubst.
  generalize dependent e.
  generalize dependent e'.
  generalize dependent t.
  generalize dependent lEnv'.
  induction Hwfd; intros lEnv' Fv t e' Hwft e0; simpl; eauto.
    rewrite <- subst_te_ee_commute; auto.
      rewrite IHHwfd with (lEnv':=lEnv') (t:=t); auto.
      eauto using notin_fv_te_typing.
Qed.

Lemma swap_subst_te_odsubst: forall t X E dsubst e K Env,
  wf_delta_osubst E dsubst Env ->
  wf_typ Env t K ->
  X `notin` dom dsubst `union` dom Env ->
  subst_te X t (apply_delta_subst dsubst e) =
  apply_delta_subst dsubst (subst_te X t e).
Proof.
  intros t X E dsubst e K Env Hwfd Hwft xndsubst.
  generalize dependent e.
  generalize dependent t.
  induction Hwfd; intros t Hwft e0; simpl; eauto.
    rewrite subst_te_commute; auto.
      eauto using notin_fv_wf.
      eauto using notin_fv_wf.
Qed.

(*******************************************************************************)
(** subst under delta/gamma *)

Lemma delta_osubst_opt :  forall E E' dsubst X t t' dsubst' K Env,
   wf_delta_osubst (E'++[(X, bind_kn K)]++E) (dsubst'++[(X, t)]++dsubst) Env ->
   X `notin` (dom E `union` dom E' `union` dom Env) ->
   ddom_env E [=] dom dsubst ->
   ddom_env E' [=] dom dsubst' ->
   wf_typ Env t K ->
   apply_delta_subst_typ (dsubst'++[(X, t)]++dsubst) t' =
     apply_delta_subst_typ (dsubst'++dsubst) (subst_tt X t t').
Proof.
  intros E E' dsubst X t t' dsubst' K Env Hwf_delta_osubst Fr Heq He1' Hwft.
  remember (E'++[(X, bind_kn K)]++E) as G.
  remember (dsubst'++[(X, t)]++dsubst) as Dsubst.
  generalize dependent t'.
  generalize dependent dsubst'.
  generalize dependent E'.
  (wf_delta_osubst_cases (induction Hwf_delta_osubst) Case); 
    intros E' HeqG Fr dsubst' HeqDsubst Heq' t'.
  Case "wf_delta_osubst_empty".
    contradict HeqG; auto.    
  Case "wf_delta_osubst_styp".
    destruct (one_eq_app _ _ _ _ _ HeqG) as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
    SCase "exists E'', E'=E&X0'' /\ E0=E&X&E'' ".
      destruct (one_eq_app _ _ _ _ _ HeqDsubst) as [[dsubst'' [DEQ1 DEQ2]] | [DEQ1 DEQ2]]; subst.
      SSCase "exists DS'',DS'=DS&X0'' /\ DS0=DS&X&DS'' ".
        simpl. simpl_env. 
        rewrite <- subst_tt_commute; auto.
          apply IHHwf_delta_osubst with (E':=E''); auto.
             apply ddom_dom__inv with (X:=X0)(b:= t)(K:=K); auto.
               apply dom_delta_osubst in Hwf_delta_osubst.
                destruct_notin.
               apply dom__ddom in H.
               rewrite Hwf_delta_osubst in H. simpl_env in *. auto.
          eauto using notin_fv_wf.
          eauto using notin_fv_wf.
      SSCase "DS'=nil /\ DS&X = DS0&X0 ".
        inversion DEQ2. subst.
        simpl_env in *. destruct_notin.
        auto.
    SCase "E'=nil /\ E&X = E0&X0 ".
      inversion EQ2; subst.
      destruct (one_eq_app _ _ _ _ _ HeqDsubst) as [[dsubst'' [DEQ1 DEQ2]] | [DEQ1 DEQ2]]; subst.
      SSCase "exists DS'',DS'=DS&X0'' /\ DS0=DS&X&DS'' ".
        simpl_env in Heq'.
        assert (X0 `notin` (singleton X0 `union` dom dsubst'') -> False).
            intro. destruct_notin. apply NotInTac0; auto.
        rewrite <- Heq' in H1.
        assert (False). apply H1; auto.
        inversion H2.
      SSCase "DS'=nil /\ DS&X = DS0&X0 ".
        inversion DEQ2; subst; auto.
  Case "wf_delta_osubst_skip".
    subst.
    destruct (one_eq_app _ _ _ _ _ HeqG) as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      apply IHHwf_delta_osubst with (E':=E''); auto.
      inversion EQ2.
Qed.

Lemma swap_subst_te_ogsubst: forall t X E D dsubst gsubst lgsubst Env lEnv e K,
  wf_lgamma_osubst E D dsubst gsubst lgsubst Env lEnv ->
  X `notin` dom Env ->
  wf_typ Env t K ->
  subst_te X t (apply_gamma_subst gsubst e) =
  apply_gamma_subst gsubst (subst_te X t e).
Proof.
  intros t X E D dsubst gsubst lgsubst Env lEnv e K Hwflg FrX Hwft.
  generalize dependent e.
  generalize dependent t.
  induction Hwflg; intros t Hwft e0; simpl; auto.
    rewrite subst_te_ee_commute; auto.
    eauto using notin_fv_te_typing.
Qed.

Lemma swap_subst_te_olgsubst: forall t X E D dsubst gsubst lgsubst Env lEnv e K,
  wf_lgamma_osubst E D dsubst gsubst lgsubst Env lEnv  ->
  X `notin` dom Env  ->
  wf_typ Env t K ->
  subst_te X t (apply_gamma_subst lgsubst e) =
  apply_gamma_subst lgsubst (subst_te X t e).
Proof.
  intros t X E D dsubst gsubst lgsubst Env lEnv e K Hwflg FrX Hwft.
  generalize dependent e.
  generalize dependent t.
  induction Hwflg; intros t Hwft e0; simpl; auto.
    rewrite subst_te_ee_commute; auto.
    eauto using notin_fv_te_typing.
Qed.

Lemma delta_osubst_permut : forall dE dsubst Env X T K t,
  wf_delta_osubst dE dsubst Env ->
  X `notin` dom dsubst `union` dom Env -> 
  wf_typ Env T K ->
  apply_delta_subst_typ dsubst (subst_tt X T t) = subst_tt X T (apply_delta_subst_typ dsubst t).
Proof.
  intros dE dsubst Env X T K t Hwfd Fr Hwft.
  generalize dependent t.
  induction Hwfd; intros; simpl; eauto.
    simpl_env in *.
    rewrite <- subst_tt_commute; eauto using notin_fv_wf.
Qed.

Lemma gamma_osubst_value : forall E D dsubst gsubst lgsubst Env lEnv v,
  wf_lgamma_osubst E D dsubst gsubst lgsubst Env lEnv ->
  value v ->
  value (apply_gamma_subst gsubst v).
Proof.
  intros E D dsubst gsubst lgsubst Env lEnv v Hwflg Hv.
  generalize dependent v.
  induction Hwflg; intros v Hv; simpl; auto.
    apply IHHwflg; auto.
    destruct Hv; simpl; auto.
      inversion H2. subst.
      apply value_abs.
        apply expr_abs with (L:=L `union` singleton x); auto.
        intros. rewrite subst_ee_open_ee_var; auto.

      inversion H2. subst.
      apply value_tabs.
        apply expr_tabs with (L:=L `union` singleton x); auto.
        intros. rewrite subst_ee_open_te_var; auto.
Qed.

Lemma lgamma_osubst_value : forall E D dsubst gsubst lgsubst Env lEnv v,
  wf_lgamma_osubst E D dsubst gsubst lgsubst Env lEnv ->
  value v ->
  value (apply_gamma_subst lgsubst v).
Proof.
  intros E D dsubst gsubst lgsubst Env lEnv v Hwflg Hv.
  generalize dependent v.
  induction Hwflg; intros v Hv; simpl; auto.
    apply IHHwflg; auto.
    destruct Hv; simpl; auto.
      inversion H4. subst.
      apply value_abs.
        apply expr_abs with (L:=L `union` singleton x); auto.
        intros. rewrite subst_ee_open_ee_var; auto.

      inversion H4. subst.
      apply value_tabs.
        apply expr_tabs with (L:=L `union` singleton x); auto.
        intros. rewrite subst_ee_open_te_var; auto.
Qed.

Lemma delta_osubst_value : forall dE dsubst Env v,
  wf_delta_osubst dE dsubst Env ->
  value (v) ->
  value (apply_delta_subst dsubst v).
Proof.
  intros dE dsubst Env v Hwfd Hv.
  generalize dependent v.
  induction Hwfd; intros v Hv; simpl; auto.
    apply IHHwfd; auto.
    destruct Hv; simpl; auto.
      inversion H1; subst.
      apply value_abs.
        apply expr_abs with (L:=L `union` singleton X); eauto using type_from_wf_typ.
          intros. rewrite subst_te_open_ee_var; eauto using type_from_wf_typ.

      inversion H1.
      apply value_tabs.
        apply expr_tabs with (L:=L `union` singleton X); auto.
          intros. rewrite subst_te_open_te_var; eauto using type_from_wf_typ.

      apply value_apair; eauto using subst_te_expr, type_from_wf_typ.
Qed.

Lemma delta_gamma_osubst_value : forall E D dsubst gsubst lgsubst Env lEnv v,
  wf_lgamma_osubst E D dsubst gsubst lgsubst Env lEnv ->
  wf_delta_osubst E dsubst Env ->
  value v ->
  value(apply_delta_subst dsubst (apply_gamma_subst gsubst v)).
Proof.
  intros.
  eapply delta_osubst_value; eauto.
  eapply gamma_osubst_value; eauto.
Qed.

Lemma delta_lgamma_osubst_value : forall E D dsubst gsubst lgsubst Env lEnv v,
  wf_lgamma_osubst E D dsubst gsubst lgsubst Env lEnv ->
  wf_delta_osubst E dsubst Env ->
  value v ->
  value(apply_delta_subst dsubst (apply_gamma_subst lgsubst v)).
Proof.
  intros.
  eapply delta_osubst_value; eauto.
  eapply lgamma_osubst_value; eauto.
Qed.

Lemma in_fv_tt_delta_osubst : forall E dsubst Env t X,
  wf_delta_osubst E dsubst Env ->
  X `in` fv_tt t ->
  X `notin` dom dsubst ->
  X `in` fv_tt (apply_delta_subst_typ dsubst t).
Proof.
  intros E dsubst Env t X Wdf Xint Xnotind.
  induction Wdf; intros; simpl; auto.
    rewrite delta_osubst_permut with (dE:=E) (Env:=Env) (K:=k); auto.      
      apply in_fv_tt_subst_tt; auto.
      
      apply dom_delta_osubst in Wdf.
      rewrite <- Wdf.
      auto using dom__ddom.
Qed.

(* ********************************************************************** *)
(* commut and subst *)

Lemma commut_gamma_osubst_open_ee: forall E D dsubst gsubst lgsubst Env lEnv e0 e,
   wf_lgamma_osubst E D dsubst gsubst lgsubst Env lEnv ->
   apply_gamma_subst gsubst (open_ee e0 e)
= open_ee (apply_gamma_subst gsubst e0) (apply_gamma_subst gsubst e).
Proof.
  intros E D dsubst gsubst lgsubst Env lEnv e0 e Hwfg.
  generalize dependent e0.
  generalize dependent e.
  induction Hwfg; intros; simpl; auto.
    rewrite subst_ee_open_ee; auto.
Qed.

Lemma commut_gamma_osubst_open_te: forall E D dsubst gsubst lgsubst Env lEnv e t,
   wf_lgamma_osubst E D dsubst gsubst lgsubst Env lEnv ->
   apply_gamma_subst gsubst (open_te e t)
= open_te (apply_gamma_subst gsubst e) (apply_gamma_subst_typ gsubst t).
Proof.
  intros E D dsubst gsubst lgsubst Env lEnv e t Hwfg.
  generalize dependent e.
  generalize dependent t.
  induction Hwfg; intros; simpl; auto.
    unfold apply_gamma_subst_typ in *.
    rewrite subst_ee_open_te; auto.
Qed.

Lemma commut_lgamma_osubst_open_ee: forall E D dsubst gsubst lgsubst Env lEnv e0 e,
   wf_lgamma_osubst E D dsubst gsubst lgsubst Env lEnv ->
   apply_gamma_subst lgsubst (open_ee e0 e)
= open_ee (apply_gamma_subst lgsubst e0) (apply_gamma_subst lgsubst e).
Proof.
  intros E D dsubst gsubst lgsubst Env lEnv e0 e Hwfg.
  generalize dependent e0.
  generalize dependent e.
  induction Hwfg; intros; simpl; auto.
    rewrite subst_ee_open_ee; auto.
Qed.

Lemma commut_lgamma_osubst_open_te: forall E D dsubst gsubst lgsubst Env lEnv e t,
   wf_lgamma_osubst E D dsubst gsubst lgsubst Env lEnv ->
   apply_gamma_subst lgsubst (open_te e t)
= open_te (apply_gamma_subst lgsubst e) (apply_gamma_subst_typ lgsubst t).
Proof.
  intros E D dsubst gsubst lgsubst Env lEnv e t Hwfg.
  generalize dependent e.
  generalize dependent t.
  induction Hwfg; intros; simpl; auto.
    unfold apply_gamma_subst_typ in *.
    rewrite subst_ee_open_te; auto.
Qed.

Lemma commut_delta_osubst_open_ee: forall dE dsubst Env e0 e,
   wf_delta_osubst dE dsubst Env ->
   apply_delta_subst dsubst (open_ee e0 e)
= open_ee (apply_delta_subst dsubst e0) (apply_delta_subst dsubst e).
Proof.
  intros dE dsubst Env e0 e Hwfd.
  generalize dependent e.
  generalize dependent e0.
  induction Hwfd; intros; simpl; auto.
    rewrite subst_te_open_ee; auto.
Qed.

Lemma commut_delta_osubst_open_te: forall dE dsubst Env e t,
   wf_delta_osubst dE dsubst Env ->
   apply_delta_subst dsubst (open_te e t)
= open_te (apply_delta_subst dsubst e) (apply_delta_subst_typ dsubst t).
Proof.
  intros dE dsubst Env e t Hwfd.
  generalize dependent e.
  generalize dependent t.
  induction Hwfd; intros; simpl; auto.
    rewrite subst_te_open_te; eauto using type_from_wf_typ.
Qed.

Lemma commut_delta_osubst_open_tt: forall dE dsubst Env T X,
   wf_delta_osubst dE dsubst Env ->
   apply_delta_subst_typ dsubst (open_tt T X)
= open_tt (apply_delta_subst_typ dsubst T) (apply_delta_subst_typ dsubst X).
Proof.
  intros dE dsubst Env T X Hwfd.
  generalize dependent X.
  generalize dependent T.
  induction Hwfd; intros; simpl; auto.
    rewrite subst_tt_open_tt; eauto using type_from_wf_typ.
Qed.

Lemma commut_delta_osubst_open_tt_rec: forall dE dsubst Env t0 t k,
   wf_delta_osubst dE dsubst Env ->
   apply_delta_subst_typ dsubst (open_tt_rec k t t0)
= open_tt_rec k (apply_delta_subst_typ dsubst t) (apply_delta_subst_typ dsubst t0).
Proof.
  intros dE dsubst Env t0 t kk Hwfd.
  generalize dependent t.
  generalize dependent t0.
  generalize dependent kk.
  induction Hwfd; intros; simpl; auto.
    rewrite subst_tt_open_tt_rec; auto.
      apply type_from_wf_typ in H0; auto.
Qed.

Lemma commut_osubst_tt_dsubst: forall t X E dsubst Env T K,
  wf_delta_osubst E dsubst Env ->
  wf_typ Env t K ->
  X `notin` dom E `union` dom Env ->
  apply_delta_subst_typ dsubst (subst_tt X t T) =
  subst_tt X t (apply_delta_subst_typ dsubst T).
Proof.
  intros t X E dsubst Env T K Hwfd Hwft Fr.
  generalize dependent t.
  generalize dependent T.
  induction Hwfd; intros; simpl; auto.
    simpl_env in*. destruct_notin.
    rewrite <- IHHwfd; auto.
      rewrite subst_tt_commute; eauto using notin_fv_wf.
Qed.

Lemma swap_subst_tt_odsubst: forall t X E dsubst Env T K,
  wf_delta_osubst E dsubst Env ->
  wf_typ E t K ->
  X `notin` dom E `union` dom Env `union` fv_tt t ->
  apply_delta_subst_typ dsubst (subst_tt X (apply_delta_subst_typ dsubst t) T)=
  apply_delta_subst_typ dsubst (subst_tt X t T).
Proof.
  intros t X E dsubst Env T K Hwfd Hwft Fr.
  assert (wf_typ (E ++ Env) t K) as J.
    rewrite_env (E ++ nil) in Hwft.
    apply wf_typ_weakening with (G:=E)(F:=Env)(E:=@nil (atom*binding)) in Hwft; simpl_env in *; auto.
      assert (J:=Hwfd).
      apply wf_delta_osubst__uniq in Hwfd. decompose [and] Hwfd.
      apply disjoint_delta_osubst in J. decompose [and] J.
      apply uniq_app_4; auto.
  clear Hwft. rename J into Hwft.
  generalize dependent t.
  generalize dependent T.
  induction Hwfd; intros; simpl; auto.
    simpl_env in*. destruct_notin.
    erewrite commut_osubst_tt_dsubst with (E:=E); eauto.
    rewrite IHHwfd; auto.
      erewrite <- commut_osubst_tt_dsubst with (E:=E); eauto.
      rewrite swap_dubst_tt; eauto using notin_fv_wf.

      apply notin_fv_tt_subst_tt with (T1:=T) (X:=X0) in NotInTac0; eauto using notin_fv_wf.

      apply wf_typ_subst_tb with (E:=E++Env) (F:=(@nil (atom*binding))) (Z:=X0) (P:=T) in Hwft; auto.
          apply wf_typ_weaken_head with (F:=E) in H0; simpl_env in *; auto.
            assert (J:=Hwfd).
            apply wf_delta_osubst__uniq in Hwfd. decompose [and] Hwfd.
            apply disjoint_delta_osubst in J. decompose [and] J.
            apply uniq_app_4; auto.

    rewrite IHHwfd; auto.
      simpl_env in Hwft.
      apply wft_strengthen_ex in Hwft; simpl;auto.
Qed.

(* *************** *)
(* red expr value typ *)

Lemma expr_preserved_under_gamma_osubst: forall E D dsubst gsubst lgsubst Env lEnv e,
   wf_lgamma_osubst E D dsubst gsubst lgsubst Env lEnv ->
   expr e ->
   expr (apply_gamma_subst gsubst e).
Proof.
  intros E D dsubst gsubst lgsubst Env lEnv e Hwfg He.
  generalize dependent e.
  induction Hwfg; intros; auto.
    simpl. apply IHHwfg.
      apply typing_regular in H0.
      decompose [and] H0.
      apply subst_ee_expr; auto.
Qed.

Lemma type_preserved_under_gamma_osubst: forall E D dsubst gsubst lgsubst Env lEnv t,
   wf_lgamma_osubst E D dsubst gsubst lgsubst Env lEnv ->
   type t ->
   type (apply_gamma_subst_typ gsubst t).
intros. unfold apply_gamma_subst_typ in *.  auto.
Qed.

Lemma expr_preserved_under_lgamma_osubst: forall E D dsubst gsubst lgsubst Env lEnv e,
   wf_lgamma_osubst E D dsubst gsubst lgsubst Env lEnv ->
   expr e ->
   expr (apply_gamma_subst lgsubst e).
Proof.
  intros E D dsubst gsubst lgsubst Env lEnv e Hwfg He.
  generalize dependent e.
  induction Hwfg; intros; auto.
    simpl. apply IHHwfg.
      apply typing_regular in H2.
      decompose [and] H2.
      apply subst_ee_expr; auto.
Qed.

Lemma type_preserved_under_lgamma_osubst: forall E D dsubst gsubst lgsubst Env lEnv t,
   wf_lgamma_osubst E D dsubst gsubst lgsubst Env lEnv ->
   type t ->
   type (apply_gamma_subst_typ lgsubst t).
intros. unfold apply_gamma_subst_typ in *.  auto.
Qed.

Lemma expr_preserved_under_delta_osubst: forall E dsubst Env e,
   wf_delta_osubst E dsubst Env ->
   expr e ->
   expr (apply_delta_subst dsubst e).
Proof.
  intros E dsubst Env e Hwfd He.
  generalize dependent e.
  induction Hwfd; intros; simpl; auto.
    apply IHHwfd.
      apply subst_te_expr; eauto using type_from_wf_typ.
Qed.

Lemma type_preserved_under_delta_osubst: forall E dsubst Env t,
   wf_delta_osubst E dsubst Env ->
   type t ->
   type (apply_delta_subst_typ dsubst t).
Proof.
  intros E dsubst Env t Hwfd Ht.
  generalize dependent t.
  induction Hwfd; intros; simpl; auto.
    apply IHHwfd.
      apply subst_tt_type; eauto using type_from_wf_typ.
Qed.

Lemma red_abs_preserved_under_delta_osubst: forall dE dsubst Env K T e1 e2,
   wf_delta_osubst dE dsubst Env ->
   red (exp_app (exp_abs K T e1) e2) (open_ee e1 e2) ->
   red (exp_app (apply_delta_subst dsubst (exp_abs K T e1)) (apply_delta_subst dsubst e2))
                  (apply_delta_subst dsubst (open_ee e1 e2)).
Proof.
  intros dE dsubst Env K T e1 e2 Hwfd Hrc.
  generalize dependent T.
  generalize dependent e1.
  generalize dependent e2.
  induction Hwfd; intros; simpl; auto.
    rewrite subst_te_open_ee.
    apply IHHwfd; auto.
      rewrite <- subst_te_open_ee.
      assert (exp_app (exp_abs K (subst_tt X T T0) (subst_te X T e1)) (subst_te X T e2)
                  = subst_te X T (exp_app (exp_abs K T0 e1) e2)). auto.
      rewrite H1.
      apply red_preserved_under_typsubst; eauto using type_from_wf_typ.
Qed.

Lemma red_tabs_preserved_under_delta_osubst: forall dE dsubst Env K e1 t2,
   wf_delta_osubst dE dsubst Env ->
   red (exp_tapp (exp_tabs K e1) t2) (open_te e1 t2) ->
   red (exp_tapp (apply_delta_subst dsubst (exp_tabs K e1)) (apply_delta_subst_typ dsubst t2))
                  (apply_delta_subst dsubst (open_te e1 t2)).
intros.
  generalize dependent e1.
  generalize dependent t2.
  induction H; intros; simpl; auto.
    rewrite subst_te_open_te; eauto using type_from_wf_typ.
    apply IHwf_delta_osubst; auto.
      rewrite <- subst_te_open_te; eauto using type_from_wf_typ.
      assert (exp_tapp (exp_tabs K (subst_te X T e1)) (subst_tt X T t2)
                  = subst_te X T (exp_tapp (exp_tabs K e1) t2)). auto.
      rewrite H3.
      apply red_preserved_under_typsubst; eauto using type_from_wf_typ.
Qed.

Lemma red_abs_preserved_under_gamma_osubst: forall E D dsubst gsubst lgsubst Env lEnv K T e1 e2,
   wf_lgamma_osubst E D dsubst gsubst lgsubst Env lEnv ->
   red (exp_app (exp_abs K T e1) e2) (open_ee e1 e2) ->
   red (exp_app (apply_gamma_subst gsubst (exp_abs K T e1)) (apply_gamma_subst gsubst e2))
                  (apply_gamma_subst gsubst (open_ee e1 e2)).
intros.
  generalize dependent T.
  generalize dependent e1.
  generalize dependent e2.
  induction H; intros; simpl; auto.
    apply typing_regular in H1.  decompose [and] H1.
    rewrite subst_ee_open_ee; auto.
    apply IHwf_lgamma_osubst; auto.
      rewrite <- subst_ee_open_ee; auto.
      assert (exp_app (exp_abs K T0 (subst_ee x e e1)) (subst_ee x e e2)
                  = subst_ee x e (exp_app (exp_abs K T0 e1) e2)) as J. auto.
      rewrite J.
      apply red_preserved_under_expsubst; auto.
Qed.

Lemma red_tabs_preserved_under_gamma_osubst: forall E D dsubst gsubst lgsubst Env lEnv K e1 t2,
   wf_lgamma_osubst E D dsubst gsubst lgsubst Env lEnv ->
   red (exp_tapp (exp_tabs K e1) t2) (open_te e1 t2) ->
   red (exp_tapp (apply_gamma_subst gsubst (exp_tabs K e1)) (apply_gamma_subst_typ gsubst t2))
                  (apply_gamma_subst gsubst (open_te e1 t2)).
intros.
  generalize dependent e1.
  generalize dependent t2.
  induction H; intros; simpl; auto.
    apply typing_regular in H1.  decompose [and] H1.
    rewrite subst_ee_open_te; auto.
    unfold apply_gamma_subst_typ in *.
    apply IHwf_lgamma_osubst; auto.
      rewrite <- subst_ee_open_te; auto.
      assert (exp_tapp (exp_tabs K (subst_ee x e e1)) t2
                  = subst_ee x e (exp_tapp (exp_tabs K e1) t2)) as J. auto.
      rewrite J.
      apply red_preserved_under_expsubst; auto.
Qed.

Lemma red_abs_preserved_under_lgamma_osubst: forall E D dsubst gsubst lgsubst Env lEnv K T e1 e2,
   wf_lgamma_osubst E D dsubst gsubst lgsubst Env lEnv ->
   red (exp_app (exp_abs K T e1) e2) (open_ee e1 e2) ->
   red (exp_app (apply_gamma_subst lgsubst (exp_abs K T e1)) (apply_gamma_subst lgsubst e2))
                  (apply_gamma_subst lgsubst (open_ee e1 e2)).
intros.
  generalize dependent T.
  generalize dependent e1.
  generalize dependent e2.
  induction H; intros; simpl; auto.
    apply typing_regular in H3.  decompose [and] H3.
    rewrite subst_ee_open_ee; auto.
    apply IHwf_lgamma_osubst; auto.
      rewrite <- subst_ee_open_ee; auto.
      assert (exp_app (exp_abs K T0 (subst_ee x e e1)) (subst_ee x e e2)
                  = subst_ee x e (exp_app (exp_abs K T0 e1) e2)) as J. auto.
      rewrite J.
      apply red_preserved_under_expsubst; auto.
Qed.

Lemma red_tabs_preserved_under_lgamma_osubst: forall E D dsubst gsubst lgsubst Env lEnv K e1 t2,
   wf_lgamma_osubst E D dsubst gsubst lgsubst Env lEnv ->
   red (exp_tapp (exp_tabs K e1) t2) (open_te e1 t2) ->
   red (exp_tapp (apply_gamma_subst lgsubst (exp_tabs K e1)) (apply_gamma_subst_typ lgsubst t2))
                  (apply_gamma_subst lgsubst (open_te e1 t2)).
intros.
  generalize dependent e1.
  generalize dependent t2.
  induction H; intros; simpl; auto.
    apply typing_regular in H3.  decompose [and] H3.
    rewrite subst_ee_open_te; auto.
    unfold apply_gamma_subst_typ in *.
    apply IHwf_lgamma_osubst; auto.
      rewrite <- subst_ee_open_te; auto.
      assert (exp_tapp (exp_tabs K (subst_ee x e e1)) t2
                  = subst_ee x e (exp_tapp (exp_tabs K e1) t2)) as J. auto.
      rewrite J.
      apply red_preserved_under_expsubst; auto.
Qed.

Lemma congr_fst : forall Env lEnv e v T1 T2,
  typing Env lEnv e (typ_with T1 T2) ->
  normalize e v ->
  exists e1, exists e2, bigstep_red (exp_fst e) e1 /\ v = exp_apair e1 e2.
Proof.
  intros Env lEnv e v T1 T2 Htyping Hnorm.
  destruct Hnorm as [Hbrc Hv].
  induction Hbrc; intros.
    apply ocanonical_form_with in Htyping; auto.
    destruct Htyping as [e1 [e2 Htyping]]; subst. 
    inversion Hv; subst.
    exists(e1). exists(e2).
    split; eauto.

    destruct (@IHHbrc) as [e1 [e2 [Hbrc' Heq]]]; auto.
       apply preservation with (e:=e); auto.
    exists (e1). exists(e2).
    split; auto.
         apply bigstep_red_trans with (e':=exp_fst e'); auto.
Qed.

Lemma congr_snd : forall Env lEnv e v T1 T2,
  typing Env lEnv e (typ_with T1 T2) ->
  normalize e v ->
  exists e1, exists e2, bigstep_red (exp_snd e) e2 /\ v = exp_apair e1 e2.
Proof.
  intros Env lEnv e v T1 T2 Htyping Hnorm.
  destruct Hnorm as [Hbrc Hv].
  induction Hbrc; intros.
    apply ocanonical_form_with in Htyping; auto.
    destruct Htyping as [e1 [e2 Htyping]]; subst. 
    inversion Hv; subst.
    exists(e1). exists(e2).
    split; eauto.

    destruct (@IHHbrc) as [e1 [e2 [Hbrc' Heq]]]; auto.
       apply preservation with (e:=e); auto.
    exists (e1). exists(e2).
    split; auto.
         apply bigstep_red_trans with (e':=exp_snd e'); auto.
Qed.

(* ********************************************************************** *)
(* weaken stronger *)
Lemma odsubst_stronger : forall E E' dsubst dsubst' X K t Env,
  wf_delta_osubst (E'++[(X,bind_kn K)]++E) (dsubst'++[(X,t)]++dsubst) Env ->
  wf_typ Env t K ->
  ddom_env E [=] dom dsubst ->
  ddom_env E' [=] dom dsubst' ->
  X `notin` (fv_env E `union` fv_env E')->
  wf_delta_osubst (E'++E) (dsubst'++dsubst) Env.
Proof.
  intros E E' dsubst dsubst' X K t Env Hwf_dsubst HT HdomE HdomE' HX.
  remember (E'++[(X,bind_kn K)]++E) as G.
  remember (dsubst'++[(X,t)]++dsubst) as dsG.
  generalize dependent E'.
  generalize dependent dsubst'.
  (wf_delta_osubst_cases (induction Hwf_dsubst) Case); intros; subst.
  Case "wf_delta_osubst_empty".
    contradict HeqG; auto.
  Case "wf_delta_osubst_styp".
    apply one_eq_app in HeqG. destruct HeqG as [[E'' [EQ1 EQ2]] |  [EQ1 EQ2]]; subst.
      apply one_eq_app in HeqdsG. destruct HeqdsG as [[dsE'' [dsEQ1 dsEQ2]] | [dsEQ1 dsEQ2]]; subst.
        simpl_env.
        apply wf_delta_osubst_styp; simpl in *; auto.
          apply IHHwf_dsubst; auto.
            apply ddom_dom__inv with (X:=X0)(b:=t)(K:=K); auto.
              apply dom_delta_osubst in Hwf_dsubst. 
              destruct_notin. apply dom__ddom in H.
              rewrite Hwf_dsubst in H. simpl_env in H. auto.

        inversion dsEQ2. subst.
        simpl in *. destruct_notin.
        contradict NotInTac; auto.

      apply one_eq_app in HeqdsG. 
      destruct HeqdsG as [[dsE'' [dsEQ1 dsEQ2]] | [dsEQ1 dsEQ2]]; subst.
        simpl_env in HdomE'.
        assert (X0 `notin` (singleton X0 `union` dom dsE'') -> False).
          intro. destruct_notin. contradict NotInTac0; auto.
        rewrite <- HdomE' in H1.
        contradict H1; auto.

        inversion dsEQ2. inversion EQ2. subst. auto.
  Case "wf_delta_osubst_skip".
    apply one_eq_app in HeqG. destruct HeqG as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      simpl_env in *. simpl in HX.
      apply wf_delta_osubst_skip; auto.
        apply IHHwf_dsubst; auto.
          rewrite <- HdomE'. simpl. clear. fsetdec.
        apply wf_typ_strengthening_typ in H0; auto.

      inversion EQ2.
Qed.

Lemma odsubst_weaken : forall E E' dsubst dsubst' X K t Env,
  wf_delta_osubst (E'++E) (dsubst'++dsubst) Env ->
  wf_typ Env t K ->
  ddom_env E [=] dom dsubst ->
  ddom_env E' [=] dom dsubst' ->
  X `notin` (dom E `union` dom E' `union` dom Env)->
  wf_delta_osubst (E'++[(X,bind_kn K)]++E) (dsubst'++[(X,t)]++dsubst) Env.
Proof.
  intros E E' dsubst dsubst' X K t Env Hwf_dsubst HT HdomE HdomE' HX.
  remember (E'++E) as G.
  remember (dsubst'++dsubst) as dsG.
  generalize dependent E'.
  generalize dependent dsubst'.
  (wf_delta_osubst_cases (induction Hwf_dsubst) Case); intros; subst.
  Case "wf_delta_osubst_empty".
    destruct dsubst.
      destruct dsubst'; inversion HeqdsG.
         destruct E.
            destruct E'; inversion HeqG.
              rewrite_env ([(X, bind_kn K)]++nil).
              rewrite_env ([(X, t)]++nil).
              eapply wf_delta_osubst_styp with (E:=(@nil (atom*binding))) (X:=X) (SE:=delta_nil) (T:=t); eauto.
            inversion HeqG.
          destruct E'; inversion HeqG.
      destruct dsubst'; inversion HeqdsG.
  Case "wf_delta_osubst_styp".
    apply one_eq_app in HeqG. destruct HeqG as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      apply one_eq_app in HeqdsG. destruct HeqdsG as [[dsE'' [dsEQ1 dsEQ2]] | [dsEQ1 dsEQ2]]; subst.
        simpl_env.
        apply wf_delta_osubst_styp; auto.
          apply IHHwf_dsubst; auto.
            apply ddom_dom__inv with (X:=X0)(b:=t)(K:=K); auto.
              apply dom_delta_osubst in Hwf_dsubst.
              destruct_notin. apply dom__ddom in H.
              rewrite Hwf_dsubst in H. simpl_env in H. auto.

        simpl in HdomE'.
        assert (X0 `notin` (singleton X0 `union` ddom_env E'') -> False).
          intro. destruct_notin. contradict NotInTac0; auto. 
        rewrite HdomE' in H1.
        contradict H1; auto. 

    apply one_eq_app in HeqdsG. 
    destruct HeqdsG as [[dsE'' [dsEQ1 dsEQ2]] | [dsEQ1 dsEQ2]]; subst.
      simpl_env in HdomE'.
      assert (X0 `notin` (singleton X0 `union` dom dsE'') -> False).
          intro. destruct_notin. contradict NotInTac0; auto. 
      rewrite <- HdomE' in H1.
      contradict H1; auto. 

      clear HdomE'.
      simpl_env.
      apply wf_delta_osubst_styp; auto.
  Case "wf_delta_osubst_skip".
    apply one_eq_app in HeqG. destruct HeqG as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      simpl_env. apply wf_delta_osubst_skip; auto.
        apply wf_typ_weakening; auto.
          apply uniq_insert_mid; auto.
            apply wf_delta_osubst__uniq in Hwf_dsubst.
            decompose [and] Hwf_dsubst; auto.    

      simpl in HdomE'.
      assert (dom dsubst' [=] {}). rewrite HdomE'. fsetdec.
      apply dom_empty_inv in H1. subst.
      simpl_env in *. apply wf_delta_osubst_styp; auto.
Qed.

Lemma odsubst_weaken_head : forall E dsubst X K t Env,
  wf_delta_osubst E dsubst Env ->
  wf_typ Env t K ->
  ddom_env E [=] dom dsubst ->
  X `notin` (dom E `union` dom Env)->
  wf_delta_osubst ([(X,bind_kn K)]++E) ([(X,t)]++dsubst) Env.
Proof.
  intros E dsubst X K t Env Hwf_dsubst Ht HdomE HX.
    apply odsubst_weaken with (K:=K) (t:=t) (E:=E) (E':=(@nil (atom*binding))) (dsubst:=dsubst) (dsubst':=delta_nil) (X:=X); simpl_env; eauto.
Qed.

Lemma typing_odsubst_stronger : forall v E dsubst dsubst' X t T Env lEnv,
  typing Env lEnv v (apply_delta_subst_typ (dsubst'++[(X,t)]++dsubst) T)->
  wf_delta_osubst E (dsubst'++[(X,t)]++dsubst) Env ->
  X `notin` ((fv_tt T) `union` dom Env)->
  typing Env lEnv v (apply_delta_subst_typ (dsubst'++dsubst) T).
Proof.
  intros.
  remember (dsubst'++[(X,t)]++dsubst) as dsG.
  generalize dependent dsubst'.
  generalize dependent T.
  (wf_delta_osubst_cases (induction H0) Case); intros; subst.
  Case "wf_delta_osubst_empty".
    contradict HeqdsG; auto.
  Case "wf_delta_osubst_styp".
      apply one_eq_app in HeqdsG. destruct HeqdsG as [[dsubst'' [dsEQ1 dsEQ2]] | [dsEQ1 dsEQ2]]; subst.
        simpl_env. simpl_env in H2. simpl.
        apply IHwf_delta_osubst with (dsubst':=dsubst''); auto.
          assert (X `notin` fv_tt T).
            apply notin_fv_wf with (E:=Env)(K:=k); auto.
          assert (X `notin` fv_tt (subst_tt X0 T T0)).
            apply notin_fv_tt_subst_tt; auto.
          simpl_env in*. auto.

        inversion dsEQ2. subst. clear dsEQ2.
        simpl in H2. rewrite <- subst_tt_fresh in H2; auto.
  Case "wf_delta_osubst_skip".
      apply IHwf_delta_osubst with (dsubst'0:=dsubst'); auto.
Qed.

Lemma typing_odsubst_weaken :  forall v E dsubst dsubst' X T t Env lEnv,
  typing  Env lEnv v (apply_delta_subst_typ (dsubst'++dsubst) T)->
  wf_delta_osubst E (dsubst'++dsubst) Env ->
  X `notin` (fv_tt T)`union` dom Env ->
  typing  Env lEnv v (apply_delta_subst_typ (dsubst'++[(X,t)]++dsubst) T).
Proof.
  intros.
  remember (dsubst'++dsubst) as dsG.
  generalize dependent dsubst'.
  generalize dependent dsubst.
  generalize dependent T.
  (wf_delta_osubst_cases (induction H0) Case); intros; subst.
  Case "wf_delta_osubst_empty".
    apply nil_eq_app in HeqdsG. destruct HeqdsG. subst.
    simpl in H. simpl.
    rewrite <- subst_tt_fresh; auto.
  Case "wf_delta_osubst_styp".
    apply one_eq_app in HeqdsG. destruct HeqdsG as [[dsE'' [dsEQ1 dsEQ2]] | [dsEQ1 dsEQ2]]; subst.
        simpl. simpl_env.
        apply IHwf_delta_osubst with (dsubst0:=dsubst) (dsubst':=dsE''); auto.
          assert (X `notin` fv_tt T); eauto using notin_fv_wf.
          assert (X `notin` fv_tt (subst_tt X0 T T0)).
            apply notin_fv_tt_subst_tt; auto.
          simpl_env in *. auto.

        simpl in H2. simpl. rewrite <- subst_tt_fresh with (T:=T0); auto.
  Case "wf_delta_osubst_skip".
    apply IHwf_delta_osubst with (dsubst0:=dsubst) (dsubst'0:=dsubst'); auto.
Qed.

Lemma typing_odsubst_weaken_head :  forall v E dsubst X T t Env lEnv,
  typing  Env lEnv v (apply_delta_subst_typ dsubst T)->
  wf_delta_osubst E dsubst Env ->
  X `notin` (fv_tt T) `union` dom Env ->
  typing  Env lEnv v (apply_delta_subst_typ ([(X,t)]++dsubst) T).
Proof.
  intros v E dsubst X T t  Env lEnv Htyping Hwfd Hfv.
  apply typing_odsubst_weaken with (E:=E)
            (dsubst:=dsubst) (dsubst':=delta_nil) (X:=X) (T:=T) (t:=t); simpl_env; eauto.
Qed.

(* ********************************************************************** *)
(** * Inversion *)

Lemma wf_lgamma_osubst__nfv : forall E D dsubst gsubst lgsubst Env lEnv x,
  wf_lgamma_osubst E D dsubst gsubst lgsubst Env lEnv ->
  x `notin` dom E ->
  x `notin` dom D ->
  x `notin` dom dsubst /\ x `notin` dom gsubst /\ x `notin` dom lgsubst 
     /\ x `notin` fv_env E /\ x `notin` fv_lenv D.
intros E D dsubst gsubst lgsubst Env lEnv x Hwfg Hfv Hfv'.
  induction Hwfg; intros; auto.
    apply notin_fv_wf with (X:=x) in H1; simpl; auto.    
    apply notin_fv_wf with (X:=x) in H3; simpl; auto.    
    simpl in Hfv; simpl; auto.
Qed.

Lemma wf_lgamma_osubst__wf_delta_osubst : forall E D dsubst gsubst lgsubst Env lEnv,
  wf_lgamma_osubst E D dsubst gsubst lgsubst Env lEnv->
  wf_delta_osubst E dsubst Env.
intros.
  induction H; auto.
Qed.


Lemma wf_lgamma_osubst__wf_osubst : forall E D dsubst gsubst lgsubst Env lEnv,
  wf_lgamma_osubst E D dsubst gsubst lgsubst Env lEnv ->
  wf_gamma_osubst E dsubst gsubst Env /\ wf_delta_osubst E dsubst Env.
intros.
  induction H; auto.
    destruct IHwf_lgamma_osubst as [J1 J2].
    split.
      apply wf_gamma_osubst_sval; auto.
      apply wf_delta_osubst_skip; auto.

    destruct IHwf_lgamma_osubst as [J1 J2].
    split.
      apply wf_gamma_osubst_skind; auto.
      apply wf_delta_osubst_styp; auto.
Qed.

Lemma delta_gamma_lgamma_osubst_value : forall E D dsubst gsubst lgsubst Env lEnv v,
  wf_lgamma_osubst E D dsubst gsubst lgsubst Env lEnv ->
  wf_delta_osubst E dsubst Env ->
  value v ->
  value(apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst v))).
Proof.
  intros.
  eapply delta_osubst_value; eauto.
  eapply gamma_osubst_value; eauto.
  eapply lgamma_osubst_value; eauto.
Qed.

Lemma wf_lgamma_osubst_disjoint : forall E lE dsubst gsubst lgsubst Env lEnv,
  wf_lgamma_osubst E lE dsubst gsubst lgsubst Env lEnv ->
  disjoint E lE /\ disjoint dsubst lgsubst /\ disjoint gsubst lgsubst /\
  disjoint E lgsubst /\ disjoint lE dsubst /\ disjoint lE gsubst.
Proof.
  intros E lE dsubst gsubst lgsubst Env lEnv H.
  induction H; auto.
    unfold disjoint. 
    repeat(split; try solve [fsetdec]).

    decompose [and] IHwf_lgamma_osubst.
    apply wf_lgamma_osubst__nfv with (x:=x) in H; auto.
    decompose [and] H.
    repeat(split; try solve [solve_uniq]).

    decompose [and] IHwf_lgamma_osubst.
    apply wf_lgamma_osubst__nfv with (x:=x) in H; auto.
    decompose [and] H.
    repeat(split; try solve [solve_uniq]).

    decompose [and] IHwf_lgamma_osubst.
    apply wf_lgamma_osubst__nfv with (x:=X) in H; auto.
    decompose [and] H.
    repeat(split; try solve [solve_uniq]).
Qed.

Lemma bindosgE__bindsE : forall E D dsubst gsubst lgsubst Env lEnv x t,
  wf_lgamma_osubst E D dsubst gsubst lgsubst Env lEnv ->
  binds x (bind_typ t) E ->
  x `notin` dom lgsubst /\
  exists e, binds x (e) gsubst /\ typing Env nil e (apply_delta_subst_typ dsubst t) 
                   /\ disjdom (fv_te e) (dom dsubst) /\ disjdom (fv_ee e) (dom gsubst) /\ disjdom (fv_ee e) (dom lgsubst).
intros E D dsubst gsubst lgsubst Env lEnv x t Hwfg Hbinds.
  generalize dependent t.
  induction Hwfg; intros; analyze_binds Hbinds.
    inversion BindsTacVal; subst.
    assert (J:=Hwfg).
    apply wf_lgamma_osubst__nfv with (x:=x0) in J; auto.
    decompose [and] J. clear J.
    split; auto.
      exists e. split; auto. split; auto.  
      assert (J := @disjoint_lgamma_osubst E lE dsE gsE lgsE Env lEnv Hwfg).
      destruct J as [J1 [J2 [J3 [J4 [J5 [J6 [J7 [J8 [J9 J10]]]]]]]]].
      unfold disjdom.
      split. 
        split; intros x xnotin.
          apply in_fv_te_typing with (X:=x) in H0; auto. 
          clear J1 J2 J4 J5 J6 J7 J8 J9 J10. solve_uniq.

          apply notin_fv_te_typing with (X:=x) in H0; auto.
          clear J1 J2 J4 J5 J6 J7 J8 J9 J10. solve_uniq.
      split. 
        split; intros x xnotin.
          destruct (x == x0); subst.
            apply in_fv_ee_typing with (x:=x0) in H0; auto.
            destruct_notin. contradict NotInTac0; auto. 
            clear J1 J3 J4 J5 J6 J7 J8 J9 J10. solve_uniq.

            apply in_fv_ee_typing with (x:=x) in H0; auto.
            assert (x `in` dom Env \/ x `in` {}) as J. fsetdec.
            destruct J as [J | J].
              assert (x `notin` dom gsE) as JJ.
                clear J1 J2 J3 J5 J6 J7 J8 J9 J10. solve_uniq.
              clear J1 J2 J3 J5 J6 J7 J8 J9 J10. solve_uniq.

              contradict J; auto.
          simpl in xnotin.
          apply notin_fv_ee_typing with (y:=x) in H0; auto.
          assert (x `in` {{x0}} \/ x `in` dom gsE) as J. fsetdec.
          destruct J as [J | J].
             fsetdec.
             clear J1 J2 J3 J5 J6 J7 J8 J9 J10. solve_uniq.

        split; intros x xnotin.
          apply in_fv_ee_typing with (x:=x) in H0; auto. 
          clear J1 J2 J3 J4 J6 J7 J8 J9 J10. solve_uniq.
          apply notin_fv_ee_typing with (y:=x) in H0; auto. 
          clear J1 J2 J3 J4 J6 J7 J8 J9 J10. solve_uniq.

    apply IHHwfg in BindsTac.
    destruct BindsTac as [J [e' [Hb [Ht [Disj1 [Disj2 Disj3]]]]]].
    split; auto.
      exists (e'). split;auto. split;auto.
      assert (JJ := @disjoint_lgamma_osubst E lE dsE gsE lgsE Env lEnv Hwfg).
      destruct JJ as [J1 [J2 [J3 [J4 [J5 [J6 [J7 [J8 [J9 J10]]]]]]]]].
      unfold disjdom.
      split. 
        split; intros x1 x1notin.
          apply in_fv_te_typing with (X:=x1) in Ht; auto. 
          clear J1 J2 J4 J5 J6 J7 J8 J9 J10. solve_uniq.

          apply notin_fv_te_typing with (X:=x1) in Ht; auto. 
          clear J1 J2 J4 J5 J6 J7 J8 J9 J10. solve_uniq.
      split. 
        split; intros x1 x1notin.
          destruct (x1 == x0); subst.
            apply in_fv_ee_typing with (x:=x0) in Ht; auto.
            destruct_notin. contradict NotInTac0; auto. fsetdec.

            apply in_fv_ee_typing with (x:=x1) in Ht; auto.
            assert (x1 `in` dom Env \/ x1 `in` {}) as JJ. fsetdec.
            destruct JJ as [JJ | JJ].
              assert (x1 `notin` dom gsE) as JJ'. 
                clear J1 J2 J3 J5 J6 J7 J8 J9 J10. solve_uniq.
              clear J1 J2 J3 J5 J6 J7 J8 J9 J10. solve_uniq.

              contradict JJ; auto.
          simpl in x1notin.
          apply notin_fv_ee_typing with (y:=x1) in Ht; auto.
          assert (x1 `in` {{x0}} \/ x1 `in` dom gsE) as JJ. fsetdec.
          destruct JJ as [JJ | JJ].
             fsetdec.
             clear J1 J2 J3 J5 J6 J7 J8 J9 J10. solve_uniq.

        split; intros x1 x1notin.
          apply in_fv_ee_typing with (x:=x1) in Ht; auto. 
          clear J1 J2 J3 J4 J6 J7 J8 J9 J10. solve_uniq.
          apply notin_fv_ee_typing with (y:=x1) in Ht; auto. 
          clear J1 J2 J3 J4 J6 J7 J8 J9 J10. solve_uniq.

    assert (H5:=Hbinds).
    apply IHHwfg in H5.
    destruct H5 as [J [e' [Hb [Ht [Disj1 [Disj2 Disj3]]]]]].
    split; auto.
      apply binds_In in Hbinds.
      destruct (x==x0); subst; auto.

      exists (e'). split;auto. split;auto.
      assert (JJ := @disjoint_lgamma_osubst E lE dsE gsE lgsE Env lEnv1 Hwfg).
      destruct JJ as [J1 [J2 [J3 [J4 [J5 [J6 [J7 [J8 [J9 J10]]]]]]]]].
      unfold disjdom.
      split. 
        split; intros x1 x1notin.
          apply in_fv_te_typing with (X:=x1) in Ht; auto. 
          clear J1 J2 J4 J5 J6 J7 J8 J9 J10 H0 H1 Disj1 Disj2 Disj3. solve_uniq.

          apply notin_fv_te_typing with (X:=x1) in Ht; auto. 
          clear J1 J2 J4 J5 J6 J7 J8 J9 J10 H0 H1 Disj1 Disj2 Disj3. solve_uniq.
      split. 
        split; intros x1 x1notin.
          apply in_fv_ee_typing with (x:=x1) in Ht; auto. 
          clear J1 J2 J3 J5 J6 J7 J8 J9 J10 H0 H1 Disj1 Disj2 Disj3. solve_uniq.
          apply notin_fv_ee_typing with (y:=x1) in Ht; auto. 
          clear J1 J2 J3 J5 J6 J7 J8 J9 J10 H0 H1 Disj1 Disj2 Disj3. solve_uniq.

        split; intros x1 x1notin.
          destruct (x1 == x0); subst.
            apply in_fv_ee_typing with (x:=x0) in Ht; auto.
            destruct_notin. contradict NotInTac0; auto. fsetdec.

            apply in_fv_ee_typing with (x:=x1) in Ht; auto.
            assert (x1 `in` dom Env \/ x1 `in` {}) as JJ. fsetdec.
            destruct JJ as [JJ | JJ].
              assert (x1 `notin` dom lgsE) as JJ'. 
                clear J1 J2 J3 J4 J6 J7 J8 J9 J10 H0 H1 Disj1 Disj2 Disj3. solve_uniq.
              clear J1 J2 J3 J4 J6 J7 J8 J9 J10 H0 H1 Disj1 Disj2 Disj3. solve_uniq.

              contradict JJ; auto.
          simpl in x1notin.
          apply notin_fv_ee_typing with (y:=x1) in Ht; auto.
          assert (x1 `in` {{x0}} \/ x1 `in` dom lgsE) as JJ. fsetdec.
          destruct JJ as [JJ | JJ].
             fsetdec.
             clear J1 J2 J3 J4 J6 J7 J8 J9 J10 H0 H1 Disj1 Disj2 Disj3. solve_uniq.

    apply IHHwfg in BindsTac; auto.
    destruct BindsTac as [J [e' [Hb [Ht [Disj1 [Disj2 Disj3]]]]]].
    split; auto.
      simpl. rewrite -> delta_osubst_permut with (dE:=E)(K:=k) (Env:=Env); auto.
        rewrite <-subst_tt_fresh; auto.
          exists (e'). split;auto. split;auto.
          assert (JJ := @disjoint_lgamma_osubst E lE dsE gsE lgsE Env lEnv Hwfg).
          destruct JJ as [J1 [J2 [J3 [J4 [J5 [J6 [J7 [J8 [J9 J10]]]]]]]]].
          unfold disjdom.
          split. 
            split; intros x0 x0notin.
              destruct (x0 == X); subst.
                apply in_fv_te_typing with (X:=X) in Ht; auto.
                apply in_fv_te_typing with (X:=x0) in Ht; auto.
                assert (x0 `notin` dom dsE) as JJ.
                  clear J1 J2 J4 J5 J6 J7 J8 J9 J10. solve_uniq.
                clear J1 J2 J4 J5 J6 J7 J8 J9 J10. solve_uniq.

                assert (x0 `in` dom dsE \/ x0 `in` {{X}}) as JJ. fsetdec.
                destruct JJ as [JJ | JJ].
                  apply notin_fv_te_typing with (X:=x0) in Ht; auto. 
                  clear J1 J2 J4 J5 J6 J7 J8 J9 J10. solve_uniq.

                  apply notin_fv_te_typing with (X:=X) in Ht; auto. 
                   fsetdec.
          split.
            split; intros x0 x0notin.
              apply in_fv_ee_typing with (x:=x0) in Ht; auto. 
              clear J1 J2 J3 J5 J6 J7 J8 J9 J10. solve_uniq.
              apply notin_fv_ee_typing with (y:=x0) in Ht; auto. 
              clear J1 J2 J3 J5 J6 J7 J8 J9 J10. solve_uniq.
    
            split; intros x0 x0notin.
              apply in_fv_ee_typing with (x:=x0) in Ht; auto. 
              clear J1 J2 J3 J4 J6 J7 J8 J9 J10. solve_uniq.
              apply notin_fv_ee_typing with (y:=x0) in Ht; auto. 
              clear J1 J2 J3 J4 J6 J7 J8 J9 J10. solve_uniq.

          apply notin_fv_wf with (E:=Env) (K:=kn_lin); auto.

        apply wf_lgamma_osubst__wf_osubst in Hwfg; auto.
          destruct Hwfg; auto.
        apply wf_lgamma_osubst__nfv with (x:=X) in Hwfg; auto.
Qed.

Lemma wf_lgamma_osubst_empty_linctx : forall E D dsubst gsubst lgsubst Env lEnv,
  wf_lgamma_osubst E D dsubst gsubst lgsubst Env lEnv ->
  dom D [=] {} ->
  dom lEnv [=] {}.
Proof.
  intros E D dsubst gsubst lgsubst Env lEnv Hwfg Dom.
  induction Hwfg; auto.
    assert (x `in` dom ([(x, lbind_typ T)]++lE)) as J. simpl. auto.
    rewrite Dom in J.
    contradict J; auto.
Qed.

Lemma lbindosgE__bindslE : forall E dsubst gsubst lgsubst Env lEnv x t,
  wf_lgamma_osubst E [(x, lbind_typ t)] dsubst gsubst lgsubst Env lEnv ->
  x `notin` dom gsubst /\
  exists e, binds x (e) lgsubst /\ typing Env lEnv e (apply_delta_subst_typ dsubst t) /\
                   disjdom (fv_te e) (dom dsubst) /\ disjdom (fv_ee e) (dom gsubst) /\ disjdom (fv_ee e) (dom lgsubst).
intros E dsubst gsubst lgsubst Env lEnv x t Hwfg.
  remember ([(x, lbind_typ t)]) as D.
  generalize dependent t.
  induction Hwfg; intros; subst.
    inversion HeqD.

    destruct (@IHHwfg t) as [J [e' [Hb [Ht [Disj1 [Disj2 Disj3]]]]]]; auto.
    split; auto.
      exists (e'). 
      split;auto. split; auto. split; auto. split; auto.
        assert (JJ := @disjoint_lgamma_osubst E [(x, lbind_typ t)] dsE gsE lgsE Env lEnv Hwfg).
        destruct JJ as [J1 [J2 [J3 [J4 [J5 [J6 [J7 [J8 [J9 J10]]]]]]]]].
        unfold disjdom.
        split; intros x1 x1notin.
          destruct (x1 == x0); subst.
            apply in_fv_ee_typing with (x:=x0) in Ht; auto.

            apply in_fv_ee_typing with (x:=x1) in Ht; auto.
            assert (x1 `in` dom Env \/ x1 `in` dom lEnv) as JJ. fsetdec.
            destruct JJ as [JJ | JJ].
              assert (x1 `notin` dom gsE) as JJ'. 
                clear J1 J2 J3 J5 J6 J7 J8 J9 J10. solve_uniq.
              clear J1 J2 J3 J5 J6 J7 J8 J9 J10. solve_uniq.

              assert (x1 `notin` dom gsE) as JJ'. 
                clear J1 J2 J3 J4 J5 J6 J7 J8 J9 Disj1 Disj2 Disj3 n. solve_uniq.
              clear J1 J2 J3 J4 J5 J6 J7 J8 J9 J10 Disj1 Disj2 Disj3. solve_uniq.
          simpl in x1notin.
          apply notin_fv_ee_typing with (y:=x0) in Ht; auto.
          assert (x1 `in` {{x0}} \/ x1 `in` dom gsE) as JJ. fsetdec.
          destruct JJ as [JJ | JJ].
             fsetdec.
             destruct Disj2 as [Disj21 Disj22]; auto.

    inversion HeqD; subst.
    assert (J:=Hwfg).
    apply wf_lgamma_osubst__nfv with (x:=x) in J; auto.
    decompose [and] J. clear J.
    split; auto.
      assert (dom lEnv1 [=] {}) as lEnv1Nil.
        apply wf_lgamma_osubst_empty_linctx in Hwfg; auto.
      apply empty_dom__empty_ctx in lEnv1Nil. subst. simpl.
      assert (J := @disjoint_lgamma_osubst E lempty dsE gsE lgsE Env lempty Hwfg).
      destruct J as [J1 [J2 [J3 [J4 [J5 [J6 [J7 [J8 [J9 J10]]]]]]]]].
      simpl_env.
      exists e. split; auto. split; auto.
      unfold disjdom.
      split. 
        split; intros x0 x0notin.
          apply in_fv_te_typing with (X:=x0) in H2; auto. 
          clear J1 J2 J4 J5 J6 J7 J8 J9 J10 H5 H7 H6 H9 H0 H1. solve_uniq.

          apply notin_fv_te_typing with (X:=x0) in H2; auto.
          clear J1 J2 J4 J5 J6 J7 J8 J9 J10 H5 H7 H6 H9 H0 H1. solve_uniq.
      split. 
        split; intros x0 x0notin.
          destruct (x == x0); subst.
            apply in_fv_ee_typing with (x:=x0) in H2; auto.

            apply in_fv_ee_typing with (x:=x0) in H2; auto.
            assert (x0 `in` dom Env \/ x0 `in` dom lEnv2) as J. fsetdec.
            destruct J as [J | J].
              clear J1 J2 J3 J5 J6 J7 J8 J9 J10 H5 H7 H6 H9 H0 H1 H. solve_uniq.

              assert (gdom_env E [=] dom gsE) as EQ1.
                apply dom_lgamma_osubst in Hwfg. decompose [and] Hwfg; auto.
              assert (dom E [=] ddom_env E `union` gdom_env E) as EQ2.
                apply dom__ddom_gdom; auto.
              rewrite <- EQ1.
              assert (x0 `notin` dom E) as JJ.
                destruct H0.
                clear J1 J2 J3 J4 J5 J6 J7 J8 J9 J10 H5 H7 H6 H9 H1 H. solve_uniq.
              rewrite EQ2 in JJ. auto.
          apply notin_fv_ee_typing with (y:=x0) in H2; auto.
            assert (x0 `notin` dom Env) as xnotinEnv.
              clear J1 J2 J3 J5 J6 J7 J8 J9 J10 H5 H7 H6 H9 H1 H2 H. solve_uniq.
            assert (x0 `notin` dom lEnv2) as x0notinlEnv2.
              assert (gdom_env E [=] dom gsE) as EQ1.
                apply dom_lgamma_osubst in Hwfg. decompose [and] Hwfg; auto.
              assert (dom E [=] ddom_env E `union` gdom_env E) as EQ2.
                apply dom__ddom_gdom; auto.
              assert (x0 `in` dom E) as JJ.
                rewrite EQ2. rewrite EQ1. auto.
              clear J1 J2 J3 J4 J5 J6 J7 J8 J9 J10 H5 H7 H6 H9 H1 H. solve_uniq.
           auto.
        split; intros x0 x0notin.
          destruct (x == x0); subst.
            apply in_fv_ee_typing with (x:=x0) in H2; auto.
            destruct_notin. contradict H2; auto.

            apply in_fv_ee_typing with (x:=x0) in H2; auto.
            assert (x0 `in` dom Env \/ x0 `in` dom lEnv2) as J. fsetdec.
            destruct J as [J | J].
              assert (x0 `notin` dom lgsE) as xnotinlgsE.
                clear J1 J2 J3 J4 J6 J7 J8 J9 J10 H5 H7 H6 H9 H0 H1 H. solve_uniq.
              auto.

              assert ({} [=] dom lgsE) as EQ1.
                apply dom_lgamma_osubst in Hwfg. decompose [and] Hwfg; auto.
              rewrite <- EQ1. auto.
          simpl in x0notin.
          apply notin_fv_ee_typing with (y:=x0) in H2; auto.
            assert (x0 `in` {{x}} \/ x0 `in` dom lgsE) as JJ. fsetdec.
            destruct JJ as [JJ | JJ].
               clear J1 J2 J3 J4 J5 J6 J7 J8 J9 J10 H5 H7 H6 H9 H1 H2. fsetdec.

               assert ({} [=] dom lgsE) as EQ1.
                 apply dom_lgamma_osubst in Hwfg. decompose [and] Hwfg; auto.
               rewrite <- EQ1 in JJ.
               contradict JJ; auto. 

    destruct (@IHHwfg t) as [J [e' [Hb [Ht [Disj1 [Disj2 Disj3]]]]]]; auto.
    split; auto.
      simpl. rewrite -> delta_osubst_permut with (dE:=E)(K:=k) (Env:=Env); auto.
        rewrite <-subst_tt_fresh; auto.
          exists (e'). split;auto. split;auto. split;auto.
          assert (JJ := @disjoint_lgamma_osubst E [(x, lbind_typ t)] dsE gsE lgsE Env lEnv Hwfg).
          destruct JJ as [J1 [J2 [J3 [J4 [J5 [J6 [J7 [J8 [J9 J10]]]]]]]]].
          unfold disjdom.
          split; intros x0 x0notin.
              destruct (x0 == X); subst.
                apply in_fv_te_typing with (X:=X) in Ht; auto.
                apply in_fv_te_typing with (X:=x0) in Ht; auto.
                assert (x0 `notin` dom dsE) as JJ.
                  clear J1 J2 J4 J5 J6 J7 J8 J9 J10. solve_uniq.
                clear J1 J2 J4 J5 J6 J7 J8 J9 J10. solve_uniq.

                assert (x0 `in` dom dsE \/ x0 `in` {{X}}) as JJ. fsetdec.
                destruct JJ as [JJ | JJ].
                  apply notin_fv_te_typing with (X:=x0) in Ht; auto. 
                  clear J1 J2 J4 J5 J6 J7 J8 J9 J10. solve_uniq.

                  apply notin_fv_te_typing with (X:=X) in Ht; auto. 
                   fsetdec.

          apply notin_fv_wf with (E:=Env) (K:=kn_lin); auto.

        apply wf_lgamma_osubst__wf_osubst in Hwfg; auto.
          destruct Hwfg; auto.
        apply wf_lgamma_osubst__nfv with (x:=X) in Hwfg; auto.
Qed.


Lemma wf_lgamma_osubst__uniq : forall E D dsubst gsubst lgsubst Env lEnv,
  wf_lgamma_osubst E D dsubst gsubst lgsubst Env lEnv -> 
  uniq gsubst /\ uniq lgsubst /\ uniq E /\ uniq D /\ uniq Env /\ uniq lEnv.
Proof.
  intros.
  induction H; auto.
    repeat (split; auto).

    decompose [and] IHwf_lgamma_osubst.
    repeat (split; auto).
      apply uniq_push; auto.
        apply wf_lgamma_osubst__nfv with (x:=x) in H; auto.

    apply wf_lgamma_osubst__nfv with (x:=x) in H; auto.
    decompose [and] IHwf_lgamma_osubst.
    repeat (split; auto).
      apply uniq_from_wf_lenv in H2; auto.

    decompose [and] IHwf_lgamma_osubst.
    repeat (split; auto).
Qed.

Lemma bindosdE__bindsT : forall E dsubst X K Env,
  wf_delta_osubst E dsubst Env ->
  binds X (bind_kn K) E ->
  exists T, binds X (T) dsubst /\ wf_typ Env T K /\ disjdom (fv_tt T) (dom dsubst).
intros.
  induction H; intros; analyze_binds H0; subst.
      inversion BindsTacVal; subst.
      exists (T). split;auto. split;auto.
      assert (J := @disjoint_delta_osubst E SE Env H).
      destruct J as [J1 J2].
      unfold disjdom.
      split; intros x xnotin.
        destruct (x == X0); subst.
          apply in_fv_wf with (E:=Env) (K:=k) in xnotin; auto.

          apply in_fv_wf with (E:=Env) (K:=k) in xnotin; auto.
          assert (x `notin` dom SE) as J. solve_uniq.
          simpl. fsetdec.
        simpl in xnotin.
          apply notin_fv_wf with (E:=Env) (K:=k); auto.
          assert (x `in` {{X0}} \/ x `in` dom SE) as J. fsetdec.
          destruct J as [J | J].
            fsetdec.
            solve_uniq.

      apply IHwf_delta_osubst in BindsTac.
      destruct BindsTac as [T' [Hb [Hwft Disj]]].
      exists (T'). split;auto. split;auto.
      assert (J := @disjoint_delta_osubst E SE Env H).
      destruct J as [J1 J2].
      unfold disjdom.
      split; intros x xnotin.
        destruct (x == X0); subst.
          apply in_fv_wf with (E:=Env) (K:=K) in xnotin; auto.

          apply in_fv_wf with (E:=Env) (K:=K) in xnotin; auto.
          assert (x `notin` dom SE) as J. solve_uniq.
          simpl. fsetdec.
        simpl in xnotin.
          apply notin_fv_wf with (E:=Env) (K:=K); auto.
          assert (x `in` {{X0}} \/ x `in` dom SE) as J. fsetdec.
           destruct J as [J | J].
               fsetdec.
               solve_uniq.
Qed.

Lemma wf_delta_osubst__nfv : forall dE dsubst X Env,
  wf_delta_osubst dE dsubst Env -> X `notin` dom dE -> X `notin` dom dsubst.
intros. induction H; auto.
Qed.

Lemma olgamma_stronger_tail : forall E lE dsubst gsubst lgsubst x t e Env lEnv,
  wf_lgamma_osubst E ([(x,lbind_typ t)]++lE) dsubst gsubst ([(x,e)]++lgsubst) Env lEnv ->
  exists lEnv1, exists lEnv2,
    lEnv = lEnv2 ++ lEnv1 /\
    typing Env lEnv2 e (apply_delta_subst_typ dsubst t) /\
    wf_lgamma_osubst E lE dsubst gsubst lgsubst Env lEnv1.
Proof.
  intros E lE dsubst gsubst lgsubst x t e Env lEnv Hwf_lgsubst.
  remember ([(x,lbind_typ t)]++lE) as lE0.
  remember ([(x,e)]++lgsubst) as lgsubst0.
  induction Hwf_lgsubst; intros; subst.
  Case "wf_lgamma_osubst_empty".
    contradict HeqlE0; simpl; auto using nil_cons.
  Case "wf_lgamma_osubst_sval".
    destruct IHHwf_lgsubst as [lEnv1 [lEnv2 [Split [Typing Wfg]]]]; subst; auto.
    exists lEnv1. exists lEnv2. split; auto.
  Case "wf_lgamma_osubst_slval".
    inversion Heqlgsubst0; subst.
    inversion HeqlE0; subst.
    exists (lEnv1). exists (lEnv2). split; auto.
  Case "wf_lgamma_osubst_skind".
    destruct IHHwf_lgsubst as [lEnv1 [lEnv2 [Split [Typing Wfg]]]]; subst; auto.
    exists lEnv1. exists lEnv2. 
    split; auto. split; auto.
      simpl. 
      rewrite <- subst_tt_fresh; auto.
      destruct (in_dec X (fv_tt t)); auto.
        apply wf_lgamma_osubst__wf_osubst in Hwf_lgsubst.
        destruct Hwf_lgsubst as [J1 J2].
        apply in_fv_tt_delta_osubst with (t:=t) (X:=X) in J2; auto.
          apply in_fv_tt_typing with (X:=X) in Typing; auto.
          
          apply dom_delta_osubst in J2.
          rewrite <- J2.
          auto using dom__ddom.
Qed.

Lemma lgamma_osubst_split__lenv_split : forall E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst Env lEnv1 lEnv2 lEnv,
  lgamma_osubst_split E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst Env lEnv1 lEnv2 lEnv ->
  lenv_split Env lEnv1 lEnv2 lEnv.
Proof.
  intros E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst Env lEnv1 lEnv2 lEnv Split.
  induction Split; auto.
  Case "lgamma_osubst_split_empty".
    apply lenv_split_empty.
      apply wf_lgamma_osubst__wf_lenv in H. 
      decompose [and] H; auto.
  Case "lgamma_osubst_split_left".
    decompose [and] H0; auto.
    apply lenv_split_lin_weakening_left; auto.
      apply wf_lenv_merge; auto.
        assert (disjoint lEnv1' lEnv1) as Disj. 
          apply uniq_from_wf_lenv in H1.
          solve_uniq.
        apply disjoint_sym_1.
        apply disjoint_eq with (D1:=lEnv1++lEnv2); auto.
          apply dom_lenv_split in IHSplit.
          rewrite IHSplit; auto.
  Case "lgamma_osubst_split_right".
    decompose [and] H0; auto.
    apply lenv_split_lin_weakening_right; auto.
      apply wf_lenv_merge; auto.
        assert (disjoint lEnv2' lEnv2) as Disj. 
          apply uniq_from_wf_lenv in H1.
          solve_uniq.
        apply disjoint_sym_1.
        apply disjoint_eq with (D1:=lEnv1++lEnv2); auto.
          apply dom_lenv_split in IHSplit.
          rewrite IHSplit; auto.  
Qed.

Lemma lgamma_osubst_split__wf_lgamma_osubst : forall E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst Env lEnv1 lEnv2 lEnv,
  lgamma_osubst_split E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst Env lEnv1 lEnv2 lEnv ->
  wf_lgamma_osubst E lE dsubst gsubst lgsubst Env lEnv. 
Proof.
  intros E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst Env lEnv1 lEnv2 lEnv H.
  (lgamma_osubst_split_cases (induction H) Case); intros; subst; auto.
    destruct H1 as [J1 [J2 J3]].
    apply wf_lgamma_osubst_slval with (lEnv1:=lEnv3) (lEnv2:=lEnv1'); auto.
      apply wf_lenv_merge; auto.
        apply wf_lgamma_osubst__wf_lenv in IHlgamma_osubst_split; auto.
        decompose [and] IHlgamma_osubst_split; auto.

        apply lgamma_osubst_split__lenv_split in H.
        assert (disjoint lEnv1' lEnv1) as Disj. 
          apply uniq_from_wf_lenv in H2.
          solve_uniq.
        apply disjoint_sym_1.
        apply disjoint_eq with (D1:=lEnv1++lEnv2); auto.
          apply dom_lenv_split in H.
          rewrite H; auto.  

    destruct H1 as [J1 [J2 J3]].
    apply wf_lgamma_osubst_slval with (lEnv1:=lEnv3) (lEnv2:=lEnv2'); auto.
      apply wf_lenv_merge; auto.
        apply wf_lgamma_osubst__wf_lenv in IHlgamma_osubst_split; auto.
        decompose [and] IHlgamma_osubst_split; auto.

        apply lgamma_osubst_split__lenv_split in H.
        assert (disjoint lEnv2' lEnv2) as Disj. 
          apply uniq_from_wf_lenv in H2.
          solve_uniq.
        apply disjoint_sym_1.
        apply disjoint_eq with (D1:=lEnv1++lEnv2); auto.
          apply dom_lenv_split in H.
          rewrite H; auto.  
Qed.


(* ********************)
(*** typing lin ctx is derministic *)

Lemma lgamma_osubst_split_nonlin_weakening_typ : forall E G lE dsubst dsubst' gsubst lgsubst1 lgsubst2 lgsubst X K t Env lEnv1 lEnv2 lEnv, 
  lgamma_osubst_split (E++G) lE (dsubst'++dsubst) gsubst lgsubst1 lgsubst2 lgsubst Env lEnv1 lEnv2 lEnv->
  X `notin` fv_lenv lE `union` dom Env `union` dom lEnv  ->
  wf_lgamma_osubst (E++[(X, bind_kn K)]++G) lE (dsubst'++[(X,t)]++dsubst) gsubst lgsubst Env lEnv ->
  lgamma_osubst_split (E++[(X, bind_kn K)]++G) lE (dsubst'++[(X,t)]++dsubst) gsubst lgsubst1 lgsubst2 lgsubst Env lEnv1 lEnv2 lEnv.
Proof.
  intros E G lE dsubst dsubst' gsubst lgsubst1 lgsubst2 lgsubst X K t Env lEnv1 lEnv2 lEnv H1 H2 H3.
  remember (E++G) as GG.
  remember (dsubst'++dsubst) as dsubst0.
  generalize dependent E. generalize dependent G.
  generalize dependent dsubst'. generalize dependent dsubst.
  (lgamma_osubst_split_cases (induction H1) Case); intros; subst; auto.
  Case "lgamma_osubst_split_left".
    destruct H0 as [J1 [J2 J3]].
    apply lgamma_osubst_split_left with (lEnv1:=lEnv1) (lEnv3:=lEnv3) (lEnv1':=lEnv1'); auto.
      apply IHlgamma_osubst_split; auto.
        simpl_env in H2. auto.
        apply olgamma_stronger_tail in H6; auto.
        destruct H6 as [lEnv2' [lEnv1'' [Split [Typinge Hwfg]]]].
        assert (dom lEnv1' [=] dom lEnv1'') as DomEq.
          eapply typing_linctx_domeq with (E:=Env) (e:=e); eauto.
        assert (lEnv3 = lEnv2') as EQ.
          apply app_lengtheq_inv_head in Split; auto.
            apply domeq_lengtheq; eauto.
        subst. auto.

      simpl in H2. auto.

      split;auto. solve_uniq.

      apply typing_odsubst_weaken with (E:=E0++G); auto.
        apply lgamma_osubst_split__wf_lgamma_osubst in H1.
          apply wf_lgamma_osubst__wf_osubst in H1.
            destruct H1; auto.
        simpl_env in H2. simpl in H2. auto.

      apply wf_typ_weakening; auto.
        apply wf_lgamma_osubst__uniq in H6.
        decompose [and] H6; auto.
  Case "lgamma_osubst_split_right".
    destruct H0 as [J1 [J2 J3]].
    apply lgamma_osubst_split_right with (lEnv2:=lEnv2) (lEnv3:=lEnv3) (lEnv2':=lEnv2'); auto.
      apply IHlgamma_osubst_split; auto.
        simpl_env in H2. auto.
        apply olgamma_stronger_tail in H6; auto.
        destruct H6 as [lEnv3' [lEnv2'' [Split [Typinge Hwfg]]]].
        assert (dom lEnv2' [=] dom lEnv2'') as DomEq.
          eapply typing_linctx_domeq with (E:=Env) (e:=e); eauto.
        assert (lEnv3 = lEnv3') as EQ.
          apply app_lengtheq_inv_head in Split; auto.
            apply domeq_lengtheq; eauto.
        subst. auto.

      simpl in H2. auto.

      split;auto. solve_uniq.
    
      apply typing_odsubst_weaken with (E:=E0++G); auto.
        apply lgamma_osubst_split__wf_lgamma_osubst in H1.
          apply wf_lgamma_osubst__wf_osubst in H1.
            destruct H1; auto.
        simpl_env in H2. simpl in H2. auto.

      apply wf_typ_weakening; auto.
        apply wf_lgamma_osubst__uniq in H6.
        decompose [and] H6; auto.
Qed.

Lemma lgamma_osubst_split_nonlin_weakening_typ_tail : forall G lE dsubst gsubst lgsubst1 lgsubst2 lgsubst X K t Env lEnv1 lEnv2 lEnv, 
  lgamma_osubst_split (G) lE dsubst gsubst lgsubst1 lgsubst2 lgsubst Env lEnv1 lEnv2 lEnv ->
  X `notin` fv_lenv lE `union` dom Env `union` dom lEnv ->
  wf_lgamma_osubst ([(X, bind_kn K)]++G) lE ([(X,t)]++dsubst) gsubst lgsubst Env lEnv ->
  lgamma_osubst_split ([(X, bind_kn K)]++G) lE ([(X,t)]++dsubst) gsubst lgsubst1 lgsubst2 lgsubst Env lEnv1 lEnv2 lEnv.
Proof.
  intros G lE dsubst gsubst lgsubst1 lgsubst2 lgsubst X K t Env lEnv1 lEnv2 lEnv H1 H2 H3.
  rewrite_env (nil ++ [(X, bind_kn K)] ++ G).
  rewrite_env (nil ++ [(X,t)] ++ dsubst).
  apply lgamma_osubst_split_nonlin_weakening_typ; auto.
Qed.

Lemma lgamma_osubst_split_nonlin_weakening : forall E G lE dsubst gsubst gsubst' lgsubst1 lgsubst2 lgsubst x T e Env lEnv1 lEnv2 lEnv, 
  lgamma_osubst_split (E++G) lE dsubst (gsubst'++gsubst) lgsubst1 lgsubst2 lgsubst Env lEnv1 lEnv2 lEnv ->
  x `notin` dom lE `union` dom Env `union` dom lEnv ->
  wf_lgamma_osubst (E++[(x, bind_typ T)]++G) lE dsubst (gsubst'++[(x,e)]++gsubst) lgsubst Env lEnv ->
  lgamma_osubst_split (E++[(x, bind_typ T)]++G) lE dsubst (gsubst'++[(x,e)]++gsubst) lgsubst1 lgsubst2 lgsubst Env lEnv1 lEnv2 lEnv.
Proof.
  intros E G lE dsubst gsubst gsubst' lgsubst1 lgsubst2 lgsubst x T e Env lEnv1 lEnv2 lEnv H1 H2 H3.
  remember (E++G) as GG.
  remember (gsubst'++gsubst) as gsubst0.
  generalize dependent E. generalize dependent G.
  generalize dependent gsubst'. generalize dependent gsubst.
  (lgamma_osubst_split_cases (induction H1) Case); intros; subst; auto.
  Case "lgamma_osubst_split_left".
    destruct H0 as [J1 [J2 J3]].
    apply lgamma_osubst_split_left with (lEnv1:=lEnv1) (lEnv3:=lEnv3) (lEnv1':=lEnv1'); auto.
      apply IHlgamma_osubst_split; auto.
        simpl_env in H2. auto.
        apply olgamma_stronger_tail in H6; auto.
        destruct H6 as [lEnv2' [lEnv1'' [Split [Typinge Hwfg]]]].
        assert (dom lEnv1' [=] dom lEnv1'') as DomEq.
          eapply typing_linctx_domeq with (E:=Env) (e:=e0); eauto.
        assert (lEnv3 = lEnv2') as EQ.
          apply app_lengtheq_inv_head in Split; auto.
            apply domeq_lengtheq; eauto.
        subst. auto.

      split;auto. solve_uniq.
    
      apply wf_typ_weakening; auto.
        apply wf_lgamma_osubst__uniq in H6.
        decompose [and] H6; auto.
  Case "lgamma_osubst_split_right".
    destruct H0 as [J1 [J2 J3]].
    apply lgamma_osubst_split_right with (lEnv2:=lEnv2) (lEnv3:=lEnv3) (lEnv2':=lEnv2'); auto.
        simpl_env in H2. auto.
        apply olgamma_stronger_tail in H6; auto.
        destruct H6 as [lEnv3' [lEnv2'' [Split [Typinge Hwfg]]]].
        assert (dom lEnv2' [=] dom lEnv2'') as DomEq.
          eapply typing_linctx_domeq with (E:=Env) (e:=e0); eauto.
        assert (lEnv3 = lEnv3') as EQ.
          apply app_lengtheq_inv_head in Split; auto.
            apply domeq_lengtheq; eauto.
        subst. auto.

      solve_uniq.

      apply wf_typ_weakening; auto.
        apply wf_lgamma_osubst__uniq in H6.
        decompose [and] H6; auto.
Qed.

Lemma lgamma_osubst_split_nonlin_weakening_tail : forall G lE dsubst gsubst lgsubst1 lgsubst2 lgsubst x T e Env lEnv1 lEnv2 lEnv, 
  lgamma_osubst_split (G) lE dsubst (gsubst) lgsubst1 lgsubst2 lgsubst Env lEnv1 lEnv2 lEnv ->
  x `notin` dom lE `union` dom Env `union` dom lEnv ->
  wf_lgamma_osubst ([(x, bind_typ T)]++G) lE dsubst ([(x,e)]++gsubst) lgsubst Env lEnv ->
  lgamma_osubst_split ([(x, bind_typ T)]++G) lE dsubst ([(x,e)]++gsubst) lgsubst1 lgsubst2 lgsubst Env lEnv1 lEnv2 lEnv.
Proof.
  intros G lE dsubst gsubst lgsubst1 lgsubst2 lgsubst x T e Env lEnv1 lEnv2 lEnv H1 H2 H3.
  rewrite_env (nil ++ [(x, bind_typ T)] ++ G).
  rewrite_env (nil ++ [(x,e)] ++ gsubst).
  apply lgamma_osubst_split_nonlin_weakening; auto.
Qed.

Lemma swap_subst_ee_olgsubst_left: forall e' x E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst e t Env lEnv1 lEnv2 lEnv lEnv1',
  lgamma_osubst_split E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst Env lEnv1 lEnv2 lEnv ->
  typing Env lEnv1' e' t ->
  disjoint lE lEnv1' ->
  x `notin` dom lgsubst `union` dom Env `union` dom lEnv `union` dom lEnv1' ->
  subst_ee x e' (apply_gamma_subst lgsubst1 e) =
  apply_gamma_subst lgsubst1 (subst_ee x e' e).
Proof.
  intros e' x E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst e t Env lEnv1 lEnv2 lEnv lEnv1' Hsplit Hwft Disj xngsubst.
  generalize dependent e.
  generalize dependent e'.
  generalize dependent t.
  generalize dependent lEnv1'.
  induction Hsplit; intros lEnv1'0 Disj Fv t e' Hwft e0; simpl; auto.
    rewrite subst_ee_commute; auto.
      rewrite IHHsplit with (lEnv1':=lEnv1'0) (t:=t); auto.
        solve_uniq.

     apply notin_fv_ee_typing with (y:=x) in H2; auto.
     apply notin_fv_ee_typing with (y:=x) in Hwft; auto.

     apply notin_fv_ee_typing with (y:=x0) in H2; auto.
     assert (x0 `notin` dom lEnv1'0) as J.
       solve_uniq.
     apply notin_fv_ee_typing with (y:=x0) in Hwft; auto.

    rewrite IHHsplit with (lEnv1':=lEnv1'0) (t:=t); auto.
      solve_uniq.
Qed.

Lemma swap_subst_ee_olgsubst_right: forall e' x E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst e t Env lEnv1 lEnv2 lEnv lEnv2',
  lgamma_osubst_split E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst Env lEnv1 lEnv2 lEnv  ->
  typing Env lEnv2' e' t ->
  disjoint lE lEnv2' ->
  x `notin` dom lgsubst `union` dom Env `union` dom lEnv `union` dom lEnv2' ->
  subst_ee x e' (apply_gamma_subst lgsubst2 e) =
  apply_gamma_subst lgsubst2 (subst_ee x e' e).
Proof.
  intros e' x E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst e t Env lEnv1 lEnv2 lEnv lEnv2' Hsplit Hwft xngsubst.
  generalize dependent e.
  generalize dependent e'.
  generalize dependent t.
  generalize dependent lEnv2'.
  induction Hsplit; intros lEnv2'0 Disj t e' Hwft e0 Fv; simpl; auto.
    rewrite IHHsplit with (lEnv2':=lEnv2'0) (t:=t); auto.
      solve_uniq.

    rewrite subst_ee_commute; auto.
      rewrite IHHsplit with (lEnv2':=lEnv2'0) (t:=t); auto.
        solve_uniq.

     apply notin_fv_ee_typing with (y:=x) in H2; auto.
     apply notin_fv_ee_typing with (y:=x) in Hwft; auto.

     apply notin_fv_ee_typing with (y:=x0) in H2; auto.
     assert (x0 `notin` dom lEnv2'0) as J.
       solve_uniq.
     apply notin_fv_ee_typing with (y:=x0) in Hwft; auto.
Qed.

Lemma lgamma_subst_split_osubst : forall E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst e Env lEnv1 lEnv2 lEnv,
  lgamma_osubst_split E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst Env lEnv1 lEnv2 lEnv ->
  apply_gamma_subst lgsubst e = (apply_gamma_subst lgsubst1 (apply_gamma_subst lgsubst2 e)).
Proof.
  intros E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst e Env lEnv1 lEnv2 lEnv Hsplit.
  (lgamma_osubst_split_cases (induction Hsplit) Case); intros; simpl; auto.
  Case "lgamma_osubst_split_left".
    destruct H0 as [J1 [J2 J3]].
    assert (J:=Hsplit).
    apply lgamma_osubst_split__wf_lgamma_osubst in J.
    assert (x `notin` dom lgsE3) as K.
      apply wf_lgamma_osubst__nfv with (x:=x) in J; auto.
    erewrite <- swap_subst_ee_olgsubst_left with (e:=apply_gamma_subst lgsE2 e); eauto.
    rewrite <- IHHsplit; auto.
    erewrite <- swap_subst_ee_olgsubst with (e:=e); eauto.
  Case "lgamma_osubst_split_right".
    destruct H0 as [J1 [J2 J3]].
    assert (J:=Hsplit).
    apply lgamma_osubst_split__wf_lgamma_osubst in J.
    assert (x `notin` dom lgsE3) as K.
      apply wf_lgamma_osubst__nfv with (x:=x) in J; auto.
    erewrite <- swap_subst_ee_olgsubst with (e:=e); eauto.
    rewrite IHHsplit; auto.
    erewrite <- swap_subst_ee_olgsubst_right with (e:=e); eauto.
    erewrite <- swap_subst_ee_olgsubst_left with (e:=apply_gamma_subst lgsE2 e); eauto.
Qed.    

Lemma lgamma_subst_split_osubst' : forall E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst e Env lEnv1 lEnv2 lEnv,
  lgamma_osubst_split E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst Env lEnv1 lEnv2 lEnv ->
  apply_gamma_subst lgsubst e = (apply_gamma_subst lgsubst2 (apply_gamma_subst lgsubst1 e)).
Proof.
  intros E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst e Env lEnv1 lEnv2 lEnv Hsplit.
  (lgamma_osubst_split_cases (induction Hsplit) Case); intros; simpl; auto.
  Case "lgamma_osubst_split_left".
    destruct H0 as [J1 [J2 J3]].
    assert (J:=Hsplit).
    apply lgamma_osubst_split__wf_lgamma_osubst in J.
    assert (x `notin` dom lgsE3) as K.
      apply wf_lgamma_osubst__nfv with (x:=x) in J; auto.
    erewrite <- swap_subst_ee_olgsubst with (e:=e); eauto.
    rewrite IHHsplit; auto.
    erewrite swap_subst_ee_olgsubst_right with (e:=apply_gamma_subst lgsE1 e); eauto.
    erewrite swap_subst_ee_olgsubst_left; eauto.
  Case "lgamma_osubst_split_right".
    destruct H0 as [J1 [J2 J3]].
    assert (J:=Hsplit).
    apply lgamma_osubst_split__wf_lgamma_osubst in J.
    assert (x `notin` dom lgsE3) as K.
      apply wf_lgamma_osubst__nfv with (x:=x) in J; auto.
    erewrite <- swap_subst_ee_olgsubst with (e:=e); eauto.
    rewrite IHHsplit; auto.
    erewrite <- swap_subst_ee_olgsubst_right with (e:=apply_gamma_subst lgsE1 e); eauto.
Qed.    

Lemma wf_lgamma_osubst_shuffle : forall E lE dsubst gsubst lgsubst e Env lEnv,
  wf_lgamma_osubst E lE dsubst gsubst lgsubst Env lEnv ->
  apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)) =
  apply_gamma_subst lgsubst (apply_delta_subst dsubst (apply_gamma_subst gsubst e)).
Proof.
  intros E lE dsubst gsubst lgsubst e Env lEnv Hwflg.
  induction Hwflg; intros; simpl; auto.
  Case "wf_lgamma_osubst_sval".
    assert (J:=Hwflg).
    assert (x `notin` dom gsE `union` dom dsE) as K.
      apply wf_lgamma_osubst__nfv with (x:=x) in J; auto.
    apply wf_lgamma_osubst__wf_osubst in J.
    destruct J as [J1 J2].
    erewrite <- swap_subst_ee_ogsubst with (e:=e); eauto.
    erewrite <- swap_subst_ee_odsubst; eauto.
    erewrite <- swap_subst_ee_ogsubst; eauto.
    erewrite <- swap_subst_ee_odsubst; eauto.
    rewrite IHHwflg.
    erewrite swap_subst_ee_olgsubst; eauto.
      apply wf_lgamma_osubst__nfv with (x:=x) in Hwflg; auto.
  Case "wf_lgamma_osubst_slval".
    destruct H0 as [JJ1 JJ2].
    assert (J:=Hwflg).
    assert (x `notin` dom gsE `union` dom dsE) as K.
      apply wf_lgamma_osubst__nfv with (x:=x) in J; auto.
    apply wf_lgamma_osubst__wf_osubst in J.
    destruct J as [J1 J2].
    assert (x `notin` dom lgsE) as K'.
      apply wf_lgamma_osubst__nfv with (x:=x) in Hwflg; auto.
    erewrite <- swap_subst_ee_olgsubst with (e:=e); eauto.
    erewrite <- swap_subst_ee_ogsubst; eauto.
    erewrite <- swap_subst_ee_odsubst; eauto.
    erewrite <- swap_subst_ee_olgsubst; eauto.
    rewrite IHHwflg. auto.
  Case "wf_lgamma_osubst_skind".
    assert (J:=Hwflg).
    assert (X `notin` dom gsE `union` dom dsE) as K.
      apply wf_lgamma_osubst__nfv with (x:=X) in J; auto.
    apply wf_lgamma_osubst__wf_osubst in J.
    destruct J as [J1 J2].
    assert (X `notin` dom lgsE) as K'.
      apply wf_lgamma_osubst__nfv with (x:=X) in Hwflg; auto.
    erewrite <- swap_subst_te_odsubst; eauto.
    rewrite IHHwflg.
    erewrite swap_subst_te_olgsubst; eauto.
    erewrite swap_subst_te_odsubst; eauto.
Qed.

Lemma lgamma_osubst_split_shuffle1 : forall E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst e Env lEnv1 lEnv2 lEnv,
  lgamma_osubst_split E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst Env lEnv1 lEnv2 lEnv ->
  apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst1 e)) =
  apply_gamma_subst lgsubst1 (apply_delta_subst dsubst (apply_gamma_subst gsubst e)).
Proof.
  intros E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst e Env lEnv1 lEnv2 lEnv Hsplit.
  induction Hsplit; intros; simpl; auto.
  Case "lgamma_osubst_split_left".
    destruct H0 as [JJ1 [JJ2 JJ3]].
    assert (J:=Hsplit).
    apply lgamma_osubst_split__wf_lgamma_osubst in J.
    assert (JJ:=J).
    apply wf_lgamma_osubst__wf_osubst in JJ.
    destruct JJ as [J1 J2].
    assert (K:=J).
    apply wf_lgamma_osubst__nfv with (x:=x) in K; auto.
    erewrite <- swap_subst_ee_olgsubst_left with (e:=e); eauto.
    erewrite <- swap_subst_ee_ogsubst; eauto.
    erewrite <- swap_subst_ee_odsubst; eauto.
    rewrite IHHsplit.
    erewrite swap_subst_ee_odsubst; eauto.
    erewrite swap_subst_ee_olgsubst_left; eauto.
    erewrite swap_subst_ee_odsubst; eauto.
Qed.

Lemma lgamma_osubst_split_shuffle2 : forall E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst e Env lEnv1 lEnv2 lEnv,
  lgamma_osubst_split E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst Env lEnv1 lEnv2 lEnv ->
  apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst2 e)) =
  apply_gamma_subst lgsubst2 (apply_delta_subst dsubst (apply_gamma_subst gsubst e)).
Proof.
  intros E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst e Env lEnv1 lEnv2 lEnv Hsplit.
  induction Hsplit; intros; simpl; auto.
  Case "lgamma_osubst_split_right".
    destruct H0 as [JJ1 [JJ2 JJ3]].
    assert (J:=Hsplit).
    apply lgamma_osubst_split__wf_lgamma_osubst in J.
    assert (JJ:=J).
    apply wf_lgamma_osubst__wf_osubst in JJ.
    destruct JJ as [J1 J2].
    assert (K:=J).
    apply wf_lgamma_osubst__nfv with (x:=x) in K; auto.
    erewrite <- swap_subst_ee_olgsubst_right with (e:=e); eauto.
    erewrite <- swap_subst_ee_ogsubst; eauto.
    erewrite <- swap_subst_ee_odsubst; eauto.
    rewrite IHHsplit.
    erewrite swap_subst_ee_odsubst; eauto.
    erewrite swap_subst_ee_olgsubst_right; eauto.
    erewrite swap_subst_ee_odsubst; eauto.
Qed.

Lemma wf_lgamma_osubst_split : forall E lE dsubst gsubst lgsubst lE1 lE2 E' Env lEnv,
  wf_lgamma_osubst E lE dsubst gsubst lgsubst Env lEnv ->
  lenv_split (E'++E) lE1 lE2 lE ->
  exists lgsubst1, exists lgsubst2, exists lEnv1, exists lEnv2,
    lgamma_osubst_split E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst Env lEnv1 lEnv2 lEnv /\
    wf_lgamma_osubst E lE1 dsubst gsubst lgsubst1 Env lEnv1 /\
    wf_lgamma_osubst E lE2 dsubst gsubst lgsubst2 Env lEnv2.
Proof. 
  intros E lE dsubst gsubst lgsubst lE1 lE2 E' Env lEnv Hwflg Hsplit.
  generalize dependent lE1. generalize dependent lE2. generalize dependent E'.
  (wf_lgamma_osubst_cases (induction Hwflg) Case); intros.
  Case "wf_lgamma_osubst_empty".
    exists gamma_nil. exists gamma_nil. exists nil. exists nil.
    inversion Hsplit; subst.
    repeat (split; auto).
  Case "wf_lgamma_osubst_sval".
    assert (J:=Hsplit).
    rewrite_env ((E'++[(x, bind_typ T)])++E) in Hsplit.
    apply IHHwflg in Hsplit. clear IHHwflg.
    destruct Hsplit as [lgsubst1 [lgsubst2 [lEnv1 [lEnv2 [J1 [J2 J3]]]]]].
    exists lgsubst1. exists lgsubst2. exists lEnv1. exists lEnv2.
    split.
      apply lgamma_osubst_split_nonlin_weakening_tail; auto.
    split.
      apply wf_lgamma_osubst_sval; auto.
        apply dom_lenv_split in J.
        apply lgamma_osubst_split__lenv_split in J1.
        apply dom_lenv_split in J1.
        rewrite J1 in H. rewrite J in H; auto.  
      apply wf_lgamma_osubst_sval; auto.
        apply dom_lenv_split in J.
        apply lgamma_osubst_split__lenv_split in J1.
        apply dom_lenv_split in J1.
        rewrite J1 in H. rewrite J in H; auto.  
  Case "wf_lgamma_osubst_slval".
    destruct H0 as [JJ1 JJ2].
    inversion Hsplit; subst.
    SCase "lenv_split_left".
      assert (J:=H6).
      apply IHHwflg in H6. clear IHHwflg.
      destruct H6 as [lgsubst1 [lgsubst2 [lEnv1' [lEnv2' [J1 [J2 J3]]]]]].
      assert (EQ:=J). apply dom_lenv_split in EQ.
      assert (EQ':=J1).
      apply lgamma_osubst_split__lenv_split in EQ'.
      apply dom_lenv_split in EQ'.
      exists ([(x,e)]++lgsubst1). exists lgsubst2. exists (lEnv2++lEnv1'). exists lEnv2'.
      split.
        apply lgamma_osubst_split_left with (lEnv1:=lEnv1') (lEnv1':=lEnv2) (lEnv3:=lEnv1); auto.
            rewrite EQ in H. rewrite EQ.
            rewrite EQ' in H. rewrite EQ'. auto.

            split; auto. split; auto.
            apply disjoint_sub with (D1:=lEnv1); auto.
              apply disjoint_sym_1.
              apply uniq_from_wf_lenv in H1. solve_uniq.

              rewrite EQ'. fsetdec.

            apply wf_lenv_merge; auto.
              apply wf_lgamma_osubst__wf_lenv in J2.
              decompose [and] J2; auto.

              apply disjoint_sym_1.
              apply disjoint_sub with (D1:=lEnv1); auto.
                apply disjoint_sym_1.
                apply uniq_from_wf_lenv in H1. solve_uniq.

                rewrite EQ'. fsetdec.
      split; auto.
        apply wf_lgamma_osubst_slval with (lEnv1:=lEnv1') (lEnv2:=lEnv2); auto.
            rewrite EQ in H.
            rewrite EQ' in H. auto.

            split; auto.
            apply disjoint_sub with (D1:=lE); auto.
              rewrite EQ. fsetdec.

            apply wf_lenv_merge; auto.
              apply wf_lgamma_osubst__wf_lenv in J2.
              decompose [and] J2; auto.

              apply disjoint_sym_1.
              apply disjoint_sub with (D1:=lEnv1); auto.
                apply disjoint_sym_1.
                apply uniq_from_wf_lenv in H1. solve_uniq.

                rewrite EQ'. fsetdec.
    SCase "lenv_split_right".
      assert (J:=H6).
      apply IHHwflg in H6. clear IHHwflg.
      destruct H6 as [lgsubst1 [lgsubst2 [lEnv1' [lEnv2' [J1 [J2 J3]]]]]].
      assert (EQ:=J). apply dom_lenv_split in EQ.
      assert (EQ':=J1).
      apply lgamma_osubst_split__lenv_split in EQ'.
      apply dom_lenv_split in EQ'.
      exists lgsubst1. exists ([(x,e)]++lgsubst2). exists (lEnv1'). exists (lEnv2++lEnv2').
      split.
        apply lgamma_osubst_split_right with (lEnv2:=lEnv2') (lEnv2':=lEnv2) (lEnv3:=lEnv1); auto.
            rewrite EQ in H. rewrite EQ.
            rewrite EQ' in H. rewrite EQ'. auto.

            split; auto. split; auto.
            apply disjoint_sub with (D1:=lEnv1); auto.
              apply uniq_from_wf_lenv in H1. solve_uniq.

              rewrite EQ'. fsetdec.

            apply wf_lenv_merge; auto.
              apply wf_lgamma_osubst__wf_lenv in J3.
              decompose [and] J3; auto.

              apply disjoint_sym_1.
              apply disjoint_sub with (D1:=lEnv1); auto.
                apply disjoint_sym_1.
                apply uniq_from_wf_lenv in H1. solve_uniq.

                rewrite EQ'. fsetdec.
      split; auto.
        apply wf_lgamma_osubst_slval with (lEnv1:=lEnv2') (lEnv2:=lEnv2); auto.
            rewrite EQ in H.
            rewrite EQ' in H. auto.

            split; auto.
            apply disjoint_sub with (D1:=lE); auto.
              rewrite EQ. fsetdec.

            apply wf_lenv_merge; auto.
              apply wf_lgamma_osubst__wf_lenv in J3.
              decompose [and] J3; auto.

              apply disjoint_sym_1.
              apply disjoint_sub with (D1:=lEnv1); auto.
                apply disjoint_sym_1.
                apply uniq_from_wf_lenv in H1. solve_uniq.

                rewrite EQ'. fsetdec.
  Case "wf_lgamma_osubst_skind".
    assert (J:=Hsplit).
    assert (K:=Hwflg).
    apply wf_lgamma_osubst__nfv with (x:=X) in K; auto. 
    rewrite_env ((E'++[(X, bind_kn k)])++E) in Hsplit.
    apply IHHwflg in Hsplit. clear IHHwflg.
    destruct Hsplit as [lgsubst1 [lgsubst2 [lEnv1' [lEnv2' [J1 [J2 J3]]]]]].
    assert (EQ:=J). apply dom_lenv_split in EQ.
    assert (EQ':=J1).
    apply lgamma_osubst_split__lenv_split in EQ'.
    apply dom_lenv_split in EQ'.
    exists lgsubst1. exists lgsubst2. exists lEnv1'.  exists lEnv2'.
    split.
      apply lgamma_osubst_split_nonlin_weakening_typ_tail; auto.
    split.
      apply wf_lgamma_osubst_skind; auto.
        rewrite EQ in H.
        rewrite EQ' in H. auto.
      apply wf_lgamma_osubst_skind; auto.
        rewrite EQ in H.
        rewrite EQ' in H. auto.
Qed.

(* ********************)
(*** closed after subst *)

Lemma wft_osubst_closed : forall E E' t K dsubst Env,
  wf_delta_osubst E dsubst Env->
  wf_typ (E'++E) t K ->
  wf_env (E'++E) ->
  wf_env (apply_delta_subst_env dsubst E' ++ Env) ->
  wf_typ (apply_delta_subst_env dsubst E' ++ Env) (apply_delta_subst_typ dsubst t) K.
Proof.
  intros E E' t K dsubst Env Hwfd Hwft Hwfe Hwfe'.
  remember (E'++E) as EE.
  generalize dependent E'.
  generalize dependent E.
  generalize dependent dsubst.
  (wf_typ_cases (induction Hwft) Case); intros; subst; simpl; eauto.
  Case "wf_typ_var".
     analyze_binds H0.
       assert (X `notin` dom E0).
         eauto using fresh_app_r.

       assert (apply_delta_subst_env dsubst E' ++ Env = apply_delta_subst_env dsubst (E' ++ Env)) as EQ.
         assert (J:=Hwfd). apply disjoint_delta_osubst in J. decompose [and] J. clear J.
         assert (J:=Hwfd). apply wf_delta_osubst__uniq in J. decompose [and] J. clear J.
         rewrite apply_delta_subst_env_cons. 
         rewrite <- apply_delta_subst_env_id with (E:=Env) (dsubst:=dsubst); auto. 

       apply wf_delta_osubst__nfv with (dsubst:=dsubst) (X:=X) in Hwfd; auto.
       rewrite apply_delta_subst_typ_nfv; auto.
       apply wf_typ_var; auto.          
         rewrite EQ.
         apply delta_subst_binds_kind with (dsubst:=dsubst); auto.

       assert (uniq dsubst).
         apply wf_delta_osubst__uniq in Hwfd. decompose [and] Hwfd. auto.
       apply bindosdE__bindsT with (X:=X)(K:=K) in Hwfd; auto.
       destruct Hwfd as [T [J1 [J2 J3]]].
       assert (apply_delta_subst_typ dsubst (typ_fvar X) = T).
         apply delta_osubst_var with (T:=T); auto.
       rewrite H1.
       apply wf_typ_weaken_head with (F:=apply_delta_subst_env dsubst E') in J2; simpl_env in *; auto.
  Case "wf_typ_arrow".
     rewrite commut_delta_subst_arrow.
     eapply wf_typ_arrow; eauto.
  Case "wf_typ_all".
     rewrite commut_delta_subst_all.
     apply wf_typ_all with (L:=L `union` dom dsubst  `union` dom (E'++E0) `union` dom (apply_delta_subst_env dsubst E') `union` dom Env).
       intros.
       assert (X `notin` L). auto.
       apply H0 with (dsubst:=dsubst) (E'0:=[(X,bind_kn K1)]++E') (E:=E0) in H2; simpl; simpl_env; eauto.
         rewrite commut_delta_osubst_open_tt with (dE:=E0) (Env:=Env) in H2; auto.
         simpl in H2. simpl_env in *.
         rewrite apply_delta_subst_typ_nfv in H2; auto.
  Case "wf_typ_with".
     rewrite commut_delta_subst_with.
     eapply wf_typ_with; eauto.
Qed.

Lemma wfle_osubst_closed : forall E E' lE dsubst Env,
  wf_delta_osubst E dsubst Env ->
  wf_lenv (E'++E) lE ->
  disjoint lE Env ->
  wf_env (apply_delta_subst_env dsubst E' ++ Env) ->
  wf_lenv (apply_delta_subst_env dsubst E' ++ Env) (apply_delta_subst_lenv dsubst lE).
Proof.
  intros E E' lE dsubst Env Hwfd Hwfle Disj Hwfe.  
  remember (E'++E) as EE.
  generalize dependent E'.
  generalize dependent E.
  generalize dependent dsubst.
  (wf_lenv_cases (induction Hwfle) Case); 
    intros; subst; simpl; simpl_env; eauto.
  Case "wf_lenv_typ".
    apply wf_lenv_typ; auto.
      apply IHHwfle with (E:=E0); auto.
        solve_uniq.
      rewrite dom_app. rewrite <- apply_delta_subst_env_dom; auto.
        solve_uniq.
      rewrite <- apply_delta_subst_lenv_dom; auto.
      eapply wft_osubst_closed; eauto.
Qed.

Lemma lenv_split_osubst_closed : forall E E' lE1 lE1' lE2 lE2' lE lE' dsubst Env  lEnv1 lEnv2 lEnv,
  wf_delta_osubst E dsubst Env ->
  lenv_split (E'++E) (lE1'++lE1) (lE2'++lE2) (lE'++lE) ->
  dom lE1 `union` dom lE2 [=] dom lE ->
  disjoint (lE'++lE) Env /\ disjoint (lE'++lE) lEnv /\ disjoint E' lEnv ->
  lenv_split Env lEnv1 lEnv2 lEnv ->
  wf_env (apply_delta_subst_env dsubst E' ++ Env) ->
  lenv_split (apply_delta_subst_env dsubst E' ++ Env) 
                       (apply_delta_subst_lenv dsubst lE1' ++ lEnv1) 
                       (apply_delta_subst_lenv dsubst lE2' ++ lEnv2) 
                       (apply_delta_subst_lenv dsubst lE' ++ lEnv).
Proof.
  intros E E' lE1 lE1' lE2 lE2' lE lE' dsubst Env lEnv1 lEnv2 lEnv Hwfd Hsplit Dom Disj Split Hwfe.  
  destruct Disj as [Disj1 [Disj2 Disj3]].
  remember (E'++E) as EE.
  remember (lE1'++lE1) as lEE1.
  remember (lE2'++lE2) as lEE2.
  remember (lE'++lE) as lEE.
  generalize dependent E'.
  generalize dependent E.
  generalize dependent lE1'.
  generalize dependent lE1.
  generalize dependent lE2'.
  generalize dependent lE2.
  generalize dependent lE'.
  generalize dependent lE.
  generalize dependent lEnv.
  generalize dependent lEnv1.
  generalize dependent lEnv2.
  generalize dependent dsubst.
  (lenv_split_cases (induction Hsplit) Case); 
    intros; subst; simpl; simpl_env; auto.
  Case "lenv_split_empty".
    symmetry in HeqlEE. apply app_eq_nil in HeqlEE. destruct HeqlEE; subst.
    symmetry in HeqlEE1. apply app_eq_nil in HeqlEE1. destruct HeqlEE1; subst.
    symmetry in HeqlEE2. apply app_eq_nil in HeqlEE2. destruct HeqlEE2; subst.
    simpl. 
    apply lenv_split_weakening_tail; auto.
      assert (J:=@apply_delta_subst_env_dom dsubst E').
      solve_uniq.      
  Case "lenv_split_left".
    apply one_eq_app in HeqlEE.
    destruct HeqlEE as [[lEE'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst; simpl; simpl_env.
    SCase "1".
      apply one_eq_app in HeqlEE1.
      destruct HeqlEE1 as [[lEE1'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst; simpl; simpl_env.
      SSCase "11".
        apply lenv_split_left; auto.
          apply IHHsplit with (E:=E0)(lE0:=lE)(lE3:=lE2)(lE2:=lE1); auto.
             solve_uniq.
             solve_uniq.

          rewrite dom_app. rewrite <- apply_delta_subst_env_dom; auto.
          assert (x `notin` dom Env) as xnotin.
            solve_uniq.
          auto.

          rewrite dom_app. rewrite <- apply_delta_subst_lenv_dom; auto.
          assert (x `notin` dom lEnv) as xnotin.
            solve_uniq.
          auto.

          eapply wft_osubst_closed; eauto.
            apply wf_lenv_split in Hsplit.
              apply wf_env_from_wf_lenv in Hsplit; auto.
      SSCase "12".
        rewrite dom_app in H0. rewrite <- Dom in H0. simpl in H0.
       destruct_notin. contradict NotInTac; auto.    
    SCase "2".
      apply one_eq_app in HeqlEE1.
      destruct HeqlEE1 as [[lEE1'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst; simpl; simpl_env.
      SSCase "21".
        assert (J:=Hsplit).
        apply dom_lenv_split in J.
        simpl in Dom. rewrite J in Dom.
        assert (x `in` dom lE1 `union` dom lE2) as J1.
          clear J H IHHsplit Hsplit H0 Disj1 Disj2 Disj3.
          rewrite Dom. clear Dom. auto.
        assert (x `notin` dom lE1 `union` dom lE2) as J2.
          clear J1 H IHHsplit Hsplit Disj1 Disj2 Disj3 Dom.
          rewrite J in H0. clear J. auto.
        contradict J1; auto.
      SSCase "22".
        assert (J:=Hsplit).
        apply dom_lenv_split in J.
        simpl in Dom. rewrite J in Dom.
        assert (lE2'=nil) as EQ.
          assert (x `notin` dom lE2') as J1.
            rewrite J in H0. 
            clear J H IHHsplit Hsplit Disj1 Disj2 Disj3 Dom.
            simpl_env in H0. auto.
          assert (disjoint lE2' D1) as J2.
            apply disjoint_lenv_split' in Hsplit.
            clear J H IHHsplit H0 Disj1 Disj2 Disj3 Dom.
            solve_uniq.
          assert (disjoint lE2' lE2) as J3.
            apply wf_lenv_split_right in Hsplit.
            apply uniq_from_wf_lenv in Hsplit.
            solve_uniq.
          clear J H IHHsplit Hsplit H0 Disj1 Disj2 Disj3.
          destruct lE2'; auto.
            destruct p.
            destruct (a==x); subst.
              simpl_env in J1. destruct_notin. contradict J1; auto.

              assert (a `in` union (add x (dom D1)) (dom lE2)) as ainsomething.
                simpl. rewrite Dom. simpl_env. auto.
              assert (a `in` {{x}} \/ a `in` dom D1 \/ a `in` dom lE2) as J.
                clear n J1 J2 J3 Dom. fsetdec.
              clear ainsomething.
              destruct J as [J | [J | J]].
                contradict J; auto.

                assert (a `in` dom ((a,l)::lE2')) as JJ.
                  simpl. auto.
                clear J1 J3 n.
                contradict J; try solve [solve_uniq].

                assert (a `in` dom ((a,l)::lE2')) as JJ.
                  simpl. auto.
                clear J1 J2 n.
                contradict J; try solve [solve_uniq].
        subst. simpl.
        apply lenv_split_weakening_tail; auto.
          assert (JJ:=@apply_delta_subst_env_dom dsubst E').
          clear Disj1 Disj2 H Dom J. solve_uniq.      
  Case "lenv_split_right".
    apply one_eq_app in HeqlEE.
    destruct HeqlEE as [[lEE'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst; simpl; simpl_env.
    SCase "1".
      apply one_eq_app in HeqlEE2.
      destruct HeqlEE2 as [[lEE2'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst; simpl; simpl_env.
      SSCase "11".
        apply lenv_split_right; auto.
          apply IHHsplit with (E:=E0)(lE0:=lE)(lE3:=lE2)(lE2:=lE1); auto.
             solve_uniq.
             solve_uniq.

          rewrite dom_app. rewrite <- apply_delta_subst_env_dom; auto.
          assert (x `notin` dom Env) as xnotin.
            solve_uniq.
          auto.

          rewrite dom_app. rewrite <- apply_delta_subst_lenv_dom; auto.
          assert (x `notin` dom lEnv) as xnotin.
            solve_uniq.
          auto.

          eapply wft_osubst_closed; eauto.
            apply wf_lenv_split in Hsplit.
              apply wf_env_from_wf_lenv in Hsplit; auto.
      SSCase "12".
        rewrite dom_app in H0. rewrite <- Dom in H0. simpl in H0.
       destruct_notin. contradict NotInTac0; auto.    
    SCase "2".
      apply one_eq_app in HeqlEE2.
      destruct HeqlEE2 as [[lEE2'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst; simpl; simpl_env.
      SSCase "21".
        assert (J:=Hsplit).
        apply dom_lenv_split in J.
        simpl in Dom. rewrite J in Dom.
        assert (x `in` dom lE1 `union` dom lE2) as J1.
          clear J H IHHsplit Hsplit H0 Disj1 Disj2 Disj3.
          rewrite Dom. clear Dom. auto.
        assert (x `notin` dom lE1 `union` dom lE2) as J2.
          clear J1 H IHHsplit Hsplit Disj1 Disj2 Disj3 Dom.
          rewrite J in H0. clear J. auto.
        contradict J1; auto.
      SSCase "22".
        assert (J:=Hsplit).
        apply dom_lenv_split in J.
        simpl in Dom. rewrite J in Dom.
        assert (lE1'=nil) as EQ.
          assert (x `notin` dom lE1') as J1.
            rewrite J in H0. 
            clear J H IHHsplit Hsplit Disj1 Disj2 Disj3 Dom.
            simpl_env in H0. auto.
          assert (disjoint lE1' D2) as J2.
            apply disjoint_lenv_split' in Hsplit.
            clear J H IHHsplit H0 Disj1 Disj2 Disj3 Dom.
            solve_uniq.
          assert (disjoint lE1' lE1) as J3.
            apply wf_lenv_split_left in Hsplit.
            apply uniq_from_wf_lenv in Hsplit.
            solve_uniq.
          clear J H IHHsplit Hsplit H0 Disj1 Disj2 Disj3.
          destruct lE1'; auto.
            destruct p.
            destruct (a==x); subst.
              simpl_env in J1. destruct_notin. contradict J1; auto.

              assert (a `in` union  (dom lE1) (add x (dom D2))) as ainsomething.
                simpl. rewrite Dom. simpl_env. auto.
              assert (a `in` {{x}} \/ a `in` dom D2 \/ a `in` dom lE1) as J.
                clear n J1 J2 J3 Dom. fsetdec.
              clear ainsomething.
              destruct J as [J | [J | J]].
                contradict J; auto.

                assert (a `in` dom ((a,l)::lE1')) as JJ.
                  simpl. auto.
                clear J1 J3 n.
                contradict J; try solve [solve_uniq].

                assert (a `in` dom ((a,l)::lE1')) as JJ.
                  simpl. auto.
                clear J1 J2 n.
                contradict J; try solve [solve_uniq].
        subst. simpl.
        apply lenv_split_weakening_tail; auto.
          assert (JJ:=@apply_delta_subst_env_dom dsubst E').
          clear Disj1 Disj2 H Dom J. solve_uniq.      
Qed.

Lemma typing_osubst_closed : forall E E' D D' e t dsubst gsubst lgsubst Env lEnv,
  wf_lgamma_osubst E D dsubst gsubst lgsubst Env lEnv ->
  typing (E'++E) (D'++D) e t ->
  disjoint D' Env -> 
  disjoint D' lEnv -> 
  wf_lenv (apply_delta_subst_env dsubst E' ++ Env) (apply_delta_subst_lenv dsubst D' ++ lEnv) ->
  wf_lenv (apply_delta_subst_env dsubst E' ++ Env) lEnv ->
  typing (apply_delta_subst_env dsubst E' ++ Env) (apply_delta_subst_lenv dsubst D' ++ lEnv) 
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e))) 
         (apply_delta_subst_typ dsubst t).
Proof.
  intros E E' D D' e t dsubst gsubst lgsubst Env lEnv Hwfg Htyp Disj1 Disj2 Wfe1 Wfe2.
  assert (wf_env (E'++E)) as Wfe. auto.
  remember (E'++E) as EE.
  remember (D'++D) as DD.
  generalize dependent E.
  generalize dependent E'.
  generalize dependent D.
  generalize dependent D'.
  generalize dependent dsubst.
  generalize dependent gsubst.
  generalize dependent lgsubst.
  generalize dependent Env.
  generalize dependent lEnv.
  (typing_cases (induction Htyp) Case); intros; subst; simpl; simpl_commut_subst; auto.
  Case "typing_var".
     apply app_nil_inv in HeqDD.
     destruct HeqDD; subst.
     assert (dom lEnv [=] {}) as lEnvNil.
       apply wf_lgamma_osubst_empty_linctx in Hwfg; auto.
     apply empty_dom__empty_ctx in lEnvNil. subst. simpl.
     analyze_binds H0.
       assert (x `notin` dom E0) as J.
         eauto using fresh_app_r.
       apply delta_subst_binds_typ with (dsubst:=dsubst) in BindsTac.
       apply wf_lgamma_osubst__nfv with (E:=E0) (dsubst:=dsubst) (gsubst:=gsubst) (x:=x) in Hwfg; auto.
       decompose [and] Hwfg. clear Hwfg.       
       rewrite apply_gamma_subst_nfv; auto.
       rewrite apply_gamma_subst_nfv; auto.
       rewrite apply_delta_subst_nfv; auto.

       assert (uniq gsubst).
         apply wf_lgamma_osubst__uniq in Hwfg. decompose [and] Hwfg; auto.
       apply bindosgE__bindsE with (x:=x) (t:=T) in Hwfg; auto.
       destruct Hwfg as [J [e [J1 [J2 [J3 [J4 J5]]]]]]. 
       rewrite apply_gamma_subst_nfv; auto.
       assert (apply_gamma_subst gsubst (exp_fvar x) = e) as EQ.
         apply gamma_osubst_var; auto.  
       rewrite EQ.
       rewrite delta_osubst_closed_exp; auto.
       apply typing_weakening with (F:=apply_delta_subst_env dsubst E') (E:=Env) (G:=@nil (atom*binding)) in J2; simpl_env in *; auto.
  Case "typing_lvar".
     rewrite_env ([(x, lbind_typ T)] ++ nil) in HeqDD.
     apply one_eq_app in HeqDD.
     destruct HeqDD as [[D'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
       SCase "x in D', D=nil".
       apply app_nil_inv in EQ2.
       destruct EQ2; subst.
       assert (dom lEnv [=] {}) as lEnvNil.
         apply wf_lgamma_osubst_empty_linctx in Hwfg; auto.
       apply empty_dom__empty_ctx in lEnvNil. subst. simpl.
       assert (x `notin` dom lempty) as J. auto.
       assert (x `notin` dom (E'++E0)) as J'.
         inversion H; auto.
       apply wf_lgamma_osubst__nfv with (E:=E0) (dsubst:=dsubst) (gsubst:=gsubst) (x:=x) in Hwfg; auto.
       decompose [and] Hwfg. clear Hwfg.
       rewrite apply_gamma_subst_nfv; auto.
       rewrite apply_gamma_subst_nfv; auto.
       rewrite apply_delta_subst_nfv; auto.
       apply typing_lvar; auto.

       SCase "x in D, D'=nil".
       assert (uniq lgsubst).
         apply wf_lgamma_osubst__uniq in Hwfg. decompose [and] Hwfg; auto.
       assert (binds x (lbind_typ T) ((x, lbind_typ T) :: lempty)) as K.
         simpl_env. apply binds_one_3; auto.
       apply lbindosgE__bindslE with (x:=x) (t:=T) in Hwfg; auto.
       destruct Hwfg as [J [e [J1 [J2 [J3 [J4 J5]]]]]].
       assert (apply_gamma_subst lgsubst (exp_fvar x) = e) as EQ.
         apply gamma_osubst_var; auto.  
       rewrite EQ.
       rewrite gamma_osubst_closed_exp; auto.
       rewrite delta_osubst_closed_exp; auto.
       apply typing_weakening with (F:=apply_delta_subst_env dsubst E') (E:=Env) (G:=@nil (atom*binding)) in J2; simpl_env in *; auto.
  Case "typing_abs".
     assert (wf_typ (apply_delta_subst_env dsubst E' ++ Env) (apply_delta_subst_typ dsubst T1) kn_nonlin) as Wft.
       apply wft_osubst_closed with (E:=E0) ; auto.
         apply wf_lgamma_osubst__wf_osubst in Hwfg.
         destruct Hwfg; auto. 
     assert (wf_gamma_osubst E0 dsubst gsubst Env) as Wfg.
       apply wf_lgamma_osubst__wf_osubst in Hwfg.
       decompose [and] Hwfg; auto.
     assert (wf_delta_osubst E0 dsubst Env) as Wfd.
       apply wf_lgamma_osubst__wf_osubst in Hwfg.
       decompose [and] Hwfg; auto.
     apply typing_abs with (L:=L `union` dom gsubst `union` dom lgsubst  
                                 `union` dom dsubst `union` dom (apply_delta_subst_env dsubst E')
                                 `union` dom (apply_delta_subst_lenv dsubst D') `union` dom (E'++E0)
                                  `union` dom Env `union` dom lEnv); auto.
       intros.
       assert (x `notin` L) as FrxL. auto.
       apply H1 with (E:=E0) (gsubst:=gsubst) (dsubst:=dsubst) (E'0:=[(x, bind_typ T1)]++E') (D'0:=D') (D:=D0) (lgsubst:=lgsubst) (Env:=Env) (lEnv:=lEnv)in FrxL; clear H1;auto.
         rewrite commut_lgamma_osubst_open_ee with (E:=E0) (dsubst:=dsubst) (D:=D0) (gsubst:=gsubst) (Env:=Env) (lEnv:=lEnv) in FrxL; auto.
         rewrite commut_gamma_osubst_open_ee with (E:=E0) (dsubst:=dsubst) (D:=D0) (lgsubst:=lgsubst) (Env:=Env) (lEnv:=lEnv) in FrxL; auto.
         rewrite commut_delta_osubst_open_ee with (dE:=E0) (Env:=Env) in FrxL; auto.
         simpl in FrxL. simpl_env in *.
         rewrite apply_gamma_subst_nfv in FrxL; auto.
         rewrite apply_gamma_subst_nfv in FrxL; auto.
         rewrite apply_delta_subst_nfv in FrxL; auto.

         rewrite_env (nil++[(x, bind_typ (apply_delta_subst_typ dsubst T1))]++apply_delta_subst_env dsubst E' ++ Env).
         apply wf_lenv_weakening; auto.
           simpl_env. apply wf_env_typ; auto.

         rewrite_env (nil++[(x, bind_typ (apply_delta_subst_typ dsubst T1))]++apply_delta_subst_env dsubst E' ++ Env).
         apply wf_lenv_weakening; auto.
           simpl_env. apply wf_env_typ; auto.

       intros J.
       apply H2 in J.
       apply sym_eq in J.
       apply app_nil_inv in J.
       destruct J; subst.
       assert (dom lEnv [=] {}) as lEnvNil.
         apply wf_lgamma_osubst_empty_linctx in Hwfg; auto.
       apply empty_dom__empty_ctx in lEnvNil. subst. simpl. auto.
  Case "typing_labs".
     assert (wf_typ (apply_delta_subst_env dsubst E' ++ Env) (apply_delta_subst_typ dsubst T1) kn_lin) as Wft.
       apply wft_osubst_closed with (E:=E0) ; auto.
         apply wf_lgamma_osubst__wf_osubst in Hwfg.
         destruct Hwfg; auto. 
     assert (wf_gamma_osubst E0 dsubst gsubst Env) as Wfg.
       apply wf_lgamma_osubst__wf_osubst in Hwfg.
       decompose [and] Hwfg; auto.
     assert (wf_delta_osubst E0 dsubst Env) as Wfd.
       apply wf_lgamma_osubst__wf_osubst in Hwfg.
       decompose [and] Hwfg; auto.
     apply typing_labs with (L:=L `union` dom gsubst `union` dom lgsubst  
                                 `union` dom dsubst `union` dom (apply_delta_subst_env dsubst E')
                                 `union` dom (apply_delta_subst_lenv dsubst D') `union` dom (E'++E0)
                                  `union` dom Env `union` dom lEnv); auto.
       intros.
       assert (x `notin` L) as FrxL. auto.
       apply H1 with (E:=E0) (gsubst:=gsubst) (dsubst:=dsubst) (E'0:=E') (D'0:=[(x, lbind_typ T1)]++D') (D:=D0) (lgsubst:=lgsubst)(Env:=Env) (lEnv:=lEnv) in FrxL; clear H1;auto.
         rewrite commut_lgamma_osubst_open_ee with (E:=E0) (dsubst:=dsubst) (D:=D0) (gsubst:=gsubst) (Env:=Env) (lEnv:=lEnv) in FrxL; auto.
         rewrite commut_gamma_osubst_open_ee with (E:=E0) (dsubst:=dsubst) (D:=D0) (lgsubst:=lgsubst) (Env:=Env) (lEnv:=lEnv) in FrxL; auto.
         rewrite commut_delta_osubst_open_ee with (dE:=E0) (Env:=Env) in FrxL; auto.
         simpl in FrxL. simpl_env in *.
         rewrite apply_gamma_subst_nfv in FrxL; auto.
         rewrite apply_gamma_subst_nfv in FrxL; auto.
         rewrite apply_delta_subst_nfv in FrxL; auto.

         rewrite_env (nil++[(x, lbind_typ (apply_delta_subst_typ dsubst T1))]++apply_delta_subst_lenv dsubst D' ++ lEnv).
         apply wf_lenv_lin_weakening; auto.

       intros J.
       apply H2 in J.
       apply sym_eq in J.
       apply app_nil_inv in J.
       destruct J; subst.
       assert (dom lEnv [=] {}) as lEnvNil.
         apply wf_lgamma_osubst_empty_linctx in Hwfg; auto.
       apply empty_dom__empty_ctx in lEnvNil. subst. simpl. auto.
  Case "typing_app".
     assert (HH:=H).
     apply lenv_split_cases_app in H.
     destruct H as [D1L [D1R [D2L [D2R [Hsplit' [Hsplit [J1 J2]]]]]]]; subst.
     assert (J:=Hwfg).
     apply wf_lgamma_osubst_split with (lE1:=D1R) (lE2:=D2R) (E':=E') in Hwfg; auto.
     destruct Hwfg as [lgsubst1 [lgsubst2 [lEnv1 [lEnv2 [Hgsplit [Hwflg1 Hwflg2]]]]]].
     assert (wf_lenv (E'++E0) D1L) as Wfe1'.
       apply wf_lenv_split_left in Hsplit'; auto.
     assert (wf_lenv (E'++E0) D2L) as Wfe2'.
       apply wf_lenv_split_right in Hsplit'; auto.
     assert (exp_app
              (apply_delta_subst dsubst
                (apply_gamma_subst gsubst
                  (apply_gamma_subst lgsubst e1)))
              (apply_delta_subst dsubst
                (apply_gamma_subst gsubst
                  (apply_gamma_subst lgsubst e2)))
              =
             exp_app 
              (apply_delta_subst dsubst
                (apply_gamma_subst gsubst
                  (apply_gamma_subst lgsubst1 e1)))
              (apply_delta_subst dsubst
                (apply_gamma_subst gsubst
                  (apply_gamma_subst lgsubst2 e2)))
            ) as EQ.
       rewrite lgamma_subst_split_osubst with (lgsubst1:=lgsubst1) (lgsubst2:=lgsubst2) (E:=E0) (lE:=D) (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst) (Env:=Env) (lEnv1:=lEnv1) (lEnv2:=lEnv2) (lEnv:=lEnv); auto.
       rewrite lgamma_subst_split_osubst' with (lgsubst1:=lgsubst1) (lgsubst2:=lgsubst2) (E:=E0) (lE:=D) (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst) (Env:=Env) (lEnv1:=lEnv1) (lEnv2:=lEnv2) (lEnv:=lEnv); auto.

       assert (forall x, x `in` dom lgsubst2 -> x `notin` fv_ee e1) as FV1.
         intros x FV.
         apply wf_lgamma_osubst__fv with (x:=x) in Hwflg2; auto.
         assert (x `in` dom D) as xinD.
           apply lenv_split_in_right with (x:=x) in Hsplit; auto.
         assert (x `notin` (dom D1R `union` dom (E'++E0))) as xnotin.
           apply lenv_split_not_in_right with (x:=x) in Hsplit; auto.
         assert (x `notin` dom D') as xnotinD'.
           apply wf_lenv_split in HH.
             apply uniq_from_wf_lenv in HH.
             apply uniq_app_3 in HH.
             solve_uniq.
         assert (x `notin` dom D1L `union` dom D2L) as xnotinD12L.
           apply dom_lenv_split in Hsplit'.
           rewrite Hsplit' in xnotinD'. auto.
         apply typing_fv with (x:=x) in Htyp1; auto.
       rewrite gamma_subst_disjoint_exp with (gsubst:=lgsubst2)(e:=e1); auto.
       assert (forall x, x `in` dom lgsubst1 -> x `notin` fv_ee e2) as FV2.
         intros x FV.
         apply wf_lgamma_osubst__fv with (x:=x) in Hwflg1; auto.
         assert (x `in` dom D) as xinD.
           apply lenv_split_in_left with (x:=x) in Hsplit; auto.
         assert (x `notin` (dom D2R `union` dom (E'++E0))) as xnotin.
           apply lenv_split_not_in_left with (x:=x) in Hsplit; auto.
         assert (x `notin` dom D') as xnotinD'.
           apply wf_lenv_split in HH.
             apply uniq_from_wf_lenv in HH.
             apply uniq_app_3 in HH.
             solve_uniq.
         assert (x `notin` dom D1L `union` dom D2L) as xnotinD12L.
           apply dom_lenv_split in Hsplit'.
           rewrite Hsplit' in xnotinD'. auto.
         apply typing_fv with (x:=x) in Htyp2; auto.
       rewrite gamma_subst_disjoint_exp with (gsubst:=lgsubst1)(e:=e2); auto.

     repeat(rewrite EQ). clear EQ.
     assert (wf_delta_osubst E0 dsubst Env) as Wfd.
       apply wf_lgamma_osubst__wf_osubst in J.
       destruct J; auto.
     apply typing_app with (T1:=apply_delta_subst_typ dsubst T1) (K:=K)
                           (D1:=apply_delta_subst_lenv dsubst D1L ++ lEnv1)
                           (D2:=apply_delta_subst_lenv dsubst D2L ++ lEnv2).     
       rewrite <- commut_delta_subst_arrow.
       apply IHHtyp1 with (E:=E0)(D:=D1R)(D':=D1L); auto.
         apply dom_lenv_split in Hsplit'. solve_uniq.

         apply dom_lenv_split in Hsplit'. 
         apply lgamma_osubst_split__lenv_split in Hgsplit.
         apply dom_lenv_split in Hgsplit. solve_uniq.

         apply wf_lenv_merge; auto.
           eapply wfle_osubst_closed; eauto.
             assert (disjoint (D'++D) Env) as Disj.
               assert (disjoint D Env) as Disj'.
                 apply disjoint_lgamma_osubst in J.
                 decompose [and] J; auto.
               clear Disj2. solve_uniq.
             apply disjoint_sub with (D1:=D'++D); auto.
               apply dom_lenv_split in HH.
               rewrite HH. simpl_env. fsetdec.

           apply lgamma_osubst_split__lenv_split in Hgsplit.
           rewrite_env (nil ++ Env) in Hgsplit.
           apply lenv_split_weakening with (F:=apply_delta_subst_env dsubst E') in Hgsplit; auto.
             apply wf_lenv_disjoint in Wfe2.
             solve_uniq.      

           assert (JJ:=@apply_delta_subst_lenv_dom dsubst D1L).
           assert (disjoint (D'++D) lEnv) as Disj.
             assert (disjoint D lEnv) as Disj'.
               apply disjoint_lgamma_osubst in J.
               decompose [and] J; auto.
             clear Disj1. solve_uniq.
           apply lgamma_osubst_split__lenv_split in Hgsplit.
           apply dom_lenv_split in Hgsplit.
           apply dom_lenv_split in HH.
           apply disjoint_sub with (D1:=D'++D); auto.
             apply disjoint_sym_1.
             apply disjoint_sub with (D1:=lEnv); auto.
               rewrite Hgsplit. fsetdec.
             rewrite <- JJ. rewrite HH. simpl_env. fsetdec.

         apply lgamma_osubst_split__lenv_split in Hgsplit.
         rewrite_env (nil ++ Env) in Hgsplit.
         apply lenv_split_weakening with (F:=apply_delta_subst_env dsubst E') in Hgsplit; auto.
           apply wf_lenv_disjoint in Wfe2.
           solve_uniq.      

       apply IHHtyp2 with (E:=E0)(D:=D2R)(D':=D2L); auto.
         apply dom_lenv_split in Hsplit'. solve_uniq.

         apply dom_lenv_split in Hsplit'. 
         apply lgamma_osubst_split__lenv_split in Hgsplit.
         apply dom_lenv_split in Hgsplit. solve_uniq.

         apply wf_lenv_merge; auto.
           eapply wfle_osubst_closed; eauto.
             assert (disjoint (D'++D) Env) as Disj.
               assert (disjoint D Env) as Disj'.
                 apply disjoint_lgamma_osubst in J.
                 decompose [and] J; auto.
               clear Disj2. solve_uniq.
             apply disjoint_sub with (D1:=D'++D); auto.
               apply dom_lenv_split in HH.
               rewrite HH. simpl_env. fsetdec.

           apply lgamma_osubst_split__lenv_split in Hgsplit.
           rewrite_env (nil ++ Env) in Hgsplit.
           apply lenv_split_weakening with (F:=apply_delta_subst_env dsubst E') in Hgsplit; auto.
             apply wf_lenv_disjoint in Wfe2.
             solve_uniq.      

           assert (JJ:=@apply_delta_subst_lenv_dom dsubst D2L).
           assert (disjoint (D'++D) lEnv) as Disj.
             assert (disjoint D lEnv) as Disj'.
               apply disjoint_lgamma_osubst in J.
               decompose [and] J; auto.
             clear Disj1. solve_uniq.
           apply lgamma_osubst_split__lenv_split in Hgsplit.
           apply dom_lenv_split in Hgsplit.
           apply dom_lenv_split in HH.
           apply disjoint_sub with (D1:=D'++D); auto.
             apply disjoint_sym_1.
             apply disjoint_sub with (D1:=lEnv); auto.
               rewrite Hgsplit. fsetdec.
             rewrite <- JJ. rewrite HH. simpl_env. fsetdec.

         apply lgamma_osubst_split__lenv_split in Hgsplit.
         rewrite_env (nil ++ Env) in Hgsplit.
         apply lenv_split_weakening with (F:=apply_delta_subst_env dsubst E') in Hgsplit; auto.
           apply wf_lenv_disjoint in Wfe2.
           solve_uniq.      

       eapply lenv_split_osubst_closed with (lE1:=D1R) (lE2:=D2R) (lE:=D); eauto.
         apply dom_lenv_split in Hsplit. fsetdec.

         apply disjoint_lgamma_osubst in J. decompose [and] J.
         split. solve_uniq.
         split; auto.
           apply wf_lenv_disjoint in Wfe2. 
           clear J H H0 H1 H2 H3 H4 H5 H6 H7 H9 Disj1 Disj2. 
           assert (JJ:=@apply_delta_subst_env_dom dsubst E').
           solve_uniq.

         apply lgamma_osubst_split__lenv_split in Hgsplit; auto.
  Case "typing_tabs".
     assert (wf_gamma_osubst E0 dsubst gsubst Env) as Wfg.
       apply wf_lgamma_osubst__wf_osubst in Hwfg.
       decompose [and] Hwfg; auto.
     assert (wf_delta_osubst E0 dsubst Env) as Wfd.
       apply wf_lgamma_osubst__wf_osubst in Hwfg.
       decompose [and] Hwfg; auto.
     apply typing_tabs with (L:=L `union` dom gsubst `union` dom lgsubst  
                                 `union` dom dsubst `union` dom (apply_delta_subst_env dsubst E')
                                 `union` dom (apply_delta_subst_lenv dsubst D') `union` dom (E'++E0)
                                 `union` dom Env `union` dom lEnv); auto.
       intros.
       rewrite <- apply_delta_subst_typ_nfv with (dsubst:=dsubst); auto.
       rewrite <- apply_gamma_subst_typ_nfv with (gsubst:=gsubst); auto.
       rewrite <- apply_gamma_subst_typ_nfv with (gsubst:=lgsubst); auto.
       rewrite <- commut_delta_osubst_open_te with (dE:=E0) (Env:=Env); auto.
       rewrite <- commut_gamma_osubst_open_te with (E:=E0) (D:=D0) (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst) (Env:=Env) (lEnv:=lEnv); auto.
       rewrite <- commut_lgamma_osubst_open_te with (E:=E0) (D:=D0) (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst) (Env:=Env) (lEnv:=lEnv); auto.
       eapply delta_gamma_lgamma_osubst_value; eauto.

       intros.
       assert (X `notin` L) as FrxL. auto.
       apply H1 with (D:=D0) (D'0:=D')(E:=E0)(gsubst:=gsubst)(lgsubst:=lgsubst)(dsubst:=dsubst)(E'0:=[(X,bind_kn K)]++E')(Env:=Env)(lEnv:=lEnv) in FrxL; clear H1; auto.
         rewrite commut_lgamma_osubst_open_te with (E:=E0)(D:=D0)(gsubst:=gsubst)(dsubst:=dsubst)(Env:=Env)(lEnv:=lEnv)  in FrxL; auto.
         rewrite commut_gamma_osubst_open_te with (E:=E0) (D:=D0) (lgsubst:=lgsubst) (dsubst:=dsubst)(Env:=Env)(lEnv:=lEnv)  in FrxL; auto.
         rewrite commut_delta_osubst_open_te with (dE:=E0)(Env:=Env) in FrxL; auto.
         rewrite commut_delta_osubst_open_tt with (dE:=E0)(Env:=Env) in FrxL; auto.
         simpl in FrxL. simpl_env in *.
         rewrite apply_delta_subst_typ_nfv in FrxL; auto.
         rewrite apply_gamma_subst_typ_nfv in FrxL; auto.
         rewrite apply_gamma_subst_typ_nfv in FrxL; auto.
         rewrite apply_delta_subst_typ_nfv in FrxL; auto.

         rewrite_env (nil++[(X, bind_kn K)]++apply_delta_subst_env dsubst E' ++ Env).
         apply wf_lenv_weakening; auto.
           simpl_env. apply wf_env_kn; auto.

         rewrite_env (nil++[(X, bind_kn K)]++apply_delta_subst_env dsubst E' ++ Env).
         apply wf_lenv_weakening; auto.
           simpl_env. apply wf_env_kn; auto.
  Case "typing_tapp".
     assert (wf_gamma_osubst E0 dsubst gsubst Env) as Wfg.
       apply wf_lgamma_osubst__wf_osubst in Hwfg.
       decompose [and] Hwfg; auto.
     assert (wf_delta_osubst E0 dsubst Env) as Wfd.
       apply wf_lgamma_osubst__wf_osubst in Hwfg.
       decompose [and] Hwfg; auto.
     rewrite commut_delta_osubst_open_tt with (dE:=E0)(Env:=Env); auto.
     apply typing_tapp with (K:=K).
       rewrite <- commut_delta_subst_all.
       eapply IHHtyp with (E:=E0) ; eauto.

       eapply wft_osubst_closed with (E:=E0); eauto.
  Case "typing_apair".
     apply typing_apair; eauto.
  Case "typing_fst".
     apply typing_fst with (T2:=apply_delta_subst_typ dsubst T2).
       rewrite <- commut_delta_subst_with.
       eapply IHHtyp with (E:=E0); eauto.
  Case "typing_snd".
     apply typing_snd with (T1:=apply_delta_subst_typ dsubst T1).
       rewrite <- commut_delta_subst_with.
       eapply IHHtyp with (E:=E0); eauto.
Qed.

Lemma typing_osubst : forall E D e t dsubst gsubst lgsubst Env lEnv,
  wf_lgamma_osubst E D dsubst gsubst lgsubst Env lEnv ->
  typing E D e t ->
  typing Env lEnv (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e))) (apply_delta_subst_typ dsubst t).
Proof.
  intros E D e t dsubst gsubst lgsubst Env lEnv Wflg Typing.
  rewrite_env (nil ++ D) in Typing.
  rewrite_env (nil ++ E) in Typing.
  apply typing_osubst_closed with (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst) (Env:=Env) (lEnv:=lEnv) in Typing; auto.
    simpl. apply wf_lgamma_osubst__wf_lenv in Wflg. decompose [and] Wflg; auto.
    simpl. apply wf_lgamma_osubst__wf_lenv in Wflg. decompose [and] Wflg; auto.
Qed.

Lemma wft_osubst: forall t dsubst E K Env,
  wf_delta_osubst E dsubst Env ->
  wf_typ E t K ->
  wf_typ Env (apply_delta_subst_typ dsubst t) K.
intros.
  rewrite_env (apply_delta_subst_env dsubst empty ++ Env).
  apply wft_osubst_closed with (E:=E) (E':=@nil (atom*binding)) (dsubst:=dsubst); auto.
    apply wf_delta_osubst__uniq in H. decompose [and] H. auto.
    apply wf_delta_osubst__uniq in H. decompose [and] H. auto.
Qed.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../../../metatheory" "-I" "../linf") ***
*** End: ***
 *)
