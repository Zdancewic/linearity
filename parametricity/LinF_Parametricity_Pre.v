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

Inductive wf_delta_subst : env -> delta_subst -> Prop :=
  | wf_delta_subst_empty :
      wf_delta_subst nil delta_nil
  | wf_delta_subst_styp : forall E SE X T k,
      wf_delta_subst E SE -> X `notin` dom E -> wf_typ nil T k ->
      wf_delta_subst ([(X, bind_kn k)] ++ E) ([(X, T)] ++ SE)
  | wf_delta_subst_skip : forall E SE x T,
      wf_delta_subst E SE -> x `notin` dom E -> wf_typ E T kn_nonlin ->
      wf_delta_subst ([(x, bind_typ T)] ++ E) SE
  .

Tactic Notation "wf_delta_subst_cases" tactic(first) tactic(c) :=
  first;
  [ c "wf_delta_subst_empty" |
    c "wf_delta_subst_styp" |
    c "wf_delta_subst_skip"].

(*  Substitutee on Gamma, map from exp vars to exprs(closed) *)

Inductive wf_gamma_subst : env -> delta_subst -> gamma_subst -> Prop :=
  | wf_gamma_subst_empty :
      wf_gamma_subst nil delta_nil gamma_nil
  | wf_gamma_subst_sval : forall x e T E dsE gsE,
      wf_gamma_subst E dsE gsE -> x `notin` dom E ->
      typing nil nil e (apply_delta_subst_typ dsE T) -> wf_typ E T kn_nonlin ->
      wf_gamma_subst ([(x, bind_typ T)] ++ E) dsE ([(x, e)]++gsE)
  | wf_gamma_subst_skind : forall X T E dsE gsE k,
      wf_gamma_subst E dsE gsE -> X `notin` dom E ->
      wf_typ nil T k ->
      wf_gamma_subst ([(X, bind_kn k)]++E) ([(X, T)]++dsE) gsE
  .

Tactic Notation "wf_gamma_subst_cases" tactic(first) tactic(c) :=
  first;
  [ c "wf_gamma_subst_empty" |
    c "wf_gamma_subst_sval" |
    c "wf_gamma_subst_skind"].

(*  Substitutee on lin Context, map from exp vars to exprs(closed) *)

Inductive wf_lgamma_subst : env -> lenv -> delta_subst -> gamma_subst -> gamma_subst -> Prop :=
  | wf_lgamma_subst_empty : 
      wf_lgamma_subst nil nil nil nil nil
  | wf_lgamma_subst_sval : forall x e T E lE dsE gsE lgsE,
      wf_lgamma_subst E lE dsE gsE lgsE -> 
      x `notin` dom E ->
      x `notin` dom lE ->
      typing nil nil e (apply_delta_subst_typ dsE T) -> 
      wf_typ E T kn_nonlin ->
      wf_lgamma_subst ([(x, bind_typ T)] ++ E) lE dsE ([(x, e)]++gsE) lgsE
  | wf_lgamma_subst_slval : forall x e T E lE dsE gsE lgsE,
      wf_lgamma_subst E lE dsE gsE lgsE -> 
      x `notin` dom E ->
      x `notin` dom lE -> 
      typing nil nil e (apply_delta_subst_typ dsE T) -> 
      wf_typ E T kn_lin ->
      wf_lgamma_subst E ([(x, lbind_typ T)] ++ lE) dsE gsE ([(x, e)]++lgsE)
  | wf_lgamma_subst_skind : forall X T E lE dsE gsE lgsE k,
      wf_lgamma_subst E lE dsE gsE lgsE -> 
      X `notin` dom E ->
      X `notin` dom lE ->
      wf_typ nil T k ->
      wf_lgamma_subst ([(X, bind_kn k)]++E) lE ([(X, T)]++dsE) gsE lgsE
  .

Tactic Notation "wf_lgamma_subst_cases" tactic(first) tactic(c) :=
  first;
  [ c "wf_lgamma_subst_empty" |
    c "wf_lgamma_subst_sval" |
    c "wf_lgamma_subst_slval" |
    c "wf_lgamma_subst_skind" ].

(* ********************************************************************** *)
(** * #<a name="split"></a># Linear Substitution Splitting *)

Inductive lgamma_subst_split : env -> lenv -> delta_subst -> gamma_subst -> gamma_subst -> gamma_subst -> gamma_subst -> Prop :=
  | lgamma_subst_split_empty: forall E dsE gsE, 
       wf_lgamma_subst E nil dsE gsE nil -> 
       lgamma_subst_split E nil dsE gsE nil nil nil 
  | lgamma_subst_split_left: forall E D dsE gsE lgsE1 lgsE2 lgsE3 x e T,
       lgamma_subst_split E D dsE gsE lgsE1 lgsE2 lgsE3 ->
       x `notin` dom E ->
       x `notin` dom D ->
       typing nil nil e (apply_delta_subst_typ dsE T) -> 
       wf_typ E T kn_lin ->
       lgamma_subst_split E ([(x, lbind_typ T)]++D) dsE gsE ([(x, e)]++lgsE1) lgsE2 ([(x, e)]++lgsE3)
  | lgamma_subst_split_right: forall E D dsE gsE lgsE1 lgsE2 lgsE3 x e T,
       lgamma_subst_split E D dsE gsE lgsE1 lgsE2 lgsE3 ->
       x `notin` dom E ->
       x `notin` dom D ->
       typing nil nil e (apply_delta_subst_typ dsE T) -> 
       wf_typ E T kn_lin ->
       lgamma_subst_split E ([(x, lbind_typ T)]++D) dsE gsE lgsE1 ([(x, e)]++lgsE2) ([(x, e)]++lgsE3)
  .

Tactic Notation "lgamma_subst_split_cases" tactic(first) tactic(c) :=
  first;
  [ c "lgamma_subst_split_empty" |
    c "lgamma_subst_split_left" |
    c "lgamma_subst_split_right"].

Hint Constructors wf_delta_subst wf_gamma_subst wf_lgamma_subst lgamma_subst_split.

(* ********************************************************************** *)
(** * Commuting properties about substitution and opening *)

Lemma swap_subst_ee_gsubst: forall e' x E D dsubst gsubst lgsubst e t,
  wf_lgamma_subst E D dsubst gsubst lgsubst ->
  typing nil nil e' t ->
  x `notin` dom gsubst ->
  subst_ee x e' (apply_gamma_subst gsubst e) =
  apply_gamma_subst gsubst (subst_ee x e' e).
Proof.
  intros e' x E D dsubst gsubst lgsubst e t Hwflg Hwft xngsubst.
  generalize dependent e.
  generalize dependent e'.
  generalize dependent t.
  induction Hwflg; intros t e' Hwft e0; simpl; eauto.
    rewrite subst_ee_commute; eauto.
      eauto using typing_fv.
      eauto using typing_fv.
Qed.

Lemma swap_subst_ee_lgsubst: forall e' x E D dsubst gsubst lgsubst e t,
  wf_lgamma_subst E D dsubst gsubst lgsubst ->
  typing nil nil e' t ->
  x `notin` dom lgsubst ->
  subst_ee x e' (apply_gamma_subst lgsubst e) =
  apply_gamma_subst lgsubst (subst_ee x e' e).
Proof.
  intros e' x E D dsubst gsubst lgsubst e t Hwflg Hwft xngsubst.
  generalize dependent e.
  generalize dependent e'.
  generalize dependent t.
  induction Hwflg; intros t e' Hwft e0; simpl; eauto.
    rewrite subst_ee_commute; eauto.
      eauto using typing_fv.
      eauto using typing_fv.
Qed.

(********************************************************)
(* well found subst give envs *)
Lemma dom_delta_subst : forall E deltaE,
  wf_delta_subst E deltaE -> ddom_env E [=] dom deltaE.
Proof.
  intros E deltaE Hwfd.
  induction Hwfd; simpl_env; fsetdec.
Qed.

Lemma wf_delta_subst__uniq : forall E dsubst,
  wf_delta_subst E dsubst -> wf_env E /\ uniq E /\ uniq dsubst.
Proof.
  intros E dsubst H.
  (wf_delta_subst_cases (induction H) Case); auto.
  Case "wf_delta_subst_styp".
    decompose [and] IHwf_delta_subst.
    split; auto.
    split; auto.
      apply dom_delta_subst in H.
      apply dom__ddom in H0. 
      rewrite H in H0; auto.
  Case "wf_delta_subst_skip".
    split; decompose [and] IHwf_delta_subst; auto.
Qed.

(*******************************************************************************)
(** subst under delta/gamma *)

Lemma delta_subst_opt :  forall E E' dsubst X t t' dsubst' K,
   wf_delta_subst (E'++[(X, bind_kn K)]++E) (dsubst'++[(X, t)]++dsubst) ->
   X `notin` (dom E `union` dom E') ->
   ddom_env E [=] dom dsubst ->
   ddom_env E' [=] dom dsubst' ->
   wf_typ nil t K ->
   apply_delta_subst_typ (dsubst'++[(X, t)]++dsubst) t' =
     apply_delta_subst_typ (dsubst'++dsubst) (subst_tt X t t').
Proof.
  intros E E' dsubst X t t' dsubst' K Hwf_delta_subst Fr Heq He1' Hwft.
  remember (E'++[(X, bind_kn K)]++E) as G.
  remember (dsubst'++[(X, t)]++dsubst) as Dsubst.
  generalize dependent t'.
  generalize dependent dsubst'.
  generalize dependent E'.
  (wf_delta_subst_cases (induction Hwf_delta_subst) Case); 
    intros E' HeqG Fr dsubst' HeqDsubst Heq' t'.
  Case "wf_delta_subst_empty".
    contradict HeqG; auto.    
  Case "wf_delta_subst_styp".
    destruct (one_eq_app _ _ _ _ _ HeqG) as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
    SCase "exists E'', E'=E&X0'' /\ E0=E&X&E'' ".
      destruct (one_eq_app _ _ _ _ _ HeqDsubst) as [[dsubst'' [DEQ1 DEQ2]] | [DEQ1 DEQ2]]; subst.
      SSCase "exists DS'',DS'=DS&X0'' /\ DS0=DS&X&DS'' ".
        simpl. simpl_env. 
        rewrite <- subst_tt_commute; auto.
          apply IHHwf_delta_subst with (E':=E''); auto.
             apply ddom_dom__inv with (X:=X0)(b:= t)(K:=K); auto.
               apply dom_delta_subst in Hwf_delta_subst.
               apply dom__ddom in H.
               rewrite Hwf_delta_subst in H. simpl_env in *. auto.
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
  Case "wf_delta_subst_skip".
    subst.
    destruct (one_eq_app _ _ _ _ _ HeqG) as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      apply IHHwf_delta_subst with (E':=E''); auto.
      inversion EQ2.
Qed.

Lemma swap_subst_te_gsubst: forall t X E D dsubst gsubst lgsubst e K,
  wf_lgamma_subst E D dsubst gsubst lgsubst ->
  wf_typ nil t K ->
  subst_te X t (apply_gamma_subst gsubst e) =
  apply_gamma_subst gsubst (subst_te X t e).
Proof.
  intros t X E D dsubst gsubst lgsubst e K Hwflg Hwft.
  generalize dependent e.
  generalize dependent t.
  induction Hwflg; intros t Hwft e0; simpl; auto.
    rewrite subst_te_ee_commute; auto.
    eauto using notin_fv_te_typing.
Qed.

Lemma swap_subst_te_lgsubst: forall t X E D dsubst gsubst lgsubst e K,
  wf_lgamma_subst E D dsubst gsubst lgsubst ->
  wf_typ nil t K ->
  subst_te X t (apply_gamma_subst lgsubst e) =
  apply_gamma_subst lgsubst (subst_te X t e).
Proof.
  intros t X E D dsubst gsubst lgsubst e K Hwflg Hwft.
  generalize dependent e.
  generalize dependent t.
  induction Hwflg; intros t Hwft e0; simpl; auto.
    rewrite subst_te_ee_commute; auto.
    eauto using notin_fv_te_typing.
Qed.

Lemma delta_subst_permut : forall dE dsubst X T K t,
  wf_delta_subst dE dsubst ->
  X `notin` dom dsubst -> wf_typ nil T K ->
  apply_delta_subst_typ dsubst (subst_tt X T t) = subst_tt X T (apply_delta_subst_typ dsubst t).
Proof.
  intros dE dsubst X T K t Hwfd Fr Hwft.
  generalize dependent t.
  induction Hwfd; intros; simpl; eauto.
    simpl_env in *.
    rewrite <- subst_tt_commute; eauto using notin_fv_wf.
Qed.

Lemma gamma_subst_value : forall E D dsubst gsubst lgsubst v,
  wf_lgamma_subst E D dsubst gsubst lgsubst ->
  value v ->
  value (apply_gamma_subst gsubst v).
Proof.
  intros E D dsubst gsubst lgsubst v Hwflg Hv.
  generalize dependent v.
  induction Hwflg; intros v Hv; simpl; auto.
    apply IHHwflg; auto.
    destruct Hv; simpl; auto.
      inversion H3. subst.
      apply value_abs.
        apply expr_abs with (L:=L `union` singleton x); auto.
        intros. rewrite subst_ee_open_ee_var; auto.

      inversion H3. subst.
      apply value_tabs.
        apply expr_tabs with (L:=L `union` singleton x); auto.
        intros. rewrite subst_ee_open_te_var; auto.
Qed.

Lemma lgamma_subst_value : forall E D dsubst gsubst lgsubst v,
  wf_lgamma_subst E D dsubst gsubst lgsubst ->
  value v ->
  value (apply_gamma_subst lgsubst v).
Proof.
  intros E D dsubst gsubst lgsubst v Hwflg Hv.
  generalize dependent v.
  induction Hwflg; intros v Hv; simpl; auto.
    apply IHHwflg; auto.
    destruct Hv; simpl; auto.
      inversion H3. subst.
      apply value_abs.
        apply expr_abs with (L:=L `union` singleton x); auto.
        intros. rewrite subst_ee_open_ee_var; auto.

      inversion H3. subst.
      apply value_tabs.
        apply expr_tabs with (L:=L `union` singleton x); auto.
        intros. rewrite subst_ee_open_te_var; auto.
Qed.

Lemma delta_subst_value : forall dE dsubst v,
  wf_delta_subst dE dsubst ->
  value (v) ->
  value (apply_delta_subst dsubst v).
Proof.
  intros dE dsubst v Hwfd Hv.
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

Lemma delta_gamma_subst_value : forall E D dsubst gsubst lgsubst v,
  wf_lgamma_subst E D dsubst gsubst lgsubst ->
  wf_delta_subst E dsubst ->
  value v ->
  value(apply_delta_subst dsubst (apply_gamma_subst gsubst v)).
Proof.
  intros.
  eapply delta_subst_value; eauto.
  eapply gamma_subst_value; eauto.
Qed.

Lemma delta_lgamma_subst_value : forall E D dsubst gsubst lgsubst v,
  wf_lgamma_subst E D dsubst gsubst lgsubst ->
  wf_delta_subst E dsubst ->
  value v ->
  value(apply_delta_subst dsubst (apply_gamma_subst lgsubst v)).
Proof.
  intros.
  eapply delta_subst_value; eauto.
  eapply lgamma_subst_value; eauto.
Qed.

(* ********************************************************************** *)
(* commut and subst *)
Lemma commut_gamma_subst_open_ee: forall E D dsubst gsubst lgsubst e0 e,
   wf_lgamma_subst E D dsubst gsubst lgsubst ->
   apply_gamma_subst gsubst (open_ee e0 e)
= open_ee (apply_gamma_subst gsubst e0) (apply_gamma_subst gsubst e).
Proof.
  intros E D dsubst gsubst lgsubst e0 e Hwfg.
  generalize dependent e0.
  generalize dependent e.
  induction Hwfg; intros; simpl; auto.
    rewrite subst_ee_open_ee; auto.
Qed.

Lemma commut_gamma_subst_open_te: forall E D dsubst gsubst lgsubst e t,
   wf_lgamma_subst E D dsubst gsubst lgsubst ->
   apply_gamma_subst gsubst (open_te e t)
= open_te (apply_gamma_subst gsubst e) (apply_gamma_subst_typ gsubst t).
Proof.
  intros E D dsubst gsubst lgsubst e t Hwfg.
  generalize dependent e.
  generalize dependent t.
  induction Hwfg; intros; simpl; auto.
    unfold apply_gamma_subst_typ in *.
    rewrite subst_ee_open_te; auto.
Qed.

Lemma commut_lgamma_subst_open_ee: forall E D dsubst gsubst lgsubst e0 e,
   wf_lgamma_subst E D dsubst gsubst lgsubst ->
   apply_gamma_subst lgsubst (open_ee e0 e)
= open_ee (apply_gamma_subst lgsubst e0) (apply_gamma_subst lgsubst e).
Proof.
  intros E D dsubst gsubst lgsubst e0 e Hwfg.
  generalize dependent e0.
  generalize dependent e.
  induction Hwfg; intros; simpl; auto.
    rewrite subst_ee_open_ee; auto.
Qed.

Lemma commut_lgamma_subst_open_te: forall E D dsubst gsubst lgsubst e t,
   wf_lgamma_subst E D dsubst gsubst lgsubst ->
   apply_gamma_subst lgsubst (open_te e t)
= open_te (apply_gamma_subst lgsubst e) (apply_gamma_subst_typ lgsubst t).
Proof.
  intros E D dsubst gsubst lgsubst e t Hwfg.
  generalize dependent e.
  generalize dependent t.
  induction Hwfg; intros; simpl; auto.
    unfold apply_gamma_subst_typ in *.
    rewrite subst_ee_open_te; auto.
Qed.

Lemma commut_delta_subst_open_ee: forall dE dsubst e0 e,
   wf_delta_subst dE dsubst ->
   apply_delta_subst dsubst (open_ee e0 e)
= open_ee (apply_delta_subst dsubst e0) (apply_delta_subst dsubst e).
Proof.
  intros dE dsubst e0 e Hwfd.
  generalize dependent e.
  generalize dependent e0.
  induction Hwfd; intros; simpl; auto.
    rewrite subst_te_open_ee; auto.
Qed.

Lemma commut_delta_subst_open_te: forall dE dsubst e t,
   wf_delta_subst dE dsubst ->
   apply_delta_subst dsubst (open_te e t)
= open_te (apply_delta_subst dsubst e) (apply_delta_subst_typ dsubst t).
Proof.
  intros dE dsubst e t Hwfd.
  generalize dependent e.
  generalize dependent t.
  induction Hwfd; intros; simpl; auto.
    rewrite subst_te_open_te; eauto using type_from_wf_typ.
Qed.

Lemma commut_delta_subst_open_tt: forall dE dsubst T X,
   wf_delta_subst dE dsubst ->
   apply_delta_subst_typ dsubst (open_tt T X)
= open_tt (apply_delta_subst_typ dsubst T) (apply_delta_subst_typ dsubst X).
Proof.
  intros dE dsubst T X Hwfd.
  generalize dependent X.
  generalize dependent T.
  induction Hwfd; intros; simpl; auto.
    rewrite subst_tt_open_tt; eauto using type_from_wf_typ.
Qed.

Lemma commut_subst_tt_dsubst: forall t X E dsubst T K,
  wf_delta_subst E dsubst ->
  wf_typ nil t K ->
  X `notin` dom E ->
  apply_delta_subst_typ dsubst (subst_tt X t T) =
  subst_tt X t (apply_delta_subst_typ dsubst T).
Proof.
  intros t X E dsubst T K Hwfd Hwft Fr.
  generalize dependent t.
  generalize dependent T.
  induction Hwfd; intros; simpl; auto.
    simpl_env in*. destruct_notin.
    rewrite <- IHHwfd; auto.
      rewrite subst_tt_commute; eauto using notin_fv_wf.
Qed.

Lemma swap_subst_tt_dsubst: forall t X E dsubst T K,
  wf_delta_subst E dsubst ->
  wf_typ E t K ->
  X `notin` dom E -> X `notin` fv_tt t ->
  apply_delta_subst_typ dsubst (subst_tt X (apply_delta_subst_typ dsubst t) T)=
  apply_delta_subst_typ dsubst (subst_tt X t T).
Proof.
  intros t X E dsubst T K Hwfd Hwft Fr1 Fr2.
  generalize dependent t.
  generalize dependent T.
  induction Hwfd; intros; simpl; auto.
    simpl_env in*. destruct_notin.
    erewrite commut_subst_tt_dsubst with (E:=E); eauto.
    rewrite IHHwfd; auto.
      erewrite <- commut_subst_tt_dsubst with (E:=E); eauto.
      rewrite swap_dubst_tt; eauto using notin_fv_wf.

      apply wf_typ_subst_tb with (E:=E) (F:=(@nil (atom*binding))) (Z:=X0) (P:=T) in Hwft; auto.
        apply wf_typ_weaken_head with (F:=E) in H0; simpl_env in *; auto.
          apply wf_delta_subst__uniq in Hwfd.
          decompose [and] Hwfd; auto.    
      apply notin_fv_tt_subst_tt; eauto using notin_fv_wf.

    rewrite IHHwfd; auto.
      apply wft_strengthen_ex in Hwft; simpl;auto.
Qed.

(* *************** *)
(* red expr value typ *)

Lemma expr_preserved_under_gamma_subst: forall E D dsubst gsubst lgsubst e,
   wf_lgamma_subst E D dsubst gsubst lgsubst ->
   expr e ->
   expr (apply_gamma_subst gsubst e).
Proof.
  intros E D dsubst gsubst lgsubst e Hwfg He.
  generalize dependent e.
  induction Hwfg; intros; auto.
    simpl. apply IHHwfg.
      apply typing_regular in H1.
      decompose [and] H1.
      apply subst_ee_expr; auto.
Qed.

Lemma type_preserved_under_gamma_subst: forall E D dsubst gsubst lgsubst t,
   wf_lgamma_subst E D dsubst gsubst lgsubst ->
   type t ->
   type (apply_gamma_subst_typ gsubst t).
intros. unfold apply_gamma_subst_typ in *.  auto.
Qed.

Lemma expr_preserved_under_lgamma_subst: forall E D dsubst gsubst lgsubst e,
   wf_lgamma_subst E D dsubst gsubst lgsubst ->
   expr e ->
   expr (apply_gamma_subst lgsubst e).
Proof.
  intros E D dsubst gsubst lgsubst e Hwfg He.
  generalize dependent e.
  induction Hwfg; intros; auto.
    simpl. apply IHHwfg.
      apply typing_regular in H1.
      decompose [and] H1.
      apply subst_ee_expr; auto.
Qed.

Lemma type_preserved_under_lgamma_subst: forall E D dsubst gsubst lgsubst t,
   wf_lgamma_subst E D dsubst gsubst lgsubst ->
   type t ->
   type (apply_gamma_subst_typ lgsubst t).
intros. unfold apply_gamma_subst_typ in *.  auto.
Qed.

Lemma expr_preserved_under_delta_subst: forall E dsubst e,
   wf_delta_subst E dsubst ->
   expr e ->
   expr (apply_delta_subst dsubst e).
Proof.
  intros E dsubst e Hwfd He.
  generalize dependent e.
  induction Hwfd; intros; simpl; auto.
    apply IHHwfd.
      apply subst_te_expr; eauto using type_from_wf_typ.
Qed.

Lemma type_preserved_under_delta_subst: forall E dsubst t,
   wf_delta_subst E dsubst ->
   type t ->
   type (apply_delta_subst_typ dsubst t).
Proof.
  intros E dsubst t Hwfd Ht.
  generalize dependent t.
  induction Hwfd; intros; simpl; auto.
    apply IHHwfd.
      apply subst_tt_type; eauto using type_from_wf_typ.
Qed.

Lemma red_abs_preserved_under_delta_subst: forall dE dsubst K T e1 e2,
   wf_delta_subst dE dsubst ->
   red (exp_app (exp_abs K T e1) e2) (open_ee e1 e2) ->
   red (exp_app (apply_delta_subst dsubst (exp_abs K T e1)) (apply_delta_subst dsubst e2))
                  (apply_delta_subst dsubst (open_ee e1 e2)).
Proof.
  intros dE dsubst K T e1 e2 Hwfd Hrc.
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

Lemma red_tabs_preserved_under_delta_subst: forall dE dsubst K e1 t2,
   wf_delta_subst dE dsubst ->
   red (exp_tapp (exp_tabs K e1) t2) (open_te e1 t2) ->
   red (exp_tapp (apply_delta_subst dsubst (exp_tabs K e1)) (apply_delta_subst_typ dsubst t2))
                  (apply_delta_subst dsubst (open_te e1 t2)).
intros.
  generalize dependent e1.
  generalize dependent t2.
  induction H; intros; simpl; auto.
    rewrite subst_te_open_te; eauto using type_from_wf_typ.
    apply IHwf_delta_subst; auto.
      rewrite <- subst_te_open_te; eauto using type_from_wf_typ.
      assert (exp_tapp (exp_tabs K (subst_te X T e1)) (subst_tt X T t2)
                  = subst_te X T (exp_tapp (exp_tabs K e1) t2)). auto.
      rewrite H3.
      apply red_preserved_under_typsubst; eauto using type_from_wf_typ.
Qed.

Lemma red_abs_preserved_under_gamma_subst: forall E D dsubst gsubst lgsubst K T e1 e2,
   wf_lgamma_subst E D dsubst gsubst lgsubst ->
   red (exp_app (exp_abs K T e1) e2) (open_ee e1 e2) ->
   red (exp_app (apply_gamma_subst gsubst (exp_abs K T e1)) (apply_gamma_subst gsubst e2))
                  (apply_gamma_subst gsubst (open_ee e1 e2)).
intros.
  generalize dependent T.
  generalize dependent e1.
  generalize dependent e2.
  induction H; intros; simpl; auto.
    apply typing_regular in H2.  decompose [and] H2.
    rewrite subst_ee_open_ee; auto.
    apply IHwf_lgamma_subst; auto.
      rewrite <- subst_ee_open_ee; auto.
      assert (exp_app (exp_abs K T0 (subst_ee x e e1)) (subst_ee x e e2)
                  = subst_ee x e (exp_app (exp_abs K T0 e1) e2)) as J. auto.
      rewrite J.
      apply red_preserved_under_expsubst; auto.
Qed.

Lemma red_tabs_preserved_under_gamma_subst: forall E D dsubst gsubst lgsubst K e1 t2,
   wf_lgamma_subst E D dsubst gsubst lgsubst ->
   red (exp_tapp (exp_tabs K e1) t2) (open_te e1 t2) ->
   red (exp_tapp (apply_gamma_subst gsubst (exp_tabs K e1)) (apply_gamma_subst_typ gsubst t2))
                  (apply_gamma_subst gsubst (open_te e1 t2)).
intros.
  generalize dependent e1.
  generalize dependent t2.
  induction H; intros; simpl; auto.
    apply typing_regular in H2.  decompose [and] H2.
    rewrite subst_ee_open_te; auto.
    unfold apply_gamma_subst_typ in *.
    apply IHwf_lgamma_subst; auto.
      rewrite <- subst_ee_open_te; auto.
      assert (exp_tapp (exp_tabs K (subst_ee x e e1)) t2
                  = subst_ee x e (exp_tapp (exp_tabs K e1) t2)) as J. auto.
      rewrite J.
      apply red_preserved_under_expsubst; auto.
Qed.

Lemma red_abs_preserved_under_lgamma_subst: forall E D dsubst gsubst lgsubst K T e1 e2,
   wf_lgamma_subst E D dsubst gsubst lgsubst ->
   red (exp_app (exp_abs K T e1) e2) (open_ee e1 e2) ->
   red (exp_app (apply_gamma_subst lgsubst (exp_abs K T e1)) (apply_gamma_subst lgsubst e2))
                  (apply_gamma_subst lgsubst (open_ee e1 e2)).
intros.
  generalize dependent T.
  generalize dependent e1.
  generalize dependent e2.
  induction H; intros; simpl; auto.
    apply typing_regular in H2.  decompose [and] H2.
    rewrite subst_ee_open_ee; auto.
    apply IHwf_lgamma_subst; auto.
      rewrite <- subst_ee_open_ee; auto.
      assert (exp_app (exp_abs K T0 (subst_ee x e e1)) (subst_ee x e e2)
                  = subst_ee x e (exp_app (exp_abs K T0 e1) e2)) as J. auto.
      rewrite J.
      apply red_preserved_under_expsubst; auto.
Qed.

Lemma red_tabs_preserved_under_lgamma_subst: forall E D dsubst gsubst lgsubst K e1 t2,
   wf_lgamma_subst E D dsubst gsubst lgsubst ->
   red (exp_tapp (exp_tabs K e1) t2) (open_te e1 t2) ->
   red (exp_tapp (apply_gamma_subst lgsubst (exp_tabs K e1)) (apply_gamma_subst_typ lgsubst t2))
                  (apply_gamma_subst lgsubst (open_te e1 t2)).
intros.
  generalize dependent e1.
  generalize dependent t2.
  induction H; intros; simpl; auto.
    apply typing_regular in H2.  decompose [and] H2.
    rewrite subst_ee_open_te; auto.
    unfold apply_gamma_subst_typ in *.
    apply IHwf_lgamma_subst; auto.
      rewrite <- subst_ee_open_te; auto.
      assert (exp_tapp (exp_tabs K (subst_ee x e e1)) t2
                  = subst_ee x e (exp_tapp (exp_tabs K e1) t2)) as J. auto.
      rewrite J.
      apply red_preserved_under_expsubst; auto.
Qed.

(* ********************************************************************** *)
(* weaken stronger *)
Lemma dsubst_stronger : forall E E' dsubst dsubst' X K t,
  wf_delta_subst (E'++[(X,bind_kn K)]++E) (dsubst'++[(X,t)]++dsubst) ->
  wf_typ nil t K ->
  ddom_env E [=] dom dsubst ->
  ddom_env E' [=] dom dsubst' ->
  X `notin` (fv_env E `union` fv_env E')->
  wf_delta_subst (E'++E) (dsubst'++dsubst).
Proof.
  intros E E' dsubst dsubst' X K t Hwf_dsubst HT HdomE HdomE' HX.
  remember (E'++[(X,bind_kn K)]++E) as G.
  remember (dsubst'++[(X,t)]++dsubst) as dsG.
  generalize dependent E'.
  generalize dependent dsubst'.
  (wf_delta_subst_cases (induction Hwf_dsubst) Case); intros; subst.
  Case "wf_delta_subst_empty".
    contradict HeqG; auto.
  Case "wf_delta_subst_styp".
    apply one_eq_app in HeqG. destruct HeqG as [[E'' [EQ1 EQ2]] |  [EQ1 EQ2]]; subst.
      apply one_eq_app in HeqdsG. destruct HeqdsG as [[dsE'' [dsEQ1 dsEQ2]] | [dsEQ1 dsEQ2]]; subst.
        simpl_env.
        apply wf_delta_subst_styp; simpl in *; auto.
          apply IHHwf_dsubst; auto.
            apply ddom_dom__inv with (X:=X0)(b:=t)(K:=K); auto.
              apply dom_delta_subst in Hwf_dsubst. apply dom__ddom in H.
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
  Case "wf_delta_subst_skip".
    apply one_eq_app in HeqG. destruct HeqG as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      simpl_env in *. simpl in HX.
      apply wf_delta_subst_skip; auto.
        apply IHHwf_dsubst; auto.
          rewrite <- HdomE'. simpl. clear. fsetdec.
        apply wf_typ_strengthening_typ in H0; auto.

      inversion EQ2.
Qed.

Lemma dsubst_weaken : forall E E' dsubst dsubst' X K t,
  wf_delta_subst (E'++E) (dsubst'++dsubst) ->
  wf_typ nil t K ->
  ddom_env E [=] dom dsubst ->
  ddom_env E' [=] dom dsubst' ->
  X `notin` (dom E `union` dom E')->
  wf_delta_subst (E'++[(X,bind_kn K)]++E) (dsubst'++[(X,t)]++dsubst).
Proof.
  intros E E' dsubst dsubst' X K t Hwf_dsubst HT HdomE HdomE' HX.
  remember (E'++E) as G.
  remember (dsubst'++dsubst) as dsG.
  generalize dependent E'.
  generalize dependent dsubst'.
  (wf_delta_subst_cases (induction Hwf_dsubst) Case); intros; subst.
  Case "wf_delta_subst_empty".
    destruct dsubst.
      destruct dsubst'; inversion HeqdsG.
         destruct E.
            destruct E'; inversion HeqG.
              rewrite_env ([(X, bind_kn K)]++nil).
              rewrite_env ([(X, t)]++nil).
              eapply wf_delta_subst_styp with (E:=(@nil (atom*binding))) (X:=X) (SE:=delta_nil) (T:=t); eauto.
            inversion HeqG.
          destruct E'; inversion HeqG.
      destruct dsubst'; inversion HeqdsG.
  Case "wf_delta_subst_styp".
    apply one_eq_app in HeqG. destruct HeqG as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      apply one_eq_app in HeqdsG. destruct HeqdsG as [[dsE'' [dsEQ1 dsEQ2]] | [dsEQ1 dsEQ2]]; subst.
        simpl_env.
        apply wf_delta_subst_styp; auto.
          apply IHHwf_dsubst; auto.
            apply ddom_dom__inv with (X:=X0)(b:=t)(K:=K); auto.
              apply dom_delta_subst in Hwf_dsubst. apply dom__ddom in H.
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
      apply wf_delta_subst_styp; auto.
  Case "wf_delta_subst_skip".
    apply one_eq_app in HeqG. destruct HeqG as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      simpl_env. apply wf_delta_subst_skip; auto.
        apply wf_typ_weakening; auto.
          apply uniq_insert_mid; auto.
            apply wf_delta_subst__uniq in Hwf_dsubst.
            decompose [and] Hwf_dsubst; auto.    

      simpl in HdomE'.
      assert (dom dsubst' [=] {}). fsetdec.
      apply dom_empty_inv in H1. subst.
      simpl_env in *. apply wf_delta_subst_styp; auto.
Qed.

Lemma dsubst_weaken_head : forall E dsubst X K t,
  wf_delta_subst E dsubst ->
  wf_typ nil t K ->
  ddom_env E [=] dom dsubst ->
  X `notin` (dom E)->
  wf_delta_subst ([(X,bind_kn K)]++E) ([(X,t)]++dsubst).
Proof.
  intros E dsubst X K t Hwf_dsubst Ht HdomE HX.
    apply dsubst_weaken with (K:=K) (t:=t) (E:=E) (E':=(@nil (atom*binding))) (dsubst:=dsubst) (dsubst':=delta_nil) (X:=X); simpl_env; eauto.
Qed.

Lemma typing_dsubst_stronger : forall v E dsubst dsubst' X t T,
  typing nil nil v (apply_delta_subst_typ (dsubst'++[(X,t)]++dsubst) T)->
  wf_delta_subst E (dsubst'++[(X,t)]++dsubst) ->
  X `notin` (fv_tt T)->
  typing nil nil v (apply_delta_subst_typ (dsubst'++dsubst) T).
Proof.
  intros.
  remember (dsubst'++[(X,t)]++dsubst) as dsG.
  generalize dependent dsubst'.
  generalize dependent T.
  (wf_delta_subst_cases (induction H0) Case); intros; subst.
  Case "wf_delta_subst_empty".
    contradict HeqdsG; auto.
  Case "wf_delta_subst_styp".
      apply one_eq_app in HeqdsG. destruct HeqdsG as [[dsubst'' [dsEQ1 dsEQ2]] | [dsEQ1 dsEQ2]]; subst.
        simpl_env. simpl_env in H2. simpl.
        apply IHwf_delta_subst with (dsubst':=dsubst''); auto.
          assert (X `notin` fv_tt T).
            apply notin_fv_wf with (E:=(@nil (atom*binding)))(K:=k); auto.
          assert (X `notin` fv_tt (subst_tt X0 T T0)).
            apply notin_fv_tt_subst_tt; auto.
          simpl_env in*. auto.

        inversion dsEQ2. subst. clear dsEQ2.
        simpl in H2. rewrite <- subst_tt_fresh in H2; auto.
  Case "wf_delta_subst_skip".
      apply IHwf_delta_subst with (dsubst'0:=dsubst'); auto.
Qed.

Lemma typing_dsubst_weaken :  forall v E dsubst dsubst' X T t,
  typing nil nil v (apply_delta_subst_typ (dsubst'++dsubst) T)->
  wf_delta_subst E (dsubst'++dsubst) ->
  X `notin` (fv_tt T)->
  typing nil nil v (apply_delta_subst_typ (dsubst'++[(X,t)]++dsubst) T).
Proof.
  intros.
  remember (dsubst'++dsubst) as dsG.
  generalize dependent dsubst'.
  generalize dependent dsubst.
  generalize dependent T.
  (wf_delta_subst_cases (induction H0) Case); intros; subst.
  Case "wf_delta_subst_empty".
    apply nil_eq_app in HeqdsG. destruct HeqdsG. subst.
    simpl in H. simpl.
    rewrite <- subst_tt_fresh; auto.
  Case "wf_delta_subst_styp".
    apply one_eq_app in HeqdsG. destruct HeqdsG as [[dsE'' [dsEQ1 dsEQ2]] | [dsEQ1 dsEQ2]]; subst.
        simpl. simpl_env.
        apply IHwf_delta_subst with (dsubst0:=dsubst) (dsubst':=dsE''); auto.
          assert (X `notin` fv_tt T); eauto using notin_fv_wf.
          assert (X `notin` fv_tt (subst_tt X0 T T0)).
            apply notin_fv_tt_subst_tt; auto.
          simpl_env in *. auto.

        simpl in H2. simpl. rewrite <- subst_tt_fresh with (T:=T0); auto.
  Case "wf_delta_subst_skip".
    apply IHwf_delta_subst with (dsubst0:=dsubst) (dsubst'0:=dsubst'); auto.
Qed.

Lemma typing_dsubst_weaken_head :  forall v E dsubst X T t,
  typing nil nil v (apply_delta_subst_typ dsubst T)->
  wf_delta_subst E dsubst ->
  X `notin` (fv_tt T)->
  typing nil nil v (apply_delta_subst_typ ([(X,t)]++dsubst) T).
Proof.
  intros v E dsubst X T t Htyping Hwfd Hfv.
  apply typing_dsubst_weaken with (E:=E)
            (dsubst:=dsubst) (dsubst':=delta_nil) (X:=X) (T:=T) (t:=t); simpl_env; eauto.
Qed.

(* ********************************************************************** *)
(** * Inversion *)

Lemma wf_lgamma_subst__nfv : forall E D dsubst gsubst lgsubst x,
  wf_lgamma_subst E D dsubst gsubst lgsubst ->
  x `notin` dom E ->
  x `notin` dom D ->
  x `notin` dom dsubst /\ x `notin` dom gsubst /\ x `notin` dom lgsubst 
     /\ x `notin` fv_env E /\ x `notin` fv_lenv D.
intros E D dsubst gsubst lgsubst x Hwfg Hfv Hfv'.
  induction Hwfg; intros; auto.
    apply notin_fv_wf with (X:=x) in H2; simpl; auto.    
    apply notin_fv_wf with (X:=x) in H2; simpl; auto.    
    simpl in Hfv; simpl; auto.
Qed.

Lemma wf_lgamma_subst__wf_lenv : forall E D dsubst gsubst lgsubst,
  wf_lgamma_subst E D dsubst gsubst lgsubst -> 
  wf_env E /\ wf_lenv E D.
Proof.
  intros.
  induction H; auto .
    destruct IHwf_lgamma_subst as [J1 J2].
    split.
      apply wf_env_typ; auto.

      rewrite_env (nil ++ [(x, bind_typ T)] ++ E).
      apply wf_lenv_weakening; auto.
        apply wf_env_typ; auto.

    destruct IHwf_lgamma_subst as [J1 J2].
    split; auto.

    destruct IHwf_lgamma_subst as [J1 J2].
    split; auto.
      rewrite_env (nil ++ [(X, bind_kn k)] ++ E).
      apply wf_lenv_weakening; auto.
        apply wf_env_kn; auto.
Qed.

Lemma wf_lgamma_subst__wf_subst : forall E D dsubst gsubst lgsubst,
  wf_lgamma_subst E D dsubst gsubst lgsubst ->
  wf_gamma_subst E dsubst gsubst /\ wf_delta_subst E dsubst.
intros.
  induction H; auto.
    destruct IHwf_lgamma_subst as [J1 J2].
    split.
      apply wf_gamma_subst_sval; auto.
      apply wf_delta_subst_skip; auto.

    destruct IHwf_lgamma_subst as [J1 J2].
    split.
      apply wf_gamma_subst_skind; auto.
      apply wf_delta_subst_styp; auto.
Qed.

Lemma delta_gamma_lgamma_subst_value : forall E D dsubst gsubst lgsubst v,
  wf_lgamma_subst E D dsubst gsubst lgsubst ->
  wf_delta_subst E dsubst ->
  value v ->
  value(apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst v))).
Proof.
  intros.
  eapply delta_subst_value; eauto.

  eapply gamma_subst_value; eauto.
  eapply lgamma_subst_value; eauto.
Qed.

Lemma wf_lgamma_subst_disjoint : forall E lE dsubst gsubst lgsubst,
  wf_lgamma_subst E lE dsubst gsubst lgsubst ->
  disjoint E lE /\ disjoint dsubst lgsubst /\ disjoint gsubst lgsubst /\
  disjoint E lgsubst /\ disjoint lE dsubst /\ disjoint lE gsubst.
Proof.
  intros E lE dsubst gsubst lgsubst H.
  induction H; auto.
    unfold disjoint. 
    repeat(split; try solve [fsetdec]).

    decompose [and] IHwf_lgamma_subst.
    apply wf_lgamma_subst__nfv with (x:=x) in H; auto.
    decompose [and] H.
    repeat(split; try solve [solve_uniq]).

    decompose [and] IHwf_lgamma_subst.
    apply wf_lgamma_subst__nfv with (x:=x) in H; auto.
    decompose [and] H.
    repeat(split; try solve [solve_uniq]).

    decompose [and] IHwf_lgamma_subst.
    apply wf_lgamma_subst__nfv with (x:=X) in H; auto.
    decompose [and] H.
    repeat(split; try solve [solve_uniq]).
Qed.

Lemma bindsgE__bindsE : forall E D dsubst gsubst lgsubst x t,
  wf_lgamma_subst E D dsubst gsubst lgsubst ->
  binds x (bind_typ t) E ->
  x `notin` dom lgsubst /\
  exists e, binds x (e) gsubst /\ typing nil nil e (apply_delta_subst_typ dsubst t).
intros E D dsubst gsubst lgsubst x t Hwfg Hbinds.
  generalize dependent t.
  induction Hwfg; intros; analyze_binds Hbinds.
    inversion BindsTacVal; subst.
    apply wf_lgamma_subst__nfv with (x:=x0) in Hwfg; auto.
    decompose [and] Hwfg.
    split; auto.
      exists e. split; auto.

    apply IHHwfg in BindsTac.
    destruct BindsTac as [J [e' [Hb Ht]]].
    split; auto.
      exists (e'). split;auto.

    assert (H3:=Hbinds).
    apply IHHwfg in H3.
    destruct H3 as [J [e' [Hb Ht]]].
    split; auto.
      apply binds_In in Hbinds.
      destruct (x==x0); subst; auto.

      exists (e'). split;auto.

    apply IHHwfg in BindsTac; auto.
    destruct BindsTac as [J1 [e' [Hb Ht]]].
    split; auto.
      simpl. rewrite -> delta_subst_permut with (dE:=E)(K:=k); auto.
        rewrite <-subst_tt_fresh; auto.
          exists (e'). split;auto.
    
          apply empty_typing__empty_fv with (X:=X) in Ht.
          decompose [and] Ht; auto.

        apply wf_lgamma_subst__wf_subst in Hwfg; auto.
          destruct Hwfg; auto.
        apply wf_lgamma_subst__nfv with (x:=X) in Hwfg; auto.
Qed.

Lemma lbindsgE__bindslE : forall E D dsubst gsubst lgsubst x t,
  wf_lgamma_subst E D dsubst gsubst lgsubst ->
  binds x (lbind_typ t) D ->
  x `notin` dom gsubst /\
  exists e, binds x (e) lgsubst /\ typing nil nil e (apply_delta_subst_typ dsubst t).
intros E D dsubst gsubst lgsubst x t Hwfg Hbinds.
  generalize dependent t.
  induction Hwfg; intros; analyze_binds Hbinds.
    assert (H3:=Hbinds).
    apply IHHwfg in H3.
    destruct H3 as [J [e' [Hb Ht]]].
    split; auto.
      apply binds_In in Hbinds.
      destruct (x==x0); subst; auto.

      exists (e'). split;auto.

    inversion BindsTacVal; subst.
    apply wf_lgamma_subst__nfv with (x:=x0) in Hwfg; auto.
    decompose [and] Hwfg.
    split; auto.
      exists e. split; auto.

    apply IHHwfg in BindsTac.
    destruct BindsTac as [J [e' [Hb Ht]]].
    split; auto.
      exists (e'). split;auto.

    assert (H2:=Hbinds).
    apply IHHwfg in H2; auto.
    destruct H2 as [J1 [e' [Hb Ht]]].
    split; auto.
      simpl. rewrite -> delta_subst_permut with (dE:=E)(K:=k); auto.
        rewrite <-subst_tt_fresh; auto.
          exists (e'). split;auto.
    
          apply empty_typing__empty_fv with (X:=X) in Ht.
          decompose [and] Ht; auto.

        apply wf_lgamma_subst__wf_subst in Hwfg; auto.
          destruct Hwfg; auto.
        apply wf_lgamma_subst__nfv with (x:=X) in Hwfg; auto.
Qed.

Lemma wf_lgamma_subst__uniq : forall E D dsubst gsubst lgsubst,
  wf_lgamma_subst E D dsubst gsubst lgsubst -> 
  uniq gsubst /\ uniq lgsubst /\ uniq E /\ uniq D.
Proof.
  intros.
  induction H; auto.
    decompose [and] IHwf_lgamma_subst.
    split.
      apply uniq_push; auto.
        apply wf_lgamma_subst__nfv with (x:=x) in H; auto.
    split; auto.

    apply wf_lgamma_subst__nfv with (x:=x) in H; auto.
    decompose [and] IHwf_lgamma_subst.
    split; auto.

    decompose [and] IHwf_lgamma_subst.
    split; auto.
Qed.

Lemma bindsdE__bindsT : forall E dsubst X K,
  wf_delta_subst E dsubst ->
  binds X (bind_kn K) E ->
  exists T, binds X (T) dsubst /\ wf_typ nil T K.
intros.
  induction H; intros; analyze_binds H0; subst.
      inversion BindsTacVal; subst.
      exists (T). split;auto.

      apply IHwf_delta_subst in BindsTac.
      destruct BindsTac as [T' [Hb Hwft]].
      exists (T'). split;auto.
Qed.

Lemma wf_delta_subst__nfv : forall dE dsubst X,
  wf_delta_subst dE dsubst -> X `notin` dom dE -> X `notin` dom dsubst.
intros. induction H; auto.
Qed.

Lemma lgamma_stronger : forall E lE lE' dsubst gsubst lgsubst lgsubst' x t e,
  wf_lgamma_subst E (lE'++[(x,lbind_typ t)]++lE) dsubst gsubst (lgsubst'++[(x,e)]++lgsubst) ->
  wf_lgamma_subst E (lE'++lE) dsubst gsubst (lgsubst'++lgsubst).
Proof.
  intros E lE lE' dsubst gsubst lgsubst lgsubst' x t e Hwf_lgsubst.
  remember (lE'++[(x,lbind_typ t)]++lE) as lE0.
  remember (lgsubst'++[(x,e)]++lgsubst) as lgsubst0.
  generalize dependent lE'.
  generalize dependent lgsubst'.
  induction Hwf_lgsubst; intros; subst.
  Case "wf_lgamma_subst_empty".
    contradict HeqlE0; auto.
  Case "wf_lgamma_subst_sval".
    apply wf_lgamma_subst_sval; simpl in *; auto.
  Case "wf_lgamma_subst_slval".
    apply one_eq_app in HeqlE0. destruct HeqlE0 as [[lE'' [EQ1 EQ2]] |  [EQ1 EQ2]]; subst.
      apply one_eq_app in Heqlgsubst0. destruct Heqlgsubst0 as [[lgsubst'' [lgsEQ1 lgsEQ2]] | [lgsEQ1 lgsEQ2]]; subst.
        simpl_env.
        apply wf_lgamma_subst_slval; simpl in *; auto.

        inversion lgsEQ2. subst.
        rewrite dom_app in H0. simpl in *. destruct_notin.
        tauto.

      apply one_eq_app in Heqlgsubst0. destruct Heqlgsubst0 as [[lgsubst'' [lgsEQ1 lgsEQ2]] | [lgsEQ1 lgsEQ2]]; subst.
        inversion EQ2; subst.
        apply wf_lgamma_subst__nfv with (x:=x0) in Hwf_lgsubst; auto.
        decompose [and] Hwf_lgsubst.
        rewrite dom_app in H4. simpl in *. destruct_notin.
        tauto.

        inversion lgsEQ2. inversion EQ2. subst. auto.
  Case "wf_lgamma_subst_skind".
    apply wf_lgamma_subst_skind; simpl in *; auto.
Qed.

Lemma lgamma_stronger_tail : forall E lE dsubst gsubst lgsubst x t e,
  wf_lgamma_subst E ([(x,lbind_typ t)]++lE) dsubst gsubst ([(x,e)]++lgsubst) ->
  wf_lgamma_subst E lE dsubst gsubst lgsubst.
Proof.
  intros E lE dsubst gsubst lgsubst x t e Hwf_lgsubst.
  rewrite_env (nil++[(x,lbind_typ t)]++lE) in Hwf_lgsubst.
  rewrite_env (nil++[(x,e)]++lgsubst) in Hwf_lgsubst.
  apply lgamma_stronger in Hwf_lgsubst; auto.
Qed.

Lemma lgamma_subst_split__wf_lgamma_subst : forall E D dsubst gsubst lgsubst1 lgsubst2 lgsubst,
  lgamma_subst_split E D dsubst gsubst lgsubst1 lgsubst2 lgsubst ->
  wf_lgamma_subst E D dsubst gsubst lgsubst. 
Proof.
  intros E D dsubst gsubst lgsubst1 lgsubst2 lgsubst H.
  (lgamma_subst_split_cases (induction H) Case); intros; subst; auto.
Qed.

Lemma lgamma_subst_split_nonlin_weakening_typ : forall E G lE dsubst dsubst' gsubst lgsubst1 lgsubst2 lgsubst X K t, 
  lgamma_subst_split (E++G) lE (dsubst'++dsubst) gsubst lgsubst1 lgsubst2 lgsubst ->
  X `notin` fv_lenv lE ->
  wf_lgamma_subst (E++[(X, bind_kn K)]++G) lE (dsubst'++[(X,t)]++dsubst) gsubst lgsubst ->
  lgamma_subst_split (E++[(X, bind_kn K)]++G) lE (dsubst'++[(X,t)]++dsubst) gsubst lgsubst1 lgsubst2 lgsubst.
Proof.
  intros E G lE dsubst dsubst' gsubst lgsubst1 lgsubst2 lgsubst X K t H1 H2 H3.
  remember (E++G) as GG.
  remember (dsubst'++dsubst) as dsubst0.
  generalize dependent E. generalize dependent G.
  generalize dependent dsubst'. generalize dependent dsubst.
  (lgamma_subst_split_cases (induction H1) Case); intros; subst; auto.
  Case "lgamma_subst_split_left".
    apply lgamma_subst_split_left; auto.
      apply IHlgamma_subst_split; auto.
        simpl_env in H2. auto.
        apply lgamma_stronger_tail in H5; auto.

      rewrite dom_app in H.
      rewrite dom_app. rewrite dom_app. simpl.
      apply wf_lgamma_subst_disjoint in H5.
      decompose [and] H5.
      apply disjoint_sym_1 in H9.
      apply disjoint_app_1 in H9.
      apply disjoint_sym_1 in H9.
      apply disjoint_app_2 in H9.
      apply disjoint_app_1 in H9.
      apply disjoint_one_1 in H9; auto.      
    
      apply typing_dsubst_weaken with (E:=E0++G); auto.
        apply lgamma_subst_split__wf_lgamma_subst in H1.
          apply wf_lgamma_subst__wf_subst in H1.
            destruct H1; auto.
        simpl_env in H2. simpl in H2. auto.

      apply wf_typ_weakening; auto.
        apply wf_lgamma_subst__uniq in H5.
        decompose [and] H5; auto.
  Case "lgamma_subst_split_right".
    apply lgamma_subst_split_right; auto.
      apply IHlgamma_subst_split; auto.
        simpl_env in H2. auto.
        apply lgamma_stronger_tail in H5; auto.

      rewrite dom_app in H.
      rewrite dom_app. rewrite dom_app. simpl.
      apply wf_lgamma_subst_disjoint in H5.
      decompose [and] H5.
      apply disjoint_sym_1 in H9.
      apply disjoint_app_1 in H9.
      apply disjoint_sym_1 in H9.
      apply disjoint_app_2 in H9.
      apply disjoint_app_1 in H9.
      apply disjoint_one_1 in H9; auto.      
    
      apply typing_dsubst_weaken with (E:=E0++G); auto.
        apply lgamma_subst_split__wf_lgamma_subst in H1.
          apply wf_lgamma_subst__wf_subst in H1.
            destruct H1; auto.
        simpl_env in H2. simpl in H2. auto.

      apply wf_typ_weakening; auto.
        apply wf_lgamma_subst__uniq in H5.
        decompose [and] H5; auto.
Qed.

Lemma lgamma_subst_split_nonlin_weakening_typ_tail : forall G lE dsubst gsubst lgsubst1 lgsubst2 lgsubst X K t, 
  lgamma_subst_split (G) lE dsubst gsubst lgsubst1 lgsubst2 lgsubst ->
  X `notin` fv_lenv lE ->
  wf_lgamma_subst ([(X, bind_kn K)]++G) lE ([(X,t)]++dsubst) gsubst lgsubst ->
  lgamma_subst_split ([(X, bind_kn K)]++G) lE ([(X,t)]++dsubst) gsubst lgsubst1 lgsubst2 lgsubst.
Proof.
  intros G lE dsubst gsubst lgsubst1 lgsubst2 lgsubst X K t H1 H2 H3.
  rewrite_env (nil ++ [(X, bind_kn K)] ++ G).
  rewrite_env (nil ++ [(X,t)] ++ dsubst).
  apply lgamma_subst_split_nonlin_weakening_typ; auto.
Qed.

Lemma lgamma_subst_split_nonlin_weakening : forall E G lE dsubst gsubst gsubst' lgsubst1 lgsubst2 lgsubst x T e, 
  lgamma_subst_split (E++G) lE dsubst (gsubst'++gsubst) lgsubst1 lgsubst2 lgsubst ->
  x `notin` dom lE ->
  wf_lgamma_subst (E++[(x, bind_typ T)]++G) lE dsubst (gsubst'++[(x,e)]++gsubst) lgsubst ->
  lgamma_subst_split (E++[(x, bind_typ T)]++G) lE dsubst (gsubst'++[(x,e)]++gsubst) lgsubst1 lgsubst2 lgsubst.
Proof.
  intros E G lE dsubst gsubst gsubst' lgsubst1 lgsubst2 lgsubst x T e H1 H2 H3.
  remember (E++G) as GG.
  remember (gsubst'++gsubst) as gsubst0.
  generalize dependent E. generalize dependent G.
  generalize dependent gsubst'. generalize dependent gsubst.
  (lgamma_subst_split_cases (induction H1) Case); intros; subst; auto.
  Case "lgamma_subst_split_left".
    apply lgamma_subst_split_left; auto.
      apply IHlgamma_subst_split; auto.
        simpl_env in H2. auto.
        apply lgamma_stronger_tail in H5; auto.

      apply wf_typ_weakening; auto.
        apply wf_lgamma_subst__uniq in H5.
        decompose [and] H5; auto.
  Case "lgamma_subst_split_right".
    apply lgamma_subst_split_right; auto.
      apply IHlgamma_subst_split; auto.
        simpl_env in H2. auto.
        apply lgamma_stronger_tail in H5; auto.

      apply wf_typ_weakening; auto.
        apply wf_lgamma_subst__uniq in H5.
        decompose [and] H5; auto.
Qed.

Lemma lgamma_subst_split_nonlin_weakening_tail : forall G lE dsubst gsubst lgsubst1 lgsubst2 lgsubst x T e, 
  lgamma_subst_split (G) lE dsubst (gsubst) lgsubst1 lgsubst2 lgsubst ->
  x `notin` dom lE ->
  wf_lgamma_subst ([(x, bind_typ T)]++G) lE dsubst ([(x,e)]++gsubst) lgsubst ->
  lgamma_subst_split ([(x, bind_typ T)]++G) lE dsubst ([(x,e)]++gsubst) lgsubst1 lgsubst2 lgsubst.
Proof.
  intros G lE dsubst gsubst lgsubst1 lgsubst2 lgsubst x T e H1 H2 H3.
  rewrite_env (nil ++ [(x, bind_typ T)] ++ G).
  rewrite_env (nil ++ [(x,e)] ++ gsubst).
  apply lgamma_subst_split_nonlin_weakening; auto.
Qed.

Lemma swap_subst_ee_lgsubst_left: forall e' x E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst e t,
  lgamma_subst_split E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst ->
  typing nil nil e' t ->
  x `notin` dom lgsubst ->
  subst_ee x e' (apply_gamma_subst lgsubst1 e) =
  apply_gamma_subst lgsubst1 (subst_ee x e' e).
Proof.
  intros e' x E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst e t Hsplit Hwft xngsubst.
  generalize dependent e.
  generalize dependent e'.
  generalize dependent t.
  induction Hsplit; intros t e' Hwft e0; simpl; eauto.
    rewrite subst_ee_commute; eauto.
      eauto using typing_fv.
      eauto using typing_fv.
Qed.

Lemma swap_subst_ee_lgsubst_right: forall e' x E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst e t,
  lgamma_subst_split E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst ->
  typing nil nil e' t ->
  x `notin` dom lgsubst ->
  subst_ee x e' (apply_gamma_subst lgsubst2 e) =
  apply_gamma_subst lgsubst2 (subst_ee x e' e).
Proof.
  intros e' x E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst e t Hsplit Hwft xngsubst.
  generalize dependent e.
  generalize dependent e'.
  generalize dependent t.
  induction Hsplit; intros t e' Hwft e0; simpl; eauto.
    rewrite subst_ee_commute; eauto.
      eauto using typing_fv.
      eauto using typing_fv.
Qed.

Lemma lgamma_subst_split_subst : forall E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst e,
  lgamma_subst_split E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst ->
  apply_gamma_subst lgsubst e = (apply_gamma_subst lgsubst1 (apply_gamma_subst lgsubst2 e)).
Proof.
  intros E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst e Hsplit.
  (lgamma_subst_split_cases (induction Hsplit) Case); intros; simpl; auto.
  Case "lgamma_subst_split_left".
    assert (J:=Hsplit).
    apply lgamma_subst_split__wf_lgamma_subst in J.
    assert (x `notin` dom lgsE3) as K.
      apply wf_lgamma_subst__nfv with (x:=x) in J; auto.
    erewrite <- swap_subst_ee_lgsubst_left with (e:=apply_gamma_subst lgsE2 e); eauto.
    rewrite <- IHHsplit; auto.
    erewrite <- swap_subst_ee_lgsubst with (e:=e); eauto.
  Case "lgamma_subst_split_right".
    assert (J:=Hsplit).
    apply lgamma_subst_split__wf_lgamma_subst in J.
    assert (x `notin` dom lgsE3) as K.
      apply wf_lgamma_subst__nfv with (x:=x) in J; auto.
    erewrite <- swap_subst_ee_lgsubst with (e:=e); eauto.
    rewrite IHHsplit; auto.
    erewrite <- swap_subst_ee_lgsubst_right with (e:=e); eauto.
    erewrite <- swap_subst_ee_lgsubst_left with (e:=apply_gamma_subst lgsE2 e); eauto.
Qed.    

Lemma lgamma_subst_split_subst' : forall E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst e,
  lgamma_subst_split E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst ->
  apply_gamma_subst lgsubst e = (apply_gamma_subst lgsubst2 (apply_gamma_subst lgsubst1 e)).
Proof.
  intros E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst e Hsplit.
  (lgamma_subst_split_cases (induction Hsplit) Case); intros; simpl; auto.
  Case "lgamma_subst_split_left".
    assert (J:=Hsplit).
    apply lgamma_subst_split__wf_lgamma_subst in J.
    assert (x `notin` dom lgsE3) as K.
      apply wf_lgamma_subst__nfv with (x:=x) in J; auto.
    erewrite <- swap_subst_ee_lgsubst with (e:=e); eauto.
    rewrite IHHsplit; auto.
    erewrite swap_subst_ee_lgsubst_right with (e:=apply_gamma_subst lgsE1 e); eauto.
    erewrite swap_subst_ee_lgsubst_left; eauto.
  Case "lgamma_subst_split_right".
    assert (J:=Hsplit).
    apply lgamma_subst_split__wf_lgamma_subst in J.
    assert (x `notin` dom lgsE3) as K.
      apply wf_lgamma_subst__nfv with (x:=x) in J; auto.
    erewrite <- swap_subst_ee_lgsubst with (e:=e); eauto.
    rewrite IHHsplit; auto.
    erewrite <- swap_subst_ee_lgsubst_right with (e:=apply_gamma_subst lgsE1 e); eauto.
Qed.    

Lemma swap_subst_ee_dsubst: forall e' x E dsubst e t,
  wf_delta_subst E dsubst ->
  typing nil nil e' t ->
  x `notin` dom dsubst ->
  subst_ee x e' (apply_delta_subst dsubst e) =
  apply_delta_subst dsubst (subst_ee x e' e).
Proof.
  intros e' x E dsubst e t Hwfd Hwft xndsubst.
  generalize dependent e.
  generalize dependent e'.
  generalize dependent t.
  induction Hwfd; intros t e' Hwft e0; simpl; eauto.
    rewrite <- subst_te_ee_commute; eauto.
      eauto using notin_fv_te_typing.
Qed.

Lemma swap_subst_te_dsubst: forall t X E dsubst e K,
  wf_delta_subst E dsubst ->
  wf_typ nil t K ->
  X `notin` dom dsubst ->
  subst_te X t (apply_delta_subst dsubst e) =
  apply_delta_subst dsubst (subst_te X t e).
Proof.
  intros t X E dsubst e K Hwfd Hwft xndsubst.
  generalize dependent e.
  generalize dependent t.
  induction Hwfd; intros t Hwft e0; simpl; eauto.
    rewrite subst_te_commute; eauto.
      eauto using notin_fv_wf.
      eauto using notin_fv_wf.
Qed.

Lemma wf_lgamma_subst_shuffle : forall E lE dsubst gsubst lgsubst e,
  wf_lgamma_subst E lE dsubst gsubst lgsubst ->
  apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)) =
  apply_gamma_subst lgsubst (apply_delta_subst dsubst (apply_gamma_subst gsubst e)).
Proof.
  intros E lE dsubst gsubst lgsubst e Hwflg.
  induction Hwflg; intros; simpl; auto.
  Case "wf_lgamma_subst_sval".
    assert (J:=Hwflg).
    assert (x `notin` dom gsE `union` dom dsE) as K.
      apply wf_lgamma_subst__nfv with (x:=x) in J; auto.
    apply wf_lgamma_subst__wf_subst in J.
    destruct J as [J1 J2].
    erewrite <- swap_subst_ee_gsubst with (e:=e); eauto.
    erewrite <- swap_subst_ee_dsubst; eauto.
    erewrite <- swap_subst_ee_gsubst; eauto.
    erewrite <- swap_subst_ee_dsubst; eauto.
    rewrite IHHwflg.
    erewrite swap_subst_ee_lgsubst; eauto.
      apply wf_lgamma_subst__nfv with (x:=x) in Hwflg; auto.
  Case "wf_lgamma_subst_slval".
    assert (J:=Hwflg).
    assert (x `notin` dom gsE `union` dom dsE) as K.
      apply wf_lgamma_subst__nfv with (x:=x) in J; auto.
    apply wf_lgamma_subst__wf_subst in J.
    destruct J as [J1 J2].
    assert (x `notin` dom lgsE) as K'.
      apply wf_lgamma_subst__nfv with (x:=x) in Hwflg; auto.
    erewrite <- swap_subst_ee_lgsubst with (e:=e); eauto.
    erewrite <- swap_subst_ee_gsubst; eauto.
    erewrite <- swap_subst_ee_dsubst; eauto.
    erewrite <- swap_subst_ee_lgsubst; eauto.
    rewrite IHHwflg. auto.
  Case "wf_lgamma_subst_skind".
    assert (J:=Hwflg).
    assert (X `notin` dom gsE `union` dom dsE) as K.
      apply wf_lgamma_subst__nfv with (x:=X) in J; auto.
    apply wf_lgamma_subst__wf_subst in J.
    destruct J as [J1 J2].
    assert (X `notin` dom lgsE) as K'.
      apply wf_lgamma_subst__nfv with (x:=X) in Hwflg; auto.
    erewrite <- swap_subst_te_dsubst; eauto.
    rewrite IHHwflg.
    erewrite swap_subst_te_lgsubst; eauto.
    erewrite swap_subst_te_dsubst; eauto.
Qed.

Lemma lgamma_subst_split_shuffle1 : forall E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst e,
  lgamma_subst_split E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst ->
  apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst1 e)) =
  apply_gamma_subst lgsubst1 (apply_delta_subst dsubst (apply_gamma_subst gsubst e)).
Proof.
  intros E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst e Hsplit.
  induction Hsplit; intros; simpl; auto.
  Case "lgamma_subst_split_left".
    assert (J:=Hsplit).
    apply lgamma_subst_split__wf_lgamma_subst in J.
    assert (JJ:=J).
    apply wf_lgamma_subst__wf_subst in JJ.
    destruct JJ as [J1 J2].
    assert (K:=J).
    apply wf_lgamma_subst__nfv with (x:=x) in K; auto.
    erewrite <- swap_subst_ee_lgsubst_left with (e:=e); eauto.
    erewrite <- swap_subst_ee_gsubst; eauto.
    erewrite <- swap_subst_ee_dsubst; eauto.
    rewrite IHHsplit.
    erewrite swap_subst_ee_dsubst; eauto.
    erewrite swap_subst_ee_lgsubst_left; eauto.
    erewrite swap_subst_ee_dsubst; eauto.
Qed.

Lemma lgamma_subst_split_shuffle2 : forall E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst e,
  lgamma_subst_split E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst ->
  apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst2 e)) =
  apply_gamma_subst lgsubst2 (apply_delta_subst dsubst (apply_gamma_subst gsubst e)).
Proof.
  intros E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst e Hsplit.
  induction Hsplit; intros; simpl; auto.
  Case "lgamma_subst_split_right".
    assert (J:=Hsplit).
    apply lgamma_subst_split__wf_lgamma_subst in J.
    assert (JJ:=J).
    apply wf_lgamma_subst__wf_subst in JJ.
    destruct JJ as [J1 J2].
    assert (K:=J).
    apply wf_lgamma_subst__nfv with (x:=x) in K; auto.
    erewrite <- swap_subst_ee_lgsubst_right with (e:=e); eauto.
    erewrite <- swap_subst_ee_gsubst; eauto.
    erewrite <- swap_subst_ee_dsubst; eauto.
    rewrite IHHsplit.
    erewrite swap_subst_ee_dsubst; eauto.
    erewrite swap_subst_ee_lgsubst_right; eauto.
    erewrite swap_subst_ee_dsubst; eauto.
Qed.

Lemma wf_lgamma_subst_split : forall E lE dsubst gsubst lgsubst lE1 lE2 E',
  wf_lgamma_subst E lE dsubst gsubst lgsubst ->
  lenv_split (E'++E) lE1 lE2 lE ->
  exists lgsubst1, exists lgsubst2,
    lgamma_subst_split E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst /\
    wf_lgamma_subst E lE1 dsubst gsubst lgsubst1 /\
    wf_lgamma_subst E lE2 dsubst gsubst lgsubst2.
Proof.
  intros E lE dsubst gsubst lgsubst lE1 lE2 E' Hwflg Hsplit.
  generalize dependent lE1. generalize dependent lE2. generalize dependent E'.
  (wf_lgamma_subst_cases (induction Hwflg) Case); intros.
  Case "wf_lgamma_subst_empty".
    exists gamma_nil. exists gamma_nil.
    inversion Hsplit; subst.
    repeat (split; auto).
  Case "wf_lgamma_subst_sval".
    assert (J:=Hsplit).
    rewrite_env ((E'++[(x, bind_typ T)])++E) in Hsplit.
    apply IHHwflg in Hsplit. clear IHHwflg.
    destruct Hsplit as [lgsubst1 [lgsubst2 [J1 [J2 J3]]]].
    exists lgsubst1. exists lgsubst2.
    split.
      apply lgamma_subst_split_nonlin_weakening_tail; auto.
    split.
      apply wf_lgamma_subst_sval; auto.
        apply dom_lenv_split in J.
        rewrite J in H0; auto.  
      apply wf_lgamma_subst_sval; auto.
        apply dom_lenv_split in J.
        rewrite J in H0; auto.
  Case "wf_lgamma_subst_slval".
    inversion Hsplit; subst.
    SCase "lenv_split_left".
      assert (J:=H6).
      apply IHHwflg in H6. clear IHHwflg.
      destruct H6 as [lgsubst1 [lgsubst2 [J1 [J2 J3]]]].
      exists ([(x,e)]++lgsubst1). exists lgsubst2. 
      split.
        apply lgamma_subst_split_left; auto.
      split; auto.
        apply wf_lgamma_subst_slval; auto.
          apply dom_lenv_split in J.
          rewrite J in H0; auto.
    SCase "lenv_split_right".
      assert (J:=H6).
      apply IHHwflg in H6. clear IHHwflg.
      destruct H6 as [lgsubst1 [lgsubst2 [J1 [J2 J3]]]].
      exists lgsubst1. exists ([(x,e)]++lgsubst2).
      split.
        apply lgamma_subst_split_right; auto.
      split; auto.
        apply wf_lgamma_subst_slval; auto.
          apply dom_lenv_split in J.
          rewrite J in H0; auto.
  Case "wf_lgamma_subst_skind".
    assert (J:=Hsplit).
    assert (K:=Hwflg).
    apply wf_lgamma_subst__nfv with (x:=X) in K; auto. 
    rewrite_env ((E'++[(X, bind_kn k)])++E) in Hsplit.
    apply IHHwflg in Hsplit. clear IHHwflg.
    destruct Hsplit as [lgsubst1 [lgsubst2 [J1 [J2 J3]]]].
    exists lgsubst1. exists lgsubst2.
    split.
      apply lgamma_subst_split_nonlin_weakening_typ_tail; auto.
    split.
      apply wf_lgamma_subst_skind; auto.
        apply dom_lenv_split in J.
        rewrite J in H0; auto.
      apply wf_lgamma_subst_skind; auto.
        apply dom_lenv_split in J.
        rewrite J in H0; auto.
Qed.

Lemma wf_lgamma_subst__fv : forall E D dsubst gsubst lgsubst x,
  wf_lgamma_subst E D dsubst gsubst lgsubst ->
  x `in` dom lgsubst ->
  x `in` dom D.
Proof.
  intros E D dsubst gsubst lgsubst x H1 H2.
  (wf_lgamma_subst_cases (induction H1) Case); intros; simpl; auto.
  Case "wf_lgamma_subst_slval".
    rewrite dom_app in H2. 
    assert (x `in` dom [(x0, e)] \/ x `in` dom lgsE) as J. fsetdec.
    destruct J as [J | J]; simpl in J; fsetdec.
Qed.    

(* ********************)
(*** closed after subst *)
Lemma wft_subst_closed : forall E E' t K dsubst,
  wf_delta_subst E dsubst ->
  wf_typ (E'++E) t K ->
  wf_env (E'++E) ->
  wf_env (apply_delta_subst_env dsubst E') ->
  wf_typ (apply_delta_subst_env dsubst E') (apply_delta_subst_typ dsubst t) K.
Proof.
  intros E E' t K dsubst Hwfd Hwft Hwfe Hwfe'.
  remember (E'++E) as EE.
  generalize dependent E'.
  generalize dependent E.
  generalize dependent dsubst.
  (wf_typ_cases (induction Hwft) Case); intros; subst; simpl; eauto.
  Case "wf_typ_var".
     analyze_binds H0.
       assert (X `notin` dom E0).
         eauto using fresh_app_r.
       apply wf_delta_subst__nfv with (dsubst:=dsubst) (X:=X) in Hwfd; auto.
       rewrite apply_delta_subst_typ_nfv; auto.
       apply wf_typ_var; auto.
         apply delta_subst_binds_kind with (dsubst:=dsubst); auto.

       assert (uniq dsubst).
         apply wf_delta_subst__uniq in Hwfd. decompose [and] Hwfd. auto.
       apply bindsdE__bindsT with (X:=X)(K:=K) in Hwfd; auto.
       destruct Hwfd as [T Hwfd]. destruct Hwfd as [J1 J2].
       assert (apply_delta_subst_typ dsubst (typ_fvar X) = T).
         apply delta_subst_var with (T:=T)(K:=K); auto.
       rewrite H1.
       apply wf_typ_weaken_head with (F:=apply_delta_subst_env dsubst E') in J2; simpl_env in *; auto.
  Case "wf_typ_arrow".
     rewrite commut_delta_subst_arrow.
     eapply wf_typ_arrow; eauto.
  Case "wf_typ_all".
     rewrite commut_delta_subst_all.
     apply wf_typ_all with (L:=L `union` dom dsubst  `union` dom (E'++E0) `union` dom (apply_delta_subst_env dsubst E')).
       intros.
       assert (X `notin` L). auto.
       apply H0 with (dsubst:=dsubst) (E'0:=[(X,bind_kn K1)]++E') (E:=E0) in H2; simpl; simpl_env; eauto.
         rewrite commut_delta_subst_open_tt with (dE:=E0) in H2; auto.
         simpl in H2. simpl_env in *.
         rewrite apply_delta_subst_typ_nfv in H2; auto.
  Case "wf_typ_with".
     rewrite commut_delta_subst_with.
     eapply wf_typ_with; eauto.
Qed.

Lemma wfle_subst_closed : forall E E' lE dsubst,
  wf_delta_subst E dsubst ->
  wf_lenv (E'++E) lE ->
  wf_env (apply_delta_subst_env dsubst E') ->
  wf_lenv (apply_delta_subst_env dsubst E') (apply_delta_subst_lenv dsubst lE).
Proof.
  intros E E' lE dsubst Hwfd Hwfle Hwfe.  
  remember (E'++E) as EE.
  generalize dependent E'.
  generalize dependent E.
  generalize dependent dsubst.
  (wf_lenv_cases (induction Hwfle) Case); 
    intros; subst; simpl; simpl_env; eauto.
  Case "wf_lenv_typ".
    apply wf_lenv_typ; eauto.
      rewrite <- apply_delta_subst_env_dom; auto.
      rewrite <- apply_delta_subst_lenv_dom; auto.
      eapply wft_subst_closed; eauto.
Qed.

Lemma lenv_split_subst_closed : forall E E' lE1 lE2 lE dsubst,
  wf_delta_subst E dsubst ->
  lenv_split (E'++E) lE1 lE2 lE ->
  wf_env (apply_delta_subst_env dsubst E') ->
  lenv_split (apply_delta_subst_env dsubst E') (apply_delta_subst_lenv dsubst lE1) (apply_delta_subst_lenv dsubst lE2) (apply_delta_subst_lenv dsubst lE).
Proof.
  intros E E' lE1 lE2 lE dsubst Hwfd Hsplit Hwfe.  
  remember (E'++E) as EE.
  generalize dependent E'.
  generalize dependent E.
  generalize dependent dsubst.
  (lenv_split_cases (induction Hsplit) Case); 
    intros; subst; simpl; simpl_env; eauto.
  Case "lenv_split_left".
    apply lenv_split_left; eauto.
      rewrite <- apply_delta_subst_env_dom; auto.
      rewrite <- apply_delta_subst_lenv_dom; auto.
      eapply wft_subst_closed; eauto.
        apply wf_lenv_split in Hsplit; auto.
  Case "lenv_split_right".
    apply lenv_split_right; eauto.
      rewrite <- apply_delta_subst_env_dom; auto.
      rewrite <- apply_delta_subst_lenv_dom; auto.
      eapply wft_subst_closed; eauto.
        apply wf_lenv_split in Hsplit; auto.
Qed.

Lemma typing_subst_closed : forall E E' D D' e t dsubst gsubst lgsubst,
  wf_lgamma_subst E D dsubst gsubst lgsubst ->
  typing (E'++E) (D'++D) e t ->
  wf_lenv (apply_delta_subst_env dsubst E') (apply_delta_subst_lenv dsubst D') ->
  typing (apply_delta_subst_env dsubst E') (apply_delta_subst_lenv dsubst D') 
         (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e))) 
         (apply_delta_subst_typ dsubst t).
Proof.
  intros.
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
  (typing_cases (induction H0) Case); intros; subst; simpl; simpl_commut_subst; auto.
  Case "typing_var".
     apply app_nil_inv in HeqDD.
     destruct HeqDD; subst.
     analyze_binds H0.
       assert (x `notin` dom E0) as J.
         eauto using fresh_app_r.
       apply delta_subst_binds_typ with (dsubst:=dsubst) in BindsTac.
       apply wf_lgamma_subst__nfv with (E:=E0) (dsubst:=dsubst) (gsubst:=gsubst) (x:=x) in H2; auto.
       decompose [and] H2. clear H2.
       rewrite apply_gamma_subst_nfv; auto.
       rewrite apply_gamma_subst_nfv; auto.
       rewrite apply_delta_subst_nfv; auto.

       assert (uniq gsubst).
         apply wf_lgamma_subst__uniq in H2. decompose [and] H2; auto.
       apply bindsgE__bindsE with (x:=x) (t:=T) in H2; auto.
       destruct H2 as [J [e H2]]. destruct H2.
       rewrite apply_gamma_subst_nfv; auto.
       assert (apply_gamma_subst gsubst (exp_fvar x) = e).
         apply gamma_subst_var with (t:=apply_delta_subst_typ dsubst T); auto.  
       rewrite H4.
       rewrite delta_subst_closed_exp with (t:=apply_delta_subst_typ dsubst T); auto.
       apply typing_weakening with (F:=apply_delta_subst_env dsubst E') (E:=@nil (atom*binding)) (G:=@nil (atom*binding)) in H3; simpl_env in *; auto.
  Case "typing_lvar".
     rewrite_env ([(x, lbind_typ T)] ++ nil) in HeqDD.
     apply one_eq_app in HeqDD.
     destruct HeqDD as [[D'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
       SCase "x in D', D=nil".
       apply app_nil_inv in EQ2.
       destruct EQ2; subst.
       assert (x `notin` dom lempty) as J. auto.
       assert (x `notin` dom (E'++E0)) as J'.
         inversion H; auto.
       apply wf_lgamma_subst__nfv with (E:=E0) (dsubst:=dsubst) (gsubst:=gsubst) (x:=x) in H0; auto.
       decompose [and] H0. clear H0.
       rewrite apply_gamma_subst_nfv; auto.
       rewrite apply_gamma_subst_nfv; auto.
       rewrite apply_delta_subst_nfv; auto.
       apply typing_lvar; auto.

       SCase "x in D, D'=nil".
       assert (uniq lgsubst).
         apply wf_lgamma_subst__uniq in H0. decompose [and] H0; auto.
       assert (binds x (lbind_typ T) ((x, lbind_typ T) :: lempty)) as K.
         simpl_env. apply binds_one_3; auto.
       apply lbindsgE__bindslE with (x:=x) (t:=T) in H0; auto.
       destruct H0 as [J [e H0]]. destruct H0.
       assert (apply_gamma_subst lgsubst (exp_fvar x) = e).
         apply gamma_subst_var with (t:=apply_delta_subst_typ dsubst T); auto.  
       rewrite H4.
       rewrite gamma_subst_closed_exp with (t:=apply_delta_subst_typ dsubst T); auto.
       rewrite delta_subst_closed_exp with (t:=apply_delta_subst_typ dsubst T); auto.
       apply typing_weakening with (F:=apply_delta_subst_env dsubst E') (E:=@nil (atom*binding)) (G:=@nil (atom*binding)) in H3; simpl_env in *; auto.
  Case "typing_abs".
     assert (wf_typ (apply_delta_subst_env dsubst E') (apply_delta_subst_typ dsubst T1) kn_nonlin) as Wft.
       apply wft_subst_closed with (E:=E0) ; auto.
         apply wf_lgamma_subst__wf_subst in H4.
         destruct H4; auto. 
     assert (wf_gamma_subst E0 dsubst gsubst) as Wfg.
       apply wf_lgamma_subst__wf_subst in H4.
       decompose [and] H4; auto.
     assert (wf_delta_subst E0 dsubst) as Wfd.
       apply wf_lgamma_subst__wf_subst in H4.
       decompose [and] H4; auto.
     apply typing_abs with (L:=L `union` dom gsubst `union` dom lgsubst  
                                 `union` dom dsubst `union` dom (apply_delta_subst_env dsubst E')
                                 `union` dom (apply_delta_subst_lenv dsubst D') `union` dom (E'++E0)); auto.
       intros.
       assert (x `notin` L) as FrxL. auto.
       apply H1 with (E:=E0) (gsubst:=gsubst) (dsubst:=dsubst) (E'0:=[(x, bind_typ T1)]++E') (D'0:=D') (D:=D0) (lgsubst:=lgsubst) in FrxL; clear H1;auto.
         rewrite commut_lgamma_subst_open_ee with (E:=E0) (dsubst:=dsubst) (D:=D0) (gsubst:=gsubst) in FrxL; auto.
         rewrite commut_gamma_subst_open_ee with (E:=E0) (dsubst:=dsubst) (D:=D0) (lgsubst:=lgsubst) in FrxL; auto.
         rewrite commut_delta_subst_open_ee with (dE:=E0) in FrxL; auto.
         simpl in FrxL. simpl_env in *.
         rewrite apply_gamma_subst_nfv in FrxL; auto.
         rewrite apply_gamma_subst_nfv in FrxL; auto.
         rewrite apply_delta_subst_nfv in FrxL; auto.

         simpl. rewrite_env (nil++[(x, bind_typ (apply_delta_subst_typ dsubst T1))]++apply_delta_subst_env dsubst E').
         apply wf_lenv_weakening; auto.
           simpl_env. apply wf_env_typ; auto.

       intros J.
       apply H2 in J.
       apply sym_eq in J.
       apply app_nil_inv in J.
       destruct J; subst; auto.
  Case "typing_labs".
     assert (wf_typ (apply_delta_subst_env dsubst E') (apply_delta_subst_typ dsubst T1) kn_lin) as Wft.
       apply wft_subst_closed with (E:=E0) ; auto.
         apply wf_lgamma_subst__wf_subst in H4.
         destruct H4; auto. 
     assert (wf_gamma_subst E0 dsubst gsubst) as Wfg.
       apply wf_lgamma_subst__wf_subst in H4.
       decompose [and] H4; auto.
     assert (wf_delta_subst E0 dsubst) as Wfd.
       apply wf_lgamma_subst__wf_subst in H4.
       decompose [and] H4; auto.
     apply typing_labs with (L:=L `union` dom gsubst `union` dom lgsubst  
                                 `union` dom dsubst `union` dom (apply_delta_subst_env dsubst E')
                                 `union` dom (apply_delta_subst_lenv dsubst D') `union` dom (E'++E0)); auto.
       intros.
       assert (x `notin` L) as FrxL. auto.
       apply H1 with (E:=E0) (gsubst:=gsubst) (dsubst:=dsubst) (E'0:=E') (D'0:=[(x, lbind_typ T1)]++D') (D:=D0) (lgsubst:=lgsubst) in FrxL; clear H1;auto.
         rewrite commut_lgamma_subst_open_ee with (E:=E0) (dsubst:=dsubst) (D:=D0) (gsubst:=gsubst) in FrxL; auto.
         rewrite commut_gamma_subst_open_ee with (E:=E0) (dsubst:=dsubst) (D:=D0) (lgsubst:=lgsubst) in FrxL; auto.
         rewrite commut_delta_subst_open_ee with (dE:=E0) in FrxL; auto.
         simpl in FrxL. simpl_env in *.
         rewrite apply_gamma_subst_nfv in FrxL; auto.
         rewrite apply_gamma_subst_nfv in FrxL; auto.
         rewrite apply_delta_subst_nfv in FrxL; auto.

         simpl. rewrite_env (nil++[(x, lbind_typ (apply_delta_subst_typ dsubst T1))]++apply_delta_subst_lenv dsubst D').
         apply wf_lenv_lin_weakening; auto.

       intros J.
       apply H2 in J.
       apply sym_eq in J.
       apply app_nil_inv in J.
       destruct J; subst; auto.
  Case "typing_app".
     assert (HH:=H).
     apply lenv_split_cases_app in H.
     destruct H as [D1L [D1R [D2L [D2R [Hsplit' [Hsplit [J1 J2]]]]]]]; subst.
     assert (J:=H0).
     apply wf_lgamma_subst_split with (lE1:=D1R) (lE2:=D2R) (E':=E') in H0; auto.
     destruct H0 as [lgsubst1 [lgsubst2 [Hgsplit [Hwflg1 Hwflg2]]]].
     assert (wf_lenv (E'++E0) D1L) as Wfe1.
       apply wf_lenv_split_left in Hsplit'; auto.
     assert (wf_lenv (E'++E0) D2L) as Wfe2.
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
       rewrite lgamma_subst_split_subst with (lgsubst1:=lgsubst1) (lgsubst2:=lgsubst2) (E:=E0) (lE:=D) (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst); auto.
       rewrite lgamma_subst_split_subst' with (lgsubst1:=lgsubst1) (lgsubst2:=lgsubst2) (E:=E0) (lE:=D) (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst); auto.

       assert (forall x, x `in` dom lgsubst2 -> x `notin` fv_ee e1) as FV1.
         intros x FV.
         apply wf_lgamma_subst__fv with (x:=x) in Hwflg2; auto.
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
         apply typing_fv with (x:=x) in H0_; auto.
       rewrite gamma_subst_disjoint_exp with (gsubst:=lgsubst2)(e:=e1); auto.
       assert (forall x, x `in` dom lgsubst1 -> x `notin` fv_ee e2) as FV2.
         intros x FV.
         apply wf_lgamma_subst__fv with (x:=x) in Hwflg1; auto.
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
         apply typing_fv with (x:=x) in H0_0; auto.
       rewrite gamma_subst_disjoint_exp with (gsubst:=lgsubst1)(e:=e2); auto.

     repeat(rewrite EQ). clear EQ.
     assert (wf_delta_subst E0 dsubst) as Wfd.
       apply wf_lgamma_subst__wf_subst in J.
       destruct J; auto.
     apply typing_app with (T1:=apply_delta_subst_typ dsubst T1) (K:=K)
                           (D1:=apply_delta_subst_lenv dsubst D1L)
                           (D2:=apply_delta_subst_lenv dsubst D2L).     
       rewrite <- commut_delta_subst_arrow.
       apply IHtyping1 with (E:=E0)(D:=D1R)(D':=D1L); auto.
         eapply wfle_subst_closed; eauto.
       apply IHtyping2 with (E:=E0)(D:=D2R)(D':=D2L); auto.
         eapply wfle_subst_closed; eauto.
       eapply lenv_split_subst_closed; eauto.

  Case "typing_tabs".
     assert (wf_gamma_subst E0 dsubst gsubst) as Wfg.
       apply wf_lgamma_subst__wf_subst in H3.
       decompose [and] H3; auto.
     assert (wf_delta_subst E0 dsubst) as Wfd.
       apply wf_lgamma_subst__wf_subst in H3.
       decompose [and] H3; auto.
     apply typing_tabs with (L:=L `union` dom gsubst `union` dom lgsubst  
                                 `union` dom dsubst `union` dom (apply_delta_subst_env dsubst E')
                                 `union` dom (apply_delta_subst_lenv dsubst D') `union` dom (E'++E0)); auto.
       intros.
       rewrite <- apply_delta_subst_typ_nfv with (dsubst:=dsubst); auto.
       rewrite <- apply_gamma_subst_typ_nfv with (gsubst:=gsubst); auto.
       rewrite <- apply_gamma_subst_typ_nfv with (gsubst:=lgsubst); auto.
       rewrite <- commut_delta_subst_open_te with (dE:=E0); auto.
       rewrite <- commut_gamma_subst_open_te with (E:=E0) (D:=D0) (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst); auto.
       rewrite <- commut_lgamma_subst_open_te with (E:=E0) (D:=D0) (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst); auto.
       eapply delta_gamma_lgamma_subst_value; eauto.

       intros.
       assert (X `notin` L) as FrxL. auto.
       apply H1 with (D:=D0) (D'0:=D')(E:=E0)(gsubst:=gsubst)(lgsubst:=lgsubst)(dsubst:=dsubst)(E'0:=[(X,bind_kn K)]++E') in FrxL; clear H1; auto.
         rewrite commut_lgamma_subst_open_te with (E:=E0)(D:=D0)(gsubst:=gsubst)(dsubst:=dsubst) in FrxL; auto.
         rewrite commut_gamma_subst_open_te with (E:=E0) (D:=D0) (lgsubst:=lgsubst) (dsubst:=dsubst) in FrxL; auto.
         rewrite commut_delta_subst_open_te with (dE:=E0) in FrxL; auto.
         rewrite commut_delta_subst_open_tt with (dE:=E0) in FrxL; auto.
         simpl in FrxL. simpl_env in *.
         rewrite apply_delta_subst_typ_nfv in FrxL; auto.
         rewrite apply_gamma_subst_typ_nfv in FrxL; auto.
         rewrite apply_gamma_subst_typ_nfv in FrxL; auto.
         rewrite apply_delta_subst_typ_nfv in FrxL; auto.

         simpl. rewrite_env (nil++[(X, bind_kn K)]++apply_delta_subst_env dsubst E').
         apply wf_lenv_weakening; auto.
           simpl_env. apply wf_env_kn; auto.
  Case "typing_tapp".
     assert (wf_gamma_subst E0 dsubst gsubst) as Wfg.
       apply wf_lgamma_subst__wf_subst in H2.
       decompose [and] H2; auto.
     assert (wf_delta_subst E0 dsubst) as Wfd.
       apply wf_lgamma_subst__wf_subst in H2.
       decompose [and] H2; auto.
     rewrite commut_delta_subst_open_tt with (dE:=E0); auto.
     apply typing_tapp with (K:=K).
       rewrite <- commut_delta_subst_all.
       eapply IHtyping with (E:=E0) ; eauto.

       eapply wft_subst_closed with (E:=E0); eauto.
  Case "typing_apair".
     apply typing_apair; eauto.
  Case "typing_fst".
     apply typing_fst with (T2:=apply_delta_subst_typ dsubst T2).
       rewrite <- commut_delta_subst_with.
       eapply IHtyping with (E:=E0); eauto.
  Case "typing_snd".
     apply typing_snd with (T1:=apply_delta_subst_typ dsubst T1).
       rewrite <- commut_delta_subst_with.
       eapply IHtyping with (E:=E0); eauto.
Qed.

Lemma typing_subst : forall E D e t dsubst gsubst lgsubst,
  wf_lgamma_subst E D dsubst gsubst lgsubst ->
  typing E D e t ->
  typing nil nil (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e))) (apply_delta_subst_typ dsubst t).
Proof.
  intros E D e t dsubst gsubst lgsubst Wflg Typing.
  rewrite_env (nil ++ D) in Typing.
  rewrite_env (nil ++ E) in Typing.
  apply typing_subst_closed with (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst) in Typing; auto.
Qed.

Lemma wft_subst: forall t dsubst E K,
  wf_delta_subst E dsubst ->
  wf_typ E t K ->
  wf_typ nil (apply_delta_subst_typ dsubst t) K.
intros.
  apply wft_subst_closed with (E:=E) (E':=@nil (atom*binding)) (dsubst:=dsubst); auto.
    apply wf_delta_subst__uniq in H. decompose [and] H. auto.
Qed.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../../../metatheory" "-I" "../linf") ***
*** End: ***
 *)
