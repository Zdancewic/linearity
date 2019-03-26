(** Authors: Jianzhou Zhao. *)

Require Import LinF_Renaming.
Require Import LinF_Parametricity.
Require Import LinF_OParametricity_App.
Require Import LinF_ContextualEq_Infrastructure.
Require Import LinF_ContextualEq_Sound.
Require Import LinF_ContextualEq_Prop.

Export Parametricity.

(*  Substitutee on Gamma, map from exp vars to exprs(closed) *)

Inductive wfv_gamma_subst : env -> delta_subst -> gamma_subst -> Prop :=
  | wfv_gamma_subst_empty :
      wfv_gamma_subst nil delta_nil gamma_nil
  | wfv_gamma_subst_sval : forall x e T E dsE gsE,
      wfv_gamma_subst E dsE gsE -> x `notin` dom E ->
      typing nil nil e (apply_delta_subst_typ dsE T) -> 
      value e ->
      wf_typ E T kn_nonlin ->
      wfv_gamma_subst ([(x, bind_typ T)] ++ E) dsE ([(x, e)]++gsE)
  | wfv_gamma_subst_skind : forall X T E dsE gsE k,
      wfv_gamma_subst E dsE gsE -> X `notin` dom E ->
      wf_typ nil T k ->
      wfv_gamma_subst ([(X, bind_kn k)]++E) ([(X, T)]++dsE) gsE
  .

Tactic Notation "wfv_gamma_subst_cases" tactic(first) tactic(c) :=
  first;
  [ c "wfv_gamma_subst_empty" |
    c "wfv_gamma_subst_sval" |
    c "wfv_gamma_subst_skind"].

(*  Substitutee on lin Context, map from exp vars to exprs(closed) *)

Inductive wfv_lgamma_subst : env -> lenv -> delta_subst -> gamma_subst -> gamma_subst -> Prop :=
  | wfv_lgamma_subst_empty : 
      wfv_lgamma_subst nil nil nil nil nil
  | wfv_lgamma_subst_sval : forall x e T E lE dsE gsE lgsE,
      wfv_lgamma_subst E lE dsE gsE lgsE -> 
      x `notin` dom E ->
      x `notin` dom lE ->
      typing nil nil e (apply_delta_subst_typ dsE T) -> 
      value e ->
      wf_typ E T kn_nonlin ->
      wfv_lgamma_subst ([(x, bind_typ T)] ++ E) lE dsE ([(x, e)]++gsE) lgsE
  | wfv_lgamma_subst_slval : forall x e T E lE dsE gsE lgsE,
      wfv_lgamma_subst E lE dsE gsE lgsE -> 
      x `notin` dom E ->
      x `notin` dom lE -> 
      typing nil nil e (apply_delta_subst_typ dsE T) -> 
      value e ->
      wf_typ E T kn_lin ->
      wfv_lgamma_subst E ([(x, lbind_typ T)] ++ lE) dsE gsE ([(x, e)]++lgsE)
  | wfv_lgamma_subst_skind : forall X T E lE dsE gsE lgsE k,
      wfv_lgamma_subst E lE dsE gsE lgsE -> 
      X `notin` dom E ->
      X `notin` dom lE ->
      wf_typ nil T k ->
      wfv_lgamma_subst ([(X, bind_kn k)]++E) lE ([(X, T)]++dsE) gsE lgsE
  .

Tactic Notation "wfv_lgamma_subst_cases" tactic(first) tactic(c) :=
  first;
  [ c "wfv_lgamma_subst_empty" |
    c "wfv_lgamma_subst_sval" |
    c "wfv_lgamma_subst_slval" |
    c "wfv_lgamma_subst_skind" ].

Definition F_ciu_eq E lE e e' t : Prop :=
  typing E lE e t /\
  typing E lE e' t /\
  forall dsubst gsubst lgsubst,
   wfv_lgamma_subst E lE dsubst gsubst lgsubst ->
   F_vobservational_eq nil nil 
     (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)))
     (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e')))
     (apply_delta_subst_typ dsubst t).

Fixpoint gen_ctx_labs (lE:lenv) (C:ctx) {struct lE} : ctx :=
  match lE with
  | nil => C
  | (x, lbind_typ T)::lE' => ctx_abs_capture kn_lin x T (close_ec (gen_ctx_labs lE' C) x)
  end.

Fixpoint gen_typ_labs (lE:lenv) (t:typ) {struct lE} : typ :=
  match lE with
  | nil => t
  | (x, lbind_typ T)::lE' => typ_arrow kn_lin T (gen_typ_labs lE' t)
  end.

Fixpoint gen_ctx_abs_capture (E:env) (C:ctx) {struct E} : ctx :=
  match E with
  | nil => C
  | (X, bind_kn K)::E' => (gen_ctx_abs_capture E' C)
  | (x, bind_typ T)::E' => ctx_abs_capture kn_lin x T (close_ec (gen_ctx_abs_capture E' C) x)
  end.

Fixpoint gen_typ_abs (E:env) (t:typ) {struct E} : typ :=
  match E with
  | nil => t
  | (X, bind_kn K)::E' => (gen_typ_abs E' t)
  | (x, bind_typ T)::E' => typ_arrow kn_lin T (gen_typ_abs E' t)
  end.

Definition gen_ctx_apair (C:ctx) := ctx_apair1 C tt.

Definition gen_typ_with (t:typ) := typ_with t Two.

Fixpoint gen_ctx_tabs_capture (E:env) (C:ctx) {struct E} : ctx :=
  match E with
  | nil => C
  | (X, bind_kn K)::E' => ctx_tabs_capture X K (close_tc (gen_ctx_tabs_capture E' C) X)
  | (x, bind_typ T)::E' => (gen_ctx_tabs_capture E' C)
  end.

Fixpoint gen_typ_tabs (E:env) (t:typ) {struct E} : typ :=
  match E with
  | nil => t
  | (X, bind_kn K)::E' => typ_all K (close_tt (gen_typ_tabs E' t) X)
  | (x, bind_typ T)::E' => (gen_typ_tabs E' t)
  end.

Fixpoint gen_ctx_tapp (dsubst:delta_subst) (C:ctx) {struct dsubst} : ctx :=
  match dsubst with
  | nil => C
  | (X, T)::dsubst' => ctx_tapp (gen_ctx_tapp dsubst' C) T
  end.

Fixpoint gen_typ_tapp (dsubst:delta_subst) (t:typ) {struct dsubst} : typ :=
  match dsubst with
  | nil => t
  | (X, T)::dsubst' => open_tt (gen_typ_tapp dsubst' t) T
  end.

Definition gen_ctx_fst (C:ctx) := ctx_fst C.

Fixpoint gen_ctx_app (gsubst:gamma_subst) (C:ctx) {struct gsubst} : ctx :=
  match gsubst with
  | nil => C
  | (x, v)::gsubst' => ctx_app1 (gen_ctx_app gsubst' C) v
  end.

Fixpoint gen_ctx_lapp (lgsubst:gamma_subst) (C:ctx) {struct lgsubst} : ctx :=
  match lgsubst with
  | nil => C
  | (x, v)::lgsubst' => ctx_app1 (gen_ctx_lapp lgsubst' C) v
  end.

Lemma wf_lgsubst_lcons_inv' : forall E x T D dsubst gsubst lgsubst,
  wf_lgamma_subst E ([(x, lbind_typ T)]++D) dsubst gsubst lgsubst ->
  exists e, exists lgsubst',
    lgsubst = [(x, e)] ++ lgsubst' /\
    dom D [=] dom lgsubst' /\
    wf_typ E T kn_lin /\
    typing nil nil e (apply_delta_subst_typ dsubst T) /\
    wf_lgamma_subst E D dsubst gsubst lgsubst'.
Proof.
  intros E x T D dsubst gsubst lgsubst Wflg.
  remember ([(x, lbind_typ T)]++D) as DD.
  generalize dependent D.        
  generalize dependent x.
  generalize dependent T.
  induction Wflg; intros; subst.
    inversion HeqDD.

    assert ([(x0, lbind_typ T0)]++D=[(x0, lbind_typ T0)]++D) as EQ. auto.
    apply IHWflg in EQ.
    destruct EQ as [e0 [lgsubst' [EQ1 [EQ2 [Wft [Typ Wflg']]]]]]; subst.
    exists e0. exists lgsubst'.
    split; auto.
    split; auto.
    split; auto.
      apply wf_typ_weaken_head; auto.
        apply wf_lgamma_subst__wf_lenv in Wflg.
        destruct Wflg; auto.        

    inversion HeqDD; subst. clear HeqDD.
    exists e. exists lgsE.
    split; auto.
    split; auto.
      apply dom_lgamma_subst in Wflg.
      decompose [and] Wflg; auto.

    assert ([(x, lbind_typ T0)]++D=[(x, lbind_typ T0)]++D) as EQ. auto.
    apply IHWflg in EQ.
    destruct EQ as [e [lgsubst' [EQ1 [EQ2 [Wft [Typ Wflg']]]]]]; subst.
    exists e. exists lgsubst'.
    split; auto.
    split; auto.
    split; auto.
      apply wf_typ_weaken_head; auto.
        apply wf_lgamma_subst__wf_lenv in Wflg.
        destruct Wflg; auto.              
    split; auto.
      simpl. simpl in H0.
      rewrite <- subst_tt_fresh; auto.
        apply notin_fv_wf with (X:=X) in Wft; auto.
Qed.

Lemma cv_ec_gen_ctx_labs_hole : forall lE,
  cv_ec (gen_ctx_labs lE ctx_hole) [=] dom lE.
Proof.
  induction lE; simpl; auto.
    destruct a.
    destruct l. simpl. 
    rewrite <- cv_ec_close_ec.
    rewrite IHlE. fsetdec.
Qed.

Lemma wf_lgsubst_kcons_inv' : forall E X K D dsubst gsubst lgsubst,
  wf_lgamma_subst ([(X, bind_kn K)]++E) D dsubst gsubst lgsubst ->
  X `notin` fv_lenv D ->
  exists T, exists dsubst', 
    dsubst = [(X, T)] ++ dsubst' /\
    ddom_env E [=] dom dsubst' /\
    wf_typ nil T K /\
    wf_lgamma_subst E D dsubst' gsubst lgsubst.
Proof.
  intros E X K D dsubst gsubst lgsubst Wflg XnD.
  remember ([(X, bind_kn K)]++E) as EE.
  generalize dependent E.        
  generalize dependent X.
  generalize dependent K.
  induction Wflg; intros; subst.
    inversion HeqEE.

    inversion HeqEE.

    assert ([(X, bind_kn K)]++E0=[(X, bind_kn K)]++E0) as EQ. auto.
    apply IHWflg in EQ.
    destruct EQ as [T0 [dsubst' [EQ1 [EQ2 [Wft Wflg']]]]]; subst.
    exists T0. exists dsubst'.
    split; auto.
    split; auto.
    split; auto.
      apply wf_lgamma_subst_slval; auto.
        simpl in H1.
        simpl_env in XnD.
        simpl in XnD.
        rewrite <- subst_tt_fresh in H1; auto.
        
        rewrite_env (nil ++ [(X, bind_kn K)] ++E0) in H2.
        simpl_env in XnD.
        simpl in XnD.
        apply wf_typ_strengthening_typ in H2; auto.

        simpl_env in XnD. auto.

    inversion HeqEE; subst.
    exists T. exists dsE.
    split; auto.
    split; auto.
      apply dom_lgamma_subst in Wflg.
      destruct Wflg as [J1 [J2 J3]]. assumption.
Qed.

Lemma wf_lgsubst_cons_inv' : forall E x T D dsubst gsubst lgsubst,
  wf_lgamma_subst ([(x, bind_typ T)]++E) D dsubst gsubst lgsubst ->
  exists e, exists gsubst', 
    gsubst = [(x, e)] ++ gsubst' /\
    gdom_env E [=] dom gsubst' /\
    wf_typ E T kn_nonlin /\
    typing  nil nil e (apply_delta_subst_typ dsubst T) /\
    wf_lgamma_subst E D dsubst gsubst' lgsubst.
Proof.
  intros E x T D dsubst gsubst lgsubst Wflg.
  remember ([(x, bind_typ T)]++E) as EE.
  generalize dependent E.        
  generalize dependent x.
  generalize dependent T.
  induction Wflg; intros; subst.
    inversion HeqEE.

    inversion HeqEE; subst. clear HeqEE.
    exists e. exists gsE.
    split; auto.
    split; auto.
      apply dom_lgamma_subst in Wflg.
      decompose [and] Wflg; auto.

    assert ([(x0, bind_typ T0)]++E0=[(x0, bind_typ T0)]++E0) as EQ. auto.
    apply IHWflg in EQ.
    destruct EQ as [e0 [gsubst' [EQ1 [EQ2 [Wft [Typ Wflg']]]]]]; subst.
    exists e0. exists gsubst'.
    split; auto.
    split; auto.
    split; auto.
    split; auto.
      apply wf_lgamma_subst_slval; auto.
        rewrite_env (nil ++ [(x0, bind_typ T0)] ++ E0) in H2.
        apply wf_typ_strengthening in H2; auto.
        apply wf_lgamma_subst__wf_lenv in Wflg.
        destruct Wflg; auto.        

    inversion HeqEE.
Qed.

Lemma dom_gamma_subst : forall E dsubst gsubst,
  wf_gamma_subst E dsubst gsubst -> 
  ddom_env E [=] dom dsubst /\
  gdom_env E [=] dom gsubst.
Proof.
  intros E dsubst gsubst Wfg.
  induction Wfg; simpl_env; simpl.
    split; auto.

    destruct IHWfg as [J1 J2].
    rewrite <- J1. rewrite <- J2.
    split; auto. fsetdec.
               clear. fsetdec.

    destruct IHWfg as [J1 J2].
    rewrite <- J1. rewrite <- J2.
    split; auto. fsetdec.
               clear. fsetdec.
Qed.

Lemma wf_gsubst_cons_inv' : forall E x T dsubst gsubst,
  wf_gamma_subst ([(x, bind_typ T)]++E) dsubst gsubst ->
  exists e, exists gsubst', 
    gsubst = [(x, e)] ++ gsubst' /\
    gdom_env E [=] dom gsubst' /\
    wf_typ E T kn_nonlin /\
    typing  nil nil e (apply_delta_subst_typ dsubst T) /\
    wf_gamma_subst E dsubst gsubst'.
Proof.
  intros E x T dsubst gsubst Wflg.
  remember ([(x, bind_typ T)]++E) as EE.
  generalize dependent E.        
  generalize dependent x.
  generalize dependent T.
  induction Wflg; intros; subst.
    inversion HeqEE.

    inversion HeqEE; subst. clear HeqEE.
    exists e. exists gsE.
    split; auto.
    split; auto.
      apply dom_gamma_subst in Wflg.
      decompose [and] Wflg; auto.

    inversion HeqEE.
Qed.

Lemma _from_subst_to_ctx_labs : forall lE E lE' t K,
  uniq lE ->
  wf_typ E t K ->
  wf_lenv E (lE'++lE) ->
  contexting E (lE'++lE) t (gen_ctx_labs lE ctx_hole) E lE' (gen_typ_labs lE t).
Proof.
  induction lE; intros E lE' t K Uniq Hwft Hwlenv.
    simpl_env in *. apply contexting_hole with (K:=K); auto.

    destruct a. destruct l. simpl_env in Uniq.
    assert (J:=Uniq).
    inversion J; subst.
    rewrite_env ((lE'++[(a, lbind_typ t0)])++lE) in Hwlenv.
    apply IHlE with (t:=t) (K:=K) in Hwlenv; auto.
      simpl.
      assert (contexting E (lE'++(a, lbind_typ t0)::lE) t (ctx_abs_capture kn_lin a t0 (close_ec (gen_ctx_labs lE ctx_hole) a)) E lE' (typ_arrow kn_lin t0 (gen_typ_labs lE t)) = 
                     contexting E (lE'++(a, lbind_typ t0)::lE) t (ctx_abs_capture kn_lin a t0 (close_ec (gen_ctx_labs lE ctx_hole) a)) E (lenv_remove (a, lbind_typ t0) (lE'++[(a, lbind_typ t0)]++nil)) (typ_arrow kn_lin t0 (gen_typ_labs lE t))) as EQ.
        rewrite lenv_remove_opt.
          simpl_env. auto.

          apply contexting_regular in Hwlenv.
          decompose [and] Hwlenv.
          clear - H5. apply uniq_from_wf_lenv in H5. simpl_env. auto.
      rewrite EQ. clear EQ.
      simpl_env. simpl_env in Hwlenv.
      apply contexting_labs_capture; auto.
        apply contexting_regular in Hwlenv.
        decompose [and] Hwlenv.
        clear - H5.
        apply wf_typ_from_lbinds_typ with (x:=a) (U:=t0) in H5; auto.

        rewrite cv_ec_gen_ctx_labs_hole. 
        apply contexting_regular in Hwlenv.
        decompose [and] Hwlenv.
        assert (a `notin` gdom_env E) as anE.
          apply dom__gdom.
          apply disjoint_wf_lenv in H2.
          clear - H2. solve_uniq.
        auto.
   
        intros JJ. inversion JJ.
Qed.

Lemma from_subst_to_ctx_labs : forall E lE t K,
  wf_lenv E lE ->
  wf_typ E t K ->
  contexting E lE t (gen_ctx_labs lE ctx_hole) E nil (gen_typ_labs lE t).
Proof.
  intros E lE t K Hwflenv Hwft.
  rewrite_env (nil++lE).
  apply  _from_subst_to_ctx_labs with (K:=K); auto.
    simpl_env. apply uniq_from_wf_lenv in Hwflenv; auto.
Qed.

Lemma cv_ec_gen_ctx_abs_capture : forall E C,
  cv_ec (gen_ctx_abs_capture E C) [=] gdom_env E `union` cv_ec C.
Proof.
  induction E; intro C; simpl.
    fsetdec.

    destruct a.
    destruct b; simpl. 
      rewrite IHE. fsetdec.

      rewrite <- cv_ec_close_ec.
      rewrite IHE. fsetdec.
Qed.

Lemma fv_ec_gen_ctx_labs_hole : forall lE,
  fv_ec (gen_ctx_labs lE ctx_hole) [=] {}.
Proof.
  induction lE; simpl; auto.
    destruct a.
    destruct l. simpl. 
    assert (J := @close_ec_fv_ec_upper (gen_ctx_labs lE ctx_hole) a).
    rewrite IHlE in J; auto.
    fsetdec.
Qed.

Lemma fv_ec_gen_ctx_abs_capture_hole : forall E C,
  fv_ec C [=] {} ->
  fv_ec (gen_ctx_abs_capture E C) [=] {}.
Proof.
  induction E; intros C Heq; simpl; auto.
    destruct a.
    destruct b; simpl.
       rewrite IHE; auto. 

      assert (J := @close_ec_fv_ec_upper (gen_ctx_abs_capture E C) a).
      rewrite IHE in J; auto.
      fsetdec.
Qed.

Lemma fv_ec_gen_ctx_tabs_capture_hole : forall E C,
  fv_ec C [=] {} ->
  fv_ec (gen_ctx_tabs_capture E C) [=] {}.
Proof.
  induction E; intros C Heq; simpl; auto.
    destruct a.
    destruct b; simpl.
      apply IHE in Heq.  rewrite <- fv_ec_close_tc. assumption.
      rewrite IHE; auto. 
Qed.

Lemma wf_typ_strengthening_remove_tmvar : forall E2 E1 E3 t K,
  wf_typ (E1++E2++E3) t K ->
  wf_typ (E1++remove_tmvar E2 ++ E3) t K.
Proof.
  induction E2; intros E1 E3 t K Wft; simpl.
    simpl_env in Wft; assumption.

     destruct a.
     destruct b; simpl_env in *.
       rewrite_env ((E1++[(a, bind_kn k)])++E2++E3) in Wft.
       apply IHE2 in Wft.
       simpl_env in Wft; auto.
       
       apply wf_typ_strengthening in Wft.
       apply IHE2 in Wft; auto.
Qed.

Lemma _from_subst_to_ctx_abs_capture : forall E E' lE t t' C,
  uniq E ->
  fv_ec C [=] {} ->
  cv_ec C [=] dom lE ->
  contexting (E'++E) lE t C (E'++E) nil t' ->
  contexting (E'++E) lE t (gen_ctx_abs_capture E C) (E'++remove_tmvar E) nil (gen_typ_abs E t').
Proof.
  induction E; intros E' lE t t' C Uniq Hfvc Hcvc Hctx.
    simpl. simpl_env in *. auto.

    destruct a. destruct b; simpl.
      simpl_env in *.
      assert (J:=Uniq).
      rewrite_env ((E'++[(a, bind_kn k)])++E) in Hctx.   
      inversion J; subst.
      apply IHE in Hctx; simpl_env; auto.
        simpl_env in Hctx. auto.

      simpl_env in *.
      assert (J:=Uniq).
      inversion J; subst.
      rewrite_env ((E'++[(a, bind_typ t0)])++E) in Hctx.
      apply IHE in Hctx; simpl_env; auto.
        simpl_env in Hctx.
        assert (contexting (E'++[(a, bind_typ t0)]++E) lE t (ctx_abs_capture kn_lin a t0 (close_ec (gen_ctx_abs_capture E C) a)) (E'++remove_tmvar E) nil (typ_arrow kn_lin t0 (gen_typ_abs E t')) = 
                     contexting (E'++[(a, bind_typ t0)]++E) lE t (ctx_abs_capture kn_lin a t0 (close_ec (gen_ctx_abs_capture E C) a)) (env_remove (a, bind_typ t0) (E'++[(a, bind_typ t0)]++remove_tmvar E)) nil (typ_arrow kn_lin t0 (gen_typ_abs E t'))) as EQ.
          rewrite env_remove_opt.
            simpl_env. auto.

            apply contexting_regular in Hctx.
            decompose [and] Hctx.
            apply uniq_from_wf_env in H4. assumption.
        rewrite EQ. clear EQ.
        apply contexting_abs_capture; auto.
          rewrite env_remove_opt.
            apply contexting_regular in Hctx.
            decompose [and] Hctx.
            apply wf_typ_from_binds_typ with (x:=a) (U:=t0) in H; auto.
            apply wf_typ_strengthening in H.      
            rewrite_env (E'++E++nil) in H.
            apply wf_typ_strengthening_remove_tmvar in H.
            simpl_env in H; assumption.

            apply contexting_regular in Hctx.
            decompose [and] Hctx.
            apply uniq_from_wf_env in H4. assumption.

          rewrite cv_ec_gen_ctx_abs_capture; auto.
            apply contexting_regular in Hctx.
            decompose [and] Hctx.
            assert (a `notin` gdom_env E) as anE.
              apply dom__gdom.
              apply uniq_from_wf_env in H.
              clear - H. solve_uniq.
            assert (a `notin` dom lE) as anlE.
              clear - H2. apply disjoint_wf_lenv in H2. solve_uniq.
            assert (a `notin` cv_ec C) as anC.
              rewrite Hcvc. auto.
            auto.
Qed.

Lemma from_subst_to_ctx_abs_capture : forall E lE t t' C,
  uniq E ->
  fv_ec C [=] {} ->
  cv_ec C [=] dom lE ->
  contexting E lE t C E nil t' ->
  contexting E lE t (gen_ctx_abs_capture E C) (remove_tmvar E) nil (gen_typ_abs E t').
Proof.
  intros E lE t t' C Hwflg Hfvc Hcvc Hctx.
  rewrite_env (nil++E).
  rewrite_env (nil++remove_tmvar E).
  apply  _from_subst_to_ctx_abs_capture; auto.
Qed.

Lemma wf_dsubst_kcons_inv' : forall E X K dsubst,
  wf_delta_subst ([(X, bind_kn K)]++E) dsubst ->
  exists T, exists dsubst', 
    dsubst = [(X, T)] ++ dsubst' /\
    ddom_env E [=] dom dsubst' /\
    wf_typ nil T K /\
    wf_delta_subst E dsubst'.
Proof.
  intros E X K dsubst Wfd.
  remember ([(X, bind_kn K)]++E) as EE.
  generalize dependent E.        
  generalize dependent X.
  generalize dependent K.
  induction Wfd; intros; subst.
    inversion HeqEE.

    inversion HeqEE; subst.
    exists T. exists SE. 
    split; auto.
    split; auto.
      apply dom_delta_subst in Wfd.
      assumption.

    inversion HeqEE.
Qed.

Lemma remove_tmvar_app : forall E E',
  remove_tmvar (E ++ E') = remove_tmvar E ++ remove_tmvar E'.
Proof.
  induction E; intros E'; simpl; auto.
    destruct a.
    destruct b; auto.
      rewrite IHE. auto.
Qed.

Lemma fv_tc_gen_ctx_labs_hole : forall lE,
  fv_tc (gen_ctx_labs lE ctx_hole) [=] ftv_lenv lE.
Proof.
  induction lE; simpl; auto.
    destruct a.
    destruct l. simpl. 
    rewrite <- fv_tc_close_ec. rewrite IHlE.  fsetdec.
Qed.

Lemma fv_tc_gen_ctx_abs_capture_hole : forall E C,
  fv_tc (gen_ctx_abs_capture E C) [=] ftv_env E `union` fv_tc C.
Proof.
  induction E; intros C; simpl.
    fsetdec.

    destruct a.
    destruct b; simpl.
      rewrite IHE.  fsetdec.
      rewrite <- fv_tc_close_ec. rewrite IHE.  fsetdec.
Qed.

Lemma cv_tc_gen_ctx_labs : forall lE,
  cv_tc (gen_ctx_labs lE ctx_hole) [=] {}.
Proof.
  induction lE; simpl.
    fsetdec.

    destruct a.
    destruct l; simpl. 
    rewrite <- cv_tc_close_ec. rewrite IHlE; auto. 
Qed.

Lemma cv_tc_gen_ctx_abs_capture : forall E C,
  cv_tc C [=] {} ->
  cv_tc (gen_ctx_abs_capture E C) [=] {}.
Proof.
  induction E; intros C Heq; simpl.
    fsetdec.

    destruct a.
    destruct b; simpl. 
      rewrite IHE; auto. 
      rewrite <- cv_tc_close_ec. rewrite IHE; auto. 
Qed.

Lemma cv_tc_gen_ctx_tabs_capture : forall E C,
  cv_tc (gen_ctx_tabs_capture E C) [=] ddom_env E `union` cv_tc C.
Proof.
  induction E; intros C; simpl.
    fsetdec.

    destruct a.
    destruct b; simpl. 
      assert (J:=@IHE C).
      assert (J':=@cv_tc_close_tc (gen_ctx_tabs_capture E C) a).
      rewrite J in J'.
      rewrite <- J'. fsetdec.

      rewrite IHE. fsetdec.
Qed.

Lemma wfe_remove_tmvar : forall E,
  wf_env E ->
  wf_env (remove_tmvar E).
Proof.
  induction E; intro Wfe; simpl; auto.
     destruct a.
     destruct b; simpl_env in *.
       inversion Wfe; subst.       
       apply notin_remove_tmvar_dom in H3.
       apply IHE in H1; auto.
       
       inversion Wfe; subst.       
       apply notin_remove_tmvar_dom in H4.
       apply IHE in H2; auto.
Qed.

Lemma wf_env_strengthening_nilgdom : forall E2 E1 E3,
  wf_env (E1++E2++E3) ->
  gdom_env E1 [=] {} ->
  wf_env (E1++E3).
Proof.
  induction E2; intros E1 E3 Wfe Gdom; simpl.
     simpl_env in Wfe; assumption.

     destruct a.
     destruct b; simpl_env in *.
       rewrite_env ((E1++[(a, bind_kn k)])++E2++E3) in Wfe.
       apply IHE2 in Wfe.          
         simpl_env in Wfe.
         apply wf_env_strengthening_typ in Wfe; auto.
           rewrite fv_env_is_ddom_env; auto.
           apply uniq_from_wf_env in Wfe.
           apply dom__ddom.
           clear - Wfe. solve_uniq.

           simpl_env. rewrite Gdom. simpl. fsetdec.
       
       apply wf_env_strengthening in Wfe.
       apply IHE2 in Wfe; auto.
Qed.

Lemma gdom_env_remove_tmvar : forall E,
  gdom_env (remove_tmvar E) [=] {}.
Proof.
  induction E; simpl; auto.
    destruct a.
    destruct b; simpl; auto.
Qed.

Lemma cv_ec_gen_ctx_tabs_capture : forall E C,
  cv_ec (gen_ctx_tabs_capture E C) [=] ddom_env E `union` cv_ec C.
Proof.
  induction E; intro C; simpl.
    fsetdec.

    destruct a.
    destruct b; simpl. 
      rewrite <- cv_ec_close_tc.
      rewrite IHE. fsetdec.

      rewrite IHE. fsetdec.
Qed.

Lemma wf_typ_Two : 
  wf_typ nil Two kn_nonlin.
Proof.
  unfold Two.
  apply wf_typ_all with (L:={}).
    intros X Xn.
    unfold open_tt. simpl.
    apply wf_typ_arrow with (K1:=kn_nonlin) (K2:=kn_nonlin); auto.
      apply wf_typ_arrow with (K1:=kn_nonlin) (K2:=kn_nonlin); auto.
Qed.

Lemma expr_tt : 
  expr tt.
Proof.
  unfold tt.
  apply expr_tabs with (L:={}).
    intros X Xn.
    unfold open_te. simpl.
    apply expr_abs with (L:={{X}}); auto.
      intros x xn.
      unfold open_ee. simpl.
      apply expr_abs with (L:={{X}} `union` {{x}}); auto.
        intros y yn.
        unfold open_ee. simpl. auto.
Qed.

Lemma type_Two :
  type Two.
Proof.
  unfold Two.
  apply type_all with (L:={}).
    intros X Xn.
    unfold open_tt. simpl.
    apply type_arrow; auto.
Qed.
 

Lemma typing_tt : forall E,
  wf_env E ->
  typing E nil tt Two.
Proof.
  intros E Wfe.
  unfold tt.
  apply typing_tabs with (L:=dom E).
    intros X Xn.
    unfold open_te. simpl.
    apply value_abs.
    apply expr_abs with (L:={{X}}); auto.
      intros x xn.
      unfold open_ee. simpl.
      apply expr_abs with (L:={{X}} `union` {{x}}); auto.
        intros y yn.
        unfold open_ee. simpl. auto.

    intros X Xn.
    unfold open_te. simpl.
    apply typing_abs with (L:=dom E `union` {{X}}); auto.
      destruct (0 == 0); simpl_env; auto.
        contradict n; auto.

      intros x xn.
      unfold open_ee. simpl.
      apply typing_abs with (L:=dom E `union` {{X}} `union` {{x}}); auto.
        intros y yn.
        unfold open_ee. simpl. simpl_env.
        apply typing_var; auto.
          apply wf_env_typ; auto.
Qed.

Lemma from_subst_to_ctx_apair : forall E lE t t' C E',
  contexting E lE t C E' nil t' ->
  contexting E lE t (gen_ctx_apair C) E' nil (gen_typ_with t').
Proof.
  intros E lE t t' C E' Hctx.
  unfold gen_ctx_apair.
  unfold gen_typ_with.
  apply contexting_apair1; auto.
    apply typing_tt.
      apply contexting_regular in Hctx. decompose [and] Hctx; auto.
Qed.

Lemma from_subst_to_ctx_fst : forall E lE t t1' t2' C E' lE',
  contexting E lE t C E' lE' (typ_with t1' t2') ->
  contexting E lE t (gen_ctx_fst C) E' lE' t1'.
Proof.
  intros E lE t t1' t2' C E' lE' Hctx.
  unfold gen_ctx_fst.
  apply contexting_fst with (T2':=t2'); auto.
Qed.

Lemma gen_ctx_tabs_capture_vcontext : forall E C,
  wf_env E ->
  vcontext C ->
  vcontext (gen_ctx_tabs_capture E C).
Proof.
  intros E C Wfe HvC.
  generalize dependent C.
  induction Wfe; intros; simpl; auto.
    apply vcontext_tabs_capture.
    apply context_tabs_capture with (L:={}).
      intros X0 X0n.
      apply IHWfe in HvC.
      apply vcontext__context in HvC.    
      rewrite close_open_tc__subst_tc; auto.
      apply subst_tc_context; auto.
Qed.

Lemma _from_subst_to_ctx_tabs_capture : forall E E' lE t t' C,
  uniq E ->
  cv_tc C [=] {} ->
  cv_ec C [=] gdom_env (E'++E) `union` dom lE ->
  vcontext C ->
  contexting (E'++E) lE t C (remove_tmvar (E'++E)) nil t' ->
  contexting (E'++E) lE t (gen_ctx_tabs_capture E C) (remove_tmvar E') nil (gen_typ_tabs E t').
Proof.
  induction E; intros E' lE t t' C Uniq Hctc Hcec HvC Hctx.
    simpl. simpl_env in *. auto.

    destruct a. destruct b; simpl in *.
      simpl_env in *.
      assert (J:=Uniq).
      inversion J; subst.
      rewrite_env ((E'++[(a, bind_kn k)])++E) in Hctx.
      apply IHE with (t:=t) in Hctx; simpl_env; auto.
        simpl_env in Hctx.
        assert (contexting (E'++[(a, bind_kn k)]++E) lE t (ctx_tabs_capture a k (close_tc (gen_ctx_tabs_capture E C) a)) (remove_tmvar E') nil (typ_all k (close_tt (gen_typ_tabs E t') a)) = 
                     contexting (E'++[(a, bind_kn k)]++E) lE t (ctx_tabs_capture a k (close_tc (gen_ctx_tabs_capture E C) a)) (env_remove (a, bind_kn k) (remove_tmvar (E'++[(a, bind_kn k)])++nil)) nil (typ_all k (close_tt (gen_typ_tabs E t') a))) as EQ.
          rewrite remove_tmvar_app. simpl. simpl_env.
          rewrite_env  (remove_tmvar E'++[(a, bind_kn k)]++nil).
          rewrite env_remove_opt.
            simpl_env. auto.
            apply contexting_regular in Hctx.
            decompose [and] Hctx.
            apply uniq_from_wf_env in H4. simpl_env. 
            rewrite remove_tmvar_app in H4. simpl. assumption.
        rewrite EQ. clear EQ.
        simpl_env.
        apply contexting_tabs_capture; auto.
          rewrite remove_tmvar_app; simpl; auto.

          rewrite cv_ec_gen_ctx_tabs_capture.
          simpl in Hcec. rewrite Hcec.
          rewrite dom__ddom_gdom in H3.
          assert (a `notin` dom lE) as J1.
            apply contexting_regular in Hctx. destruct Hctx as [_ [JJ _]].
            clear - JJ. apply disjoint_wf_lenv in JJ. solve_uniq.
          assert (a `notin` dom E') as J2.
            apply contexting_regular in Hctx. destruct Hctx as [JJ _].
            clear - JJ. apply uniq_from_wf_env in JJ. solve_uniq.
          apply dom__gdom in J2.
          clear - H3 J1 J2. fsetdec.

          apply gen_ctx_tabs_capture_vcontext; auto.
            apply contexting_regular in Hctx.
            decompose [and] Hctx. clear - H.
            apply wf_env_strengthening_tail in H.
            apply wf_env_strengthening_tail in H; auto.

          apply contexting_regular in Hctx.
          decompose [and] Hctx.
          rewrite remove_tmvar_app. simpl.
          rewrite_env  (remove_tmvar E'++[(a, bind_kn k)]++nil).
          rewrite env_remove_opt.
            simpl_env. apply wf_lenv_empty. 
            apply wfe_remove_tmvar in H.
            rewrite remove_tmvar_app in H.
            rewrite remove_tmvar_app in H.
            simpl in H. simpl_env in H.
            rewrite_env (remove_tmvar E'++([(a, bind_kn k)]++remove_tmvar E)++nil) in H.
            apply wf_env_strengthening_nilgdom in H.
               simpl_env in H. assumption.
               apply gdom_env_remove_tmvar.
  
            apply uniq_from_wf_env in H4. 
            rewrite remove_tmvar_app in H4. simpl in *.
            assumption.

      simpl_env in *.
      inversion Uniq; subst.
      rewrite_env ((E'++[(a, bind_typ t0)])++E) in Hctx.   
      apply IHE in Hctx; simpl_env; auto.
        rewrite remove_tmvar_app in  Hctx.
        simpl in Hctx. simpl_env in Hctx. auto.
Qed.

Lemma from_subst_to_ctx_tabs_capture : forall E lE t t' C,
  uniq E ->
  cv_tc C [=] {} ->
  cv_ec C [=] gdom_env E `union` dom lE ->
  vcontext C ->
  contexting E lE t C (remove_tmvar E) nil t' ->
  contexting E lE t (gen_ctx_tabs_capture E C) nil nil  (gen_typ_tabs E t').
Proof.
  intros E lE t t' C Uniq Hctc HvC Hctx.
  rewrite_env (nil++E).
  apply  _from_subst_to_ctx_tabs_capture; auto.
Qed.

Lemma gen_typ_tabs_app : forall E E' t,
  gen_typ_tabs (E ++ E') t = gen_typ_tabs E (gen_typ_tabs E' t).
Proof.
  induction E; intros E' t; simpl; auto.
    destruct a.
    destruct b; auto.
      rewrite IHE. auto.
Qed.

Lemma gen_typ_tabs_id : forall E t,
  ddom_env E [=] {} ->
  gen_typ_tabs E t = t.
Proof.
  induction E; intros t Heq; simpl; auto.
    destruct a.
    destruct b; auto.
      simpl in Heq.
      assert (a `in` {}) as FALSE.
        rewrite <- Heq.
        auto.
      contradict FALSE; auto.
Qed.

Lemma wf_dsubst_nil_dsubst : forall E,
  wf_delta_subst E nil ->
  ddom_env E [=] {}.
Proof.
  induction E; intros Wfd; auto.
    destruct a.
    destruct b; simpl.
      simpl_env in Wfd.
      inversion Wfd; subst.

      simpl_env in Wfd.
      inversion Wfd; subst.
      auto.
Qed.      

Lemma ddom_env_remove_tmvar : forall E,
  ddom_env (remove_tmvar E) [=] ddom_env E.
Proof.
  induction E; simpl; auto.
    destruct a.
    destruct b; simpl; auto.
Qed.

Lemma wf_dsubst_dapp_inv : forall EE dsubst' dsubst,
  wf_delta_subst EE (dsubst'++dsubst) ->
  gdom_env EE [=] {} ->
  exists E', exists E, 
    EE = E' ++ E /\
    ddom_env E [=] dom dsubst /\
    ddom_env E' [=] dom dsubst' /\
    wf_delta_subst E dsubst /\
    wf_delta_subst E' dsubst'.
Proof.
  intros EE dsubst' dsubst Wfd Dom.
  remember (dsubst'++dsubst) as dsE.
  generalize dependent dsubst'.        
  generalize dependent dsubst. 
  induction Wfd; intros; subst.
    symmetry in HeqdsE.
    apply app_eq_nil in HeqdsE.
    destruct HeqdsE; subst.
    exists nil. exists nil. simpl. auto.

    apply one_eq_app in HeqdsE.
    destruct HeqdsE as [[dsE'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      assert (dsE''++dsubst=dsE''++dsubst) as EQ. auto.
      apply IHWfd in EQ.
      destruct EQ as [E1 [E2 [EQ1 [EQ2 [EQ3 [Hwfd1 Hwfd2]]]]]]; subst.
      exists ([(X, bind_kn k)]++E1). exists E2.
      simpl. split; auto. split; auto. 
      split. rewrite EQ3. clear. fsetdec.
      split; auto.
        simpl_env.
        apply wf_delta_subst_styp; auto.
      
        simpl in Dom. assumption.     
 
      assert (SE=nil++SE) as EQ. auto.
      apply IHWfd in EQ.
      destruct EQ as [E1 [E2 [EQ1 [EQ2 [EQ3 [Hwfd1 Hwfd2]]]]]]; subst.
      exists nil. exists ([(X, bind_kn k)]++E1++E2).
      simpl. split; auto. 
      split. simpl_env. rewrite EQ2. rewrite EQ3. clear. fsetdec.
      split; auto.
      split; auto.
        simpl_env.
        apply wf_delta_subst_styp; auto.
    
        simpl in Dom. assumption.     

    simpl in Dom.
    assert (x `in` {}) as FALSE.
           rewrite <- Dom.
           auto.
    contradict FALSE; auto.
Qed.

Lemma remove_tmvar_id : forall E,
  gdom_env E [=] {} ->
  remove_tmvar E = E.
Proof.
  induction E; intros; simpl; auto.
    destruct a.
    destruct b; simpl in *.
      rewrite IHE; auto.

      assert (a `in` {}) as FALSE.
        rewrite <- H.
        auto.
      contradict FALSE; auto.
Qed.      

Lemma remove_tmvar_app_inv : forall E E1 E2,
  remove_tmvar E = E1 ++ E2 ->
  exists E1', exists E2',
    E = E1' ++ E2' /\
    remove_tmvar E1' = E1 /\
    remove_tmvar E2' = E2.
Proof.
  induction E; intros E1 E2 H.
    simpl in H.
    symmetry in H.
    apply app_eq_nil in H.
    destruct H as [J1 J2]; subst.
    exists nil. exists nil. split; auto.

    simpl in H.
    destruct a.
    destruct b.
      simpl_env in H.
      apply one_eq_app in H. destruct H as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
        apply IHE in EQ2. 
        destruct EQ2 as [E1' [E2' [EQ1 [H1 H2]]]]; subst.
        exists ([(a, bind_kn k)]++E1'). exists E2'.
        split; auto.

        exists nil. exists ((a, bind_kn k)::E).
        split; auto.

      apply IHE in H. 
      destruct H as [E1' [E2' [EQ1 [H1 H2]]]]; subst.
      simpl_env.
      exists ([(a, bind_typ t)]++E1'). exists E2'.
      split; auto.
Qed.

Lemma gen_typ_tabs_opt : forall E1 X K E2 t,
  uniq (E1++[(X, bind_kn K)]++E2) ->
  ddom_env (E1++[(X, bind_kn K)]++E2) [=] {{X}} -> 
  gen_typ_tabs (E1++[(X, bind_kn K)]++E2) t = typ_all K (close_tt t X).
Proof.
  induction E1; intros x t0 E2 t Uniq Hdom.
    simpl in *.
    simpl_env in Uniq. inversion Uniq; subst.
    rewrite gen_typ_tabs_id; auto.
      clear - Hdom H3. apply dom__ddom in H3. fsetdec.
    
    destruct a.
    destruct b; simpl in *.
      simpl_env in Hdom.
      assert (a <> x) as anx.
        simpl_env in Uniq. clear - Uniq. solve_uniq.
      assert (a `in` {{x}}) as aisx.
        rewrite <- Hdom.
        auto.
      contradict aisx; auto.

      inversion Uniq; subst.
      apply IHE1 with (t:=t) in H1; auto.
Qed.

Lemma wf_dsubst_single_inv : forall E X d,
  wf_delta_subst E [(X, d)] ->
  exists E1, exists E2, exists K,
    E = E1 ++ [(X, bind_kn K)] ++ E2 /\
    wf_typ nil d K /\ ddom_env E1 [=] {} /\ ddom_env E2 [=] {}.
Proof.
  induction E; intros X d Hwfd.
    inversion Hwfd.

    destruct a.
    destruct b; simpl_env in *.
      inversion Hwfd; subst.     
      exists nil. exists E. exists k. split; auto. 
      split; auto. simpl. split; auto.
      apply wf_dsubst_nil_dsubst in H3; auto.

      inversion Hwfd; subst.
      apply IHE in H2.
      destruct H2 as [E1 [E2 [K [J1 [J2 [J3 J4]]]]]]; subst.
      exists ([(a, bind_typ t)]++E1). exists E2. exists K.
      split; auto.
Qed.

Lemma remove_tmvar_single_inv : forall E a K,
  remove_tmvar E = [(a, bind_kn K)] ->
  exists E1, exists E2,
    E = E1 ++ [(a, bind_kn K)] ++ E2 /\ remove_tmvar E1 = nil /\ remove_tmvar E2 = nil.
Proof.
  induction E; intros X K H.
    simpl in H.
    inversion H.

    destruct a.
    destruct b; simpl in *; simpl_env in *.
      inversion H; subst.     
      exists nil. exists E. auto. 

      apply IHE in H.
      destruct H as [E1 [E2 [J1 [J2 J3]]]]; subst.
      exists ([(a, bind_typ t)]++E1). exists E2. 
      split; auto.
Qed.  

Inductive wf_dsubst : delta_subst -> Prop :=
  | wf_dsubst_empty :
      wf_dsubst delta_nil
  | wf_dsubst_styp : forall SE X T k,
      wf_dsubst SE -> X `notin` dom SE -> wf_typ nil T k ->
      wf_dsubst ([(X, T)] ++ SE)
  .

Tactic Notation "wf_dsubst_cases" tactic(first) tactic(c) :=
  first;
  [ c "wf_dsubst_empty" |
    c "wf_dsubst_styp"].

Hint Constructors wf_dsubst.

Lemma dsubst_nil_typ :  forall dsubst X t dsubst',
   wf_dsubst (dsubst'++[(X, t)]++dsubst) ->
  exists K, wf_typ nil t K.
Proof.
  intros dsubst X t dsubst' Hwf_dsubst.
  remember (dsubst'++[(X, t)]++dsubst) as Dsubst.
  generalize dependent dsubst'.
  (wf_dsubst_cases (induction Hwf_dsubst) Case); 
    intros dsubst' HeqDsubst.
  Case "wf_dsubst_empty".
    contradict HeqDsubst; auto.    
  Case "wf_dsubst_styp".
    destruct (one_eq_app _ _ _ _ _ HeqDsubst) as [[dsubst'' [DEQ1 DEQ2]] | [DEQ1 DEQ2]]; subst.
    SCase "exists DS'',DS'=DS&X0'' /\ DS0=DS&X&DS'' ".
      destruct IHHwf_dsubst with (dsubst':=dsubst'') as [K J]; auto.
      exists K. exact J.
    SCase "DS'=nil /\ DS&X = DS0&X0 ".
      inversion DEQ2. subst.
      exists k. exact H0.
Qed.

Lemma dsubst_opt :  forall dsubst X t t' dsubst',
   wf_dsubst (dsubst'++[(X, t)]++dsubst) ->
   apply_delta_subst_typ (dsubst'++[(X, t)]++dsubst) t' =
     apply_delta_subst_typ (dsubst'++dsubst) (subst_tt X t t').
Proof.
  intros dsubst X t t' dsubst' Hwf_dsubst.
  remember (dsubst'++[(X, t)]++dsubst) as Dsubst.
  generalize dependent t'.
  generalize dependent dsubst'.
  (wf_dsubst_cases (induction Hwf_dsubst) Case); 
    intros dsubst' HeqDsubst t'.
  Case "wf_dsubst_empty".
    contradict HeqDsubst; auto.    
  Case "wf_dsubst_styp".
    destruct (one_eq_app _ _ _ _ _ HeqDsubst) as [[dsubst'' [DEQ1 DEQ2]] | [DEQ1 DEQ2]]; subst.
    SCase "exists DS'',DS'=DS&X0'' /\ DS0=DS&X&DS'' ".
        simpl. simpl_env. 
        rewrite <- subst_tt_commute; auto.
          eauto using notin_fv_wf.

          apply dsubst_nil_typ in Hwf_dsubst.
          destruct Hwf_dsubst as [K Wft].
          eauto using notin_fv_wf.
    SCase "DS'=nil /\ DS&X = DS0&X0 ".
        inversion DEQ2. subst.
        simpl_env in *. destruct_notin.
        auto.
Qed.

Ltac tac_wfd_fresh_X :=
   match goal with
  | H: wf_delta_subst (?E ++ [(?X, _)]) (?dsubst ++ [(?X, _)]) |- _ => 
    apply wf_delta_subst__uniq in H;
    destruct H as [J1 [J2 J3]];
    solve_uniq
  | H: wf_delta_subst (?E' ++ [(?X, _)] ++ ?E) (?dsubst' ++ [(?X, _)] ++ ?dsubst) |- _ => 
    apply wf_delta_subst__uniq in H;
    destruct H as [J1 [J2 J3]];
    solve_uniq
  end.

Lemma ddom_dom__inv' : forall A (sE : list (atom * A)) E X b K,
  ddom_env (E++[(X, bind_kn K)]) [=] dom (sE++[(X, b)]) ->
  X `notin` ddom_env E ->
  X `notin` dom sE ->
  ddom_env E [=] dom sE.
Proof.
  intros.
  simpl_env in *.
  fsetdec.
Qed.

Lemma dsubst_head_opt :  forall dsubst X t t',
   wf_dsubst (dsubst++[(X, t)]) ->
   apply_delta_subst_typ (dsubst++[(X, t)]) t' =
     apply_delta_subst_typ dsubst (subst_tt X t t').
Proof.
  intros dsubst X t t' Hwfd.
  rewrite_env (dsubst++nil).
  rewrite_env (dsubst++[(X, t)]++nil).
  apply dsubst_opt; auto.
Qed.

Lemma wf_delta_subst__wf_dsubst : forall E dsubst,
  wf_delta_subst E dsubst ->
  wf_dsubst dsubst.
Proof.
  intros E dsubst Hwfd.
  (wf_delta_subst_cases (induction Hwfd) Case); auto.
  Case "wf_delta_subst_styp".
    apply wf_dsubst_styp with (k:=k); auto.
      apply dom_delta_subst in Hwfd.
      rewrite <- Hwfd.
      apply dom__ddom; auto.
Qed.

Lemma wf_dsubst_styp_rev : forall SE X T k,
  wf_dsubst SE -> X `notin` dom SE -> wf_typ nil T k ->
  wf_dsubst (SE++[(X, T)]).
Proof.
  intros SE X T k Wfd.
  generalize dependent X.
  generalize dependent T.
  generalize dependent k.
  induction Wfd; intros; auto.
    rewrite_env ([(X, T)]++delta_nil).
    apply wf_dsubst_styp with (k:=k); auto.

    simpl_env.
    apply wf_dsubst_styp with (k:=k); auto.
    apply IHWfd with (k:=k0); auto.
Qed.

Lemma dom_rev : forall A (E : @list (atom*A)),
  dom E [=] dom (rev E).
Proof.
  intros A E.
  induction E; simpl; auto.
    destruct a. simpl_env.
    rewrite IHE. fsetdec.
Qed.

Lemma wf_dsubst_rev : forall E,
  wf_dsubst E ->
  wf_dsubst (rev E).
Proof.
  intros E Wfd.
  induction Wfd; intros; auto.
    simpl. simpl_env.
    apply wf_dsubst_styp_rev with (k:=k); auto.
      rewrite <- dom_rev; auto.
Qed.

Lemma gen_typ_tabs_type : forall E t,
  type t ->
  type (gen_typ_tabs E t).
Proof.
  induction E; intros t Htype; simpl; auto.
    destruct a.
    destruct b; auto.
     apply type_all with (L:={{a}}).
       intros X FrX.
       rewrite close_open_tt__subst_tt; auto.
Qed.

Lemma type_preserved_under_dsubst: forall dsubst t,
   wf_dsubst dsubst ->
   type t ->
   type (apply_delta_subst_typ dsubst t).
Proof.
  intros dsubst t Hwfd Ht.
  generalize dependent t.
  induction Hwfd; intros; simpl; auto.
    apply IHHwfd.
      apply subst_tt_type; eauto using type_from_wf_typ.
Qed.

Lemma gen_typ_tabs_subst_tt_commute : forall E X T K t,
  X `notin` dom E ->
  wf_typ nil T K ->
  gen_typ_tabs E (subst_tt X T t)  = subst_tt X T (gen_typ_tabs E t).
Proof.
  induction E; intros X T K t HC Wft; simpl; auto.
  destruct a.
  destruct b; simpl.
    rewrite IHE with (K:=K); auto.
    rewrite subst_tt_close_tt; auto.
      apply notin_fv_wf with (X:=a) in Wft; auto.

    rewrite IHE with (K:=K); auto.
Qed.

Lemma dsubst_permut : forall dsubst X T K t,
  wf_dsubst dsubst ->
  X `notin` dom dsubst -> wf_typ nil T K ->
  apply_delta_subst_typ dsubst (subst_tt X T t) = subst_tt X T (apply_delta_subst_typ dsubst t).
Proof.
  intros dsubst X T K t Hwfd Fr Hwft.
  generalize dependent t.
  induction Hwfd; intros; simpl; eauto.
    simpl_env in *.
    rewrite <- subst_tt_commute; eauto using notin_fv_wf.
Qed.

Lemma in_remove_tmvar_dom : forall x E,
  x `in` dom (remove_tmvar E) ->
  x `in` dom E.
Proof.
  intros x.
  induction E; intros; simpl; auto.
    destruct a.
    simpl_env in H.
    destruct_notin.
    destruct b; simpl in *; auto.
      assert (x `in` {{a}} \/ x `in` dom (remove_tmvar E)) as J. fsetdec.
      destruct J as [J | J]; fsetdec.
Qed.

Lemma _from_subst_to_ctx_tapp : forall dsubst' E' E lE t t' C,
  wf_delta_subst (remove_tmvar E')  (rev dsubst') ->
  type t' ->
  contexting (E'++E) lE t C nil nil (gen_typ_tabs (E'++E) t') ->
  contexting (E'++E) lE t (gen_ctx_tapp dsubst' C) nil nil (gen_typ_tabs E (apply_delta_subst_typ dsubst' t')).
Proof.
  induction dsubst'; intros E' E lE t t' C Hwfd Htype Hctx; simpl.
    simpl in Hwfd.
    apply wf_dsubst_nil_dsubst in Hwfd.
    rewrite gen_typ_tabs_app in Hctx.
    rewrite gen_typ_tabs_id in Hctx; auto.
    rewrite ddom_env_remove_tmvar in Hwfd; auto.

    destruct a. simpl in Hwfd. simpl_env in Hwfd.
    apply wf_dsubst_dapp_inv in Hwfd; auto using gdom_env_remove_tmvar.
    destruct Hwfd as [E1 [E2 [EQ1 [EQ2 [EQ3 [Hwfd1 Hwfd2]]]]]]; subst.
    apply remove_tmvar_app_inv in EQ1.
    destruct EQ1 as [E1' [E2' [EQ' [EQ2' EQ3']]]]; subst.
    rewrite_env (E1'++(E2'++E)) in Hctx.
    apply IHdsubst' in Hctx; auto.
    rewrite gen_typ_tabs_app in Hctx.
    assert (gen_typ_tabs E (apply_delta_subst_typ dsubst' (subst_tt a d t')) = 
                   open_tt (close_tt (gen_typ_tabs E (apply_delta_subst_typ dsubst' t')) a) d) as EQ.
      rewrite close_open_tt__subst_tt; auto.
        assert (J:=Hwfd1).
        apply wf_dsubst_single_inv in J.
        destruct J as [E1 [E2 [K [J1 [J2 [J3 J4]]]]]]; subst.
        rewrite <- gen_typ_tabs_subst_tt_commute with (K:=K); auto.
          rewrite dsubst_permut with (K:=K); auto.
           apply wf_delta_subst__wf_dsubst in Hwfd2.
           apply wf_dsubst_rev in Hwfd2.
           rewrite <- rev_involutive; auto.

           rewrite dom_rev.
           rewrite <- EQ3.
           apply dom__ddom.
           apply notin_remove_tmvar_dom.
           assert (a `in` dom E2') as J.
             apply in_remove_tmvar_dom.
             rewrite J1. simpl_env. auto.
           apply contexting_regular in Hctx.
           destruct Hctx as [J' _].
           apply uniq_from_wf_env in J'.
           clear - J' J. solve_uniq.

         assert (a `in` dom E2') as J.
           apply in_remove_tmvar_dom.
         rewrite J1. simpl_env. auto.
         apply contexting_regular in Hctx.
         destruct Hctx as [J' _].
         apply uniq_from_wf_env in J'.
         clear - J' J. solve_uniq.
          
        apply gen_typ_tabs_type.
        apply type_preserved_under_dsubst; auto.
           apply wf_delta_subst__wf_dsubst in Hwfd2.
           apply wf_dsubst_rev in Hwfd2.
           rewrite <- rev_involutive; auto.
        
    rewrite EQ. clear EQ.
    assert (J:=Hwfd1).
    apply wf_dsubst_single_inv in J.
    destruct J as [E1 [E2 [K [EQ4 [Hwft [JJ1 JJ2]]]]]]; subst.
    apply contexting_tapp with (K:=K); auto.
    assert (exists E21', exists E22', 
                     E2' = E21' ++ [(a, bind_kn K)]++E22' /\
                     remove_tmvar E21' = E1 /\
                     remove_tmvar E22' = E2
                 ) as EQ. 
      clear - EQ4.
      assert (J:=EQ4).
      apply remove_tmvar_app_inv in EQ4.
      destruct EQ4 as [F1 [F2 [J1 [J2 J3]]]].
      apply remove_tmvar_app_inv in J3.
      destruct J3 as [F3 [F4 [J4 [J5 J6]]]].
      subst.
      apply remove_tmvar_single_inv in J5.
      destruct J5 as [F5 [F6 [J1 [J2 J3]]]]; subst.
      exists (F1++F5). exists (F6++F4).
      simpl_env. split; auto.
      rewrite remove_tmvar_app.
      rewrite remove_tmvar_app.
      rewrite J3. rewrite J2.
      split; auto.
    destruct EQ as [E21' [E22' [EQ5 [EQ6 EQ7]]]]; subst.     
    rewrite gen_typ_tabs_opt in Hctx; auto.
      simpl_env in Hctx; simpl_env; auto.

      apply contexting_regular in Hctx.
      decompose [and] Hctx.
      apply uniq_from_wf_env in H.
      clear - H. solve_uniq.
      
      rewrite EQ4 in Hwfd1. clear - Hwfd1 EQ4. 
      apply wf_dsubst_single_inv in Hwfd1.
      destruct Hwfd1 as [E1 [E2 [K0 [J1 [J2 [J3 J4]]]]]]; subst.
      rewrite J1 in EQ4.
      rewrite <- ddom_env_remove_tmvar.
      rewrite EQ4. 
      simpl_env. rewrite J3. rewrite J4. fsetdec.
Qed.

Lemma from_subst_to_ctx_tapp : forall E lE dsubst t t' C,
  wf_delta_subst (remove_tmvar E) (rev dsubst)  ->
  type t' ->
  contexting E lE t C nil nil (gen_typ_tabs E t') ->
  contexting E lE t (gen_ctx_tapp dsubst C) nil nil (apply_delta_subst_typ dsubst t').
Proof.
  intros E lE dsubst t t' C Hwfd Htype Hctx.
  rewrite_env (E++nil) in Hctx.
  apply  _from_subst_to_ctx_tapp with (dsubst':=dsubst) in Hctx; simpl in Hctx; simpl_env in Hctx; auto.
Qed.

Lemma gen_typ_abs_app : forall E E' t,
  gen_typ_abs (E ++ E') t = gen_typ_abs E (gen_typ_abs E' t).
Proof.
  induction E; intros E' t; simpl; auto.
    destruct a.
    destruct b; auto.
      rewrite IHE. auto.
Qed.

Lemma gen_typ_abs_id : forall E t,
  gdom_env E [=] {} ->
  gen_typ_abs E t = t.
Proof.
  induction E; intros t Heq; simpl; auto.
    destruct a.
    destruct b; auto.
      simpl in Heq.
      assert (a `in` {}) as FALSE.
        rewrite <- Heq.
        auto.
      contradict FALSE; auto.
Qed.

Lemma wf_gsubst_nil_gsubst : forall E dsubst,
  wf_gamma_subst E dsubst nil->
  gdom_env E [=] {}.
Proof.
  induction E; intros dsubst Wfg; auto.
    destruct a.
    destruct b; simpl.
      simpl_env in Wfg.
      inversion Wfg; subst; eauto.

      simpl_env in Wfg.
      inversion Wfg; subst.
Qed.      

Lemma gdom_env_remove_typvar : forall E,
  gdom_env (remove_typvar E) [=] gdom_env E.
Proof.
  induction E; simpl; auto.
    destruct a.
    destruct b; simpl; auto.
Qed.

Lemma wf_gamma_subst__nfv : forall E dsubst gsubst x,
  wf_gamma_subst E dsubst gsubst ->
  x `notin` dom E ->
  x `notin` dom dsubst /\ x `notin` dom gsubst  /\ x `notin` fv_env E.
intros E dsubst gsubst x Hwfg Hfv.
  induction Hwfg; intros; auto.
    apply notin_fv_wf with (X:=x) in H1; simpl; auto.    
    apply notin_fv_wf with (X:=x) in H0; simpl; auto.    
Qed.

Lemma wf_gamma_subst__uniq : forall E dsubst gsubst,
  wf_gamma_subst E dsubst gsubst -> 
  uniq gsubst /\ uniq dsubst /\ uniq E.
Proof.
  intros.
  induction H; auto.
    decompose [and] IHwf_gamma_subst.
    split.
      apply uniq_push; auto.
        apply wf_gamma_subst__nfv with (x:=x) in H; auto.
    split; auto.

    apply wf_gamma_subst__nfv with (x:=X) in H; auto.
    decompose [and] IHwf_gamma_subst.
    split; auto.
Qed.

Lemma wf_gamma_subst_strengthen_when_nilE : forall E dsubst gsubst,
  wf_gamma_subst E dsubst gsubst ->
  ddom_env E [=] {} ->
  wf_gamma_subst nil dsubst nil.
Proof.
  intros E dsubst gsubst Hwfg Heq.
  induction Hwfg; auto.
    simpl in Heq.
    assert (X `in` {}) as FALSE.
           rewrite <- Heq.
           auto.
    contradict FALSE; auto.
Qed.

Lemma wf_gsubst_gapp_inv : forall EE gsubst' gsubst,
  wf_gamma_subst EE nil (gsubst'++gsubst) ->
  ddom_env EE [=] {} ->
  exists E', exists E, 
    EE = E' ++ E /\
    gdom_env E [=] dom gsubst /\
    gdom_env E' [=] dom gsubst' /\
    wf_gamma_subst E nil gsubst /\
    wf_gamma_subst E' nil gsubst'.
Proof.
  intros EE gsubst' gsubst Wfg Dom.
  remember (gsubst'++gsubst) as gsE.
  generalize dependent gsubst'.        
  generalize dependent gsubst. 
  induction Wfg; intros; subst.
    symmetry in HeqgsE.
    apply app_eq_nil in HeqgsE.
    destruct HeqgsE as [J1 J2]; subst.
    exists nil. exists nil. split; auto.

    apply one_eq_app in HeqgsE. destruct HeqgsE as [[gsE'' [gsEQ1 gsEQ2]] | [gsEQ1 gsEQ2]]; subst.
         assert (gsE''++gsubst = gsE''++gsubst) as EQ. auto.
         simpl_env in Dom.
         apply IHWfg in EQ.
           destruct EQ as [E1 [E2 [EQ1 [EQ2 [EQ3 [Wfg1 Wfg2]]]]]]; subst.
           exists ([(x, bind_typ T)]++E1). exists E2.
           split; auto.
           split; auto.
           split; auto.
             simpl. rewrite EQ3. fsetdec.
           split; auto.
             simpl_env. apply wf_gamma_subst_sval; auto.
             rewrite_env ((E1++E2)++nil) in H1.
             apply wft_strengthen_ex in H1; auto.
               rewrite_env (nil++E1++nil).
               apply wf_typ_weakening; auto.
                 apply wf_gamma_subst__uniq in Wfg2.
                 decompose [and] Wfg2.
                 simpl_env. auto.
               clear - Dom. fsetdec.
             clear - Dom. fsetdec.

         exists nil. exists ([(x, bind_typ T)]++E).
         split; auto.
         split.
           simpl_env. apply dom_gamma_subst in Wfg.
           destruct Wfg. rewrite H3. fsetdec.
         split; auto.
         split.
           simpl_env. apply wf_gamma_subst_sval; auto.
           apply wf_gamma_subst_strengthen_when_nilE in Wfg; auto.

         simpl in Dom.
         assert (X `in` {}) as FALSE.
           rewrite <- Dom.
           auto.
         contradict FALSE; auto.
Qed.

Lemma ddom_env_remove_typvar : forall E,
  ddom_env (remove_typvar E) [=] {}.
Proof.
  induction E; simpl; auto.
    destruct a.
    destruct b; simpl; auto.
Qed.

Lemma remove_typvar_id : forall E,
  ddom_env E [=] {} ->
  remove_typvar E = E.
Proof.
  induction E; intros; simpl; auto.
    destruct a.
    destruct b; simpl in *.
      assert (a `in` {}) as FALSE.
        rewrite <- H.
        auto.
      contradict FALSE; auto.

      rewrite IHE; auto.
Qed.      

Lemma remove_typvar_app_inv : forall E E1 E2,
  remove_typvar E = E1 ++ E2 ->
  exists E1', exists E2',
    E = E1' ++ E2' /\
    remove_typvar E1' = E1 /\
    remove_typvar E2' = E2.
Proof.
  induction E; intros E1 E2 H.
    simpl in H.
    symmetry in H.
    apply app_eq_nil in H.
    destruct H as [J1 J2]; subst.
    exists nil. exists nil. split; auto.

    simpl in H.
    destruct a.
    destruct b.
      apply IHE in H. 
      destruct H as [E1' [E2' [EQ1 [H1 H2]]]]; subst.
      simpl_env.
      exists ([(a, bind_kn k)]++E1'). exists E2'.
      split; auto.

      simpl_env in H.
      apply one_eq_app in H. destruct H as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
        apply IHE in EQ2. 
        destruct EQ2 as [E1' [E2' [EQ1 [H1 H2]]]]; subst.
        exists ([(a, bind_typ t)]++E1'). exists E2'.
        split; auto.

        exists nil. exists ((a, bind_typ t)::E).
        split; auto.
Qed.

Lemma gen_typ_abs_opt : forall E1 x t0 E2 t,
  uniq (E1++[(x, bind_typ t0)]++E2) ->
  gdom_env (E1++[(x, bind_typ t0)]++E2) [=] {{x}} -> 
  gen_typ_abs (E1++[(x, bind_typ t0)]++E2) t = typ_arrow kn_lin t0 t.
Proof.
  induction E1; intros x t0 E2 t Uniq Hdom.
    simpl in *.
    simpl_env in Uniq. inversion Uniq; subst.
    rewrite gen_typ_abs_id; auto.
      clear - Hdom H3. apply dom__gdom in H3. fsetdec.
    
    destruct a.
    destruct b; simpl in *.
      inversion Uniq; subst.
      apply IHE1 with (t:=t) in H1; auto.

      simpl_env in Hdom.
      assert (a <> x) as anx.
        simpl_env in Uniq. clear - Uniq. solve_uniq.
      assert (a `in` {{x}}) as aisx.
        rewrite <- Hdom.
        auto.
      contradict aisx; auto.
Qed.

Lemma wf_gsubst_single_inv : forall E x v,
  wf_gamma_subst E nil [(x, v)] ->
  exists E1, exists E2, exists t,
    E = E1 ++ [(x, bind_typ t)] ++ E2 /\
    typing nil nil v t.
Proof.
  induction E; intros x v Hwfg.
    inversion Hwfg.

    destruct a.
    destruct b; simpl_env in *.
      inversion Hwfg; subst.

      inversion Hwfg; subst.     
      exists nil. exists E. exists t. split; auto. 
Qed.

Lemma apply_delta_subst_env_gdom : forall dsubst E,
  gdom_env E [=] gdom_env (apply_delta_subst_env dsubst E).
Proof.
  induction E; intros; simpl; auto.
    destruct a. 
    destruct b; simpl; rewrite <- IHE; fsetdec.
Qed.

Lemma apply_delta_subst_env_ddom : forall dsubst E,
  ddom_env E [=] ddom_env (apply_delta_subst_env dsubst E).
Proof.
  induction E; intros; simpl; auto.
    destruct a. 
    destruct b; simpl; rewrite <- IHE; fsetdec.
Qed.

Lemma apply_delta_subst_env_remove_typvar_commut : forall E dsubst,
  apply_delta_subst_env dsubst (remove_typvar E) =
    remove_typvar (apply_delta_subst_env dsubst E).
Proof.
  induction E; intros dsubst; simpl; auto.
    destruct a.
    destruct b; simpl; auto.
      rewrite IHE; auto.
Qed.

Lemma apply_delta_subst_env_app_inv : forall E dsubst E1 E2,
  apply_delta_subst_env dsubst E = E1 ++ E2 ->
  exists E1', exists E2',
    E = E1' ++ E2' /\
    apply_delta_subst_env dsubst E1' = E1 /\
    apply_delta_subst_env dsubst E2' = E2.
Proof.
  induction E; intros dsubst E1 E2 H.
    simpl in H.
    symmetry in H.
    apply app_eq_nil in H.
    destruct H as [J1 J2]; subst.
    exists nil. exists nil. split; auto.

    simpl in H.
    destruct a.
    destruct b.
      simpl_env in H.
      apply one_eq_app in H. destruct H as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
        apply IHE in EQ2. 
        destruct EQ2 as [E1' [E2' [EQ1 [H1 H2]]]]; subst.
        exists ([(a, bind_kn k)]++E1'). exists E2'.
        split; auto.

        exists nil. exists ((a, bind_kn k)::E).
        split; auto.

      simpl_env in H.
      apply one_eq_app in H. destruct H as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
        apply IHE in EQ2. 
        destruct EQ2 as [E1' [E2' [EQ1 [H1 H2]]]]; subst.
        exists ([(a, bind_typ t)]++E1'). exists E2'.
        split; auto.

        exists nil. exists ((a, bind_typ t)::E).
        split; auto.
Qed.

Lemma apply_delta_subst_env_app : forall E E' dsubst,
  apply_delta_subst_env dsubst (E ++ E') = 
    apply_delta_subst_env dsubst E ++ apply_delta_subst_env dsubst E'.
Proof.
  induction E; intros E' dsubst; simpl; auto.
    destruct a.
    destruct b; rewrite IHE; auto.
Qed.

Lemma wf_dsubst_app_inv' : forall E E' dsE,
  wf_delta_subst (E'++E) dsE ->
  gdom_env (E'++E) [=] {} ->
  exists dsubst', exists dsubst, 
    dsE = dsubst' ++ dsubst /\
    ddom_env E [=] dom dsubst /\
    ddom_env E' [=] dom dsubst' /\
    wf_delta_subst E dsubst /\
    wf_delta_subst E' dsubst'.
Proof.
  intros E E' dsE Wfd Dom.
  remember (E'++E) as EE.
  generalize dependent E'.        
  generalize dependent E. 
  induction Wfd; intros; subst.
    symmetry in HeqEE.
    apply app_eq_nil in HeqEE.
    destruct HeqEE; subst.
    exists nil. exists nil. simpl. auto.

    apply one_eq_app in HeqEE.
    destruct HeqEE as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      assert (E''++E0=E''++E0) as EQ. auto.
      apply IHWfd in EQ.
      destruct EQ as [dsubst1 [dsubst2 [EQ1 [EQ2 [EQ3 [Hwfd1 Hwfd2]]]]]]; subst.
      exists ([(X, T)]++dsubst1). exists dsubst2.
      simpl. split; auto. split; auto. 
      split. rewrite EQ3. clear. fsetdec.
      split; auto.
        simpl_env.
        apply wf_delta_subst_styp; auto.
      
        simpl in Dom. assumption.     
 
      assert (E=nil++E) as EQ. auto.
      apply IHWfd in EQ.
      destruct EQ as [dsubst1 [dsubst2 [EQ1 [EQ2 [EQ3 [Hwfd1 Hwfd2]]]]]]; subst.
      exists nil. exists ([(X, T)]++dsubst1++dsubst2).
      simpl. split; auto. 
      split. simpl_env. rewrite EQ2. rewrite <- EQ3. clear. fsetdec.
      split; auto.
      split; auto.
        simpl_env.
        apply wf_delta_subst_styp; auto.
    
        simpl in Dom. assumption.     

    simpl in Dom.
    assert (x `in` {}) as FALSE.
           rewrite <- Dom.
           auto.
    contradict FALSE; auto.
Qed.

Lemma wf_dsubst_app_merge : forall E E' dsubst dsubst',
  wf_delta_subst E dsubst ->
  wf_delta_subst E' dsubst' ->
  uniq (E'++E) ->
  wf_delta_subst (E'++E) (dsubst'++dsubst).
Proof.
  intros E E' dsubst dsubst' Hwfd Hwfd' Uniq.
  generalize dependent E.
  generalize dependent dsubst.
  induction Hwfd'; intros; simpl_env; auto.
    simpl_env in Uniq.
    inversion Uniq; subst.
    apply IHHwfd' in Hwfd; auto.

    simpl_env in Uniq.
    inversion Uniq; subst.
    apply IHHwfd' in Hwfd; auto.
    apply wf_delta_subst_skip; auto.
      rewrite_env (E++E0++nil).
      apply wf_typ_weakening; simpl_env; auto.
Qed.

Lemma apply_delta_subst_env_uniq : forall E dsubst,
  uniq E ->
  uniq (apply_delta_subst_env dsubst E).
Proof.
  induction E; intros dsubst Uniq; simpl; auto.
    destruct a.
    destruct b.
      inversion Uniq; subst.
      simpl_env.
      apply uniq_push; auto.
        rewrite <- apply_delta_subst_env_dom; auto.
     
      inversion Uniq; subst.
      simpl_env.
      apply uniq_push; auto.
        rewrite <- apply_delta_subst_env_dom; auto.
Qed.


Lemma apply_delta_subst_env_nil : forall E,
  apply_delta_subst_env nil E = E.
Proof.
  induction E; simpl; auto.
  destruct a.
  destruct b; simpl.
    rewrite IHE; auto.
    rewrite IHE; auto.
Qed.

Lemma apply_delta_subst_env_cons : forall E X T dsubst,
  apply_delta_subst_env ([(X, T)]++dsubst) E = apply_delta_subst_env dsubst (map (subst_tb X T) E).
Proof.
  induction E; intros X T dsubst; simpl; auto.
  destruct a.
  destruct b; simpl; simpl_env.
    rewrite IHE; auto.
    rewrite IHE; auto.
Qed.

Lemma apply_delta_subst_env_subst_tb_swap : forall F E dsubst X T K,
  wf_delta_subst E dsubst ->
  X `notin` dom E ->
  wf_typ empty T K ->
  apply_delta_subst_env dsubst (map (subst_tb X T) F) =
    map (subst_tb X T) (apply_delta_subst_env dsubst F).
Proof.
  induction F; intros E dsubst X T K Hwfd XnE Hwft; simpl; auto.
  destruct a.
  destruct b; simpl; simpl_env.
    rewrite IHF with (E:=E) (K:=K); auto.
    rewrite delta_subst_permut with (dE:=E) (K:=K); auto.
      rewrite IHF with (E:=E) (K:=K); auto.
      apply dom_delta_subst in Hwfd. rewrite <- Hwfd. 
      apply dom__ddom in XnE. auto.
Qed.  

Lemma wf_dsubst_dapp_head : forall EE dsubst' dsubst,
  wf_delta_subst EE (dsubst'++dsubst) ->
  exists E', exists E, 
    EE = E' ++ E /\
    ddom_env E [=] dom dsubst /\
    ddom_env E' [=] dom dsubst' /\
    wf_delta_subst E dsubst.
Proof.
  intros EE dsubst' dsubst Wfd.
  remember (dsubst'++dsubst) as dsE.
  generalize dependent dsubst'.        
  generalize dependent dsubst. 
  induction Wfd; intros; subst.
    symmetry in HeqdsE.
    apply app_eq_nil in HeqdsE.
    destruct HeqdsE; subst.
    exists nil. exists nil. simpl. auto.

    apply one_eq_app in HeqdsE.
    destruct HeqdsE as [[dsE'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      assert (dsE''++dsubst=dsE''++dsubst) as EQ. auto.
      apply IHWfd in EQ.
      destruct EQ as [E1 [E2 [EQ1 [EQ2 [EQ3 Hwfd2]]]]]; subst.
      exists ([(X, bind_kn k)]++E1). exists E2.
      simpl. split; auto. split; auto. 
      split; auto. rewrite EQ3. clear. fsetdec.
 
      assert (SE=nil++SE) as EQ. auto.
      apply IHWfd in EQ.
      destruct EQ as [E1 [E2 [EQ1 [EQ2 [EQ3 Hwfd2]]]]]; subst.
      exists nil. exists ([(X, bind_kn k)]++E1++E2).
      simpl. split; auto. 
      split. simpl_env. rewrite EQ2. rewrite EQ3. clear. fsetdec.
      split; auto.
        simpl_env.
        apply wf_delta_subst_styp; auto.

    assert (dsubst'++dsubst=dsubst'++dsubst) as EQ. auto.
    apply IHWfd in EQ.
    destruct EQ as [E1 [E2 [EQ1 [EQ2 [EQ3 Hwfd2]]]]]; subst.
    exists ([(x, bind_typ T)]++E1). exists E2.
    simpl. split; auto. 
Qed.

Lemma apply_delta_subst_env_dsubst_app : forall dsubst' dsubst E F,
  wf_delta_subst F (dsubst'++dsubst) -> 
  apply_delta_subst_env (dsubst'++dsubst) E =
    apply_delta_subst_env dsubst' (apply_delta_subst_env dsubst E).
Proof.
  intros dsubst' dsubst E F Hwfd.
  remember (dsubst'++dsubst) as dsE.
  generalize dependent dsubst'.
  generalize dependent E.
  induction Hwfd; intros; subst.
    symmetry in HeqdsE.
    apply app_eq_nil in HeqdsE.
    destruct HeqdsE; subst.
    rewrite apply_delta_subst_env_nil.
    rewrite apply_delta_subst_env_nil. auto.

    apply one_eq_app in HeqdsE.
    destruct HeqdsE as [[dsE'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      assert (dsE''++dsubst=dsE''++dsubst) as EQ. auto.
      simpl_env.
      rewrite apply_delta_subst_env_cons.
      rewrite apply_delta_subst_env_cons. 
      apply IHHwfd with (E:=map (subst_tb X T) E0) in EQ.
      assert (J:=Hwfd).
      apply wf_dsubst_dapp_head in J.
      destruct J as [E1 [E2 [J1 [J2 [J3 J4]]]]]; subst.
      rewrite <- apply_delta_subst_env_subst_tb_swap with (E:=E2) (K:=k) (dsubst:=dsubst); auto.   

      simpl_env.
      rewrite apply_delta_subst_env_nil. auto.

    assert (dsubst'++dsubst=dsubst'++dsubst) as EQ. auto.
    apply IHHwfd with (E:=E0) in EQ. assumption.
Qed.

Lemma commut_subst_tt_rdsubst: forall t X E dsubst T K,
  wf_delta_subst E dsubst ->
  wf_typ nil t K ->
  X `notin` dom E ->
  apply_delta_subst_typ (rev dsubst) (subst_tt X t T) =
  subst_tt X t (apply_delta_subst_typ (rev dsubst) T).
Proof.
  intros t X E dsubst T K Hwfd Hwft Fr.
  generalize dependent t.
  generalize dependent T.
  induction Hwfd; intros; simpl; auto.
    simpl_env in*. destruct_notin.
    assert (J:=Hwfd).
    apply wf_delta_subst__wf_dsubst in Hwfd.
    apply wf_dsubst_rev in Hwfd.
    apply dom_delta_subst in J.
    apply wf_dsubst_styp_rev with (X:=X0) (T:=T) (k:=k) in Hwfd; auto.
      rewrite dsubst_head_opt; auto.
      rewrite dsubst_head_opt; auto.
      rewrite <- IHHwfd; auto.
        rewrite subst_tt_commute; eauto using notin_fv_wf.
 
     apply dom__ddom in H.     
      rewrite J in H.
      rewrite <- dom_rev; auto.
Qed.

Lemma apply_delta_subst_typ_rev : forall E dsubst t,
  wf_delta_subst E dsubst ->
  apply_delta_subst_typ dsubst t = apply_delta_subst_typ (rev dsubst) t.
proof.
  let E, dsubst, t:typ be such that Hwfd:(wf_delta_subst E dsubst). 
  escape.
  generalize dependent t.
  induction Hwfd; intro t; simpl; simpl_env; auto.
    rewrite commut_subst_tt_dsubst with (E:=E) (K:=k); auto.
    rewrite IHHwfd.
    rewrite <- commut_subst_tt_rdsubst with (E:=E) (K:=k); auto.
    rewrite dsubst_head_opt; auto.
    apply wf_dsubst_styp_rev with (k:=k); auto.
       apply wf_delta_subst__wf_dsubst in Hwfd.
       apply wf_dsubst_rev; auto.

       apply dom_delta_subst in Hwfd.
       apply dom__ddom in H.     
        rewrite Hwfd in H.
        rewrite <- dom_rev; auto.
  return.
  end proof.
Qed.

Lemma dsubst_te_opt :  forall dsubst X t e dsubst',
   wf_dsubst (dsubst'++[(X, t)]++dsubst) ->
   apply_delta_subst (dsubst'++[(X, t)]++dsubst) e =
     apply_delta_subst (dsubst'++dsubst) (subst_te X t e).
Proof.
  intros dsubst X t e dsubst' Hwf_dsubst.
  remember (dsubst'++[(X, t)]++dsubst) as Dsubst.
  generalize dependent e.
  generalize dependent dsubst'.
  (wf_dsubst_cases (induction Hwf_dsubst) Case); 
    intros dsubst' HeqDsubst e.
  Case "wf_dsubst_empty".
    contradict HeqDsubst; auto.    
  Case "wf_dsubst_styp".
      destruct (one_eq_app _ _ _ _ _ HeqDsubst) as [[dsubst'' [DEQ1 DEQ2]] | [DEQ1 DEQ2]]; subst.
      SSCase "exists DS'',DS'=DS&X0'' /\ DS0=DS&X&DS'' ".
        simpl. simpl_env. 
        rewrite <- subst_te_commute; auto.
          eauto using notin_fv_wf.

          apply dsubst_nil_typ in Hwf_dsubst.
          destruct Hwf_dsubst as [K Wft].
          eauto using notin_fv_wf.
      SSCase "DS'=nil /\ DS&X = DS0&X0 ".
        inversion DEQ2. subst.
        simpl_env in *. destruct_notin.
        auto.
Qed.

Lemma dsubst_te_head_opt :  forall dsubst X t e,
   wf_dsubst (dsubst++[(X, t)]) ->
   apply_delta_subst (dsubst++[(X, t)]) e =
     apply_delta_subst dsubst (subst_te X t e).
Proof.
  intros dsubst X t e Hwfd.
  rewrite_env (dsubst++nil).
  rewrite_env (dsubst++[(X, t)]++nil).
  apply dsubst_te_opt; auto.
Qed.

Lemma swap_subst_te_rdsubst: forall t X E dsubst e K,
  wf_delta_subst E dsubst ->
  wf_typ nil t K ->
  X `notin` dom dsubst ->
  subst_te X t (apply_delta_subst (rev dsubst) e) =
  apply_delta_subst (rev dsubst) (subst_te X t e).
Proof.
  intros t X E dsubst e K Hwfd Hwft xndsubst.
  generalize dependent e.
  generalize dependent t.
  induction Hwfd; intros t Hwft e0; simpl; eauto.
    simpl_env.
    simpl_env in*. destruct_notin.
    assert (J:=Hwfd).
    apply wf_delta_subst__wf_dsubst in Hwfd.
    apply wf_dsubst_rev in Hwfd.
    apply dom_delta_subst in J.
    apply wf_dsubst_styp_rev with (X:=X0) (T:=T) (k:=k) in Hwfd; auto.
      rewrite dsubst_te_head_opt; auto.
      rewrite dsubst_te_head_opt; auto.
      rewrite IHHwfd; auto.
        rewrite subst_te_commute; eauto using notin_fv_wf.
 
     apply dom__ddom in H.     
      rewrite J in H.
      rewrite <- dom_rev; auto.
Qed.

Lemma apply_delta_subst_rev : forall E dsubst e,
  wf_delta_subst E dsubst ->
  apply_delta_subst dsubst e = apply_delta_subst (rev dsubst) e.
proof.
  let E, dsubst, e:exp be such that Hwfd:(wf_delta_subst E dsubst). 
  escape.
  generalize dependent e.
  induction Hwfd; intro e; simpl; simpl_env; auto.
    assert (X `notin` dom SE) as J.
      apply dom_delta_subst in Hwfd.
      apply dom__ddom in H.     
      rewrite Hwfd in H. exact H.
    rewrite <- swap_subst_te_dsubst with (E:=E) (K:=k); auto.
    rewrite IHHwfd.
    rewrite swap_subst_te_rdsubst with (E:=E) (K:=k); auto.
    rewrite dsubst_te_head_opt; auto.
    apply wf_dsubst_styp_rev with (k:=k); auto.
        apply wf_delta_subst__wf_dsubst in Hwfd.
        apply wf_dsubst_rev; auto.

        apply dom_delta_subst in Hwfd.
        apply dom__ddom in H.     
         rewrite Hwfd in H.
         rewrite <- dom_rev; auto.
  return.
  end proof.
Qed.

Inductive wf_gsubst : gamma_subst -> Prop :=
  | wf_gsubst_empty :
      wf_gsubst gamma_nil
  | wf_gsubst_sval : forall SE x e T,
      wf_gsubst SE -> x `notin` dom SE -> typing nil nil e T ->
      wf_gsubst ([(x, e)] ++ SE)
  .

Tactic Notation "wf_gsubst_cases" tactic(first) tactic(c) :=
  first;
  [ c "wf_gsubst_empty" |
    c "wf_gsubst_sval"].

Hint Constructors wf_gsubst.

Lemma gsubst_nil_term :  forall gsubst x e gsubst',
   wf_gsubst (gsubst'++[(x, e)]++gsubst) ->
  exists t, typing nil nil e t.
Proof.
  intros gsubst x e gsubst' Hwf_gsubst.
  remember (gsubst'++[(x, e)]++gsubst) as Gsubst.
  generalize dependent gsubst'.
  (wf_gsubst_cases (induction Hwf_gsubst) Case); 
    intros gsubst' HeqGsubst.
  Case "wf_gsubst_empty".
    contradict HeqGsubst; auto.    
  Case "wf_gsubst_sval".
    destruct (one_eq_app _ _ _ _ _ HeqGsubst) as [[gsubst'' [GEQ1 GEQ2]] | [GEQ1 GEQ2]]; subst.
    SCase "exists GS'',GS'=GS&x0'' /\ GS0=GS&x&GS'' ".
      destruct IHHwf_gsubst with (gsubst':=gsubst'') as [t J]; auto.
      exists t. exact J.
    SCase "GS'=nil /\ GS&x = GS0&x0 ".
      inversion GEQ2. subst.
      exists T. exact H0.
Qed.

Lemma gsubst_opt :  forall gsubst x e e' gsubst',
   wf_gsubst (gsubst'++[(x, e)]++gsubst) ->
   apply_gamma_subst (gsubst'++[(x, e)]++gsubst) e' =
     apply_gamma_subst (gsubst'++gsubst) (subst_ee x e e').
Proof.
  intros gsubst x e e' gsubst' Hwf_gsubst.
  remember (gsubst'++[(x, e)]++gsubst) as Gsubst.
  generalize dependent e'.
  generalize dependent gsubst'.
  (wf_gsubst_cases (induction Hwf_gsubst) Case); 
    intros gsubst' HeqGsubst e'.
  Case "wf_gsubst_empty".
    contradict HeqGsubst; auto.    
  Case "wf_gsubst_sval".
    destruct (one_eq_app _ _ _ _ _ HeqGsubst) as [[gsubst'' [GEQ1 GEQ2]] | [GEQ1 GEQ2]]; subst.
    SCase "exists GS'',GS'=GS&x0'' /\ GS0=GS&x&GS'' ".
        simpl. simpl_env. 
        apply gsubst_nil_term in Hwf_gsubst.
        destruct Hwf_gsubst as [t Typing].
        rewrite <- subst_ee_commute; auto.
          apply notin_fv_ee_typing with (y:=x0) in H0; auto.
          apply notin_fv_ee_typing with (y:=x0) in Typing; auto.

          apply notin_fv_ee_typing with (y:=x) in H0; auto.
          apply notin_fv_ee_typing with (y:=x) in Typing; auto.
    SCase "GS'=nil /\ GS&x = GS0&x0 ".
        inversion GEQ2. subst.
        simpl_env in *. destruct_notin.
        auto.
Qed.

Lemma gsubst_head_opt :  forall gsubst x e e',
   wf_gsubst (gsubst++[(x, e)]) ->
   apply_gamma_subst (gsubst++[(x, e)]) e' =
     apply_gamma_subst gsubst (subst_ee x e e').
Proof.
  intros gsubst x e e' Hwfg.
  rewrite_env (gsubst++nil).
  rewrite_env (gsubst++[(x, e)]++nil).
  apply gsubst_opt; auto.
Qed.

Lemma wf_gamma_subst__wf_gsubst : forall E dsubst gsubst,
  wf_gamma_subst E dsubst gsubst ->
  wf_gsubst gsubst.
Proof.
  intros E dsubst gsubst Hwfg.
  (wf_gamma_subst_cases (induction Hwfg) Case); auto.
  Case "wf_gamma_subst_sval".
    apply wf_gsubst_sval with (T:=apply_delta_subst_typ dsE T); auto.
      apply dom_gamma_subst in Hwfg. destruct Hwfg as [J1 J2].
      rewrite <- J2.
      apply dom__gdom; auto.
Qed.

Lemma wf_gsubst_sval_rev : forall SE x e T,
  wf_gsubst SE -> x `notin` dom SE -> typing nil nil e T ->
  wf_gsubst (SE++[(x, e)]).
Proof.
  intros SE x e T Wfg.
  generalize dependent x.
  generalize dependent e.
  generalize dependent T.
  induction Wfg; intros; auto.
    rewrite_env ([(x, e)]++gamma_nil).
    apply wf_gsubst_sval with (T:=T); auto.

    simpl_env.
    apply wf_gsubst_sval with (T:=T); auto.
    apply IHWfg with (T:=T0); auto.
Qed.

Lemma wf_gsubst_rev : forall E,
  wf_gsubst E ->
  wf_gsubst (rev E).
Proof.
  intros E Wfg.
  induction Wfg; intros; auto.
    simpl. simpl_env.
    apply wf_gsubst_sval_rev with (T:=T); auto.
      rewrite <- dom_rev; auto.
Qed.

Lemma swap_subst_ee_rgsubst: forall e' x E dsubst gsubst e t,
  wf_gamma_subst E dsubst gsubst ->
  typing nil nil e' t ->
  x `notin` dom gsubst ->
  subst_ee x e' (apply_gamma_subst (rev gsubst) e) =
  apply_gamma_subst (rev gsubst) (subst_ee x e' e).
Proof.
  intros e' x E dsubst gsubst e t Hwfg Typing xngsubst.
  generalize dependent e.
  generalize dependent e'.
  generalize dependent t.
  induction Hwfg; intros t e' Typing e0; simpl; eauto.
    simpl_env in*. destruct_notin.
    assert (J:=Hwfg).
    apply wf_gamma_subst__wf_gsubst in Hwfg.
    apply wf_gsubst_rev in Hwfg.
    apply dom_gamma_subst in J. destruct J as [J1 J2].
    apply wf_gsubst_sval_rev with (x:=x0) (e:=e) (T:=apply_delta_subst_typ dsE T) in Hwfg; auto.
      rewrite gsubst_head_opt; auto.
      rewrite gsubst_head_opt; auto.
      rewrite IHHwfg with (t:=t); auto.
      rewrite subst_ee_commute; eauto.
        apply notin_fv_ee_typing with (y:=x0) in H0; auto.
        apply notin_fv_ee_typing with (y:=x0) in Typing; auto.

        apply notin_fv_ee_typing with (y:=x) in H0; auto.
        apply notin_fv_ee_typing with (y:=x) in Typing; auto.
 
     apply dom__gdom in H.     
      rewrite J2 in H.
      rewrite <- dom_rev; auto.
Qed.

Lemma swap_subst_ee_gsubst': forall e' x E dsubst gsubst e t,
  wf_gamma_subst E dsubst gsubst ->
  typing nil nil e' t ->
  x `notin` dom gsubst ->
  subst_ee x e' (apply_gamma_subst gsubst e) =
  apply_gamma_subst gsubst (subst_ee x e' e).
Proof.
  intros e' x E dsubst gsubst e t Hwfg Hwft xngsubst.
  generalize dependent e.
  generalize dependent e'.
  generalize dependent t.
  induction Hwfg; intros t e' Hwft e0; simpl; eauto.
    rewrite subst_ee_commute; eauto.
      eauto using typing_fv.
      eauto using typing_fv.
Qed.

Lemma apply_gamma_subst_rev : forall E dsubst gsubst e,
  wf_gamma_subst E dsubst gsubst ->
  apply_gamma_subst gsubst e = apply_gamma_subst (rev gsubst) e.
proof.
  let E, dsubst, gsubst, e:exp be such that Hwfg:(wf_gamma_subst E dsubst gsubst). 
  escape.
  generalize dependent e.
  induction Hwfg; intro e0; simpl; simpl_env; auto.
    assert (x `notin` dom gsE) as J.
       apply dom_gamma_subst in Hwfg.
       destruct Hwfg as [J1 J2].
       apply dom__gdom in H.     
        rewrite J2 in H. exact H.
    rewrite <- swap_subst_ee_gsubst' with (E:=E) (dsubst:=dsE) (t:=apply_delta_subst_typ dsE T); auto.
    rewrite IHHwfg.
    rewrite swap_subst_ee_rgsubst with (E:=E) (dsubst:=dsE) (t:=apply_delta_subst_typ dsE T); auto.
    rewrite gsubst_head_opt; auto.
    apply wf_gsubst_sval_rev with (T:=apply_delta_subst_typ dsE T); auto.
       apply wf_gamma_subst__wf_gsubst in Hwfg.
       apply wf_gsubst_rev; auto.

       apply dom_gamma_subst in Hwfg.
       destruct Hwfg as [J1 J2].
       apply dom__gdom in H.     
        rewrite J2 in H. 
        rewrite <- dom_rev; auto.
  return.
  end proof.
Qed.

Lemma wf_lgamma_subst__wf_gsubst : forall E D dsubst gsubst lgsubst,
  wf_lgamma_subst E D dsubst gsubst lgsubst->
  wf_gsubst gsubst.
Proof.
  intros E D dsubst gsubst lgsubst Hwflg.
  (wf_lgamma_subst_cases (induction Hwflg) Case); auto.
  Case "wf_lgamma_subst_sval".
    apply wf_gsubst_sval with (T:=apply_delta_subst_typ dsE T); auto.
      apply dom_lgamma_subst in Hwflg. destruct Hwflg as [J1 [J2 J3]].
      rewrite <- J2.
      apply dom__gdom; auto.
Qed.

Lemma wf_lgamma_subst__wf_lgsubst : forall E D dsubst gsubst lgsubst,
  wf_lgamma_subst E D dsubst gsubst lgsubst->
  wf_gsubst lgsubst.
Proof.
  intros E D dsubst gsubst lgsubst Hwflg.
  (wf_lgamma_subst_cases (induction Hwflg) Case); auto.
  Case "wf_lgamma_subst_slval".
    apply wf_gsubst_sval with (T:=apply_delta_subst_typ dsE T); auto.
      apply dom_lgamma_subst in Hwflg. destruct Hwflg as [J1 [J2 J3]].
      rewrite <- J3. exact H0.
Qed.

Lemma swap_subst_ee_rlgsubst: forall e' x E D dsubst gsubst lgsubst e t,
  wf_lgamma_subst E D dsubst gsubst lgsubst ->
  typing nil nil e' t ->
  x `notin` dom lgsubst ->
  subst_ee x e' (apply_gamma_subst (rev lgsubst) e) =
  apply_gamma_subst (rev lgsubst) (subst_ee x e' e).
Proof.
  intros e' x E D dsubst gsubst lgsubst e t Hwflg Typing xngsubst.
  generalize dependent e.
  generalize dependent e'.
  generalize dependent t.
  induction Hwflg; intros t e' Typing e0; simpl; eauto.
    simpl_env in*. destruct_notin.
    assert (J:=Hwflg).
    apply wf_lgamma_subst__wf_lgsubst in Hwflg.
    apply wf_gsubst_rev in Hwflg.
    apply dom_lgamma_subst in J. destruct J as [J1 [J2 J3]].
    apply wf_gsubst_sval_rev with (x:=x0) (e:=e) (T:=apply_delta_subst_typ dsE T) in Hwflg; auto.
      rewrite gsubst_head_opt; auto.
      rewrite gsubst_head_opt; auto.
      rewrite IHHwflg with (t:=t); auto.
      rewrite subst_ee_commute; eauto.
        apply notin_fv_ee_typing with (y:=x0) in H1; auto.
        apply notin_fv_ee_typing with (y:=x0) in Typing; auto.

        apply notin_fv_ee_typing with (y:=x) in H1; auto.
        apply notin_fv_ee_typing with (y:=x) in Typing; auto.
 
      rewrite J3 in H0.
      rewrite <- dom_rev; auto.
Qed.

Lemma apply_lgamma_subst_rev : forall E lE dsubst gsubst lgsubst e,
  wf_lgamma_subst E lE dsubst gsubst lgsubst ->
  apply_gamma_subst lgsubst e = apply_gamma_subst (rev lgsubst) e.
proof.
  let E, lE, dsubst, gsubst, lgsubst, e:exp be such that Hwflg:(wf_lgamma_subst E lE dsubst gsubst lgsubst). 
  escape.
  generalize dependent e.
  induction Hwflg; intro e0; simpl; simpl_env; auto.
    assert (x `notin` dom lgsE) as J.
       apply dom_lgamma_subst in Hwflg.
       destruct Hwflg as [J1 [J2 J3]].
        rewrite J3 in H0. exact H0.
    rewrite <- swap_subst_ee_lgsubst with (E:=E) (dsubst:=dsE) (t:=apply_delta_subst_typ dsE T) (D:=lE) (gsubst:=gsE); auto.
    rewrite IHHwflg.
    rewrite swap_subst_ee_rlgsubst with (E:=E) (dsubst:=dsE) (t:=apply_delta_subst_typ dsE T) (D:=lE) (gsubst:=gsE); auto.
    rewrite gsubst_head_opt; auto.
    apply wf_gsubst_sval_rev with (T:=apply_delta_subst_typ dsE T); auto.
       apply wf_lgamma_subst__wf_lgsubst in Hwflg.
       apply wf_gsubst_rev; auto.

       apply dom_lgamma_subst in Hwflg.
       destruct Hwflg as [J1 [J2 J3]].
        rewrite J3 in H0. 
        rewrite <- dom_rev; auto.
  return.
  end proof.
Qed.

Lemma remove_typvar_single_inv : forall E a T,
  remove_typvar E = [(a, bind_typ T)] ->
  exists E1, exists E2,
    E = E1 ++ [(a, bind_typ T)] ++ E2 /\ remove_typvar E1 = nil /\ remove_typvar E2 = nil.
Proof.
  induction E; intros x T H.
    simpl in H.
    inversion H.

    destruct a.
    destruct b; simpl in *; simpl_env in *.
      apply IHE in H.
      destruct H as [E1 [E2 [J1 [J2 J3]]]]; subst.
      exists ([(a, bind_kn k)]++E1). exists E2. 
      split; auto.

      inversion H; subst.     
      exists nil. exists E. auto. 
Qed.  

Lemma apply_delta_subst_env_nil_inv : forall E dsubst,
  apply_delta_subst_env dsubst E =  nil ->
  E = nil.
Proof.
  induction E; intros dsubst H; auto.
  destruct a.
  destruct b; simpl in H.
     inversion H.
     inversion H.
Qed.

Lemma apply_delta_subst_env_single_inv : forall E dsubst a T,
  apply_delta_subst_env dsubst E = [(a, bind_typ T)] ->
  exists T',
    E = [(a, bind_typ T')] /\ apply_delta_subst_typ dsubst T' = T.
Proof.
  induction E; intros dsubst x T H.
    simpl in H.
    inversion H.

    destruct a.
    destruct b; simpl in *; simpl_env in *.
      inversion H; subst.     

      inversion H; subst.     
      apply apply_delta_subst_env_nil_inv in H3.
      subst.
      exists t. split; auto.
Qed.  

Lemma remove_typvar_app : forall E E',
  remove_typvar (E ++ E') = remove_typvar E ++ remove_typvar E'.
Proof.
  induction E; intros E'; simpl; auto.
    destruct a.
    destruct b; auto.
      rewrite IHE. auto.
Qed.

Lemma _from_subst_to_ctx_app : forall gsubst' dsubst' dsubst E' E lE t t' C,
  wf_delta_subst (remove_tmvar E') dsubst' ->
  wf_delta_subst (remove_tmvar E) dsubst ->
  wf_gamma_subst (apply_delta_subst_env (dsubst'++dsubst) (remove_typvar E')) nil (rev gsubst') ->
  contexting (E'++E) lE t C nil nil (gen_typ_abs (apply_delta_subst_env (rev (dsubst'++dsubst)) (E'++E)) (apply_delta_subst_typ (rev (dsubst'++dsubst)) t')) ->
  contexting (E'++E) lE t (gen_ctx_app gsubst' C) nil nil (gen_typ_abs (apply_delta_subst_env (rev (dsubst'++dsubst)) E) (apply_delta_subst_typ (rev (dsubst'++dsubst)) t')).
Proof.
  induction gsubst'; intros dsubst' dsubst E' E lE t t' C Hwfd' Hwfd Hwfg Hctx; simpl.
    simpl in Hwfg.
    apply wf_gsubst_nil_gsubst in Hwfg.
    rewrite apply_delta_subst_env_app in Hctx.
    rewrite gen_typ_abs_app in Hctx.
    rewrite gen_typ_abs_id in Hctx; auto.
    rewrite <- apply_delta_subst_env_gdom in Hwfg.
    rewrite <- apply_delta_subst_env_gdom.
    rewrite gdom_env_remove_typvar in Hwfg; auto.

    destruct a. simpl in Hwfg. simpl_env in Hwfg.
    apply wf_gsubst_gapp_inv in Hwfg; 
      try solve [auto | rewrite <- apply_delta_subst_env_ddom; auto using ddom_env_remove_typvar].
    destruct Hwfg as [E1 [E2 [EQ1 [EQ2 [EQ3 [Hwfg1 Hwfg2]]]]]]; subst.
    rewrite apply_delta_subst_env_remove_typvar_commut in EQ1.
    apply remove_typvar_app_inv in EQ1.
    destruct EQ1 as [E1' [E2' [EQ' [EQ2' EQ3']]]]; subst.
    apply apply_delta_subst_env_app_inv in EQ'.
    destruct EQ' as [E1'0 [E2'0 [EQ5 [EQ6 EQ7]]]]; subst.
    rewrite_env (E1'0++(E2'0++E)) in Hctx.
    rewrite remove_tmvar_app in Hwfd'.
    assert (gdom_env (remove_tmvar E1'0 ++ remove_tmvar E2'0) [=] {}) as EQ.
      rewrite <- remove_tmvar_app.
      apply gdom_env_remove_tmvar; auto.
    assert (EQ5:=Hwfd').
    apply wf_dsubst_app_inv' in EQ5; auto.
    destruct EQ5 as [dsubst1'0 [dsubst2'0 [EQ5 [EQ6 [EQ7 [Hwfd'2 Hwfd'1]]]]]]; subst.
    rewrite <- apply_delta_subst_env_remove_typvar_commut in Hwfg2.
    assert (wf_delta_subst (remove_tmvar (E2'0++E)) (dsubst2'0++dsubst)) as Hwfd0.
      rewrite remove_tmvar_app.
      apply wf_dsubst_app_merge; auto.
        apply contexting_regular in Hctx.
        decompose [and] Hctx. clear - H.
        apply wfe_remove_tmvar in H; auto.
         rewrite remove_tmvar_app in H.
         rewrite remove_tmvar_app in H.
         rewrite_env (nil ++ remove_tmvar E1'0 ++ remove_tmvar E2'0 ++ remove_tmvar E) in H.
        apply wf_env_strengthening_nilgdom in H; auto.
    simpl_env in Hctx. simpl_env in Hwfg2.
    apply IHgsubst' with (dsubst':=dsubst1'0) in Hctx; auto.
    rewrite apply_delta_subst_env_app in Hctx.
    rewrite gen_typ_abs_app in Hctx.
    rewrite <- apply_delta_subst_env_remove_typvar_commut in Hwfg1.
    assert (J:=Hwfg1).
    apply wf_gsubst_single_inv in J.
    destruct J as [E1 [E2 [T [EQ4 Htyping]]]]; subst.
    assert (exists E21', exists E22', exists T',
                       E2'0 = E21' ++ [(a, bind_typ T')]++E22' /\
                       T = apply_delta_subst_typ (dsubst1'0++dsubst2'0++dsubst) T' /\
                       apply_delta_subst_env (dsubst1'0++dsubst2'0++dsubst) (remove_typvar E21') = E1 /\
                       apply_delta_subst_env (dsubst1'0++dsubst2'0++dsubst) (remove_typvar E22') = E2
                   ) as EQ'.
      clear - EQ4. simpl_env in EQ4.
      assert (J:=EQ4).
       rewrite apply_delta_subst_env_remove_typvar_commut in EQ4.
      apply remove_typvar_app_inv in EQ4.
      destruct EQ4 as [F1 [F2 [J1 [J2 J3]]]].
      apply remove_typvar_app_inv in J3.
      destruct J3 as [F3 [F4 [J4 [J5 J6]]]].
      subst.
      apply remove_typvar_single_inv in J5.
      destruct J5 as [F5 [F6 [J3 [J4 J5]]]]; subst.
      apply apply_delta_subst_env_app_inv in J1.
      destruct J1 as [F7 [F8 [J7 [J8 J9]]]]; subst.
      apply apply_delta_subst_env_app_inv in J9.
      destruct J9 as [F9 [F10 [J10 [J11 J12]]]]; subst.
      apply apply_delta_subst_env_app_inv in J11.
      destruct J11 as [F11 [F12 [J13 [J14 J15]]]]; subst.
      apply apply_delta_subst_env_app_inv in J15.
      destruct J15 as [F13 [F14 [J16 [J17 J18]]]]; subst.
      apply apply_delta_subst_env_single_inv in J17.
      destruct J17 as [T' [J19 J20]]; subst.
      exists (F7++F11). exists (F14++F10). exists T'.
      simpl_env. split; auto.  split; auto.
      rewrite <- apply_delta_subst_env_remove_typvar_commut.
      rewrite <- apply_delta_subst_env_remove_typvar_commut.
      rewrite remove_typvar_app.
      rewrite remove_typvar_app.
      rewrite apply_delta_subst_env_app.
      rewrite apply_delta_subst_env_app.
      rewrite <- apply_delta_subst_env_remove_typvar_commut in J4.
      rewrite J4.
      rewrite <- apply_delta_subst_env_remove_typvar_commut in J5.
      rewrite J5.
      split; auto.
    destruct EQ' as [E21' [E22' [T' [EQ8 [EQ9 [EQ10 EQ11]]]]]]; subst.     
    apply contexting_app1 with (K:=kn_lin) (D1':=nil) (D2':=nil)(T1':=apply_delta_subst_typ (rev (dsubst1'0++dsubst2'0++dsubst)) T'); auto.
      rewrite distr_rev in Hctx.
      rewrite distr_rev in Hctx.
      simpl_env in Hctx.
      rewrite apply_delta_subst_env_app in Hctx.
      rewrite apply_delta_subst_env_app in Hctx.
      simpl in Hctx.
      simpl_env in Hctx.
      rewrite <- distr_rev in Hctx.
      rewrite <- distr_rev in Hctx.
      simpl_env.
      rewrite gen_typ_abs_opt in Hctx; auto.
        simpl_env in Hctx. auto.

        assert (uniq (E21'++[(a, bind_typ T')]++E22')) as Uniq.
          apply contexting_regular in Hctx.
          decompose [and] Hctx.
          apply uniq_from_wf_env in H.
          clear - H. solve_uniq.
        apply apply_delta_subst_env_uniq with (dsubst:=(rev ((dsubst1'0++dsubst2'0)++dsubst))) in Uniq; auto.
        rewrite apply_delta_subst_env_app in Uniq.
        rewrite apply_delta_subst_env_app in Uniq; assumption.

        simpl_env. simpl.
        rewrite <- apply_delta_subst_env_gdom.
        rewrite <- apply_delta_subst_env_gdom.
        rewrite  gdom_env_remove_typvar in EQ2.
        rewrite <- apply_delta_subst_env_gdom in EQ2.
        simpl_env in EQ2. simpl in EQ2. rewrite EQ2. 
        clear. fsetdec.

      clear - Htyping Hwfd Hwfd' Hctx.  
      rewrite <- apply_delta_subst_typ_rev with (E:=(remove_tmvar E1'0++remove_tmvar (E21' ++ [(a, bind_typ T')] ++E22')) ++ remove_tmvar E); auto.
        rewrite_env ((dsubst1'0++dsubst2'0)++dsubst).
        apply wf_dsubst_app_merge; auto.
          apply contexting_regular in Hctx. decompose [and] Hctx. clear Hctx.
          apply wfe_remove_tmvar in H.      
          apply uniq_from_wf_env in H. clear - H.
          repeat (rewrite remove_tmvar_app).
          repeat (rewrite remove_tmvar_app in H). 
          simpl_env in H. simpl_env. auto.

      clear - Htyping.
      eapply empty_typing_disjdom; eauto.
Qed.

Lemma from_subst_to_ctx_app : forall E lE dsubst gsubst t t' C,
  wf_delta_subst (remove_tmvar E) dsubst ->
  wf_gamma_subst (apply_delta_subst_env dsubst (remove_typvar E)) nil (rev gsubst) ->
  contexting E lE t C nil nil (gen_typ_abs  (apply_delta_subst_env (rev dsubst) E)  (apply_delta_subst_typ (rev dsubst) t')) ->
  contexting E lE t (gen_ctx_app gsubst C) nil nil  (apply_delta_subst_typ (rev dsubst) t').
Proof.
  intros E lE dsubst gsubst t t' C Hwfd Hwfg Hctx.
  rewrite_env (E++nil).
  assert (gen_typ_abs (apply_delta_subst_env (rev (dsubst++nil)) nil) (apply_delta_subst_typ (rev (dsubst++nil)) t') = (apply_delta_subst_typ (rev dsubst) t')) as EQ.
    simpl. simpl_env. auto.
  rewrite <- EQ.
  apply _from_subst_to_ctx_app; simpl_env; auto.
Qed.

Lemma gen_typ_labs_app : forall lE lE' t,
  gen_typ_labs (lE ++ lE') t = gen_typ_labs lE (gen_typ_labs lE' t).
Proof.
  induction lE; intros lE' t; simpl; auto.
    destruct a.
    destruct l; rewrite IHlE; auto.
Qed.

Lemma gen_typ_labs_id : forall lE t,
  dom lE [=] {} ->
  gen_typ_labs lE t = t.
Proof.
  induction lE; intros t Heq; simpl; auto.
    destruct a.
    destruct l.
    simpl in Heq.
    assert (a `in` {}) as FALSE.
      rewrite <- Heq.
      auto.
    contradict FALSE; auto.
Qed.

Lemma wf_lgsubst_nil_lgsubst : forall lE E dsubst gsubst,
  wf_lgamma_subst E lE dsubst gsubst nil->
  dom lE [=] {}.
Proof.
  induction lE; intros E dsubst gsubst Wflg; auto.
    destruct a.
    destruct l; simpl.
    apply dom_lgamma_subst in Wflg.
    decompose [and] Wflg.
    simpl in H2. auto.
Qed.      

Lemma wf_lgamma_subst_strengthen_when_nillE : forall E lE dsubst gsubst lgsubst,
  wf_lgamma_subst E lE dsubst gsubst lgsubst ->
  wf_lgamma_subst E nil dsubst gsubst nil.
Proof.
  intros E lE dsubst gsubst lgsubst Hwflg.
  induction Hwflg; auto.
Qed.

Lemma wf_lgsubst_gapp_inv : forall lEE lgsubst' lgsubst,
  wf_lgamma_subst nil lEE nil nil (lgsubst'++lgsubst) ->
  exists lE', exists lE, 
    lEE = lE' ++ lE /\
    dom lE [=] dom lgsubst /\
    dom lE' [=] dom lgsubst' /\
    wf_lgamma_subst nil lE nil nil lgsubst /\
    wf_lgamma_subst nil lE' nil nil lgsubst'.
Proof.
  intros lEE lgsubst' lgsubst Wflg.
  remember (lgsubst'++lgsubst) as lgsE.
  generalize dependent lgsubst'.        
  generalize dependent lgsubst. 
  induction Wflg; intros; subst.
    symmetry in HeqlgsE.
    apply app_eq_nil in HeqlgsE.
    destruct HeqlgsE as [J1 J2]; subst.
    exists nil. exists nil. split; auto.

    assert (lgsubst'++lgsubst = lgsubst'++lgsubst) as EQ. auto.
    apply IHWflg in EQ.
    destruct EQ as [lE1 [lE2 [EQ1 [EQ2 [EQ3 [Wfg1 Wfg2]]]]]]; subst.
    exists lE1. exists lE2.
           split; auto.

    apply one_eq_app in HeqlgsE. destruct HeqlgsE as [[lgsE'' [lgsEQ1 lgsEQ2]] | [lgsEQ1 lgsEQ2]]; subst.
         assert (lgsE''++lgsubst = lgsE''++lgsubst) as EQ. auto.
         apply IHWflg in EQ.
           destruct EQ as [lE1 [lE2 [EQ1 [EQ2 [EQ3 [Wflg1 Wflg2]]]]]]; subst.
           exists ([(x, lbind_typ T)]++lE1). exists lE2.
           split; auto.
           split; auto.
           split; auto.
             simpl. rewrite EQ3. fsetdec.
           split; auto.
             simpl_env. apply wf_lgamma_subst_slval; auto.

         exists nil. exists ([(x, lbind_typ T)]++lE).
         split; auto.
         split.
           simpl_env. apply dom_lgamma_subst in Wflg.
           decompose [and] Wflg. rewrite H6. fsetdec.
         split; auto.
         split.
           simpl_env. apply wf_lgamma_subst_slval; auto.
           apply wf_lgamma_subst_strengthen_when_nillE in Wflg; auto.

    assert (lgsubst'++lgsubst = lgsubst'++lgsubst) as EQ. auto.
    apply IHWflg in EQ.
    destruct EQ as [lE1 [lE2 [EQ1 [EQ2 [EQ3 [Wfg1 Wfg2]]]]]]; subst.
    exists lE1. exists lE2.
           split; auto.
Qed.

Lemma gen_typ_labs_opt : forall lE1 x t0 lE2 t,
  uniq (lE1++[(x, lbind_typ t0)]++lE2) ->
  dom (lE1++[(x, lbind_typ t0)]++lE2) [=] {{x}} -> 
  gen_typ_labs (lE1++[(x, lbind_typ t0)]++lE2) t = typ_arrow kn_lin t0 t.
Proof.
  induction lE1; intros x t0 lE2 t Uniq Hdom.
    simpl in *.
    simpl_env in Uniq. inversion Uniq; subst.
    rewrite gen_typ_labs_id; auto.
      clear - Hdom H3. fsetdec.
    
    destruct a.
    destruct l; simpl in *.
      simpl_env in Hdom.
      assert (a <> x) as anx.
        simpl_env in Uniq. clear - Uniq. solve_uniq.
      assert (a `in` {{x}}) as aisx.
        rewrite <- Hdom.
        auto.
      contradict aisx; auto.
Qed.

Lemma wf_lgsubst_single_inv : forall lE x v,
  wf_lgamma_subst nil lE nil nil [(x, v)] ->
  exists lE1, exists lE2, exists t,
    lE = lE1 ++ [(x, lbind_typ t)] ++ lE2 /\
    typing nil nil v t.
Proof.
  induction lE; intros x v Hwflg.
    inversion Hwflg.

    destruct a.
    destruct l; simpl_env in *.
      inversion Hwflg; subst.     
      exists nil. exists lE. exists t. split; auto. 
Qed.

Lemma apply_delta_subst_lenv_app_inv : forall lE dsubst lE1 lE2,
  apply_delta_subst_lenv dsubst lE = lE1 ++ lE2 ->
  exists lE1', exists lE2',
    lE = lE1' ++ lE2' /\
    apply_delta_subst_lenv dsubst lE1' = lE1 /\
    apply_delta_subst_lenv dsubst lE2' = lE2.
Proof.
  induction lE; intros dsubst lE1 lE2 H.
    simpl in H.
    symmetry in H.
    apply app_eq_nil in H.
    destruct H as [J1 J2]; subst.
    exists nil. exists nil. split; auto.

    simpl in H.
    destruct a.
    destruct l.
      simpl_env in H.
      apply one_eq_app in H. destruct H as [[lE'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
        apply IHlE in EQ2. 
        destruct EQ2 as [lE1' [lE2' [EQ1 [H1 H2]]]]; subst.
        exists ([(a, lbind_typ t)]++lE1'). exists lE2'.
        split; auto.

        exists nil. exists ((a, lbind_typ t)::lE).
        split; auto.
Qed.

Lemma apply_delta_subst_lenv_app : forall lE lE' dsubst,
  apply_delta_subst_lenv dsubst (lE ++ lE') = 
    apply_delta_subst_lenv dsubst lE ++ apply_delta_subst_lenv dsubst lE'.
Proof.
  induction lE; intros lE' dsubst; simpl; auto.
    destruct a.
    destruct l; rewrite IHlE; auto.
Qed.

Lemma apply_delta_subst_lenv_uniq : forall E dsubst,
  uniq E ->
  uniq (apply_delta_subst_lenv dsubst E).
Proof.
  induction E; intros dsubst Uniq; simpl; auto.
    destruct a.
    destruct l.
      inversion Uniq; subst.
      simpl_env.
      apply uniq_push; auto.
        rewrite <- apply_delta_subst_lenv_dom; auto.
Qed.

Lemma apply_delta_subst_lenv_nil_inv : forall lE dsubst,
  apply_delta_subst_lenv dsubst lE =  nil ->
  lE = nil.
Proof.
  induction lE; intros dsubst H; auto.
  destruct a.
  destruct l; simpl in H.
     inversion H.
Qed.

Lemma apply_delta_subst_lenv_single_inv : forall E dsubst a T,
  apply_delta_subst_lenv dsubst E = [(a, lbind_typ T)] ->
  exists T',
    E = [(a, lbind_typ T')] /\ apply_delta_subst_typ dsubst T' = T.
Proof.
  induction E; intros dsubst x T H.
    simpl in H.
    inversion H.

    destruct a.
    destruct l; simpl in *; simpl_env in *.
      inversion H; subst.     
      apply apply_delta_subst_lenv_nil_inv in H3.
      subst.
      exists t. split; auto.
Qed.  

Lemma _from_subst_to_ctx_lapp : forall lgsubst' dsubst E lE' lE t t' C,
  wf_delta_subst (remove_tmvar E) dsubst ->
  wf_lgamma_subst nil (apply_delta_subst_lenv dsubst lE') nil nil (rev lgsubst') ->
  contexting E (lE'++lE) t C nil nil (gen_typ_labs (apply_delta_subst_lenv (rev dsubst) (lE'++lE)) (apply_delta_subst_typ (rev dsubst) t')) ->
  contexting E (lE'++lE) t (gen_ctx_lapp lgsubst' C) nil nil (gen_typ_labs (apply_delta_subst_lenv (rev dsubst) lE) (apply_delta_subst_typ (rev dsubst) t')).
Proof.
  induction lgsubst'; intros dsubst E lE' lE t t' C Hwfd Hwflg' Hctx; simpl.
    simpl in Hwflg'.
    apply wf_lgsubst_nil_lgsubst in Hwflg'.
    rewrite apply_delta_subst_lenv_app in Hctx.
    rewrite gen_typ_labs_app in Hctx.
    rewrite gen_typ_labs_id in Hctx; auto.
    rewrite <- apply_delta_subst_lenv_dom in Hwflg'.
    rewrite <- apply_delta_subst_lenv_dom; auto.

    destruct a. simpl in Hwflg'. simpl_env in Hwflg'.
    apply wf_lgsubst_gapp_inv in Hwflg'; 
      try solve [auto | rewrite <- apply_delta_subst_lenv_dom; auto].
    destruct Hwflg' as [lE1 [lE2 [EQ1 [EQ2 [EQ3 [Hwflg1' Hwflg2']]]]]]; subst.
    apply apply_delta_subst_lenv_app_inv in EQ1.
    destruct EQ1 as [lE1'0 [lE2'0 [EQ5 [EQ6 EQ7]]]]; subst.
    simpl_env in Hctx.
    apply IHlgsubst' with (dsubst:=dsubst) in Hctx; auto.
    rewrite apply_delta_subst_lenv_app in Hctx.
    rewrite gen_typ_labs_app in Hctx.
    assert (J:=Hwflg1').
    apply wf_lgsubst_single_inv in J.
    destruct J as [E1 [E2 [T [EQ4 Htyping]]]]; subst.
    assert (exists lE21', exists lE22', exists T',
                       lE2'0 = lE21' ++ [(a, lbind_typ T')]++lE22' /\
                       T = apply_delta_subst_typ dsubst T' /\
                       apply_delta_subst_lenv dsubst lE21' = E1 /\
                       apply_delta_subst_lenv dsubst lE22' = E2
                   ) as EQ'. 
      clear - EQ4. simpl_env in EQ4.
      assert (J:=EQ4).
      apply apply_delta_subst_lenv_app_inv in EQ4.
      destruct EQ4 as [F7 [F8 [J7 [J8 J9]]]]; subst.
      apply apply_delta_subst_lenv_app_inv in J9.
      destruct J9 as [F9 [F10 [J10 [J11 J12]]]]; subst.
      apply apply_delta_subst_lenv_single_inv in J11.
      destruct J11 as [T' [J19 J20]]; subst.
      exists (F7). exists (F10). exists T'.
      simpl_env. split; auto. 
    destruct EQ' as [lE21' [lE22' [T' [EQ8 [EQ9 [EQ10 EQ11]]]]]]; subst.     
    apply contexting_app1 with (K:=kn_lin) (D1':=nil) (D2':=nil)(T1':=apply_delta_subst_typ (rev dsubst) T'); auto.
      simpl_env in Hctx.
      rewrite apply_delta_subst_lenv_app in Hctx.
      rewrite apply_delta_subst_lenv_app in Hctx.
      simpl in Hctx.
      simpl_env in Hctx.
      simpl_env.
      rewrite gen_typ_labs_opt in Hctx; auto.
        simpl_env in Hctx. auto.
     
        assert (uniq (lE21'++[(a, lbind_typ T')]++lE22')) as Uniq.
          apply contexting_regular in Hctx.
          decompose [and] Hctx.
          apply uniq_from_wf_lenv in H1.
          clear - H1. solve_uniq.
        apply apply_delta_subst_lenv_uniq with (dsubst:=(rev dsubst)) in Uniq; auto.
        rewrite apply_delta_subst_lenv_app in Uniq.
        rewrite apply_delta_subst_lenv_app in Uniq; assumption.

        simpl_env. simpl.
        rewrite <- apply_delta_subst_lenv_dom.
        rewrite <- apply_delta_subst_lenv_dom.
        rewrite <- apply_delta_subst_lenv_dom in EQ2.
        simpl_env in EQ2. simpl in EQ2. rewrite EQ2. 
        clear. fsetdec.

      clear - Htyping Hwfd.  
      rewrite <- apply_delta_subst_typ_rev with (E:=remove_tmvar E); auto.

      clear - Htyping.
      eapply empty_typing_disjdom; eauto.
Qed.

Lemma from_subst_to_ctx_lapp : forall E lE dsubst lgsubst t t' C,
  wf_delta_subst (remove_tmvar E) dsubst ->
  wf_lgamma_subst nil (apply_delta_subst_lenv dsubst lE) nil nil (rev lgsubst) ->
  contexting E lE t C nil nil  (gen_typ_labs (apply_delta_subst_lenv (rev dsubst) lE) (apply_delta_subst_typ (rev dsubst) t')) ->
  contexting E lE t (gen_ctx_lapp lgsubst C) nil nil (apply_delta_subst_typ (rev dsubst) t').
Proof.
  intros E lE dsubst lgsubst t t' C Hwfd Hwfg Hctx.
  rewrite_env (lE++nil).
  assert (gen_typ_labs (apply_delta_subst_lenv (rev dsubst) nil) (apply_delta_subst_typ (rev dsubst) t') = (apply_delta_subst_typ (rev dsubst) t')) as EQ.
    simpl. auto.
  rewrite <- EQ.
  apply _from_subst_to_ctx_lapp; simpl_env; auto.
Qed.

Lemma dom_ddom_remove_tmvar : forall E,
  dom (remove_tmvar E) [=] ddom_env (remove_tmvar E).
Proof.
  induction E; simpl; auto.
    destruct a.
    destruct b; simpl; auto.
      fsetdec.
Qed.

Lemma wf_delta_subst__remove_tmvar : forall E dsubst,
  wf_delta_subst E dsubst ->
  wf_delta_subst (remove_tmvar E) dsubst.
Proof.
  induction 1; simpl; simpl_env; auto.
    apply wf_delta_subst_styp; auto.
      rewrite dom_ddom_remove_tmvar.
      rewrite ddom_env_remove_tmvar.
      apply dom__ddom; auto.      
Qed.

Lemma notin_remove_typvar_dom : forall x E,
  x `notin` dom E ->
  x `notin` dom (remove_typvar E).
Proof.
  intros x.
  induction E; intros; simpl; auto.
    destruct a.
    simpl_env in H.
    destruct_notin.
    destruct b; simpl; auto.
Qed.

Lemma wf_gamma_subst__wf_subst : forall E dsubst gsubst,
  wf_gamma_subst E dsubst gsubst -> wf_delta_subst E dsubst /\ wf_env E.
intros.
  induction H; auto.
    destruct IHwf_gamma_subst.
    split; auto.

    destruct IHwf_gamma_subst.
    split; auto.
Qed.

Lemma wf_gamma_subst__remove_typvar : forall E dsubst gsubst,
  wf_gamma_subst E dsubst gsubst ->
  wf_gamma_subst (apply_delta_subst_env dsubst (remove_typvar E)) nil gsubst.
Proof.
  intros E dsubst gsubst Hwfg.
  induction Hwfg; simpl; simpl_env; auto.
    apply wf_gamma_subst_sval; auto.
      apply notin_remove_typvar_dom in H.
      rewrite <- apply_delta_subst_env_dom; auto.

      apply wft_subst with (dsubst:=dsE) in H1; auto.
        rewrite_env (apply_delta_subst_env dsE (remove_typvar E) ++ nil).
        apply wf_typ_weaken_head; auto.
          simpl_env.
          apply wf_gamma_subst__uniq in IHHwfg. decompose [and] IHHwfg; auto.

        apply wf_gamma_subst__wf_subst in Hwfg. destruct Hwfg as [J1 J2]. exact J1.
 
    rewrite apply_delta_subst_env_cons.
    rewrite apply_delta_subst_env_subst_tb_swap with (E:=E) (K:=k); auto.
      rewrite <- map_subst_tb_id; auto.
        apply wf_gamma_subst__wf_subst in IHHwfg. destruct IHHwfg as [J1 J2]. exact J2.

        apply notin_remove_typvar_dom in H.
        rewrite <- apply_delta_subst_env_dom; auto.

      apply wf_gamma_subst__wf_subst in Hwfg. destruct Hwfg as [J1 J2]. exact J1.
Qed.

Lemma apply_delta_subst_lenv_nil : forall lE,
  apply_delta_subst_lenv nil lE = lE.
Proof.
  induction lE; simpl; auto.
  destruct a.
  destruct l; simpl.
    rewrite IHlE; auto.
Qed.

Lemma apply_delta_subst_gen_typ_labs_commut : forall lE dsubst t,
  (gen_typ_labs (apply_delta_subst_lenv dsubst lE) (apply_delta_subst_typ dsubst t))
    = apply_delta_subst_typ dsubst (gen_typ_labs lE t).
Proof.  
  induction lE; intros dsubst t; simpl; simpl_env; auto.
    destruct a. destruct l. simpl.
    rewrite IHlE. simpl_commut_subst. auto.
Qed.

Lemma apply_delta_subst_gen_typ_abs_commut : forall E dsubst t,
  (gen_typ_abs (apply_delta_subst_env dsubst E) (apply_delta_subst_typ dsubst t))
    = apply_delta_subst_typ dsubst (gen_typ_abs E t).
Proof.  
  induction E; intros dsubst t; simpl; simpl_env; auto.
    destruct a.
    destruct b; simpl.
      rewrite IHE. simpl_commut_subst. auto.
      rewrite IHE. simpl_commut_subst. auto.
Qed.

Lemma apply_delta_subst_lenv_cons' : forall E X T dsubst,
  apply_delta_subst_lenv ([(X, T)]++dsubst) E = apply_delta_subst_lenv dsubst (map (subst_tlb X T) E).
Proof.
  induction E; intros X T dsubst; simpl; auto.
  destruct a.
  destruct l; simpl; simpl_env.
    rewrite IHE; auto.
Qed.

Lemma apply_delta_subst_lenv_subst_tlb_swap : forall F E dsubst X T K,
  wf_delta_subst E dsubst ->
  X `notin` dom E ->
  wf_typ empty T K ->
  apply_delta_subst_lenv dsubst (map (subst_tlb X T) F) =
    map (subst_tlb X T) (apply_delta_subst_lenv dsubst F).
Proof.
  induction F; intros E dsubst X T K Hwfd XnE Hwft; simpl; auto.
  destruct a.
  destruct l; simpl; simpl_env.
    rewrite delta_subst_permut with (dE:=E) (K:=K); auto.
      rewrite IHF with (E:=E) (K:=K); auto.
      apply dom_delta_subst in Hwfd. rewrite <- Hwfd. 
      apply dom__ddom in XnE. auto.
Qed.  

Lemma wf_lgamma_subst__remove_typvar : forall E lE dsubst gsubst lgsubst,
  wf_lgamma_subst E lE dsubst gsubst lgsubst->
  wf_lgamma_subst nil (apply_delta_subst_lenv dsubst lE) nil nil lgsubst.
Proof.
  intros E lE dsubst gsubst lgsubst Hwflg.
  induction Hwflg; simpl; simpl_env; auto.
    apply wf_lgamma_subst_slval; auto.
      apply notin_remove_typvar_dom in H.
      rewrite <- apply_delta_subst_lenv_dom; auto.

    rewrite apply_delta_subst_lenv_cons'.
    rewrite apply_delta_subst_lenv_subst_tlb_swap with (E:=E) (K:=k); auto.
      rewrite <- map_subst_tlb_id with (G:=nil); auto.
        apply wf_lgamma_subst__wf_lenv in IHHwflg. destruct IHHwflg as [J1 J2]. exact J2.

      apply wf_lgamma_subst__wf_subst in Hwflg. destruct Hwflg as [J1 J2]. exact J2.
Qed.


Lemma gen_typ_abs_type : forall E t,
  wf_env E ->
  type t ->
  type (gen_typ_abs E t).
Proof.
  intros E t Hwfe.
  generalize dependent t.
  induction Hwfe; intros e Htype; simpl; auto.
     apply type_arrow; auto.
       apply type_from_wf_typ in H; auto.
Qed.
    
Lemma gen_typ_labs_type : forall E lE t,
  wf_lenv E lE ->
  type t ->
  type (gen_typ_labs lE t).
Proof.
  intros E lE t Hwfle.
  generalize dependent t.
  induction Hwfle; intros e Htype; simpl; auto.
     apply type_arrow; auto.
       apply type_from_wf_typ in H1; auto.
Qed.

Lemma cv_ec_gen_ctx_labs : forall lE C,
  cv_ec (gen_ctx_labs lE C) [=] dom lE `union` cv_ec C.
Proof.
  induction lE; intro C; simpl.
    fsetdec.

    destruct a.
    destruct l; simpl. 
      rewrite <- cv_ec_close_ec.
      rewrite IHlE. fsetdec.
Qed.

Lemma gen_ctx_abs_capture_context : forall E C,
  wf_env E ->
  fv_ec C [=] {} ->
  context C ->
  context (gen_ctx_abs_capture E C).
Proof.
  intros E C Wfe Hfvc Hctx.
  generalize dependent C.
  induction Wfe; intros; simpl; simpl_env in *; auto.
      apply IHWfe in Hctx; simpl_env; auto.
        apply context_abs_capture with (L:={{x}} `union` dom E); auto.
          apply type_from_wf_typ in H; auto.

          intros x0 Hx0.
          rewrite close_open_ec__subst_ec; auto.
            apply subst_ec_context; auto.
Qed.

Lemma gen_ctx_labs_context : forall lE E,
  wf_lenv E lE ->
  context (gen_ctx_labs lE ctx_hole).
Proof.
  intros lE E Hwlenv.
  induction Hwlenv.
    simpl_env in *. apply context_hole; auto.

    simpl.
    apply context_abs_capture with (L:={{x}} `union` dom D); auto.
      apply type_from_wf_typ in H1; auto.

      intros x0 Hx0.
      rewrite close_open_ec__subst_ec; auto.
        apply subst_ec_context; auto.
Qed.

Lemma wf_from_subst_to_ctx : forall E lE dsubst gsubst lgsubst t K,
  wf_lgamma_subst E lE dsubst gsubst lgsubst ->
  wf_typ E t K ->
  contexting E lE t ( gen_ctx_lapp (rev lgsubst) (gen_ctx_app (rev gsubst) (gen_ctx_fst (gen_ctx_tapp (rev dsubst) (gen_ctx_tabs_capture E (gen_ctx_apair (gen_ctx_abs_capture E  (gen_ctx_labs lE ctx_hole)))))))) nil nil (apply_delta_subst_typ (rev dsubst) t).
Proof.
  intros E lE dsubst gsubst lgsubst t K Hwflg Hwft.
  apply from_subst_to_ctx_lapp with (dsubst:=dsubst); auto.
    apply wf_lgamma_subst__wf_subst in Hwflg. destruct Hwflg. 
    apply  wf_delta_subst__remove_tmvar; auto.

    rewrite rev_involutive. 
    apply wf_lgamma_subst__remove_typvar in Hwflg; auto.
  rewrite apply_delta_subst_gen_typ_labs_commut.
  apply from_subst_to_ctx_app with (dsubst:=dsubst); auto.
    apply wf_lgamma_subst__wf_subst in Hwflg. destruct Hwflg.
    apply  wf_delta_subst__remove_tmvar; auto.
 
    apply wf_lgamma_subst__wf_subst in Hwflg. destruct Hwflg.
    rewrite rev_involutive. 
    apply wf_gamma_subst__remove_typvar; auto.
  apply from_subst_to_ctx_fst with (t2':=Two); auto.  
  rewrite apply_delta_subst_gen_typ_abs_commut.
  assert (
    typ_with (apply_delta_subst_typ (rev dsubst) (gen_typ_abs E (gen_typ_labs lE t))) Two =
    apply_delta_subst_typ (rev dsubst) (typ_with (gen_typ_abs E (gen_typ_labs lE t)) Two)
    ) as EQ.
    simpl_commut_subst.
    rewrite delta_subst_closed_typ with (t:=Two) (K:=kn_nonlin); auto.
      apply wf_typ_Two.
  rewrite EQ. clear EQ.
  apply from_subst_to_ctx_tapp; auto.
    apply wf_lgamma_subst__wf_subst in Hwflg. destruct Hwflg. 
    rewrite rev_involutive.
    apply  wf_delta_subst__remove_tmvar; auto.

    apply wf_lgamma_subst__wf_lenv in Hwflg.
    destruct Hwflg as [J1 J2].
    apply type_with.
      apply gen_typ_abs_type; auto.
        apply gen_typ_labs_type with (E:=E); auto.
           apply type_from_wf_typ in Hwft; auto.
      apply type_Two.

  assert (J:=Hwflg).
  apply wf_lgamma_subst__uniq in Hwflg. 
  decompose [and] Hwflg; auto.
  apply wf_lgamma_subst__wf_lenv in J.
  decompose [and] J; auto.
  unfold gen_ctx_apair.
  apply from_subst_to_ctx_tabs_capture; simpl; auto.
    apply cv_tc_gen_ctx_abs_capture.
    apply cv_tc_gen_ctx_labs.

    unfold gen_ctx_apair. simpl.
    rewrite cv_ec_gen_ctx_abs_capture.
    rewrite cv_ec_gen_ctx_labs.
    simpl. fsetdec.

    apply vcontext_apair1.
    apply context_apair1; auto.
      apply gen_ctx_abs_capture_context; auto.
        apply fv_ec_gen_ctx_labs_hole.
        apply gen_ctx_labs_context with (E:=E); auto.
        apply expr_tt.

  apply from_subst_to_ctx_apair; auto.  
  apply from_subst_to_ctx_abs_capture; auto.
    apply fv_ec_gen_ctx_labs_hole.
    apply cv_ec_gen_ctx_labs_hole.
  apply from_subst_to_ctx_labs with (K:=K); auto.
Qed.

Fixpoint gen_exp_labs (lE:lenv) (e:exp) {struct lE} : exp :=
  match lE with
  | nil => e
  | (x, lbind_typ T)::lE' => exp_abs kn_lin T (close_ee (shift_ee (gen_exp_labs lE' e)) x)
  end.

Fixpoint gen_exp_abs (E:env) (e:exp) {struct E} : exp :=
  match E with
  | nil => e
  | (X, bind_kn K)::E' => (gen_exp_abs E' e)
  | (x, bind_typ T)::E' => exp_abs kn_lin T (close_ee (shift_ee (gen_exp_abs E' e)) x)
  end.

Definition gen_exp_apair (e:exp) := exp_apair e tt.

Fixpoint gen_exp_tabs (E:env) (e:exp) {struct E} : exp :=
  match E with
  | nil => e
  | (X, bind_kn K)::E' => exp_tabs K (close_te (shift_te (gen_exp_tabs E' e)) X)
  | (x, bind_typ T)::E' => (gen_exp_tabs E' e)
  end.

Fixpoint gen_exp_tapp (dsubst:delta_subst) (e:exp) {struct dsubst} : exp :=
  match dsubst with
  | nil => e
  | (X, T)::dsubst' => exp_tapp (gen_exp_tapp dsubst' e) T
  end.

Definition gen_exp_fst (e:exp) := exp_fst e.

Fixpoint gen_exp_app (gsubst:gamma_subst) (e:exp) {struct gsubst} : exp :=
  match gsubst with
  | nil => e
  | (x, v)::gsubst' => exp_app (gen_exp_app gsubst' e) v
  end.

Fixpoint gen_exp_lapp (lgsubst:gamma_subst) (e:exp) {struct lgsubst} : exp :=
  match lgsubst with
  | nil => e
  | (x, v)::lgsubst' => exp_app (gen_exp_lapp lgsubst' e) v
  end.

Lemma plug_gen_ctx_lapp__gen_exp_lapp : forall lgsubst C e,
  plug (gen_ctx_lapp lgsubst C) e = gen_exp_lapp lgsubst (plug C e).
Proof.
  induction lgsubst; intros C e; simpl; auto.
    destruct a. simpl.
    rewrite IHlgsubst. auto.
Qed.
  
Lemma plug_gen_ctx_app__gen_exp_app : forall gsubst C e,
   plug (gen_ctx_app gsubst C) e = gen_exp_app gsubst (plug C e).
Proof.
  induction gsubst; intros C e; simpl; auto.
    destruct a. simpl.
    rewrite IHgsubst. auto.
Qed.

Lemma plug_gen_ctx_tapp__gen_exp_tapp : forall dsubst C e,
   plug (gen_ctx_tapp dsubst C) e = gen_exp_tapp dsubst (plug C e).
Proof.
  induction dsubst; intros C e; simpl; auto.
    destruct a. simpl.
    rewrite IHdsubst. auto.
Qed.

Lemma gen_ctx_tabs_capture_context : forall E C,
  wf_env E ->
  context C ->
  context (gen_ctx_tabs_capture E C).
Proof.
  intros E C Wfe Hctx.
  generalize dependent C.
  induction Wfe; intros; simpl; simpl_env in *; auto.
      apply IHWfe in Hctx; auto.
        apply context_tabs_capture with (L:={{X}} `union` dom E); auto.
          intros X0 HX0.
          rewrite close_open_tc__subst_tc; auto.
            apply subst_tc_context; auto.
Qed.

Lemma plug_gen_ctx_tabs_capture__gen_exp_tabs : forall E C e,
   wf_env E ->
   context C ->
   disjdom (ddom_env E) (cv_ec C) ->
   plug (gen_ctx_tabs_capture E C) e = gen_exp_tabs E (plug C e).
Proof.
  intros E C e Wfe Context Disj.
  generalize dependent C.
  generalize dependent e.
  induction Wfe; intros e C Context Disj; simpl; auto.
      rewrite <- IHWfe; auto.
      unfold close_te.
      unfold close_tc.
      rewrite <- close_te_rec_plug.
        unfold shift_te.
        rewrite shift_te_rec_plug.
        rewrite <- shift_tc_rec_context with (C:=gen_ctx_tabs_capture E C); auto.
          apply gen_ctx_tabs_capture_context; auto. 

          rewrite cv_ec_gen_ctx_tabs_capture.
          assert (X `notin` cv_ec C) as J.
            apply disjdom_one_1.
            apply disjdom_sym_1. 
            apply disjdom_sub with (D1:=ddom_env ([(X, bind_kn K)]++E)).
              apply disjdom_sym_1; auto.
              simpl. fsetdec.
          apply dom__ddom in H.
          fsetdec.

          apply disjdom_sym_1. 
          apply disjdom_sub with (D1:=ddom_env ([(X, bind_kn K)]++E)).
            apply disjdom_sym_1; auto.
            simpl. fsetdec.
Qed.

Lemma plug_gen_ctx_abs_capture__gen_exp_abs : forall C E e,
   wf_env E ->
   fv_ec C [=] {} ->
   disjdom (cv_ec C) (dom E) ->
   context C ->
   plug (gen_ctx_abs_capture E C) e = gen_exp_abs E (plug C e).
Proof.
  intros C E e Wfe Hfv Disj Context.
  generalize dependent C.
  generalize dependent e.
  induction Wfe; intros e C Hfv Disj Context; simpl; auto.
      rewrite <- IHWfe; auto.
      apply disjdom_sub with (D1:=dom ([(X, bind_kn K)]++E)); auto.
        simpl_env. fsetdec.

      rewrite <- IHWfe; auto.
        unfold close_ee.
        unfold close_ec.
        rewrite <- close_ee_rec_plug.
          unfold shift_ee.
          rewrite shift_ee_rec_plug.
          rewrite <- shift_ec_rec_context with (C:=gen_ctx_abs_capture E C); auto.
            apply gen_ctx_abs_capture_context; auto. 

            rewrite cv_ec_gen_ctx_abs_capture.
            assert (x `notin` cv_ec C) as J.
              apply disjdom_one_1.
              apply disjdom_sym_1.
              apply disjdom_sub with (D1:=dom ([(x, bind_typ T)]++E)); auto.
                simpl_env. fsetdec.
            apply dom__gdom in H0. auto.

        apply disjdom_sub with (D1:=dom ([(x, bind_typ T)]++E)); auto.
          simpl_env. fsetdec.
Qed.

Lemma gen_ctx_labs_context' : forall lE E C,
  wf_lenv E lE ->
  fv_ec C [=] {} ->
  context C ->
  context (gen_ctx_labs lE C).
Proof.
  intros lE E C Hwlenv Hfvc Hctx .
  induction Hwlenv; simpl; auto.
    apply context_abs_capture with (L:={{x}} `union` dom D); auto.
      apply type_from_wf_typ in H1; auto.

      intros x0 Hx0.
      rewrite close_open_ec__subst_ec; auto.
        apply subst_ec_context; auto.
Qed.

Lemma plug_gen_ctx_labs__gen_exp_labs : forall C E lE e,
   wf_lenv E lE ->
   fv_ec C [=] {} ->
   disjdom (cv_ec C) (dom lE) ->
   context C ->
   plug (gen_ctx_labs lE C) e = gen_exp_labs lE (plug C e).
Proof.
  intros C E lE e Wfle Hfv Disj Context.
  generalize dependent C.
  generalize dependent e.
  induction Wfle; intros e C Hfv Disj Context; simpl; auto.
      rewrite <- IHWfle; auto.
        unfold close_ee.
        unfold close_ec.
        rewrite <- close_ee_rec_plug.
          unfold shift_ee.
          rewrite shift_ee_rec_plug.
          rewrite <- shift_ec_rec_context with (C:=gen_ctx_labs D C); auto.
            apply gen_ctx_labs_context' with (E:=E); auto. 

            rewrite cv_ec_gen_ctx_labs.
            assert (x `notin` cv_ec C) as J.
              apply disjdom_one_1.
              apply disjdom_sym_1.
              apply disjdom_sub with (D1:=dom ([(x, lbind_typ T)]++D)); auto.
                simpl_env. fsetdec.
            auto.

        apply disjdom_sub with (D1:=dom ([(x, lbind_typ T)]++D)); auto.
          simpl_env. fsetdec.
Qed.

Lemma eval_gen_exp_lapp: forall lgsubst e e',
  wf_gsubst lgsubst ->
  bigstep_red e e' ->
  bigstep_red (gen_exp_lapp lgsubst e) (gen_exp_lapp lgsubst e').
Proof.
  intros lgsubst e e' Hwflg Hbred. 
  generalize dependent e.
  generalize dependent e'.
  induction Hwflg; intros; simpl; auto.
    apply bigstep_red_app_1; auto.
Qed.

Lemma eval_gen_exp_app: forall gsubst e e',
  wf_gsubst gsubst ->
  bigstep_red e e' ->
  bigstep_red (gen_exp_app gsubst e) (gen_exp_app gsubst e').
Proof.
  intros gsubst e e' Hwfg Hbred. 
  generalize dependent e.
  generalize dependent e'.
  induction Hwfg; intros; simpl; auto.
    apply bigstep_red_app_1; auto.
Qed.

Lemma eval_gen_exp_tapp: forall dsubst e e',
  wf_dsubst dsubst ->
  bigstep_red e e' ->
  bigstep_red (gen_exp_tapp dsubst e) (gen_exp_tapp dsubst e').
Proof.
  intros dsubst e e' Hwfd Hbred. 
  generalize dependent e.
  generalize dependent e'.
  induction Hwfd; intros; simpl; auto.
    apply bigstep_red_tapp; auto.
      apply type_from_wf_typ in H0; auto.
Qed.

Lemma gen_exp_tapp_app : forall E E' e,
  gen_exp_tapp (E ++ E') e = gen_exp_tapp E (gen_exp_tapp E' e).
Proof.
  induction E; intros E' e; simpl; auto.
    destruct a. rewrite IHE; auto.
Qed.

Lemma bigstep_red_preserved_under_subst_te: forall e e' X T,
   bigstep_red e e' ->
   type T ->
   bigstep_red (subst_te X T e) (subst_te X T e').
Proof.
  intros e e' X T H.
  generalize dependent X.
  generalize dependent T.
  induction H; intros; auto.
    apply bigstep_red_trans with (subst_te X T e'); auto.
       apply red_preserved_under_typsubst; auto.
Qed.

Lemma gen_exp_tabs_expr : forall E e,
  expr e ->
  expr (gen_exp_tabs E e).
Proof.
  induction E; intros e Hexpr; simpl; auto.
    destruct a.
    destruct b; auto.
      rewrite <- shift_te_expr; auto.
     apply expr_tabs with (L:={{a}}).
       intros X FrX.
       rewrite close_open_te__subst_te; auto.
Qed.

Lemma gen_exp_tapp_subst_te_commute : forall dsubst e X T,
  wf_dsubst dsubst ->
  gen_exp_tapp dsubst (subst_te X T e) = subst_te X T (gen_exp_tapp dsubst e).
Proof.
  intros dsubst e X T Hwfd.
  generalize dependent e.
  generalize dependent X.
  generalize dependent T.
  induction Hwfd; intros; simpl; auto.
    rewrite IHHwfd.
    rewrite <- subst_tt_fresh; auto.
      apply notin_fv_wf with (X:=X0) in H0; auto.
Qed.

Lemma gen_exp_tabs_subst_tt_commute : forall E X T K e,
  X `notin` dom E ->
  wf_typ nil T K ->
  gen_exp_tabs E (subst_te X T e)  = subst_te X T (gen_exp_tabs E e).
Proof.
  induction E; intros X T K e HC Wft; simpl; auto.
  destruct a.
  destruct b; simpl.
    rewrite IHE with (K:=K); auto.
    rewrite subst_te_close_te; auto.
      unfold shift_te.
      rewrite subst_te_shift_te_rec; auto.
        apply type_from_wf_typ in Wft; auto.
      apply notin_fv_wf with (X:=a) in Wft; auto.

    rewrite IHE with (K:=K); auto.
Qed.

Lemma swap_subst_te_dsubst': forall t X dsubst e K,
  wf_dsubst dsubst ->
  wf_typ nil t K ->
  X `notin` dom dsubst ->
  subst_te X t (apply_delta_subst dsubst e) =
  apply_delta_subst dsubst (subst_te X t e).
Proof.
  intros t X dsubst e K Hwfd Hwft xndsubst.
  generalize dependent e.
  generalize dependent t.
  induction Hwfd; intros t Hwft e0; simpl; eauto.
    rewrite subst_te_commute; eauto.
      eauto using notin_fv_wf.
      eauto using notin_fv_wf.
Qed.

Lemma dsubst_stronger' : forall dsubst dsubst' X t,
  wf_dsubst (dsubst'++[(X,t)]++dsubst) ->
  wf_dsubst (dsubst'++dsubst).
Proof.
  intros dsubst dsubst' X t Hwf_dsubst.
  remember (dsubst'++[(X,t)]++dsubst) as dsG.
  generalize dependent dsubst'.
  (wf_dsubst_cases (induction Hwf_dsubst) Case); intros; subst.
  Case "wf_dsubst_empty".
    contradict HeqdsG; auto.
  Case "wf_dsubst_styp".
      apply one_eq_app in HeqdsG. destruct HeqdsG as [[dsE'' [dsEQ1 dsEQ2]] | [dsEQ1 dsEQ2]]; subst.
        simpl_env.
        apply wf_dsubst_styp with (k:=k); simpl in *; auto.

        inversion dsEQ2. subst. simpl_env; auto.
Qed.

Lemma dsubst_strengthen :  forall dsubst dsubst1 dsubst2,
   wf_dsubst (dsubst1++dsubst++dsubst2) ->
   wf_dsubst (dsubst1++dsubst2).
Proof.
  induction dsubst; intros dsubst1 dsubst2 H; simpl_env in *; auto.
    destruct a.
    apply dsubst_stronger' in H; auto.
Qed.

Lemma dsubst_strengthen_head :  forall dsubst1 dsubst2,
   wf_dsubst (dsubst1++dsubst2) ->
   wf_dsubst (dsubst1).
Proof.
  intros dsubst1 dsubst2 H.
  rewrite_env (dsubst1++dsubst2++nil) in H.
  apply dsubst_strengthen in H; simpl_env in H; auto.
Qed.

Lemma dsubst_strengthen_tail :  forall dsubst1 dsubst2,
   wf_dsubst (dsubst1++dsubst2) ->
   wf_dsubst (dsubst2).
Proof.
  intros dsubst1 dsubst2 H.
  rewrite_env (nil++dsubst1++dsubst2) in H.
  apply dsubst_strengthen in H; simpl_env in H; auto.
Qed.

Lemma _eval_gen_exp_tabs_list: forall E' E dsubst' dsubst e,
  wf_delta_subst (E'++E) (dsubst' ++dsubst) ->  
  ddom_env E' [=] dom dsubst' ->
  ddom_env E [=] dom dsubst ->
  expr e ->
  bigstep_red (gen_exp_tapp (rev (dsubst' ++dsubst)) (gen_exp_tabs (E'++E) e))
                           (gen_exp_tapp (rev dsubst) (gen_exp_tabs E (apply_delta_subst dsubst' e))).
Proof.
  intros E' E dsubst' dsubst e Hwfd Dom Hexpr.
  remember (E'++E) as EE.
  remember (dsubst'++dsubst) as dsE.
  generalize dependent E'.
  generalize dependent E.
  generalize dependent dsubst'.
  generalize dependent dsubst.
  generalize dependent e.
  induction Hwfd; intros; subst.
    symmetry in HeqEE.
    apply app_eq_nil in HeqEE.
    destruct HeqEE as [J1 J2]; subst.

    symmetry in HeqdsE.
    apply app_eq_nil in HeqdsE.
    destruct HeqdsE as [J1 J2]; subst.

    simpl. auto.

    apply one_eq_app in HeqEE. destruct HeqEE as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      apply one_eq_app in HeqdsE. destruct HeqdsE as [[dsE'' [dsEQ1 dsEQ2]] | [dsEQ1 dsEQ2]]; subst.
         assert (dsE''++dsubst = dsE''++dsubst) as EQ. auto.
         assert (ddom_env E'' [=] dom dsE'') as J.
           apply ddom_dom__inv with (X:=X)(b:=T)(K:=k); auto.
             apply dom__ddom in H.
             apply dom_delta_subst in Hwfd.
             rewrite Hwfd in H. simpl_env in H. auto.
         apply IHHwfd with (e:=e) (E:=E0) (E':=E'') in EQ; auto.
         simpl_env.
         rewrite distr_rev. simpl. simpl_env.
         rewrite gen_exp_tapp_app. simpl.
         rewrite <- shift_te_expr; try solve [apply gen_exp_tabs_expr; auto].
         apply bigstep_red__trans with (e' := gen_exp_tapp (rev (dsE''++dsubst)) (open_te (close_te (gen_exp_tabs (E''++E0) e) X) T)).
           apply eval_gen_exp_tapp.
             apply wf_delta_subst__wf_dsubst in Hwfd.
             apply wf_dsubst_rev; auto.

             apply bigstep_red_trans with (e':= (open_te (close_te (gen_exp_tabs (E''++E0) e) X) T)); auto.
               apply red_tabs.
                 apply expr_tabs with (L:={}).
                   intros X0 HX0.
                   rewrite close_open_te__subst_te; auto.
                     apply subst_te_expr; auto.
                        apply gen_exp_tabs_expr; auto.
                        apply gen_exp_tabs_expr; auto.
                 apply type_from_wf_typ in H0; auto.
           assert (open_te (close_te (gen_exp_tabs (E''++E0) e) X) T = subst_te X T (gen_exp_tabs (E''++E0) e)) as EQ'.
             rewrite close_open_te__subst_te; auto.
               apply gen_exp_tabs_expr; auto.
           rewrite EQ'.
           assert (gen_exp_tapp (rev (dsE''++dsubst)) (subst_te X T (gen_exp_tabs (E''++E0) e)) =
                             subst_te X T (gen_exp_tapp (rev (dsE''++dsubst)) (gen_exp_tabs (E''++E0) e))) as EQ''.
             rewrite gen_exp_tapp_subst_te_commute; auto.
             apply wf_delta_subst__wf_dsubst in Hwfd.
             apply wf_dsubst_rev in Hwfd; auto.
           rewrite EQ''.
           assert (gen_exp_tapp (rev dsubst) (gen_exp_tabs E0 (apply_delta_subst dsE'' (subst_te X T e))) =
                            subst_te X T (gen_exp_tapp (rev dsubst) (gen_exp_tabs E0 (apply_delta_subst dsE'' e)))) as EQ'''.
             rewrite <- gen_exp_tapp_subst_te_commute; auto.
               rewrite <- gen_exp_tabs_subst_tt_commute with (K:=k); auto.
                 rewrite swap_subst_te_dsubst' with (K:=k); auto.
                   apply wf_delta_subst__wf_dsubst in Hwfd.
                   apply dsubst_strengthen_head in Hwfd; auto.

                    apply dom_delta_subst in Hwfd.
                    apply dom__ddom in H.
                    rewrite Hwfd in H.
                    simpl_env in H. auto.
               apply wf_delta_subst__wf_dsubst in Hwfd.
               apply dsubst_strengthen_tail in Hwfd.
               apply wf_dsubst_rev in Hwfd; auto.
           rewrite EQ'''.
           apply bigstep_red_preserved_under_subst_te; auto.
             apply type_from_wf_typ in H0; auto.

         simpl in Dom.
         assert (X `in` {}) as FALSE.
           rewrite <- Dom.
           auto.
         contradict FALSE; auto.

      apply one_eq_app in HeqdsE. destruct HeqdsE as [[dsE'' [dsEQ1 dsEQ2]] | [dsEQ1 dsEQ2]]; subst.
         simpl in Dom.
         assert (X `in` {}) as FALSE.
           rewrite Dom.
           auto.
         contradict FALSE; auto.

         simpl_env.
         rewrite distr_rev. simpl. simpl_env. auto.
           
    apply one_eq_app in HeqEE. destruct HeqEE as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
         simpl.
         assert (dsubst'++dsubst = dsubst'++dsubst) as EQ. auto.
         simpl in Dom.
         apply IHHwfd with (e:=e) (E:=E0) (E':=E'') in EQ; auto.

         simpl in *. symmetry in Dom.
         apply dom_empty_inv in Dom.
         subst. simpl. auto.
Qed.

Lemma eval_gen_exp_tabs_list: forall E dsubst e,
  wf_delta_subst E dsubst ->  
  expr e ->
  bigstep_red (gen_exp_tapp (rev dsubst) (gen_exp_tabs E e)) (apply_delta_subst dsubst e).
Proof.
  intros E dsubst e Hwfd Hexpr.
  rewrite_env (E++nil) in Hwfd.
  rewrite_env (dsubst++nil) in Hwfd.
  apply _eval_gen_exp_tabs_list with (e:=e) in Hwfd; auto.
    simpl_env in Hwfd; auto.
    apply dom_delta_subst in Hwfd. simpl_env in Hwfd. auto.
Qed.

Lemma gen_exp_app_app : forall E E' e,
  gen_exp_app (E ++ E') e = gen_exp_app E (gen_exp_app E' e).
Proof.
  induction E; intros E' e; simpl; auto.
    destruct a. rewrite IHE; auto.
Qed.

Lemma bigstep_red_preserved_under_subst_ee: forall e e' x v,
   bigstep_red e e' ->
   expr v ->
   bigstep_red (subst_ee x v e) (subst_ee x v e').
Proof.
  intros e e' x v H.
  generalize dependent x.
  generalize dependent v.
  induction H; intros; auto.
    apply bigstep_red_trans with (subst_ee x v e'); auto.
       apply red_preserved_under_expsubst; auto.
Qed.

Lemma gen_exp_abs_expr : forall E e,
  wf_env E ->
  expr e ->
  expr (gen_exp_abs E e).
Proof.
  intros E e Hwfe.
  generalize dependent e.
  induction Hwfe; intros e Hexpr; simpl; auto.
      rewrite <- shift_ee_expr; auto.
     apply expr_abs with (L:={{x}}).
       apply type_from_wf_typ in H; auto.

       intros x0 Frx0.
       rewrite close_open_ee__subst_ee; auto.
Qed.

Lemma gen_exp_app_subst_ee_commute : forall gsubst e x v,
  wf_gsubst gsubst ->
  gen_exp_app gsubst (subst_ee x v e) = subst_ee x v (gen_exp_app gsubst e).
Proof.
  intros gsubst e x v Hwfg.
  generalize dependent e.
  generalize dependent x.
  generalize dependent v.
  induction Hwfg; intros; simpl; auto.
    rewrite IHHwfg.
    rewrite <- subst_ee_fresh with (e:=e); auto.
      apply notin_fv_ee_typing with (y:=x0) in H0; auto.
Qed.

Lemma gen_exp_abs_subst_ee_commute : forall E x v T e,
  x `notin` dom E ->
  typing nil nil v T ->
  gen_exp_abs E (subst_ee x v e)  = subst_ee x v (gen_exp_abs E e).
Proof.
  induction E; intros x v T e HC Typing; simpl; auto.
  destruct a.
  destruct b; simpl.
    rewrite IHE with (T:=T); auto.

    rewrite IHE with (T:=T); auto.
    rewrite subst_ee_close_ee; auto.
      unfold shift_ee.
      rewrite subst_ee_shift_ee_rec; auto.

     apply notin_fv_ee_typing with (y:=a) in Typing; auto.
Qed.

Lemma swap_subst_ee_gsubst'': forall e' x gsubst e t,
  wf_gsubst gsubst ->
  typing nil nil e' t ->
  x `notin` dom gsubst ->
  subst_ee x e' (apply_gamma_subst gsubst e) =
  apply_gamma_subst gsubst (subst_ee x e' e).
Proof.
  intros e' x gsubst e t Hwflg Hwft xngsubst.
  generalize dependent e.
  generalize dependent e'.
  generalize dependent t.
  induction Hwflg; intros t e' Hwft e0; simpl; eauto.
    rewrite subst_ee_commute; eauto.
      eauto using typing_fv.
      eauto using typing_fv.
Qed.

Lemma gsubst_stronger' : forall gsubst gsubst' x v,
  wf_gsubst (gsubst'++[(x,v)]++gsubst) ->
  wf_gsubst (gsubst'++gsubst).
Proof.
  intros gsubst gsubst' x v Hwf_gsubst.
  remember (gsubst'++[(x,v)]++gsubst) as gsG.
  generalize dependent gsubst'.
  (wf_gsubst_cases (induction Hwf_gsubst) Case); intros; subst.
  Case "wf_gsubst_empty".
    contradict HeqgsG; auto.
  Case "wf_gsubst_sval".
      apply one_eq_app in HeqgsG. destruct HeqgsG as [[gsE'' [gsEQ1 gsEQ2]] | [gsEQ1 gsEQ2]]; subst.
        simpl_env.
        apply wf_gsubst_sval with (T:=T); simpl in *; auto.

        inversion gsEQ2. subst. simpl_env; auto.
Qed.

Lemma gsubst_strengthen :  forall gsubst gsubst1 gsubst2,
   wf_gsubst (gsubst1++gsubst++gsubst2) ->
   wf_gsubst (gsubst1++gsubst2).
Proof.
  induction gsubst; intros gsubst1 gsubst2 H; simpl_env in *; auto.
    destruct a.
    apply gsubst_stronger' in H; auto.
Qed.

Lemma gsubst_strengthen_head :  forall gsubst1 gsubst2,
   wf_gsubst (gsubst1++gsubst2) ->
   wf_gsubst (gsubst1).
Proof.
  intros gsubst1 gsubst2 H.
  rewrite_env (gsubst1++gsubst2++nil) in H.
  apply gsubst_strengthen in H; simpl_env in H; auto.
Qed.

Lemma gsubst_strengthen_tail :  forall gsubst1 gsubst2,
   wf_gsubst (gsubst1++gsubst2) ->
   wf_gsubst (gsubst2).
Proof.
  intros gsubst1 gsubst2 H.
  rewrite_env (nil++gsubst1++gsubst2) in H.
  apply gsubst_strengthen in H; simpl_env in H; auto.
Qed.

Lemma wfv_gamma_subst__wf_gamma_subst : forall E dsubst gsubst,
  wfv_gamma_subst E dsubst gsubst ->
  wf_gamma_subst E dsubst gsubst.
Proof.
  intros E dsubst gsubst Hwfg.
  induction Hwfg; auto.
Qed.

Lemma wfv_lgamma_subst__wf_lgamma_subst : forall E D dsubst gsubst lgsubst,
  wfv_lgamma_subst E D dsubst gsubst lgsubst ->
  wf_lgamma_subst E D dsubst gsubst lgsubst.
Proof.
  intros E D dsubst gsubst lgsubst Hwflg.
  induction Hwflg; auto.
Qed.

Lemma wfv_gamma_subst__wf_gsubst : forall E dsubst gsubst,
  wfv_gamma_subst E dsubst gsubst ->
  wf_gsubst gsubst.
Proof.
  intros E dsubst gsubst Hwfg.
  apply wfv_gamma_subst__wf_gamma_subst in Hwfg.
  apply wf_gamma_subst__wf_gsubst in Hwfg; auto.
Qed.

Lemma wfv_lgamma_subst__wf_lgsubst : forall E D dsubst gsubst lgsubst,
  wfv_lgamma_subst E D dsubst gsubst lgsubst ->
  wf_gsubst lgsubst.
Proof.
  intros E D dsubst gsubst lgsubst Hwflg.
  apply wfv_lgamma_subst__wf_lgamma_subst in Hwflg.
  apply wf_lgamma_subst__wf_lgsubst in Hwflg; auto.
Qed.

Lemma wfv_lgamma_subst__wf_gsubst : forall E D dsubst gsubst lgsubst,
  wfv_lgamma_subst E D dsubst gsubst lgsubst ->
  wf_gsubst gsubst.
Proof.
  intros E D dsubst gsubst lgsubst Hwflg.
  apply wfv_lgamma_subst__wf_lgamma_subst in Hwflg.
  apply wf_lgamma_subst__wf_gsubst in Hwflg; auto.
Qed.

Lemma _eval_gen_exp_abs_list: forall E' E dsubst gsubst' gsubst e,
  wfv_gamma_subst (E'++E) dsubst (gsubst' ++gsubst) ->  
  gdom_env E' [=] dom gsubst' ->
  gdom_env E [=] dom gsubst ->
  expr e ->
  bigstep_red (gen_exp_app (rev (gsubst' ++gsubst)) (gen_exp_abs (E'++E) e))
                           (gen_exp_app (rev gsubst) (gen_exp_abs E (apply_gamma_subst gsubst' e))).
Proof.
  intros E' E dsubst' gsubst' gsubst e Hwfg Dom' Dom Hexpr.
  remember (E'++E) as EE.
  remember (gsubst'++gsubst) as gsE.
  generalize dependent E'.
  generalize dependent E.
  generalize dependent gsubst'.
  generalize dependent gsubst.
  generalize dependent e.
  induction Hwfg; intros; subst.
    symmetry in HeqEE.
    apply app_eq_nil in HeqEE.
    destruct HeqEE as [J1 J2]; subst.

    symmetry in HeqgsE.
    apply app_eq_nil in HeqgsE.
    destruct HeqgsE as [J1 J2]; subst.

    simpl. auto.

    apply one_eq_app in HeqEE. destruct HeqEE as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      apply one_eq_app in HeqgsE. destruct HeqgsE as [[gsE'' [gsEQ1 gsEQ2]] | [gsEQ1 gsEQ2]]; subst.
         assert (gsE''++gsubst = gsE''++gsubst) as EQ. auto.
         assert (gdom_env E'' [=] dom gsE'') as J.
           apply gdom_dom__inv with (x:=x)(b:=e)(t:=T); auto.
             apply dom__gdom in H. simpl_env in H. auto.

             apply dom__gdom in H.
             apply wfv_gamma_subst__wf_gamma_subst in Hwfg.
             apply dom_gamma_subst in Hwfg. destruct Hwfg.
             rewrite H4 in H. simpl_env in H. auto.
         apply IHHwfg with (e:=e0) (E:=E0) (E':=E'') in EQ; auto.
         simpl_env.
         rewrite distr_rev. simpl. simpl_env.
         rewrite gen_exp_app_app. simpl.
         assert (wf_env (E''++E0)) as Hwfe.
           apply wfv_gamma_subst__wf_gamma_subst in Hwfg.
           apply wf_gamma_subst__wf_subst in Hwfg. destruct Hwfg; auto.
         rewrite <- shift_ee_expr; try solve [apply gen_exp_abs_expr; auto].
         apply bigstep_red__trans with (e' := gen_exp_app (rev (gsE''++gsubst)) (open_ee (close_ee (gen_exp_abs (E''++E0) e0) x) e)).
           apply eval_gen_exp_app.
             apply wfv_gamma_subst__wf_gsubst in Hwfg.
             apply wf_gsubst_rev; auto.

             apply bigstep_red_trans with (e':= (open_ee (close_ee (gen_exp_abs (E''++E0) e0) x) e)); auto.
               apply red_abs; auto.
                 apply expr_abs with (L:={}).
                   apply type_from_wf_typ in H2; auto.

                   intros x0 Hx0.
                   rewrite close_open_ee__subst_ee; auto.
                     apply subst_ee_expr; auto.
                        apply gen_exp_abs_expr; auto.
                        apply gen_exp_abs_expr; auto.

           assert (open_ee (close_ee (gen_exp_abs (E''++E0) e0) x) e = subst_ee x e (gen_exp_abs (E''++E0) e0)) as EQ'.
             rewrite close_open_ee__subst_ee; auto.
               apply gen_exp_abs_expr; auto.
           rewrite EQ'.
           assert (gen_exp_app (rev (gsE''++gsubst)) (subst_ee x e (gen_exp_abs (E''++E0) e0)) =
                             subst_ee x e (gen_exp_app (rev (gsE''++gsubst)) (gen_exp_abs (E''++E0) e0))) as EQ''.
             rewrite gen_exp_app_subst_ee_commute; auto.
             apply wfv_gamma_subst__wf_gsubst in Hwfg.
             apply wf_gsubst_rev in Hwfg; auto.
           rewrite EQ''.
           assert (gen_exp_app (rev gsubst) (gen_exp_abs E0 (apply_gamma_subst gsE'' (subst_ee x e e0))) =
                            subst_ee x e (gen_exp_app (rev gsubst) (gen_exp_abs E0 (apply_gamma_subst gsE'' e0)))) as EQ'''.
             rewrite <- gen_exp_app_subst_ee_commute; auto.
               rewrite <- gen_exp_abs_subst_ee_commute with (T:=apply_delta_subst_typ dsE T); auto.
                 rewrite swap_subst_ee_gsubst'' with (t:=apply_delta_subst_typ dsE T); auto.
                   apply wfv_gamma_subst__wf_gsubst in Hwfg.
                   apply gsubst_strengthen_head in Hwfg; auto.

                    apply wfv_gamma_subst__wf_gamma_subst in Hwfg.
                    apply dom_gamma_subst in Hwfg.
                    apply dom__gdom in H. destruct Hwfg as [J1 J2].
                    rewrite J2 in H.
                    simpl_env in H. auto.
               apply wfv_gamma_subst__wf_gsubst in Hwfg.
               apply gsubst_strengthen_tail in Hwfg.
               apply wf_gsubst_rev in Hwfg; auto.
           rewrite EQ'''.
           apply bigstep_red_preserved_under_subst_ee; auto.

         simpl in Dom'.
         assert (x `in` {}) as FALSE.
           rewrite <- Dom'.
           auto.
         contradict FALSE; auto.

      apply one_eq_app in HeqgsE. destruct HeqgsE as [[gsE'' [gsEQ1 gsEQ2]] | [gsEQ1 gsEQ2]]; subst.
         simpl in Dom'.
         assert (x `in` {}) as FALSE.
           rewrite Dom'.
           auto.
         contradict FALSE; auto.

         simpl_env.
         rewrite distr_rev. simpl. simpl_env. auto.
           
    apply one_eq_app in HeqEE. destruct HeqEE as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
         simpl.
         assert (gsubst'++gsubst = gsubst'++gsubst) as EQ. auto.
         simpl in Dom'.
         apply IHHwfg with (e:=e) (E:=E0) (E':=E'') in EQ; auto.

         simpl in *. symmetry in Dom'.
         apply dom_empty_inv in Dom'.
         subst. simpl. auto.
Qed.

Lemma eval_gen_exp_abs_list: forall E dsubst gsubst e,
  wfv_gamma_subst E dsubst gsubst ->  
  expr e ->
  bigstep_red (gen_exp_app (rev gsubst) (gen_exp_abs E e)) (apply_gamma_subst gsubst e).
Proof.
  intros E dsubst gsubst e Hwfg Hexpr.
  rewrite_env (E++nil) in Hwfg.
  rewrite_env (gsubst++nil) in Hwfg.
  apply _eval_gen_exp_abs_list with (e:=e) in Hwfg; auto.
    simpl_env in Hwfg; auto.
    apply wfv_gamma_subst__wf_gamma_subst in Hwfg.
    apply dom_gamma_subst in Hwfg. simpl_env in Hwfg. destruct Hwfg; auto.
Qed.

Lemma gen_exp_lapp_app : forall lE lE' e,
  gen_exp_lapp (lE ++ lE') e = gen_exp_lapp lE (gen_exp_lapp lE' e).
Proof.
  induction lE; intros lE' e; simpl; auto.
    destruct a. rewrite IHlE; auto.
Qed.

Lemma gen_exp_labs_expr : forall E lE e,
  wf_lenv E lE ->
  expr e ->
  expr (gen_exp_labs lE e).
Proof.
  intros E lE e Hwfle Hexpr.
  generalize dependent e.
  induction Hwfle; intros e Hexpr; simpl; auto.
     apply expr_abs with (L:={{x}}).
       apply type_from_wf_typ in H1; auto.   

       intros x0 Frx0.
       rewrite <- shift_ee_expr; auto.
       rewrite close_open_ee__subst_ee; auto.
Qed.

Lemma gen_exp_lapp_subst_ee_commute : forall gsubst e x v,
  wf_gsubst gsubst ->
  gen_exp_lapp gsubst (subst_ee x v e) = subst_ee x v (gen_exp_lapp gsubst e).
Proof.
  intros gsubst e x v Hwfg.
  generalize dependent e.
  generalize dependent x.
  generalize dependent v.
  induction Hwfg; intros; simpl; auto.
    rewrite IHHwfg.
    rewrite <- subst_ee_fresh with (e:=e); auto.
      apply notin_fv_ee_typing with (y:=x0) in H0; auto.
Qed.

Lemma gen_exp_labs_subst_ee_commute : forall lE x v T e,
  x `notin` dom lE ->
  typing nil nil v T ->
  gen_exp_labs lE (subst_ee x v e)  = subst_ee x v (gen_exp_labs lE e).
Proof.
  induction lE; intros x v T e HC Typing; simpl; auto.
  destruct a.
  destruct l; simpl.
    rewrite IHlE with (T:=T); auto.
    rewrite subst_ee_close_ee; auto.
      unfold shift_ee.
      rewrite subst_ee_shift_ee_rec; auto.

     apply notin_fv_ee_typing with (y:=a) in Typing; auto.
Qed.

Lemma _eval_gen_exp_labs_list: forall E lE' lE dsubst gsubst lgsubst' lgsubst e,
  wfv_lgamma_subst E (lE'++lE) dsubst gsubst (lgsubst' ++lgsubst) ->  
  dom lE' [=] dom lgsubst' ->
  dom lE [=] dom lgsubst ->
  expr e ->
  bigstep_red (gen_exp_lapp (rev (lgsubst' ++lgsubst)) (gen_exp_labs (lE'++lE) e))
                           (gen_exp_lapp (rev lgsubst) (gen_exp_labs lE (apply_gamma_subst lgsubst' e))).
Proof.
  intros E lE' lE dsubst gsubst lgsubst' lgsubst e Hwflg Dom' Dom Hexpr.
  remember (lE'++lE) as lEE.
  remember (lgsubst'++lgsubst) as lgsE.
  generalize dependent lE'.
  generalize dependent lE.
  generalize dependent lgsubst'.
  generalize dependent lgsubst.
  generalize dependent e.
  induction Hwflg; intros; subst.
    symmetry in HeqlEE.
    apply app_eq_nil in HeqlEE.
    destruct HeqlEE as [J1 J2]; subst.

    symmetry in HeqlgsE.
    apply app_eq_nil in HeqlgsE.
    destruct HeqlgsE as [J1 J2]; subst.

    simpl. auto.

    assert (lgsubst'++lgsubst = lgsubst'++lgsubst) as EQ. auto.
    simpl in Dom'.
    apply IHHwflg with (e:=e0) (lE:=lE0) (lE'0:=lE') in EQ; auto.

    apply one_eq_app in HeqlEE. destruct HeqlEE as [[lE'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      apply one_eq_app in HeqlgsE. destruct HeqlgsE as [[lgsE'' [lgsEQ1 lgsEQ2]] | [lgsEQ1 lgsEQ2]]; subst.
         assert (lgsE''++lgsubst = lgsE''++lgsubst) as EQ. auto.
         assert (dom lE'' [=] dom lgsE'') as J.
           apply dom_dom__inv with (x:=x)(b':=e)(b:=lbind_typ T); auto.
             apply wfv_lgamma_subst__wf_lgamma_subst in Hwflg.
             apply dom_lgamma_subst in Hwflg. decompose [and] Hwflg.
             rewrite H7 in H0. simpl_env in H0. auto.
         apply IHHwflg with (e:=e0) (lE:=lE0) (lE':=lE'') in EQ; auto.
         simpl_env.
         rewrite distr_rev. simpl. simpl_env.
         rewrite gen_exp_lapp_app. simpl.
         assert (wf_lenv E (lE''++lE0)) as Hwfle.
           apply wfv_lgamma_subst__wf_lgamma_subst in Hwflg.
           apply wf_lgamma_subst__wf_lenv in Hwflg. destruct Hwflg; auto.
         rewrite <- shift_ee_expr; try solve [apply gen_exp_labs_expr with (E:=E); auto].
         apply bigstep_red__trans with (e' := gen_exp_lapp (rev (lgsE''++lgsubst)) (open_ee (close_ee (gen_exp_labs (lE''++lE0) e0) x) e)).
           apply eval_gen_exp_lapp.
             apply wfv_lgamma_subst__wf_lgsubst in Hwflg.
             apply wf_gsubst_rev; auto.

             apply bigstep_red_trans with (e':= (open_ee (close_ee (gen_exp_labs (lE''++lE0) e0) x) e)); auto.
               apply red_abs; auto.
                 apply expr_abs with (L:={}).
                   apply type_from_wf_typ in H3; auto.

                   intros x0 Hx0.
                   rewrite close_open_ee__subst_ee; auto.
                     apply subst_ee_expr; auto.
                        apply gen_exp_labs_expr with (E:=E); auto.
                        apply gen_exp_labs_expr with (E:=E); auto.

           assert (open_ee (close_ee (gen_exp_labs (lE''++lE0) e0) x) e = subst_ee x e (gen_exp_labs (lE''++lE0) e0)) as EQ'.
             rewrite close_open_ee__subst_ee; auto.
               apply gen_exp_labs_expr with (E:=E); auto.
           rewrite EQ'.
           assert (gen_exp_lapp (rev (lgsE''++lgsubst)) (subst_ee x e (gen_exp_labs (lE''++lE0) e0)) =
                             subst_ee x e (gen_exp_lapp (rev (lgsE''++lgsubst)) (gen_exp_labs (lE''++lE0) e0))) as EQ''.
             rewrite gen_exp_lapp_subst_ee_commute; auto.
             apply wfv_lgamma_subst__wf_lgsubst in Hwflg.
             apply wf_gsubst_rev in Hwflg; auto.
           rewrite EQ''.
           assert (gen_exp_lapp (rev lgsubst) (gen_exp_labs lE0 (apply_gamma_subst lgsE'' (subst_ee x e e0))) =
                            subst_ee x e (gen_exp_lapp (rev lgsubst) (gen_exp_labs lE0 (apply_gamma_subst lgsE'' e0)))) as EQ'''.
             rewrite <- gen_exp_lapp_subst_ee_commute; auto.
               rewrite <- gen_exp_labs_subst_ee_commute with (T:=apply_delta_subst_typ dsE T); auto.
                 rewrite swap_subst_ee_gsubst'' with (t:=apply_delta_subst_typ dsE T); auto.
                   apply wfv_lgamma_subst__wf_lgsubst in Hwflg.
                   apply gsubst_strengthen_head in Hwflg; auto.

                    apply wfv_lgamma_subst__wf_lgamma_subst in Hwflg.
                    apply dom_lgamma_subst in Hwflg.
                    simpl_env in H0.
                    destruct_notin.             
                    rewrite J in H0. auto.
               apply wfv_lgamma_subst__wf_lgsubst in Hwflg.
               apply gsubst_strengthen_tail in Hwflg.
               apply wf_gsubst_rev in Hwflg; auto.
           rewrite EQ'''.
           apply bigstep_red_preserved_under_subst_ee; auto.

         simpl in Dom'.
         assert (x `in` {}) as FALSE.
           rewrite <- Dom'.
           auto.
         contradict FALSE; auto.

      apply one_eq_app in HeqlgsE. destruct HeqlgsE as [[lgsE'' [lgsEQ1 lgsEQ2]] | [lgsEQ1 lgsEQ2]]; subst.
         simpl in Dom'.
         assert (x `in` {}) as FALSE.
           rewrite Dom'.
           auto.
         contradict FALSE; auto.

         simpl_env.
         rewrite distr_rev. simpl. simpl_env. auto.

    assert (lgsubst'++lgsubst = lgsubst'++lgsubst) as EQ. auto.
    simpl in Dom'.
    apply IHHwflg with (e:=e) (lE:=lE0) (lE'0:=lE') in EQ; auto.
Qed.

Lemma eval_gen_exp_labs_list: forall E lE dsubst gsubst lgsubst e,
  wfv_lgamma_subst E lE dsubst gsubst lgsubst ->  
  expr e ->
  bigstep_red (gen_exp_lapp (rev lgsubst) (gen_exp_labs lE e)) (apply_gamma_subst lgsubst e).
Proof.
  intros E lE dsubst gsubst lgsubst e Hwflg Hexpr.
  rewrite_env (lE++nil) in Hwflg.
  rewrite_env (lgsubst++nil) in Hwflg.
  apply _eval_gen_exp_labs_list with (e:=e) in Hwflg; auto.
    simpl_env in Hwflg; auto.
    apply wfv_lgamma_subst__wf_lgamma_subst in Hwflg.
    apply dom_lgamma_subst in Hwflg.
    decompose [and] Hwflg. simpl_env in H2. auto.
Qed.

Lemma swap_subst_te_gsubst: forall T X gsubst e K,
  wf_gsubst gsubst ->
  wf_typ nil T K ->
  subst_te X T (apply_gamma_subst gsubst e) =
  apply_gamma_subst gsubst (subst_te X T e).
Proof.
  intros T X gsubst e K Hwflg Hwft.
  generalize dependent e.
  generalize dependent T.
  generalize dependent K.
  induction Hwflg; intros; simpl; eauto.
    rewrite subst_te_ee_commute; eauto.
      eauto using notin_fv_te_typing.
Qed.

Lemma wf_dgamma_subst_reorder : forall dsubst gsubst e,
  wf_dsubst dsubst ->
  wf_gsubst gsubst ->
  (apply_delta_subst dsubst (apply_gamma_subst gsubst e)) = 
     (apply_gamma_subst gsubst (apply_delta_subst dsubst e)).
Proof.
  intros dsubst gsubst e Hwfd.
  generalize dependent gsubst.
  generalize dependent e.
  induction Hwfd; intros; simpl; auto.
    rewrite swap_subst_te_gsubst with (K:=k); auto.
Qed.

Lemma wf_ggamma_subst_reorder : forall gsubst lgsubst e,
  wf_gsubst gsubst ->
  wf_gsubst lgsubst ->
  disjoint gsubst lgsubst ->
  (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e)) = 
     (apply_gamma_subst lgsubst (apply_gamma_subst gsubst e)).
Proof.
  intros gsubst lgsubst e Hwfg.
  generalize dependent lgsubst.
  generalize dependent e.
  induction Hwfg; intros; simpl; auto.
    rewrite swap_subst_ee_gsubst'' with (t:=T); auto.
      rewrite IHHwfg; auto.
        solve_uniq.
      solve_uniq.
Qed.

Lemma wf_lgamma_subst__wf_dsubst : forall E D dsubst gsubst lgsubst,
  wf_lgamma_subst E D dsubst gsubst lgsubst->
  wf_dsubst dsubst.
Proof.
  intros E D dsubst gsubst lgsubst Hwflg.
  (wf_lgamma_subst_cases (induction Hwflg) Case); auto.
  Case "wf_lgamma_subst_skind".
    apply wf_dsubst_styp with (k:=k); auto.
      apply dom_lgamma_subst in Hwflg. destruct Hwflg as [J1 [J2 J3]].
      rewrite <- J1.
      apply dom__ddom; auto.
Qed.

Lemma wf_lgamma_subst_reorder : forall E lE dsubst gsubst lgsubst e,
  wf_lgamma_subst E lE dsubst gsubst lgsubst ->
  (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e))) = 
    (apply_gamma_subst  lgsubst (apply_gamma_subst gsubst (apply_delta_subst dsubst e))).
Proof.  
  intros E lE dsubst gsubst lgsubst e Hwflg.
  assert (J1:=Hwflg). apply wf_lgamma_subst__wf_dsubst in J1; auto.
  assert (J2:=Hwflg). apply wf_lgamma_subst__wf_gsubst in J2; auto.
  assert (J3:=Hwflg). apply wf_lgamma_subst__wf_lgsubst in J3; auto.
  rewrite wf_dgamma_subst_reorder; auto.
  rewrite wf_dgamma_subst_reorder; auto.
  rewrite wf_ggamma_subst_reorder; auto.
    apply wf_lgamma_subst_disjoint in Hwflg. decompose [and] Hwflg; auto.
Qed.

Lemma gen_ctx_tabs_capture_abs_labs_context : forall E lE,
  wf_lenv E lE ->
  context (gen_ctx_tabs_capture E (gen_ctx_abs_capture E  (gen_ctx_labs lE ctx_hole))).
Proof.
  intros E lE Wfle.
  apply gen_ctx_tabs_capture_context; auto.
  apply gen_ctx_abs_capture_context; auto.
    apply fv_ec_gen_ctx_labs_hole.
    apply gen_ctx_labs_context with (E:=E); auto.
Qed.

Lemma gen_ctx_abs_capture_labs_context : forall E lE,
  wf_lenv E lE ->
  context (gen_ctx_abs_capture E  (gen_ctx_labs lE ctx_hole)).
Proof.
  intros E lE Wfle.
  apply gen_ctx_abs_capture_context; auto.
    apply fv_ec_gen_ctx_labs_hole.
    apply gen_ctx_labs_context with (E:=E); auto.
Qed.

Lemma expr_preserved_under_dsubst: forall dsubst e,
   wf_dsubst dsubst ->
   expr e ->
   expr (apply_delta_subst dsubst e).
Proof.
  intros dsubst e Hwfd He.
  generalize dependent e.
  induction Hwfd; intros; simpl; auto.
    apply IHHwfd.
      apply subst_te_expr; eauto using type_from_wf_typ.
Qed.

Lemma expr_preserved_under_gsubst: forall gsubst e,
   wf_gsubst gsubst ->
   expr e ->
   expr (apply_gamma_subst gsubst e).
Proof.
  intros gsubst e Hwfg He.
  generalize dependent e.
  induction Hwfg; intros; auto.
    simpl. apply IHHwfg.
      apply subst_ee_expr; auto.
Qed.


Lemma gen_exp_abs_subst_te_commute : forall E X T K e,
  wf_typ nil T K ->
  gen_exp_abs (map (subst_tb X T) E) (subst_te X T e)  = subst_te X T (gen_exp_abs E e).
Proof.
  induction E; intros X T K e Wft; simpl; auto.
  destruct a.
  destruct b; simpl.
    rewrite IHE with (K:=K); auto.

    rewrite IHE with (K:=K); auto.
    rewrite subst_te_close_ee; auto.
      unfold shift_ee.
      rewrite subst_te_shift_ee_rec; auto.
Qed.

Lemma gen_exp_labs_subst_te_commute : forall lE X T K e,
  wf_typ nil T K ->
  gen_exp_labs (map (subst_tlb X T) lE) (subst_te X T e)  = subst_te X T (gen_exp_labs lE e).
Proof.
  induction lE; intros X T K e Wft; simpl; auto.
  destruct a.
  destruct l; simpl.
    rewrite IHlE with (K:=K); auto.
    rewrite subst_te_close_ee; auto.
      unfold shift_ee.
      rewrite subst_te_shift_ee_rec; auto.
Qed.

Lemma gen_exp_abs_dsubst_commute : forall dsubst E e,
  wf_dsubst dsubst ->
  gen_exp_abs (apply_delta_subst_env dsubst E) (apply_delta_subst dsubst e)  = apply_delta_subst dsubst (gen_exp_abs E e).
Proof.
  intros dsubst E e Wfd; simpl; auto.
  generalize dependent E.
  generalize dependent e.
  induction Wfd; intros; simpl; auto.
    rewrite apply_delta_subst_env_nil; auto.

    simpl_env.
    rewrite <- gen_exp_abs_subst_te_commute with (K:=k); auto.    
    rewrite <- IHWfd; auto.
    rewrite apply_delta_subst_env_cons; auto.
Qed.

Lemma gen_exp_labs_dsubst_commute : forall dsubst lE e,
  wf_dsubst dsubst ->
  gen_exp_labs (apply_delta_subst_lenv dsubst lE) (apply_delta_subst dsubst e)  = apply_delta_subst dsubst (gen_exp_labs lE e).
Proof.
  intros dsubst lE e Wfd; simpl; auto.
  generalize dependent lE.
  generalize dependent e.
  induction Wfd; intros; simpl; auto.
    rewrite apply_delta_subst_lenv_nil; auto.

    simpl_env.
    rewrite <- gen_exp_labs_subst_te_commute with (K:=k); auto.    
    rewrite <- IHWfd; auto.
    rewrite apply_delta_subst_lenv_cons'; auto.
Qed.


Lemma gen_exp_labs_gsubst_commute : forall gsubst lE e,
  wf_gsubst gsubst ->
  disjoint lE gsubst ->
  gen_exp_labs lE (apply_gamma_subst gsubst e) = 
    apply_gamma_subst gsubst (gen_exp_labs lE e).
Proof.
  intros gsubst lE e Wfg Disj; simpl; auto.
  generalize dependent lE.
  generalize dependent e.
  induction Wfg; intros; simpl; auto.
    rewrite <- gen_exp_labs_subst_ee_commute with (T:=T); auto.    
      rewrite <- IHWfg; auto.
        solve_uniq.
      solve_uniq.
Qed.

Lemma dsubst_binds_typ :  forall dsubst X t,
  wf_dsubst dsubst ->
  binds X t dsubst ->
  exists K, wf_typ nil t K.
Proof.
  intros dsubst X t Hwf_dsubst.
  generalize dependent X.
  generalize dependent t.
  (wf_dsubst_cases (induction Hwf_dsubst) Case); 
    intros t X0 HeqDsubst.
  inversion HeqDsubst.

  analyze_binds HeqDsubst.
    exists k. auto.

    apply IHHwf_dsubst with (X:=X0); auto.
Qed.

Lemma apply_delta_subst_typ_subst_tt_id : forall dsubst X T t,
  wf_dsubst dsubst ->
  binds X T dsubst ->
  apply_delta_subst_typ dsubst (subst_tt X T t) = apply_delta_subst_typ dsubst t.
Proof.
  intros dsubst X T t Hwfd Hbinds.
  generalize dependent X.
  generalize dependent T.
  generalize dependent t.
  induction Hwfd; intros; simpl; auto.
    inversion Hbinds.

    analyze_binds Hbinds.
      rewrite <- subst_tt_fresh with (T:=subst_tt X T t); auto.
        apply notin_fv_tt_subst_tt_var; auto.
          eauto using notin_fv_wf.

        rewrite subst_tt_commute; auto.
          apply dsubst_binds_typ in BindsTac; auto.
          destruct BindsTac as [K J].
          eauto using notin_fv_wf.

          eauto using notin_fv_wf.

          apply binds_In in BindsTac. solve_uniq.
Qed.

Lemma wf_gamma_subst__wf_dsubst : forall E dsubst gsubst,
  wf_gamma_subst E dsubst gsubst ->
  wf_dsubst dsubst.
Proof.
  intros E dsubst gsubst Hwfg.
  (wf_gamma_subst_cases (induction Hwfg) Case); auto.
  Case "wf_gamma_subst_skind".
    apply wf_dsubst_styp with (k:=k); auto.
      apply dom_gamma_subst in Hwfg. destruct Hwfg as [J1 J2].
      rewrite <- J1.
      apply dom__ddom; auto.
Qed.

Lemma wf_typ_tt_in : forall E t X T K K',
  wf_env E ->
  wf_typ E t K ->
  binds X (bind_kn K') E ->
  wf_typ nil T K' ->
  wf_typ (map (subst_tb X T) E) (subst_tt X T t) K.
Proof.
  intros E t X T K K' Hwfe Hwft Binds Hwft'.
  generalize dependent K'.
  generalize dependent T. 
  generalize dependent X.
  induction Hwft; intros; simpl.
    destruct (X==X0); subst.
      assert (bind_kn K= bind_kn K') as EQ.
        apply binds_unique with (E:=E) (x:=X0); auto.
      inversion EQ; subst.
      rewrite_env (map (subst_tb X0 T) E ++ nil).
      apply wf_typ_weaken_head; auto.

      apply wf_typ_var; auto.
        apply binds_map_2 with (f:=subst_tb X0 T) in H0.
        simpl in H0. auto.

    apply wf_typ_arrow with (K1:=K1) (K2:=K2); eauto.

    apply wf_typ_all with (L:=L `union` dom E `union` {{X}}); eauto.
      intros X0 HX0.
      assert (X0 `notin` L) as J. auto.
      apply H in J.
      assert (wf_env ([(X0, bind_kn K1)]++E)) as J1. auto.
      apply H0 with (X:=X0) (T:=T) (K':=K') (X0:=X) in J1; auto.
      simpl in J1. simpl_env in J1.
      rewrite subst_tt_open_tt_var; auto.
        apply type_from_wf_typ in Hwft'; auto.

    apply wf_typ_with with (K1:=K1) (K2:=K2); eauto.

    apply wf_typ_sub; eauto.
Qed.

Lemma wf_typ_tt_notin : forall E t X T K K',
  uniq E ->
  wf_typ E t K ->
  X `notin` dom E ->
  wf_typ nil T K' ->
  wf_typ (map (subst_tb X T) E) (subst_tt X T t) K.
Proof.
  intros E t X T K K' Hwfe Hwft HX Hwft'.
  generalize dependent K'.
  generalize dependent T. 
  generalize dependent X.
  induction Hwft; intros; simpl.
    destruct (X==X0); subst.
      apply binds_In in H0. 
      contradict H0; auto.

      apply wf_typ_var; auto.
        apply binds_map_2 with (f:=subst_tb X0 T) in H0.
        simpl in H0. auto.

    apply wf_typ_arrow with (K1:=K1) (K2:=K2); eauto.

    apply wf_typ_all with (L:=L `union` dom E `union` {{X}}); eauto.
      intros X0 HX0.
      assert (X0 `notin` L) as J. auto.
      apply H in J.
      assert (uniq ([(X0, bind_kn K1)]++E)) as J1. auto.
      apply H0 with (X:=X0) (T:=T) (K':=K') (X0:=X) in J1; auto.
      simpl in J1. simpl_env in J1.
      rewrite subst_tt_open_tt_var; auto.
        apply type_from_wf_typ in Hwft'; auto.

    apply wf_typ_with with (K1:=K1) (K2:=K2); eauto.

    apply wf_typ_sub; eauto.
Qed.

Lemma subst_tt_fv_tt_sub : forall t X T k,
  wf_typ nil T k ->
  fv_tt (subst_tt X T t) [<=] fv_tt t.
Proof.
  induction t; intros X T kk Hwft; simpl; try solve [eauto | fsetdec].
    destruct (a==X); simpl; try solve [fsetdec].
      apply wft_fv_tt_sub in Hwft.
      fsetdec.

    assert (J1:=@IHt1 X T kk Hwft).
    assert (J2:=@IHt2 X T kk Hwft).
    fsetdec.

    assert (J1:=@IHt1 X T kk Hwft).
    assert (J2:=@IHt2 X T kk Hwft).
    fsetdec.
Qed.

Lemma apply_delta_subst_typ_fv_tt : forall dsubst t,
  wf_dsubst dsubst ->
  fv_tt (apply_delta_subst_typ dsubst t) [<=] fv_tt t.
Proof.
  intros dsubst t Hwfd.
  generalize dependent t.
  induction Hwfd; intros; simpl.
    fsetdec.

    assert (J:=@IHHwfd (subst_tt X T t)).
    assert (J':=@subst_tt_fv_tt_sub t X T k H0).
    fsetdec.    
Qed.

Lemma subst_tt_fv_tt_notin : forall t X T k,
  wf_typ nil T k ->
  X `notin` fv_tt (subst_tt X T t).
Proof.
  induction t; intros X T kk Hwft; simpl; try solve [eauto | fsetdec].
    destruct (a==X); simpl; try solve [fsetdec].
      apply notin_fv_wf with (X:=X) in Hwft; auto.
Qed.

Lemma wf_delta_subst_dsubst_id : forall E dsubst t K,
  wf_delta_subst E dsubst ->
  wf_typ E t K ->
  wf_typ (apply_delta_subst_env dsubst E) (apply_delta_subst_typ dsubst t) K.
Proof.
  intros E dsubst t K Hwfd.
  generalize dependent t.
  generalize dependent K.
  induction Hwfd; intros; simpl; simpl_env; auto.
    apply wf_typ_weaken_head; auto.
      rewrite apply_delta_subst_env_cons.
      rewrite apply_delta_subst_env_subst_tb_swap with (E:=E) (K:=k); auto.
      rewrite_env (nil++[(X, bind_kn k)]++E) in H1.
      apply wf_typ_subst_tb with (F:=nil) (Z:=X) (T:=t) (K:=K) (P:=T) in H1.
        simpl_env in H1.
        apply IHHwfd in H1.
          apply wf_typ_tt_notin with (X:=X) (T:=T) (K':=k) in H1; auto.
            rewrite <- subst_tt_fresh in H1; auto.
              apply wf_delta_subst__wf_dsubst in Hwfd.
              assert (J:=@apply_delta_subst_typ_fv_tt SE (subst_tt X T t) Hwfd).
              assert (J':=@subst_tt_fv_tt_notin t X T k H0).
              fsetdec.
 
            apply apply_delta_subst_env_uniq.
            apply wf_delta_subst__uniq in Hwfd.
            decompose [and] Hwfd; auto.

             rewrite <- (@apply_delta_subst_env_dom (SE) E); auto.

        rewrite_env (E++nil).
        apply wf_typ_weaken_head; auto.
          apply wf_delta_subst__uniq in Hwfd.
          decompose [and] Hwfd; auto.

      assert (uniq E) as Uniq.
        apply wf_delta_subst__uniq in Hwfd.
        decompose [and] Hwfd; auto.
      apply apply_delta_subst_env_uniq with (dsubst:=[(X, T)]++SE) in Uniq.
      rewrite (@apply_delta_subst_env_dom ([(X, T)]++SE) E) in H.
      solve_uniq.
 
    apply wf_typ_weaken_head; auto.
      apply IHHwfd.
        rewrite_env (nil++[(x, bind_typ T)]++E) in H1.
        apply wf_typ_strengthening in H1; auto.

      assert (uniq E) as Uniq.
        apply wf_delta_subst__uniq in Hwfd.
        decompose [and] Hwfd; auto.
      apply apply_delta_subst_env_uniq with (dsubst:=SE) in Uniq.
      rewrite (@apply_delta_subst_env_dom SE E) in H.
      solve_uniq.
Qed.

Lemma wf_env_tt_notin : forall E X T K,
  wf_env E ->
  X `notin` dom E ->
  wf_typ nil T K ->
  wf_env (map (subst_tb X T) E).
Proof.
  intros E X T K Hwfe HX Hwft.
  generalize dependent K.
  generalize dependent T. 
  generalize dependent X.
  induction Hwfe; intros; simpl; simpl_env; auto.
    apply wf_env_kn; eauto.

    apply wf_env_typ; eauto.
      eapply wf_typ_tt_notin; eauto.
Qed.

Lemma wf_env_dsubst_id : forall E dsubst,
  wf_delta_subst E dsubst ->
  wf_env E->
  wf_env (apply_delta_subst_env dsubst E).
Proof.
  intros E dsubst Hwfd.
  induction Hwfd; intros Hwfe; simpl; simpl_env; auto.
    apply wf_env_kn; auto.
      rewrite apply_delta_subst_env_cons.
      rewrite apply_delta_subst_env_subst_tb_swap with (E:=E) (K:=k); auto.
      apply wf_env_tt_notin with (K:=k); auto.
        apply IHHwfd.
        inversion Hwfe; subst; auto.
  
         rewrite <- (@apply_delta_subst_env_dom (SE) E); auto.
       rewrite <- (@apply_delta_subst_env_dom ([(X, T)]++SE) E); auto.

    apply wf_env_typ; auto.
      apply IHHwfd.
      inversion Hwfe; subst; auto.

      apply wf_delta_subst_dsubst_id; auto.

      rewrite <- (@apply_delta_subst_env_dom (SE) E); auto.
Qed.

Lemma delta_subst_binds_typ :  forall E dsubst X t,
  wf_delta_subst E dsubst ->
  binds X t dsubst ->
  exists K, wf_typ nil t K /\ binds X (bind_kn K) E.
Proof.
  intros E dsubst X t Hwf_dsubst Binds.
  generalize dependent X.
  generalize dependent t.
  (wf_delta_subst_cases (induction Hwf_dsubst) Case); 
    intros t X0 HeqDsubst.
  inversion HeqDsubst.

  analyze_binds HeqDsubst.
    exists k. auto.

    apply IHHwf_dsubst in BindsTac; auto.
    destruct BindsTac as [K [J1 J2]].
    exists K. split; auto.

  apply IHHwf_dsubst in HeqDsubst; auto.
  destruct HeqDsubst as [K [J1 J2]].
  exists K. split; auto.
Qed.

Lemma wf_gamma_subst_subst_tt_notin : forall E dsubst gsubst X T K,
  wf_gamma_subst E dsubst gsubst ->
  X `notin` dom E ->
  wf_typ nil T K ->
  wf_gamma_subst (map (subst_tb X T) E) dsubst gsubst.
Proof.
  intros E dsubst gsubst X T K Hwfg HX Wft.
  generalize dependent T.
  generalize dependent X.
  generalize dependent K.
  induction Hwfg; intros; simpl; simpl_env; auto.
    apply wf_gamma_subst_sval; eauto.
      rewrite delta_subst_permut with (dE:=E) (K:=K); auto.
        rewrite <- subst_tt_fresh; auto.
          apply typing_regular in H0.
          destruct H0 as [_ [_ [_ J]]].
          eauto using notin_fv_wf. 

          apply wf_gamma_subst__wf_subst in Hwfg.
          destruct Hwfg; auto.
        apply dom_gamma_subst in Hwfg.
        destruct Hwfg as [J1 J2].
        rewrite <- J1. apply dom__ddom; auto.

      assert (J:=Hwfg).
      apply wf_gamma_subst__wf_subst in J. destruct J as [J1 J2].
      apply wf_typ_tt_notin with (K':=K); auto.

      apply wf_gamma_subst_skind; auto.
      apply IHHwfg with (K:=K); auto.
Qed.

Lemma wf_gamma_subst_subst_tt_in : forall E dsubst gsubst X T,
  wf_gamma_subst E dsubst gsubst ->
  binds X T dsubst ->
  wf_gamma_subst (map (subst_tb X T) E) dsubst gsubst.
Proof.
  intros E dsubst gsubst X T Hwfg Binds.
  generalize dependent T.
  generalize dependent X.
  induction Hwfg; intros; simpl; simpl_env; auto.
    apply wf_gamma_subst_sval; eauto.
      rewrite apply_delta_subst_typ_subst_tt_id; auto.
        apply wf_gamma_subst__wf_dsubst in Hwfg. auto.
    
      assert (J:=Hwfg).
      apply wf_gamma_subst__wf_subst in J. destruct J as [J1 J2].
      apply delta_subst_binds_typ with (X:=X) (t:=T0) in J1; auto.
      destruct J1 as [K' [J11 J12]].
      apply wf_typ_tt_in with (K':=K'); auto.

      apply wf_gamma_subst_skind; auto.
        analyze_binds Binds; auto.
          rewrite <- map_subst_tb_id; auto.
          apply wf_gamma_subst__wf_subst in Hwfg.
          destruct Hwfg; auto.
Qed.

Lemma wf_gamma_subst_dsubst_id : forall E dsubst gsubst,
  wf_gamma_subst E dsubst gsubst ->
  wf_gamma_subst (apply_delta_subst_env dsubst E) dsubst gsubst.
Proof.
  intros E dsubst gsubst Hwfg.
  induction Hwfg; simpl; simpl_env; auto.
    apply wf_gamma_subst_sval; auto.
      rewrite <- apply_delta_subst_env_dom; auto.
      rewrite delta_subst_closed_typing with (e:=e); auto.

      apply wf_delta_subst_dsubst_id; auto.
        apply wf_gamma_subst__wf_subst in Hwfg.
        destruct Hwfg; auto.

    apply wf_gamma_subst_skind; auto.
      rewrite apply_delta_subst_env_cons.
      rewrite apply_delta_subst_env_subst_tb_swap with (E:=E) (K:=k); auto.
        apply wf_gamma_subst_subst_tt_notin with (K:=k); auto.  
        rewrite <- apply_delta_subst_env_dom; auto.

        apply wf_gamma_subst__wf_subst in Hwfg.
        destruct Hwfg; auto.

      rewrite apply_delta_subst_env_cons.
      rewrite apply_delta_subst_env_subst_tb_swap with (E:=E) (K:=k); auto.
        rewrite dom_map.
        rewrite <- apply_delta_subst_env_dom; auto.

        apply wf_gamma_subst__wf_subst in Hwfg.
        destruct Hwfg; auto.
Qed.

Lemma wf_lgamma_subst_subst_tt_notin : forall E lE dsubst gsubst lgsubst X T K,
  wf_lgamma_subst E lE dsubst gsubst lgsubst ->
  X `notin` dom E ->
  wf_typ nil T K ->
  wf_lgamma_subst (map (subst_tb X T) E) (map (subst_tlb X T) lE) dsubst gsubst lgsubst.
Proof.
  intros E lE dsubst gsubst lgsubst X T K Hwflg HX Wft.
  generalize dependent T.
  generalize dependent X.
  generalize dependent K.
  induction Hwflg; intros; simpl; simpl_env; auto.
    apply wf_lgamma_subst_sval; eauto.
      rewrite delta_subst_permut with (dE:=E) (K:=K); auto.
        rewrite <- subst_tt_fresh; auto.
          apply typing_regular in H1.
          destruct H1 as [_ [_ [_ J]]].
          eauto using notin_fv_wf. 

          apply wf_lgamma_subst__wf_subst in Hwflg.
          destruct Hwflg; auto.
        apply dom_lgamma_subst in Hwflg.
        destruct Hwflg as [J1 [J2 J3]].
        rewrite <- J1. apply dom__ddom; auto.

      assert (J:=Hwflg).
      apply wf_lgamma_subst__wf_subst in J. destruct J as [J1 J2].
      apply wf_typ_tt_notin with (K':=K); auto.
        apply wf_delta_subst__uniq in J2. decompose [and] J2; auto.

    apply wf_lgamma_subst_slval; eauto.
      rewrite delta_subst_permut with (dE:=E) (K:=K); auto.
        rewrite <- subst_tt_fresh; auto.
          apply typing_regular in H1.
          destruct H1 as [_ [_ [_ J]]].
          eauto using notin_fv_wf. 

          apply wf_lgamma_subst__wf_subst in Hwflg.
          destruct Hwflg; auto.
        apply dom_lgamma_subst in Hwflg.
        destruct Hwflg as [J1 [J2 J3]].
        rewrite <- J1. apply dom__ddom; auto.

      assert (J:=Hwflg).
      apply wf_lgamma_subst__wf_subst in J. destruct J as [J1 J2].
      apply wf_typ_tt_notin with (K':=K); auto.
        apply wf_delta_subst__uniq in J2. decompose [and] J2; auto.

    apply wf_lgamma_subst_skind; auto.
    apply IHHwflg with (K:=K); auto.
Qed.

Lemma wf_lgamma_subst_dsubst_id : forall E lE dsubst gsubst lgsubst,
  wf_lgamma_subst E lE dsubst gsubst lgsubst ->
  wf_lgamma_subst (apply_delta_subst_env dsubst E) (apply_delta_subst_lenv dsubst lE) dsubst gsubst lgsubst.
Proof.
  intros E lE dsubst gsubst lgsubst Hwflg.
  induction Hwflg; simpl; simpl_env; auto.
    apply wf_lgamma_subst_sval; auto.
      rewrite <- apply_delta_subst_env_dom; auto.

      rewrite <- apply_delta_subst_lenv_dom; auto.

      rewrite delta_subst_closed_typing with (e:=e); auto.

      apply wf_delta_subst_dsubst_id; auto.
        apply wf_lgamma_subst__wf_subst in Hwflg.
        destruct Hwflg; auto.

    apply wf_lgamma_subst_slval; auto.
      rewrite <- apply_delta_subst_env_dom; auto.

      rewrite <- apply_delta_subst_lenv_dom; auto.

      rewrite delta_subst_closed_typing with (e:=e); auto.

      apply wf_delta_subst_dsubst_id; auto.
        apply wf_lgamma_subst__wf_subst in Hwflg.
        destruct Hwflg; auto.

    apply wf_lgamma_subst_skind; auto.
      rewrite apply_delta_subst_env_cons.
      rewrite apply_delta_subst_lenv_cons'.
      rewrite apply_delta_subst_env_subst_tb_swap with (E:=E) (K:=k); auto.
        rewrite apply_delta_subst_lenv_subst_tlb_swap with (E:=E) (K:=k); auto.
          apply wf_lgamma_subst_subst_tt_notin with (K:=k); auto.  
           rewrite <- apply_delta_subst_env_dom; auto.

          apply wf_lgamma_subst__wf_subst in Hwflg.
          destruct Hwflg; auto.

        apply wf_lgamma_subst__wf_subst in Hwflg.
        destruct Hwflg; auto.

      rewrite apply_delta_subst_env_cons.
      rewrite apply_delta_subst_env_subst_tb_swap with (E:=E) (K:=k); auto.
        rewrite dom_map.
        rewrite <- apply_delta_subst_env_dom; auto.

        apply wf_lgamma_subst__wf_subst in Hwflg.
        destruct Hwflg; auto.

      rewrite apply_delta_subst_lenv_cons'.
      rewrite apply_delta_subst_lenv_subst_tlb_swap with (E:=E) (K:=k); auto.
        rewrite dom_map.
        rewrite <- apply_delta_subst_lenv_dom; auto.

        apply wf_lgamma_subst__wf_subst in Hwflg.
        destruct Hwflg; auto.
Qed.

Lemma wf_lenv_dsubst_id : forall E lE dsubst,
  wf_delta_subst E dsubst ->
  wf_lenv E lE ->
  wf_lenv (apply_delta_subst_env dsubst E) (apply_delta_subst_lenv dsubst lE).
Proof.
  intros E lE dsubst Hwfd Hwfe.
  generalize dependent dsubst.
  induction Hwfe; intros; simpl; simpl_env; auto.
    apply wf_lenv_empty.
      apply wf_env_dsubst_id; auto.

    apply wf_lenv_typ; auto.
      rewrite <- apply_delta_subst_env_dom; auto.
      rewrite <- apply_delta_subst_lenv_dom; auto.
      apply wf_delta_subst_dsubst_id; auto.
Qed.

Hint Constructors wfv_gamma_subst wfv_lgamma_subst.

Lemma wfv_gamma_subst_subst_tt_notin : forall E dsubst gsubst X T K,
  wfv_gamma_subst E dsubst gsubst ->
  X `notin` dom E ->
  wf_typ nil T K ->
  wfv_gamma_subst (map (subst_tb X T) E) dsubst gsubst.
Proof.
  intros E dsubst gsubst X T K Hwfg HX Wft.
  generalize dependent T.
  generalize dependent X.
  generalize dependent K.
  induction Hwfg; intros; simpl; simpl_env; auto.
    apply wfv_gamma_subst_sval; eauto.
      rewrite delta_subst_permut with (dE:=E) (K:=K); auto.
        rewrite <- subst_tt_fresh; auto.
          apply typing_regular in H0.
          destruct H0 as [_ [_ [_ J]]].
          eauto using notin_fv_wf. 

          apply wfv_gamma_subst__wf_gamma_subst in Hwfg.
          apply wf_gamma_subst__wf_subst in Hwfg.
          destruct Hwfg; auto.
        apply wfv_gamma_subst__wf_gamma_subst in Hwfg.
        apply dom_gamma_subst in Hwfg.
        destruct Hwfg as [J1 J2].
        rewrite <- J1. apply dom__ddom; auto.

      assert (J:=Hwfg).
      apply wfv_gamma_subst__wf_gamma_subst in J.
      apply wf_gamma_subst__wf_subst in J. destruct J as [J1 J2].
      apply wf_typ_tt_notin with (K':=K); auto.

      apply wfv_gamma_subst_skind; auto.
      apply IHHwfg with (K:=K); auto.
Qed.

Lemma wfv_gamma_subst_dsubst_id : forall E dsubst gsubst,
  wfv_gamma_subst E dsubst gsubst ->
  wfv_gamma_subst (apply_delta_subst_env dsubst E) dsubst gsubst.
Proof.
  intros E dsubst gsubst Hwfg.
  induction Hwfg; simpl; simpl_env; auto.
    apply wfv_gamma_subst_sval; auto.
      rewrite <- apply_delta_subst_env_dom; auto.
      rewrite delta_subst_closed_typing with (e:=e); auto.

      apply wf_delta_subst_dsubst_id; auto.
        apply wfv_gamma_subst__wf_gamma_subst in Hwfg.
        apply wf_gamma_subst__wf_subst in Hwfg.
        destruct Hwfg; auto.

    apply wfv_gamma_subst_skind; auto.
      rewrite apply_delta_subst_env_cons.
      rewrite apply_delta_subst_env_subst_tb_swap with (E:=E) (K:=k); auto.
        apply wfv_gamma_subst_subst_tt_notin with (K:=k); auto.  
        rewrite <- apply_delta_subst_env_dom; auto.

        apply wfv_gamma_subst__wf_gamma_subst in Hwfg.
        apply wf_gamma_subst__wf_subst in Hwfg.
        destruct Hwfg; auto.

      rewrite apply_delta_subst_env_cons.
      rewrite apply_delta_subst_env_subst_tb_swap with (E:=E) (K:=k); auto.
        rewrite dom_map.
        rewrite <- apply_delta_subst_env_dom; auto.

        apply wfv_gamma_subst__wf_gamma_subst in Hwfg.
        apply wf_gamma_subst__wf_subst in Hwfg.
        destruct Hwfg; auto.
Qed.

Lemma wfv_lgamma_subst__wf_subst : forall E D dsubst gsubst lgsubst,
  wfv_lgamma_subst E D dsubst gsubst lgsubst ->
  wfv_gamma_subst E dsubst gsubst /\ wf_delta_subst E dsubst.
intros.
  induction H; auto.
    destruct IHwfv_lgamma_subst as [J1 J2].
    split.
      apply wfv_gamma_subst_sval; auto.
      apply wf_delta_subst_skip; auto.

    destruct IHwfv_lgamma_subst as [J1 J2].
    split.
      apply wfv_gamma_subst_skind; auto.
      apply wf_delta_subst_styp; auto.
Qed.

Lemma wfv_lgamma_subst_subst_tt_notin : forall E lE dsubst gsubst lgsubst X T K,
  wfv_lgamma_subst E lE dsubst gsubst lgsubst ->
  X `notin` dom E ->
  wf_typ nil T K ->
  wfv_lgamma_subst (map (subst_tb X T) E) (map (subst_tlb X T) lE) dsubst gsubst lgsubst.
Proof.
  intros E lE dsubst gsubst lgsubst X T K Hwflg HX Wft.
  generalize dependent T.
  generalize dependent X.
  generalize dependent K.
  induction Hwflg; intros; simpl; simpl_env; auto.
    apply wfv_lgamma_subst_sval; eauto.
      rewrite delta_subst_permut with (dE:=E) (K:=K); auto.
        rewrite <- subst_tt_fresh; auto.
          apply typing_regular in H1.
          destruct H1 as [_ [_ [_ J]]].
          eauto using notin_fv_wf. 

          apply wfv_lgamma_subst__wf_subst in Hwflg.
          destruct Hwflg; auto.
        apply wfv_lgamma_subst__wf_lgamma_subst in Hwflg.
        apply dom_lgamma_subst in Hwflg.
        destruct Hwflg as [J1 [J2 J3]].
        rewrite <- J1. apply dom__ddom; auto.

      assert (J:=Hwflg).
      apply wfv_lgamma_subst__wf_subst in J. destruct J as [J1 J2].
      apply wf_typ_tt_notin with (K':=K); auto.
        apply wf_delta_subst__uniq in J2. decompose [and] J2; auto.

    apply wfv_lgamma_subst_slval; eauto.
      rewrite delta_subst_permut with (dE:=E) (K:=K); auto.
        rewrite <- subst_tt_fresh; auto.
          apply typing_regular in H1.
          destruct H1 as [_ [_ [_ J]]].
          eauto using notin_fv_wf. 

          apply wfv_lgamma_subst__wf_subst in Hwflg.
          destruct Hwflg; auto.
        apply wfv_lgamma_subst__wf_lgamma_subst in Hwflg.
        apply dom_lgamma_subst in Hwflg.
        destruct Hwflg as [J1 [J2 J3]].
        rewrite <- J1. apply dom__ddom; auto.

      assert (J:=Hwflg).
      apply wfv_lgamma_subst__wf_subst in J. destruct J as [J1 J2].
      apply wf_typ_tt_notin with (K':=K); auto.
        apply wf_delta_subst__uniq in J2. decompose [and] J2; auto.

    apply wfv_lgamma_subst_skind; auto.
    apply IHHwflg with (K:=K); auto.
Qed.

Lemma wfv_lgamma_subst_dsubst_id : forall E lE dsubst gsubst lgsubst,
  wfv_lgamma_subst E lE dsubst gsubst lgsubst ->
  wfv_lgamma_subst (apply_delta_subst_env dsubst E) (apply_delta_subst_lenv dsubst lE) dsubst gsubst lgsubst.
Proof.
  intros E lE dsubst gsubst lgsubst Hwflg.
  induction Hwflg; simpl; simpl_env; auto.
    apply wfv_lgamma_subst_sval; auto.
      rewrite <- apply_delta_subst_env_dom; auto.

      rewrite <- apply_delta_subst_lenv_dom; auto.

      rewrite delta_subst_closed_typing with (e:=e); auto.

      apply wf_delta_subst_dsubst_id; auto.
        apply wfv_lgamma_subst__wf_subst in Hwflg.
        destruct Hwflg; auto.

    apply wfv_lgamma_subst_slval; auto.
      rewrite <- apply_delta_subst_env_dom; auto.

      rewrite <- apply_delta_subst_lenv_dom; auto.

      rewrite delta_subst_closed_typing with (e:=e); auto.

      apply wf_delta_subst_dsubst_id; auto.
        apply wfv_lgamma_subst__wf_subst in Hwflg.
        destruct Hwflg; auto.

    apply wfv_lgamma_subst_skind; auto.
      rewrite apply_delta_subst_env_cons.
      rewrite apply_delta_subst_lenv_cons'.
      rewrite apply_delta_subst_env_subst_tb_swap with (E:=E) (K:=k); auto.
        rewrite apply_delta_subst_lenv_subst_tlb_swap with (E:=E) (K:=k); auto.
          apply wfv_lgamma_subst_subst_tt_notin with (K:=k); auto.  
           rewrite <- apply_delta_subst_env_dom; auto.

          apply wfv_lgamma_subst__wf_subst in Hwflg.
          destruct Hwflg; auto.

        apply wfv_lgamma_subst__wf_subst in Hwflg.
        destruct Hwflg; auto.

      rewrite apply_delta_subst_env_cons.
      rewrite apply_delta_subst_env_subst_tb_swap with (E:=E) (K:=k); auto.
        rewrite dom_map.
        rewrite <- apply_delta_subst_env_dom; auto.

        apply wfv_lgamma_subst__wf_subst in Hwflg.
        destruct Hwflg; auto.

      rewrite apply_delta_subst_lenv_cons'.
      rewrite apply_delta_subst_lenv_subst_tlb_swap with (E:=E) (K:=k); auto.
        rewrite dom_map.
        rewrite <- apply_delta_subst_lenv_dom; auto.

        apply wfv_lgamma_subst__wf_subst in Hwflg.
        destruct Hwflg; auto.
Qed.

Lemma ddom_gdom_disjdom : forall E,
  uniq E ->
  disjdom (ddom_env E) (gdom_env E).
Proof.
  intros E Uniq.
  induction Uniq; simpl.
    apply disjdom_nil_1.
    
    destruct a.
      eapply disjdom_app_l.
      split; auto.
        eapply disjdom_one_l; auto.
        apply dom__gdom; auto.
    
      eapply disjdom_app_r; auto.
      split; auto.
        eapply disjdom_one_l; auto.
        apply disjdom_sym_1; auto.
Qed.

Lemma bigstep_red_fst_beta : forall e e',
  bigstep_red e e' ->
  bigstep_red (exp_fst e) (exp_fst e').
Proof.
  intros e e' Hrel.
  induction Hrel; auto.
    apply bigstep_red_trans with (e':=exp_fst e'); auto.
Qed.    

Lemma eval_from_subst_to_ctx : forall E lE dsubst gsubst lgsubst e t,
  wfv_lgamma_subst E lE dsubst gsubst lgsubst ->
  typing E lE e t ->
  bigstep_red 
    (plug (gen_ctx_lapp (rev lgsubst) (gen_ctx_app (rev gsubst) (gen_ctx_fst (gen_ctx_tapp (rev dsubst) (gen_ctx_tabs_capture E (gen_ctx_apair (gen_ctx_abs_capture E  (gen_ctx_labs lE ctx_hole)))))))) e)
    (apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e))).
Proof.
  intros E lE dsubst gsubst lgsubst e t Hwflg Htyping.
  assert (JJ:=Hwflg). apply wfv_lgamma_subst__wf_lgamma_subst in JJ.
  rewrite wf_lgamma_subst_reorder with (E:=E) (lE:=lE); auto.
  rewrite plug_gen_ctx_lapp__gen_exp_lapp.
  rewrite plug_gen_ctx_app__gen_exp_app.
  unfold gen_ctx_fst. simpl.
  rewrite plug_gen_ctx_tapp__gen_exp_tapp.
  assert (disjdom (ddom_env E) (cv_ec (gen_ctx_abs_capture E (gen_ctx_labs lE ctx_hole)))) as JJ'.
    apply disjdom_sym_1.
    apply disjdom_eq with (D1:=gdom_env E `union` dom lE).
      eapply disjdom_app_l.
      split.
        apply disjdom_sym_1.
        apply ddom_gdom_disjdom; auto.
       
        apply disjdom_sub with (D1:=dom E).
          apply disjoint__disjdom. 
          apply wfv_lgamma_subst__wf_lgamma_subst in Hwflg.
          apply wf_lgamma_subst__wf_lenv in Hwflg.
          destruct Hwflg as [J1 J2].
          apply disjoint_wf_lenv in J2; auto.

          rewrite dom__ddom_gdom. fsetdec.
        rewrite cv_ec_gen_ctx_abs_capture.
        rewrite cv_ec_gen_ctx_labs. 
        simpl. fsetdec.
  rewrite plug_gen_ctx_tabs_capture__gen_exp_tabs; try solve [auto |   apply context_apair1; [apply gen_ctx_abs_capture_labs_context; auto | apply expr_tt]].
  unfold gen_ctx_apair. simpl.
  rewrite plug_gen_ctx_abs_capture__gen_exp_abs; try solve [
    auto | 
    apply gen_ctx_labs_context with (E:=E); auto |
    apply fv_ec_gen_ctx_labs_hole |
    apply disjdom_eq with (D1:=dom lE); try solve [
      apply disjoint__disjdom;
      apply typing_regular in Htyping;
      destruct Htyping as [_ [J [_ _] ]];
      apply disjoint_wf_lenv in J; auto |
      rewrite cv_ec_gen_ctx_labs_hole; fsetdec]
   ].
  rewrite plug_gen_ctx_labs__gen_exp_labs with (E:=E); simpl; try solve [auto | apply disjdom_nil_1].

  apply bigstep_red__trans with (e':=(gen_exp_lapp (rev lgsubst) (gen_exp_labs (apply_delta_subst_lenv dsubst lE) (apply_gamma_subst (rev gsubst) (apply_delta_subst (rev dsubst) e))))).
    apply eval_gen_exp_lapp; auto.
      apply wfv_lgamma_subst__wf_lgamma_subst in Hwflg.
      apply wf_lgamma_subst__wf_lgsubst in Hwflg.
      apply wf_gsubst_rev; auto.

    apply bigstep_red__trans with (e':=(gen_exp_app (rev gsubst) (gen_exp_abs (apply_delta_subst_env dsubst E) (gen_exp_labs (apply_delta_subst_lenv dsubst lE) (apply_delta_subst (rev dsubst) e))))).
      apply eval_gen_exp_app; auto.
        apply wfv_lgamma_subst__wf_gsubst in Hwflg.
        apply wf_gsubst_rev; auto.

    apply bigstep_red__trans with (e':=exp_fst (exp_apair (gen_exp_abs (apply_delta_subst_env dsubst E) (gen_exp_labs (apply_delta_subst_lenv dsubst lE) (apply_delta_subst (rev dsubst) e))) tt)).
      apply bigstep_red_fst_beta .
        assert (apply_delta_subst dsubst (exp_apair (gen_exp_abs E (gen_exp_labs lE e)) tt) =
                          exp_apair
                           (gen_exp_abs (apply_delta_subst_env dsubst E) 
                             (gen_exp_labs (apply_delta_subst_lenv dsubst lE) 
                               (apply_delta_subst (rev dsubst) e))) tt) as EQ.
          simpl_commut_subst.
          assert (J:=Hwflg). 
          apply wfv_lgamma_subst__wf_lgamma_subst in J.
          apply wf_lgamma_subst__wf_dsubst in J.
          rewrite <- gen_exp_abs_dsubst_commute; auto.
          rewrite <- gen_exp_labs_dsubst_commute; auto.
          rewrite <- apply_delta_subst_rev with (E:=E); auto.
            rewrite delta_osubst_closed_exp with (e:=tt); auto.
              apply disjdom_eq with (D1:={}).
                apply disjdom_nil_1.
                simpl. fsetdec.

            apply wfv_lgamma_subst__wf_lgamma_subst in Hwflg.
            apply wf_lgamma_subst__wf_subst in Hwflg. decompose [and] Hwflg; auto.
        rewrite <- EQ.
        assert (J:=Hwflg).
        apply wfv_lgamma_subst__wf_lgamma_subst in J.
        apply wf_lgamma_subst__wf_subst in J. destruct J as [J1 J2].
        apply eval_gen_exp_tabs_list with (E:=E) (dsubst:=dsubst); auto.
          apply expr_apair.
            apply gen_exp_abs_expr; auto.
              apply gen_exp_labs_expr with (E:=E); auto.
            apply expr_tt.

      apply bigstep_red_trans with (e':=gen_exp_abs (apply_delta_subst_env dsubst E) (gen_exp_labs (apply_delta_subst_lenv dsubst lE) (apply_delta_subst (rev dsubst) e))); auto.
        apply red_fst_beta.
          apply gen_exp_abs_expr; auto.
            apply wf_env_dsubst_id ; auto.
              apply wfv_lgamma_subst__wf_lgamma_subst in Hwflg.
              apply wf_lgamma_subst__wf_subst in Hwflg. destruct Hwflg; auto.

            apply gen_exp_labs_expr with (E:=(apply_delta_subst_env dsubst E)); auto.             
             apply wf_lenv_dsubst_id ; auto.
              apply wfv_lgamma_subst__wf_lgamma_subst in Hwflg.
              apply wf_lgamma_subst__wf_subst in Hwflg. destruct Hwflg; auto.

             apply expr_preserved_under_dsubst; auto.
               apply wfv_lgamma_subst__wf_lgamma_subst in Hwflg.
               apply wf_lgamma_subst__wf_subst in Hwflg. destruct Hwflg as [J1 J2].
               apply wf_delta_subst__wf_dsubst in J2; auto.
               apply wf_dsubst_rev; auto.

             apply expr_tt.

        assert (apply_gamma_subst gsubst (gen_exp_labs (apply_delta_subst_lenv dsubst lE) (apply_delta_subst (rev dsubst) e)) =
                         gen_exp_labs (apply_delta_subst_lenv dsubst lE) (apply_gamma_subst (rev gsubst) (apply_delta_subst (rev dsubst) e))) as EQ.
          assert (J:=Hwflg). apply wfv_lgamma_subst__wf_gsubst in J.
          rewrite <- gen_exp_labs_gsubst_commute; auto.
            rewrite <- apply_gamma_subst_rev with (E:=E) (dsubst:=dsubst); auto.
              apply wfv_lgamma_subst__wf_lgamma_subst in Hwflg.
              apply wf_lgamma_subst__wf_subst in Hwflg. decompose [and] Hwflg; auto.
            apply wfv_lgamma_subst__wf_lgamma_subst in Hwflg.
            apply wf_lgamma_subst_disjoint in Hwflg. 
            destruct Hwflg as [_ [_ [_ [_ [_ H]]]]].
            assert (J':=@apply_delta_subst_lenv_dom dsubst lE).
            solve_uniq.

        rewrite <- EQ.
        assert (J:=Hwflg).
        apply wfv_lgamma_subst__wf_subst in J. destruct J as [J1 J2].
        apply eval_gen_exp_abs_list with (dsubst:=dsubst) (gsubst:=gsubst); auto. 

          apply wfv_gamma_subst_dsubst_id; auto.

          apply gen_exp_labs_expr with (E:=apply_delta_subst_env dsubst E); auto.
             apply wf_lenv_dsubst_id ; auto.

             apply expr_preserved_under_dsubst; auto.
                apply wf_dsubst_rev.
                  apply wf_delta_subst__wf_dsubst in J2; auto.

     assert (J:=Hwflg).
     apply wfv_lgamma_subst__wf_subst in J. destruct J as [J1 J2].
     apply wf_lgamma_subst__wf_subst in JJ. destruct JJ as [J3 J4].
     rewrite apply_gamma_subst_rev with (E:=E) (dsubst:=dsubst) (gsubst:=gsubst); auto.
     rewrite apply_delta_subst_rev with (E:=E) (dsubst:=dsubst); auto.
     apply eval_gen_exp_labs_list with (E:=apply_delta_subst_env dsubst E) (dsubst:=dsubst) (gsubst:=gsubst); auto.
        apply wfv_lgamma_subst_dsubst_id; auto.

        apply expr_preserved_under_gsubst; auto.
           apply wf_gsubst_rev.
              apply wfv_gamma_subst__wf_gsubst in J1; auto.
          apply expr_preserved_under_dsubst; auto.
             apply wf_dsubst_rev.
                apply wf_delta_subst__wf_dsubst in J2; auto.
Qed.

Lemma hole_red : forall C e e',
  red e e' ->
  cbv_ctx C ->
  red (plug C e) (plug C e').
Proof.
  induction C; intros ee ee' Hred HvC; simpl; 
    try solve [auto | inversion HvC | destruct HvC as [J1 J2]; eauto].
Qed.

Lemma hole_bigstep_red : forall e e' C,
  bigstep_red e e' ->
  cbv_ctx C ->
  bigstep_red (plug C e) (plug C e').
Proof.
  intros e e' C Hred HvC.
  induction Hred; auto.
    apply bigstep_red_trans with (e':=plug C e'); auto using hole_red.    
Qed.

Lemma cbv_ctx_cv_ec : forall C,
  cbv_ctx C ->
  cv_ec C [=] {}.
Proof. 
  induction C; intros HvC; simpl in *; 
    try solve [inversion HvC |
                         destruct HvC as [J1 J2]; rewrite (@IHC J1); fsetdec |
                         destruct HvC as [J1 J2]; rewrite (@IHC J2); fsetdec |
                          rewrite (@IHC HvC); fsetdec |
                         fsetdec
                         ].
Qed.

Lemma F_observational_eq__F_ciu_eq : forall E lE e e' t,
  F_observational_eq E lE e e' t ->
  F_ciu_eq E lE e e' t.
Proof.
  intros E lE e e' t Hob.
  destruct Hob as [Htyp [Htyp' J]].
  split; auto.
  split; auto.
    intros dsubst gsubst lgsubst Hwflg.
    assert (JJ:=Hwflg). apply wfv_lgamma_subst__wf_lgamma_subst in JJ.
    split.
      apply typing_subst with (E:=E) (D:=lE); auto.
    split.
      apply typing_subst with (E:=E) (D:=lE); auto.
      intros C Contexting HvC.
      assert (wf_delta_subst E dsubst) as Wfd.
        apply wfv_lgamma_subst__wf_subst in Hwflg. destruct Hwflg. auto.
      rewrite apply_delta_subst_typ_rev with (E:=E) in Contexting; auto.
      assert (wf_typ E t kn_lin) as J1. auto.
      assert (J2:=@wf_from_subst_to_ctx E lE dsubst gsubst lgsubst t kn_lin JJ J1).
      assert (J3:=@eval_from_subst_to_ctx E lE dsubst gsubst lgsubst e t Hwflg Htyp).
      assert (J4:=@eval_from_subst_to_ctx E lE dsubst gsubst lgsubst e' t Hwflg Htyp').
      assert (contexting E lE t (plugC C (( gen_ctx_lapp (rev lgsubst) (gen_ctx_app (rev gsubst) (gen_ctx_fst (gen_ctx_tapp (rev dsubst) (gen_ctx_tabs_capture E (gen_ctx_apair (gen_ctx_abs_capture E  (gen_ctx_labs lE ctx_hole)))))))))) nil nil Two) as J5.      
        apply contexting_plugC_contexting with (E':=nil) (D':=nil) (T':=apply_delta_subst_typ (rev dsubst) t); auto.
          apply disjdom_sym_1.
          apply disjdom_eq with (D1:={}).
            apply disjdom_nil_1.
            
            rewrite cbv_ctx_cv_ec; auto. 
            apply fv_ec_contexting_sub in Contexting.
            clear - Contexting. fsetdec.

      apply J in J5.
      split.
        apply contexting_plug_typing with (E:=nil) (D:=nil) (T:=apply_delta_subst_typ (rev dsubst) t); auto.
          rewrite <- apply_delta_subst_typ_rev with (E:=E); auto.
          apply typing_subst with (E:=E) (D:=lE); auto.
      split.
        apply contexting_plug_typing with (E:=nil) (D:=nil) (T:=apply_delta_subst_typ (rev dsubst) t); auto.
          rewrite <- apply_delta_subst_typ_rev with (E:=E); auto.
          apply typing_subst with (E:=E) (D:=lE); auto.
      destruct J5 as [J5 [J6 [[J7 J8] | [J7 J8]]]].
        left.
        split. 
          apply bigstep_red_normalization with (u:=plug (plugC C (( gen_ctx_lapp (rev lgsubst) (gen_ctx_app (rev gsubst) (gen_ctx_fst (gen_ctx_tapp (rev dsubst) (gen_ctx_tabs_capture E (gen_ctx_apair (gen_ctx_abs_capture E  (gen_ctx_labs lE ctx_hole)))))))))) e) (t:=Two); auto.
            rewrite plug_plugC.
              apply hole_bigstep_red; auto.
              apply disjdom_eq with (D1:={}).
                apply disjdom_nil_1.
                rewrite cbv_ctx_cv_ec; auto.

          apply bigstep_red_normalization with (u:=plug (plugC C (( gen_ctx_lapp (rev lgsubst) (gen_ctx_app (rev gsubst) (gen_ctx_fst (gen_ctx_tapp (rev dsubst) (gen_ctx_tabs_capture E (gen_ctx_apair (gen_ctx_abs_capture E  (gen_ctx_labs lE ctx_hole)))))))))) e') (t:=Two); auto.
            rewrite plug_plugC.
              apply hole_bigstep_red; auto.
              apply disjdom_eq with (D1:={}).
                apply disjdom_nil_1.
                rewrite cbv_ctx_cv_ec; auto.
        
        right.
        split. 
          apply bigstep_red_normalization with (u:=plug (plugC C (( gen_ctx_lapp (rev lgsubst) (gen_ctx_app (rev gsubst) (gen_ctx_fst (gen_ctx_tapp (rev dsubst) (gen_ctx_tabs_capture E (gen_ctx_apair (gen_ctx_abs_capture E  (gen_ctx_labs lE ctx_hole)))))))))) e) (t:=Two); auto.
            rewrite plug_plugC.
              apply hole_bigstep_red; auto.
              apply disjdom_eq with (D1:={}).
                apply disjdom_nil_1.
                rewrite cbv_ctx_cv_ec; auto.
          apply bigstep_red_normalization with (u:=plug (plugC C (( gen_ctx_lapp (rev lgsubst) (gen_ctx_app (rev gsubst) (gen_ctx_fst (gen_ctx_tapp (rev dsubst) (gen_ctx_tabs_capture E (gen_ctx_apair  (gen_ctx_abs_capture E  (gen_ctx_labs lE ctx_hole)))))))))) e') (t:=Two); auto.
            rewrite plug_plugC.
              apply hole_bigstep_red; auto.
              apply disjdom_eq with (D1:={}).
                apply disjdom_nil_1.
                rewrite cbv_ctx_cv_ec; auto.
Qed.

Lemma F_ciu_eq__refl : forall E lE e t,
  typing E lE e t ->
  F_ciu_eq E lE e e t.
Proof.
  intros E lE e t Typ.
  split; auto.
  split; auto.
  intros dsubst gsubst lgsubst Hwflg.
  apply F_observational_eq__F_vobservational_eq.
  apply F_observational_eq__refl; auto.
    apply typing_subst with (E:=E) (D:=lE); auto.
      apply wfv_lgamma_subst__wf_lgamma_subst; auto.
Qed.

Lemma F_ciu_eq__sym : forall E lE e e' t,
  F_ciu_eq E lE e e' t ->
  F_ciu_eq E lE e' e t.
Proof.
  intros E lE e e' t Hciu.
  destruct Hciu as [Typ [Typ' J]].
  split; auto.
  split; auto.
    intros dsubst gsubst lgsubst Hwflg.
    apply F_vobservational_eq__sym; auto.
Qed.

Lemma F_ciu_eq__trans : forall E lE e e' e'' t,
  F_ciu_eq E lE e e' t ->
  F_ciu_eq E lE e' e'' t ->
  F_ciu_eq E lE e e'' t.
Proof.
  intros E lE e e' e'' t Hciu Hciu'.
  destruct Hciu as [Typ [Typ' J]].
  destruct Hciu' as [_ [Typ'' J']].
  split; auto.
  split; auto.
    intros dsubst gsubst lgsubst Hwflg.
    apply F_vobservational_eq__trans with (e':=apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e'))); auto.
Qed.

Lemma F_ciu_eq__beta : forall E lE e e' t,
  typing E lE e t ->
  red e e' ->
  F_ciu_eq E lE e e' t.
Proof.
  intros E lE e e' t Typ Red.
  split; auto.
  split. apply preservation with (e':=e') in Typ; auto.
    intros dsubst gsubst lgsubst Hwflg.
    apply F_observational_eq__F_vobservational_eq.
    apply F_observational_eq__beta.
      apply typing_subst with (E:=E) (D:=lE); auto.
        apply wfv_lgamma_subst__wf_lgamma_subst; auto.
      apply red_preserved_under_subst with (E:=E) (D:=lE); auto.
      apply wfv_lgamma_subst__wf_lgamma_subst; auto.
Qed.
      
Lemma F_ciu_eq__mbeta : forall E lE e e' t,
  typing E lE e t ->
  bigstep_red e e' ->
  F_ciu_eq E lE e e' t.
Proof.
  intros E lE e e' t Typ Red.
  induction Red.
    apply F_ciu_eq__refl; auto.
    apply F_ciu_eq__trans with (e':=e').
      apply F_ciu_eq__beta; auto.
      apply IHRed.
        apply preservation with (e':=e') in Typ; auto.
Qed.

Lemma wfv_lgamma_subst_split : forall E lE dsubst gsubst lgsubst lE1 lE2 E',
  wfv_lgamma_subst E lE dsubst gsubst lgsubst ->
  lenv_split (E'++E) lE1 lE2 lE ->
  exists lgsubst1, exists lgsubst2,
    lgamma_subst_split E lE dsubst gsubst lgsubst1 lgsubst2 lgsubst /\
    wfv_lgamma_subst E lE1 dsubst gsubst lgsubst1 /\
    wfv_lgamma_subst E lE2 dsubst gsubst lgsubst2.
Proof.
  intros E lE dsubst gsubst lgsubst lE1 lE2 E' Hwflg Hsplit.
  generalize dependent lE1. generalize dependent lE2. generalize dependent E'.
  (wfv_lgamma_subst_cases (induction Hwflg) Case); intros.
  Case "wfv_lgamma_subst_empty".
    exists gamma_nil. exists gamma_nil.
    inversion Hsplit; subst.
    repeat (split; auto).
  Case "wfv_lgamma_subst_sval".
    assert (J:=Hsplit).
    rewrite_env ((E'++[(x, bind_typ T)])++E) in Hsplit.
    apply IHHwflg in Hsplit. clear IHHwflg.
    destruct Hsplit as [lgsubst1 [lgsubst2 [J1 [J2 J3]]]].
    exists lgsubst1. exists lgsubst2.
    split.
      apply lgamma_subst_split_nonlin_weakening_tail; auto.
        apply wfv_lgamma_subst__wf_lgamma_subst; auto.
    split.
      apply wfv_lgamma_subst_sval; auto.
        apply dom_lenv_split in J.
        rewrite J in H0; auto.  
      apply wfv_lgamma_subst_sval; auto.
        apply dom_lenv_split in J.
        rewrite J in H0; auto.
  Case "wfv_lgamma_subst_slval".
    inversion Hsplit; subst.
    SCase "lenv_split_left".
      assert (J:=H7).
      apply IHHwflg in H7. clear IHHwflg.
      destruct H7 as [lgsubst1 [lgsubst2 [J1 [J2 J3]]]].
      exists ([(x,e)]++lgsubst1). exists lgsubst2. 
      split.
        apply lgamma_subst_split_left; auto.
      split; auto.
        apply wfv_lgamma_subst_slval; auto.
          apply dom_lenv_split in J.
          rewrite J in H0; auto.
    SCase "lenv_split_right".
      assert (J:=H7).
      apply IHHwflg in H7. clear IHHwflg.
      destruct H7 as [lgsubst1 [lgsubst2 [J1 [J2 J3]]]].
      exists lgsubst1. exists ([(x,e)]++lgsubst2).
      split.
        apply lgamma_subst_split_right; auto.
      split; auto.
        apply wfv_lgamma_subst_slval; auto.
          apply dom_lenv_split in J.
          rewrite J in H0; auto.
  Case "wfv_lgamma_subst_skind".
    assert (J:=Hsplit).
    assert (K:=Hwflg).
    apply wfv_lgamma_subst__wf_lgamma_subst in K; auto.
    apply wf_lgamma_subst__nfv with (x:=X) in K; auto. 
    rewrite_env ((E'++[(X, bind_kn k)])++E) in Hsplit.
    apply IHHwflg in Hsplit. clear IHHwflg.
    destruct Hsplit as [lgsubst1 [lgsubst2 [J1 [J2 J3]]]].
    exists lgsubst1. exists lgsubst2.
    split.
      apply lgamma_subst_split_nonlin_weakening_typ_tail; auto.
        apply wfv_lgamma_subst__wf_lgamma_subst; auto.
    split.
      apply wfv_lgamma_subst_skind; auto.
        apply dom_lenv_split in J.
        rewrite J in H0; auto.
      apply wfv_lgamma_subst_skind; auto.
        apply dom_lenv_split in J.
        rewrite J in H0; auto.
Qed.

Lemma F_ciu_eq__congr_app : forall E lE1 lE2 lE e1 e1' e2 e2' K t1 t2,
   F_ciu_eq E lE1 e1 e1' (typ_arrow K t1 t2) ->
   value e1' ->
   F_ciu_eq E lE2 e2 e2' t1 -> 
   lenv_split E lE1 lE2 lE ->
   F_ciu_eq E lE (exp_app e1 e2) (exp_app e1' e2') t2.
Proof.
   intros E lE1 lE2 lE e1 e1' e2 e2' K t1 t2 Hciu1 Hv1' Hciu2 Split.
   destruct Hciu1 as [Typ1 [Typ1' Heq1]].
   destruct Hciu2 as [Typ2 [Typ2' Heq2]].
   split; eauto.
   split; eauto.
    intros dsubst gsubst lgsubst Hwflg.
    apply wfv_lgamma_subst_split with (lE1:=lE1) (lE2:=lE2) (E':=nil) in Hwflg; auto.
    destruct Hwflg as [lgsubst1 [lgsubst2 [Hsplit [Hwflg1 Hwflg2]]]].
    assert (apply_delta_subst dsubst
            (apply_gamma_subst gsubst
              (apply_gamma_subst lgsubst (exp_app e1 e2)) 
            ) =
            apply_delta_subst dsubst
            (apply_gamma_subst gsubst
              (exp_app 
                (apply_gamma_subst lgsubst1 e1)
                (apply_gamma_subst lgsubst2 e2)
              )               
            )
          ) as EQ.
     simpl_commut_subst in *.
     rewrite lgamma_subst_split_subst' with (lgsubst1:=lgsubst1) (lgsubst2:=lgsubst2) (E:=E) (lE:=lE) (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst); auto.
     rewrite lgamma_subst_split_subst with (lgsubst1:=lgsubst1) (lgsubst2:=lgsubst2) (E:=E) (lE:=lE) (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst); auto.
     rewrite lgamma_subst_split_shuffle2 with (lgsubst:=lgsubst) (lgsubst1:=lgsubst1) (E:=E) (lE:=lE) ; auto.
     apply typing_subst with (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst1) in Typ1; try solve [auto | apply wfv_lgamma_subst__wf_lgamma_subst; auto].
     apply typing_subst with (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst2) in Typ2; try solve [auto | apply wfv_lgamma_subst__wf_lgamma_subst; auto].
     erewrite gamma_subst_closed_exp; eauto.
     rewrite lgamma_subst_split_shuffle1 with (lgsubst:=lgsubst) (lgsubst2:=lgsubst2) (E:=E) (lE:=lE) (e:=apply_gamma_subst lgsubst2 e2) ; auto.
     erewrite gamma_subst_closed_exp with 
         (e:=apply_delta_subst dsubst
            (apply_gamma_subst gsubst
              (apply_gamma_subst lgsubst2 e2))
          ); eauto.
    repeat(rewrite EQ). clear EQ.
    assert (apply_delta_subst dsubst
            (apply_gamma_subst gsubst
              (apply_gamma_subst lgsubst (exp_app e1' e2')) 
            ) =
            apply_delta_subst dsubst
            (apply_gamma_subst gsubst
              (exp_app 
                (apply_gamma_subst lgsubst1 e1')
                (apply_gamma_subst lgsubst2 e2')
              )               
            )
          ) as EQ.
     simpl_commut_subst in *.
     rewrite lgamma_subst_split_subst' with (lgsubst1:=lgsubst1) (lgsubst2:=lgsubst2) (E:=E) (lE:=lE) (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst); auto.
     rewrite lgamma_subst_split_subst with (lgsubst1:=lgsubst1) (lgsubst2:=lgsubst2) (E:=E) (lE:=lE) (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst); auto.
     rewrite lgamma_subst_split_shuffle2 with (lgsubst:=lgsubst) (lgsubst1:=lgsubst1) (E:=E) (lE:=lE) ; auto.
     apply typing_subst with (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst1) in Typ1'; try solve [auto | apply wfv_lgamma_subst__wf_lgamma_subst; auto].
     apply typing_subst with (dsubst:=dsubst) (gsubst:=gsubst) (lgsubst:=lgsubst2) in Typ2'; try solve [auto | apply wfv_lgamma_subst__wf_lgamma_subst; auto].
     erewrite gamma_subst_closed_exp; eauto.
     rewrite lgamma_subst_split_shuffle1 with (lgsubst:=lgsubst) (lgsubst2:=lgsubst2) (E:=E) (lE:=lE) (e:=apply_gamma_subst lgsubst2 e2') ; auto.
     erewrite gamma_subst_closed_exp with 
         (e:=apply_delta_subst dsubst
            (apply_gamma_subst gsubst
              (apply_gamma_subst lgsubst2 e2'))
          ); eauto.
    repeat(rewrite EQ). clear EQ.
    assert (J:=Hwflg1).
    apply Heq1 in Hwflg1; auto. 
    simpl_commut_subst in *.
    apply F_vobservational_eq__congr_app with (lE1:=nil) (lE2:=nil) (K:=K) (t1:=apply_delta_subst_typ dsubst t1); auto.
      apply wfv_lgamma_subst__wf_lgamma_subst in J.
      eapply delta_gamma_lgamma_subst_value; eauto.
        apply wf_lgamma_subst__wf_subst in J. destruct J; auto.
Qed.

Lemma F_ciu_eq__congr_tapp : forall E lE e1 e1' t2 K t,
   F_ciu_eq E lE e1 e1' (typ_all K t) ->
   wf_typ E t2 K ->
   F_ciu_eq E lE (exp_tapp e1 t2) (exp_tapp e1' t2) (open_tt t t2).
Proof.
  intros E lE e1 e1' t2 K t Heq Wft2.
  destruct Heq as [Typ [Typ' Heq]].
  split; eauto.
  split; eauto.
    intros dsubst gsubst lgsubst Hwflg.
    simpl_commut_subst in *.
    assert (J:=Hwflg).
    apply wfv_lgamma_subst__wf_subst in J.
    destruct J as [_ J].
    rewrite commut_delta_subst_open_tt with (dE:=E); auto.
    apply Heq in Hwflg; auto. 
    simpl_commut_subst in *.
    apply wft_subst with (dsubst:=dsubst) in Wft2; auto.
    apply F_vobservational_eq__congr_tapp with (K:=K); auto.
Qed.

Lemma F_ciu_eq__congr_fst : forall E lE e1 e1' e2 e2' t1 t2,
   F_ciu_eq E lE (exp_apair e1 e2) (exp_apair e1' e2') (typ_with t1 t2) ->
   F_ciu_eq E lE e1 e1' t1.
Proof.
  intros E lE e1 e1' e2 e2' t1 t2 Heq.
  destruct Heq as [Typ [Typ' Heq]].
  split.
    inversion Typ; subst; auto.
  split.
    inversion Typ'; subst; auto.

    intros dsubst gsubst lgsubst Hwflg.
    apply Heq in Hwflg; auto. 
    simpl_commut_subst in *.
    apply F_vobservational_eq__congr_fst in Hwflg; auto.
Qed.

Lemma F_ciu_eq__congr_snd : forall E lE e1 e1' e2 e2' t1 t2,
   F_ciu_eq E lE (exp_apair e1 e2) (exp_apair e1' e2') (typ_with t1 t2) ->
   F_ciu_eq E lE e2 e2' t2.
Proof.
  intros E lE e1 e1' e2 e2' t1 t2 Heq.
  destruct Heq as [Typ [Typ' Heq]].
  split.
    inversion Typ; subst; auto.
  split.
    inversion Typ'; subst; auto.

    intros dsubst gsubst lgsubst Hwflg.
    apply Heq in Hwflg; auto. 
    simpl_commut_subst in *.
    apply F_vobservational_eq__congr_snd in Hwflg; auto.
Qed.

Definition P_F_related_terms__respect_for_ciueq (n:nat) := 
  forall t E rsubst dsubst dsubst' e1 e2 e1' e2',
  typ_size t = n ->
  F_Rsubst E rsubst dsubst dsubst' ->
  F_related_terms t rsubst dsubst dsubst' e1 e2 ->
  F_ciu_eq nil nil e1 e1' (apply_delta_subst_typ dsubst t) -> 
  F_ciu_eq nil nil e2 e2' (apply_delta_subst_typ dsubst' t) -> 
  F_related_terms t rsubst dsubst dsubst' e1' e2'.

Axiom Rel__respect_for_ciueq : forall E rsubst a R e1 e1' t1 e2 e2' t2,
  wf_rho_subst E rsubst ->
  binds a R rsubst ->
  F_ciu_eq nil nil e1 e1' t1 ->
  F_ciu_eq nil nil e2 e2' t2 ->
  R e1 e2 ->
  R e1' e2'.

Lemma _F_related_terms__respect_for_ciueq: forall n, P_F_related_terms__respect_for_ciueq n.
Proof.
  intro n.
  apply lt_wf_ind. clear n.
  intros n H.
  unfold P_F_related_terms__respect_for_ciueq in *.
  intros t E rsubst dsubst dsubst' e1 e2 e1' e2' Hsize HRsubst Hrel Hctx1 Hctx2.
  destruct Hrel as [v1 [v2 [Htypingv1 [Htypingv2 [Hn_e1v1 [Hn_e2v2 Hrel]]]]]].
  assert (exists v1', normalize e1' v1') as Hn_e1'v1'.
    apply strong_normalization with (t:=apply_delta_subst_typ dsubst t); auto.
       destruct Hctx1 as [J1 [J2 J3]]; auto.
  assert (exists v2', normalize e2' v2') as Hn_e2'v2'.
    apply strong_normalization with (t:=apply_delta_subst_typ dsubst' t); auto.
       destruct Hctx2 as [J1 [J2 J3]]; auto.
  destruct Hn_e1'v1' as [v1' Hn_e1'v1'].
  destruct Hn_e2'v2' as [v2' Hn_e2'v2'].
  exists v1'. exists v2'.
  split.
    destruct Hctx1 as [J1 [J2 J3]]; auto.
  split.
    destruct Hctx2 as [J1 [J2 J3]]; auto.
  split; auto.
  split; auto.
  assert (F_ciu_eq nil nil v1 v1' (apply_delta_subst_typ dsubst t)) as Hctxv1.
      apply F_ciu_eq__trans with (e':=e1).
        apply F_ciu_eq__sym.
        apply F_ciu_eq__mbeta.
          destruct Hctx1 as [J1 [J2 J3]]; auto.
          destruct Hn_e1v1; auto.
        apply F_ciu_eq__trans with (e':=e1'); auto.
          apply F_ciu_eq__mbeta.
            destruct Hctx1 as [J1 [J2 J3]]; auto.
            destruct Hn_e1'v1'; auto.
  assert (F_ciu_eq nil nil v2 v2' (apply_delta_subst_typ dsubst' t)) as Hctxv2.
      apply F_ciu_eq__trans with (e':=e2).
        apply F_ciu_eq__sym.
        apply F_ciu_eq__mbeta.
          destruct Hctx2 as [J1 [J2 J3]]; auto.
          destruct Hn_e2v2; auto.
        apply F_ciu_eq__trans with (e':=e2'); auto.
          apply F_ciu_eq__mbeta.
            destruct Hctx2 as [J1 [J2 J3]]; auto.
            destruct Hn_e2'v2'; auto.
  (typ_cases (destruct t) Case).
  Case "typ_bvar". (*bvar*)
  apply F_related_values_bvar_leq in Hrel; auto.
  Case "typ_fvar". (* fvar *)
  apply F_related_values_fvar_leq in Hrel.
  apply F_related_values_fvar_req.
  unfold In_rel in Hrel.
  destruct Hrel as [R0 [Hb [Hv1 [Hv2' Hr]]]]; subst; simpl.
  exists (R0).
  simpl_env.
  repeat(split; auto).
    destruct Hn_e1'v1'; auto.
    destruct Hn_e2'v2'; auto.
    apply Rel__respect_for_ciueq with (e1:=v1) (e2:=v2) (t1:=apply_delta_subst_typ dsubst a) (t2:=apply_delta_subst_typ dsubst' a) (a:=a) (rsubst:=rsubst) (E:=E); auto.
      apply F_Rsubst__wf_subst in HRsubst.
      decompose [prod] HRsubst; auto.
  Case "typ_arrow". (* arrow *)
  apply F_related_values_arrow_leq in Hrel.
  apply F_related_values_arrow_req.  
  destruct Hrel as [Hv1 [Hv2 Harrow]]; subst.
  repeat(split; auto; simpl_env in *).
    destruct Hn_e1'v1'; auto.
    destruct Hn_e2'v2'; auto.
    intros x x' Htypingx Htypingx' Harrow'.
    destruct (@Harrow x x') as [u [u' [Hnorm_vxu [Hnorm_v'x'u' Hrel_wft1]]]]; auto.
    assert (typ_size t2 < typ_size (typ_arrow k t1 t2)) as G1. simpl. omega.
    apply H with (e1:=exp_app v1 x) (e2:=exp_app v2 x') (t:=t2) (E:=E)
                        (e1':=exp_app v1' x) (e2':=exp_app v2' x')
                        (rsubst:=rsubst) (dsubst:=dsubst) (dsubst':=dsubst') in G1; auto.
      destruct G1 as [v3 [v3' [Typing3 [Typing3' [Hn_v3 [Hn_v3' G1]]]]]].
      exists v3. exists v3'.
      split; auto.

      exists u. exists u'.
      split.
        apply typing_app with (D1:=nil) (D2:=nil) (T1:=apply_delta_subst_typ dsubst t1) (K:=k); auto.
          simpl_commut_subst in Htypingv1.
          apply preservation_normalization with (e:=e1); auto.
      split.
        apply typing_app with (D1:=nil) (D2:=nil) (T1:=apply_delta_subst_typ dsubst' t1) (K:=k); auto.
          simpl_commut_subst in Htypingv2.
          apply preservation_normalization with (e:=e2); auto.
      split; auto.

      simpl_commut_subst in Hctxv1.
      apply F_ciu_eq__congr_app with (lE1:=nil) (lE2:=nil) (t1:=apply_delta_subst_typ dsubst t1) (K:=k); auto.
        destruct Hn_e1'v1'; auto.
        apply F_ciu_eq__refl; auto.

      simpl_commut_subst in Hctxv2.
      apply F_ciu_eq__congr_app with (lE1:=nil) (lE2:=nil) (t1:=apply_delta_subst_typ dsubst' t1) (K:=k); auto.
        destruct Hn_e2'v2'; auto.
        apply F_ciu_eq__refl; auto.
  Case "typ_all". (* all *)
  apply F_related_values_all_leq in Hrel.
  apply F_related_values_all_req.  
  destruct Hrel as [Hv1 [Hv2 [L Hall]]]; subst.
  repeat(split; auto; simpl_env in *).
    destruct Hn_e1'v1'; auto.
    destruct Hn_e2'v2'; auto.
    exists (L `union` fv_env E).
    intros X t2 t2' R Fr Hwfr Hfv.
    assert (X `notin` L)  as XnL. auto.
    destruct (@Hall X t2 t2' R XnL) as [w0 [w'0 [Hnorm_vt2w0 [Hnorm_v't2'w'0 Hrel_wft]]]]; auto.
    assert (typ_size (open_tt t X) < typ_size (typ_all k t)) as G. 
      simpl. rewrite open_tt_typ_size_eq. omega.
    apply H with (e1:=exp_tapp v1 t2) (e2:=exp_tapp v2 t2') (t:=open_tt t X)
                        (e1':=exp_tapp v1' t2) (e2':=exp_tapp v2' t2') (E:=[(X, bind_kn k)]++E)
                        (rsubst:=[(X, R)]++rsubst) (dsubst:=[(X, t2)]++dsubst) (dsubst':=[(X, t2')]++dsubst') in G; auto.
      destruct G as [v3 [v3' [Typing3 [Typing3' [Hn_v3 [Hn_v3' G]]]]]].
      exists v3. exists v3'.
      split; auto.

      apply F_Rsubst_rel; auto.

      exists w0. exists w'0.
      simpl.
      assert (type t2) as type2.
        apply wfr_left_inv in Hwfr.
        apply type_from_wf_typ in Hwfr; auto.
      rewrite subst_tt_open_tt; auto.
      rewrite <- subst_tt_fresh; auto.
      simpl.
      destruct (X==X); subst; try solve [contradict n; auto].
      assert (type t2') as type2'.
        apply wfr_right_inv in Hwfr.
        apply type_from_wf_typ in Hwfr; auto.
      rewrite subst_tt_open_tt; auto.
      rewrite <- subst_tt_fresh; auto.
      simpl.
      destruct (X==X); subst; try solve [contradict n; auto].
      assert (J:=HRsubst).
      apply F_Rsubst__wf_subst in J.
      decompose [prod] J.
      rewrite commut_delta_subst_open_tt with (dE:=E); auto.
      rewrite delta_subst_closed_typ with (t:=t2) (K:=k); eauto using wfr_left_inv.
      rewrite commut_delta_subst_open_tt with (dE:=E); auto.
      rewrite delta_subst_closed_typ with (t:=t2') (K:=k); eauto using wfr_right_inv.
      split.
        apply typing_tapp with (K:=k); eauto using wfr_left_inv.
          simpl_commut_subst in Htypingv1.
          apply preservation_normalization with (e:=e1); auto.     
      split.
        apply typing_tapp with (K:=k); eauto using wfr_right_inv.
          simpl_commut_subst in Htypingv2.
          apply preservation_normalization with (e:=e2); auto.
      split; auto.

      simpl.
      assert (wf_typ nil t2 k) as Wft2.
        apply wfr_left_inv in Hwfr. auto.
      assert (type t2) as type2.
        apply wfr_left_inv in Hwfr. auto.
        apply type_from_wf_typ in Hwfr; auto.
      rewrite subst_tt_open_tt; auto.
      rewrite <- subst_tt_fresh; auto.
      simpl.
      destruct (X==X); subst; try solve [contradict n; auto].
      assert (J:=HRsubst).
      apply F_Rsubst__wf_subst in J.
      decompose [prod] J.
      rewrite commut_delta_subst_open_tt with (dE:=E); auto.
      rewrite delta_subst_closed_typ with (t:=t2) (K:=k); eauto using wfr_left_inv.
      simpl_commut_subst in Hctxv1.
      apply F_ciu_eq__congr_tapp with (K:=k); auto.

      simpl.
      assert (wf_typ nil t2' k) as Wft2'.
        apply wfr_right_inv in Hwfr. auto.
      assert (type t2') as type2'.
        apply wfr_right_inv in Hwfr.
        apply type_from_wf_typ in Hwfr; auto.
      rewrite subst_tt_open_tt; auto.
      rewrite <- subst_tt_fresh; auto.
      simpl.
      destruct (X==X); subst; try solve [contradict n; auto].
      assert (J:=HRsubst).
      apply F_Rsubst__wf_subst in J.
      decompose [prod] J.
      rewrite commut_delta_subst_open_tt with (dE:=E); auto.
      rewrite delta_subst_closed_typ with (t:=t2') (K:=k); eauto using wfr_right_inv.
      simpl_commut_subst in Hctxv2.
      apply F_ciu_eq__congr_tapp with (K:=k); auto.
  Case "typ_with". (* with *)
  apply F_related_values_with_leq in Hrel.
  apply F_related_values_with_req.
  destruct Hrel as [Hv [Hv' [f1 [f2 [f1' [f2' [Heq [Heq' 
                                [[u1 [u1' [Hnorm_f1u1 [Hnorm_f1'u1' Hrel_wft1]]]] 
                                 [u2 [u2' [Hnorm_F2u2 [Hnorm_f2'u2' Hrel_wft2]]]]]
                              ]]]]]]]]; subst.
  repeat(split; auto; simpl_env in *).
    destruct Hn_e1'v1'; auto.
    destruct Hn_e2'v2'; auto.
   
    assert (exists g1, exists g2, v1' = exp_apair g1 g2) as J.
      simpl_commut_subst in Hctxv1.
      assert (J:=Hctxv1). destruct J as [J1 [J2 J3]].
      assert (J:=Hn_e1'v1'). destruct J as [J4 J5].
      apply canonical_form_with in J2; auto.
    assert (exists g1', exists g2', v2' = exp_apair g1' g2') as J'.
      simpl_commut_subst in Hctxv2.
      assert (J':=Hctxv2). destruct J' as [J1 [J2 J3]].
      assert (J':=Hn_e2'v2'). destruct J' as [J4 J5].
      apply canonical_form_with in J2; auto.
    destruct J as [g1 [g2 J]].
    destruct J' as [g1' [g2' J']]. 
    subst.
    exists g1. exists g2. exists g1'. exists g2'.
    split; auto.
    split; auto.
    split.
      assert (typ_size t1 < typ_size (typ_with t1 t2)) as G1. simpl. omega.
      apply H with (e1:=f1) (e2:=f1') (t:=t1) (E:=E)
                        (e1':=g1) (e2':=g1')
                        (rsubst:=rsubst) (dsubst:=dsubst) (dsubst':=dsubst') in G1; auto.
      destruct G1 as [v3 [v3' [Typing3 [Typing3' [Hn_v3 [Hn_v3' G1]]]]]].
      exists v3. exists v3'.
      split; auto.

      exists u1. exists u1'.
      split.
        simpl_commut_subst in Htypingv1.
        apply preservation_normalization with (v:=exp_apair f1 f2) in Htypingv1; auto.     
        inversion Htypingv1; subst; auto.
      split.
        simpl_commut_subst in Htypingv2.
        apply preservation_normalization with (v:=exp_apair f1' f2') in Htypingv2; auto.     
        inversion Htypingv2; subst; auto.
      split; auto.

      simpl_commut_subst in Hctxv1.
      apply F_ciu_eq__congr_fst in Hctxv1; auto.

      simpl_commut_subst in Hctxv2.
      apply F_ciu_eq__congr_fst in Hctxv2; auto.

      assert (typ_size t2 < typ_size (typ_with t1 t2)) as G2. simpl. omega.
      apply H with (e1:=f2) (e2:=f2') (t:=t2) (E:=E)
                        (e1':=g2) (e2':=g2')
                        (rsubst:=rsubst) (dsubst:=dsubst) (dsubst':=dsubst') in G2; auto.
      destruct G2 as [v3 [v3' [Typing3 [Typing3' [Hn_v3 [Hn_v3' G2]]]]]].
      exists v3. exists v3'.
      split; auto.

      exists u2. exists u2'.
      split.
        simpl_commut_subst in Htypingv1.
        apply preservation_normalization with (v:=exp_apair f1 f2) in Htypingv1; auto.     
        inversion Htypingv1; subst; auto.
      split.
        simpl_commut_subst in Htypingv2.
        apply preservation_normalization with (v:=exp_apair f1' f2') in Htypingv2; auto.     
        inversion Htypingv2; subst; auto.
      split; auto.

      simpl_commut_subst in Hctxv1.
      apply F_ciu_eq__congr_snd in Hctxv1; auto.

      simpl_commut_subst in Hctxv2.
      apply F_ciu_eq__congr_snd in Hctxv2; auto.
Qed.  

Lemma F_related_terms__respect_for_ciueq : forall t E rsubst dsubst dsubst' e1 e2 e1' e2',
  F_Rsubst E rsubst dsubst dsubst' ->
  F_related_terms t rsubst dsubst dsubst' e1 e2 ->
  F_ciu_eq nil nil e1 e1' (apply_delta_subst_typ dsubst t) -> 
  F_ciu_eq nil nil e2 e2' (apply_delta_subst_typ dsubst' t) -> 
  F_related_terms t rsubst dsubst dsubst' e1' e2'.
Proof.
  intros t E rsubst dsubst dsubst' e1 e2 e1' e2' HRsubst Hrel Hctx1 Hctx2.
  assert (P_F_related_terms__respect_for_ciueq (typ_size t)) as J.
    apply (@_F_related_terms__respect_for_ciueq (typ_size t)).
  unfold P_F_related_terms__respect_for_ciueq in J.
  eapply J; eauto.
Qed.

Lemma F_related_subst__vinversion:
  forall (E:env) (lE:lenv) (rsubst:rho_subst) (dsubst:delta_subst) (dsubst':delta_subst) gsubst gsubst' lgsubst lgsubst',
  F_related_subst E lE gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' ->
  ((wf_delta_subst E dsubst) * (wf_delta_subst E dsubst') *
   (wfv_lgamma_subst E lE dsubst gsubst lgsubst)* (wfv_lgamma_subst E lE dsubst' gsubst' lgsubst') *
   (wf_rho_subst E rsubst) * (wf_env E))%type.
Proof.
  intros E lE rsubst dsubst dsubst' gsubst gsubst' lgsubst lgsubst' HRsub.
  (F_related_subst_cases (induction HRsub) Case).
    repeat (split; auto).
  Case "F_related_subst_kind".
    decompose [prod] IHHRsub.
    repeat (split; eauto using wfr_left_inv, wfr_right_inv).
      apply wf_delta_subst_styp; eauto using wfr_left_inv.
      apply wf_delta_subst_styp; eauto using wfr_right_inv.
      apply wfv_lgamma_subst_skind; eauto using wfr_left_inv.
      apply wfv_lgamma_subst_skind; eauto using wfr_right_inv.
      apply wf_rho_subst_srel; auto.
      apply wf_env_kn; auto.
  Case "F_related_subst_typ".
    decompose [prod] IHHRsub.
    repeat (split; eauto).
      apply wf_delta_subst_skip; auto. 
      apply wf_delta_subst_skip; auto. 
      apply wfv_lgamma_subst_sval; auto. 
         apply F_related_values_inversion in H1. destruct H1; auto.
      apply wfv_lgamma_subst_sval; auto. 
         apply F_related_values_inversion in H1. destruct H1; auto.
      apply wf_rho_subst_skip; auto.
      apply wf_env_typ; auto.
  Case "F_related_subst_ltyp".
    decompose [prod] IHHRsub.
    repeat (split; eauto).
      apply wfv_lgamma_subst_slval; auto. 
         apply F_related_values_inversion in H1. destruct H1; auto.
      apply wfv_lgamma_subst_slval; auto. 
         apply F_related_values_inversion in H1. destruct H1; auto.
Qed.

Lemma F_logical_related__respect_for_ciueq : forall E lE e1 e2 e1' e2' t,
  F_logical_related E lE e1 e2 t ->
  F_ciu_eq E lE e1 e1' t -> 
  F_ciu_eq E lE e2 e2' t -> 
  F_logical_related E lE e1' e2' t.
Proof.
  intros E lE e1 e2 e1' e2' t Hlrel Hciueq Hciueq'.
  destruct Hlrel as [Typ1 [Typ2 Hlrel]].
  assert (J:=Hciueq).
  destruct J as [_ [Typ1' J1]].
  assert (J':=Hciueq').
  destruct J' as [_ [Typ2' J2]].
  split; auto.
  split; auto.
    intros dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst H_relsubst H_Rsubst.
    assert (J:=@Hlrel dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst H_relsubst H_Rsubst).
    apply F_related_terms__respect_for_ciueq with
      (E:=E)
      (e1:=(apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e1))))
      (e2:=(apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e2)))); auto.
      split; auto.
        apply typing_subst with (E:=E) (D:=lE); auto.
          apply F_related_subst__vinversion in H_relsubst.
          decompose [prod] H_relsubst; apply wfv_lgamma_subst__wf_lgamma_subst; auto.
      split; auto.
        apply typing_subst with (E:=E) (D:=lE); auto.
          apply F_related_subst__vinversion in H_relsubst.
          decompose [prod] H_relsubst; apply wfv_lgamma_subst__wf_lgamma_subst; auto.

        intros dsubst0 gsubst0 lgsubst0 Hwflg0.
        apply F_related_subst__vinversion in H_relsubst.
        decompose [prod] H_relsubst; auto.
        apply typing_subst with (dsubst:=dsubst)(gsubst:=gsubst)(lgsubst:=lgsubst) in Typ1; try solve [auto | apply wfv_lgamma_subst__wf_lgamma_subst; auto].
        rewrite gamma_subst_closed_exp with (e:=(apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e1)))) (t:=apply_delta_subst_typ dsubst t); auto.
        rewrite gamma_subst_closed_exp with (e:=(apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e1)))) (t:=apply_delta_subst_typ dsubst t); auto.
        rewrite delta_subst_closed_exp with (e:=(apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e1)))) (t:=apply_delta_subst_typ dsubst t); auto.        
        apply typing_subst with (dsubst:=dsubst)(gsubst:=gsubst)(lgsubst:=lgsubst) in Typ1'; try solve [auto | apply wfv_lgamma_subst__wf_lgamma_subst; auto].
        rewrite gamma_subst_closed_exp with (e:=(apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e1')))) (t:=apply_delta_subst_typ dsubst t); auto.
        rewrite gamma_subst_closed_exp with (e:=(apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e1')))) (t:=apply_delta_subst_typ dsubst t); auto.
        rewrite delta_subst_closed_exp with (e:=(apply_delta_subst dsubst (apply_gamma_subst gsubst (apply_gamma_subst lgsubst e1')))) (t:=apply_delta_subst_typ dsubst t); auto.        
        rewrite delta_subst_closed_typ with (t:=apply_delta_subst_typ dsubst t) (K:=kn_lin); auto.        

      split; auto.
        apply typing_subst with (E:=E) (D:=lE); auto.
          apply F_related_subst__inversion in H_relsubst.
          decompose [prod] H_relsubst; auto.
      split; auto.
        apply typing_subst with (E:=E) (D:=lE); auto.
          apply F_related_subst__inversion in H_relsubst.
          decompose [prod] H_relsubst; auto.

        intros dsubst0 gsubst0 lgsubst0 Hwflg0.
        apply F_related_subst__vinversion in H_relsubst.
        decompose [prod] H_relsubst; auto.
        apply typing_subst with (dsubst:=dsubst')(gsubst:=gsubst')(lgsubst:=lgsubst') in Typ2; try solve [auto | apply wfv_lgamma_subst__wf_lgamma_subst; auto].
        rewrite gamma_subst_closed_exp with (e:=(apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e2)))) (t:=apply_delta_subst_typ dsubst' t); auto.
        rewrite gamma_subst_closed_exp with (e:=(apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e2)))) (t:=apply_delta_subst_typ dsubst' t); auto.
        rewrite delta_subst_closed_exp with (e:=(apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e2)))) (t:=apply_delta_subst_typ dsubst' t); auto.        
        apply typing_subst with (dsubst:=dsubst')(gsubst:=gsubst')(lgsubst:=lgsubst') in Typ2'; try solve [auto | apply wfv_lgamma_subst__wf_lgamma_subst; auto].
        rewrite gamma_subst_closed_exp with (e:=(apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e2')))) (t:=apply_delta_subst_typ dsubst' t); auto.
        rewrite gamma_subst_closed_exp with (e:=(apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e2')))) (t:=apply_delta_subst_typ dsubst' t); auto.
        rewrite delta_subst_closed_exp with (e:=(apply_delta_subst dsubst' (apply_gamma_subst gsubst' (apply_gamma_subst lgsubst' e2')))) (t:=apply_delta_subst_typ dsubst' t); auto.        
        rewrite delta_subst_closed_typ with (t:=apply_delta_subst_typ dsubst' t) (K:=kn_lin); auto.        
Qed.

Lemma F_ciu_eq__F_logical_related : forall E lE e e' t,
  F_ciu_eq E lE e e' t ->
  F_logical_related E lE e e' t.
Proof.
  intros E lE e e' t Hciueq.
  assert (J:=Hciueq).
  destruct J as [Typ [Typ' J]].
  assert (Hciueq':=@F_ciu_eq__refl E lE e t Typ).
  assert (F_logical_related E lE e e t) as Hrel.
    split; auto.
    split; auto.
      intros dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst H_relsubst H_Rsubst.
      apply parametricity with (E:=E) (lE:=lE); auto.
  apply F_logical_related__respect_for_ciueq with (e1:=e) (e2:=e); auto.
Qed.

Lemma F_logical_related__complete : forall E lE e e' t,
  F_observational_eq E lE e e' t ->
  F_logical_related E lE e e' t.
Proof.
  intros E lE e e' t Hctx.
  apply F_ciu_eq__F_logical_related.
  apply F_observational_eq__F_ciu_eq in Hctx; auto.
Qed.

Lemma F_ciu_eq__F_observational_eq : forall E lE e e' t,
  F_ciu_eq E lE e e' t ->
  F_observational_eq E lE e e' t.
Proof.
  intros E lE e e' t Hciu.
  apply F_logical_related__sound.
  apply F_ciu_eq__F_logical_related; auto.
Qed.

(***************************************************************)
(*                                               Double Negation                                        *)
(***************************************************************)
(* nA = \X. (A->X)->X *)
Parameter K : kn.
Parameter K' : kn.
Parameter A : typ.
Definition dnegA := (typ_all K (typ_arrow K (typ_arrow K' A (typ_bvar 0)) (typ_bvar 0))).

Axiom wftA : wf_typ nil A K.

Lemma wftdnegA : wf_typ nil dnegA K.
Proof.
  unfold dnegA.
  assert (HwftA:=wftA).
  apply wf_typ_all with (L:={}).
      intros X HfvX.
      unfold open_tt. simpl. 
      assert (J:=HwftA).
      apply type_from_wf_typ in J.
      rewrite <- open_tt_rec_type; auto.
      apply wf_typ_arrow with (K1:=K') (K2:=K); auto.
        apply wf_typ_arrow with (K1:=K) (K2:=K); auto.
          apply wf_typ_weaken_head with (F:=X~bind_kn K) in HwftA; auto.
Qed.

Hint Resolve wftA wftdnegA.

(* i = \x: A. \X. \g : A-> X. g x : A -> nA *)
Definition fun_to_dnegA := 
  exp_abs 
    kn_nonlin
        A 
    (exp_tabs K
        (exp_abs K
             (typ_arrow K' A (typ_bvar 0)) 
             (exp_app (exp_bvar 0) (exp_bvar 1))
        )
    ).

(* j = \h: nA. h[A] (\x:A. x)  : nA -> A *)
Definition fun_from_dnegA := 
  exp_abs 
    kn_nonlin
    dnegA
    (exp_app 
        (exp_tapp (exp_bvar 0)  A)
        (exp_abs K' A (exp_bvar 0))
    ).

Lemma typing_fun_to_dneg :
  typing nil nil fun_to_dnegA (typ_arrow kn_nonlin A dnegA).
Proof.
  assert (HwftA := wftA).
  unfold fun_to_dnegA. unfold dnegA.
  destruct K.
  Case "K=kn_lin".
  apply typing_labs with (L := {}); auto.
  intros x Hfvx.
    unfold open_ee. simpl. 
    apply typing_tabs with (L := singleton x).
    intros X HfvX.
      unfold open_te. simpl. 
      apply value_abs.
      apply expr_abs with (L:=singleton x `union` singleton X).
        apply type_from_wf_typ in HwftA.
        rewrite <- open_tt_rec_type; auto.

        intros x0 x0n.
        unfold open_ee. simpl. auto.       

    intros X HfvX.
    unfold open_te. unfold open_tt. simpl. 
    assert (J:=HwftA).
    apply type_from_wf_typ in J.
    rewrite <- open_tt_rec_type; auto.
    destruct K'.
    SCase "K'=kn_lin".
      apply typing_labs with (L := singleton x `union` singleton X).
        apply wf_typ_arrow with (K1:=kn_lin) (K2:=kn_lin); auto.
          rewrite_env (nil ++ [(X, bind_kn kn_lin)] ++ nil).
          apply wf_typ_weakening; auto.

        intros x0 Hfvx0.
           unfold open_ee. simpl.
           apply typing_app with (T1:=A)(K:=kn_lin) (D1:=[(x0, lbind_typ (typ_arrow kn_lin A X))]) (D2:=[(x, lbind_typ A)]); auto.
             apply typing_lvar.
               rewrite_env ([(x0, lbind_typ (typ_arrow kn_lin A X))]++nil).
               apply wf_lenv_typ; auto.
                 apply wf_lenv_empty; auto.
                   rewrite_env ([(X, bind_kn kn_lin)]++nil).
                   apply wf_env_kn; auto.
                apply wf_typ_arrow with (K1:=kn_lin) (K2:=kn_lin); auto.
                  rewrite_env (nil ++ [(X, bind_kn kn_lin)] ++ nil).
                  apply wf_typ_weakening; auto.
             apply typing_lvar.
               rewrite_env ([(x, lbind_typ A)]++nil).
               apply wf_lenv_typ; auto.
                 apply wf_lenv_empty; auto.
                   rewrite_env ([(X, bind_kn kn_lin)]++nil).
                   apply wf_env_kn; auto.
                 rewrite_env (nil ++ [(X, bind_kn kn_lin)] ++ nil).
                apply wf_typ_weakening; auto.
             rewrite_env ([(x0, lbind_typ (typ_arrow kn_lin A X))]++[(x, lbind_typ A)]++nil).
             rewrite_env ([(x0, lbind_typ (typ_arrow kn_lin A X))]++nil).
             rewrite_env ([(x, lbind_typ A)]++nil).
             apply lenv_split_left; auto.
               apply lenv_split_right; auto.
                 apply lenv_split_empty; auto.
                   rewrite_env ([(X, bind_kn kn_lin)]++nil).
                   apply wf_env_kn; auto.
                 rewrite_env (nil ++ [(X, bind_kn kn_lin)] ++ nil).
                 apply wf_typ_weakening; auto.
              apply wf_typ_arrow with (K1:=kn_lin) (K2:=kn_lin); auto.
                rewrite_env (nil ++ [(X, bind_kn kn_lin)] ++ nil).
                apply wf_typ_weakening; auto.

        intros JJ. inversion JJ.
    SCase "K'=kn_nonlin".
      apply typing_abs with (L := singleton x `union` singleton X).
        apply wf_typ_arrow with (K1:=kn_lin) (K2:=kn_lin); auto.
          rewrite_env (nil ++ [(X, bind_kn kn_lin)] ++ nil).
          apply wf_typ_weakening; auto.

        intros x0 Hfvx0.
           unfold open_ee. simpl.
           apply typing_app with (T1:=A)(K:=kn_nonlin) (D1:=nil) (D2:=[(x, lbind_typ A)]); auto.
             apply typing_var; auto.
               rewrite_env ([(x0, bind_typ (typ_arrow kn_nonlin A X))]++[(X, bind_kn kn_lin)]).
               apply wf_env_typ; auto.
                   rewrite_env ([(X, bind_kn kn_lin)]++nil).
                   apply wf_env_kn; auto.
                apply wf_typ_arrow with (K1:=kn_lin) (K2:=kn_lin); auto.
                  rewrite_env (nil ++ [(X, bind_kn kn_lin)] ++ nil).
                  apply wf_typ_weakening; auto.
             apply typing_lvar.
               rewrite_env ([(x, lbind_typ A)]++nil).
               apply wf_lenv_typ; auto.
                 apply wf_lenv_empty; auto.
                   simpl_env.
                   apply wf_env_typ; auto.
                     rewrite_env ([(X, bind_kn kn_lin)]++nil).
                     apply wf_env_kn; auto.

                     apply wf_typ_arrow with (K1:=kn_lin) (K2:=kn_lin); auto.
                       rewrite_env (nil ++ [(X, bind_kn kn_lin)] ++ nil).
                       apply wf_typ_weakening; auto.
                 rewrite_env (nil ++ ([(x0, bind_typ (typ_arrow kn_nonlin A X))]++[(X, bind_kn kn_lin)]) ++ nil).
                apply wf_typ_weakening; auto.
             simpl_env.
             rewrite_env ([(x, lbind_typ A)]++nil).
             rewrite_env ([(x, lbind_typ A)]++nil).
             apply lenv_split_right; auto.
               apply lenv_split_empty; auto.
                   simpl_env.
                   apply wf_env_typ; auto.
                     rewrite_env ([(X, bind_kn kn_lin)]++nil).
                     apply wf_env_kn; auto.

                     apply wf_typ_arrow with (K1:=kn_lin) (K2:=kn_lin); auto.
                       rewrite_env (nil ++ [(X, bind_kn kn_lin)] ++ nil).
                       apply wf_typ_weakening; auto.
                 rewrite_env (nil ++ ([(x0, bind_typ (typ_arrow kn_nonlin A X))]++[(X, bind_kn kn_lin)]) ++nil).
                 apply wf_typ_weakening; auto.

        intros JJ. inversion JJ.
  Case "K=kn_nonlin".
  apply typing_abs with (L := {}); auto.
  intros x Hfvx.
    unfold open_ee. simpl. 
    apply typing_tabs with (L := singleton x).
    intros X HfvX.
      unfold open_te. simpl. 
      apply value_abs.
      apply expr_abs with (L:=singleton x `union` singleton X).
        apply type_from_wf_typ in HwftA.
        rewrite <- open_tt_rec_type; auto.

        intros x0 x0n.
        unfold open_ee. simpl. auto.       

    intros X HfvX.
    unfold open_te. unfold open_tt. simpl. 
    assert (J:=HwftA).
    apply type_from_wf_typ in J.
    rewrite <- open_tt_rec_type; auto.
    destruct K'.
    SCase "K'=kn_lin".
      apply typing_labs with (L := singleton x `union` singleton X); auto.
        apply wf_typ_arrow with (K1:=kn_nonlin) (K2:=kn_nonlin); auto.
          rewrite_env (nil ++ ([(X, bind_kn kn_nonlin)]++[(x, bind_typ A)]) ++ nil).
          apply wf_typ_weakening; auto.

        intros x0 Hfvx0.
           unfold open_ee. simpl.
           apply typing_app with (T1:=A)(K:=kn_lin) (D1:=[(x0, lbind_typ (typ_arrow kn_lin A X))]) (D2:=nil); auto.
             apply typing_lvar.
               rewrite_env ([(x0, lbind_typ (typ_arrow kn_lin A X))]++nil).
               apply wf_lenv_typ; auto.
                 apply wf_lenv_empty; auto.
                   simpl_env.
                   apply wf_env_kn; auto.
                      rewrite_env ([(x, bind_typ A)] ++ nil).
                     apply wf_env_typ; auto.
                apply wf_typ_arrow with (K1:=kn_nonlin) (K2:=kn_nonlin); auto.
                  rewrite_env (nil ++ ([(X, bind_kn kn_nonlin)] ++ [(x, bind_typ A)]) ++ nil).
                  apply wf_typ_weakening; auto.
             apply typing_var; auto.
               simpl_env.
               apply wf_env_kn; auto.
                 rewrite_env ([(x, bind_typ A)] ++ nil).
                 apply wf_env_typ; auto.
             simpl_env.
             rewrite_env ([(x0, lbind_typ (typ_arrow kn_lin A X))]++nil).
             apply lenv_split_left; auto.
               apply lenv_split_empty; auto.
                 apply wf_env_kn; auto.
                   rewrite_env ([(x, bind_typ A)] ++ nil).
                   apply wf_env_typ; auto.
               apply wf_typ_arrow with (K1:=kn_nonlin) (K2:=kn_nonlin); auto.
                 rewrite_env (nil ++ ([(X, bind_kn kn_nonlin)] ++ [(x, bind_typ A)]) ++ nil).
                 apply wf_typ_weakening; auto.
    SCase "K'=kn_nonlin".
      apply typing_abs with (L := singleton x `union` singleton X); auto.
        apply wf_typ_arrow with (K1:=kn_nonlin) (K2:=kn_nonlin); auto.
          rewrite_env (nil ++ ([(X, bind_kn kn_nonlin)]++[(x, bind_typ A)]) ++ nil).
          apply wf_typ_weakening; auto.

        intros x0 Hfvx0.
           unfold open_ee. simpl.
           apply typing_app with (T1:=A)(K:=kn_nonlin) (D1:=nil) (D2:=nil); auto.
             apply typing_var; auto.
               rewrite_env ([(x0, bind_typ (typ_arrow kn_nonlin A X))]++[(X, bind_kn kn_nonlin)]++[(x, bind_typ A)]++nil).
               apply wf_env_typ; auto.
                 apply wf_typ_weakening; auto.
                    apply wf_typ_arrow with (K1:=kn_lin) (K2:=kn_nonlin); auto.
                      rewrite_env (nil ++ [(X, bind_kn kn_nonlin)] ++ nil).
                      apply wf_typ_weakening; auto.
             apply typing_var; auto.
               rewrite_env ([(x0, bind_typ (typ_arrow kn_nonlin A X))]++[(X, bind_kn kn_nonlin)]++[(x, bind_typ A)]++nil).
               apply wf_env_typ; auto.
                 apply wf_typ_weakening; auto.
                    apply wf_typ_arrow with (K1:=kn_lin) (K2:=kn_nonlin); auto.
                      rewrite_env (nil ++ [(X, bind_kn kn_nonlin)] ++ nil).
                      apply wf_typ_weakening; auto.
             rewrite_env ([(x0, bind_typ (typ_arrow kn_nonlin A X))]++[(X, bind_kn kn_nonlin)]++[(x, bind_typ A)]++nil).
            apply lenv_split_empty; auto.
               apply wf_env_typ; auto.
                 apply wf_typ_weakening; auto.
                    apply wf_typ_arrow with (K1:=kn_lin) (K2:=kn_nonlin); auto.
                      rewrite_env (nil ++ [(X, bind_kn kn_nonlin)] ++ nil).
                      apply wf_typ_weakening; auto.
Qed. 

Lemma typing_fun_from_dneg :
  typing nil nil fun_from_dnegA (typ_arrow kn_nonlin dnegA A).
Proof.
  assert (HwftA := wftA).
  assert (HwftdnegA := wftdnegA).
  unfold fun_from_dnegA. unfold dnegA in *.
  destruct K.
  Case "K=kn_lin".
  apply typing_labs with (L := {}); auto.
  intros x Hfvx.
    unfold open_ee. simpl. 
    apply typing_app with (T1:=typ_arrow K' A A) (K:=kn_lin) (D1:=([(x, lbind_typ (typ_all kn_lin (typ_arrow kn_lin (typ_arrow K' A 0) 0)))]) ++ nil) (D2:=nil); auto.
      assert (open_tt (typ_arrow kn_lin (typ_arrow K' A 0) 0) A = typ_arrow kn_lin (typ_arrow K'  A A) A) as Heq.
        unfold open_tt. simpl.
        apply type_from_wf_typ in HwftA.
        rewrite <- open_tt_rec_type; auto.
      rewrite <- Heq.
      apply typing_tapp with (K:=kn_lin); auto.
        simpl_env.
        apply typing_lvar; simpl_env; auto.
           assert ([(x, lbind_typ (typ_all kn_lin (typ_arrow kn_lin (typ_arrow K' A 0) 0)))] = 
                           [(x, lbind_typ (typ_all kn_lin (typ_arrow kn_lin (typ_arrow K' A 0) 0)))] ++ nil); auto. 
           rewrite H. clear H. 
           apply wf_lenv_typ; auto.
      apply typing_labs with (L := singleton x); auto.
      intros x0 Hfvx0.
      unfold open_ee. simpl. 
      apply typing_lvar; simpl_env.
        rewrite_env ([(x0, lbind_typ A)] ++ nil).
        apply wf_lenv_typ; auto.
      simpl_env.
      rewrite_env ([(x, lbind_typ (typ_all kn_lin (typ_arrow kn_lin (typ_arrow K' A 0) 0)))]++nil).
      apply lenv_split_left; auto.
  Case "K=kn_nonlin".
  apply typing_abs with (L := {}); auto.
  intros x Hfvx.
    unfold open_ee. simpl. 
    apply typing_app with (T1:=typ_arrow K' A A) (K:=kn_nonlin) (D1:= nil) (D2:=nil); auto.
      assert (open_tt (typ_arrow kn_nonlin (typ_arrow K' A 0) 0) A = typ_arrow kn_nonlin (typ_arrow K' A A) A) as Heq.
        unfold open_tt. simpl.
        apply type_from_wf_typ in HwftA.
        rewrite <- open_tt_rec_type; auto.
      rewrite <- Heq.
      apply typing_tapp with (K:=kn_nonlin); auto.
        simpl_env.
        apply typing_var; simpl_env; auto.
           assert ([(x, bind_typ (typ_all kn_nonlin (typ_arrow kn_nonlin (typ_arrow K' A 0) 0)))] = 
                           [(x, bind_typ (typ_all kn_nonlin (typ_arrow kn_nonlin (typ_arrow K' A 0) 0)))] ++ nil); auto. 
           rewrite H. clear H. 
           apply wf_env_typ; auto.
        rewrite_env (nil++[(x, bind_typ (typ_all kn_nonlin (typ_arrow kn_nonlin (typ_arrow K' A 0) 0)))] ++ nil).
        apply wf_typ_weakening; auto.
      apply typing_abs with (L := singleton x); auto.
        rewrite_env (nil++[(x, bind_typ (typ_all kn_nonlin (typ_arrow kn_nonlin (typ_arrow K' A 0) 0)))] ++ nil).
        apply wf_typ_weakening; auto.

        intros x0 Hfvx0.
        unfold open_ee. simpl. 
        apply typing_var; simpl_env; auto.
           assert ([(x, bind_typ (typ_all kn_nonlin (typ_arrow kn_nonlin (typ_arrow K' A 0) 0)))] = 
                           [(x, bind_typ (typ_all kn_nonlin (typ_arrow kn_nonlin (typ_arrow K' A 0) 0)))] ++ nil); auto. 
           rewrite H. clear H. 
           apply wf_env_typ; auto.

            rewrite_env (nil++[(x, bind_typ (typ_all kn_nonlin (typ_arrow kn_nonlin (typ_arrow K' A 0) 0)))] ++ nil).
            apply wf_typ_weakening; auto.

        simpl_env.
        apply lenv_split_empty; auto.
          rewrite_env ([(x, bind_typ (typ_all kn_nonlin (typ_arrow kn_nonlin (typ_arrow K' A 0) 0)))]++nil).
          apply wf_env_typ; auto.
Qed.

Hint Resolve typing_fun_to_dneg typing_fun_from_dneg.

Lemma isomorphism_left : forall x,
  typing nil nil x A -> 
  value x ->
  F_observational_eq nil nil (exp_app fun_from_dnegA (exp_app fun_to_dnegA x)) x A.
Proof.
  intros x Htyping Hvalue.
  unfold fun_from_dnegA.

  assert (type A) as TypeA.
     apply typing_regular in Htyping.
     decompose [and] Htyping.
     apply type_from_wf_typ in H3; auto.

  assert (open_tt (typ_arrow K (typ_arrow K' A (typ_bvar 0)) (typ_bvar 0)) A = typ_arrow K (typ_arrow K' A A) A) as EQ.
     unfold open_tt. simpl.
     rewrite <- open_tt_rec_type; auto.

  apply F_observational_eq__trans with (e':=
      (exp_app 
          fun_from_dnegA
          (exp_tabs K
             (exp_abs K
                (typ_arrow K' A (typ_bvar 0)) 
                (exp_app (exp_bvar 0) x)
             )
          )
      )).
   Case "EQ1".
     apply F_observational_eq__congr_app with (t1:=dnegA) (lE1:=nil) (lE2:=nil) (K:=kn_nonlin); auto.
       apply F_observational_eq__refl; auto.

       assert ( (open_ee (exp_tabs K (exp_abs K (typ_arrow K' A (typ_bvar 0)) (exp_app (exp_bvar 0) (exp_bvar 1)))) x)
                    = (exp_tabs K (exp_abs K (typ_arrow K' A (typ_bvar 0)) (exp_app (exp_bvar 0) x)))
                    ) as Heq.
          unfold open_ee. simpl. auto.
       rewrite <- Heq.
       apply F_observational_eq__beta; auto.
         apply typing_app with (T1:=A) (K:=kn_nonlin) (D1:=nil) (D2:=nil); auto.
         apply red_abs; auto.
           apply expr_abs with (L:={}); auto.
             intros x0 x0notin.
             unfold open_ee. simpl.
             apply expr_tabs with (L:={{x0}}); auto.
               intros X0 X0notin.
               unfold open_te. simpl.
               apply expr_abs with (L:={{x0}} `union` {{X0}}); auto.
                 rewrite <- open_tt_rec_type; auto.                

                 intros x1 x1notin.
                 unfold open_ee. simpl; auto.

  Case "EQ2".
  unfold fun_from_dnegA.
  apply F_observational_eq__trans with (e':=
      (exp_app 
          (exp_tapp (exp_tabs K (exp_abs K (typ_arrow K' A (typ_bvar 0)) (exp_app (exp_bvar 0) x)))  A)
          (exp_abs K' A (exp_bvar 0))
      )
  ).
    SCase "EQ21".
     assert ( (open_ee 
                          (exp_app 
                            (exp_tapp 0  A)
                            (exp_abs K' A (exp_bvar 0))
                          )
                          (exp_tabs K (exp_abs K (typ_arrow K' A (typ_bvar 0)) (exp_app (exp_bvar 0) x))))
                    = (exp_app 
                          (exp_tapp (exp_tabs K (exp_abs K (typ_arrow K' A (typ_bvar 0)) (exp_app (exp_bvar 0) x)))  A)
                          (exp_abs K' A (exp_bvar 0))
                        )
                    ) as Heq.
          unfold open_ee. simpl. auto.
      rewrite <- Heq.
      apply F_observational_eq__beta; auto.
         apply typing_app with (T1:=dnegA) (K:=kn_nonlin) (D1:=nil) (D2:=nil); auto.
           apply typing_tabs with (L:={}).
              intros X Xnotin.
              unfold open_te. unfold open_tt. simpl. rewrite <- open_te_rec_expr; auto.
              apply value_abs.
              apply expr_abs with (L:={{X}}); auto.
                rewrite <- open_tt_rec_type; auto.

                intros x0 x0n.
                unfold open_ee. simpl.
                rewrite <- open_ee_rec_expr; auto.

              intros X Xnotin.
              unfold open_te. unfold open_tt. simpl. rewrite <- open_te_rec_expr; auto.
              rewrite <- open_tt_rec_type; auto.
              destruct K'.
              SSCase "K'=1".
              apply typing_labs with (L:={{X}}); auto.
                apply wf_typ_arrow with (K1:=K) (K2:=K); auto.
                  rewrite_env (nil ++ [(X, bind_kn K)] ++ nil).
                  apply wf_typ_weakening; auto.

                intros x0 x0notin.
                unfold open_ee. simpl.
                rewrite <- open_ee_rec_expr; auto.
                assert (wf_lenv [(X, bind_kn K)] [(x0, lbind_typ (typ_arrow kn_lin A X))]) as Wfle.
                  rewrite_env ([(x0, lbind_typ (typ_arrow kn_lin A X))]++nil). 
                  apply wf_lenv_typ; auto.
                    apply wf_lenv_empty; auto.
                       rewrite_env ([(X, bind_kn K)]++nil). 
                       apply wf_env_kn; auto.

                     apply wf_typ_arrow with (K1:=K) (K2:=K); auto.
                       rewrite_env (nil ++ [(X, bind_kn K)] ++ nil).
                       apply wf_typ_weakening; auto.                    
               apply typing_app with (T1:=A) (K:=kn_lin) (D1:=[(x0, lbind_typ (typ_arrow kn_lin A X))]) (D2:=nil); auto.
                    rewrite_env (nil ++ ([(X, bind_kn K)]) ++ nil).
                    apply typing_weakening; simpl_env; auto.

                    simpl_env.
                    rewrite_env ([(x0, lbind_typ (typ_arrow kn_lin A X))]++nil).
                    apply lenv_split_left; auto.
                      apply wf_typ_arrow with (K1:=K) (K2:=K); auto.
                        rewrite_env (nil ++ [(X, bind_kn K)] ++ nil).
                        apply wf_typ_weakening; auto.                    
              SSCase "K'=*".
              apply typing_abs with (L:={{X}}); auto.
                apply wf_typ_arrow with (K1:=K) (K2:=K); auto.
                  rewrite_env (nil ++ [(X, bind_kn K)] ++ nil).
                  apply wf_typ_weakening; auto.

                intros x0 x0notin.
                unfold open_ee. simpl.
                rewrite <- open_ee_rec_expr; auto.
                assert (wf_env ([(x0, bind_typ (typ_arrow kn_nonlin A X))]++[(X, bind_kn K)])) as Wfe.
                  apply wf_env_typ; auto.
                     rewrite_env ([(X, bind_kn K)]++nil). 
                     apply wf_env_kn; auto.

                     apply wf_typ_arrow with (K1:=K) (K2:=K); auto.
                       rewrite_env (nil ++ [(X, bind_kn K)] ++ nil).
                       apply wf_typ_weakening; auto.                    
               apply typing_app with (T1:=A) (K:=kn_nonlin) (D1:=nil) (D2:=nil); auto.
                    rewrite_env (nil ++ ([(x0, bind_typ (typ_arrow kn_nonlin A X))]++[(X, bind_kn K)]) ++ nil).
                    apply typing_weakening; simpl_env; auto.

         apply red_abs; auto.
           apply expr_abs with (L:={}); auto.
             apply type_from_wf_typ with (E:= nil) (K:=K).
               apply wftdnegA.
             intros x0 x0notin.
             unfold open_ee. simpl.
             apply expr_app; auto.
               apply expr_abs with (L:={{x0}}); auto.
                 intros x1 x1notin.
                 unfold open_ee. simpl; auto.
           apply value_tabs.
             apply expr_tabs with (L:={}); auto.
               intros X Xnotin.
               unfold open_te. simpl.
                rewrite <- open_te_rec_expr; auto.
                rewrite <- open_tt_rec_type; auto.
               apply expr_abs with (L:={{X}}); auto.
                 intros x0 x0notin.
                 unfold open_ee.
                 simpl. rewrite <- open_ee_rec_expr; auto.

    SCase "EQ22".
    apply F_observational_eq__trans with (e':=
      (exp_app 
          (exp_abs K (typ_arrow K' A A) (exp_app (exp_bvar 0) x))
          (exp_abs K' A (exp_bvar 0))
      )
    ).
      SSCase "EQ221".
      apply F_observational_eq__congr_app with (t1:=typ_arrow K' A A) (lE1:=nil) (lE2:=nil) (K:=K); auto.
        SSSCase "EQ2211".
        assert (open_tt (typ_arrow K (typ_arrow K' A (typ_bvar 0)) (typ_bvar 0)) A = typ_arrow K (typ_arrow K' A A) A) as EQ'.
          unfold open_tt. simpl.
          rewrite <- open_tt_rec_type; auto.
        rewrite <- EQ'.
        assert (open_te (exp_abs K (typ_arrow K' A 0) (exp_app 0 x)) A = exp_abs K (typ_arrow K' A A) (exp_app 0 x)) as J.
          unfold open_te. simpl.
          rewrite <- open_te_rec_expr; auto.
          rewrite <- open_tt_rec_type; auto.
        rewrite <- J.
        apply F_observational_eq__beta; auto.
          apply typing_tapp with (K:=K); auto.
            apply typing_tabs with (L:={}).
              intros X Xnotin.
              unfold open_te. unfold open_tt. simpl. rewrite <- open_te_rec_expr; auto.
              apply value_abs.
              rewrite <- open_tt_rec_type; auto.
              apply expr_abs with (L:={{X}}); auto.
                intros x0 x0notin.
                unfold open_ee. simpl.
                rewrite <- open_ee_rec_expr; auto.

              intros X Xnotin.
              unfold open_te. unfold open_tt. simpl. 
              rewrite <- open_te_rec_expr; auto.
              rewrite <- open_tt_rec_type; auto.
              destruct K'.
              SSSSCase "K'=1".
              apply typing_labs with (L:={{X}}); auto.
                apply wf_typ_arrow with (K1:=K) (K2:=K); auto.
                  rewrite_env (nil ++ [(X, bind_kn K)] ++ nil).
                  apply wf_typ_weakening; auto.                                    

                intros x0 x0notin.
                unfold open_ee. simpl.
                rewrite <- open_ee_rec_expr; auto.
                assert (wf_lenv [(X, bind_kn K)] [(x0, lbind_typ (typ_arrow kn_lin A X))]) as Wfle.
                  rewrite_env ([(x0, lbind_typ (typ_arrow kn_lin A X))]++nil).
                  apply wf_lenv_typ; auto.
                     apply wf_lenv_empty.
                       rewrite_env ([(X, bind_kn K)]++nil). 
                       apply wf_env_kn; auto.

                     apply wf_typ_arrow with (K1:=K) (K2:=K); auto.
                       rewrite_env (nil ++ [(X, bind_kn K)] ++ nil).
                       apply wf_typ_weakening; auto.                 
                apply typing_app with (T1:=A) (K:=kn_lin) (D1:=[(x0, lbind_typ (typ_arrow kn_lin A X))]) (D2:=nil); auto.
                  rewrite_env (nil ++ ([(X, bind_kn K)]) ++ nil).
                  apply typing_weakening; simpl_env; auto.

                  simpl_env.
                  rewrite_env ([(x0, lbind_typ (typ_arrow kn_lin A X))]++nil).
                  apply lenv_split_left; auto.
                    apply wf_typ_arrow with (K1:=K) (K2:=K); auto.
                      rewrite_env (nil ++ [(X, bind_kn K)] ++ nil).
                      apply wf_typ_weakening; auto.                    
              SSSSCase "K'=*".
              apply typing_abs with (L:={{X}}); auto.
                apply wf_typ_arrow with (K1:=K) (K2:=K); auto.
                  rewrite_env (nil ++ [(X, bind_kn K)] ++ nil).
                  apply wf_typ_weakening; auto.                                    

                intros x0 x0notin.
                unfold open_ee. simpl.
                rewrite <- open_ee_rec_expr; auto.
                assert (wf_env ([(x0, bind_typ (typ_arrow kn_nonlin A X))]++[(X, bind_kn K)])) as Wfe.
                  apply wf_env_typ; auto.
                     rewrite_env ([(X, bind_kn K)]++nil). 
                     apply wf_env_kn; auto.

                     apply wf_typ_arrow with (K1:=K) (K2:=K); auto.
                       rewrite_env (nil ++ [(X, bind_kn K)] ++ nil).
                       apply wf_typ_weakening; auto.                 
                apply typing_app with (T1:=A) (K:=kn_nonlin) (D1:=nil) (D2:=nil); auto.
                  rewrite_env (nil ++ ([(x0, bind_typ (typ_arrow kn_nonlin A X))]++[(X, bind_kn K)]) ++ nil).
                  apply typing_weakening; simpl_env; auto.

          apply red_tabs; auto.
            apply expr_tabs with (L:={}).
              intros X Xnotin.
              unfold open_te. unfold open_tt. simpl. 
              rewrite <- open_te_rec_expr; auto.              
              rewrite <- open_tt_rec_type; auto.              
              apply expr_abs with (L:={{X}}).
                apply type_arrow; auto.
                intros x0 x0notin.
                unfold open_ee. simpl. rewrite <- open_ee_rec_expr; auto. 

        SSSCase "EQ2212".
        apply F_observational_eq__refl.
          apply typing_labs with (L:={}); auto.
            intros x0 x0notin.
            unfold open_ee. simpl.
            apply typing_lvar; auto.
               rewrite_env ([(x0, lbind_typ A)] ++ nil).
              apply wf_lenv_typ; auto.

      SSCase "EQ222".
      apply F_observational_eq__trans with (e':=
          (exp_app (exp_abs K' A (exp_bvar 0)) x)
       ).

        SSSCase "EQ2221".
        assert (open_ee (exp_app (exp_bvar 0) x) (exp_abs K' A (exp_bvar 0))
                      = (exp_app (exp_abs K' A (exp_bvar 0)) x)
             ) as Heq.
             unfold open_ee. simpl.
             rewrite <-  open_ee_rec_expr; auto.
        rewrite <- Heq.   
        apply F_observational_eq__beta; auto.
          apply typing_app with (T1:=typ_arrow K' A A) (D1:=nil) (D2:=nil) (K:=K); auto.
            destruct K'.
            SSSSCase "K'=1".
            apply typing_labs with (L:={}); auto.
                apply wf_typ_arrow with (K1:=K) (K2:=K); auto.
           
                intros x0 Hfvx0.
                unfold open_ee. simpl; auto.
                rewrite <-  open_ee_rec_expr; auto.
                assert (wf_lenv empty ([(x0, lbind_typ (typ_arrow kn_lin A A))])) as Wfle.
                  rewrite_env ([(x0, lbind_typ (typ_arrow kn_lin A A))] ++ nil).
                  apply wf_lenv_typ; auto.
                    apply wf_typ_arrow with (K1:=K) (K2:=K); auto.
                apply typing_app with (T1:=A) (D1:=[(x0, lbind_typ (typ_arrow kn_lin A A))]) (D2:=nil) (K:=kn_lin); auto.
                   simpl_env.
                   rewrite_env ([(x0, lbind_typ (typ_arrow kn_lin A A))] ++ nil).
                   apply lenv_split_left; auto.
                     apply wf_typ_arrow with (K1:=K) (K2:=K); auto.
            SSSSCase "K'=*".
            apply typing_abs with (L:={}); auto.
                apply wf_typ_arrow with (K1:=K) (K2:=K); auto.
           
                intros x0 Hfvx0.
                unfold open_ee. simpl; auto.
                rewrite <-  open_ee_rec_expr; auto.
                assert (wf_env ([(x0, bind_typ (typ_arrow kn_nonlin A A))])) as Wfe.
                  rewrite_env ([(x0, bind_typ (typ_arrow kn_nonlin A A))] ++ nil).
                  apply wf_env_typ; auto.
                    apply wf_typ_arrow with (K1:=K) (K2:=K); auto.
                apply typing_app with (T1:=A) (D1:=nil) (D2:=nil) (K:=kn_nonlin); auto.
                   rewrite_env (nil ++ [(x0, bind_typ (typ_arrow kn_nonlin A A))] ++ nil).
                   apply typing_weakening; simpl_env; auto.

            apply typing_labs with (L:={}); auto.           
                intros x0 Hfvx0.
                unfold open_ee. simpl.
                apply typing_lvar; auto.
                   rewrite_env ([(x0, lbind_typ A)] ++ nil).
                   apply wf_lenv_typ; auto.

          apply red_abs.
            apply expr_abs with (L:={}); auto.           
                intros x0 Hfvx0.
                unfold open_ee. simpl; auto.
                rewrite <-  open_ee_rec_expr; auto.
            apply value_abs.
              apply expr_abs with (L:={}); auto.           
                intros x0 Hfvx0.
                unfold open_ee. simpl; auto.

        SSSCase "EQ2222".
        assert (open_ee 0 x = x) as Heq.
             unfold open_ee. simpl. auto.
        rewrite <- Heq.   
        apply F_observational_eq__beta; auto.
          apply typing_app with (T1:=A) (D1:=nil) (D2:=nil) (K:=K'); auto.
            apply typing_labs with (L:={}); auto.
                intros x0 Hfvx0.
                unfold open_ee. simpl; auto.
                apply typing_lvar; auto.
                   rewrite_env ([(x0, lbind_typ A)] ++ nil).
                   apply wf_lenv_typ; auto.
          apply red_abs; auto.
            apply expr_abs with (L:={}); auto.
                intros x0 Hfvx0.
                unfold open_ee. simpl; auto.
Qed.

Require Import LinF_Parametricity_App.

Lemma dnegation_type_inversion : forall nt B B', 
  typing nil nil nt dnegA->
  (forall x y RY, 
   wfr RY B B' K ->
   exists Y:atom, 
   (F_related_terms (typ_arrow K' A Y) 
                                 ([(Y, RY)])
                                 ([(Y, B)])
                                 ([(Y, B')])
                                  x y ->
   F_related_terms (typ_fvar Y)
                                 ([(Y, RY)])
                                 ([(Y, B)])
                                 ([(Y, B')])
                                 (exp_app (exp_tapp nt B) x) (exp_app (exp_tapp nt B') y))).
Proof.
  intros nt B B' Htyping x y RY Hwfr.

  assert (F_related_terms dnegA rho_nil delta_nil delta_nil nt nt) as Frel_All.
    apply fundamental_parametricity; auto.
  destruct Frel_All as [v [v'[Ht [Ht' [Hn_ntv [Hn_nt'v' Frel_All]]]]]].

  apply F_related_values_all_leq in Frel_All.
  destruct Frel_All as [Hvy [Hvy' [LY Hall]]].

  pick fresh Y. 
  assert (Y `notin` LY) as FrY. auto.
  destruct (@Hall Y B B' RY FrY) as [vv [vv' [Hn_wBvv [Hn_w'B'vv' Hrel_wft]]]]; auto.
    assert (Y `notin` fv_tt A) as YnA.
      apply notin_fv_wf with (E:=nil) (K:=K); auto.
    simpl. auto.
  unfold open_tt in*. simpl in *. clear Hall.

  assert (type A) as TypeA.
     apply type_from_wf_typ with (E:=nil) (K:=K); auto.

  exists (Y).
  intros Hterm. simpl_env in *.
  rewrite <- open_tt_rec_type in *; auto.

  assert (Harrow := @F_related_values_arrow_leq (typ_arrow K' A Y) Y ([(Y,RY)]) ([(Y,B)]) ([(Y,B')]) vv vv' K Hrel_wft).
  destruct Harrow as [Hvv [Hvv' Harrow]].
  destruct Hterm as [v0 [v'0 [Ht_x [Ht_y [Hn_xv0 [Hn_yv'0 Hrel]]]]]].

  destruct (@Harrow v0 v'0) as [u [u' [Hn_vvxu [Hn_vv'yu' Hrel_wft2]]]]; auto.
    eapply preservation_normalization; eauto.
    eapply preservation_normalization; eauto.
  clear Harrow.

  simpl in *.
  assert ((if Y==Y then B else typ_fvar Y) = B) as EqB.
    destruct (Y==Y); auto. contradict n; auto.
  assert ((if Y==Y then B' else typ_fvar Y) = B') as EqB'.
    destruct (Y==Y); auto. contradict n; auto.
  rewrite EqB in *.  rewrite EqB' in *.

  assert (Y `notin` fv_tt A) as YnA.
    apply notin_fv_wf with (E:=nil) (K:=K); auto.
  rewrite <- subst_tt_fresh with (T:=A) in Ht_x; auto.
  rewrite <- subst_tt_fresh with (T:=A) in Ht_y; auto.
  clear EqB EqB'.

  assert (normalize (exp_tapp nt B) vv).
    apply congr_tapp with (v1:=v); auto.
      eapply type_from_wf_typ with (E:=nil); eauto using wfr_left_inv.

  assert (normalize (exp_tapp nt B') vv').
    apply congr_tapp with (v1:=v'); auto.
      eapply type_from_wf_typ with (E:=nil); eauto using wfr_right_inv.
    
  assert (open_tt (typ_arrow K (typ_arrow K' A (typ_bvar 0)) (typ_bvar 0)) B = typ_arrow K (typ_arrow K' A B) B) as EqNAB.
    unfold open_tt. simpl. 
    rewrite <- open_tt_rec_type; auto.

  assert (open_tt (typ_arrow K (typ_arrow K' A (typ_bvar 0)) (typ_bvar 0)) B' = typ_arrow K (typ_arrow K' A B') B') as EqNAB'.
    unfold open_tt. simpl. 
    rewrite <- open_tt_rec_type; auto.

  assert (normalize (exp_app (exp_tapp nt B) x) u).
    apply congr_app with (v1:=vv) (v2:=v0); auto.
      assert (typing nil nil (exp_tapp nt B) (typ_arrow K (typ_arrow K' A B) B)).
        rewrite <- EqNAB.
        apply typing_tapp with (K:=K); eauto using wfr_left_inv.
      auto.

  assert (normalize (exp_app (exp_tapp nt B') y) u').
    apply congr_app with (v1:=vv') (v2:=v'0); auto.
      assert (typing nil nil (exp_tapp nt B') (typ_arrow K (typ_arrow K' A B') B')).
        rewrite <- EqNAB'.
        apply typing_tapp with (K:=K); eauto using wfr_right_inv.
      auto.

  exists(u). exists(u'). simpl in *.
    split; simpl.
    destruct (Y==Y); try solve [contradict n; auto | auto].
      apply typing_app with (T1:=typ_arrow K' A B) (D1:=nil) (D2:=nil) (K:=K); auto.
        rewrite <- EqNAB.
        apply typing_tapp with (K:=K); eauto using wfr_left_inv.

    split; simpl; auto.
    destruct (Y==Y); try solve [contradict n; auto | auto].
      apply typing_app with (T1:=typ_arrow K' A B') (D1:=nil) (D2:=nil) (K:=K); auto.
        rewrite <- EqNAB'.
        apply typing_tapp with (K:=K); eauto using wfr_right_inv.
Qed.

Definition Rfun (A A':typ) (f:exp) K (v v':exp) : Prop := 
  typing nil nil v A /\ typing nil nil v' A' /\
  typing nil nil f (typ_arrow K A A') /\
  F_vobservational_eq nil nil (exp_app f v) v' A'
  .

Lemma Rfun_wfr : forall A A' K Q a,
  wf_typ nil A K -> 
  wf_typ nil A' K -> 
  wfr (Rfun A A' a Q) A A' K.
Proof.
  intros.
  split; auto.
Qed.

Corollary Rearrangement_DNegation : forall nt f B, 
  typing nil nil nt dnegA ->
  wf_typ nil B K ->
  typing nil nil f (typ_arrow K' A B) ->
  value f ->
  Rfun A B f K'
                      (exp_app (exp_tapp nt A) (exp_abs K' A (exp_bvar 0)))
                      (exp_app (exp_tapp nt B) (exp_abs K' A (exp_app f 0)))
  .
Proof.
  intros nt f B Htypingnt HwftB Htypingf Hvf.

  assert (wf_typ nil A K) as HwftA. auto.

  destruct (@dnegation_type_inversion nt A B
                             Htypingnt 
                             (exp_abs K' A (exp_bvar 0)) (exp_abs K' A (exp_app f 0))
                             (Rfun A B f K')
                 ) as [Y JJ]; auto using Rfun_wfr.

  assert (F_related_terms (typ_arrow K' A Y) [(Y, Rfun A B f K')] [(Y, A)] [(Y, B)] (exp_abs K' A 0) (exp_abs K' A (exp_app f 0))) as H.
    Case "(exp_abs A (exp_bvar 0)) and (exp_abs A (exp_app f (exp_bvar 0))) are related".
    assert (type A) as TypeA.
       apply type_from_wf_typ with (E:=nil) (K:=K); auto.
    assert (Y `notin` fv_tt A) as YnA.
      apply notin_fv_wf with (E:=nil) (K:=K); auto.
    assert (value (exp_abs K' A 0)) as Jv1.
      apply value_abs.
         apply expr_abs with (L:={{Y}}); auto.
            intros x xnotin.
            unfold open_ee. simpl. auto.      
      assert (value (exp_abs K' A (exp_app f 0))) as Jv2.
        apply value_abs.
           apply expr_abs with (L:={{Y}}); auto.
              intros x xnotin.
              unfold open_ee. simpl.
              rewrite <- open_ee_rec_expr; auto.

    exists (exp_abs K' A (exp_bvar 0)). exists (exp_abs K'  A (exp_app f (exp_bvar 0))). 
      split; simpl.
      SCase "typing".
          destruct (Y==Y); subst; auto. 
            rewrite <- subst_tt_fresh; auto.
            destruct K.
              apply typing_labs with ({{Y}}); auto.
                 intros x xnotin.
                 unfold open_ee. simpl.
                 apply typing_lvar; auto.
                    rewrite_env ([(x, lbind_typ A)]++nil).
                    apply wf_lenv_typ; auto.
              apply typing_abs with ({{Y}}); auto.
                 intros x xnotin.
                 unfold open_ee. simpl.
                 apply typing_var; auto.
                    rewrite_env ([(x, bind_typ A)]++nil).
                    apply wf_env_typ; auto.
             contradict n; auto.
                   
      split; simpl.
      SCase "typing".
        destruct (Y==Y); subst; auto. 
          rewrite <- subst_tt_fresh; auto.
          destruct K.
          SSCase "K=1".
            apply typing_labs with ({{Y}}); auto.
               intros x xnotin.
               unfold open_ee. simpl.
               rewrite <- open_ee_rec_expr; auto.
               apply typing_app with (T1:=A)(D1:=nil)(D2:=[(x, lbind_typ A)])(K:=K'); auto.
                 apply typing_lvar; auto.
                    simpl_env.
                    rewrite_env ([(x, lbind_typ A)]++nil).
                    apply wf_lenv_typ; auto.
                 simpl_env.
                 rewrite_env ([(x, lbind_typ A)]++nil).
                 apply lenv_split_right; auto.
          SSCase "K=*".
            apply typing_abs with ({{Y}}); auto.
               intros x xnotin.
               unfold open_ee. simpl.
               rewrite <- open_ee_rec_expr; auto.
               apply typing_app with (T1:=A)(D1:=nil)(D2:=nil)(K:=K'); auto.
                 rewrite_env (nil++[(x, bind_typ A)]++nil).
                 apply typing_weakening; auto.
                   apply wf_lenv_weakening; auto.
                      rewrite_env ([(x, bind_typ A)]++nil).
                      apply wf_env_typ; auto.
                 apply typing_var; auto.
                    rewrite_env ([(x, bind_typ A)]++nil).
                    apply wf_env_typ; auto.
                 simpl_env.
                 apply lenv_split_empty; auto.
                    rewrite_env ([(x, bind_typ A)]++nil).
                    apply wf_env_typ; auto.
          contradict n; auto.

      unfold normalize.
      split; auto.
      split; auto.

      SCase "Terms".
      apply F_related_values_arrow_req. simpl.
      split; auto.
      split; auto.
      intros x x' Htyping Htyping' Hrel_xx'.
        rewrite <- subst_tt_fresh in Htyping; auto.
        rewrite <- subst_tt_fresh in Htyping'; auto.

        assert (F_vobservational_eq nil nil x x' A) as x_eq_x'.
          apply F_observational_eq__F_vobservational_eq.
          apply F_logical_related__sound; auto.
          split; auto.
          split; auto.
            intros dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Hrelsubst HRsubst.
            inversion Hrelsubst; subst.
            simpl.
            exists x. exists x'.
            simpl.
            split; auto.
            split; auto.
            split. split; auto.
                       apply F_related_values_inversion in Hrel_xx'.
                       destruct Hrel_xx'; auto.
            split. split; auto.
                       apply F_related_values_inversion in Hrel_xx'.
                       destruct Hrel_xx'; auto.
              rewrite_env (nil ++ [(Y, Rfun A B f K')] ++ nil) in Hrel_xx'.
              rewrite_env (nil ++ [(Y, A)] ++ nil) in Hrel_xx'.
              rewrite_env (nil ++ [(Y, B)] ++ nil) in Hrel_xx'.
              apply Frel_stronger with (E:=nil) (E':=nil) (K:=K) in Hrel_xx'; simpl_env; auto using Rfun_wfr.
                rewrite_env ([(Y, Rfun A B f K')] ++ nil).
                rewrite_env ([(Y, bind_kn K)] ++ nil).
                apply wf_rho_subst_srel; auto.

                rewrite_env ([(Y, A)] ++ nil).
                rewrite_env ([(Y, bind_kn K)] ++ nil).
                apply wf_delta_subst_styp; auto.
                
                rewrite_env ([(Y, B)] ++ nil).
                rewrite_env ([(Y, bind_kn K)] ++ nil).
                apply wf_delta_subst_styp; auto.
  
        assert (exists fx', normalize (exp_app f x') fx') as Hn_fx'2fx'.
          apply strong_normalization with (t:=B); auto.
            apply typing_app with (T1:=A) (D1:=nil) (D2:=nil) (K:=K'); auto.
        destruct Hn_fx'2fx' as [fx' [Hb_fx'2fx' Valuefx']].

        exists x. exists fx'. 
        assert (value x) as Valuex.
          apply F_related_values_inversion in Hrel_xx'.
          destruct Hrel_xx'; auto.
        assert (value x') as Valuex'.
          apply F_related_values_inversion in Hrel_xx'.
          destruct Hrel_xx'; auto.
        repeat(split; auto).
           SSCase "Red".
           apply bigstep_red_trans with (e':=x); auto.
             assert (red (exp_app (exp_abs K' A 0) x) x = red (exp_app (exp_abs K' A 0) x) (open_ee 0 x)) as Heq.
               unfold open_ee. simpl. auto.
             rewrite Heq.
             apply red_abs; auto.
             
           SSCase "Red".
           apply bigstep_red_trans with (e':=exp_app f x'); auto.
             assert (exp_app f x' = open_ee (exp_app f 0) x') as Heq.
               unfold open_ee. simpl. 
               rewrite <- open_ee_rec_expr; auto.
             rewrite Heq.
             apply red_abs; auto.

           SSCase "Terms".
            apply F_related_values_fvar_req. simpl.
            exists(Rfun A B f K').
            split; auto.
            split; auto.
            split; auto.
            split; auto.
            split; auto.
              apply preservation_bigstep_red with (e:=exp_app f x'); auto.
                apply typing_app with (T1:=A) (D1:=nil) (D2:=nil) (K:=K'); auto.
            split; auto.
              apply F_vobservational_eq__trans with (e':=exp_app f x'); auto.
                apply F_vobservational_eq__congr_app with (lE1:=nil) (lE2:=nil) (K:=K') (t1:=A); auto.
                  apply F_observational_eq__F_vobservational_eq.
                  apply F_observational_eq__refl; auto.

                apply F_observational_eq__F_vobservational_eq.                   
                apply F_observational_eq__mbeta; auto.
                  apply typing_app with (T1:=A) (D1:=nil) (D2:=nil) (K:=K'); auto.

  (* nt[A] id and  nt[B](\x. fx) are related as Rfun*)
  apply JJ in H; auto using Rfun_wfr.
  destruct H as [v [v' [Typing1 [Typing2 [Heq_ntAidv [Heq_ntBfv' [R [Hb [Valuev [Valuev' Hrel]]]]]]]]]]; subst.
  simpl in Typing1.
  simpl in Typing2.
  destruct (Y==Y); try solve [auto | contradict n; auto].
  unfold Rfun.
  split; auto.
  split; auto.
  split; auto.
    Case "Eq".
    apply F_vobservational_eq__trans with (e':=exp_app f v).
      apply F_vobservational_eq__congr_app with (t1:=A) (lE1:=nil) (lE2:=nil) (K:=K'); auto.
        apply F_observational_eq__F_vobservational_eq.
        apply F_observational_eq__refl; auto.

        apply F_observational_eq__F_vobservational_eq.
        apply F_observational_eq__mbeta; auto.
          destruct Heq_ntAidv; auto.
      apply F_vobservational_eq__trans with (e':=v').
        analyze_binds Hb.
        destruct Hrel as [J1 [J2 [J3 J4]]]; auto.

        apply F_vobservational_eq__sym.
          apply F_observational_eq__F_vobservational_eq.
          apply F_observational_eq__mbeta; auto.
            destruct Heq_ntBfv'; auto.
Qed.

Lemma id_typing : typing nil nil (exp_abs K' A 0) (typ_arrow K' A A).
Proof. 
            assert (J:=wftA).
            destruct K.
              apply typing_labs with ({}); auto.
                 intros x xnotin.
                 unfold open_ee. simpl.
                 apply typing_lvar; auto.
                    rewrite_env ([(x, lbind_typ A)]++nil).
                    apply wf_lenv_typ; auto.
              apply typing_abs with ({}); auto.
                 intros x xnotin.
                 unfold open_ee. simpl.
                 apply typing_var; auto.
                    rewrite_env ([(x, bind_typ A)]++nil).
                    apply wf_env_typ; auto.
Qed.

Hint Resolve id_typing.

Lemma isomorphism_right : forall h,
  typing nil nil h dnegA -> 
  value h ->
  F_observational_eq nil nil (exp_app fun_to_dnegA (exp_app fun_from_dnegA h)) h dnegA.
Proof.
  intros h Htyping Valueh.
  assert (J:=@wftA).
  unfold fun_from_dnegA.
  assert (type A) as typeA.
    apply type_from_wf_typ with (E:=nil) (K:=K); auto.
  assert (type dnegA) as typednegA.
    apply type_from_wf_typ with (E:=nil) (K:=K); auto.
  assert (typing nil nil (exp_app (exp_tapp h A) (exp_abs K' A 0)) A) as Typing1.
      apply typing_app with (T1:=typ_arrow K' A A) (D1:=nil) (D2:=nil) (K:=K); auto. 
        assert (open_tt (typ_arrow K (typ_arrow K' A 0) 0) A = typ_arrow K (typ_arrow K' A A) A) as EQ.
          unfold open_tt. simpl. rewrite <- open_tt_rec_type; auto.
        rewrite <- EQ.
        apply typing_tapp with (K:=K); auto.

  apply F_observational_eq__trans with (e':=exp_app fun_to_dnegA (exp_app (exp_tapp h A) (exp_abs K' A 0))).
Case "EQ1".
    assert  (open_ee (exp_app (exp_tapp 0 A) (exp_abs K' A 0))  h
              = exp_app (exp_tapp h A) (exp_abs K' A 0)
                ) as Heq.
      unfold open_ee. simpl. auto.
    rewrite <- Heq.
    apply F_observational_eq__congr_app with (lE1:=nil) (lE2:=nil) (t1:=A) (K:=kn_nonlin); auto.
      apply F_observational_eq__refl; auto.
      apply F_observational_eq__beta.
        apply typing_app with (D1:=nil) (D2:=nil) (T1:=dnegA) (K:=kn_nonlin); auto.
        apply red_abs; auto.
          apply expr_abs with (L:={}); auto.
            intros x xn.
            unfold open_ee. simpl.
            apply expr_app; auto.
              apply expr_abs with (L:={}); auto.
                intros x0 x0n.
                unfold open_ee. simpl. auto.

Case "EQ2".
  assert (exists v, normalize (exp_app (exp_tapp h A) (exp_abs K' A 0)) v) as Hn_hAid_v.
    apply strong_normalization with (t:=A); auto.

  destruct Hn_hAid_v as [v [Hb_hAid_v Valuev]].
  assert (typing nil nil v A) as Typing2.
    apply preservation_bigstep_red with (e':=v) in Typing1; auto.  
  assert (forall (X x:atom), expr (exp_abs K (typ_arrow K' A X) (exp_app 0 x))) as Expr1.
    intros X x.
    apply expr_abs with (L:={{x}} `union` {{X}}); auto.
      intros x0 x0n.
      unfold open_ee. simpl. auto.
  apply F_observational_eq__trans with (e':=exp_app fun_to_dnegA v).

SCase "EQ21".
  apply F_observational_eq__congr_app with (lE1:=nil) (lE2:=nil) (t1:=A) (K:=kn_nonlin); auto.

SSCase "EQ211".
  apply F_observational_eq__refl; auto.

SSCase "EQ212".
  apply F_observational_eq__mbeta; auto.

SCase "EQ22".
  unfold fun_to_dnegA.
  apply F_observational_eq__trans with (e':=exp_tabs K (exp_abs K (typ_arrow K' A 0) (exp_app 0 v))).
  
SSCase "EQ221".
  assert  (open_ee (exp_tabs K (exp_abs K (typ_arrow K' A 0) (exp_app 0 1))) v
            = exp_tabs K (exp_abs K (typ_arrow K' A 0) (exp_app 0 v))
              ) as Heq.
    unfold open_ee. simpl. auto.
  rewrite <- Heq.
  apply F_observational_eq__beta.
    apply typing_app with (D1:=nil) (D2:=nil) (T1:=A) (K:=kn_nonlin); auto.
    apply red_abs; auto.
       apply expr_abs with (L:={}); auto.
         intros x xn.
         unfold open_ee. simpl.
         apply expr_tabs with (L:={{x}}); auto.
           intros X Xn.
           unfold open_te. simpl.
           rewrite <- open_tt_rec_type; auto.

SSCase "EQ222".
  apply F_observational_eq__trans with (e':=exp_tabs K (exp_abs K (typ_arrow K' A 0) (exp_app 0 (exp_app (exp_tapp h A) (exp_abs K' A 0))))).

SSSCase "EQ2221".
  unfold dnegA in *.
  destruct K'.
    (* K' = 1 *)
    apply F_observational_eq__congr_tabs_labs with (L:={}); auto.
      intros X Xn.
      unfold open_tt. simpl.
      rewrite <- open_tt_rec_type; auto.
      apply wf_typ_arrow with (K1:=K) (K2:=K); auto.
        rewrite_env (nil ++ [(X, bind_kn K)] ++ nil).
        apply wf_typ_weakening; auto.

      intros X x Xn xn.
       unfold open_te. unfold open_tt. unfold open_ee. simpl.
       rewrite <- open_tt_rec_type; auto.
       rewrite <- open_te_rec_expr; auto.
       rewrite <- open_te_rec_expr; auto.
        rewrite <- open_ee_rec_expr; auto.
        rewrite <- open_ee_rec_expr; auto.
        apply F_observational_eq__congr_app with (lE1:=[(x, lbind_typ (typ_arrow kn_lin A X))]) (lE2:=nil) (t1:=A) (K:=kn_lin); auto.
          apply F_observational_eq__refl; auto.
             apply typing_lvar; auto.
                rewrite_env ([(x, lbind_typ (typ_arrow kn_lin A X))]++nil).
                apply wf_lenv_typ; auto.
                  apply wf_lenv_empty.
                    rewrite_env ([(X, bind_kn K)]++nil).
                    apply wf_env_kn; auto.
                 apply wf_typ_arrow with (K1:=K) (K2:=K); auto.
                   rewrite_env (nil ++ [(X, bind_kn K)] ++ nil).
                   apply wf_typ_weakening; auto.
          apply F_observational_eq__sym; auto.
            apply F_observational_eq__mbeta; auto.
              rewrite_env (nil ++ [(X, bind_kn K)] ++ nil).
              apply typing_weakening; auto.
                apply wf_lenv_empty.
                  rewrite_env ([(X, bind_kn K)]++nil).
                  apply wf_env_kn; auto.
           simpl_env.
           rewrite_env ([(x, lbind_typ (typ_arrow kn_lin A X))]++nil).
           apply lenv_split_left; auto.
             apply lenv_split_empty.
               rewrite_env ([(X, bind_kn K)]++nil).
               apply wf_env_kn; auto.
             apply wf_typ_arrow with (K1:=K) (K2:=K); auto.
               rewrite_env (nil ++ [(X, bind_kn K)] ++ nil).
               apply wf_typ_weakening; auto.

    (* K' = * *)
    apply F_observational_eq__congr_tabs_abs with (L:={}); auto.
      intros X Xn.
      unfold open_tt. simpl.
      rewrite <- open_tt_rec_type; auto.
      apply wf_typ_arrow with (K1:=K) (K2:=K); auto.
        rewrite_env (nil ++ [(X, bind_kn K)] ++ nil).
        apply wf_typ_weakening; auto.

      intros X x Xn xn.
       unfold open_te. unfold open_tt. unfold open_ee. simpl.
       rewrite <- open_tt_rec_type; auto.
       rewrite <- open_te_rec_expr; auto.
       rewrite <- open_te_rec_expr; auto.
        rewrite <- open_ee_rec_expr; auto.
        rewrite <- open_ee_rec_expr; auto.
        apply F_observational_eq__congr_app with (lE1:=nil) (lE2:=nil) (t1:=A) (K:=kn_nonlin); auto.
          apply F_observational_eq__refl; auto.
             apply typing_var; auto.
               simpl_env.
               apply wf_env_typ; auto.
                  rewrite_env ([(X, bind_kn K)]++nil).
                  apply wf_env_kn; auto.
 
                  apply wf_typ_arrow with (K1:=K) (K2:=K); auto.
                   rewrite_env (nil ++ [(X, bind_kn K)] ++ nil).
                   apply wf_typ_weakening; auto.
          apply F_observational_eq__sym; auto.
            apply F_observational_eq__mbeta; auto.
              rewrite_env (nil ++ ([(x, bind_typ (typ_arrow kn_nonlin A X))]++[(X, bind_kn K)]) ++ nil).
              apply typing_weakening; auto.
                apply wf_lenv_empty.
                simpl_env.
                apply wf_env_typ; auto.
                  rewrite_env ([(X, bind_kn K)]++nil).
                  apply wf_env_kn; auto.
 
                  apply wf_typ_arrow with (K1:=K) (K2:=K); auto.
                   rewrite_env (nil ++ [(X, bind_kn K)] ++ nil).
                   apply wf_typ_weakening; auto.
           simpl_env.
           apply lenv_split_empty.
             apply wf_env_typ; auto.
               rewrite_env ([(X, bind_kn K)]++nil).
               apply wf_env_kn; auto.

               apply wf_typ_arrow with (K1:=K) (K2:=K); auto.
                 rewrite_env (nil ++ [(X, bind_kn K)] ++ nil).
                 apply wf_typ_weakening; auto.

SSSCase "EQ2222".
  apply F_observational_eq__trans with (e':=exp_tabs K (exp_abs K (typ_arrow K' A 0) (exp_app (exp_tapp h 0) 0))).

SSSSCase "EQ22221".
  assert (JJ:=Rearrangement_DNegation).
  assert (Typing5:=id_typing).
  unfold dnegA in *.
  destruct K'.
    (* K' = 1 *)
    apply F_observational_eq__congr_tabs_labs with (L:={}); auto.
      intros X Xn.
      unfold open_tt. simpl.
      rewrite <- open_tt_rec_type; auto.
      apply wf_typ_arrow with (K1:=K) (K2:=K); auto.
        rewrite_env (nil ++ [(X, bind_kn K)] ++ nil).
        apply wf_typ_weakening; auto.

       intros X x Xn xn.
       unfold open_te. unfold open_tt. unfold open_ee. simpl.
       rewrite <- open_tt_rec_type; auto.
       rewrite <- open_te_rec_expr; auto.
       rewrite <- open_ee_rec_expr; auto.
       simpl_env.
       assert (wf_env [(X, bind_kn K)]) as Wfe1.
                       rewrite_env ([(X, bind_kn K)]++nil).
                       apply wf_env_kn; auto.
       assert (wf_typ [(X, bind_kn K)] A K) as Wft2.
                   rewrite_env (nil ++ [(X, bind_kn K)] ++ nil).
                   apply wf_typ_weakening; auto.
       assert (wf_typ [(X, bind_kn K)] (typ_arrow kn_lin A X) kn_lin) as Wft1.
               apply wf_typ_arrow with (K1:=K) (K2:=K); auto.
       assert (wf_lenv [(X, bind_kn K)] [(x, lbind_typ (typ_arrow kn_lin A X))]) as Wfle1.
                   rewrite_env ([(x, lbind_typ (typ_arrow kn_lin A X))]++nil).
                   apply wf_lenv_typ; auto.
        apply F_ciu_eq__F_observational_eq.
        split.
          apply typing_app with (T1:=A) (D1:=[(x, lbind_typ (typ_arrow kn_lin A X))]) (D2:=nil) (K:=kn_lin); auto.
            apply typing_app with (T1:=typ_arrow kn_lin A A) (D1:=nil) (D2:=nil) (K:=K); auto.
              assert (open_tt (typ_arrow K (typ_arrow kn_lin A 0) 0) A = typ_arrow K (typ_arrow kn_lin A A) A) as EQ.
                unfold open_tt. simpl. rewrite <- open_tt_rec_type; auto.
               rewrite <- EQ.
               apply typing_tapp with (K:=K); auto.
                 rewrite_env (nil ++ [(X, bind_kn K)] ++ nil).
                 apply typing_weakening; auto.

                 rewrite_env (nil ++ [(X, bind_kn K)] ++ nil).
                 apply typing_weakening; auto.
             rewrite_env ([(x, lbind_typ (typ_arrow kn_lin A X))]++nil).
             apply lenv_split_left; auto.
        split. 
          apply typing_app with (T1:=typ_arrow kn_lin A X) (D2:=[(x, lbind_typ (typ_arrow kn_lin A X))]) (D1:=nil) (K:=K); auto.
              assert (open_tt (typ_arrow K (typ_arrow kn_lin A 0) 0) X = typ_arrow K (typ_arrow kn_lin A X) X) as EQ.
                unfold open_tt. simpl. rewrite <- open_tt_rec_type; auto.
               rewrite <- EQ.
               apply typing_tapp with (K:=K); auto.
                 rewrite_env (nil ++ [(X, bind_kn K)] ++ nil).
                 apply typing_weakening; auto.
               rewrite_env ([(x, lbind_typ (typ_arrow kn_lin A X))]++nil).
               apply lenv_split_right; auto.

          intros dsubst gsubst lgsubst Hwflg.
          inversion Hwflg; subst.
          (* inversion Hwflg1 *)
            inversion H2; subst.
            inversion H5; subst.
            simpl in *.
            destruct (x==x); try solve [contradict n; auto].
            destruct (X==X); try solve [contradict n; auto].
            assert (X `notin` fv_te e) as Xn1.
              apply notin_fv_te_typing with (X:=X) in H6; auto.
            assert (x `notin` fv_ee h) as xn1.
              apply notin_fv_ee_typing with (y:=x) in Htyping; auto.
            assert (X `notin` fv_tt A) as Xn2.
              apply notin_fv_wf with (X:=X) in J; auto.
            assert (X `notin` fv_te h) as Xn3.
              apply notin_fv_te_typing with (X:=X) in Htyping; auto.
            rewrite <- subst_ee_fresh; auto.
            rewrite <- subst_tt_fresh; auto.
            rewrite <- subst_te_fresh; auto.
            rewrite <- subst_te_fresh; auto.
            rewrite <- subst_tt_fresh in H6; auto.
           apply F_vobservational_eq__trans with (e':=exp_app (exp_tapp h T) (exp_abs kn_lin A (exp_app e 0))); auto.

             assert (JJ':=@JJ h e T Htyping H15 H6).
             destruct JJ' as [J1 [J2 [J3 J4]]]; auto.

             assert (typing nil nil (exp_tapp h T) (typ_arrow K (typ_arrow kn_lin A T) T)) as Ht_hT.
               assert (open_tt (typ_arrow K (typ_arrow kn_lin A 0) 0) T = typ_arrow K (typ_arrow kn_lin A T) T) as EQ.
                 unfold open_tt. simpl. rewrite <- open_tt_rec_type; auto.
               rewrite <- EQ.
               apply typing_tapp with (K:=K); auto.
             assert (exists v0, normalize (exp_tapp h T) v0) as Hn_hT_v0.
               apply strong_normalization with (t:=typ_arrow K (typ_arrow kn_lin A T) T); auto.
             destruct Hn_hT_v0 as [v0 Hn_hT_v0].
             assert (F_vobservational_eq nil nil (exp_app (exp_tapp h T) e) (exp_app v0 e) T) as hT_eq_v0.
               apply F_observational_eq__F_vobservational_eq.
               apply F_observational_eq__mbeta.
                 apply typing_app with (D1:=nil) (D2:=nil) (T1:=typ_arrow kn_lin A T) (K:=K); auto.

                 destruct Hn_hT_v0.
                 apply bigstep_red_app_1; auto.                      
             assert (F_vobservational_eq nil nil (exp_app (exp_tapp h T) (exp_abs kn_lin A (exp_app e 0))) (exp_app v0 (exp_abs kn_lin A (exp_app e 0))) T) as hT_eq_eta_e.
               apply F_observational_eq__F_vobservational_eq.
               apply F_observational_eq__mbeta.
                 apply typing_app with (D1:=nil) (D2:=nil) (T1:=typ_arrow kn_lin A T) (K:=K); auto.
                   apply typing_eta_abs; auto.

                 destruct Hn_hT_v0.
                 apply bigstep_red_app_1; auto.                      
                   apply expr_abs with (L:={}); auto.
                     intros x0 Hx0. unfold open_ee. simpl.
                     rewrite <- open_ee_rec_expr; auto.

             apply F_vobservational_eq__trans with (e':=exp_app v0 (exp_abs kn_lin A (exp_app e 0))); auto.
             apply F_vobservational_eq__sym in hT_eq_v0. 
             apply F_vobservational_eq__trans with (e':=exp_app v0 e); auto.
             destruct Hn_hT_v0 as [Hv0 Hr_hT_v0].
             apply F_vobservational_eq__congr_app with (lE1:=nil) (lE2:=nil) (K:=K) (t1:=typ_arrow kn_lin A T); auto.
               apply F_observational_eq__F_vobservational_eq.
               apply F_observational_eq__refl; auto.
                 apply preservation_bigstep_red with (e:=exp_tapp h T); auto.

               apply F_vobservational_eq__sym.
               apply F_observational_eq__F_vobservational_eq.
               apply F_observational_eq__eta_abs; auto.

          (* inversion Hwflg2 *)
            inversion H2; subst.
            inversion H4; subst.
            simpl in *.
            assert (X `notin` fv_tt (typ_arrow kn_lin A X)) as Xn1.
              apply notin_fv_wf with (X:=X) in H15; auto.
            simpl in Xn1.
            destruct_notin.
            contradict NotInTac1; auto.

    (* K' = * *)
    apply F_observational_eq__congr_tabs_abs with (L:={}); auto.
      intros X Xn.
      unfold open_tt. simpl.
      rewrite <- open_tt_rec_type; auto.
      apply wf_typ_arrow with (K1:=K) (K2:=K); auto.
        rewrite_env (nil ++ [(X, bind_kn K)] ++ nil).
        apply wf_typ_weakening; auto.

       intros X x Xn xn.
       unfold open_te. unfold open_tt. unfold open_ee. simpl.
       rewrite <- open_tt_rec_type; auto.
       rewrite <- open_te_rec_expr; auto.
       rewrite <- open_ee_rec_expr; auto.
       simpl_env.
       assert (wf_env [(X, bind_kn K)]) as Wfe1.
                       rewrite_env ([(X, bind_kn K)]++nil).
                       apply wf_env_kn; auto.
       assert (wf_typ [(X, bind_kn K)] A K) as Wft2.
                   rewrite_env (nil ++ [(X, bind_kn K)] ++ nil).
                   apply wf_typ_weakening; auto.
       assert (wf_typ [(X, bind_kn K)] (typ_arrow kn_nonlin A X) kn_nonlin) as Wft1.
               apply wf_typ_arrow with (K1:=K) (K2:=K); auto.
        assert (wf_env ([(x, bind_typ (typ_arrow kn_nonlin A X))]++[(X, bind_kn K)])) as Wfle1.
                   apply wf_env_typ; auto.
        assert (wf_typ ([(x, bind_typ (typ_arrow kn_nonlin A X))]++[(X, bind_kn K)]) A K) as Wft3.
                   rewrite_env (nil ++([(x, bind_typ (typ_arrow kn_nonlin A X))]++[(X, bind_kn K)]) ++ nil).
                   apply wf_typ_weakening; auto.
        apply F_ciu_eq__F_observational_eq.
        split.
          apply typing_app with (T1:=A) (D1:=nil) (D2:=nil) (K:=kn_nonlin); auto.
            apply typing_app with (T1:=typ_arrow kn_nonlin A A) (D1:=nil) (D2:=nil) (K:=K); auto.
              assert (open_tt (typ_arrow K (typ_arrow kn_nonlin A 0) 0) A = typ_arrow K (typ_arrow kn_nonlin A A) A) as EQ.
                unfold open_tt. simpl. rewrite <- open_tt_rec_type; auto.
               rewrite <- EQ.
               apply typing_tapp with (K:=K); auto.
                 rewrite_env (nil ++ ([(x, bind_typ (typ_arrow kn_nonlin A X))]++[(X, bind_kn K)]) ++ nil).
                 apply typing_weakening; auto.

                 rewrite_env (nil ++ ([(x, bind_typ (typ_arrow kn_nonlin A X))]++[(X, bind_kn K)]) ++ nil).
                 apply typing_weakening; auto.
        split. 
          apply typing_app with (T1:=typ_arrow kn_nonlin A X) (D2:=nil) (D1:=nil) (K:=K); auto.
              assert (open_tt (typ_arrow K (typ_arrow kn_nonlin A 0) 0) X = typ_arrow K (typ_arrow kn_nonlin A X) X) as EQ.
                unfold open_tt. simpl. rewrite <- open_tt_rec_type; auto.
               rewrite <- EQ.
               apply typing_tapp with (K:=K); auto.
                 rewrite_env (nil ++ ([(x, bind_typ (typ_arrow kn_nonlin A X))]++[(X, bind_kn K)]) ++ nil).
                 apply typing_weakening; auto.

          intros dsubst gsubst lgsubst Hwflg.
          inversion Hwflg; subst.
          (* inversion Hwflg1 *)
            inversion H2; subst.
            inversion H6; subst.
            simpl in *.
            destruct (x==x); try solve [contradict n; auto].
            destruct (X==X); try solve [contradict n; auto].
            assert (X `notin` fv_te e) as Xn1.
              apply notin_fv_te_typing with (X:=X) in H5; auto.
            assert (x `notin` fv_ee h) as xn1.
              apply notin_fv_ee_typing with (y:=x) in Htyping; auto.
            assert (X `notin` fv_tt A) as Xn2.
              apply notin_fv_wf with (X:=X) in J; auto.
            assert (X `notin` fv_te h) as Xn3.
              apply notin_fv_te_typing with (X:=X) in Htyping; auto.
            rewrite <- subst_ee_fresh; auto.
            rewrite <- subst_tt_fresh; auto.
            rewrite <- subst_te_fresh; auto.
            rewrite <- subst_te_fresh; auto.
            rewrite <- subst_tt_fresh in H5; auto.
           apply F_vobservational_eq__trans with (e':=exp_app (exp_tapp h T) (exp_abs kn_nonlin A (exp_app e 0))); auto.

             assert (JJ':=@JJ h e T Htyping H15 H5).
             destruct JJ' as [J1 [J2 [J3 J4]]]; auto.
   
             assert (typing nil nil (exp_tapp h T) (typ_arrow K (typ_arrow kn_nonlin A T) T)) as Ht_hT.
               assert (open_tt (typ_arrow K (typ_arrow kn_nonlin A 0) 0) T = typ_arrow K (typ_arrow kn_nonlin A T) T) as EQ.
                 unfold open_tt. simpl. rewrite <- open_tt_rec_type; auto.
               rewrite <- EQ.
               apply typing_tapp with (K:=K); auto.
             assert (exists v0, normalize (exp_tapp h T) v0) as Hn_hT_v0.
               apply strong_normalization with (t:=typ_arrow K (typ_arrow kn_nonlin A T) T); auto.
             destruct Hn_hT_v0 as [v0 Hn_hT_v0].
             assert (F_vobservational_eq nil nil (exp_app (exp_tapp h T) e) (exp_app v0 e) T) as hT_eq_v0.
               apply F_observational_eq__F_vobservational_eq.
               apply F_observational_eq__mbeta.
                 apply typing_app with (D1:=nil) (D2:=nil) (T1:=typ_arrow kn_nonlin A T) (K:=K); auto.

                 destruct Hn_hT_v0.
                 apply bigstep_red_app_1; auto.                      
             assert (F_vobservational_eq nil nil (exp_app (exp_tapp h T) (exp_abs kn_nonlin A (exp_app e 0))) (exp_app v0 (exp_abs kn_nonlin A (exp_app e 0))) T) as hT_eq_eta_e.
               apply F_observational_eq__F_vobservational_eq.
               apply F_observational_eq__mbeta.
                 apply typing_app with (D1:=nil) (D2:=nil) (T1:=typ_arrow kn_nonlin A T) (K:=K); auto.
                   apply typing_eta_abs; auto.

                 destruct Hn_hT_v0.
                 apply bigstep_red_app_1; auto.                      
                   apply expr_abs with (L:={}); auto.
                     intros x0 Hx0. unfold open_ee. simpl.
                     rewrite <- open_ee_rec_expr; auto.

             apply F_vobservational_eq__trans with (e':=exp_app v0 (exp_abs kn_nonlin A (exp_app e 0))); auto.
             apply F_vobservational_eq__sym in hT_eq_v0. 
             apply F_vobservational_eq__trans with (e':=exp_app v0 e); auto.
             destruct Hn_hT_v0 as [Hv0 Hr_hT_v0].
             apply F_vobservational_eq__congr_app with (lE1:=nil) (lE2:=nil) (K:=K) (t1:=typ_arrow kn_nonlin A T); auto.
               apply F_observational_eq__F_vobservational_eq.
               apply F_observational_eq__refl; auto.
                 apply preservation_bigstep_red with (e:=exp_tapp h T); auto.

               apply F_vobservational_eq__sym.
               apply F_observational_eq__F_vobservational_eq.
               apply F_observational_eq__eta_abs; auto.

SSSSCase "EQ22222".
  apply F_observational_eq__sym.
  apply F_observational_eq__eta_tabs; auto.
Qed.

(* 
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../../../metatheory/" "-I" "../linf/") ***
*** End: ***
 *)

