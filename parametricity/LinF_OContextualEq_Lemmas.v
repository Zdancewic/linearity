(** Authors: Jianzhou Zhao. *)

Require Import LinF_PreLib.
Require Import LinF_Renaming.
Require Export LinF_OParametricity.
Require Import LinF_OParametricity_Macro.
Require Import LinF_ContextualEq_Def.
Require Import LinF_ContextualEq_Infrastructure.
Require Import LinF_ContextualEq_Lemmas.

Export OParametricity.

Lemma wf_dsubst_app_inv : forall E1 E2 dsubst Env,
  wf_delta_osubst (E1++E2) dsubst Env->
  exists dsubst1, exists dsubst2, 
    dsubst = dsubst1 ++ dsubst2 /\
    ddom_env E1 [=] dom dsubst1 /\
    ddom_env E2 [=] dom dsubst2.
Proof.
  intros E1 E2 dsubst Env Wfd.
  remember (E1++E2) as E.
  generalize dependent E1.        
  generalize dependent E2.
  induction Wfd; intros; subst.
    symmetry in HeqE.
    apply app_eq_nil in HeqE.
    destruct HeqE; subst.
    exists nil. exists nil. simpl. auto.

    apply one_eq_app in HeqE.
    destruct HeqE as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      assert (E''++E2=E''++E2) as EQ. auto.
      apply IHWfd in EQ.
      destruct EQ as [dsubst1 [dsubst2 [EQ1 [EQ2 EQ3]]]]; subst.
      exists ([(X, T)]++dsubst1). exists dsubst2.
      simpl. split; auto. split; auto. fsetdec.
 
      assert (E=nil++E) as EQ. auto.
      apply IHWfd in EQ.
      destruct EQ as [dsubst1 [dsubst2 [EQ1 [EQ2 EQ3]]]]; subst.
      exists nil. exists ([(X, T)]++dsubst1++dsubst2).
      simpl. split; auto. split; auto. simpl_env. fsetdec.

    apply one_eq_app in HeqE.
    destruct HeqE as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      assert (E''++E2=E''++E2) as EQ. auto.
      apply IHWfd in EQ.
      destruct EQ as [dsubst1 [dsubst2 [EQ1 [EQ2 EQ3]]]]; subst.
      exists (dsubst1). exists dsubst2.
      simpl. split; auto.
 
      assert (E=nil++E) as EQ. auto.
      apply IHWfd in EQ.
      destruct EQ as [dsubst1 [dsubst2 [EQ1 [EQ2 EQ3]]]]; subst.
      exists nil. exists (dsubst1++dsubst2).
      simpl. split; auto. split; auto. simpl_env. fsetdec.
Qed.

Lemma wf_olgsubst_app_inv : forall E1 E2 D dsubst gsubst lgsubst Env lEnv,
  wf_lgamma_osubst (E1++E2) D dsubst gsubst lgsubst Env lEnv ->
  exists dsubst1, exists dsubst2, exists gsubst1, exists gsubst2,
    dsubst = dsubst1 ++ dsubst2 /\
    ddom_env E1 [=] dom dsubst1 /\
    ddom_env E2 [=] dom dsubst2 /\
    gsubst = gsubst1 ++ gsubst2 /\
    gdom_env E1 [=] dom gsubst1 /\
    gdom_env E2 [=] dom gsubst2.
Proof.
  intros E1 E2 D dsubst gsubst lgsubst Env lEnv Wflg.
  remember (E1++E2) as E.
  generalize dependent E1.        
  generalize dependent E2.
  induction Wflg; intros; subst.
    symmetry in HeqE.
    apply app_eq_nil in HeqE.
    destruct HeqE; subst.
    exists nil. exists nil. exists nil. exists nil. simpl. split; auto.

    apply one_eq_app in HeqE.
    destruct HeqE as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      assert (E''++E2=E''++E2) as EQ. auto.
      apply IHWflg in EQ.
      destruct EQ as [dsubst1 [dsubst2 [gsubst1 [gsubst2 [EQ1 [EQ2 [EQ3 [EQ4 [EQ5 EQ6]]]]]]]]]; subst.
      exists dsubst1. exists dsubst2.
      exists ([(x, e)]++gsubst1). exists gsubst2.
      simpl. split; auto. split; auto. split; auto. split; auto. split; auto. fsetdec.
 
      assert (E=nil++E) as EQ. auto.
      apply IHWflg in EQ.
      destruct EQ as [dsubst1 [dsubst2 [gsubst1 [gsubst2 [EQ1 [EQ2 [EQ3 [EQ4 [EQ5 EQ6]]]]]]]]]; subst.
      exists nil. exists (dsubst1++dsubst2).
      exists nil. exists ([(x, e)]++gsubst1++gsubst2).
      simpl. simpl_env.  split; auto. split; auto. split; auto. 
      rewrite <- EQ2. rewrite <- EQ3. clear. fsetdec. 
      split; auto. split; auto. 
      rewrite <- EQ5. rewrite <- EQ6. clear. fsetdec.

    assert (E1++E2=E1++E2) as EQ. auto.
    apply IHWflg in EQ.
    destruct EQ as [dsubst1 [dsubst2 [gsubst1 [gsubst2 [EQ1 [EQ2 [EQ3 [EQ4 [EQ5 EQ6]]]]]]]]]; subst.
    exists dsubst1. exists dsubst2.
    exists (gsubst1). exists gsubst2.
    split; auto.

    apply one_eq_app in HeqE.
    destruct HeqE as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      assert (E''++E2=E''++E2) as EQ. auto.
      apply IHWflg in EQ.
      destruct EQ as [dsubst1 [dsubst2 [gsubst1 [gsubst2 [EQ1 [EQ2 [EQ3 [EQ4 [EQ5 EQ6]]]]]]]]]; subst.
      exists ([(X, T)]++dsubst1). exists dsubst2.
      exists gsubst1. exists gsubst2.
      simpl. split; auto. split; auto. 
      rewrite <- EQ2. clear. fsetdec.
 
      assert (E=nil++E) as EQ. auto.
      apply IHWflg in EQ.
      destruct EQ as [dsubst1 [dsubst2 [gsubst1 [gsubst2 [EQ1 [EQ2 [EQ3 [EQ4 [EQ5 EQ6]]]]]]]]]; subst.
      exists nil. exists ([(X, T)]++dsubst1++dsubst2).
      exists gsubst1. exists gsubst2.
      simpl. split; auto. split; auto. split; auto. simpl_env. 
      rewrite <- EQ2. rewrite EQ3. clear. fsetdec.
Qed.

Lemma wf_olgsubst_lapp_inv : forall E D1 D2 dsubst gsubst lgsubst Env lEnv,
  wf_lgamma_osubst E (D1++D2) dsubst gsubst lgsubst Env lEnv ->
  exists lgsubst1, exists lgsubst2,
    lgsubst = lgsubst1 ++ lgsubst2 /\
    dom D1 [=] dom lgsubst1 /\
    dom D2 [=] dom lgsubst2.
Proof.
  intros E D1 D2 dsubst gsubst lgsubst Env lEnv Wflg.
  remember (D1++D2) as D.
  generalize dependent D1.        
  generalize dependent D2.
  induction Wflg; intros; subst.
    symmetry in HeqD.
    apply app_eq_nil in HeqD.
    destruct HeqD; subst.
    exists nil. exists nil. simpl. split; auto.

    assert (D1++D2=D1++D2) as EQ. auto.
    apply IHWflg in EQ.
    destruct EQ as [lgsubst1 [lgsubst2 [EQ1 [EQ2 EQ3]]]]; subst.
    exists (lgsubst1). exists lgsubst2.
    split; auto.

    apply one_eq_app in HeqD.
    destruct HeqD as [[D'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      assert (D''++D2=D''++D2) as EQ. auto.
      apply IHWflg in EQ.
      destruct EQ as [lgsubst1 [lgsubst2 [EQ1 [EQ2 EQ3]]]]; subst.
      exists ([(x, e)]++lgsubst1). exists lgsubst2.
      simpl. split; auto. split; auto. 
      rewrite <- EQ2. clear. fsetdec.
 
      assert (lE=nil++lE) as EQ. auto.
      apply IHWflg in EQ.
      destruct EQ as [lgsubst1 [lgsubst2 [EQ1 [EQ2 EQ3]]]]; subst.
      exists nil. exists ([(x, e)]++lgsubst1++lgsubst2).
      simpl. simpl_env.  split; auto. split; auto. 
      rewrite <- EQ2. rewrite <- EQ3. clear. fsetdec.

    assert (D1++D2=D1++D2) as EQ. auto.
    apply IHWflg in EQ.
    destruct EQ as [lgsubst1 [lgsubst2 [EQ1 [EQ2 EQ3]]]]; subst.
    exists (lgsubst1). exists lgsubst2.
    split; auto.
Qed.

Lemma dom_F_Related_osubst : forall E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv,
  F_Related_osubst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
  ddom_env E [=] dom dsubst /\
  ddom_env E [=] dom dsubst' /\
  ddom_env E [=] dom rsubst /\
  gdom_env E [=] dom gsubst /\
  gdom_env E [=] dom gsubst' /\
  dom D [=] dom lgsubst /\
  dom D [=] dom lgsubst'.
Proof.
  induction 1; simpl.
    split; auto. split; auto.

    destruct IHF_Related_osubst as [J1 [J2 [J3 [J4 [J5 [J6 J7]]]]]].
    rewrite <- J1. rewrite <- J2. rewrite <- J3. rewrite <- J4.
    rewrite <- J5. rewrite <- J6. rewrite <- J7.  
    split; auto. fsetdec.
    split. clear. fsetdec.
    split. clear. fsetdec.
    split. clear. fsetdec.
    split. clear. fsetdec.
    split. clear. fsetdec.
               clear. fsetdec.

    destruct IHF_Related_osubst as [J1 [J2 [J3 [J4 [J5 [J6 J7]]]]]].
    rewrite <- J1. rewrite <- J2. rewrite <- J3. rewrite <- J4.
    rewrite <- J5. rewrite <- J6. rewrite <- J7.  
    split; auto. fsetdec.
    split. clear. fsetdec.
    split. clear. fsetdec.
    split. clear. fsetdec.
    split. clear. fsetdec.
    split. clear. fsetdec.
               clear. fsetdec.

    destruct IHF_Related_osubst as [J1 [J2 [J3 [J4 [J5 [J6 J7]]]]]].
    rewrite <- J1. rewrite <- J2. rewrite <- J3. rewrite <- J4.
    rewrite <- J5. rewrite <- J6. rewrite <- J7.  
    split; auto. fsetdec.
    split. clear. fsetdec.
    split. clear. fsetdec.
    split. clear. fsetdec.
    split. clear. fsetdec.
    split. clear. fsetdec.
               clear. fsetdec.
Qed.

Lemma dom_lgamma_osubst : forall E D dsubst gsubst lgsubst Env lEnv,
  wf_lgamma_osubst E D dsubst gsubst lgsubst Env lEnv -> 
  ddom_env E [=] dom dsubst /\
  gdom_env E [=] dom gsubst /\
  dom D [=] dom lgsubst.
Proof.
  intros E D dsubst gsubst lgsubst Env lEnv Wflg.
  induction Wflg; simpl_env; simpl.
    split; auto.

    destruct IHWflg as [J1 [J2 J3]].
    rewrite <- J1. rewrite <- J2. rewrite <- J3.
    split; auto. fsetdec.
    split. clear. fsetdec.
               clear. fsetdec.

    destruct IHWflg as [J1 [J2 J3]].
    rewrite <- J1. rewrite <- J2. rewrite <- J3.
    split; auto. fsetdec.
    split. clear. fsetdec.
               clear. fsetdec.

    destruct IHWflg as [J1 [J2 J3]].
    rewrite <- J1. rewrite <- J2. rewrite <- J3.
    split; auto. fsetdec.
    split. clear. fsetdec.
               clear. fsetdec.
Qed.

Lemma wf_olgsubst_lcons_inv : forall E x T D dsubst gsubst lgsubst Env lEnv,
  wf_lgamma_osubst E ([(x, lbind_typ T)]++D) dsubst gsubst lgsubst Env lEnv ->
  exists e, exists lgsubst', exists lEnv1, exists lEnv',
    lgsubst = [(x, e)] ++ lgsubst' /\
    dom D [=] dom lgsubst' /\
    wf_typ E T kn_lin /\
    lEnv = lEnv1 ++ lEnv' /\
    typing  Env lEnv1 e (apply_delta_subst_typ dsubst T) /\
    wf_lgamma_osubst E D dsubst gsubst lgsubst' Env lEnv'.
Proof.
  intros E x T D dsubst gsubst lgsubst Env lEnv Wflg.
  remember ([(x, lbind_typ T)]++D) as DD.
  generalize dependent D.        
  generalize dependent x.
  generalize dependent T.
  induction Wflg; intros; subst.
    inversion HeqDD.

    assert ([(x0, lbind_typ T0)]++D=[(x0, lbind_typ T0)]++D) as EQ. auto.
    apply IHWflg in EQ.
    destruct EQ as [e0 [lgsubst' [lEnv1 [lEnv' [EQ1 [EQ2 [Wft [EQ3 [Typ Wflg']]]]]]]]]; subst.
    exists e0. exists lgsubst'. exists lEnv1. exists lEnv'. 
    split; auto.
    split; auto.
    split; auto.
      apply wf_typ_weaken_head; auto.
        apply wf_lgamma_osubst__wf_lenv in Wflg.
        destruct Wflg; auto.        

    inversion HeqDD; subst. clear HeqDD.
    exists e. exists lgsE. exists lEnv2. exists lEnv1.
    split; auto.
    split; auto.
      apply dom_lgamma_osubst in Wflg.
      decompose [and] Wflg; auto.

    assert ([(x, lbind_typ T0)]++D=[(x, lbind_typ T0)]++D) as EQ. auto.
    apply IHWflg in EQ.
    destruct EQ as [e [lgsubst' [lEnv1 [lEnv' [EQ1 [EQ2 [Wft [EQ3 [Typ Wflg']]]]]]]]]; subst.
    exists e. exists lgsubst'. exists lEnv1. exists lEnv'. 
    split; auto.
    split; auto.
    split; auto.
      apply wf_typ_weaken_head; auto.
        apply wf_lgamma_osubst__wf_lenv in Wflg.
        destruct Wflg; auto.              
    split; auto.
    split; auto.
      simpl. simpl in H0.
      rewrite <- subst_tt_fresh; auto.
        apply notin_fv_wf with (X:=X) in Wft; auto.
Qed.

Lemma F_Related_osubst_lcons_inv : forall E x T D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv,
  F_Related_osubst E ([(x, lbind_typ T)]++D) gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
  exists v, exists lgsubst0,
    exists v', exists lgsubst0',
    exists lEnv1, exists lEnv',
      lgsubst = [(x, v)] ++ lgsubst0 /\
      lgsubst' = [(x, v')] ++ lgsubst0' /\
      dom D [=] dom lgsubst0 /\
      dom D [=] dom lgsubst0' /\
      wf_typ E T kn_lin /\
      lEnv = lEnv1 ++ lEnv' /\
      typing Env lEnv1 v (apply_delta_subst_typ dsubst T) /\
      typing Env lEnv1 v' (apply_delta_subst_typ dsubst' T) /\
      F_Related_ovalues T rsubst dsubst dsubst' v v' Env lEnv1 /\
      F_Related_osubst E D gsubst gsubst' lgsubst0 lgsubst0' rsubst dsubst dsubst' Env lEnv'.
Proof.
  intros E x T D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv Hrel_subst.
  remember ([(x, lbind_typ T)]++D) as DD.
  generalize dependent D.        
  generalize dependent x.
  generalize dependent T.
  induction Hrel_subst; intros; subst.
    inversion HeqDD.

    assert ([(x, lbind_typ T)]++D=[(x, lbind_typ T)]++D) as EQ. auto.
    apply IHHrel_subst in EQ.
    destruct EQ as [v [lgsubst0 [v' [lgsubst0' [lEnv1 [lEnv' [EQ1 [EQ2 [EQ3 [EQ4 [Wft [EQ5 [Typ [Typ' [Hrel Sub]]]]]]]]]]]]]]]; subst.
    exists v. exists lgsubst0.
    exists v'. exists lgsubst0'.
    exists lEnv1. exists lEnv'.
    simpl_env.
    split; auto.
    split; auto.
    split; auto.
    split; auto.
    split.
      apply wf_typ_weaken_head; auto.
        apply F_Related_osubst__inversion in Hrel_subst.
        decompose [prod] Hrel_subst. auto.
    split; auto.
    split.
      simpl.
      rewrite <- subst_tt_fresh; auto.
        apply notin_fv_wf with (X:=X) in Wft; auto.
    split.
      simpl.
      rewrite <- subst_tt_fresh; auto.
        apply notin_fv_wf with (X:=X) in Wft; auto.
    split.
      apply F_Related_osubst__inversion in Hrel_subst.
      decompose [prod] Hrel_subst.
      apply Forel_weaken_head with (E:=E) (K:=K); auto.
        apply dom_delta_osubst in a0; auto.
        apply dom_delta_osubst in b6; auto.
        apply dom_rho_subst in b3; auto.
        simpl_env in H. apply notin_fv_wf with (X:=X) in Wft; auto.
        apply wfor_left_inv in H0; auto.        
        apply wfor_right_inv in H0; auto.        

      simpl_env in H.
      apply F_Related_osubst_kind; auto.

    assert ([(x0, lbind_typ T)]++D=[(x0, lbind_typ T)]++D) as EQ. auto.
    apply IHHrel_subst in EQ.
    destruct EQ as [v0 [lgsubst0 [v'0 [lgsubst0' [lEnv1 [lEnv' [EQ1 [EQ2 [EQ3 [EQ4 [Wft [EQ5 [Typ [Typ' [Hrel Sub]]]]]]]]]]]]]]]; subst.
    exists v0. exists lgsubst0.
    exists v'0. exists lgsubst0'.
    exists lEnv1. exists lEnv'.
    simpl_env.
    split; auto.
    split; auto.
    split; auto.
    split; auto.
    split.
      apply wf_typ_weaken_head; auto.
        apply F_Related_osubst__inversion in Hrel_subst.
        decompose [prod] Hrel_subst. auto.
    split; auto.
    split; auto.
    split; auto.
    split; auto.
      simpl_env in H2. simpl in H2.
      apply F_Related_osubst_typ; auto.

    simpl_env in HeqDD.
    inversion HeqDD; subst.
    exists v. exists lgsubst.
    exists v'. exists lgsubst'.
    exists lEnv2. exists lEnv1.
    simpl_env.
    assert (J:=Hrel_subst).
    apply F_Related_osubst__inversion in J.
    decompose [prod] J.
    split; auto.
    split; auto.
    split.
        apply dom_lgamma_osubst in b5.
        decompose [and] b5; auto.
    split.
        apply dom_lgamma_osubst in b4.
        decompose [and] b4; auto.
    split; auto.
Qed.

Lemma Forel_stronger_head:  forall t E v v' rsubst dsubst dsubst' X R t2 t2' K Env lEnv,
  F_Related_ovalues t ([(X, R)]++rsubst) ([(X, t2)]++dsubst) ([(X, t2')]++dsubst') v v' Env lEnv ->
  X `notin` (fv_env E `union` (fv_tt t) `union` fv_env Env `union` fv_lenv lEnv)->
  wf_typ Env t2 K ->
  wf_typ Env t2' K ->
  wf_rho_subst ([(X, bind_kn K)]++E) ([(X, R)]++rsubst) ->
  wf_delta_osubst ([(X, bind_kn K)]++E) ([(X, t2)]++dsubst) Env ->
  wf_delta_osubst ([(X, bind_kn K)]++E) ([(X, t2')]++dsubst') Env ->
  F_Related_ovalues t rsubst dsubst dsubst' v v' Env lEnv
  .
Proof.
  intros t E v v' rsubst dsubst dsubst' X R t2 t2' K Env lEnv Hrel HX Hwft2 Hwft2' Rsubst Dsubst Dsubst'.
  rewrite_env (nil ++ [(X, R)] ++ rsubst) in Hrel.
  rewrite_env (nil ++ [(X, t2)] ++ dsubst) in Hrel.
  rewrite_env (nil ++ [(X, t2')] ++ dsubst') in Hrel.
  apply Forel_stronger with (E:=E) (E':=nil) (K:=K) in Hrel; auto.
    inversion Dsubst; subst.
    apply dom_delta_osubst in H5. auto.

    inversion Dsubst'; subst.
    apply dom_delta_osubst in H5. auto.

    inversion Rsubst; subst.
    apply dom_rho_subst in H1. auto.    
Qed.

Lemma  Forel_stronger_heads:  forall t E' E v v' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 Env lEnv,
  F_Related_ovalues t (rsubst'++rsubst) (dsubst0++dsubst) (dsubst'0++dsubst') v v' Env lEnv ->
  ddom_env E [=] dom dsubst ->
  ddom_env E [=] dom dsubst' ->
  ddom_env E' [=] dom dsubst0 ->
  ddom_env E' [=] dom dsubst'0 ->
  ddom_env E [=] dom rsubst ->
  ddom_env E' [=] dom rsubst' ->
  fv_tt t [<=] ddom_env E ->
  disjdom (dom rsubst') (fv_lenv lEnv) ->
  wf_rho_subst (E'++E) (rsubst'++rsubst) ->
  wf_delta_osubst (E'++E) (dsubst0++dsubst) Env ->
  wf_delta_osubst (E'++E) (dsubst'0++dsubst') Env ->
  F_Related_ovalues t rsubst dsubst dsubst' v v' Env lEnv
  .
Proof.
  intros t E' E v v' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 Env lEnv 
    Hrel Hdomd Hdomd' Hdomd0 Hdomd0' Hdomr Hdomr' Hsub Hdisj Hwfr Hwfd Hwfd'.         
  remember (E'++E)  as EE.
  remember (rsubst'++rsubst) as rS.
  generalize dependent E'.
  generalize dependent rsubst'.
  generalize dependent dsubst0.
  generalize dependent dsubst'0.
  (wf_rho_subst_cases (induction Hwfr) Case); intros; subst.
  Case "wf_rho_subst_empty".
    symmetry in HeqrS.
    apply app_eq_nil in HeqrS.
    destruct HeqrS; subst.

    symmetry in HeqEE.
    apply app_eq_nil in HeqEE.
    destruct HeqEE; subst.
    
    inversion Hwfd; subst.
    inversion Hwfd'; subst.

    symmetry in H.
    apply app_eq_nil in H.
    destruct H; subst.

    symmetry in H1.
    apply app_eq_nil in H1.
    destruct H1; subst.

    auto.
  Case "wf_rho_subst_srel".
    inversion Hwfd; subst.
    inversion Hwfd'; subst.    
    simpl_env in *.
    apply one_eq_app in HeqrS. destruct HeqrS as [[rS0 [rEQ1 rEQ2]] | [rEQ1 rEQ2]]; subst.
      apply one_eq_app in H3. destruct H3 as [[dsubst1 [dEQ1 dEQ2]] | [dEQ1 dEQ2]]; subst.
        apply one_eq_app in H5. destruct H5 as [[dsubst1' [dEQ1' dEQ2']] | [dEQ1' dEQ2']]; subst.
          apply one_eq_app in HeqEE. destruct HeqEE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
            simpl_env in Hrel.
            assert (X `notin` fv_env (E0'++E)) as XnE.
              apply wfe_dom_fv_env; auto.
              apply wf_rho_subst__uniq in Hwfr.
              decompose [and] Hwfr; auto.
            apply Forel_stronger_head with (E:=E0'++E) (K:=k) in Hrel; auto.
               apply IHHwfr with (dsubst'0:=dsubst1') (dsubst0:=dsubst1) (rsubst':=rS0) (E':=E0'); auto.
                 clear - Hdisj. 
                 simpl in Hdisj.
                 apply disjdom_cons_2 in Hdisj; auto.

                 apply ddom_dom__inv with (X:=X)(b:=T)(K:=k); auto.
                   destruct_notin.
                   apply dom_delta_osubst in H4.
                   apply free_env__free_ddom in XnE.
                    rewrite H4 in XnE. simpl_env in XnE. auto.

                 apply ddom_dom__inv with (X:=X)(b:=T0)(K:=k); auto.
                   destruct_notin.
                   apply dom_delta_osubst in H8.
                   apply free_env__free_ddom in XnE.
                    rewrite H8 in XnE. simpl_env in XnE. auto.
 
                 apply ddom_dom__inv with (X:=X)(b:=R)(K:=k); auto.
                   destruct_notin.
                   apply dom_rho_subst in Hwfr.
                   apply free_env__free_ddom in XnE.
                    rewrite Hwfr in XnE. simpl_env in XnE. auto.

                 assert (X `notin` fv_tt t) as Xnt.
                   apply free_env__free_ddom in XnE.
                   clear Hrel H H4 H8 Hwfr IHHwfr H4 Hwfd H8 Hwfd' Hdomr' Hdomd0 Hdomd0'.
                   simpl_env in XnE.
                   fsetdec.
                 assert (X `notin` fv_env Env) as XnEnv.
                   apply wf_delta_osubst__uniq in H4. decompose [and] H4.
                   apply wfe_dom_fv_env; auto.
                 assert (X `notin` fv_lenv lEnv) as XnlEnv.
                   clear - Hdisj. simpl in Hdisj. apply disjdom_cons_1 in Hdisj; auto.
                 auto.

            simpl_env in Hdomr'.
            assert (X `notin` (singleton X `union` dom rS0) -> False) as J.
              intro. destruct_notin. contradict NotInTac0; auto.
            rewrite <- Hdomr' in J.
            contradict J; auto.

          apply one_eq_app in HeqEE. destruct HeqEE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
            simpl_env in Hdomd0'.
            assert (X `notin` (singleton X `union` ddom_env E0') -> False) as J.
              intro. destruct_notin. contradict NotInTac0; auto.
            rewrite Hdomd0' in J.
            contradict J; auto.

            simpl_env in Hdomd0.
            assert (X `notin` (singleton X `union` dom dsubst1) -> False) as J.
              intro. destruct_notin. contradict NotInTac0; auto.
            rewrite <- Hdomd0 in J.
            contradict J; auto.

        apply one_eq_app in HeqEE. destruct HeqEE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
          simpl_env in Hdomd0.
          assert (X `notin` (singleton X `union` ddom_env E0') -> False) as J.
            intro. destruct_notin. contradict NotInTac0; auto.
          rewrite Hdomd0 in J.
          contradict J; auto.

          simpl_env in Hdomr'.
          assert (X `notin` (singleton X `union` dom rS0) -> False) as J.
            intro. destruct_notin. contradict NotInTac0; auto.
          rewrite <- Hdomr' in J.
          contradict J; auto.

      apply one_eq_app in HeqEE. destruct HeqEE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
        simpl_env in Hdomr'.
        assert (X `notin` (singleton X `union` ddom_env E0') -> False) as J.
          intro. destruct_notin. contradict NotInTac0; auto.
        rewrite Hdomr' in J.
        contradict J; auto.

        simpl in Hdomd0. symmetry in Hdomd0.  apply dom_empty_inv in Hdomd0.
        simpl in Hdomd0'. symmetry in Hdomd0'.  apply dom_empty_inv in Hdomd0'.
        subst. 
        simpl_env in H7. simpl_env in H3.
        subst.
        simpl_env. auto.

  Case "wf_rho_subst_skip".
    inversion Hwfd; subst.
    inversion Hwfd'; subst.    
    simpl_env in *.
    apply one_eq_app in HeqEE. destruct HeqEE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
      apply IHHwfr with (dsubst'0:=dsubst'0) (dsubst0:=dsubst0) (rsubst'0:=rsubst') (E':=E0'); auto.

      simpl in Hdomd0. symmetry in Hdomd0.  apply dom_empty_inv in Hdomd0.
      simpl in Hdomd0'. symmetry in Hdomd0'.  apply dom_empty_inv in Hdomd0'.
      simpl in Hdomr'. symmetry in Hdomr'.  apply dom_empty_inv in Hdomr'.
      subst. auto.
Qed.

Lemma  Forel_weaken_heads:  forall t E' E v v' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 Env lEnv ,
  F_Related_ovalues t rsubst dsubst dsubst' v v' Env lEnv ->
  ddom_env E [=] dom dsubst ->
  ddom_env E [=] dom dsubst' ->
  ddom_env E' [=] dom dsubst0 ->
  ddom_env E' [=] dom dsubst'0 ->
  ddom_env E [=] dom rsubst ->
  ddom_env E' [=] dom rsubst' ->
  fv_tt t [<=] ddom_env E ->
  disjdom (dom rsubst') (fv_lenv lEnv) ->
  wf_rho_subst (E'++E) (rsubst'++rsubst) ->
  wf_delta_osubst (E'++E) (dsubst0++dsubst) Env ->
  wf_delta_osubst (E'++E) (dsubst'0++dsubst') Env ->
  F_Related_ovalues t (rsubst'++rsubst) (dsubst0++dsubst) (dsubst'0++dsubst') v v' Env lEnv
  .
Proof.
  intros t E' E v v' rsubst rsubst' dsubst dsubst' dsubst0 dsubst'0 Env lEnv Hrel
    Hdomd Hdomd' Hdomd0 Hdomd0' Hdomr Hdomr' Hsub Hdisj Hwfr Hwfd Hwfd'.         
  remember (E'++E)  as EE.
  remember (rsubst'++rsubst) as rS.
  generalize dependent E'.
  generalize dependent rsubst'.
  generalize dependent dsubst0.
  generalize dependent dsubst'0.
  (wf_rho_subst_cases (induction Hwfr) Case); intros; subst.
  Case "wf_rho_subst_empty".
    symmetry in HeqrS.
    apply app_eq_nil in HeqrS.
    destruct HeqrS; subst.

    symmetry in HeqEE.
    apply app_eq_nil in HeqEE.
    destruct HeqEE; subst.
    
    inversion Hwfd; subst.
    inversion Hwfd'; subst.

    symmetry in H.
    apply app_eq_nil in H.
    destruct H; subst.

    symmetry in H1.
    apply app_eq_nil in H1.
    destruct H1; subst.

    auto.
  Case "wf_rho_subst_srel".
    inversion Hwfd; subst.
    inversion Hwfd'; subst.    
    simpl_env in *.
    apply one_eq_app in HeqrS. destruct HeqrS as [[rS0 [rEQ1 rEQ2]] | [rEQ1 rEQ2]]; subst.
      apply one_eq_app in H3. destruct H3 as [[dsubst1 [dEQ1 dEQ2]] | [dEQ1 dEQ2]]; subst.
        apply one_eq_app in H5. destruct H5 as [[dsubst1' [dEQ1' dEQ2']] | [dEQ1' dEQ2']]; subst.
          apply one_eq_app in HeqEE. destruct HeqEE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
            assert (X `notin` fv_env (E0'++E)) as XnE.
              apply wfe_dom_fv_env; auto.
              apply wf_rho_subst__uniq in Hwfr.
              decompose [and] Hwfr; auto.
            apply Forel_weaken_head with (E:=E0'++E) (K:=k); auto.
               apply IHHwfr with (dsubst'0:=dsubst1') (dsubst0:=dsubst1) (rsubst':=rS0) (E':=E0'); auto.
                 clear - Hdisj. 
                 simpl in Hdisj.
                 apply disjdom_cons_2 in Hdisj; auto.

                 apply ddom_dom__inv with (X:=X)(b:=T)(K:=k); auto.
                   destruct_notin.
                   apply dom_delta_osubst in H4.
                   apply free_env__free_ddom in XnE.
                    rewrite H4 in XnE. simpl_env in XnE. auto.

                 apply ddom_dom__inv with (X:=X)(b:=T0)(K:=k); auto.
                   destruct_notin.
                   apply dom_delta_osubst in H8.
                   apply free_env__free_ddom in XnE.
                    rewrite H8 in XnE. simpl_env in XnE. auto.
 
                 apply ddom_dom__inv with (X:=X)(b:=R)(K:=k); auto.
                   destruct_notin.
                   apply dom_rho_subst in Hwfr.
                   apply free_env__free_ddom in XnE.
                    rewrite Hwfr in XnE. simpl_env in XnE. auto.

               apply dom_delta_osubst in H4. auto.

               apply dom_delta_osubst in H8. auto.

               apply dom_rho_subst in Hwfr. auto.

               assert (X `notin` fv_tt t) as Xnt.
                 apply free_env__free_ddom in XnE.
                 clear Hrel H H6 H10 Hwfr IHHwfr H4 Hwfd H8 Hwfd' Hdomr' Hdomd0 Hdomd0'.
                 simpl_env in XnE.
                  fsetdec.
                 assert (X `notin` fv_env Env) as XnEnv.
                   apply wf_delta_osubst__uniq in H4. decompose [and] H4.
                   apply wfe_dom_fv_env; auto.
                 assert (X `notin` fv_lenv lEnv) as XnlEnv.
                   clear - Hdisj. simpl in Hdisj. apply disjdom_cons_1 in Hdisj; auto.
                 auto.

            simpl_env in Hdomr'.
            assert (X `notin` (singleton X `union` dom rS0) -> False) as J.
              intro. destruct_notin. contradict NotInTac0; auto.
            rewrite <- Hdomr' in J.
            contradict J; auto.

          apply one_eq_app in HeqEE. destruct HeqEE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
            simpl_env in Hdomd0'.
            assert (X `notin` (singleton X `union` ddom_env E0') -> False) as J.
              intro. destruct_notin. contradict NotInTac0; auto.
            rewrite Hdomd0' in J.
            contradict J; auto.

            simpl_env in Hdomd0.
            assert (X `notin` (singleton X `union` dom dsubst1) -> False) as J.
              intro. destruct_notin. contradict NotInTac0; auto.
            rewrite <- Hdomd0 in J.
            contradict J; auto.

        apply one_eq_app in HeqEE. destruct HeqEE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
          simpl_env in Hdomd0.
          assert (X `notin` (singleton X `union` ddom_env E0') -> False) as J.
            intro. destruct_notin. contradict NotInTac0; auto.
          rewrite Hdomd0 in J.
          contradict J; auto.

          simpl_env in Hdomr'.
          assert (X `notin` (singleton X `union` dom rS0) -> False) as J.
            intro. destruct_notin. contradict NotInTac0; auto.
          rewrite <- Hdomr' in J.
          contradict J; auto.

      apply one_eq_app in HeqEE. destruct HeqEE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
        simpl_env in Hdomr'.
        assert (X `notin` (singleton X `union` ddom_env E0') -> False) as J.
          intro. destruct_notin. contradict NotInTac0; auto.
        rewrite Hdomr' in J.
        contradict J; auto.

        simpl in Hdomd0. symmetry in Hdomd0.  apply dom_empty_inv in Hdomd0.
        simpl in Hdomd0'. symmetry in Hdomd0'.  apply dom_empty_inv in Hdomd0'.
        subst. 
        simpl_env in H5. simpl_env in H3.
        subst.
        simpl_env. auto.

  Case "wf_rho_subst_skip".
    inversion Hwfd; subst.
    inversion Hwfd'; subst.    
    simpl_env in *.
    apply one_eq_app in HeqEE. destruct HeqEE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
      apply IHHwfr with (dsubst'0:=dsubst'0) (dsubst0:=dsubst0) (rsubst'0:=rsubst') (E':=E0'); auto.

      simpl in Hdomd0. symmetry in Hdomd0.  apply dom_empty_inv in Hdomd0.
      simpl in Hdomd0'. symmetry in Hdomd0'.  apply dom_empty_inv in Hdomd0'.
      simpl in Hdomr'. symmetry in Hdomr'.  apply dom_empty_inv in Hdomr'.
      subst. auto.
Qed.

Lemma apply_delta_osubst_typ_strenghen : forall E1 E2 dsubst1 dsubst2 T Env,
  wf_delta_osubst (E1++E2) (dsubst1++dsubst2) Env ->
  ddom_env E1 [=] dom dsubst1 ->
  ddom_env E2 [=] dom dsubst2 ->
  fv_tt T [<=] ddom_env E2 ->
  apply_delta_subst_typ (dsubst1++dsubst2) T = apply_delta_subst_typ dsubst2 T.
Proof.
  intros E1 E2 dsubst1 dsubst2 T Env Hwfd Hdom1 Hdom2 Hsub.
  remember (E1++E2) as E.
  remember (dsubst1++dsubst2) as dsubst.
  generalize dependent E1.
  generalize dependent dsubst1.
  (wf_delta_osubst_cases (induction Hwfd) Case); intros; subst.
  Case "wf_delta_osubst_empty".
    symmetry in HeqE.
    apply app_eq_nil in HeqE.
    destruct HeqE; subst.

    symmetry in Heqdsubst.
    apply app_eq_nil in Heqdsubst.
    destruct Heqdsubst; subst.
    
    simpl. auto.
  Case "wf_delta_osubst_styp".
    apply one_eq_app in HeqE. destruct HeqE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
      apply one_eq_app in Heqdsubst. destruct Heqdsubst as [[dsubst0' [dEQ1' dEQ2']] | [dEQ1' dEQ2']]; subst; auto.
        simpl.
        assert (X `notin` fv_env (E0'++E2)) as XnE.
          apply wfe_dom_fv_env; auto.
          apply  wf_delta_osubst__uniq in Hwfd.
          decompose [and] Hwfd; auto.
          apply free_env__free_ddom in XnE.
        rewrite <- subst_tt_fresh; auto.
          eapply IHHwfd; eauto.
            apply ddom_dom__inv with (X:=X)(b:=T0)(K:=k); auto.
            apply dom_delta_osubst in Hwfd.
            rewrite Hwfd in XnE.
            simpl_env in XnE. auto.
          simpl_env in XnE.  fsetdec.
            
        simpl in Hdom1. symmetry in Hdom1.  apply dom_empty_inv in Hdom1.
        subst. 
        simpl_env in Heqdsubst.
        subst. auto.
  Case "wf_delta_osubst_skip".
    apply one_eq_app in HeqE. destruct HeqE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
      eapply IHHwfd; eauto.

      simpl in Hdom1. symmetry in Hdom1.  apply dom_empty_inv in Hdom1.
      subst. auto. 
Qed.

Lemma gamma_osubst_opt :  forall E E' D dsubst x t gsubst gsubst' v lgsubst e Env lEnv,
   wf_lgamma_osubst (E'++[(x, bind_typ t)]++E) D dsubst (gsubst'++[(x, v)]++gsubst) lgsubst Env lEnv ->
   gdom_env E [=] dom gsubst ->
   gdom_env E' [=] dom gsubst' ->
   typing Env nil v (apply_delta_subst_typ dsubst t) ->
   apply_gamma_subst (gsubst'++[(x, v)]++gsubst) e =
    apply_gamma_subst (gsubst'++gsubst) (subst_ee x v e).
Proof.
  intros E E' D dsubst x t gsubst gsubst' v lgsubst e Env lEnv Hwf_lgamma_subst Heq Heq' Typ.
  remember (E'++[(x, bind_typ t)]++E) as G.
  remember (gsubst'++[(x, v)]++gsubst) as Gsubst.
  generalize dependent e.
  generalize dependent gsubst'.
  generalize dependent E'.
  (wf_lgamma_osubst_cases (induction Hwf_lgamma_subst) Case); intros; subst.
  Case "wf_lgamma_osubst_empty".
    contradict HeqG; auto.    
  Case "wf_lgamma_osubst_sval".
    destruct (one_eq_app _ _ _ _ _ HeqG) as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
    SCase "exists E'', E'=E&X0'' /\ E0=E&X&E'' ".
      destruct (one_eq_app _ _ _ _ _ HeqGsubst) as [[gsubst'' [GEQ1 GEQ2]] | [GEQ1 GEQ2]]; subst.
      SSCase "exists GS'',GS'=GS&X0'' /\ GS0=GS&X&GS'' ".
        simpl. simpl_env. 
        rewrite <- subst_ee_commute; auto.
           apply IHHwf_lgamma_subst with (E':=E'') (gsubst':=gsubst''); auto.
             apply gdom_dom__inv with (x:=x0)(b:= e)(t:=T); auto.
               destruct_notin.
               apply dom__gdom in H.
               simpl_env in H. auto.

               apply dom_lgamma_osubst in Hwf_lgamma_subst.
               destruct Hwf_lgamma_subst as [J1 [J2 J3]].
               destruct_notin.
               apply dom__gdom in H.
               rewrite J2 in H. simpl_env in *. auto.
          eauto using notin_fv_ee_typing.
          assert (x `notin` dom Env).
            apply disjoint_lgamma_osubst in Hwf_lgamma_subst.
            decompose [and] Hwf_lgamma_subst.
            clear - H5. solve_uniq.
          eauto using notin_fv_ee_typing.
      SSCase "GS'=nil /\ GS&X = GS0&X0 ".
        inversion GEQ2. subst.
        simpl_env in *. destruct_notin.
        auto.
    SCase "E'=nil /\ E&X = E0&X0 ".
      inversion EQ2; subst.
      destruct (one_eq_app _ _ _ _ _ HeqGsubst) as [[gsubst'' [GEQ1 GEQ2]] | [GEQ1 GEQ2]]; subst.
      SSCase "exists GS'',GS'=GS&X0'' /\ GS0=GS&X&GS'' ".
        simpl_env in Heq'.
        assert (x0 `notin` (singleton x0 `union` dom gsubst'') -> False) as J.
            intro. destruct_notin. apply NotInTac0; auto.
        rewrite <- Heq' in J.
        contradict J; auto.
     SSCase "GS'=nil /\ GS&X = GS0&X0 ".
        inversion GEQ2; subst; auto.
  Case "wf_lgamma_osubst_slval".
    apply IHHwf_lgamma_subst with (E'0:=E') (gsubst'0:=gsubst'); auto.
  Case "wf_lgamma_osubst_skind".
    destruct (one_eq_app _ _ _ _ _ HeqG) as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      apply IHHwf_lgamma_subst with (E':=E'') (gsubst'0:=gsubst'); auto.
        simpl in Typ.
        apply wf_lgamma_osubst__wf_lenv in Hwf_lgamma_subst.
        destruct Hwf_lgamma_subst as [J1 J2].
        apply wfe_dom_fv_env with (x:=X) in J1; auto.
        simpl_env in J1. simpl in J1.
        rewrite <- subst_tt_fresh in Typ; auto.

      simpl_env in HeqG.
      inversion HeqG.
Qed.

Lemma dom_F_Rosubst : forall E rsubst dsubst dsubst' Env,
  F_Rosubst E rsubst dsubst dsubst' Env ->
  ddom_env E [=] dom dsubst /\
  ddom_env E [=] dom dsubst' /\
  ddom_env E [=] dom rsubst.
Proof.
  induction 1; simpl.
    split; auto.

    destruct IHF_Rosubst as [J1 [J2 J3]].
    rewrite <- J1. rewrite <- J2. rewrite <- J3.  
    split; auto. fsetdec.
    split. clear. fsetdec.
               clear. fsetdec.

    destruct IHF_Rosubst as [J1 [J2 J3]].
    rewrite <- J1. rewrite <- J2. rewrite <- J3.  
    split; auto. fsetdec.
    split. clear. fsetdec.
               clear. fsetdec.
Qed.

Lemma delta_osubst_opt' :  forall E E' dsubst dsubst' X k t e Env,
   wf_delta_osubst (E'++[(X, bind_kn k)]++E) (dsubst'++[(X, t)]++dsubst) Env ->
   ddom_env E [=] dom dsubst ->
   ddom_env E' [=] dom dsubst' ->
   wf_typ Env t k ->
   apply_delta_subst (dsubst'++[(X, t)]++dsubst) e =
    apply_delta_subst (dsubst'++dsubst) (subst_te X t e).
Proof.
  intros E E' dsubst dsubst' X k t e Env Hwf_delta_subst Heq Heq' Typ.
  remember (E'++[(X, bind_kn k)]++E) as G.
  remember (dsubst'++[(X, t)]++dsubst) as Dsubst.
  generalize dependent e.
  generalize dependent dsubst'.
  generalize dependent E'.
  (wf_delta_osubst_cases (induction Hwf_delta_subst) Case); intros; subst.
  Case "wf_delta_osubst_empty".
    contradict HeqG; auto.    
  Case "wf_delta_osubst_styp".
    destruct (one_eq_app _ _ _ _ _ HeqG) as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
    SCase "exists E'', E'=E&X0'' /\ E0=E&X&E'' ".
      destruct (one_eq_app _ _ _ _ _ HeqDsubst) as [[dsubst'' [DEQ1 DEQ2]] | [DEQ1 DEQ2]]; subst.
      SSCase "exists DS'',DS'=DS&X0'' /\ DS0=DS&X&DS'' ".
        simpl. simpl_env. 
        rewrite <- subst_te_commute; auto.
           apply IHHwf_delta_subst with (E':=E'') (dsubst':=dsubst''); auto.
             apply ddom_dom__inv with (X:=X0)(b:= T)(K:=k0); auto.
               apply dom_delta_osubst in Hwf_delta_subst.
               destruct_notin.
               apply dom__ddom in H.
               rewrite Hwf_delta_subst in H. simpl_env in *. auto.
          assert (X `notin` dom Env). 
            apply disjoint_delta_osubst in Hwf_delta_subst.
            decompose [and] Hwf_delta_subst.
            clear - H1. solve_uniq.
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
        assert (X0 `notin` (singleton X0 `union` dom dsubst'') -> False) as J.
            intro. destruct_notin. apply NotInTac0; auto.
        rewrite <- Heq' in J.
        contradict J; auto.
     SSCase "DS'=nil /\ DS&X = DS0&X0 ".
        inversion DEQ2; subst; auto.
  Case "wf_delta_osubst_skip".
    destruct (one_eq_app _ _ _ _ _ HeqG) as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      apply IHHwf_delta_subst with (E':=E'') (dsubst'0:=dsubst'); auto.

      simpl_env in HeqG.
      inversion HeqG.
Qed.

Definition P_Forel_typ_permute_renaming_one (n:nat) := 
  ((forall t v v' E1 E2 E3 rsubst1 rsubst2 rsubst3 dsubst1 dsubst2 dsubst3 dsubst1' dsubst2' dsubst3' X R t2 t2' Y K Env lEnv,
  typ_size t = n ->
  (F_Related_ovalues t (rsubst1++rsubst2++[(X, R)]++rsubst3) (dsubst1++dsubst2++[(X, t2)]++dsubst3) (dsubst1'++dsubst2'++[(X, t2')]++dsubst3') v v' Env lEnv->
  ddom_env E1 [=] dom rsubst1 ->
  ddom_env E1 [=] dom dsubst1 ->
  ddom_env E1 [=] dom dsubst1' ->
  ddom_env E2 [=] dom rsubst2 ->
  ddom_env E2 [=] dom dsubst2 ->
  ddom_env E2 [=] dom dsubst2' ->
  ddom_env E3 [=] dom rsubst3 ->
  ddom_env E3 [=] dom dsubst3 ->
  ddom_env E3 [=] dom dsubst3' ->
  wfor Env R t2 t2' K ->
  wf_rho_subst (E1++E2++[(X, bind_kn K)]++E3) (rsubst1++rsubst2++[(X, R)]++rsubst3) ->
  wf_delta_osubst (E1++E2++[(X, bind_kn K)]++E3) (dsubst1++dsubst2++[(X, t2)]++dsubst3) Env ->
  wf_delta_osubst (E1++E2++[(X, bind_kn K)]++E3) (dsubst1'++dsubst2'++[(X, t2')]++dsubst3') Env  ->
  wf_delta_osubst (E1++[(Y, bind_kn K)]++E2++E3) (dsubst1++[(Y, t2)]++dsubst2++dsubst3) Env  ->
  wf_delta_osubst (E1++[(Y, bind_kn K)]++E2++E3) (dsubst1'++[(Y, t2')]++dsubst2'++dsubst3') Env  ->
  Y `notin` (dom E1 `union` dom E2 `union` dom E3 `union` (fv_tt t) `union` dom Env `union` dom lEnv)->
  F_Related_ovalues (subst_tt X Y t) (rsubst1++[(Y, R)]++rsubst2++rsubst3) (dsubst1++[(Y, t2)]++dsubst2++dsubst3) (dsubst1'++[(Y, t2')]++dsubst2'++dsubst3') v v' Env lEnv))
  *
  (forall t v v' E1 E2 E3 (rsubst1 rsubst2 rsubst3:rho_subst) dsubst1 dsubst2 dsubst3 dsubst1' dsubst2' dsubst3' (X:atom) (R:rel) t2 t2' (Y:atom) K Env lEnv,
  typ_size t = n ->
  (F_Related_ovalues (subst_tt X Y t) (rsubst1++[(Y, R)]++rsubst2++rsubst3) (dsubst1++[(Y, t2)]++dsubst2++dsubst3) (dsubst1'++[(Y, t2')]++dsubst2'++dsubst3') v v' Env lEnv ->
  ddom_env E1 [=] dom rsubst1 ->
  ddom_env E1 [=] dom dsubst1 ->
  ddom_env E1 [=] dom dsubst1' ->
  ddom_env E2 [=] dom rsubst2 ->
  ddom_env E2 [=] dom dsubst2 ->
  ddom_env E2 [=] dom dsubst2' ->
  ddom_env E3 [=] dom rsubst3 ->
  ddom_env E3 [=] dom dsubst3 ->
  ddom_env E3 [=] dom dsubst3' ->
  wfor Env R t2 t2' K ->
  wf_rho_subst (E1++E2++[(X, bind_kn K)]++E3) (rsubst1++rsubst2++[(X, R)]++rsubst3) ->
  wf_delta_osubst (E1++E2++[(X, bind_kn K)]++E3) (dsubst1++dsubst2++[(X, t2)]++dsubst3) Env ->
  wf_delta_osubst (E1++E2++[(X, bind_kn K)]++E3) (dsubst1'++dsubst2'++[(X, t2')]++dsubst3') Env ->
  wf_delta_osubst (E1++[(Y, bind_kn K)]++E2++E3) (dsubst1++[(Y, t2)]++dsubst2++dsubst3) Env ->
  wf_delta_osubst (E1++[(Y, bind_kn K)]++E2++E3) (dsubst1'++[(Y, t2')]++dsubst2'++dsubst3') Env ->
  Y `notin` (dom E1 `union` dom E2 `union` dom E3 `union` (fv_tt t) `union` dom Env `union` dom lEnv)->
  F_Related_ovalues t (rsubst1++rsubst2++[(X, R)]++rsubst3) (dsubst1++dsubst2++[(X, t2)]++dsubst3) (dsubst1'++dsubst2'++[(X, t2')]++dsubst3') v v' Env lEnv))) % type
  .

Lemma _Forel_typ_permute_renaming_one:  forall n, P_Forel_typ_permute_renaming_one n.
Proof.
  intro n.
  apply lt_wf_ind. clear n.
  intros n H.
  unfold P_Forel_typ_permute_renaming_one in *.
  split.
  (* -> *)
  intros t v v' E1 E2 E3 rsubst1 rsubst2 rsubst3 dsubst1 dsubst2 dsubst3 dsubst1' dsubst2' dsubst3' X R t2 t2' Y K Env lEnv
     Htsize Hrel Heqr1 Heqd1 Heqd1' Heqr2 Heqd2 Heqd2' Heqr3 Heqd3 Heqd3' WfR Wfr Wfd Wfd' Wfd0 Wfd0' Hfv.
  (typ_cases (destruct t) Case).

  Case "typ_bvar". (*bvar*)
  apply F_Related_ovalues_bvar_leq in Hrel; auto.

  Case "typ_fvar". (* fvar *)
  apply F_Related_ovalues_fvar_leq in Hrel.
  unfold In_rel in Hrel.  
  destruct Hrel as [R0 [Hb [Hv [Hv' Hr]]]]; subst; simpl.
  simpl. simpl_env.
  destruct (a==X); subst.
    apply F_Related_ovalues_fvar_req.
    apply wf_rho_subst__uniq in Wfr.
    decompose [and] Wfr.
    analyze_binds_uniq Hb.
      exists (R).
      simpl_env.
      repeat(split; auto).

    apply F_Related_ovalues_fvar_req.
    apply wf_rho_subst__uniq in Wfr.
    decompose [and] Wfr.
    analyze_binds_uniq Hb.
      exists (R0).
      simpl_env.
      repeat(split; auto).

      exists (R0).
      simpl_env.
      repeat(split; auto).

      exists (R0).
      simpl_env.
      repeat(split; auto).

  Case "typ_arrow". (* arrow *)
  apply F_Related_ovalues_arrow_leq in Hrel.
  simpl. simpl_env.
  apply F_Related_ovalues_arrow_req.
  destruct Hrel as [Hv [Hv' [L Harrow]]]; subst.
  repeat(split; simpl_env; auto).
     SCase "arrow".
     exists (L `union` {{Y}}).
     intros lEnv1 x x' Htypingx Htypingx' Wfle Disj Harrow'.
     rename Harrow' into Hrel_wft1'.
     simpl_env in *.

     assert (typ_size t1 < typ_size (typ_arrow k t1 t3)) as G1. simpl. omega.
     apply H in G1; auto.
     destruct G1 as [Hrel_wft1_wft1' Hrel_wft1'_wft1].
     simpl in Hfv.
     assert (Y `notin` dom lEnv1).
       apply disjdom_one_1.
       apply disjdom_app_2 in Disj; auto.
     apply Hrel_wft1'_wft1 with (E1:=E1) (E2:=E2) (E3:=E3) (K:=K) in Hrel_wft1'; auto; simpl_env.
       SSCase "arrow".
       destruct (@Harrow lEnv1 x x') as [u [u' [Hnorm_vxu [Hnorm_v'x'u' Hrel_wft1]]]]; auto.
         assert (ddom_env (E2++E3) [=] dom (dsubst2++dsubst3)) as EQ1.
           simpl_env. rewrite Heqd2. rewrite Heqd3. 
           clear. fsetdec.
         assert (wf_typ Env t2 K) as Wft2.
           apply wfor_left_inv in WfR; auto.
         rewrite delta_osubst_opt with (Env:=Env) (E:=E2++E3) (E':=E1) (K:=K) in Htypingx; auto.
         assert (ddom_env (E1++E2) [=] dom (dsubst1++dsubst2)) as EQ2.
           simpl_env. rewrite Heqd1. rewrite Heqd2. 
           clear. fsetdec.
         rewrite_env ((dsubst1++dsubst2)++[(X, t2)]++dsubst3).
         rewrite_env ((dsubst1++dsubst2)++[(X, t2)]++dsubst3) in Wfd.
         rewrite_env ((E1++E2)++[(X, bind_kn K)]++E3) in Wfd.
         assert (X `notin` dom (E1++E2) `union` dom E3 `union` dom Env) as Xn.
           apply wf_rho_subst__uniq in Wfr.
           decompose [and] Wfr.
           apply disjoint_delta_osubst in Wfd.
           decompose [and] Wfd.
           clear - H3 H2.
           simpl_env. solve_uniq.
         rewrite delta_osubst_opt with (Env:=Env) (E:=E3) (E':=E1++E2) (K:=K); auto.
           simpl_env.
           rewrite subst_tt_tt' with (Env:=Env) (K:=K) in Htypingx; auto.

         assert (ddom_env (E2++E3) [=] dom (dsubst2'++dsubst3')) as EQ1.
           simpl_env. rewrite Heqd2'. rewrite Heqd3'. 
           clear. fsetdec.
         assert (wf_typ Env t2' K) as Wft2'.
           apply wfor_right_inv in WfR; auto.
         rewrite delta_osubst_opt with (Env:=Env) (E:=E2++E3) (E':=E1) (K:=K) in Htypingx'; auto.
         assert (ddom_env (E1++E2) [=] dom (dsubst1'++dsubst2')) as EQ2.
           simpl_env. rewrite Heqd1'. rewrite Heqd2'. 
           clear. fsetdec.
         rewrite_env ((dsubst1'++dsubst2')++[(X, t2')]++dsubst3').
         rewrite_env ((dsubst1'++dsubst2')++[(X, t2')]++dsubst3') in Wfd'.
         rewrite_env ((E1++E2)++[(X, bind_kn K)]++E3) in Wfd'.
         assert (X `notin` dom (E1++E2) `union` dom E3 `union` dom Env) as Xn.
           apply wf_rho_subst__uniq in Wfr.
           decompose [and] Wfr.
           apply disjoint_delta_osubst in Wfd.
           decompose [and] Wfd.
           clear - H3 H2.
           simpl_env. solve_uniq.
         rewrite delta_osubst_opt with (Env:=Env) (E:=E3) (E':=E1++E2) (K:=K); auto.
           simpl_env.
           rewrite subst_tt_tt' with (Env:=Env) (K:=K) in Htypingx'; auto.

         apply disjdom_app_1 in Disj. auto.

       exists (u). exists (u'). repeat(split; auto).
       assert (typ_size t3 < typ_size (typ_arrow k t1 t3)) as G2. simpl. omega.
       apply H in G2. destruct G2 as [Hrel_wft2_wft2' Hrel_wft2'_wft2].
       simpl in Hfv.
       apply Hrel_wft2_wft2' with (E1:=E1) (E2:=E2) (E3:=E3) (K:=K); auto.

  Case "typ_all". (* all *)
  apply F_Related_ovalues_all_leq in Hrel.
  simpl. simpl_env.
  apply F_Related_ovalues_all_req.
  destruct Hrel as [Hv [Hv' [L' Hall]]]; subst.
  repeat(split; simpl_env; auto).
     SCase "all".
     exists (L' `union` singleton X `union` singleton Y `union` dom E1 `union` dom E2 `union` dom E3 `union` fv_tt t `union` dom Env `union` dom lEnv).
      intros X1 t3 t2'0 R0 Fr Hwfr' Hfv'.
      assert (X1 `notin` L') as Fr''. auto.
      destruct (@Hall X1 t3 t2'0 R0 Fr'') as [w0 [w'0 [Hnorm_vt2w0 [Hnorm_v't2'w'0 Hrel_wft]]]]; auto.
      exists (w0). exists (w'0). repeat(split; auto).
      assert (typ_size (open_tt t X1) < typ_size (typ_all k t)) as G. 
        simpl. rewrite open_tt_typ_size_eq. omega.
      apply H in G. destruct G as [Hrel_wft_wft' Hrel_wft'_wft].
      simpl_env in Hrel_wft_wft'. clear H Hrel_wft'_wft.
      simpl_env.
      rewrite subst_tt_fresh with (T:=X1) (Z:=X) (U:=Y); auto.
      rewrite <- subst_tt_open_tt; auto.  
      apply Hrel_wft_wft' with (t0:=(open_tt t X1)) 
                               (E1:=[(X1, bind_kn k)]++E1)(E2:=E2)(E3:=E3) (K:=K)
                               (rsubst1:=[(X1,R0)]++rsubst1)(rsubst2:=rsubst2)(rsubst3:=rsubst3)
                               (dsubst1:=[(X1,t3)]++dsubst1)(dsubst2:=dsubst2)(dsubst3:=dsubst3)
                               (dsubst1':=[(X1,t2'0)]++dsubst1')(dsubst2':=dsubst2')(dsubst3':=dsubst3')
                               (v:=w0) (v':=w'0)
                               (X:=X) (R:=R) 
                               (t2:=t2) (t2':=t2')
                               ; simpl_env; auto; clear Hrel_wft_wft'.
          eapply odsubst_weaken_head; simpl_env; eauto using wfor_left_inv.
          eapply odsubst_weaken_head; simpl_env; eauto using wfor_right_inv.
          eapply odsubst_weaken_head; simpl_env; eauto using wfor_left_inv.
          eapply odsubst_weaken_head; simpl_env; eauto using wfor_right_inv.
          SSCase "fv".
          destruct_notin.
          simpl in *. auto using notin_fv_tt_open_tt.

  Case "typ_with". (* with *)
  apply F_Related_ovalues_with_leq in Hrel.
  simpl. simpl_env.
  apply F_Related_ovalues_with_req.
  destruct Hrel as [Hv [Hv' [e1 [e2 [e1' [e2' [Heq [Heq' 
                                [[u1 [u1' [Hnorm_e1u1 [Hnorm_e1'u1' Hrel_wft1]]]] 
                                 [u2 [u2' [Hnorm_e2u2 [Hnorm_e2'u2' Hrel_wft2]]]]]
                              ]]]]]]]]; subst.
  repeat(split; auto; simpl_env in * ).
     SCase "with".
     simpl in Hfv.
     exists (e1). exists (e2). exists (e1'). exists (e2'). repeat(split; auto).
       SSCase "with1".
       exists (u1). exists (u1').  repeat(split;auto).
       simpl_env in *.
       assert (typ_size t1 < typ_size (typ_with t1 t3)) as G1. simpl. omega.
       apply H in G1. destruct G1 as [Hrel_wft1_wft1' Hrel_wft1'_wft1].
       simpl in Hfv.
       apply Hrel_wft1_wft1' with (E1:=E1) (E2:=E2) (E3:=E3) (K:=K); auto.
       SSCase "with2".
       exists (u2). exists (u2').  repeat(split; auto).
       assert (typ_size t3 < typ_size (typ_with t1 t3)) as G2. simpl. omega.
       apply H in G2. destruct G2 as [Hrel_wft2_wft2' Hrel_wft2'_wft2].
      simpl in Hfv.
      apply Hrel_wft2_wft2' with (E1:=E1) (E2:=E2) (E3:=E3) (K:=K); auto.

  (* <- *)
  intros t v v' E1 E2 E3 rsubst1 rsubst2 rsubst3 dsubst1 dsubst2 dsubst3 dsubst1' dsubst2' dsubst3' X R t2 t2' Y K Env lEnv
     Htsize Hrel Heqr1 Heqd1 Heqd1' Heqr2 Heqd2 Heqd2' Heqr3 Heqd3 Heqd3' WfR Wfr Wfd Wfd' Wfd0 Wfd0' Hfv.
  (typ_cases (destruct t) Case).

  Case "typ_bvar". (*bvar*)
  apply F_Related_ovalues_bvar_leq in Hrel; auto.

  Case "typ_fvar". (* fvar *)
  apply F_Related_ovalues_fvar_req.
  simpl in Hrel. simpl_env in Hrel.
  destruct (a==X); subst.
    apply F_Related_ovalues_fvar_leq in Hrel.
    unfold In_rel in Hrel.  
    destruct Hrel as [R0 [Hb [Hv [Hv' [Hadm Hr]]]]]; subst.
    exists R.
    repeat(split; auto).
      apply wf_rho_subst__uniq in Wfr.
      decompose [and] Wfr.
      destruct_notin.
      apply dom__ddom in Hfv.
      rewrite Heqr1 in Hfv.
      apply dom__ddom in NotInTac.
      rewrite Heqr2 in NotInTac.
      apply dom__ddom in NotInTac0.
      rewrite Heqr3 in NotInTac0.
      analyze_binds_uniq Hb.

      apply wf_rho_subst__uniq in Wfr.
      decompose [and] Wfr.
      destruct_notin.
      apply dom__ddom in Hfv.
      rewrite Heqr1 in Hfv.
      apply dom__ddom in NotInTac.
      rewrite Heqr2 in NotInTac.
      apply dom__ddom in NotInTac0.
      rewrite Heqr3 in NotInTac0.
      analyze_binds_uniq Hb.

    apply F_Related_ovalues_fvar_leq in Hrel.
    unfold In_rel in Hrel.  
    destruct Hrel as [R0 [Hb [Hv [Hv' [Hadm Hr]]]]]; subst.
    apply wf_rho_subst__uniq in Wfr.
    decompose [and] Wfr.
    destruct_notin.
    apply dom__ddom in Hfv.
    rewrite Heqr1 in Hfv.
    apply dom__ddom in NotInTac.
    rewrite Heqr2 in NotInTac.
    apply dom__ddom in NotInTac0.
    rewrite Heqr3 in NotInTac0.
    analyze_binds_uniq Hb.
      exists R0.
      repeat(split; auto).

      simpl. auto.

      exists (R0).
      repeat(split; auto).

      exists (R0).
      repeat(split; auto).

  Case "typ_arrow". (* arrow *)
  simpl in Hrel. simpl_env in Hrel.
  apply F_Related_ovalues_arrow_leq in Hrel.
  apply F_Related_ovalues_arrow_req.
  destruct Hrel as [Hv [Hv' [L Harrow]]]; subst.
  repeat(split; simpl_env in *; auto).
     SCase "arrow".
     exists (L `union` {{Y}}).
     intros lEnv1 x x' Htypingx Htypingx' Wfle Disj Harrow'.
     rename Harrow' into Hrel_wft1.
 
     assert (typ_size t1 < typ_size (typ_arrow k t1 t3)) as G1. simpl. omega.
     apply H in G1. destruct G1 as [Hrel_wft1_wft1' Hrel_wft1'_wft1].
     simpl in Hfv.
     assert (Y `notin` dom lEnv1).
       apply disjdom_one_1.
       apply disjdom_app_2 in Disj; auto.
     apply Hrel_wft1_wft1' with (X:=X)(Y:=Y)(R:=R)(t2:=t2)(t2':=t2')(E1:=E1)(E2:=E2)(E3:=E3)(K:=K) in Hrel_wft1; auto; simpl_env.
       SSCase "arrow".
       destruct (@Harrow lEnv1 x x') as [u [u' [Hnorm_vxu [Hnorm_v'x'u' Hrel_wft1']]]]; auto.
         assert (ddom_env (E2++E3) [=] dom (dsubst2++dsubst3)) as EQ1.
           simpl_env. rewrite Heqd2. rewrite Heqd3. 
           clear. fsetdec.
         assert (wf_typ Env t2 K) as Wft2.
           apply wfor_left_inv in WfR; auto.
         rewrite delta_osubst_opt with (E:=E2++E3) (E':=E1) (K:=K) (Env:=Env); auto.
         assert (ddom_env (E1++E2) [=] dom (dsubst1++dsubst2)) as EQ2.
           simpl_env. rewrite Heqd1. rewrite Heqd2. 
           clear. fsetdec.
         rewrite_env ((dsubst1++dsubst2)++[(X, t2)]++dsubst3) in Htypingx.
         rewrite_env ((dsubst1++dsubst2)++[(X, t2)]++dsubst3) in Wfd.
         rewrite_env ((E1++E2)++[(X, bind_kn K)]++E3) in Wfd.
         assert (X `notin` dom (E1++E2) `union` dom E3 `union` dom Env) as Xn.
           apply wf_rho_subst__uniq in Wfr.
           decompose [and] Wfr.
           apply disjoint_delta_osubst in Wfd.
           decompose [and] Wfd.
           clear - H3 H2.
           simpl_env. solve_uniq.
         rewrite delta_osubst_opt with (E:=E3) (E':=E1++E2) (K:=K) (Env:=Env) in Htypingx; auto.
           simpl_env  in Htypingx.
           rewrite subst_tt_tt' with (K:=K) (Env:=Env); auto.

         assert (ddom_env (E2++E3) [=] dom (dsubst2'++dsubst3')) as EQ1.
           simpl_env. rewrite Heqd2'. rewrite Heqd3'. 
           clear. fsetdec.
         assert (wf_typ Env t2' K) as Wft2'.
           apply wfor_right_inv in WfR; auto.
         rewrite delta_osubst_opt with (E:=E2++E3) (E':=E1) (K:=K) (Env:=Env); auto.
         assert (ddom_env (E1++E2) [=] dom (dsubst1'++dsubst2')) as EQ2.
           simpl_env. rewrite Heqd1'. rewrite Heqd2'. 
           clear. fsetdec.
         rewrite_env ((dsubst1'++dsubst2')++[(X, t2')]++dsubst3') in Htypingx'.
         rewrite_env ((dsubst1'++dsubst2')++[(X, t2')]++dsubst3') in Wfd'.
         rewrite_env ((E1++E2)++[(X, bind_kn K)]++E3) in Wfd'.
         assert (X `notin` dom (E1++E2) `union` dom E3 `union` dom Env) as Xn.
           apply wf_rho_subst__uniq in Wfr.
           decompose [and] Wfr.
           apply disjoint_delta_osubst in Wfd.
           decompose [and] Wfd.
           clear - H3 H2.
           simpl_env. solve_uniq.
         rewrite delta_osubst_opt with (E:=E3) (E':=E1++E2) (K:=K) (Env:=Env) in Htypingx'; auto.
           simpl_env  in Htypingx'.
           rewrite subst_tt_tt' with (K:=K) (Env:=Env); auto.

         apply disjdom_app_1 in Disj. auto.

       exists (u). exists (u'). repeat(split; auto).
       assert (typ_size t3 < typ_size (typ_arrow k t1 t3)) as G2. simpl. omega.
       apply H in G2. destruct G2 as [Hrel_wft2_wft2' Hrel_wft2'_wft2].
       simpl in Hfv.
       apply Hrel_wft2'_wft2 with (X:=X)(Y:=Y)(R:=R)(t2:=t2)(t2':=t2')(E1:=E1)(E2:=E2)(E3:=E3)(K:=K); auto.

  Case "typ_all". (* all *)
  simpl in Hrel. simpl_env in Hrel.
  apply F_Related_ovalues_all_leq in Hrel.
  apply F_Related_ovalues_all_req.
  destruct Hrel as [Hv [Hv' [L' Hall]]]; subst.
  repeat(split; auto; simpl_env in *).
     SCase "all".
      exists (L' `union` singleton X `union` singleton Y `union` dom E1 `union` dom E2 `union` dom E3 `union` fv_tt (subst_tt X Y t) `union` dom Env `union` dom lEnv).
      intros X1 t3 t2'0 R0 Fr Hwfr' Hfv'.
      assert (X1 `notin` L') as Fr''. auto.
      destruct (@Hall X1 t3 t2'0 R0 Fr'') as [w0 [w'0 [Hnorm_vt2w0 [Hnorm_v't2'w'0 Hrel_wft]]]]; auto.
          destruct_notin. simpl_env. simpl. auto.
      exists (w0). exists (w'0). repeat(split; auto).
      assert (typ_size (open_tt t X1) < typ_size (typ_all k t)) as G. 
        simpl. rewrite open_tt_typ_size_eq. omega.
      apply H in G. destruct G as [Hrel_wft_wft' Hrel_wft'_wft].
      simpl_env in Hrel_wft'_wft. clear H Hrel_wft_wft'.
      simpl_env. simpl_env in Hrel_wft.
      rewrite subst_tt_fresh with (T:=X1) (Z:=X) (U:=Y) in Hrel_wft; auto.
      rewrite <- subst_tt_open_tt in Hrel_wft; auto.  
      apply Hrel_wft'_wft with (t0:=(open_tt t X1)) 
                               (E1:=[(X1, bind_kn k)]++E1)(E2:=E2)(E3:=E3) (K:=K)
                               (rsubst1:=[(X1,R0)]++rsubst1)(rsubst2:=rsubst2)(rsubst3:=rsubst3)
                               (dsubst1:=[(X1,t3)]++dsubst1)(dsubst2:=dsubst2)(dsubst3:=dsubst3)
                               (dsubst1':=[(X1,t2'0)]++dsubst1')(dsubst2':=dsubst2')(dsubst3':=dsubst3')
                               (v:=w0) (v':=w'0)
                               (X:=X) (R:=R) (Y:=Y)
                               (t2:=t2) (t2':=t2')
                               ; simpl_env; auto; clear Hrel_wft'_wft.
          eapply odsubst_weaken_head; simpl_env; eauto using wfor_left_inv.
          eapply odsubst_weaken_head; simpl_env; eauto using wfor_right_inv.
          eapply odsubst_weaken_head; simpl_env; eauto using wfor_left_inv.
          eapply odsubst_weaken_head; simpl_env; eauto using wfor_right_inv.
          SSCase "fv".
          destruct_notin. simpl in NotInTac5. simpl.
          auto using notin_fv_tt_open_tt.

  Case "typ_with". (* with *)
  simpl in Hrel. simpl_env in Hrel.
  apply F_Related_ovalues_with_leq in Hrel.
  apply F_Related_ovalues_with_req.
  destruct Hrel as [Hv [Hv' [e1 [e2 [e1' [e2' [Heq [Heq' 
                                [[u1 [u1' [Hnorm_e1u1 [Hnorm_e1'u1' Hrel_wft1]]]] 
                                 [u2 [u2' [Hnorm_e2u2 [Hnorm_e2'u2' Hrel_wft2]]]]]
                              ]]]]]]]]; subst.
  repeat(split; auto; simpl_env in *).
     SCase "with".
     simpl in Hfv.
     exists (e1). exists (e2). exists (e1'). exists (e2'). repeat(split; auto).
       SSCase "with1".
       exists (u1). exists (u1'). repeat(split; auto).
       simpl_env in *.
       assert (typ_size t1 < typ_size (typ_with t1 t3)) as G1. simpl. omega.
       apply H in G1. destruct G1 as [Hrel_wft1_wft1' Hrel_wft1'_wft1].
       simpl in Hfv.
       eapply Hrel_wft1'_wft1; eauto.
       SSCase "with2".
       exists (u2). exists (u2'). repeat(split; auto).
       assert (typ_size t3 < typ_size (typ_with t1 t3)) as G2. simpl. omega.
       apply H in G2. destruct G2 as [Hrel_wft2_wft2' Hrel_wft2'_wft2].
       simpl in Hfv.
       eapply Hrel_wft2'_wft2; eauto.
Qed.

Lemma Forel_typ_permute_renaming_one': forall t v v' E1 E2 E3 rsubst1 rsubst2 rsubst3 dsubst1 dsubst2 dsubst3 dsubst1' dsubst2' dsubst3' X R t2 t2' Y K Env lEnv,
  F_Related_ovalues t (rsubst1++rsubst2++[(X, R)]++rsubst3) (dsubst1++dsubst2++[(X, t2)]++dsubst3) (dsubst1'++dsubst2'++[(X, t2')]++dsubst3') v v' Env lEnv ->
  ddom_env E1 [=] dom rsubst1 ->
  ddom_env E1 [=] dom dsubst1 ->
  ddom_env E1 [=] dom dsubst1' ->
  ddom_env E2 [=] dom rsubst2 ->
  ddom_env E2 [=] dom dsubst2 ->
  ddom_env E2 [=] dom dsubst2' ->
  ddom_env E3 [=] dom rsubst3 ->
  ddom_env E3 [=] dom dsubst3 ->
  ddom_env E3 [=] dom dsubst3' ->
  wfor Env R t2 t2' K ->
  wf_rho_subst (E1++E2++[(X, bind_kn K)]++E3) (rsubst1++rsubst2++[(X, R)]++rsubst3) ->
  wf_delta_osubst (E1++E2++[(X, bind_kn K)]++E3) (dsubst1++dsubst2++[(X, t2)]++dsubst3) Env ->
  wf_delta_osubst (E1++E2++[(X, bind_kn K)]++E3) (dsubst1'++dsubst2'++[(X, t2')]++dsubst3') Env ->
  wf_delta_osubst (E1++[(Y, bind_kn K)]++E2++E3) (dsubst1++[(Y, t2)]++dsubst2++dsubst3) Env ->
  wf_delta_osubst (E1++[(Y, bind_kn K)]++E2++E3) (dsubst1'++[(Y, t2')]++dsubst2'++dsubst3') Env ->
  Y `notin` (dom E1 `union` dom E2 `union` dom E3 `union` (fv_tt t) `union` dom Env `union` dom lEnv)->
  F_Related_ovalues (subst_tt X Y t) (rsubst1++[(Y, R)]++rsubst2++rsubst3) (dsubst1++[(Y, t2)]++dsubst2++dsubst3) (dsubst1'++[(Y, t2')]++dsubst2'++dsubst3') v v' Env lEnv
  .
Proof.
  intros.
  assert (P_Forel_typ_permute_renaming_one (typ_size t)) as J.
    apply (@_Forel_typ_permute_renaming_one (typ_size t)).
  unfold P_Forel_typ_permute_renaming_one in J.
  destruct J. eauto.
Qed.

Lemma Forel_typ_permute_renaming_one: forall t v v' E1 E2 rsubst1 rsubst2 dsubst1 dsubst2 dsubst1' dsubst2' X R t2 t2' Y K Env lEnv,
  F_Related_ovalues t (rsubst1++[(X, R)]++rsubst2) (dsubst1++[(X, t2)]++dsubst2) (dsubst1'++[(X, t2')]++dsubst2') v v' Env lEnv ->
  ddom_env E1 [=] dom rsubst1 ->
  ddom_env E1 [=] dom dsubst1 ->
  ddom_env E1 [=] dom dsubst1' ->
  ddom_env E2 [=] dom rsubst2 ->
  ddom_env E2 [=] dom dsubst2 ->
  ddom_env E2 [=] dom dsubst2' ->
  wfor Env R t2 t2' K ->
  wf_rho_subst (E1++[(X, bind_kn K)]++E2) (rsubst1++[(X, R)]++rsubst2) ->
  wf_delta_osubst (E1++[(X, bind_kn K)]++E2) (dsubst1++[(X, t2)]++dsubst2) Env ->
  wf_delta_osubst (E1++[(X, bind_kn K)]++E2) (dsubst1'++[(X, t2')]++dsubst2') Env ->
  wf_delta_osubst ([(Y, bind_kn K)]++E1++E2) ([(Y, t2)]++dsubst1++dsubst2) Env ->
  wf_delta_osubst ([(Y, bind_kn K)]++E1++E2) ([(Y, t2')]++dsubst1'++dsubst2') Env ->
  Y `notin` (dom E1 `union` dom E2 `union` (fv_tt t) `union` dom Env `union` dom lEnv)->
  F_Related_ovalues (subst_tt X Y t) ([(Y, R)]++rsubst1++rsubst2) ([(Y, t2)]++dsubst1++dsubst2) ([(Y, t2')]++dsubst1'++dsubst2') v v' Env lEnv
  .
Proof.
  intros.
  rewrite_env (nil++[(Y, R)]++rsubst1++rsubst2).
  rewrite_env (nil++[(Y, t2)]++dsubst1++dsubst2).
  rewrite_env (nil++[(Y, t2')]++dsubst1'++dsubst2').
  apply Forel_typ_permute_renaming_one' with (E1:=nil) (E2:=E1) (E3:=E2) (K:=K); auto.
Qed.

Lemma disjdom_fv_lenv_wfle : forall L Env lEnv,
  wf_lenv Env lEnv ->
  disjdom L (dom Env) ->
  disjdom L (dom lEnv) ->
  disjdom L (fv_lenv lEnv).
Proof.
  intros L Env lEnv Wfle Disj1 Disj2.
  split; intros x xn.
    destruct Disj1 as [J1 J2].
    destruct Disj2 as [J3 J4].
    assert (xn':=xn).
    apply J1 in xn.
    apply J3 in xn'.
    apply notin_fv_lenv_wfle with (X:=x) in Wfle; auto.

    destruct Disj1 as [J1 J2].
    destruct Disj2 as [J3 J4].
    intro J.
    assert (xn':=J).
    apply J1 in J.
    apply J3 in xn'.
    apply notin_fv_lenv_wfle with (X:=x) in Wfle; auto.
Qed.

Lemma typing_fv_te_upper : forall E lE e t,
  typing E lE e t ->
  fv_te e [<=] dom E.
Proof.
  intros E lE e t Typing.
  (typing_cases (induction Typing) Case); intros; subst; simpl.
  Case "typing_var".
    apply binds_In in H0.
    fsetdec.
  Case "typing_lvar".
    fsetdec.
  Case "typing_abs".
    pick fresh x.
    assert (x `notin` L) as xnL. auto.
    apply H1 in xnL.
    assert (J:=@fv_te_open_ee_eq e1 x).
    rewrite J in xnL.
    assert (J':=@wft_fv_tt_sub E T1 kn_nonlin H).
    destruct_notin.
    clear - J' xnL NotInTac. simpl in xnL. fsetdec.
  Case "typing_labs".
    pick fresh x.
    assert (x `notin` L) as xnL. auto.
    apply H1 in xnL.
    assert (J:=@fv_te_open_ee_eq e1 x).
    rewrite J in xnL.
    assert (J':=@wft_fv_tt_sub E T1 kn_lin H).
    clear - J' xnL. fsetdec.
  Case "typing_app".
    fsetdec.
  Case "typing_tabs".
    pick fresh X.
    assert (X `notin` L) as XnL. auto.
    apply H1 in XnL.
    assert (J:=@open_te_fv_te_lower e1 X).
    simpl in XnL.
    assert (fv_te e1 [<=] add X (dom E)) as JJ.
      clear - XnL J. fsetdec.
    destruct_notin.
    clear - JJ NotInTac.
    fsetdec.
  Case "typing_tapp".
    assert (J':=@wft_fv_tt_sub E T K H).
     fsetdec.
  Case "typing_apair". fsetdec.
  Case "typing_fst". auto.
  Case "typing_snd". auto.
Qed.

Lemma wf_lgamma_osubst__empty_lctx : forall E dsubst gsubst lgsubst Env lEnv,
  wf_lgamma_osubst E nil dsubst gsubst lgsubst Env lEnv ->
  lEnv = nil /\ lgsubst = nil.
Proof.
  intros E dsubst gsubst lgsubst Env lEnv Hwflg.
  remember lempty as lE.
  induction Hwflg; simpl; auto.
    inversion HeqlE.
Qed.

Lemma wf_olgsubst_cons_inv : forall E x T D dsubst gsubst lgsubst Env lEnv,
  wf_lgamma_osubst ([(x, bind_typ T)]++E) D dsubst gsubst lgsubst Env lEnv ->
  exists e, exists gsubst', 
    gsubst = [(x, e)] ++ gsubst' /\
    gdom_env E [=] dom gsubst' /\
    wf_typ E T kn_nonlin /\
    typing  Env nil e (apply_delta_subst_typ dsubst T) /\
    wf_lgamma_osubst E D dsubst gsubst' lgsubst Env lEnv.
Proof.
  intros E x T D dsubst gsubst lgsubst Env lEnv Wflg.
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
      apply dom_lgamma_osubst in Wflg.
      decompose [and] Wflg; auto.

    assert ([(x0, bind_typ T0)]++E0=[(x0, bind_typ T0)]++E0) as EQ. auto.
    apply IHWflg in EQ.
    destruct EQ as [e0 [gsubst' [EQ1 [EQ2 [Wft [Typ Wflg']]]]]]; subst.
    exists e0. exists gsubst'.
    split; auto.
    split; auto.
    split; auto.
    split; auto.
      apply wf_lgamma_osubst_slval; auto.
        destruct H0 as [J1 J2].
        split; auto.
          clear - J1. solve_uniq.
 
        rewrite_env (nil ++ [(x0, bind_typ T0)] ++ E0) in H3.
        apply wf_typ_strengthening in H3; auto.
        apply wf_lgamma_osubst__wf_lenv in Wflg.
        destruct Wflg; auto.        

    inversion HeqEE.
Qed.

Lemma wf_olgsubst_kcons_inv : forall E X K D dsubst gsubst lgsubst Env lEnv,
  wf_lgamma_osubst ([(X, bind_kn K)]++E) D dsubst gsubst lgsubst Env lEnv ->
  X `notin` fv_lenv D ->
  exists T, exists dsubst', 
    dsubst = [(X, T)] ++ dsubst' /\
    ddom_env E [=] dom dsubst' /\
    wf_typ Env T K /\
    wf_lgamma_osubst E D dsubst' gsubst lgsubst Env lEnv.
Proof.
  intros E X K D dsubst gsubst lgsubst Env lEnv Wflg XnD.
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
      apply wf_lgamma_osubst_slval; auto.
        destruct H0 as [J1 J2].
        split; auto.
          clear - J1. solve_uniq.
 
        simpl in H2.
        simpl_env in XnD.
        simpl in XnD.
        rewrite <- subst_tt_fresh in H2; auto.
        
        rewrite_env (nil ++ [(X, bind_kn K)] ++E0) in H3.
        simpl_env in XnD.
        simpl in XnD.
        apply wf_typ_strengthening_typ in H3; auto.

        simpl_env in XnD. auto.

    inversion HeqEE; subst.
    exists T. exists dsE.
    split; auto.
    split; auto.
      apply dom_lgamma_osubst in Wflg.
      destruct Wflg as [J1 [J2 J3]]. assumption.
Qed.

Lemma lgamma_osubst_opt :  forall E D D' dsubst x t gsubst lgsubst lgsubst' v e Env lEnv' lEnv0 lEnv,
   wf_lgamma_osubst E (D'++[(x, lbind_typ t)]++D) dsubst gsubst (lgsubst'++[(x, v)]++lgsubst) Env (lEnv'++lEnv0++lEnv)->
   wf_lgamma_osubst E D dsubst gsubst lgsubst Env lEnv->
   wf_lgamma_osubst E D' dsubst gsubst lgsubst' Env lEnv'->
   typing Env lEnv0 v (apply_delta_subst_typ dsubst t) ->
   apply_gamma_subst (lgsubst'++[(x, v)]++lgsubst) e =
    apply_gamma_subst (lgsubst'++lgsubst) (subst_ee x v e).
Proof.
  intros E D D' dsubst x t gsubst lgsubst lgsubst' v e Env lEnv' lEnv0 lEnv
    Hwf_lgamma_osubst Hwflg Hwflg' Typ.
  remember (D'++[(x, lbind_typ t)]++D) as G.
  remember (lgsubst'++[(x, v)]++lgsubst) as Gsubst.
  remember (lEnv'++lEnv0++lEnv) as lE.
  generalize dependent e.
  generalize dependent lgsubst'.
  generalize dependent D'.
  generalize dependent lEnv'.
  generalize dependent lEnv0.
  generalize dependent lEnv.
  (wf_lgamma_osubst_cases (induction Hwf_lgamma_osubst) Case); intros; subst.
  Case "wf_lgamma_osubst_empty".
    contradict HeqG; auto.    
  Case "wf_lgamma_osubst_sval".
    apply IHHwf_lgamma_osubst with (D'0:=D') (lgsubst'0:=lgsubst') (lEnv:=lEnv0) (lEnv2:=lEnv1) (lEnv'0:=lEnv'); auto.
      assert (J:=Hwflg).
      apply wf_olgsubst_cons_inv in J.      
      destruct J as [v0 [gsubst' [EQ1 [EQ2 [WftT [Typingv0 J]]]]]].
      inversion EQ1; subst; auto.
      
      assert (J:=Hwflg').
      apply wf_olgsubst_cons_inv in J.      
      destruct J as [v0 [gsubst' [EQ1 [EQ2 [WftT [Typingv0 J]]]]]].
      inversion EQ1; subst; auto.
  Case "wf_lgamma_osubst_slval".
    destruct (one_eq_app _ _ _ _ _ HeqG) as [[D'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
    SCase "exists D'', D'=D&X0'' /\ D0=D&X&D'' ".
      destruct (one_eq_app _ _ _ _ _ HeqGsubst) as [[lgsubst'' [GEQ1 GEQ2]] | [GEQ1 GEQ2]]; subst.
      SSCase "exists GS'',GS'=GS&X0'' /\ GS0=GS&X&GS'' ".
        simpl. simpl_env. 
        rewrite <- subst_ee_commute; auto.
           assert (J:=Hwflg'). simpl_env in J.
           apply wf_olgsubst_lcons_inv in J.      
           destruct J as [v0 [lgsubst' [lEnv3 [lEnv4 [EQ1 [EQ2 [WftT [EQ3 [Typingv0 J]]]]]]]]]; subst.
           inversion EQ1; subst.
           assert (length lEnv3 = length lEnv2) as EQ.
             clear - Typingv0 H2.
             assert (dom lEnv3 [=] dom lEnv2) as JJ.
               apply typing_ldom in Typingv0.
               apply typing_ldom in H2.
               rewrite <- H2.
               rewrite <- Typingv0.
               clear. fsetdec.
             apply domeq_lengtheq; auto.
                apply typing_regular in Typingv0.
                decompose [and] Typingv0; eauto.

                apply typing_regular in H2.
                decompose [and] H2; eauto.
           simpl_env in HeqlE.
           assert (EQ':=HeqlE).
           apply app_lengtheq_inv_head in EQ'; auto.
           subst.
           apply app_inv_tail in HeqlE; subst.
           apply IHHwf_lgamma_osubst with (D':=D'') (lgsubst'0:=lgsubst') (lEnv1:=lEnv) (lEnv2:=lEnv0) (lEnv':=lEnv4); auto.

          clear - Typ H2 H HeqlE.
          apply notin_fv_ee_typing with (y:=x0) in H2; auto.
          assert (x0 `notin` dom (lEnv'++lEnv0++lEnv)) as x0n.
            rewrite <- HeqlE.
            simpl_env. auto.
          simpl_env in x0n.
          apply notin_fv_ee_typing with (y:=x0) in Typ; auto.
         
          clear - Typ H2 H0 HeqlE Hwf_lgamma_osubst.
          assert (x `notin` dom Env) as xn1.
            apply disjoint_lgamma_osubst in Hwf_lgamma_osubst.
            decompose [and] Hwf_lgamma_osubst.
            clear - H5. solve_uniq.
          assert (x `notin` dom lEnv1) as xn2.
            apply disjoint_lgamma_osubst in Hwf_lgamma_osubst.
            decompose [and] Hwf_lgamma_osubst.
            clear - H7. solve_uniq.
          assert (x `notin` dom lEnv2) as xn3.
            decompose [and] H0.
            clear - H1. solve_uniq.
          assert (x `notin` dom (lEnv'++lEnv0++lEnv)) as xn4.
            rewrite <- HeqlE.
            simpl_env. auto.
          simpl_env in xn4.
          apply notin_fv_ee_typing with (y:=x) in H2; auto.
          apply notin_fv_ee_typing with (y:=x) in Typ; auto.
      SSCase "GS'=nil /\ GS&X = GS0&X0 ".
        inversion GEQ2. subst.
        simpl_env in *. destruct_notin.
        auto.
    SCase "E'=nil /\ E&X = E0&X0 ".
      inversion EQ2; subst.
      destruct (one_eq_app _ _ _ _ _ HeqGsubst) as [[lgsubst'' [GEQ1 GEQ2]] | [GEQ1 GEQ2]]; subst.
      SSCase "exists GS'',GS'=GS&X0'' /\ GS0=GS&X&GS'' ".
        apply dom_lgamma_osubst in Hwflg'.
        decompose [and] Hwflg'.
        simpl_env in H7.
        assert (x0 `notin` (singleton x0 `union` dom lgsubst'') -> False) as J.
            intro. destruct_notin. apply NotInTac0; auto.
        rewrite <- H7 in J.
        contradict J; auto.
     SSCase "GS'=nil /\ GS&X = GS0&X0 ".
        inversion GEQ2; subst; auto.
  Case "wf_lgamma_osubst_skind".
    apply IHHwf_lgamma_osubst with (D'0:=D') (lgsubst'0:=lgsubst') (lEnv:=lEnv0) (lEnv2:=lEnv1) (lEnv'0:=lEnv'); auto.
      assert (J:=Hwflg).
      apply wf_olgsubst_kcons_inv in J.      
      destruct J as [T0 [dsubst' [EQ1 [EQ2 [WftT J]]]]].
      inversion EQ1; subst; auto.
      apply notin_fv_lenv_wfle with (E:=E); auto.
        apply wf_lgamma_osubst__wf_lenv in Hwf_lgamma_osubst.
        destruct Hwf_lgamma_osubst as [J1 [J2 [J3 J4]]].
        rewrite_env (nil ++ (D'++[(x, lbind_typ t)]) ++ D) in J2.
        apply wf_lenv_lin_strengthening' in J2; auto.
      
      simpl in Typ.
      apply wf_lgamma_osubst__wf_lenv in Hwf_lgamma_osubst.
      destruct Hwf_lgamma_osubst as [J1 [J2 [J3 J4]]].
      apply notin_fv_lenv_wfle with (X:=X) in J2; auto.
      simpl_env in J2. simpl in J2.
      rewrite <- subst_tt_fresh in Typ; auto.

      assert (J:=Hwflg').
      apply wf_olgsubst_kcons_inv in J.      
      destruct J as [T0 [dsubst' [EQ1 [EQ2 [WftT J]]]]].
      inversion EQ1; subst; auto.
      apply notin_fv_lenv_wfle with (E:=E); auto.
        apply wf_lgamma_osubst__wf_lenv in Hwf_lgamma_osubst.
        destruct Hwf_lgamma_osubst as [J1 [J2 [J3 J4]]].
        rewrite_env (D'++([(x, lbind_typ t)] ++ D)++nil) in J2.
        apply wf_lenv_lin_strengthening' in J2; simpl_env in J2; auto. 
Qed.

Lemma F_Related_osubst_without_lin : forall E D dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
  F_Related_osubst E D gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
  F_Related_osubst E nil gsubst gsubst' nil nil rsubst dsubst dsubst' Env nil.
Proof.
  intros E D dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv Hrel_subst.
  induction Hrel_subst; intros; auto.
Qed.

Lemma F_Related_olgsubst_lapp_inv : forall E D1 D2 dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv,
  F_Related_osubst E (D1++D2) gsubst gsubst' lgsubst lgsubst' rsubst dsubst dsubst' Env lEnv ->
  exists lgsubst1, exists lgsubst2,
  exists lgsubst1', exists lgsubst2',
  exists lEnv1, exists lEnv2,
    lgsubst = lgsubst1 ++ lgsubst2 /\
    lgsubst' = lgsubst1' ++ lgsubst2' /\
    dom D1 [=] dom lgsubst1 /\
    dom D2 [=] dom lgsubst2 /\
    dom D1 [=] dom lgsubst1' /\
    dom D2 [=] dom lgsubst2' /\
    lEnv = lEnv1 ++ lEnv2 /\
    F_Related_osubst E D1 gsubst gsubst' lgsubst1 lgsubst1' rsubst dsubst dsubst' Env lEnv1 /\
    F_Related_osubst E D2 gsubst gsubst' lgsubst2 lgsubst2' rsubst dsubst dsubst' Env lEnv2.
Proof.
Proof.
  intros E D1 D2 dsubst dsubst' gsubst gsubst' lgsubst lgsubst' rsubst Env lEnv Hrel_subst.
  remember (D1++D2) as DD.
  generalize dependent D1.        
  induction Hrel_subst; intros; subst.
    symmetry in HeqDD.
    apply app_eq_nil in HeqDD.
    destruct HeqDD as [EQ1 EQ2]; subst.
    exists nil. exists nil. exists nil. exists nil. exists nil. exists nil.
    repeat(split; auto).

    assert (D1++D2=D1++D2) as EQ. auto.
    apply IHHrel_subst in EQ.
    destruct EQ as [lgsubst1 [lgsubst2 [lgsubst1' [lgsubst2' [lEnv1 [lEnv2 [EQ1 [EQ2 [EQ3 [EQ4 [EQ5 [EQ6 [EQ7 [Hrel_Sub1 Hrel_Sub2]]]]]]]]]]]]]]; subst.
    exists lgsubst1. exists lgsubst2. exists lgsubst1'. exists lgsubst2'. exists lEnv1. exists lEnv2.
    simpl_env.
    split; auto.
    split; auto.
    split; auto.
    split; auto.
    split; auto.
    split; auto.
    split; auto.
    split.
      simpl_env in H.
      apply F_Related_osubst_kind; auto.

      simpl_env in H.
      apply F_Related_osubst_kind; auto.

    assert (D1++D2=D1++D2) as EQ. auto.
    apply IHHrel_subst in EQ.
    destruct EQ as [lgsubst1 [lgsubst2 [lgsubst1' [lgsubst2' [lEnv1 [lEnv2 [EQ1 [EQ2 [EQ3 [EQ4 [EQ5 [EQ6 [EQ7 [Hrel_Sub1 Hrel_Sub2]]]]]]]]]]]]]]; subst.
    exists lgsubst1. exists lgsubst2. exists lgsubst1'. exists lgsubst2'. exists lEnv1. exists lEnv2.
    simpl_env.
    split; auto.
    split; auto.
    split; auto.
    split; auto.
    split; auto.
    split; auto.
    split; auto.
    split.
      simpl_env in H2.
      apply F_Related_osubst_typ; auto.

      simpl_env in H2.
      apply F_Related_osubst_typ; auto.

    simpl_env in HeqDD.
    apply one_eq_app in HeqDD.
    destruct HeqDD as [[D1' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      assert (D1'++D2=D1'++D2) as EQ. auto.
      apply IHHrel_subst in EQ.
      destruct EQ as [lgsubst1 [lgsubst2 [lgsubst1' [lgsubst2' [lEnv3 [lEnv4 [EQ1 [EQ2 [EQ3 [EQ4 [EQ5 [EQ6 [EQ7 [Hrel_Sub1 Hrel_Sub2]]]]]]]]]]]]]]; subst.
      exists ([(x,v)]++lgsubst1). exists lgsubst2. exists ([(x,v')]++lgsubst1'). exists lgsubst2'. exists (lEnv2++lEnv3). exists lEnv4.
      simpl_env.
      split; auto.
      split; auto.
      split; auto.
      split; auto.
      split; auto.
      split; auto.
      split; auto.
      split; auto.
        simpl_env in H4.
        apply F_Related_osubst_ltyp; auto.
          destruct H1 as [J1 J2].
          split; auto.
             clear - J2. solve_uniq.

          rewrite_env ((lEnv2++lEnv3)++lEnv4++nil) in H2.
          apply wf_lenv_lin_strengthening' in H2.
          simpl_env in H2. assumption.

      exists nil. exists ([(x,v)]++lgsubst). exists nil. exists ([(x,v')]++lgsubst'). exists nil. exists (lEnv2++lEnv1).
      simpl_env.
      split; auto.
      split; auto.
      split; auto.
      split.
        apply F_Related_osubst__inversion in Hrel_subst.
        decompose [prod] Hrel_subst.
        apply dom_lgamma_osubst in b5.
        decompose [and] b5.
         rewrite <- H9. clear. fsetdec.
      split; auto.
      split.
        apply F_Related_osubst__inversion in Hrel_subst.
        decompose [prod] Hrel_subst.
        apply dom_lgamma_osubst in b4.
        decompose [and] b4.
         rewrite <- H9. clear. fsetdec.
      split; auto.
      split; auto.
        apply F_Related_osubst_without_lin in Hrel_subst; auto.

        simpl_env in H4.
        apply F_Related_osubst_ltyp; auto.
Qed.

Lemma F_Related_osubst_lgweaken : forall D1 E D2 gsubst gsubst' lgsubst1 lgsubst2 lgsubst1' lgsubst2' rsubst dsubst dsubst' x T e e' Env lEnv1 lEnv2 lEnv,
  F_Related_osubst E (D1++D2) gsubst gsubst' (lgsubst1++lgsubst2) (lgsubst1'++lgsubst2') rsubst dsubst dsubst' Env (lEnv1++lEnv2) ->
  dom D1 [=] dom lgsubst1 ->
  dom D1 [=] dom lgsubst1' ->
  dom D2 [=] dom lgsubst2 ->
  dom D2 [=] dom lgsubst2' ->
  x `notin` (dom D1 `union` dom D2 `union` dom E `union` fv_env Env `union` fv_lenv lEnv1 `union` fv_lenv lEnv2 `union` dom lEnv)->
  disjoint lEnv E ->
  disjoint lEnv (D1++D2) ->
  wf_lenv Env (lEnv1++lEnv++lEnv2) ->
  wf_lgamma_osubst E D1 dsubst gsubst lgsubst1 Env lEnv1 ->
  wf_lgamma_osubst E D2 dsubst' gsubst' lgsubst2' Env lEnv2 ->
  wf_typ E T kn_lin ->
  typing Env lEnv e (apply_delta_subst_typ dsubst T) ->
  typing Env lEnv e' (apply_delta_subst_typ dsubst' T) ->
  F_Related_ovalues T rsubst dsubst dsubst' e e' Env lEnv ->
  F_Related_osubst E (D1++[(x, lbind_typ T)]++D2) gsubst gsubst' (lgsubst1++[(x, e)]++lgsubst2) (lgsubst1'++[(x, e')]++lgsubst2') rsubst dsubst dsubst' Env (lEnv1++lEnv++lEnv2).
Proof.
  induction D1; intros E D2 gsubst gsubst' lgsubst1 lgsubst2 lgsubst1' lgsubst2' rsubst dsubst dsubst' x T e e' Env lEnv1 lEnv2 lEnv
                Hrel_subst Hdomlg1 Hdomlg1' Hdomlg2 Hdomlg2' Hx Disj1 Disj2 Wfe Hwflg1 Hwflg2 Hwft Htyp Htyp' Hrel.
    simpl in Hdomlg1. symmetry in Hdomlg1.  apply dom_empty_inv in Hdomlg1.
    simpl in Hdomlg1'. symmetry in Hdomlg1'.  apply dom_empty_inv in Hdomlg1'.
    subst.
    apply wf_lgamma_osubst__empty_lctx in Hwflg1.
    destruct Hwflg1 as [J1 J2]; subst.
    simpl_env.
    apply F_Related_osubst_ltyp; auto.
      apply F_Related_osubst__inversion in Hrel_subst.
      decompose [prod] Hrel_subst.
      assert (x `notin` fv_env E) as xnE.
        apply wfe_dom_fv_env; auto.
      assert (x `notin` fv_lenv D2) as xnlE.
        apply notin_fv_lenv_wfle with (E:=E); auto.
          apply wf_lgamma_osubst__wf_lenv in b4.
          destruct b4; auto.
      assert (x `notin` fv_tt T) as xnT.
        apply notin_fv_wf with (X:=x) in Hwft; auto.
      assert (x `notin` fv_lenv lEnv) as xnlEnv.
        apply notin_dom__notin_fv_lenv with (E:=Env); auto.
      auto.
    
    destruct a.
    destruct l.
    assert (J:=Hrel_subst). simpl_env in J.
    apply F_Related_osubst_lcons_inv in J.
    destruct J as [v [lgsubst [v' [lgsubts' [lEnv1' [lEnv2' [EQ1 [EQ2 [EQ3 [EQ4 [Wft [EQ5 [Typ [Typ' [Hrel' Hrel_subst']]]]]]]]]]]]]]]; subst.
    symmetry in EQ1.
    symmetry in EQ2.
    apply one_eq_app in EQ1. destruct EQ1 as [[lgsubst0 [lgEQ1 lgEQ2]] | [lgEQ1 lgEQ2]]; subst.
      apply one_eq_app in EQ2. destruct EQ2 as [[lgsubst0' [lgEQ1' lgEQ2']] | [lgEQ1' lgEQ2']]; subst.
        simpl_env.
        simpl_env in Hrel_subst.
        apply F_Related_osubst__inversion in Hrel_subst.
        decompose [prod] Hrel_subst.
        assert (J:=Hwflg1). simpl_env in J.
        apply wf_olgsubst_lcons_inv in J.      
        destruct J as [v0 [lgsubst' [lEnv3 [lEnv4 [EQ1 [EQ2 [WftT [EQ6 [Typingv0 J]]]]]]]]]; subst.
        inversion EQ1; subst.
        assert (length lEnv3 = length lEnv1') as EQ.
             clear - Typingv0 Typ.
             assert (dom lEnv3 [=] dom lEnv1') as JJ.
               apply typing_ldom in Typingv0.
               apply typing_ldom in Typ.
               rewrite <- Typ.
               rewrite <- Typingv0.
               clear. fsetdec.
            apply domeq_lengtheq; auto.
              apply typing_regular in Typingv0.
              decompose [and] Typingv0; eauto.

              apply typing_regular in Typ.
              decompose [and] Typ; eauto.
         simpl_env in EQ5.
         assert (EQ':=EQ5).
         apply app_lengtheq_inv_head in EQ'; auto.
         subst.
         apply app_inv_tail in EQ5; subst.
         simpl_env.
         apply F_Related_osubst_ltyp; auto.
          simpl_env in Hx.
          apply IHD1; auto.
            apply dom_dom__inv with (x:=a)(b:=lbind_typ t)(b':=v'); auto.
              inversion b1; subst.
              simpl_env in H5. clear - H5. auto.

              apply wf_lgamma_osubst__uniq in b4.
              decompose [and] b4.
              inversion H1; subst.
              simpl_env in H9. clear - H9. auto.

              clear - Disj2.
              solve_uniq.

              clear - Wfe.
              rewrite_env (nil++lEnv1'++(lEnv4++lEnv++lEnv2)) in Wfe.
              apply wf_lenv_lin_strengthening' in Wfe; auto.

          split.
            apply disjoint_lgamma_osubst in b5.
            decompose [and] b5.
            clear - H4. solve_uniq.

            apply disjoint_lgamma_osubst in b5.
            decompose [and] b5.
            clear - H5 Hx.
            assert (x `notin` dom lEnv1') as xn.
              simpl_env in Hx.
              apply free_lenv__free_dom; auto.
            clear Hx.
            solve_uniq.

            clear - Wfe.
            apply wf_lenv_merge.
              rewrite_env (lEnv1'++(lEnv4++lEnv++lEnv2)++nil) in Wfe.
              apply wf_lenv_lin_strengthening' in Wfe; simpl_env in Wfe; auto.

              rewrite_env (nil++lEnv1'++(lEnv4++lEnv++lEnv2)) in Wfe.
              apply wf_lenv_lin_strengthening' in Wfe; auto.

              apply uniq_from_wf_lenv in Wfe.
              solve_uniq.

            assert (a `notin` fv_env E) as anE.
              clear - b5.
              apply wf_lgamma_osubst__wf_lenv in b5.
              decompose [and] b5.
              apply wfe_dom_fv_env; auto.
                inversion H1; subst; auto.
            assert (a `notin` fv_lenv (D1++D2)) as anD.
              clear - b5.
              apply wf_lgamma_osubst__wf_lenv in b5.
              decompose [and] b5.
              inversion H1; subst.
              apply notin_fv_lenv_wfle with (E:=E); auto.
            assert (a `notin` fv_tt T) as xnT.
              apply notin_fv_wf with (X:=a) in Hwft; auto.
            assert (a `notin` fv_tt t) as xnt.
              apply notin_fv_wf with (X:=a) in Wft; auto.
            assert (a `notin` fv_env Env) as anEnv.
              clear - b5.
              assert (J:=b5).
              apply disjoint_lgamma_osubst in J.
              decompose [and] J.               
              apply wf_lgamma_osubst__wf_lenv in b5.
              decompose [and] b5.
              clear - H10 H1.
              apply wfe_dom_fv_env; auto.
                 solve_uniq.
            assert (a `notin` fv_lenv (lEnv4++lEnv++lEnv2)) as anlEnv.
              clear - Wfe b5 Disj2.
              assert (J:=b5).
              apply disjoint_lgamma_osubst in J.
              decompose [and] J.               
              apply wf_lgamma_osubst__wf_lenv in b5.
              decompose [and] b5.
              clear - Wfe H3 H5 Disj2.
              apply notin_fv_lenv_wfle with (E:=Env); auto.
                rewrite_env (nil++lEnv1'++(lEnv4++lEnv++lEnv2)) in Wfe.
                apply wf_lenv_lin_strengthening' in Wfe; auto.

                clear - H3. solve_uniq.

                clear - H5 Disj2. simpl_env. solve_uniq.
            assert (a `notin` fv_lenv lEnv1') as anlEnv'.
              clear - b5.
              assert (J:=b5).
              apply disjoint_lgamma_osubst in J.
              decompose [and] J.               
              apply wf_lgamma_osubst__wf_lenv in b5.
              decompose [and] b5.
              clear - H13 H3 H5.
              apply notin_fv_lenv_wfle with (E:=Env); auto.
                rewrite_env (lEnv1'++(lEnv4++lEnv2)++nil) in H13.
                apply wf_lenv_lin_strengthening' in H13; simpl_env in H13; auto.

                clear - H3. solve_uniq.

                clear - H5. solve_uniq.
            assert (a <> x) as anx.
               clear - Hx.
               simpl_env in Hx. fsetdec.
            clear - anE anD xnt xnT anEnv anlEnv anlEnv' anx.
            simpl_env in *. simpl in *.
            fsetdec.

        simpl_env in Hdomlg1'.
        assert (a `notin` (singleton a `union` dom D1) -> False) as J.
          intro. destruct_notin. contradict NotInTac0; auto.
        rewrite Hdomlg1' in J.
        contradict J; auto.

      simpl_env in Hdomlg1.
      assert (a `notin` (singleton a `union` dom D1) -> False) as J.
        intro. destruct_notin. contradict NotInTac0; auto.
      rewrite Hdomlg1 in J.
      contradict J; auto.
Qed.

Lemma F_Related_osubst_dweaken : forall E1 E2 D gsubst gsubst' lgsubst lgsubst' rsubst1 rsubst2 dsubst1 dsubst2 dsubst1' dsubst2' X t t' R K Env lEnv,
  F_Related_osubst (E1++E2) D gsubst gsubst' lgsubst lgsubst' (rsubst1++rsubst2) (dsubst1++dsubst2) (dsubst1'++dsubst2') Env lEnv ->
  ddom_env E1 [=] dom dsubst1 ->
  ddom_env E1 [=] dom dsubst1' ->
  ddom_env E1 [=] dom rsubst1 ->
  ddom_env E2 [=] dom dsubst2 ->
  ddom_env E2 [=] dom dsubst2' ->
  ddom_env E2 [=] dom rsubst2 ->
  X `notin` (dom E1 `union` dom E2 `union` dom D `union` fv_env Env `union` fv_lenv lEnv)->
  wfor Env R t t' K ->
  F_Related_osubst (E1++[(X, bind_kn K)]++E2) D gsubst gsubst' lgsubst lgsubst' (rsubst1++[(X, R)]++rsubst2) (dsubst1++[(X, t)]++dsubst2) (dsubst1'++[(X, t')]++dsubst2') Env lEnv.
Proof.
  intros E1 E2 D gsubst gsubst' lgsubst lgsubst' rsubst1 rsubst2 dsubst1 dsubst2 dsubst1' dsubst2' X t t' R K Env lEnv
                Hrel_subst Hdomd1 Hdomd1' Hdomr1 Hdomd2 Hdomd2' Hdomr2 HX Hwfr.
  remember (E1++E2) as E.
  remember (rsubst1++rsubst2) as rsubst.
  remember (dsubst1++dsubst2) as dsubst.
  remember (dsubst1'++dsubst2') as dsubst'.
  generalize dependent E1.
  generalize dependent dsubst1.
  generalize dependent dsubst1'.
  generalize dependent rsubst1.  
  (F_Related_osubst_cases (induction Hrel_subst) Case); intros; subst.
  Case "F_Related_osubst_empty".
    symmetry in Heqdsubst.
    apply app_eq_nil in Heqdsubst.
    destruct Heqdsubst; subst.

    symmetry in Heqdsubst'.
    apply app_eq_nil in Heqdsubst'.
    destruct Heqdsubst'; subst.

    symmetry in Heqrsubst.
    apply app_eq_nil in Heqrsubst.
    destruct Heqrsubst; subst.

    symmetry in HeqE.
    apply app_eq_nil in HeqE.
    destruct HeqE; subst.
    rewrite_env ([(X, R)]++nil).
    rewrite_env ([(X, t)]++nil).
    rewrite_env ([(X, t')]++nil).
    apply F_Related_osubst_kind; auto.

  Case "F_Related_osubst_kind".
    simpl_env in *.
    apply one_eq_app in Heqrsubst. destruct Heqrsubst as [[rsubst0 [rEQ1 rEQ2]] | [rEQ1 rEQ2]]; subst.
      apply one_eq_app in Heqdsubst. destruct Heqdsubst as [[dsubst0 [dEQ1 dEQ2]] | [dEQ1 dEQ2]]; subst.
        apply one_eq_app in Heqdsubst'. destruct Heqdsubst' as [[dsubst0' [dEQ1' dEQ2']] | [dEQ1' dEQ2']]; subst.
          apply one_eq_app in HeqE. destruct HeqE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
            simpl_env.
            apply F_Related_osubst_kind; auto.
              apply IHHrel_subst with (rsubst1:=rsubst0) (dsubst1:=dsubst0) (dsubst1':=dsubst0'); auto.
                apply ddom_dom__inv with (X:=X0)(b:=t0)(K:=K); auto.
                  simpl_env in H. destruct_notin.
                  apply free_env__free_ddom in H; auto.
                   
                  destruct_notin.
                  apply free_env__free_ddom in H.
                  apply dom_F_Related_osubst in Hrel_subst.
                  destruct Hrel_subst as [J1 [J2 [J3 [J4 [J5 [J6 J7]]]]]].
                  rewrite J1 in H.
                  simpl_env in H. auto.
                apply ddom_dom__inv with (X:=X0)(b:=t'0)(K:=K); auto.
                  simpl_env in H. destruct_notin.
                  apply free_env__free_ddom in H; auto.
                   
                  destruct_notin.
                  apply free_env__free_ddom in H.
                  apply dom_F_Related_osubst in Hrel_subst.
                  destruct Hrel_subst as [J1 [J2 [J3 [J4 [J5 [J6 J7]]]]]].
                  rewrite J2 in H.
                  simpl_env in H. auto.
                apply ddom_dom__inv with (X:=X0)(b:=R0)(K:=K); auto.
                  simpl_env in H. destruct_notin.
                  apply free_env__free_ddom in H; auto.
                   
                  destruct_notin.
                  apply free_env__free_ddom in H.
                  apply dom_F_Related_osubst in Hrel_subst.
                  destruct Hrel_subst as [J1 [J2 [J3 [J4 [J5 [J6 J7]]]]]].
                  rewrite J3 in H.
                  simpl_env in H. auto.
                simpl_env. simpl. simpl_env in HX. simpl in HX.
                simpl_env in H. auto. 

            simpl_env in Hdomd1.
            assert (X0 `notin` (singleton X0 `union` dom dsubst0) -> False) as J.
              intro. destruct_notin. contradict NotInTac0; auto.
            rewrite <- Hdomd1 in J.
            contradict J; auto.

          simpl_env in Hdomd1'.
          simpl_env in Hdomd1.
          assert (X0 `notin` (singleton X0 `union` dom dsubst0) -> False) as J.
            intro. destruct_notin. contradict NotInTac0; auto.
          rewrite <- Hdomd1 in J.
          rewrite Hdomd1' in J.
          contradict J; auto.
        simpl_env in Hdomd1.
        simpl_env in Hdomr1.
        assert (X0 `notin` (singleton X0 `union` dom rsubst0) -> False) as J.
          intro. destruct_notin. contradict NotInTac0; auto.
        rewrite <- Hdomr1 in J.
        rewrite Hdomd1 in J.
        contradict J; auto.
      apply one_eq_app in HeqE. destruct HeqE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
        simpl in Hdomr1.
        assert (X0 `notin` (singleton X0 `union` ddom_env E0') -> False) as J.
          intro. destruct_notin. contradict NotInTac0; auto.
        rewrite Hdomr1 in J.
        contradict J; auto.

        simpl in Hdomd1. symmetry in Hdomd1.  apply dom_empty_inv in Hdomd1.
        simpl in Hdomd1'. symmetry in Hdomd1'.  apply dom_empty_inv in Hdomd1'.
        subst. 
        simpl_env in Heqdsubst. simpl_env in Heqdsubst'.
        subst. simpl_env.
        apply F_Related_osubst_kind; auto.
          apply F_Related_osubst_kind; auto. 

          assert (X `notin` fv_env E) as XnE.
            apply wfe_dom_fv_env; auto.
              apply F_Related_osubst__inversion in Hrel_subst.
              decompose [prod] Hrel_subst; auto. 
          assert (X `notin` fv_lenv lE) as XnlE.
            apply notin_fv_lenv_wfle with (E:=E); auto.
              apply F_Related_osubst__inversion in Hrel_subst.
              decompose [prod] Hrel_subst.
              apply wf_lgamma_osubst__wf_lenv in b4.
              destruct b4; auto.
          simpl_env. simpl in HX. simpl. auto.
          
  Case "F_Related_osubst_typ".
    simpl_env in *.
    apply one_eq_app in HeqE. destruct HeqE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
      simpl in Hdomd1. simpl in Hdomd1'. simpl in Hdomr1.
      simpl_env.
      apply F_Related_osubst_typ; auto.
        rewrite delta_osubst_opt with (E:=E2) (E':=E0') (K:=K) (Env:=Env); eauto.
          rewrite <- subst_tt_fresh; auto.
            apply notin_fv_wf with (X:=X) in H3; auto.
         
          apply F_Related_osubst__inversion in Hrel_subst.
          decompose [prod] Hrel_subst.
          apply odsubst_weaken; auto.
            apply wfor_left_inv in Hwfr; auto.

          apply wfor_left_inv in Hwfr; auto.

        rewrite delta_osubst_opt with (E:=E2) (E':=E0') (K:=K) (Env:=Env); eauto.
          rewrite <- subst_tt_fresh; auto.
            apply notin_fv_wf with (X:=X) in H3; auto.
         
          apply F_Related_osubst__inversion in Hrel_subst.
          decompose [prod] Hrel_subst.
          apply odsubst_weaken; auto.
            apply wfor_right_inv in Hwfr; auto.

          apply wfor_right_inv in Hwfr; auto.

        apply F_Related_osubst__inversion in Hrel_subst.
        decompose [prod] Hrel_subst.
        apply Forel_weaken with (E:=E2) (E':=E0') (K:=K); auto.
          assert (X `notin` fv_env (E0'++E2)) as XnE.
            apply wfe_dom_fv_env; auto.
          assert (X `notin` fv_tt t0) as Xnt0.
            apply notin_fv_wf with (X:=X) in H3; auto.
          simpl_env in XnE. auto.

          apply wfor_left_inv in Hwfr; auto.
          apply wfor_right_inv in Hwfr; auto.

        assert (x `notin` fv_tt t0) as xnt0.
          apply notin_fv_wf with (X:=x) in H3; auto.
        simpl_env. simpl. simpl in HX. simpl_env in H2. simpl in H2. auto.

        apply wf_typ_weakening; auto.
          apply F_Related_osubst__inversion in Hrel_subst.
          decompose [prod] Hrel_subst.
          simpl in HX. 
          apply uniq_insert_mid; auto.

      simpl in Hdomd1. symmetry in Hdomd1.  apply dom_empty_inv in Hdomd1.
      simpl in Hdomd1'. symmetry in Hdomd1'.  apply dom_empty_inv in Hdomd1'.
      simpl in Hdomr1. symmetry in Hdomr1.  apply dom_empty_inv in Hdomr1.
      subst. simpl_env. 
      apply F_Related_osubst_kind; auto.
        apply F_Related_osubst_typ; auto.

        assert (X `notin` fv_env E) as XnE.
          apply wfe_dom_fv_env; auto.
            apply F_Related_osubst__inversion in Hrel_subst.
            decompose [prod] Hrel_subst; auto. 
        assert (X `notin` fv_lenv lE) as XnlE.
          apply notin_fv_lenv_wfle with (E:=E); auto.
            apply F_Related_osubst__inversion in Hrel_subst.
            decompose [prod] Hrel_subst.
            apply wf_lgamma_osubst__wf_lenv in b4.
            destruct b4; auto.
        assert (X `notin` fv_tt t0) as Xnt0.
          apply notin_fv_wf with (X:=X) in H3; auto.
        simpl_env. simpl. simpl in HX. auto.
          
  Case "F_Related_osubst_ltyp".
    simpl_env in *.
    apply F_Related_osubst_ltyp; auto.
      rewrite delta_osubst_opt with (E:=E2) (E':=E1) (K:=K) (Env:=Env); eauto.
        rewrite <- subst_tt_fresh; auto.
          apply notin_fv_wf with (X:=X) in H5; auto.
         
        apply F_Related_osubst__inversion in Hrel_subst.
        decompose [prod] Hrel_subst.
        apply odsubst_weaken; auto.
          apply wfor_left_inv in Hwfr; auto.

        apply wfor_left_inv in Hwfr; auto.

      rewrite delta_osubst_opt with (E:=E2) (E':=E1) (K:=K) (Env:=Env); eauto.
        rewrite <- subst_tt_fresh; auto.
          apply notin_fv_wf with (X:=X) in H5; auto.
         
        apply F_Related_osubst__inversion in Hrel_subst.
        decompose [prod] Hrel_subst.
        apply odsubst_weaken; auto.
          apply wfor_right_inv in Hwfr; auto.

        apply wfor_right_inv in Hwfr; auto.

      destruct H1.
      split; auto.
         clear IHHrel_subst Hrel_subst H3 H0 H H5 H4 Hdomd1 Hdomd1' Hdomr1 Hdomd2 Hdomd2' Hdomr2.
         destruct_notin.
         apply free_lenv__free_dom in NotInTac3.
          solve_uniq.

      apply F_Related_osubst__inversion in Hrel_subst.
      decompose [prod] Hrel_subst.
      apply Forel_weaken with (E:=E2) (E':=E1) (K:=K); auto.
        assert (X `notin` fv_env (E1++E2)) as XnE.
          apply wfe_dom_fv_env; auto.
        assert (X `notin` fv_tt t0) as Xnt0.
          apply notin_fv_wf with (X:=X) in H5; auto.
        simpl_env in XnE. auto.

        apply wfor_left_inv in Hwfr; auto.
        apply wfor_right_inv in Hwfr; auto.

      assert (x `notin` fv_tt t0) as xnt0.
        apply notin_fv_wf with (X:=x) in H5; auto.
      simpl_env. simpl. auto.

      apply wf_typ_weakening; auto.
        apply F_Related_osubst__inversion in Hrel_subst.
        decompose [prod] Hrel_subst.
        simpl in HX. 
        apply uniq_insert_mid; auto.
Qed.

Lemma F_Related_osubst_gweaken : forall E1 E2 D gsubst1 gsubst2 gsubst1' gsubst2' lgsubst lgsubst' rsubst1 rsubst2 dsubst1 dsubst2 dsubst1' dsubst2' x T e e' Env lEnv,
  F_Related_osubst (E1++E2) D (gsubst1++gsubst2) (gsubst1'++gsubst2') lgsubst lgsubst' (rsubst1++rsubst2) (dsubst1++dsubst2) (dsubst1'++dsubst2') Env lEnv ->
  gdom_env E1 [=] dom gsubst1 ->
  gdom_env E1 [=] dom gsubst1' ->
  gdom_env E2 [=] dom gsubst2 ->
  gdom_env E2 [=] dom gsubst2' ->
  ddom_env E1 [=] dom dsubst1 ->
  ddom_env E1 [=] dom dsubst1' ->
  ddom_env E1 [=] dom rsubst1 ->
  ddom_env E2 [=] dom dsubst2 ->
  ddom_env E2 [=] dom dsubst2' ->
  ddom_env E2 [=] dom rsubst2 ->
  x `notin` (dom E1 `union` dom E2 `union` dom D `union` fv_env Env  `union` fv_lenv lEnv)->
  wf_typ E2 T kn_nonlin ->
  typing Env nil e (apply_delta_subst_typ dsubst2 T) ->
  typing Env nil e' (apply_delta_subst_typ dsubst2' T) ->
  F_Related_ovalues T rsubst2 dsubst2 dsubst2' e e' Env nil ->
  F_Related_osubst (E1++[(x, bind_typ T)]++E2) D (gsubst1++[(x, e)]++gsubst2) (gsubst1'++[(x, e')]++gsubst2') lgsubst lgsubst' (rsubst1++rsubst2) (dsubst1++dsubst2) (dsubst1'++dsubst2') Env lEnv.
Proof.
  intros E1 E2 D gsubst1 gsubst2 gsubst1' gsubst2' lgsubst lgsubst' rsubst1 rsubst2 dsubst1 dsubst2 dsubst1' dsubst2' x T e e' Env lEnv
                Hrel_subst Hdomg1 Hdomg1' Hdomg2 Hdomg2' Hdomd1 Hdomd1' Hdomr1 Hdomd2 Hdomd2' Hdomr2 Hx Hwft Htyp Htyp' Hrel.
  remember (E1++E2) as E.
  remember (gsubst1++gsubst2) as gsubst.
  remember (gsubst1'++gsubst2') as gsubst'.
  remember (rsubst1++rsubst2) as rsubst.
  remember (dsubst1++dsubst2) as dsubst.
  remember (dsubst1'++dsubst2') as dsubst'.
  generalize dependent E1.
  generalize dependent dsubst1.
  generalize dependent dsubst1'.
  generalize dependent rsubst1.  
  generalize dependent gsubst1.
  generalize dependent gsubst1'.
  (F_Related_osubst_cases (induction Hrel_subst) Case); intros; subst.
  Case "F_Related_osubst_empty".
    symmetry in Heqdsubst.
    apply app_eq_nil in Heqdsubst.
    destruct Heqdsubst; subst.

    symmetry in Heqdsubst'.
    apply app_eq_nil in Heqdsubst'.
    destruct Heqdsubst'; subst.

    symmetry in Heqrsubst.
    apply app_eq_nil in Heqrsubst.
    destruct Heqrsubst; subst.

    symmetry in Heqgsubst.
    apply app_eq_nil in Heqgsubst.
    destruct Heqgsubst; subst.

    symmetry in Heqgsubst'.
    apply app_eq_nil in Heqgsubst'.
    destruct Heqgsubst'; subst.

    symmetry in HeqE.
    apply app_eq_nil in HeqE.
    destruct HeqE; subst.
    rewrite_env ([(x, bind_typ T)]++empty).
    rewrite_env ([(x, e)]++gamma_nil).
    rewrite_env ([(x, e')]++gamma_nil).
    apply F_Related_osubst_typ; auto.
       simpl. eauto using notin_fv_wf.

  Case "F_Related_osubst_kind".
    simpl_env in *.
    apply one_eq_app in Heqrsubst. destruct Heqrsubst as [[rsubst0 [rEQ1 rEQ2]] | [rEQ1 rEQ2]]; subst.
      apply one_eq_app in Heqdsubst. destruct Heqdsubst as [[dsubst0 [dEQ1 dEQ2]] | [dEQ1 dEQ2]]; subst.
        apply one_eq_app in Heqdsubst'. destruct Heqdsubst' as [[dsubst0' [dEQ1' dEQ2']] | [dEQ1' dEQ2']]; subst.
          apply one_eq_app in HeqE. destruct HeqE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
            simpl_env.
            apply F_Related_osubst_kind; auto.
              apply IHHrel_subst with (rsubst1:=rsubst0) (dsubst1:=dsubst0) (dsubst1':=dsubst0') (gsubst1'0:=gsubst1'); auto.
                apply ddom_dom__inv with (X:=X)(b:=t)(K:=K); auto.
                  simpl_env in H. destruct_notin.
                  apply free_env__free_ddom in H; auto.
                   
                  destruct_notin.
                  apply free_env__free_ddom in H.
                  apply dom_F_Related_osubst in Hrel_subst.
                  destruct Hrel_subst as [J1 [J2 [J3 [J4 [J5 [J6 J7]]]]]].
                  rewrite J1 in H.
                  simpl_env in H. auto.
                apply ddom_dom__inv with (X:=X)(b:=t')(K:=K); auto.
                  simpl_env in H. destruct_notin.
                  apply free_env__free_ddom in H; auto.
                   
                  destruct_notin.
                  apply free_env__free_ddom in H.
                  apply dom_F_Related_osubst in Hrel_subst.
                  destruct Hrel_subst as [J1 [J2 [J3 [J4 [J5 [J6 J7]]]]]].
                  rewrite J2 in H.
                  simpl_env in H. auto.
                apply ddom_dom__inv with (X:=X)(b:=R)(K:=K); auto.
                  simpl_env in H. destruct_notin.
                  apply free_env__free_ddom in H; auto.
                   
                  destruct_notin.
                  apply free_env__free_ddom in H.
                  apply dom_F_Related_osubst in Hrel_subst.
                  destruct Hrel_subst as [J1 [J2 [J3 [J4 [J5 [J6 J7]]]]]].
                  rewrite J3 in H.
                  simpl_env in H. auto.
                simpl_env. simpl. simpl_env in Hx. simpl in Hx.
                simpl_env in H. 
                assert (X `notin` fv_tt T) as XnT.
                  apply notin_fv_wf with (X:=X) in Hwft; auto.
                auto.

            simpl_env in Hdomd1.
            assert (X `notin` (singleton X `union` dom dsubst0) -> False) as J.
              intro. destruct_notin. contradict NotInTac0; auto.
            rewrite <- Hdomd1 in J.
            contradict J; auto.

          simpl_env in Hdomd1'.
          simpl_env in Hdomd1.
          assert (X `notin` (singleton X `union` dom dsubst0) -> False) as J.
            intro. destruct_notin. contradict NotInTac0; auto.
          rewrite <- Hdomd1 in J.
          rewrite Hdomd1' in J.
          contradict J; auto.
        simpl_env in Hdomd1.
        simpl_env in Hdomr1.
        assert (X `notin` (singleton X `union` dom rsubst0) -> False) as J.
          intro. destruct_notin. contradict NotInTac0; auto.
        rewrite <- Hdomr1 in J.
        rewrite Hdomd1 in J.
        contradict J; auto.
      apply one_eq_app in HeqE. destruct HeqE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
        simpl in Hdomr1.
        assert (X `notin` (singleton X `union` ddom_env E0') -> False) as J.
          intro. destruct_notin. contradict NotInTac0; auto.
        rewrite Hdomr1 in J.
        contradict J; auto.

        simpl in Hdomg1. symmetry in Hdomg1.  apply dom_empty_inv in Hdomg1.
        simpl in Hdomg1'. symmetry in Hdomg1'.  apply dom_empty_inv in Hdomg1'.
        simpl in Hdomd1. symmetry in Hdomd1.  apply dom_empty_inv in Hdomd1.
        simpl in Hdomd1'. symmetry in Hdomd1'.  apply dom_empty_inv in Hdomd1'.
        subst. 
        simpl_env in Heqdsubst. simpl_env in Heqdsubst'.
        subst.
        simpl_env.

        assert (J:=Hrel_subst).
        apply F_Related_osubst__inversion in J.
        decompose [prod] J.
        assert (x `notin` fv_env E) as xnE.
          apply wfe_dom_fv_env; auto.
        assert (x `notin` fv_lenv lE) as xnlE.
          apply notin_fv_lenv_wfle with (E:=E); auto.
            apply wf_lgamma_osubst__wf_lenv in b4.
            destruct b4; auto.
        assert (x `notin` fv_tt T) as xnT.
          apply notin_fv_wf with (X:=x) in Hwft; auto.

        apply F_Related_osubst_typ; simpl; auto.
          simpl_env.
          apply F_Related_osubst_kind; simpl; auto.

  Case "F_Related_osubst_typ".
    simpl_env in *.
    apply one_eq_app in Heqgsubst. destruct Heqgsubst as [[gsubst0 [gEQ1 gEQ2]] | [gEQ1 gEQ2]]; subst.
      apply one_eq_app in Heqgsubst'. destruct Heqgsubst' as [[gsubst0' [gEQ1' gEQ2']] | [gEQ1' gEQ2']]; subst.
        apply one_eq_app in HeqE. destruct HeqE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
          simpl_env.
          apply F_Related_osubst_typ; auto.
              apply IHHrel_subst with (rsubst3:=rsubst1) (dsubst3:=dsubst1) (dsubst1'0:=dsubst1') (gsubst1:=gsubst0) (gsubst1':=gsubst0'); auto.
                apply gdom_dom__inv with (x:=x0)(b:=v)(t:=t); auto.
                  simpl_env in H2. destruct_notin.
                  apply free_env__free_gdom in H2; auto.

                  destruct_notin.
                  apply free_env__free_gdom in H2.
                  apply dom_F_Related_osubst in Hrel_subst.
                  destruct Hrel_subst as [J1 [J2 [J3 [J4 [J5 [J6 J7]]]]]].
                  rewrite J4 in H2.
                  simpl_env in H2. auto.
                apply gdom_dom__inv with (x:=x0)(b:=v')(t:=t); auto.
                  simpl_env in H2. destruct_notin.
                  apply free_env__free_gdom in H2; auto.
                   
                  destruct_notin.
                  apply free_env__free_gdom in H2.
                  apply dom_F_Related_osubst in Hrel_subst.
                  destruct Hrel_subst as [J1 [J2 [J3 [J4 [J5 [J6 J7]]]]]].
                  rewrite J5 in H2.
                  simpl_env in H2. auto.

                simpl_env. simpl. simpl_env in Hx. simpl in Hx.
                simpl_env in H2. 
                assert (x0 `notin` fv_tt T) as x0nT.
                  apply notin_fv_wf with (X:=x0) in Hwft; auto.
                auto.

                apply wf_typ_weakening; auto.
                  apply F_Related_osubst__inversion in Hrel_subst.
                  decompose [prod] Hrel_subst.
                  simpl in Hx. 
                  apply uniq_insert_mid; auto.

            simpl_env in Hdomg1.
            assert (x0 `notin` (singleton x0 `union` dom gsubst0) -> False) as J.
              intro. destruct_notin. contradict NotInTac0; auto.
            rewrite <- Hdomg1 in J.
            contradict J; auto.

          simpl_env in Hdomg1'.
          simpl_env in Hdomg1.
          assert (x0 `notin` (singleton x0 `union` dom gsubst0) -> False) as J.
            intro. destruct_notin. contradict NotInTac0; auto.
          rewrite <- Hdomg1 in J.
          rewrite Hdomg1' in J.
          contradict J; auto.
      apply one_eq_app in HeqE. destruct HeqE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
        simpl in Hdomg1.
        assert (x0 `notin` (singleton x0 `union` gdom_env E0') -> False) as J.
          intro. destruct_notin. contradict NotInTac0; auto.
        rewrite Hdomg1 in J.
        contradict J; auto.

        simpl in Hdomg1'. symmetry in Hdomg1'.  apply dom_empty_inv in Hdomg1'.
        simpl in Hdomd1. symmetry in Hdomd1.  apply dom_empty_inv in Hdomd1.
        simpl in Hdomd1'. symmetry in Hdomd1'.  apply dom_empty_inv in Hdomd1'.
        simpl in Hdomr1. symmetry in Hdomr1.  apply dom_empty_inv in Hdomr1.
        subst. 
        simpl_env in Heqgsubst'.
        subst.
        simpl_env.

        assert (J:=Hrel_subst).
        apply F_Related_osubst__inversion in J.
        decompose [prod] J.
        assert (x `notin` fv_env E) as xnE.
          apply wfe_dom_fv_env; auto.
        assert (x `notin` fv_lenv lE) as xnlE.
          apply notin_fv_lenv_wfle with (E:=E); auto.
            apply wf_lgamma_osubst__wf_lenv in b4.
            destruct b4; auto.
        assert (x `notin` fv_tt T) as xnT.
          apply notin_fv_wf with (X:=x) in Hwft; auto.
        assert (x `notin` fv_tt t) as xnt.
          apply notin_fv_wf with (X:=x) in H3; auto.
        simpl in Hx. auto.
        apply F_Related_osubst_typ; simpl; auto.
          simpl_env.
          apply F_Related_osubst_typ; simpl; auto.

  Case "F_Related_osubst_ltyp".
    simpl_env in *.
    apply F_Related_osubst_ltyp; auto.
      apply IHHrel_subst with (rsubst3:=rsubst1) (dsubst3:=dsubst1) (dsubst1'0:=dsubst1') (gsubst3:=gsubst1) (gsubst1'0:=gsubst1'); auto.

      destruct H1.
      split; auto.
         clear IHHrel_subst Hrel_subst H3 H0 H H5 H4 Hdomd1 Hdomd1' Hdomr1 Hdomd2 Hdomd2' Hdomr2.
         destruct_notin.
         apply free_lenv__free_dom in NotInTac2.
         solve_uniq.

      assert (x0 `notin` fv_tt T) as x0nT.
        apply notin_fv_wf with (X:=x0) in Hwft; auto.
      assert (x0 `notin` fv_tt t) as x0nt.
        apply notin_fv_wf with (X:=x0) in H5; auto.
      simpl_env. simpl. auto.

      apply wf_typ_weakening; auto.
        apply F_Related_osubst__inversion in Hrel_subst.
        decompose [prod] Hrel_subst.
        simpl in Hx. 
        apply uniq_insert_mid; auto.
Qed.

Lemma F_Rosubst_gweaken : forall E1 E2 rsubst dsubst dsubst' x T Env,
  F_Rosubst (E1++E2) rsubst dsubst dsubst' Env ->
  x `notin` (dom E1 `union` dom E2 `union` fv_env Env)->
  wf_typ E2 T kn_nonlin ->
  F_Rosubst (E1++[(x, bind_typ T)]++E2) rsubst dsubst dsubst' Env.
Proof.
  intros E1 E2 rsubst dsubst dsubst' x T Env HRsubst Hx Wft.
  remember (E1++E2) as EE.
  generalize dependent E1.
  (F_Rosubst_cases (induction HRsubst) Case); intros; subst.
  Case "F_Rosubst_empty".
    symmetry in HeqEE.
    apply app_eq_nil in HeqEE.
    destruct HeqEE; subst.
    simpl_env.
    rewrite_env ([(x, bind_typ T)]++nil). rewrite_env (nil++rho_nil).
    rewrite_env (nil++delta_nil).  rewrite_env (nil++delta_nil).
    apply F_Rosubst_typ; auto.
 
  Case "F_Rosubst_rel".
    simpl_env in *.
    apply one_eq_app in HeqEE. destruct HeqEE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
      simpl_env.
      apply F_Rosubst_rel; auto.
        assert (X `notin` fv_tt T) as XnT.
          apply notin_fv_wf with (X:=X) in Wft; auto.
            destruct_notin.
            apply free_env__free_dom in H0. 
            simpl_env in H0. auto.
        simpl_env in H0. simpl_env. simpl. auto.

      simpl_env.
      apply F_Rosubst_typ; auto.
        apply F_Rosubst_rel; auto.

        assert (x `notin` fv_env E) as XnE.
          apply wfe_dom_fv_env; auto.
          apply F_Rosubst__wf_osubst in HRsubst.
          decompose [prod] HRsubst.
          apply  wf_rho_subst__uniq in b. 
          decompose [and] b; auto.
        simpl. auto.
 
  Case "F_Rosubst_typ".
    simpl_env in *.
    apply one_eq_app in HeqEE. destruct HeqEE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
      simpl_env.
      apply F_Rosubst_typ; auto.
        apply wf_typ_weakening; auto.
          apply F_Rosubst__wf_osubst in HRsubst.
          decompose [prod] HRsubst.
          apply  wf_rho_subst__uniq in b. 
          decompose [and] b; auto.
      
          assert (x0 `notin` fv_tt T) as x0nT.
            apply notin_fv_wf with (X:=x0) in Wft; auto.
              destruct_notin.
              apply free_env__free_dom in H0. 
              simpl_env in H0. auto.
          simpl_env in H0. simpl_env. simpl. auto.

      simpl_env.
      apply F_Rosubst_typ; auto.
        apply F_Rosubst_typ; auto.

        assert (x `notin` fv_env E) as XnE.
          apply wfe_dom_fv_env; auto.
          apply F_Rosubst__wf_osubst in HRsubst.
          decompose [prod] HRsubst.
          apply  wf_rho_subst__uniq in b. 
          decompose [and] b; auto.
        assert (x `notin` fv_tt T0) as xnT.
          apply notin_fv_wf with (X:=x) in H; auto.
        simpl. auto.
Qed.

Lemma F_Rosubst_dweaken : forall E1 E2 rsubst1 rsubst2 dsubst1 dsubst2 dsubst1' dsubst2' X R t2 t2' K Env,
  F_Rosubst (E1++E2) (rsubst1++rsubst2) (dsubst1++dsubst2) (dsubst1'++dsubst2') Env ->
  ddom_env E1 [=] dom dsubst1 ->
  ddom_env E1 [=] dom dsubst1' ->
  ddom_env E1 [=] dom rsubst1 ->
  ddom_env E2 [=] dom dsubst2 ->
  ddom_env E2 [=] dom dsubst2' ->
  ddom_env E2 [=] dom rsubst2 ->
  X `notin` (dom E1 `union` dom E2 `union` fv_env Env)->
  wfor Env R t2 t2' K ->
  F_Rosubst (E1++[(X, bind_kn K)]++E2) (rsubst1++[(X, R)]++rsubst2) (dsubst1++[(X, t2)]++dsubst2) (dsubst1'++[(X, t2')]++dsubst2') Env.
Proof.
  intros E1 E2 rsubst1 rsubst2 dsubst1 dsubst2 dsubst1' dsubst2' X R t2 t2' K Env HRsubst 
    Hdomd1 Hdomd1' Hdomr1 Hdomd2 Hdomd2' Hdomr2 HX Hwfr.
  remember (E1++E2) as E.
  remember (rsubst1++rsubst2) as rsubst.
  remember (dsubst1++dsubst2) as dsubst.
  remember (dsubst1'++dsubst2') as dsubst'.
  generalize dependent E1.
  generalize dependent dsubst1.
  generalize dependent dsubst1'.
  generalize dependent rsubst1.  
  (F_Rosubst_cases (induction HRsubst) Case); intros; subst.
  Case "F_Rosubst_empty".
    symmetry in HeqE.
    apply app_eq_nil in HeqE.
    destruct HeqE; subst.

    symmetry in Heqdsubst.
    apply app_eq_nil in Heqdsubst.
    destruct Heqdsubst; subst.

    symmetry in Heqdsubst'.
    apply app_eq_nil in Heqdsubst'.
    destruct Heqdsubst'; subst.

    symmetry in Heqrsubst.
    apply app_eq_nil in Heqrsubst.
    destruct Heqrsubst; subst.

    simpl_env.
    rewrite_env ([(X, bind_kn K)]++nil). 
    rewrite_env ([(X, R)]++rho_nil).
    rewrite_env ([(X, t2)]++delta_nil).  
    rewrite_env ([(X, t2')]++delta_nil).
    apply F_Rosubst_rel; auto.
 
  Case "F_Rosubst_rel".
    simpl_env in *.
    apply one_eq_app in Heqrsubst. destruct Heqrsubst as [[rsubst0 [rEQ1 rEQ2]] | [rEQ1 rEQ2]]; subst.
      apply one_eq_app in Heqdsubst. destruct Heqdsubst as [[dsubst0 [dEQ1 dEQ2]] | [dEQ1 dEQ2]]; subst.
        apply one_eq_app in Heqdsubst'. destruct Heqdsubst' as [[dsubst0' [dEQ1' dEQ2']] | [dEQ1' dEQ2']]; subst.
          apply one_eq_app in HeqE. destruct HeqE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
            simpl_env.
            apply F_Rosubst_rel; auto.
              apply IHHRsubst with (rsubst1:=rsubst0) (dsubst1:=dsubst0) (dsubst1':=dsubst0'); auto.
                apply ddom_dom__inv with (X:=X0)(b:=t)(K:=K); auto.
                  simpl_env in H0. destruct_notin.
                  apply free_env__free_ddom in H0; auto.
                   
                  destruct_notin.
                  apply free_env__free_ddom in H0.
                  apply dom_F_Rosubst in HRsubst.
                  destruct HRsubst as [J1 [J2 J3]].
                  rewrite J1 in H0.
                  simpl_env in H0. auto.
                apply ddom_dom__inv with (X:=X0)(b:=t')(K:=K); auto.
                  simpl_env in H0. destruct_notin.
                  apply free_env__free_ddom in H0; auto.
                   
                  destruct_notin.
                  apply free_env__free_ddom in H0.
                  apply dom_F_Rosubst in HRsubst.
                  destruct HRsubst as [J1 [J2 J3]].
                  rewrite J2 in H0.
                  simpl_env in H0. auto.
                apply ddom_dom__inv with (X:=X0)(b:=R)(K:=K); auto.
                  simpl_env in H0. destruct_notin.
                  apply free_env__free_ddom in H0; auto.
                   
                  destruct_notin.
                  apply free_env__free_ddom in H0.
                  apply dom_F_Rosubst in HRsubst.
                  destruct HRsubst as [J1 [J2 J3]].
                  rewrite J3 in H0.
                  simpl_env in H0. auto.
                simpl_env. simpl. simpl_env in HX. simpl in HX.
                simpl_env in H0. 
                auto.

            simpl_env in Hdomd1.
            assert (X0 `notin` (singleton X0 `union` dom dsubst0) -> False) as J.
              intro. destruct_notin. contradict NotInTac0; auto.
            rewrite <- Hdomd1 in J.
            contradict J; auto.

          simpl_env in Hdomd1'.
          simpl_env in Hdomd1.
          assert (X0 `notin` (singleton X0 `union` dom dsubst0) -> False) as J.
            intro. destruct_notin. contradict NotInTac0; auto.
          rewrite <- Hdomd1 in J.
          rewrite Hdomd1' in J.
          contradict J; auto.
        simpl_env in Hdomd1.
        simpl_env in Hdomr1.
        assert (X0 `notin` (singleton X0 `union` dom rsubst0) -> False) as J.
          intro. destruct_notin. contradict NotInTac0; auto.
        rewrite <- Hdomr1 in J.
        rewrite Hdomd1 in J.
        contradict J; auto.
      apply one_eq_app in HeqE. destruct HeqE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
        simpl in Hdomr1.
        assert (X0 `notin` (singleton X0 `union` ddom_env E0') -> False) as J.
          intro. destruct_notin. contradict NotInTac0; auto.
        rewrite Hdomr1 in J.
        contradict J; auto.

        simpl in Hdomd1. symmetry in Hdomd1.  apply dom_empty_inv in Hdomd1.
        simpl in Hdomd1'. symmetry in Hdomd1'.  apply dom_empty_inv in Hdomd1'.
        subst. 
        simpl_env in Heqdsubst. simpl_env in Heqdsubst'.
        subst.
        simpl_env.

        assert (J:=HRsubst).
        apply F_Rosubst__wf_osubst in J.
        decompose [prod] J.
        apply wf_rho_subst__uniq in b.
        decompose [and] b.
        assert (X `notin` fv_env E) as XnE.
          apply wfe_dom_fv_env; auto.
        apply F_Rosubst_rel; simpl; auto.
          simpl_env.
          apply F_Rosubst_rel; simpl; auto.
 
  Case "F_Rosubst_typ".
    simpl_env in *.
    apply one_eq_app in HeqE. destruct HeqE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
      simpl_env.
      apply F_Rosubst_typ; auto.
        apply wf_typ_weakening; auto.
          apply F_Rosubst__wf_osubst in HRsubst.
          decompose [prod] HRsubst.
          apply  wf_rho_subst__uniq in b. 
          decompose [and] b; auto.       
        simpl_env in H0. simpl_env. simpl. auto.

      simpl in Hdomd1. symmetry in Hdomd1.  apply dom_empty_inv in Hdomd1.
      simpl in Hdomd1'. symmetry in Hdomd1'.  apply dom_empty_inv in Hdomd1'.
      simpl in Hdomr1. symmetry in Hdomr1.  apply dom_empty_inv in Hdomr1.
      subst. 
      simpl_env.
      apply F_Rosubst_rel; auto.
        apply F_Rosubst_typ; auto.

        assert (X `notin` fv_env E) as XnE.
          apply wfe_dom_fv_env; auto.
          apply F_Rosubst__wf_osubst in HRsubst.
          decompose [prod] HRsubst.
          apply  wf_rho_subst__uniq in b. 
          decompose [and] b; auto.
        assert (X `notin` fv_tt T) as XnT.
          apply notin_fv_wf with (X:=X) in H; auto.
        simpl. auto.
Qed.

Lemma free_dom__free_env: forall x E,
  x `in` dom E ->
  x `in` fv_env E.
Proof.
  induction E as [ | [x1 b1] E ]; simpl; intros H; auto.
  destruct b1; fsetdec.
Qed.

Lemma free_dom__free_lenv: forall x E,
  x `in` dom E ->
  x `in` fv_lenv E.
Proof.
  induction E as [ | [x1 b1] E ]; simpl; intros H; auto.
  destruct b1; fsetdec.
Qed.

Lemma ddom__dom: forall x E,
  x `in` ddom_env E ->
  x `in` dom E.
Proof.
  induction E as [ | [x1 b1] E ]; simpl; intros H; auto.
  destruct b1; fsetdec.
Qed.                       

Lemma gdom__dom: forall x E,
  x `in` gdom_env E ->
  x `in` dom E.
Proof.
  induction E as [ | [x1 b1] E ]; simpl; intros H; auto.
  destruct b1; fsetdec.
Qed.                       

Lemma disjoint_innotin1 : forall A B (D1:list (atom*A)) (D2:list (atom*B)) x,
  disjoint D1 D2 ->
  x `in` dom D1 ->
  x `notin` dom D2.
Proof.
  intros A B D1 D2 x Disj xinD1.
  solve_uniq.
Qed.

Lemma disjoint_innotin2 : forall A B (D1:list (atom*A)) (D2:list (atom*B)) x,
  disjoint D1 D2 ->
  x `in` dom D2 ->
  x `notin` dom D1.
Proof.
  intros A B D1 D2 x Disj xinD1.
  solve_uniq.
Qed.

Lemma fv_env__includes__dom : forall Env,
  dom Env [<=] fv_env Env.
Proof.
  intros Env.
  induction Env; simpl.
    fsetdec.
    destruct a. destruct b; fsetdec.
Qed.


