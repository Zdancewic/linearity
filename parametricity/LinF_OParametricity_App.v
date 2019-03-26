(** Authors: Jianzhou Zhao. *)

Require Export Metatheory.
Require Import LinF_Definitions.
Require Import LinF_Infrastructure.
Require Import LinF_Lemmas.
Require Import LinF_Soundness.
Require Import LinF_OParametricity.
Require Import LinF_Renaming.

Export OParametricity.

(***************************************************************)
(*                 Beta Eta Equivalence                                     *)
(***************************************************************)
Inductive beta_eta_eq : env -> lenv -> exp -> exp -> typ -> Prop :=
  | bee_refl : forall E lE e t, 
      typing E lE e t ->
      beta_eta_eq E lE e e t
  | bee_sym : forall E lE e e' t, 
      beta_eta_eq E lE e e' t -> 
      beta_eta_eq E lE e' e t
  | bee_trans : forall E lE e e' e'' t, 
      beta_eta_eq E lE e e' t -> 
      beta_eta_eq E lE e' e'' t -> 
      beta_eta_eq E lE e e'' t 
  | bee_red : forall E lE e v t, 
      typing E lE e t ->
      bigstep_red e v -> 
      beta_eta_eq E lE e v t
  | bee_congr_app : forall E lE1 lE2 lE e1 e2 e2' K t1 t2,
      typing E lE1 e1 (typ_arrow K t1 t2) ->
      beta_eta_eq E lE2 e2 e2' t1 -> 
      lenv_split E lE1 lE2 lE ->
      beta_eta_eq E lE (exp_app e1 e2) (exp_app e1 e2') t2
  .  

Hint Constructors beta_eta_eq.

Lemma beta_eta_eq__regular : forall E lE e e' t,
  beta_eta_eq E lE e e' t ->
  typing E lE e t /\ typing E lE e' t.
Proof.
  induction 1; auto.
    destruct IHbeta_eta_eq; auto.

    destruct IHbeta_eta_eq1.
    destruct IHbeta_eta_eq2; auto.

    split; auto.
       apply preservation_bigstep_red with (e':=v) in H; auto.

    destruct IHbeta_eta_eq.
     split; eauto.
Qed.    

Lemma renaming_length : forall lEnv x y,
  length lEnv = length (subst_atom_lenv lEnv x y).
Proof.
  induction lEnv; intros x y; simpl. auto.
    destruct a.
    destruct (x==a); subst; simpl; auto.
Qed.     

Lemma zero_length__lempty : forall lEnv,
  length lEnv = 0 ->
  lEnv = lempty.
Proof.
  induction lEnv; intros; auto.
    destruct a. simpl in H. inversion H.
Qed.

Lemma bee_lin_renaming_one : forall E lE' lE e e' t x y b,
  beta_eta_eq E (lE'++[(x,b)]++lE) e e' t ->
  y `notin` dom E `union` dom lE' `union` dom lE ->
  beta_eta_eq E (lE'++[(y,b)]++lE) (subst_ee x y e) (subst_ee x y e') t.
Proof.
  intros E lE' lE e e' t x y b Bee ynotin.
  destruct (x == y); subst.
    rewrite subst_ee_id. rewrite subst_ee_id. auto.

  remember (lE'++[(x, b)]++lE) as lEE.
  generalize dependent lE'.
  generalize dependent lE.
  generalize dependent x.
  generalize dependent b.
  induction Bee; intros; subst; auto.
    apply bee_refl.
      apply typing_lin_renaming_one; auto.

    apply bee_trans with (e':=subst_ee x y e'); eauto.

    apply bee_red.
      apply typing_lin_renaming_one; auto.
      apply bigstep_red_renaming_one; auto.
        apply notin_fv_ee_typing with (y:=y) in H; auto.

    simpl. destruct b.
    assert (Split:=H0).
    apply lenv_split_cases_mid in H0.
    destruct H0 as [LEFT | RIGHT].
    SCase "left".
      destruct LEFT as [D1L [D1R [D2L [D2R [Q1 [Q2 [S1 S2]]]]]]]; subst.
      assert (D1L ++ [(x, lbind_typ t)] ++ D1R=D1L ++ [(x, lbind_typ t)] ++ D1R) as IH1. auto.
      assert (DomEq2:=S2).
      apply dom_lenv_split in DomEq2.
      rewrite DomEq2 in ynotin.
      assert (DomEq1:=S1).
      apply dom_lenv_split in DomEq1.
      rewrite DomEq1 in ynotin.
      assert (x `notin` (dom (D2L++D2R) `union` dom E)) as J.
        eapply lenv_split_not_in_left; eauto.
          simpl_env. auto.
      assert (G:=Bee).
      apply beta_eta_eq__regular in G. destruct G as [G2 G2'].
      rewrite <- (non_subst E (D2L++D2R) e2 t1 x y); auto.
      rewrite <- (non_subst E (D2L++D2R) e2' t1 x y); auto.
      apply (bee_congr_app E (D1L ++ [(y, lbind_typ t)] ++ D1R) (D2L ++ D2R) _ _ _ _ K t1 t2); auto.
        apply typing_lin_renaming_one; auto.

        simpl_env.
        eapply lenv_split_sub_left; eauto.
          apply wf_lenv_split in Split.
          apply wf_lenv_renaming_one with (x0:=x); auto.
             assert (x `notin` dom lE') as xnotinlE'.
               apply uniq_from_wf_lenv in Split.
               apply fresh_mid_head in Split; auto.
             assert (x `notin` dom lE0) as xnotinlE0.
               apply uniq_from_wf_lenv in Split.
               apply fresh_mid_tail in Split; auto.
             auto.

             rewrite DomEq1. rewrite DomEq2. auto.
    SCase "right".
      destruct RIGHT as [D1L [D1R [D2L [D2R [Q1 [Q2 [S1 S2]]]]]]]; subst.
      assert (D2L ++ [(x, lbind_typ t)] ++ D2R=D2L ++ [(x, lbind_typ t)] ++ D2R) as IH2. auto.
      assert (DomEq2:=S2).
      apply dom_lenv_split in DomEq2.
      rewrite DomEq2 in ynotin.
      assert (DomEq1:=S1).
      apply dom_lenv_split in DomEq1.
      rewrite DomEq1 in ynotin.
      assert (x `notin` (dom (D1L++D1R) `union` dom E)) as J.
        eapply lenv_split_not_in_right; eauto.
          simpl_env. auto.
      rewrite <- (non_subst E (D1L++D1R) e1 (typ_arrow K t1 t2) x y); auto.
      apply (bee_congr_app E (D1L ++ D1R) (D2L ++ [(y, lbind_typ t)] ++ D2R) _ _ _ _ K t1 t2); auto.
        simpl_env.
        eapply lenv_split_sub_right; eauto.
          apply wf_lenv_split in Split.
          apply wf_lenv_renaming_one with (x0:=x); auto.
             assert (x `notin` dom lE') as xnotinlE'.
               apply uniq_from_wf_lenv in Split.
               apply fresh_mid_head in Split; auto.
             assert (x `notin` dom lE0) as xnotinlE0.
               apply uniq_from_wf_lenv in Split.
               apply fresh_mid_tail in Split; auto.
             auto.

             rewrite DomEq1. rewrite DomEq2. auto.
Qed.

Lemma bee_lin_renaming : forall E lE e e' t (x y:atom),
  beta_eta_eq E lE e e' t ->
  x `notin` dom E ->
  y `notin` dom E `union` dom lE ->
  beta_eta_eq E (subst_atom_lenv lE x y) (subst_ee x y e) (subst_ee x y e') t.
Proof.
  intros E lE e e' t x y Bee xnotin ynotin.
  destruct (@in_dec x (dom lE)) as [xin | xnotin'].
    apply binds_In_inv in xin.
    destruct xin as [b Binds].
    assert (uniq lE) as Uniq.
      apply beta_eta_eq__regular in Bee. destruct Bee.
      eauto.
    apply subst_atom_lenv_in_inv with (y:=y) in Binds; eauto.
    destruct Binds as [lE1 [lE2 [EQ1 EQ2]]]; subst.
    rewrite EQ2.
    apply bee_lin_renaming_one with (y:=y)(E:=E) in Bee; auto.

    assert (J:=Bee).
    apply beta_eta_eq__regular in J. destruct J as [J J'].
    apply notin_fv_ee_typing with (y:=x) in J; auto.
    apply notin_fv_ee_typing with (y:=x) in J'; auto.
    rewrite <- subst_ee_fresh; auto.
    rewrite <- subst_ee_fresh; auto.
    rewrite <- subst_atom_lenv_notin_inv; auto.
Qed.

(***************************************************************)
(*                               Relations                                            *)
(***************************************************************)
Definition Rfun Env l (A A':typ) (f:exp) K (v v':exp) : Prop := 
  exists lEnv,
  length lEnv = l /\ 
  typing Env lEnv v A /\ typing Env lEnv v' A' /\
  typing Env nil f (typ_arrow K A A') /\
  beta_eta_eq Env lEnv (exp_app f v) v' A'
  .

Definition Rid Env l (A:typ) (v v':exp) : Prop := 
  exists lEnv,
  length lEnv = l /\ 
  typing Env lEnv v A /\ typing Env lEnv v' A /\ beta_eta_eq Env lEnv v v' A
  .

Lemma Rfun_admissible : forall Env l A A' Q a,
  admissible Env (Rfun Env l A A' a Q).
Proof.
  intros Env l A A' Q a.
  intros v v' R x y Frx Frx' Fry.
    destruct (x==y); subst.
      rewrite subst_ee_id. rewrite subst_ee_id. auto.

    destruct R as [lEnv [lEq [Typingv [Typingv' [Typingf Bee]]]]].
    exists (subst_atom_lenv lEnv x y).
    assert (x `notin` dom Env) as xnEnv.
      apply typing_ldom in Typingv.
      rewrite Typingv in Frx.
      apply typing_regular in Typingv'.
      decompose [and] Typingv'. clear Typingv'.
      apply disjoint_wf_lenv in H1.
      clear Frx' Fry H H0 H3. solve_uniq.
    assert (y `notin` dom Env) as ynEnv.
      destruct_notin; auto.
        fsetdec.
    assert (y `notin` dom lEnv) as ynlEnv.
      apply typing_ldom in Typingv.
      rewrite <- Typingv. clear Typingv.
      destruct_notin; auto.
        contradict NotInTac; auto.
    split. rewrite <- renaming_length; auto.
    split. apply typing_lin_renaming; auto.
    split. apply typing_lin_renaming; auto.
    split; auto.
      apply bee_lin_renaming with (x:=x) (y:=y) in Bee; auto.
        simpl in Bee. 
        rewrite <- subst_ee_fresh in Bee; auto.
          apply notin_fv_ee_typing with (y:=x) in Typingf; auto.
Qed.

Lemma Rfun_wfor : forall Env l A A' K Q a,
  wf_typ Env A K -> 
  wf_typ Env A' K -> 
  wfor Env (Rfun Env l A A' a Q) A A' K.
Proof.
  intros.
  split; auto.
  split; auto.
    apply Rfun_admissible.
Qed.

Lemma Rid_admissible : forall Env l A,
  admissible Env (Rid Env l A).
Proof.
  intros Env l A.
  intros v v' R x y Frx Frx' Fry.
    destruct (x==y); subst.
      rewrite subst_ee_id. rewrite subst_ee_id. auto.

    destruct R as [lEnv [lEq [Typingv [Typingv' Bee]]]].
    exists (subst_atom_lenv lEnv x y).
    assert (x `notin` dom Env) as xnEnv.
      apply typing_ldom in Typingv.
      rewrite Typingv in Frx.
      apply typing_regular in Typingv'.
      decompose [and] Typingv'. clear Typingv'.
      apply disjoint_wf_lenv in H1.
      clear Frx' Fry H0 H H3. solve_uniq.
    assert (y `notin` dom Env) as ynEnv.
      destruct_notin; auto.
        fsetdec.
    assert (y `notin` dom lEnv) as ynlEnv.
      apply typing_ldom in Typingv.
      rewrite <- Typingv. clear Typingv.
      destruct_notin; auto.
        contradict NotInTac; auto.
    split. rewrite <- renaming_length; auto.
    split. apply typing_lin_renaming; auto.
    split. apply typing_lin_renaming; auto.
      apply bee_lin_renaming with (x:=x) (y:=y) in Bee; auto.
Qed.

Lemma Rid_wfor : forall Env l A K,
  wf_typ Env A K -> 
  wfor Env (Rid Env l A) A A K.
Proof.
  intros.
  split; auto.
  split; auto.
    apply Rid_admissible.
Qed.

(***************************************************************)
(*                 Fundamental Parametricity                            *)
(***************************************************************)
Corollary fundamental_oparametricity: forall e t Env,
   typing nil nil e t ->
   wf_env Env ->
   F_Related_oterms t rho_nil delta_nil delta_nil e e Env nil.
Proof.
  intros.
  assert (apply_delta_subst delta_nil (apply_gamma_subst gamma_nil (apply_gamma_subst gamma_nil e)) = e) as Heq; auto.
  rewrite <- Heq.
  eapply oparametricity; eauto.
Qed.

(***************************************************************)
(*                             Termination                                          *)
(***************************************************************)
Lemma otermination : forall e t dsubst dsubst' gsubst gsubst' rsubst Env lEnv,
   F_Related_oterms t rsubst dsubst dsubst'
                                 (apply_delta_subst dsubst (apply_gamma_subst gsubst e))
                                 (apply_delta_subst dsubst' (apply_gamma_subst gsubst' e)) Env lEnv ->
   exists v, exists v', 
     normalize (apply_delta_subst dsubst (apply_gamma_subst gsubst e)) v /\
     normalize (apply_delta_subst dsubst' (apply_gamma_subst gsubst' e)) v' /\
     F_Related_ovalues t rsubst dsubst dsubst' v v' Env lEnv.
Proof.
  intros e t dsubst dsubst' gsubst gsubst' rsubst Env lEnv Hrel.
  destruct Hrel as [v [v' Hrel]]. decompose [and] Hrel.
  exists (v). exists (v').
  split; auto.
Qed.

Corollary strong_normalization : forall e t,
   typing nil nil e t ->
   exists v, normalize e v. 
Proof.
  intros e t Typ.
  apply fundamental_oparametricity with (Env:=nil) in Typ; auto.
  destruct Typ as [v [v' [H1 [H2 [H3 [H4 H5]]]]]].
  exists v. auto.
Qed.  

(***************************************************************)
(*                             Identification                                         *)
(***************************************************************)
(* 
  \I : \X. X-> X. \A. \A'. \a: A-> A'. a I[A] = I[A'] a

  The above lemma implies the polymophic function I can only be 
  identity function. This can be proved by contradiction.

  The definition of identity function is
    \X. \v:X. I[X]v = v,  where '=' should be the beta-eta-equivalence.
  The negation of the above defn is 
    ex X, ex v:X, I[X]v <> v

  If I is not an identity function, without lose of generality, suppose
       exist X0, exists v0:X0, s.t. I[X0] v0 = v' <> v0
  We can pick a function a:X0->X0 which is defined as
    a[u] = v0 if u = v'
    a[u] = u otherwise
  then, 
     a I[X0] v0 = a (I[X0] v0) = a v' = v0
     I[X0] a v0 = I[X0] (a v0) = I[X0] v0 = v'
  We proved a I[X0] v0 <> I[X0] a v0 since v0 <> v',
  but this is contradictary to 
     \I : \X. X-> X. \A. \A'. \a: A-> A'. a I[A] = I[A'] a
   which we are proving below.

  So I can only be an identity function.
*)
Lemma Identification : forall Id A A' Q K, 
  typing nil nil Id (typ_all Q (typ_arrow K (typ_bvar 0) (typ_bvar 0))) ->
  (forall x y R, exists X,
   wfor nil R A A' Q ->
   F_Related_oterms (typ_fvar X)
                                 ([(X,R)])
                                 ([(X,A)])
                                 ([(X,A')])
                                  x y nil nil ->
   F_Related_oterms (typ_fvar X)
                                 ([(X,R)])
                                 ([(X,A)])
                                 ([(X,A')])
                                 (exp_app (exp_tapp Id A) x) (exp_app (exp_tapp Id A') y) nil nil).
Proof.
  intros Id A A' Q K Htyping x y R.
  assert (wf_typ nil (typ_all Q (typ_arrow K (typ_bvar 0) (typ_bvar 0))) kn_lin) as WFT.
    apply typing_regular in Htyping. decompose [and] Htyping; auto.

  assert (F_Related_oterms (typ_all Q (typ_arrow K (typ_bvar 0) (typ_bvar 0))) rho_nil delta_nil delta_nil Id Id nil nil) as Forel_All.
    apply fundamental_oparametricity; auto.
  destruct Forel_All as [v [v' [Htypingid [Htypingid' [Hn [Hn' Forel_All]]]]]].

  apply F_Related_ovalues_all_leq in Forel_All.
  destruct Forel_All as [Hv [Hv' [L' Hall]]]; subst.

  pick fresh X. 
  exists (X). intros Hwfor Hterm.
  assert (X `notin` L') as Fr'. auto.
  destruct (@Hall X A A' R Fr') as [w [w' [Hnorm_vt2w [Hnorm_v't2'w' Hrel_wft]]]]; auto.
  unfold open_tt in*. simpl in *.

  assert (wf_typ ((X, bind_kn Q)::nil) (typ_arrow K (typ_fvar X) (typ_fvar X)) K) as WFT'.
    eapply wf_typ_arrow; eauto.

  apply F_Related_ovalues_arrow_leq in Hrel_wft.
  destruct Hrel_wft as [Hw [Hw' [L Harrow]]]; subst.
  simpl_env in *. 
  assert ((if X==X then A else typ_fvar X) = A) as Heq.
    destruct (X==X); auto. contradict n; auto.
  assert ((if X==X then A' else typ_fvar X) = A') as Heq'.
    destruct (X==X); auto. contradict n; auto.
  simpl in *.
  rewrite Heq in *. rewrite Heq' in *. clear Heq Heq'.

  destruct Hterm as [v0 [v'0 [Htypingv0 [Htypingv'0 [Hnorm [Hnorm' Hrel]]]]]]; subst.

  destruct (@Harrow nil v0 v'0) as [u [u' [Hn_wxu [Hn_w'x'u' Hrel_wft2]]]]; auto.
    simpl in Htypingv0.
    assert ((if X==X then A else typ_fvar X) = A).
      destruct (X==X); auto. contradict n; auto.
    rewrite H in Htypingv0.
    eapply preservation_normalization; eauto.

    simpl in Htypingv'0.
    assert ((if X==X then A' else typ_fvar X) = A').
      destruct (X==X); auto. contradict n; auto.
    rewrite H in Htypingv'0.
    eapply preservation_normalization; eauto.

    apply disjdom_sym_1.
    apply disjdom_nil_1.

  assert (normalize (exp_tapp Id A) w).
      apply congr_tapp with (v1:=v); auto.
      eapply type_from_wf_typ with (E:=@nil (atom*binding)); eauto using wfor_left_inv.

  assert (normalize (exp_tapp Id A') w').
      apply congr_tapp with (v1:=v'); auto.
      eapply type_from_wf_typ with (E:=@nil (atom*binding)); eauto using wfor_right_inv.
    
  assert (normalize (exp_app (exp_tapp Id A) x) u).
      apply congr_app with (v1:=w) (v2:=v0); auto.
        apply expr_tapp; auto.
          eapply type_from_wf_typ; eauto using wfor_left_inv.

  assert (normalize (exp_app (exp_tapp Id A') y) u').
      apply congr_app with (v1:=w') (v2:=v'0); auto.
        apply expr_tapp; auto.
          eapply type_from_wf_typ; eauto using wfor_right_inv.

  unfold F_Related_oterms. exists(u). exists(u').
    split; simpl.
    destruct (X==X); try solve [contradict n; auto].
    apply typing_app with (T1:=A) (K:=K) (D1:=nil) (D2:=nil); auto.
      assert (open_tt (typ_arrow K (typ_bvar 0) (typ_bvar 0)) A = typ_arrow K A A) as Heq.
        unfold open_tt. auto.
      rewrite <- Heq.
      eapply typing_tapp; eauto using wfor_left_inv.
        simpl in Htypingv0.
        assert ((if X==X then A else typ_fvar X) = A) as Heq.
          destruct (X==X); auto. contradict n; auto.
        rewrite Heq in Htypingv0.
        assumption.

    split; simpl.
    destruct (X==X); try solve [contradict n; auto].
    eapply typing_app with (T1:=A')(K:=K) (D1:=nil) (D2:=nil); auto.
      assert (open_tt (typ_arrow K (typ_bvar 0) (typ_bvar 0)) A' = typ_arrow K A' A') as Heq.
        unfold open_tt. auto.
      rewrite <- Heq.
      eapply typing_tapp; eauto using wfor_right_inv.
        simpl in Htypingv'0.
        assert ((if X==X then A' else typ_fvar X) = A') as Heq.
          destruct (X==X); auto. contradict n; auto.
        rewrite Heq in Htypingv'0.
        assumption.

    split; auto.
Qed.

Corollary Rearrangement_Identification : forall Id a A A' K, 
  typing nil nil Id (typ_all kn_lin (typ_arrow K (typ_bvar 0) (typ_bvar 0))) ->
  typing nil nil a (typ_arrow K A A') ->
  (forall x, 
    typing nil nil x A ->
    Rfun nil 0 A A' a K (exp_app (exp_tapp Id A) x) (exp_app (exp_tapp Id A') (exp_app a x))
  ).
Proof.
  intros Id a A A' K Htypingid Htypinga x Htypingx.
  assert (exists x0, normalize x x0) as Hn_xx0.
    apply strong_normalization with (t:=A); auto.
  assert  (exists x'0, normalize (exp_app a x) x'0) as Hn_axx'0.
    apply strong_normalization with (t:=A'); auto.
      eapply typing_app with (T1:=A); eauto.

  assert (wf_typ nil A kn_lin) as HwftA. auto.
  assert (wf_typ nil A' kn_lin) as HwftA'. 
    apply typing_regular in Htypinga. decompose [and] Htypinga.
    apply wft_arrow_inv in H3. destruct H3; auto.
  destruct (@Identification Id A A' kn_lin K Htypingid x (exp_app a x) (Rfun nil 0 A A' a K)) as [X JJ].

  (* x and  (exp_app a x) are related as Rfun*)
  assert (wf_typ ((X, bind_kn kn_lin)::nil) (typ_fvar X) kn_lin) as WFT.
    apply wf_typ_var; unfold binds; simpl; auto.

  destruct Hn_xx0 as [x0 [Hbrc_xx0 Hx0]]. 
  destruct Hn_axx'0 as [x'0 [Hbrc_axx'0 Hx'0]].
  assert (F_Related_oterms (typ_fvar X) 
                                 ([(X,(Rfun nil 0 A A' a K))])
                                 ([(X, A)])
                                 ([(X, A')])
                                  x (exp_app a x) nil nil).
    Case "Fterms".
    exists (x0). exists (x'0).
      split; simpl.
      SCase "Typing".
      destruct (X==X); auto; contradict n; auto.
    
      split; simpl.
      SCase "Typing".
      destruct (X==X).
        apply typing_app with (T1:=A) (D1:=nil) (D2:=nil) (K:=K); auto.
        contradict n; auto.

      unfold normalize.
      split; auto.
      split; auto.
      SCase "Fvalues".
        apply F_Related_ovalues_fvar_req. simpl.
        exists(Rfun nil 0 A A' a K).
        repeat(split; auto).
           SSCase "admin". apply Rfun_admissible.

           exists nil.
           repeat(split; auto).
           SSCase "Typing".
           destruct (X==X); try solve [contradict n; auto].
             apply preservation_normalization with (e:=x); auto.
               unfold normalize; auto.
           SSCase "Typing".
           destruct (X==X); try solve [contradict n; auto].
             apply preservation_normalization with (e:=exp_app a x); auto.
               apply typing_app with (T1:=A)(D1:=nil) (D2:=nil) (K:=K); auto.
                 unfold normalize; auto.
           SSCase "Beta-Eta-Equivalence".
           apply bee_trans with (e':=(exp_app a x)); eauto.
     
  (* Id[A] x and  Id[A'] (exp_app a x) are related as Rfun*)
  apply JJ in H; auto using Rfun_wfor.
  subst.
  destruct H as [v [v' [Htypingv [Htypingv' [[Hbrc Hv] [[Hbrc' Hv'] [R [Hb [_ [_ [Hadmin Hrel]]]]]]]]]]]; subst.
  unfold Rfun.
  assert ((if X==X then A else typ_fvar X) = A) as HeqA.
    destruct (X==X); auto. contradict n; auto.
  assert ((if X==X then A' else typ_fvar X) = A') as HeqA'.
    destruct (X==X); auto. contradict n; auto.
  simpl in *. simpl_env in *.
  rewrite HeqA in *. rewrite HeqA' in *. clear HeqA HeqA'.
  exists nil.
  repeat(split; auto).
    Case "Beta-Eta-Equivalence".
    analyze_binds Hb; subst.
    destruct Hrel as [lEnv Hrel].
    decompose [and] Hrel.
    unfold Rfun in Hrel. decompose [and] Hrel.
    apply zero_length__lempty in H. subst lEnv.
    apply bee_trans with (e':=exp_app a v).
      eapply bee_congr_app; eauto using bee_refl.
      apply bee_trans with (e':=v'); auto.
Qed.

Corollary EQ_Identification : forall Id K, 
  typing nil nil Id (typ_all kn_lin (typ_arrow K (typ_bvar 0) (typ_bvar 0))) ->
  (forall x y A, 
    Rid nil 0 A x y -> 
    Rid nil 0 A (exp_app (exp_tapp Id A) x) (exp_app (exp_tapp Id A) y)
  ).
Proof.
  intros Id K Htypingid x y A HRid.
  unfold Rid in *. destruct HRid as [lEnv [lEq [Htypingx [Htypingy Heq_xy]]]].
  apply zero_length__lempty in lEq. subst lEnv.
  assert (exists x0, normalize x x0) as Hn_xx0.
    apply strong_normalization with (t:=A); auto.
  assert (exists y0, normalize y y0) as Hn_yy0.
    apply strong_normalization with (t:=A); auto.
  destruct Hn_xx0 as [x0 [Hbrc_xx0 Hx0]].
  destruct Hn_yy0 as [y0 [Hbrc_yy0 Hy0]].
  destruct (@Identification Id A A kn_lin K Htypingid x y (Rid nil 0 A)) as [X JJ].
  
  assert (wf_typ ((X, bind_kn kn_lin)::nil) (typ_fvar X) kn_lin) as WFT.
    apply wf_typ_var.
       unfold binds. simpl. auto. 
       simpl_env. apply binds_one_3; auto.

  assert (F_Related_oterms (typ_fvar X) 
                                 ([(X,(Rid nil 0 A))])
                                 ([(X, A)])
                                 ([(X, A)])
                                  x y nil nil).
    unfold F_Related_oterms. exists (x0). exists (y0).
      unfold normalize.
      split; simpl.
      destruct (X==X); auto; try solve [contradict n; auto].    
      split; simpl.
      destruct (X==X); auto; try solve [contradict n; auto].
      split; auto.
      split; auto.
      apply F_Related_ovalues_fvar_req. simpl.
      exists(Rid nil 0 A).
      repeat(split; auto).
         apply Rid_admissible.
         exists nil.
         repeat(split; auto).
         destruct (X==X); try solve [contradict n; auto].
           apply preservation_normalization with (e:=x); auto.
            unfold normalize. auto.
         destruct (X==X); try solve [contradict n; auto].
           apply preservation_normalization with (e:=y); auto.
            unfold normalize. auto.
         apply bee_trans with (e':=x); auto.
            apply bee_trans with (e':=y); eauto.

  apply JJ in H; auto using Rid_wfor. subst.
  destruct H as [v [v' [Htypingv [Htypingv' [[Hbrc Hv] [[Hbrc' Hv'] [R [Hb [_ [_ Hrel]]]]]]]]]]; subst.
  assert ((if X==X then A else typ_fvar X) = A) as HeqA.
    destruct (X==X); auto. contradict n; auto.
  simpl in *. simpl_env in *.
  rewrite HeqA in *. clear HeqA.
  exists nil.
  repeat(split; auto). 
    eapply bee_congr_app with (K:=K); eauto.
      assert (open_tt (typ_arrow K (typ_bvar 0) (typ_bvar 0)) A = typ_arrow K A A) as Heq.
        unfold open_tt. auto.
      rewrite <- Heq.
      eapply typing_tapp; eauto.
        apply typing_regular in Htypingx. 
        decompose [and] Htypingx; auto.
Qed.

(***************************************************************)
(*                             Boolean Function                                *)
(***************************************************************)
(* 
  \B : \X. X->X-> X. 
     \A. \A'. \a: A-> A'. 
          \t: A. \f: A.
           a (B[A] t f)  = B[A'] (a t) (a f)

  The above lemma implies the polymophic function B can only be 
  Boolean function. This can be proved by contradiction.

  The definition of Boolean function is
    \X. \t:X. \f:X. B[X] t f = t \/ B[X] t f = f ,  
    where '=' should be the beta-eta-equivalence.
  The negation of the above defn is 
    ex X, ex t:X, ex f:X, B[X] t f <> t /\ B[X] t f <> f ,  

  If B is not an identity function, without lose of generality, suppose
    ex X0, ex t0:X0, ex f0:X0, B[X0] t0 f0 = v /\ v <> t0 /\ v <> f0,  

  We can pick a function a:X0->X0 which is defined as
    a[u] = t0 if u = v
    a[u] = u otherwise
  then, 
     a (B[X0] t0 f0) = a v = t0
     I[X0] (a t0) (a f0)= I[X0] t0 f0 = v
  We proved a (B[X0] t0 f0) <> I[X0] (a t0) (a f0) since t0 <> v,
  but this is contradictary to 
  \B : \X. X->X-> X. 
     \A. \A'. \a: A-> A'. 
          \t: A. \f: A.
           a (B[A] t f)  = B[A'] (a t) (a f)
   which we are proving below.

  So B can only be an boolean function.
*)
Lemma CBoolean : forall CBool A A' Q K K', 
  typing nil nil CBool (typ_all Q (typ_arrow K (typ_bvar 0) (typ_arrow K' (typ_bvar 0) (typ_bvar 0)))) ->
  (forall t1 t2 f1 f2 R, exists X, 
   wfor nil R A A' Q->
   F_Related_oterms (typ_fvar X) 
                                 ([(X,R)])
                                 ([(X,A)])
                                 ([(X,A')])
                                 t1 t2 nil nil ->
   F_Related_oterms (typ_fvar X) 
                                 ([(X,R)])
                                 ([(X,A)])
                                 ([(X,A')])
                                 f1 f2 nil nil ->
   F_Related_oterms (typ_fvar X) 
                                 ([(X,R)])
                                 ([(X,A)])
                                 ([(X,A')])
                                 (exp_app (exp_app (exp_tapp CBool A) t1) f1) 
                                 (exp_app (exp_app (exp_tapp CBool A') t2) f2) nil nil).
Proof.
  intros CBool A A' Q K K' Htyping_bool t1 t2 f1 f2 R.
  assert (wf_typ nil (typ_all Q (typ_arrow K (typ_bvar 0) (typ_arrow K' (typ_bvar 0) (typ_bvar 0)))) K) as WFT.
    apply wf_typ_all with (L:={}).
      intros X Hfv.
      unfold open_tt. simpl. simpl_env. 
      eapply wf_typ_arrow with (K1:=Q)(K2:=K'); eauto.
        eapply wf_typ_arrow; eauto.

  assert (F_Related_oterms (typ_all Q (typ_arrow K (typ_bvar 0) (typ_arrow K' (typ_bvar 0) (typ_bvar 0)))) rho_nil delta_nil delta_nil CBool CBool nil nil) as Forel_All.
    apply fundamental_oparametricity; auto.
  destruct Forel_All as [v [v' [Htypingid [Htypingid' [Hn [Hn' Forel_All]]]]]].

  apply F_Related_ovalues_all_leq in Forel_All.
  destruct Forel_All as [Hv [Hv' [L' Hall]]]; subst.

  pick fresh X. 
  exists (X). intros Hwfor Htermt Htermf.
  assert (wf_typ [(X,bind_kn Q)] (typ_fvar X) Q) as WFTvar. auto.
  assert (X `notin` L') as Fr'. auto.
  destruct (@Hall X A A' R Fr') as [w [w' [Hnorm_vt2w [Hnorm_v't2'w' Hrel_wft]]]]; auto.
  unfold open_tt in*. simpl in *.

  assert (wf_typ ((X, bind_kn Q)::nil) (typ_arrow K (typ_fvar X) (typ_arrow K' (typ_fvar X) (typ_fvar X))) K) as WFT'; eauto.

  apply F_Related_ovalues_arrow_leq in Hrel_wft.
  destruct Hrel_wft as [Hw [Hw' [Lt Harrow]]]; subst.
  simpl_env in *.
  assert ((if X==X then A else typ_fvar X) = A) as Heq.
    destruct (X==X); auto. contradict n; auto.
  assert ((if X==X then A' else typ_fvar X) = A') as Heq'.
    destruct (X==X); auto. contradict n; auto.
  simpl in *.
  rewrite Heq in *. rewrite Heq' in *. clear Heq Heq'.

  destruct Htermt as [v0 [v'0 [Htypingv0 [Htypingv'0 [Hnorm [Hnorm' Hrelt]]]]]]; subst.
  destruct (@Harrow nil v0 v'0) as [u [u' [Hn_wxu [Hn_w'x'u' Hrel_wft2]]]]; auto.
    simpl in Htypingv0.
    assert ((if X==X then A else typ_fvar X) = A).
      destruct (X==X); auto. contradict n; auto.
    rewrite H in Htypingv0.
    eapply preservation_normalization; eauto.

    simpl in Htypingv'0.
    assert ((if X==X then A' else typ_fvar X) = A').
      destruct (X==X); auto. contradict n; auto.
    rewrite H in Htypingv'0.
    eapply preservation_normalization; eauto.

    apply disjdom_sym_1.
    apply disjdom_nil_1.    

  apply F_Related_ovalues_arrow_leq in Hrel_wft2.
  simpl_env in *.
  destruct Hrel_wft2 as [Hu [Hu' [Lf Harrow']]]; subst.
  assert ((if X==X then A else typ_fvar X) = A) as Heq.
    destruct (X==X); auto. contradict n; auto.
  assert ((if X==X then A' else typ_fvar X) = A') as Heq'.
    destruct (X==X); auto. contradict n; auto.
  simpl in *.
  rewrite Heq in *. rewrite Heq' in *. clear Heq Heq'.

  destruct Htermf as [v1 [v'1 [Htypingv1 [Htypingv'1 [Hnorm1 [Hnorm1' Hrelf]]]]]]; subst.
  destruct (@Harrow' nil v1 v'1) as [x [x' [Hn_uxu0 [Hn_u'x'u'0 Hrel_wft22]]]]; auto.
    simpl in Htypingv1.
    assert ((if X==X then A else typ_fvar X) = A).
      destruct (X==X); auto. contradict n; auto.
    rewrite H in Htypingv1.
    eapply preservation_normalization; eauto.

    simpl in Htypingv'1.
    assert ((if X==X then A' else typ_fvar X) = A').
      destruct (X==X); auto. contradict n; auto.
    rewrite H in Htypingv'1.
    eapply preservation_normalization; eauto.

    apply disjdom_sym_1.
    apply disjdom_nil_1.    

  assert (wf_typ nil A Q) as wft_A.
      apply wfor_left_inv in Hwfor; auto.

  assert (type A) as TypeA. eauto using type_from_wf_typ.

  assert (wf_typ nil A' Q) as wft_A'.
      apply wfor_right_inv in Hwfor; auto.

  assert (type A') as TypeA'. eauto using type_from_wf_typ.

  assert (normalize (exp_tapp CBool A) w).
      apply congr_tapp with (v1:=v); auto.

  assert (normalize (exp_tapp CBool A') w').
      apply congr_tapp with (v1:=v'); auto.
    
  assert (normalize (exp_app (exp_tapp CBool A) t1) u).
      apply congr_app with (v1:=w) (v2:=v0); auto.

  assert (normalize (exp_app (exp_tapp CBool A') t2) u').
      apply congr_app with (v1:=w') (v2:=v'0); auto.

  assert (normalize (exp_app (exp_app (exp_tapp CBool A) t1) f1) x).
      apply congr_app with (v1:=u) (v2:=v1); auto. 

  assert (normalize (exp_app (exp_app (exp_tapp CBool A') t2) f2) x').
      apply congr_app with (v1:=u') (v2:=v'1); auto.

  unfold F_Related_oterms. exists (x). exists (x').
    split; simpl.
    destruct (X==X); try solve [contradict n; auto].
    apply typing_app with (T1:=A)(D1:=nil) (D2:=nil) (K:=K'); auto.
      apply typing_app with (T1:=A)(D1:=nil) (D2:=nil) (K:=K); auto.
        assert (open_tt (typ_arrow K (typ_bvar 0) (typ_arrow K' (typ_bvar 0) (typ_bvar 0))) A = typ_arrow K A (typ_arrow K' A A)) as Heq.
          unfold open_tt. auto.
        rewrite <- Heq.
        apply typing_tapp with (K:=Q); auto.

        simpl in Htypingv1.
        assert ((if X==X then A else typ_fvar X) = A) as Heq.
          destruct (X==X); auto; contradict n; auto.
        rewrite Heq in Htypingv1; auto.

    split; simpl.
    destruct (X==X); try solve [contradict n; auto].
    apply typing_app with (T1:=A')(D1:=nil) (D2:=nil) (K:=K'); auto.
      apply typing_app with (T1:=A')(D1:=nil) (D2:=nil) (K:=K); auto.
        assert (open_tt (typ_arrow K (typ_bvar 0) (typ_arrow K' (typ_bvar 0) (typ_bvar 0))) A' = typ_arrow K A' (typ_arrow K' A' A')) as Heq.
          unfold open_tt. auto.
        rewrite <- Heq.
        apply typing_tapp with (K:=Q); auto.

        simpl in Htypingv'1.
        assert ((if X==X then A' else typ_fvar X) = A') as Heq.
          destruct (X==X); auto; contradict n; auto.
        rewrite Heq in Htypingv'1; auto.

    split; auto.
Qed.

Corollary Rearrangement_CBoolean : forall CBool a A A' K K' Q, 
  typing nil nil CBool (typ_all kn_lin (typ_arrow K (typ_bvar 0) (typ_arrow K' (typ_bvar 0) (typ_bvar 0)))) ->
  typing nil nil a (typ_arrow Q A A') ->
  (forall t f, 
    typing nil nil t A -> 
    typing nil nil f A -> 
    Rfun nil 0 A A' a Q (exp_app (exp_app (exp_tapp CBool A) t) f) (exp_app (exp_app (exp_tapp CBool A') (exp_app a t)) (exp_app a f))
  ).
Proof.
  intros CBool a A A' K K' Q Htypingid Htypinga t f 
    Htypingt Htypingf.
  assert (exists t0, normalize t t0) as Hn_tt0.
    apply strong_normalization with (t:=A); auto.
  assert (exists t'0, normalize (exp_app a t) t'0) as  Hn_att'0.
    apply strong_normalization with (t:=A'); auto.
      eapply typing_app with (T1:=A); eauto.
  assert (exists f0, normalize f f0) as  Hn_ff0.
    apply strong_normalization with (t:=A); auto.
  assert (exists f'0, normalize (exp_app a f) f'0) as  Hn_aff'0.
    apply strong_normalization with (t:=A'); auto.
      eapply typing_app with (T1:=A); eauto.
  assert (wf_typ nil A kn_lin) as HwftA. auto.
  assert (wf_typ nil A' kn_lin) as HwftA'. 
    apply typing_regular in Htypinga. decompose [and] Htypinga.
    apply wft_arrow_inv in H3. destruct H3; auto.
  destruct (@CBoolean CBool A A' kn_lin K K' Htypingid t (exp_app a t) f (exp_app a f) (Rfun nil 0 A A' a Q)) as [X JJ].
  
(**)
  assert (wf_typ ((X, bind_kn kn_lin)::nil) (typ_fvar X) kn_lin) as WFT.
    apply wf_typ_var; unfold binds; simpl; auto.

  destruct Hn_tt0 as [t0 [Hbrc_tt0 Ht0]]. 
  destruct Hn_att'0 as [t'0 [Hbrc_att'0 Ht'0]].
  assert (F_Related_oterms (typ_fvar X)
                                 ([(X,(Rfun nil 0 A A' a Q))])
                                 ([(X, A)])
                                 ([(X, A')])
                                  t (exp_app a t) nil nil).
    unfold F_Related_oterms. exists (t0). exists (t'0).
      split; simpl.
      destruct (X==X); auto; contradict n; auto.
    
      split; simpl.
      destruct (X==X).
        apply typing_app with (T1:=A)(D1:=nil) (D2:=nil) (K:=Q); auto.
        contradict n; auto.

      unfold normalize.
      split; auto.
      split; auto.
        apply F_Related_ovalues_fvar_req. simpl.
        exists(Rfun nil 0 A A' a Q).
        repeat(split; auto).
           apply Rfun_admissible.
           exists nil.
           repeat(split; auto).     
           destruct (X==X); try solve [contradict n; auto].
             apply preservation_normalization with (e:=t); auto.
               unfold normalize; auto.
           destruct (X==X); try solve [contradict n; auto].
             apply preservation_normalization with (e:=exp_app a t); auto.
               apply typing_app with (T1:=A)(D1:=nil) (D2:=nil) (K:=Q); auto.
                 unfold normalize; auto.
           eapply bee_trans with (e':=exp_app a t); eauto.
(**)
     
  destruct Hn_ff0 as [f0 [Hbrc_ff0 Hf0]]. 
  destruct Hn_aff'0 as [f'0 [Hbrc_aff'0 Hf'0]].
  assert (F_Related_oterms (typ_fvar X) 
                                 ([(X,(Rfun nil 0 A A' a Q))])
                                 ([(X, A)])
                                 ([(X, A')])
                                  f (exp_app a f) nil nil).
    unfold F_Related_oterms. exists (f0). exists (f'0).
      split; simpl.
        destruct (X==X); auto; contradict n; auto.    
      split; simpl.
      destruct (X==X).
        apply typing_app with (T1:=A)(D1:=nil) (D2:=nil) (K:=Q); auto.
        contradict n; auto.

      unfold normalize.
      split; auto.
      split; auto.
        apply F_Related_ovalues_fvar_req. simpl.
        exists(Rfun nil 0 A A' a Q).
        repeat(split; auto).
         apply Rfun_admissible.
         exists nil.
         repeat(split; auto).
         destruct (X==X); try solve [contradict n; auto].
            apply preservation_normalization with (e:=f); auto.
               unfold normalize; auto.
         destruct (X==X); try solve [contradict n; auto].
           apply preservation_normalization with (e:=exp_app a f); auto.
             apply typing_app with (T1:=A)(D1:=nil) (D2:=nil) (K:=Q); auto.
             unfold normalize; auto.
         eapply bee_trans with (e':=exp_app a f); eauto.
(**)

  apply JJ in H; auto using Rfun_wfor. subst.
  destruct H as [v [v' [Htypingv [Htypingv' [[Hbrc Hv] [[Hbrc' Hv'] [R [Hb [_ [_ [Hadmin Hrel]]]]]]]]]]]; subst.
  unfold Rfun.
  repeat(split; auto).
    exists nil.
    repeat(split; auto).
    apply typing_app with (T1:=A)(D1:=nil) (D2:=nil) (K:=K'); auto.
      apply typing_app with (T1:=A)(D1:=nil) (D2:=nil) (K:=K); auto.
        assert (open_tt (typ_arrow K (typ_bvar 0) (typ_arrow K' (typ_bvar 0) (typ_bvar 0))) A = typ_arrow K A (typ_arrow K' A A)) as Heq.
          unfold open_tt. auto.
        rewrite <- Heq.
        apply typing_tapp with (K:=kn_lin); auto.
    apply typing_app with (T1:=A')(D1:=nil) (D2:=nil) (K:=K'); auto.
      apply typing_app with (T1:=A')(D1:=nil) (D2:=nil) (K:=K); auto.
        assert (open_tt (typ_arrow K (typ_bvar 0) (typ_arrow K' (typ_bvar 0) (typ_bvar 0))) A' = typ_arrow K A' (typ_arrow K' A' A')) as Heq.
          unfold open_tt. auto.
        rewrite <- Heq.
        apply typing_tapp with (K:=kn_lin); auto.
      apply typing_app with (T1:=A)(D1:=nil) (D2:=nil) (K:=Q); auto.
      apply typing_app with (T1:=A)(D1:=nil) (D2:=nil) (K:=Q); auto.
    assert ((if X==X then A else typ_fvar X) = A) as HeqA.
      destruct (X==X); auto. contradict n; auto.
    assert ((if X==X then A' else typ_fvar X) = A') as HeqA'.
      destruct (X==X); auto. contradict n; auto.
    simpl in *. simpl_env in *.
    rewrite HeqA in *. rewrite HeqA' in *.
    analyze_binds Hb.
    destruct Hrel as [lEnv Hrel].
    unfold Rfun in Hrel.  decompose [and] Hrel. clear Hrel.
    apply zero_length__lempty in H. subst lEnv.
    apply bee_trans with (e':=exp_app a v).
      eapply bee_congr_app; eauto using bee_refl.
      eapply bee_trans with (e':=v'); eauto.
Qed.

Corollary  CBool_Identification : forall CBool K K', 
  typing nil nil CBool (typ_all kn_lin (typ_arrow K (typ_bvar 0) (typ_arrow K' (typ_bvar 0) (typ_bvar 0)))) ->
  (forall t1 t2 f1 f2 A, 
    Rid nil 0 A t1 t2 -> 
    Rid nil 0 A f1 f2 -> 
    Rid nil 0 A (exp_app (exp_app (exp_tapp CBool A) t1) f1) (exp_app (exp_app (exp_tapp CBool A) t2) f2)
  ).
Proof.
  intros CBool K K' Htyping_bool t1 t2 f1 f2 A HRidt HRidf.
  unfold Rid in *. 

  destruct HRidt as [lEnvt [lEqt [Htypingt1 [Htypingt2 Heq_t1t2]]]].
  apply zero_length__lempty in lEqt. subst lEnvt.
  assert (exists vt1, normalize t1 vt1) as Hn_t1vt1.
    apply strong_normalization with (t:=A); auto.
  assert (exists vt2, normalize t2 vt2) as Hn_t2vt2.
    apply strong_normalization with (t:=A); auto.
  destruct Hn_t1vt1 as [vt1 [Hbrc_t1v1 Hvt1]].
  destruct Hn_t2vt2 as [vt2 [Hbrc_t2v2 Hvt2]].

  destruct HRidf as [lEnvf [lEqf [Htypingf1 [Htypingf2 Heq_f1f2]]]].
  apply zero_length__lempty in lEqf. subst lEnvf.
  assert (exists vf1, normalize f1 vf1) as Hn_f1vf1.
    apply strong_normalization with (t:=A); auto.
  assert (exists vf2, normalize f2 vf2) as Hn_f2vf2.
    apply strong_normalization with (t:=A); auto.
  destruct Hn_f1vf1 as [vf1 [Hbrc_f1v1 Hvf1]].
  destruct Hn_f2vf2 as [vf2 [Hbrc_f2v2 Hvf2]].

  destruct (@CBoolean CBool A A kn_lin K K' Htyping_bool t1 t2 f1 f2 (Rid nil 0 A)) as [X JJ]. 
  
  assert (wfor nil (Rid nil 0 A) A A kn_lin) as wfor.
    apply Rid_wfor; auto.

  assert (wf_typ ((X, bind_kn kn_lin)::nil) (typ_fvar X) kn_lin) as WFT.
    apply wf_typ_var.
       unfold binds. simpl. auto. 
       simpl_env. apply binds_one_3; auto.

  assert ((if X==X then A else typ_fvar X) = A) as HeqA.
    destruct (X==X); auto. contradict n; auto.

  assert (F_Related_oterms (typ_fvar X) 
                                 ([(X,(Rid nil 0 A))])
                                 ([(X, A)])
                                 ([(X, A)])
                                  t1 t2 nil nil).
    unfold F_Related_oterms. exists (vt1). exists (vt2).
      unfold normalize.
      split; simpl.
      destruct (X==X); auto; try solve [contradict n; auto].    
      split; simpl.
      destruct (X==X); auto; try solve [contradict n; auto].
      split; auto.
      split; auto.
        apply F_Related_ovalues_fvar_req. simpl.
        exists(Rid nil 0 A).
        repeat(split; auto).
          apply Rid_admissible.
          exists nil. repeat(split; auto).
          destruct (X==X); try solve [contradict n; auto].
            apply preservation_normalization with (e:=t1); auto.
              unfold normalize. auto.
          destruct (X==X); try solve [contradict n; auto].
           apply preservation_normalization with (e:=t2); auto.
              unfold normalize. auto.
          apply bee_trans with (e':=t1); auto.
             apply bee_trans with (e':=t2); auto.

  assert (F_Related_oterms (typ_fvar X) 
                                 ([(X,(Rid nil 0 A))])
                                 ([(X, A)])
                                 ([(X, A)])
                                  f1 f2 nil nil).
    unfold F_Related_oterms. exists (vf1). exists (vf2).
      unfold normalize.
      split; simpl.
      destruct (X==X); auto; try solve [contradict n; auto].    
      split; simpl.
      destruct (X==X); auto; try solve [contradict n; auto].
      split; auto.
      split; auto.
        apply F_Related_ovalues_fvar_req. simpl.
        exists(Rid nil 0 A).
        repeat(split; auto).
          apply Rid_admissible.
          exists nil. repeat(split; auto).
          destruct (X==X); try solve [contradict n; auto].
            apply preservation_normalization with (e:=f1); auto.
               unfold normalize. auto.
          destruct (X==X); try solve [contradict n; auto].
             apply preservation_normalization with (e:=f2); auto.
               unfold normalize. auto.
          apply bee_trans with (e':=f1); auto.
              apply bee_trans with (e':=f2); auto.

  apply JJ in H; auto using Rid_wfor.
  destruct H as [v [v' [Htypingv [Htypingv' [[Hbrc Hv] [[Hbrc' Hv'] [R [Hb [_ [_ [Hadmin Hrel]]]]]]]]]]].
  exists nil. repeat(split; auto).
    apply typing_app with (T1:=A)(D1:=nil) (D2:=nil) (K:=K'); auto.
      apply typing_app with (T1:=A)(D1:=nil) (D2:=nil) (K:=K); auto.
        assert (open_tt (typ_arrow K (typ_bvar 0) (typ_arrow K' (typ_bvar 0) (typ_bvar 0))) A = typ_arrow K A (typ_arrow K' A A)) as Heq.
          unfold open_tt. auto.
        rewrite <- Heq.
        apply typing_tapp with (K:=kn_lin) ; auto.
    apply typing_app with (T1:=A)(D1:=nil) (D2:=nil) (K:=K'); auto.
      apply typing_app with (T1:=A)(D1:=nil) (D2:=nil) (K:=K); auto.
        assert (open_tt (typ_arrow K (typ_bvar 0) (typ_arrow K' (typ_bvar 0) (typ_bvar 0))) A = typ_arrow K A (typ_arrow K' A A)) as Heq.
          unfold open_tt. auto.
        rewrite <- Heq.
        apply typing_tapp with (K:=kn_lin) ; auto.
    analyze_binds Hb.
    destruct Hrel as [lEnv Hrel].
    decompose [and] Hrel. clear Hrel.
    apply zero_length__lempty in H. subst lEnv.
    simpl in *. simpl_env in *. rewrite HeqA in *. 
    apply bee_trans with (e':=v); auto.
      apply bee_trans with (e':=v'); auto.
Qed.

(***************************************************************)
(*               Open Identification                           *)
(***************************************************************)

Lemma lenv_split_left_empty: forall G E,
  wf_lenv G E ->  
  lenv_split G lempty E E.
Proof.
  intros G E H.
  induction H; auto.
Qed.

Lemma lenv_split_right_empty: forall G E,
  wf_lenv G E ->  
  lenv_split G E lempty E.
Proof.
  intros G E H.
  induction H; auto.
Qed.
    
Lemma expr_renaming': forall e1 asubst,
  expr e1 ->
  expr (subst_atoms_exp asubst e1).
Proof.
  intros e1 asubst Expr.
  generalize dependent e1.
  induction asubst; intros; simpl; auto.
    destruct a.
    apply IHasubst.
    apply subst_ee_expr; auto.
Qed.  

Lemma value_renamings': forall e1 asubst,
  value e1 ->
  value (subst_atoms_exp asubst e1).
Proof.
  intros e1 asubst Val.
  generalize dependent e1.
  induction asubst; intros; simpl; auto.
    destruct a.
    apply IHasubst.
    apply value_through_subst_ee with (x:=a) (u:=a0) in Val; auto.
Qed.  

Lemma OIdentification : forall Id A A' Q K E lE v0 v'0 R,
  typing nil nil Id (typ_all Q (typ_arrow K (typ_bvar 0) (typ_bvar 0))) ->
  wfor E R A A' Q ->
  value v0 ->
  value v'0 ->
  typing E lE v0 A ->
  typing E lE v'0 A' ->   
  exists X,
   wf_typ ([(X, bind_kn Q)]) (typ_fvar X) Q ->
   F_Related_ovalues (typ_fvar X)
                                 ([(X,R)])
                                 ([(X,A)])
                                 ([(X,A')])
                                  v0 v'0 E lE ->
   F_Related_oterms (typ_fvar X)
                                 ([(X,R)])
                                 ([(X,A)])
                                 ([(X,A')])
                                 (exp_app (exp_tapp Id A) v0) (exp_app (exp_tapp Id A') v'0) E lE.
Proof.
  intros Id A A' Q K E lE v0 v'0 R Htyping Hwfor Hv0 Hv'0 Htypingv0 Htypingv'0.
  assert (wf_typ nil (typ_all Q (typ_arrow K (typ_bvar 0) (typ_bvar 0))) kn_lin) as WFT.
    apply typing_regular in Htyping. decompose [and] Htyping; auto.

  assert (F_Related_oterms (typ_all Q (typ_arrow K (typ_bvar 0) (typ_bvar 0))) rho_nil delta_nil delta_nil Id Id E nil) as Forel_All.
    apply fundamental_oparametricity; auto.
  destruct Forel_All as [v [v' [Htypingid [Htypingid' [Hn [Hn' Forel_All]]]]]].

  apply F_Related_ovalues_all_leq in Forel_All.
  destruct Forel_All as [Hv [Hv' [L' Hall]]]; subst.

  pick fresh X. 
  exists (X). intros WFTvar Hrel.
  assert (X `notin` L') as Fr'. auto.
  destruct (@Hall X A A' R Fr') as [w [w' [Hnorm_vt2w [Hnorm_v't2'w' Hrel_wft]]]]; auto.
  unfold open_tt in*. simpl in *.

  assert (wf_typ ((X, bind_kn Q)::nil) (typ_arrow K (typ_fvar X) (typ_fvar X)) K) as WFT'.
    eapply wf_typ_arrow; eauto.

  apply F_Related_ovalues_arrow_leq in Hrel_wft.
  destruct Hrel_wft as [Hw [Hw' [L Harrow]]]; subst.
  simpl_env in *. 
  assert ((if X==X then A else typ_fvar X) = A) as Heq.
    destruct (X==X); auto. contradict n; auto.
  assert ((if X==X then A' else typ_fvar X) = A') as Heq'.
    destruct (X==X); auto. contradict n; auto.
  simpl in *.
  rewrite Heq in *. rewrite Heq' in *. clear Heq Heq'.

   assert (uniq lE) as Uniq.
     apply typing_regular in Htypingv0. destruct Htypingv0 as [JJ1 [JJ2 [JJ3 JJ4]]].
     apply uniq_from_wf_lenv in JJ2; auto.
  assert (disjoint E lE) as Disj'.
     apply typing_regular in Htypingv0. destruct Htypingv0 as [JJ1 [JJ2 [JJ3 JJ4]]].
     apply disjoint_wf_lenv in JJ2; auto.
  assert (JJ:=@pick_lenv (L `union` L' `union` {{X}}  `union` dom E) lE Uniq).
  destruct JJ as [asubst [Wfa [lE_eq_asubst Disj]]].
  assert (disjoint asubst E) as Disj''.
     apply disjoint_eq with (D1:=lE); auto.
  assert (disjdom (atom_subst_codom asubst) (union (dom E) (dom lE))) as Disj'''.
     eapply  disjdom_app_r.
     split.
       apply disjdom_sym_1 in Disj.
       apply disjdom_sub with (D2:=dom E) in Disj; auto.
         apply disjdom_sym_1; auto.
         clear Harrow Uniq Disj Hall Fr Fr' Disj' lE_eq_asubst Disj'' WFT'.
         fsetdec.
       apply disjdom_eq with (D1:=dom asubst); auto.
         apply wf_asubst_dom_codom_disjoint; auto.
         rewrite  lE_eq_asubst. clear lE_eq_asubst.  
         clear. fsetdec. 
  destruct (@Harrow (subst_atoms_lenv asubst lE) (subst_atoms_exp asubst v0) (subst_atoms_exp asubst v'0)) as [u [u' [Hn_wxu [Hn_w'x'u' Hrel_wft2]]]]; auto.
     apply typing_lin_renamings; auto.
     apply typing_lin_renamings; auto.
     simpl_env.  apply wf_lenv_renamings; auto.

     assert (J:=@subst_atoms_lenv__dom_eq asubst lE Wfa Uniq lE_eq_asubst).
     apply disjdom_sym_1 in Disj.
     apply disjdom_sub with (D2:=L) in Disj; auto.
       apply disjdom_sym_1.
       apply disjdom_eq with (D1:=atom_subst_codom asubst); auto.
          rewrite J. 
         clear. fsetdec.       
       clear. fsetdec.       
     apply Forel_lin_renamings with (E:=[(X,bind_kn Q)]); auto.
       rewrite_env ([(X,R)]++nil). rewrite_env ([(X,bind_kn Q)]++nil).
       apply wf_rho_subst_srel; auto.

       rewrite_env ([(X,A)]++nil). rewrite_env ([(X,bind_kn Q)]++nil).
       apply wf_delta_osubst_styp; eauto using wfor_left_inv.

       rewrite_env ([(X,A')]++nil). rewrite_env ([(X,bind_kn Q)]++nil).
       apply wf_delta_osubst_styp; eauto using wfor_right_inv.

       simpl. destruct (X==X); try solve [auto | contradict n; auto].
       simpl. destruct (X==X); try solve [auto | contradict n; auto].

   assert (F_Related_ovalues X [(X,R)] [(X,A)] [(X,A')] (rev_subst_atoms_exp asubst u) (rev_subst_atoms_exp asubst u') E (lE++lempty)) as Hrel_wft2'.
     assert (lE++lempty = rev_subst_atoms_lenv asubst ((subst_atoms_lenv asubst lE)++ lempty)) as Eq1.
       rewrite rev_subst_atoms_lenv_app.
       rewrite <- id_rev_subst_atoms_lenv; auto.
         rewrite <- rev_subst_atoms_lenv_notin_inv; auto.
           simpl. 
           apply disjdom_sym_1.
           apply disjdom_nil_1.

           rewrite lE_eq_asubst. 
           clear. fsetdec.       
   
         apply disjdom_sym_1.
         apply disjdom_eq with (D1:=dom asubst); auto.
           apply wf_asubst_dom_codom_disjoint; auto.
           rewrite  lE_eq_asubst. clear lE_eq_asubst.  
           clear. fsetdec.       
     rewrite Eq1. simpl_env.
     apply Forel_lin_rev_renamings with (E:=[(X, bind_kn Q)]); auto.
       rewrite_env ([(X,R)]++nil). rewrite_env ([(X,bind_kn Q)]++nil).
       apply wf_rho_subst_srel; auto.

       rewrite_env ([(X,A)]++nil). rewrite_env ([(X,bind_kn Q)]++nil).
       apply wf_delta_osubst_styp; eauto using wfor_left_inv.

       rewrite_env ([(X,A')]++nil). rewrite_env ([(X,bind_kn Q)]++nil).
       apply wf_delta_osubst_styp; eauto using wfor_right_inv.

       simpl. destruct (X==X); try solve [contradict n; auto].
       apply preservation_normalization with (e:=exp_app w (subst_atoms_exp asubst v0)); auto.
         apply typing_app with (T1:=A) (K:=K) (D1:=lempty) (D2:=subst_atoms_lenv asubst lE).
           apply preservation_normalization with (e:=exp_tapp v A); auto.
             assert (open_tt (typ_arrow K (typ_bvar 0) (typ_bvar 0)) A = typ_arrow K A A) as Heq.
               unfold open_tt. auto.
             rewrite <- Heq.
             eapply typing_tapp; eauto using wfor_left_inv.
               apply preservation_normalization with (e:=Id); auto.
               apply typing_lin_renamings; auto.
               apply lenv_split_left_empty; auto.
                 apply wf_lenv_renamings; auto.

       simpl. destruct (X==X); try solve [contradict n; auto].
       apply preservation_normalization with (e:=exp_app w' (subst_atoms_exp asubst v'0)); auto.
         apply typing_app with (T1:=A') (K:=K) (D1:=lempty) (D2:=subst_atoms_lenv asubst lE).
           apply preservation_normalization with (e:=exp_tapp v' A'); auto.
             assert (open_tt (typ_arrow K (typ_bvar 0) (typ_bvar 0)) A' = typ_arrow K A' A') as Heq.
               unfold open_tt. auto.
             rewrite <- Heq.
             eapply typing_tapp; eauto using wfor_right_inv.
               apply preservation_normalization with (e:=Id); auto.
               apply typing_lin_renamings; auto.
               apply lenv_split_left_empty; auto.
                 apply wf_lenv_renamings; auto.

       apply disjdom_sym_1 in Disj.
       apply disjdom_sub with (D2:=dom E) in Disj; auto.
          clear. fsetdec.       

       apply disjdom_eq with (D1:=dom lE); auto.
       eapply disjdom_app_r.
       split.
         apply disjoint__disjdom; auto.
       
         assert (J:=@subst_atoms_lenv__dom_eq asubst lE Wfa Uniq lE_eq_asubst).
         apply disjdom_eq with (D1:=atom_subst_codom asubst); auto.
           apply disjdom_sym_1.
           apply disjdom_eq with (D1:=dom asubst); auto.
             apply wf_asubst_dom_codom_disjoint; auto.
             rewrite  lE_eq_asubst. clear lE_eq_asubst.  
             clear. fsetdec.       
           rewrite J. 
           clear. fsetdec.       

  assert (normalize (exp_tapp Id A) w).
      apply congr_tapp with (v1:=v); auto.
      eapply type_from_wf_typ with (E:=E); eauto using wfor_left_inv.

  assert (normalize (exp_tapp Id A') w').
      apply congr_tapp with (v1:=v'); auto.
      eapply type_from_wf_typ with (E:=E); eauto using wfor_right_inv.

  assert (normalize (exp_app (exp_tapp Id A) v0) (rev_subst_atoms_exp asubst u)).
      apply congr_app with (v1:=w) (v2:=v0); auto.
        apply expr_tapp; auto.
          eapply type_from_wf_typ; eauto using wfor_left_inv.
        unfold normalize. auto.

       apply normalize_rev_renamings with (asubst:=asubst) in Hn_wxu; auto.
       rewrite rev_subst_atoms_exp__app in Hn_wxu.
       rewrite <- id_rev_subst_atoms_exp with (asubst:=asubst) in Hn_wxu; auto.
         rewrite <- rev_wf_asubst_id with (asubst:=asubst) (e:=w) in Hn_wxu; auto.
         apply disjdom_sub with (D1:=dom E).
             apply disjdom_sym_1 in Disj.
             apply disjdom_sub with (D2:=dom E) in Disj; auto.
             clear. fsetdec.       

             assert (typing E lempty w (typ_arrow K A A)) as Typ.
               apply preservation_normalization with (e:=exp_tapp Id A); auto.
                 assert (open_tt (typ_arrow K (typ_bvar 0) (typ_bvar 0)) A = typ_arrow K A A) as Heq.
                   unfold open_tt. auto.
                 rewrite <- Heq.
                 eapply typing_tapp; eauto using wfor_left_inv.
               apply typing_fv_ee_upper in Typ; auto.
                 simpl in Typ.
                 clear Harrow Uniq Disj Hall Fr Fr' Disj' lE_eq_asubst Disj'' WFT'.
                 fsetdec.
          apply typing_fv_ee_lower in Htypingv0; auto.
          rewrite <- lE_eq_asubst. clear Fr Fr' Harrow. assumption.

          apply typing_fv_ee_upper in Htypingv0; auto.
          apply disjdom_sub with (D1:=union (dom E) (dom lE)); auto.  

  assert (normalize (exp_app (exp_tapp Id A') v'0) (rev_subst_atoms_exp asubst u')).
      apply congr_app with (v1:=w') (v2:=v'0); auto.
        apply expr_tapp; auto.
          eapply type_from_wf_typ; eauto using wfor_right_inv.
        unfold normalize. auto.

       apply normalize_rev_renamings with (asubst:=asubst) in Hn_w'x'u'; auto.
       rewrite rev_subst_atoms_exp__app in Hn_w'x'u'.
       rewrite <- id_rev_subst_atoms_exp with (asubst:=asubst) in Hn_w'x'u'; auto.
         rewrite <- rev_wf_asubst_id with (asubst:=asubst) (e:=w') in Hn_w'x'u'; auto.
         apply disjdom_sub with (D1:=dom E).
             apply disjdom_sym_1 in Disj.
             apply disjdom_sub with (D2:=dom E) in Disj; auto.
               clear. fsetdec.       

             assert (typing E lempty w' (typ_arrow K A' A')) as Typ.
               apply preservation_normalization with (e:=exp_tapp Id A'); auto.
                 assert (open_tt (typ_arrow K (typ_bvar 0) (typ_bvar 0)) A' = typ_arrow K A' A') as Heq.
                   unfold open_tt. auto.
                 rewrite <- Heq.
                 eapply typing_tapp; eauto using wfor_right_inv.
               apply typing_fv_ee_upper in Typ; auto.
                 simpl in Typ.  
                 clear Harrow Uniq Disj Hall Fr Fr' Disj' lE_eq_asubst Disj'' WFT'.
                  fsetdec.
          apply typing_fv_ee_lower in Htypingv'0; auto.
          rewrite <- lE_eq_asubst. clear Fr Fr' Harrow. assumption.

          apply typing_fv_ee_upper in Htypingv'0; auto.
          apply disjdom_sub with (D1:=union (dom E) (dom lE)); auto.  

  exists(rev_subst_atoms_exp asubst u). exists(rev_subst_atoms_exp asubst u').
    split; simpl.
    destruct (X==X); try solve [contradict n; auto].
    apply typing_app with (T1:=A) (K:=K) (D1:=nil) (D2:=lE); auto.
      assert (open_tt (typ_arrow K (typ_bvar 0) (typ_bvar 0)) A = typ_arrow K A A) as Heq.
        unfold open_tt. auto.
      rewrite <- Heq.
      eapply typing_tapp; eauto using wfor_left_inv.

      apply lenv_split_left_empty; auto.

    split; simpl.
    destruct (X==X); try solve [contradict n; auto].
    eapply typing_app with (T1:=A')(K:=K) (D1:=nil) (D2:=lE); auto.
      assert (open_tt (typ_arrow K (typ_bvar 0) (typ_bvar 0)) A' = typ_arrow K A' A') as Heq.
        unfold open_tt. auto.
      rewrite <- Heq.
      eapply typing_tapp; eauto using wfor_right_inv.

      apply lenv_split_left_empty; auto.

    split; auto.
Qed.

Corollary EQ_OIdentification : forall Id K, 
  typing nil nil Id (typ_all kn_lin (typ_arrow K (typ_bvar 0) (typ_bvar 0))) ->
  (forall E lE x0 y0 A, 
    typing E lE x0 A ->
    typing E lE y0 A ->
    value x0 -> 
    value y0 ->
    Rid E (length lE) A x0 y0 -> 
    Rid E (length lE) A (exp_app (exp_tapp Id A) x0) (exp_app (exp_tapp Id A) y0)
  ).
Proof.
  intros Id K Htypingid E lE x0 y0 A Typingx0 Typingy0 Hx0 Hy0 HRid.
  unfold Rid in *. destruct HRid as [lEnv [lEq [Htypingx [Htypingy Heq_xy]]]].
  destruct (@OIdentification Id A A kn_lin K E lE x0 y0 (Rid E (length lE) A) Htypingid) as [X JJ]; auto using Rid_wfor.
  
  assert (wf_typ ((X, bind_kn kn_lin)::nil) (typ_fvar X) kn_lin) as WFT.
    apply wf_typ_var.
       unfold binds. simpl. auto. 
       simpl_env. apply binds_one_3; auto.

  assert (F_Related_ovalues (typ_fvar X) 
                                 ([(X,(Rid E (length lE) A))])
                                 ([(X, A)])
                                 ([(X, A)])
                                  x0 y0 E lE).
      apply F_Related_ovalues_fvar_req. simpl.
      exists(Rid E (length lE) A).
      repeat(split; auto).
        apply Rid_admissible.
        exists lEnv. repeat(split; auto).

  apply JJ in H; auto using Rid_wfor. subst.
  destruct H as [v [v' [Htypingv [Htypingv' [[Hbrc Hv] [[Hbrc' Hv'] [R [Hb [_ [_ [Hadmin Hrel]]]]]]]]]]]; subst.
  assert ((if X==X then A else typ_fvar X) = A) as HeqA.
    destruct (X==X); auto. contradict n; auto.
  simpl in *. simpl_env in *.
  rewrite HeqA in *. clear HeqA.
  exists lEnv. repeat(split; auto).
    apply typing_app with (D1:=lempty)(D2:=lEnv)(T1:=A)(K:=K); auto.
      assert (open_tt (typ_arrow K (typ_bvar 0) (typ_bvar 0)) A = typ_arrow K A A) as Heq.
        unfold open_tt. auto.
      rewrite <- Heq.
      eapply typing_tapp with (K:=kn_lin); eauto.
        rewrite_env (nil++E++nil).
        apply typing_weakening; auto.
          simpl_env. auto.

      apply lenv_split_left_empty; auto.

    apply typing_app with (D1:=lempty)(D2:=lEnv)(T1:=A)(K:=K); auto.
      assert (open_tt (typ_arrow K (typ_bvar 0) (typ_bvar 0)) A = typ_arrow K A A) as Heq.
        unfold open_tt. auto.
      rewrite <- Heq.
      eapply typing_tapp with (K:=kn_lin); eauto.
        rewrite_env (nil++E++nil).
        apply typing_weakening; auto.
          simpl_env. auto.

      apply lenv_split_left_empty; auto.

    eapply bee_congr_app with (K:=K) (lE1:=lempty) (lE2:=lEnv) (t1:=A); eauto.
      assert (open_tt (typ_arrow K (typ_bvar 0) (typ_bvar 0)) A = typ_arrow K A A) as Heq.
        unfold open_tt. auto.
      rewrite <- Heq.
      eapply typing_tapp with (K:=kn_lin); eauto.
        rewrite_env (nil++E++nil).
        apply typing_weakening; auto.
          simpl_env. auto.

     apply lenv_split_left_empty; auto.
Qed.


(***************************************************************)
(*                Linear Boolean is Empty                                                       *)
(***************************************************************)
Lemma OCBoolean : forall CBool A A' Q K K' E lE0 lE1 v0 v'0 v1 v'1 R, 
  typing nil nil CBool (typ_all Q (typ_arrow K (typ_bvar 0) (typ_arrow K' (typ_bvar 0) (typ_bvar 0)))) ->
  wfor E R A A' Q->
  value v0 -> value v'0 -> value v1 -> value v'1 ->
  typing E lE0 v0 A ->
  typing E lE0 v'0 A' ->
  typing E lE1 v1 A ->
  typing E lE1 v'1 A' ->
  disjoint lE0 lE1 ->
  exists X, 
   F_Related_ovalues (typ_fvar X) 
                                 ([(X,R)])
                                 ([(X,A)])
                                 ([(X,A')])
                                 v0 v'0 E lE0 ->
   F_Related_ovalues (typ_fvar X) 
                                 ([(X,R)])
                                 ([(X,A)])
                                 ([(X,A')])
                                 v1 v'1 E lE1 ->
   F_Related_oterms (typ_fvar X) 
                                 ([(X,R)])
                                 ([(X,A)])
                                 ([(X,A')])
                                 (exp_app (exp_app (exp_tapp CBool A) v0) v1) 
                                 (exp_app (exp_app (exp_tapp CBool A') v'0) v'1) E (lE0 ++ lE1).
Proof.
  intros CBool A A' Q K K' E lE0 lE1 v0 v'0 v1 v'1 R Htyping_bool Hwfor Hv0 Hv'0 Hv1 Hv'1 Htypingv0 Htypingv'0 Htypingv1 Htypingv'1 Disj.
  assert (wf_typ nil (typ_all Q (typ_arrow K (typ_bvar 0) (typ_arrow K' (typ_bvar 0) (typ_bvar 0)))) K) as WFT.
    apply wf_typ_all with (L:={}).
      intros X Hfv.
      unfold open_tt. simpl. simpl_env. 
      eapply wf_typ_arrow with (K1:=Q)(K2:=K'); eauto.
        eapply wf_typ_arrow; eauto.

  assert (F_Related_oterms (typ_all Q (typ_arrow K (typ_bvar 0) (typ_arrow K' (typ_bvar 0) (typ_bvar 0)))) rho_nil delta_nil delta_nil CBool CBool E nil) as Forel_All.
    apply fundamental_oparametricity; auto.
  destruct Forel_All as [v [v' [Htypingid [Htypingid' [Hn [Hn' Forel_All]]]]]].

  apply F_Related_ovalues_all_leq in Forel_All.
  destruct Forel_All as [Hv [Hv' [L' Hall]]]; subst.

  pick fresh X. 
  exists (X). intros Hrelt Hrelf.
  assert (wf_typ [(X,bind_kn Q)] (typ_fvar X) Q) as WFTvar. auto.
  assert (X `notin` L') as Fr'. auto.
  destruct (@Hall X A A' R Fr') as [w [w' [Hnorm_vt2w [Hnorm_v't2'w' Hrel_wft]]]]; auto.
  unfold open_tt in*. simpl in *.

  assert (wf_typ ((X, bind_kn Q)::nil) (typ_arrow K (typ_fvar X) (typ_arrow K' (typ_fvar X) (typ_fvar X))) K) as WFT'; eauto.

  apply F_Related_ovalues_arrow_leq in Hrel_wft.
  destruct Hrel_wft as [Hw [Hw' [Lt Harrow]]]; subst.
  simpl_env in *.
  assert ((if X==X then A else typ_fvar X) = A) as Heq.
    destruct (X==X); auto. contradict n; auto.
  assert ((if X==X then A' else typ_fvar X) = A') as Heq'.
    destruct (X==X); auto. contradict n; auto.
  simpl in *.
  rewrite Heq in *. rewrite Heq' in *. clear Heq Heq'.

  assert (uniq lE0) as Uniq0.
     apply typing_regular in Htypingv0. destruct Htypingv0 as [JJ1 [JJ2 [JJ3 JJ4]]].
     apply uniq_from_wf_lenv in JJ2; auto.
  assert (disjoint E lE0) as Disj0'.
     apply typing_regular in Htypingv0. destruct Htypingv0 as [JJ1 [JJ2 [JJ3 JJ4]]].
     apply disjoint_wf_lenv in JJ2; auto.
  assert (JJ:=@pick_lenv (Lt `union` L' `union` {{X}}  `union` dom E) lE0 Uniq0).
  destruct JJ as [asubst0 [Wfa [lE0_eq_asubst0 Disj0]]].
  assert (disjoint asubst0 E) as Disj0''.
     apply disjoint_eq with (D1:=lE0); auto.
  assert (disjdom (atom_subst_codom asubst0) (union (dom E) (dom lE0))) as Disj0'''.
     eapply  disjdom_app_r.
     split.
       apply disjdom_sym_1 in Disj0.
       apply disjdom_sub with (D2:=dom E) in Disj0; auto.
         apply disjdom_sym_1; auto.
         clear. fsetdec.       
       apply disjdom_eq with (D1:=dom asubst0); auto.
         apply wf_asubst_dom_codom_disjoint; auto.
         rewrite  lE0_eq_asubst0. clear lE0_eq_asubst0.  
         clear. fsetdec.       
  destruct (@Harrow (subst_atoms_lenv asubst0 lE0) (subst_atoms_exp asubst0 v0) (subst_atoms_exp asubst0 v'0)) as [u [u' [Hn_wxu [Hn_w'x'u' Hrel_wft2]]]]; auto.
     apply typing_lin_renamings; auto.
     apply typing_lin_renamings; auto.
     simpl_env.  apply wf_lenv_renamings; auto.

     assert (J:=@subst_atoms_lenv__dom_eq asubst0 lE0 Wfa Uniq0 lE0_eq_asubst0).
     apply disjdom_sym_1 in Disj0.
     apply disjdom_sub with (D2:=Lt) in Disj0; auto.
       apply disjdom_sym_1.
       apply disjdom_eq with (D1:=atom_subst_codom asubst0); auto.
          rewrite J. 
         clear. fsetdec.       
       clear. fsetdec.       
     apply Forel_lin_renamings with (E:=[(X,bind_kn Q)]); auto.
       rewrite_env ([(X,R)]++nil). rewrite_env ([(X,bind_kn Q)]++nil).
       apply wf_rho_subst_srel; auto.

       rewrite_env ([(X,A)]++nil). rewrite_env ([(X,bind_kn Q)]++nil).
       apply wf_delta_osubst_styp; eauto using wfor_left_inv.

       rewrite_env ([(X,A')]++nil). rewrite_env ([(X,bind_kn Q)]++nil).
       apply wf_delta_osubst_styp; eauto using wfor_right_inv.

       simpl. destruct (X==X); try solve [auto | contradict n; auto].
       simpl. destruct (X==X); try solve [auto | contradict n; auto].

   assert (F_Related_ovalues (typ_arrow K' X X) [(X,R)] [(X,A)] [(X,A')] (rev_subst_atoms_exp asubst0 u) (rev_subst_atoms_exp asubst0 u') E (lE0++lempty)) as Hrel_wft2'.
     assert (lE0++lempty = rev_subst_atoms_lenv asubst0 ((subst_atoms_lenv asubst0 lE0)++ lempty)) as Eq1.
       rewrite rev_subst_atoms_lenv_app.
       rewrite <- id_rev_subst_atoms_lenv; auto.
         rewrite <- rev_subst_atoms_lenv_notin_inv; auto.
           simpl. 
           apply disjdom_sym_1.
           apply disjdom_nil_1.

           rewrite lE0_eq_asubst0. 
           clear. fsetdec.       

         apply disjdom_sym_1.
         apply disjdom_eq with (D1:=dom asubst0); auto.
           apply wf_asubst_dom_codom_disjoint; auto.
           rewrite  lE0_eq_asubst0. clear lE0_eq_asubst0.  
           clear. fsetdec.       
    rewrite Eq1. simpl_env.
     apply Forel_lin_rev_renamings with (E:=[(X, bind_kn Q)]); auto.
       simpl_env in Hrel_wft2. assumption.

       rewrite_env ([(X,R)]++nil). rewrite_env ([(X,bind_kn Q)]++nil).
       apply wf_rho_subst_srel; auto.

       rewrite_env ([(X,A)]++nil). rewrite_env ([(X,bind_kn Q)]++nil).
       apply wf_delta_osubst_styp; eauto using wfor_left_inv.

       rewrite_env ([(X,A')]++nil). rewrite_env ([(X,bind_kn Q)]++nil).
       apply wf_delta_osubst_styp; eauto using wfor_right_inv.

       simpl. destruct (X==X); try solve [contradict n; auto].
       apply preservation_normalization with (e:=exp_app w (subst_atoms_exp asubst0 v0)); auto.
         apply typing_app with (T1:=A) (K:=K) (D1:=lempty) (D2:=subst_atoms_lenv asubst0 lE0).
           apply preservation_normalization with (e:=exp_tapp v A); auto.
             assert (open_tt (typ_arrow K (typ_bvar 0) (typ_arrow K' (typ_bvar 0) (typ_bvar 0))) A = typ_arrow K A (typ_arrow K' A A)) as Heq.
               unfold open_tt. auto.
             rewrite <- Heq.
             eapply typing_tapp; eauto using wfor_left_inv.
               apply preservation_normalization with (e:=CBool); auto.
               apply typing_lin_renamings; auto.
               apply lenv_split_left_empty; auto.
                 apply wf_lenv_renamings; auto.

       simpl. destruct (X==X); try solve [contradict n; auto].
       apply preservation_normalization with (e:=exp_app w' (subst_atoms_exp asubst0 v'0)); auto.
         apply typing_app with (T1:=A') (K:=K) (D1:=lempty) (D2:=subst_atoms_lenv asubst0 lE0).
           apply preservation_normalization with (e:=exp_tapp v' A'); auto.
             assert (open_tt (typ_arrow K (typ_bvar 0) (typ_arrow K' (typ_bvar 0) (typ_bvar 0))) A' = typ_arrow K A' (typ_arrow K' A' A')) as Heq.
               unfold open_tt. auto.
             rewrite <- Heq.
             eapply typing_tapp; eauto using wfor_right_inv.
               apply preservation_normalization with (e:=CBool); auto.
               apply typing_lin_renamings; auto.
               apply lenv_split_left_empty; auto.
                 apply wf_lenv_renamings; auto.

       apply disjdom_sym_1 in Disj0.
       apply disjdom_sub with (D2:=dom E) in Disj0; auto.
         clear. fsetdec.       

       apply disjdom_eq with (D1:=dom lE0); auto.
       eapply disjdom_app_r.
       split.
         apply disjoint__disjdom; auto.
       
         assert (J:=@subst_atoms_lenv__dom_eq asubst0 lE0 Wfa Uniq0 lE0_eq_asubst0).
         apply disjdom_eq with (D1:=atom_subst_codom asubst0); auto.
           apply disjdom_sym_1.
           apply disjdom_eq with (D1:=dom asubst0); auto.
             apply wf_asubst_dom_codom_disjoint; auto.
             rewrite  lE0_eq_asubst0. clear lE0_eq_asubst0.  
             clear. fsetdec.       
           rewrite J. 
           clear. fsetdec.       

  apply F_Related_ovalues_arrow_leq in Hrel_wft2'.
  simpl_env in *.
  destruct Hrel_wft2' as [Hu [Hu' [Lf Harrow']]]; subst.
  assert ((if X==X then A else typ_fvar X) = A) as Heq.
    destruct (X==X); auto. contradict n; auto.
  assert ((if X==X then A' else typ_fvar X) = A') as Heq'.
    destruct (X==X); auto. contradict n; auto. 
  simpl in *.
  rewrite Heq in *. rewrite Heq' in *. clear Heq Heq'.

  assert (wf_typ E A Q) as wft_A.
      apply wfor_left_inv in Hwfor; auto.

  assert (type A) as TypeA. eauto using type_from_wf_typ.

  assert (wf_typ E A' Q) as wft_A'.
      apply wfor_right_inv in Hwfor; auto.

  assert (type A') as TypeA'. eauto using type_from_wf_typ.

  assert (normalize (exp_tapp CBool A) w).
      apply congr_tapp with (v1:=v); auto.

  assert (normalize (exp_tapp CBool A') w').
      apply congr_tapp with (v1:=v'); auto.
    
  assert (normalize (exp_app (exp_tapp CBool A) v0) (rev_subst_atoms_exp asubst0 u)) as Hn'_wxu.
      apply congr_app with (v1:=w) (v2:=v0); auto.
        unfold normalize; auto.

       apply normalize_rev_renamings with (asubst:=asubst0) in Hn_wxu; auto.
       rewrite rev_subst_atoms_exp__app in Hn_wxu.
       rewrite <- id_rev_subst_atoms_exp with (asubst:=asubst0) in Hn_wxu; auto.
         rewrite <- rev_wf_asubst_id with (asubst:=asubst0) (e:=w) in Hn_wxu; auto.
         apply disjdom_sub with (D1:=dom E).
             apply disjdom_sym_1 in Disj0.
             apply disjdom_sub with (D2:=dom E) in Disj0; auto.
               clear. fsetdec.       

             assert (typing E lempty w (typ_arrow K A (typ_arrow K' A A))) as Typ.
               apply preservation_normalization with (e:=exp_tapp CBool A); auto.
                 assert (open_tt (typ_arrow K (typ_bvar 0) (typ_arrow K' (typ_bvar 0) (typ_bvar 0))) A = typ_arrow K A (typ_arrow K' A A)) as Heq.
                   unfold open_tt. auto.
                 rewrite <- Heq.
                 eapply typing_tapp; eauto using wfor_left_inv.
               apply typing_fv_ee_upper in Typ; auto.
                 simpl in Typ.
                 clear Harrow Uniq0 Disj0 Hall Fr Fr' Disj0' lE0_eq_asubst0 Disj0'' WFT'.
                 fsetdec.
          apply typing_fv_ee_lower in Htypingv0; auto.
          rewrite <- lE0_eq_asubst0. clear Fr Fr' Harrow. assumption.

          apply typing_fv_ee_upper in Htypingv0; auto.
          apply disjdom_sub with (D1:=union (dom E) (dom lE0)); auto.  

  assert (normalize (exp_app (exp_tapp CBool A') v'0) (rev_subst_atoms_exp asubst0 u')) as Hn'_w'x'u'.
      apply congr_app with (v1:=w') (v2:=v'0); auto.
        unfold normalize; auto.

       apply normalize_rev_renamings with (asubst:=asubst0) in Hn_w'x'u'; auto.
       rewrite rev_subst_atoms_exp__app in Hn_w'x'u'.
       rewrite <- id_rev_subst_atoms_exp with (asubst:=asubst0) in Hn_w'x'u'; auto.
         rewrite <- rev_wf_asubst_id with (asubst:=asubst0) (e:=w') in Hn_w'x'u'; auto.
         apply disjdom_sub with (D1:=dom E).
             apply disjdom_sym_1 in Disj0.
             apply disjdom_sub with (D2:=dom E) in Disj0; auto.
               clear. fsetdec.       

             assert (typing E lempty w' (typ_arrow K A' (typ_arrow K' A' A'))) as Typ.
               apply preservation_normalization with (e:=exp_tapp CBool A'); auto.
                 assert (open_tt (typ_arrow K (typ_bvar 0) (typ_arrow K' (typ_bvar 0) (typ_bvar 0))) A' = typ_arrow K A' (typ_arrow K' A' A')) as Heq.
                   unfold open_tt. auto.
                 rewrite <- Heq.
                 eapply typing_tapp; eauto using wfor_right_inv.
               apply typing_fv_ee_upper in Typ; auto.
                 simpl in Typ.
                 clear Harrow Uniq0 Disj0 Hall Fr Fr' Disj0' lE0_eq_asubst0 Disj0'' WFT'.
                 fsetdec.
          apply typing_fv_ee_lower in Htypingv'0; auto.
          rewrite <- lE0_eq_asubst0. clear Fr Fr' Harrow. assumption.

          apply typing_fv_ee_upper in Htypingv'0; auto.
          apply disjdom_sub with (D1:=union (dom E) (dom lE0)); auto.  

  assert (uniq lE1) as Uniq1.
     apply typing_regular in Htypingv1. destruct Htypingv1 as [JJ1 [JJ2 [JJ3 JJ4]]].
     apply uniq_from_wf_lenv in JJ2; auto.
  assert (disjoint E lE1) as Disj1'.
     apply typing_regular in Htypingv1. destruct Htypingv1 as [JJ1 [JJ2 [JJ3 JJ4]]].
     apply disjoint_wf_lenv in JJ2; auto.
  assert (JJ:=@pick_lenv (Lf `union` Lt `union` L' `union` {{X}}  `union` dom E `union` dom lE0) lE1 Uniq1).
  destruct JJ as [asubst1 [Wfa1 [lE1_eq_asubst1 Disj1]]].
  assert (disjoint asubst1 E) as Disj1''.
     apply disjoint_eq with (D1:=lE1); auto.
  assert (disjdom (atom_subst_codom asubst1) (union (dom E) (dom lE1))) as Disj1'''.
     eapply  disjdom_app_r.
     split.
       apply disjdom_sym_1 in Disj1.
       apply disjdom_sub with (D2:=dom E) in Disj1; auto.
         apply disjdom_sym_1; auto.
         clear. fsetdec.       
       apply disjdom_eq with (D1:=dom asubst1); auto.
         apply wf_asubst_dom_codom_disjoint; auto.
         rewrite  lE1_eq_asubst1. clear lE1_eq_asubst1.  
         clear. fsetdec.       
  destruct (@Harrow' (subst_atoms_lenv asubst1 lE1) (subst_atoms_exp asubst1 v1) (subst_atoms_exp asubst1 v'1)) as [x [x' [Hn_uxu0 [Hn_u'x'u'0 Hrel_wft22]]]]; auto.
     apply typing_lin_renamings; auto.
     apply typing_lin_renamings; auto.
     apply wf_lenv_merge; auto.
       apply wf_lenv_renamings; auto.

       assert (disjdom (atom_subst_codom asubst1) (dom lE1)) as Disj3.
         apply disjdom_app_r in Disj1'''. destruct Disj1'''.
         apply disjdom_sym_1; auto.
       assert (J:=@subst_atoms_lenv__dom_upper asubst1 lE1 Wfa1 Uniq1 Disj3).
       apply disjdom__disjoint.
       apply disjdom_sym_1.
       apply disjdom_sub with (D1:=union (dom lE1) (atom_subst_codom asubst1)); auto.
       eapply disjdom_app_r.
         split.
           apply disjoint__disjdom.
           apply disjoint_sym_1; auto.
            
           apply disjdom_sym_1 in Disj1.
           apply disjdom_sub with (D2:=(dom lE0)) in Disj1; auto.
             clear. fsetdec.       

     assert (J:=@subst_atoms_lenv__dom_eq asubst1 lE1 Wfa1 Uniq1 lE1_eq_asubst1).
     apply disjdom_sym_1 in Disj1.
     apply disjdom_sub with (D2:=Lf) in Disj1; auto.
       apply disjdom_sym_1.
       apply disjdom_eq with (D1:=atom_subst_codom asubst1); auto.
          rewrite J. 
          clear. fsetdec.       
       clear. fsetdec.       
     apply Forel_lin_renamings with (E:=[(X,bind_kn Q)]); auto.
       rewrite_env ([(X,R)]++nil). rewrite_env ([(X,bind_kn Q)]++nil).
       apply wf_rho_subst_srel; auto.

       rewrite_env ([(X,A)]++nil). rewrite_env ([(X,bind_kn Q)]++nil).
       apply wf_delta_osubst_styp; eauto using wfor_left_inv.

       rewrite_env ([(X,A')]++nil). rewrite_env ([(X,bind_kn Q)]++nil).
       apply wf_delta_osubst_styp; eauto using wfor_right_inv.

       simpl. destruct (X==X); try solve [auto | contradict n; auto].
       simpl. destruct (X==X); try solve [auto | contradict n; auto].

   assert (F_Related_ovalues X [(X,R)] [(X,A)] [(X,A')] (rev_subst_atoms_exp asubst1 x) (rev_subst_atoms_exp asubst1 x') E (lE1++lE0)) as Hrel_wft22'.
     assert (lE1++lE0 = rev_subst_atoms_lenv asubst1 ((subst_atoms_lenv asubst1 lE1)++ lE0)) as Eq1.
       rewrite rev_subst_atoms_lenv_app.
       rewrite <- id_rev_subst_atoms_lenv; auto.
         rewrite <- rev_subst_atoms_lenv_notin_inv; auto.
           apply disjdom_sym_1 in Disj1.
           apply disjdom_sub with (D2:=dom lE0) in Disj1; auto.
             clear. fsetdec.       
         rewrite lE1_eq_asubst1. 
         clear. fsetdec.       

         apply disjdom_sym_1.
         apply disjdom_eq with (D1:=dom asubst1); auto.
           apply wf_asubst_dom_codom_disjoint; auto.
           rewrite  lE1_eq_asubst1. clear lE1_eq_asubst1.  
           clear. fsetdec.       
     rewrite Eq1. simpl_env.
     apply Forel_lin_rev_renamings with (E:=[(X, bind_kn Q)]); auto.
       rewrite_env ([(X,R)]++nil). rewrite_env ([(X,bind_kn Q)]++nil).
       apply wf_rho_subst_srel; auto.

       rewrite_env ([(X,A)]++nil). rewrite_env ([(X,bind_kn Q)]++nil).
       apply wf_delta_osubst_styp; eauto using wfor_left_inv.

       rewrite_env ([(X,A')]++nil). rewrite_env ([(X,bind_kn Q)]++nil).
       apply wf_delta_osubst_styp; eauto using wfor_right_inv.

       simpl. destruct (X==X); try solve [contradict n; auto].
       apply preservation_normalization with (e:=exp_app (rev_subst_atoms_exp asubst0 u) (subst_atoms_exp asubst1 v1)); auto.
         apply typing_app with (T1:=A) (K:=K') (D1:=lE0) (D2:=subst_atoms_lenv asubst1 lE1).
           apply preservation_normalization with (e:=exp_app (exp_tapp CBool A) v0); auto.
             apply typing_app with (T1:=A) (K:=K) (D1:=lempty) (D2:=lE0); auto.
               assert (open_tt (typ_arrow K (typ_bvar 0) (typ_arrow K' (typ_bvar 0) (typ_bvar 0))) A = typ_arrow K A (typ_arrow K' A A)) as Heq.
                 unfold open_tt. auto.
               rewrite <- Heq.
               eapply typing_tapp; eauto using wfor_left_inv.

               apply lenv_split_left_empty; auto.

             apply typing_lin_renamings; auto.

             apply lenv_split_commute.
             apply disjoint__lenv_split; auto.
               apply wf_lenv_renamings; auto.

               assert (J:=@subst_atoms_lenv__dom_eq asubst1 lE1 Wfa1 Uniq1 lE1_eq_asubst1).
               apply disjdom_sym_1 in Disj1.
               apply disjdom_sub with (D2:=dom lE0) in Disj1; auto.
                 apply disjdom__disjoint.
                 apply disjdom_eq with (D1:=atom_subst_codom asubst1); auto.
                   rewrite J. 
                   clear. fsetdec.             
                 clear. fsetdec.

       simpl. destruct (X==X); try solve [contradict n; auto].
       apply preservation_normalization with (e:=exp_app (rev_subst_atoms_exp asubst0 u') (subst_atoms_exp asubst1 v'1)); auto.
         apply typing_app with (T1:=A') (K:=K') (D1:=lE0) (D2:=subst_atoms_lenv asubst1 lE1).
           apply preservation_normalization with (e:=exp_app (exp_tapp CBool A') v'0); auto.
             apply typing_app with (T1:=A') (K:=K) (D1:=lempty) (D2:=lE0); auto.
               assert (open_tt (typ_arrow K (typ_bvar 0) (typ_arrow K' (typ_bvar 0) (typ_bvar 0))) A' = typ_arrow K A' (typ_arrow K' A' A')) as Heq.
                 unfold open_tt. auto.
               rewrite <- Heq.
               eapply typing_tapp; eauto using wfor_right_inv.

               apply lenv_split_left_empty; auto.

             apply typing_lin_renamings; auto.

             apply lenv_split_commute.
             apply disjoint__lenv_split; auto.
               apply wf_lenv_renamings; auto.

               assert (J:=@subst_atoms_lenv__dom_eq asubst1 lE1 Wfa1 Uniq1 lE1_eq_asubst1).
               apply disjdom_sym_1 in Disj1.
               apply disjdom_sub with (D2:=dom lE0) in Disj1; auto.
                 apply disjdom__disjoint.
                 apply disjdom_eq with (D1:=atom_subst_codom asubst1); auto.
                   rewrite J. 
                   clear. fsetdec.             
                 clear. fsetdec.

       apply disjdom_sym_1 in Disj1.
       apply disjdom_sub with (D2:=dom E) in Disj1; auto.
         clear. fsetdec.

       apply disjdom_eq with (D1:=dom lE1); auto.
       eapply disjdom_app_r.
       split.
         apply disjoint__disjdom; auto.
       
         apply disjoint__disjdom.
         eapply disjoint_app_l.
         split; auto.
           assert (J:=@subst_atoms_lenv__dom_eq asubst1 lE1 Wfa1 Uniq1 lE1_eq_asubst1).
           apply disjdom__disjoint.
           apply disjdom_eq with (D1:=atom_subst_codom asubst1); auto.
             apply disjdom_sym_1.
             apply disjdom_eq with (D1:=dom asubst1); auto.
               apply wf_asubst_dom_codom_disjoint; auto.
               rewrite  lE1_eq_asubst1. clear.
               fsetdec. 
             rewrite J. clear. fsetdec.

  assert (normalize (exp_app (exp_app (exp_tapp CBool A) v0) v1) (rev_subst_atoms_exp asubst1 x)).
      apply congr_app with (v1:=rev_subst_atoms_exp asubst0 u) (v2:=v1); auto. 
        unfold normalize; auto.

       apply normalize_rev_renamings with (asubst:=asubst1) in Hn_uxu0; auto.
       rewrite rev_subst_atoms_exp__app in Hn_uxu0.
       rewrite <- id_rev_subst_atoms_exp with (asubst:=asubst1) in Hn_uxu0; auto.
         rewrite <- rev_wf_asubst_id with (asubst:=asubst1) (e:=rev_subst_atoms_exp asubst0 u) in Hn_uxu0; auto.
         apply disjdom_sub with (D1:=dom E `union` dom lE0).
             apply disjdom_sym_1 in Disj1.
             apply disjdom_sub with (D2:=dom E `union` dom lE0) in Disj1; auto.
               clear. fsetdec.             

             assert (typing E lE0 (rev_subst_atoms_exp asubst0 u) (typ_arrow K' A A)) as Typ.
               apply preservation_normalization with (e:=exp_app (exp_tapp CBool A) v0); auto.
                  apply typing_app with (T1:=A) (K:=K) (D1:=lempty) (D2:=lE0); auto.
                    assert (open_tt (typ_arrow K (typ_bvar 0) (typ_arrow K' (typ_bvar 0) (typ_bvar 0))) A = typ_arrow K A (typ_arrow K' A A)) as Heq.
                      unfold open_tt. auto.
                    rewrite <- Heq.
                    eapply typing_tapp; eauto using wfor_left_inv.
                    
                    apply lenv_split_left_empty; auto.
               apply typing_fv_ee_upper in Typ; auto.
          apply typing_fv_ee_lower in Htypingv1; auto.
          rewrite <- lE1_eq_asubst1. clear Fr Fr' Harrow. assumption.

          apply typing_fv_ee_upper in Htypingv1; auto.
          apply disjdom_sub with (D1:=union (dom E) (dom lE1)); auto.  

  assert (normalize (exp_app (exp_app (exp_tapp CBool A') v'0) v'1) (rev_subst_atoms_exp asubst1 x')).
      apply congr_app with (v1:=rev_subst_atoms_exp asubst0 u') (v2:=v'1); auto. 
        unfold normalize; auto.

       apply normalize_rev_renamings with (asubst:=asubst1) in Hn_u'x'u'0; auto.
       rewrite rev_subst_atoms_exp__app in Hn_u'x'u'0.
       rewrite <- id_rev_subst_atoms_exp with (asubst:=asubst1) in Hn_u'x'u'0; auto.
         rewrite <- rev_wf_asubst_id with (asubst:=asubst1) (e:=rev_subst_atoms_exp asubst0 u') in Hn_u'x'u'0; auto.
         apply disjdom_sub with (D1:=dom E `union` dom lE0).
             apply disjdom_sym_1 in Disj1.
             apply disjdom_sub with (D2:=dom E `union` dom lE0) in Disj1; auto.
               clear. fsetdec.             

             assert (typing E lE0 (rev_subst_atoms_exp asubst0 u') (typ_arrow K' A' A')) as Typ.
               apply preservation_normalization with (e:=exp_app (exp_tapp CBool A') v'0); auto.
                  apply typing_app with (T1:=A') (K:=K) (D1:=lempty) (D2:=lE0); auto.
                    assert (open_tt (typ_arrow K (typ_bvar 0) (typ_arrow K' (typ_bvar 0) (typ_bvar 0))) A' = typ_arrow K A' (typ_arrow K' A' A')) as Heq.
                      unfold open_tt. auto.
                    rewrite <- Heq.
                    eapply typing_tapp; eauto using wfor_right_inv.
                    
                    apply lenv_split_left_empty; auto.
               apply typing_fv_ee_upper in Typ; auto.
          apply typing_fv_ee_lower in Htypingv'1; auto.
          rewrite <- lE1_eq_asubst1. clear Fr Fr' Harrow. assumption.

          apply typing_fv_ee_upper in Htypingv'1; auto.
          apply disjdom_sub with (D1:=union (dom E) (dom lE1)); auto.  

  unfold F_Related_oterms. exists (rev_subst_atoms_exp asubst1 x). exists (rev_subst_atoms_exp asubst1 x').
    split; simpl.
    destruct (X==X); try solve [contradict n; auto].
    apply typing_app with (T1:=A)(D1:=lE0) (D2:=lE1) (K:=K'); auto.
      apply typing_app with (T1:=A)(D1:=nil) (D2:=lE0) (K:=K); auto.
        assert (open_tt (typ_arrow K (typ_bvar 0) (typ_arrow K' (typ_bvar 0) (typ_bvar 0))) A = typ_arrow K A (typ_arrow K' A A)) as Heq.
          unfold open_tt. auto.
        rewrite <- Heq.
        apply typing_tapp with (K:=Q); auto.

        apply lenv_split_left_empty; auto.
      apply disjoint__lenv_split; auto.

    split; simpl.
    destruct (X==X); try solve [contradict n; auto].
    apply typing_app with (T1:=A')(D1:=lE0) (D2:=lE1) (K:=K'); auto.
      apply typing_app with (T1:=A')(D1:=nil) (D2:=lE0) (K:=K); auto.
        assert (open_tt (typ_arrow K (typ_bvar 0) (typ_arrow K' (typ_bvar 0) (typ_bvar 0))) A' = typ_arrow K A' (typ_arrow K' A' A')) as Heq.
          unfold open_tt. auto.
        rewrite <- Heq.
        apply typing_tapp with (K:=Q); auto.

        apply lenv_split_left_empty; auto.
      apply disjoint__lenv_split; auto.

    split; auto.
Qed.

Definition Rlid Env l1 l2 (A:typ) (v v':exp) : Prop := 
  (exists lEnv1, (length lEnv1 = l1 /\ typing Env lEnv1 v A /\ typing Env lEnv1 v' A /\ beta_eta_eq Env lEnv1 v v' A)) \/
  (exists lEnv2, (length lEnv2 = l2 /\ typing Env lEnv2 v A /\ typing Env lEnv2 v' A /\ beta_eta_eq Env lEnv2 v v' A)).

Lemma Rlid_admissible : forall Env l1 l2 A,
  admissible Env (Rlid Env l1 l2 A).
Proof.
  intros Env l1 l2 A.
  intros v v' R x y Frx Frx' Fry.
    destruct (x==y); subst.
      rewrite subst_ee_id. rewrite subst_ee_id. auto.

    destruct R as [[lEnv1 [lEq1 [Typingv1 [Typingv1' Bee1]]]]|[lEnv2 [lEq2 [Typingv2 [Typingv2' Bee2]]]]].
    left. exists (subst_atom_lenv lEnv1 x y).
    assert (x `notin` dom Env) as xnEnv.
      apply typing_ldom in Typingv1.
      rewrite Typingv1 in Frx.
      apply typing_regular in Typingv1'.
      decompose [and] Typingv1'. clear Typingv1'.
      apply disjoint_wf_lenv in H1.
      clear Frx' Fry H H0 H3. solve_uniq.
    assert (y `notin` dom Env) as ynEnv.
      destruct_notin; auto.
        fsetdec.
    assert (y `notin` dom lEnv1) as ynlEnv1.
      apply typing_ldom in Typingv1.
      rewrite <- Typingv1. clear Typingv1.
      destruct_notin; auto.
        contradict NotInTac; auto.
    split. rewrite <- renaming_length; auto.
    split. apply typing_lin_renaming; auto.
    split. apply typing_lin_renaming; auto.
      apply bee_lin_renaming with (x:=x) (y:=y) in Bee1; auto.

    right. exists (subst_atom_lenv lEnv2 x y).
    assert (x `notin` dom Env) as xnEnv.
      apply typing_ldom in Typingv2.
      rewrite Typingv2 in Frx.
      apply typing_regular in Typingv2'.
      decompose [and] Typingv2'. clear Typingv2'.
      apply disjoint_wf_lenv in H1.
      clear Frx' Fry H H0 H3. solve_uniq.
    assert (y `notin` dom Env) as ynEnv.
      destruct_notin; auto.
        fsetdec.
    assert (y `notin` dom lEnv2) as ynlEnv2.
      apply typing_ldom in Typingv2.
      rewrite <- Typingv2. clear Typingv2.
      destruct_notin; auto.
        contradict NotInTac; auto.
    split. rewrite <- renaming_length; auto.
    split. apply typing_lin_renaming; auto.
    split. apply typing_lin_renaming; auto.
      apply bee_lin_renaming with (x:=x) (y:=y) in Bee2; auto.
Qed.

Lemma Rlid_wfor : forall Env l1 l2 A K,
  wf_typ Env A K -> 
  wfor Env (Rlid Env l1 l2 A) A A K.
Proof.
  intros.
  split; auto.
  split; auto.
    apply Rlid_admissible.
Qed.

Lemma in_list_inv : forall A (E:list (atom*A)) x,
  x `in` dom E ->
  exists E1, exists E2, exists b, E = E1 ++ [(x,b)] ++ E2.
Proof.
  induction E; intros x xin.
    contradict xin; auto.

    destruct a. simpl in xin.
    assert (x `in` {{a}} \/ x `in` dom E) as J. fsetdec.
    destruct J as [J | J].
      exists nil. exists E. exists a0.
      destruct (x==a); subst; auto.
        contradict J; auto.

      apply IHE in J. destruct J as [E1 [E2 [b J]]]; subst.
      exists ((a,a0)::E1). exists E2. exists b. auto.
Qed.

Lemma uniq_domeq__lengtheq : forall A (lE lE':list (atom*A)),
  uniq lE ->
  uniq lE' ->
  dom lE [=] dom lE' ->
  length lE = length lE'.
Proof.
  intros A lE lE' Uniq Uniq' DomEq.
  generalize dependent lE'.
  induction Uniq; intros.
    inversion Uniq'; subst; auto.
      simpl in DomEq. 
      assert (x `in` add x (dom E)) as xin. auto.
      rewrite <- DomEq in xin.
      contradict xin; auto.
 
    inversion Uniq'; subst; auto.    
      simpl in DomEq. 
      assert (x `in` add x (dom E)) as xin. auto.
      rewrite DomEq in xin.
      contradict xin; auto.
   
    destruct (x==x0); subst.
      assert (dom E [=] dom E0) as EQ.
        simpl in DomEq. fsetdec.
      apply IHUniq in EQ; auto.
      simpl. rewrite EQ. auto.

      assert (x `in` dom ([(x,a)]++E)) as J. simpl. auto.
      assert (x `in` dom ([(x0,a0)]++E0)) as J'. rewrite DomEq in J. assumption.
      assert (x `in` dom E0) as J''. simpl in J'. fsetdec.
      apply in_list_inv in J''. clear J'.
      destruct J'' as [E1 [E2 [b EQ]]]; subst.
     assert (dom E [=] AtomSetImpl.diff (dom ([(x,a)]++E)) {{x}}) as EQ1.
       simpl. clear H1 Uniq' DomEq. fsetdec.
     assert (dom ([(x0, a0)]++E1++E2) [=] AtomSetImpl.diff (dom ([(x0, a0)]++E1++[(x,b)]++E2)) {{x}}) as EQ2.
       simpl_env in *. clear H Uniq DomEq. 
       assert (x `notin` dom E1) as xnE1.
         apply fresh_mid_head in H0; auto.
       assert (x `notin` dom E2) as xnE2.
         apply fresh_mid_tail in H0; auto.
       clear J EQ1 H1 Uniq'. fsetdec.
      assert (dom E [=] dom ([(x0, a0)]++E1++E2)) as EQ.
        rewrite EQ1. rewrite EQ2. 
        clear n J H0 H1 Uniq' EQ1 EQ2. fsetdec.
      apply IHUniq in EQ; auto.
        simpl. rewrite EQ.
        simpl_env. repeat (rewrite app_length). simpl. auto.
 
        simpl_env in H1. 
        clear H IHUniq n J Uniq' DomEq EQ1 EQ2 EQ.
        solve_uniq.
Qed.

Corollary OCBool_Identification : forall CBool K K', 
  typing nil nil CBool (typ_all kn_lin (typ_arrow K (typ_bvar 0) (typ_arrow K' (typ_bvar 0) (typ_bvar 0)))) ->
  (forall E lEt lEf vt1 vt2 vf1 vf2 A, 
    value vt1 -> value vt2 -> value vf1 -> value vf2 ->
    typing E lEt vt1 A ->
    typing E lEt vt2 A ->
    typing E lEf vf1 A ->
    typing E lEf vf2 A ->
    disjoint lEt lEf ->
    Rlid E (length lEt) (length lEf) A vt1 vt2 -> 
    Rlid E (length lEt) (length lEf) A vf1 vf2 -> 
    (lEt = nil \/ lEf = nil)
  ).
Proof.
  intros CBool K K' Htyping_bool E lEt lEf vt1 vt2 vf1 vf2 A Hvt1 Hvt2 Hvf1 Hvf2 Htypingvt1 Htypingvt2 Htypingvf1 Htypingvf2 Disj HRlidt HRlidf.

  unfold Rlid in *. 

  destruct (@OCBoolean CBool A A kn_lin K K' E lEt lEf vt1 vt2 vf1 vf2 (Rlid E (length lEt) (length lEf) A) Htyping_bool) as [X JJ]; auto using Rlid_wfor.
  
  assert (wfor E (Rlid E (length lEt) (length lEf) A) A A kn_lin) as wfor.
    apply Rlid_wfor; auto.

  assert (wf_typ ((X, bind_kn kn_lin)::nil) (typ_fvar X) kn_lin) as WFT.
    apply wf_typ_var.
       unfold binds. simpl. auto. 
       simpl_env. apply binds_one_3; auto.

  assert ((if X==X then A else typ_fvar X) = A) as HeqA.
    destruct (X==X); auto. contradict n; auto.

  assert (F_Related_ovalues (typ_fvar X) 
                                 ([(X,(Rlid E (length lEt) (length lEf) A))])
                                 ([(X, A)])
                                 ([(X, A)])
                                  vt1 vt2 E lEt).
        apply F_Related_ovalues_fvar_req. simpl.
        exists(Rlid E (length lEt) (length lEf) A).
        repeat(split; auto).
          apply Rlid_admissible.

  assert (F_Related_ovalues (typ_fvar X) 
                                 ([(X,(Rlid E (length lEt) (length lEf) A))])
                                 ([(X, A)])
                                 ([(X, A)])
                                  vf1 vf2 E lEf).
        apply F_Related_ovalues_fvar_req. simpl.
        exists(Rlid E (length lEt) (length lEf) A).
        repeat(split; auto).
          apply Rlid_admissible.

  apply JJ in H; auto using Rlid_wfor.
  destruct H as [v [v' [Htypingv [Htypingv' [[Hbrc Hv] [[Hbrc' Hv'] [R [Hb [_ [_ [Hadmin Hrel]]]]]]]]]]].
  
  analyze_binds Hb.
  unfold Rlid in Hrel. 
  destruct Hrel as [[lEnv1 [lEq1 [HHtypingv [HHtypingv' Heq_vv']]]] | [lEnv2 [lEq2 [HHtypingv [HHtypingv' Heq_vv']]]]].
    apply preservation_bigstep_red with (e':=v) in Htypingv; auto.
    simpl in Htypingv. rewrite HeqA in Htypingv.
    assert (dom (lEt ++ lEf) [=] dom lEnv1) as EQ.
      apply typing_ldom in HHtypingv.
      apply typing_ldom in Htypingv.
      rewrite <- Htypingv. rewrite <- HHtypingv.
      fsetdec.
    assert (length (lEt ++ lEf) = length lEt) as EQ'.
      apply uniq_domeq__lengtheq in EQ; auto.
        rewrite <- lEq1. auto.
        apply typing_regular in Htypingv. decompose [and] Htypingv. apply uniq_from_wf_lenv in H2; auto.
        apply typing_regular in HHtypingv. decompose [and] HHtypingv. apply uniq_from_wf_lenv in H2; auto.
    right.
    rewrite app_length in EQ'.
    assert (length lEf = 0) as J.
      clear lEq1. omega.
    apply zero_length__lempty in J. auto.

    apply preservation_bigstep_red with (e':=v) in Htypingv; auto.
    simpl in Htypingv. rewrite HeqA in Htypingv.
    assert (dom (lEt ++ lEf) [=] dom lEnv2) as EQ.
      apply preservation_bigstep_red with (e':=v') in Htypingv'; auto.
      apply typing_ldom in HHtypingv'.
      apply typing_ldom in Htypingv'.
      rewrite <- Htypingv'. rewrite <- HHtypingv'.
      fsetdec.
    assert (length (lEt ++ lEf) = length lEf) as EQ'.
      apply uniq_domeq__lengtheq in EQ; auto.
        rewrite <- lEq2. auto.
        apply typing_regular in Htypingv'. decompose [and] Htypingv'. apply uniq_from_wf_lenv in H2; auto.
        apply typing_regular in HHtypingv'. decompose [and] HHtypingv'. apply uniq_from_wf_lenv in H2; auto.
    left.
    rewrite app_length in EQ'.
    assert (length lEt = 0) as J.
      clear lEq2. omega.
    apply zero_length__lempty in J. auto.
Qed.

Definition T := (typ_all kn_nonlin 0).

Lemma T_is_type : type T.
Proof.
  unfold T.
  apply type_all with (L:={}).
    intros X Xnotin.
    unfold open_tt. simpl. auto.
Qed.

Lemma T_is_wft : forall E,  
  uniq E -> 
  wf_typ E T kn_nonlin.
Proof.
  intros E Uniq.
  unfold T.
  apply wf_typ_all with (L:=dom E).
    intros X Xnotin.
    unfold open_tt. simpl. 
    apply wf_typ_var; auto.
Qed.

Lemma OCBool_Empty : forall CBool K K', 
  typing nil nil CBool (typ_all kn_lin (typ_arrow K (typ_bvar 0) (typ_arrow K' (typ_bvar 0) (typ_bvar 0)))) ->
  False.
Proof.
  intros CBool K K' H.
  assert (J:=@OCBool_Identification CBool K K' H). clear H.
  pick fresh x.  pick fresh y.
  assert (value (exp_abs kn_lin T x)) as Valuet.
    apply value_abs.
      apply expr_abs with  (L:={{x}} `union` {{y}}) ; auto.
        apply T_is_type.
        intros x0 x0notin.
        unfold open_ee. simpl. auto.

  assert (value (exp_abs kn_lin T y)) as Valuef.  
    apply value_abs.
      apply expr_abs with  (L:={{x}} `union` {{y}}) ; auto.
        apply T_is_type.
        intros x0 x0notin.
        unfold open_ee. simpl. auto.

  assert (typing nil [(x, lbind_typ T)] 
                      (exp_abs kn_lin T x)
                      (typ_arrow kn_lin T T)) as Typingt.
    apply typing_abs with  (L:={{x}} `union` {{y}}) ; auto.
      apply wf_typ_all with (L:={{x}} `union` {{y}}); auto.
        intros X Xnotin.
        unfold open_tt. simpl.
        apply wf_typ_var; auto.

      intros x0 x0notin.
      unfold open_ee. simpl.
      apply typing_lvar.
         rewrite_env ([(x, lbind_typ T)]++nil).
         apply wf_lenv_typ; auto.
           simpl_env. apply wf_lenv_empty; auto.
           rewrite_env ([(x0, bind_typ T)]++nil).
           apply wf_env_typ; auto.
             apply T_is_wft; auto.
       
       apply wf_typ_sub.    
         apply T_is_wft; auto.
         
       intro JJ. inversion JJ.

  assert (typing nil [(y, lbind_typ T)] 
                      (exp_abs kn_lin T y)
                      (typ_arrow kn_lin T T)) as Typingf.
    apply typing_abs with  (L:={{x}} `union` {{y}}) ; auto.
      apply wf_typ_all with (L:={{x}} `union` {{y}}); auto.
        intros X Xnotin.
        unfold open_tt. simpl.
        apply wf_typ_var; auto.

      intros x0 x0notin.
      unfold open_ee. simpl.
      apply typing_lvar.
         rewrite_env ([(y, lbind_typ T)]++nil).
         apply wf_lenv_typ; auto.
           simpl_env. apply wf_lenv_empty; auto.
           rewrite_env ([(x0, bind_typ T)]++nil).
           apply wf_env_typ; auto.
             apply T_is_wft; auto.
       
       apply wf_typ_sub.    
         apply T_is_wft; auto.
         
       intro JJ. inversion JJ.

  assert (disjoint [(x, lbind_typ T)] [(y, lbind_typ T)]) as Disj.
    auto.

  assert (Rlid nil 1 1 (typ_arrow kn_lin T T) (exp_abs kn_lin T x) (exp_abs kn_lin T x)) as Rlidx.
    unfold Rlid.
    left. exists [(x, lbind_typ T)]. split; auto.

  assert (Rlid nil 1 1 (typ_arrow kn_lin T T) (exp_abs kn_lin T y) (exp_abs kn_lin T y)) as Rlidy.
    unfold Rlid.
    right. exists [(y, lbind_typ T)]. split; auto.

  destruct (@J nil [(x, lbind_typ T)] [(y, lbind_typ T)] 
                                 (exp_abs kn_lin T x) (exp_abs kn_lin T x)
                                 (exp_abs kn_lin T y) (exp_abs kn_lin T y)
                                 (typ_arrow kn_lin T T)
                                 Valuet Valuet Valuef Valuef
                                 Typingt Typingt Typingf Typingf
                                 Disj Rlidx Rlidy) as [EQ | EQ]; 
    inversion EQ.
Qed.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../../../metatheory" "-I" "../linf") ***
*** End: ***
 *)
