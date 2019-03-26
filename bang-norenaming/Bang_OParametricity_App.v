(** Authors: Jianzhou Zhao. *)

Require Export Metatheory.
Require Import Bang_Definitions.
Require Import Bang_Infrastructure.
Require Import Bang_Lemmas.
Require Import Bang_Soundness.
Require Import Bang_OParametricity.
Require Import Bang_Renaming.

Export OParametricity.

(***************************************************************)
(** *                Beta Eta Equivalence                      *)
(***************************************************************)
Inductive beta_eta_eq : env -> lenv -> exp -> exp -> typ -> Prop :=
  | bee_refl : forall E lA lE e t, 
      uniq lA ->
      dom lE [=] dom lA ->
      typing E lE e t ->
      beta_eta_eq E lA e e t
  | bee_sym : forall E lA e e' t, 
      beta_eta_eq E lA e e' t -> 
      beta_eta_eq E lA e' e t
  | bee_trans : forall E lA e e' e'' t, 
      beta_eta_eq E lA e e' t -> 
      beta_eta_eq E lA e' e'' t -> 
      beta_eta_eq E lA e e'' t 
  | bee_red : forall E lA lE e v t, 
      uniq lA ->
      dom lE [=] dom lA ->
      typing E lE e t ->
      bigstep_red e v -> 
      beta_eta_eq E lA e v t
  | bee_congr_app : forall E lA1 lA2 lA e1 e1' e2 e2' t1 t2,
      uniq lA ->
      uniq (lA1 ++ lA2) ->
      beta_eta_eq E lA1 e1 e1' (typ_arrow t1 t2) -> 
      beta_eta_eq E lA2 e2 e2' t1 -> 
      dom (lA1 ++ lA2) [=] dom lA ->
      beta_eta_eq E lA (exp_app e1 e2) (exp_app e1' e2') t2
  | bee_congr_bang : forall E e e' t,
      beta_eta_eq E nil e e' t -> 
      beta_eta_eq E nil (exp_bang e) (exp_bang e') (typ_bang t)
  .  

Hint Resolve bee_sym bee_congr_bang.

Lemma typing_uniqlE : forall E lE e t,
  typing E lE e t ->
  uniq lE.
Proof.
  intros E lE e t H.
  apply typing_regular in H.
  decompose [and] H. clear H.
  apply uniq_from_wf_lenv in H2; auto.
Qed.

Lemma bee_uniqlE : forall E lE e e' t,
  beta_eta_eq E lE e e' t -> uniq lE.
Proof.
  induction 1; auto.
Qed.

Lemma bee_disjoint : forall E lE e e' t,
  beta_eta_eq E lE e e' t ->
  disjoint E lE.
Proof.
  intros E lE e e' t H.
  induction H; auto.
    apply typing_regular in H1.
    decompose [and] H1. clear H1.
    apply disjoint_wf_lenv in H4.
    solve_uniq.

    apply typing_regular in H1.
    decompose [and] H1. clear H1.
    apply disjoint_wf_lenv in H5.
    solve_uniq.
    
    simpl_env in H3.
    solve_uniq.
Qed.

Lemma bee_ldom : forall E lE e e' t,
  beta_eta_eq E lE e e' t ->
  AtomSetImpl.diff (fv_ee e) (gdom_env E) [=] dom lE /\
  AtomSetImpl.diff (fv_ee e') (gdom_env E) [=] dom lE.
Proof.
  induction 1; auto.
    apply typing_ldom in H1. split; fsetdec.

    destruct IHbeta_eta_eq; auto.

    destruct IHbeta_eta_eq1.
    destruct IHbeta_eta_eq2.  
    split; auto.

    assert (J:=H1).
    apply preservation_bigstep_red with (e':=v) in J; auto.
    apply typing_ldom in H1. 
    apply typing_ldom in J. 
    split; fsetdec.

    destruct IHbeta_eta_eq1.
    destruct IHbeta_eta_eq2.
    simpl_env in H3.
    rewrite <- H3. simpl.
    split; fsetdec.
Qed.    

Lemma nonempty_dom__isnt__empty_dom : forall a D,
  {} [=] add a D ->
  False.
Proof. 
  intros.
  assert (a `in` add a D) as a_in_empty. auto.
  rewrite <- H in a_in_empty.
  contradict a_in_empty.
  fsetdec.
Qed.

Lemma empty_domeq_inv : forall A (D:list (atom*A)),
  {} [=] dom D ->
  D = nil.
Proof.
  intros A D H. 
  destruct D; auto.
    destruct p. 
    simpl in H.
    apply nonempty_dom__isnt__empty_dom in H.
    inversion H.
Qed.

Lemma bee_domeq : forall E lE lE' e e' t,
  beta_eta_eq E lE e e' t ->
  dom lE [=] dom lE' ->
  uniq lE' ->
  beta_eta_eq E lE' e e' t.
Proof.
  intros E lE lE' e e' t H DomEq UniqlE'.
  generalize dependent lE'.
  induction H; intros; auto.
    apply bee_refl with (lE:=lE); auto.
      fsetdec.

    apply bee_trans with (e':=e'); eauto.

    apply bee_red with (lE:=lE); auto.
      fsetdec.

    apply bee_congr_app with (lA1:=lA1)(lA2:=lA2)(t1:=t1); auto.
      fsetdec.

    simpl in DomEq.
    apply empty_domeq_inv in DomEq. subst.
    apply bee_congr_bang; auto.
Qed.

Lemma bee_eq_lenv_left : forall E lE e e' t lE',
  beta_eta_eq E lE e e' t ->
  typing E lE' e t ->
  dom lE [=] dom lE'.
Proof.
  intros.
  apply bee_ldom in H.
  destruct H.
  rewrite <- H.
  apply typing_ldom in H0.
  rewrite <- H0.
  fsetdec.
Qed.

Lemma bee_eq_lenv_right : forall E lE e e' t lE',
  beta_eta_eq E lE e e' t ->
  typing E lE' e' t ->
  dom lE [=] dom lE'.
Proof.
  intros.
  apply bee_ldom in H.
  destruct H.
  rewrite <- H1.
  apply typing_ldom in H0.
  rewrite <- H0.
  fsetdec.
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

Lemma subst_atom_lenv_eqdom : forall lE lE' x y,
  uniq lE ->
  uniq lE' ->
  dom lE [=] dom lE' ->
  dom (subst_atom_lenv lE x y) [=] dom (subst_atom_lenv lE' x y).
Proof.
  intros lE lE' x y UniqlE UniqlE' H.
  generalize dependent lE'.
  generalize dependent x.
  generalize dependent y.
  induction UniqlE; intros.
    inversion UniqlE'; subst; simpl; auto.
      simpl in H.
      apply nonempty_dom__isnt__empty_dom in H.
      inversion H.

    assert (x `in` dom lE') as x_in_lE'.
      rewrite <- H0. simpl. auto.
    assert (J:=UniqlE').
    apply uniq_binds_inv with (x:=x) in J; auto.
    destruct J as [E1' [E2' [b [EQ1' Uniq12']]]]; subst.

    assert (dom E [=] dom (E1'++E2')) as EQ.
      assert (x `notin` dom E1' `union` dom E2') as xnE12'.
        clear - UniqlE'. solve_uniq.
      clear - xnE12' H H0.
      simpl_env in H0.
      simpl_env.
      assert (dom E [=] AtomSetImpl.diff (union {{x}} (dom E)) {{x}}) as Diff1.
        clear - H. fsetdec.
      assert (dom E1' `union` dom E2' [=] AtomSetImpl.diff (union (dom E1') (union {{x}} (dom E2'))) {{x}}) as Diff2.
        clear - xnE12'. fsetdec.
      rewrite Diff1. rewrite Diff2.
      rewrite H0. clear. fsetdec.
    apply IHUniqlE with (x:=x0)(y:=y) in EQ; auto.
    rewrite subst_atom_lenv_app.
    rewrite subst_atom_lenv_app.
    rewrite subst_atom_lenv_app.
    simpl_env.
    rewrite EQ.
    rewrite subst_atom_lenv_app.
    simpl_env.
    simpl.
    destruct (x0==x); subst; simpl; 
      fsetdec.
Qed.

Lemma subst_atom_lenv_in_dom : forall lE lE1 lE2 x y (b:lbinding),
  uniq lE ->
  uniq (lE1++[(x,b)]++lE2) ->
  dom lE [=] dom (lE1++[(x,b)]++lE2) ->
  dom (subst_atom_lenv lE x y) [=] dom (lE1++[(y,b)]++lE2).
Proof.
  intros lE lE1 lE2 x y b UniqlE Uniq Domeq.
  assert (J:=@subst_atom_lenv_eqdom lE (lE1++[(x,b)]++lE2) x y UniqlE Uniq Domeq).
  rewrite J.
  rewrite subst_atom_lenv_app.
  rewrite subst_atom_lenv_app. 
  simpl_env.
  assert (x `notin` dom lE1) as xnlE1.
    clear - Uniq. solve_uniq.
  rewrite <- subst_atom_lenv_notin_inv; auto.
  assert (x `notin` dom lE2) as xnlE2.
    clear - Uniq. solve_uniq.
  rewrite <- subst_atom_lenv_notin_inv with (lE:=lE2); auto.      
  simpl.
  destruct (x==x); simpl.
    fsetdec.
    contradict n; auto.
Qed.

Lemma bee_lin_renaming : forall E lE e e' t (x y:atom),
  beta_eta_eq E lE e e' t ->
  x `notin` dom E ->
  y `notin` dom E `union` dom lE ->
  beta_eta_eq E (subst_atom_lenv lE x y) (subst_ee x y e) (subst_ee x y e') t.
Proof.
  intros E lE e e' t x y Bee xnotin ynotin.
  destruct (@in_dec x (dom lE)) as [xin | xnotin'].
  Case "xin".
  generalize dependent x.
  generalize dependent y.
  induction Bee; intros; subst; auto.
    SCase "refl".
    apply bee_refl with (lE:=subst_atom_lenv lE x y).
      apply uniq_renaming; auto.

      apply subst_atom_lenv_eqdom; auto.
        apply typing_uniqlE in H1; auto.

      apply typing_lin_renaming; auto.
       rewrite H0. simpl_env. fsetdec.

    SCase "trans".
    apply bee_trans with (e':=subst_ee x y e'); eauto.

    SCase "red".
    assert (y `notin` dom lE) as ynlE.
      rewrite H0. simpl_env. fsetdec.
    apply bee_red with (lE:=subst_atom_lenv lE x y); auto.
      apply uniq_renaming; auto.

      apply subst_atom_lenv_eqdom; auto.
        apply typing_uniqlE in H1; auto.

      apply typing_lin_renaming; auto.

      apply bigstep_red_renaming_one; auto.
        apply notin_fv_ee_typing with (y:=y) in H1; auto.

    SCase "congr_app".
    simpl.
    destruct (@in_dec x (dom lA1)) as [xinlA1 | xnotinlA1].
      SSCase "xinlA1".
      destruct (@in_dec x (dom lA2)) as [xinlA2 | xnotinlA2].
        SSSCase "xinlA2".
        clear - xinlA1 xinlA2 H0.
        contradict xinlA1. solve_uniq.
       
        SSSCase "xnotinlA2".
        apply bee_congr_app with (lA1:=subst_atom_lenv lA1 x y)(lA2:=lA2)(t1:=t1); auto.
          apply uniq_renaming; auto.

          assert (y `notin` dom lA1 `union` dom lA2) as ynlA12.
            simpl_env in H1. rewrite H1. 
            fsetdec.
          clear - H0 ynlA12.
          assert (disjoint (subst_atom_lenv lA1 x y) lA2) as Disj.
            assert (disjoint lA1 lA2) as Disj. solve_uniq.
            destruct_uniq.
            generalize dependent lA2.
            generalize dependent y.
            induction H0; simpl; intros; auto.
              destruct (x==x0); subst.
                 solve_uniq.
                 solve_uniq.
          destruct_uniq.
          assert (uniq (subst_atom_lenv lA1 x y)) as J.
            apply uniq_renaming; auto.
          apply uniq_app_4; auto.

          apply IHBee1; auto.
            simpl_env in H1. rewrite <- H1 in ynotin. 
            fsetdec.
                    
          rewrite <- subst_ee_fresh; auto.
            rewrite <- subst_ee_fresh; auto.
              clear - xnotin xnotinlA2 Bee2. 
              apply bee_ldom in Bee2.
              destruct Bee2 as [_ J].
              apply dom__gdom in xnotin.
              fsetdec.
            clear - xnotin xnotinlA2 Bee2. 
            apply bee_ldom in Bee2.
            destruct Bee2 as [J _].
            apply dom__gdom in xnotin.
            fsetdec.

          assert (J:=@subst_atom_lenv_eqdom (lA1++lA2) lA x y H0 H H1).
          rewrite <- J.
          rewrite subst_atom_lenv_app.
          simpl_env.
          rewrite <- subst_atom_lenv_notin_inv with (lE:=lA2); auto.
          fsetdec.

      SSCase "xnotinlA1".
      destruct (@in_dec x (dom lA2)) as [xinlA2 | xnotinlA2].
        SSSCase "xinlA2".
        apply bee_congr_app with (lA2:=subst_atom_lenv lA2 x y)(lA1:=lA1)(t1:=t1); auto.
          apply uniq_renaming; auto.

          assert (y `notin` dom lA1 `union` dom lA2) as ynlA12.
            simpl_env in H1. rewrite H1. 
            fsetdec.
          clear - H0 ynlA12.
          assert (disjoint lA1 (subst_atom_lenv lA2 x y)) as Disj.
            assert (disjoint lA1 lA2) as Disj. solve_uniq.
            destruct_uniq.
            generalize dependent lA1.
            generalize dependent y.
            generalize dependent x.
            induction UniqTac; simpl; intros; auto.
              destruct (x0==x); subst.
                 assert (disjoint lA1 E) as Disj1. solve_uniq.
                 apply IHUniqTac with (x:=x)(y:=y) in Disj1; auto.

                 assert (disjoint lA1 E) as Disj1. solve_uniq.
                 apply IHUniqTac with (x:=x0)(y:=y) in Disj1; auto.
                 simpl_env.             
                 destruct_uniq.
                 clear - Disj1 Disj. solve_uniq.
          destruct_uniq.
          assert (uniq (subst_atom_lenv lA2 x y)) as J.
            apply uniq_renaming; auto.
          apply uniq_app_4; auto.

          rewrite <- subst_ee_fresh; auto.
            rewrite <- subst_ee_fresh; auto.
              clear - xnotin xnotinlA1 Bee1. 
              apply bee_ldom in Bee1.
              destruct Bee1 as [_ J].
              apply dom__gdom in xnotin.
              fsetdec.
            clear - xnotin xnotinlA1 Bee1. 
            apply bee_ldom in Bee1.
            destruct Bee1 as [J _].
            apply dom__gdom in xnotin.
            fsetdec.

          apply IHBee2; auto.
            simpl_env in H1. rewrite <- H1 in ynotin. 
            fsetdec.
                    
          assert (J:=@subst_atom_lenv_eqdom (lA1++lA2) lA x y H0 H H1).
          rewrite <- J.
          rewrite subst_atom_lenv_app.
          simpl_env.
          rewrite <- subst_atom_lenv_notin_inv with (lE:=lA1); auto.
          fsetdec.

        SSSCase "xnotinlA2".
        clear - xnotinlA1 xnotinlA2 H1 xin.
        assert (x `in` dom lA1 `union` dom lA2) as xinlA12.
          simpl_env in H1. rewrite H1.
          fsetdec.
        contradict xinlA12. fsetdec.

    SCase "congr_bang".
    simpl. apply bee_congr_bang; auto.
      apply IHBee; auto.

  Case "xnotin".
    assert (J:=Bee).
    apply bee_ldom in J. destruct J as [J J'].
    rewrite <- subst_ee_fresh; auto.
      rewrite <- subst_ee_fresh; auto.
        rewrite <- subst_atom_lenv_notin_inv; auto.
        
        clear J ynotin Bee. 
        apply dom__gdom in xnotin.
        fsetdec.

      clear J' ynotin Bee. 
      apply dom__gdom in xnotin.
      fsetdec.
Qed.

(***************************************************************)
(** *                           Relations                      *)
(***************************************************************)
Definition Rfun Env l (A A':typ) (f:exp) (v v':exp) : Prop := 
  exists lEnv,
  length lEnv = l /\ 
  typing Env lEnv v A /\ typing Env lEnv v' A' /\
  typing Env nil f (typ_arrow A A') /\
  beta_eta_eq Env lEnv (exp_app f v) v' A'
  .

Definition Rid Env l (A:typ) (v v':exp) : Prop := 
  exists lEnv,
  length lEnv = l /\ 
  typing Env lEnv v A /\ typing Env lEnv v' A /\ beta_eta_eq Env lEnv v v' A
  .

Lemma Rfun_wfor : forall Env l A A' a,
  wf_typ Env A -> 
  wf_typ Env A' -> 
  wfor Env (Rfun Env l A A' a) A A'.
Proof.
  intros.
  split; auto.
Qed.

Lemma Rid_wfor : forall Env l A,
  wf_typ Env A -> 
  wfor Env (Rid Env l A) A A.
Proof.
  intros.
  split; auto.
Qed.

(***************************************************************)
(** *               Fundamental OParametricity                 *)
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
(** *                          Termination                     *)
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
(** *        Linear Identification with closed contexts        *)
(***************************************************************)
Lemma LIdentificationC : forall Id A A', 
  typing nil nil Id (typ_all (typ_arrow (typ_bvar 0) (typ_bvar 0))) ->
  (forall x y R, exists X,
   wfor nil R A A' ->
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
  intros Id A A' Htyping x y R.
  assert (wf_typ nil (typ_all (typ_arrow (typ_bvar 0) (typ_bvar 0)))) as WFT.
    apply typing_regular in Htyping. decompose [and] Htyping; auto.

  assert (F_Related_oterms (typ_all (typ_arrow (typ_bvar 0) (typ_bvar 0))) rho_nil delta_nil delta_nil Id Id nil nil) as Forel_All.
    apply fundamental_oparametricity; auto.
  destruct Forel_All as [v [v' [Htypingid [Htypingid' [Hn [Hn' Forel_All]]]]]].

  apply F_Related_ovalues_all_leq in Forel_All.
  destruct Forel_All as [Hv [Hv' [L' Hall]]]; subst.

  pick fresh X. 
  exists (X). intros Hwfor Hterm.
  assert (X `notin` L') as Fr'. auto.
  destruct (@Hall X A A' R Fr') as [w [w' [Hnorm_vt2w [Hnorm_v't2'w' Hrel_wft]]]]; auto.
  unfold open_tt in*. simpl in *.

  assert (wf_typ ((X, bind_kn)::nil) (typ_arrow (typ_fvar X) (typ_fvar X))) as WFT'.
    eapply wf_typ_arrow; eauto.

  apply F_Related_ovalues_arrow_leq in Hrel_wft.
  destruct Hrel_wft as [Hw [Hw' Harrow]]; subst.
  simpl_env in *. 
  assert ((if X==X then A else typ_fvar X) = A) as Heq.
    destruct (X==X); auto. contradict n; auto.
  assert ((if X==X then A' else typ_fvar X) = A') as Heq'.
    destruct (X==X); auto. contradict n; auto.
  simpl in *.
  rewrite Heq in *. rewrite Heq' in *. clear Heq Heq'.

  destruct Hterm as [v0 [v'0 [Htypingv0 [Htypingv'0 [Hnorm [Hnorm' Hrel]]]]]]; subst.

  destruct (@Harrow nil x y) as [u [u' [Hn_wxu [Hn_w'x'u' Hrel_wft2]]]]; auto.
    simpl in Htypingv0.
    assert ((if X==X then A else typ_fvar X) = A).
      destruct (X==X); auto. contradict n; auto.
    rewrite H in Htypingv0.
    assumption.

    simpl in Htypingv'0.
    assert ((if X==X then A' else typ_fvar X) = A').
      destruct (X==X); auto. contradict n; auto.
    rewrite H in Htypingv'0.
    assumption.

    exists(v0). exists(v'0).
    split; auto.

  assert (normalize (exp_tapp Id A) w).
      apply congr_tapp with (v1:=v); auto.
      eapply type_from_wf_typ with (E:=@nil (atom*binding)); eauto using wfor_left_inv.

  assert (normalize (exp_tapp Id A') w').
      apply congr_tapp with (v1:=v'); auto.
      eapply type_from_wf_typ with (E:=@nil (atom*binding)); eauto using wfor_right_inv.
    
  assert (normalize (exp_app (exp_tapp Id A) x) u).
      apply congr_app with (v1:=w); auto.
        apply expr_tapp; auto.
          eapply type_from_wf_typ; eauto using wfor_left_inv.

  assert (normalize (exp_app (exp_tapp Id A') y) u').
      apply congr_app with (v1:=w'); auto.
        apply expr_tapp; auto.
          eapply type_from_wf_typ; eauto using wfor_right_inv.

  unfold F_Related_oterms. exists(u). exists(u').
    split; simpl.
    destruct (X==X); try solve [contradict n; auto].
    apply typing_app with (T1:=A) (D1:=nil) (D2:=nil); auto.
      assert (open_tt (typ_arrow (typ_bvar 0) (typ_bvar 0)) A = typ_arrow A A) as Heq.
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
    eapply typing_app with (T1:=A')(D1:=nil) (D2:=nil); auto.
      assert (open_tt (typ_arrow (typ_bvar 0) (typ_bvar 0)) A' = typ_arrow A' A') as Heq.
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

(** 
  forall I : \/X. X-oX. forall A A'. forall a: A-> A'. 
    a I[A] = I[A'] a

  The above lemma implies the polymophic function I can only be 
  identity function. This can be proved by contradiction.

  The definition of identity function is
    forall A (v:A). I[A]v = v,  where '=' should be the beta-eta-equivalence.
  The negation of the above defn is 
    ex A, ex v:A, I[A]v <> v

  If I is not an identity function, without lose of generality, suppose
       exist A0, exists v0:A0, s.t. I[A0] v0 = v' <> v0
  We can pick a function a:A0->A0 which is defined as
    a u  = v0 if u = v'
    a u = u otherwise
  then, 
     a (I[A0] v0) = a (I[A0] v0) = a v' = v0
     I[A0] (a v0) = I[A0] v0 = v'
  We proved a (I[A0] v0) <> I[A0] (a v0) since v0 <> v',
  but this is contradictary to the above lemma.

  So I can only be an identity function.
*)
Corollary Rearrangement_LIdentificationC : forall Id a A A', 
  typing nil nil Id (typ_all (typ_arrow (typ_bvar 0) (typ_bvar 0))) ->
  typing nil nil a (typ_arrow A A') ->
  (forall x, 
    typing nil nil x A ->
    Rfun nil 0 A A' a (exp_app (exp_tapp Id A) x) (exp_app (exp_tapp Id A') (exp_app a x))
  ).
Proof.
  intros Id a A A' Htypingid Htypinga x Htypingx.
  assert (exists x0, normalize x x0) as Hn_xx0.
    apply strong_normalization with (t:=A); auto.
  assert  (exists x'0, normalize (exp_app a x) x'0) as Hn_axx'0.
    apply strong_normalization with (t:=A'); auto.
      eapply typing_app with (T1:=A); eauto.

  assert (wf_typ nil A) as HwftA. auto.
  assert (wf_typ nil A') as HwftA'. 
    apply typing_regular in Htypinga. decompose [and] Htypinga.
    apply wft_arrow_inv in H3. destruct H3; auto.
  destruct (@LIdentificationC Id A A' Htypingid x (exp_app a x) (Rfun nil 0 A A' a)) as [X JJ].

  (* x and  (exp_app a x) are related as Rfun*)
  assert (wf_typ ((X, bind_kn)::nil) (typ_fvar X)) as WFT.
    apply wf_typ_var; unfold binds; simpl; auto.

  destruct Hn_xx0 as [x0 [Hbrc_xx0 Hx0]]. 
  destruct Hn_axx'0 as [x'0 [Hbrc_axx'0 Hx'0]].
  assert (F_Related_oterms (typ_fvar X) 
                                 ([(X,(Rfun nil 0 A A' a))])
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
        apply typing_app with (T1:=A) (D1:=nil) (D2:=nil); auto.
        contradict n; auto.

      unfold normalize.
      split; auto.
      split; auto.
      SCase "Fvalues".
        apply F_Related_ovalues_fvar_req. simpl.
        exists(Rfun nil 0 A A' a).
        repeat(split; auto).
           exists nil.
           repeat(split; auto).
           SSCase "Typing".
           destruct (X==X); try solve [contradict n; auto].
             apply preservation_normalization with (e:=x); auto.
               unfold normalize; auto.
           SSCase "Typing".
           destruct (X==X); try solve [contradict n; auto].
             apply preservation_normalization with (e:=exp_app a x); auto.
               apply typing_app with (T1:=A)(D1:=nil) (D2:=nil); auto.
                 unfold normalize; auto.
           SSCase "Beta-Eta-Equivalence".
           apply bee_trans with (e':=(exp_app a x)); auto.
             apply bee_congr_app with (lA1:=nil)(lA2:=nil)(t1:=A); auto.
               apply bee_refl with (lE:=nil); auto.
                 apply bee_sym.
                 apply bee_red with (lE:=nil); auto.
             apply bee_red with (lE:=nil); eauto.
     
  (* Id[A] x and  Id[A'] (exp_app a x) are related as Rfun*)
  apply JJ in H; auto using Rfun_wfor.
  subst.
  destruct H as [v [v' [Htypingv [Htypingv' [[Hbrc Hv] [[Hbrc' Hv'] [R [Hb [_ [_ Hrel]]]]]]]]]]; subst.
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
      apply bee_congr_app with (lA1:=nil)(lA2:=nil)(t1:=A); eauto.
        apply bee_refl with (lE:=nil); auto.
        apply bee_red with (lE:=nil); auto.
      apply bee_trans with (e':=v'); auto.
        apply bee_sym.
        apply bee_red with (lE:=nil); auto.
Qed.

Corollary EQ_LIdentificationC : forall Id, 
  typing nil nil Id (typ_all (typ_arrow (typ_bvar 0) (typ_bvar 0))) ->
  (forall x y A, 
    Rid nil 0 A x y -> 
    Rid nil 0 A (exp_app (exp_tapp Id A) x) (exp_app (exp_tapp Id A) y)
  ).
Proof.
  intros Id Htypingid x y A HRid.
  unfold Rid in *. destruct HRid as [lEnv [lEq [Htypingx [Htypingy Heq_xy]]]].
  apply zero_length__lempty in lEq. subst lEnv.
  assert (exists x0, normalize x x0) as Hn_xx0.
    apply strong_normalization with (t:=A); auto.
  assert (exists y0, normalize y y0) as Hn_yy0.
    apply strong_normalization with (t:=A); auto.
  destruct Hn_xx0 as [x0 [Hbrc_xx0 Hx0]].
  destruct Hn_yy0 as [y0 [Hbrc_yy0 Hy0]].
  destruct (@LIdentificationC Id A A Htypingid x y (Rid nil 0 A)) as [X JJ].
  
  assert (wf_typ ((X, bind_kn)::nil) (typ_fvar X)) as WFT.
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
         exists nil.
         repeat(split; auto).
         destruct (X==X); try solve [contradict n; auto].
           apply preservation_normalization with (e:=x); auto.
            unfold normalize. auto.
         destruct (X==X); try solve [contradict n; auto].
           apply preservation_normalization with (e:=y); auto.
            unfold normalize. auto.
         apply bee_trans with (e':=x); auto.
           apply bee_sym.
             apply bee_red with (lE:=nil); auto.
           apply bee_trans with (e':=y); eauto.
             apply bee_red with (lE:=nil); auto.

  apply JJ in H; auto using Rid_wfor. subst.
  destruct H as [v [v' [Htypingv [Htypingv' [[Hbrc Hv] [[Hbrc' Hv'] [R [Hb [_ [_ Hrel]]]]]]]]]]; subst.
  assert ((if X==X then A else typ_fvar X) = A) as HeqA.
    destruct (X==X); auto. contradict n; auto.
  simpl in *. simpl_env in *.
  rewrite HeqA in *. clear HeqA.
  exists nil.
  repeat(split; auto). 
    apply bee_congr_app with (lA1:=nil) (lA2:=nil)(t1:=A); auto.
      apply bee_refl with (lE:=nil); auto.
        assert (open_tt (typ_arrow (typ_bvar 0) (typ_bvar 0)) A = typ_arrow A A) as Heq.
          unfold open_tt. auto.
        rewrite <- Heq.
        eapply typing_tapp; eauto.
Qed.

(***************************************************************)
(** *       Linear Boolean Function with closed contexts       *)
(***************************************************************)
Lemma LBooleanC : forall Bool A A', 
  typing nil nil Bool (typ_all (typ_arrow (typ_bvar 0) (typ_arrow (typ_bvar 0) (typ_bvar 0)))) ->
  (forall t1 t2 f1 f2 R, exists X, 
   wfor nil R A A' ->
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
                                 (exp_app (exp_app (exp_tapp Bool A) t1) f1) 
                                 (exp_app (exp_app (exp_tapp Bool A') t2) f2) nil nil).
Proof.
  intros Bool A A' Htyping_bool t1 t2 f1 f2 R.
  assert (wf_typ nil (typ_all (typ_arrow (typ_bvar 0) (typ_arrow (typ_bvar 0) (typ_bvar 0))))) as WFT.
    apply wf_typ_all with (L:={}).
      intros X Hfv.
      unfold open_tt. simpl. simpl_env. 
      eapply wf_typ_arrow; eauto.
        eapply wf_typ_arrow; eauto.

  assert (F_Related_oterms (typ_all (typ_arrow (typ_bvar 0) (typ_arrow (typ_bvar 0) (typ_bvar 0)))) rho_nil delta_nil delta_nil Bool Bool nil nil) as Forel_All.
    apply fundamental_oparametricity; auto.
  destruct Forel_All as [v [v' [Htypingid [Htypingid' [Hn [Hn' Forel_All]]]]]].

  apply F_Related_ovalues_all_leq in Forel_All.
  destruct Forel_All as [Hv [Hv' [L' Hall]]]; subst.

  pick fresh X. 
  exists (X). intros Hwfor Htermt Htermf.
  assert (wf_typ [(X,bind_kn)] (typ_fvar X)) as WFTvar. auto.
  assert (X `notin` L') as Fr'. auto.
  destruct (@Hall X A A' R Fr') as [w [w' [Hnorm_vt2w [Hnorm_v't2'w' Hrel_wft]]]]; auto.
  unfold open_tt in*. simpl in *.

  assert (wf_typ ((X, bind_kn)::nil) (typ_arrow (typ_fvar X) (typ_arrow (typ_fvar X) (typ_fvar X)))) as WFT'; eauto.

  apply F_Related_ovalues_arrow_leq in Hrel_wft.
  destruct Hrel_wft as [Hw [Hw' Harrow]]; subst.
  simpl_env in *.
  assert ((if X==X then A else typ_fvar X) = A) as Heq.
    destruct (X==X); auto. contradict n; auto.
  assert ((if X==X then A' else typ_fvar X) = A') as Heq'.
    destruct (X==X); auto. contradict n; auto.
  simpl in *.
  rewrite Heq in *. rewrite Heq' in *. clear Heq Heq'.

  destruct Htermt as [v0 [v'0 [Htypingv0 [Htypingv'0 [Hnorm [Hnorm' Hrelt]]]]]]; subst.
  destruct (@Harrow nil t1 t2) as [u [u' [Hn_wxu [Hn_w'x'u' Hrel_wft2]]]]; auto.
    simpl in Htypingv0.
    assert ((if X==X then A else typ_fvar X) = A).
      destruct (X==X); auto. contradict n; auto.
    rewrite H in Htypingv0.
    assumption.

    simpl in Htypingv'0.
    assert ((if X==X then A' else typ_fvar X) = A').
      destruct (X==X); auto. contradict n; auto.
    rewrite H in Htypingv'0.
    assumption.

    exists(v0). exists(v'0).
    split; auto.

  apply F_Related_ovalues_arrow_leq in Hrel_wft2.
  simpl_env in *.
  destruct Hrel_wft2 as [Hu [Hu' Harrow']]; subst.
  assert ((if X==X then A else typ_fvar X) = A) as Heq.
    destruct (X==X); auto. contradict n; auto.
  assert ((if X==X then A' else typ_fvar X) = A') as Heq'.
    destruct (X==X); auto. contradict n; auto.
  simpl in *.
  rewrite Heq in *. rewrite Heq' in *. clear Heq Heq'.

  destruct Htermf as [v1 [v'1 [Htypingv1 [Htypingv'1 [Hnorm1 [Hnorm1' Hrelf]]]]]]; subst.
  destruct (@Harrow' nil f1 f2) as [x [x' [Hn_uxu0 [Hn_u'x'u'0 Hrel_wft22]]]]; auto.
    simpl in Htypingv1.
    assert ((if X==X then A else typ_fvar X) = A).
      destruct (X==X); auto. contradict n; auto.
    rewrite H in Htypingv1.
    assumption.

    simpl in Htypingv'1.
    assert ((if X==X then A' else typ_fvar X) = A').
      destruct (X==X); auto. contradict n; auto.
    rewrite H in Htypingv'1.
    assumption.

    exists(v1). exists(v'1).
    split; auto.

  assert (wf_typ nil A) as wft_A.
      apply wfor_left_inv in Hwfor; auto.

  assert (type A) as TypeA. eauto using type_from_wf_typ.

  assert (wf_typ nil A') as wft_A'.
      apply wfor_right_inv in Hwfor; auto.

  assert (type A') as TypeA'. eauto using type_from_wf_typ.

  assert (normalize (exp_tapp Bool A) w).
      apply congr_tapp with (v1:=v); auto.

  assert (normalize (exp_tapp Bool A') w').
      apply congr_tapp with (v1:=v'); auto.
    
  assert (normalize (exp_app (exp_tapp Bool A) t1) u).
      apply congr_app with (v1:=w); auto.

  assert (normalize (exp_app (exp_tapp Bool A') t2) u').
      apply congr_app with (v1:=w'); auto.

  assert (normalize (exp_app (exp_app (exp_tapp Bool A) t1) f1) x).
      apply congr_app with (v1:=u); auto. 

  assert (normalize (exp_app (exp_app (exp_tapp Bool A') t2) f2) x').
      apply congr_app with (v1:=u'); auto.

  unfold F_Related_oterms. exists (x). exists (x').
    split; simpl.
    destruct (X==X); try solve [contradict n; auto].
    apply typing_app with (T1:=A)(D1:=nil) (D2:=nil); auto.
      apply typing_app with (T1:=A)(D1:=nil) (D2:=nil); auto.
        assert (open_tt (typ_arrow (typ_bvar 0) (typ_arrow (typ_bvar 0) (typ_bvar 0))) A = typ_arrow A (typ_arrow A A)) as Heq.
          unfold open_tt. auto.
        rewrite <- Heq.
        apply typing_tapp; auto.

        simpl in Htypingv1.
        assert ((if X==X then A else typ_fvar X) = A) as Heq.
          destruct (X==X); auto; contradict n; auto.
        rewrite Heq in Htypingv1; auto.

    split; simpl.
    destruct (X==X); try solve [contradict n; auto].
    apply typing_app with (T1:=A')(D1:=nil) (D2:=nil); auto.
      apply typing_app with (T1:=A')(D1:=nil) (D2:=nil); auto.
        assert (open_tt (typ_arrow (typ_bvar 0) (typ_arrow (typ_bvar 0) (typ_bvar 0))) A' = typ_arrow A' (typ_arrow A' A')) as Heq.
          unfold open_tt. auto.
        rewrite <- Heq.
        apply typing_tapp; auto.

        simpl in Htypingv'1.
        assert ((if X==X then A' else typ_fvar X) = A') as Heq.
          destruct (X==X); auto; contradict n; auto.
        rewrite Heq in Htypingv'1; auto.

    split; auto.
Qed.

Corollary Rearrangement_LBooleanC : forall Bool a A A', 
  typing nil nil Bool (typ_all (typ_arrow (typ_bvar 0) (typ_arrow (typ_bvar 0) (typ_bvar 0)))) ->
  typing nil nil a (typ_arrow A A') ->
  (forall t f, 
    typing nil nil t A -> 
    typing nil nil f A -> 
    Rfun nil 0 A A' a (exp_app (exp_app (exp_tapp Bool A) t) f) (exp_app (exp_app (exp_tapp Bool A') (exp_app a t)) (exp_app a f))
  ).
Proof.
  intros Bool a A A' Htypingid Htypinga t f 
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
  assert (wf_typ nil A) as HwftA. auto.
  assert (wf_typ nil A') as HwftA'. 
    apply typing_regular in Htypinga. decompose [and] Htypinga.
    apply wft_arrow_inv in H3. destruct H3; auto.
  destruct (@LBooleanC Bool A A' Htypingid t (exp_app a t) f (exp_app a f) (Rfun nil 0 A A' a)) as [X JJ].
  
(**)
  assert (wf_typ ((X, bind_kn)::nil) (typ_fvar X)) as WFT.
    apply wf_typ_var; unfold binds; simpl; auto.

  destruct Hn_tt0 as [t0 [Hbrc_tt0 Ht0]]. 
  destruct Hn_att'0 as [t'0 [Hbrc_att'0 Ht'0]].
  assert (F_Related_oterms (typ_fvar X)
                                 ([(X,(Rfun nil 0 A A' a))])
                                 ([(X, A)])
                                 ([(X, A')])
                                  t (exp_app a t) nil nil).
    unfold F_Related_oterms. exists (t0). exists (t'0).
      split; simpl.
      destruct (X==X); auto; contradict n; auto.
    
      split; simpl.
      destruct (X==X).
        apply typing_app with (T1:=A)(D1:=nil) (D2:=nil); auto.
        contradict n; auto.

      unfold normalize.
      split; auto.
      split; auto.
        apply F_Related_ovalues_fvar_req. simpl.
        exists(Rfun nil 0 A A' a).
        repeat(split; auto).
           exists nil.
           repeat(split; auto).     
           destruct (X==X); try solve [contradict n; auto].
             apply preservation_normalization with (e:=t); auto.
               unfold normalize; auto.
           destruct (X==X); try solve [contradict n; auto].
             apply preservation_normalization with (e:=exp_app a t); auto.
               apply typing_app with (T1:=A)(D1:=nil) (D2:=nil); auto.
                 unfold normalize; auto.
           apply bee_trans with (e':=exp_app a t); auto.
             apply bee_congr_app with (lA1:=nil)(lA2:=nil)(t1:=A); auto.
               apply bee_refl with (lE:=nil); auto.
               apply bee_sym.
                 apply bee_red with (lE:=nil); auto.
             apply bee_red with (lE:=nil); eauto.
(**)
     
  destruct Hn_ff0 as [f0 [Hbrc_ff0 Hf0]]. 
  destruct Hn_aff'0 as [f'0 [Hbrc_aff'0 Hf'0]].
  assert (F_Related_oterms (typ_fvar X) 
                                 ([(X,(Rfun nil 0 A A' a))])
                                 ([(X, A)])
                                 ([(X, A')])
                                  f (exp_app a f) nil nil).
    unfold F_Related_oterms. exists (f0). exists (f'0).
      split; simpl.
        destruct (X==X); auto; contradict n; auto.    
      split; simpl.
      destruct (X==X).
        apply typing_app with (T1:=A)(D1:=nil) (D2:=nil); auto.
        contradict n; auto.

      unfold normalize.
      split; auto.
      split; auto.
        apply F_Related_ovalues_fvar_req. simpl.
        exists(Rfun nil 0 A A' a).
        repeat(split; auto).
         exists nil.
         repeat(split; auto).
         destruct (X==X); try solve [contradict n; auto].
            apply preservation_normalization with (e:=f); auto.
               unfold normalize; auto.
         destruct (X==X); try solve [contradict n; auto].
           apply preservation_normalization with (e:=exp_app a f); auto.
             apply typing_app with (T1:=A)(D1:=nil) (D2:=nil); auto.
             unfold normalize; auto.
         apply bee_trans with (e':=exp_app a f); auto.
           apply bee_congr_app with (lA1:=nil)(lA2:=nil)(t1:=A); auto.
             apply bee_refl with (lE:=nil); auto.
             apply bee_sym.
               apply bee_red with (lE:=nil); auto.
           apply bee_red with (lE:=nil); eauto.
(**)

  apply JJ in H; auto using Rfun_wfor. subst.
  destruct H as [v [v' [Htypingv [Htypingv' [[Hbrc Hv] [[Hbrc' Hv'] [R [Hb [_ [_ Hrel]]]]]]]]]]; subst.
  unfold Rfun.
  repeat(split; auto).
    exists nil.
    repeat(split; auto).
    apply typing_app with (T1:=A)(D1:=nil) (D2:=nil); auto.
      apply typing_app with (T1:=A)(D1:=nil) (D2:=nil); auto.
        assert (open_tt (typ_arrow (typ_bvar 0) (typ_arrow (typ_bvar 0) (typ_bvar 0))) A = typ_arrow A (typ_arrow A A)) as Heq.
          unfold open_tt. auto.
        rewrite <- Heq.
        apply typing_tapp; auto.
    apply typing_app with (T1:=A')(D1:=nil) (D2:=nil); auto.
      apply typing_app with (T1:=A')(D1:=nil) (D2:=nil); auto.
        assert (open_tt (typ_arrow (typ_bvar 0) (typ_arrow (typ_bvar 0) (typ_bvar 0))) A' = typ_arrow A' (typ_arrow A' A')) as Heq.
          unfold open_tt. auto.
        rewrite <- Heq.
        apply typing_tapp; auto.
      apply typing_app with (T1:=A)(D1:=nil) (D2:=nil); auto.
      apply typing_app with (T1:=A)(D1:=nil) (D2:=nil); auto.
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
      apply bee_congr_app with (lA1:=nil)(lA2:=nil)(t1:=A); auto.
        apply bee_refl with (lE:=nil); auto.
        apply bee_red with (lE:=nil); auto.
      eapply bee_trans with (e':=v'); eauto.
        apply bee_sym.
        apply bee_red with (lE:=nil); auto.
Qed.

Corollary LBooleanC_Identification : forall Bool, 
  typing nil nil Bool (typ_all (typ_arrow (typ_bvar 0) (typ_arrow (typ_bvar 0) (typ_bvar 0)))) ->
  (forall t1 t2 f1 f2 A, 
    Rid nil 0 A t1 t2 -> 
    Rid nil 0 A f1 f2 -> 
    Rid nil 0 A (exp_app (exp_app (exp_tapp Bool A) t1) f1) (exp_app (exp_app (exp_tapp Bool A) t2) f2)
  ).
Proof.
  intros Bool Htyping_bool t1 t2 f1 f2 A HRidt HRidf.
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

  destruct (@LBooleanC Bool A A Htyping_bool t1 t2 f1 f2 (Rid nil 0 A)) as [X JJ]. 
  
  assert (wfor nil (Rid nil 0 A) A A) as wfor.
    apply Rid_wfor; auto.

  assert (wf_typ ((X, bind_kn)::nil) (typ_fvar X)) as WFT.
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
          exists nil. repeat(split; auto).
          destruct (X==X); try solve [contradict n; auto].
            apply preservation_normalization with (e:=t1); auto.
              unfold normalize. auto.
          destruct (X==X); try solve [contradict n; auto].
           apply preservation_normalization with (e:=t2); auto.
              unfold normalize. auto.
          apply bee_trans with (e':=t1); auto.
            apply bee_sym.
            apply bee_red with (lE:=nil); auto.

            apply bee_trans with (e':=t2); auto.
              apply bee_red with (lE:=nil); auto.

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
          exists nil. repeat(split; auto).
          destruct (X==X); try solve [contradict n; auto].
            apply preservation_normalization with (e:=f1); auto.
               unfold normalize. auto.
          destruct (X==X); try solve [contradict n; auto].
             apply preservation_normalization with (e:=f2); auto.
               unfold normalize. auto.
          apply bee_trans with (e':=f1); auto.
            apply bee_sym.
            apply bee_red with (lE:=nil); auto.

            apply bee_trans with (e':=f2); auto.
              apply bee_red with (lE:=nil); auto.

  apply JJ in H; auto using Rid_wfor.
  destruct H as [v [v' [Htypingv [Htypingv' [[Hbrc Hv] [[Hbrc' Hv'] [R [Hb [_ [_ Hrel]]]]]]]]]].
  exists nil. repeat(split; auto).
    apply typing_app with (T1:=A)(D1:=nil) (D2:=nil); auto.
      apply typing_app with (T1:=A)(D1:=nil) (D2:=nil); auto.
        assert (open_tt (typ_arrow (typ_bvar 0) (typ_arrow (typ_bvar 0) (typ_bvar 0))) A = typ_arrow A (typ_arrow A A)) as Heq.
          unfold open_tt. auto.
        rewrite <- Heq.
        apply typing_tapp; auto.
    apply typing_app with (T1:=A)(D1:=nil) (D2:=nil); auto.
      apply typing_app with (T1:=A)(D1:=nil) (D2:=nil); auto.
        assert (open_tt (typ_arrow (typ_bvar 0) (typ_arrow (typ_bvar 0) (typ_bvar 0))) A = typ_arrow A (typ_arrow A A)) as Heq.
          unfold open_tt. auto.
        rewrite <- Heq.
        apply typing_tapp; auto.
    analyze_binds Hb.
    destruct Hrel as [lEnv Hrel].
    decompose [and] Hrel. clear Hrel.
    apply zero_length__lempty in H. subst lEnv.
    simpl in *. simpl_env in *. rewrite HeqA in *. 
    apply bee_trans with (e':=v); auto.
      apply bee_red with (lE:=nil); auto.
      apply bee_trans with (e':=v'); auto.
        apply bee_sym.
        apply bee_red with (lE:=nil); auto.
Qed.

(***************************************************************)
(** *    Linear Identification with open contexts              *)
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

Lemma LIdentification : forall Id A A' E lE e0 e'0 R,
  typing nil nil Id (typ_all (typ_arrow (typ_bvar 0) (typ_bvar 0))) ->
  wfor E R A A' ->
  typing E lE e0 A ->
  typing E lE e'0 A' ->   
  exists X,
   wf_typ ([(X, bind_kn)]) (typ_fvar X) ->
   F_Related_oterms (typ_fvar X)
                                 ([(X,R)])
                                 ([(X,A)])
                                 ([(X,A')])
                                  e0 e'0 E lE ->
   F_Related_oterms (typ_fvar X)
                                 ([(X,R)])
                                 ([(X,A)])
                                 ([(X,A')])
                                 (exp_app (exp_tapp Id A) e0) (exp_app (exp_tapp Id A') e'0) E lE.
Proof.
  intros Id A A' E lE e0 e'0 R Htyping Hwfor Htypinge0 Htypinge'0.
  assert (wf_typ nil (typ_all (typ_arrow (typ_bvar 0) (typ_bvar 0)))) as WFT.
    apply typing_regular in Htyping. decompose [and] Htyping; auto.

  assert (F_Related_oterms (typ_all (typ_arrow (typ_bvar 0) (typ_bvar 0))) rho_nil delta_nil delta_nil Id Id E nil) as Forel_All.
    apply fundamental_oparametricity; auto.
  destruct Forel_All as [v [v' [Htypingid [Htypingid' [Hn [Hn' Forel_All]]]]]].

  apply F_Related_ovalues_all_leq in Forel_All.
  destruct Forel_All as [Hv [Hv' [L' Hall]]]; subst.

  pick fresh X. 
  exists (X). intros WFTvar Hrel.
  assert (X `notin` L') as Fr'. auto.
  destruct (@Hall X A A' R Fr') as [w [w' [Hnorm_vt2w [Hnorm_v't2'w' Hrel_wft]]]]; auto.
  unfold open_tt in*. simpl in *.

  assert (wf_typ ((X, bind_kn)::nil) (typ_arrow (typ_fvar X) (typ_fvar X))) as WFT'.
    eapply wf_typ_arrow; eauto.

  apply F_Related_ovalues_arrow_leq in Hrel_wft.
  destruct Hrel_wft as [Hw [Hw' Harrow]]; subst.
  simpl_env in *. 
  assert ((if X==X then A else typ_fvar X) = A) as Heq.
    destruct (X==X); auto. contradict n; auto.
  assert ((if X==X then A' else typ_fvar X) = A') as Heq'.
    destruct (X==X); auto. contradict n; auto.
  simpl in *.
  rewrite Heq in *. rewrite Heq' in *. clear Heq Heq'.

  destruct (@Harrow lE e0 e'0) as [u [u' [Hn_wxu [Hn_w'x'u' Hrel_wft2]]]]; auto.
     simpl_env. auto.

     destruct Hrel as [v0 [v'0 [Hte0 [Hte'0 [He0nv0 [He'0nv'0 Hrel]]]]]].
     exists v0. exists v'0.
     split; auto.

  assert (normalize (exp_tapp Id A) w).
      apply congr_tapp with (v1:=v); auto.

  assert (normalize (exp_tapp Id A') w').
      apply congr_tapp with (v1:=v'); auto.

  assert (normalize (exp_app (exp_tapp Id A) e0) u).
      apply congr_app with (v1:=w); auto.

  assert (normalize (exp_app (exp_tapp Id A') e'0) u').
      apply congr_app with (v1:=w'); auto.

  exists u. exists u'.
    split; simpl.
    destruct (X==X); try solve [contradict n; auto].
    apply typing_app with (T1:=A) (D1:=nil) (D2:=lE); auto.
      assert (open_tt (typ_arrow (typ_bvar 0) (typ_bvar 0)) A = typ_arrow A A) as Heq.
        unfold open_tt. auto.
      rewrite <- Heq.
      eapply typing_tapp; eauto using wfor_left_inv.

      apply lenv_split_left_empty; auto.

    split; simpl.
    destruct (X==X); try solve [contradict n; auto].
    eapply typing_app with (T1:=A') (D1:=nil) (D2:=lE); auto.
      assert (open_tt (typ_arrow (typ_bvar 0) (typ_bvar 0)) A' = typ_arrow A' A') as Heq.
        unfold open_tt. auto.
      rewrite <- Heq.
      eapply typing_tapp; eauto using wfor_right_inv.

      apply lenv_split_left_empty; auto.

    split; auto.
Qed.

Corollary EQ_LIdentification : forall Id, 
  typing nil nil Id (typ_all (typ_arrow (typ_bvar 0) (typ_bvar 0))) ->
  (forall E lE x0 y0 A,
    typing E lE x0 A ->
    typing E lE y0 A ->
    value x0 ->
    value y0 ->
    Rid E (length lE) A x0 y0 -> 
    Rid E (length lE) A (exp_app (exp_tapp Id A) x0) (exp_app (exp_tapp Id A) y0)
  ).
Proof.
  intros Id Htypingid E lE x0 y0 A Typingx0 Typingy0 Hvx0 Hvy0 HRid.
  unfold Rid in *. destruct HRid as [lEnv [lEq [Htypingx [Htypingy Heq_xy]]]].
  destruct (@LIdentification Id A A E lE x0 y0 (Rid E (length lE) A) Htypingid) as [X JJ]; auto using Rid_wfor.
  
  assert (wf_typ ((X, bind_kn)::nil) (typ_fvar X)) as WFT.
    apply wf_typ_var.
       unfold binds. simpl. auto. 
       simpl_env. apply binds_one_3; auto.

  assert (F_Related_oterms (typ_fvar X) 
                                 ([(X,(Rid E (length lE) A))])
                                 ([(X, A)])
                                 ([(X, A)])
                                  x0 y0 E lE).
    exists x0. exists y0. simpl.
    destruct (X==X); try solve [contradict n; auto].
    repeat(split; auto).
      apply F_Related_ovalues_fvar_req. simpl.
      exists(Rid E (length lE) A).
      repeat(split; auto).
        exists lEnv. repeat(split; auto).

  apply JJ in H; auto using Rid_wfor. subst.
  destruct H as [v [v' [Htypingv [Htypingv' [[Hbrc Hv] [[Hbrc' Hv'] [R [Hb [_ [_ Hrel]]]]]]]]]]; subst.
  assert ((if X==X then A else typ_fvar X) = A) as HeqA.
    destruct (X==X); auto. contradict n; auto.
  simpl in *. simpl_env in *.
  rewrite HeqA in *. clear HeqA.
  exists lEnv. repeat(split; auto).
    apply typing_app with (D1:=lempty)(D2:=lEnv)(T1:=A); auto.
      assert (open_tt (typ_arrow (typ_bvar 0) (typ_bvar 0)) A = typ_arrow A A) as Heq.
        unfold open_tt. auto.
      rewrite <- Heq.
      eapply typing_tapp; eauto.
        rewrite_env (nil++E++nil).
        apply typing_weakening; auto.
          simpl_env. auto.

      apply lenv_split_left_empty; auto.

    apply typing_app with (D1:=lempty)(D2:=lEnv)(T1:=A); auto.
      assert (open_tt (typ_arrow (typ_bvar 0) (typ_bvar 0)) A = typ_arrow A A) as Heq.
        unfold open_tt. auto.
      rewrite <- Heq.
      eapply typing_tapp; eauto.
        rewrite_env (nil++E++nil).
        apply typing_weakening; auto.
          simpl_env. auto.

      apply lenv_split_left_empty; auto.

    eapply bee_congr_app with (lA1:=lempty) (lA2:=lEnv) (t1:=A); eauto.
      apply bee_refl with (lE:=nil); auto.
      assert (open_tt (typ_arrow (typ_bvar 0) (typ_bvar 0)) A = typ_arrow A A) as Heq.
        unfold open_tt. auto.
      rewrite <- Heq.
      eapply typing_tapp; eauto.
        rewrite_env (nil++E++nil).
        apply typing_weakening; auto.
          simpl_env. auto.

     simpl. fsetdec.
Qed.

(***************************************************************)
(** *                Linear Boolean is Empty                   *)
(***************************************************************)
Lemma LBoolean : forall Bool A A' E lE0 lE1 e0 e'0 e1 e'1 R, 
  typing nil nil Bool (typ_all (typ_arrow (typ_bvar 0) (typ_arrow (typ_bvar 0) (typ_bvar 0)))) ->
  wfor E R A A' ->
  typing E lE0 e0 A ->
  typing E lE0 e'0 A' ->
  typing E lE1 e1 A ->
  typing E lE1 e'1 A' ->
  disjoint lE0 lE1 ->
  exists X, 
   F_Related_oterms (typ_fvar X) 
                                 ([(X,R)])
                                 ([(X,A)])
                                 ([(X,A')])
                                 e0 e'0 E lE0 ->
   F_Related_oterms (typ_fvar X) 
                                 ([(X,R)])
                                 ([(X,A)])
                                 ([(X,A')])
                                 e1 e'1 E lE1 ->
   F_Related_oterms (typ_fvar X) 
                                 ([(X,R)])
                                 ([(X,A)])
                                 ([(X,A')])
                                 (exp_app (exp_app (exp_tapp Bool A) e0) e1) 
                                 (exp_app (exp_app (exp_tapp Bool A') e'0) e'1) E (lE0 ++ lE1).
Proof.
  intros Bool A A' E lE0 lE1 e0 e'0 e1 e'1 R Htyping_bool Hwfor Htypinge0 Htypinge'0 Htypinge1 Htypinge'1 Disj.
  assert (wf_typ nil (typ_all (typ_arrow (typ_bvar 0) (typ_arrow (typ_bvar 0) (typ_bvar 0))))) as WFT.
    apply wf_typ_all with (L:={}).
      intros X Hfv.
      unfold open_tt. simpl. simpl_env. 
      eapply wf_typ_arrow; eauto.
        eapply wf_typ_arrow; eauto.

  assert (F_Related_oterms (typ_all (typ_arrow (typ_bvar 0) (typ_arrow (typ_bvar 0) (typ_bvar 0)))) rho_nil delta_nil delta_nil Bool Bool E nil) as Forel_All.
    apply fundamental_oparametricity; auto.
  destruct Forel_All as [v [v' [Htypingid [Htypingid' [Hn [Hn' Forel_All]]]]]].

  apply F_Related_ovalues_all_leq in Forel_All.
  destruct Forel_All as [Hv [Hv' [L' Hall]]]; subst.

  pick fresh X. 
  exists (X). intros Hrelt Hrelf.
  assert (wf_typ [(X,bind_kn)] (typ_fvar X)) as WFTvar. auto.
  assert (X `notin` L') as Fr'. auto.
  destruct (@Hall X A A' R Fr') as [w [w' [Hnorm_vt2w [Hnorm_v't2'w' Hrel_wft]]]]; auto.
  unfold open_tt in*. simpl in *.

  assert (wf_typ ((X, bind_kn)::nil) (typ_arrow (typ_fvar X) (typ_arrow (typ_fvar X) (typ_fvar X)))) as WFT'; eauto.

  apply F_Related_ovalues_arrow_leq in Hrel_wft.
  destruct Hrel_wft as [Hw [Hw' Harrow]]; subst.
  simpl_env in *.
  assert ((if X==X then A else typ_fvar X) = A) as Heq.
    destruct (X==X); auto. contradict n; auto.
  assert ((if X==X then A' else typ_fvar X) = A') as Heq'.
    destruct (X==X); auto. contradict n; auto.
  simpl in *.
  rewrite Heq in *. rewrite Heq' in *. clear Heq Heq'.

  destruct (@Harrow lE0 e0 e'0) as [u [u' [Hn_wxu [Hn_w'x'u' Hrel_wft2]]]]; auto.
     simpl_env. auto.

     destruct Hrelt as [v0 [v'0 [Hv0 [Hv'0 [He0nv0 [He'0nv'0 Hrelt]]]]]].
     exists v0. exists v'0.
     split; auto.

  apply F_Related_ovalues_arrow_leq in Hrel_wft2.
  simpl_env in *.
  destruct Hrel_wft2 as [Hu [Hu' Harrow']]; subst.
  assert ((if X==X then A else typ_fvar X) = A) as Heq.
    destruct (X==X); auto. contradict n; auto.
  assert ((if X==X then A' else typ_fvar X) = A') as Heq'.
    destruct (X==X); auto. contradict n; auto. 
  simpl in *.
  rewrite Heq in *. rewrite Heq' in *. clear Heq Heq'.

  assert (wf_typ E A) as wft_A.
      apply wfor_left_inv in Hwfor; auto.

  assert (type A) as TypeA. eauto using type_from_wf_typ.

  assert (wf_typ E A') as wft_A'.
      apply wfor_right_inv in Hwfor; auto.

  assert (type A') as TypeA'. eauto using type_from_wf_typ.

  assert (normalize (exp_tapp Bool A) w).
      apply congr_tapp with (v1:=v); auto.

  assert (normalize (exp_tapp Bool A') w').
      apply congr_tapp with (v1:=v'); auto.
    
  assert (normalize (exp_app (exp_tapp Bool A) e0) u) as Hn'_wxu.
      apply congr_app with (v1:=w); auto.

  assert (normalize (exp_app (exp_tapp Bool A') e'0) u') as Hn'_w'x'u'.
      apply congr_app with (v1:=w'); auto.

  destruct (@Harrow' lE1 e1 e'1) as [x [x' [Hn_uxu0 [Hn_u'x'u'0 Hrel_wft22]]]]; auto.
     apply wf_lenv_merge; auto.
     destruct Hrelf as [v1 [v'1 [Hv1 [Hv'1 [He1nv1 [He'1nv'1 Hrelf]]]]]].
     exists v1. exists v'1.
     split; auto.

  assert (normalize (exp_app (exp_app (exp_tapp Bool A) e0) e1) x).
      apply congr_app with (v1:=u); auto. 

  assert (normalize (exp_app (exp_app (exp_tapp Bool A') e'0) e'1) x').
      apply congr_app with (v1:=u'); auto. 

  exists x. exists x'.
    split; simpl.
    destruct (X==X); try solve [contradict n; auto].
    apply typing_app with (T1:=A)(D1:=lE0) (D2:=lE1); auto.
      apply typing_app with (T1:=A)(D1:=nil) (D2:=lE0); auto.
        assert (open_tt (typ_arrow (typ_bvar 0) (typ_arrow (typ_bvar 0) (typ_bvar 0))) A = typ_arrow A (typ_arrow A A)) as Heq.
          unfold open_tt. auto.
        rewrite <- Heq.
        apply typing_tapp; auto.

        apply lenv_split_left_empty; auto.
      apply disjoint__lenv_split; auto.

    split; simpl.
    destruct (X==X); try solve [contradict n; auto].
    apply typing_app with (T1:=A')(D1:=lE0) (D2:=lE1); auto.
      apply typing_app with (T1:=A')(D1:=nil) (D2:=lE0); auto.
        assert (open_tt (typ_arrow (typ_bvar 0) (typ_arrow (typ_bvar 0) (typ_bvar 0))) A' = typ_arrow A' (typ_arrow A' A')) as Heq.
          unfold open_tt. auto.
        rewrite <- Heq.
        apply typing_tapp; auto.

        apply lenv_split_left_empty; auto.
      apply disjoint__lenv_split; auto.

    split; auto.
Qed.

Definition Rlid Env l1 l2 (A:typ) (v v':exp) : Prop := 
  (exists lEnv1, (length lEnv1 = l1 /\ typing Env lEnv1 v A /\ typing Env lEnv1 v' A /\ beta_eta_eq Env lEnv1 v v' A)) \/
  (exists lEnv2, (length lEnv2 = l2 /\ typing Env lEnv2 v A /\ typing Env lEnv2 v' A /\ beta_eta_eq Env lEnv2 v v' A)).

Lemma Rlid_wfor : forall Env l1 l2 A,
  wf_typ Env A -> 
  wfor Env (Rlid Env l1 l2 A) A A.
Proof.
  intros.
  split; auto.
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

Corollary LBool_Identification : forall Bool, 
  typing nil nil Bool (typ_all (typ_arrow (typ_bvar 0) (typ_arrow (typ_bvar 0) (typ_bvar 0)))) ->
  (forall E lEt lEf et1 et2 ef1 ef2 vt1 vt2 vf1 vf2 A, 
    normalize et1 vt1 ->
    normalize et2 vt2 ->
    normalize ef1 vf1 ->
    normalize ef2 vf2 ->
    typing E lEt et1 A ->
    typing E lEt et2 A ->
    typing E lEf ef1 A ->
    typing E lEf ef2 A ->
    disjoint lEt lEf ->
    Rlid E (length lEt) (length lEf) A vt1 vt2 -> 
    Rlid E (length lEt) (length lEf) A vf1 vf2 -> 
    (lEt = nil \/ lEf = nil)
  ).
Proof.
  intros Bool Htyping_bool E lEt lEf et1 et2 ef1 ef2 vt1 vt2 vf1 vf2 A Hnt1 Hnt2 Hnf1 Hnf2 
    Htypinget1 Htypinget2 Htypingef1 Htypingef2 Disj HRlidt HRlidf.

  unfold Rlid in *. 

  destruct (@LBoolean Bool A A E lEt lEf et1 et2 ef1 ef2 (Rlid E (length lEt) (length lEf) A) Htyping_bool) as [X JJ]; auto using Rlid_wfor.
  
  assert (wfor E (Rlid E (length lEt) (length lEf) A) A A) as wfor.
    apply Rlid_wfor; auto.

  assert (wf_typ ((X, bind_kn)::nil) (typ_fvar X)) as WFT.
    apply wf_typ_var.
       unfold binds. simpl. auto. 
       simpl_env. apply binds_one_3; auto.

  assert ((if X==X then A else typ_fvar X) = A) as HeqA.
    destruct (X==X); auto. contradict n; auto.

  assert (F_Related_oterms (typ_fvar X) 
                                 ([(X,(Rlid E (length lEt) (length lEf) A))])
                                 ([(X, A)])
                                 ([(X, A)])
                                  et1 et2 E lEt).
    exists vt1. exists vt2. simpl.
    destruct (X==X); try solve [contradict n; auto].    
    repeat(split; auto).
        apply F_Related_ovalues_fvar_req. simpl.
        exists(Rlid E (length lEt) (length lEf) A).
        repeat(split; auto).
          destruct Hnt1; auto.
          destruct Hnt2; auto.

  assert (F_Related_oterms (typ_fvar X) 
                                 ([(X,(Rlid E (length lEt) (length lEf) A))])
                                 ([(X, A)])
                                 ([(X, A)])
                                  ef1 ef2 E lEf).
    exists vf1. exists vf2. simpl.
    destruct (X==X); try solve [contradict n; auto].    
    repeat(split; auto).
        apply F_Related_ovalues_fvar_req. simpl.
        exists(Rlid E (length lEt) (length lEf) A).
        repeat(split; auto).
          destruct Hnf1; auto.
          destruct Hnf2; auto.

  apply JJ in H; auto using Rlid_wfor.
  destruct H as [v [v' [Htypingv [Htypingv' [[Hbrc Hv] [[Hbrc' Hv'] [R [Hb [_ [_ Hrel]]]]]]]]]].
  
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

Definition T := (typ_all 0).

Lemma T_is_type : type T.
Proof.
  unfold T.
  apply type_all with (L:={}).
    intros X Xnotin.
    unfold open_tt. simpl. auto.
Qed.

Lemma T_is_wft : forall E,  
  uniq E -> 
  wf_typ E T.
Proof.
  intros E Uniq.
  unfold T.
  apply wf_typ_all with (L:=dom E).
    intros X Xnotin.
    unfold open_tt. simpl. 
    apply wf_typ_var; auto.
Qed.

Lemma LBool_Empty : forall Bool, 
  typing nil nil Bool (typ_all (typ_arrow (typ_bvar 0) (typ_arrow (typ_bvar 0) (typ_bvar 0)))) ->
  False.
Proof.
  intros Bool H.
  assert (J:=@LBool_Identification Bool H). clear H.
  pick fresh x.  pick fresh y.
  assert (value (exp_tabs x)) as Valuet.
    apply value_tabs.
      apply expr_tabs with  (L:={{x}} `union` {{y}}) ; auto.
        intros X0 X0notin.
        unfold open_te. simpl. auto.

  assert (value (exp_tabs y)) as Valuef.  
    apply value_tabs.
      apply expr_tabs with  (L:={{x}} `union` {{y}}) ; auto.
        intros X0 X0notin.
        unfold open_te. simpl. auto.

  assert (typing nil [(x, lbind_typ T)] 
                      (exp_tabs x)
                      (typ_all T)) as Typingt.
    apply typing_tabs with  (L:={{x}} `union` {{y}}) ; auto.
      intros X0 X0notin.
      unfold open_te. unfold open_tt. simpl.
      apply typing_lvar.
         rewrite_env ([(x, lbind_typ T)]++nil).
         apply wf_lenv_typ; auto.
           simpl_env. apply wf_lenv_empty; auto.
           rewrite_env ([(X0, bind_kn)]++nil).
           apply wf_env_kn; auto.
       
       apply T_is_wft; auto.
         
  assert (typing nil [(y, lbind_typ T)] 
                      (exp_tabs y)
                      (typ_all T)) as Typingf.
    apply typing_tabs with  (L:={{x}} `union` {{y}}) ; auto.
      intros X0 X0notin.
      unfold open_te. unfold open_tt. simpl.
      apply typing_lvar.
         rewrite_env ([(y, lbind_typ T)]++nil).
         apply wf_lenv_typ; auto.
           simpl_env. apply wf_lenv_empty; auto.
           rewrite_env ([(X0, bind_kn)]++nil).
           apply wf_env_kn; auto.

       apply T_is_wft; auto.
         
  assert (disjoint [(x, lbind_typ T)] [(y, lbind_typ T)]) as Disj.
    auto.

  assert (Rlid nil 1 1 (typ_all T) (exp_tabs x) (exp_tabs x)) as Rlidx.
    unfold Rlid.
    left. exists [(x, lbind_typ T)]. 
    split; auto. split; auto. split; auto.
    apply bee_refl with (lE:=[(x, lbind_typ T)]); auto.
      fsetdec.

  assert (Rlid nil 1 1 (typ_all T) (exp_tabs y) (exp_tabs y)) as Rlidy.
    unfold Rlid.
    right. exists [(y, lbind_typ T)].
    split; auto. split; auto. split; auto.
    apply bee_refl with (lE:=[(y, lbind_typ T)]); auto.
      fsetdec.

  assert (normalize (exp_tabs x) (exp_tabs x)) as Hnet.
    split; auto.

  assert (normalize (exp_tabs y) (exp_tabs y)) as Hnef.
    split; auto.

  destruct (@J nil [(x, lbind_typ T)] [(y, lbind_typ T)] 
                                 (exp_tabs x) (exp_tabs x)
                                 (exp_tabs y) (exp_tabs y)
                                 (exp_tabs x) (exp_tabs x)
                                 (exp_tabs y) (exp_tabs y)
                                 (typ_all T)
                                 Hnet Hnet Hnef Hnef
                                 Typingt Typingt Typingf Typingf
                                 Disj Rlidx Rlidy) as [EQ | EQ]; 
    inversion EQ.
Qed.

(***************************************************************)
(** *        Intuitionistic Identification                     *)
(***************************************************************)
Lemma IIdentification : forall Id A A' E e0 e'0 R, 
  typing nil nil Id (typ_all (typ_arrow (typ_bang (typ_bvar 0)) (typ_bvar 0))) ->
  wfor E R A A' ->
  typing E lempty e0 A ->
  typing E lempty e'0 A' ->   
  exists X,
   wf_typ ([(X, bind_kn)]) (typ_fvar X) ->
   F_Related_oterms (typ_fvar X)
                    ([(X,R)])
                    ([(X,A)])
                    ([(X,A')])
                    e0 e'0 E lempty ->
   F_Related_oterms (typ_fvar X)
                    ([(X,R)])
                    ([(X,A)])
                    ([(X,A')])
                    (exp_app (exp_tapp Id A) (exp_bang e0)) 
                    (exp_app (exp_tapp Id A') (exp_bang e'0)) E lempty.
Proof.
  intros Id A A' E e0 e'0 R Htyping Hwfor Htypinge0 Htypinge'0.
  assert (wf_typ nil (typ_all (typ_arrow (typ_bang (typ_bvar 0)) (typ_bvar 0)))) as WFT.
    apply typing_regular in Htyping. decompose [and] Htyping; auto.

  assert (F_Related_oterms (typ_all (typ_arrow (typ_bang (typ_bvar 0)) (typ_bvar 0))) rho_nil delta_nil delta_nil Id Id E nil) as Forel_All.
    apply fundamental_oparametricity; auto.
  destruct Forel_All as [v [v' [Htypingid [Htypingid' [Hn [Hn' Forel_All]]]]]].

  apply F_Related_ovalues_all_leq in Forel_All.
  destruct Forel_All as [Hv [Hv' [L' Hall]]]; subst.

  pick fresh X. 
  exists (X). intros WFTvar Hrel.
  assert (X `notin` L') as Fr'. auto.
  destruct (@Hall X A A' R Fr') as [w [w' [Hnorm_vt2w [Hnorm_v't2'w' Hrel_wft]]]]; auto.
  unfold open_tt in*. simpl in *.

  assert (wf_typ ((X, bind_kn)::nil) (typ_arrow (typ_bang (typ_fvar X)) (typ_fvar X))) as WFT'.
    eapply wf_typ_arrow; eauto.

  apply F_Related_ovalues_arrow_leq in Hrel_wft.
  destruct Hrel_wft as [Hw [Hw' Harrow]]; subst.
  simpl_env in *. 
  assert ((if X==X then A else typ_fvar X) = A) as Heq.
    destruct (X==X); auto. contradict n; auto.
  assert ((if X==X then A' else typ_fvar X) = A') as Heq'.
    destruct (X==X); auto. contradict n; auto.
  simpl in *.
  rewrite Heq in *. rewrite Heq' in *. clear Heq Heq'.

  destruct (@Harrow lempty (exp_bang e0) (exp_bang e'0)) as [u [u' [Hn_wxu [Hn_w'x'u' Hrel_wft2]]]]; auto.
     simpl_env. auto.

     destruct Hrel as [v0 [v'0 [Hte0 [Hte'0 [He0nv0 [He'0nv'0 Hrel]]]]]].
     exists (exp_bang e0).
     exists (exp_bang e'0).
     split. split; auto.
     split. split; auto.
         apply F_Related_ovalues_bang_req.
         split; auto. split; auto.
         exists e0. exists e'0.
         split; auto. split; auto.
         exists v0. exists v'0.
         split; auto.

  assert (normalize (exp_tapp Id A) w).
      apply congr_tapp with (v1:=v); auto.

  assert (normalize (exp_tapp Id A') w').
      apply congr_tapp with (v1:=v'); auto.

  assert (normalize (exp_app (exp_tapp Id A) (exp_bang e0)) u).
      apply congr_app with (v1:=w); auto.

  assert (normalize (exp_app (exp_tapp Id A') (exp_bang e'0)) u').
      apply congr_app with (v1:=w'); auto.

  exists u. exists u'.
    split; simpl.
    destruct (X==X); try solve [contradict n; auto].
    apply typing_app with (T1:=typ_bang A) (D1:=nil) (D2:=lempty); auto.
      assert (open_tt (typ_arrow (typ_bang (typ_bvar 0)) (typ_bvar 0)) A = 
              typ_arrow (typ_bang A) A) as Heq.
        unfold open_tt. auto.
      rewrite <- Heq.
      eapply typing_tapp; eauto using wfor_left_inv.

    split; simpl.
    destruct (X==X); try solve [contradict n; auto].
    eapply typing_app with (T1:=typ_bang A') (D1:=nil) (D2:=lempty); auto.
      assert (open_tt (typ_arrow (typ_bang (typ_bvar 0)) (typ_bvar 0)) A' = 
              typ_arrow (typ_bang A') A') as Heq.
        unfold open_tt. auto.
      rewrite <- Heq.
      eapply typing_tapp; eauto using wfor_right_inv.

    split; auto.
Qed.

Corollary EQ_IIdentification : forall Id, 
  typing nil nil Id (typ_all (typ_arrow (typ_bang (typ_bvar 0)) (typ_bvar 0))) ->
  (forall E x0 y0 A,
    typing E lempty x0 A ->
    typing E lempty y0 A ->
    value x0 ->
    value y0 ->
    Rid E 0 A x0 y0 -> 
    Rid E 0 A (exp_app (exp_tapp Id A) (exp_bang x0)) (exp_app (exp_tapp Id A) (exp_bang y0))
  ).
Proof.
  intros Id Htypingid E x0 y0 A Typingx0 Typingy0 Hvx0 Hvy0 HRid.
  unfold Rid in *. destruct HRid as [lEnv [lEq [Htypingx [Htypingy Heq_xy]]]].
  destruct (@IIdentification Id A A E x0 y0 (Rid E 0 A) Htypingid) as [X JJ]; auto using Rid_wfor.
  apply zero_length__lempty in lEq. subst.
  
  assert (wf_typ ((X, bind_kn)::nil) (typ_fvar X)) as WFT.
    apply wf_typ_var.
       unfold binds. simpl. auto. 
       simpl_env. apply binds_one_3; auto.

  assert (F_Related_oterms (typ_fvar X) 
                                 ([(X,(Rid E 0 A))])
                                 ([(X, A)])
                                 ([(X, A)])
                                  x0 y0 E lempty).
    exists x0. exists y0. simpl.
    destruct (X==X); try solve [contradict n; auto].
    repeat(split; auto).
      apply F_Related_ovalues_fvar_req. simpl.
      exists(Rid E 0 A).
      repeat(split; auto).
        exists lempty. repeat(split; auto).

  apply JJ in H; auto using Rid_wfor. subst.
  destruct H as [v [v' [Htypingv [Htypingv' [[Hbrc Hv] [[Hbrc' Hv'] [R [Hb [_ [_ Hrel]]]]]]]]]]; subst.
  assert ((if X==X then A else typ_fvar X) = A) as HeqA.
    destruct (X==X); auto. contradict n; auto.
  simpl in *. simpl_env in *.
  rewrite HeqA in *. clear HeqA.
  exists (lempty++lempty). repeat(split; auto).
    apply bee_congr_app with (lA1:=lempty) (lA2:=lempty) (t1:=typ_bang A); auto.
      apply bee_refl with (lE:=nil); auto.
      assert (open_tt (typ_arrow (typ_bang (typ_bvar 0)) (typ_bvar 0)) A = 
              typ_arrow (typ_bang A) A) as Heq.
        unfold open_tt. auto.
      rewrite <- Heq.
      eapply typing_tapp; eauto.
        rewrite_env (nil++E++nil).
        apply typing_weakening; auto.
          simpl_env. auto.
Qed.

Definition Req1 Env (e:exp) (A:typ) (v v':exp) : Prop := 
  (beta_eta_eq Env nil v e A /\ beta_eta_eq Env nil v' e A)
  .

Lemma Req1_wfor : forall Env e A,
  wf_typ Env A -> 
  wfor Env (Req1 Env e A) A A.
Proof.
  intros.
  split; auto.
Qed.

Corollary BehaveLike_IIdentification : forall Id A x0 E, 
  typing nil nil Id (typ_all (typ_arrow (typ_bang (typ_bvar 0)) (typ_bvar 0))) ->
  typing E lempty x0 A ->
  value x0 ->
  beta_eta_eq E lempty (exp_app (exp_tapp Id A) (exp_bang x0)) x0 A.
Proof.
  intros Id A x0 E Htypingid Typingx0 Hvx0.
  destruct (@IIdentification Id A A E x0 x0 (Req1 E x0 A) Htypingid) as [X JJ]; auto using Req1_wfor.
  
  assert (wf_typ ((X, bind_kn)::nil) (typ_fvar X)) as WFT.
    apply wf_typ_var.
       unfold binds. simpl. auto. 
       simpl_env. apply binds_one_3; auto.

  assert (F_Related_oterms (typ_fvar X) 
                                 ([(X,(Req1 E x0 A))])
                                 ([(X, A)])
                                 ([(X, A)])
                                  x0 x0 E lempty).
    exists x0. exists x0. simpl.
    destruct (X==X); try solve [contradict n; auto].
    repeat(split; auto).
      apply F_Related_ovalues_fvar_req. simpl.
      exists(Req1 E x0 A).
      repeat(split; auto).
        apply bee_refl with (lE:=nil); auto.
        apply bee_refl with (lE:=nil); auto.

  apply JJ in H; auto using Req1_wfor. subst.
  destruct H as [v [v' [Htypingv [Htypingv' [[Hbrc Hv] [[Hbrc' Hv'] [R [Hb [_ [_ Hrel]]]]]]]]]]; subst.
  assert ((if X==X then A else typ_fvar X) = A) as HeqA.
    destruct (X==X); auto. contradict n; auto.
  simpl in *. simpl_env in *.
  rewrite HeqA in *. clear HeqA.
  analyze_binds Hb; subst.
  destruct Hrel as [asubst Hrel].
  decompose [and] Hrel. clear Hrel.
  apply bee_trans with (e':=v); auto.
    apply bee_red with (lE:=nil); auto.
Qed.

(***************************************************************)
(** *           Intuitionistic Boolean                         *)
(***************************************************************)
Lemma IBoolean : forall Bool A A' E e0 e'0 e1 e'1 R, 
  typing nil nil Bool (typ_all (typ_arrow (typ_bang (typ_bvar 0)) (typ_arrow (typ_bang (typ_bvar 0)) (typ_bvar 0)))) ->
  wfor E R A A' ->
  typing E lempty e0 A ->
  typing E lempty e'0 A' ->
  typing E lempty e1 A ->
  typing E lempty e'1 A' ->
  exists X, 
   F_Related_oterms (typ_fvar X) 
                                 ([(X,R)])
                                 ([(X,A)])
                                 ([(X,A')])
                                 e0 e'0 E lempty ->
   F_Related_oterms (typ_fvar X) 
                                 ([(X,R)])
                                 ([(X,A)])
                                 ([(X,A')])
                                 e1 e'1 E lempty ->
   F_Related_oterms (typ_fvar X) 
                                 ([(X,R)])
                                 ([(X,A)])
                                 ([(X,A')])
                                 (exp_app (exp_app (exp_tapp Bool A) (exp_bang e0)) (exp_bang e1)) 
                                 (exp_app (exp_app (exp_tapp Bool A') (exp_bang e'0)) (exp_bang e'1)) E lempty.
Proof.
  intros Bool A A' E e0 e'0 e1 e'1 R Htyping_bool Hwfor Htypinge0 Htypinge'0 Htypinge1 Htypinge'1.
  assert (wf_typ nil (typ_all (typ_arrow (typ_bang (typ_bvar 0)) (typ_arrow (typ_bang (typ_bvar 0)) (typ_bvar 0))))) as WFT.
    apply wf_typ_all with (L:={}).
      intros X Hfv.
      unfold open_tt. simpl. simpl_env. 
      eapply wf_typ_arrow; eauto.
        eapply wf_typ_arrow; eauto.

  assert (F_Related_oterms (typ_all (typ_arrow (typ_bang (typ_bvar 0)) (typ_arrow (typ_bang (typ_bvar 0)) (typ_bvar 0)))) rho_nil delta_nil delta_nil Bool Bool E nil) as Forel_All.
    apply fundamental_oparametricity; auto.
  destruct Forel_All as [v [v' [Htypingid [Htypingid' [Hn [Hn' Forel_All]]]]]].

  apply F_Related_ovalues_all_leq in Forel_All.
  destruct Forel_All as [Hv [Hv' [L' Hall]]]; subst.

  pick fresh X. 
  exists (X). intros Hrelt Hrelf.
  assert (wf_typ [(X,bind_kn)] (typ_fvar X)) as WFTvar. auto.
  assert (X `notin` L') as Fr'. auto.
  destruct (@Hall X A A' R Fr') as [w [w' [Hnorm_vt2w [Hnorm_v't2'w' Hrel_wft]]]]; auto.
  unfold open_tt in*. simpl in *.

  assert (wf_typ ((X, bind_kn)::nil) (typ_arrow (typ_bang (typ_fvar X)) (typ_arrow (typ_bang (typ_fvar X)) (typ_fvar X)))) as WFT'; eauto.

  apply F_Related_ovalues_arrow_leq in Hrel_wft.
  destruct Hrel_wft as [Hw [Hw' Harrow]]; subst.
  simpl_env in *.
  assert ((if X==X then A else typ_fvar X) = A) as Heq.
    destruct (X==X); auto. contradict n; auto.
  assert ((if X==X then A' else typ_fvar X) = A') as Heq'.
    destruct (X==X); auto. contradict n; auto.
  simpl in *.
  rewrite Heq in *. rewrite Heq' in *. clear Heq Heq'.

  destruct (@Harrow lempty (exp_bang e0) (exp_bang e'0)) as [u [u' [Hn_wxu [Hn_w'x'u' Hrel_wft2]]]]; auto.
     simpl_env.  auto.

     destruct Hrelt as [v0 [v'0 [Hv0 [Hv'0 [He0nv0 [He'0nv'0 Hrelt]]]]]].
     exists (exp_bang e0). 
     exists (exp_bang e'0).
     split. split; auto.
     split. split; auto.
         apply F_Related_ovalues_bang_req.
         split; auto. split; auto.
         exists e0. exists e'0.
         split; auto. split; auto.
         exists v0. exists v'0.
         split; auto.

  apply F_Related_ovalues_arrow_leq in Hrel_wft2.
  simpl_env in *.
  destruct Hrel_wft2 as [Hu [Hu' Harrow']]; subst.
  assert ((if X==X then A else typ_fvar X) = A) as Heq.
    destruct (X==X); auto. contradict n; auto.
  assert ((if X==X then A' else typ_fvar X) = A') as Heq'.
    destruct (X==X); auto. contradict n; auto. 
  simpl in *.
  rewrite Heq in *. rewrite Heq' in *. clear Heq Heq'.

  assert (wf_typ E A) as wft_A.
      apply wfor_left_inv in Hwfor; auto.

  assert (type A) as TypeA. eauto using type_from_wf_typ.

  assert (wf_typ E A') as wft_A'.
      apply wfor_right_inv in Hwfor; auto.

  assert (type A') as TypeA'. eauto using type_from_wf_typ.

  assert (normalize (exp_tapp Bool A) w).
      apply congr_tapp with (v1:=v); auto.

  assert (normalize (exp_tapp Bool A') w').
      apply congr_tapp with (v1:=v'); auto.
    
  assert (normalize (exp_app (exp_tapp Bool A) (exp_bang e0)) u) as Hn'_wxu.
      apply congr_app with (v1:=w); auto.

  assert (normalize (exp_app (exp_tapp Bool A') (exp_bang e'0)) u') as Hn'_w'x'u'.
      apply congr_app with (v1:=w'); auto.

  destruct (@Harrow' lempty (exp_bang e1) (exp_bang e'1)) as [x [x' [Hn_uxu0 [Hn_u'x'u'0 Hrel_wft22]]]]; auto.
     destruct Hrelf as [v1 [v'1 [Hv1 [Hv'1 [He1nv1 [He'1nv'1 Hrelf]]]]]].
     exists (exp_bang e1). 
     exists (exp_bang e'1).
     split. split; auto.
     split. split; auto.
         apply F_Related_ovalues_bang_req.
         split; auto. split; auto.
         exists e1. exists e'1.
         split; auto. split; auto.
         exists v1. exists v'1.
         split; auto.

  assert (normalize (exp_app (exp_app (exp_tapp Bool A) (exp_bang e0)) (exp_bang e1)) x).
      apply congr_app with (v1:=u); auto. 

  assert (normalize (exp_app (exp_app (exp_tapp Bool A') (exp_bang e'0)) (exp_bang e'1)) x').
      apply congr_app with (v1:=u'); auto. 

  exists x. exists x'.
    split; simpl.
    destruct (X==X); try solve [contradict n; auto].
    apply typing_app with (T1:=typ_bang A)(D1:=lempty) (D2:=lempty); auto.
      apply typing_app with (T1:=typ_bang A)(D1:=nil) (D2:=lempty); auto.
        assert (open_tt (typ_arrow (typ_bang (typ_bvar 0)) (typ_arrow (typ_bang (typ_bvar 0)) (typ_bvar 0))) A = typ_arrow (typ_bang A) (typ_arrow (typ_bang A) A)) as Heq.
          unfold open_tt. auto.
        rewrite <- Heq.
        apply typing_tapp; auto.

    split; simpl.
    destruct (X==X); try solve [contradict n; auto].
    apply typing_app with (T1:=typ_bang A')(D1:=lempty) (D2:=lempty); auto.
      apply typing_app with (T1:=typ_bang A')(D1:=nil) (D2:=lempty); auto.
        assert (open_tt (typ_arrow (typ_bang (typ_bvar 0)) (typ_arrow (typ_bang (typ_bvar 0)) (typ_bvar 0))) A' = typ_arrow (typ_bang A') (typ_arrow (typ_bang A') A')) as Heq.
          unfold open_tt. auto.
        rewrite <- Heq.
        apply typing_tapp; auto.

    split; auto.
Qed.

Definition Req2 Env (t f:exp) (A:typ) (v v':exp) : Prop := 
  ((beta_eta_eq Env nil v t A /\ beta_eta_eq Env nil v' t A) \/
  (beta_eta_eq Env nil v f A /\ beta_eta_eq Env nil v' f A))
  .

Lemma Req2_wfor : forall Env t f A,
  wf_typ Env A -> 
  wfor Env (Req2 Env t f A) A A.
Proof.
  intros.
  split; auto.
Qed.

Corollary BehaveLike_IBoolean : forall Bool, 
  typing nil nil Bool (typ_all (typ_arrow (typ_bang (typ_bvar 0)) (typ_arrow (typ_bang (typ_bvar 0)) (typ_bvar 0)))) ->
  (forall E et ef vt vf A, 
    normalize et vt ->
    normalize ef vf ->
    typing E lempty et A ->
    typing E lempty ef A ->
    (beta_eta_eq E nil (exp_app (exp_app (exp_tapp Bool A) (exp_bang et)) (exp_bang ef)) et A \/ 
     beta_eta_eq E nil (exp_app (exp_app (exp_tapp Bool A) (exp_bang et)) (exp_bang ef)) ef A)
  ).
Proof.
  intros Bool Htyping_bool E et ef vt vf A Hnt Hnf
    Htypinget Htypingef.

  assert (wfor E (Req2 E et ef A) A A) as wfor.
    apply Req2_wfor; auto.

  destruct (@IBoolean Bool A A E et et ef ef 
            (Req2 E et ef A) Htyping_bool
           ) as [X JJ]; auto using Req2_wfor.
  
  assert (wf_typ ((X, bind_kn)::nil) (typ_fvar X)) as WFT.
    apply wf_typ_var.
       unfold binds. simpl. auto. 
       simpl_env. apply binds_one_3; auto.

  assert ((if X==X then A else typ_fvar X) = A) as HeqA.
    destruct (X==X); auto. contradict n; auto.

  assert (F_Related_oterms (typ_fvar X) 
                                 ([(X, Req2 E et ef A)])
                                 ([(X, A)])
                                 ([(X, A)])
                                  et et E lempty).
    exists vt. exists vt. simpl.
    destruct (X==X); try solve [contradict n; auto].    
    repeat(split; auto).
        apply F_Related_ovalues_fvar_req. simpl.
        exists(Req2 E et ef A).
        repeat(split; auto).
          destruct Hnt; auto.
          destruct Hnt; auto.
          left. split.
            apply bee_sym.
            apply bee_red with (lE:=nil); auto. 
              destruct Hnt; auto.
            apply bee_sym.
            apply bee_red with (lE:=nil); auto. 
              destruct Hnt; auto.

  assert (F_Related_oterms (typ_fvar X) 
                                 ([(X, Req2 E et ef A)])
                                 ([(X, A)])
                                 ([(X, A)])
                                  ef ef E lempty).
    exists vf. exists vf. simpl.
    destruct (X==X); try solve [contradict n; auto].    
    repeat(split; auto).
        apply F_Related_ovalues_fvar_req. simpl.
        exists(Req2 E et ef A).
        repeat(split; auto).
          destruct Hnf; auto.
          destruct Hnf; auto.
          right. split.
            apply bee_sym.
            apply bee_red with (lE:=nil); auto. 
              destruct Hnf; auto.
            apply bee_sym.
            apply bee_red with (lE:=nil); auto. 
              destruct Hnf; auto.

  apply JJ in H; auto using Req2_wfor.
  destruct H as [v [v' [Htypingv [Htypingv' [[Hbrc Hv] [[Hbrc' Hv'] [R [Hb [_ [_ Hrel]]]]]]]]]].
  
  analyze_binds Hb.
  unfold Req2 in Hrel. 
  destruct Hrel as [[HBeet HBeet']|[HBeef HBeef']].
    left.
    simpl in Htypingv.
    destruct (X==X); try solve [contradict n; auto].
    apply bee_trans with (e':=v); auto.
      apply bee_red with (lE:=nil); auto. 

    right.
    simpl in Htypingv.
    destruct (X==X); try solve [contradict n; auto].
    apply bee_trans with (e':=v); auto.
      apply bee_red with (lE:=nil); auto. 
Qed.

(***************************************************************)
(** *           Intuitionistic Nat                             *)
(***************************************************************)
Lemma INat : forall Nat A A' E e0 e'0 e1 e'1 R, 
  typing nil nil Nat 
    (typ_all 
      (typ_arrow 
        (typ_bang (typ_arrow (typ_bvar 0) (typ_bvar 0)))
        (typ_arrow (typ_bang (typ_bvar 0)) (typ_bvar 0))
      )
    ) ->
  wfor E R A A' ->
  typing E lempty e0 (typ_arrow A A) ->
  typing E lempty e'0 (typ_arrow A' A') ->
  typing E lempty e1 A ->
  typing E lempty e'1 A' ->
  exists X, 
   F_Related_oterms (typ_arrow (typ_fvar X) (typ_fvar X))
                                 ([(X,R)])
                                 ([(X,A)])
                                 ([(X,A')])
                                 e0 e'0 E lempty ->
   F_Related_oterms (typ_fvar X) 
                                 ([(X,R)])
                                 ([(X,A)])
                                 ([(X,A')])
                                 e1 e'1 E lempty ->
   F_Related_oterms (typ_fvar X) 
                                 ([(X,R)])
                                 ([(X,A)])
                                 ([(X,A')])
                                 (exp_app (exp_app (exp_tapp Nat A) (exp_bang e0)) (exp_bang e1)) 
                                 (exp_app (exp_app (exp_tapp Nat A') (exp_bang e'0)) (exp_bang e'1)) E lempty.
Proof.
  intros Nat A A' E e0 e'0 e1 e'1 R Htyping_bool Hwfor Htypinge0 Htypinge'0 Htypinge1 Htypinge'1.
  assert (wf_typ nil (typ_all (typ_arrow (typ_bang (typ_arrow (typ_bvar 0) (typ_bvar 0))) (typ_arrow (typ_bang (typ_bvar 0)) (typ_bvar 0))))) as WFT.
    apply wf_typ_all with (L:={}).
      intros X Hfv.
      unfold open_tt. simpl. simpl_env. 
      eapply wf_typ_arrow; eauto.
        apply wf_typ_bang.
          eapply wf_typ_arrow; eauto.
        eapply wf_typ_arrow; eauto.

  assert (F_Related_oterms (typ_all (typ_arrow (typ_bang (typ_arrow (typ_bvar 0) (typ_bvar 0))) (typ_arrow (typ_bang (typ_bvar 0)) (typ_bvar 0)))) rho_nil delta_nil delta_nil Nat Nat E nil) as Forel_All.
    apply fundamental_oparametricity; auto.
  destruct Forel_All as [v [v' [Htypingid [Htypingid' [Hn [Hn' Forel_All]]]]]].

  apply F_Related_ovalues_all_leq in Forel_All.
  destruct Forel_All as [Hv [Hv' [L' Hall]]]; subst.

  pick fresh X. 
  exists (X). intros Hrelt Hrelf.
  assert (wf_typ [(X,bind_kn)] (typ_fvar X)) as WFTvar. auto.
  assert (X `notin` L') as Fr'. auto.
  destruct (@Hall X A A' R Fr') as [w [w' [Hnorm_vt2w [Hnorm_v't2'w' Hrel_wft]]]]; auto.
  unfold open_tt in*. simpl in *.

  assert (wf_typ ((X, bind_kn)::nil) (typ_arrow (typ_bang (typ_arrow (typ_fvar X) (typ_fvar X))) (typ_arrow (typ_bang (typ_fvar X)) (typ_fvar X)))) as WFT'.
    apply wf_typ_arrow.
      apply wf_typ_bang; auto.
      apply wf_typ_arrow; auto.

  apply F_Related_ovalues_arrow_leq in Hrel_wft.
  destruct Hrel_wft as [Hw [Hw' Harrow]]; subst.
  simpl_env in *.
  assert ((if X==X then A else typ_fvar X) = A) as Heq.
    destruct (X==X); auto. contradict n; auto.
  assert ((if X==X then A' else typ_fvar X) = A') as Heq'.
    destruct (X==X); auto. contradict n; auto.
  simpl in *.
  rewrite Heq in *. rewrite Heq' in *. clear Heq Heq'.

  destruct (@Harrow lempty (exp_bang e0) (exp_bang e'0)) as [u [u' [Hn_wxu [Hn_w'x'u' Hrel_wft2]]]]; auto.
     simpl_env. auto.

     destruct Hrelt as [v0 [v'0 [Hv0 [Hv'0 [He0nv0 [He'0nv'0 Hrelt]]]]]].
     exists (exp_bang e0). 
     exists (exp_bang e'0).
     split. split; auto.
     split. split; auto.
         apply F_Related_ovalues_bang_req.
         split; auto. split; auto.
         exists e0. exists e'0.
         split; auto. split; auto.
         exists v0. exists v'0.
         split; auto.

  apply F_Related_ovalues_arrow_leq in Hrel_wft2.
  simpl_env in *.
  destruct Hrel_wft2 as [Hu [Hu' Harrow']]; subst.
  assert ((if X==X then A else typ_fvar X) = A) as Heq.
    destruct (X==X); auto. contradict n; auto.
  assert ((if X==X then A' else typ_fvar X) = A') as Heq'.
    destruct (X==X); auto. contradict n; auto. 
  simpl in *.
  rewrite Heq in *. rewrite Heq' in *. clear Heq Heq'.

  assert (wf_typ E A) as wft_A.
      apply wfor_left_inv in Hwfor; auto.

  assert (type A) as TypeA. eauto using type_from_wf_typ.

  assert (wf_typ E A') as wft_A'.
      apply wfor_right_inv in Hwfor; auto.

  assert (type A') as TypeA'. eauto using type_from_wf_typ.

  assert (normalize (exp_tapp Nat A) w).
      apply congr_tapp with (v1:=v); auto.

  assert (normalize (exp_tapp Nat A') w').
      apply congr_tapp with (v1:=v'); auto.
    
  assert (normalize (exp_app (exp_tapp Nat A) (exp_bang e0)) u) as Hn'_wxu.
      apply congr_app with (v1:=w); auto.

  assert (normalize (exp_app (exp_tapp Nat A') (exp_bang e'0)) u') as Hn'_w'x'u'.
      apply congr_app with (v1:=w'); auto.

  destruct (@Harrow' lempty (exp_bang e1) (exp_bang e'1)) as [x [x' [Hn_uxu0 [Hn_u'x'u'0 Hrel_wft22]]]]; auto.
     destruct Hrelf as [v1 [v'1 [Hv1 [Hv'1 [He1nv1 [He'1nv'1 Hrelf]]]]]].
     exists (exp_bang e1). 
     exists (exp_bang e'1).
     split. split; auto.
     split. split; auto.
         apply F_Related_ovalues_bang_req.
         split; auto. split; auto.
         exists e1. exists e'1.
         split; auto. split; auto.
         exists v1. exists v'1.
         split; auto.

  assert (normalize (exp_app (exp_app (exp_tapp Nat A) (exp_bang e0)) (exp_bang e1)) x).
      apply congr_app with (v1:=u); auto. 

  assert (normalize (exp_app (exp_app (exp_tapp Nat A') (exp_bang e'0)) (exp_bang e'1)) x').
      apply congr_app with (v1:=u'); auto. 

  exists x. exists x'.
    split; simpl.
    destruct (X==X); try solve [contradict n; auto].
    apply typing_app with (T1:=typ_bang A)(D1:=lempty) (D2:=lempty); auto.
      apply typing_app with (T1:=typ_bang (typ_arrow A A))(D1:=nil) (D2:=lempty); auto.
        assert (open_tt (typ_arrow (typ_bang (typ_arrow (typ_bvar 0) (typ_bvar 0))) (typ_arrow (typ_bang (typ_bvar 0)) (typ_bvar 0))) A = typ_arrow (typ_bang (typ_arrow A A)) (typ_arrow (typ_bang A) A)) as Heq.
          unfold open_tt. auto.
        rewrite <- Heq.
        apply typing_tapp; auto.

    split; simpl.
    destruct (X==X); try solve [contradict n; auto].
    apply typing_app with (T1:=typ_bang A')(D1:=lempty) (D2:=lempty); auto.
      apply typing_app with (T1:=typ_bang (typ_arrow A' A'))(D1:=nil) (D2:=lempty); auto.
        assert (open_tt (typ_arrow (typ_bang (typ_arrow (typ_bvar 0) (typ_bvar 0))) (typ_arrow (typ_bang (typ_bvar 0)) (typ_bvar 0))) A' = typ_arrow (typ_bang (typ_arrow A' A')) (typ_arrow (typ_bang A') A')) as Heq.
          unfold open_tt. auto.
        rewrite <- Heq.
        apply typing_tapp; auto.

    split; auto.
Qed.

(***************************************************************)
(** *                Linear Nat                                *)
(***************************************************************)
Lemma LNat : forall Nat A A' E lE0 lE1 e0 e'0 e1 e'1 R, 
  typing nil nil Nat (typ_all (typ_arrow (typ_arrow (typ_bvar 0) (typ_bvar 0)) (typ_arrow (typ_bvar 0) (typ_bvar 0)))) ->
  wfor E R A A' ->
  typing E lE0 e0 (typ_arrow A A) ->
  typing E lE0 e'0 (typ_arrow A' A') ->
  typing E lE1 e1 A ->
  typing E lE1 e'1 A' ->
  disjoint lE0 lE1 ->
  exists X, 
   F_Related_oterms (typ_arrow (typ_fvar X) (typ_fvar X)) 
                                 ([(X,R)])
                                 ([(X,A)])
                                 ([(X,A')])
                                 e0 e'0 E lE0 ->
   F_Related_oterms (typ_fvar X) 
                                 ([(X,R)])
                                 ([(X,A)])
                                 ([(X,A')])
                                 e1 e'1 E lE1 ->
   F_Related_oterms (typ_fvar X) 
                                 ([(X,R)])
                                 ([(X,A)])
                                 ([(X,A')])
                                 (exp_app (exp_app (exp_tapp Nat A) e0) e1) 
                                 (exp_app (exp_app (exp_tapp Nat A') e'0) e'1) E (lE0 ++ lE1).
Proof.
  intros Nat A A' E lE0 lE1 e0 e'0 e1 e'1 R Htyping_bool Hwfor Htypinge0 Htypinge'0 Htypinge1 Htypinge'1 Disj.
  assert (wf_typ nil (typ_all (typ_arrow (typ_arrow (typ_bvar 0) (typ_bvar 0)) (typ_arrow (typ_bvar 0) (typ_bvar 0))))) as WFT.
    apply wf_typ_all with (L:={}).
      intros X Hfv.
      unfold open_tt. simpl. simpl_env. 
      eapply wf_typ_arrow; eauto.
        eapply wf_typ_arrow; eauto.
        eapply wf_typ_arrow; eauto.

  assert (F_Related_oterms (typ_all (typ_arrow (typ_arrow (typ_bvar 0) (typ_bvar 0)) (typ_arrow (typ_bvar 0) (typ_bvar 0)))) rho_nil delta_nil delta_nil Nat Nat E nil) as Forel_All.
    apply fundamental_oparametricity; auto.
  destruct Forel_All as [v [v' [Htypingid [Htypingid' [Hn [Hn' Forel_All]]]]]].

  apply F_Related_ovalues_all_leq in Forel_All.
  destruct Forel_All as [Hv [Hv' [L' Hall]]]; subst.

  pick fresh X. 
  exists (X). intros Hrelt Hrelf.
  assert (wf_typ [(X,bind_kn)] (typ_fvar X)) as WFTvar. auto.
  assert (X `notin` L') as Fr'. auto.
  destruct (@Hall X A A' R Fr') as [w [w' [Hnorm_vt2w [Hnorm_v't2'w' Hrel_wft]]]]; auto.
  unfold open_tt in*. simpl in *.

  assert (wf_typ ((X, bind_kn)::nil) (typ_arrow (typ_arrow (typ_fvar X) (typ_fvar X)) (typ_arrow (typ_fvar X) (typ_fvar X)))) as WFT'; auto.

  apply F_Related_ovalues_arrow_leq in Hrel_wft.
  destruct Hrel_wft as [Hw [Hw' Harrow]]; subst.
  simpl_env in *.
  assert ((if X==X then A else typ_fvar X) = A) as Heq.
    destruct (X==X); auto. contradict n; auto.
  assert ((if X==X then A' else typ_fvar X) = A') as Heq'.
    destruct (X==X); auto. contradict n; auto.
  simpl in *.
  rewrite Heq in *. rewrite Heq' in *. clear Heq Heq'.

  destruct (@Harrow lE0 e0 e'0) as [u [u' [Hn_wxu [Hn_w'x'u' Hrel_wft2]]]]; auto.
     simpl_env. auto.

     destruct Hrelt as [v0 [v'0 [Hv0 [Hv'0 [He0nv0 [He'0nv'0 Hrelt]]]]]].
     exists v0. exists v'0.
     split; auto.


  apply F_Related_ovalues_arrow_leq in Hrel_wft2.
  simpl_env in *.
  destruct Hrel_wft2 as [Hu [Hu' Harrow']]; subst.
  assert ((if X==X then A else typ_fvar X) = A) as Heq.
    destruct (X==X); auto. contradict n; auto.
  assert ((if X==X then A' else typ_fvar X) = A') as Heq'.
    destruct (X==X); auto. contradict n; auto. 
  simpl in *.
  rewrite Heq in *. rewrite Heq' in *. clear Heq Heq'.

  assert (wf_typ E A) as wft_A.
      apply wfor_left_inv in Hwfor; auto.

  assert (type A) as TypeA. eauto using type_from_wf_typ.

  assert (wf_typ E A') as wft_A'.
      apply wfor_right_inv in Hwfor; auto.

  assert (type A') as TypeA'. eauto using type_from_wf_typ.

  assert (normalize (exp_tapp Nat A) w).
      apply congr_tapp with (v1:=v); auto.

  assert (normalize (exp_tapp Nat A') w').
      apply congr_tapp with (v1:=v'); auto.
    
  assert (normalize (exp_app (exp_tapp Nat A) e0) u) as Hn'_wxu.
      apply congr_app with (v1:=w); auto.

  assert (normalize (exp_app (exp_tapp Nat A') e'0) u') as Hn'_w'x'u'.
      apply congr_app with (v1:=w'); auto.

  destruct (@Harrow' lE1 e1 e'1) as [x [x' [Hn_uxu0 [Hn_u'x'u'0 Hrel_wft22]]]]; auto.
     apply wf_lenv_merge; auto.

     destruct Hrelf as [v1 [v'1 [Hv1 [Hv'1 [He1nv1 [He'1nv'1 Hrelf]]]]]].
     exists v1. exists v'1.
     split; auto.

  assert (normalize (exp_app (exp_app (exp_tapp Nat A) e0) e1) x).
      apply congr_app with (v1:=u); auto. 

  assert (normalize (exp_app (exp_app (exp_tapp Nat A') e'0) e'1) x').
      apply congr_app with (v1:=u'); auto. 

  exists x. exists x'.
    split; simpl.
    destruct (X==X); try solve [contradict n; auto].
    apply typing_app with (T1:=A)(D1:=lE0) (D2:=lE1); auto.
      apply typing_app with (T1:=typ_arrow A A)(D1:=nil) (D2:=lE0); auto.
        assert (open_tt (typ_arrow (typ_arrow 0 0) (typ_arrow (typ_bvar 0) (typ_bvar 0))) A = typ_arrow (typ_arrow A A) (typ_arrow A A)) as Heq.
          unfold open_tt. auto.
        rewrite <- Heq.
        apply typing_tapp; auto.

        apply lenv_split_left_empty; auto.
      apply disjoint__lenv_split; auto.

    split; simpl.
    destruct (X==X); try solve [contradict n; auto].
    apply typing_app with (T1:=A')(D1:=lE0) (D2:=lE1); auto.
      apply typing_app with (T1:=typ_arrow A' A')(D1:=nil) (D2:=lE0); auto.
        assert (open_tt (typ_arrow (typ_arrow 0 0) (typ_arrow (typ_bvar 0) (typ_bvar 0))) A' = typ_arrow (typ_arrow A' A') (typ_arrow A' A')) as Heq.
          unfold open_tt. auto.
        rewrite <- Heq.
        apply typing_tapp; auto.

        apply lenv_split_left_empty; auto.
      apply disjoint__lenv_split; auto.

    split; auto.
Qed.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../../../metatheory" "-I" "../Bang") ***
*** End: ***
 *)
