(** Authors: Jianzhou Zhao. *)

Require Export Metatheory.
Require Import LinF_Definitions.
Require Import LinF_Infrastructure.
Require Import LinF_Lemmas.
Require Import LinF_Soundness.
Require Import LinF_Parametricity.

Export Parametricity.

(***************************************************************)
(*                 Beta Eta Equivalence                                     *)
(***************************************************************)
Inductive beta_eta_eq : exp -> exp -> Prop :=
  | bee_refl : forall e, 
      expr e -> beta_eta_eq e e
  | bee_sym : forall e e', 
      beta_eta_eq e' e -> beta_eta_eq e e'
  | bee_trans : forall e e' e'', 
      beta_eta_eq e e' -> beta_eta_eq e' e'' -> beta_eta_eq e e''
  | bee_red : forall e v, 
      bigstep_red e v -> beta_eta_eq e v
  | bee_app : forall e1 e2 e2',
      expr (exp_app e1 e2) ->
      beta_eta_eq e2 e2' -> beta_eta_eq (exp_app e1 e2) (exp_app e1 e2')
  .  

Hint Constructors beta_eta_eq.

Lemma bee_reflexivity : forall e,
  expr e -> beta_eta_eq e e.
intros; auto.
Qed.

Lemma bee_symm : forall e e',
  beta_eta_eq e e' -> beta_eta_eq e' e.
intros.
  induction H; eauto.
Qed.

Lemma bee_transitivity : forall e e' e'',
  beta_eta_eq e e' -> beta_eta_eq e' e'' -> beta_eta_eq e e''.
intros.
  generalize dependent e''.
  induction H; intros; eauto.
Qed.

(***************************************************************)
(*                               Relations                                            *)
(***************************************************************)
Definition Rfun (A A':typ) (f:exp) K (v v':exp) : Prop := 
  value (v) /\ value (v') /\
  typing nil nil v A /\ typing nil nil v' A' /\
  typing nil nil f (typ_arrow K A A') /\
  beta_eta_eq (exp_app f v) v'
  .
Definition Rid (A:typ) (v v':exp) : Prop := 
  value v /\ value v' /\
  typing nil nil v A /\ typing nil nil v' A /\ beta_eta_eq v v'.

Lemma Rfun_wfr : forall A A' K Q a,
  wf_typ nil A K -> 
  wf_typ nil A' K -> 
  wfr (Rfun A A' a Q) A A' K.
Proof.
  intros.
  split; auto.
Qed.

Lemma Rid_wfr : forall A K,
  wf_typ nil A K -> 
  wfr (Rid A) A A K.
Proof.
  intros.
  split; auto.
Qed.

(***************************************************************)
(*                 Fundamental Parametricity                            *)
(***************************************************************)
Corollary fundamental_parametricity: forall e t,
   typing nil nil e t ->
   F_related_terms t rho_nil delta_nil delta_nil e e.
Proof.
  intros.
  assert (apply_delta_subst delta_nil (apply_gamma_subst gamma_nil (apply_gamma_subst gamma_nil e)) = e) as Heq; auto.
  rewrite <- Heq.
  eapply parametricity; eauto.
Qed.

(***************************************************************)
(*                             Termination                                          *)
(***************************************************************)
Lemma termination : forall e t dsubst dsubst' gsubst gsubst' rsubst,
   F_related_terms t rsubst dsubst dsubst'
                                 (apply_delta_subst dsubst (apply_gamma_subst gsubst e))
                                 (apply_delta_subst dsubst' (apply_gamma_subst gsubst' e)) ->
   exists v, exists v', 
     normalize (apply_delta_subst dsubst (apply_gamma_subst gsubst e)) v /\
     normalize (apply_delta_subst dsubst' (apply_gamma_subst gsubst' e)) v' /\
     F_related_values t rsubst dsubst dsubst' v v'.
Proof.
  intros e t dsubst dsubst' gsubst gsubst' rsubst Hrel.
  destruct Hrel as [v [v' Hrel]]. decompose [and] Hrel.
  exists (v). exists (v').
  split; auto.
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
   wf_typ ([(X, bind_kn Q)]) (typ_fvar X) Q ->
   wfr R A A' Q ->
   F_related_terms (typ_fvar X)
                                 ([(X,R)])
                                 ([(X,A)])
                                 ([(X,A')])
                                  x y ->
   F_related_terms (typ_fvar X)
                                 ([(X,R)])
                                 ([(X,A)])
                                 ([(X,A')])
                                 (exp_app (exp_tapp Id A) x) (exp_app (exp_tapp Id A') y)).
Proof.
  intros Id A A' Q K Htyping x y R.
  assert (wf_typ nil (typ_all Q (typ_arrow K (typ_bvar 0) (typ_bvar 0))) kn_lin) as WFT.
    apply typing_regular in Htyping. decompose [and] Htyping; auto.

  assert (F_related_terms (typ_all Q (typ_arrow K (typ_bvar 0) (typ_bvar 0))) rho_nil delta_nil delta_nil Id Id) as Frel_All.
    apply fundamental_parametricity; auto.
  destruct Frel_All as [v [v' [Htypingid [Htypingid' [Hn [Hn' Frel_All]]]]]].

  apply F_related_values_all_leq in Frel_All.
  destruct Frel_All as [Hv [Hv' [L' Hall]]]; subst.

  pick fresh X. 
  exists (X). intros WFTvar Hwfr Hterm.
  assert (X `notin` L') as Fr'. auto.
  destruct (@Hall X A A' R Fr') as [w [w' [Hnorm_vt2w [Hnorm_v't2'w' Hrel_wft]]]]; auto.
  unfold open_tt in*. simpl in *.

  assert (wf_typ ((X, bind_kn Q)::nil) (typ_arrow K (typ_fvar X) (typ_fvar X)) K) as WFT'.
    eapply wf_typ_arrow; eauto.

  apply F_related_values_arrow_leq in Hrel_wft.
  destruct Hrel_wft as [Hw [Hw' Harrow]]; subst.
  simpl_env in *. 
  assert ((if X==X then A else typ_fvar X) = A) as Heq.
    destruct (X==X); auto. contradict n; auto.
  assert ((if X==X then A' else typ_fvar X) = A') as Heq'.
    destruct (X==X); auto. contradict n; auto.
  simpl in *.
  rewrite Heq in *. rewrite Heq' in *. clear Heq Heq'.

  destruct Hterm as [v0 [v'0 [Htypingv0 [Htypingv'0 [Hnorm [Hnorm' Hrel]]]]]]; subst.

  destruct (@Harrow v0 v'0) as [u [u' [Hn_wxu [Hn_w'x'u' Hrel_wft2]]]]; auto.
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

  assert (normalize (exp_tapp Id A) w).
      apply congr_tapp with (v1:=v); auto.
      eapply type_from_wf_typ with (E:=@nil (atom*binding)); eauto using wfr_left_inv.

  assert (normalize (exp_tapp Id A') w').
      apply congr_tapp with (v1:=v'); auto.
      eapply type_from_wf_typ with (E:=@nil (atom*binding)); eauto using wfr_right_inv.
    
  assert (normalize (exp_app (exp_tapp Id A) x) u).
      apply congr_app with (v1:=w) (v2:=v0); auto.
        apply expr_tapp; auto.
          eapply type_from_wf_typ; eauto using wfr_left_inv.

  assert (normalize (exp_app (exp_tapp Id A') y) u').
      apply congr_app with (v1:=w') (v2:=v'0); auto.
        apply expr_tapp; auto.
          eapply type_from_wf_typ; eauto using wfr_right_inv.

  unfold F_related_terms. exists(u). exists(u').
    split; simpl.
    destruct (X==X); try solve [contradict n; auto].
    apply typing_app with (T1:=A) (K:=K) (D1:=nil) (D2:=nil); auto.
      assert (open_tt (typ_arrow K (typ_bvar 0) (typ_bvar 0)) A = typ_arrow K A A) as Heq.
        unfold open_tt. auto.
      rewrite <- Heq.
      eapply typing_tapp; eauto using wfr_left_inv.
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
      eapply typing_tapp; eauto using wfr_right_inv.
        simpl in Htypingv'0.
        assert ((if X==X then A' else typ_fvar X) = A') as Heq.
          destruct (X==X); auto. contradict n; auto.
        rewrite Heq in Htypingv'0.
        assumption.

    split; auto.
Qed.

Corollary  Rearrangement_Identification : forall Id a A A' K, 
  typing nil nil Id (typ_all kn_lin (typ_arrow K (typ_bvar 0) (typ_bvar 0))) ->
  typing nil nil a (typ_arrow K A A') ->
  (forall x, 
    typing nil nil x A -> 
    (exists x0, normalize x x0) ->
    (exists x'0, normalize (exp_app a x) x'0) ->
    (exists y0, exists y'0, 
     normalize (exp_app (exp_tapp Id A) x) y0 /\ 
     normalize (exp_app (exp_tapp Id A') (exp_app a x)) y'0 /\
     Rfun A A' a K y0 y'0)
  ).
Proof.
  intros Id a A A' K Htypingid Htypinga x Htypingx Hn_xx0 Hn_axx'0.
  assert (wf_typ nil A kn_lin) as HwftA. auto.
  assert (wf_typ nil A' kn_lin) as HwftA'. 
    apply typing_regular in Htypinga. decompose [and] Htypinga.
    apply wft_arrow_inv in H3. destruct H3; auto.
  destruct (@Identification Id A A' kn_lin K Htypingid x (exp_app a x) (Rfun A A' a K)) as [X JJ].

  (* x and  (exp_app a x) are related as Rfun*)
  assert (wf_typ ((X, bind_kn kn_lin)::nil) (typ_fvar X) kn_lin) as WFT.
    apply wf_typ_var; unfold binds; simpl; auto.

  destruct Hn_xx0 as [x0 [Hbrc_xx0 Hx0]]. 
  destruct Hn_axx'0 as [x'0 [Hbrc_axx'0 Hx'0]].
  assert (F_related_terms (typ_fvar X) 
                                 ([(X,(Rfun A A' a K))])
                                 ([(X, A)])
                                 ([(X, A')])
                                  x (exp_app a x)).
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
        apply F_related_values_fvar_req. simpl.
        exists(Rfun A A' a K).
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
           apply bee_trans with (e':=(exp_app a x)); auto.
     
  (* Id[A] x and  Id[A'] (exp_app a x) are related as Rfun*)
  apply JJ in H; auto using Rfun_wfr.
  subst.
  destruct H as [v [v' [Htypingv [Htypingv' [[Hbrc Hv] [[Hbrc' Hv'] [R [Hb [_ [_ Hrel]]]]]]]]]]; subst.
  exists (v). exists (v'). unfold normalize.
  unfold Rfun.
  repeat(split; auto).
    Case "Typing".
    apply preservation_normalization with (e:=exp_app (exp_tapp Id A) x); auto.
      apply typing_app with (T1:=A)(D1:=nil) (D2:=nil) (K:=K); auto.
        assert (open_tt (typ_arrow K (typ_bvar 0) (typ_bvar 0)) A = typ_arrow K A A).
          unfold open_tt. auto.
        rewrite <- H.
        apply typing_tapp with (K:=kn_lin); auto.
      unfold normalize; auto.
    Case "Typing".
    apply preservation_normalization with (e:=exp_app (exp_tapp Id A') (exp_app a x)); auto.
      apply typing_app with (T1:=A')(D1:=nil) (D2:=nil) (K:=K); auto.
        assert (open_tt (typ_arrow K (typ_bvar 0) (typ_bvar 0)) A' = typ_arrow K A' A').
          unfold open_tt. auto.
        rewrite <- H.
        apply typing_tapp with (K:=kn_lin); auto.
          apply typing_app with (T1:=A)(D1:=nil) (D2:=nil) (K:=K); auto.
      unfold normalize; auto.
    Case "Beta-Eta-Equivalence".
    analyze_binds Hb; subst.
      unfold In_rel in Hrel. decompose [and] Hrel.
      unfold Rfun in Hrel. decompose [and] Hrel.
      assumption.
Qed.

Corollary  EQ_Identification : forall Id K, 
  typing nil nil Id (typ_all kn_lin (typ_arrow K (typ_bvar 0) (typ_bvar 0))) ->
  (forall x y A, 
    Rid A x y -> 
    (exists x0, normalize x x0) ->
    (exists y0, normalize y y0) ->
    (exists x'0, exists y'0, 
      normalize (exp_app (exp_tapp Id A) x) x'0 /\
      normalize (exp_app (exp_tapp Id A) y) y'0 /\
      Rid A x'0 y'0)
  ).
Proof.
  intros Id K Htypingid x y A HRid Hn_xx0  Hn_yy0.
  unfold Rid in *. destruct HRid as [Hvx [Hvy [Htypingx [Htypingy Heq_xy]]]].
  destruct Hn_xx0 as [x0 [Hbrc_xx0 Hx0]].
  destruct Hn_yy0 as [y0 [Hbrc_yy0 Hy0]].
  destruct (@Identification Id A A kn_lin K Htypingid x y (Rid A)) as [X JJ].
  
  assert (wf_typ ((X, bind_kn kn_lin)::nil) (typ_fvar X) kn_lin) as WFT.
    apply wf_typ_var.
       unfold binds. simpl. auto. 
       simpl_env. apply binds_one_3; auto.

  assert (F_related_terms (typ_fvar X) 
                                 ([(X,(Rid A))])
                                 ([(X, A)])
                                 ([(X, A)])
                                  x y).
    unfold F_related_terms. exists (x0). exists (y0).
      unfold normalize.
      split; simpl.
      destruct (X==X); auto; try solve [contradict n; auto].    
      split; simpl.
      destruct (X==X); auto; try solve [contradict n; auto].
      split; auto.
      split; auto.
      apply F_related_values_fvar_req. simpl.
      exists(Rid A).
      repeat(split; auto).
         destruct (X==X); try solve [contradict n; auto].
           apply preservation_normalization with (e:=x); auto.
            unfold normalize. auto.
         destruct (X==X); try solve [contradict n; auto].
           apply preservation_normalization with (e:=y); auto.
            unfold normalize. auto.
         apply bee_trans with (e':=x); auto.
            apply bee_trans with (e':=y); auto.

  apply JJ in H; auto using Rid_wfr. subst.
  destruct H as [v [v' [Htypingv [Htypingv' [[Hbrc Hv] [[Hbrc' Hv'] [R [Hb [_ [_ Hrel]]]]]]]]]]; subst.
  exists (v). exists (v').
  repeat(split; auto).
    apply preservation_normalization with (e:=(exp_app (exp_tapp Id A) x)); auto.
      apply typing_app with (T1:=A)(D1:=nil) (D2:=nil) (K:=K); auto.
        assert (open_tt (typ_arrow K (typ_bvar 0) (typ_bvar 0)) A = typ_arrow K A A).
          unfold open_tt. auto.
        rewrite <- H.
        apply typing_tapp with (K:=kn_lin); auto.
            unfold normalize. auto.
    apply preservation_normalization with (e:=(exp_app (exp_tapp Id A) y)); auto.
      apply typing_app with (T1:=A)(D1:=nil) (D2:=nil) (K:=K); auto.
        assert (open_tt (typ_arrow K (typ_bvar 0) (typ_bvar 0)) A = typ_arrow K A A).
          unfold open_tt. auto.
        rewrite <- H.
        apply typing_tapp with (K:=kn_lin); auto.
            unfold normalize. auto.
    analyze_binds Hb; subst.
      unfold In_rel in Hrel. decompose [and] Hrel.
      unfold Rid in Hrel. decompose [and] Hrel.
      assumption.
Qed.

(***************************************************************)
(*                             Boolean Function                                *)
(***************************************************************)
(* 
  \B : \X. X->X-> X. 
     \A. \A'. \a: A-> A'. 
          \t: A. \f: A.
           a (B[A] t f)  = B[A'] (a t) (a f)

  The above lemma implies the polymophic function I can only be 
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

  So I can only be an boolean function.
*)
Lemma CBoolean : forall CBool A A' Q K K', 
  typing nil nil CBool (typ_all Q (typ_arrow K (typ_bvar 0) (typ_arrow K' (typ_bvar 0) (typ_bvar 0)))) ->
  (forall t1 t2 f1 f2 R, exists X, 
   wf_typ ([(X,bind_kn Q)]) (typ_fvar X) Q->
   wfr R A A' Q->
   F_related_terms (typ_fvar X) 
                                 ([(X,R)])
                                 ([(X,A)])
                                 ([(X,A')])
                                 t1 t2 ->
   F_related_terms (typ_fvar X) 
                                 ([(X,R)])
                                 ([(X,A)])
                                 ([(X,A')])
                                 f1 f2 ->
   F_related_terms (typ_fvar X) 
                                 ([(X,R)])
                                 ([(X,A)])
                                 ([(X,A')])
                                 (exp_app (exp_app (exp_tapp CBool A) t1) f1) 
                                 (exp_app (exp_app (exp_tapp CBool A') t2) f2)).
Proof.
  intros CBool A A' Q K K' Htyping_bool t1 t2 f1 f2 R.
  assert (wf_typ nil (typ_all Q (typ_arrow K (typ_bvar 0) (typ_arrow K' (typ_bvar 0) (typ_bvar 0)))) K) as WFT.
    apply wf_typ_all with (L:={}).
      intros X Hfv.
      unfold open_tt. simpl. simpl_env. 
      eapply wf_typ_arrow with (K1:=Q)(K2:=K'); eauto.
        eapply wf_typ_arrow; eauto.

  assert (F_related_terms (typ_all Q (typ_arrow K (typ_bvar 0) (typ_arrow K' (typ_bvar 0) (typ_bvar 0)))) rho_nil delta_nil delta_nil CBool CBool) as Frel_All.
    apply fundamental_parametricity; auto.
  destruct Frel_All as [v [v' [Htypingid [Htypingid' [Hn [Hn' Frel_All]]]]]].

  apply F_related_values_all_leq in Frel_All.
  destruct Frel_All as [Hv [Hv' [L' Hall]]]; subst.

  pick fresh X. 
  exists (X). intros WFTvar Hwfr Htermt Htermf.
  assert (X `notin` L') as Fr'. auto.
  destruct (@Hall X A A' R Fr') as [w [w' [Hnorm_vt2w [Hnorm_v't2'w' Hrel_wft]]]]; auto.
  unfold open_tt in*. simpl in *.

  assert (wf_typ ((X, bind_kn Q)::nil) (typ_arrow K (typ_fvar X) (typ_arrow K' (typ_fvar X) (typ_fvar X))) K) as WFT'; eauto.

  apply F_related_values_arrow_leq in Hrel_wft.
  destruct Hrel_wft as [Hw [Hw' Harrow]]; subst.
  simpl_env in *.
  assert ((if X==X then A else typ_fvar X) = A) as Heq.
    destruct (X==X); auto. contradict n; auto.
  assert ((if X==X then A' else typ_fvar X) = A') as Heq'.
    destruct (X==X); auto. contradict n; auto.
  simpl in *.
  rewrite Heq in *. rewrite Heq' in *. clear Heq Heq'.

  destruct Htermt as [v0 [v'0 [Htypingv0 [Htypingv'0 [Hnorm [Hnorm' Hrelt]]]]]]; subst.
  destruct (@Harrow v0 v'0) as [u [u' [Hn_wxu [Hn_w'x'u' Hrel_wft2]]]]; auto.
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

  apply F_related_values_arrow_leq in Hrel_wft2.
  simpl_env in *.
  destruct Hrel_wft2 as [Hu [Hu' Harrow']]; subst.
  assert ((if X==X then A else typ_fvar X) = A) as Heq.
    destruct (X==X); auto. contradict n; auto.
  assert ((if X==X then A' else typ_fvar X) = A') as Heq'.
    destruct (X==X); auto. contradict n; auto.
  simpl in *.
  rewrite Heq in *. rewrite Heq' in *. clear Heq Heq'.

  destruct Htermf as [v1 [v'1 [Htypingv1 [Htypingv'1 [Hnorm1 [Hnorm1' Hrelf]]]]]]; subst.
  destruct (@Harrow' v1 v'1) as [x [x' [Hn_uxu0 [Hn_u'x'u'0 Hrel_wft22]]]]; auto.
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

  assert (wf_typ nil A Q) as wft_A.
      apply wfr_left_inv in Hwfr; auto.

  assert (type A) as TypeA. eauto using type_from_wf_typ.

  assert (wf_typ nil A' Q) as wft_A'.
      apply wfr_right_inv in Hwfr; auto.

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

  unfold F_related_terms. exists (x). exists (x').
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

Corollary  Rearrangement_CBoolean : forall CBool a A A' K K' Q, 
  typing nil nil CBool (typ_all kn_lin (typ_arrow K (typ_bvar 0) (typ_arrow K' (typ_bvar 0) (typ_bvar 0)))) ->
  typing nil nil a (typ_arrow Q A A') ->
  (forall t f, 
    typing nil nil t A -> 
    typing nil nil f A -> 
    (exists t0, normalize t t0) ->
    (exists t'0, normalize (exp_app a t) t'0) ->
    (exists f0, normalize f f0) ->
    (exists f'0, normalize (exp_app a f) f'0) ->
    (exists v, exists v',
      normalize (exp_app (exp_app (exp_tapp CBool A) t) f) v /\
      normalize (exp_app (exp_app (exp_tapp CBool A') (exp_app a t)) (exp_app a f)) v' /\
      Rfun A A' a Q v v')
  ).
Proof.
  intros CBool a A A' K K' Q Htypingid Htypinga t f 
    Htypingt Htypingf Hn_tt0 Hn_att'0 Hn_ff0 Hn_aff'0.
  assert (wf_typ nil A kn_lin) as HwftA. auto.
  assert (wf_typ nil A' kn_lin) as HwftA'. 
    apply typing_regular in Htypinga. decompose [and] Htypinga.
    apply wft_arrow_inv in H3. destruct H3; auto.
  destruct (@CBoolean CBool A A' kn_lin K K' Htypingid t (exp_app a t) f (exp_app a f) (Rfun A A' a Q)) as [X JJ].
  
(**)
  assert (wf_typ ((X, bind_kn kn_lin)::nil) (typ_fvar X) kn_lin) as WFT.
    apply wf_typ_var; unfold binds; simpl; auto.

  destruct Hn_tt0 as [t0 [Hbrc_tt0 Ht0]]. 
  destruct Hn_att'0 as [t'0 [Hbrc_att'0 Ht'0]].
  assert (F_related_terms (typ_fvar X)
                                 ([(X,(Rfun A A' a Q))])
                                 ([(X, A)])
                                 ([(X, A')])
                                  t (exp_app a t)).
    unfold F_related_terms. exists (t0). exists (t'0).
      split; simpl.
      destruct (X==X); auto; contradict n; auto.
    
      split; simpl.
      destruct (X==X).
        apply typing_app with (T1:=A)(D1:=nil) (D2:=nil) (K:=Q); auto.
        contradict n; auto.

      unfold normalize.
      split; auto.
      split; auto.
        apply F_related_values_fvar_req. simpl.
        exists(Rfun A A' a Q).
        repeat(split; auto).
           destruct (X==X); try solve [contradict n; auto].
             apply preservation_normalization with (e:=t); auto.
               unfold normalize; auto.
           destruct (X==X); try solve [contradict n; auto].
             apply preservation_normalization with (e:=exp_app a t); auto.
               apply typing_app with (T1:=A)(D1:=nil) (D2:=nil) (K:=Q); auto.
                 unfold normalize; auto.
           apply bee_trans with (e':=exp_app a t); auto.
(**)
     
  destruct Hn_ff0 as [f0 [Hbrc_ff0 Hf0]]. 
  destruct Hn_aff'0 as [f'0 [Hbrc_aff'0 Hf'0]].
  assert (F_related_terms (typ_fvar X) 
                                 ([(X,(Rfun A A' a Q))])
                                 ([(X, A)])
                                 ([(X, A')])
                                  f (exp_app a f)).
    unfold F_related_terms. exists (f0). exists (f'0).
      split; simpl.
        destruct (X==X); auto; contradict n; auto.    
      split; simpl.
      destruct (X==X).
        apply typing_app with (T1:=A)(D1:=nil) (D2:=nil) (K:=Q); auto.
        contradict n; auto.

      unfold normalize.
      split; auto.
      split; auto.
        apply F_related_values_fvar_req. simpl.
        exists(Rfun A A' a Q).
        repeat(split; auto).
         destruct (X==X); try solve [contradict n; auto].
            apply preservation_normalization with (e:=f); auto.
               unfold normalize; auto.
         destruct (X==X); try solve [contradict n; auto].
           apply preservation_normalization with (e:=exp_app a f); auto.
             apply typing_app with (T1:=A)(D1:=nil) (D2:=nil) (K:=Q); auto.
             unfold normalize; auto.
         apply bee_trans with (e':=exp_app a f); auto.
(**)

  apply JJ in H; auto using Rfun_wfr. subst.
  destruct H as [v [v' [Htypingv [Htypingv' [[Hbrc Hv] [[Hbrc' Hv'] [R [Hb [_ [_ Hrel]]]]]]]]]]; subst.
  exists (v). exists (v'). unfold normalize.
  unfold Rfun.
  repeat(split; auto).
    apply preservation_normalization with (e:=(exp_app (exp_app (exp_tapp CBool A) t) f)); auto.
      apply typing_app with (T1:=A)(D1:=nil) (D2:=nil) (K:=K'); auto.
        apply typing_app with (T1:=A)(D1:=nil) (D2:=nil) (K:=K); auto.
          assert (open_tt (typ_arrow K (typ_bvar 0) (typ_arrow K' (typ_bvar 0) (typ_bvar 0))) A = typ_arrow K A (typ_arrow K' A A)) as Heq.
            unfold open_tt. auto.
          rewrite <- Heq.
          apply typing_tapp with (K:=kn_lin); auto.
      unfold normalize; auto.
    apply preservation_normalization with (e:=(exp_app (exp_app (exp_tapp CBool A') (exp_app a t)) (exp_app a f))); auto.
      apply typing_app with (T1:=A')(D1:=nil) (D2:=nil) (K:=K'); auto.
        apply typing_app with (T1:=A')(D1:=nil) (D2:=nil) (K:=K); auto.
          assert (open_tt (typ_arrow K (typ_bvar 0) (typ_arrow K' (typ_bvar 0) (typ_bvar 0))) A' = typ_arrow K A' (typ_arrow K' A' A')) as Heq.
            unfold open_tt. auto.
          rewrite <- Heq.
          apply typing_tapp with (K:=kn_lin) ; auto.
        apply typing_app with (T1:=A)(D1:=nil) (D2:=nil) (K:=Q); auto.
        apply typing_app with (T1:=A)(D1:=nil) (D2:=nil) (K:=Q); auto.
          unfold normalize; auto.
    analyze_binds Hb; subst.
      unfold In_rel in Hrel. decompose [and] Hrel.
      unfold Rfun in Hrel. decompose [and] Hrel; assumption.
Qed.

Corollary  CBool_Identification : forall CBool K K', 
  typing nil nil CBool (typ_all kn_lin (typ_arrow K (typ_bvar 0) (typ_arrow K' (typ_bvar 0) (typ_bvar 0)))) ->
  (forall t1 t2 f1 f2 A, 
    Rid A t1 t2 -> Rid A f1 f2 -> 
    (exists vt1, normalize t1 vt1) ->
    (exists vt2, normalize t2 vt2) ->
    (exists vf1, normalize f1 vf1) ->
    (exists vf2, normalize f2 vf2) ->
    (exists v, exists v',
      normalize (exp_app (exp_app (exp_tapp CBool A) t1) f1) v /\
      normalize (exp_app (exp_app (exp_tapp CBool A) t2) f2) v' /\
      Rid A v v')
  ).
Proof.
  intros CBool K K' Htyping_bool t1 t2 f1 f2 A HRidt HRidf Hn_t1vt1 Hn_t2vt2 Hn_f1vf1 Hn_f2vf2.
  unfold Rid in *. 
  destruct HRidt as [Ht1 [Ht2 [Htypingt1 [Htypingt2 Heq_t1t2]]]].
  destruct Hn_t1vt1 as [vt1 [Hbrc_t1v1 Hvt1]].
  destruct Hn_t2vt2 as [vt2 [Hbrc_t2v2 Hvt2]].
  destruct HRidf as [Hf1 [Hf2 [Htypingf1 [Htypingf2 Heq_f1f2]]]].
  destruct Hn_f1vf1 as [vf1 [Hbrc_f1v1 Hvf1]].
  destruct Hn_f2vf2 as [vf2 [Hbrc_f2v2 Hvf2]].
  destruct (@CBoolean CBool A A kn_lin K K' Htyping_bool t1 t2 f1 f2 (Rid A)) as [X JJ]. 
  
  assert (wfr (Rid A) A A kn_lin) as WFR.
    split; auto.

  assert (wf_typ ((X, bind_kn kn_lin)::nil) (typ_fvar X) kn_lin) as WFT.
    apply wf_typ_var.
       unfold binds. simpl. auto. 
       simpl_env. apply binds_one_3; auto.

  assert (F_related_terms (typ_fvar X) 
                                 ([(X,(Rid A))])
                                 ([(X, A)])
                                 ([(X, A)])
                                  t1 t2).
    unfold F_related_terms. exists (vt1). exists (vt2).
      unfold normalize.
      split; simpl.
      destruct (X==X); auto; try solve [contradict n; auto].    
      split; simpl.
      destruct (X==X); auto; try solve [contradict n; auto].
      split; auto.
      split; auto.
        apply F_related_values_fvar_req. simpl.
        exists(Rid A).
        repeat(split; auto).
          destruct (X==X); try solve [contradict n; auto].
            apply preservation_normalization with (e:=t1); auto.
              unfold normalize. auto.
          destruct (X==X); try solve [contradict n; auto].
           apply preservation_normalization with (e:=t2); auto.
              unfold normalize. auto.
          apply bee_trans with (e':=t1); auto.
             apply bee_trans with (e':=t2); auto.

  assert (F_related_terms (typ_fvar X) 
                                 ([(X,(Rid A))])
                                 ([(X, A)])
                                 ([(X, A)])
                                  f1 f2).
    unfold F_related_terms. exists (vf1). exists (vf2).
      unfold normalize.
      split; simpl.
      destruct (X==X); auto; try solve [contradict n; auto].    
      split; simpl.
      destruct (X==X); auto; try solve [contradict n; auto].
      split; auto.
      split; auto.
        apply F_related_values_fvar_req. simpl.
        exists(Rid A).
        repeat(split; auto).
          destruct (X==X); try solve [contradict n; auto].
            apply preservation_normalization with (e:=f1); auto.
               unfold normalize. auto.
          destruct (X==X); try solve [contradict n; auto].
             apply preservation_normalization with (e:=f2); auto.
               unfold normalize. auto.
          apply bee_trans with (e':=f1); auto.
              apply bee_trans with (e':=f2); auto.

  apply JJ in H; auto using Rid_wfr. subst.
  destruct H as [v [v' [Htypingv [Htypingv' [[Hbrc Hv] [[Hbrc' Hv'] [R [Hb [_ [_ Hrel]]]]]]]]]]; subst.
  exists (v). exists (v').
  repeat(split; auto).
    apply preservation_normalization with (e:=(exp_app (exp_app (exp_tapp CBool A) t1) f1)); auto.
      apply typing_app with (T1:=A)(D1:=nil) (D2:=nil) (K:=K'); auto.
        apply typing_app with (T1:=A)(D1:=nil) (D2:=nil) (K:=K); auto.
          assert (open_tt (typ_arrow K (typ_bvar 0) (typ_arrow K' (typ_bvar 0) (typ_bvar 0))) A = typ_arrow K A (typ_arrow K' A A)) as Heq.
            unfold open_tt. auto.
          rewrite <- Heq.
          apply typing_tapp with (K:=kn_lin) ; auto.
            unfold normalize. auto.
    apply preservation_normalization with (e:=(exp_app (exp_app (exp_tapp CBool A) t2) f2)); auto.
      apply typing_app with (T1:=A)(D1:=nil) (D2:=nil) (K:=K'); auto.
        apply typing_app with (T1:=A)(D1:=nil) (D2:=nil) (K:=K); auto.
          assert (open_tt (typ_arrow K (typ_bvar 0) (typ_arrow K' (typ_bvar 0) (typ_bvar 0))) A = typ_arrow K A (typ_arrow K' A A)) as Heq.
            unfold open_tt. auto.
          rewrite <- Heq.
          apply typing_tapp with (K:=kn_lin); auto.
            unfold normalize. auto.
    analyze_binds Hb; subst.
      unfold In_rel in Hrel. decompose [and] Hrel.
      unfold Rid in Hrel. decompose [and] Hrel.
      assumption.
Qed.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../../../metatheory" "-I" "../linf") ***
*** End: ***
 *)
