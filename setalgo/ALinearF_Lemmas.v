
 (** Administrative lemmas for Algorithmic Lightweight Linear F

    Table of contents:
      - #<a href="##wft">Properties of wf_typ</a>#
      - #<a href="##oktwft">Properties of wf_env and wf_typ</a>#
      - #<a href="##okt">Properties of wf_env</a>#
      - #<a href="##subst">Properties of substitution</a>#
      - #<a href="##regularity">Regularity lemmas</a>#
      - #<a href="##auto">Automation</a># *)

Require Export LinF_Lemmas.
Require Export ALinearF_Infrastructure.
Require Export ALinearF_Denv.
Require Import Omega.

Axiom skip : False.
Ltac skip := assert False; [ apply skip | contradiction ].

(* ********************************************************************** *)
(** * #<a name="wft"></a># Properties of [wf_typ] *)

(** If a type is well-formed in an environment, then it is locally
    closed. *)

Lemma type_from_wf_atyp : forall G T K,
  wf_atyp G T K -> type T.
Proof.
  intros G T K H; induction H; eauto.
Qed.

Lemma wf_genv_from_wf_denv : forall G D,
  wf_denv G D ->
  wf_genv G.
Proof. intros. induction H; eauto.
Qed.

Lemma uniq_from_wf_genv : forall G,
  wf_genv G ->
  uniq G.
Proof with simpl_env; eauto.
  intros. induction H...
Qed.

Lemma uniq_from_wf_denv_lin : forall G D,
  wf_denv G D ->
  uniq D.
Proof with simpl_env; eauto.
  intros. induction H...
Qed.


Lemma uniq_from_wf_denv_nonlin : forall G D,
  wf_denv G D ->
  uniq G.
Proof.
  intros. 
  apply wf_genv_from_wf_denv in H.
    apply uniq_from_wf_genv; auto.
Qed.


Lemma uniq_from_wf_atyp : forall G T K,
  wf_atyp G T K -> uniq G.
Proof.
  intros G T K Wf_atyp.
  induction Wf_atyp; auto.
    pick fresh X.
    assert (X `notin` L) as J. auto.
    apply H0 in J.
    inversion J; auto.
Qed.

Lemma denv_dom_dinv : forall G D x,  
  wf_denv G D -> 
  x `in` dom D ->  
  x `notin` dom G.
Proof with simpl_env; eauto.  
  intros G D x H1 H2.
  generalize dependent x. 
  induction H1; intros.  
    fsetdec. 
    destruct (x0 == x).  
    Case "x0 = x". subst...  
    Case "x0 <> x". simpl in H3. 
      assert (EMap.In x0 <#[(x, T)]++D#>) as J.
        eapply in_find_iff.
        rewrite H4.
        eapply in_find_iff.
        apply in_dom_implies_In; auto.
      apply IHwf_denv; auto.
        simpl in J.
        apply add_in_iff in J.
        destruct J as [J | J]; subst.
          contradict n; auto.
          apply In_implies_in_dom; auto. 
Qed.

Lemma denv_dom_ginv : forall G D x,  
  wf_denv G D ->  
  x `in` dom G ->  
  x `notin` dom D.
Proof with simpl_env; eauto.  
  intros G D x H1 H2. 
  generalize dependent x.    
  induction H1; intros. fsetdec. 
    destruct (x0 == x).   
      Case "x0 = x". subst...   
      Case "x0 <> x".
        apply IHwf_denv in H5.
        assert (~EMap.In x0 <#[(x, T)]++D#>) as J.
          apply notin_dom_implies_notIn; auto.
        apply not_find_in_iff in J.
        rewrite H4 in J.
        apply not_find_in_iff in J.
          apply notIn_implies_notin_dom2; auto. 
Qed.

(* ********************************************************************** *)
(**  Uniq *)
Lemma uniq_renaming : forall A x y (Tx Ty:A) E1 E2,
  x `notin` dom(E2) `union` dom(E1) ->
  y `notin` dom(E2) `union` dom(E1) ->
  x <> y ->
  uniq (E2 ++ [(x, Tx)] ++ E1) ->
  uniq (E2 ++ [(y, Ty)] ++ E1).
Proof.
  intros A x y Tx Ty E1 E2 Frx Fry Hxny Uniq.
  remember (E2++[(x,Tx)]++E1) as F.
  generalize dependent E1.
  generalize dependent E2.
  generalize dependent x.
  generalize dependent Tx.
  induction Uniq; intros.
    assert (J := @nil_neq_one_mid (atom*A) (x,Tx) E2 E1).
    contradict J; auto.
   
    apply one_eq_app in HeqF.
    destruct HeqF as [[qs [H1 H2]] | [H1 H2]]; subst; simpl_env.
      apply uniq_push; auto.
      apply IHUniq with (x:=x0) (Tx0:=Tx); auto.

      inversion H2; subst. clear H2.
      apply uniq_push; auto.
Qed.

Lemma uniq_exchange : forall A E1 E2 E3 x y (Tx Ty:A),
  uniq (E3++[(x,Tx)]++E2++[(y,Ty)]++E1) ->
  uniq (E3++[(y,Ty)]++E2++[(x,Tx)]++E1).
Proof.
  intros A E1 E2 E3 x y Tx Ty Uniq.
  remember (E3++[(x,Tx)]++E2++[(y,Ty)]++E1) as F.
  generalize dependent E1.
  generalize dependent E2.
  generalize dependent E3.
  generalize dependent x.
  generalize dependent y.
  generalize dependent Tx.
  generalize dependent Ty.
  induction Uniq; intros.
    assert (J := @nil_neq_one_mid (atom*A) (x,Tx) E3 (E2++[(y,Ty)]++E1)).
    contradict J; auto.
   
    apply one_eq_app in HeqF.
    destruct HeqF as [[qs [H1 H2]] | [H1 H2]]; subst; simpl_env.
      apply uniq_push; auto.
      inversion H2; subst.
      simpl_env in Uniq.
      assert (HynE1:=Uniq).
      apply fresh_mid_tail in HynE1.
      assert (HynE2:=Uniq).
      apply fresh_mid_head in HynE2.
      apply uniq_push; auto.
        apply uniq_renaming with (x:=y) (Tx:=Ty); auto.
Qed.

(* ********************************************************************** *)
(** Regularity *)
Lemma denv_regular : forall G D,
  wf_denv G D ->
  wf_genv G.
Proof. intros. induction H; eauto.
Qed.


Lemma wf_atyp_from_wf_genv_typ : forall x T G,
  wf_genv ([(x, gbind_typ T)] ++ G) ->
  wf_atyp G T kn_nonlin.
Proof.
  intros x T G H. inversion H; auto.
Qed.


Lemma notin_fv_awf : forall G (X : atom) T K,
  wf_atyp G T K ->
  X `notin` dom G ->
  X `notin` fv_tt T.
Proof with auto.
  intros G X T K Wf_atyp.
  induction Wf_atyp; intros Fr; simpl...
  Case "wf_atyp_var".
    assert (X0 `in` (dom G))...
    eapply binds_In; eauto. fsetdec.
  Case "wf_atyp_all".
    pick fresh Y.
    apply (notin_fv_tt_open Y)...
Qed.


(* ********************************************************************** *)
(**  Permutation. *)
Lemma denv_permutation : forall G D D',
  wf_denv G D ->
  uniq D' ->
  D ~~~ D' ->
  wf_denv G D'.
Proof.
  intros G D D' Hwfd Huniq Heq.
  generalize dependent D'.  
  induction Hwfd; intros.
    apply dmap_eq_empty_inv in Heq; auto.
    apply denv_eq_empty_inv in Heq; subst; auto.
     
    eapply wf_denv_typ; eauto.      
      eapply Equal_trans; eauto.
Qed.
              
(* ********************************************************************** *)
(** Weakening *)
Lemma wf_atyp_weakening : forall T E F G K,
  wf_atyp (G ++ E) T K ->
  uniq (G ++ F ++ E) ->
  wf_atyp (G ++ F ++ E) T K.
Proof with simpl_env; eauto.
  intros T E F G K Hwf_atyp Hk.
  remember (G ++ E) as FF.
  generalize dependent G.
  induction Hwf_atyp; intros GG Hok Heq; subst...
  Case "type_all".
    pick fresh Y and apply wf_atyp_all...
    rewrite <- app_assoc.
    apply H0...
Qed.

Lemma wf_atyp_weakening_head : forall T E F K,
  wf_atyp E T K ->
  uniq (F ++ E) ->
  wf_atyp (F ++ E) T K.
Proof.
  intros.
  rewrite_env (gempty ++ F++ E).
  auto using wf_atyp_weakening.
Qed.

Hint Resolve wf_atyp_weakening_head .


Lemma wf_atyp_strengthening : forall E F x U T K,
 wf_atyp (F ++ [(x, gbind_typ U)] ++ E) T K ->
 wf_atyp (F ++ E) T K.
Proof with simpl_env; eauto.
  intros E F x U T K H.
  remember (F ++ [(x, gbind_typ U)] ++ E) as G.
  generalize dependent F.
  induction H; intros F Heq; subst...
  Case "wf_atyp_var".
    analyze_binds H0...
  Case "wf_atyp_all".
    pick fresh Y and apply wf_atyp_all...
    rewrite <- app_assoc.
    apply H0...
Qed.

Lemma wf_atyp_strengthening_head : forall E x U T K,
 wf_atyp ([(x, gbind_typ U)] ++ E) T K ->
 wf_atyp E T K.
Proof with simpl_env; eauto.
  intros E x U T K Wf_atyp.
  rewrite_env (nil ++ E).
  eapply wf_atyp_strengthening; eauto.
Qed.

Lemma wf_genv_strengthening : forall x T E F,
  wf_genv (F ++ [(x, gbind_typ T)] ++ E) ->
  wf_genv (F ++ E).
Proof with eauto using wf_atyp_strengthening.
  induction F; intros Wf_env; inversion Wf_env; subst; simpl_env in *...
Qed.

Lemma wf_genv_strengthening_head: forall E F,
  wf_genv (F ++ E) ->
  wf_genv E.
Proof.
  intros E F H.
  induction F; auto.
  rewrite_env ([a] ++ (F ++ E)) in H.
  apply IHF.
  inversion H; auto.
Qed.

Lemma wf_denv_nonlin_term_strengthening : forall x T E F D,
  wf_denv (F ++ [(x, gbind_typ T)] ++ E) D ->
  wf_denv (F ++ E) D.
Proof.
  intros x T E F D Wf_denv.
  remember (F ++ [(x, gbind_typ T)] ++ E) as G.
  induction Wf_denv; subst.
    apply wf_denv_empty.
      apply wf_genv_strengthening in H; auto.
    apply wf_denv_typ with (D:=D) (x:=x0) (T:=T0) (K:=K); auto.
      eapply wf_atyp_strengthening; eauto.
Qed.

Lemma wf_denv_nonlin_term_strengthening_head : forall x T E D,
  wf_denv ([(x, gbind_typ T)] ++ E) D ->
  wf_denv E D.
Proof.
  intros x T E D Wf_denv.
  rewrite_env (nil ++ E).
  eapply wf_denv_nonlin_term_strengthening; eauto.
Qed.

Lemma wf_atyp_from_gbinds_typ : forall x U G,
  wf_genv G ->
  binds x (gbind_typ U) G ->
  exists K, wf_atyp G U K.
Proof with auto using wf_atyp_weakening_head. intros. generalize dependent x. generalize dependent U.
  induction H; intros U xx J; analyze_binds J...
  assert (exists K, wf_atyp G U K).
  eapply IHwf_genv. eauto. inversion H1. exists x. eapply wf_atyp_weakening_head . 
  auto. apply uniq_push... apply uniq_from_wf_genv ...
  inversion BindsTacVal; subst... exists kn_nonlin... eapply wf_atyp_weakening_head...
  apply uniq_push... apply uniq_from_wf_genv...
  assert (exists K, wf_atyp G U K).
  eapply IHwf_genv. eauto. inversion H2. exists x0. eapply wf_atyp_weakening_head...
  apply uniq_push... apply uniq_from_wf_genv...
Qed.


Lemma wf_atyp_from_dbinds_typ : forall x U G D,
  wf_denv G D ->
  binds x U D ->
  exists K, wf_atyp G U K.
Proof with auto using wf_atyp_weaken_head. intros. generalize dependent x. generalize dependent U.
  induction H; intros U xx J.
    analyze_binds J...
    
    assert(J1:=@denv_to_dmap_iso D' xx U H3).
    apply J1 in J.
    rewrite <- H4 in J.
    apply find_mapsto_iff in J.
    simpl in J.
    apply add_mapsto_iff in J.
    destruct J as [[J2 J3]|[J2 J3]]; subst.
      exists K. auto.
      apply IHwf_denv with (x:=xx).
        apply find_mapsto_iff in J3.
          apply uniq_from_wf_denv_lin in H.
          assert(J4:=@denv_to_dmap_iso D xx U H).
          apply J4. auto.
Qed.

Lemma wf_denv_lin_strengthening_dmap : forall G D D' x,
  wf_denv G D ->
  uniq D' ->
  (<#D#>[-]x) ~~ <#D'#> ->
  wf_denv G D'.
Proof.
  intros G D D' x Wf_denv Huniq Heq.
  generalize dependent D'.
  generalize dependent x.
  induction Wf_denv; intros.
    (* wf_denv_empty *)
    assert (J:=@dmap_empty_remove_refl x).
    assert (D' = dempty) as K.
      apply denv_eq_empty_inv.
        apply dmap_eq_empty_inv.
           eapply Equal_trans; eauto.
    subst. auto.

    (* wf_denv_typ *)
    destruct (x0==x); subst.
      (* x0 = x *)
      (* (x:T++D)-x ~~ D ~~ D'-x ~~ D'0 *)
      apply denv_permutation with (D:=D); auto.
        apply Equal_trans with (m':=<#D'#>[-]x); auto.
           apply Equal_trans with (m':=<#[(x,T)]++D#>[-]x); auto.
             apply Equal_sym.
                simpl.
                apply dmap_add_remove_refl.
                  apply notin_dom_implies_notIn; auto.      
             apply dmap_remove_preserves_Equal; auto.                  
      (* x0 <> x *)
      assert (wf_denv G <@ <#D#>[-]x0 @>) as Wf_denv'.
        apply IHWf_denv with (x:=x0).
          apply dmap_to_denv_is_uniq.
          apply denv_to_from_dmap.
      apply wf_denv_typ with (D:=<@ <#D#>[-]x0 @>) (x:=x) (T:=T) (K:=K); auto.
        apply notIn_implies_notin_dom.
          unfold not.
          intro J.
          apply remove_in_iff in J. 
          destruct J as [J1 J2].
          apply In_implies_in_dom in J2.
          apply H1; auto.
        apply Equal_trans with (m':=<#D'#>[-]x0); auto.
          apply dmap_remove_preserves_Equal with (x:=x0) in H3; auto.
          apply Equal_trans with (m':=<#[(x,T)]++D#>[-]x0); auto.
            apply Equal_trans with (m':=<#[(x,T)]#>|_|(<#D#>[-]x0)); auto.
              apply Equal_trans with (m':=<#[(x,T)]#>|_|<# <@ <#D#>[-]x0 @> #>); auto.
                apply disjoint_denv_cons_union.
                  apply uniq_push; auto.
                    apply uniq_from_wf_denv_lin in Wf_denv; auto.                                      
                      apply dmap_to_denv_is_uniq.
                    apply notIn_implies_notin_dom.
                      unfold not. intro J.
                      apply remove_in_iff in J.
                      destruct J as [J1 J2].
                      apply In_implies_in_dom in J2.
                      apply H1; auto.
              apply Equal_sym.
                apply dmap_Equal_rewrite_Union_right with (M2:=<#D#>[-]x0); auto.
                  apply denv_to_from_dmap.
                  apply Equal_refl.
              apply Equal_trans with (m':=(<#[(x,T)]#>|_|<#D#>)[-]x0); auto.
                apply Equal_trans with (m':=(<#[(x,T)]#>[-]x0)|_|(<#D#>[-]x0)); auto.
                  apply dmap_Equal_rewrite_Union_left with (M1:=<#[(x,T)]#>); auto.
                    apply dmap_remove_refl.
                      unfold not. intro J.
                      simpl in J. apply add_in_iff in J.
                      destruct J as [J | J]; subst; auto.
                        apply empty_in_iff in J; auto.
                    apply Equal_refl.
                  apply Equal_sym.
                    apply dmap_union_remove_distr; auto.
                apply dmap_remove_preserves_Equal.
                  apply Equal_sym.
                  apply disjoint_denv_cons_union.
                    apply uniq_push; auto.
                      apply uniq_from_wf_denv_lin in Wf_denv; auto.
Qed.

Lemma wf_denv_lin_strengthening_x : forall x T G E F,
  wf_denv G (F ++ [(x, T)] ++ E) ->
  wf_denv G (F ++ E).
Proof.
  intros x T G E F Wf_denv.
  assert (Uniq := Wf_denv).
  apply uniq_from_wf_denv_lin in Uniq.
  (* (F++x:T++E)-x ~~ F++E *)  
  assert (<# F ++ [(x, T)] ++ E #> ~~ (<#F#> |_| (<#[(x, T)]++E#>))) as Heq1.
    apply disjoint_denv_cons_union; auto.
  assert (<# [(x, T)] ++ E #> ~~ (<#[(x, T)]#> |_| <#E#>)) as Heq2.
    apply disjoint_denv_cons_union; auto.
       eapply uniq_app_2; eauto.
  assert (<# F ++ [(x, T)] ++ E #> ~~ (<#F#> |_| (<#[(x, T)]#> |_| <#E#>))) as Heq3.
    apply dmap_Equal_rewrite_Union_right with (M2 := <# [(x, T)] ++ E #>); auto.
  clear Heq1 Heq2.
  apply dmap_remove_preserves_Equal with (x:=x) in Heq3.    
  assert (J1 := @dmap_union_remove_distr <#F#> (<# [(x,T)] #> |_| <#E#>) x).
  assert (J2 := @dmap_union_remove_distr <# [(x,T)] #> <#E#> x).
  apply dmap_Equal_rewrite_Union_right with (M2' := (<#[(x, T)]#>[-]x) |_| (<#E#>[-]x)) in J1; auto.
  assert ((<#[(x,T)]#>[-]x) ~~ @@) as Heq1.
    simpl.
    apply dmap_add_remove_refl; auto.
      unfold not.
      intro J.
      apply empty_in_iff in J. auto.
   
  assert (((<#[(x, T)]#>[-]x) |_| (<#E#>[-]x)) ~~
         ((<#E#>[-]x) |_| (<#[(x, T)]#>[-]x))) as Heq4.
    apply dmap_union_sym; auto.
      apply dmap_remove_preserves_disjoint.
      apply uniq_app_2 in Uniq.
      apply uniq_app_3 in Uniq; auto.
      apply denv_dmap_disjoint; auto.

  apply dmap_Equal_rewrite_Union_right with (M2' := @@) in Heq4; auto.
  assert (Heq5 := @dmap_union_empty_refl (<#E#>[-]x)).
  apply dmap_Equal_rewrite_Union_right with (M2' := (<#E#>[-]x)) in J1; auto.
   
  clear Heq4 Heq5 Heq1 J2.
      
  assert ((<#F#>[-]x) ~~ <#F#>) as Heq1.
    apply Equal_sym.
    apply dmap_remove_refl; auto.
      rewrite_env ((F++[(x,T)])++E) in Uniq.
      apply uniq_app_1 in Uniq.
      apply uniq_app_3 in Uniq.
      apply disjoint_sym_1 in Uniq.
      apply disjoint_one_1 in Uniq.
      apply notin_dom_implies_notIn; auto.
  assert ((<#E#>[-]x) ~~ <#E#>) as Heq2.
    apply Equal_sym.
    apply dmap_remove_refl; auto.
      apply uniq_app_2 in Uniq.
      apply uniq_app_3 in Uniq.
      apply disjoint_one_1 in Uniq.
      apply notin_dom_implies_notIn; auto.
  apply dmap_Equal_rewrite_Union_left with (M1':=<#F#>) in J1; auto.
  apply dmap_Equal_rewrite_Union_right with (M2':=<#E#>) in J1; auto.
  clear Heq1 Heq2.

  assert (<#F ++ E#> ~~ (<#F#> |_| <#E#>)) as Heq.
    apply disjoint_denv_cons_union.
  eapply uniq_remove_mid; eauto.
    
  apply wf_denv_lin_strengthening_dmap with (D':=F++E) (x:=x) in Wf_denv; auto.
    apply uniq_from_wf_denv_lin in Wf_denv.
      eapply uniq_remove_mid; eauto.
    apply Equal_trans with (m':=<#F#>|_|<#E#>); auto.
      apply Equal_trans with (m':=(<#F#>|_|<#[(x,T)]#>|_|<#E#>)[-]x); auto.
        apply Equal_sym; auto.
Qed.
  
Lemma wf_denv_lin_strengthening : forall G E D F,
  wf_denv G (F ++ D ++ E) ->
  wf_denv G (F ++ E).
Proof.
  intros G E D F.
  generalize dependent G.
  generalize dependent F.
  generalize dependent E.
  induction D; intros; auto.
    destruct a as [x T].
    rewrite_env (F ++ [(x, T)] ++ (D ++ E)) in H.
    apply wf_denv_lin_strengthening_x in H. auto.
Qed.


Lemma wf_denv_lin_strengthening_head : forall G E D,
  wf_denv G (D ++ E) ->
  wf_denv G E.
Proof.
  intros G E D Wf_denv.
  rewrite_env (nil ++ D ++ E) in Wf_denv.
  apply wf_denv_lin_strengthening in Wf_denv; auto.
Qed.


Lemma gbinds_weaken_at_tail : forall (x:atom) (a:gbinding) F G,
  binds x a F ->
  uniq (F ++ G) ->
  binds x a (F ++ G).
Proof.
  intros x a F G H J.
  rewrite_env (F ++ G ++ nil).
  apply binds_weaken; simpl_env; trivial.
Qed.



Lemma wf_atyp_typ_strengthening : forall E F X Q T K,
 wf_atyp (F ++ [(X, gbind_kn Q)] ++ E) T K ->
 X `notin` genv_fv_tt F `union` fv_tt T ->
 wf_atyp (F ++ E) T K.
Proof with simpl_env; eauto.
  intros E F X Q T K H FrX.
  remember (F ++ [(X, gbind_kn Q)] ++ E) as G.
  generalize dependent F.
  induction H; intros F Heq FrX; subst...
  Case "wf_atyp_var".
    analyze_binds H0... simpl. auto.
  Case "wf_atyp_arrow".
    simpl in *. eauto.
  Case "wf_atyp_all".
    simpl in FrX.
    pick fresh Y and apply wf_atyp_all...
    rewrite <- app_assoc.
    apply H0...
Qed.

Lemma wf_genv_typ_strengthening : forall X K E F,
  wf_genv (F ++ [(X, gbind_kn K)] ++ E) ->
  X `notin` genv_fv_tt F ->
  wf_genv (F ++ E).
Proof.
  intros X K E F Wf_genv FrX.
  remember (F ++ [(X, gbind_kn K)] ++ E) as G.
  generalize dependent X.
  generalize dependent K.
  generalize dependent E.
  generalize dependent F.
  induction G; intros.
    assert (J := @nil_neq_one_mid (atom*gbinding) (X,gbind_kn K) F E).
    contradict J; auto.

    simpl_env in HeqG.
    apply one_eq_app in HeqG.
    destruct HeqG as [[qs [H1 H2]]|[H1 H2]]; subst.
      destruct a. destruct g; simpl_env.
        apply wf_genv_kn; auto.
          apply IHG with (X0:=X) (K0:=K); auto.
            inversion Wf_genv; auto.
          apply uniq_from_wf_genv in Wf_genv.
          simpl_env in Wf_genv.
          rewrite_env (nil ++ [(a, gbind_kn k)] ++ qs ++ [(X, gbind_kn K)] ++ E) in Wf_genv.
          apply fresh_mid_tail in Wf_genv.
          simpl in Wf_genv.
          rewrite dom_app in Wf_genv.
          rewrite dom_cons in Wf_genv.
          destruct_notin.
          rewrite dom_app.
          fsetdec.
        apply wf_genv_typ; auto.
          apply IHG with (X0:=X) (K0:=K); auto.
            inversion Wf_genv; auto.
            simpl in FrX. auto.
          inversion Wf_genv; subst.
          simpl_env in H3.
          apply wf_atyp_typ_strengthening in H3; auto.
            simpl in FrX. auto.
          apply uniq_from_wf_genv in Wf_genv.
          simpl_env in Wf_genv.
          rewrite_env (nil ++ [(a, gbind_typ t)] ++ qs ++ [(X, gbind_kn K)] ++ E) in Wf_genv.
          apply fresh_mid_tail in Wf_genv.
          simpl in Wf_genv.
          rewrite dom_app in Wf_genv.
          rewrite dom_cons in Wf_genv.
          destruct_notin.
          rewrite dom_app.
          fsetdec.
      inversion H2; subst. clear H2.
      inversion Wf_genv; auto.

Qed.

Lemma wf_denv_nonlin_typ_strengthening : forall X K E F D,
  wf_denv (F ++ [(X, gbind_kn K)] ++ E) D ->
  X `notin` genv_fv_tt F `union` denv_fv_tt D ->
  wf_denv (F ++ E) D.
Proof.
  intros X K E F D Wf_denv FrX.
  remember (F ++ [(X, gbind_kn K)] ++ E) as G.
  generalize dependent K.
  induction Wf_denv; intros; subst.
    apply wf_denv_empty.
      apply wf_genv_typ_strengthening in H; auto.

    assert (Uniq:=Wf_denv).
    apply uniq_from_wf_denv_lin in Uniq.
    assert (uniq ([(x, T)]++D)) as Uniq'.
      apply uniq_push; auto.
    assert (J:=@dmap_eq__denv_fv_tt_eq ([(x, T)]++D) D' Uniq' H2 H3).
    assert (X `notin` denv_fv_tt ([(x, T)]++D)) as W.
      unfold not. intro U.
      apply J in U.
      solve_uniq.
    simpl in W.
    apply wf_denv_typ with (D:=D) (x:=x) (T:=T) (K:=K); auto.
      eapply IHWf_denv; eauto.
      eapply wf_atyp_typ_strengthening; eauto.
Qed.


Lemma wf_denv_nonlin_typ_strengthening_head : forall X K E D,
  wf_denv ([(X, gbind_kn K)] ++ E) D ->
  X `notin` denv_fv_tt D ->
  wf_denv E D.
Proof.
  intros X K E D Wf_denv FrX.
  rewrite_env (nil ++ E).
  eapply wf_denv_nonlin_typ_strengthening; eauto.
Qed.


Lemma wf_denv_nonlin_weakening : forall E F G D,
  wf_denv (F ++ E) D ->
  disjoint G D ->
  wf_genv (F ++ G ++ E) ->
  wf_denv (F ++ G ++ E) D.
Proof.
  intros E F G D Wf_denv Disj Wf_genv.
  remember (F ++ E) as GG.
  generalize dependent G.
  generalize dependent E.
  generalize dependent F.
  induction Wf_denv; intros; subst.
    apply wf_denv_empty; auto.
    apply wf_denv_typ with (D:=D) (x:=x) (T:=T) (K:=K); auto.
      apply IHWf_denv; auto.
        eapply disjoint_remove; eauto.

      eapply wf_atyp_weakening; eauto.
        apply uniq_from_wf_genv; auto.      
      assert (x `in` dom D') as J.
        apply In_implies_in_dom.
        eapply in_find_iff.
        rewrite <- H3.
        eapply in_find_iff.
        simpl.
        eapply add_in_iff.
        auto.

      assert (x `notin` dom G0) as J'.
        apply disjoint_sym in Disj.
        apply disjoint_in_notin with (x:=x) in Disj; auto.
      rewrite dom_app in H0.
      rewrite dom_app.
      auto.
Qed.

Lemma wf_denv_nonlin_weakening_head : forall E G D,
  wf_denv E D ->
  disjoint G D ->
  wf_genv (G ++ E) ->
  wf_denv (G ++ E) D.
Proof.
  intros. rewrite_env (gempty ++ G ++ E). rewrite_env (gempty ++ G ++ E) in H1.
  apply wf_denv_nonlin_weakening; auto.
Qed.



Lemma wf_denv_lin_weakening : forall x T E F G K,  
  wf_denv G (F ++ E) ->
  x `notin` dom G `union` dom F `union` dom E ->
  wf_atyp G T K ->
  wf_denv G (F ++ [(x, T)] ++ E).
Proof.
  intros x T E F G K Wf_denv FrX Wf_atyp.
  remember (F ++ E) as D.
  generalize dependent F. 
  generalize dependent E.
  generalize dependent x.
  generalize dependent T. 
  generalize dependent K. 
  induction Wf_denv; intros; subst.  
    destruct E; destruct F; simpl in *; simpl_env in *; auto.
      rewrite_env ([(x, T)]).
      apply wf_denv_typ with (D:=dempty) (x:=x) (T:=T) (K:=K); auto.
        simpl. apply Equal_refl.

      assert (J := @nil_neq_one_mid (atom*typ) p dempty F). 
      contradict J; auto.      

      assert (J := @nil_neq_one_mid (atom*typ) p dempty E). 
      contradict J; auto.      

      assert (J := @nil_neq_one_mid (atom*typ) p ([p0]++F) E). 
      contradict J; auto.      

    destruct (x==x0); subst.
      (*x==x0*)
      assert (EMap.In x0 <# [(x0, T)]++D #>) as J.
        apply in_dom_implies_In; auto.
          rewrite dom_app. simpl. fsetdec.
      apply in_find_iff in J.
      rewrite H3 in J.
      apply in_find_iff in J.
      apply In_implies_in_dom in J.
      contradict J; auto.
      (*x<>x0*)
      apply wf_denv_typ with (D:=[(x,T)]++D) (x:=x0) (T:=T0) (K:=K0); auto.
        rewrite_env (dempty ++ [(x,T)] ++D).
        eapply IHWf_denv with (K:=K); eauto.

        unfold not. intro J.
        apply in_dom_implies_In in J; auto.
        apply in_find_iff in J.
        rewrite H3 in J.
        apply in_find_iff in J.
        apply In_implies_in_dom in J.
        contradict J; auto.

        apply dmap_add_preserves_Equal with (x:=x0) (T:=T0) in H3.
        assert (uniq ([(x0,T0)]++F)) as Uniq'.
          apply uniq_push; auto.
            apply uniq_app_1 in H2; auto.
        assert (J:=@disjoint_denv_cons_commut ([(x0,T0)]) F Uniq').
        apply Equal_trans with (m':=<#[(x0,T0)]++F++E#>); auto.
          apply Equal_trans with (m':=<#[(x0,T0)]++F#>|_|<#E#>); auto.
            rewrite_env (([(x0, T0)]++F)++E).
            apply disjoint_denv_cons_union; auto.
              simpl_env; auto.
            apply Equal_trans with (m':=<#F++[(x0,T0)]#>|_|<#E#>); auto.
              apply dmap_Equal_rewrite_Union_left with (M1:=<#[(x0,T0)]++F#>); auto.
                apply Equal_refl.
              rewrite_env ((F++[(x0, T0)])++E).
              apply Equal_sym.
              apply disjoint_denv_cons_union; auto.
                simpl_env; auto.
Qed.

Lemma wf_denv_lin_weakening_head : forall x T D G K,  
  wf_denv G D ->
  x `notin` dom G `union` dom D ->
  wf_atyp G T K ->
  wf_denv G ([(x, T)] ++ D).
Proof.
  intros x T D G K Wf_denv FrX Wf_atyp.
  rewrite_env (dempty ++ [(x, T)] ++ D).
  eapply wf_denv_lin_weakening; eauto.
Qed.

(* ********************************************************************** *)
(** type susbt *)
Lemma kn_order_trans : forall K K' K'',
  kn_order K K' -> kn_order K' K'' -> kn_order K K''.
Proof.
  intros K K' K'' H1 H2.
  generalize dependent K''.
  induction H1; intros; auto.
    destruct K''.
      apply kn_order_base.
      apply kn_order_refl.
Qed.

Lemma wf_atyp_sub : forall G T K K',
  wf_atyp G T K ->
  kn_order K K' ->
  wf_atyp G T K'.
Proof.
  intros G T K K' Hkn Hord.
  generalize dependent K'.
  (wf_atyp_cases (induction Hkn) Case); intros; subst; auto.
  Case "wf_atyp_var".
    apply wf_atyp_var with (K':=K'); auto.
      eapply kn_order_trans; eauto.
  Case "wf_atyp_arrow".
    eapply wf_atyp_arrow with (K':=K'); auto.
      eapply kn_order_trans; eauto.
  Case "wf_atyp_all".
    apply wf_atyp_all with (L:=L).
    intros X HfrX.
    apply H0; auto.
Qed.

Lemma wf_atyp_subst_typ : forall F Q E Z P T K Q',
  wf_atyp (F ++ [(Z, gbind_kn Q)] ++ E) T K ->
  wf_atyp E P Q' ->
  kn_order Q' Q ->
  wf_atyp (map (subst_tgb Z P) F ++ E) (subst_tt Z P T) K.
Proof with simpl_env; eauto using wf_atyp_weakening_head, type_from_wf_atyp, wf_atyp_sub.
  intros F Q E Z P T K Q' WT WP KOrd.
  remember (F ++ [(Z, gbind_kn Q)] ++ E) as G.
  generalize dependent F.
  induction WT; intros F EQ; subst; simpl subst_tt...
  Case "wf_atyp_var".
    rename H1 into KOrd'.
    rename H into Huniq.
    rename H0 into Hbinds.
    destruct (X == Z).
    SCase "X=Z".
      subst...
      apply binds_mid_eq in Hbinds; auto.
      inversion Hbinds. subst...
    SCase "X<>Z".
      analyze_binds Hbinds...
      apply wf_atyp_var with (K':=K'); auto.
        assert ((subst_tgb Z P (gbind_kn K)) = (gbind_kn K)) as H1.
          simpl. auto. 
        apply uniq_map_app_l. 
        eapply uniq_remove_mid. eapply Huniq.

        apply gbinds_weaken_at_tail.
          assert (gbind_kn K' = (subst_tgb Z P (gbind_kn K'))) as H1.
            simpl; auto. 
          rewrite H1.
          apply binds_map. auto. apply uniq_map_app_l.
          apply (@uniq_remove_mid gbinding F [(Z, gbind_kn Q)] E). auto.          
  Case "wf_atyp_all".
    pick fresh Y and apply wf_atyp_all...
    rewrite subst_tt_open_tt_var...
    rewrite_env (map (subst_tgb Z P) ([(Y, gbind_kn K1)] ++ F) ++ E).
    apply H0...
Qed.

Lemma wf_genv_subst_typ : forall K Z P E K' F,
  wf_genv (F ++ [(Z, gbind_kn K)] ++ E) ->
  wf_atyp E P K' ->
  kn_order K' K ->
  wf_genv (map (subst_tgb Z P) F ++ E).
Proof with eauto 6 using wf_atyp_subst_typ.
  induction F; intros Wf_env WP KOrd; simpl_env;
    inversion Wf_env; simpl_env in *; simpl subst_tgb...
Qed.


Lemma wf_denv_subst_typ : forall P Z K E D K' F,
 wf_denv (F ++ [(Z, gbind_kn K)] ++ E) D ->
 wf_atyp E P K' ->
 kn_order K' K ->
 wf_denv (map (subst_tgb Z P) F ++ E) (map (subst_tdb Z P) D).
Proof.
  intros P Z K E D K' F Wf_denv WP KOrd.
  remember (F ++ [(Z, gbind_kn K)] ++ E) as G.
  generalize dependent P.
  generalize dependent K'.
  induction Wf_denv; intros; simpl_env; subst; auto.
    apply wf_denv_empty; auto.
      eapply wf_genv_subst_typ; eauto.
    apply wf_denv_typ with (D:=map (subst_tdb Z P) D) (x:=x) (T:=subst_tt Z P T) (K:=K0); eauto.
      eapply wf_atyp_subst_typ; eauto.
      assert (J1 := @denv_dmap_map D' (subst_tdb Z P)).
      assert (J2 := @denv_dmap_map ([(x, T)]++D) (subst_tdb Z P)).
      rewrite_env (map (subst_tdb Z P) ([(x, T)]++D)).
        apply dmap_map_preserves_Equal with (f:=subst_tdb Z P) in H3; auto.
        apply Equal_trans with (m':=EMap.map (subst_tdb Z P) <#D'#>); auto.
          apply Equal_trans with (m':=EMap.map (subst_tdb Z P) <#[(x, T)]++D#>); auto.
            apply Equal_sym; auto.
Qed.

Lemma wf_genv_free_typvar : forall G x T Z,
  wf_genv G ->
  binds x (gbind_typ T) G ->
  Z `notin` dom G ->
  Z `notin` fv_tt T.
Proof.
  intros G x T Z Wf_genv Binds ZnotinG.
  induction Wf_genv.
    inversion Binds.

    rewrite dom_app in ZnotinG.
    analyze_binds_uniq Binds.
      apply uniq_push; auto. 
        apply uniq_from_wf_genv; auto.

    rewrite dom_app in ZnotinG.
    analyze_binds_uniq Binds; subst.
      apply uniq_push; auto. 
        apply uniq_from_wf_genv; auto.
      inversion BindsTacVal; subst.
        
      apply notin_fv_awf with (X:=Z) in H; auto.
Qed.

Lemma value_through_subst_typ : forall e Z P,
  type P ->
  value e ->
  value (subst_te Z P e).
Proof.
  intros e Z P Typ H.
  induction H; simpl; auto using subst_te_expr.
  assert (expr (subst_te Z P (exp_abs K T e1))).
    apply subst_te_expr; auto.
  apply value_abs. simpl in H0; auto.

  assert (expr (subst_te Z P (exp_tabs K e1))).
    apply subst_te_expr; auto.
  apply value_tabs. simpl in H0; auto.
Qed.

Lemma atyping_through_subst_te : forall F E D e T D' P Q Q' Z,
  atyping (F ++ [(Z, gbind_kn Q)] ++ E) D e T D' ->
  wf_atyp E P Q' ->
  kn_order Q' Q ->
  atyping (map (subst_tgb Z P) F ++ E) 
          (map (subst_tdb Z P) D) 
          (subst_te Z P e) (subst_tt Z P T)
          (map (subst_tdb Z P) D'). 
Proof.
  intros F E D e T D' P Q Q' Z Htyp Hkn KOrder.
  remember (F++[(Z, gbind_kn Q)]++E) as G.
  generalize dependent Z.
  generalize dependent Q'.
  generalize dependent Q.
  generalize dependent P.
  generalize dependent E.
  generalize dependent F.
  (atyping_cases (induction Htyp) Case); intros; subst; simpl.
  Case "atyping_uvar". 
    rename H0 into Wf_denv.
    rename H into Binds.
    analyze_binds_uniq Binds.
      eapply uniq_from_wf_denv_nonlin; eauto.
      (* x notin E, x<>Z, x:T in F*)
      apply atyping_uvar; auto.
        eapply wf_denv_subst_typ; eauto.
      (* x:T in E, x<>Z, x notin F*)
      apply atyping_uvar; auto.
        apply binds_app_r.
          rewrite <- subst_tt_fresh; auto.
          apply wf_genv_free_typvar with (G:=E) (x:=x); auto.
            rewrite_env ((F++[(Z, gbind_kn Q)])++E) in Wf_denv.
            apply wf_genv_from_wf_denv in Wf_denv.
            apply wf_genv_strengthening_head in Wf_denv; auto.

            apply uniq_from_wf_denv_nonlin in Wf_denv.
            solve_uniq.
        eapply wf_denv_subst_typ; eauto.
  Case "atyping_lvar". 
    rename H0 into Wf_denv.
    rename H into Binds.
    rename H1 into Uniq'.
    rename H2 into Eq.
    apply atyping_lvar; auto.
      eapply wf_denv_subst_typ; eauto.
        intros y.
        remember (EMap.find (elt:=typ) y <# map (subst_tdb Z P) D' #>) as R.
        destruct R; apply sym_eq in HeqR.
          apply map_find_some__denv_find_some in HeqR.
          destruct HeqR as [T' [H1 H2]]; subst.
          rewrite <- Eq in H1.
          apply denv_remove_find_some__map_remove_find_some with (f:=subst_tdb Z P) in H1; auto.
          
          apply (@denv_find_none_map_iff D' y (subst_tdb Z P)) in HeqR.
          rewrite <- Eq in HeqR.
          apply denv_remove_find_none__map_remove_find_none; auto.    
  Case "atyping_uabs".
    apply atyping_uabs with (L:=L).
      eapply wf_atyp_subst_typ; eauto.
      intros x Frx.
        rewrite_env (map (subst_tgb Z P) ([(x, gbind_typ V)]++F) ++ E). 
        rewrite subst_te_open_ee_var; auto.
        eapply H1; eauto.
      intros J.
        apply H2 in J.
        apply denv_map_preserves_Equal; auto.
  Case "atyping_labs".
    apply atyping_labs with (L:=L) (Q:=Q).
      eapply wf_atyp_subst_typ; eauto.
      intros x Frx.
        rewrite_env (map (subst_tdb Z P) ([(x, V)]++D)). 
        rewrite subst_te_open_ee_var; auto.
        eapply H1; eauto.
      intros J.
        apply H2 in J.
        apply denv_map_preserves_Equal; auto.
  Case "atyping_app".
    apply atyping_app with (T1:=subst_tt Z P T1) (K:=K) (D2:=map (subst_tdb Z P) D2); eauto.
  Case "atyping_tabs".
    apply atyping_tabs with (L:=L `union` singleton Z).
      intros X FrX.
      assert (X `notin` L) as XnL. auto.
      apply H in XnL.
      rewrite subst_te_open_te_var; eauto using type_from_wf_atyp.
      apply value_through_subst_typ; eauto using type_from_wf_atyp.

      intros X FrX.
        rewrite_env (map (subst_tgb Z P) ([(X, gbind_kn K)]++F) ++ E). 
        assert (type P) as Htp.
          eapply type_from_wf_atyp; eauto.
        rewrite subst_te_open_te_var; auto.
        rewrite subst_tt_open_tt_var; auto.
        eapply H1; eauto.
  Case "atyping_tapp".
    rewrite subst_tt_open_tt; auto.
      apply atyping_tapp with (K:=K) (K':=K'); auto. 
        eapply IHHtyp; eauto.
        eapply wf_atyp_subst_typ; eauto.
      eapply type_from_wf_atyp; eauto.
Qed.

Lemma map_subst_tgb_id : forall G Z P,
  wf_genv G ->
  Z `notin` dom G ->
  G = map (subst_tgb Z P) G.
Proof with auto.
  intros G Z P H.
  induction H; simpl; intros Fr; simpl_env...
  rewrite <- IHwf_genv...
  rewrite <- IHwf_genv...
    rewrite <- subst_tt_fresh... eapply notin_fv_awf; eauto.
Qed.


Lemma map_subst_tdb_id : forall D G Z P,
  wf_denv G D ->
  Z `notin` dom G `union` dom D ->
  D = map (subst_tdb Z P) D.
Proof with auto.
  induction D; intros G Z P Wf_denv ZnotinD.
    simpl. auto.
    destruct a. simpl in *.
    assert (wf_denv G D) as Wfdenv'.
      apply wf_denv_lin_strengthening_head with (D:=[(a,t)]); auto.
    apply IHD with (Z:=Z) (P:=P) in Wfdenv'; auto.
    rewrite <- Wfdenv'.
    rewrite <- subst_tt_fresh...
    apply wf_atyp_from_dbinds_typ with (x:=a) (U:=t) in Wf_denv; auto.
      destruct Wf_denv as [K Wf_denv]. 
      eapply notin_fv_awf with (G:=G); eauto.
Qed.

(* ********************************************************************** *)
(** renaming *)
Lemma wf_atyp_typ_renaming : forall (X Y : atom) E T Q K,
  X `notin` (fv_tt T `union` dom E) ->
  Y `notin` (fv_tt T `union` dom E) ->
  X <> Y ->
  wf_atyp ([(X, gbind_kn Q)] ++ E) (open_tt T X) K ->
  wf_atyp ([(Y, gbind_kn Q)] ++ E) (open_tt T Y) K.
Proof.
  intros X Y E T Q K FrX FrY HXnY Wf_atyp.
  destruct_notin. 
  rewrite (subst_tt_intro X); auto.
  rewrite_env (gempty ++ [(Y, gbind_kn Q)] ++ E).
  assert (gempty = map (subst_tgb X Y) gempty) as Heq.
    simpl. auto.
  rewrite Heq.
  apply wf_atyp_subst_typ with (Q:=Q) (Q':=Q); auto.
    simpl_env. eapply wf_atyp_weakening; eauto. 
      apply uniq_from_wf_atyp in Wf_atyp.
      inversion Wf_atyp; auto.
    simpl. eapply wf_atyp_var; eauto.
      apply uniq_from_wf_atyp in Wf_atyp.
      inversion Wf_atyp; auto.
Qed.

(* ********************************************************************** *)
(** regular *)
Lemma _atyping_regular : forall G D1 e T D2,
  atyping G D1 e T D2 ->
  (wf_genv G  /\ wf_denv G D1 /\ wf_denv G D2 /\ exists K, wf_atyp G T K).
Proof with simpl_env; eauto.
  intros G D1 e T D2 Htyp.
  (atyping_cases (induction Htyp) Case); intros; subst.
  Case "atyping_uvar". 
    repeat split...
      apply wf_genv_from_wf_denv in H0; auto.
      apply wf_genv_from_wf_denv in H0.
        eauto using wf_atyp_from_gbinds_typ.
  Case "atyping_lvar". 
    repeat split...
      apply wf_genv_from_wf_denv in H0; auto.
      eapply wf_denv_lin_strengthening_dmap; eauto.
      eauto using wf_atyp_from_dbinds_typ.
  Case "atyping_uabs".
    pick fresh y.
    destruct (H1 y) as [J1 [J2 [J3 [K' J4]]]]...
    repeat split...
      inversion J1; auto.
      eapply wf_denv_nonlin_term_strengthening_head; eauto.
      eapply wf_denv_nonlin_term_strengthening_head; eauto.
      exists K.
        eapply wf_atyp_arrow with (K2:=K'); eauto.
          eapply wf_atyp_strengthening_head; eauto.
  Case "atyping_labs".
    pick fresh y.
    destruct (H1 y) as [J1 [J2 [J3 [K' J4]]]]...
    split.
      inversion J1; auto.
    split.
      eapply wf_denv_lin_strengthening_head; eauto.
    split; auto.
      exists K.
        eapply wf_atyp_arrow with (K2:=K'); eauto.
  Case "atyping_app".
    destruct IHHtyp1 as [Wf_genv1 [Wf_denv1 [Uniq1 [EX1 J1]]]].
    destruct IHHtyp2 as [Wf_genv2 [Wf_denv2 [Uniq2 [EX2 J2]]]].
    split; auto.
    split; auto.
    split; auto.
      inversion J1; subst.
      exists K2. auto.
  Case "atyping_tabs".
    pick fresh Y.
    destruct (H1 Y) as [J1 [J2 [J3 [K' J4]]]]...
    split; auto.
      inversion J1; auto.
    split; auto.
      eapply wf_denv_nonlin_typ_strengthening_head; eauto.
    split.
      eapply wf_denv_nonlin_typ_strengthening_head; eauto.
      exists K'.
      apply wf_atyp_all with (L:=L `union` fv_tt T1 `union` dom G `union` singleton Y).
      intros X FrX.
      destruct_notin.
      eapply wf_atyp_typ_renaming; eauto.
  Case "atyping_tapp".
    destruct IHHtyp as [Wf_genv [Wf_denv [Uniq [EX J]]]].
    split; auto.
    split; auto.
    split; auto.
      inversion J; subst.
      pick fresh Y.
      assert (Y `notin` L) as FrY.
        auto.
      apply H5 in FrY.
      exists EX.
        rewrite_env (nil ++ [(Y, gbind_kn K)] ++ G) in FrY.     
        apply wf_atyp_subst_typ with (P:=T) (Z:=Y) (Q:=K) (Q':=K') in FrY; auto.
        simpl_env in FrY.
        rewrite (subst_tt_intro Y)...
Qed.


Lemma _atyping_expr : forall G D e T D',
  atyping G D e T D' -> expr e.
Proof with eauto.
  intros G D e T D' Typ.
  induction Typ; subst...
    eapply expr_abs; eauto.
      apply type_from_wf_atyp in H; eauto.
    eapply expr_abs; eauto.
      apply type_from_wf_atyp in H; eauto.
    eapply expr_tapp; eauto.
      apply type_from_wf_atyp in H; eauto.
Qed.

Lemma atyping_regular : forall G D1 e T D2,
  atyping G D1 e T D2 ->
  (wf_genv G  /\ wf_denv G D1 /\ wf_denv G D2 /\ (exists K, wf_atyp G T K) /\ expr e).
Proof.
  intros G D1 e T D2 Typ.
  assert (Typ' := Typ).
  apply _atyping_regular in Typ.
  apply _atyping_expr in Typ'.
  decompose [and] Typ; auto.
Qed.

Lemma atyping_nonlin_weakening : forall F E D e T D' G,
  atyping (F ++ E) D e T D' ->
  wf_denv (F ++ G ++ E) D ->
  atyping (F ++ G ++ E) D e T D'.
Proof.
  intros F E D e T D' G Htyp.
  remember (F++E) as GG.
  generalize dependent F.
  generalize dependent E.  
  generalize dependent G.
  (atyping_cases (induction Htyp) Case); intros; subst; auto.
  Case "atyping_uabs".
    apply atyping_uabs with (L:=L `union` dom D `union` dom (F++G0++E)); auto.
      apply wf_atyp_weakening; auto.
        eapply uniq_from_wf_denv_nonlin; eauto.
      intros x Frx.
        rewrite_env (([(x, gbind_typ V)]++F)++G0++E).
        apply H1; auto.
          rewrite_env ([(x, gbind_typ V)]++(F++G0++E)).
          apply wf_denv_nonlin_weakening_head; auto.
            apply wf_genv_typ; auto.
              eapply wf_genv_from_wf_denv; eauto.
              apply wf_atyp_weakening; auto.
                eapply uniq_from_wf_denv_nonlin; eauto.
  Case "atyping_labs".
    apply atyping_labs with (L:=L `union` dom D `union` dom (F++G0++E)) (Q:=Q); auto.
      apply wf_atyp_weakening; auto.
        eapply uniq_from_wf_denv_nonlin; eauto.
      intros x Frx.
        apply H1; auto.
          eapply wf_denv_lin_weakening_head with (K:=Q) ; eauto.
              apply wf_atyp_weakening; auto.
                eapply uniq_from_wf_denv_nonlin; eauto.
  Case "atyping_app".
    apply atyping_app with (T1:=T1) (K:=K) (D2:=D2); auto.
      assert (atyping (F++G0++E) D1 e1 (typ_arrow K T1 T2) D2) as Htyp1'.
        apply IHHtyp1; auto.
      apply IHHtyp2; auto.
        apply atyping_regular in Htyp1'.
        destruct Htyp1' as [Wf_genv [Wf_denv1 [Wf_denv2 Wf_atyp1]]]. 
        auto.
  Case "atyping_tabs".
    apply atyping_tabs with (L:=L `union` dom D `union` dom (F++G0++E)); auto.
      intros X FrX.
        rewrite_env (([(X, gbind_kn K)]++F)++G0++E).
        apply H1; auto.
          rewrite_env ([(X, gbind_kn K)]++(F++G0++E)).
          apply wf_denv_nonlin_weakening_head; auto.
            apply wf_genv_kn; auto.
              eapply wf_genv_from_wf_denv; eauto.
  Case "atyping_tapp".
    apply atyping_tapp with (K':=K') (K:=K); auto.
      apply wf_atyp_weakening; auto.
        eapply uniq_from_wf_denv_nonlin; eauto.
Qed.

(** Context Monotonity*)

Lemma denv_mono : forall G D1 e T D2,
  atyping G D1 e T D2 ->
  <#D2#> <<= <#D1#>.
Proof with simpl_env; eauto.
  intros G D1 e T D2 Htyp.
  (atyping_cases (induction Htyp) Case); intros; subst; auto.
  Case "atyping_uvar". 
    apply dmap_Sub_refl; auto.
  Case "atyping_lvar". 
    apply dmap_Equal_rewrite_Sub_left with (M1:=<#D#>[-]x); auto.
      apply dmap_remove_mono.
  Case "atyping_uabs". 
    pick fresh y. apply H1 with y. auto.
  Case "atyping_labs". 
   pick fresh y.
   apply dmap_Equal_rewrite_Sub_right with (M2:=<#[(y,V)]++D#>[-]y); auto.
     simpl. apply dmap_add_remove_refl.
       apply notin_dom_implies_notIn; auto.
     apply dmap_sub_remove_free; auto.
       apply notin_dom_implies_notIn; auto.
  Case "atyping_app". 
    eapply dmap_Sub_trans; eauto.
  Case "atyping_tabs". 
    pick fresh Y. apply H1 with Y. auto.
Qed.

Lemma denv_mono_in_dom : forall G D1 e T D2 x,
  atyping G D1 e T D2 ->
  x `in` dom D2 ->
  x `in` dom D1.
Proof with eauto.
  intros. apply denv_mono in H. 
  unfold EMap_Submap in H.
  destruct H as [H1 H2].
  apply in_dom_implies_In in H0.
  apply In_implies_in_dom. auto.  
Qed.

Lemma denv_mono_notin_dom : forall G D1 e T D2 x,
  atyping G D1 e T D2 ->
  x `notin` dom D1 ->
  x `notin` dom D2.
Proof.
  intros.
  unfold not. intro J.
  apply H0. 
  apply denv_mono_in_dom with (x:=x) in H; auto.
Qed.

Lemma denv_mono_in_denv_fv_tt : forall G D1 e T D2 x,
  atyping G D1 e T D2 ->
  x `in` denv_fv_tt D2 ->
  x `in` denv_fv_tt D1.
Proof with eauto.
  intros G D1 e T D2 x Htyp Hxin.
  assert (J:=Htyp).  
  apply denv_mono in Htyp.
  apply atyping_regular in J.
  decompose [and] J. 
  eapply denv_sub_in_denv_fv_tt with (D2:=D2) ; eauto.
    eapply uniq_from_wf_denv_lin; eauto.
    eapply uniq_from_wf_denv_lin; eauto.
Qed.


Lemma denv_mono_notin_denv_fv_tt : forall G D1 e T D2 x,
  atyping G D1 e T D2 ->
  x `notin` denv_fv_tt D1 ->
  x `notin` denv_fv_tt D2.
Proof.
  intros.
  unfold not. intro J.
  apply H0. 
  apply denv_mono_in_denv_fv_tt with (x:=x) in H; auto.
Qed.

Corollary denv_mono_empty : forall G e T D2,
  atyping G dempty e T D2 ->
  <#D2#> ~~ @@.
Proof with eauto.
  intros. apply denv_mono in H.
  simpl in H.
  apply Sub_Empty_Empty; auto.
Qed.


(* ********************************************************************** *)
(** renaming *)
Lemma atyping_nonlin_typ_renaming : forall E D e T D' (X Y:atom) Q,
  X `notin` (fv_tt T `union` fv_te e `union` dom E `union` dom D `union` denv_fv_tt D) ->
  Y `notin` (fv_tt T `union` fv_te e `union` dom E `union` dom D `union` denv_fv_tt D) ->
  X <> Y ->
  atyping ([(X, gbind_kn Q)] ++ E) D (open_te e X) (open_tt T X) D' ->
  atyping ([(Y, gbind_kn Q)] ++ E) D (open_te e Y) (open_tt T Y) D'.
Proof.
  intros E D e T D' X Y Q FrX FrY HXnY Htyping.
  destruct_notin. 
  rewrite (subst_te_intro X); auto.
  rewrite (subst_tt_intro X); auto.
  rewrite_env (gempty ++ [(Y, gbind_kn Q)] ++ E).
  assert (gempty = map (subst_tgb X Y) gempty) as Hgeq.
    simpl. auto.
  rewrite Hgeq. clear Hgeq.
  assert (D = map (subst_tdb X Y) D) as Hdeq.
    apply map_subst_tdb_id with (G:=E); auto.
      apply atyping_regular in Htyping.
        decompose [and] Htyping; auto.
        apply wf_denv_nonlin_typ_strengthening_head in H1; auto.
  rewrite Hdeq. clear Hdeq.
  assert (D' = map (subst_tdb X Y) D') as Hdeq'.
    apply map_subst_tdb_id with (G:=E); auto.
      assert (J:=Htyping).
      apply atyping_regular in Htyping.
        decompose [and] Htyping; auto.
        apply wf_denv_nonlin_typ_strengthening_head in H0; auto.
          apply denv_mono_notin_denv_fv_tt with (x:=X) in J; auto.

      apply denv_mono_notin_dom with (x:=X) in Htyping; auto.
  rewrite Hdeq'. clear Hdeq'.
  apply atyping_through_subst_te with (Q:=Q) (Q':=Q); auto.
    simpl_env. eapply atyping_nonlin_weakening; eauto. 
      apply atyping_regular in Htyping.
      destruct Htyping as [Wf_genv [Wf_denv [Uniq Wf_atyp]]].
      apply wf_denv_nonlin_weakening; auto.
        apply wf_genv_kn; auto.
          inversion Wf_genv; subst.
          apply wf_genv_kn; auto.
    simpl. eapply wf_atyp_var; eauto.
      apply atyping_regular in Htyping.
      destruct Htyping as [Wf_genv [Wf_denv [Uniq Wf_atyp]]].
      apply uniq_from_wf_genv in Wf_genv.
      inversion Wf_genv; auto.
Qed.


Lemma wf_atyp_term_renaming : forall (x y : atom) F E T K V,
  x `notin` dom E `union` dom F ->
  y `notin` dom E `union` dom F ->
  x <> y ->
  wf_atyp (F ++ [(x, gbind_typ V)] ++ E) T K ->
  wf_atyp (F ++ [(y, gbind_typ V)] ++ E) T K.
Proof.
  intros x y F E T K V Frx Fry Hxny Wf_atyp.
  apply wf_atyp_weakening; auto.
    apply wf_atyp_strengthening in Wf_atyp; auto.
    apply uniq_from_wf_atyp in Wf_atyp.
    eapply uniq_renaming; eauto.
Qed.

Lemma wf_atyp_term_renaming_head : forall (x y : atom) E T K V,
  x `notin` dom E ->
  y `notin` dom E ->
  x <> y ->
  wf_atyp ([(x, gbind_typ V)] ++ E) T K ->
  wf_atyp ([(y, gbind_typ V)] ++ E) T K.
Proof.
  intros x y E T K V Frx Fry Hxny Wf_atyp.
  rewrite_env (gempty++[(y, gbind_typ V)] ++ E).
  eapply wf_atyp_term_renaming with (x:=x); eauto.
Qed.


Lemma wf_genv_term_renaming : forall F E (x y:atom) V,
  x `notin` dom E `union` dom F ->
  y `notin` dom E `union` dom F ->
  x <> y ->
  wf_genv (F ++ [(x, gbind_typ V)] ++ E) ->
  wf_genv (F ++ [(y, gbind_typ V)] ++ E).
Proof.
  intros F E x y V Frx Fry Hxny Wf_genv.
  remember (F ++ [(x, gbind_typ V)] ++ E) as G.
  generalize dependent F.
  generalize dependent E.
  generalize dependent y.
  generalize dependent x.
  generalize dependent V.
  induction Wf_genv; intros; subst.
    apply nil_neq_one_mid in HeqG.
    inversion HeqG.

    apply one_eq_app in HeqG.
    destruct HeqG as [[qs [H1 H2]]|[H1 H2]]; subst; simpl_env in *.
      apply wf_genv_kn; auto.
        eapply IHWf_genv; eauto.
      inversion H2.

    apply one_eq_app in HeqG.
    destruct HeqG as [[qs [H1 H2]]|[H1 H2]]; subst; simpl_env in *.
      apply wf_genv_typ; auto.
        eapply IHWf_genv; eauto.
          eapply wf_atyp_term_renaming with (x := x0); eauto.
      inversion H2; subst.
      apply wf_genv_typ; auto.
Qed.

Lemma wf_denv_nonlin_term_renaming : forall F E D (x y:atom) V,
  x `notin` (dom E `union` dom F `union` dom D) ->
  y `notin` (dom E `union` dom F `union` dom D) ->
  x <> y ->
  wf_denv (F ++ [(x, gbind_typ V)] ++ E) D ->
  wf_denv (F ++ [(y, gbind_typ V)] ++ E) D.
Proof.
  intros F E D x y V Frx Fry Hxny Wf_denv.
  apply wf_denv_nonlin_weakening.
    apply wf_denv_nonlin_term_strengthening in Wf_denv; auto.
    apply disjoint_one_2; auto.
    eapply wf_genv_term_renaming with (x := x); eauto.
      eapply wf_genv_from_wf_denv; eauto.
Qed.           

Lemma value_through_subst_ee : forall e x e',
  expr e' ->
  value e ->
  value (subst_ee x e' e).
Proof.
  intros e x e' exp H.
  induction H; simpl; auto using subst_ee_expr. 
  assert (expr (subst_ee x e' (exp_abs K T e1))).
    apply subst_ee_expr; auto.
  apply value_abs. simpl in H0; auto.

  assert (expr (subst_ee x e' (exp_tabs K e1))).
    apply subst_ee_expr; auto.
  apply value_tabs. simpl in H0; auto.
Qed.

Lemma value_renaming: forall e (x y:atom) kk,
  x `notin` (fv_ee e) ->  
  y `notin` (fv_ee e) ->  
  x <> y ->    
  value (open_ee_rec kk x e) ->
  value (open_ee_rec kk y e).
Proof.
  intros e x y kk Frx Fry Hxny Value.
  rewrite (subst_ee_intro_rec x); auto.
  apply value_through_subst_ee; auto.
Qed.

Definition P_atyping_nonlin_term_renaming_rec (n:nat) :=
  (forall F E D e T D' (x y:atom) V kk,
  exp_size e = n ->
  x `notin` (fv_ee e `union` dom E `union` dom F `union` dom D) ->
  y `notin` (fv_ee e `union` dom E `union` dom F `union` dom D) ->
  x <> y ->
  atyping (F++[(x, gbind_typ V)] ++ E) D (open_ee_rec kk x e) T D' ->
  atyping (F++[(y, gbind_typ V)] ++ E) D (open_ee_rec kk y e) T D').

Lemma _atyping_nonlin_term_renaming_rec: forall n, P_atyping_nonlin_term_renaming_rec n.
Proof with omega || auto.
  intros N.
  apply lt_wf_rec. clear N. unfold P_atyping_nonlin_term_renaming_rec.
  intros N IH F E D e T D' x y V kk Hsize Frx Fry Hxny Htyping.
  (exp_cases (destruct e) Case); simpl in *...
    (* bvar *)
    simpl in *. destruct (kk==n); simpl_env in*.
      (*kk==n*)
      inversion Htyping; subst.
        (*atyping_uvar*)
        analyze_binds_uniq H0.         
          apply uniq_from_wf_denv_nonlin in H3; auto.
          inversion BindsTacVal; subst.
          apply atyping_uvar; auto.
            eapply wf_denv_nonlin_term_renaming with (x:=x); eauto.
        (*atyping_lvar*)
        apply denv_dom_ginv with (x:=x) in H1; auto.
          apply binds_In in H0. 
          contradict H0; auto.

          rewrite dom_app. simpl. fsetdec.
      (*kk<>n*)
      inversion Htyping.
    (* fvar *)
    simpl in *; simpl_env in *.
    inversion Htyping; subst.
      (*atyping_uvar*)
      analyze_binds_uniq H0.
        apply uniq_from_wf_denv_nonlin in H3; auto.
        apply atyping_uvar; auto.
          eapply wf_denv_nonlin_term_renaming; eauto.
        apply atyping_uvar; auto.
          eapply wf_denv_nonlin_term_renaming; eauto.
      (*atyping_lvar*)
      apply atyping_lvar; auto.
        eapply wf_denv_nonlin_term_renaming with (x := x); eauto.
    (* abs *)
    simpl in *; simpl_env in *.
    inversion Htyping; subst.
      (*atyping_uabs*)
      destruct_notin.
      apply atyping_uabs with (L:=L `union` singleton x `union` singleton y); auto.
        eapply wf_atyp_term_renaming with (x := x); eauto.
        intros x0 Frx0.
        unfold open_ee in *.
        rewrite <- open_ee_rec_commute; auto.
        rewrite_env (([(x0,gbind_typ t)]++F)++((y,gbind_typ V)::E)).
        apply IH with (e:=(open_ee_rec 0 x0 e)) (x:=x) (m:=exp_size (open_ee_rec 0 x0 e)); auto.
          rewrite open_ee_rec_exp_size_eq; auto.
          assert (x `notin` fv_ee (open_ee_rec 0 x0 e)) as J.
            apply notin_fv_ee_open_ee_rec; auto.
          simpl in *; auto.
          assert (y `notin` fv_ee (open_ee_rec 0 x0 e)) as J.
            apply notin_fv_ee_open_ee_rec; auto.
          simpl in *; auto.
          rewrite open_ee_rec_commute; auto.
          simpl_env. apply H7; auto.
      (*atyping_labs*)
      destruct_notin.
      apply atyping_labs with (L:=L `union` singleton x `union` singleton y) (Q:=Q); auto.
        eapply wf_atyp_term_renaming; eauto.
        intros x0 Frx0.
        unfold open_ee in *.
        rewrite <- open_ee_rec_commute; auto.
        simpl.
        apply IH with (e:=(open_ee_rec 0 x0 e)) (x:=x) (m:=exp_size (open_ee_rec 0 x0 e)); auto.
          rewrite open_ee_rec_exp_size_eq; auto.
          assert (x `notin` fv_ee (open_ee_rec 0 x0 e)) as J.
            apply notin_fv_ee_open_ee_rec; auto.
          simpl in *; auto.
          assert (y `notin` fv_ee (open_ee_rec 0 x0 e)) as J.
            apply notin_fv_ee_open_ee_rec; auto.
          simpl in *; auto.
          rewrite open_ee_rec_commute; auto.
          simpl_env. apply H7; auto.
    (* app *)
    inversion Htyping; subst.
    apply atyping_app with (T1:=T1) (D2:=D2) (K:=K); auto.
      apply IH with (e:=e1) (x:=x) (m:=exp_size e1); auto.
        simpl. omega.
      apply IH with (e:=e2) (x:=x) (m:=exp_size e2); auto.
        simpl. omega.
        assert (x `notin` dom D2) as J.
          apply denv_mono_notin_dom with (x:=x) in H3; auto.
        auto.
        assert (y `notin` dom D2) as J.
          apply denv_mono_notin_dom with (x:=y) in H3; auto.
        auto.
    (* tabs *)
    simpl in *; simpl_env in *.
    inversion Htyping; subst.
    destruct_notin.
    apply atyping_tabs with (L:=L `union` singleton x `union` singleton y); auto.
      intros X FrX.
      assert (X `notin` L) as XnL. auto.
      apply H3 in XnL.
      unfold open_te in *.
      rewrite open_te_ee_rec_commute.
      rewrite open_te_ee_rec_commute in XnL.
      apply value_renaming with (x:=x) ; auto using notin_fv_ee_open_te_rec.

      intros X0 FrX0.
      unfold open_te in *.                                                           
      rewrite open_te_ee_rec_commute; auto.
      rewrite_env (([(X0,gbind_kn k)]++F)++(y,gbind_typ V)::E).
      apply IH with (e:=(open_te_rec 0 X0 e)) (x:=x) (m:=exp_size (open_te_rec 0 X0 e)); auto.
          rewrite open_te_rec_exp_size_eq; auto.
          assert (x `notin` fv_ee (open_te_rec 0 X0 e)) as J.
            apply notin_fv_ee_open_te_rec; auto.
          simpl. fsetdec.
          assert (y `notin` fv_ee (open_te_rec 0 X0 e)) as J.
            apply notin_fv_ee_open_te_rec; auto.
          simpl. fsetdec.
          rewrite <- open_te_ee_rec_commute; auto.
          simpl_env. apply H6; auto.    
    (* tapp *)
    inversion Htyping; subst.
    apply atyping_tapp with (K:=K) (K':=K'); auto.
      apply IH with (e:=e) (x:=x) (m:=exp_size e); auto.
      simpl_env. apply wf_atyp_term_renaming with (x:=x); auto.
    (* apair *) skip.
    (* fst *) skip.
    (* snd *) skip.
Qed.

Lemma atyping_nonlin_term_renaming_rec : forall F E D e T D' (x y:atom) V kk,
  x `notin` (fv_tt T `union` fv_ee e `union` dom E `union` dom F `union` dom D) ->
  y `notin` (fv_tt T `union` fv_ee e `union` dom E `union` dom F `union` dom D) ->
  x <> y ->
  atyping (F++[(x, gbind_typ V)] ++ E) D (open_ee_rec kk x e) T D' ->
  atyping (F++[(y, gbind_typ V)] ++ E) D (open_ee_rec kk y e) T D'.
Proof.
  intros F E D e T D' x y V kk Frx Fry Hxny Htyping.
  assert (J : P_atyping_nonlin_term_renaming_rec (exp_size e)) by auto using _atyping_nonlin_term_renaming_rec.
  unfold P_atyping_nonlin_term_renaming_rec in *.
  eapply J with (x:=x); eauto.
Qed.

Lemma atyping_nonlin_term_renaming_head : forall E D e T D' (x y:atom) V,
  x `notin` (fv_tt T `union` fv_ee e `union` dom E `union` dom D) ->
  y `notin` (fv_tt T `union` fv_ee e `union` dom E `union` dom D) ->
  x <> y ->
  atyping ([(x, gbind_typ V)] ++ E) D (open_ee e x) T D' ->
  atyping ([(y, gbind_typ V)] ++ E) D (open_ee e y) T D'.
Proof.
  intros E D e T D' x y V Frx Fry Hxny Htyping.
  rewrite_env (gempty ++ [(y, gbind_typ V)] ++ E).
  eapply atyping_nonlin_term_renaming_rec with (x:=x); eauto.
Qed.

Lemma wf_denv_lin_renaming : forall F E G (x y:atom) V,
  x `notin` (dom E `union` dom F `union` dom G) ->
  y `notin` (dom E `union` dom F `union` dom G) ->
  x <> y ->
  wf_denv G (F ++ [(x, V)] ++ E) ->
  wf_denv G (F ++ [(y, V)] ++ E).
Proof.
  intros F E G x y V Frx Fry Hxny Wf_denv.
  assert (exists K, wf_atyp G V K) as J.
    eapply wf_atyp_from_dbinds_typ with (x:=x); eauto.
  destruct J as [K J].
  apply wf_denv_lin_weakening with (K:=K); auto.
  apply wf_denv_lin_strengthening in Wf_denv; auto.
Qed.           

Lemma wf_denv_lin_renaming_head : forall E G (x y:atom) V,
  x `notin` (dom E `union` dom G) ->
  y `notin` (dom E `union` dom G) ->
  x <> y ->
  wf_denv G ([(x, V)] ++ E) ->
  wf_denv G ([(y, V)] ++ E).
Proof.
  intros E G x y V Frx Fry Hxny Wf_denv.
  rewrite_env (dempty ++ [(y, V)] ++ E).
  apply wf_denv_lin_renaming with (x:=x); auto.
Qed.

Lemma uniq_env_inv : forall A (F E F' E':list(atom*A)) x (B:A),
  uniq (F++[(x,B)]++E) ->
  F++[(x,B)]++E = F'++[(x,B)]++E' ->
  F = F' /\ E = E'.
Proof.
  intros A F E F' E' x B Uniq Eq.
  generalize dependent E.
  generalize dependent E'.
  generalize dependent F'.
  induction F; intros.
    simpl_env in Eq.
    apply one_eq_app in Eq.
    destruct Eq as [[es [H1 H2]]|[H1 H2]]; subst.
      rewrite_env (([(x,B)]++es)++[(x,B)]++E') in Uniq.
      solve_uniq.

      inversion H2; subst. auto.      

    destruct a.
    simpl_env in Eq.
    apply one_eq_app in Eq.
    destruct Eq as [[es [H1 H2]]|[H1 H2]]; subst.
      apply IHF in H2; auto.
        destruct H2 as [H21 H22]; subst. auto.
        inversion Uniq; subst; auto.

      inversion H2. subst.
      rewrite_env (([(a,a0)]++F)++[(a,a0)]++E) in Uniq.
      apply fresh_mid_head in Uniq.
      simpl_env in *. solve_notin.
Qed.

Lemma denv_fv_ginv : forall G D x b,  
  wf_denv G D ->  
  binds x b G ->  
  x `notin` dom D.
Proof.  
  intros. 
  eapply denv_dom_ginv; eauto.
Qed.

Lemma denv_mono_binds : forall G D1 e T D2 x V,   
  atyping G D1 e T D2 ->  
  binds x V D1 ->  
  (x `in` fv_ee e /\ x `notin` dom D2) 
    \/  
  (x `notin` fv_ee e /\ binds x V D2).
Proof with simpl_env; eauto. 
  intros G D1 e T D2 x V Htyp HxinD1. 
  (atyping_cases (induction Htyp) Case); subst...
  Case "atyping_uvar". 
    destruct (x0 == x)...  
    SCase "x0 = x". 
      subst. 
      assert (x `notin` dom D) as contra. 
        eapply denv_fv_ginv; eauto.
      eauto.
  Case "atyping_lvar".
    destruct (x0 == x)...   
    SCase "x0 = x". 
      subst. left. 
      simpl fv_ee.
      split.
        fsetdec.
        assert (~ EMap.In x (<#D#> [-] x)) as J.
          apply dmap_remove_clear.
        apply notIn_implies_notin_dom2.
        eapply not_find_in_iff.
        rewrite <- H2.
        eapply not_find_in_iff; auto.
    SCase "x0 <> x". 
      right. 
      split; auto.
        eapply denv_to_dmap_iso; auto.
        rewrite <- H2.        
        eapply find_mapsto_iff.
        apply dmap_remove_noteq_mapsto; auto.
        eapply find_mapsto_iff.
        eapply denv_to_dmap_iso; auto.
          apply uniq_from_wf_denv_lin in H0; auto.
  Case "atyping_uabs". 
    simpl fv_ee. 
    pick fresh x0. 
    assert (x `in` fv_ee (open_ee e1 x0) /\ x `notin` dom D' \/      
            x `notin` fv_ee (open_ee e1 x0) /\ binds x V D') as J1. 
      auto. 
    destruct J1 as [[J1 J2]|[J1 J2]]; eauto 6.
  Case "atyping_labs".
    simpl fv_ee. 
    pick fresh x0.  
    assert (x `in` fv_ee (open_ee e1 x0) /\ x `notin` dom D' \/      
            x `notin` fv_ee (open_ee e1 x0) /\ binds x V D') as J1.
      apply H1; auto.
    destruct J1 as [[J1 J2]|[J1 J2]]; eauto 6.
  Case "atyping_app". 
    simpl fv_ee. 
    apply IHHtyp1 in HxinD1. 
    destruct HxinD1 as [[H1 H2]|[H1 H2]].
    SCase "left". 
      left.
      split.
        fsetdec.
        apply denv_mono_notin_dom with (x:=x) in Htyp2; auto.
     SCase "right".
       apply IHHtyp2 in H2.
       destruct H2 as [[H21 H22]|[H21 H22]]; auto.
   Case "atyping_tabs". 
     simpl fv_ee. 
     pick fresh X.     
     assert (x `in` fv_ee (open_te e1 X) /\ x `notin` dom D' \/      
             x `notin` fv_ee (open_te e1 X) /\ binds x V D') as J. 
       auto.
     destruct J as [[J1 J2]|[J1 J2]]; auto.
     SCase "left". 
       left. split; auto. 
        eapply in_open_te_fv_ee with (Y:=X); auto.
     SCase "right". 
       right. split; auto.
        eapply notin_open_te_fv_ee with (Y:=X); auto.
Qed.

Lemma denv_mono_aux : forall G D1 e T D2 x,   
  atyping G D1 e T D2 ->  
  x `in` dom D1 ->  
  (x `in` fv_ee e /\ x `notin` dom D2) 
    \/  
  (x `notin` fv_ee e /\ x `in` dom D2).
Proof with simpl_env; eauto. 
  intros G D1 e T D2 x Htyp HxinD1. 
  (atyping_cases (induction Htyp) Case); subst...
  Case "atyping_uvar". 
    destruct (x0 == x)...  
    SCase "x0 = x". 
      subst. 
      assert (x `notin` dom D) as contra. 
        eapply denv_fv_ginv; eauto.
      eauto.
  Case "atyping_lvar".
    destruct (x0 == x)...   
    SCase "x0 = x". 
      subst. left. 
      simpl fv_ee.
      split.
        fsetdec.
        assert (~ EMap.In x (<#D#> [-] x)) as J.
          apply dmap_remove_clear.
        apply notIn_implies_notin_dom2.
        eapply not_find_in_iff.
        rewrite <- H2.
        eapply not_find_in_iff; auto.
    SCase "x0 <> x". 
      right. 
      split; auto.
        apply In_implies_in_dom.  
        eapply in_find_iff.
        rewrite <- H2.
        eapply in_find_iff.
        apply dmap_remove_noteq_in; auto.
        apply in_dom_implies_In; auto.

  Case "atyping_uabs". 
    simpl fv_ee. 
    pick fresh x0. 
    assert (x `in` fv_ee (open_ee e1 x0) /\ x `notin` dom D' \/      
            x `notin` fv_ee (open_ee e1 x0) /\ x `in` dom D') as J1. 
      auto. 
    destruct J1 as [[J1 J2]|[J1 J2]]; eauto 6.
  Case "atyping_labs". 
    simpl fv_ee. 
    pick fresh x0.  
    assert (x `in` fv_ee (open_ee e1 x0) /\ x `notin` dom D' \/      
            x `notin` fv_ee (open_ee e1 x0) /\ x `in` dom D') as J1.
      apply H1; auto.
        rewrite dom_app. simpl. fsetdec.
    destruct J1 as [[J1 J2]|[J1 J2]]; eauto 6.
  Case "atyping_app". 
    simpl fv_ee. 
    apply IHHtyp1 in HxinD1. 
    destruct HxinD1 as [[H1 H2]|[H1 H2]].
    SCase "left". 
      left.
      split.
        fsetdec.
        apply denv_mono_notin_dom with (x:=x) in Htyp2; auto.
     SCase "right".
       apply IHHtyp2 in H2.
       destruct H2 as [[H21 H22]|[H21 H22]]; eauto 6.
   Case "atyping_tabs". 
     simpl fv_ee. 
     pick fresh X.     
     assert (x `in` fv_ee (open_te e1 X) /\ x `notin` dom D' \/      
             x `notin` fv_ee (open_te e1 X) /\ x `in` dom D') as J. 
       auto.
     destruct J as [[J1 J2]|[J1 J2]]; eauto 6.
Qed.

Lemma denv_mono_disjoint : forall G D e t D' x,
  atyping G D e t D' ->
  x `in` fv_ee e ->
  x `notin` dom D'.
Proof.
  intros G D e t D' x Htyp xine.
  destruct (@in_dec x (dom D)) as [H | H].
    apply denv_mono_aux with (x:=x) in Htyp; auto.
    apply denv_mono_notin_dom with (x:=x) in Htyp; auto.
Qed.

Lemma atyping_fv_inv : forall G D1 e T D2 x,  
  atyping G D1 e T D2 ->  
  x `notin` dom G ->  
  x `notin` dom D1 ->  
  x  `notin` fv_ee e /\ x `notin` dom D2.
Proof with simpl_env; eauto. 
  intros G D1 e T D2 x Htyp HxnotinG HxnotinD1. 
  (atyping_cases (induction Htyp) Case); simpl fv_ee; simpl fv_te; simpl fv_tt; subst.
  Case "atyping_uvar". 
    split; auto.
      destruct (x == x0); subst; auto.
        apply binds_In in H. contradict H; auto.
  Case "atyping_lvar". 
    split; auto.
      destruct (x == x0); subst; auto.
        apply binds_In in H. contradict H; auto.

      apply notIn_implies_notin_dom2.
      eapply not_find_in_iff.
      rewrite <- H2.
      eapply not_find_in_iff.
      intro J.
      apply remove_in_iff in J.
      destruct J as [J1 J2].
      apply In_implies_in_dom in J2.
      contradict J2; auto.
  Case "atyping_uabs". 
    pick fresh x0.
    assert (x `notin` fv_ee (open_ee e1 x0) /\
            x `notin` dom D') as J.
      apply H1; auto.
    destruct J as [J1 J2].
    split; auto.
  Case "atyping_labs". 
    pick fresh x0.
    assert (x `notin` fv_ee (open_ee e1 x0) /\
            x `notin` dom D') as J.
      apply H1; auto.
    destruct J as [J1 J2].
    split; auto.
  Case "atyping_app".     
    assert (x `notin` fv_ee e1 /\
            x `notin` dom D2) as J1.
      apply IHHtyp1; auto.
    destruct J1 as [J11 J12].
    assert (x `notin` fv_ee e2 /\
            x `notin` dom D3) as J2.
      apply IHHtyp2; auto.
    destruct J2 as [J21 J22].
    split; auto.
  Case "atyping_tabs". 
    pick fresh X0.
    assert (x `notin` fv_ee (open_te e1 X0) /\
            x `notin` dom D') as J.
      apply H1; auto.
    destruct J as [J1 J2].
    split; auto.
      apply notin_open_te_fv_ee_rec in J1; auto.
  Case "atyping_tapp".     
    assert (x `notin` fv_ee e1 /\
            x `notin` dom D') as J1.
      apply IHHtyp; auto.
    destruct J1 as [J11 J12].
    split; auto.
Qed.

Corollary denv_mono_app : forall G D1 e1 e2 T D2 x,  
  atyping G D1 (exp_app e1 e2) T D2  ->  
  x `in` dom D1 ->  
  (x `in` fv_ee e1 /\ x `notin` fv_ee e2 /\ x `notin` dom D2) 
    \/  
  (x `notin` fv_ee e1 /\ x `in` fv_ee e2 /\ x `notin` dom D2) 
    \/  
  (x `notin` fv_ee e1 /\ x `notin` fv_ee e2 /\ x `in` dom D2).
Proof with simpl_env; eauto. 
  intros G D1 e1 e2 T D2 x Htyp HinD1.
  inversion Htyp; subst.   
  assert ((x `in` fv_ee e1 /\ x `notin` dom D3) \/  
          (x `notin` fv_ee e1 /\ x `in` dom D3)) as J1.
    eapply denv_mono_aux; eauto. 
  destruct J1 as [[J1 J2]|[J1 J2]]; auto.
  Case "left".
    left. split; auto.
      assert (Htyp1 := H3).
      apply atyping_regular in H3. 
      destruct H3 as [E1 [E2 [E3 [E4 E5]]]].   
      assert (x `notin` dom G) as J3. 
        eapply denv_dom_dinv with (D:=D1); eauto.    
      apply atyping_fv_inv with (x:=x) in H6; auto.
  Case "right".
    right.
    assert ((x `in` fv_ee e2 /\ x `notin` dom D2) \/  
            (x `notin` fv_ee e2 /\ x `in` dom D2)) as JJ2.
      eapply denv_mono_aux; eauto. 
    destruct JJ2 as [[JJ1 JJ2]|[JJ1 JJ2]]; auto.
Qed.

Definition P_atyping_lin_term_renaming_rec (n:nat) :=
  (forall G F E e T D' (x y:atom) V kk,
  exp_size e = n ->
  x `notin` (fv_ee e `union` dom G `union` dom F `union` dom E) ->
  y `notin` (fv_ee e `union` dom G `union` dom F `union` dom E) ->
  x <> y ->
  atyping G (F ++ [(x, V)] ++ E) (open_ee_rec kk x e) T D' ->
  (
    ((x `in` fv_ee (open_ee_rec kk x e)) -> 
      atyping G (F ++ [(y, V)] ++ E) (open_ee_rec kk y e) T D'))
   /\
    ((x `notin` fv_ee (open_ee_rec kk x e)) -> 
      forall D1' D2',
       D' = D1' ++ [(x, V)] ++ D2' ->
       atyping G (F ++ [(y, V)] ++ E) (open_ee_rec kk y e) T (D1' ++ [(y, V)] ++ D2'))
  ).

Lemma _atyping_lin_term_renaming_rec: forall n, P_atyping_lin_term_renaming_rec n.
Proof with omega || auto.
  intros N.
  apply lt_wf_rec. clear N. unfold P_atyping_lin_term_renaming_rec.
  intros N IH G F E e T D' x y V kk Hsize Frx Fry Hxny Htyping.
  (exp_cases (destruct e) Case); simpl in *...
    (* bvar *)
    simpl in *. destruct (kk==n); simpl_env in*.
      (*kk==n*)
      inversion Htyping; subst.
        (*atyping_uvar*)
        apply denv_dom_dinv with (x:=x) in H3; auto.
          apply binds_In in H0. 
          contradict H0; auto.

          rewrite dom_app. simpl. fsetdec.
        (*atyping_lvar*)
        assert (uniq (F ++ [(x,V)] ++ E)) as Uniq.
          apply uniq_from_wf_denv_lin in H1; auto.
        analyze_binds_uniq H0; subst.
          split; intro Hx.
            (* x `in` fv_ee x *)
            apply atyping_lvar; auto.
              eapply wf_denv_lin_renaming with (x:=x); eauto.
              apply Equal_trans with (m':=<#F++[(x,V)]++E#>[-]x); auto.
                apply Equal_trans with (m':=<#F++E#>).
                  apply denv_remove_mid.
                    apply uniq_from_wf_denv_lin in H1; auto.
                    apply uniq_renaming with (x:=x) (Tx:=V); auto.
                  apply Equal_sym.
                    apply denv_remove_mid.
                      apply uniq_from_wf_denv_lin in H1; auto.
            (* x `notin` fv_ee x *)
            simpl in Hx.
            assert (False) as K.
              apply Hx. clear Hx.
              fsetdec.
            inversion K.            
      (*kk<>n*)
      inversion Htyping.
    (* fvar *)
    simpl in *; simpl_env in *.
    inversion Htyping; subst.
      (*atyping_uvar*)
      split; intro J.
        assert (a `notin` dom (F++[(x,V)]++E)) as Hanotind.
          apply denv_dom_ginv with (x:=a) in H3; auto.
            apply binds_In in H0; auto.
        rewrite dom_app in Hanotind.
        rewrite dom_app in Hanotind.
        simpl in Hanotind.
        contradict J; auto.

        intros D1' D2' Heq.
      simpl_env in Heq.
      assert (uniq (F++[(x,V)]++E)) as Uniq.
        apply uniq_from_wf_denv_lin in H3; auto.
      apply uniq_env_inv in Heq; auto.
      destruct Heq as [H1 H2]; subst.
      simpl_env.
      apply atyping_uvar; auto.
        apply wf_denv_lin_renaming with (x:=x); auto.
      (*atyping_lvar*)
      assert (uniq (F ++ [(x,V)] ++ E)) as Uniq.
        apply uniq_from_wf_denv_lin in H1; auto.
      analyze_binds_uniq H0; subst.
        (* a:T in F, a notin x, E *)
        split; intro Hx.
          contradict Hx; auto.
          clear IH.
          assert (EMap.MapsTo x V (<#F++[(x,V)]++E#>[-]a)) as J.
            eapply remove_mapsto_iff.
              split.
                fsetdec.
                   
                destruct (@Equal_mapsto_iff typ (<#F++[(x,V)]++E#>) (<#[(x,V)]++F++E#>)) as [J1 J2].
                assert (<#F++[(x,V)]++E#> ~~ <#[(x,V)]++F++E#>) as HH.
                  rewrite_env (dempty++F++dempty++[(x,V)]++E).
                  rewrite_env (dempty++[(x,V)]++dempty++F++E).
                  apply disjoint_denv_cons_commut_aux; auto.
                apply J1 with (k:=x) (e:=V) in HH.
                eapply HH.
                simpl.
                eapply add_mapsto_iff; auto.
          assert (EMap.MapsTo x V (<#D'#>)) as J'.
            destruct (@Equal_mapsto_iff typ (<#F++[(x,V)]++E#>[-]a) (<#D'#>)) as [J1 J2].
            apply J1 with (k:=x) (e:=V) in H5.
            eapply H5. auto.
          apply find_mapsto_iff in J'.
          apply denv_to_dmap_iso in J'; auto.
          apply binds_inv in J'.
          destruct J' as [E' [F' J']]; subst.
          intros D1' D2' Heq.
          simpl_env in Heq.
          apply uniq_env_inv in Heq; auto.
          destruct Heq as [HH1 HH2].
          subst D1'. subst D2'.
          simpl_env.
          assert (y `notin` union (dom F') (dom E')) as K.
            assert (<#F'++[(x,V)]++E'#> <<= <#F++[(x,V)]++E#>) as HH.
              apply denv_mono in Htyping; auto.
            apply dmap_remove_preserves_Sub in HH; auto.
            rewrite <- dom_app.
            apply denv_sub_notin_dom with (D1:=F++E); auto.
              apply uniq_remove_mid in H2. auto.
              apply uniq_remove_mid in Uniq. auto.                

          apply atyping_lvar; auto.
            apply wf_denv_lin_renaming with (x:=x); auto.
            apply uniq_renaming with (x:=x) (Tx:=V); auto.
              assert (H7:=H2).
              apply fresh_mid_tail in H2.
              apply fresh_mid_head in H7.
              auto.
    
              assert (y<>a) as Hyna.
                destruct (y==a); subst; auto.
              apply dmap_remove_renaming with (x:=x); auto.
                apply uniq_remove_mid in Uniq.
                apply uniq_insert_mid; auto.

                apply uniq_remove_mid in H2.
                apply uniq_insert_mid; auto.
                 
        (* a:T in E, a notin x, F *)
        split; intro Hx.
          contradict Hx; auto.
          clear IH.
          assert (EMap.MapsTo x V (<#F++[(x,V)]++E#>[-]a)) as J.
            eapply remove_mapsto_iff.
              split.
                fsetdec.
                   
                destruct (@Equal_mapsto_iff typ (<#F++[(x,V)]++E#>) (<#[(x,V)]++F++E#>)) as [J1 J2].
                assert (<#F++[(x,V)]++E#> ~~ <#[(x,V)]++F++E#>) as HH.
                  rewrite_env (dempty++F++dempty++[(x,V)]++E).
                  rewrite_env (dempty++[(x,V)]++dempty++F++E).
                  apply disjoint_denv_cons_commut_aux; auto.
                apply J1 with (k:=x) (e:=V) in HH.
                eapply HH.
                simpl.
                eapply add_mapsto_iff; auto.
          assert (EMap.MapsTo x V (<#D'#>)) as J'.
            destruct (@Equal_mapsto_iff typ (<#F++[(x,V)]++E#>[-]a) (<#D'#>)) as [J1 J2].
            apply J1 with (k:=x) (e:=V) in H5.
            eapply H5. auto.
          apply find_mapsto_iff in J'.
          apply denv_to_dmap_iso in J'; auto.
          apply binds_inv in J'.
          destruct J' as [E' [F' J']]; subst.
          intros D1' D2' Heq.
          simpl_env in Heq.
          apply uniq_env_inv in Heq; auto.
          destruct Heq as [HH1 HH2].
          subst D1'. subst D2'.
          simpl_env.
          assert (y `notin` union (dom F') (dom E')) as K.
            assert (<#F'++[(x,V)]++E'#> <<= <#F++[(x,V)]++E#>) as HH.
              apply denv_mono in Htyping; auto.
            apply dmap_remove_preserves_Sub in HH; auto.
            rewrite <- dom_app.
            apply denv_sub_notin_dom with (D1:=F++E); auto.
              apply uniq_remove_mid in H2. auto.
              apply uniq_remove_mid in Uniq. auto.                

          apply atyping_lvar; auto.
            apply wf_denv_lin_renaming with (x:=x); auto.
            apply uniq_renaming with (x:=x) (Tx:=V); auto.
              assert (H8:=H2).
              apply fresh_mid_tail in H2.
              apply fresh_mid_head in H8.
              auto.
    
              assert (y<>a) as Hyna.
                destruct (y==a); subst; auto.
              apply dmap_remove_renaming with (x:=x); auto.
                apply uniq_remove_mid in Uniq.
                apply uniq_insert_mid; auto.

                apply uniq_remove_mid in H2.
                apply uniq_insert_mid; auto.

    (* abs *)
    simpl in *; simpl_env in *.
    inversion Htyping; subst.
     (*atyping_uabs*)
     destruct_notin.
     split; intro J.
      (* x in \x.e *)
      apply atyping_uabs with (L:=L `union` singleton x `union` singleton y); auto.
        intros x0 Frx0.
        unfold open_ee in *.
        rewrite <- open_ee_rec_commute; auto.
        simpl.
        assert (      
          (x `in` fv_ee (open_ee_rec (S kk) x (open_ee_rec 0 x0 e)) ->
            atyping ((x0, gbind_typ t)::G) (F ++ (y, V) :: E) (open_ee_rec (S kk) y (open_ee_rec 0 x0 e)) T1 D') 
          /\
          (x `notin` fv_ee (open_ee_rec (S kk) x (open_ee_rec 0 x0 e)) ->
            forall D1' D2',
                D' = D1' ++ (x, V) :: D2' ->
                atyping ((x0, gbind_typ t)::G) (F ++ (y, V) :: E) (open_ee_rec (S kk) y (open_ee_rec 0 x0 e)) T1
                  (D1' ++ (y, V) :: D2'))
        ) as IHH.
          apply IH with (e:=(open_ee_rec 0 x0 e)) (x:=x) (m:=exp_size (open_ee_rec 0 x0 e)); auto.
            rewrite open_ee_rec_exp_size_eq; auto.
            assert (x `notin` fv_ee (open_ee_rec 0 x0 e)) as J'.
              apply notin_fv_ee_open_ee_rec; auto.
            simpl. fsetdec.
            assert (y `notin` fv_ee (open_ee_rec 0 x0 e)) as J'.
              apply notin_fv_ee_open_ee_rec; auto.
            simpl. fsetdec.
            rewrite open_ee_rec_commute; auto.
            simpl_env. apply H7; auto.
        clear IH.
        destruct IHH as [IHH1 IHH2]. clear IHH2.
        apply IHH1.
          rewrite open_ee_rec_commute; auto.
          apply in_fv_ee_open_ee_rec; auto.

        intro J'. apply H8 in J'.
        assert (uniq (F ++ [(x,V)] ++ E)) as Uniq.
          apply atyping_regular in Htyping.
          decompose [and] Htyping.
          apply uniq_from_wf_denv_lin in H1; auto.
        assert (<#F++[(x,V)]++E#>~~<#[(x,V)]++F++E#>) as Heq.
          rewrite_env (dempty++F++dempty++[(x,V)]++E).
          rewrite_env (dempty++[(x,V)]++dempty++F++E).
          apply disjoint_denv_cons_commut_aux; auto.
        assert (<#[(x,V)]++F++E#>~~<#D'#>) as Heq'.
          apply Equal_trans with (m':=<#F++[(x,V)]++E#>); auto.
            apply Equal_sym; auto.  
        assert (x `in` dom D') as HxinD'.
          apply In_implies_in_dom.
          eapply in_find_iff.
          rewrite <- Heq'.
          eapply in_find_iff.
          simpl.
          eapply add_in_iff; auto.
   
        assert (x `notin` dom D') as Contra.
          apply denv_mono_aux with (x:=x) in Htyping; auto.
            rewrite dom_app. rewrite dom_app.
            simpl. fsetdec.
        contradict HxinD'; auto.
      (* x notin \x.e *)
      intros D1' D2' Eq. subst.
      apply atyping_uabs with (L:=L `union` singleton x `union` singleton y); auto.
        intros x0 Frx0.
        unfold open_ee in *.
        rewrite <- open_ee_rec_commute; auto.
        simpl.     
        assert (      
          (x `in` fv_ee (open_ee_rec (S kk) x (open_ee_rec 0 x0 e)) ->
            atyping ((x0, gbind_typ t)::G) (F ++ (y, V) :: E) (open_ee_rec (S kk) y (open_ee_rec 0 x0 e)) T1 (D1' ++ (x, V) :: D2')) 
          /\
          (x `notin` fv_ee (open_ee_rec (S kk) x (open_ee_rec 0 x0 e)) ->
            forall D1'0 D2'0,
                D1' ++ (x, V) :: D2' = D1'0 ++ (x, V) :: D2'0 ->
                atyping ((x0, gbind_typ t)::G) (F ++ (y, V) :: E) (open_ee_rec (S kk) y (open_ee_rec 0 x0 e)) T1
                  (D1'0 ++ (y, V) :: D2'0))
        ) as IHH.
          apply IH with (e:=(open_ee_rec 0 x0 e)) (x:=x) (m:=exp_size (open_ee_rec 0 x0 e)); auto.
            rewrite open_ee_rec_exp_size_eq; auto.
            assert (x `notin` fv_ee (open_ee_rec 0 x0 e)) as J'.
              apply notin_fv_ee_open_ee_rec; auto.
            simpl. fsetdec.
            assert (y `notin` fv_ee (open_ee_rec 0 x0 e)) as J'.
              apply notin_fv_ee_open_ee_rec; auto.
            simpl. fsetdec.
            rewrite open_ee_rec_commute; auto.
            simpl_env. apply H7; auto.
        clear IH.
        destruct IHH as [IHH1 IHH2]. clear IHH1.
        apply IHH2; auto.
          rewrite open_ee_rec_commute; auto.
          apply notin_fv_ee_open_ee_rec; auto.

        intro J'. apply H8 in J'.
        simpl_env.
        assert (uniq (F++ [(x,V)] ++ E)) as Uniq.
          apply atyping_regular in Htyping.
          decompose [and] Htyping.
          apply uniq_from_wf_denv_lin in H1; auto.
        assert (uniq (D1'++ [(x,V)] ++ D2')) as Uniq'.
          apply atyping_regular in Htyping.
          decompose [and] Htyping.
          apply uniq_from_wf_denv_lin in H0; auto.
        assert (y `notin` union (dom D1') (dom D2')) as K.
          assert (<#D1'++[(x,V)]++D2'#> <<= <#F++[(x,V)]++E#>) as HH.
            apply denv_mono in Htyping; auto.
          apply dmap_remove_preserves_Sub in HH; auto.
          rewrite <- dom_app.
          apply denv_sub_notin_dom with (D1:=F++E); auto.
            apply uniq_remove_mid in Uniq'. auto.                
            apply uniq_remove_mid in Uniq. auto.  
        apply dmap_Equal_renaming with (x:=x); auto.
          apply uniq_remove_mid in Uniq.
          apply uniq_insert_mid; auto.

          apply uniq_remove_mid in Uniq'.
          apply uniq_insert_mid; auto.
     (*atyping_labs*)
     destruct_notin.
     split; intro J.
      (* x in \x.e *)
      apply atyping_labs with (L:=L `union` singleton x `union` singleton y) (Q:=Q); auto.
        intros x0 Frx0.
        unfold open_ee in *.
        rewrite <- open_ee_rec_commute; auto.
        simpl.
        assert (      
          (x `in` fv_ee (open_ee_rec (S kk) x (open_ee_rec 0 x0 e)) ->
            atyping G (((x0, t) :: F) ++ (y, V) :: E) (open_ee_rec (S kk) y (open_ee_rec 0 x0 e)) T1 D') 
          /\
          (x `notin` fv_ee (open_ee_rec (S kk) x (open_ee_rec 0 x0 e)) ->
            forall D1' D2',
                D' = D1' ++ (x, V) :: D2' ->
                atyping G (((x0, t):: F) ++ (y, V) :: E) (open_ee_rec (S kk) y (open_ee_rec 0 x0 e)) T1
                  (D1' ++ (y, V) :: D2'))
        ) as IHH.
          apply IH with (e:=(open_ee_rec 0 x0 e)) (x:=x) (m:=exp_size (open_ee_rec 0 x0 e)); auto.
            rewrite open_ee_rec_exp_size_eq; auto.
            assert (x `notin` fv_ee (open_ee_rec 0 x0 e)) as J'.
              apply notin_fv_ee_open_ee_rec; auto.
            simpl. fsetdec.
            assert (y `notin` fv_ee (open_ee_rec 0 x0 e)) as J'.
              apply notin_fv_ee_open_ee_rec; auto.
            simpl. fsetdec.
            rewrite open_ee_rec_commute; auto.
            simpl_env. apply H7; auto.
        clear IH.
        destruct IHH as [IHH1 IHH2]. clear IHH2.
        apply IHH1.
          rewrite open_ee_rec_commute; auto.
          apply in_fv_ee_open_ee_rec; auto.

        intro J'. apply H8 in J'.
        assert (uniq (F ++ [(x,V)] ++ E)) as Uniq.
          apply atyping_regular in Htyping.
          decompose [and] Htyping.
          apply uniq_from_wf_denv_lin in H1; auto.
        assert (<#F++[(x,V)]++E#>~~<#[(x,V)]++F++E#>) as Heq.
          rewrite_env (dempty++F++dempty++[(x,V)]++E).
          rewrite_env (dempty++[(x,V)]++dempty++F++E).
          apply disjoint_denv_cons_commut_aux; auto.
        assert (<#[(x,V)]++F++E#>~~<#D'#>) as Heq'.
          apply Equal_trans with (m':=<#F++[(x,V)]++E#>); auto.
            apply Equal_sym; auto.  
        assert (x `in` dom D') as HxinD'.
          apply In_implies_in_dom.
          eapply in_find_iff.
          rewrite <- Heq'.
          eapply in_find_iff.
          simpl.
          eapply add_in_iff; auto.

        assert (x `notin` dom D') as Contra.
          apply denv_mono_aux with (x:=x) in Htyping; auto.
            rewrite dom_app. rewrite dom_app.
            simpl. fsetdec.
        contradict HxinD'; auto.
      (* x notin \x.e *)
      intros D1' D2' Eq. subst.
      apply atyping_labs with (L:=L `union` singleton x `union` singleton y) (Q:=Q); auto.
        intros x0 Frx0.
        unfold open_ee in *.
        rewrite <- open_ee_rec_commute; auto.
        simpl.     
        assert (      
          (x `in` fv_ee (open_ee_rec (S kk) x (open_ee_rec 0 x0 e)) ->
            atyping G (((x0, t)::F) ++ (y, V) :: E) (open_ee_rec (S kk) y (open_ee_rec 0 x0 e)) T1 (D1' ++ (x, V) :: D2')) 
          /\
          (x `notin` fv_ee (open_ee_rec (S kk) x (open_ee_rec 0 x0 e)) ->
            forall D1'0 D2'0,
                D1' ++ (x, V) :: D2' = D1'0 ++ (x, V) :: D2'0 ->
                atyping G (((x0, t)::F) ++ (y, V) :: E) (open_ee_rec (S kk) y (open_ee_rec 0 x0 e)) T1
                  (D1'0 ++ (y, V) :: D2'0))
        ) as IHH.
          apply IH with (e:=(open_ee_rec 0 x0 e)) (x:=x) (m:=exp_size (open_ee_rec 0 x0 e)); auto.
            rewrite open_ee_rec_exp_size_eq; auto.
            assert (x `notin` fv_ee (open_ee_rec 0 x0 e)) as J'.
              apply notin_fv_ee_open_ee_rec; auto.
            simpl. fsetdec.
            assert (y `notin` fv_ee (open_ee_rec 0 x0 e)) as J'.
              apply notin_fv_ee_open_ee_rec; auto.
            simpl. fsetdec.
            rewrite open_ee_rec_commute; auto.
            simpl_env. apply H7; auto.
        clear IH.
        destruct IHH as [IHH1 IHH2]. clear IHH1.
        apply IHH2; auto.
          rewrite open_ee_rec_commute; auto.
          apply notin_fv_ee_open_ee_rec; auto.

        intro J'. apply H8 in J'.
        simpl_env.
        assert (uniq (F++ [(x,V)] ++ E)) as Uniq.
          apply atyping_regular in Htyping.
          decompose [and] Htyping.
          apply uniq_from_wf_denv_lin in H1; auto.
        assert (uniq (D1'++ [(x,V)] ++ D2')) as Uniq'.
          apply atyping_regular in Htyping.
          decompose [and] Htyping.
          apply uniq_from_wf_denv_lin in H0; auto.
        assert (y `notin` union (dom D1') (dom D2')) as K.
          assert (<#D1'++[(x,V)]++D2'#> <<= <#F++[(x,V)]++E#>) as HH.
            apply denv_mono in Htyping; auto.
          apply dmap_remove_preserves_Sub in HH; auto.
          rewrite <- dom_app.
          apply denv_sub_notin_dom with (D1:=F++E); auto.
            apply uniq_remove_mid in Uniq'. auto.                
            apply uniq_remove_mid in Uniq. auto.  
        apply dmap_Equal_renaming with (x:=x); auto.
          apply uniq_remove_mid in Uniq.
          apply uniq_insert_mid; auto.

          apply uniq_remove_mid in Uniq'.
          apply uniq_insert_mid; auto.
    (* app *)
    inversion Htyping; subst.
    assert (      
     (x `in` fv_ee (open_ee_rec kk x e1) ->
       atyping G (F ++ (y, V) :: E) (open_ee_rec kk y e1) (typ_arrow K T1 T) D2) 
     /\
     (x `notin` fv_ee (open_ee_rec kk x e1) ->
       forall D21 D22,
          D2 = D21 ++ (x, V) :: D22 ->
          atyping G (F ++ (y, V) :: E) (open_ee_rec kk y e1) (typ_arrow K T1 T)
            (D21 ++ (y, V) :: D22))
     ) as IHH1.
       apply IH with (e:=e1) (x:=x) (m:=exp_size e1); auto.
         omega.
    destruct IHH1 as [IHH11 IHH12].
    assert (
      (x `in` fv_ee (open_ee_rec kk x e1) /\ x `notin` fv_ee (open_ee_rec kk x e2) /\ x `notin` dom D') 
        \/  
      (x `notin` fv_ee (open_ee_rec kk x e1) /\ x `in` fv_ee (open_ee_rec kk x e2) /\ x `notin` dom D') 
        \/  
      (x `notin` fv_ee (open_ee_rec kk x e1) /\ x `notin` fv_ee (open_ee_rec kk x e2) /\ x `in` dom D')
    ) as J.
      apply denv_mono_app with (D1:=F++(x,V)::E) (T:=T) (G:=G).
        eapply atyping_app with (T1:=T1) (K:=K) (D2:=D2); eauto.
        rewrite dom_app. rewrite dom_cons. simpl. fsetdec.
    destruct J as [[J1 [J2 J3]] | [[J1 [J2 J3]] | [J1 [J2 J3]]]].
      (*x in e1, x notin e2, x notin D'*)
      split; intro J.
        eapply atyping_app with (T1:=T1) (K:=K) (D2:=D2); eauto.
          rewrite subst_ee_intro_rec with (x:=x); auto.
          rewrite <- subst_ee_fresh; auto.
        destruct_notin. contradict J1; auto.       
      (*x notin e1, x in e2, x notin D'*)
      assert (binds x V D2) as HxinD2.
        apply denv_mono_binds with (x:=x) (V:=V) in H3; auto.
          destruct H3 as [[H31 H32]|[H31 H32]]; auto.
            contradict H31; auto.
      apply binds_inv in HxinD2.
      destruct HxinD2 as [D21 [D22 Heq]]; subst.
      apply IHH12 with (D23:=D22) (D24:=D21) in J1; auto.
      clear IHH12 IHH11.
      assert (      
       (x `in` fv_ee (open_ee_rec kk x e2) ->
         atyping G (D22 ++ (y, V) :: D21) (open_ee_rec kk y e2) T1 D') 
       /\
       (x `notin` fv_ee (open_ee_rec kk x e2) ->
         forall D1' D2',
            D' = D1' ++ (x, V) :: D2' ->
            atyping G (D22 ++ (y, V) :: D21) (open_ee_rec kk y e2) T1
              (D1' ++ (y, V) :: D2'))
       ) as IHH2.
         assert (uniq (F ++ [(x,V)] ++ E)) as Uniq.
           apply atyping_regular in H3. 
           decompose [and] H3.
           apply uniq_from_wf_denv_lin in H1; auto.
         assert (uniq (D22 ++ [(x,V)] ++ D21)) as Uniq'.
           apply atyping_regular in H3. 
           decompose [and] H3.
           apply uniq_from_wf_denv_lin in H0; auto.
         assert (<#D22++D21#> <<= <#F++E#>) as Hsub.
           apply denv_mono in H3.
             simpl_env in H3.
             apply dmap_remove_preserves_Sub in H3; auto.
         assert (x `notin` union (dom D22) (dom D21)) as J.
           rewrite <- dom_app.
           apply denv_sub_notin_dom with (x:=x) in Hsub; auto.
             apply uniq_remove_mid in Uniq'; auto.
             apply uniq_remove_mid in Uniq; auto.
         assert (y `notin` union (dom D22) (dom D21)) as J'.
           rewrite <- dom_app.
           apply denv_sub_notin_dom with (x:=y) in Hsub; auto.
             apply uniq_remove_mid in Uniq'; auto.
             apply uniq_remove_mid in Uniq; auto.
         apply IH with (e:=e2) (x:=x) (m:=exp_size e2); auto.
           omega.
       clear IH.
       destruct IHH2 as [IHH21 IHH22]. clear IHH22.
       split; intro J.      
          apply IHH21 in J2.
          eapply atyping_app with (T1:=T1) (K:=K) (D2:=D22++(y,V)::D21); eauto.
          destruct_notin. contradict J2; auto.       
      (*x notin e1, x notin e2, x in D'*)
      assert (binds x V D2) as HxinD2.
        apply denv_mono_binds with (x:=x) (V:=V) in H3; auto.
          destruct H3 as [[H31 H32]|[H31 H32]]; auto.
            contradict H31; auto.
      apply binds_inv in HxinD2.
      destruct HxinD2 as [D21 [D22 Heq]]; subst.
      assert (J11:=J1).
      apply IHH12 with (D23:=D22) (D24:=D21) in J1; auto.
      clear IHH12 IHH11.
      assert (      
       (x `in` fv_ee (open_ee_rec kk x e2) ->
         atyping G (D22 ++ (y, V) :: D21) (open_ee_rec kk y e2) T1 D') 
       /\
       (x `notin` fv_ee (open_ee_rec kk x e2) ->
         forall D1' D2',
            D' = D1' ++ (x, V) :: D2' ->
            atyping G (D22 ++ (y, V) :: D21) (open_ee_rec kk y e2) T1
              (D1' ++ (y, V) :: D2'))
       ) as IHH2.
         assert (uniq (F ++ [(x,V)] ++ E)) as Uniq.
           apply atyping_regular in H3. 
           decompose [and] H3.
           apply uniq_from_wf_denv_lin in H1; auto.
         assert (uniq (D22 ++ [(x,V)] ++ D21)) as Uniq'.
           apply atyping_regular in H3. 
           decompose [and] H3.
           apply uniq_from_wf_denv_lin in H0; auto.
         assert (<#D22++D21#> <<= <#F++E#>) as Hsub.
           apply denv_mono in H3.
             simpl_env in H3.
             apply dmap_remove_preserves_Sub in H3; auto.
         assert (x `notin` union (dom D22) (dom D21)) as J.
           rewrite <- dom_app.
           apply denv_sub_notin_dom with (x:=x) in Hsub; auto.
             apply uniq_remove_mid in Uniq'; auto.
             apply uniq_remove_mid in Uniq; auto.
         assert (y `notin` union (dom D22) (dom D21)) as J'.
           rewrite <- dom_app.
           apply denv_sub_notin_dom with (x:=y) in Hsub; auto.
             apply uniq_remove_mid in Uniq'; auto.
             apply uniq_remove_mid in Uniq; auto.
         apply IH with (e:=e2) (x:=x) (m:=exp_size e2); auto.
           omega.
       clear IH.
       destruct IHH2 as [IHH21 IHH22]. clear IHH21.
       split; intro J.
          contradict J; auto.       

          intros D1' D2' EQ; subst.
          apply IHH22 with (D1'0:=D1') (D2'0:=D2') in J2; auto.
          eapply atyping_app with (T1:=T1) (K:=K) (D2:=D22++(y,V)::D21); eauto.
    (* tabs *)
    simpl in *; simpl_env in *.
    inversion Htyping; subst.
    destruct_notin.
    split; intro J.
      (* x in \x.e *)
      apply atyping_tabs with (L:=L `union` singleton x `union` singleton y); auto.
        intros X FrX.
        assert (X `notin` L) as XnL. auto.
        apply H3 in XnL.
        unfold open_te in *.
        rewrite open_te_ee_rec_commute.
        rewrite open_te_ee_rec_commute in XnL.
        apply value_renaming with (x:=x) ; auto using notin_fv_ee_open_te_rec.

        intros X0 FrX0.
        unfold open_te in *.                                                           
        rewrite open_te_ee_rec_commute; auto.
        simpl.
        assert (      
          (x `in` fv_ee (open_ee_rec kk x (open_te_rec 0 X0 e)) ->
            atyping ((X0, gbind_kn k)::G) (F ++ (y, V) :: E) (open_ee_rec kk y (open_te_rec 0 X0 e)) (open_tt T1 X0) D') 
          /\
          (x `notin` fv_ee (open_ee_rec kk x (open_te_rec 0 X0 e)) ->
            forall D1' D2',
                D' = D1' ++ (x, V) :: D2' ->
                atyping ((X0, gbind_kn k)::G) (F ++ (y, V) :: E) (open_ee_rec kk y (open_te_rec 0 X0 e)) (open_tt T1 X0)
                  (D1' ++ (y, V) :: D2'))
        ) as IHH.
          apply IH with (e:=(open_te_rec 0 X0 e)) (x:=x) (m:=exp_size (open_te_rec 0 X0 e)); auto.
            rewrite open_te_rec_exp_size_eq; auto.
            assert (x `notin` fv_ee (open_te_rec 0 X0 e)) as J'.
              apply notin_fv_ee_open_te_rec; auto.
            simpl. fsetdec.
            assert (y `notin` fv_ee (open_te_rec 0 X0 e)) as J'.
              apply notin_fv_ee_open_te_rec; auto.
            simpl. fsetdec.
            rewrite <- open_te_ee_rec_commute; auto.
            simpl_env. apply H6; auto.    
        clear IH.
        destruct IHH as [IHH1 IHH2]. clear IHH2.
        apply IHH1.
          rewrite <- open_te_ee_rec_commute; auto.
          apply in_fv_ee_open_te_rec; auto.
      (* x notin \x.e *)
      intros D1' D2' Eq. subst.
      apply atyping_tabs with (L:=L `union` singleton x `union` singleton y); auto.
        intros X FrX.
        assert (X `notin` L) as XnL. auto.
        apply H3 in XnL.
        unfold open_te in *.
        rewrite open_te_ee_rec_commute.
        rewrite open_te_ee_rec_commute in XnL.
        apply value_renaming with (x:=x) ; auto using notin_fv_ee_open_te_rec.

        intros X0 FrX0.
        unfold open_te in *.                                                           
        rewrite open_te_ee_rec_commute; auto.
        simpl.
        assert (      
          (x `in` fv_ee (open_ee_rec kk x (open_te_rec 0 X0 e)) ->
            atyping ((X0, gbind_kn k)::G) (F ++ (y, V) :: E) (open_ee_rec kk y (open_te_rec 0 X0 e)) (open_tt T1 X0) (D1' ++ [(x,V)] ++ D2')) 
          /\
          (x `notin` fv_ee (open_ee_rec kk x (open_te_rec 0 X0 e)) ->
            forall D1'0 D2'0,
                D1' ++ [(x,V)] ++ D2' = D1'0 ++ (x, V) :: D2'0 ->
                atyping ((X0, gbind_kn k)::G) (F ++ (y, V) :: E) (open_ee_rec kk y (open_te_rec 0 X0 e)) (open_tt T1 X0)
                  (D1'0 ++ (y, V) :: D2'0))
        ) as IHH.
          apply IH with (e:=(open_te_rec 0 X0 e)) (x:=x) 
                        (m:=exp_size (open_te_rec 0 X0 e)) (kk:=kk) 
                        (y:=y)(V:=V) (G:=(X0, gbind_kn k)::G)
                        (F:=F) (E:=E)
                        (D':=D1' ++ [(x,V)] ++ D2') (T:=(open_tt T1 X0)); auto.
            rewrite open_te_rec_exp_size_eq; auto.
            assert (x `notin` fv_ee (open_te_rec 0 X0 e)) as J'.
              apply notin_fv_ee_open_te_rec; auto.
            simpl. fsetdec.
            assert (y `notin` fv_ee (open_te_rec 0 X0 e)) as J'.
              apply notin_fv_ee_open_te_rec; auto.
            simpl. fsetdec.
            rewrite <- open_te_ee_rec_commute; auto.
            simpl_env. apply H6; auto.    
        clear IH.
        destruct IHH as [IHH1 IHH2]. clear IHH1.
        apply IHH2; auto.
          rewrite <- open_te_ee_rec_commute; auto.
          apply notin_fv_ee_open_te_rec; auto.
    (* tapp *)
    inversion Htyping; subst.
    destruct_notin.
    assert (      
      (x `in` fv_ee (open_ee_rec kk x e) ->
        atyping G (F ++ (y, V) :: E) (open_ee_rec kk y e) (typ_all K T2) D') 
      /\
      (x `notin` fv_ee (open_ee_rec kk x e) ->
        forall D1' D2',
          D' = D1' ++ (x, V) :: D2' ->
          atyping G (F ++ (y, V) :: E) (open_ee_rec kk y e) (typ_all K T2)
            (D1' ++ (y, V) :: D2'))
    ) as IHH.
      apply IH with (e:=e) (x:=x) (m:=exp_size e); auto.
    clear IH.
    destruct IHH as [IHH1 IHH2].
    split; intro J.
      (* x in \x.e *)
      apply atyping_tapp with (K:=K) (K':=K'); auto.
      (* x notin \x.e *)
      intros D1' D2' Eq. subst.
      apply atyping_tapp with (K:=K) (K':=K'); auto.
    (* apair *) skip.
    (* fst *) skip.
    (* snd *) skip.
Qed.

Lemma atyping_lin_term_renaming_rec : forall G F E e T D' (x y:atom) V kk,
  x `notin` (fv_ee e `union` dom G `union` dom F `union` dom E) ->
  y `notin` (fv_ee e `union` dom G `union` dom F `union` dom E) ->
  x <> y ->  atyping G (F ++ [(x, V)] ++ E) (open_ee_rec kk x e) T D' ->
  (
    ((x `in` fv_ee (open_ee_rec kk x e)) -> 
      atyping G (F ++ [(y, V)] ++ E) (open_ee_rec kk y e) T D'))
   /\
    ((x `notin` fv_ee (open_ee_rec kk x e)) -> 
      forall D1' D2',
       D' = D1' ++ [(x, V)] ++ D2' ->
       atyping G (F ++ [(y, V)] ++ E) (open_ee_rec kk y e) T (D1' ++ [(y, V)] ++ D2')
  ).
Proof.
  intros G F E e T D' x y V kk Frx Fry Hxny Htyping.
  assert (J : P_atyping_lin_term_renaming_rec (exp_size e)) by auto using _atyping_lin_term_renaming_rec.
  unfold P_atyping_lin_term_renaming_rec in *.
  eapply J with (x:=x); eauto.
Qed.

Lemma atyping_lin_term_renaming_head : forall G E e T D' (x y:atom) V kk,
  x `notin` (fv_ee e `union` dom G `union` dom E) ->
  y `notin` (fv_ee e `union` dom G `union` dom E) ->
  x <> y ->  atyping G ([(x, V)] ++ E) (open_ee_rec kk x e) T D' ->
  (
    ((x `in` fv_ee (open_ee_rec kk x e)) -> 
      atyping G ([(y, V)] ++ E) (open_ee_rec kk y e) T D'))
   /\
    ((x `notin` fv_ee (open_ee_rec kk x e)) -> 
      forall D2',
       D' = [(x, V)] ++ D2' ->
       atyping G ([(y, V)] ++ E) (open_ee_rec kk y e) T ([(y, V)] ++ D2')
  ).
Proof.
  intros G E e T D' x y V kk Frx Fry Hxny Htyping.
  rewrite_env (dempty ++ [(x, V)] ++ E) in Htyping.
  apply atyping_lin_term_renaming_rec with (y:=y) in Htyping; eauto.
  destruct Htyping as [H1 H2].
  split; auto.
    intros J D2' Eq; subst.
    apply H2 with (D1':=dempty) (D2'0:=D2') in J; auto.
Qed.

Lemma atyping_lin_term_renaming_head_in : forall G D e T D' (x y:atom) V,
  x `notin` (fv_ee e `union` dom G `union` dom D) ->
  y `notin` (fv_ee e `union` dom G `union` dom D) ->
  x <> y ->
  x `in` fv_ee (open_ee e x) -> 
  atyping G ([(x, V)] ++ D) (open_ee e x) T D' ->
  atyping G ([(y, V)] ++ D) (open_ee e y) T D'.
Proof.
  intros G D e T D' x y V Frx Fry Hxny Hxin Htyping.
  assert(
    ((x `in` fv_ee (open_ee e x)) -> 
      atyping G ([(y, V)] ++ D) (open_ee e y) T D')
   /\
    ((x `notin` fv_ee (open_ee e x)) -> 
      forall D2',
       D' = [(x, V)] ++ D2' ->
       atyping G ([(y, V)] ++ D) (open_ee e y) T ([(y, V)] ++ D2')
    )
  ) as H.
    apply atyping_lin_term_renaming_head; auto.
  destruct H; auto.
Qed.

Lemma atyping_lin_term_renaming_head_notin : forall G D e T D' (x y:atom) V,
  x `notin` (fv_ee e `union` dom G `union` dom D) ->
  y `notin` (fv_ee e `union` dom G `union` dom D) ->
  x <> y ->
  x `notin` fv_ee (open_ee e x) -> 
  atyping G ([(x, V)] ++ D) (open_ee e x) T D' ->
  forall D2',
  D' = [(x, V)] ++ D2' ->
  atyping G ([(y, V)] ++ D) (open_ee e y) T ([(y, V)] ++ D2').
Proof.
  intros G D e T D' x y V Frx Fry Hxny Hxin Htyping.
  assert(
    ((x `in` fv_ee (open_ee e x)) -> 
      atyping G ([(y, V)] ++ D) (open_ee e y) T D')
   /\
    ((x `notin` fv_ee (open_ee e x)) -> 
      forall D2',
       D' = [(x, V)] ++ D2' ->
       atyping G ([(y, V)] ++ D) (open_ee e y) T ([(y, V)] ++ D2')
    )
  ) as H.
    apply atyping_lin_term_renaming_head; auto.
  destruct H; auto.
Qed.

(* ********************************************************************** *)
(**  Permutation. *)
Lemma atyping_permutation : forall G D1 D1' e t D2,
  atyping G D1 e t D2 ->
  uniq D1' ->
  D1 ~~~ D1' ->
  exists D2', atyping G D1' e t D2' /\ D2 ~~~ D2'.
Proof.
  intros G D1 D1' e t D2 Htyp Huniq' Heq.
  generalize dependent D1'.
  assert (Htyping:=Htyp).
  (atyping_cases (induction Htyp) Case); intros; subst.
  Case "atyping_uvar". 
    apply denv_permutation with (D':=D1') in H0; auto.
    exists D1'. split; auto.
  Case "atyping_lvar".
    assert (J:=H0).
    apply uniq_from_wf_denv_lin in J.
    apply denv_permutation with (D':=D1') in H0; auto.
    exists D'.
    split.
      apply atyping_lvar; auto.
        eapply binds_permutation; eauto.
        apply Equal_trans with (m':=<# D #>[-]x); auto.    
          apply dmap_remove_preserves_Equal; auto.
            apply Equal_sym; auto.
      apply Equal_refl.
  Case "atyping_uabs".
    pick fresh x.
    assert (x `notin` L) as HfrL. auto.
    apply H1 with (D1':=D1') in HfrL; auto.
    destruct HfrL as [D2' [Htyp2' Heq']].
    exists D2'.
    split; auto.
      apply atyping_uabs with (L:=L `union` fv_tt T1 `union` fv_ee e1 `union` dom G `union` dom D1' `union` singleton x); auto.
        intros x0 Hx0.
        destruct_notin.
        eapply atyping_nonlin_term_renaming_head; eauto.       

        intro J.
        apply H2 in J.
        apply Equal_trans with (m':=<#D'#>); auto.
          apply Equal_trans with (m':=<#D#>); auto.
            apply Equal_sym; auto.
  Case "atyping_labs".
    pick fresh x.
    assert (x `notin` L) as HfrL. auto.
    apply H1 with (D1':=[(x, V)] ++ D1') in HfrL; auto.
      destruct HfrL as [D2' [Htyp2' Heq']].
      exists D2'. (* this is ok, because x isnt D2'!!! *)
      split; auto.
        apply atyping_labs with (L:=L `union` fv_tt T1 `union` fv_ee e1 
                                      `union` dom G `union` dom D1' `union` dom D2' 
                                      `union` singleton x) (Q:=Q); auto.
          intros x0 Hx0.
          destruct_notin.
          apply atyping_lin_term_renaming_head_in with (x:=x); auto.       
            assert (x `notin` dom D2') as J.
              eapply (@denv_equal_notin_dom_iff D' D2' x Heq'); auto.
          apply denv_mono_aux with (x:=x) in Htyp2'; auto.
            destruct Htyp2' as [[J1 J2]|[J1 J2]]; auto.
              contradict J2; auto.
            rewrite dom_app. simpl. fsetdec.

          intro J.
          apply H2 in J.
          apply Equal_trans with (m':=<#D'#>); auto.
            apply Equal_trans with (m':=<#D#>); auto.
              apply Equal_sym; auto.
      apply denv_add_preserves_Equal; auto.
  Case "atyping_app".
    assert (J := Heq).
    apply IHHtyp1 in J; auto.
      destruct J as [D2' [Jtyp1 Heq1]].
      apply IHHtyp2 in Heq1; auto.
        destruct Heq1 as [D3' [Jtyp2 Heq2]].
        exists D3'.
        split; eauto.
          apply atyping_regular in Jtyp1.
          decompose [and] Jtyp1; auto.
          eapply uniq_from_wf_denv_lin; eauto.
  Case "atyping_tabs".
    pick fresh X.
    assert (X `notin` L) as HfrL. auto.
    apply H1 with (D1':= D1') in HfrL; auto.
    destruct HfrL as [D2' [Htyp2 Heq']].
    exists D2'.
    split; auto.
      apply atyping_tabs with (L:=L `union` fv_tt T1 `union` fv_te e1 `union` dom G `union` dom D1' `union` dom D2' `union` singleton X `union` denv_fv_tt D1' ); auto.
        intros X0 HX0.
        destruct_notin.
        apply atyping_nonlin_typ_renaming with (X:=X); auto.
  Case "atyping_tapp".
    apply IHHtyp in Heq; auto.
      destruct Heq as [D2' [Jtyp1 Heq]].
      exists D2'.
      split; eauto.
Qed.

(* ********************************************************************** *)
(** Weakening and Strengthening *)
Lemma wf_genv_merging: forall E F G,
  wf_genv (G ++ E) ->
  wf_genv (F ++ E) ->
  uniq (G ++ F ++ E) ->
  wf_genv (G ++ F ++ E).
Proof.
  intros E F G. 
  generalize dependent F.
  induction G; intros F H1 H2 OK.
  Case "empty".
    simpl_env. auto.
  rewrite_env ([a] ++ (G ++ E)) in H1.
  rewrite_env ([a] ++ (G ++ F ++ E)).
  rewrite_env ([a] ++ (G ++ F ++ E)) in OK.
  inversion H1.
  Case "kn".
    apply wf_genv_kn. apply IHG. auto. auto. eapply uniq_app_2. eauto. subst. inversion OK. auto.
  Case "typ".
    eapply wf_genv_typ. apply IHG; auto. eapply uniq_app_2. eauto. eapply wf_atyp_weakening. eapply H4.
    eapply uniq_app_2. eauto. subst. inversion OK. auto.
Qed.


Lemma wf_genv_merging_head: forall E F,
  wf_genv E ->
  wf_genv F ->
  uniq (F ++ E) ->
  wf_genv (F ++ E).
Proof.
  intros E F.
  generalize dependent E.
  induction F; intros E WF1 WF2 OK.
  simpl. auto.
  inversion WF2. 
  rewrite_env ([(X, gbind_kn K)] ++ F ++ E).
  eapply wf_genv_kn. apply IHF; auto. rewrite_env ([a] ++ (F ++ E)) in OK. eapply uniq_app_2. eapply OK. subst a.
  inversion OK.  auto.
  rewrite_env ([(x, gbind_typ T)] ++ F ++ E).
  eapply wf_genv_typ. apply IHF; auto. rewrite_env ([a] ++ (F ++ E)) in OK. eapply uniq_app_2. eapply OK. 
  rewrite_env (F ++ E ++ gempty). apply wf_atyp_weakening. rewrite <- app_nil_end. eapply H2.
  rewrite <- app_nil_end. rewrite_env ([a] ++ (F ++ E)) in OK. eapply uniq_app_2. eapply OK. 
  subst a. inversion OK.  auto.
Qed.



(* *********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

(** The lemma [uniq_from_wf_env] was already added above as a hint since it
    helps blur the distinction between [wf_env] and [ok] in proofs.

    As currently stated, the regularity lemmas are ill-suited to be
    used with [auto] and [eauto] since they end in conjunctions.  Even
    if we were, for example, to split [sub_regularity] into three
    separate lemmas, the resulting lemmas would be usable only by
    [eauto] and there is no guarantee that [eauto] would be able to
    find proofs effectively.  Thus, the hints below apply the
    regularity lemmas and [type_from_wf_typ] to discharge goals about
    local closure and well-formedness, but in such a way as to
    minimize proof search.

    The first hint introduces an [wf_env] fact into the context.  It
    works well when combined with the lemmas relating [wf_env] and
    [wf_typ].  We choose to use those lemmas explicitly via [(auto
    using ...)] tactics rather than add them as hints.  When used this
    way, the explicitness makes the proof more informative rather than
    more cluttered (with useless details).

    The other three hints try outright to solve their respective
    goals. *)

Hint Extern 1 (wf_genv ?G) =>
  match goal with
  | H: atyping _ _ _ _ _ |- _ => apply (proj1 (atyping_regular _ _ _ _ _ H))
  end.

Hint Extern 1 (wf_denv ?G ?D ) =>
  match goal with
  | H: atyping _ _ _ _ _ |- _ => apply (proj1 (proj2 (atyping_regular _ _ _ _ _ H)))
  | H: atyping _ _ _ _ _ |- _ => apply (proj1 (proj2 (proj2 (atyping_regular _ _ _ _ _ H))))
  end.

Hint Extern 1 (expr ?e) =>
  match goal with
  | H: atyping _ _ ?e _ _ |- _ => apply (proj2 (proj2 (proj2 (proj2 (atyping_regular _ _ _ _ _ H)))))
  | H: red ?e _ |- _ => apply (proj1 (red_regular _ _ _ _ H))
  | H: red _ ?e |- _ => apply (proj2 (red_regular _ _ _ _ H))
  end.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../../../metatheory" "-I" "../linf") ***
*** End: ***
 *)

