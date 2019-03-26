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

(*
Axiom skip : False.
Ltac skip := assert False; [ apply skip | contradiction ].
*)

Lemma value_through_open_te: forall e1 T,
  value e1 ->
  value (open_te e1 T).
Proof.
  intros.
  unfold open_te. 
  rewrite <- open_te_rec_expr; auto.
Qed.

Lemma nonlin_value_is_under_equal_linctx : forall G D e T D',
  atyping G D e T D' ->
  wf_atyp G T kn_nonlin ->
  value e ->
  D ~~~ D'.
Proof.
  intros G D e T D' Hatyp Hwf_atyp Hvalue.
  (* linear ctx is mon *)
  assert (Hdenv_mon := Hatyp).
  apply denv_mono in Hdenv_mon.
  (atyping_cases (induction Hatyp) Case); try solve [inversion Hvalue].
  Case "atyping_uabs".
    (* trivial, because when k is *, the lin ctx cannot be changed *)
    inversion Hwf_atyp; subst.
    inversion H10; subst.
    assert (kn_nonlin = kn_nonlin) as EQ; auto.
  Case "atyping_labs".
    (* trivial, because when k is *, the lin ctx cannot be changed *)
    inversion Hwf_atyp; subst.
    inversion H10; subst.
    assert (kn_nonlin = kn_nonlin) as EQ; auto.
  Case "atyping_tabs".
    (* By IH *)
    inversion Hwf_atyp; subst.
    pick fresh X.
    apply H1 with (X:=X); auto.
Qed.

Lemma wf_denv_lin_sub_strengthening : forall G D D',  
  wf_denv G D ->  
  <#D'#> <<= <#D#> ->
  uniq D' ->
  wf_denv G D'.
Proof.  
  intros G D D'.  
  generalize dependent G.  
  generalize dependent D'. 
  induction D; intros D' G Wf_denv Hsub UniqD'; auto.   
    simpl in Hsub.
    apply Sub_Empty_Empty in Hsub.
    apply Equal_sym in Hsub.
    apply dmap_eq_empty_inv in Hsub.
    apply denv_eq_empty_inv in Hsub. 
    subst. auto.

    destruct a as [a t].
    destruct (@EMapsTo_dec a t <#D'#>) as [J1 | J1].
      assert (EMap.In a <#D'#>) as J.
        destruct (@in_mapsto_iff <#D'#> a) as [H1 H2].
        apply H1.
        exists t. auto.
      apply dmap_remove_preserves_Sub_right with (x:=a) in Hsub.
        apply dmap_Equal_rewrite_Sub_right with (M2':=<#D#>) in Hsub.
          simpl_env in Wf_denv.
          assert (Wf_denv':=Wf_denv).
          apply wf_denv_lin_strengthening_head in Wf_denv; auto.
          apply IHD with (D':=<@<#D'#>[-]a@>) in Wf_denv.
            assert (a `notin` dom G) as HanotinG.
              apply denv_dom_dinv with (x:=a) in Wf_denv'; auto.
                rewrite dom_app. simpl. fsetdec.
            apply wf_atyp_from_dbinds_typ with (x:=a) (U:=t) in Wf_denv'; auto.
            destruct Wf_denv' as [K Wf_atyp].
            apply wf_denv_typ with (x:=a) (T:=t) (D:=<@<#D'#>[-]a@>) (K:=K); auto.
              apply notIn_implies_notin_dom.
              intro H.
              apply remove_in_iff in H.
              destruct H as [H1 H2].
              apply H1; auto.

            intro y.
            remember (EMap.find (elt:=typ) y <#D'#>) as R.
            destruct R; apply sym_eq in HeqR.
              eapply find_mapsto_iff.
              simpl.
              eapply add_mapsto_iff.
              destruct (a==y); subst.
                apply find_mapsto_iff in HeqR.
                left. split; auto.
                  apply MapsTo_fun with (x:=y) (m:=<#D'#>); auto.
                right. split; auto.
                  rewrite <- remove_iff_raw_remove.
                  assert (H := @denv_to_from_dmap (<#D'#>[-]a)).
                  eapply (@Equal_mapsto_rewrite (<#D'#>[-]a) <#<@<#D'#>[-]a@>#>); auto.
                  eapply remove_mapsto_iff.
                  split; auto.
                    apply find_mapsto_iff in HeqR; auto.

              eapply not_find_in_iff.
              simpl.
              apply not_find_in_iff in HeqR.
              intro H.
              apply HeqR. clear HeqR.
              apply add_in_iff in H.
              destruct H as [H | H]; subst; auto.
                rewrite <- remove_iff_raw_remove in H.
                assert (HH := @denv_to_from_dmap (<#D'#>[-]a)).                         
                apply (@in_if_Equal (<#D'#>[-]a) <#<@<#D'#>[-]a@>#>) in H; auto.
                apply remove_in_iff in H.
                destruct H as [H1 H2]; auto.

            apply dmap_Equal_rewrite_Sub_left with (M1':=<#<@<#D'#>[-]a@>#>) in Hsub; auto.
              apply denv_to_from_dmap; auto.
                apply dmap_to_denv_is_uniq.

          apply dmap_add_remove_refl; auto.
            apply notin_dom_implies_notIn.
              apply uniq_from_wf_denv_lin in Wf_denv.
              inversion Wf_denv; auto.

      apply dmap_sub_remove_free with (x:=a) in Hsub; auto.
        apply dmap_Equal_rewrite_Sub_right with (M2':=<#D#>) in Hsub.
          apply IHD; auto.
            simpl_env in Wf_denv.
            apply wf_denv_lin_strengthening_head in Wf_denv; auto.
          apply dmap_add_remove_refl; auto.
            apply notin_dom_implies_notIn.
              apply uniq_from_wf_denv_lin in Wf_denv.
              inversion Wf_denv; auto.

        intro J. apply J1. clear J1.
        destruct Hsub as [Hsub1 Hsub2].
        assert (K:=J).
        apply in_mapsto_iff in J.
        destruct J as [e J].
        apply Hsub1 in K. 
        assert (EMap.MapsTo a t <#(a,t)::D#>) as KK.
          simpl. eapply add_mapsto_iff.
          left; auto.
        assert (e = t) as JJ. 
          eapply beq_typ_iff_eq. eauto.
        subst. auto.         
Qed.

Lemma wf_denv_lin_diff_strengthening : forall G D D',
  wf_denv G D ->
  wf_denv G <@<#D#>--<#D'#>@>.
Proof.
  intros G D D' Wf_denv.
  generalize dependent D'.
  induction Wf_denv; intros.
    simpl. apply denv_permutation with (D:=dempty); auto.
      apply uniq_nil.
      apply Equal_refl.

    assert (J:=@IHWf_denv D'0).
    apply dmap_diff_preserves_Equal with (M'':=<#D'0#>) in H3.
    assert (((<#[(x, T)]#>--<#D'0#>) |_| (<#D#>--<#D'0#>)) ~~ <#D'#> -- <#D'0#>) as JJ.
      eapply Equal_trans with (m':=<#[(x,T)]++D#>--<#D'0#>); auto.
        apply Equal_sym.
        eapply Equal_trans with (m':=(<#[(x,T)]#>|_|<#D#>)--<#D'0#>); auto.
          apply dmap_Equal_rewrite_diff_left with (M1:=<#[(x,T)]++D#>); auto.
            apply disjoint_denv_cons_union.
              apply uniq_push; auto.
                apply uniq_from_wf_denv_lin in Wf_denv; auto.
            apply Equal_refl.        
          apply dmap_union_diff_distr.

    destruct (in_dec x (dom D'0)) as [xinD'0 | xnotinD'0].
      (* x in dom D'0 *)
      apply denv_permutation with (D:=<@<#D#>--<#D'0#>@>); auto.
        apply dmap_to_denv_is_uniq.
        apply Equal_trans with (m':=(<#[(x, T)]#>--<#D'0#>) |_| (<#D#>--<#D'0#>)); auto.
          apply dmap_Equal_rewrite_Union_left with (M1:=@@).
            apply Equal_sym.
              apply singleton_diff_empty; auto.
          apply Equal_trans with (m':=<#D#>--<#D'0#>); auto.
            apply Equal_sym.
              apply denv_to_from_dmap; auto.
            apply Equal_sym.
              apply dmap_union_empty_refl.
                   
          apply Equal_trans with (m':=(<#[(x, T)]++D#>--<#D'0#>)); auto.
            apply Equal_sym.
              eapply Equal_trans with (m':=(<#[(x,T)]#>|_|<#D#>)--<#D'0#>); auto.
                apply dmap_Equal_rewrite_diff_left with (M1:=<#[(x,T)]++D#>); auto.
                  apply disjoint_denv_cons_union.
                    apply uniq_push; auto.
                      apply uniq_from_wf_denv_lin in Wf_denv; auto.
                  apply Equal_refl.
              apply dmap_union_diff_distr.
            apply Equal_trans with (m':=<#D'#>--<#D'0#>); auto.
              apply denv_to_from_dmap; auto.
      (* x notin dom D'0 *)
      assert (x `notin` dom (<@ <#D#> -- <#D'0#> @>)) as xnotinD.
        assert ((<#D#>--<#D'0#>)<<=<#D#>) as Hsub.
          apply dmap_diff_mono; auto.
        apply denv_sub_notin_dom with (D1:=D); auto.
          apply dmap_to_denv_is_uniq.
          apply uniq_from_wf_denv_lin in Wf_denv; auto.
          apply dmap_Equal_rewrite_Sub_left with (M1:=(<#D#>--<#D'0#>)); auto.
            apply denv_to_from_dmap; auto.
      apply wf_denv_typ with (D:=<@<#D#>--<#D'0#>@>) (x:=x) (T:=T) (K:=K); auto.       
        apply dmap_to_denv_is_uniq.
        apply Equal_trans with (m':=(<#[(x, T)]#>--<#D'0#>) |_| (<#D#>--<#D'0#>)); auto.
          apply dmap_Equal_rewrite_Union_left with (M1:=<#[(x,T)]#>).
            apply Equal_sym.
              apply singleton_diff_refl; auto.
            apply dmap_Equal_rewrite_Union_right with (M2:=<#<@<#D#>--<#D'0#>@>#>).
              apply Equal_sym.
                apply denv_to_from_dmap; auto.
            apply disjoint_denv_cons_union.
              apply uniq_push; auto.
                apply dmap_to_denv_is_uniq.
          apply Equal_trans with (m':=(<#[(x, T)]++D#>--<#D'0#>)); auto.
            apply Equal_sym.
              eapply Equal_trans with (m':=(<#[(x,T)]#>|_|<#D#>)--<#D'0#>); auto.
                apply dmap_Equal_rewrite_diff_left with (M1:=<#[(x,T)]++D#>); auto.
                  apply disjoint_denv_cons_union.
                    apply uniq_push; auto.
                      apply uniq_from_wf_denv_lin in Wf_denv; auto.
                  apply Equal_refl.
              apply dmap_union_diff_distr.
            apply Equal_trans with (m':=<#D'#>--<#D'0#>); auto.
              apply denv_to_from_dmap; auto.
Qed.

Lemma atyping_lin_diff_strengthening : forall G D1 e T D2 D,
  atyping G D1 e T D2 ->
  (forall x, x `in` (fv_ee e) -> x `notin` (dom D)) ->
  exists D', atyping G <@<#D1#>--<#D#>@> e T D' /\ D' ~~~ <@<#D2#>--<#D#>@>.
Proof.
  intros G D1 e T D2 D Htyp Hinc.
  generalize dependent D.
  (atyping_cases (induction Htyp) Case); intros; subst.  
  Case "atyping_uvar".
    exists (<@<#D#>--<#D0#>@>).
    split.
      apply atyping_uvar; auto.
        apply wf_denv_lin_diff_strengthening; auto.  
      apply Equal_refl.
  Case "atyping_lvar".
    exists (<@<#D'#>--<#D0#>@>).
    split.
      apply atyping_lvar with (D:=<@<#D#>--<#D0#>@>); auto.
        eapply denv_to_dmap_iso.
          apply dmap_to_denv_is_uniq. 
          eapply find_mapsto_iff.
            assert (J := @denv_to_from_dmap (<#D#>--<#D0#>)).
            eapply (@Equal_mapsto_rewrite (<#D#>--<#D0#>) <#<@<#D#>--<#D0#>@>#>); auto.
            eapply diff_mapsto_iff.
            split.
              apply denv_to_dmap_iso in H.
                apply uniq_from_wf_denv_lin in H0; auto.
              eapply find_mapsto_iff; auto.

              apply notin_dom_implies_notIn.
                apply Hinc. simpl. fsetdec.
        apply wf_denv_lin_diff_strengthening; auto.
        apply dmap_to_denv_is_uniq.  
        apply dmap_diff_preserves_Equal with (M'':=<#D0#>) in H2.
        eapply Equal_trans with (m':=<#D'#>--<#D0#>).
          eapply Equal_trans with (m':=(<#D#>[-]x)--<#D0#>); auto.
            eapply Equal_trans with (m':=(<#D#>--<#D0#>)[-]x); auto.
              apply dmap_remove_preserves_Equal.
                apply Equal_sym.
                  apply denv_to_from_dmap.
              apply dmap_diff_remove_commut.
          apply denv_to_from_dmap.
      apply Equal_refl.
  Case "atyping_uabs".
    pick fresh z.
    assert (    
      exists D'0, 
        atyping ([(z, gbind_typ V)]++G) <@<#D#>--<#D0#>@> (open_ee e1 z) T1 D'0 /\ 
        D'0 ~~~ <@<#D'#>--<#D0#>@>
    ) as IH.
      apply H1; auto.
        intros y yine1.
        destruct (z == y); subst; auto.
          apply Hinc.
            simpl.
            apply in_open_ee_fv_ee in yine1; auto.
    clear H1. destruct IH as [D'0 [IH D'0eq]].
    exists D'0.
    split; auto.
      assert (z `notin` dom (<@ <#D#> -- <#D0#> @>)) as znotinD.
        apply notin_dom_diff; auto.
          assert (z `notin` L) as J. auto.
          apply H0 in J. apply atyping_regular in J.
          decompose [and] J. apply uniq_from_wf_denv_lin in H4; auto.
      apply atyping_uabs with (L:=L `union` dom D0 `union` dom (<@ <#D#> -- <#D0#> @>)
                                    `union` (fv_tt T1) `union` (fv_ee e1) `union` dom G `union` singleton z); auto.
        intros x Frx. 
        apply atyping_nonlin_term_renaming_head with (x:=z); auto.


        intro J.
        apply H2 in J.
        apply Equal_trans with (m':=<#D#>--<#D0#>).
          apply Equal_sym.
            apply denv_to_from_dmap.
          apply Equal_trans with (m':=<#D'#>--<#D0#>).
            apply dmap_diff_preserves_Equal; auto.
            apply Equal_trans with (m':=<#<@<#D'#>--<#D0#>@>#>).
              apply denv_to_from_dmap.
              apply Equal_sym; auto.
  Case "atyping_labs".
    pick fresh z.
    assert (    
      exists D'0, 
        atyping G <@<#[(z, V)]++D#>--<#D0#>@> (open_ee e1 z) T1 D'0 /\ 
        D'0 ~~~ <@<#D'#>--<#D0#>@>
    ) as IH.
      apply H1; auto.
        intros y yine1.
        destruct (z == y); subst; auto.
          apply Hinc.
            simpl.
            apply in_open_ee_fv_ee in yine1; auto.
    clear H1. destruct IH as [D'0 [IH D'0eq]].
    assert (z `notin` dom (<@ <#D#> -- <#D0#> @>)) as znotinD.
      apply notin_dom_diff; auto.
        assert (z `notin` L) as J. auto.
        apply H0 in J. apply atyping_regular in J.
        decompose [and] J. apply uniq_from_wf_denv_lin in H4; auto.
        inversion H4; subst; auto.
    assert (z `notin` dom (<@ <#D'#> -- <#D0#> @>)) as znotinD'.
      apply notin_dom_diff; auto.
        assert (z `notin` L) as J. auto.
        apply H0 in J. apply atyping_regular in J.
        decompose [and] J. apply uniq_from_wf_denv_lin in H3; auto.
    assert (<@<#[(z, V)]++D#>--<#D0#>@> ~~~ [(z, V)]++(<@<#D#>--<#D0#>@>)) as J.
      apply add_diff_commut; auto.
        assert (z `notin` L) as J. auto.
        apply H0 in J. apply atyping_regular in J.
        decompose [and] J. apply uniq_from_wf_denv_lin in H4.
        inversion H4; subst; auto.
    assert (uniq ([(z,V)]++<@<#D#>--<#D0#>@>)) as Uniq.
      apply uniq_push; auto.
        apply dmap_to_denv_is_uniq.
    apply atyping_permutation with (D1':=[(z, V)]++(<@<#D#>--<#D0#>@>)) in IH; auto.
    destruct IH as [B'0 [IH B'0eq]].
    exists B'0.
    split; auto.
      apply atyping_labs with (L:=L `union` dom D0 `union` dom (<@ <#D#> -- <#D0#> @>)
                                  `union` (fv_tt T1) `union` (fv_ee e1) `union` dom G `union` singleton z) 
                            (Q:=Q); auto.
        intros x Frx.
        apply atyping_lin_term_renaming_head_in with (x:=z); auto.
          apply denv_mono_aux with (x:=z) in IH.
            destruct IH as [[HH1 HH2]|[HH1 HH2]]; auto.
              apply denv_Equal_in_dom with (D2:=<@<#D'#>--<#D0#>@>) in HH2.
                contradict HH2; auto.
                apply Equal_trans with (m':=<#D'0#>); auto.
                  apply Equal_sym; auto.
            rewrite dom_app. simpl. clear Fr. fsetdec.
        intro JJ.
        apply H2 in JJ.
        apply Equal_trans with (m':=<#D#>--<#D0#>).
          apply Equal_sym.
            apply denv_to_from_dmap.
          apply Equal_trans with (m':=<#D'0#>); auto.
            apply Equal_trans with (m':=<#D'#>--<#D0#>).
              apply dmap_diff_preserves_Equal; auto.
              apply Equal_trans with (m':=<#<@<#D'#>--<#D0#>@>#>).
                apply denv_to_from_dmap.
                apply Equal_sym; auto.
      apply Equal_trans with (m':=<#D'0#>); auto.
        apply Equal_sym; auto.
  Case "atyping_app".
    assert (    
      exists D', 
        atyping G <@<#D1#>--<#D#>@> e1 (typ_arrow K T1 T2) D' /\ 
        D' ~~~ <@<#D2#>--<#D#>@>
    ) as IH1.
      apply IHHtyp1; auto.
        intros y yine1.
        apply Hinc. simpl. fsetdec.
    clear IHHtyp1. destruct IH1 as [D'2 [IH1 D'2eq]].
    assert (    
      exists D', 
        atyping G <@<#D2#>--<#D#>@> e2 T1 D' /\ 
        D' ~~~ <@<#D3#>--<#D#>@>
    ) as IH2.
      apply IHHtyp2; auto.
        intros y yine2.
        apply Hinc. simpl. fsetdec.
    clear IHHtyp2. destruct IH2 as [D'3 [IH2 D'3eq]].

    apply atyping_permutation with (D1':=D'2) in IH2; auto.
      destruct IH2 as [D''3 [IH2 D''3eq]].
      exists D''3. 
      split.
        eapply atyping_app; eauto.
        apply Equal_trans with (m':=<#D'3#>); auto.
          apply Equal_sym. auto.

      apply atyping_regular in IH1.
      decompose [and] IH1.
      apply uniq_from_wf_denv_lin in H0; auto.
      
      apply Equal_sym. auto.
  Case "atyping_tabs".
    pick fresh Z.
    assert (    
      exists D'0, 
        atyping ([(Z, gbind_kn K)]++G) <@<#D#>--<#D0#>@> (open_te e1 Z) (open_tt T1 Z) D'0 /\ 
        D'0 ~~~ <@<#D'#>--<#D0#>@>
    ) as IH.
      apply H1; auto.
        intros Y yine1.
        destruct (Z == Y); subst; auto.
          apply Hinc.
            simpl.
            apply in_open_te_fv_ee in yine1; auto.
    clear H1. destruct IH as [D'0 [IH D'0eq]].
    exists D'0.
    split; auto.
      assert (Z `notin` dom (<@ <#D#> -- <#D0#> @>)) as ZnotinD.
        apply notin_dom_diff; auto.
          assert (Z `notin` L) as J. auto.
          apply H0 in J. apply atyping_regular in J.
          decompose [and] J. apply uniq_from_wf_denv_lin in H3; auto.
      assert (Z `notin` denv_fv_tt (<@ <#D#> -- <#D0#> @>)) as ZnotinD'.
        apply notin_denv_fv_tt_diff; auto.
          assert (Z `notin` L) as J. auto.
          apply H0 in J. apply atyping_regular in J.
          decompose [and] J. apply uniq_from_wf_denv_lin in H3; auto.
      apply atyping_tabs with (L:=L `union` dom D0 `union` dom (<@ <#D#> -- <#D0#> @>)
                                    `union` (fv_tt T1) `union` (fv_te e1) 
                                    `union` dom G `union` singleton Z `union` denv_fv_tt (<@ <#D#> -- <#D0#> @>)); auto.
        intros X FrX. 
        apply atyping_nonlin_typ_renaming with (X:=Z); auto.
  Case "atyping_tapp".
    assert (    
      exists D'0, 
        atyping G <@<#D#>--<#D0#>@> e1 (typ_all K T2) D'0 /\ 
        D'0 ~~~ <@<#D'#>--<#D0#>@>
    ) as IH.
      apply IHHtyp; auto.
    clear IHHtyp. destruct IH as [D'0 [IH D'0eq]].
    exists D'0. 
    split; auto.
      eapply atyping_tapp; eauto.
Qed.

Lemma atyping_lin_union_weakening : forall G D1 e T D2 D,
  atyping G D1 e T D2 ->
  wf_denv G <@<#D1#>|_|<#D#>@> ->
  <#D1#> ** <#D#> ->
  uniq D ->
  exists D', atyping G <@<#D1#>|_|<#D#>@> e T D' /\ D' ~~~ <@<#D2#>|_|<#D#>@>.
Proof.
  intros G D1 e T D2 D Htyp Wf_denv Disj UniqD.
  generalize dependent D.
  (atyping_cases (induction Htyp) Case); intros; subst.  
  Case "atyping_uvar".
    exists (<@<#D#>|_|<#D0#>@>).
    split.
      apply atyping_uvar; auto.
      apply Equal_refl.
  Case "atyping_lvar".
    exists (<@<#D'#>|_|<#D0#>@>).
    apply denv_to_dmap_iso in H.
      apply uniq_from_wf_denv_lin in H0; auto.
    apply find_mapsto_iff in H.
    assert (~ EMap.In x <#D0#>) as J.
      apply dmap_Disjoint_in_notin with (x:=x) (T:=T) in Disj; auto.
    split.
      apply atyping_lvar; auto.
        eapply denv_to_dmap_iso.
          apply dmap_to_denv_is_uniq.
          eapply find_mapsto_iff.
            assert (JJ := @denv_to_from_dmap (<#D#>|_|<#D0#>)).
            eapply (@Equal_mapsto_rewrite (<#D#>|_|<#D0#>) <#<@<#D#>|_|<#D0#>@>#>); auto.
            eapply update_mapsto_iff.
            right. split; auto.
        apply dmap_to_denv_is_uniq.
        apply Equal_trans with (m':=<#D'#>|_|<#D0#>).
          apply Equal_sym.
            apply dmap_Equal_rewrite_remove_left with (M1:=<#D#>|_|<#D0#>).
              apply denv_to_from_dmap.
              apply Equal_trans with (m':=(<#D#>[-]x)|_|(<#D0#>[-]x)).
                apply dmap_Equal_rewrite_Union_right with (M2:=<#D0#>).
                  apply dmap_remove_refl; auto. 
                  apply dmap_Equal_rewrite_Union_left with (M1:=<#D'#>).
                    apply Equal_sym; auto.
                    apply Equal_refl.
                apply Equal_sym.
                  apply dmap_union_remove_distr.
          apply denv_to_from_dmap.
      apply Equal_refl.
  Case "atyping_uabs".
    pick fresh z.
    assert (    
      exists D'0, 
        atyping ([(z, gbind_typ V)]++G) <@<#D#>|_|<#D0#>@> (open_ee e1 z) T1 D'0 /\ 
        D'0 ~~~ <@<#D'#>|_|<#D0#>@>
    ) as IH.
      apply H1; auto.
        apply wf_denv_nonlin_weakening_head; auto.
          apply disjoint_one_2.
            apply notin_dom_union; auto.
          apply wf_genv_typ; auto.
            apply wf_genv_from_wf_denv in Wf_denv; auto.
    clear H1. destruct IH as [D'0 [IH D'0eq]].
    exists D'0.
    split; auto.
      assert (z `notin` dom (<@ <#D#> |_| <#D0#> @>)) as znotinD.
        apply notin_dom_union; auto.
      apply atyping_uabs with (L:=L `union` dom D0 `union` dom (<@ <#D#> |_| <#D0#> @>)
                                    `union` (fv_tt T1) `union` (fv_ee e1) `union` dom G `union` singleton z); auto.
        intros x Frx. 
        apply atyping_nonlin_term_renaming_head with (x:=z); auto.

        intro J.
        apply H2 in J.
        apply Equal_trans with (m':=<#D#>|_|<#D0#>).
          apply Equal_sym.
            apply denv_to_from_dmap.
          apply Equal_trans with (m':=<#D'#>|_|<#D0#>).
            apply dmap_Equal_rewrite_Union_left with (M1:=<#D#>); auto.
              apply Equal_refl.
            apply Equal_trans with (m':=<#<@<#D'#>|_|<#D0#>@>#>).
              apply denv_to_from_dmap.
              apply Equal_sym; auto.
  Case "atyping_labs".
    pick fresh z.
    assert (z `notin` dom (<@ <#D#> |_| <#D0#> @>)) as znotinD.
      apply notin_dom_union; auto.
    assert (z `notin` dom (<@ <#D'#> |_| <#D0#> @>)) as znotinD'.
      apply notin_dom_union; auto.
    assert (<@<#[(z, V)]++D#>|_|<#D0#>@> ~~~ [(z, V)]++(<@<#D#>|_|<#D0#>@>)) as J.
      apply add_union_commut; auto.
        assert (z `notin` L) as J. auto.
        apply H0 in J. apply atyping_regular in J.
        decompose [and] J. 
        apply wf_denv_lin_strengthening_head in H5.
        apply uniq_from_wf_denv_lin in H5; auto.
    assert (    
      exists D'0, 
        atyping G <@<#[(z, V)]++D#>|_|<#D0#>@> (open_ee e1 z) T1 D'0 /\ 
        D'0 ~~~ <@<#D'#>|_|<#D0#>@>
    ) as IH.
      apply H1; auto.
        apply denv_permutation with (D:=[(z, V)]++(<@<#D#>|_|<#D0#>@>)); auto.
          apply wf_denv_lin_weakening_head with (K:=Q); auto.
            apply dmap_to_denv_is_uniq.
            apply Equal_sym; auto.
        simpl.
        apply dmap_add_preserves_disjoint_left; auto.
          apply notin_dom_implies_notIn; auto.
    clear H1. destruct IH as [D'0 [IH D'0eq]].
    assert (uniq ([(z,V)]++<@<#D#>|_|<#D0#>@>)) as Uniq.
      apply uniq_push; auto.
        apply dmap_to_denv_is_uniq.
    apply atyping_permutation with (D1':=[(z, V)]++(<@<#D#>|_|<#D0#>@>)) in IH; auto.
    destruct IH as [B'0 [IH B'0eq]].
    exists B'0.
    split; auto.
      apply atyping_labs with (L:=L `union` dom D0 `union` dom (<@ <#D#> |_| <#D0#> @>)
                                  `union` (fv_tt T1) `union` (fv_ee e1) `union` dom G `union` singleton z) 
                            (Q:=Q); auto.
        intros x Frx.
        apply atyping_lin_term_renaming_head_in with (x:=z); auto.
          apply denv_mono_aux with (x:=z) in IH.
            destruct IH as [[HH1 HH2]|[HH1 HH2]]; auto.
              apply denv_Equal_in_dom with (D2:=<@<#D'#>|_|<#D0#>@>) in HH2.
                contradict HH2; auto.
                apply Equal_trans with (m':=<#D'0#>); auto.
                  apply Equal_sym; auto.
            rewrite dom_app. simpl. clear Fr. fsetdec.
        intro JJ.
        apply H2 in JJ.
        apply Equal_trans with (m':=<#D#>|_|<#D0#>).
          apply Equal_sym.
            apply denv_to_from_dmap.
          apply Equal_trans with (m':=<#D'0#>); auto.
            apply Equal_trans with (m':=<#D'#>|_|<#D0#>).
              apply dmap_union_preserves_Equal_right; auto.
              apply Equal_trans with (m':=<#<@<#D'#>|_|<#D0#>@>#>).
                apply denv_to_from_dmap.
                apply Equal_sym; auto.
      apply Equal_trans with (m':=<#D'0#>); auto.
        apply Equal_sym; auto.
  Case "atyping_app".
    assert (    
      exists D', 
        atyping G <@<#D1#>|_|<#D#>@> e1 (typ_arrow K T1 T2) D' /\ 
        D' ~~~ <@<#D2#>|_|<#D#>@>
    ) as IH1.
      apply IHHtyp1; auto.
    clear IHHtyp1. destruct IH1 as [D'2 [IH1 D'2eq]].
    assert (    
      exists D', 
        atyping G <@<#D2#>|_|<#D#>@> e2 T1 D' /\ 
        D' ~~~ <@<#D3#>|_|<#D#>@>
    ) as IH2.
      apply IHHtyp2; auto.
        apply wf_denv_lin_sub_strengthening with (D:=<@<#D1#>|_|<#D#>@>); auto.
          apply dmap_Equal_rewrite_Sub_left with (M1:=<#D2#>|_|<#D#>).
            apply denv_to_from_dmap.
            apply dmap_Equal_rewrite_Sub_right with (M2:=<#D1#>|_|<#D#>).
              apply denv_to_from_dmap.
              apply dmap_union_preserves_Sub_right.
                apply denv_mono in Htyp1; auto.
          apply dmap_to_denv_is_uniq.
        apply dmap_Sub_preserves_disjoint_left with (M1:=<#D1#>); auto.
          apply denv_mono in Htyp1; auto.
    clear IHHtyp2. destruct IH2 as [D'3 [IH2 D'3eq]].

    apply atyping_permutation with (D1':=D'2) in IH2; auto.
      destruct IH2 as [D''3 [IH2 D''3eq]].
      exists D''3. 
      split.
        eapply atyping_app; eauto.
        apply Equal_trans with (m':=<#D'3#>); auto.
          apply Equal_sym. auto.

      apply atyping_regular in IH1.
      decompose [and] IH1.
      apply uniq_from_wf_denv_lin in H0; auto.
      
      apply Equal_sym. auto.
  Case "atyping_tabs".
    pick fresh Z.
    assert (    
      exists D'0, 
        atyping ([(Z, gbind_kn K)]++G) <@<#D#>|_|<#D0#>@> (open_te e1 Z) (open_tt T1 Z) D'0 /\ 
        D'0 ~~~ <@<#D'#>|_|<#D0#>@>
    ) as IH.
      apply H1; auto.
        apply wf_denv_nonlin_weakening_head; auto.
          apply disjoint_one_2.
            apply notin_dom_union; auto.
          apply wf_genv_kn; auto.
            apply wf_genv_from_wf_denv in Wf_denv; auto.
    clear H1. destruct IH as [D'0 [IH D'0eq]].
    exists D'0.
    split; auto.
      assert (Z `notin` dom (<@ <#D#> |_| <#D0#> @>)) as ZnotinD.
        apply notin_dom_union; auto.
      assert (Z `notin` denv_fv_tt (<@ <#D#> |_| <#D0#> @>)) as ZnotinD'.
        assert (Z `notin` denv_fv_tt D /\ Z `notin` denv_fv_tt D0) as K'. auto.
        apply notin_denv_fv_tt_union in K'; auto.
          assert (Z `notin` L) as J. auto.
          apply H0 in J. apply atyping_regular in J.
          decompose [and] J. 
          apply uniq_from_wf_denv_lin in H3; auto.
      apply atyping_tabs with (L:=L `union` dom D0 `union` dom (<@ <#D#> |_| <#D0#> @>)
                                    `union` (fv_tt T1) `union` (fv_te e1) 
                                    `union` dom G `union` singleton Z `union` denv_fv_tt (<@ <#D#> |_| <#D0#> @>)); auto.
        intros X FrX. 
        apply atyping_nonlin_typ_renaming with (X:=Z); auto.
  Case "atyping_tapp".
    assert (    
      exists D'0, 
        atyping G <@<#D#>|_|<#D0#>@> e1 (typ_all K T2) D'0 /\ 
        D'0 ~~~ <@<#D'#>|_|<#D0#>@>
    ) as IH.
      apply IHHtyp; auto.
    clear IHHtyp. destruct IH as [D'0 [IH D'0eq]].
    exists D'0. 
    split; auto.
      eapply atyping_tapp; eauto.
Qed.

Lemma atyping_through_nonlin_subst_ee : forall S x T e e' G1 G2 D1 D2 D3 D3',
  atyping (G2 ++ [(x, gbind_typ S)] ++ G1) D1 e T D2 ->
  atyping G1 D3 e' S D3' ->
  D3 ~~~ D3' ->
  (<#D1#> -- <#D2#>) ** <#D3#> ->
  wf_denv (G2 ++ G1) <@ (<#D1#> -- <#D2#>) |_| <#D3#> @> ->
  (x `in` fv_ee(e) -> 
     exists B3',
       atyping (G2 ++ G1) <@ (<#D1#> -- <#D2#>) |_| <#D3#> @> (subst_ee x e' e) T B3' /\
       B3' ~~~ D3')
    /\
  (x `notin` fv_ee(e) -> 
     exists B2,
       atyping (G2 ++ G1) D1 (subst_ee x e' e) T B2 /\
       B2 ~~~ D2).
Proof.
  intros S x T e e' G1 G2 D1 D2 D3 D3' Htyp Htyp' D3eqD3' Disj Wf_denv.
  assert (uniq D3) as UniqD3.
    apply atyping_regular in Htyp'.
    decompose [and] Htyp'.
    apply uniq_from_wf_denv_lin in H1; auto.
  remember (G2 ++ [(x, gbind_typ S)] ++ G1) as G.
  generalize dependent G2.
  generalize dependent G1.
  generalize dependent S.
  generalize dependent x.
  generalize dependent D3.
  generalize dependent D3'.
  generalize dependent e'.
  (atyping_cases (induction Htyp) Case); intros; subst.  
  Case "atyping_uvar".
    assert (uniq (G2 ++ [(x0, gbind_typ S)] ++ G1)) as Uniq.
      apply uniq_from_wf_denv_nonlin in H0; auto.
    rename H into Binds.
    rename H0 into Wf_denv'.
    analyze_binds_uniq Binds.
    SCase "x in G2, x<>x0, x notin G1".
      split; intro J; simpl in J.
        contradict J; auto.
        exists D.
        split.
          rewrite <- subst_ee_fresh; auto.
          apply atyping_uvar; auto.
            apply wf_denv_nonlin_term_strengthening in Wf_denv'; auto.
          apply Equal_refl.
    SCase "x notin G2, x=x0, x notin G1".
      inversion BindsTacVal; subst.
      split; intro J; simpl in J.
        (*x0 in x0*)
        assert (uniq <@(<#D#>--<#D#>) |_| <#D3#>@>) as Uniq'.
          apply uniq_from_wf_denv_lin in Wf_denv; auto.        
        assert (D3 ~~~ <@(<#D#>--<#D#>) |_| <#D3#>@>) as EQ.
          apply Equal_trans with (m':=(<#D#>--<#D#>) |_| <#D3#>).
            apply dmap_Equal_rewrite_Union_left with (M1:=@@).
              apply Equal_sym.
                apply dmap_diff_refl.
              apply Equal_sym.
                apply dmap_union_empty_refl.                 
            apply denv_to_from_dmap; auto.
        assert (wf_denv (G2++G1) D3) as Wf_denv''.
          apply denv_permutation with (D:=<@ (<#D#>--<#D#>) |_| <#D3#> @>); auto.
            apply uniq_from_wf_denv_lin in Wf_denv'; auto.
            apply Equal_sym; auto.
        rewrite_env (nil++G1) in Htyp'.
        apply atyping_nonlin_weakening with (G:=G2) in Htyp'; simpl_env; auto.
        apply atyping_permutation with (D1':=<@(<#D#>--<#D#>) |_| <#D3#>@>) in Htyp'; auto.
        destruct Htyp' as [D2' [Htyp' D3'eqD2']].
        exists D2'.
        split.
          simpl. simpl_env in Htyp'. 
          destruct (x0==x0); subst; auto.
            contradict n; auto.
          apply Equal_sym; auto.            
        (*x0 notin x0*)
        contradict J; try solve [auto | fsetdec].
    SCase "x notin G1, x<>x0, x in G2".
      split; intro J; simpl in J.
        contradict J; auto.
        exists D.
        split.
          rewrite <- subst_ee_fresh; auto.
          apply atyping_uvar; auto.
            apply wf_denv_nonlin_term_strengthening in Wf_denv'; auto.
          apply Equal_refl.
  Case "atyping_lvar".
    assert (x `notin` dom (G2++[(x0,gbind_typ S)]++G1)) as XnotinG.
      apply denv_dom_dinv with (x:=x) in H0; auto.
        apply binds_In in H; auto.
    rewrite dom_app in XnotinG. rewrite dom_app in XnotinG. 
    simpl in XnotinG. 
    split; intro J; simpl in J.
      contradict J; auto.
      exists D'.
      split.
        rewrite <- subst_ee_fresh; auto.
        apply atyping_lvar; auto.
          apply wf_denv_nonlin_term_strengthening in H0; auto.
        apply Equal_refl.
  Case "atyping_uabs".
    assert (wf_atyp (G2++G1) V kn_nonlin) as Wf_atyp.
      apply wf_atyp_strengthening in H; auto.
    pick fresh y.
    assert (y `notin` dom <@(<#D#>--<#D'#>) |_| <#D3#>@>) as YnotinD.
      apply notIn_implies_notin_dom.
        intro J.
        apply update_in_iff in J.
        destruct J as [J | J].
          apply diff_in_iff in J.
          destruct J as [J1 J2].
          apply In_implies_in_dom in J1.
          contradict J1; auto.

          apply In_implies_in_dom in J.
          contradict J; auto.
    assert (y `notin` fv_ee (subst_ee x e' e1)) as HynotinSubst.
      apply notin_fv_ee_subst_ee; auto.
      auto.
    assert (wf_denv ([(y, gbind_typ V)]++G2++G1) <@(<#D#>--<#D'#>) |_| <#D3#>@>) as Wf_denv'.
      rewrite_env (nil++[(y, gbind_typ V)]++(G2++G1)).
      apply wf_denv_nonlin_weakening; auto.
        simpl_env.
        apply wf_genv_typ; auto.
          apply wf_genv_from_wf_denv in Wf_denv; auto.
    assert (
    (x `in` fv_ee(open_ee e1 y) -> 
       exists B3',
         atyping (([(y, gbind_typ V)]++G2) ++ G1) <@ (<#D#> -- <#D'#>) |_| <#D3#> @> (subst_ee x e' (open_ee e1 y)) T1 B3' /\
         B3' ~~~ D3')
      /\
    (x `notin` fv_ee(open_ee e1 y) -> 
       exists B',
         atyping (([(y, gbind_typ V)]++G2) ++ G1) D (subst_ee x e' (open_ee e1 y)) T1 B' /\
         B' ~~~ D')
    ) as IH.
     apply H1 with (S0:=S); auto.
    clear H1.
    destruct IH as [IHin IHnotin].
    split; intro J; simpl in J.
      (* x `in` \y. e1 *)
      apply in_fv_ee_open_ee with (y:=y) in J; auto.
      apply IHin in J.
      destruct J as [B3' [Htyp'' B3'eqD3']].
      exists B3'. simpl.       
      split; auto.
        apply atyping_uabs with (L:=L `union` (fv_tt T1) `union` fv_ee (subst_ee x e' e1) `union` dom(G2++G1) `union` dom <@(<#D#>--<#D'#>) |_| <#D3#>@> `union` singleton y); auto.
          intros x0 Frx0.
          apply atyping_nonlin_term_renaming_head with (x:=y); auto.
            rewrite subst_ee_open_ee_var; auto.

            intro Keq. 
            apply H2 in Keq.
            apply Equal_trans with (m':=<#D3#>); auto.
              apply Equal_trans with (m':=(<#D#>--<#D'#>) |_| <#D3#>).
                apply Equal_sym.
                  apply denv_to_from_dmap; auto.
                    apply uniq_from_wf_denv_lin in Wf_denv'; auto.
                apply Equal_sym.
                  apply dmap_Equal_rewrite_Union_left with (M1:=@@).
                    apply dmap_Equal_diff_refl; auto.
                      apply Equal_sym.
                        apply dmap_union_empty_refl.                 
              apply Equal_trans with (m':= <#D3'#>); auto.
                apply Equal_sym; auto.
      (* x `notin` \y. e1 *)
      apply notin_fv_ee_open_ee with (y:=y) in J; auto.
      apply IHnotin in J.
      destruct J as [B' [Htyp'' B'eqD']].
      exists B'. simpl.       
      split; auto.
        apply atyping_uabs with (L:=L `union` (fv_tt T1) `union` fv_ee (subst_ee x e' e1) `union` dom(G2++G1) `union` dom D `union` singleton y); auto.
          intros x0 Frx0.
          apply atyping_nonlin_term_renaming_head with (x:=y); auto.
            rewrite subst_ee_open_ee_var; auto.

            intro Keq. 
            apply H2 in Keq.
            apply Equal_trans with (m':= <#D'#>); auto.
              apply Equal_sym; auto.
  Case "atyping_labs".
    assert (wf_atyp (G2++G1) V Q) as Wf_atyp.
      apply wf_atyp_strengthening in H; auto.
    pick fresh y.
    assert (y `notin` dom <@(<#D#>--<#D'#>) |_| <#D3#>@>) as YnotinD.
      apply notIn_implies_notin_dom.
        intro J.
        apply update_in_iff in J.
        destruct J as [J | J].
          apply diff_in_iff in J.
          destruct J as [J1 J2].
          apply In_implies_in_dom in J1.
          contradict J1; auto.

          apply In_implies_in_dom in J.
          contradict J; auto.
    assert (uniq <@(<#[(y, V)]++D#>--<#D'#>) |_| <#D3#>@>) as UniqDD.
      apply dmap_to_denv_is_uniq.
    assert (<@(<#[(y, V)]++D#>--<#D'#>) |_| <#D3#>@> ~~~ 
            ([(y, V)]++<@(<#D#>--<#D'#>) |_| <#D3#>@>)
    ) as DDeq.
      apply Equal_trans with (m':=(<#[(y, V)]++D#>--<#D'#>) |_| <#D3#>).
        apply Equal_sym.
          apply denv_to_from_dmap.
        apply Equal_sym.
          apply dmap_Equal_rewrite_Union_left with (M1:=<#<@<#[(y, V)]++D#>--<#D'#>@>#>).
            apply Equal_sym.
              apply denv_to_from_dmap.
            apply dmap_Equal_rewrite_Union_left with (M1:=<#[(y, V)]++(<@<#D#>--<#D'#>@>)#>).
              apply Equal_sym.
                apply add_diff_commut; auto.
                  assert (y `notin` L) as Fry. auto.
                  apply H0 in Fry.
                  apply atyping_regular in Fry.
                  decompose [and] Fry.
                  apply uniq_from_wf_denv_lin in H5.
                  inversion H5; subst; auto.
              apply dmap_Equal_rewrite_Union_left with (M1:=<#[(y, V)]#>|_|<#(<@<#D#>--<#D'#>@>)#>).
                apply Equal_sym.
                  apply disjoint_denv_cons_union.
                    apply uniq_push.
                      apply dmap_to_denv_is_uniq. 
                        apply notin_dom_diff; auto.
                          assert (y `notin` L) as Fry. auto.
                          apply H0 in Fry.
                          apply atyping_regular in Fry.
                          decompose [and] Fry.
                          apply uniq_from_wf_denv_lin in H5.
                          inversion H5; subst; auto.
                apply Equal_trans with (m':=<#[(y, V)]#>|_|<#(<@<#D#>--<#D'#>|_|<#D3#>@>)#>).
                  apply disjoint_denv_cons_union.
                    apply uniq_push; auto.
                      apply dmap_to_denv_is_uniq. 
                  apply Equal_sym.                   
                    apply dmap_Equal_rewrite_Union_right with (M2:=(<#D#>--<#D'#>)|_|<#D3#>).
                      apply denv_to_from_dmap.
                      apply Equal_sym.                   
                        apply dmap_Equal_rewrite_Union_left with (M1:=<#[(y,V)]#>|_|(<#D#>--<#D'#>)).
                          apply dmap_Equal_rewrite_Union_right with (M2:=(<#D#>--<#D'#>)).
                            apply denv_to_from_dmap.
                            apply Equal_refl.
                          apply Equal_sym.
                            apply dmap_union_assoc.
    assert (y `notin` fv_ee (subst_ee x e' e1)) as HynotinSubst.
      apply notin_fv_ee_subst_ee; auto.
      auto.
    assert (
    (x `in` fv_ee(open_ee e1 y) -> 
       exists B3',
         atyping (G2 ++ G1) <@ (<#[(y, V)]++D#> -- <#D'#>) |_| <#D3#> @> (subst_ee x e' (open_ee e1 y)) T1 B3' /\
         B3' ~~~ D3')
      /\
    (x `notin` fv_ee(open_ee e1 y) -> 
       exists B',
         atyping (G2 ++ G1) ([(y, V)]++D) (subst_ee x e' (open_ee e1 y)) T1 B' /\
         B' ~~~ D')
    ) as IH.
     apply H1 with (S0:=S); auto.
       apply dmap_add_preserves_disjoint_left with (x:=y) (T:=V) in Disj; auto.
         simpl. apply dmap_Equal_preserves_disjoint_left with (M1:=y:::V[+](<#D#>--<#D'#>)); auto.
           apply Equal_sym.
             apply dmap_diff_distr; auto.
               apply notin_dom_implies_notIn; auto.
         apply notin_dom_implies_notIn; auto.
       apply wf_denv_typ with (x:=y) (T:=V) (D:=<@(<#D#>--<#D'#>) |_| <#D3#>@>) (K:=Q); auto.
         apply Equal_sym; auto.
    clear H1.
    destruct IH as [IHin IHnotin].
    split; intro J; simpl in J.
      (* x `in` \y. e1 *)
      apply in_fv_ee_open_ee with (y:=y) in J; auto.
      apply IHin in J.
      destruct J as [B3' [Htyp'' B3'eqD3']].
      assert (uniq ([(y, V)]++<@(<#D#>--<#D'#>) |_| <#D3#>@>)) as UniqDD'.
        apply uniq_push; auto.
          apply uniq_from_wf_denv_lin in Wf_denv; auto.
      apply atyping_permutation with (D1':=[(y, V)]++<@(<#D#>--<#D'#>) |_| <#D3#>@>) in Htyp''; auto.
      destruct Htyp'' as [B3'' [Htyp'' B3'eqB3'']].
      assert (y `notin` dom B3'') as YnotinB3''.
        apply notIn_implies_notin_dom2.
        intro J.
        apply in_find_iff in J.
        rewrite <- B3'eqB3'' in J.
        rewrite B3'eqD3' in J.
        apply in_find_iff in J.
        apply In_implies_in_dom in J.
        contradict J; auto.
      exists B3''. simpl.       
      split.
        apply atyping_labs with (L:=L `union` (fv_tt T1) `union` fv_ee (subst_ee x e' e1) `union` dom(G2++G1) `union` dom <@(<#D#>--<#D'#>) |_| <#D3#>@> `union` singleton y `union` dom B3') (Q:=Q); auto.
          intros x0 Frx0.
          rewrite <- subst_ee_open_ee_var in Htyp''; auto.
          apply atyping_lin_term_renaming_head_in with (x:=y); auto.
            assert (
              (y `in` fv_ee (open_ee (subst_ee x e' e1) y) /\ y `notin` dom B3'')    
                 \/    
              (y `notin` fv_ee (open_ee (subst_ee x e' e1) y) /\ y `in` dom B3'')
            ) as Mono.
              apply denv_mono_aux with (x:=y) in Htyp''.
                destruct Htyp'' as [[HH1 HH2]|[HH1 HH2]].
                  left. split; auto.
                  contradict HH2; auto.
              rewrite dom_app. simpl. clear Frx0. clear Fr.
                fsetdec.
            destruct Mono as [[HH1 HH2]|[HH1 HH2]]; auto.
              contradict HH2; auto.

          intro Keq. 
          apply H2 in Keq.
          apply Equal_trans with (m':=<#D3#>); auto.
              apply Equal_trans with (m':=(<#D#>--<#D'#>) |_| <#D3#>).
                apply Equal_sym.
                  apply denv_to_from_dmap; auto.
                    apply uniq_from_wf_denv_lin in Wf_denv; auto.
                apply Equal_sym.
                  apply dmap_Equal_rewrite_Union_left with (M1:=@@).
                    apply dmap_Equal_diff_refl; auto.
                      apply Equal_sym.
                        apply dmap_union_empty_refl.                 
              apply Equal_trans with (m':= <#B3'#>); auto.
                apply Equal_trans with (m':= <#D3'#>); auto.
                  apply Equal_sym; auto.
                apply Equal_trans with (m':= <#B3'#>); auto.
                  apply Equal_sym; auto.
      (* x `notin` \y. e1 *)
      apply notin_fv_ee_open_ee with (y:=y) in J; auto.
      apply IHnotin in J.
      destruct J as [B' [Htyp'' B'eqD']].
      assert (y `notin` dom B') as YnotinB'.
        apply notIn_implies_notin_dom2.
        intro J.
        apply in_find_iff in J.
        rewrite B'eqD' in J.
        apply in_find_iff in J.
        apply In_implies_in_dom in J.
        contradict J; auto.
      exists B'. simpl.       
      split; auto.
        apply atyping_labs with (L:=L `union` (fv_tt T1) `union` fv_ee (subst_ee x e' e1) `union` dom(G2++G1) `union` dom D `union` singleton y) (Q:=Q); auto.
          intros x0 Frx0.
          rewrite <- subst_ee_open_ee_var in Htyp''; auto.
          apply atyping_lin_term_renaming_head_in with (x:=y); auto.
            assert (
              (y `in` fv_ee (open_ee (subst_ee x e' e1) y) /\ y `notin` dom B')    
                 \/    
              (y `notin` fv_ee (open_ee (subst_ee x e' e1) y) /\ y `in` dom B')
            ) as Mono.
              apply denv_mono_aux with (x:=y) in Htyp''.
                destruct Htyp'' as [[HH1 HH2]|[HH1 HH2]].
                  left. split; auto.
                  contradict HH2; auto.
              rewrite dom_app. simpl. clear Frx0. clear Fr.
                fsetdec.
            destruct Mono as [[HH1 HH2]|[HH1 HH2]]; auto.
              contradict HH2; auto.

          intro Keq. 
          apply H2 in Keq.
          apply Equal_trans with (m':= <#D'#>); auto.
            apply Equal_sym; auto.
  Case "atyping_app".
    (* we first show some facts of ctx mono *)
    assert (<#D2#> <<= <#D1#>) as D2inD1.
      apply denv_mono in Htyp1; auto.
    assert (<#D3#> <<= <#D2#>) as D3inD2.
      apply denv_mono in Htyp2; auto.
    assert (((<#D1#>--<#D2#>)|_|<#D0#>) <<= ((<#D1#>--<#D3#>)|_|<#D0#>)) as Dsub.
      apply dmap_Sub_rewrite_Union_left.
        apply dmap_Sub_diff_right; auto.
    assert (wf_denv (G2++G1) <@(<#D1#>--<#D2#>)|_|<#D0#>@>) as Wf_denv'.
      apply wf_denv_lin_sub_strengthening with (D:=<@(<#D1#>--<#D3#>)|_|<#D0#>@>); auto.
        apply dmap_Equal_rewrite_Sub_left with (M1:=(<#D1#>--<#D2#>)|_|<#D0#>); auto.
          apply denv_to_from_dmap.
        apply dmap_Equal_rewrite_Sub_right with (M2:=(<#D1#>--<#D3#>)|_|<#D0#>); auto.
          apply denv_to_from_dmap; auto.
            apply uniq_from_wf_denv_lin in Wf_denv; auto.
        apply dmap_to_denv_is_uniq.
    assert (
    (x `in` fv_ee e1 -> 
       exists B3',
         atyping (G2 ++ G1) <@ (<#D1#> -- <#D2#>) |_| <#D0#> @> (subst_ee x e' e1) (typ_arrow K T1 T2) B3' /\
         B3' ~~~ D3')
      /\
    (x `notin` fv_ee e1 -> 
       exists B2,
         atyping (G2 ++ G1) D1 (subst_ee x e' e1) (typ_arrow K T1 T2) B2 /\
         B2 ~~~ D2)
    ) as IH1.
     apply IHHtyp1 with (S0:=S); auto.
       apply dmap_Sub_preserves_disjoint_left with (M1:=<#D1#>--<#D3#>); auto.
         apply dmap_Sub_diff_right; auto.
    clear IHHtyp1.
    destruct IH1 as [IHHtyp1in IHHtyp1notin].
    assert (((<#D2#>--<#D3#>)|_|<#D0#>) <<= ((<#D1#>--<#D3#>)|_|<#D0#>)) as Dsub'.
      apply dmap_Sub_rewrite_Union_left.
        apply dmap_Sub_diff_left; auto.
    assert (wf_denv (G2++G1) <@(<#D2#>--<#D3#>)|_|<#D0#>@>) as Wf_denv''.
      apply wf_denv_lin_sub_strengthening with (D:=<@(<#D1#>--<#D3#>)|_|<#D0#>@>); auto.
        apply dmap_Equal_rewrite_Sub_left with (M1:=(<#D2#>--<#D3#>)|_|<#D0#>); auto.
          apply denv_to_from_dmap.
        apply dmap_Equal_rewrite_Sub_right with (M2:=(<#D1#>--<#D3#>)|_|<#D0#>); auto.
          apply denv_to_from_dmap; auto.
            apply uniq_from_wf_denv_lin in Wf_denv; auto.
        apply dmap_to_denv_is_uniq.
    assert (
    (x `in` fv_ee e2 -> 
       exists B3',
         atyping (G2 ++ G1) <@ (<#D2#> -- <#D3#>) |_| <#D0#> @> (subst_ee x e' e2) T1 B3' /\
         B3' ~~~ D3')
      /\
    (x `notin` fv_ee e2 -> 
       exists B3,
         atyping (G2 ++ G1) D2 (subst_ee x e' e2) T1 B3 /\
         B3 ~~~ D3)
    ) as IH2.
     apply IHHtyp2 with (S0:=S); auto.
       apply dmap_Sub_preserves_disjoint_left with (M1:=<#D1#>--<#D3#>); auto.
         apply dmap_Sub_diff_left; auto.
    clear IHHtyp2.
    destruct IH2 as [IHHtyp2in IHHtyp2notin].
    split; intro J.
    SCase "x in e1e2".
      destruct (@in_dec x (fv_ee e1)) as [Hxine1 | Hxnotine1].
      SSCase "x in e1".
        destruct (@in_dec x (fv_ee e2)) as [Hxine2 | Hxnotine2].
        SSSCase "x in e2".
          apply IHHtyp1in in Hxine1. clear IHHtyp1in IHHtyp1notin.
          apply IHHtyp2in in Hxine2. clear IHHtyp2in IHHtyp2notin.
          destruct Hxine1 as [B3' [Hxine1 B3'eqD3']].
          destruct Hxine2 as [B3'' [Hxine2 B3''eqD3']].
          (* IH1 strengthening *)
          assert (forall x0, x0 `in` fv_ee (subst_ee x e' e1) -> x0 `notin` dom B3') as Diff1.
            intros x0 Hx0insubst1.
            apply denv_mono_disjoint with (x:=x0) in Hxine1; auto.
          apply atyping_lin_diff_strengthening with (D:=B3') in Hxine1; auto.
          assert (uniq <@<#D1#>--<#D2#>@>) as Uniq1.
            apply dmap_to_denv_is_uniq.
          assert (<@<#<@(<#D1#>--<#D2#>)|_|<#D0#>@>#>--<#B3'#>@> ~~~ <@<#D1#>--<#D2#>@>) as EQ1.
            apply Equal_trans with (m':=<#D1#>--<#D2#>).
              apply Equal_trans with (m':=<#<@(<#D1#>--<#D2#>)|_|<#D0#>@>#>--<#B3'#>).
                apply Equal_sym.
                  apply denv_to_from_dmap.
                apply Equal_sym.
                  apply dmap_Equal_rewrite_diff_left with (M1:=(<#D1#>--<#D2#>)|_|<#D0#>).
                    apply denv_to_from_dmap.
                    apply Equal_trans with (m':=((<#D1#>--<#D2#>)--<#B3'#>) |_| (<#D0#>--<#B3'#>)).
                      apply dmap_Equal_rewrite_Union_left with (M1:=<#D1#>--<#D2#>).
                        apply Equal_sym.
                          apply disjoint_diff_refl.
                            apply dmap_Equal_preserves_disjoint_right with (M2:=<#D0#>).
                              apply dmap_Sub_preserves_disjoint_left with (M1:=<#D1#>--<#D3#>); auto.
                                apply dmap_Sub_diff_right; auto.
                              eapply Equal_trans with (m':=<#D3'#>); auto.
                                apply Equal_sym; auto.
                        apply dmap_Equal_rewrite_Union_right with (M2:=@@).
                          apply dmap_Equal_diff_refl.
                            eapply Equal_trans with (m':=<#D3'#>); auto.
                              apply Equal_sym; auto.
                          apply Equal_trans with (m':=@@ |_| (<#D1#>--<#D2#>)); auto.
                            apply Equal_sym.
                              apply dmap_union_empty_refl; auto.
                            apply dmap_union_sym.
                              apply empty_disjoint.
                    apply Equal_sym.
                        apply dmap_union_diff_distr; auto.
              apply denv_to_from_dmap.
          destruct Hxine1 as [D2' [Hxine1 EmptyeqD2']].
          apply atyping_permutation with (D1':=<@<#D1#>--<#D2#>@>) in Hxine1; auto.
          destruct Hxine1 as [C2' [Hxine1 C2'eqD2']].
          clear Diff1 EQ1.
          
          (* IH2 strengthening *)
          assert (forall x0, x0 `in` fv_ee (subst_ee x e' e2) -> x0 `notin` dom B3'') as Diff2.
            intros x0 Hx0insubst2.
            apply denv_mono_disjoint with (x:=x0) in Hxine2; auto.
          apply atyping_lin_diff_strengthening with (D:=B3'') in Hxine2; auto.
          assert (uniq <@<#D2#>--<#D3#>@>) as Uniq2.
            apply dmap_to_denv_is_uniq.
          assert (<@<#<@(<#D2#>--<#D3#>)|_|<#D0#>@>#>--<#B3''#>@> ~~~ <@<#D2#>--<#D3#>@>) as EQ2.
            apply Equal_trans with (m':=<#D2#>--<#D3#>).
              apply Equal_trans with (m':=<#<@(<#D2#>--<#D3#>)|_|<#D0#>@>#>--<#B3''#>).
                apply Equal_sym.
                  apply denv_to_from_dmap.
                apply Equal_sym.
                  apply dmap_Equal_rewrite_diff_left with (M1:=(<#D2#>--<#D3#>)|_|<#D0#>).
                    apply denv_to_from_dmap.
                    apply Equal_trans with (m':=((<#D2#>--<#D3#>)--<#B3''#>) |_| (<#D0#>--<#B3''#>)).
                      apply dmap_Equal_rewrite_Union_left with (M1:=<#D2#>--<#D3#>).
                        apply Equal_sym.
                          apply disjoint_diff_refl.
                            apply dmap_Equal_preserves_disjoint_right with (M2:=<#D0#>).
                              apply dmap_Sub_preserves_disjoint_left with (M1:=<#D1#>--<#D3#>); auto.
                                apply dmap_Sub_diff_left; auto.
                              eapply Equal_trans with (m':=<#D3'#>); auto.
                                apply Equal_sym; auto.
                        apply dmap_Equal_rewrite_Union_right with (M2:=@@).
                          apply dmap_Equal_diff_refl.
                            eapply Equal_trans with (m':=<#D3'#>); auto.
                              apply Equal_sym; auto.
                          apply Equal_trans with (m':=@@ |_| (<#D2#>--<#D3#>)); auto.
                            apply Equal_sym.
                              apply dmap_union_empty_refl; auto.
                            apply dmap_union_sym.
                              apply empty_disjoint.
                    apply Equal_sym.
                        apply dmap_union_diff_distr; auto.
              apply denv_to_from_dmap.
          destruct Hxine2 as [D3'' [Hxine2 EmptyeqD3'']].
          apply atyping_permutation with (D1':=<@<#D2#>--<#D3#>@>) in Hxine2; auto.
          destruct Hxine2 as [C3'' [Hxine2 C3''eqD3'']].
          clear Diff2 EQ2.

          (* IH1 weakening *)
          assert (<@(<#<@<#D1#>--<#D2#>@>#>|_|<#D2#>)@> ~~~ D1) as EQ1'.
            apply Equal_trans with (m':=<#<@<#D1#>--<#D2#>@>#>|_|<#D2#>).
              apply Equal_sym.
                apply denv_to_from_dmap.
              apply Equal_sym.
                apply dmap_Equal_rewrite_Union_left with (M1:=<#D1#>--<#D2#>).
                  apply denv_to_from_dmap.
                  apply Equal_sym.
                    apply dmap_diff_union_refl; auto.
          assert (wf_denv (G2++G1) <@(<#<@<#D1#>--<#D2#>@>#>|_|<#D2#>)@>) as Wf_denv_union1.
            apply denv_permutation with (D:=D1).
              apply atyping_regular in Htyp1.
                decompose [and] Htyp1.
                apply wf_denv_nonlin_term_strengthening in H1; auto.
              apply dmap_to_denv_is_uniq.
              apply Equal_sym; auto.
          assert (<#<@<#D1#>--<#D2#>@>#> ** <#D2#>) as Disj1.
            apply dmap_Equal_preserves_disjoint_left with (M1:=<#D1#>--<#D2#>).
              apply diff_disjoint.
              apply Equal_sym.
                apply denv_to_from_dmap.
          assert (uniq D2) as Uniq2'.
            apply atyping_regular in Htyp1.
            decompose [and] Htyp1.
            apply uniq_from_wf_denv_lin in H0; auto.
          apply atyping_lin_union_weakening with (D:=D2) in Hxine1; auto.
          destruct Hxine1 as [E2'' [Hxine1 EqE2'']].
          assert (uniq D1) as Uniq1'.
            apply atyping_regular in Htyp1.
            decompose [and] Htyp1.
            apply uniq_from_wf_denv_lin in H1; auto.
          apply atyping_permutation with (D1':=D1) in Hxine1; auto.
          destruct Hxine1 as [D2'' [Hxine1 EqD2'']].
          clear EQ1' Uniq2'.

          (* IH2 weakening *)
          assert (<@(<#<@<#D2#>--<#D3#>@>#>|_|<#D3#>)@> ~~~ D2'') as EQ2'.
            apply Equal_trans with (m':=<#<@<#D2#>--<#D3#>@>#>|_|<#D3#>).
              apply Equal_sym.
                apply denv_to_from_dmap.
              apply Equal_sym.
                apply dmap_Equal_rewrite_Union_left with (M1:=<#D2#>--<#D3#>).
                  apply denv_to_from_dmap.
                  apply Equal_sym.
                    apply Equal_trans with (m':=<#D2#>).
                      apply dmap_diff_union_refl; auto.
                      apply Equal_trans with (m':=<#E2''#>); auto.
                        apply Equal_trans with (m':=<#<@<#C2'#>|_|<#D2#>@>#>); auto.                        
                          apply Equal_trans with (m':=<#C2'#>|_|<#D2#>); auto.
                            apply dmap_Equal_rewrite_Union_left with (M1:=@@). 
                              apply Equal_trans with (m':=<#D2'#>); auto.
                                apply Equal_trans with (m':=<#<@<#B3'#>--<#B3'#>@>#>); auto.
                                  apply Equal_trans with (m':=<#B3'#>--<#B3'#>); auto.
                                    apply dmap_Equal_diff_refl.
                                    apply Equal_refl.
                                  apply denv_to_from_dmap.  
                                apply Equal_sym; auto.
                              apply Equal_sym.
                                apply dmap_union_empty_refl.
                            apply denv_to_from_dmap.
                          apply Equal_sym; auto.
          assert (wf_denv (G2++G1) <@(<#<@<#D2#>--<#D3#>@>#>|_|<#D3#>)@>) as Wf_denv_union2.
            apply denv_permutation with (D:=D2'').
              apply atyping_regular in Hxine1.
                decompose [and] Hxine1. auto.
              apply dmap_to_denv_is_uniq.
              apply Equal_sym; auto.
          assert (<#<@<#D2#>--<#D3#>@>#> ** <#D3#>) as Disj2.
            apply dmap_Equal_preserves_disjoint_left with (M1:=<#D2#>--<#D3#>).
              apply diff_disjoint.
              apply Equal_sym.
                apply denv_to_from_dmap.
          assert (uniq D3) as Uniq3'.
            apply atyping_regular in Htyp2.
            decompose [and] Htyp2.
            apply uniq_from_wf_denv_lin in H0; auto.
          apply atyping_lin_union_weakening with (D:=D3) in Hxine2; auto.
          destruct Hxine2 as [E3''' [Hxine2 EqE3''']].
          assert (uniq D2'') as Uniq2'.
            apply atyping_regular in Hxine1.
            decompose [and] Hxine1.
            apply uniq_from_wf_denv_lin in H0; auto.
          apply atyping_permutation with (D1':=D2'') in Hxine2; auto.
          destruct Hxine2 as [D3''' [Hxine2 EqD3''']].
          clear EQ2' Uniq3'.
          
          (* By atyping_app *)
          simpl.
          assert (atyping (G2++G1) D1 (exp_app (subst_ee x e' e1) (subst_ee x e' e2)) T2 D3''') as Htyp12.
            apply atyping_app with (T1:=T1) (K:=K) (D2:=D2''); auto.

          (* IH12 strengthening *)
          assert (forall x0, x0 `in` fv_ee (exp_app (subst_ee x e' e1) (subst_ee x e' e2)) -> x0 `notin` dom D3''') as Diff.
            intros x0 Hx0insubst.
            apply denv_mono_disjoint with (x:=x0) in Htyp12; auto.
          apply atyping_lin_diff_strengthening with (D:=D3''') in Htyp12; auto.
          destruct Htyp12 as [C' [Htyp12 EqC']].

          (* IH12 weakening *)
          clear Diff.
          assert (<#D3'''#> ~~ <#D3#>) as D3'''eqD3.
                  apply Equal_trans with (m':=<#E3'''#>); auto.
                    apply Equal_sym; auto.
                    apply Equal_trans with (m':=<#<@<#C3''#>|_|<#D3#>@>#>); auto.
                      apply Equal_sym.
                        apply Equal_trans with (m':=<#C3''#>|_|<#D3#>); auto.
                          apply dmap_Equal_rewrite_Union_left with (M1:=@@).
                            apply Equal_trans with (m':=<#D3''#>); auto.
                              apply Equal_trans with (m':=<#<@<#B3''#>--<#B3''#>@>#>); auto. 
                                apply Equal_trans with (m':=<#B3''#>--<#B3''#>).
                                  apply dmap_Equal_diff_refl.
                                    apply Equal_refl.
                                  apply denv_to_from_dmap.  
                                apply Equal_sym; auto.
                              apply Equal_sym.
                                apply dmap_union_empty_refl.
                          apply denv_to_from_dmap.
          assert (<@(<#<@<#D1#>--<#D3'''#>@>#>|_|<#D0#>)@> ~~~ <@((<#D1#>--<#D3#>)|_|<#D0#>)@>) as EQ2.
            apply Equal_trans with (m':=(<#<@<#D1#>--<#D3'''#>@>#>|_|<#D0#>)).
              apply Equal_sym.
                apply denv_to_from_dmap.
              apply Equal_trans with (m':=(<#D1#>--<#D3#>)|_|<#D0#>).
                apply Equal_sym.      
                  apply dmap_Equal_rewrite_Union_left with (M1:=<#D1#>--<#D3#>); auto. 
                    apply Equal_trans with (m':=<#D1#>--<#D3'''#>).
                      apply dmap_Equal_rewrite_diff_right with (M2:=<#D3#>); auto. 
                        apply Equal_sym; auto.
                        apply Equal_refl.
                      apply denv_to_from_dmap.
                  apply Equal_refl.
                apply denv_to_from_dmap.
          assert (wf_denv (G2++G1) <@(<#<@<#D1#>--<#D3'''#>@>#>|_|<#D0#>)@>) as Wf_denv_union.
            apply denv_permutation with (D:=<@((<#D1#>--<#D3#>)|_|<#D0#>)@>); auto.
              apply dmap_to_denv_is_uniq.
              apply Equal_sym; auto.
          assert (<#<@<#D1#>--<#D3'''#>@>#> ** <#D0#>) as Disj12.
            apply dmap_Equal_preserves_disjoint_left with (M1:=<#D1#>--<#D3#>); auto.
              apply Equal_trans with (m':=<#D1#>--<#D3'''#>).
                apply Equal_sym.
                  apply denv_to_from_dmap.
                apply dmap_Equal_rewrite_diff_right with (M2:=<#D3'''#>); auto.
                  apply Equal_refl.
          apply atyping_lin_union_weakening with (D:=D0) in Htyp12; auto.
          destruct Htyp12 as [E3 [Htyp12 EqE3]].
          assert (uniq <@((<#D1#>--<#D3#>)|_|<#D0#>)@>) as Uniq3.
            apply dmap_to_denv_is_uniq.
          apply atyping_permutation with (D1':=<@(<#D1#>--<#D3#>)|_|<#D0#>@>) in Htyp12; auto.
          destruct Htyp12 as [B3 [Htyp12 EqB3]].
          exists B3.
          split; auto.
            apply Equal_trans with (m':=<#E3#>).
              apply Equal_sym; auto. 
                apply Equal_trans with (m':=<#<@<#C'#>|_|<#D0#>@>#>); auto.
                apply Equal_trans with (m':=<#D0#>); auto.
                  apply Equal_trans with (m':=<#C'#>|_|<#D0#>).
                    apply Equal_sym.
                      apply denv_to_from_dmap.
                    apply Equal_sym.
                      apply dmap_Equal_rewrite_Union_left with (M1:=@@).
                        apply Equal_trans with (m':=<#<@<#D3'''#>--<#D3'''#>@>#>); auto. 
                          apply Equal_trans with (m':=<#D3'''#>--<#D3'''#>).
                            apply dmap_Equal_diff_refl.
                              apply Equal_refl.
                            apply denv_to_from_dmap.  
                          apply Equal_sym; auto.
                        apply Equal_sym.
                          apply dmap_union_empty_refl.
        SSSCase "x notin e2".
          apply IHHtyp1in in Hxine1. clear IHHtyp1in IHHtyp1notin.
          apply IHHtyp2notin in Hxnotine2. clear IHHtyp2in IHHtyp2notin.
          destruct Hxine1 as [B3' [Hxine1 B3'eqD3']].
          destruct Hxnotine2 as [B3'' [Hxnotine2 B3''eqD3']].
          (* IH1 strengthening *)
          assert (forall x0, x0 `in` fv_ee (subst_ee x e' e1) -> x0 `notin` dom B3') as Diff1.
            intros x0 Hx0insubst1.
            apply denv_mono_disjoint with (x:=x0) in Hxine1; auto.
          apply atyping_lin_diff_strengthening with (D:=B3') in Hxine1; auto.
          assert (uniq <@<#D1#>--<#D2#>@>) as Uniq1.
            apply dmap_to_denv_is_uniq.
          assert (<@<#<@(<#D1#>--<#D2#>)|_|<#D0#>@>#>--<#B3'#>@> ~~~ <@<#D1#>--<#D2#>@>) as EQ1.
            apply Equal_trans with (m':=<#D1#>--<#D2#>).
              apply Equal_trans with (m':=<#<@(<#D1#>--<#D2#>)|_|<#D0#>@>#>--<#B3'#>).
                apply Equal_sym.
                  apply denv_to_from_dmap.
                apply Equal_sym.
                  apply dmap_Equal_rewrite_diff_left with (M1:=(<#D1#>--<#D2#>)|_|<#D0#>).
                    apply denv_to_from_dmap.
                    apply Equal_trans with (m':=((<#D1#>--<#D2#>)--<#B3'#>) |_| (<#D0#>--<#B3'#>)).
                      apply dmap_Equal_rewrite_Union_left with (M1:=<#D1#>--<#D2#>).
                        apply Equal_sym.
                          apply disjoint_diff_refl.
                            apply dmap_Equal_preserves_disjoint_right with (M2:=<#D0#>).
                              apply dmap_Sub_preserves_disjoint_left with (M1:=<#D1#>--<#D3#>); auto.
                                apply dmap_Sub_diff_right; auto.
                              eapply Equal_trans with (m':=<#D3'#>); auto.
                                apply Equal_sym; auto.
                        apply dmap_Equal_rewrite_Union_right with (M2:=@@).
                          apply dmap_Equal_diff_refl.
                            eapply Equal_trans with (m':=<#D3'#>); auto.
                              apply Equal_sym; auto.
                          apply Equal_trans with (m':=@@ |_| (<#D1#>--<#D2#>)); auto.
                            apply Equal_sym.
                              apply dmap_union_empty_refl; auto.
                            apply dmap_union_sym.
                              apply empty_disjoint.
                    apply Equal_sym.
                        apply dmap_union_diff_distr; auto.
              apply denv_to_from_dmap.
          destruct Hxine1 as [D2' [Hxine1 EmptyeqD2']].
          apply atyping_permutation with (D1':=<@<#D1#>--<#D2#>@>) in Hxine1; auto.
          destruct Hxine1 as [C2' [Hxine1 C2'eqD2']].
          clear Diff1 EQ1.
          
          (* IH2 strengthening *)
          assert (forall x0, x0 `in` fv_ee (subst_ee x e' e2) -> x0 `notin` dom B3'') as Diff2.
            intros x0 Hx0insubst2.
            apply denv_mono_disjoint with (x:=x0) in Hxnotine2; auto.
          apply atyping_lin_diff_strengthening with (D:=B3'') in Hxnotine2; auto.
          destruct Hxnotine2 as [D3'' [Hxnotine2 EmptyeqD3'']].
          clear Diff2.

          (* IH2 weakening *)
          assert (wf_denv (G2++G1) <@(<#<@<#D2#>--<#B3''#>@>#>|_|<#D3'#>)@>) as Wf_denv_union2.
            apply wf_denv_lin_sub_strengthening with (D:=<@<#D1#>--<#D3#>|_|<#D3'#>@>); auto.
              apply denv_permutation with (D:=<@<#D1#>--<#D3#>|_|<#D0#>@>); auto.
                apply dmap_to_denv_is_uniq.
                apply dmap_denv_Equal_injection_add.
                  apply dmap_Equal_rewrite_Union_right with (M2:=<#D0#>); auto.
                    apply Equal_refl.
              apply dmap_denv_Sub_injection_add.
                apply dmap_Sub_rewrite_Union_left with (M1:=<#<@<#D2#>--<#B3''#>@>#>).
                  apply dmap_Equal_rewrite_Sub_left with (M1:=<#D2#>--<#B3''#>).
                    apply denv_to_from_dmap.
                      apply dmap_Equal_rewrite_Sub_right with (M2:=<#D1#>--<#B3''#>).
                        apply dmap_Equal_rewrite_diff_right with (M2:=<#B3''#>); auto.
                          apply Equal_refl.                    
                        apply dmap_Sub_diff_left; auto.
              apply dmap_to_denv_is_uniq.
          assert (<#<@<#D2#>--<#B3''#>@>#> ** <#D3'#>) as Disj2.
            apply dmap_Sub_preserves_disjoint_left with (M1:=<#D1#>--<#D3#>).
              apply dmap_Equal_preserves_disjoint_right with (M2:=<#D0#>); auto.
                apply Equal_sym; auto.              
              apply dmap_Equal_rewrite_Sub_left with (M1:=<#D2#>--<#B3''#>).
                apply denv_to_from_dmap.
                apply dmap_Equal_rewrite_Sub_right with (M2:=<#D1#>--<#B3''#>).
                  apply dmap_Equal_rewrite_diff_right with (M2:=<#B3''#>); auto.
                    apply Equal_refl.                    
                  apply dmap_Sub_diff_left; auto.
          assert (uniq D3') as Uniq3'.
            apply atyping_regular in Htyp'.
            decompose [and] Htyp'.
            apply uniq_from_wf_denv_lin in H0; auto.
          apply atyping_lin_union_weakening with (D:=D3') in Hxnotine2; auto.
          destruct Hxnotine2 as [E3''' [Hxnotine2 EqE3''']].
          clear Disj2 Uniq3'.

          (* IH1 weakening *)
          assert (<@(<#<@<#D1#>--<#D2#>@>#>|_|<#<@<#<@<#D2#>--<#B3''#>@>#>|_|<#D3'#>@>#>)@> ~~~ <@(<#D1#>--<#D3#>)|_|<#D0#>@>) as EQ1'.           
            apply Equal_trans with (m':=<#<@<#D1#>--<#B3''#>@>#>|_|<#D3'#>).
              apply Equal_trans with (m':=<#<@<#D1#>--<#D2#>@>#>|_|<#<@<#<@<#D2#>--<#B3''#>@>#>|_|<#D3'#>@>#>).
                apply Equal_sym.
                  apply denv_to_from_dmap.
                apply Equal_trans with (m':=<#<@<#D1#>--<#D2#>@>#>|_|<#<@<#D2#>--<#B3''#>@>#>|_|<#D3'#>); auto.
                  apply Equal_sym.
                    apply dmap_Equal_rewrite_Union_right with (M2:=<#<@<#D2#>--<#B3''#>@>#>|_|<#D3'#>).
                      apply denv_to_from_dmap.
                      apply Equal_refl.
                  apply Equal_trans with (m':=(<#D1#>--<#D2#>)|_|<#<@<#D2#>--<#B3''#>@>#>|_|<#D3'#>); auto.
                    apply dmap_Equal_rewrite_Union_left with (M1:=<#<@<#D1#>--<#D2#>@>#>).
                      apply Equal_sym.
                        apply denv_to_from_dmap.
                      apply Equal_refl.
                    apply Equal_trans with (m':=(<#D1#>--<#D2#>)|_|(<#D2#>--<#B3''#>)|_|<#D3'#>); auto.
                      apply dmap_Equal_rewrite_Union_right with (M2:=<#<@<#D2#>--<#B3''#>@>#>|_|<#D3'#>).
                        apply dmap_Equal_rewrite_Union_left with (M1:=<#<@<#D2#>--<#B3''#>@>#>).
                          apply Equal_sym.
                            apply denv_to_from_dmap.
                          apply Equal_refl.
                        apply Equal_refl.
                  apply dmap_Equal_rewrite_Union_left with (M1:=(<#D1#>--<#D2#>)|_|(<#D2#>--<#B3''#>)).
                    apply Equal_trans with (m':=(<#D1#>--<#B3''#>)).
                      apply dmap_diff_merge; auto.
                        apply dmap_Equal_rewrite_Sub_left with (M1:=<#D3#>); auto.
                          apply Equal_sym; auto.
                      apply denv_to_from_dmap.
                    apply Equal_sym.
                      apply dmap_union_assoc.
              apply Equal_trans with (m':=(<#D1#>--<#B3''#>|_|<#D3'#>)).
                apply dmap_Equal_rewrite_Union_left with (M1:=<#<@(<#D1#>--<#B3''#>)@>#>).
                  apply Equal_sym.
                    apply denv_to_from_dmap.
                  apply Equal_refl.                  
                apply Equal_trans with (m':=(<#D1#>--<#D3#>|_|<#D0#>)).
                  apply Equal_trans with (m':=(<#D1#>--<#D3#>|_|<#D3'#>)).
                    apply dmap_Equal_rewrite_Union_left with (M1:=<#D1#>--<#B3''#>).
                      apply dmap_Equal_rewrite_diff_right with (M2:=<#B3''#>); auto.
                       apply Equal_refl.
                       apply Equal_refl.
                    apply dmap_Equal_rewrite_Union_right with (M2:=<#D3'#>).
                      apply Equal_sym; auto.
                      apply Equal_refl.
                  apply denv_to_from_dmap.
          assert (wf_denv (G2++G1) <@(<#<@<#D1#>--<#D2#>@>#>|_|<#<@<#<@<#D2#>--<#B3''#>@>#>|_|<#D3'#>@>#>)@>) as Wf_denv_union1.
            apply denv_permutation with (D:=<@(<#D1#>--<#D3#>)|_|<#D0#>@>); auto.
              apply dmap_to_denv_is_uniq.
              apply Equal_sym; auto.
          assert (<#<@<#D1#>--<#D2#>@>#> ** <#<@<#<@<#D2#>--<#B3''#>@>#>|_|<#D3'#>@>#>) as Disj1.
            apply dmap_denv_diff_injection_add.
              apply dmap_disjoint_app.
                apply dmap_Equal_preserves_disjoint_right with (M2:=<#D2#>--<#B3''#>).
                  apply dmap_Sub_preserves_disjoint_right with (M2:=<#D2#>).
                    apply diff_disjoint.
                    apply dmap_diff_mono.
                  apply Equal_sym.
                    apply denv_to_from_dmap.
            apply dmap_Sub_preserves_disjoint_right with (M2:=<#D0#>).
              apply dmap_Sub_preserves_disjoint_left with (M1:=<#D1#>--<#D3#>); auto.
                apply dmap_Sub_diff_right; auto.
              apply denv_mono in Htyp'; auto.
          assert (uniq <@<#<@<#D2#>--<#B3''#>@>#>|_|<#D3'#>@>) as Uniq2'.
            apply dmap_to_denv_is_uniq.
          apply atyping_lin_union_weakening with (D:=<@<#<@<#D2#>--<#B3''#>@>#>|_|<#D3'#>@>) in Hxine1; auto.
          destruct Hxine1 as [E2'' [Hxine1 EqE2'']].
          assert (uniq <@(<#D1#>--<#D3#>)|_|<#D0#>@>) as Uniq1'.
            apply dmap_to_denv_is_uniq.
          apply atyping_permutation with (D1':=<@(<#D1#>--<#D3#>)|_|<#D0#>@>) in Hxine1; auto.
          destruct Hxine1 as [D2'' [Hxine1 EqD2'']].
          clear EQ1' Uniq2' Uniq1' Disj1.

          (* By atyping_app *)
          assert (uniq D2'') as Uniq2''.
            apply atyping_regular in Hxine1.
            decompose [and] Hxine1.
            apply uniq_from_wf_denv_lin in H0; auto.
          assert (<@<#<@<#D2#>--<#B3''#>@>#> |_| <#D3'#>@> ~~~ D2'') as EQ.
            apply Equal_trans with (m':=<#E2''#>); auto.
              apply Equal_trans with (m':=<#<@<#C2'#>|_|<#<@<#<@<#D2#>--<#B3''#>@>#>|_|<#D3'#>@>#>@>#>); auto.
                apply dmap_denv_Equal_injection_add.
                  apply Equal_trans with (m':=<#C2'#>|_|<#<@<#D2#>--<#B3''#>@>#>|_|<#D3'#>); auto.
                    apply Equal_trans with (m':=<#C2'#>|_|(<#D2#>--<#B3''#>)|_|<#D3'#>); auto.
                      apply Equal_trans with (m':=(<#D2#>--<#B3''#>)|_|<#D3'#>); auto.
                        apply dmap_Equal_rewrite_Union_left with (M1:=<#<@(<#D2#>--<#B3''#>)@>#>).
                          apply Equal_sym.
                            apply denv_to_from_dmap.
                          apply Equal_refl.   
                        apply Equal_sym.
                          apply dmap_Equal_rewrite_Union_left with (M1:=<#C2'#>|_|<#D2#>--<#B3''#>).
                            apply Equal_trans with (m':=@@ |_| <#D2#>--<#B3''#>).
                              apply dmap_Equal_rewrite_Union_left with (M1:=<#C2'#>).
                                apply Equal_trans with (m':=<#D2'#>).
                                  apply Equal_sym; auto.
                                  apply Equal_trans with (m':=<#<@<#B3'#>--<#B3'#>@>#>); auto.
                                    apply Equal_trans with (m':=<#B3'#>--<#B3'#>); auto.
                                      apply Equal_sym.
                                        apply denv_to_from_dmap.
                                      apply dmap_diff_refl.
                                apply Equal_refl.   
                              apply dmap_union_empty_refl.
                            apply Equal_sym.
                              apply dmap_union_assoc.
                      apply dmap_Equal_rewrite_Union_right with (M2:=(<#D2#>--<#B3''#>)|_|<#D3'#>).
                        apply dmap_Equal_rewrite_Union_left with (M1:=(<#D2#>--<#B3''#>)).
                          apply denv_to_from_dmap.
                          apply Equal_refl.   
                        apply Equal_refl.   
                    apply dmap_Equal_rewrite_Union_right with (M2:=<#<@<#D2#>--<#B3''#>@>#>|_|<#D3'#>).
                      apply denv_to_from_dmap.
                      apply Equal_refl.
                apply Equal_sym; auto.
          apply atyping_permutation with (D1':=D2'') in Hxnotine2; auto.
          destruct Hxnotine2 as [D2''' [Hxnotine2 EqD2''']].

          exists (D2''').
          split.
            apply atyping_app with (T1:=T1) (K:=K) (D2:=D2''); auto.
            apply Equal_trans with (m':=<#E3'''#>).
              apply Equal_sym; auto.
              apply Equal_trans with (m':=<#<@<#D3''#>|_|<#D3'#>@>#>); auto.
                apply Equal_trans with (m':=<#D3''#>|_|<#D3'#>).
                  apply Equal_sym.
                    apply denv_to_from_dmap.
                  apply Equal_sym.
                    apply dmap_Equal_rewrite_Union_left with (M1:=@@).
                      apply Equal_trans with (m':=<#<@<#B3''#>--<#B3''#>@>#>).
                        apply Equal_trans with (m':=<#B3''#>--<#B3''#>).
                          apply Equal_sym.
                            apply dmap_diff_refl.
                          apply denv_to_from_dmap.
                        apply Equal_sym; auto.
                      apply Equal_sym.
                        apply dmap_union_empty_refl.
      SSCase "x notin e1".
        destruct (@in_dec x (fv_ee e2)) as [Hxine2 | Hxnotine2].
        SSSCase "x in e2".
          apply IHHtyp1notin in Hxnotine1. clear IHHtyp1in IHHtyp1notin.
          apply IHHtyp2in in Hxine2. clear IHHtyp2in IHHtyp2notin.
          destruct Hxnotine1 as [B2 [Hxnotine1 B2eqD2]].
          destruct Hxine2 as [B3'' [Hxine2 B3''eqD3']].
          (* IH1 strengthening *)
          assert (forall x0, x0 `in` fv_ee (subst_ee x e' e1) -> x0 `notin` dom D3) as Diff1.
            intros x0 Hx0insubst1.
            apply denv_sub_notin_dom with (D1:=B2); auto.
              apply atyping_regular in Htyp2.
              decompose [and] Htyp2.
              apply uniq_from_wf_denv_lin in H0; auto.
          
              apply atyping_regular in Hxnotine1.
              decompose [and] Hxnotine1.
              apply uniq_from_wf_denv_lin in H0; auto.

              apply denv_mono_disjoint with (x:=x0) in Hxnotine1; auto.

              apply dmap_Equal_rewrite_Sub_right with (M2:=<#D2#>); auto.
                apply Equal_sym; auto.

              apply denv_mono_disjoint with (x:=x0) in Hxnotine1; auto.
          apply atyping_lin_diff_strengthening with (D:=D3) in Hxnotine1; auto.
          destruct Hxnotine1 as [D2' [Hxnotine1 EmptyeqD2']].
          clear Diff1.

          (* IH1 weakening *)
          assert (wf_denv (G2++G1) <@(<#<@<#D1#>--<#D3#>@>#>|_|<#D0#>)@>) as Wf_denv_union1.
            apply denv_permutation with (D:=<@(<#D1#>--<#D3#>)|_|<#D0#>@>); auto.
              apply dmap_to_denv_is_uniq.
              apply dmap_denv_Equal_injection_add.
                apply dmap_Equal_rewrite_Union_left with (M1:=<#D1#>--<#D3#>); auto.
                  apply denv_to_from_dmap.  
                  apply Equal_refl.
          assert (<#<@<#D1#>--<#D3#>@>#> ** <#D0#>) as Disj1.
            apply dmap_Equal_preserves_disjoint_left with (M1:=<#D1#>--<#D3#>); auto.
              apply Equal_sym.
                apply denv_to_from_dmap.
          apply atyping_lin_union_weakening with (D:=D0) in Hxnotine1; auto.
          destruct Hxnotine1 as [E2'' [Hxnotine1 EqE2'']].
          assert (<@(<#<@<#D1#>--<#D3#>@>#>|_|<#D0#>)@> ~~~ <@((<#D1#>--<#D3#>)|_|<#D0#>)@>) as EQ1.
            apply dmap_denv_Equal_injection_add.  
            apply dmap_Equal_rewrite_Union_left with (M1:=<#D1#>--<#D3#>); auto. 
              apply Equal_refl.
              apply dmap_Equal_rewrite_Union_left with (M1:=<#<@<#D1#>--<#D3#>@>#>); auto. 
                apply Equal_sym.
                  apply denv_to_from_dmap.
                apply Equal_refl.
          apply atyping_permutation with (D1':=<@((<#D1#>--<#D3#>)|_|<#D0#>)@>) in Hxnotine1; 
            try solve [auto | apply dmap_to_denv_is_uniq].
          destruct Hxnotine1 as [D2'' [Hxnotine1 EqD2'']].
          clear EQ1.

          (* for typ2 *)
          assert (<@(<#D2#>--<#D3#>)|_|<#D0#>@> ~~~ D2'') as EQ2.
            eapply Equal_trans with (m':=<#E2''#>); auto.
              eapply Equal_trans with (m':=<#<@<#D2'#>|_|<#D0#>@>#>); auto.
                apply dmap_denv_Equal_injection_add.  
                  apply dmap_Equal_rewrite_Union_left with (M1:=<#D2#>--<#D3#>); auto. 
                    apply Equal_sym. 
                      apply Equal_trans with (m':=<#<@<#B2#>--<#D3#>@>#>); auto.
                        apply Equal_trans with (m':=<#B2#>--<#D3#>); auto.
                          apply Equal_sym.
                            apply denv_to_from_dmap.
                          apply dmap_Equal_rewrite_diff_left with (M1:=<#B2#>); auto. 
                           apply Equal_refl.
                    apply Equal_refl.
                apply Equal_sym; auto.
          assert (uniq D2'') as uniqD2''.
            apply atyping_regular in Hxnotine1.
            decompose [and] Hxnotine1.
            apply uniq_from_wf_denv_lin in H0; auto.
          apply atyping_permutation with (D1':=D2'') in Hxine2; 
            try solve [auto | apply dmap_to_denv_is_uniq].
          destruct Hxine2 as [C3'' [Hxine2 EqC2'']].
          clear EQ2 uniqD2''.

          (* By atyping_app *)
          simpl. exists C3''.
          split; auto.
            apply atyping_app with (T1:=T1) (K:=K) (D2:=D2''); auto.
            apply Equal_trans with (m':=<#B3''#>); auto.
              apply Equal_sym; auto. 
        SSSCase "x notin e2".
          simpl in J.
          assert (x `in` fv_ee e1 \/x `in` fv_ee e2) as KK.
            clear Hxnotine1 Hxnotine2. fsetdec.
          destruct KK as [KK | KK].
            contradict KK; auto.
            contradict KK; auto.
    SCase "x notin e1e2".
      destruct (@in_dec x (fv_ee e1)) as [Hxine1 | Hxnotine1].
      SSCase "x in e1".
        destruct (@in_dec x (fv_ee e2)) as [Hxine2 | Hxnotine2].
        SSSCase "x in e2".
          simpl in J. 
          contradict Hxine1; auto.
        SSSCase "x notin e2".
          simpl in J. 
          contradict Hxine1; auto.
      SSCase "x notin e1".
        destruct (@in_dec x (fv_ee e2)) as [Hxine2 | Hxnotine2].
        SSSCase "x in e2".
          simpl in J. 
          contradict Hxine2; auto.
        SSSCase "x notin e2".
          apply IHHtyp1notin in Hxnotine1. clear IHHtyp1in IHHtyp1notin.
          apply IHHtyp2notin in Hxnotine2. clear IHHtyp2in IHHtyp2notin.
          destruct Hxnotine1 as [B2 [Hxnotine1 B2eqD2]].
          destruct Hxnotine2 as [B3 [Hxnotine2 B3eqD3]].
          apply Equal_sym in B2eqD2.
          assert (uniq B2) as uniqB2.
            apply atyping_regular in Hxnotine1.
            decompose [and] Hxnotine1.
            apply uniq_from_wf_denv_lin in H0; auto.
          apply atyping_permutation with (D1':=B2) in Hxnotine2; auto.
          destruct Hxnotine2 as [B3' [Hxnotine2 B3'eqB3]].
          exists B3'.
          split.
            apply atyping_app with (D2:=B2) (T1:=T1) (K:=K); auto.
            eapply Equal_trans with (m':=<#B3#>); auto.
              apply Equal_sym; auto.
  Case "atyping_tabs".
    pick fresh Y.
    assert (Y `notin` dom <@(<#D#>--<#D'#>) |_| <#D3#>@>) as YnotinD.
      apply notIn_implies_notin_dom.
        intro J.
        apply update_in_iff in J.
        destruct J as [J | J].
          apply diff_in_iff in J.
          destruct J as [J1 J2].
          apply In_implies_in_dom in J1.
          contradict J1; auto.

          apply In_implies_in_dom in J.
          contradict J; auto.
    assert (Y `notin` denv_fv_tt <@(<#D#>--<#D'#>) |_| <#D3#>@>) as YnotinD'.
      assert (Y `notin` denv_fv_tt <@<#D#> -- <#D'#>@>) as K''.
        apply notin_denv_fv_tt_diff; auto.
          assert (Y `notin` L) as J. auto.
          apply H0 in J. apply atyping_regular in J.
          decompose [and] J. 
          apply uniq_from_wf_denv_lin in H4; auto.
      assert (Y `notin` denv_fv_tt <@<#D#> -- <#D'#>@> /\ Y `notin` denv_fv_tt D3) as K'. 
        auto.
      apply notin_denv_fv_tt_union in K'; auto.
        apply dmap_to_denv_is_uniq.
        apply dmap_Equal_preserves_disjoint_left with (M1:=<#D#>--<#D'#>); auto.
          apply Equal_sym.
            apply denv_to_from_dmap.
      assert (<@(<#D#>--<#D'#>) |_| <#D3#>@> ~~~ <@(<#<@<#D#>--<#D'#>@>#>) |_| <#D3#>@>) as EQ.
        apply dmap_denv_Equal_injection_add.
          apply dmap_Equal_rewrite_Union_left with (M1:=<#D#>--<#D'#>); auto.
            apply denv_to_from_dmap.
            apply Equal_refl.
      apply dmap_eq__denv_fv_tt_eq_notin with (X:=Y) in EQ; auto.
        apply dmap_to_denv_is_uniq.
        apply dmap_to_denv_is_uniq.
    assert (Y `notin` fv_te (subst_ee x e' e1)) as HynotinSubst.
      apply notin_fv_te_subst_ee; auto.
      auto.
    assert (wf_denv ([(Y, gbind_kn K)]++G2++G1) <@(<#D#>--<#D'#>) |_| <#D3#>@>) as Wf_denv'.
      rewrite_env (nil++[(Y, gbind_kn K)]++(G2++G1)).
      apply wf_denv_nonlin_weakening; auto.
        simpl_env.
        apply wf_genv_kn; auto.
          apply wf_genv_from_wf_denv in Wf_denv; auto.
    assert (
    (x `in` fv_ee(open_te e1 Y) -> 
       exists B3',
         atyping (([(Y, gbind_kn K)]++G2) ++ G1) <@ (<#D#> -- <#D'#>) |_| <#D3#> @> (subst_ee x e' (open_te e1 Y)) (open_tt T1 Y) B3' /\
         B3' ~~~ D3')
      /\
    (x `notin` fv_ee(open_te e1 Y) -> 
       exists B',
         atyping (([(Y, gbind_kn K)]++G2) ++ G1) D (subst_ee x e' (open_te e1 Y)) (open_tt T1 Y) B' /\
         B' ~~~ D')
    ) as IH.
     apply H1 with (S0:=S); auto.
    clear H1.
    destruct IH as [IHin IHnotin].
    split; intro J; simpl in J.
      (* x `in` \y. e1 *)
      apply in_fv_ee_open_te with (Y:=Y) in J; auto.
      apply IHin in J.
      destruct J as [B3' [Htyp'' B3'eqD3']].
      exists B3'. simpl.       
      split; auto.
        apply atyping_tabs with (L:=L `union` (fv_tt T1) `union` fv_te (subst_ee x e' e1) 
                                      `union` dom(G2++G1) `union` dom <@(<#D#>--<#D'#>) |_| <#D3#>@> 
                                      `union` denv_fv_tt <@(<#D#>--<#D'#>) |_| <#D3#>@> 
                                      `union` singleton Y); auto.
          intros X FrX.
          assert (X `notin` L) as XnL. clear - FrX. auto.
          apply H in XnL.
          rewrite subst_ee_open_te_var; eauto using type_from_wf_atyp.
          apply value_through_subst_ee; auto.

          intros X0 FrX0.
          apply atyping_nonlin_typ_renaming with (X:=Y).
            assert (Y `notin` dom (G2++G1)) as JJ. 
              rewrite dom_app. destruct_notin. auto.
            clear FrX0. destruct_notin. fsetdec.

            clear Fr. destruct_notin. fsetdec.

            clear Fr. destruct_notin. auto.

            rewrite subst_ee_open_te_var; auto.
      (* x `notin` \y. e1 *)
      apply notin_fv_ee_open_te with (Y:=Y) in J; auto.
      apply IHnotin in J.
      destruct J as [B' [Htyp'' B'eqD']].
      exists B'. simpl.       
      split; auto.
        apply atyping_tabs with (L:=L `union` (fv_tt T1) `union` fv_te (subst_ee x e' e1) 
                                      `union` dom(G2++G1) `union` dom D 
                                      `union` denv_fv_tt D
                                      `union` singleton Y); auto.
          intros X FrX.
          assert (X `notin` L) as XnL. clear - FrX. auto.
          apply H in XnL.
          rewrite subst_ee_open_te_var; eauto using type_from_wf_atyp.
          apply value_through_subst_ee; auto.

          intros X0 FrX0.
          apply atyping_nonlin_typ_renaming with (X:=Y); auto.
            rewrite subst_ee_open_te_var; auto.
  Case "atyping_tapp".
    assert (
    (x `in` fv_ee e1 -> 
       exists B3',
         atyping (G2 ++ G1) <@ (<#D#> -- <#D'#>) |_| <#D3#> @> (subst_ee x e' e1) (typ_all K T2) B3' /\
         B3' ~~~ D3')
      /\
    (x `notin` fv_ee e1 -> 
       exists B',
         atyping (G2 ++ G1) D (subst_ee x e' e1) (typ_all K T2) B' /\
         B' ~~~ D')
    ) as IH.
     apply IHHtyp with (S0:=S); auto.
    clear IHHtyp.
    destruct IH as [IHin IHnotin].
    split; intro J; simpl in J.
      (* x `in` \y. e1 *)
      apply IHin in J.
      destruct J as [B3' [Htyp'' B3'eqD3']].
      exists B3'. simpl.       
      split; auto.
        eapply atyping_tapp; eauto.
          apply wf_atyp_strengthening in H; auto.
      (* x `notin` \y. e1 *)
      apply IHnotin in J.
      destruct J as [B' [Htyp'' B'eqD']].
      exists B'. simpl.       
      split; auto.
        eapply atyping_tapp; eauto.
          apply wf_atyp_strengthening in H; auto.
Qed.

Lemma atyping_through_lin_subst_ee : forall S x G T e e' D1 D D2 D3 D3',
  atyping G (D2 ++ [(x, S)] ++ D1) e T D ->
  atyping G D3 e' S D3' ->
  (<#D2++D1#> -- <#D#>) ** <#D3#> ->
  wf_denv G <@ (<#D2++D1#> -- <#D#>) |_| <#D3#> @> ->
  x `notin` dom(D3) ->
  (x `in` fv_ee(e) -> 
     exists B3',
       atyping G <@ (<#D2++D1#> -- <#D#>) |_| <#D3#> @> (subst_ee x e' e) T B3' /\
       B3' ~~~ D3') 
    /\
  (x `notin` fv_ee(e) -> 
     exists B,
       atyping G (D2 ++ D1) (subst_ee x e' e) T B /\
       <#B#> ~~ (<#D#> [-] x)).
Proof.
  intros S x G T e e' D1 D D2 D3 D3' Htyp Htyp' Disj Wf_denv xnotinD3.
  remember (D2 ++ [(x, S)] ++ D1) as DD.
  generalize dependent D2.
  generalize dependent D1.
  generalize dependent S.
  generalize dependent x.
  generalize dependent D3.
  generalize dependent D3'.
  generalize dependent e'.
  (atyping_cases (induction Htyp) Case); intros; subst.  
  Case "atyping_uvar".
    assert (x `notin` dom (D2 ++ [(x0, S)] ++ D1)) as xnotinDD.
      apply denv_dom_ginv with (x:=x) in H0; auto.
        apply binds_In in H; auto.
    split; intro J.
      (* x0 in fv_ee x *) 
      rewrite dom_app in xnotinDD.
      rewrite dom_app in xnotinDD.
      simpl in xnotinDD.
      destruct_notin.
      simpl in J.
      contradict J; auto.
      (* x0 notin fv_ee x *) 
      exists (D2++D1).
      split.
        rewrite <- subst_ee_fresh; auto.
        apply atyping_uvar; auto.
          apply wf_denv_lin_strengthening in H0; auto.
            apply Equal_sym.
              apply denv_remove_mid.
                apply uniq_from_wf_denv_lin in H0; auto.
  Case "atyping_lvar".
    assert (uniq (D2 ++ [(x0, S)] ++ D1)) as Uniq.
      apply uniq_from_wf_denv_lin in H0; auto.
    rename H into Binds.
    rename H0 into Wf_denv'.
    analyze_binds_uniq Binds.
    SCase "x in D2, x<>x0, x notin D1".
      split; intro J; simpl in J.
        contradict J; auto.
        exists (<@(<#D2 ++ [(x0, S)] ++ D1#>[-]x)[-]x0@>).
        split.
          rewrite <- subst_ee_fresh; auto.
          apply atyping_lvar; auto.
            apply wf_denv_lin_strengthening in Wf_denv'; auto.
            apply dmap_to_denv_is_uniq.
            apply Equal_trans with (m':=(<#D2 ++ [(x0, S)] ++ D1#>[-]x)[-]x0).
              apply Equal_trans with (m':=(<#D2 ++ [(x0, S)] ++ D1#>[-]x0)[-]x).
                apply dmap_remove_preserves_Equal.
                  apply Equal_sym.
                    apply denv_remove_mid.
                      apply uniq_from_wf_denv_lin in Wf_denv'; auto.
                apply dmap_remove_remove_commut.
              apply denv_to_from_dmap.
          apply Equal_trans with (m':=(<#D2 ++ [(x0, S)] ++ D1#>[-]x)[-]x0).
            apply Equal_sym.
               apply denv_to_from_dmap.
            apply dmap_remove_preserves_Equal; auto.
    SCase "x notin D2, x=x0, x notin D1".
      subst.
      split; intro J; simpl in J.
        (*x0 in x0*)
        assert (uniq <@(<#D2++D1#>--<#D'#>) |_| <#D3#>@>) as Uniq'.
          apply uniq_from_wf_denv_lin in Wf_denv; auto.        
        assert (D3 ~~~ <@(<#D2++D1#>--<#D'#>) |_| <#D3#>@>) as EQ.
          apply Equal_trans with (m':=(<#D2++D1#>--<#D'#>) |_| <#D3#>).
            apply dmap_Equal_rewrite_Union_left with (M1:=@@).
              apply dmap_Equal_diff_refl.
                apply Equal_trans with (m':=<#D2++[(x0, S)]++D1#>[-]x0); auto.
                  apply Equal_sym.
                    apply denv_remove_mid.
                      apply uniq_from_wf_denv_lin in Wf_denv'; auto.
              apply Equal_sym.
                apply dmap_union_empty_refl.                 
            apply denv_to_from_dmap; auto.
        apply atyping_permutation with (D1':=<@(<#D2++D1#>--<#D'#>) |_| <#D3#>@>) in Htyp'; auto.
        destruct Htyp' as [D2' [Htyp' D3'eqD2']].
        exists D2'.
        split.
          simpl. simpl_env in Htyp'. 
          destruct (x0==x0); subst; auto.
            contradict n; auto.
          apply Equal_sym; auto.        
        (*x0 notin x0*)
        contradict J; try solve [auto | fsetdec].
    SCase "x notin D1, x<>x0, x in D2".
      split; intro J; simpl in J.
        contradict J; auto.
        exists (<@(<#D2 ++ [(x0, S)] ++ D1#>[-]x)[-]x0@>).
        split.
          rewrite <- subst_ee_fresh; auto.
          apply atyping_lvar; auto.
            apply wf_denv_lin_strengthening in Wf_denv'; auto.
            apply dmap_to_denv_is_uniq.
            apply Equal_trans with (m':=(<#D2 ++ [(x0, S)] ++ D1#>[-]x)[-]x0).
              apply Equal_trans with (m':=(<#D2 ++ [(x0, S)] ++ D1#>[-]x0)[-]x).
                apply dmap_remove_preserves_Equal.
                  apply Equal_sym.
                    apply denv_remove_mid.
                      apply uniq_from_wf_denv_lin in Wf_denv'; auto.
                apply dmap_remove_remove_commut.
              apply denv_to_from_dmap.
          apply Equal_trans with (m':=(<#D2 ++ [(x0, S)] ++ D1#>[-]x)[-]x0).
            apply Equal_sym.
               apply denv_to_from_dmap.
            apply dmap_remove_preserves_Equal; auto.
  Case "atyping_uabs".
    pick fresh y.
    assert (y `notin` dom <@(<#D2++D1#>--<#D'#>) |_| <#D3#>@>) as YnotinD.
      apply notIn_implies_notin_dom.
        intro J.
        apply update_in_iff in J.
        destruct J as [J | J].
          apply diff_in_iff in J.
          destruct J as [J1 J2].
          apply In_implies_in_dom in J1.
          contradict J1; auto.

          apply In_implies_in_dom in J.
          contradict J; auto.
    assert (y `notin` fv_ee (subst_ee x e' e1)) as HynotinSubst.
      apply notin_fv_ee_subst_ee; auto.
      auto.
    assert (wf_denv ([(y, gbind_typ V)]++G) <@(<#D2++D1#>--<#D'#>) |_| <#D3#>@>) as Wf_denv'.
      rewrite_env (nil++[(y, gbind_typ V)]++G).
      apply wf_denv_nonlin_weakening; auto.
        simpl_env.
        apply wf_genv_typ; auto.
    assert (
    (x `in` fv_ee(open_ee e1 y) -> 
       exists B3',
         atyping ([(y, gbind_typ V)]++G) <@ (<#D2++D1#> -- <#D'#>) |_| <#D3#> @> (subst_ee x e' (open_ee e1 y)) T1 B3' /\
         B3' ~~~ D3')
      /\
    (x `notin` fv_ee(open_ee e1 y) -> 
       exists B',
         atyping ([(y, gbind_typ V)]++G) (D2++D1) (subst_ee x e' (open_ee e1 y)) T1 B' /\
         <#B'#> ~~ <#D'#>[-]x)
    ) as IH.
     apply H1 with (S0:=S); auto.
      rewrite_env (nil ++ [(y, gbind_typ V)] ++ G).
      apply atyping_nonlin_weakening; auto.
        simpl_env.
        apply atyping_regular in Htyp'.
        decompose [and] Htyp'; auto.
        apply wf_denv_nonlin_weakening_head; auto.
    clear H1.
    destruct IH as [IHin IHnotin].
    split; intro J; simpl in J.
      (* x `in` \y. e1 *)
      assert (JJ := J).
      apply in_fv_ee_open_ee with (y:=y) in J; auto.
      apply IHin in J.
      destruct J as [B3' [Htyp'' B3'eqD3']].
      exists B3'. simpl.       
      split; auto.
        apply atyping_uabs with (L:=L `union` (fv_tt T1) `union` fv_ee (subst_ee x e' e1) `union` dom(G) `union` dom <@(<#D2++D1#>--<#D'#>) |_| <#D3#>@> `union` singleton y); auto.
          intros x0 Frx0.
          apply atyping_nonlin_term_renaming_head with (x:=y); auto.
            rewrite subst_ee_open_ee_var; auto.

            intro Keq. 
            apply H2 in Keq.
            assert (x `notin` dom D') as xnotinD'.
              assert (y `notin` L) as Frx0. auto.
              apply H0 in Frx0.
              apply denv_mono_disjoint with (x:=x) in Frx0; auto.
            apply notin_dom_implies_notIn in xnotinD'.
            assert (False) as FF.
              apply xnotinD'.
              eapply in_find_iff.
              rewrite <- Keq.
              eapply in_find_iff.
              apply in_dom_implies_In.
              rewrite dom_app. rewrite dom_app. 
              simpl. clear Fr. fsetdec.
            inversion FF.
      (* x `notin` \y. e1 *)
      apply notin_fv_ee_open_ee with (y:=y) in J; auto.
      apply IHnotin in J.
      destruct J as [B' [Htyp'' B'eqD']].
      exists B'. simpl.       
      split; auto.
        apply atyping_uabs with (L:=L `union` (fv_tt T1) `union` fv_ee (subst_ee x e' e1) `union` dom(G) `union` dom (D2++D1) `union` singleton y); auto.
          intros x0 Frx0.
          apply atyping_nonlin_term_renaming_head with (x:=y); auto.
            rewrite subst_ee_open_ee_var; auto.

            intro Keq. 
            apply H2 in Keq.
            apply Equal_trans with (m':= <#D'#>[-]x); auto.
              apply Equal_trans with (m':= <#D2++[(x,S)]++D1#>[-]x); auto.
                apply Equal_sym.
                  apply denv_remove_mid.
                    assert (y `notin` L) as Frx0. auto.
                    apply H0 in Frx0.
                    apply atyping_regular in Frx0.
                    decompose [and] Frx0.
                    apply uniq_from_wf_denv_lin in H4; auto.
                apply dmap_remove_preserves_Equal; auto.
              apply Equal_sym; auto.
  Case "atyping_labs".
    pick fresh y.
    assert (y `notin` dom <@(<#D2++D1#>--<#D'#>) |_| <#D3#>@>) as YnotinD.
      apply notIn_implies_notin_dom.
        intro J.
        apply update_in_iff in J.
        destruct J as [J | J].
          apply diff_in_iff in J.
          destruct J as [J1 J2].
          apply In_implies_in_dom in J1.
          contradict J1; auto.

          apply In_implies_in_dom in J.
          contradict J; auto.
    assert (uniq <@(<#[(y, V)]++D2++D1#>--<#D'#>) |_| <#D3#>@>) as UniqDD.
      apply dmap_to_denv_is_uniq.
    assert (<@(<#[(y, V)]++D2++D1#>--<#D'#>) |_| <#D3#>@> ~~~ 
            ([(y, V)]++<@(<#D2++D1#>--<#D'#>) |_| <#D3#>@>)
    ) as DDeq.
      apply Equal_trans with (m':=(<#[(y, V)]++D2++D1#>--<#D'#>) |_| <#D3#>).
        apply Equal_sym.
          apply denv_to_from_dmap.
        apply Equal_sym.
          apply dmap_Equal_rewrite_Union_left with (M1:=<#<@<#[(y, V)]++D2++D1#>--<#D'#>@>#>).
            apply Equal_sym.
              apply denv_to_from_dmap.
            apply dmap_Equal_rewrite_Union_left with (M1:=<#[(y, V)]++(<@<#D2++D1#>--<#D'#>@>)#>).
              apply Equal_sym.
                apply add_diff_commut; auto.
                  assert (y `notin` L) as Fry. auto.
                  apply H0 in Fry.
                  apply atyping_regular in Fry.
                  decompose [and] Fry.
                  apply uniq_from_wf_denv_lin in H5.
                  inversion H5; subst; auto.
                    simpl_env in H10.
                    apply uniq_remove_mid in H10; auto.
              apply dmap_Equal_rewrite_Union_left with (M1:=<#[(y, V)]#>|_|<#(<@<#D2++D1#>--<#D'#>@>)#>).
                apply Equal_sym.
                  apply disjoint_denv_cons_union.
                    apply uniq_push.
                      apply dmap_to_denv_is_uniq. 
                        apply notin_dom_diff; auto.
                          assert (y `notin` L) as Fry. auto.
                          apply H0 in Fry.
                          apply atyping_regular in Fry.
                          decompose [and] Fry.
                          apply uniq_from_wf_denv_lin in H5.
                          inversion H5; subst; auto.
                            simpl_env in H10.
                            apply uniq_remove_mid in H10; auto.
                apply Equal_trans with (m':=<#[(y, V)]#>|_|<#(<@<#D2++D1#>--<#D'#>|_|<#D3#>@>)#>).
                  apply disjoint_denv_cons_union.
                    apply uniq_push; auto.
                      apply dmap_to_denv_is_uniq. 
                  apply Equal_sym.                   
                    apply dmap_Equal_rewrite_Union_right with (M2:=(<#D2++D1#>--<#D'#>)|_|<#D3#>).
                      apply denv_to_from_dmap.
                      apply Equal_sym.                   
                        apply dmap_Equal_rewrite_Union_left with (M1:=<#[(y,V)]#>|_|(<#D2++D1#>--<#D'#>)).
                          apply dmap_Equal_rewrite_Union_right with (M2:=(<#D2++D1#>--<#D'#>)).
                            apply denv_to_from_dmap.
                            apply Equal_refl.
                          apply Equal_sym.
                            apply dmap_union_assoc.
    assert (y `notin` fv_ee (subst_ee x e' e1)) as HynotinSubst.
      apply notin_fv_ee_subst_ee; auto.
      auto.
    assert (
    (x `in` fv_ee(open_ee e1 y) -> 
       exists B3',
         atyping G <@ (<#([(y, V)]++D2)++D1#> -- <#D'#>) |_| <#D3#> @> (subst_ee x e' (open_ee e1 y)) T1 B3' /\
         B3' ~~~ D3')
      /\
    (x `notin` fv_ee(open_ee e1 y) -> 
       exists B',
         atyping G (([(y, V)]++D2)++D1) (subst_ee x e' (open_ee e1 y)) T1 B' /\
         <#B'#> ~~ <#D'#>[-]x)
    ) as IH.
     apply H1 with (S0:=S); auto.
       apply dmap_add_preserves_disjoint_left with (x:=y) (T:=V) in Disj; auto.
         simpl. apply dmap_Equal_preserves_disjoint_left with (M1:=y:::V[+](<#D2++D1#>--<#D'#>)); auto.
           apply Equal_sym.
             apply dmap_diff_distr; auto.
               apply notin_dom_implies_notIn; auto.
         apply notin_dom_implies_notIn; auto.
       apply wf_denv_typ with (x:=y) (T:=V) (D:=<@(<#D2++D1#>--<#D'#>) |_| <#D3#>@>) (K:=Q); auto.
         apply Equal_sym; auto.
    clear H1.
    destruct IH as [IHin IHnotin].
    split; intro J; simpl in J.
      (* x `in` \y. e1 *)
      assert (JJ := J).
      apply in_fv_ee_open_ee with (y:=y) in J; auto.
      apply IHin in J. clear IHin IHnotin.
      destruct J as [B3' [Htyp'' B3'eqD3']].
      assert (uniq ([(y, V)]++<@(<#D2++D1#>--<#D'#>) |_| <#D3#>@>)) as UniqDD'.
        apply uniq_push; auto.
          apply uniq_from_wf_denv_lin in Wf_denv; auto.
      apply atyping_permutation with (D1':=[(y, V)]++<@(<#D2++D1#>--<#D'#>) |_| <#D3#>@>) in Htyp''; auto.
      destruct Htyp'' as [B3'' [Htyp'' B3'eqB3'']].
      assert (y `notin` dom B3'') as YnotinB3''.
        apply notIn_implies_notin_dom2.
        intro J.
        apply in_find_iff in J.
        rewrite <- B3'eqB3'' in J.
        rewrite B3'eqD3' in J.
        apply in_find_iff in J.
        apply In_implies_in_dom in J.
        contradict J; auto.
      exists B3''. simpl.       
      split.
        apply atyping_labs with (L:=L `union` (fv_tt T1) `union` fv_ee (subst_ee x e' e1) `union` dom(G) `union` dom <@(<#D2++D1#>--<#D'#>) |_| <#D3#>@> `union` singleton y `union` dom B3') (Q:=Q); auto.
          intros x0 Frx0.
          rewrite <- subst_ee_open_ee_var in Htyp''; auto.
          apply atyping_lin_term_renaming_head_in with (x:=y); auto.
            assert (
              (y `in` fv_ee (open_ee (subst_ee x e' e1) y) /\ y `notin` dom B3'')    
                 \/    
              (y `notin` fv_ee (open_ee (subst_ee x e' e1) y) /\ y `in` dom B3'')
            ) as Mono.
              apply denv_mono_aux with (x:=y) in Htyp''.
                destruct Htyp'' as [[HH1 HH2]|[HH1 HH2]].
                  left. split; auto.
                  contradict HH2; auto.
              rewrite dom_app. simpl. clear Frx0. clear Fr.
                fsetdec.
            destruct Mono as [[HH1 HH2]|[HH1 HH2]]; auto.
              contradict HH2; auto.

          intro Keq. 
          apply H2 in Keq.
            assert (x `notin` dom D') as xnotinD'.
              assert (y `notin` L) as Frx0. auto.
              apply H0 in Frx0.
              apply denv_mono_disjoint with (x:=x) in Frx0; auto.
            apply notin_dom_implies_notIn in xnotinD'.
            assert (False) as FF.
              apply xnotinD'.
              eapply in_find_iff.
              rewrite <- Keq.
              eapply in_find_iff.
              apply in_dom_implies_In.
              rewrite dom_app. rewrite dom_app. 
              simpl. clear Fr. fsetdec.
            inversion FF.

          apply Equal_trans with (m':=<#B3'#>); auto.
            apply Equal_sym; auto.
      (* x `notin` \y. e1 *)
      apply notin_fv_ee_open_ee with (y:=y) in J; auto.
      apply IHnotin in J.
      destruct J as [B' [Htyp'' B'eqD']].
      assert (y `notin` dom B') as YnotinB'.
        apply notIn_implies_notin_dom2.
        intro J.
        apply in_find_iff in J.
        rewrite B'eqD' in J.
        apply in_find_iff in J.
        apply dmap_remove_in_noteq in J; auto.
          apply In_implies_in_dom in J.
          contradict J; auto.

          destruct_notin. auto.
      exists B'. simpl.       
      split; auto.
        apply atyping_labs with (L:=L `union` (fv_tt T1) `union` fv_ee (subst_ee x e' e1) `union` dom(G) `union` dom (D2++D1) `union` singleton y) (Q:=Q); auto.
          intros x0 Frx0.
          rewrite <- subst_ee_open_ee_var in Htyp''; auto.
          apply atyping_lin_term_renaming_head_in with (x:=y); auto.
            assert (
              (y `in` fv_ee (open_ee (subst_ee x e' e1) y) /\ y `notin` dom B')    
                 \/    
              (y `notin` fv_ee (open_ee (subst_ee x e' e1) y) /\ y `in` dom B')
            ) as Mono.
              apply denv_mono_aux with (x:=y) in Htyp''.
                destruct Htyp'' as [[HH1 HH2]|[HH1 HH2]].
                  left. split; auto.
                  contradict HH2; auto.
              rewrite dom_app. simpl. clear Frx0. clear Fr.
                fsetdec.
            destruct Mono as [[HH1 HH2]|[HH1 HH2]]; auto.
              contradict HH2; auto.

          intro Keq. 
          apply H2 in Keq.
          apply Equal_trans with (m':= <#D'#>[-]x); auto.
            apply Equal_trans with (m':= <#D2++[(x,S)]++D1#>[-]x); auto.
              apply Equal_sym.
                apply denv_remove_mid.
                  assert (y `notin` L) as Frx0. auto.
                  apply H0 in Frx0.
                  apply atyping_regular in Frx0.
                  decompose [and] Frx0.
                  apply uniq_from_wf_denv_lin in H4; auto.
                  inversion H4; subst; auto.
              apply dmap_remove_preserves_Equal; auto.
            apply Equal_sym; auto.
  Case "atyping_app".
    rename D4 into D11.
    rename D5 into D12.
    (* we first show some facts of ctx mono *)
    assert (<#D2#> <<= <#D12 ++ [(x, S)] ++ D11#>) as D2inD1.
      apply denv_mono in Htyp1; auto.
    assert (<#D3#> <<= <#D2#>) as D3inD2.
      apply denv_mono in Htyp2; auto.
    assert (((<#D12++D11#>--<#D2#>)|_|<#D0#>) <<= ((<#D12++D11#>--<#D3#>)|_|<#D0#>)) as Dsub.
      apply dmap_Sub_rewrite_Union_left.
        apply dmap_Sub_diff_right; auto.
    assert (<#D3'#> <<= <#D0#>) as D3'inD0.
      apply denv_mono in Htyp'; auto.
    assert (wf_denv G <@(<#D12++D11#>--<#D2#>)|_|<#D0#>@>) as Wf_denv'.
      apply wf_denv_lin_sub_strengthening with (D:=<@(<#D12++D11#>--<#D3#>)|_|<#D0#>@>); auto.
        apply dmap_Equal_rewrite_Sub_left with (M1:=(<#D12++D11#>--<#D2#>)|_|<#D0#>); auto.
          apply denv_to_from_dmap.
        apply dmap_Equal_rewrite_Sub_right with (M2:=(<#D12++D11#>--<#D3#>)|_|<#D0#>); auto.
          apply denv_to_from_dmap; auto.
            apply uniq_from_wf_denv_lin in Wf_denv; auto.
        apply dmap_to_denv_is_uniq.
    assert (
    (x `in` fv_ee e1 -> 
       exists B3',
         atyping G <@ (<#D12++D11#> -- <#D2#>) |_| <#D0#> @> (subst_ee x e' e1) (typ_arrow K T1 T2) B3' /\
         B3' ~~~ D3')
      /\
    (x `notin` fv_ee e1 -> 
       exists B2,
         atyping G (D12++D11) (subst_ee x e' e1) (typ_arrow K T1 T2) B2 /\
         <#B2#> ~~ <#D2#>[-]x)
    ) as IH1.
     apply IHHtyp1 with (S0:=S); auto.
       apply dmap_Sub_preserves_disjoint_left with (M1:=<#D12++D11#>--<#D3#>); auto.
         apply dmap_Sub_diff_right; auto.
    clear IHHtyp1.
    destruct IH1 as [IHHtyp1in IHHtyp1notin].
    assert (
    (x `in` fv_ee e1 /\ x `notin` fv_ee e2 /\ x `notin` dom D3)     
      \/    
    (x `notin` fv_ee e1 /\ x `in` fv_ee e2 /\ x `notin` dom D3)     
      \/    
    (x `notin` fv_ee e1 /\ x `notin` fv_ee e2 /\ x `in` dom D3)
    ) as Mono_app.
      assert (atyping G (D12 ++ [(x, S)] ++ D11) (exp_app e1 e2) T2 D3) as Htyp.
        eapply atyping_app; eauto.
      apply denv_mono_app with (x:=x) in Htyp; auto.
        rewrite dom_app. rewrite dom_app. simpl.
        fsetdec.
    rename xnotinD3 into xnotinD0.
    destruct Mono_app as [[xine1 [xnotine2 xnotinD3]] | 
                         [[xnotine1 [xine2 xnotinD3]] |
                          [xnotine1 [xnotine2 xinD3]]]].
    SCase "x in e1, x notin e2, x notin D3".
      (* IH1 *)
      assert (IHtyp1 := xine1).
      apply IHHtyp1in in IHtyp1. clear IHHtyp1in IHHtyp1notin.
      destruct IHtyp1 as [B3' [IHtyp1 B3'eqD3']].

      (* IH1 weakening *)
      assert (<@(<#<@<#D12++D11#>--<#D2#>@>#>|_|<#<@<#<@<#D2#>--<#D3#>@>#>|_|<#D0#>@>#>)@> ~~~ <@(<#D12++D11#>--<#D3#>)|_|<#D0#>@>) as EQ1'.           
            apply Equal_trans with (m':=<#<@<#D12++D11#>--<#D3#>@>#>|_|<#D0#>).
              apply Equal_trans with (m':=<#<@<#D12++D11#>--<#D2#>@>#>|_|<#<@<#<@<#D2#>--<#D3#>@>#>|_|<#D0#>@>#>).
                apply Equal_sym.
                  apply denv_to_from_dmap.
                apply Equal_trans with (m':=<#<@<#D12++D11#>--<#D2#>@>#>|_|<#<@<#D2#>--<#D3#>@>#>|_|<#D0#>); auto.
                  apply Equal_sym.
                    apply dmap_Equal_rewrite_Union_right with (M2:=<#<@<#D2#>--<#D3#>@>#>|_|<#D0#>).
                      apply denv_to_from_dmap.
                      apply Equal_refl.
                  apply Equal_trans with (m':=(<#D12++D11#>--<#D2#>)|_|<#<@<#D2#>--<#D3#>@>#>|_|<#D0#>); auto.
                    apply dmap_Equal_rewrite_Union_left with (M1:=<#<@<#D12++D11#>--<#D2#>@>#>).
                      apply Equal_sym.
                        apply denv_to_from_dmap.
                      apply Equal_refl.
                    apply Equal_trans with (m':=(<#D12++D11#>--<#D2#>)|_|(<#D2#>--<#D3#>)|_|<#D0#>); auto.
                      apply dmap_Equal_rewrite_Union_right with (M2:=<#<@<#D2#>--<#D3#>@>#>|_|<#D0#>).
                        apply dmap_Equal_rewrite_Union_left with (M1:=<#<@<#D2#>--<#D3#>@>#>).
                          apply Equal_sym.
                            apply denv_to_from_dmap.
                          apply Equal_refl.
                        apply Equal_refl.
                  apply dmap_Equal_rewrite_Union_left with (M1:=(<#D12++D11#>--<#D2#>)|_|(<#D2#>--<#D3#>)).
                    apply Equal_trans with (m':=(<#D12++D11#>--<#D3#>)).
                      apply dmap_diff_merge; auto.
                        apply dmap_remove_preserves_Sub_right with (x:=x) in D2inD1.
                          apply dmap_Equal_rewrite_Sub_right with (M2:=<#D12++[(x,S)]++D11#>[-]x).
                            apply denv_remove_mid.
                              apply atyping_regular in Htyp1.
                              decompose [and] Htyp1.
                              apply uniq_from_wf_denv_lin in H1; auto.
                            apply dmap_Equal_rewrite_Sub_left with (M1:=<#D2#>[-]x); auto.
                              apply Equal_sym.
                                apply dmap_remove_refl.
                                  apply denv_mono_disjoint with (x:=x) in Htyp1; auto.
                                    apply notin_dom_implies_notIn; auto.
                      apply denv_to_from_dmap.
                    apply Equal_sym.
                      apply dmap_union_assoc.
              apply Equal_trans with (m':=(<#D12++D11#>--<#D3#>|_|<#D0#>)).
                apply dmap_Equal_rewrite_Union_left with (M1:=<#<@(<#D12++D11#>--<#D3#>)@>#>).
                  apply Equal_sym.
                    apply denv_to_from_dmap.
                  apply Equal_refl.                  
                apply denv_to_from_dmap.
      assert (<#D12++[(x,S)]++D11#>--<#D3#> ** <#D0#>) as Disj2'.
        apply dmap_Equal_preserves_disjoint_left with (M1:=x:::S[+](<#D12++D11#>--<#D3#>)); auto.
          apply Disjoint_sym.
            apply dmap_disjoint_cons.
              apply notin_dom_implies_notIn; auto.
              apply Disjoint_sym; auto.
          apply Equal_trans with (m':=(<#[(x,S)]++D12++D11#>--<#D3#>)); auto.
            apply dmap_Equal_rewrite_diff_left with (M1:=<#D12++[(x,S)]++D11#>).
              rewrite_env (nil ++ D12++nil++[(x,S)]++D11).
              rewrite_env (nil ++ [(x,S)]++nil++D12++D11).
              apply disjoint_denv_cons_commut_aux; simpl_env.
                apply atyping_regular in Htyp1.
                decompose [and] Htyp1.
                apply uniq_from_wf_denv_lin in H1. auto.

              apply Equal_refl.
            simpl. apply Equal_sym.
              apply dmap_diff_distr; auto.
                apply notin_dom_implies_notIn; auto.
      assert (<#<@<#D2#>--<#D3#>@>#> ** <#D0#>) as Disj2.
        apply dmap_Sub_preserves_disjoint_left with (M1:=<#D12++[(x,S)]++D11#>--<#D3#>); auto.
          apply dmap_Equal_rewrite_Sub_left with (M1:=<#D2#>--<#D3#>).
            apply denv_to_from_dmap.
            apply dmap_Sub_diff_left with (M1:=<#D2#>); auto.
      assert (<@(<#<@<#D12++D11#>--<#D2#>|_|<#D0#>@>#>)|_|(<#<@<#D2#>--<#D3#>@>#>)@> ~~~ <@(<#D12++D11#>--<#D3#>)|_|<#D0#>@>) as EQ1.
        apply Equal_trans with (m':=<#<@(<#<@<#D12++D11#>--<#D2#>@>#>|_|<#<@<#<@<#D2#>--<#D3#>@>#>|_|<#D0#>@>#>)@>#>); auto.
          apply dmap_denv_Equal_injection_add.
            apply dmap_Equal_rewrite_Union_right with (M2:=<#<@<#D2#>--<#D3#>@>#>|_|<#D0#>).
              apply denv_to_from_dmap.
              apply dmap_Equal_rewrite_Union_left with (M1:=<#D12++D11#>--<#D2#>).
                apply denv_to_from_dmap.
                apply Equal_sym.
                  apply dmap_Equal_rewrite_Union_left with (M1:=<#D12++D11#>--<#D2#>|_|<#D0#>).
                    apply denv_to_from_dmap.
                    apply Equal_trans with (m':=(<#D12++D11#>--<#D2#>)|_|(<#D0#>|_|<#<@<#D2#>--<#D3#>@>#>)); auto.
                      apply dmap_Equal_rewrite_Union_right with (M2:=<#<@<#D2#>--<#D3#>@>#>|_|<#D0#>).
                        apply dmap_union_sym; auto.
                        apply Equal_refl.
                      apply Equal_sym.
                        apply dmap_union_assoc.
      assert (wf_denv G <@(<#<@<#D12++D11#>--<#D2#>|_|<#D0#>@>#>)|_|(<#<@<#D2#>--<#D3#>@>#>)@>) as Wf_denv_union1.
        apply denv_permutation with (D:=<@(<#D12++D11#>--<#D3#>)|_|<#D0#>@>); auto.
          apply dmap_to_denv_is_uniq.
          apply Equal_sym; auto.
      assert (<#<@<#D12++D11#>--<#D2#>|_|<#D0#>@>#> ** (<#<@<#D2#>--<#D3#>@>#>)) as Disj1.
        apply dmap_denv_diff_injection_add.
          apply Disjoint_sym.
            apply dmap_disjoint_app.
              apply Disjoint_sym.            
                apply dmap_Sub_preserves_disjoint_right with (M2:=<#D2#>).
                  apply diff_disjoint.
                  apply dmap_diff_mono.
              apply dmap_Equal_preserves_disjoint_left with (M1:=<#<@<#D2#>--<#D3#>@>#>); auto.
                apply denv_to_from_dmap.
      assert (uniq <@<#D2#>--<#D3#>@>) as Uniq2'.
        apply dmap_to_denv_is_uniq.
      apply atyping_lin_union_weakening with (D:=<@<#D2#>--<#D3#>@>) in IHtyp1; auto.
      destruct IHtyp1 as [E2'' [IHtyp1 EqE2'']].
      assert (uniq <@(<#D12++D11#>--<#D3#>)|_|<#D0#>@>) as Uniq1'.
        apply dmap_to_denv_is_uniq.
      apply atyping_permutation with (D1':=<@(<#D12++D11#>--<#D3#>)|_|<#D0#>@>) in IHtyp1; auto.
      destruct IHtyp1 as [D2'' [IHtyp1 EqD2'']].
      clear EQ1 EQ1' Uniq2' Uniq1' Disj1 Wf_denv_union1.

      (* IH2 strengthening *)
      assert (forall x0, x0 `in` fv_ee e2 -> x0 `notin` dom D3) as Diff2.
        intros x0 Hx0ine2.
        apply denv_mono_disjoint with (x:=x0) in Htyp2; auto.
      apply atyping_lin_diff_strengthening with (D:=D3) in Htyp2; auto.
      destruct Htyp2 as [D3'' [Htyp2 EmptyeqD3'']].
      clear Diff2.

      (* IH2 weakening *)
      assert (x `notin` dom <@(<#D12++D11#>--<#D3#>) |_| <#D0#>@>) as xnotinD.
        apply notIn_implies_notin_dom.
          intro J.
          apply update_in_iff in J.
          destruct J as [J | J].
            apply diff_in_iff in J.
            destruct J as [J1 J2].
            apply In_implies_in_dom in J1.
            apply atyping_regular in Htyp1; auto.
            decompose [and] Htyp1.
            apply uniq_from_wf_denv_lin in H1; auto.
            assert (J := H1).
            apply fresh_mid_tail in H1.
            apply fresh_mid_head in J.
            contradict J1; auto.

            apply In_implies_in_dom in J.
            contradict J; auto.
      assert ([(x,S)]++<@<#D12++D11#>--<#D3#>|_|<#D0#>@> ~~~ <@<#D12++[(x,S)]++D11#>--<#D3#>|_|<#D0#>@>) as EQ.
        apply Equal_trans with (m':=<#D12++[(x,S)]++D11#>--<#D3#>|_|<#D0#>); auto.        
          apply dmap_Equal_rewrite_Union_left with (M1:=x:::S[+](<#D12++D11#>--<#D3#>)); auto.
            apply Equal_trans with (m':=(<#[(x,S)]++D12++D11#>--<#D3#>)); auto.
              simpl.
              apply dmap_diff_distr; auto.
                apply notin_dom_implies_notIn; auto.

              apply dmap_Equal_rewrite_diff_left with (M1:=<#[(x,S)]++D12++D11#>).
                rewrite_env (nil ++ D12++nil++[(x,S)]++D11).
                rewrite_env (nil ++ [(x,S)]++nil++D12++D11).
                apply disjoint_denv_cons_commut_aux; simpl_env.
                  apply atyping_regular in Htyp1.
                  decompose [and] Htyp1.
                  apply uniq_from_wf_denv_lin in H1.
                  apply uniq_push; auto.
                    apply uniq_remove_mid in H1; auto.
                    assert (J:=H1).
                    apply fresh_mid_tail in H1.
                    apply fresh_mid_head in J.
                    rewrite dom_app. fsetdec.

                apply Equal_refl.

              simpl. apply Equal_trans with (m':=(x:::S[+]((<#D12++D11#>--<#D3#>) |_| <#D0#>))).
                apply dmap_Equal_rewrite_add_right.
                  apply Equal_sym.
                    apply denv_to_from_dmap.
                apply dmap_union_add_distr_left.
                  apply notin_dom_implies_notIn; auto.
             apply denv_to_from_dmap.
      assert (wf_denv G <@<#D12++[(x,S)]++D11#>--<#D3#>|_|<#D0#>@>) as Wf_denv''.
        assert (exists K, wf_atyp G S K) as Wf_atyp.
          apply atyping_regular in Htyp'.
          decompose [and] Htyp'; auto.
        destruct Wf_atyp as [Q Wf_atyp].
        apply denv_permutation with (D:=[(x,S)]++<@<#D12++D11#>--<#D3#>|_|<#D0#>@>); auto.
          apply wf_denv_typ with (x:=x) (T:=S) (D:=<@<#D12++D11#>--<#D3#>|_|<#D0#>@>) (K:=Q); auto.
            apply denv_dom_dinv with (D:=D12++[(x,S)]++D11).
              apply atyping_regular in Htyp'.
              decompose [and] Htyp'; auto.

              rewrite dom_app. rewrite dom_app. simpl. fsetdec.
            apply uniq_push; auto.
              apply dmap_to_denv_is_uniq.
            apply Equal_refl.
          apply dmap_to_denv_is_uniq.
      assert (wf_denv G <@(<#<@<#D2#>--<#D3#>@>#>|_|<#D3'#>)@>) as Wf_denv_union2.
        apply wf_denv_lin_sub_strengthening with (D:=<@<#D12++[(x,S)]++D11#>--<#D3#>|_|<#D0#>@>); auto.         
          apply dmap_denv_Sub_injection_add.
            apply dmap_Sub_trans with (M':=<#D12++[(x,S)]++D11#>--<#D3#>|_|<#D3'#>).
              apply dmap_Sub_rewrite_Union_left with (M1:=<#<@<#D2#>--<#D3#>@>#>).
                apply dmap_Equal_rewrite_Sub_left with (M1:=<#<@<#D2#>--<#D3#>@>#>).
                  apply Equal_refl.                    
                  apply dmap_Equal_rewrite_Sub_left with (M1:=<#D2#>--<#D3#>).
                    apply denv_to_from_dmap.
                    apply dmap_Sub_diff_left; auto.
              apply dmap_Sub_rewrite_Union_right with (M2:=<#D3'#>); auto.
          apply dmap_to_denv_is_uniq.
       assert (<#<@<#D2#>--<#D3#>@>#> ** <#D3'#>) as Disj2''.
         apply dmap_Sub_preserves_disjoint_left with (M1:=<#D12++[(x,S)]++D11#>--<#D3#>).
           apply dmap_Sub_preserves_disjoint_right with (M2:=<#D0#>); auto.
           apply dmap_Equal_rewrite_Sub_left with (M1:=<#D2#>--<#D3#>).
             apply denv_to_from_dmap.
             apply dmap_Sub_diff_left with (M1:=<#D2#>); auto.
       assert (uniq D3') as Uniq3'.
            apply atyping_regular in Htyp'.
            decompose [and] Htyp'.
            apply uniq_from_wf_denv_lin in H0; auto.
       apply atyping_lin_union_weakening with (D:=D3') in Htyp2; auto.
       destruct Htyp2 as [E3''' [Htyp2 EqE3''']].
       clear Disj2'' Uniq3' Disj2' Wf_denv_union2.

       (* By atyping_app *)
       assert (uniq D2'') as Uniq2''.
         apply atyping_regular in IHtyp1.
         decompose [and] IHtyp1.
         apply uniq_from_wf_denv_lin in H0; auto.
       assert (<@<#<@<#D2#>--<#D3#>@>#> |_| <#D3'#>@> ~~~ D2'') as EQ'.
         apply Equal_trans with (m':=<#E2''#>); auto.
           apply Equal_trans with (m':=<#<@<#B3'#>|_|<#<@<#D2#>--<#D3#>@>#>@>#>); auto.
             apply dmap_denv_Equal_injection_add.
               apply Equal_trans with (m':=<#<@<#D2#>--<#D3#>@>#>|_|<#B3'#>).
                 apply dmap_Equal_rewrite_Union_right with (M2:=<#D3'#>).
                   apply Equal_sym; auto.
                   apply Equal_refl.
                 apply dmap_union_sym.
                   apply dmap_Sub_preserves_disjoint_right with (M2:=<#D0#>).
                     apply dmap_Sub_preserves_disjoint_left with (M1:=<#D12++D11#>--<#D3#>); auto.
                       apply dmap_Equal_rewrite_Sub_left with (M1:=<#D2#>--<#D3#>).
                         apply denv_to_from_dmap.            
                         apply dmap_Sub_diff_left.
                           apply dmap_remove_preserves_Sub_right with (x:=x) in D2inD1; auto.
                             apply dmap_Equal_rewrite_Sub_left with (M1:=<#D2#>[-]x).
                               apply Equal_sym.
                                 apply dmap_remove_refl.
                                   apply denv_mono_disjoint with (x:=x) in Htyp1; auto.
                                     apply notin_dom_implies_notIn; auto.
                               apply dmap_Equal_rewrite_Sub_right with (M2:=<#D12++[(x,S)]++D11#>[-]x); auto.
                                 apply denv_remove_mid.
                                   apply atyping_regular in Htyp1.
                                   decompose [and] Htyp1.
                                   apply uniq_from_wf_denv_lin in H1; auto. 
                     apply dmap_Equal_rewrite_Sub_left with (M1:=<#D3'#>); auto.
             apply Equal_sym; auto.
           apply Equal_sym; auto.
       apply atyping_permutation with (D1':=D2'') in Htyp2; auto.
       destruct Htyp2 as [D2''' [Htyp2 EqD2''']].

      (* atyping_app *)
      split; intro J.
        (* x `in` fv_ee (exp_app e1 e2) *)
         exists (D2''').
         split.
            simpl.
            rewrite subst_ee_fresh with (x:=x) (u:=e') (e:=e2) in Htyp2; auto.
            apply atyping_app with (T1:=T1) (K:=K) (D2:=D2''); auto.

            apply Equal_trans with (m':=<#E3'''#>).
              apply Equal_sym; auto.
              apply Equal_trans with (m':=<#<@<#D3''#>|_|<#D3'#>@>#>); auto.
                apply Equal_trans with (m':=<#D3''#>|_|<#D3'#>).
                  apply Equal_sym.
                    apply denv_to_from_dmap.
                  apply Equal_sym.
                    apply dmap_Equal_rewrite_Union_left with (M1:=@@).
                      apply Equal_trans with (m':=<#<@<#D3#>--<#D3#>@>#>).
                        apply Equal_trans with (m':=<#D3#>--<#D3#>).
                          apply Equal_sym.
                            apply dmap_diff_refl.
                          apply denv_to_from_dmap.
                        apply Equal_sym; auto.
                      apply Equal_sym.
                        apply dmap_union_empty_refl.
        (* x `notin` fv_ee (exp_app e1 e2) *)
        simpl in J.
        destruct_notin.
        contradict xine1; auto.
    SCase "x notin e1, x in e2, x notin D3".
      (* IH1 *)
      assert (IHtyp1 := xnotine1).
      apply IHHtyp1notin in IHtyp1. clear IHHtyp1in IHHtyp1notin.
      destruct IHtyp1 as [B2 [IHtyp1 B2eqD2_x]].

      (* IH2 *)
      (* first of all, x must be in D2 *)
      assert (
      (x `in` fv_ee e1 /\ x `notin` dom D2)     
        \/    
      (x `notin` fv_ee e1 /\ binds x S D2)
      ) as Mono_binds.
        apply denv_mono_binds with (x:=x) (V:=S) in Htyp1; auto.
      destruct Mono_binds as [[xine1 xnotinD2]|[xnotine1' xbindsD2]].
        contradict xine1; auto.

        apply binds_inv in xbindsD2.
        destruct xbindsD2 as [D21 [D22 xbindsD]]; subst.
        assert (<#D22++D21#> <<= <#D12++D11#>) as Dsub''.
              apply dmap_remove_preserves_Sub in D2inD1; auto.
                apply atyping_regular in Htyp1.
                decompose [and] Htyp1.
                apply uniq_from_wf_denv_lin in H0; auto.

                apply atyping_regular in Htyp1.
                decompose [and] Htyp1.
                apply uniq_from_wf_denv_lin in H1; auto.
        assert (((<#D22++D21#>--<#D3#>)|_|<#D0#>) <<= ((<#D12++D11#>--<#D3#>)|_|<#D0#>)) as Dsub'.
          apply dmap_Sub_rewrite_Union_left.
            apply dmap_Sub_diff_left; auto.
        assert (wf_denv G <@(<#D22++D21#>--<#D3#>)|_|<#D0#>@>) as Wf_denv''.
          apply wf_denv_lin_sub_strengthening with (D:=<@(<#D12++D11#>--<#D3#>)|_|<#D0#>@>); auto.
            apply dmap_Equal_rewrite_Sub_left with (M1:=(<#D22++D21#>--<#D3#>)|_|<#D0#>); auto.
              apply denv_to_from_dmap.
            apply dmap_Equal_rewrite_Sub_right with (M2:=(<#D12++D11#>--<#D3#>)|_|<#D0#>); auto.
              apply denv_to_from_dmap; auto.
                apply uniq_from_wf_denv_lin in Wf_denv; auto.
            apply dmap_to_denv_is_uniq.
        assert (
        (x `in` fv_ee e2 -> 
           exists B3',
             atyping G <@ (<#D22++D21#> -- <#D3#>) |_| <#D0#> @> (subst_ee x e' e2) T1 B3' /\
             B3' ~~~ D3')
          /\
        (x `notin` fv_ee e2 -> 
           exists B3,
             atyping G (D22++D21) (subst_ee x e' e2) T1 B3 /\
             <#B3#> ~~ <#D3#>[-]x)
        ) as IH2.
         apply IHHtyp2 with (S0:=S); auto.
           apply dmap_Sub_preserves_disjoint_left with (M1:=<#D12++D11#>--<#D3#>); auto.
             apply dmap_Sub_diff_left; auto.
        clear IHHtyp2.     
        destruct IH2 as [IHHtyp2in IHHtyp2notin].
        split; intro J.
        (* x `in` fv_ee (exp_app e1 e2) *)
           assert (IHtyp2 := xine2).
           apply IHHtyp2in in IHtyp2. clear IHHtyp2in IHHtyp2notin.
           destruct IHtyp2 as [B3 [IHtyp2 B3eqD3']].

          (* IH1 strengthening *)
          assert (forall x0, x0 `in` fv_ee (subst_ee x e' e1) -> x0 `notin` dom D3) as Diff1.
            intros x0 Hx0insubst1.
            rewrite <- subst_ee_fresh in Hx0insubst1; auto.
            assert (atyping G (D12++[(x,S)]++D11) (exp_app e1 e2) T2 D3) as Htyp12.
              eapply atyping_app with (D2:=D22++[(x,S)]++D21) (T1:=T1) (K:=K); eauto.
            apply denv_mono_disjoint with (x:=x0) in Htyp12; auto.
              simpl. fsetdec.
          apply atyping_lin_diff_strengthening with (D:=D3) in IHtyp1; auto.
          destruct IHtyp1 as [D2' [IHtyp1 eqD2']].
          clear Diff1.

          (* IH1 weakening *)
          assert (wf_denv G <@(<#<@<#D12++D11#>--<#D3#>@>#>|_|<#D0#>)@>) as Wf_denv_union1.
            apply denv_permutation with (D:=<@(<#D12++D11#>--<#D3#>)|_|<#D0#>@>); auto.
              apply dmap_to_denv_is_uniq.
              apply dmap_denv_Equal_injection_add.
                apply dmap_Equal_rewrite_Union_left with (M1:=<#D12++D11#>--<#D3#>); auto.
                  apply denv_to_from_dmap.  
                  apply Equal_refl.
          assert (<#<@<#D12++D11#>--<#D3#>@>#> ** <#D0#>) as Disj1.
            apply dmap_Equal_preserves_disjoint_left with (M1:=<#D12++D11#>--<#D3#>); auto.
              apply Equal_sym.
                apply denv_to_from_dmap.
          assert (uniq D0) as uniqD0.
            apply atyping_regular in Htyp'.
            decompose [and] Htyp'.
            apply uniq_from_wf_denv_lin in H1; auto.
          apply atyping_lin_union_weakening with (D:=D0) in IHtyp1; auto.
          destruct IHtyp1 as [E2'' [IHtyp1 EqE2'']].
          assert (<@(<#<@<#D12++D11#>--<#D3#>@>#>|_|<#D0#>)@> ~~~ <@((<#D12++D11#>--<#D3#>)|_|<#D0#>)@>) as EQ1.
            apply dmap_denv_Equal_injection_add.  
            apply dmap_Equal_rewrite_Union_left with (M1:=<#D12++D11#>--<#D3#>); auto. 
              apply Equal_refl.
              apply dmap_Equal_rewrite_Union_left with (M1:=<#<@<#D12++D11#>--<#D3#>@>#>); auto. 
                apply Equal_sym.
                  apply denv_to_from_dmap.
                apply Equal_refl.
          apply atyping_permutation with (D1':=<@((<#D12++D11#>--<#D3#>)|_|<#D0#>)@>) in IHtyp1; 
            try solve [auto | apply dmap_to_denv_is_uniq].
          destruct IHtyp1 as [D2'' [IHtyp1 EqD2'']].
          clear EQ1.
          clear Disj1 Wf_denv_union1.

          (* for typ2 *)
          assert (<@(<#D22++D21#>--<#D3#>)|_|<#D0#>@> ~~~ D2'') as EQ2.
            eapply Equal_trans with (m':=<#E2''#>); auto.
              eapply Equal_trans with (m':=<#<@<#D2'#>|_|<#D0#>@>#>); auto.
                apply dmap_denv_Equal_injection_add.  
                  apply dmap_Equal_rewrite_Union_left with (M1:=<#D22++D21#>--<#D3#>); auto. 
                    apply Equal_sym. 
                      apply Equal_trans with (m':=<#<@<#B2#>--<#D3#>@>#>); auto.
                        apply Equal_trans with (m':=<#B2#>--<#D3#>); auto.
                          apply Equal_sym.
                            apply denv_to_from_dmap.
                          apply dmap_Equal_rewrite_diff_left with (M1:=<#D22++[(x,S)]++D21#>[-]x); auto. 
                            apply denv_remove_mid.
                              apply atyping_regular in Htyp1.
                              decompose [and] Htyp1.
                              apply uniq_from_wf_denv_lin in H0; auto.
                            apply dmap_Equal_rewrite_diff_left with (M1:=<#B2#>); auto. 
                             apply Equal_refl.
                    apply Equal_refl.
                apply Equal_sym; auto.
          assert (uniq D2'') as uniqD2''.
            apply atyping_regular in IHtyp1.
            decompose [and] IHtyp1.
            apply uniq_from_wf_denv_lin in H0; auto.
          apply atyping_permutation with (D1':=D2'') in IHtyp2; 
            try solve [auto | apply dmap_to_denv_is_uniq].
          destruct IHtyp2 as [C3'' [IHtyp2 EqC2'']].
          clear EQ2 uniqD2''.

          (* By atyping_app *)
          simpl. exists C3''.
          split; auto.
            apply atyping_app with (T1:=T1) (K:=K) (D2:=D2''); auto.
            apply Equal_trans with (m':=<#B3#>); auto.
              apply Equal_sym; auto. 
        (* x `notin` fv_ee (exp_app e1 e2) *)
           simpl in J.
           destruct_notin.
           contradict xine2; auto.
    SCase "x notin e1, x notin e2, x in D3".
      (* IH1 *)
      assert (IHtyp1 := xnotine1).
      apply IHHtyp1notin in IHtyp1. clear IHHtyp1in IHHtyp1notin.
      destruct IHtyp1 as [B2 [IHtyp1 B2eqD2_x]].

      (* IH2 strengthening *)
      assert (forall x0, x0 `in` fv_ee e2 -> x0 `notin` dom[(x, S)]) as Diff2.
        intros x0 Hx0ine2.
        destruct (x0 == x); subst; auto.
      apply atyping_lin_diff_strengthening with (D:=[(x,S)]) in Htyp2; auto.
      destruct Htyp2 as [B3 [Htyp2 B3eqD3_x]].
      assert (uniq B2) as UniqB2.
        apply atyping_regular in IHtyp1.
        decompose [and] IHtyp1.
        apply uniq_from_wf_denv_lin in H0; auto.
      assert (<@<#D2#>--<#[(x,S)]#>@> ~~~ B2) as EQ2.
        apply Equal_trans with (m':=<#D2#>[-]x).
          apply Equal_trans with (m':=<#D2#>--<#[(x,S)]#>).
            apply Equal_sym.
              apply denv_to_from_dmap.
            apply Equal_sym.
              apply remove_is_singleton_diff.
          apply Equal_sym; auto.
      apply atyping_permutation with (D1':=B2) in Htyp2; auto.
      destruct Htyp2 as [C3 [Htyp2 C3eqB3]].
      clear Diff2 EQ2.

      (* atyping_app *)
      split; intro J.
        (* x `in` fv_ee (exp_app e1 e2) *)
        simpl in J.
        assert (x `in` fv_ee e1 \/ x `in` fv_ee e2) as JJ. fsetdec.
        destruct JJ as [JJ | JJ].
          contradict JJ; auto.
          contradict JJ; auto.
        (* x `notin` fv_ee (exp_app e1 e2) *)
        exists C3.
        split.
          simpl. 
          rewrite subst_ee_fresh with (x:=x) (u:=e') (e:=e2) in Htyp2; auto.
          apply atyping_app with (T1:=T1) (K:=K) (D2:=B2); auto.

          apply Equal_trans with (m':=<#B3#>).
            apply Equal_sym; auto.
            apply Equal_trans with (m':=<#D3#>--<#[(x,S)]#>).
              apply Equal_trans with (m':=<#<@<#D3#>--<#[(x,S)]#>@>#>); auto.
                apply Equal_sym.
                  apply denv_to_from_dmap.
              apply Equal_sym.
                apply remove_is_singleton_diff.
  Case "atyping_tabs".
    pick fresh Y.
    assert (Y `notin` dom <@(<#D2++D1#>--<#D'#>) |_| <#D3#>@>) as YnotinD.
      apply notIn_implies_notin_dom.
        intro J.
        apply update_in_iff in J.
        destruct J as [J | J].
          apply diff_in_iff in J.
          destruct J as [J1 J2].
          apply In_implies_in_dom in J1.
          contradict J1; auto.

          apply In_implies_in_dom in J.
          contradict J; auto.
    assert (Y `notin` denv_fv_tt (D2 ++ D1)) as HH.
      rewrite denv_fv_tt_app. auto.
    assert (Y `notin` denv_fv_tt <@(<#D2++D1#>--<#D'#>) |_| <#D3#>@>) as YnotinD'.
      assert (Y `notin` denv_fv_tt <@<#D2++D1#> -- <#D'#>@>) as K''.
        apply notin_denv_fv_tt_diff; auto.
          assert (Y `notin` L) as J. auto.
          apply H0 in J. apply atyping_regular in J.
          decompose [and] J. 
          apply uniq_from_wf_denv_lin in H4; auto.
          apply uniq_remove_mid in H4; auto.
      assert (Y `notin` denv_fv_tt <@<#D2++D1#> -- <#D'#>@> /\ Y `notin` denv_fv_tt D3) as K'. 
        auto.
      apply notin_denv_fv_tt_union in K'; auto.
        apply dmap_to_denv_is_uniq.

        apply atyping_regular in Htyp'.
        decompose [and] Htyp'.
        apply uniq_from_wf_denv_lin in H4; auto.

        apply dmap_Equal_preserves_disjoint_left with (M1:=<#D2++D1#>--<#D'#>); auto.
          apply Equal_sym.
            apply denv_to_from_dmap.
      assert (<@(<#D2++D1#>--<#D'#>) |_| <#D3#>@> ~~~ <@(<#<@<#D2++D1#>--<#D'#>@>#>) |_| <#D3#>@>) as EQ.
        apply dmap_denv_Equal_injection_add.
          apply dmap_Equal_rewrite_Union_left with (M1:=<#D2++D1#>--<#D'#>); auto.
            apply denv_to_from_dmap.
            apply Equal_refl.
      apply dmap_eq__denv_fv_tt_eq_notin with (X:=Y) in EQ; auto.
        apply dmap_to_denv_is_uniq.
        apply dmap_to_denv_is_uniq.
    assert (Y `notin` fv_te (subst_ee x e' e1)) as HynotinSubst.
      apply notin_fv_te_subst_ee; auto.
      auto.
    assert (wf_denv ([(Y, gbind_kn K)]++G) <@(<#D2++D1#>--<#D'#>) |_| <#D3#>@>) as Wf_denv'.
      rewrite_env (nil++[(Y, gbind_kn K)]++G).
      apply wf_denv_nonlin_weakening; auto.
        simpl_env.
        apply wf_genv_kn; auto.
    assert (
    (x `in` fv_ee(open_te e1 Y) -> 
       exists B3',
         atyping ([(Y, gbind_kn K)]++G) <@ (<#D2++D1#> -- <#D'#>) |_| <#D3#> @> (subst_ee x e' (open_te e1 Y)) (open_tt T1 Y) B3' /\
         B3' ~~~ D3')
      /\
    (x `notin` fv_ee(open_te e1 Y) -> 
       exists B',
         atyping ([(Y, gbind_kn K)]++G) (D2++D1) (subst_ee x e' (open_te e1 Y)) (open_tt T1 Y) B' /\
         <#B'#> ~~ <#D'#>[-]x)
    ) as IH.
     apply H1 with (S0:=S); auto.
      rewrite_env (nil ++ [(Y, gbind_kn K)] ++ G).
      apply atyping_nonlin_weakening; auto.
        simpl_env.
        apply atyping_regular in Htyp'.
        decompose [and] Htyp'; auto.
        apply wf_denv_nonlin_weakening_head; auto.
    clear H1.
    destruct IH as [IHin IHnotin].
    split; intro J; simpl in J.
      (* x `in` \y. e1 *)
      apply in_fv_ee_open_te with (Y:=Y) in J; auto.
      apply IHin in J.
      destruct J as [B3' [Htyp'' B3'eqD3']].
      exists B3'. simpl.       
      split; auto.
        apply atyping_tabs with (L:=L `union` (fv_tt T1) `union` fv_te (subst_ee x e' e1) 
                                      `union` dom(G) `union` dom <@(<#D2++D1#>--<#D'#>) |_| <#D3#>@> 
                                      `union` denv_fv_tt <@(<#D2++D1#>--<#D'#>) |_| <#D3#>@> 
                                      `union` singleton Y); auto.
          intros X FrX.
          assert (X `notin` L) as XnL. clear - FrX. auto.
          apply H in XnL.
          rewrite subst_ee_open_te_var; eauto using type_from_wf_atyp.
          apply value_through_subst_ee; auto.

          intros X0 FrX0.
          apply atyping_nonlin_typ_renaming with (X:=Y).
            clear FrX0. destruct_notin. fsetdec.

            clear Fr. destruct_notin. fsetdec.

            clear Fr. destruct_notin. auto.

            rewrite subst_ee_open_te_var; auto.
      (* x `notin` \y. e1 *)
      apply notin_fv_ee_open_te with (Y:=Y) in J; auto.
      apply IHnotin in J.
      destruct J as [B' [Htyp'' B'eqD']].
      exists B'. simpl.       
      split; auto.
        apply atyping_tabs with (L:=L `union` (fv_tt T1) `union` fv_te (subst_ee x e' e1) 
                                      `union` dom G `union` dom (D2++D1)
                                      `union` denv_fv_tt (D2++D1)
                                      `union` singleton Y); auto.
          intros X FrX.
          assert (X `notin` L) as XnL. clear - FrX. auto.
          apply H in XnL.
          rewrite subst_ee_open_te_var; eauto using type_from_wf_atyp.
          apply value_through_subst_ee; auto.

          intros X0 FrX0.
          apply atyping_nonlin_typ_renaming with (X:=Y); auto.
            rewrite subst_ee_open_te_var; auto.
  Case "atyping_tapp".
    assert (
    (x `in` fv_ee e1 -> 
       exists B3',
         atyping G <@ (<#D2++D1#> -- <#D'#>) |_| <#D3#> @> (subst_ee x e' e1) (typ_all K T2) B3' /\
         B3' ~~~ D3')
      /\
    (x `notin` fv_ee e1 -> 
       exists B',
         atyping G (D2++D1) (subst_ee x e' e1) (typ_all K T2) B' /\
         <#B'#> ~~ <#D'#>[-]x)
    ) as IH.
     apply IHHtyp with (S0:=S); auto.
    clear IHHtyp.
    destruct IH as [IHin IHnotin].
    split; intro J; simpl in J.
      (* x `in` \y. e1 *)
      apply IHin in J.
      destruct J as [B3' [Htyp'' B3'eqD3']].
      exists B3'. simpl.       
      split; auto.
        eapply atyping_tapp; eauto.
      (* x `notin` \y. e1 *)
      apply IHnotin in J.
      destruct J as [B' [Htyp'' B'eqD']].
      exists B'. simpl.       
      split; auto.
        eapply atyping_tapp; eauto.
Qed.


(* ********************************************************************** *)
(** * #<a name="preservation"></a># Preservation *)

(* ********************************************************************** *)
(** ** Preservation *)

Lemma apreservation : forall e e' T G D D',
  atyping G D e T D' ->
  red e e' ->
  exists B', atyping G D  e' T B' /\ B' ~~~ D'.
Proof with simpl_env; eauto.
  intros e e' T G D D' aTyp Red. 
  generalize dependent e'. 
  (atyping_cases (induction aTyp) Case); 
    intros e' Red;  try solve [inversion Red; subst; eauto].
  Case "atyping_app". inversion Red; subst...
    SCase "red_app_1".
      rename H1 into Hexpr2.
      rename H3 into Hred1.
      apply IHaTyp1 in Hred1.
      clear IHaTyp1.
      destruct Hred1 as [B2 [IHaTyp1 B2eqD2]].
      apply Equal_sym in B2eqD2.
      assert (uniq B2) as UniqB2.
        apply atyping_regular in IHaTyp1.
        decompose [and] IHaTyp1.
        apply uniq_from_wf_denv_lin in H0; auto.
      apply atyping_permutation with (D1':=B2) in aTyp2; eauto.
      destruct aTyp2 as [B3 [aTyp2 B3eqD3]].
      exists B3. split.
        eapply atyping_app; eauto.
        apply Equal_sym; auto.        
    SCase "red_app_2".
      rename H1 into Hvalue1.
      rename H3 into Hred2.
      apply IHaTyp2 in Hred2.
      clear IHaTyp2.
      destruct Hred2 as [B3 [IHaTyp3 B2eqD3]].
      exists B3. split; auto.
        eapply atyping_app; eauto.
    SCase "red_abs". 
      rename H1 into Hexpr_abs.
      rename H3 into Hvalue2.
      inversion aTyp1; subst...
      SSCase "atyping_uabs".
        rename H8 into Hkind1.
        rename H9 into Htyp2.
        rename H10 into Hdep.
        (* nonlin value e2 implies that its lin ctx are equal *)        
        assert (Hequal_ctx := aTyp2).
        apply nonlin_value_is_under_equal_linctx in Hequal_ctx; auto.
        (* show G |-> (D1 -- D2), D2 *) 
        pick fresh x.
        assert (x `notin` L) as Htyp2'. auto.
        apply Htyp2 in Htyp2'. clear Htyp2.
        assert (wf_denv G D1) as WfD1.
          apply atyping_regular in Htyp2'.
          decompose [and] Htyp2'; auto.
        assert (<#D2#> <<= <#D1#>) as SubD21.
          apply denv_mono in Htyp2'; auto.
        assert (((<#D1#>--<#D2#>)|_|<#D2#>) ~~ <#D1#>) as EQ.
          apply dmap_diff_union_refl; auto.
        assert (uniq <@ (<#D1#>--<#D2#>)|_|<#D2#> @>) as UniqD12.
          apply dmap_to_denv_is_uniq.
        assert (wf_denv G <@ (<#D1#>--<#D2#>)|_|<#D2#> @>) as WfD12.
          apply denv_permutation with (D:=D1); auto.
            apply Equal_trans with (m':=(<#D1#> -- <#D2#>) |_| <#D2#>).
              apply Equal_sym.
                apply dmap_diff_union_refl; auto.
              apply denv_to_from_dmap; auto.
        (* The result follows by atyping_through_nonlin_subst_ee *)
        assert (
        (x `in` fv_ee(open_ee e0 x) -> 
          exists B3,
            atyping (nil ++ G) <@ (<#D1#> -- <#D2#>) |_| <#D2#> @> (subst_ee x e2 (open_ee e0 x)) T2 B3 /\
            B3 ~~~ D3)
        /\
        (x `notin` fv_ee(open_ee e0 x) -> 
          exists B2,
            atyping (nil ++ G) D1 (subst_ee x e2 (open_ee e0 x)) T2 B2 /\
            B2 ~~~ D2)
        ) as J.
          rewrite_env (nil ++ [(x, gbind_typ T1)] ++ G) in Htyp2'.
          apply atyping_through_nonlin_subst_ee with (D3:=D2) (S:=T1); auto.
            apply diff_disjoint.
            apply atyping_regular in Htyp2'. 
              decompose [and] Htyp2'. apply uniq_from_wf_denv_lin in H0; auto.
        destruct J as [J1 J2].
        destruct (@in_dec x (fv_ee (open_ee e0 x))) as [Hxin | Hxnotin].
          (* x in (fv_ee (open_ee 0 x) *)
          apply J1 in Hxin.
          destruct Hxin as [B3 [Hsubst_typ B3eqD3]].
          rewrite <- subst_ee_intro in Hsubst_typ; auto.
          simpl_env in Hsubst_typ.
          apply atyping_permutation with (D1':=D1) in Hsubst_typ; auto.
            destruct Hsubst_typ as [D2' [Hsubst_typ B3eqD2']].
            exists D2'.
              split; auto.
                apply Equal_trans with (m':=<#B3#>); auto.
                  apply Equal_sym; auto.
            apply uniq_from_wf_denv_lin in WfD1; auto.
            apply Equal_trans with (m':=(<#D1#>--<#D2#>)|_|<#D2#>); auto.
              apply Equal_sym.
                apply denv_to_from_dmap; auto.
          (* x notin (fv_ee (open_ee 0 x) *)
          apply J2 in Hxnotin.
          destruct Hxnotin as [B2 [Hsubst_typ B2eqD2]].
          exists B2.
          split.
            rewrite <- subst_ee_intro in Hsubst_typ; auto.
            simpl_env in Hsubst_typ; auto.

            apply Equal_trans with (m':=<#D2#>); auto.
      SSCase "atyping_labs".
        rename H8 into Hkind1.
        rename H9 into Htyp2.
        rename H10 into Hdep.
        (* show G |-> (D1 -- D2), D2 *) 
        pick fresh x.
        assert (x `notin` L) as Htyp2'. auto.
        apply Htyp2 in Htyp2'. clear Htyp2.
        assert (wf_denv G D1) as WfD1.
          apply atyping_regular in Htyp2'.
          decompose [and] Htyp2'; auto.
        assert (<#D2#> <<= <#D1#>) as SubD21.
          apply denv_mono in Htyp2'; auto.
          apply dmap_sub_remove_free with (x:=x) in Htyp2'.
            apply dmap_Equal_rewrite_Sub_right with (M2:=<#[(x,T1)]++D1#>[-]x); auto.
              simpl. apply dmap_add_remove_refl.
                apply notin_dom_implies_notIn; auto.
            apply notin_dom_implies_notIn; auto.
        assert (((<#D1#>--<#D2#>)|_|<#D2#>) ~~ <#D1#>) as EQ.
          apply dmap_diff_union_refl; auto.
        assert (uniq <@ (<#D1#>--<#D2#>)|_|<#D2#> @>) as UniqD12.
          apply dmap_to_denv_is_uniq.
        assert (wf_denv G <@ (<#D1#>--<#D2#>)|_|<#D2#> @>) as WfD12.
          apply denv_permutation with (D:=D1); auto.
            apply Equal_trans with (m':=(<#D1#> -- <#D2#>) |_| <#D2#>).
              apply Equal_sym.
                apply dmap_diff_union_refl; auto.
              apply denv_to_from_dmap; auto.
        (* The result follows by atyping_through_lin_subst_ee *)
        assert (
        (x `in` fv_ee(open_ee e0 x) -> 
           exists B3,
             atyping G <@ (<#nil++D1#> -- <#D2#>) |_| <#D2#> @> (subst_ee x e2 (open_ee e0 x)) T2 B3 /\
             B3 ~~~ D3) 
           /\
        (x `notin` fv_ee(open_ee e0 x) -> 
           exists B,
             atyping G (nil ++ D1) (subst_ee x e2 (open_ee e0 x)) T2 B /\
             <#B#> ~~ (<#D2#> [-] x))
        ) as J.
          rewrite_env (nil ++ [(x, T1)] ++ D1) in Htyp2'.
          apply atyping_through_lin_subst_ee with (D3:=D2) (S:=T1); auto.
            simpl. apply diff_disjoint.
        destruct J as [J1 J2].
        destruct (@in_dec x (fv_ee (open_ee e0 x))) as [Hxin | Hxnotin].
          (* x in (fv_ee (open_ee 0 x) *)
          apply J1 in Hxin.
          destruct Hxin as [B3 [Hsubst_typ B3eqD3]].
          rewrite <- subst_ee_intro in Hsubst_typ; auto.
          simpl_env in Hsubst_typ.
          apply atyping_permutation with (D1':=D1) in Hsubst_typ; auto.
            destruct Hsubst_typ as [D2' [Hsubst_typ B3eqD2']].
            exists D2'.
              split; auto.
                apply Equal_trans with (m':=<#B3#>); auto.
                  apply Equal_sym; auto.
            apply uniq_from_wf_denv_lin in WfD1; auto.
            apply Equal_trans with (m':=(<#D1#>--<#D2#>)|_|<#D2#>); auto.
              apply Equal_sym.
                apply denv_to_from_dmap; auto.
          (* x notin (fv_ee (open_ee e0 x) *)
          assert (
          (x `in` fv_ee (open_ee e0 x) /\ x `notin` dom D2) 
            \/  
          (x `notin` fv_ee (open_ee e0 x) /\ x `in` dom D2)
          ) as Mono.
            apply denv_mono_aux with (x:=x) in Htyp2'; auto.
              rewrite dom_app. simpl. fsetdec.
          destruct Mono as [[H1 H2]|[H1 H2]].
            contradict H1; auto.
            contradict H2; auto.
  Case "atyping_tapp". inversion Red; subst...
    SCase "red_tapp". 
      rename H3 into Htype.
      rename H5 into Hred1.
      apply IHaTyp in Hred1.
      clear IHaTyp.
      destruct Hred1 as [B' [IHaTyp B'eqD']].
      apply Equal_sym in B'eqD'.
      assert (uniq B') as UniqB'.
        apply atyping_regular in IHaTyp.
        decompose [and] IHaTyp.
        apply uniq_from_wf_denv_lin in H2; auto.
      exists B'. split.
        eapply atyping_tapp; eauto.
        apply Equal_sym; auto.      
    SCase "red_tabs". 
      rename H3 into Hexpr_tabs.
      inversion aTyp; subst...
      (* The result follows by atyping_through_subst_te *)
      pick fresh X.
      assert (X `notin` L) as Htyp. auto.
      apply H10 in Htyp. clear H10.
      rewrite_env (nil ++ [(X, gbind_kn K)] ++ G) in Htyp.
      apply atyping_through_subst_te with (P:=T) (Q':=K') in Htyp; auto.
      simpl_env in Htyp.
      rewrite <- subst_tt_intro in Htyp; auto.
      rewrite <- subst_te_intro in Htyp; auto.
      rewrite <- subst_tdb_fresh in Htyp; auto.
      rewrite <- subst_tdb_fresh in Htyp; auto.
      exists D'. split; auto.
        apply Equal_refl.
Qed.

(* ********************************************************************** *)
(** * #<a name="progress"></a># Progress *)


(* ********************************************************************** *)
(** ** Canonical forms *)

Lemma acanonical_form_abs : forall e K U1 U2,
  value e ->
  atyping gempty dempty e (typ_arrow K U1 U2) dempty ->
  exists V, exists e1, e = exp_abs K V e1.
Proof.
  intros e K U1 U2 Val Typ.
  remember dempty as D.
  remember gempty as G.
  remember (typ_arrow K U1 U2) as T.
  revert K U1 U2 HeqT HeqD HeqG.
  induction Typ; intros QQ U1 U2 EQT EQD EQG; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
  Case "atyping_uabs".
    inversion EQT; subst.    
    exists U1. exists e1. auto.
  Case "atyping_labs".
    inversion EQT; subst.    
    exists U1. exists e1. auto.
Qed.

Lemma acanonical_form_tabs : forall e K U,
  value e ->
  atyping gempty dempty e (typ_all K U) dempty ->
  exists V, exists e1, e = exp_tabs V e1.
Proof.
  intros e K U Val Typ.
  remember dempty as D.
  remember gempty as G.
  remember (typ_all K U) as T.
  revert K U HeqT HeqD HeqG.
  induction Typ; intros QQ U EQT EQD EQG; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
Qed.

(* ********************************************************************** *)
(** ** Progress *)

Lemma _aprogress : forall G D e T D',
  atyping G D e T D' ->
  G = gempty ->
  D = dempty ->
  D' = dempty ->
  value e \/ exists e', red e e'.
Proof with eauto.
  intros G D e T D' Typ.
  assert (Typ' : atyping G D e T D')...
  induction Typ; intros EQG EQD EQD'; subst...
  Case "atyping_uvar".
    inversion H.
  Case "atyping_lvar".
    inversion H.
  Case "atyping_app".
    right.
    assert (D2 = dempty) as EQ.
      apply denv_mono_empty in Typ1.
        apply Equal_sym in Typ1.
        apply dmap_eq_empty_inv in Typ1.
        apply denv_eq_empty_inv; auto.
    subst.
    destruct IHTyp1 as [Val1 | [e1' Rede1']]...
    SCase "Val1".
      destruct IHTyp2 as [Val2 | [e2' Rede2']]...
      SSCase "Val2".
        destruct (acanonical_form_abs _ _ _ _ Val1 Typ1) as [S [e3 EQ]].
        subst.
        exists (open_ee e3 e2)...
  Case "atyping_tapp".
    right.
    destruct IHTyp as [Val1 | [e1' Rede1']]...
    SCase "Val1".
      destruct (acanonical_form_tabs _ _ _ Val1 Typ) as [S [e3 EQ]].
      subst.
      exists (open_te e3 T)...
      apply red_tabs; auto.
        apply type_from_wf_atyp in H; auto.
    SCase "e1' Rede1'".
      exists (exp_tapp e1' T)...
      apply red_tapp; auto.
        apply type_from_wf_atyp in H; auto.
Qed.    

Lemma aprogress : forall e T,
  atyping gempty dempty e T dempty ->
  value e \/ exists e', red e e'.
Proof with eauto.
  intros e T Typ.
  eapply _aprogress; eauto.
Qed.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../../../metatheory" "-I" "../linf") ***
*** End: ***
 *)