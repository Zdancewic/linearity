(** Type-safety proofs for Algorithmic Lightweight Linear F

    Authors: Aileen Zhang, Jianzhou Zhao, and Steve Zdancewic.

    In parentheses are given the label of the corresponding lemma in
    the appendix (informal proofs) of the POPLmark Challenge.

    Table of contents:
      - #<a href="##typing">Properties of typing</a>#
      - #<a href="##preservation">Preservation</a>#
      - #<a href="##progress">Progress</a># *)

Require Export ALinearF_Soundness.
Require Export ALinearF_NLemmas.
Require Import Omega.
Require Import Tactics.

Axiom skip : False.
Ltac skip := assert False; [ apply skip | contradiction ].

Lemma nonlin_value_is_under_equal_linctx : forall G D e T D',
  atyping G D e T D' ->
  wf_atyp G T kn_nonlin ->
  value e ->
  D = D'.
Proof.
  intros G D e T D' Hatyp Hwf_atyp Hvalue.
  (* linear ctx is mon *)
  assert (Hdenv_mon := Hatyp).
  apply denv_mono in Hdenv_mon.
  (atyping_cases (induction Hatyp) Case); try solve [inversion Hvalue].
  Case "atyping_uabs".
    (* trivial, because when k is *, the lin ctx cannot be changed *)
    inversion Hwf_atyp; subst.
    assert (kn_nonlin = kn_nonlin) as EQ; auto.
  Case "atyping_labs".
    (* trivial, because when k is *, the lin ctx cannot be changed *)
    inversion Hwf_atyp; subst.
    assert (kn_nonlin = kn_nonlin) as EQ; auto.
  Case "atyping_tabs".
    (* By IH *)
    inversion Hwf_atyp; subst.
    pick fresh X.
    apply H1 with (X:=X); auto.
      apply value_through_open_te; auto.
Qed.

Lemma atyping_through_lin_subst_ee : forall S x G T e e' D1 D D2 D3 D3',
  atyping G (D2 ++ [(x, dbind_typ S)] ++ D1) e T D ->
  atyping G D3 e' S D3' ->
  wf_denv G (D3 ++ ((D2 ++ D1) -- D)) ->
  x `notin` dom(D3) ->
  (x `in` fv_ee(e) -> 
       atyping G (D3 ++ ((D2 ++ D1) -- D)) (subst_ee x e' e) T D3') 
    /\
  (x `notin` fv_ee(e) -> 
        atyping G (D2 ++ D1) (subst_ee x e' e) T (D [-] x)).
Proof.
  intros S x G T e e' D1 D D2 D3 D3' Htyp Htyp' Hwfdenv Hnotin.
  remember (D2 ++ [(x, dbind_typ S)] ++ D1) as DD.
  generalize dependent D2.
  generalize dependent D1.
  generalize dependent D3.
  generalize dependent D3'.
  generalize dependent e'.
  generalize dependent S.
  generalize dependent x.
  (atyping_cases (induction Htyp) Case); intros; subst.
  Case "atyping_uvar". 
     rename x0 into y.
     rename H into Hbinds.
     rename H0 into Hwfdenv'.
     (* x must be free in D1, y:S, D2 *)
     assert (HxnoinD := denv_fv_ginv G (D2 ++ [(y, dbind_typ S)] ++ D1) x (gbind_typ T) Hwfdenv' Hbinds).
     simpl_env in HxnoinD. notin_simpl.
     rename H into HxnotinD2.
     rename H2 into HxnotinD1.
     rename H0 into Hxny'.
     rename H3 into Hxny.
     (* x {e'/y} = x *)
     rewrite <- subst_ee_fresh; auto.  
     split; intro Hy_fvx; simpl in Hy_fvx.
        (* y in fv_ee(x) *)
        absurd_hyp Hy_fvx; auto.
        (* y notin fv_ee(x) *)   
        assert (Hwfdenv'' := wf_denv_lin_strengthening y S G D1 D2 Hwfdenv').
        assert ((D2 ++ [(y, dbind_typ S)] ++ D1) [-] y = (D2 ++ D1)) as Heq.   
           apply wf_denv__ok in Hwfdenv'.
           destruct Hwfdenv' as [Hwfgenv Hok].
           apply minus_dist; auto.
              apply fresh_mid_tail_In with (x:=y) (G:=D2) (F:=[(y, dbind_typ S)]); auto.
                 simpl_env. fsetdec.
              apply fresh_mid_head_In with (x:=y) (E:=D1) (F:=[(y, dbind_typ S)]); auto.
                 simpl_env. fsetdec.
         rewrite Heq; auto.
  Case "atyping_lvar".
      rename x0 into y.
      rename H into Hbinds.
      rename H0 into Hwfdenv'. 
      binds_cases Hbinds; simpl_env in *; notin_simpl.
      SCase "x in D1, x<>y, x notin D2".
        rename H into Hxny'.
        rename H1 into Hxny.
        rename H0 into Hbinds.
        (* x {e'/y} = x *)
        rewrite <- subst_ee_fresh; auto.  
        split; intro Hy_fvx; simpl in Hy_fvx.
          (* y in fv_ee(x) *)
          absurd_hyp Hy_fvx; auto.
          (* y notin fv_ee(x) *)   
          assert (Hwfdenv'' := wf_denv_lin_strengthening y S G D1 D2 Hwfdenv').
          assert ((D2 ++ [(y, dbind_typ S)] ++ D1) [-] y = (D2 ++ D1)) as Heq.   
            apply wf_denv__ok in Hwfdenv'.
            destruct Hwfdenv' as [Hwfgenv Hok].
            apply minus_dist; auto.
              apply fresh_mid_tail_In with (x:=y) (G:=D2) (F:=[(y, dbind_typ S)]); auto.
                 simpl_env. fsetdec.
              apply fresh_mid_head_In with (x:=y) (E:=D1) (F:=[(y, dbind_typ S)]); auto.
                 simpl_env. fsetdec.
          assert ((((D2 ++ [(y, dbind_typ S)] ++ D1) [-] y) [-] x) =
                       (((D2 ++ [(y, dbind_typ S)] ++ D1) [-] x) [-] y)) as Heq'.  
             apply minus_commut.
          rewrite <- Heq'.
          rewrite Heq; auto.         
      SCase "x notin D1, x=y, x in D2".
        inversion H0; subst. clear H0.
        simpl. destruct (x==x); simpl_env.
           SSCase "x=x". 
              clear e.
              split; intro Hy_fvx; simpl in Hy_fvx.
                (* y in fv_ee(x) *)
               apply wf_denv__ok in Hwfdenv'.
               destruct Hwfdenv' as [Hwfgenv Hok].
                assert ((D2++[(x, dbind_typ S)]++D1) [-] x = (D2 ++ D1)) as Heq.   
                  apply minus_dist; auto.
                    apply fresh_mid_tail_In with (x:=x) (G:=D2) (F:=[(x, dbind_typ S)]); auto.
                      simpl_env. fsetdec.
                rewrite Heq.
                assert (((D2 ++ D1) -- (D2++D1)) ~~ dempty) as Heq'.
                  apply minus_refl.
                apply eq_preserves_atyping with (D1:=D3) (D2:=D3'); auto.
                  rewrite_env (D3 ++ (D2 ++ D1 -- D2 ++ D1) ++ nil).
                  apply denv_eq_symm.
                  apply eq_preserves_eq with (D2:=dempty); auto.
                    simpl_env. apply denv_eq_refl.
                    apply denv_eq_symm; auto.
                  apply denv_eq_refl.
                (* y notin fv_ee(x) *)   
                absurd_hyp Hy_fvx; fsetdec.
           SSCase "x<>x".
              absurd_hyp n; auto.
      SCase "x notin D1, x<>y, x in D2".
        assert (Hok := Hwfdenv').
        apply wf_denv__ok in Hok.
        destruct Hok as [Hwfgenv Hok].
        assert (x `in` dom D2) as HinD2. 
           skip. (* binds -> in *)
        assert (Hok' := Hok).
        apply fresh_tail_In with (x:=x) in Hok; auto.
        simpl_env in *; notin_simpl.
        rename H2 into Hxny'.
        rename H3 into Hxny.
        rename H0 into Hbinds.
        rename H1 into HnotD1.
        (* x {e'/y} = x *)
        rewrite <- subst_ee_fresh; auto.  
        split; intro Hy_fvx; simpl in Hy_fvx.
          (* y in fv_ee(x) *)
          absurd_hyp Hy_fvx; auto.
          (* y notin fv_ee(x) *)   
          assert (Hwfdenv'' := wf_denv_lin_strengthening y S G D1 D2 Hwfdenv').
          assert ((D2 ++ [(y, dbind_typ S)] ++ D1) [-] y = (D2 ++ D1)) as Heq.   
            apply minus_dist; auto.
              apply fresh_mid_tail_In with (x:=y) (G:=D2) (F:=[(y, dbind_typ S)]); auto.
                 simpl_env. fsetdec.
              apply fresh_mid_head_In with (x:=y) (E:=D1) (F:=[(y, dbind_typ S)]); auto.
                 simpl_env. fsetdec.
          assert ((((D2 ++ [(y, dbind_typ S)] ++ D1) [-] y) [-] x) =
                       (((D2 ++ [(y, dbind_typ S)] ++ D1) [-] x) [-] y)) as Heq'.  
             apply minus_commut.
          rewrite <- Heq'. rewrite Heq; auto.
  Case "atyping_uabs".
     split; intro Hy_fvx; simpl in Hy_fvx; simpl.
        (* y in fv_ee(\ K V e1) *)
        apply atyping_uabs with (L:=L `union` dom G `union` singleton x); auto.
           intros y Hfry.
           apply in_fv_ee_open_ee with (y:=y) in Hy_fvx; auto.
           assert (y `notin` L) as Htyp1. auto.
           apply H0 in Htyp1. clear H0.
           (* weakening on Hwfdenv *)
           assert (wf_genv (nil++ [(y, gbind_typ V)] ++ G)) as Hwfgenv.
             simpl_env. apply wf_genv_typ; auto.
           rewrite_env (nil ++ G) in Hwfdenv.
           apply wf_denv_weakening with (G:=[(y, gbind_typ V)]) in Hwfdenv; auto.
           (* weakening on Htyp' *)
           assert (wf_denv (nil ++ [(y, gbind_typ V)] ++ G) D3) as Hwfdenv'.
             apply wf_denv_weakening; auto.
               simpl_env.  apply atyping_regular in Htyp'.
               decompose [and] Htyp'; auto.
           rewrite_env (nil ++ G) in Htyp'.
           apply atyping_nonlin_weakening with (G:=[(y, gbind_typ V)]) in Htyp'; auto.
           (* By IH on Htyp1 *)
           assert (HtypIH1 := Hwfdenv).
           apply H1 with (x0:=y) (x1:=x) (e':=e') (D3':=D3') (S0:=S) in HtypIH1; auto.
           destruct HtypIH1 as [HtypIH1_in HtypIH1_notin].
           apply HtypIH1_in in Hy_fvx.
           rewrite subst_ee_open_ee_var; auto.
             apply atyping_regular in Htyp'. decompose [and] Htyp'; auto.
        intros J.
        apply H2 in J.
        skip. (* nil = A, x, B*)
        (* y notin fv_ee(\ K V e1) *)   
        apply atyping_uabs with (L:=L `union` dom G `union` singleton x); auto.
           intros y Hfry.
           apply notin_fv_ee_open_ee with (y:=y) in Hy_fvx; auto.
           assert (y `notin` L) as Htyp1. auto.
           apply H0 in Htyp1. clear H0.
           (* weakening on Hwfdenv *)
           assert (wf_genv (nil++ [(y, gbind_typ V)] ++ G)) as Hwfgenv.
             simpl_env. apply wf_genv_typ; auto.
           rewrite_env (nil ++ G) in Hwfdenv.
           apply wf_denv_weakening with (G:=[(y, gbind_typ V)]) in Hwfdenv; auto.
           (* weakening on Htyp' *)
           assert (wf_denv (nil ++ [(y, gbind_typ V)] ++ G) D3) as Hwfdenv'.
             apply wf_denv_weakening; auto.
               simpl_env.  apply atyping_regular in Htyp'.
               decompose [and] Htyp'; auto.
           rewrite_env (nil ++ G) in Htyp'.
           apply atyping_nonlin_weakening with (G:=[(y, gbind_typ V)]) in Htyp'; auto.
           (* By IH on Htyp1 *)
           assert (HtypIH1 := Hwfdenv).
           apply H1 with (x0:=y) (x1:=x) (e':=e') (D3':=D3') (S0:=S) in HtypIH1; auto.
           destruct HtypIH1 as [HtypIH1_in HtypIH1_notin].
           apply HtypIH1_notin in Hy_fvx.
           rewrite subst_ee_open_ee_var; auto.
             apply atyping_regular in Htyp'. decompose [and] Htyp'; auto.
        intros J.
        apply H2 in J.
        skip. (* nil = A, x, B*)
  Case "atyping_labs".
     split; intro Hy_fvx; simpl in Hy_fvx; simpl.
        (* y in fv_ee(\ K V e1) *)
        apply atyping_labs with (L:=L `union` dom D1 `union` dom D2 `union` singleton x `union` dom D3
                                                           `union` dom G `union`  dom (D3 ++ (D2 ++ D1 -- D'))); auto.
           intros y Hfry.
           apply in_fv_ee_open_ee with (y:=y) in Hy_fvx; auto.
           assert (y `notin` L) as Htyp1. auto.
           apply H0 in Htyp1. clear H0.
           (* weakening on Hwfdenv *)
           assert (D3 ++ (([(y, dbind_typ V)] ++ D2) ++ D1 -- D') ~~
                        [(y, dbind_typ V)] ++ D3 ++ (D2 ++ D1 -- D')) as Heq.
             (*
                 y notin D2++x++D1,  
                 D' <<= D2++x++D.
                 so y++D2++x++D1 - D' = y ++ (D2++x++D1 - D').
             *)
             skip.
           assert (wf_denv G (D3 ++ (([(y, dbind_typ V)] ++ D2) ++ D1 -- D'))) as Hwfdenv'.
              apply eq_preserves_wf_denv with (D:=[(y, dbind_typ V)] ++ D3 ++ (D2 ++ D1 -- D')).
                  apply wf_denv_typ; auto.
                      notin_simpl; auto.
                  apply denv_eq_symm; auto.
           (* By IH on Htyp1 *)
           assert (HtypIH1 := Hwfdenv').
           apply H1 with (x0:=y) (x1:=x) (e':=e') (D3':= D3') (S0:=S) in HtypIH1; auto.
           destruct HtypIH1 as [HtypIH1_in HtypIH1_notin].
           apply HtypIH1_in in Hy_fvx.
           rewrite subst_ee_open_ee_var; auto.
             apply eq_preserves_atyping with (D1:=D3 ++ (([(y, dbind_typ V)] ++ D2) ++ D1 -- D')) (D2:=D3'); auto.
                apply denv_eq_refl.            
             apply atyping_regular in Htyp'. decompose [and] Htyp'; auto.
        intros J.
        apply H2 in J.
        skip. (* nil = A, x, B*)
        (* y notin fv_ee(\ K V e1) *)   
        apply atyping_labs with (L:=L `union` dom D1 `union` dom D2 `union` singleton x `union` dom D3
                                                           `union` dom G `union`  dom (D3 ++ (D2 ++ D1 -- D'))); auto.
           intros y Hfry.
           apply notin_fv_ee_open_ee with (y:=y) in Hy_fvx; auto.
           assert (y `notin` L) as Htyp1. auto.
           apply H0 in Htyp1. clear H0.
           assert (D3 ++ (([(y, dbind_typ V)] ++ D2) ++ D1 -- D') ~~
                        [(y, dbind_typ V)] ++ D3 ++ (D2 ++ D1 -- D')) as Heq.
             (*
                 y notin D2++x++D1,  
                 D' <<= D2++x++D.
                 so y++D2++x++D1 - D' = y ++ (D2++x++D1 - D').
             *)
             skip.
           assert (wf_denv G (D3 ++ (([(y, dbind_typ V)] ++ D2) ++ D1 -- D'))) as Hwfdenv'.
              apply eq_preserves_wf_denv with (D:=[(y, dbind_typ V)] ++ D3 ++ (D2 ++ D1 -- D')).
                  apply wf_denv_typ; auto.
                      notin_simpl; auto.
                  apply denv_eq_symm; auto.
           (* By IH on Htyp1 *)
           assert (HtypIH1 := Hwfdenv').
           apply H1 with (x0:=y) (x1:=x) (e':=e') (D3':= D3') (S0:=S) in HtypIH1; auto.
           destruct HtypIH1 as [HtypIH1_in HtypIH1_notin].
           apply HtypIH1_notin in Hy_fvx.
           rewrite subst_ee_open_ee_var; auto.
             apply atyping_regular in Htyp'. decompose [and] Htyp'; auto.
        intros J.
        apply H2 in J.
        skip. (* nil = A, x, B*)
  Case "atyping_app".
     (* lin ctx mon *)
     assert (Hdenv_mon21 := Htyp1).          
     assert (Hdenv_mon32 := Htyp2).
     assert (Hdenv_mon' := Htyp').
     apply denv_mono in Hdenv_mon21.
     apply denv_mono in Hdenv_mon32.
     apply denv_mono in Hdenv_mon'.
     (* By IH of T1->T2 *)
     assert (D3 <<= D5 ++ [(x, dbind_typ S)] ++ D4) as Hdenv_mon31.
       eapply denv_sub_trans; eauto.
     assert (wf_denv G (D0 ++ (D5 ++ D4 -- D2))) as Hwfdenv'.
       rewrite_env (D0 ++ (D5 ++ D4 -- D2) ++ nil).
       apply wf_denv_lin_strengthening3 with (D2:=(D5 ++ D4 -- D3)); simpl_env; auto.
         apply minus_flip; auto.
     assert (HtypIH1:=Hwfdenv').
     apply IHHtyp1 with (x0:=x) (e':=e') (D3':=D3') (S0:=S) in HtypIH1; auto.
     (* discuss of where x is *)    
     assert (atyping G (D5++[(x, dbind_typ S)]++D4) (exp_app e1 e2) T2 D3) as Htyp.
         eapply atyping_app; eauto.
     assert (x `in` dom (D5 ++ [(x, dbind_typ S)] ++ D4)) as Hnotin'.
         skip.
     assert (binds x (dbind_typ S) (D5 ++ [(x, dbind_typ S)] ++ D4)) as Hbinds.
         skip.
     apply denv_mono_app2 with (x:=x) (b:=dbind_typ S) in Htyp; auto.
     destruct Htyp as [[Hxine1 [Hxnotine2 HxnotinD3]] | 
                                   [[Hxnotine1 [Hxine2 HxnotinD3]] |
                                    [Hxnotine1 [Hxnotine2 HxinD3]]
                                   ]
                                  ].
     SCase "Hxine1 Hxnotine2 HxnotinD3".
       destruct HtypIH1 as [HtypIH1_in HtypIH1_notin]. clear HtypIH1_notin.
       assert (Htyp1':=Hxine1).
       apply HtypIH1_in in Htyp1'.
       assert (dom D3' ** dom (D2 -- D3)) as Hdis.
          skip.
       assert ((D3' ++ (D2 -- D3)) ~~ ((D2 -- D3) || D3')) as Heq0.
          apply denv_eq_trans with (D':=D3'||(D2--D3)).
            apply denv_union_disjoin; auto.
            apply denv_union_symm; auto.
       assert (atyping G (D3' ++ (D2 -- D3)) e2 T1 D3') as Htyp2'.
          assert ((D3' || (D2 -- D3)) ~~ (D3' ++ (D2 -- D3))) as Heq.
             apply denv_eq_symm.
               apply denv_union_disjoin.
                  apply denv_disjoin_concat with (D1:=D0) (D2:=D5++[(x, dbind_typ S)]++D4 -- D3); auto.
                     apply wf_denv__ok in Hwfdenv.
                       destruct Hwfdenv as [Hwfgenv Hok].
                       apply ok__disjoin in Hok.
                         skip. (* from Hok and Hnotin *)
                     apply minus_stable; auto.
          assert ((D3' || dempty) ~~ D3' ) as Heq'.
            rewrite denv_union_empty.
            apply denv_eq_refl.
          apply eq_preserves_atyping with (D1:=D3' || (D2 -- D3)) (D2:=D3' || dempty); auto.
          apply atyping_lin_weakening2; auto.
            apply atyping_lin_strengthening3; auto.
               skip.
       assert (D0 ++ (D5 ++ D4 -- D3) ~~ ((D2 -- D3) || (D0 ++ (D5 ++ D4 -- D2)))) as Heq''.
         skip.
       assert (wf_denv G ((D2 -- D3) || (D0 ++ (D5 ++ D4 -- D2)))) as Hwfdenv''.
         apply eq_preserves_wf_denv with (D:=D0 ++ (D5 ++ D4 -- D3)); auto.
       apply atyping_lin_weakening2 with (D:=D2--D3) in Htyp1'; auto.
       apply eq_preserves_atyping with (D1':=D0 ++ (D5 ++ D4 -- D3)) (D2':=D3'++(D2--D3)) in Htyp1'; 
         try solve [apply denv_eq_symm; auto].
       split; intro Hy_fvx; simpl in Hy_fvx; simpl.
          apply atyping_app with (T1:=T1) (K:=K) (D2:=D3'++(D2--D3)); auto.
            rewrite <- subst_ee_fresh; auto.
          skip. (* Hy_fvx and Hxine1 *)          

     SCase "Hxnotine1 Hxine2 HxnotinD3".
       destruct HtypIH1 as [HtypIH1_in HtypIH1_notin]. clear HtypIH1_in.
       assert (Htyp1':=Hxnotine1).
       apply HtypIH1_notin in Htyp1'.
       (* lin ctx mon aux *)
       assert (Hdenv_mon21' := Htyp1).          
       apply denv_mono_aux2 with (x:=x) (b:=dbind_typ S) in Hdenv_mon21'; auto.
       destruct Hdenv_mon21' as [[Ha Hb] | [Ha Hb]].
          SSCase "x in e1, x notin D2".
              absurd_hyp Hxnotine1; fsetdec.
          SSCase "x notin e1, x in D2".
              assert (exists D21, exists D22, D2 = D22 ++ [(x, dbind_typ S)] ++ D21) as Heq.
                 skip.
              destruct Heq as [D21 [D22 Heq]]; subst.
              assert ((D22++D21) <<= (D5 ++ D4)) as Hsub.
                 skip.
              assert ((D0 ++ ((D22++D21) -- D3)) <<= (D0 ++ ((D5 ++ D4) -- D3))) as Hsub'.
                 skip.
              (* By IH of T1 *)
              assert (Hwfdenv0 := Hwfdenv).
              rewrite_env (nil ++ (D0 ++ (D5 ++ D4 -- D3)) ++ nil) in Hwfdenv.
              apply wf_denv_lin_strengthening3 with (D2':=D0 ++ ((D22++D21) -- D3)) in Hwfdenv; auto.
              assert (HtypIH2:=Hwfdenv). simpl_env in HtypIH2.
              apply IHHtyp2 with (x0:=x) (e':=e') (D3':=D3') (S0:=S) in HtypIH2; auto.
              destruct HtypIH2 as [HtypIH2_in HtypIH2_notin]. clear HtypIH2_notin.
              assert (Htyp2':=Hxine2).
              apply HtypIH2_in in Htyp2'.

              assert ((fv_ee(subst_ee x e' e1)) ** (dom D3)) as Hdist.
                 skip.
              apply atyping_lin_strengthening2 with (D'':=D3) in Htyp1'; auto.
              assert (((D22 ++ [(x, dbind_typ S)] ++ D21) [-] x) ~~ (D22 ++ D21)) as Heq'.
                 skip.
              assert ((((D22 ++ [(x, dbind_typ S)] ++ D21) [-] x) -- D3) ~~ ((D22 ++ D21) -- D3)) as Heq''.
                 skip.
              apply eq_preserves_atyping with (D1':=D5++D4--D3) (D2':=D22++D21 -- D3) in Htyp1'; 
                 try solve [ apply denv_eq_refl | auto ].
              rewrite_env (nil ++ (D22 ++ D21 -- D3)) in Htyp1'.
              rewrite_env (nil ++ (D5 ++ D4 -- D3)) in Htyp1'.
              apply atyping_lin_weakening with (D:=D0) in Htyp1'; auto.
              simpl_env in Htyp1'.

              split; intro Hy_fvx; simpl in Hy_fvx; simpl.
                 apply atyping_app with (T1:=T1) (K:=K) (D2:=D0 ++ (D22++D21--D3)); auto.
                 skip. (* Hy_fvx and Hxine2 *)          

     SCase "Hxnotine1 Hxnotine2 HxinD3". 
       destruct HtypIH1 as [HtypIH1_in HtypIH1_notin]. clear HtypIH1_in.
       assert (Htyp1':=Hxnotine1).
       apply HtypIH1_notin in Htyp1'.
       (* lin ctx mon aux *)
       assert (Hdenv_mon21' := Htyp1).          
       apply denv_mono_aux2 with (x:=x) (b:=dbind_typ S) in Hdenv_mon21'; auto.
       destruct Hdenv_mon21' as [[Ha Hb] | [Ha Hb]].
          SSCase "x in e1, x notin D2".
              absurd_hyp Hxnotine1; fsetdec.
          SSCase "x notin e1, x in D2".
              assert (exists D21, exists D22, D2 = D22 ++ [(x, dbind_typ S)] ++ D21) as Heq.
                 skip.
              destruct Heq as [D21 [D22 Heq]]; subst.
              assert ((D22++D21) <<= (D5 ++ D4)) as Hsub.
                 skip.
              assert ((D0 ++ ((D22++D21) -- D3)) <<= (D0 ++ ((D5 ++ D4) -- D3))) as Hsub'.
                 skip.
              (* By IH of T1 *)
              assert (Hwfdenv0 := Hwfdenv).
              rewrite_env (nil ++ (D0 ++ (D5 ++ D4 -- D3)) ++ nil) in Hwfdenv.
              apply wf_denv_lin_strengthening3 with (D2':=D0 ++ ((D22++D21) -- D3)) in Hwfdenv; auto.
              assert (HtypIH2:=Hwfdenv). simpl_env in HtypIH2.
              apply IHHtyp2 with (x0:=x) (e':=e') (D3':=D3') (S0:=S) in HtypIH2; auto.
              destruct HtypIH2 as [HtypIH2_in HtypIH2_notin]. clear HtypIH2_in.
              assert (Htyp2':=Hxnotine2).
              apply HtypIH2_notin in Htyp2'.

              assert (((D22 ++ [(x, dbind_typ S)] ++ D21) [-] x) ~~ (D22 ++ D21)) as Heq'.
                 skip.
              apply eq_preserves_atyping with (D1':=D5++D4) (D2':=D22++D21) in Htyp1'; 
                 try solve [ apply denv_eq_refl | auto ].

              split; intro Hy_fvx; simpl in Hy_fvx; simpl.
                skip. (* Hy_fvx and Hxnotine1 and Hxnotine2 *)          
                apply atyping_app with (T1:=T1) (K:=K) (D2:=D22++D21); auto.
 
  Case "atyping_tabs". 
     split; intro Hy_fvx; simpl in Hy_fvx; simpl.
        (* y in fv_ee(\ K e1) *)
        apply atyping_tabs with (L:=L `union` dom G `union` singleton x); auto.
           (* value_through_subst_ee *)     
           apply value_through_subst_ee; auto.
             apply atyping_regular in Htyp'. decompose [and] Htyp'; auto.

           intros Y HfrY.
           apply in_fv_ee_open_te with (Y:=Y) in Hy_fvx; auto.
           assert (Y `notin` L) as Htyp1. auto.
           apply H0 in Htyp1. clear H0.
           (* weakening on Hwfdenv *)
           assert (wf_genv (nil++ [(Y, gbind_kn K)] ++ G)) as Hwfgenv.
             simpl_env. apply wf_genv_kn; auto.
           rewrite_env (nil ++ G) in Hwfdenv.
           apply wf_denv_weakening with (G:=[(Y, gbind_kn K)]) in Hwfdenv; auto.
           (* weakening on Htyp' *)
           assert (wf_denv (nil ++ [(Y, gbind_kn K)] ++ G) D3) as Hwfdenv'.
             apply wf_denv_weakening; auto.
               simpl_env.  apply atyping_regular in Htyp'.
               decompose [and] Htyp'; auto.
           rewrite_env (nil ++ G) in Htyp'.
           apply atyping_nonlin_weakening with (G:=[(Y, gbind_kn K)]) in Htyp'; auto.
           (* By IH on Htyp1 *)
           assert (HtypIH1 := Hwfdenv).
           apply H1 with (X:=Y) (x0:=x) (e':=e') (D3':=D3') (S0:=S) in HtypIH1; auto.
           destruct HtypIH1 as [HtypIH1_in HtypIH1_notin].
           apply HtypIH1_in in Hy_fvx.
           rewrite subst_ee_open_te_var; auto.
             apply atyping_regular in Htyp'. decompose [and] Htyp'; auto.
        (* y notin fv_ee(\ K e1) *)   
        apply atyping_tabs with (L:=L `union` dom G `union` singleton x); auto.
           (* value_through_subst_ee *)     
           apply value_through_subst_ee; auto.
             apply atyping_regular in Htyp'. decompose [and] Htyp'; auto.

           intros Y HfrY.
           apply notin_fv_ee_open_te with (Y:=Y) in Hy_fvx; auto.
           assert (Y `notin` L) as Htyp1. auto.
           apply H0 in Htyp1. clear H0.
           (* weakening on Hwfdenv *)
           assert (wf_genv (nil++ [(Y, gbind_kn K)] ++ G)) as Hwfgenv.
             simpl_env. apply wf_genv_kn; auto.
           rewrite_env (nil ++ G) in Hwfdenv.
           apply wf_denv_weakening with (G:=[(Y, gbind_kn K)]) in Hwfdenv; auto.
           (* weakening on Htyp' *)
           assert (wf_denv (nil ++ [(Y, gbind_kn K)] ++ G) D3) as Hwfdenv'.
             apply wf_denv_weakening; auto.
               simpl_env.  apply atyping_regular in Htyp'.
               decompose [and] Htyp'; auto.
           rewrite_env (nil ++ G) in Htyp'.
           apply atyping_nonlin_weakening with (G:=[(Y, gbind_kn K)]) in Htyp'; auto.
           (* By IH on Htyp1 *)
           assert (Htyp1' := Hwfdenv).
           apply H1 with (X:=Y) (x0:=x) (e':=e') (D3':=D3') (S0:=S) in Htyp1'; auto.
           destruct Htyp1' as [Htyp1'_in Htyp1'_notin].
           apply Htyp1'_notin in Hy_fvx.
           rewrite subst_ee_open_te_var; auto.
             apply atyping_regular in Htyp'. decompose [and] Htyp'; auto.   
   Case "atyping_tapp". 
     (* By IH on Htyp *)
     assert (HtypIH := Hwfdenv).
     apply IHHtyp with (x0:=x) (e':=e') (D3':=D3') (S0:=S) in HtypIH; auto.
     destruct HtypIH as [HtypIH1_in HtypIH1_notin].
     split; intro Hy_fvx; simpl in Hy_fvx; simpl.
        (* y in fv_ee(e1 [T]) *)
           apply HtypIH1_in in Hy_fvx.
           eapply atyping_tapp; eauto.
        (* y notin fv_ee(e1 [T]) *)
           (* By IH on Htyp *)
           apply HtypIH1_notin in Hy_fvx.
           eapply atyping_tapp; eauto.
Qed.

(* ********************************************************************** *)
(** * #<a name="preservation"></a># Preservation *)

(* ********************************************************************** *)
(** ** Preservation *)

Lemma npreservation : forall e e' T G D D',
  atyping G D e T D' ->
  red e e' ->
  atyping G D  e' T D'.
Proof with simpl_env; eauto.
  intros e e' T G D D' aTyp Red. 
  generalize dependent e'. 
  (atyping_cases (induction aTyp) Case); 
    intros e' Red;  try solve [inversion Red; subst; eauto].
  Case "atyping_app". inversion Red; subst...
    rename H1 into Hexpr_abs.
    rename H3 into Hvalue2.
    SCase "red_abs". inversion aTyp1; subst...
      SSCase "atyping_uabs".
        rename H8 into Hkind1.
        rename H9 into Htyp2.
        rename H10 into Hdep.
        (* nonlin value e2 implies that its lin ctx is empty *)        
        assert (Hempty_ctx := aTyp2).
        apply nonlin_value_is_under_equal_linctx in Hempty_ctx; auto.
        destruct Hempty_ctx; subst.
        (* The result follows by empty_atyping_through_nonlin_subst_ee *)
        pick fresh x.
        assert (x `notin` L) as Htyp2'. auto.
        apply Htyp2 in Htyp2'. clear Htyp2.
        rewrite_env (nil ++ [(x, gbind_typ T1)] ++ G) in Htyp2'.
        skip. (* we cannot apply empty_atyping_through_nonlin_subst_ee *)
        (* 
        apply empty_atyping_through_nonlin_subst_ee with (u:=e2) in Htyp2'; auto.
        simpl_env in Htyp2'.
        rewrite <- subst_ee_intro in Htyp2'; auto.
        *)
      SSCase "atyping_labs".
        rename H8 into Hkind1.
        rename H9 into Htyp2.
        rename H10 into Hdep.
        (* linear ctx is mon *)
        assert (Hdenv_mon21 := aTyp1).          
        assert (Hdenv_mon32 := aTyp2).
        apply denv_mono in Hdenv_mon21.
        apply denv_mono in Hdenv_mon32.
        assert (D3 <<= D1) as Hdenv_mon31.
          eapply denv_sub_trans; eauto.
        (* G |-> D2 ++ (D1 -- D2) *)
        assert (D2 ++ (D1 -- D2) ~~ D1) as Denv_eq.
          apply minus_unchanged; auto.
        assert (wf_denv G D1) as HwfD1.
          apply typ_regular in aTyp1.
          decompose [and] aTyp1; auto.
        assert (wf_denv G (D2 ++ (D1 -- D2) )) as HwfD12.
          apply eq_preserves_wf_denv with (D:=D1); auto.
             apply denv_eq_symm; auto.
        (* make the assumption a correct form for subst *)     
        pick fresh x.
        assert (x `notin` L) as Htyp2'. auto.
        apply Htyp2 in Htyp2'. clear Htyp2.
        rewrite_env (nil ++ [(x, dbind_typ T1)] ++ D1) in Htyp2'.
        (* apply atyping_through_lin_subst_ee *) 
        assert (Htyp2 := Htyp2').
        apply atyping_through_lin_subst_ee with (e':=e2) (D3:=D2) (D3':=D3) in Htyp2'; auto.
          (* simpl env *)
          simpl_env in Htyp2'.
          rewrite <- subst_ee_intro in Htyp2'; auto.
          destruct Htyp2' as [Htyp2'_in Htyp2'_notin].
          assert (Hdec := in_dec x (fv_ee(open_ee e0 x))).
          destruct Hdec as [Hdec_in | Hdec_notin].
            SSSCase "x `in` fv_ee(open_ee e0 x".
              apply eq_preserves_atyping with (D1:=D2++(D1--D2)) (D2:=D3); auto.
                assert ((D2 -- D2) ~~ dempty) as Heq.
                  apply minus_refl.
                apply denv_eq_refl.
            SSSCase "x `notin` fv_ee(open_ee e0 x)".
               (* denv ctx is mono aux *)
               assert (Hdenv_mon21' := Htyp2). 
               assert (binds x (dbind_typ T1) (nil ++ [(x, dbind_typ T1)] ++ D1)) as Hbinds.
                 skip.
               apply denv_mono_aux2 with (x:=x) (b:=dbind_typ T1) in Hdenv_mon21'; auto.
                   destruct Hdenv_mon21' as [[Hin_fv Hnotin_dom] | [Hnotin_fv Hin_dom]].
                      (* x in fv_ee(open_ee e0 x) /\ x notin dom D2 *)
                      absurd_hyp Hin_fv; auto.
                      (* x notin fv_ee(open_ee e0 x) /\ x in dom D2 *)
                      skip. (* Hin_dom Fr *)
  Case "atyping_tapp". inversion Red; subst...
    rename H3 into Hexpr_tabs.
    SCase "red_tabs". inversion aTyp; subst...
        (* The result follows by atyping_through_subst_te *)
        pick fresh X.
        assert (X `notin` L) as Htyp. auto.
        apply H10 in Htyp. clear H10.
        rewrite_env (nil ++ [(X, gbind_kn K)] ++ G) in Htyp.
        apply atyping_through_subst_te with (P:=T) (K':=K') in Htyp; auto.
        simpl_env in Htyp.
        rewrite <- subst_tt_intro in Htyp; auto.
        rewrite <- subst_te_intro in Htyp; auto.
        rewrite <- subst_tdb_fresh in Htyp; auto.
        rewrite <- subst_tdb_fresh in Htyp; auto.
Qed.
