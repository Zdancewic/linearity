 (** Denv lemmas for Algorithmic Lightweight Linear F *)

Require Export LinF_Lemmas.
Require Export ALinearF_Infrastructure.
Require Import Omega.

Lemma in_dec : forall x A,
  {x `in` A} + {x `notin` A}.
Proof. 
  intros x A.
  apply AtomSetProperties.In_dec.
Qed. 
   
(* ********************************************************************** *)
(**  iso. *)
Lemma denv_to_dmap_iso : forall D x t,
  uniq D ->
  (binds x t D <-> EMap.find x <# D #> = Some t).
Proof.
  intros D x t Uniq.
  generalize dependent x.
  generalize dependent t.
  induction Uniq; intros; simpl.
    split; intro J.
      inversion J.

      apply find_mapsto_iff in J.
        apply empty_mapsto_iff in J. inversion J.

    split; intro J.
      eapply find_mapsto_iff.
      eapply add_mapsto_iff.
      analyze_binds_uniq J; subst.
        right.
        split.
          auto.
          apply IHUniq in BindsTac.
          apply find_mapsto_iff in BindsTac; auto.

      apply find_mapsto_iff in J.
      apply add_mapsto_iff in J.
      destruct J as [[J1 J2] | [J1 J2]]; subst; simpl_env.
        apply binds_app_l. auto. 
        apply binds_app_r. 
          apply find_mapsto_iff in J2.
            apply <- IHUniq in J2. apply J2.
Qed.

Lemma binds_InA_iff : forall M (x:atom) (t:typ),
  binds x t M <-> InA (@EMap.eq_key_elt _) (x,t) M.
Proof.
  split.
    apply In_InA.
      intro x0.
      destruct x0.
      unfold EMap.eq_key_elt.
      unfold EMap.Raw.PX.eqke.
      auto.
    
    generalize dependent x.
    generalize dependent t.
    induction M; intros t x J; simpl.
      apply InA_nil in J. inversion J.

      apply InA_cons in J.
      destruct J as [J | J]. 
        destruct a.
        unfold EMap.eq_key_elt in J.
        unfold EMap.Raw.PX.eqke in J.
        simpl in J.
        destruct J as [J1 J2]; subst; simpl_env.
          apply binds_app_l. auto.

        simpl_env.
        apply binds_app_r. auto.
Qed.

Lemma dmap_to_denv_iso : forall M x t,
  EMap.find x M = Some t <-> binds x t <@ M @>.
Proof.
  intros M x t.
  split; intro J.
    eapply binds_InA_iff.  
    apply find_mapsto_iff in J.
    apply -> elements_mapsto_iff; auto.

    apply binds_InA_iff in J.
    eapply find_mapsto_iff.
    apply -> elements_mapsto_iff; auto.
Qed.   


Lemma notinInA_notindom : forall l a t,
  ~ InA (@EMap.eq_key typ) (a,t) l ->
  a `notin` dom l.
Proof.
  induction l; intros; auto.
    destruct a as [k e].
    simpl_env in *.
    intro J.
    apply H. clear H.
    eapply InA_app_iff ; auto.
    assert (a0 `in` singleton k \/ a0 `in` dom l) as K.
      fsetdec.
    destruct K as [K | K].
       left. apply InA_cons_hd; auto.
       unfold EMap.eq_key.
       unfold EMap.Raw.PX.eqk.
       simpl; auto. fsetdec.

       right.
       assert ({ InA (@EMap.eq_key _) (a0, t) l } + { ~ InA (@EMap.eq_key _) (a0, t) l }) as W.
         apply InA_dec; auto.
           unfold EMap.eq_key.
           unfold EMap.Raw.PX.eqk.
           intros x y.
           destruct (@eq_dec (fst x) (fst y)) as [tHfst | fHfst]; auto.
       destruct W as [W | W]; auto.
         apply IHl in W.
           contradict K; auto.
Qed.
    
Lemma NoDupAList_is_uniq : forall l,
  NoDupA (@EMap.eq_key typ) l -> 
  uniq l.
Proof.
  intros l nodupl.
  induction nodupl; auto.
    assert (NoDupA (@EMap.eq_key _) (x::l)) as V.
      apply NoDupA_cons; auto.
    destruct x as [a t].
    simpl_env.
    apply uniq_push; auto.
      apply notinInA_notindom in H. auto.
Qed.


Lemma dmap_to_denv_is_uniq : forall M,
  uniq <@M@>.
Proof.
  intros M.
  assert (J := @EMap.elements_3w typ M).
  unfold dmap_to_denv.
  apply NoDupAList_is_uniq; auto.
Qed.

Lemma denv_to_from_dmap : forall M,
  M ~~ <# <@M@> #>.
Proof.
  unfold EMap.Equal.
  intros M y.
  remember (EMap.find (elt:=typ) y <# <@M@> #>) as R.
  destruct R; apply sym_eq in HeqR.
    apply denv_to_dmap_iso in HeqR; auto.
      apply dmap_to_denv_is_uniq.
    apply dmap_to_denv_iso in HeqR; auto.

    remember (EMap.find (elt:=typ) y M) as R'.
    destruct R'; apply sym_eq in HeqR'; auto.
      apply dmap_to_denv_iso in HeqR'.
      apply denv_to_dmap_iso in HeqR'; auto.
        apply dmap_to_denv_is_uniq.
      rewrite HeqR' in HeqR. auto.
Qed.   

(* ********************************************************************** *)
(**  Free Variables. *)
Lemma notin_dom_implies_notIn : forall (D:denv) x, 
  x `notin` dom D -> ~ EMap.In x <#D#>.
Proof.
  induction D; intros x H; simpl.
    unfold not. intro J.
    apply empty_in_iff in J. auto.  

    unfold not. intro J.
    destruct a as [y t].
    simpl in H.
    apply add_in_iff in J.
    destruct J as [J | J]; subst; auto.
      apply IHD in J; auto.
Qed.

Lemma dom_binds_iff: forall A (E : list (atom*A)) x,
  x `in` dom E <-> exists a, binds x a E.
Proof.
  intros A E x.
  split; intro J.
    induction E.
      fsetdec.

      destruct a.
      simpl_env in J.
      assert ((x = a) \/ (x `in` dom E)) as G.
        fsetdec.
      destruct G as [G | G]; subst.
        exists a0. 
        simpl_env. 
        apply binds_app_l. auto. 

        apply IHE in G.
        destruct G as [a' G].
        exists a'.
        simpl_env. 
        apply binds_app_r. auto. 

    destruct J as [a J].
    apply binds_In in J; auto.
Qed.    

Lemma notIn_implies_notin_dom : forall (M:dmap) x, 
  ~ EMap.In x M -> x `notin` dom <@ M @>.
Proof.
  intros M x H.
  unfold not. intro J. apply H. clear H.
  apply dom_binds_iff in J.
  destruct J as [a J].
  apply dmap_to_denv_iso in J.
  eapply in_find_iff.
  rewrite J. 
  unfold not. intro H. inversion H.
Qed.  

Lemma in_dom_implies_In : forall (D:denv) x, 
  x `in` dom D -> EMap.In x <#D#>.
Proof.
  induction D; intros x H; simpl.
    apply dom_binds_iff in H.
    destruct H as [a H].
    inversion H.
 
    destruct a as [y t].
    simpl in H.
    assert (x = y \/ x `in` dom D) as J.
      fsetdec.  
    destruct J as [J | J]; subst; auto.
      eapply add_in_iff. auto.
      eapply add_in_iff.
        right. auto.
Qed.

Lemma notIn_implies_notin_dom2 : forall (D:denv) x, 
  ~ EMap.In x <#D#> -> x `notin` dom D.
Proof.
  induction D; intros x J; simpl; auto.
    destruct a.    
    unfold not. intro G. apply J. clear J.
    simpl.
    eapply add_in_iff.
    assert (x = a \/ x `in` dom D) as J.
      fsetdec.  
    destruct J as [J | J]; subst; auto.
      right.
      apply in_dom_implies_In in J; auto.
Qed.

Lemma In_implies_in_dom : forall (D:denv) x, 
  EMap.In x <#D#> -> x `in` dom D.
Proof.
  induction D; intros x H; simpl.
    simpl in H.
    apply empty_in_iff in H.
    inversion H.
 
    destruct a as [y t].
    simpl in H.
    apply add_in_iff in H.
    destruct H as [H | H]; subst; auto.
Qed.


Lemma denv_eq_empty_inv : forall D,
  EMap.Empty <#D#> -> D = dempty.
Proof.
  intros D H.
  destruct D; auto.
    unfold EMap.Empty in H.
    unfold EMap.Raw.Empty in H.
    simpl in H.
    destruct p as [p1 p2].
    assert (J := @add_eq_o typ <#D#> p1 p1 p2).
    assert (p1 = p1) as K. auto.
    apply J in K.
    apply find_mapsto_iff in K.
    apply H in K. 
    inversion K.
Qed.

(* ********************************************************************** *)
(** denv props *)
Lemma denv_dmap_map : forall (D:denv) (f:typ->typ),
  EMap.map f <#D#> ~~ <# map f D #>.
Proof.
  induction D; intro f; simpl.
    intro y.
    remember (EMap.find (elt:=typ) y @@) as R.
    destruct R; apply sym_eq in HeqR.
      apply find_mapsto_iff in HeqR.
        apply empty_mapsto_iff in HeqR. inversion HeqR.

      apply not_find_in_iff in HeqR.
      eapply not_find_in_iff. 
      apply HeqR.

    destruct a.
    intro y.
    remember (EMap.find (elt:=typ) y (a:::f t[+]<#map f D#>)) as R.
    destruct R; apply sym_eq in HeqR.
      apply find_mapsto_iff in HeqR.
      eapply find_mapsto_iff.
      map_iff. apply add_mapsto_iff in HeqR.
      destruct HeqR as [[H1 H2] | [H1 H2]]; subst.
        exists t. split; auto.
           map_iff. auto.
 
        destruct (@Equal_mapsto_iff typ (EMap.map f <#D#>) (<#map f D#>)) as [H3 H4].
        apply (@H3 (@IHD f)) in H2.
        apply map_mapsto_iff in H2.
        destruct H2 as [a0 [H21 H22]].
        exists a0. split; auto.
           map_iff. auto.

      apply not_find_in_iff in HeqR.
      eapply not_find_in_iff. 
      unfold not. intro J. apply HeqR. clear HeqR.
      map_iff. apply -> map_in_iff in J.
      apply add_in_iff in J.
      destruct J as [J | J]; auto.
        right.      
        destruct (@in_if_Equal (EMap.map f <#D#>) (<#map f D#>) (@IHD f) y) as [H1 H2].
        apply H1.
        map_iff. auto.
Qed.


Lemma denv_dmap_disjoint : forall D D',
  disjoint D D' ->
  <#D#> ** <#D'#>.
Proof.
  induction D; intros D' Hd.
    simpl.
    unfold Disjoint.
    intro k.
    unfold not. intro J.
    destruct J as [J1 J2].
    apply empty_in_iff in J1. auto.
   
    simpl. destruct a.
    unfold Disjoint.
    intro k.
    unfold not. intro J.
    destruct J as [J1 J2].
    apply add_in_iff in J1.
    destruct J1 as [J1 | J1]; subst.
      rewrite_env ([(k, t)] ++ D) in Hd.
      apply disjoint_app_1 in Hd.
      apply disjoint_one_1 in Hd.
      apply notin_dom_implies_notIn in Hd. auto.
   
      rewrite_env ([(a, t)] ++ D) in Hd.
      apply disjoint_app_2 in Hd.
      apply IHD in Hd.
      destruct (@Disjoint_alt typ <#D#> <#D'#>) as [H1 H2].
      apply <- in_mapsto_iff in J1.
      destruct J1 as [e1 J1].
      apply <- in_mapsto_iff in J2.
      destruct J2 as [e2 J2].
      apply H1 with (k:=k) (e:=e1) (e':=e2) in Hd; auto.
Qed.

Lemma disjoint_denv_cons_union : forall D1 D2,
  uniq (D1 ++ D2) ->
  <#D1 ++ D2#> ~~ (<#D1#> |_| <#D2#>).
Proof.
  induction D1; intros D2 Huniq y; simpl_env; simpl.
    assert (J:=@dmap_union_empty_refl <#D2#>).
    rewrite J; auto.

    destruct a.
    simpl_env in Huniq.
    assert (J:=Huniq).
    apply uniq_app_2 in J.
    assert (K:=@dmap_add_preserves_Equal 
                <#D1++D2#> (<#D1#>|_|<#D2#>) 
                a t (@IHD1 D2 J)).
    assert ((a:::t[+](<#D1#> |_| <#D2#>)) ~~ ((a:::t[+]<#D1#>) |_| <#D2#>)) as G.
      apply dmap_union_add_distr_left.
        apply notin_dom_implies_notIn.
          apply uniq_app_3 in Huniq.
          apply disjoint_one_1 in Huniq.
          auto.
    assert ((a:::t[+](<#D1 ++ D2#>)) ~~ ((a:::t[+]<#D1#>) |_| <#D2#>)) as GG.
      eapply Equal_trans; eauto.
    rewrite GG. auto.
Qed.

Lemma disjoint_denv_cons_commut : forall D1 D2,
  uniq (D1 ++ D2) ->
  <#D1 ++ D2#> ~~ <#D2 ++ D1#>.
Proof.
  intros D1 D2 Uniq.
  assert (J1:=@disjoint_denv_cons_union D1 D2 Uniq).
  apply uniq_app_iff in Uniq.
  destruct Uniq as [H1 [H2 H3]].
  assert (uniq (D2 ++ D1)) as Uniq'.
    apply uniq_app; auto.
  assert (J2:=@disjoint_denv_cons_union D2 D1 Uniq').
  assert (J3:=@denv_dmap_disjoint D1 D2 H3).
  assert (J4:=@dmap_union_sym <#D1#> <#D2#> J3).
  eapply Equal_trans; eauto.
    eapply Equal_trans; eauto.
      apply Equal_sym; auto.
Qed.

Lemma disjoint_in_notin : forall A B (D:list (atom*A)) (D':list (atom*B)) x,
  disjoint D D' ->
  x `in` dom D -> 
  x `notin` dom D'.
Proof.
  intros A B D D' x Disj Hin.
  generalize dependent D'.
  generalize dependent x.
  induction D; intros.
    simpl Hin. contradict Hin; auto.
    destruct a. simpl in *.
      simpl_env in *.
      apply disjoint_app_l in Disj.
      destruct Disj as [J1 J2].
      assert (x = a \/ x `in` dom D) as J.
        fsetdec.
      destruct J as [J | J]; subst; auto.
        apply disjoint_one_1 in J1; auto.
Qed.

Lemma in_notin_disjoint : forall A B (D:list (atom*A)) (D':list (atom*B)),
  (forall x, x `in` dom D -> x `notin` dom D')->
  disjoint D D'.
Proof.
  intros A B D D' H.
  generalize dependent D'.
  induction D; intros.
    unfold disjoint. simpl. fsetdec.

    destruct a.
    simpl_env in *.
    apply disjoint_app_3.
      apply disjoint_one_2; auto.
        apply H. simpl. fsetdec.
      apply IHD.
        intros x Hin.
        apply H. simpl. fsetdec.
Qed.

Lemma disjoint_remove : forall A (G:list(atom*A)) D D' x T,
  <#[(x,T)]++D#> ~~ <#D'#> ->
  disjoint G D' ->
  disjoint G D.
Proof.
  intros A G D D' x T Heq Hdisj.
  apply in_notin_disjoint.
  intros y Hyin.
  apply disjoint_in_notin with (x:=y) in Hdisj; auto.
  unfold not. intro J. apply Hdisj. clear Hdisj.
  apply In_implies_in_dom.
  eapply in_find_iff.
  rewrite <- Heq.
  eapply in_find_iff.
  simpl. eapply add_in_iff.
  apply in_dom_implies_In in J.
  auto.
Qed.

Lemma in_denv_fv_tt__ex_binds : forall X D,
  X `in` denv_fv_tt D -> 
  exists T, exists x, binds x T D /\ X `in` fv_tt T.
Proof.
  induction D; intro J; simpl in J. 
    contradict J; auto.
    
    destruct a.
    assert (X `in` (fv_tt t) \/ X `in` (denv_fv_tt D)) as H.
      fsetdec.
    destruct H as [H | H].
      exists t. exists a.
      simpl_env.
      split; auto.
  
      apply IHD in H.
      destruct H as [T [x [H1 H2]]].
      exists T. exists x. 
      simpl_env.
      split; auto.
Qed.

Lemma binds__denv_fv_tt : forall x T D X,
  binds x T D ->
  X `in` fv_tt T ->
  X `in` denv_fv_tt D.
Proof.
  intros x T D X Hbinds Hin.
  induction D.
    inversion Hbinds.

    simpl in Hbinds. simpl.
    destruct a.
    analyze_binds Hbinds.
Qed.      

Lemma binds_iff__denv_fv_tt_eq : forall (D1 D2: denv),
  (forall x T, binds x T D1 <-> binds x T D2) ->
  (forall X, X `in` denv_fv_tt D1 <-> X `in` denv_fv_tt D2).
Proof.
  destruct D1; intros D2 H X.
    split; intro J.
      simpl in J. 
      contradict J; auto.

      apply in_denv_fv_tt__ex_binds in J.
      destruct J as [T [x [J1 J2]]].
      apply H in J1.
      inversion J1.
    split; intro J.
      destruct p.
      simpl_env in J.
      assert (X `in` (denv_fv_tt [(a,t)]) \/ X `in` (denv_fv_tt D1)) as J1.
        simpl. simpl in J. fsetdec.
      destruct J1 as [J1 | J1].
        assert (K:=J1).
        apply in_denv_fv_tt__ex_binds in J1.
        destruct J1 as [T [x [J1 J2]]].
        assert (K1:=J1).
        apply binds_one_iff in K1. destruct K1; subst.
        apply binds_app_l with (F:=D1) in J1.
        apply H in J1.
        simpl in K.
        apply binds__denv_fv_tt with (X:=X) in J1; auto.

        apply in_denv_fv_tt__ex_binds in J1.
        destruct J1 as [T [x [J1 J2]]].
        apply binds_app_r with (E:=[(a,t)]) in J1.
        apply H in J1.
        apply binds__denv_fv_tt with (X:=X) in J1; auto.
  
      destruct p. simpl.
      apply in_denv_fv_tt__ex_binds in J.
      destruct J as [T [x [J1 J2]]].
      apply H in J1.
      simpl_env in J1.
      analyze_binds J1.
        apply binds__denv_fv_tt with (X:=X) in BindsTac; auto.
Qed.

Lemma dmap_eq__binds_iff : forall (D1 D2: denv),
  uniq D1 ->
  uniq D2 ->
  <#D1#> ~~ <#D2#> ->
  (forall x T, binds x T D1 <-> binds x T D2).
Proof.
  intros D1 D2 Uniq1 Uniq2 Heq x T.  
  assert (J1 := @denv_to_dmap_iso D1 x T Uniq1).
  assert (J2 := @denv_to_dmap_iso D2 x T Uniq2).
  rewrite Heq in J1.
  split; intro J.
    eapply J2; eauto.
      apply J1; auto.
    eapply J1; eauto.
      apply J2; auto.
Qed.
  
Lemma dmap_eq__denv_fv_tt_eq : forall (D1 D2: denv),
  uniq D1 ->
  uniq D2 ->
  <#D1#> ~~ <#D2#> ->
  (forall X, X `in` denv_fv_tt D1 <-> X `in` denv_fv_tt D2).
Proof.
  intros D1 D2 Uniq1 Uniq2 Heq.
  apply binds_iff__denv_fv_tt_eq.
    apply dmap_eq__binds_iff; auto.
Qed.

Lemma binds_inv : forall A x (a:A) E,
  binds x a E ->
  exists E1, exists E2, E = E2 ++ [(x, a)] ++ E1.
Proof.
  intros A x a E Hbinds.
  induction E.
    inversion Hbinds.
  
    destruct a0 as [y T].
    analyze_binds Hbinds; subst.
      exists E. exists nil. auto.

      apply IHE in BindsTac.
      destruct BindsTac as [E1 [E2 H0]]; subst.
      exists E1. exists ([(y,T)]++E2). auto.
Qed.


Lemma denv_find_some__map_find_some : forall D x T f,
  EMap.find x <#D#> = Some T ->
  EMap.find x <#map f D#> = Some (f T).
Proof.
  induction D; intros x T f H.
    rewrite empty_o in H. inversion H.

    simpl in *. destruct a.
    apply find_mapsto_iff in H.
    apply add_mapsto_iff in H.
    eapply find_mapsto_iff.
    eapply add_mapsto_iff.
    destruct H as [[H1 H2]|[H1 H2]]; subst; auto.
      right.
      split; auto.
        eapply find_mapsto_iff.
        eapply IHD; eauto.
          eapply find_mapsto_iff; auto.
Qed.      

Lemma denv_remove_find_some__map_remove_find_some : forall D x T f y,
  EMap.find x (<#D#>[-]y) = Some T ->
  EMap.find x (<#map f D#>[-]y) = Some (f T).
Proof.
  induction D; intros x T f y H.
    apply find_mapsto_iff in H.
    apply remove_mapsto_iff in H.
    destruct H as [H1 H2].
    apply find_mapsto_iff in H2.
    rewrite empty_o in H2. inversion H2.

    simpl in *. destruct a.
    apply find_mapsto_iff in H.
    apply remove_mapsto_iff in H.
    destruct H as [H1 H2].
    eapply find_mapsto_iff.
    eapply remove_mapsto_iff.
    split; auto.
    apply add_mapsto_iff in H2.
    eapply add_mapsto_iff.
    destruct H2 as [[H21 H22]|[H21 H22]]; subst; auto.
      right.
      split; auto.
        eapply find_mapsto_iff.
        apply denv_find_some__map_find_some; auto.
        eapply find_mapsto_iff; auto.
Qed.      

Lemma denv_find_nnone_map_iff : forall D x f,
  EMap.find x <#map f D#> <> None <->
  EMap.find x <#D#> <> None .
Proof.
  induction D; intros x f.
    split; intro H.
      rewrite empty_o in H. contradict H; auto.
      rewrite empty_o in H. contradict H; auto.

    split; intro H; simpl in *. 
      destruct a.
      apply in_find_iff in H.
      apply add_in_iff in H.
      eapply in_find_iff.
      eapply add_in_iff.
      destruct H as [H|H]; subst; auto.
        right.
        eapply in_find_iff.
          destruct (@IHD x f) as [IHD1 IHD2].
          apply IHD1; eauto.
            eapply in_find_iff; auto.

      destruct a.
      apply in_find_iff in H.
      apply add_in_iff in H.
      eapply in_find_iff.
      eapply add_in_iff.
      destruct H as [H|H]; subst; auto.
        right.
        eapply in_find_iff.
          destruct (@IHD x f) as [IHD1 IHD2].
          apply IHD2; eauto.
            eapply in_find_iff; auto.
Qed.      


Lemma denv_remove_find_none__map_remove_find_none : forall D x f y,
  EMap.find x (<#D#>[-]y) = None ->
  EMap.find x (<#map f D#>[-]y) = None.
Proof.
  induction D; intros x f y H.
    apply not_find_in_iff in H.
    eapply not_find_in_iff.
    unfold not. intro J. apply H. clear H.
    apply remove_in_iff in J.
    destruct J as [J1 J2].
    apply in_find_iff in J2.
    rewrite empty_o in J2. contradict J2; auto.

    simpl in *. destruct a.
    apply not_find_in_iff in H.
    eapply not_find_in_iff.
    unfold not. intro J. apply H. clear H.
    apply remove_in_iff in J.
    destruct J as [J1 J2].
    eapply remove_in_iff.
    split; auto.
    apply add_in_iff in J2.
    eapply add_in_iff.
    destruct J2 as [J2|J2]; subst; auto.
      right.
      eapply in_find_iff.
      apply in_find_iff in J2.
      destruct (@denv_find_nnone_map_iff D x f) as [J21 J22].
      apply J21 in J2; auto.
Qed.      

Lemma denv_find_none_map_iff : forall D x f,
  EMap.find x <#map f D#> = None <->
  EMap.find x <#D#> = None .
Proof.
  intros D x f.
  split; intro J.
    remember (EMap.find x <#D#>) as R.
    destruct R; apply sym_eq in HeqR; auto.
      assert (EMap.find x <#D#> <> None) as H.
        rewrite HeqR. unfold not. intro H. inversion H.
      apply (@denv_find_nnone_map_iff D x f) in H.
      rewrite J in H. contradict H; auto.

    remember (EMap.find x <#map f D#>) as R.
    destruct R; apply sym_eq in HeqR; auto.
      assert (EMap.find x <#map f D#> <> None) as H.
        rewrite HeqR. unfold not. intro H. inversion H.
      apply (@denv_find_nnone_map_iff D x f) in H.
      rewrite J in H. contradict H; auto.
Qed.

Lemma map_find_some__denv_find_some : forall D x T f,
  EMap.find x <#map f D#> = Some T ->
  exists T', EMap.find x <#D#> = Some T' /\ f T' = T.
Proof.
  induction D; intros x T f H.
    rewrite empty_o in H. inversion H.

    simpl in *. destruct a.
    apply find_mapsto_iff in H.
    apply add_mapsto_iff in H.
    destruct H as [[H1 H2]|[H1 H2]]; subst; auto.
      exists t. split; auto.
      eapply find_mapsto_iff.
      eapply add_mapsto_iff; auto.
     
      apply find_mapsto_iff in H2; auto.
      apply IHD in H2; auto.
      destruct H2 as [T' [H21 H22]]; subst.
      exists T'. split; auto. 
      eapply find_mapsto_iff.
      eapply add_mapsto_iff; auto.
      right.
      split; auto.
        eapply find_mapsto_iff; auto.
Qed.      

Lemma disjoint_denv_cons_3commut_aux : forall B C D,
  uniq(B++C++D) ->
  (B++C++D) ~~~ (D++C++B).
Proof.
  intros B C D Uniq.
  apply Equal_trans with (m':=<#B#>|_|<#C++D#>).
    apply disjoint_denv_cons_union; auto.    
    apply Equal_trans with (m':=<#B#>|_|<#D++C#>).
      apply dmap_Equal_rewrite_Union_right with (M2:=<#C++D#>).
        apply disjoint_denv_cons_commut; auto.
          apply uniq_app_2 in Uniq; auto.
      apply Equal_refl.

    apply Equal_trans with (m':=<#D++C#>|_|<#B#>).
      apply dmap_union_sym.
        apply denv_dmap_disjoint.
          apply uniq_app_iff in Uniq.
          destruct Uniq as [H1 [H2 H3]].
          apply disjoint_sym in H3.
          apply <- disjoint_sym.
          apply disjoint_app_3.
            apply disjoint_app_2 in H3; auto.
            apply disjoint_app_1 in H3; auto.
      apply Equal_sym.
      rewrite_env ((D++C)++B).
      apply disjoint_denv_cons_union; auto.    
        apply uniq_app_iff in Uniq.
        destruct Uniq as [H1 [H2 H3]].
        apply uniq_app; auto.
          solve_uniq.
          apply disjoint_sym in H3.
          apply disjoint_app_3.
            apply disjoint_app_2 in H3; auto.
            apply disjoint_app_1 in H3; auto.
Qed.

Lemma disjoint_denv_cons_commut_aux : forall A B C D E,
  uniq(A++B++C++D++E) ->
  (A++B++C++D++E) ~~~ (A++D++C++B++E).
Proof.
  intros A B C D E Uniq.
  apply Equal_trans with (m':=<#A#>|_|<#B++C++D++E#>).
    apply disjoint_denv_cons_union; auto.    

    apply Equal_sym.
    apply dmap_Equal_rewrite_Union_right with (M2:=<#D++C++B++E#>).
      apply Equal_trans with (m':=<#B++C++D#>|_|<#E#>).
        apply dmap_Equal_rewrite_Union_left with (M1:=<#D++C++B#>).
          apply disjoint_denv_cons_3commut_aux.
            solve_uniq.
        rewrite_env ((D++C++B)++E).
        apply disjoint_denv_cons_union; auto.    
          solve_uniq.

        apply Equal_sym.
        rewrite_env ((B++C++D)++E).
        apply disjoint_denv_cons_union; auto.    
          solve_uniq.

      apply disjoint_denv_cons_union; auto.    
        solve_uniq.
Qed.

Lemma denv_map_preserves_Equal : forall D D' f,
  D ~~~ D' ->
  map f D ~~~ map f D'.
Proof.
  intros D D' f Heq x.
  remember (EMap.find x <#map f D'#>) as R.
  destruct R; apply sym_eq in HeqR; auto.
    apply map_find_some__denv_find_some in HeqR.
    destruct HeqR as [T' [H1 H2]]; subst.
    rewrite <- Heq in H1.
    apply denv_find_some__map_find_some; auto.

    destruct (@denv_find_none_map_iff D' x f) as [H1 H2].
    apply H1 in HeqR.
    rewrite <- Heq in HeqR.
    destruct (@denv_find_none_map_iff D x f) as [H3 H4].
    apply H4; auto.
Qed.

Lemma binds_permutation : forall x T D D',
  uniq D ->
  uniq D' ->
  binds x T D ->
  D ~~~ D' ->
  binds x T D'.
Proof.
  intros x T D D' Huniq Huniq' H1 H2.
  apply denv_to_dmap_iso in H1; auto.
  eapply denv_to_dmap_iso; auto.
  rewrite H2 in H1; auto.
Qed.

Lemma denv_add_preserves_Equal : forall (D D':denv) x T,
  D ~~~ D' ->
  ([(x, T)] ++ D) ~~~ ([(x, T)] ++ D').
Proof.
  intros D D' x T H.
  intro y. simpl.
  eapply dmap_add_preserves_Equal; auto.
Qed.

Lemma denv_equal_in_dom_iff : forall D D' x,
  D ~~~ D' -> (x `in` dom D <-> x `in` dom D').
Proof.
  intros D D' x Heq.
  split; intro J.
    apply in_dom_implies_In in J.
    apply in_find_iff in J.
    rewrite Heq in J.
    apply in_find_iff in J.
    apply In_implies_in_dom in J; auto.

    apply in_dom_implies_In in J.
    apply in_find_iff in J.
    rewrite <- Heq in J.
    apply in_find_iff in J.
    apply In_implies_in_dom in J; auto.
Qed.

Lemma denv_equal_notin_dom_iff : forall D D' x,
  D ~~~ D' -> (x `notin` dom D <-> x `notin` dom D').
Proof.
  intros D D' x Heq.
  split; intro J.
    apply notIn_implies_notin_dom2.
    unfold not. intro H.
    apply in_find_iff in H.
    rewrite <- Heq in H.
    apply in_find_iff in H.
    apply In_implies_in_dom in H.
    contradict H; auto.

    apply notIn_implies_notin_dom2.
    unfold not. intro H.
    apply in_find_iff in H.
    rewrite Heq in H.
    apply in_find_iff in H.
    apply In_implies_in_dom in H.
    contradict H; auto.
Qed.

Lemma remove_iff_raw_remove : forall M x,
  <@M [-] x@> = EMap.Raw.remove x M.
Proof.
  simpl. auto.
Qed.

Lemma singleton_diff_empty : forall x T D,
  x `in` dom D ->
  (<#[(x, T)]#>--<#D#>) ~~ @@.
Proof.
  intros x T D xinD y.
  remember (EMap.find (elt:=typ) y @@) as R.
  apply sym_eq in HeqR.
  destruct R.
    apply find_mapsto_iff in HeqR.
    apply empty_mapsto_iff in HeqR.
    inversion HeqR.

    clear HeqR.
    eapply not_find_in_iff.
    intro J.
    apply diff_in_iff in J.
    destruct J as [J1 J2].
    simpl in J1.
    apply add_in_iff in J1.
    destruct J1 as [J1 | J1]; subst.
      apply notIn_implies_notin_dom2 in J2.
      apply J2; auto.
  
      apply empty_in_iff in J1. auto.
Qed.    

Lemma singleton_diff_refl : forall x T D,
  x `notin` dom D ->
  (<#[(x, T)]#>--<#D#>) ~~ <#[(x, T)]#>.
Proof.
  intros x T D xinD y.
  remember (EMap.find (elt:=typ) y <#[(x, T)]#>) as R.
  apply sym_eq in HeqR.
  destruct R.
    eapply find_mapsto_iff.
    eapply diff_mapsto_iff.
    apply find_mapsto_iff in HeqR.
    simpl in HeqR.
    apply add_mapsto_iff in HeqR.
    destruct HeqR as [[H1 H2] | [H1 H2]]; subst.
      split; auto.
        simpl. eapply add_mapsto_iff. auto.
        apply notin_dom_implies_notIn; auto.

      apply empty_mapsto_iff in H2.
      inversion H2.
  
    eapply not_find_in_iff.
    apply not_find_in_iff in HeqR.
    intro J. apply HeqR. clear HeqR.
    apply diff_in_iff in J.
    destruct J as [J1 J2].
    simpl in J1.
    apply add_in_iff in J1.
    destruct J1 as [J1 | J1]; subst.
      simpl.
      eapply add_in_iff. auto.
  
      simpl.
      eapply add_in_iff. auto.
Qed.

Lemma remove_is_singleton_diff : forall M x T,
  (M [-] x) ~~ (M -- <#[(x, T)]#>).
Proof.
  intros M x T y.
  remember (EMap.find (elt:=typ) y (M--<#[(x,T)]#>)) as R.
  apply sym_eq in HeqR.
  destruct R.
    eapply find_mapsto_iff.
    eapply remove_mapsto_iff.
    apply find_mapsto_iff in HeqR.
    apply diff_mapsto_iff in HeqR.
    destruct HeqR as [H1 H2].
    split; auto.
      intro J. subst.
      apply H2. clear H2.
      simpl. eapply add_in_iff. auto.

    eapply not_find_in_iff.
    apply not_find_in_iff in HeqR.
    intro J. apply HeqR. clear HeqR.
    simpl in J. 
    eapply diff_in_iff.
    apply remove_in_iff in J.
    destruct J as [J1 J2].
    split; auto.
      intro J. apply J1. clear J2.
      simpl in J. apply add_in_iff in J.
      destruct J; auto.
        apply empty_in_iff in H.
        inversion H.
Qed.

Lemma denv_Equal_in_dom : forall D1 D2 x,  
  D1 ~~~ D2 ->  
  x `in` dom D1 ->   
  x `in` dom D2.
Proof.
  intros D1 D2 x Heq HinD1. 
  apply in_dom_implies_In in HinD1.
  apply in_find_iff in HinD1.
  rewrite Heq in HinD1.
  apply in_find_iff in HinD1.
  apply In_implies_in_dom in HinD1; auto.
Qed.

Lemma denv_Equal_notin_dom : forall D1 D2 x,  
  D1 ~~~ D2 ->  
  x `notin` dom D1 ->   
  x `notin` dom D2.
Proof.
  intros D1 D2 x Heq HnotinD1. 
  apply notin_dom_implies_notIn in HnotinD1.
  eapply notIn_implies_notin_dom2.
  intro J.
  apply HnotinD1. clear HnotinD1.
  apply in_find_iff in J.
  rewrite <- Heq in J.
  apply in_find_iff in J. auto.
Qed.

Lemma mapsto_denv_fv_tt : forall D x t y,
  EMap.MapsTo x t <#D#> ->
  y `in` fv_tt t ->
  y `in` denv_fv_tt D.
Proof.
  induction D; intros x t Y Hmaps Hyint.
    apply empty_mapsto_iff in Hmaps.
    inversion Hmaps.
    
    simpl in *.
    destruct a.
    apply add_mapsto_iff in Hmaps.
    destruct Hmaps as [[H1 H2]|[H1 H2]]; subst; auto.
      apply IHD with (y:=Y) in H2; auto.
Qed.

Lemma denv_sub_in_denv_fv_tt : forall D1 D2 x,
  uniq D2 -> uniq D1 ->
  <#D2#> <<= <#D1#> ->
  x `in` denv_fv_tt D2 ->
  x `in` denv_fv_tt D1.
Proof. 
  intros D1 D2 x Uniq2 Uniq1 Hsub HinD2.
  generalize dependent D1.  
  generalize dependent x.
  induction Uniq2; simpl; intros.
    contradict HinD2; auto.

    assert (x0 `in` fv_tt a \/ x0 `in` denv_fv_tt E) as J.
      fsetdec.
    destruct J as [J | J].
      unfold EMap_Submap in Hsub.
      destruct Hsub as [H1 H2].
      assert (EMap.MapsTo x a (x:::a[+]<#E#>)) as K.
        eapply add_mapsto_iff; auto.
      assert (EMap.In x (x:::a[+]<#E#>)) as KK.
        eapply add_in_iff; auto.
      apply H1 in KK.
      apply in_find_iff in KK.
      remember (EMap.find (elt:=typ) x <#D1#>) as R.
      destruct R; apply sym_eq in HeqR.
        apply find_mapsto_iff in HeqR.        
        apply H2 with (t':=t) in K; auto.  
          apply beq_typ_iff_eq in K. subst.
          eapply mapsto_denv_fv_tt; eauto.
        contradict KK; auto.

      apply IHUniq2; auto.
        apply dmap_sub_remove_left with (x:=x) in Hsub.
          apply dmap_Equal_rewrite_Sub_left with (M1:=(x:::a[+]<#E#>)[-]x); auto.
            apply dmap_add_remove_refl; auto.
              apply notin_dom_implies_notIn; auto.
Qed.
    
Lemma denv_sub_notin_denv_fv_tt : forall D1 D2 x,  
  uniq D2 -> uniq D1 ->
  <#D2#> <<= <#D1#> ->  
  x `notin` denv_fv_tt D1 ->
  x `notin` denv_fv_tt D2.    
Proof. 
  intros D1 D2 x Uniq2 Uniq1 Hsub HnotinD1.
  destruct (@in_dec x (denv_fv_tt D2)) as [H | H]; auto.
  apply denv_sub_in_denv_fv_tt with (D1:=D1) in H; auto.
Qed.

Lemma denv_sub_in_dom : forall D1 D2 x,
  <#D2#> <<= <#D1#> ->
  x `in` dom D2 ->  
  x `in` dom D1.
Proof. 
  intros D1 D2 x Hsub HinD2.
  destruct Hsub as [Hsub1 Hsub2].
  apply in_dom_implies_In in HinD2.
  apply Hsub1 in HinD2.
  apply In_implies_in_dom in HinD2; auto.
Qed.

Lemma denv_sub_notin_dom : forall D1 D2 x,
  uniq D2 -> uniq D1 ->
  <#D2#> <<= <#D1#> ->
  x `notin` dom D1 ->  
  x `notin` dom D2.
Proof. 
  intros D1 D2 x Uniq2 Uniq1 Hsub HnotinD1.
  intro J.
  apply HnotinD1.
  apply denv_sub_in_dom with (x:=x) in Hsub; auto.
Qed.

Lemma dmap_remove_renaming_head : forall E E' x V a y,
  uniq ([(x, V)]++E) ->
  uniq ([(x, V)]++E') ->
  <#[(x, V)]++E#>[-]a ~~ <#[(x, V)]++E'#> ->
  y <> a ->
  <#[(y, V)]++E#>[-]a ~~ <#[(y, V)]++E'#>.
Proof.
  intros E E' x V a y Uniq Uniq' Heq Hyna.
  intro z.
  remember (EMap.find (elt:=typ) z (<#[(y,V)]++E#>[-]a)) as R.
  destruct R; apply sym_eq in HeqR; apply sym_eq.
    apply find_mapsto_iff in HeqR.
    apply remove_mapsto_iff in HeqR.
    destruct HeqR as [Hanz Hmaps].
    simpl in *.
    apply add_mapsto_iff in Hmaps.
    destruct Hmaps as [[H1 H2]|[H1 H2]]; subst.
      eapply find_mapsto_iff.
      eapply add_mapsto_iff; auto.

      eapply find_mapsto_iff.
      eapply add_mapsto_iff.
      right. split; auto.
        assert (EMap.MapsTo z t ((x:::V[+]<#E#>)[-]a)) as J.
          eapply remove_mapsto_iff.
          split; auto.
            eapply add_mapsto_iff.
            right. split; auto.
              destruct (x==z); subst; auto.
                inversion Uniq; subst.
                apply notin_dom_implies_notIn in H5.
                apply find_mapsto_iff in H2.
                apply not_find_in_iff in H5.
                rewrite H5 in H2.
                inversion H2.
        rewrite Heq in J.
        apply add_mapsto_iff in J.
        destruct J as [[J1 J2]|[J1 J2]]; subst; auto.
          inversion Uniq; subst.
          apply notin_dom_implies_notIn in H5.
          apply find_mapsto_iff in H2.
          apply not_find_in_iff in H5.
          rewrite H5 in H2.
          inversion H2.

    apply not_find_in_iff in HeqR.
    eapply not_find_in_iff.
    intro J.
    apply HeqR. clear HeqR. simpl in *.
    eapply remove_in_iff.
    apply add_in_iff in J.
    destruct J as [J | J]; subst.
      split; auto.
        eapply add_in_iff. auto.

      assert (EMap.In z (x:::V[+]<#E'#>)) as H.
        eapply add_in_iff. auto.
      rewrite <- Heq in H.
      apply remove_in_iff in H.
      destruct H as [H1 H2].
      destruct (a==z); subst.
        split; auto.
        eapply add_in_iff.
        apply add_in_iff in H2.
        destruct H2 as [H2 | H2]; subst; auto.
          inversion Uniq'; subst.
          apply notin_dom_implies_notIn in H4.
          contradict J; auto.
          
        split; auto.
          apply add_in_iff in H2.
          destruct H2 as [H2 | H2]; subst.
            inversion Uniq'; subst.
            apply notin_dom_implies_notIn in H4.
            contradict J; auto.
     
            eapply add_in_iff. auto.
Qed.            

Lemma notin_dom_diff : forall D x D',
  uniq D ->
  x `notin` dom D ->
  x `notin` dom <@<#D#> -- <#D'#>@>.
Proof.
  intros D x D' uniqD notinD.
  assert ((<#D#>--<#D'#>)<<=<#D#>) as Hsub.
    apply dmap_diff_mono; auto.
  apply denv_sub_notin_dom with (D1:=D); auto.
    apply dmap_to_denv_is_uniq.  
  apply dmap_Equal_rewrite_Sub_left with (M1:=(<#D#>--<#D'#>)); auto.
    apply denv_to_from_dmap; auto.
Qed.

Lemma notin_denv_fv_tt_diff : forall D x D',
  uniq D ->
  x `notin` denv_fv_tt D ->
  x `notin` denv_fv_tt <@<#D#> -- <#D'#>@>.
Proof.
  intros D x D' uniqD notinD.
  assert ((<#D#>--<#D'#>)<<=<#D#>) as Hsub.
    apply dmap_diff_mono.
  apply denv_sub_notin_denv_fv_tt with (D1:=D); auto.
    apply dmap_to_denv_is_uniq.
  apply dmap_Equal_rewrite_Sub_left with (M1:=(<#D#>--<#D'#>)); auto.
    apply denv_to_from_dmap.
Qed.

Lemma add_diff_commut : forall z V D D0,
  uniq D ->
  z `notin` dom D0 `union` dom D ->
  <@<#[(z, V)]++D#>--<#D0#>@> ~~~ [(z, V)]++(<@<#D#>--<#D0#>@>).
Proof.
  intros z V D D0 uniqD znotinD.
  apply Equal_trans with (m':=<#[(z,V)]++D#>--<#D0#>).
    apply Equal_sym.
      apply denv_to_from_dmap.
    apply Equal_trans with (m':=<#[(z,V)]#>|_|<#<@<#D#>--<#D0#>@>#>).
      apply dmap_Equal_rewrite_Union_right with (M2:=(<#D#>--<#D0#>)); auto.
        apply denv_to_from_dmap; auto.
        apply Equal_trans with (m':=(<#[(z,V)]#>--<#D0#>)|_|(<#D#>--<#D0#>)).
          apply Equal_trans with (m':=(<#[(z,V)]#>|_|<#D#>)--<#D0#>).
            apply dmap_Equal_rewrite_diff_left with (M1:=(<#[(z,V)]++D#>)); auto.
              apply disjoint_denv_cons_union.
                apply uniq_push; auto.
              apply Equal_refl.
            apply dmap_union_diff_distr.
          apply dmap_Equal_rewrite_Union_left with (M1:=(<#[(z,V)]#>--<#D0#>)).
            apply singleton_diff_refl; auto.
            apply Equal_refl.
       apply Equal_sym. 
         apply disjoint_denv_cons_union.
           apply uniq_push; auto.
             apply dmap_to_denv_is_uniq.
             apply notin_dom_diff; auto.
Qed.
    
Lemma notin_dom_union : forall D x D',
  x `notin` dom D ->
  x `notin` dom D' ->
  x `notin` dom <@<#D#> |_| <#D'#>@>.
Proof.
  intros D x D' notinD notinD'.
  apply notIn_implies_notin_dom.
  intro J.
  apply update_in_iff in J.
  destruct J as [J | J].
    apply notinD.
    apply In_implies_in_dom; auto.

    apply notinD'.
    apply In_implies_in_dom; auto.
Qed.

Lemma dmap_denv_disjoint : forall D D',
  <#D#> ** <#D'#> ->
  disjoint D D'.
Proof.  
    induction D; intros D' Hd.
    unfold disjoint. simpl. fsetdec.
   
    simpl in *. destruct a.
    unfold Disjoint in Hd.
    simpl_env. 
    eapply disjoint_app_l.
    split.
      apply disjoint_one_2.
      apply notIn_implies_notin_dom2.
      intro J.
      apply (@Hd a).
      split; auto.
        eapply add_in_iff. auto.
          
      apply IHD.
      intros k J.
      apply (@Hd k).
      destruct J as [J1 J2].
      split; auto.
        eapply add_in_iff. auto.
Qed.     

Lemma in_denv_fv_tt_union : forall D x D',
  uniq D -> uniq D' -> <#D#> ** <#D'#> ->
  (x `in` denv_fv_tt <@<#D#> |_| <#D'#>@> <->
   x `in` denv_fv_tt (D ++ D')).
Proof.
  intros D x D' uniqD uniqD' disj.
  apply binds_iff__denv_fv_tt_eq.
  intros y T.
  split; intro J.
    eapply denv_to_dmap_iso. 
      apply uniq_app_4; auto.
        apply dmap_denv_disjoint; auto.
      apply denv_to_dmap_iso in J.
        apply dmap_to_denv_is_uniq.
        eapply find_mapsto_iff.    
        apply find_mapsto_iff in J.
        assert (H' := @denv_to_from_dmap (<#D#>|_|<#D'#>)).
        eapply (@Equal_mapsto_rewrite (<#D#>|_|<#D'#>) <#<@<#D#>|_|<#D'#>@>#>) in J; auto.
        assert ((<#D#>|_|<#D'#>) ~~ <#D++D'#>) as H''.
          apply Equal_sym.
            apply disjoint_denv_cons_union.
              apply uniq_app_4; auto.
                apply dmap_denv_disjoint; auto.
        eapply (@Equal_mapsto_rewrite (<#D#>|_|<#D'#>) <#D++D'#>); auto.
                  
    eapply denv_to_dmap_iso. 
      apply dmap_to_denv_is_uniq.
      apply denv_to_dmap_iso in J.
        apply uniq_app_4; auto.
          apply dmap_denv_disjoint; auto.
        eapply find_mapsto_iff.    
        apply find_mapsto_iff in J.
        assert (H' := @denv_to_from_dmap (<#D#>|_|<#D'#>)).
        eapply (@Equal_mapsto_rewrite (<#D#>|_|<#D'#>)); auto.
        assert ((<#D#>|_|<#D'#>) ~~ <#D++D'#>) as H''.
          apply Equal_sym.
            apply disjoint_denv_cons_union.
              apply uniq_app_4; auto.
                apply dmap_denv_disjoint; auto.
        eapply (@Equal_mapsto_rewrite (<#D#>|_|<#D'#>) <#D++D'#>); auto.
Qed.

Lemma denv_fv_tt_app : forall D D',
  denv_fv_tt (D ++ D') [=] denv_fv_tt D `union` denv_fv_tt D'.
Proof.
  induction D as [ | [x1 a1] ]; simpl.
    fsetdec.
    intro D'. assert (J := @IHD D').
    fsetdec.
Qed.

Lemma notin_denv_fv_tt_union : forall D x D',
  uniq D -> uniq D' -> <#D#> ** <#D'#> ->
  (x `notin` denv_fv_tt D /\ x `notin` denv_fv_tt D' 
    <->
  x `notin` denv_fv_tt <@<#D#> |_| <#D'#>@>).
Proof.
  intros D x D' uniqD uniqD' disj.
  split; intros J.
    intro H.
    apply in_denv_fv_tt_union in H; auto.
    rewrite denv_fv_tt_app in H.
    destruct J as [J1 J2].
    assert (x `in` (denv_fv_tt D) \/ x `in` (denv_fv_tt D')) as K.
      fsetdec.
    destruct K as [K | K].
      apply J1. auto.
      apply J2. auto.

    split.
      intro H. apply J. clear J.
      eapply in_denv_fv_tt_union; auto.
      rewrite denv_fv_tt_app. fsetdec.

      intro H. apply J. clear J.
      eapply in_denv_fv_tt_union; auto.
      rewrite denv_fv_tt_app. fsetdec.
Qed.

Lemma add_union_commut : forall z V D D0,
  uniq D ->
  <#D#> ** <#D0#> ->
  z `notin` dom D0 `union` dom D ->
  <@<#[(z, V)]++D#>|_|<#D0#>@> ~~~ [(z, V)]++(<@<#D#>|_|<#D0#>@>).
Proof.
  intros z V D D0 uniqD disj znotinD.
  apply Equal_trans with (m':=<#[(z,V)]++D#>|_|<#D0#>).
    apply Equal_sym.
      apply denv_to_from_dmap.
    apply Equal_trans with (m':=<#[(z,V)]#>|_|<#<@<#D#>|_|<#D0#>@>#>).
      apply dmap_Equal_rewrite_Union_right with (M2:=(<#D#>|_|<#D0#>)); auto.
        apply denv_to_from_dmap; auto.
        apply Equal_trans with (m':=(<#[(z,V)]#>|_|<#D0#>)|_|(<#D#>|_|<#D0#>)).
          apply Equal_trans with (m':=(<#[(z,V)]#>|_|<#D#>)|_|<#D0#>).
            apply dmap_Equal_rewrite_Union_left with (M1:=(<#[(z,V)]++D#>)); auto.
              apply disjoint_denv_cons_union.
                apply uniq_push; auto.
              apply Equal_refl.
            apply dmap_union_distr.
          apply Equal_trans with (m':=<#[(z,V)]#>|_|(<#D0#>|_|(<#D#>|_|<#D0#>))).
            apply dmap_union_assoc.
            apply Equal_sym.
              apply dmap_Equal_rewrite_Union_right with (M2:=(<#D#>|_|(<#D0#>|_|<#D0#>))); auto.
                apply Equal_trans with (m':=(<#D0#>|_|<#D#>)|_|<#D0#>).
                  apply Equal_trans with (m':=(<#D#>|_|<#D0#>)|_|<#D0#>).
                    apply dmap_Equal_rewrite_Union_left with (M1:=(<#D#>|_|<#D0#>)).
                      apply Equal_refl.                      
                    apply Equal_sym.
                      apply dmap_union_assoc.
                  apply dmap_Equal_rewrite_Union_left with (M1:=(<#D#>|_|<#D0#>)); auto.
                    apply dmap_union_sym; auto.
                    apply Equal_refl.
                  apply dmap_union_assoc.
                apply dmap_Equal_rewrite_Union_right with (M2:=(<#D#>|_|<#D0#>)); auto.
                  apply dmap_Equal_rewrite_Union_right with (M2:=<#D0#>); auto.
                    apply Equal_sym.
                      apply dmap_union_refl.
                    apply Equal_refl.
                  apply Equal_refl.
       apply Equal_sym. 
         apply disjoint_denv_cons_union.
           apply uniq_push; auto.
             apply dmap_to_denv_is_uniq.
             apply notin_dom_union; auto.
Qed.

Lemma dmap_denv_Equal_injection : forall M M',
  M ~~ M' <-> <#<@M@>#> ~~ <#<@M'@>#>.
Proof.
  intros M M'.
  split; intro J.
    eapply Equal_trans with (m':=M).
      apply Equal_sym.
        apply denv_to_from_dmap.
      eapply Equal_trans with (m':=M'); auto.
        apply denv_to_from_dmap.

    eapply Equal_trans with (m':=<#<@M@>#>).
      apply denv_to_from_dmap.
      eapply Equal_trans with (m':=<#<@M'@>#>); auto.
        apply Equal_sym.
          apply denv_to_from_dmap.
Qed.

Lemma dmap_denv_Equal_injection_add : forall M M',
  M ~~ M' -> <#<@M@>#> ~~ <#<@M'@>#>.
Proof.
  intros M M' J.
  apply dmap_denv_Equal_injection in J; auto.
Qed.

Lemma dmap_denv_Equal_injection_remove : forall M M',
  <#<@M@>#> ~~ <#<@M'@>#> -> M ~~ M'.
Proof.
  intros M M' J.
  apply dmap_denv_Equal_injection in J; auto.
Qed.

Lemma dmap_denv_Sub_injection : forall M M',
  M <<= M' <-> <#<@M@>#> <<= <#<@M'@>#>.
Proof.
  intros M M'.
  split; intro J.
    apply dmap_Equal_rewrite_Sub_left with (M1:=M).
      apply denv_to_from_dmap.
      apply dmap_Equal_rewrite_Sub_right with (M2:=M'); auto.
        apply denv_to_from_dmap.
                 
    apply dmap_Equal_rewrite_Sub_left with (M1:=<#<@M@>#>).
      apply Equal_sym.
        apply denv_to_from_dmap.
      apply dmap_Equal_rewrite_Sub_right with (M2:=<#<@M'@>#>); auto.
        apply Equal_sym.
          apply denv_to_from_dmap.
Qed.

Lemma dmap_denv_Sub_injection_add : forall M M',
  M <<= M' -> <#<@M@>#> <<= <#<@M'@>#>.
Proof.
  intros M M' J.
  apply dmap_denv_Sub_injection in J; auto.
Qed.

Lemma dmap_denv_Sub_injection_remove : forall M M',
  <#<@M@>#> <<= <#<@M'@>#> -> M <<= M'.
Proof.
  intros M M' J.
  apply dmap_denv_Sub_injection in J; auto.
Qed.


Lemma dmap_denv_diff_injection : forall M M',
  M ** M' <-> <#<@M@>#> ** <#<@M'@>#>.
Proof.
  intros M M'.
  split; intro J.
    apply dmap_Equal_preserves_disjoint_left with (M1:=M).
      apply dmap_Equal_preserves_disjoint_right with (M2:=M'); auto.
        apply Equal_sym.
          apply denv_to_from_dmap.
      apply Equal_sym.
        apply denv_to_from_dmap.

    apply dmap_Equal_preserves_disjoint_left with (M1:=<#<@M@>#>).
      apply dmap_Equal_preserves_disjoint_right with (M2:=<#<@M'@>#>); auto.
        apply denv_to_from_dmap.
      apply denv_to_from_dmap.
Qed.

Lemma dmap_denv_diff_injection_add : forall M M',
  M ** M' -> <#<@M@>#> ** <#<@M'@>#>.
Proof.
  intros M M' J.
  apply dmap_denv_diff_injection in J; auto.
Qed.

Lemma dmap_denv_diff_injection_remove : forall M M',
  <#<@M@>#> ** <#<@M'@>#> -> M ** M'.
Proof.
  intros M M' J.
  apply dmap_denv_diff_injection in J; auto.
Qed.

Lemma dmap_eq__denv_fv_tt_eq_notin : forall (D1 D2: denv),
  uniq D1 ->
  uniq D2 ->
  <#D1#> ~~ <#D2#> ->
  (forall X, X `notin` denv_fv_tt D1 <-> X `notin` denv_fv_tt D2).
Proof.
  intros D1 D2 Uniq1 Uniq2 Heq.
  intros X.
  split; intro J.
    intro H. apply J. clear J.
    eapply dmap_eq__denv_fv_tt_eq; eauto.

    intro H. apply J. clear J.
    apply dmap_eq__denv_fv_tt_eq with (X:=X) in Heq; eauto.
    eapply Heq; eauto.
Qed.


Lemma dmap_remove_preserves_Sub_head : forall E E' x V,
  uniq ([(x,V)]++E) ->
  uniq ([(x,V)]++E') ->
  <#[(x,V)]++E#> <<= <#[(x,V)]++E'#> ->
  <#E#> <<= <#E'#>.
Proof.
  intros E E' x V Uniq Uniq' Hsub.
  destruct Hsub as [Hsub1 Hsub2].
  split.
    intros k Hin.
    assert (EMap.In (elt:=typ) k <#[(x,V)]++E#>) as J.
      simpl.
      eapply add_in_iff. auto.
    apply Hsub1 in J.
    simpl in J. apply add_in_iff in J.
    destruct J as [J | J]; auto.
      subst.
      rewrite_env (nil ++ [(k, V)] ++ E) in Uniq.
      apply fresh_mid_tail in Uniq.
      apply notin_dom_implies_notIn in Uniq.
      contradict Hin; auto.

    intros k t t' Hmapsto Hmapsto'.
    assert (x <> k) as H.
      destruct (x==k); subst; auto.
        rewrite_env (nil ++ [(k, V)] ++ E) in Uniq.
        apply fresh_mid_tail in Uniq.
        apply notin_dom_implies_notIn in Uniq.
       
        apply find_mapsto_iff in Hmapsto.
        apply not_find_in_iff in Uniq.
        rewrite Hmapsto in Uniq.
        inversion Uniq.  
    assert (EMap.MapsTo k t <#[(x,V)]++E#>) as J.
      simpl.
      eapply add_mapsto_iff; auto.
    assert (EMap.MapsTo k t' <#[(x,V)]++E'#>) as J'.
      simpl.
      eapply add_mapsto_iff; auto.
    eauto.
Qed.      

Lemma dmap_remove_preserves_Sub : forall F E F' E' x V,
  uniq (F++[(x,V)]++E) ->
  uniq (F'++[(x,V)]++E') ->
  <#F++[(x,V)]++E#> <<= <#F'++[(x,V)]++E'#> ->
  <#F++E#> <<= <#F'++E'#>.
Proof.
  intros F E F' E' x V Uniq Uniq' Eq.
  assert (<#F++[(x,V)]++E#>~~<#[(x,V)]++F++E#>) as Heq.
    rewrite_env (dempty++F++dempty++[(x,V)]++E).
    rewrite_env (dempty++[(x,V)]++dempty++F++E).
    apply disjoint_denv_cons_commut_aux; auto.
  assert (<#F'++[(x,V)]++E'#>~~<#[(x,V)]++F'++E'#>) as Heq'.
    rewrite_env (dempty++F'++dempty++[(x,V)]++E').
    rewrite_env (dempty++[(x,V)]++dempty++F'++E').
    apply disjoint_denv_cons_commut_aux; auto.
  apply dmap_Equal_rewrite_Sub_left with (M1':=<#[(x,V)]++F++E#>) in Eq; auto.
  apply dmap_Equal_rewrite_Sub_right with (M2':=<#[(x,V)]++F'++E'#>) in Eq; auto.
  apply dmap_remove_preserves_Sub_head in Eq; auto.
    solve_uniq.
    solve_uniq.
Qed.
  
Lemma dmap_remove_renaming : forall F E F' E' x V a y,
  uniq (F++[(x, V)]++E) ->
  uniq (F'++[(x, V)]++E') ->
  uniq (F++[(y, V)]++E) ->
  uniq (F'++[(y, V)]++E') ->
  <#F++[(x, V)]++E#>[-]a ~~ <#F'++[(x, V)]++E'#> ->
  y <> a ->
  <#F++[(y, V)]++E#>[-]a ~~ <#F'++[(y, V)]++E'#>.
Proof.
  intros F E F' E' x V a y Uniq Uniq' Uniq'' Uniq''' Eq Hyna.
  assert (<#F++[(x,V)]++E#>~~<#[(x,V)]++F++E#>) as Heq.
    rewrite_env (dempty++F++dempty++[(x,V)]++E).
    rewrite_env (dempty++[(x,V)]++dempty++F++E).
    apply disjoint_denv_cons_commut_aux; auto.
  assert (<#F'++[(x,V)]++E'#>~~<#[(x,V)]++F'++E'#>) as Heq'.
    rewrite_env (dempty++F'++dempty++[(x,V)]++E').
    rewrite_env (dempty++[(x,V)]++dempty++F'++E').
    apply disjoint_denv_cons_commut_aux; auto.
  assert (<#F++[(y,V)]++E#>~~<#[(y,V)]++F++E#>) as Heq''.
    rewrite_env (dempty++F++dempty++[(y,V)]++E).
    rewrite_env (dempty++[(y,V)]++dempty++F++E).
    apply disjoint_denv_cons_commut_aux; auto.
  assert (<#F'++[(y,V)]++E'#>~~<#[(y,V)]++F'++E'#>) as Heq'''.
    rewrite_env (dempty++F'++dempty++[(y,V)]++E').
    rewrite_env (dempty++[(y,V)]++dempty++F'++E').
    apply disjoint_denv_cons_commut_aux; auto.
  apply Equal_trans with (m':=<#[(y,V)]++F++E#>[-]a); auto.
    apply dmap_remove_preserves_Equal; auto.
    apply Equal_trans with (m':=<#[(y,V)]++F'++E'#>); auto.
      apply dmap_remove_renaming_head with (x:=x); auto.
        solve_uniq.
        solve_uniq.
        apply Equal_trans with (m':=<#F'++[(x,V)]++E'#>); auto.
          apply Equal_trans with (m':=<#F++[(x,V)]++E#>[-]a); auto.
            apply dmap_remove_preserves_Equal; auto.
              apply Equal_sym; auto.          
      apply Equal_sym; auto.          
Qed.      

Lemma dmap_Equal_renaming_head : forall E E' x V y,
  uniq ([(x, V)]++E) ->
  uniq ([(x, V)]++E') ->
  <#[(x, V)]++E#> ~~ <#[(x, V)]++E'#> ->
  <#[(y, V)]++E#> ~~ <#[(y, V)]++E'#>.
Proof.
  intros E E' x V y Uniq Uniq' Heq.
  intro z.
  remember (EMap.find (elt:=typ) z (<#[(y,V)]++E#>)) as R.
  destruct R; apply sym_eq in HeqR; apply sym_eq.
    apply find_mapsto_iff in HeqR.
    simpl in *.
    apply add_mapsto_iff in HeqR.
    destruct HeqR as [[H1 H2]|[H1 H2]]; subst.
      eapply find_mapsto_iff.
      eapply add_mapsto_iff; auto.

      eapply find_mapsto_iff.
      eapply add_mapsto_iff.
      right. split; auto.
        assert (EMap.MapsTo z t (x:::V[+]<#E#>)) as J.
          eapply add_mapsto_iff.
          right. split; auto.
            destruct (x==z); subst; auto.
              inversion Uniq; subst.
              apply notin_dom_implies_notIn in H5.
              apply find_mapsto_iff in H2.
              apply not_find_in_iff in H5.
              rewrite H5 in H2.
              inversion H2.
        rewrite Heq in J.
        apply add_mapsto_iff in J.
        destruct J as [[J1 J2]|[J1 J2]]; subst; auto.
          inversion Uniq; subst.
          apply notin_dom_implies_notIn in H5.
          apply find_mapsto_iff in H2.
          apply not_find_in_iff in H5.
          rewrite H5 in H2.
          inversion H2.

    apply not_find_in_iff in HeqR.
    eapply not_find_in_iff.
    intro J.
    apply HeqR. clear HeqR. simpl in *.
    apply add_in_iff in J.
    destruct J as [J | J]; subst.
      eapply add_in_iff. auto.

      assert (EMap.In z (x:::V[+]<#E'#>)) as H.
        eapply add_in_iff. auto.
      rewrite <- Heq in H.

      eapply add_in_iff.
      apply add_in_iff in H.
      destruct H as [H | H]; subst; auto.
        inversion Uniq'; subst.
        apply notin_dom_implies_notIn in H3.
        contradict J; auto.
Qed.            
      
Lemma dmap_Equal_renaming : forall F E F' E' x V y,
  uniq (F++[(x, V)]++E) ->
  uniq (F'++[(x, V)]++E') ->
  uniq (F++[(y, V)]++E) ->
  uniq (F'++[(y, V)]++E') ->
  <#F++[(x, V)]++E#> ~~ <#F'++[(x, V)]++E'#> ->
  <#F++[(y, V)]++E#> ~~ <#F'++[(y, V)]++E'#>.
Proof.
  intros F E F' E' x V y Uniq Uniq' Uniq'' Uniq''' Eq.
  assert (<#F++[(x,V)]++E#>~~<#[(x,V)]++F++E#>) as Heq.
    rewrite_env (dempty++F++dempty++[(x,V)]++E).
    rewrite_env (dempty++[(x,V)]++dempty++F++E).
    apply disjoint_denv_cons_commut_aux; auto.
  assert (<#F'++[(x,V)]++E'#>~~<#[(x,V)]++F'++E'#>) as Heq'.
    rewrite_env (dempty++F'++dempty++[(x,V)]++E').
    rewrite_env (dempty++[(x,V)]++dempty++F'++E').
    apply disjoint_denv_cons_commut_aux; auto.
  assert (<#F++[(y,V)]++E#>~~<#[(y,V)]++F++E#>) as Heq''.
    rewrite_env (dempty++F++dempty++[(y,V)]++E).
    rewrite_env (dempty++[(y,V)]++dempty++F++E).
    apply disjoint_denv_cons_commut_aux; auto.
  assert (<#F'++[(y,V)]++E'#>~~<#[(y,V)]++F'++E'#>) as Heq'''.
    rewrite_env (dempty++F'++dempty++[(y,V)]++E').
    rewrite_env (dempty++[(y,V)]++dempty++F'++E').
    apply disjoint_denv_cons_commut_aux; auto.
  apply Equal_trans with (m':=<#[(y,V)]++F++E#>); auto.
    apply Equal_trans with (m':=<#[(y,V)]++F'++E'#>); auto.
      apply dmap_Equal_renaming_head with (x:=x); auto.
        solve_uniq.
        solve_uniq.
        apply Equal_trans with (m':=<#F'++[(x,V)]++E'#>); auto.
          apply Equal_trans with (m':=<#F++[(x,V)]++E#>); auto.
            apply Equal_sym; auto.          
      apply Equal_sym; auto.          
Qed.      

Lemma dmap_remove_noteq_in : forall (M:dmap) x y,
  EMap.In y M ->
  x <> y ->
  EMap.In y (M[-]x).
Proof.
  intros M x y Hin Hnot.
  eapply remove_in_iff.
  split; auto.
Qed.

Lemma dmap_remove_noteq_mapsto : forall (M:dmap) x y V,
  EMap.MapsTo y V M ->
  x <> y ->
  EMap.MapsTo y V (M[-]x).
Proof.
  intros M x y V Hin Hnot.
  eapply remove_mapsto_iff.
  split; auto.
Qed.

Lemma denv_remove_mid : forall F E x V,
  uniq (F ++ [(x, V)] ++ E) ->
  <#F ++ [(x, V)] ++ E#>[-]x ~~ <#F ++ E#>.
Proof.
  intros F E x V Uniq.
  apply Equal_trans with (m':=<#[(x,V)]++F++E#>[-]x).
    apply dmap_remove_preserves_Equal; auto.
      rewrite_env (dempty++F++dempty++[(x,V)]++E).
      rewrite_env (dempty++[(x,V)]++dempty++F++E).
      apply disjoint_denv_cons_commut_aux.
        simpl_env. auto.
    simpl. apply dmap_add_remove_refl; auto.
      apply notin_dom_implies_notIn; auto.
        assert (J:=Uniq).
        apply fresh_mid_tail in Uniq.
        apply fresh_mid_head in J.
        auto.
Qed.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../../../metatheory" "-I" "../linf") ***
*** End: ***
 *)
