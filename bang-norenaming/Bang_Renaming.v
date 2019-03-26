(** Authors: Jianzhou Zhao. *)

Require Export Bang_PreLib.

(*Require Export Bang_OParametricity_Pre.*)

Notation atom_subst := (list (atom * atom)).
Notation atom_nil := (@nil (atom * atom)).

(*******************************************************************************)
(** Renaming *)

Fixpoint subst_atom_lenv (lE:lenv) (x:atom) (y:atom) {struct lE} : lenv :=
  match lE with
  | nil => nil
  | ((z, b)::lE') =>
    if x == z 
    then 
      ((y, b)::subst_atom_lenv lE' x y)   
    else
      ((z, b)::subst_atom_lenv lE' x y)   
  end.

Fixpoint subst_atoms_lenv (asubst:atom_subst) (E:lenv) {struct asubst} : lenv :=
  match asubst with
  | nil => E
  | pair x y::asubst' => (subst_atoms_lenv asubst' (subst_atom_lenv E x y))
  end.

Fixpoint atom_subst_atoms (asubst:atom_subst) : atoms :=
  match asubst with
  | nil => {}
  | pair x y::asubst' => 
      {{x}} `union` {{y}} `union` atom_subst_atoms asubst'
  end.

Fixpoint atom_subst_codom (asubst:atom_subst) : atoms :=
  match asubst with
  | nil => {}
  | pair x y::asubst' => 
      {{y}} `union` atom_subst_codom asubst'
  end.

Fixpoint subst_atoms_exp (asubst:atom_subst) (e:exp) {struct asubst} : exp :=
  match asubst with
  | nil => e
  | pair x y::asubst' => (subst_atoms_exp asubst' (subst_ee x y e))
  end.

Fixpoint rev_subst_atoms_lenv (asubst:atom_subst) (E:lenv) {struct asubst} : lenv :=
  match asubst with
  | nil => E
  | pair x y::asubst' => (rev_subst_atoms_lenv asubst' (subst_atom_lenv E y x))
  end.

Fixpoint rev_subst_atoms_exp (asubst:atom_subst) (e:exp) {struct asubst} : exp :=
  match asubst with
  | nil => e
  | pair x y::asubst' => (rev_subst_atoms_exp asubst' (subst_ee y x e))
  end.

Inductive wf_atom_subst : atom_subst -> Prop :=
  | wf_atom_subst_empty : wf_atom_subst nil
  | wf_atom_subst_cons : forall AE x y,
      wf_atom_subst AE -> 
      x `notin` atom_subst_atoms AE ->
      y `notin` atom_subst_atoms AE `union` {{x}}->
      wf_atom_subst ([(x, y)] ++ AE)
  .

Tactic Notation "wf_atom_subst_cases" tactic(first) tactic(c) :=
  first;
  [ c "wf_atom_subst_empty" |
    c "wf_atom_subst_cons"].

Hint Constructors wf_atom_subst.

Lemma asubst_atoms__dom_codom : forall AS,
  atom_subst_atoms AS [=] dom AS `union` atom_subst_codom AS.
Proof.
  intros AS.
  induction AS.
    simpl. fsetdec.
    destruct a. simpl. rewrite IHAS. fsetdec.
Qed.

Fixpoint replace_asubst_atoms (asubst:atom_subst) (x z:atom) : atom_subst :=
  match asubst with 
  | nil => nil
  | (a, y)::asubst =>
    if (a==x) 
    then (x, z)::replace_asubst_atoms asubst x z 
    else  (a, y)::replace_asubst_atoms asubst x z 
  end.

Lemma binds_asubst_inv : forall (asubst:atom_subst) x y,
  wf_atom_subst asubst ->
  binds x y asubst ->
  y `in` atom_subst_atoms asubst.
Proof.
  intros asubst x y Hwfa Binds.
  generalize dependent x.
  generalize dependent y.
  induction Hwfa; intros.
    inversion Binds.
    analyze_binds Binds.
      simpl. auto.
      apply IHHwfa in BindsTac. simpl. auto.
Qed.

Lemma  replace_asubst_atoms_dom : forall (asubst:atom_subst) ,
  wf_atom_subst asubst ->
  (
    (forall (x a z:atom), 
       binds x a asubst -> 
       (AtomSetImpl.diff (atom_subst_atoms (asubst)) {{a}} `union` {{z}})
         [=] atom_subst_atoms (replace_asubst_atoms asubst x z)) 
    /\
    (forall (x z:atom),
      x `notin` dom asubst -> 
      atom_subst_atoms (asubst) [=] atom_subst_atoms (replace_asubst_atoms asubst x z)) 
   ).
Proof.
  intros asubst Wfa.
  induction Wfa.
    split; intros.
      inversion H.
      simpl. fsetdec.

    destruct IHWfa as [J1 J2].
    split; intros.
      simpl.
      analyze_binds H1.
        destruct (x==x); simpl.
           assert (x `notin` dom AE).
              rewrite asubst_atoms__dom_codom in H. auto.
           apply J2 with (z:=z) in H1.
           rewrite <- H1.
           fsetdec.

           contradict n; auto.
       destruct (x==x0); subst.
         apply binds_In in BindsTac.
         rewrite asubst_atoms__dom_codom in H. 
         contradict BindsTac; auto.
      
         assert (J:=BindsTac).
         apply J1 with (z:=z) in BindsTac. simpl.
         rewrite <- BindsTac.
         apply binds_asubst_inv in J; auto.
         assert (a <> x) as anx. fsetdec.         
         assert (a <> y) as any. fsetdec.
         assert (AtomSetImpl.diff ({{x}} `union` {{y}} `union` (atom_subst_atoms AE)) {{a}}
                     [=] {{x}} `union` {{y}} `union` (AtomSetImpl.diff (atom_subst_atoms AE)) {{a}}
                   ).
           clear H H0 J1 J2 BindsTac n.
           fsetdec.
         rewrite H1. 
         clear H H0 J1 J2 BindsTac n anx any H1 J.
         fsetdec.

      simpl. simpl_env in H1.
      destruct_notin.
      destruct (x==x0); subst.
        contradict H1; auto.

        apply J2 with (z:=z) in NotInTac.  
        simpl. rewrite <- NotInTac. fsetdec.
Qed.       

Lemma  replace_asubst_atoms_in_dom : forall (asubst:atom_subst) (x a z:atom),
  wf_atom_subst asubst ->
  binds x a asubst -> 
  (AtomSetImpl.diff (atom_subst_atoms (asubst)) {{a}} `union` {{z}})
    [=] atom_subst_atoms (replace_asubst_atoms asubst x z).  
Proof.
  intros asubst x a z Hwfa Binds.
  destruct (@replace_asubst_atoms_dom asubst Hwfa); auto.
Qed.

Lemma  replace_asubst_atoms_notin_dom : forall (asubst:atom_subst) (x z:atom),
  wf_atom_subst asubst ->
  x `notin` dom asubst -> 
  atom_subst_atoms (asubst) [=] atom_subst_atoms (replace_asubst_atoms asubst x z). 
Proof.
  intros asubst x z Hwfa Binds.
  destruct (@replace_asubst_atoms_dom asubst Hwfa); auto.
Qed.

Lemma wf_replace_asubst_dom : forall asubst x z,
  wf_atom_subst asubst ->
  dom (replace_asubst_atoms asubst x z) [=] dom asubst. 
Proof.
  intros asubst x z Wfa.
  generalize dependent x.
  generalize dependent z.
  induction Wfa; intros.
    simpl. auto.
    simpl. destruct (x==x0); subst; simpl.
      rewrite IHWfa. fsetdec.
      rewrite IHWfa. fsetdec.
Qed.

Lemma  replace_asubst_codom : forall (asubst:atom_subst) ,
  wf_atom_subst asubst ->
  (
    (forall (x a z:atom), 
       binds x a asubst -> 
       (AtomSetImpl.diff (atom_subst_codom (asubst)) {{a}} `union` {{z}})
         [=] atom_subst_codom (replace_asubst_atoms asubst x z)) 
    /\
    (forall (x z:atom),
      x `notin` dom asubst -> 
      atom_subst_codom (asubst) [=] atom_subst_codom (replace_asubst_atoms asubst x z)) 
   ).
Proof.
  intros asubst Wfa.
  induction Wfa.
    split; intros.
      inversion H.
      simpl. fsetdec.

    destruct IHWfa as [J1 J2].
    split; intros.
      simpl.
      analyze_binds H1.
        destruct (x==x); simpl.
           assert (x `notin` dom AE).
              rewrite asubst_atoms__dom_codom in H. auto.
           rewrite asubst_atoms__dom_codom in H0.
           apply J2 with (z:=z) in H1.
           rewrite <- H1.
           fsetdec.

           contradict n; auto.
       destruct (x==x0); subst.
         apply binds_In in BindsTac.
         rewrite asubst_atoms__dom_codom in H. 
         contradict BindsTac; auto.
      
         assert (J:=BindsTac).
         apply J1 with (z:=z) in BindsTac. simpl.
         rewrite <- BindsTac.
         apply binds_asubst_inv in J; auto.
         assert (a <> x) as anx. fsetdec.         
         assert (a <> y) as any. fsetdec.
         assert (AtomSetImpl.diff ({{y}} `union` (atom_subst_codom AE)) {{a}}
                     [=] {{y}} `union` (AtomSetImpl.diff (atom_subst_codom AE)) {{a}}
                   ).
           clear H H0 J1 J2 BindsTac n.
           fsetdec.
         rewrite H1. 
         clear H H0 J1 J2 BindsTac n anx any H1 J.
         fsetdec.

      simpl. simpl_env in H1.
      destruct_notin.
      destruct (x==x0); subst.
        contradict H1; auto.

        apply J2 with (z:=z) in NotInTac.  
        simpl. rewrite <- NotInTac. fsetdec.
Qed.       

Lemma  replace_asubst_in_codom : forall (asubst:atom_subst) (x a z:atom),
  wf_atom_subst asubst ->
  binds x a asubst -> 
  (AtomSetImpl.diff (atom_subst_codom (asubst)) {{a}} `union` {{z}})
    [=] atom_subst_codom (replace_asubst_atoms asubst x z).  
Proof.
  intros asubst x a z Hwfa Binds.
  destruct (@replace_asubst_codom asubst Hwfa); auto.
Qed.

Lemma  replace_asubst_notin_codom : forall (asubst:atom_subst) (x z:atom),
  wf_atom_subst asubst ->
  x `notin` dom asubst -> 
  atom_subst_codom (asubst) [=] atom_subst_codom (replace_asubst_atoms asubst x z). 
Proof.
  intros asubst x z Hwfa Binds.
  destruct (@replace_asubst_codom asubst Hwfa); auto.
Qed.

Lemma wf_replace_asubst_atoms : forall asubst x z,
  wf_atom_subst asubst ->
  z `notin` atom_subst_atoms (asubst) ->
  wf_atom_subst (replace_asubst_atoms asubst x z). 
Proof.
  intros asubst x z Wfa znotin.
  induction Wfa; simpl; auto.
    simpl_env.
    destruct (x0==x); subst.
      simpl in znotin. destruct_notin. clear znotin NotInTac2 NotInTac4.
      apply wf_atom_subst_cons; auto.
        rewrite asubst_atoms__dom_codom in H.
        apply replace_asubst_atoms_notin_dom with (x:=x)(z:=z) in Wfa; auto.
        rewrite <- Wfa. rewrite asubst_atoms__dom_codom. auto.

        rewrite asubst_atoms__dom_codom in H.
        apply replace_asubst_atoms_notin_dom with (x:=x)(z:=z) in Wfa; auto.
        rewrite <- Wfa. auto.
      simpl in znotin. destruct_notin. clear znotin NotInTac2 NotInTac4.
      apply wf_atom_subst_cons; auto.
        destruct (in_dec x (dom AE)) as [J | J].
          apply binds_In_inv in J.
          destruct J as [a Binds].
          apply replace_asubst_atoms_in_dom with (z:=z) in Binds; auto.
          rewrite <- Binds. rewrite asubst_atoms__dom_codom. 
          clear Binds n H0 NotInTac3 NotInTac1 NotInTac.
          rewrite asubst_atoms__dom_codom in H.
          assert (x0 `notin` (union (dom AE) (atom_subst_codom AE))) as x0notin. fsetdec.
          assert (x0 `notin` AtomSetImpl.diff (union (dom AE) (atom_subst_codom AE)) {{a}}) as x0notin'. fsetdec.
          clear x0notin H Wfa IHWfa.
          intro. 
          assert (x0 `in` AtomSetImpl.diff (union (dom AE) (atom_subst_codom AE)) {{a}} \/ x0 `in` {{z}}) as J.
            fsetdec. 
          clear H. destruct J as [J | J].
            apply x0notin'. auto.
            contradict J; auto.

          apply replace_asubst_atoms_notin_dom with (x:=x)(z:=z) in Wfa; auto.
          rewrite <- Wfa. auto.
          
        destruct (in_dec x (dom AE)) as [J | J].
          apply binds_In_inv in J.
          destruct J as [a Binds].
          apply replace_asubst_atoms_in_dom with (z:=z) in Binds; auto.
          rewrite <- Binds. rewrite asubst_atoms__dom_codom. 
          clear Binds n H NotInTac1.
          rewrite asubst_atoms__dom_codom in H0.
          fsetdec.

          apply replace_asubst_atoms_notin_dom with (x:=x)(z:=z) in Wfa; auto.
          rewrite <- Wfa. auto.
Qed.

Lemma codom_asubst_inv : forall (asubst:atom_subst) y,
  wf_atom_subst asubst ->
  y `in` atom_subst_codom asubst ->
  exists x, binds x y asubst.
Proof.
  intros asubst y Hwfa yin.
  generalize dependent y.
  induction Hwfa; intros.
    simpl in yin. contradict yin; auto.

    simpl in yin.
    assert (y0 `in` {{y}} \/ y0 `in` atom_subst_codom AE) as J. fsetdec.
    destruct J as [J | J].
      exists x.
      destruct (y0==y); subst; auto.
        contradict J; auto.

        apply IHHwfa in J. 
        destruct J as [x0 J].
        exists x0. auto.
Qed.

Ltac gather_atoms :=
  let A := ltac_map (fun x : atoms => x) in
  let B := ltac_map (fun x : atom => singleton x) in
  let C := ltac_map (fun x : exp => fv_te x) in
  let D := ltac_map (fun x : exp => fv_ee x) in
  let E := ltac_map (fun x : typ => fv_tt x) in
  let F := ltac_map (fun x : env => dom x) in
  let G := ltac_map (fun x : env => fv_env x) in
  let H := ltac_map (fun x : lenv => dom x) in
  let I := ltac_map (fun x : lenv => fv_lenv x) in
  let J := ltac_map (fun x : atom_subst => atom_subst_atoms x) in
  simplify_list_of_atom_sets (A ++ B ++ C ++ D ++ E ++ F ++ G ++ H ++ I ++ J).

Tactic Notation "pick" "fresh" ident(x) :=
  let L := gather_atoms in (pick fresh x for L).

Lemma pick_lenv : forall L (lE:lenv),
  uniq lE ->
  exists asubst,
    wf_atom_subst asubst /\
    dom lE [=] dom asubst /\
    disjdom L (atom_subst_codom asubst).
Proof.
  intros L lE Uniq.
  induction Uniq.
    exists (@nil (atom*atom)). 
    split. apply wf_atom_subst_empty.
    split; auto.
      split; intros; auto.
        simpl in H. contradict H; auto.

    destruct (IHUniq) as [AS [J1 [J2 J3]]].
    pick fresh y.
    destruct (in_dec x (atom_subst_codom AS)).
      pick fresh z.
      assert (J:=J1).
      apply codom_asubst_inv with (y:=x) in J; auto.
      destruct J as [x0 J].
      exists ([(x,y)]++(replace_asubst_atoms AS x0 z)).
      split.
        apply wf_atom_subst_cons; auto.
          apply wf_replace_asubst_atoms; auto.

          apply replace_asubst_atoms_in_dom with (z:=z) in J; auto.
          rewrite <- J. clear J. clear J2. 
          destruct_notin.
          clear H Fr Fr0 NotInTac0 NotInTac1 NotInTac2 NotInTac3 NotInTac4 NotInTac5 NotInTac6 NotInTac7 NotInTac8 NotInTac9 NotInTac10 i.
          fsetdec.           

          apply replace_asubst_atoms_in_dom with (z:=z) in J; auto.
          rewrite <- J. clear J. clear J2. 
          destruct_notin.
          clear H Fr Fr0 NotInTac0 NotInTac1 NotInTac2 NotInTac4 NotInTac5 NotInTac6 NotInTac7 NotInTac9 i NotInTac.
          fsetdec.           
      split.
        simpl. rewrite wf_replace_asubst_dom;auto. rewrite <- J2. fsetdec.
      
        destruct J3 as [J31 J32].
        split; intros.
          simpl. assert (JJ:=H0).
          apply J31 in H0.
          apply replace_asubst_in_codom with (z:=z) in J; auto.
          rewrite <- J. clear J.
          destruct (x1==y); subst.
            contradict JJ; auto.
          destruct (x1==z); subst.
            contradict JJ; auto.
          clear Fr Fr0 JJ H J31 J32 J2 i. fsetdec.

          simpl in H0.
          assert (x1 `in` {{y}} \/ x1 `in` (atom_subst_codom (replace_asubst_atoms AS x0 z))) as JJ. 
            clear Fr Fr0 H J31 J32 J2 i. fsetdec.
          destruct JJ as [JJ | JJ].
            destruct (x1==y); subst.
               destruct_notin. auto.
               contradict JJ; auto.

            destruct (x1==z); subst.
               destruct_notin. auto.

               apply J32.             
               apply replace_asubst_in_codom with (z:=z) in J; auto.
               rewrite <- J in JJ. clear J.
               clear Fr Fr0 H J31 J32 J2 i H0. fsetdec.         

      exists ([(x,y)]++AS).
      split.
        apply wf_atom_subst_cons; auto.
          rewrite asubst_atoms__dom_codom. 
          rewrite <- J2. auto.
      split.
        simpl. rewrite J2. fsetdec.

        simpl. destruct J3 as [J31 J32].
        split; intros.
          destruct (x0 == x); subst; auto.
            destruct (x0 == y); subst.
              contradict H0; auto.
              apply J31 in H0. auto.

           assert (x0 `in` {{y}} \/ x0 `in` (atom_subst_codom AS)) as J. fsetdec.
           destruct J as [J | J].
             destruct_notin.
             contradict J. fsetdec.

             apply J32; auto.        
Qed.

Lemma atom_subst_atoms__includes__dom : forall AE,
  dom AE [<=] atom_subst_atoms AE.
Proof.
  induction AE; simpl.
    fsetdec.

    destruct a. fsetdec.
Qed.

Lemma atom_subst_atoms__dom : forall x AE,
  x `notin` atom_subst_atoms AE ->
  x `notin` dom AE.
Proof.
  intros x AE.
  assert (J:=atom_subst_atoms__includes__dom AE).
  fsetdec.
Qed.

Lemma wf_atom_subst__uniq : forall AE,
  wf_atom_subst AE -> uniq AE.
Proof.
  intros AE H.
  induction H; auto using atom_subst_atoms__dom.    
Qed.

Lemma wf_lenv_renaming_one : forall E lE' lE x0 y0 b,
  wf_lenv E (lE'++[(x0, b)]++lE) ->
  x0 `notin` dom E `union` dom lE' `union` dom lE ->
  y0 `notin` dom E `union` dom lE' `union` dom lE ->
  wf_lenv E (lE'++[(y0, b)]++lE).
Proof with auto.
  intros E lE' lE x0 y0 b Wfle Fvx0 Fvy0.
  destruct (x0 == y0); subst...
  destruct b.
  apply wf_lenv_lin_weakening; auto.
    apply wf_typ_from_lbinds_typ with (x:=x0) (U:=t) in Wfle; auto.
    apply wf_lenv_lin_strengthening' in Wfle; auto.
Qed.  

Lemma subst_atom_lenv_notin_inv : forall (lE:lenv) (x y:atom),
  x `notin` dom lE -> 
  lE = subst_atom_lenv lE x y.
Proof.
  intros lE x y.
  induction lE; intros.
    simpl. auto.

    destruct a. simpl.
    destruct (x==a); subst.
      simpl in H. destruct_notin. contradict H; auto.
      rewrite <- IHlE; auto.
Qed.

Lemma subst_atom_lenv_in_inv : forall (lE:lenv) (x y:atom) b,
  uniq lE ->
  binds x b lE -> 
  exists lE1, exists lE2, 
    lE = lE1 ++ [(x, b)] ++ lE2 /\
    subst_atom_lenv lE x y = lE1 ++ [(y, b)] ++ lE2.
Proof.
  intros lE x y b Uniq.
  generalize dependent x.
  generalize dependent y.
  generalize dependent b.
  induction Uniq; intros.
    inversion H.

    analyze_binds H0.
      exists (@nil (atom*lbinding)). exists E.
      split; auto.
        simpl.
        destruct (@eq_dec atom _ x x); subst.
          rewrite <- subst_atom_lenv_notin_inv; auto. 

          contradict n; auto.
      apply IHUniq with (y:=y) in BindsTac.
      destruct BindsTac as [lE1 [lE2 [EQ1 EQ2]]]; subst.
      exists ([(x, a)]++lE1). exists lE2.
      split; auto. 
        simpl.    
        destruct (x0 == x); subst.
          simpl_env in H.
          destruct_notin.
          contradict NotInTac; auto.

          simpl_env.  
          rewrite_env ([(x,a)]++(lE1++[(y,b)]++lE2)). rewrite <-EQ2. 
          auto.
Qed.

Lemma typing_lin_renaming_one : forall E lE' lE e t x y b,
  typing E (lE'++[(x,b)]++lE) e t ->
  y `notin` dom E `union` dom lE' `union` dom lE ->
  typing E (lE'++[(y,b)]++lE) (subst_ee x y e) t.
Proof.
  intros E lE' lE e t x y b Typing ynotin.
  remember (lE'++[(x, b)]++lE) as lEE.
  generalize dependent lE'.
  generalize dependent lE.
  generalize dependent x.
  generalize dependent b.
  (typing_cases (induction Typing) Case); intros; subst; simpl.
  Case "typing_var".
    simpl in HeqlEE. 
    symmetry in HeqlEE.
    contradict HeqlEE.
    apply app_cons_not_nil.
  Case "typing_lvar".
    rewrite_env ([(x, lbind_typ T)]++nil) in HeqlEE.
    apply one_eq_app in HeqlEE.
    destruct HeqlEE as [[lE'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      symmetry in EQ2.
      contradict EQ2. simpl.
      apply app_cons_not_nil.
      
      inversion EQ2; subst.
      simpl_env.
      simpl.
      destruct (x==x).
        apply typing_lvar.
          rewrite_env ([(y, lbind_typ T)]++nil).
          apply wf_lenv_typ; auto.
            apply wf_typ_from_lbinds_typ with (x:=x) (U:=T) in H; auto.
        contradict n; auto.
  Case "typing_abs".
    apply typing_abs with (L:=dom E `union` dom lE' `union` dom lE `union` {{x}} `union` {{y}} `union` L); auto.
      intros x0 x0notin.
      simpl_env.
      assert (x0 `notin` L) as x0nL. auto.
      apply H1 with (b0:=b)(lE0:=lE)(lE'0:=[(x0, lbind_typ T1)]++lE')(x1:=x) in x0nL; auto.
        rewrite subst_ee_open_ee in x0nL; auto.
        rewrite <- subst_ee_fresh with (e:=x0) in x0nL; auto.
  Case "typing_app".
    destruct b.
    assert (Split:=H).
    apply lenv_split_cases_mid in H.
    destruct H as [LEFT | RIGHT].
    SCase "left".
      destruct LEFT as [D1L [D1R [D2L [D2R [Q1 [Q2 [S1 S2]]]]]]]; subst.
      assert (D1L ++ [(x, lbind_typ t)] ++ D1R=D1L ++ [(x, lbind_typ t)] ++ D1R) as IH1. auto.
      assert (DomEq2:=S2).
      apply dom_lenv_split in DomEq2.
      rewrite DomEq2 in ynotin.
      assert (DomEq1:=S1).
      apply dom_lenv_split in DomEq1.
      rewrite DomEq1 in ynotin.
      apply IHTyping1 in IH1; auto.
      clear IHTyping1 IHTyping2.
      assert (x `notin` (dom (D2L++D2R) `union` dom E)) as J.
        eapply lenv_split_not_in_left; eauto.
          simpl_env. auto.
      rewrite <- (non_subst E (D2L++D2R) e2 T1 x y); auto.
      apply (typing_app T1 E (D1L ++ [(y, lbind_typ t)] ++ D1R) (D2L ++ D2R)); auto.
        simpl_env.
        eapply lenv_split_sub_left; eauto.
          apply wf_lenv_split in Split.
          apply wf_lenv_renaming_one with (x0:=x); auto.
             assert (x `notin` dom lE') as xnotinlE'.
               apply uniq_from_wf_lenv in Split.
               apply fresh_mid_head in Split; auto.
             assert (x `notin` dom lE) as xnotinlE.
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
      apply IHTyping2 in IH2; auto.
      clear IHTyping1 IHTyping2.
      assert (x `notin` (dom (D1L++D1R) `union` dom E)) as J.
        eapply lenv_split_not_in_right; eauto.
          simpl_env. auto.
      rewrite <- (non_subst E (D1L++D1R) e1 (typ_arrow T1 T2) x y); auto.
      apply (typing_app T1 E (D1L ++ D1R) (D2L ++ [(y, lbind_typ t)] ++ D2R)); auto.
        simpl_env.
        eapply lenv_split_sub_right; eauto.
          apply wf_lenv_split in Split.
          apply wf_lenv_renaming_one with (x0:=x); auto.
             assert (x `notin` dom lE') as xnotinlE'.
               apply uniq_from_wf_lenv in Split.
               apply fresh_mid_head in Split; auto.
             assert (x `notin` dom lE) as xnotinlE.
               apply uniq_from_wf_lenv in Split.
               apply fresh_mid_tail in Split; auto.
             auto.

             rewrite DomEq1. rewrite DomEq2. auto.
  Case "typing_tabs".
    apply typing_tabs with (L:=dom E `union` dom lE' `union` dom lE `union` {{x}} `union` {{y}} `union` L); auto.
      intros X Xnotin.
      simpl_env.
      assert (X `notin` L) as XnL. auto.
      apply H0 with (b0:=b)(lE0:=lE)(lE'0:=lE')(x0:=x) in XnL; auto.
        rewrite subst_ee_open_te in XnL; auto.
  Case "typing_tapp".
    apply typing_tapp; auto.
      simpl_env.
      apply IHTyping; auto.
  Case "typing_bang".
    contradict HeqlEE. apply nil_neq_one_mid.
  Case "typing_let".
    destruct b.
    assert (Split:=H1).
    apply lenv_split_cases_mid in H1.
    destruct H1 as [LEFT | RIGHT].
    SCase "left".
      destruct LEFT as [D1L [D1R [D2L [D2R [Q1 [Q2 [S1 S2]]]]]]]; subst.
      assert (D1L ++ [(x, lbind_typ t)] ++ D1R=D1L ++ [(x, lbind_typ t)] ++ D1R) as IH1. auto.
      assert (DomEq2:=S2).
      apply dom_lenv_split in DomEq2.
      rewrite DomEq2 in ynotin.
      assert (DomEq1:=S1).
      apply dom_lenv_split in DomEq1.
      rewrite DomEq1 in ynotin.
      apply IHTyping in IH1; auto.
      clear IHTyping H0.
      assert (x `notin` (dom (D2L++D2R) `union` dom E)) as J.
        eapply lenv_split_not_in_left; eauto.
          simpl_env. auto.
      apply typing_let with (L:=L `union` {{y}} `union` {{x}})(D1:=(D1L ++ [(y, lbind_typ t)] ++ D1R))(D2:=(D2L ++ D2R))(T1:=T1); auto.
        intros x0 x0n.
        rewrite subst_ee_open_ee_var; auto.
        rewrite <- (non_subst ([(x0, bind_typ T1)]++E) (D2L++D2R) (open_ee e2 x0) T2 x y); auto.

        simpl_env.
        eapply lenv_split_sub_left; eauto.
          apply wf_lenv_split in Split.
          apply wf_lenv_renaming_one with (x0:=x); auto.
             assert (x `notin` dom lE') as xnotinlE'.
               apply uniq_from_wf_lenv in Split.
               apply fresh_mid_head in Split; auto.
             assert (x `notin` dom lE) as xnotinlE.
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
      clear IHTyping.
      assert (x `notin` (dom (D1L++D1R) `union` dom E)) as J.
        eapply lenv_split_not_in_right; eauto.
          simpl_env. auto.
      rewrite <- (non_subst E (D1L++D1R) e1 (typ_bang T1) x y); auto.
      apply typing_let with (L:=L `union` {{y}} `union` {{x}})(D1:=(D1L ++ D1R))(D2:=(D2L ++ [(y, lbind_typ t)] ++ D2R))(T1:=T1); auto.
        intros x0 x0n.
        rewrite subst_ee_open_ee_var; auto.

        simpl_env.
        eapply lenv_split_sub_right; eauto.
          apply wf_lenv_split in Split.
          apply wf_lenv_renaming_one with (x0:=x); auto.
             assert (x `notin` dom lE') as xnotinlE'.
               apply uniq_from_wf_lenv in Split.
               apply fresh_mid_head in Split; auto.
             assert (x `notin` dom lE) as xnotinlE.
               apply uniq_from_wf_lenv in Split.
               apply fresh_mid_tail in Split; auto.
             auto.

             rewrite DomEq1. rewrite DomEq2. auto.
  Case "typing_apair".
    simpl_env.
    apply typing_apair; auto.
  Case "typing_fst".
    simpl_env.
    apply typing_fst with (T2:=T2); auto.
  Case "typing_snd".
    simpl_env.
    apply typing_snd with (T1:=T1); auto.
Qed.

Lemma typing_lin_renaming : forall E lE e t x y,
  typing E lE e t ->
  x `notin` dom E ->
  y `notin` dom E `union` dom lE ->
  typing E (subst_atom_lenv lE x y) (subst_ee x y e) t.
Proof.
  intros E lE e t x y Typing xnotin ynotin.
  destruct (@in_dec x (dom lE)) as [xin | xnotin'].
    apply binds_In_inv in xin.
    destruct xin as [b Binds].
    apply subst_atom_lenv_in_inv with (y:=y) in Binds; eauto.
    destruct Binds as [lE1 [lE2 [EQ1 EQ2]]]; subst.
    rewrite EQ2.
    apply typing_lin_renaming_one with (y:=y)(E:=E) in Typing; auto.

    assert (J:=Typing).
    apply notin_fv_ee_typing with (y:=x) in Typing; auto.
    rewrite <- subst_ee_fresh; auto.
    rewrite <- subst_atom_lenv_notin_inv; auto.
Qed.
  
Lemma subst_atoms_lenv_nil : forall asubst,
  subst_atoms_lenv asubst nil = nil.
Proof.
  induction asubst; auto.
    destruct a. simpl. auto.
Qed.

Lemma subst_atom_lenv_app : forall lE1 lE2 x y,
  subst_atom_lenv (lE1++lE2) x y =
    subst_atom_lenv lE1 x y ++ subst_atom_lenv lE2 x y.
Proof.
  intros.
  remember (lE1++lE2) as lE.
  generalize dependent lE1.
  generalize dependent lE2.
  induction lE; intros; simpl; auto.
    symmetry in HeqlE.
    apply app_eq_nil in HeqlE.
    destruct HeqlE; subst.
    simpl. auto.

    destruct a.
    destruct (x == a); subst.
      simpl_env in HeqlE.
      apply one_eq_app in HeqlE.
      destruct HeqlE as [[lE1' [EQ1 EQ2]]|[EQ1 EQ2]]; subst.
        simpl.
        destruct (a==a).
           erewrite IHlE; eauto.
           simpl_env. auto.

           contradict n; auto.
        simpl. 
        destruct (a==a); auto.
           contradict n; auto.

      simpl_env in HeqlE.
      apply one_eq_app in HeqlE.
      destruct HeqlE as [[lE1' [EQ1 EQ2]]|[EQ1 EQ2]]; subst.
        simpl.
        destruct (x==a); subst.
           contradict n; auto.

           erewrite IHlE; eauto.
           simpl_env. auto.
        simpl. 
        destruct (x==a); subst; auto.
           contradict n; auto.
Qed.

Lemma subst_atoms_lenv_app : forall asubst lE1 lE2,
  subst_atoms_lenv asubst (lE1++lE2) =
    subst_atoms_lenv asubst lE1 ++ subst_atoms_lenv asubst lE2.
Proof.
  induction asubst; intros; simpl; auto.
    destruct a. 
    rewrite subst_atom_lenv_app; auto.
Qed.      

Lemma wf_asubst_dom_codom_disjoint : forall asubst,
  wf_atom_subst asubst ->
  disjdom (dom asubst) (atom_subst_codom asubst).
Proof.
  intros asubst Wfa.
  induction Wfa; simpl.
    split; intros; auto.
    
    destruct IHWfa as [J1 J2].
    split; intros.
      assert (x0 `in` {{x}} \/ x0 `in` dom AE) as J.  fsetdec.
      clear H1.
      destruct J as [J | J].
        destruct (x0==x); subst.
          rewrite asubst_atoms__dom_codom in H. auto.
          contradict J; auto.

        destruct (x0==y); subst.
          rewrite asubst_atoms__dom_codom in H0.
          contradict J; auto.
   
          apply J1 in J. 
          clear H J1 J2.
          destruct_notin. clear NotInTac0 H0. fsetdec.

      assert (x0 `in` {{y}} \/ x0 `in` atom_subst_codom AE) as J.  fsetdec.
      clear H1.
      destruct J as [J | J].
        destruct (x0==x); subst.
          destruct_notin. contradict J; auto.              
          rewrite asubst_atoms__dom_codom in H0. fsetdec.

        rewrite asubst_atoms__dom_codom in H.
        assert (x0 <> x) as x0nx.
          clear H0 J1 J2.  fsetdec.       
        apply J2 in J. fsetdec.
Qed.

Lemma subst_atoms_lenv_notin_inv : forall asubst lE,
  wf_atom_subst asubst ->
  disjoint asubst lE -> 
  lE = subst_atoms_lenv asubst lE.
Proof.
  intros asubst lE Wfa.
  induction Wfa; intros.
    simpl. auto.
 
    simpl.
    rewrite <- subst_atom_lenv_notin_inv.
      rewrite <- IHWfa. 
        auto.
        solve_uniq.
      solve_uniq.
Qed.

Lemma subst_atoms_lenv_inv : forall asubst lE (x y:atom) b,
  wf_atom_subst asubst ->
  uniq lE ->
  binds x y asubst -> 
  binds x b lE -> 
  exists lE1, exists lE2, 
  lE = lE1 ++ [(x, b)] ++ lE2 /\
  subst_atoms_lenv asubst lE = subst_atoms_lenv asubst lE1 ++ [(y, b)] ++ subst_atoms_lenv asubst lE2.
Proof.
  intros asubst lE x y b Wfa Uniq.
  generalize dependent lE.
  generalize dependent x.
  generalize dependent y.
  generalize dependent b.
  induction Wfa; intros.
    inversion H.
 
    analyze_binds H1.
      apply subst_atom_lenv_in_inv with (y:=y) in H2; auto.
      destruct H2 as [lE1 [lE2 [EQ1 EQ2]]]; subst.
      exists lE1. exists lE2.
      split; auto.
        simpl. simpl_env. 
        simpl_env in EQ2.
        rewrite EQ2.
        assert (uniq lE1). solve_uniq.
        assert (uniq lE2). solve_uniq.
        assert (x `notin` dom lE1). solve_uniq.
        assert (x `notin` dom  lE2). solve_uniq.
        rewrite <- subst_atom_lenv_notin_inv with (x:=x) (y:=y)(lE:=lE1); auto.
        rewrite <- subst_atom_lenv_notin_inv with (x:=x) (y:=y)(lE:=lE2); auto.
        rewrite subst_atoms_lenv_app.
        rewrite subst_atoms_lenv_app.
        rewrite <- subst_atoms_lenv_notin_inv with (lE:=(y~b)); auto.
          rewrite asubst_atoms__dom_codom in H0.
          clear H H1 H2 H3 H4 IHWfa Uniq EQ2.
          solve_uniq.

      assert (x <> x0) as xnx0.
        apply binds_In in BindsTac.
        rewrite asubst_atoms__dom_codom in H.
        clear H0 IHWfa Uniq.
        fsetdec.       
      apply IHWfa with (b:=b) (lE:=lE) in BindsTac; auto. 
      destruct BindsTac as [lE1 [lE2 [EQ1 EQ2]]]; subst.
      exists lE1. exists lE2.
      split; auto.
        simpl. simpl_env. 
        rewrite subst_atoms_lenv_app in EQ2.
        rewrite subst_atoms_lenv_app in EQ2.
        rewrite subst_atom_lenv_app.
        rewrite subst_atom_lenv_app.
        rewrite subst_atoms_lenv_app.
        rewrite subst_atoms_lenv_app.
        simpl.
        destruct (x == x0); subst.
          contradict xnx0; auto.

          simpl_env.
          apply app_inv_head in EQ2.
          apply app_inv_tail in EQ2.         
          simpl_env in EQ2.
          rewrite EQ2. auto. 
Qed.

Lemma typing_lin_renamings : forall E lE e t asubst,
  typing E lE e t ->
  wf_atom_subst asubst ->
  disjoint asubst E ->
  disjdom (atom_subst_codom asubst) (dom E `union` dom lE) ->
  typing E (subst_atoms_lenv asubst lE) (subst_atoms_exp asubst e) t.
Proof.
  intros E lE e t asubst Typing Wfa Disj1 Disj2.
  generalize dependent E.
  generalize dependent lE.
  generalize dependent e.
  generalize dependent t.
  induction Wfa; intros; simpl; auto.
    apply IHWfa.
      apply typing_lin_renaming; auto.
        solve_uniq.

        destruct Disj2 as [J1 J2].
        apply J1.
        simpl. auto.

      solve_uniq.

      simpl in Disj2.
      destruct (in_dec x (dom lE)).
         apply binds_In_inv in i.
         destruct i as [a Binds].
         apply subst_atom_lenv_in_inv with (y:=y) in Binds; auto.
           destruct Binds as [lE1 [lE2 [EQ1 EQ2]]]; subst.
           rewrite EQ2.
           destruct Disj2 as [J1 J2].
           split; intros.
             assert (x0 <> y) as x0ny.
               rewrite asubst_atoms__dom_codom in H0.
               clear H IHWfa J1 J2 EQ2. fsetdec.
             assert (x0 `in` union {{y}} (atom_subst_codom AE)) as x0in. fsetdec.
             apply J1 in x0in. simpl_env in x0in. simpl_env. fsetdec.

             assert (x0 `in` {{y}} \/ x0 `in` (dom E) `union` (dom lE1) `union` (dom lE2)) as x0in. 
               simpl_env in H1. fsetdec.
             clear H1.
             destruct x0in as [x0in | x0in].
               clear H J1 J2 Disj1 EQ2.
               rewrite asubst_atoms__dom_codom in H0.
               fsetdec.
                
               assert (x0 `in` (dom E) `union` dom (lE1++[(x,a)]++lE2)) as x0in'. 
                 simpl_env. fsetdec.
               apply J2 in x0in'. fsetdec.
           apply typing_regular in Typing.
           decompose [and] Typing. apply uniq_from_wf_lenv in H3; auto.

         rewrite <- subst_atom_lenv_notin_inv with (x:=x) (y:=y)(lE:=lE); auto.
           destruct Disj2 as [J1 J2].
           split; intros.
              apply J1; auto.
              apply J2 in H1; auto.
Qed.

Lemma wf_asubst_id : forall asubst e,
  wf_atom_subst asubst ->
  disjdom (dom asubst) (fv_ee e) ->
  e = (subst_atoms_exp asubst e).
Proof.
  intros asubst e Wfa Disj.
  generalize dependent e.
  induction Wfa; intros.
    simpl. auto.
    simpl. rewrite <- subst_ee_fresh with (e:=e); auto.
      apply IHWfa.
        destruct Disj as [J1 J2].
        split; intros.
          apply J1. simpl_env. fsetdec.
          apply J2 in H1. simpl_env in H1. auto.
      destruct Disj as [J1 J2].  
      apply J1. simpl. auto. 
Qed.

Lemma wf_lenv_renaming : forall E lE x y,
  wf_lenv E lE ->
  x `notin` dom E ->
  y `notin` dom E `union` dom lE ->
  wf_lenv E (subst_atom_lenv lE x y).
Proof.
  intros E lE x y Wfle xnotin ynotin.
  destruct (@in_dec x (dom lE)) as [xin | xnotin'].
    apply binds_In_inv in xin.
    destruct xin as [b Binds].
    apply subst_atom_lenv_in_inv with (y:=y) in Binds; eauto.
    destruct Binds as [lE1 [lE2 [EQ1 EQ2]]]; subst.
    rewrite EQ2.
    apply wf_lenv_renaming_one with (y0:=y)(E:=E) in Wfle; auto.
       apply uniq_from_wf_lenv in Wfle.
       assert (x `notin` dom lE1). apply fresh_mid_head in Wfle; auto.
       assert (x `notin` dom lE2). apply fresh_mid_tail in Wfle; auto.
       fsetdec.

    assert (J:=Wfle).
    rewrite <- subst_atom_lenv_notin_inv; auto.
Qed.  

Lemma wf_lenv_renamings : forall E lE asubst,
  wf_lenv E lE ->
  wf_atom_subst asubst ->
  disjoint asubst E ->
  disjdom (atom_subst_codom asubst) (dom E `union` dom lE) ->
  wf_lenv E (subst_atoms_lenv asubst lE).
Proof.
  intros E lE asubst Wfle Wfa Disj1 Disj2.
  generalize dependent E.
  generalize dependent lE.
  induction Wfa; intros; simpl; auto.
    apply IHWfa.
      apply wf_lenv_renaming; auto.
        solve_uniq.

        destruct Disj2 as [J1 J2].
        apply J1.
        simpl. auto.

      solve_uniq.

      simpl in Disj2.
      destruct (in_dec x (dom lE)).
         apply binds_In_inv in i.
         destruct i as [a Binds].
         apply subst_atom_lenv_in_inv with (y:=y) in Binds; auto.
           destruct Binds as [lE1 [lE2 [EQ1 EQ2]]]; subst.
           rewrite EQ2.
           destruct Disj2 as [J1 J2].
           split; intros.
             assert (x0 <> y) as x0ny.
               rewrite asubst_atoms__dom_codom in H0.
               clear H IHWfa J1 J2 EQ2. fsetdec.
             assert (x0 `in` union {{y}} (atom_subst_codom AE)) as x0in. fsetdec.
             apply J1 in x0in. simpl_env in x0in. simpl_env. fsetdec.

             assert (x0 `in` {{y}} \/ x0 `in` (dom E) `union` (dom lE1) `union` (dom lE2)) as x0in. 
               simpl_env in H1. fsetdec.
             clear H1.
             destruct x0in as [x0in | x0in].
               clear H J1 J2 Disj1 EQ2.
               rewrite asubst_atoms__dom_codom in H0.
               fsetdec.
                
               assert (x0 `in` (dom E) `union` dom (lE1++[(x,a)]++lE2)) as x0in'. 
                 simpl_env. fsetdec.
               apply J2 in x0in'. fsetdec.
           apply uniq_from_wf_lenv in Wfle; auto.

         rewrite <- subst_atom_lenv_notin_inv with (x:=x) (y:=y)(lE:=lE); auto.
           destruct Disj2 as [J1 J2].
           split; intros.
              apply J1; auto.
              apply J2 in H1; auto.
Qed.

(*******************************************************************************)
(** Reverse Renaming *)

Lemma typing_lin_rev_renamings : forall E lE e t asubst,
  typing E lE e t ->
  wf_atom_subst asubst ->
  disjdom (atom_subst_codom asubst) (dom E) ->
  disjdom (dom asubst) (dom E `union` dom lE) ->
  typing E (rev_subst_atoms_lenv asubst lE) (rev_subst_atoms_exp asubst e) t.
Proof.
  intros E lE e t asubst Typing Wfa Disj1 Disj2.
  generalize dependent E.
  generalize dependent lE.
  generalize dependent e.
  generalize dependent t.
  induction Wfa; intros; simpl; auto.
    apply IHWfa.
      apply typing_lin_renaming; try solve [assumption].
        destruct Disj1 as [J1 J2].
        assert (y `in` atom_subst_codom ([(x,y)]++AE)). simpl. auto.
        apply J1 in H1. auto.

        destruct Disj2 as [J1 J2].
        apply J1.
        simpl. auto.

      destruct Disj1 as [J1 J2].
      split; intros.
        apply J1. simpl. auto.
        apply J2 in H1. simpl in H1. auto.

      simpl in Disj2.
      destruct (in_dec y (dom lE)).
         apply binds_In_inv in i.
         destruct i as [a Binds].
         apply subst_atom_lenv_in_inv with (y:=x) in Binds; auto.
           destruct Binds as [lE1 [lE2 [EQ1 EQ2]]]; subst.
           rewrite EQ2.
           destruct Disj2 as [J1 J2].
           split; intros.
             assert (x0 <> x) as x0ny.
               rewrite asubst_atoms__dom_codom in H.
               clear H0 IHWfa J1 J2 EQ2. fsetdec.
             assert (x0 `in` add x (dom AE)) as x0in. fsetdec.
             apply J1 in x0in. simpl_env in x0in. simpl_env. fsetdec.

             assert (x0 `in` {{x}} \/ x0 `in` (dom E) `union` (dom lE1) `union` (dom lE2)) as x0in. 
               simpl_env in H1. fsetdec.
             clear H1.
             destruct x0in as [x0in | x0in].
               clear H0 J1 J2 Disj1 EQ2.
               rewrite asubst_atoms__dom_codom in H.
               fsetdec.
                
               assert (x0 `in` (dom E) `union` dom (lE1++[(y,a)]++lE2)) as x0in'. 
                 simpl_env. fsetdec.
               apply J2 in x0in'. fsetdec.
           apply typing_regular in Typing.
           decompose [and] Typing. apply uniq_from_wf_lenv in H3; auto.

         rewrite <- subst_atom_lenv_notin_inv with (x:=y) (y:=x)(lE:=lE); auto.
           destruct Disj2 as [J1 J2].
           split; intros.
              apply J1; auto.
              apply J2 in H1; auto.
Qed.

(*******************************************************************************)
(** misc *)

Lemma id_rev_subst_atom_lenv : forall lE x y,
  uniq lE ->
  x `in` dom lE ->
  y `notin` dom lE ->
  lE = (subst_atom_lenv (subst_atom_lenv lE x y) y x).
Proof.
  intros lE x y Uniq xinlE ynoitnlE.
  apply binds_In_inv in xinlE.
  destruct xinlE as [b xinlE].
  apply subst_atom_lenv_in_inv with (y:=y) in xinlE; eauto.
  destruct xinlE as [lE1 [lE2 [EQ1 EQ2]]]; subst.
  rewrite EQ2.

  assert (binds y b (lE1 ++ [(y,b)] ++  lE2)) as Binds. auto.
  assert (uniq (lE1++[(y,b)]++lE2)) as Uniq'. solve_uniq.
  apply subst_atom_lenv_in_inv with (y:=x) in Binds; eauto.
  destruct Binds as [lE1' [lE2' [EQ1' EQ2']]]; subst.
  rewrite EQ2'.
  apply mid_list_inv in EQ1'; auto.
  destruct EQ1'; subst.
  auto.
Qed.

Lemma subst_atoms_lenv__dom_upper : forall asubst lEnv,
  wf_atom_subst asubst ->
  uniq lEnv ->
  disjdom (atom_subst_codom asubst) (dom lEnv) ->
  dom (subst_atoms_lenv asubst lEnv) [<=] dom lEnv `union` atom_subst_codom asubst.
Proof.
  intros asubst lEnv Wfa Uniq Disj.
  generalize dependent lEnv.
  induction Wfa; intros.
    simpl. fsetdec.

    simpl.
    destruct (in_dec x (dom lEnv)) as [J | J].
      apply binds_In_inv in J. destruct J as [b J].
      apply subst_atom_lenv_in_inv with (y:=y) in J; auto.
      destruct J as [lE1 [lE2 [EQ1 EQ2]]]; subst.
      rewrite EQ2. 
      rewrite subst_atoms_lenv_app.
      rewrite subst_atoms_lenv_app.
      simpl_env.
      assert (uniq (lE1++lE2)) as Uniq'. solve_uniq.
      apply IHWfa in Uniq'; auto.
         rewrite subst_atoms_lenv_app in Uniq'.
         rewrite dom_app in Uniq'.
         rewrite <- subst_atoms_lenv_notin_inv with (lE:=(y ~ b)); auto.
           simpl_env.
           simpl_env in Uniq'.
           clear Wfa H H0 IHWfa Uniq Disj EQ2.
           fsetdec.

           rewrite asubst_atoms__dom_codom in H0.
           clear Wfa Uniq H IHWfa Uniq' Disj EQ2.
           solve_uniq.

           destruct Disj as [J1 J2].
           split; intros.
             assert (x0 `in` atom_subst_codom ([(x,y)]++AE)) as x0in. simpl. auto.
             apply J1 in x0in. simpl_env in x0in. simpl_env. auto.

             assert (x0 `in` dom (lE1++[(x,b)]++lE2)) as x0in. simpl_env. simpl_env in H1. fsetdec.
             apply J2 in x0in. simpl in x0in. auto.

      apply subst_atom_lenv_notin_inv with (y:=y) in J; auto.
      rewrite <- J.  clear J.
      apply IHWfa in Uniq; auto.
        clear Wfa H H0 IHWfa Disj.
        fsetdec.

        destruct Disj as [J1 J2].
        split; intros.
          assert (x0 `in` atom_subst_codom ([(x,y)]++AE)) as x0in. simpl. auto.
          apply J1 in x0in. simpl_env in x0in. simpl_env. auto.

          apply J2 in H1. simpl in H1. auto.
Qed.

Lemma uniq_renaming : forall lE x y,
  uniq lE ->
  y `notin` dom lE ->
  uniq (subst_atom_lenv lE x y).
Proof.
  intros lE x y Uniq ynotin.
  destruct (@in_dec x (dom lE)) as [xin | xnotin'].
    apply binds_In_inv in xin.
    destruct xin as [b Binds].
    apply subst_atom_lenv_in_inv with (y:=y) in Binds; eauto.
    destruct Binds as [lE1 [lE2 [EQ1 EQ2]]]; subst.
    rewrite EQ2.
    apply uniq_renaming_one with (y0:=y)in Uniq; auto.
       assert (x `notin` dom lE1). apply fresh_mid_head in Uniq; auto.
       assert (x `notin` dom lE2). apply fresh_mid_tail in Uniq; auto.
       fsetdec.

    rewrite <- subst_atom_lenv_notin_inv; auto.
Qed.  

Lemma uniq_renamings : forall lE asubst,
  uniq lE ->
  wf_atom_subst asubst ->
  disjdom (atom_subst_codom asubst) (dom lE) ->
  uniq (subst_atoms_lenv asubst lE).
Proof.
  intros lE asubst Uniq Wfa Disj.
  generalize dependent lE.
  induction Wfa; intros; simpl; auto.
    apply IHWfa.
      apply uniq_renaming; auto.
        destruct Disj as [J1 J2].
        apply J1.
        simpl. auto.

      simpl in Disj.
      destruct (in_dec x (dom lE)).
         apply binds_In_inv in i.
         destruct i as [a Binds].
         apply subst_atom_lenv_in_inv with (y:=y) in Binds; auto.
           destruct Binds as [lE1 [lE2 [EQ1 EQ2]]]; subst.
           rewrite EQ2.
           destruct Disj as [J1 J2].
           split; intros.
             assert (x0 <> y) as x0ny.
               rewrite asubst_atoms__dom_codom in H0.
               clear H IHWfa J1 J2 EQ2. fsetdec.
             assert (x0 `in` union {{y}} (atom_subst_codom AE)) as x0in. fsetdec.
             apply J1 in x0in. simpl_env in x0in. simpl_env. fsetdec.

             assert (x0 `in` {{y}} \/ x0 `in` (dom lE1) `union` (dom lE2)) as x0in. 
               simpl_env in H1. fsetdec.
             clear H1.
             destruct x0in as [x0in | x0in].
               clear H J1 J2 EQ2.
               rewrite asubst_atoms__dom_codom in H0.
               fsetdec.
                
               assert (x0 `in` dom (lE1++[(x,a)]++lE2)) as x0in'. 
                 simpl_env. fsetdec.
               apply J2 in x0in'. fsetdec.

         rewrite <- subst_atom_lenv_notin_inv with (x:=x) (y:=y)(lE:=lE); auto.
           destruct Disj as [J1 J2].
           split; intros.
              apply J1; auto.
              apply J2 in H1; auto.
Qed.

Lemma subst_atom_lenv_swap : forall lE y x a0 a,
  uniq lE ->
  y <> x -> a <> a0 ->
  y <> a0 -> y <> a ->
  x <> a0 -> x <> a ->
  x `notin` dom lE -> a `notin` dom lE ->
  subst_atom_lenv (subst_atom_lenv lE y x) a0 a =
    subst_atom_lenv (subst_atom_lenv lE a0 a) y x.
Proof.
  intros lE a1 a2 a3 a4 Uniq.
  generalize dependent a1.
  generalize dependent a2.
  generalize dependent a3.
  generalize dependent a4.
  induction Uniq; intros; simpl; auto.
    destruct (a1==x); subst; simpl.
      destruct (a3==x); subst; simpl.
        contradict H2; auto.
        destruct (a3==a2); subst; simpl.
          contradict H4; auto.
          destruct (@eq_dec atom _ x x); subst; simpl.
            simpl in *.
            rewrite <- IHUniq; auto.

            contradict n1; auto.
        destruct (a3==x); subst; simpl.
          destruct (a1==a4); subst; simpl.
            contradict H3; auto.

            simpl in *.
            rewrite <- IHUniq; auto.
          destruct (a1==x); subst; simpl.
            contradict n; auto.

            simpl in *.
            rewrite <- IHUniq; auto.
Qed.

Lemma id_subst_atom_lenv : forall lE x,
  lE = subst_atom_lenv lE x x.
Proof. 
  induction lE; intros; simpl; auto.
    destruct a. 
    destruct (x==a); subst.
       rewrite <- IHlE; auto.
       rewrite <- IHlE; auto.
Qed.

Lemma subst_atoms_lenv_swap :  forall AE lE x y, 
  wf_atom_subst AE ->  
  x `notin` atom_subst_atoms AE ->
  y `notin` atom_subst_atoms AE ->
  x <> y ->
  uniq lE ->
  x `notin` dom lE ->
  (atom_subst_codom AE) [<=] dom lE ->
  disjdom (dom AE) (dom lE) ->
  rev_subst_atoms_lenv AE (subst_atom_lenv lE y x) = subst_atom_lenv (rev_subst_atoms_lenv AE lE) y x.
Proof.
  intros AE lE x y Wfa xnotinAE ynotinAE xny Uniq xnotinlE Sub Disj.
  generalize dependent lE.
  generalize dependent x.
  generalize dependent y.
  induction Wfa; intros.
    simpl. auto.

    simpl in xnotinAE. simpl in ynotinAE.
    rewrite asubst_atoms__dom_codom in xnotinAE.
    rewrite asubst_atoms__dom_codom in ynotinAE.
    simpl in *.
    assert (x  `notin` dom lE) as a0nlE.
      destruct Disj as [Disj1 Disj2].
      apply Disj1. auto.
    assert (y `in` dom lE) as ainlE.
      clear xnotinAE ynotinAE xny xnotinlE IHWfa.
      fsetdec.
    assert (y <> x) as a0na.
      clear xnotinAE ynotinAE xny xnotinlE IHWfa.
      fsetdec.
    rewrite subst_atom_lenv_swap; auto.   
      rewrite IHWfa; auto.
        rewrite asubst_atoms__dom_codom. auto.
        rewrite asubst_atoms__dom_codom. auto.
        apply uniq_renaming; auto.
        
        apply binds_In_inv in ainlE.
        destruct ainlE as [b ainlE].
        apply subst_atom_lenv_in_inv with (y:=x) in ainlE; eauto.
        destruct ainlE as [lE1 [lE2 [EQ1 EQ2]]]; subst.
        rewrite EQ2. 
        clear ynotinAE xny IHWfa. auto.        

        apply binds_In_inv in ainlE.
        destruct ainlE as [b ainlE].
        apply subst_atom_lenv_in_inv with (y:=x) in ainlE; eauto.
        destruct ainlE as [lE1 [lE2 [EQ1 EQ2]]]; subst.
        rewrite EQ2.
        rewrite asubst_atoms__dom_codom in H.
        rewrite asubst_atoms__dom_codom in H0.
        assert (AtomSetImpl.diff (union {{y}} (atom_subst_codom AE)) {{y}} [=] (atom_subst_codom AE)) as EQ.
          clear xnotinAE ynotinAE xny a0na a0nlE Sub Disj. fsetdec.
        assert (y `notin` dom lE1) as xnotinlE1.
          apply fresh_mid_head in Uniq; auto.
        assert (y `notin` dom lE2) as xnotinlE2.
          apply fresh_mid_tail in Uniq; auto.
        simpl_env in Sub.
        assert (AtomSetImpl.diff (union (dom lE1) (union {{y}} (dom lE2))) {{y}}[=] union (dom lE1) (dom lE2)) as EQ'. 
          clear xnotinAE ynotinAE xny a0na a0nlE Sub Disj EQ EQ2. fsetdec.
        assert (dom (lE1++lE2) [<=] dom (lE1++[(x,b)]++lE2)) as Sub'.
          simpl_env. clear xnotinAE ynotinAE xny a0na a0nlE Sub Disj EQ EQ2 EQ'. fsetdec.
        assert ((atom_subst_codom AE) [<=] dom (lE1++lE2)) as Sub''.
          rewrite <- EQ. simpl_env. rewrite <- EQ'.
          clear xnotinAE ynotinAE xny a0na a0nlE Sub' Disj EQ EQ2 EQ' xnotinlE1 xnotinlE2 xnotinlE IHWfa H H0.
          fsetdec.
        clear xnotinAE ynotinAE xny a0na a0nlE Sub Disj EQ EQ2 EQ' xnotinlE1 xnotinlE2 xnotinlE IHWfa H H0.
        fsetdec.
 
        apply binds_In_inv in ainlE.
        destruct ainlE as [b ainlE].
        apply subst_atom_lenv_in_inv with (y:=x) in ainlE; eauto.
        destruct ainlE as [lE1 [lE2 [EQ1 EQ2]]]; subst.
        rewrite EQ2.
        apply disjdom_cons_2 in Disj.
        rewrite asubst_atoms__dom_codom in H.
        rewrite asubst_atoms__dom_codom in H0.
        destruct Disj as [Disj1 Disj2].
        split; intros.
          assert (x1 <> x) as x1nx.
            clear xnotinAE ynotinAE xny a0na a0nlE Sub Disj1 Disj2 EQ2 H0. 
            fsetdec.          
          apply Disj1 in H1. simpl_env in H1. simpl_env. 
          clear xnotinAE ynotinAE xny a0na a0nlE Sub Disj1 Disj2 EQ2 H0. 
          fsetdec.

          destruct (x1 == x); subst.
            clear xnotinAE ynotinAE xny a0na a0nlE Sub Disj1 Disj2 EQ2 H0. 
            fsetdec.          
          apply Disj2. simpl_env in H1. simpl_env. 
          clear xnotinAE ynotinAE xny a0na a0nlE Sub Disj1 Disj2 EQ2 H0. 
          fsetdec.
Qed.

Lemma subst_atoms_lenv__dom_lower : forall asubst lEnv,
  wf_atom_subst asubst ->
  uniq lEnv ->
  dom asubst [<=] dom lEnv ->
  disjdom (atom_subst_codom asubst) (dom lEnv) ->
  atom_subst_codom asubst [<=] dom (subst_atoms_lenv asubst lEnv).
Proof.
  intros asubst lEnv Wfa Uniq Sub Disj.
  generalize dependent lEnv.
  induction Wfa; intros.
    simpl. fsetdec.

    simpl.
    assert (x `in` dom lEnv) as J.
      simpl in Sub.
      clear H H0 Disj.
      fsetdec.
    apply binds_In_inv in J. destruct J as [b J].
    apply subst_atom_lenv_in_inv with (y:=y) in J; auto.
    destruct J as [lE1 [lE2 [EQ1 EQ2]]]; subst.
    rewrite EQ2. 
    rewrite subst_atoms_lenv_app.
    rewrite subst_atoms_lenv_app.
    simpl_env.
    assert (uniq (lE1++lE2)) as Uniq'. solve_uniq.
    assert (dom AE [<=] dom (lE1++lE2)) as Sub'.
      assert (x `notin` dom lE1) as xnotinlE1.
        apply fresh_mid_head in Uniq; auto.
      assert (x `notin` dom lE2) as xnotinlE2.
        apply fresh_mid_tail in Uniq; auto.
      rewrite asubst_atoms__dom_codom in H.
      clear H0 Disj IHWfa Uniq EQ2.
      simpl_env in Sub. simpl_env.
      fsetdec.
    assert (disjdom (atom_subst_codom AE) (dom (lE1++lE2))) as Disj'.
      destruct Disj as [Disj1 Disj2].
      split; intros.
         assert (x0 `in` atom_subst_codom ([(x, y)]++AE)) as x0in. simpl. auto.
         apply Disj1 in x0in. simpl_env in x0in. simpl_env. auto.
       
         assert (x0 `in` dom (lE1++[(x, b)]++lE2)) as x0in. simpl_env. simpl_env in H1. fsetdec.
         apply Disj2 in x0in. simpl in x0in. auto.      
    apply IHWfa in Uniq'; auto.
       rewrite subst_atoms_lenv_app in Uniq'.
       rewrite dom_app in Uniq'.
       rewrite <- subst_atoms_lenv_notin_inv with (lE:=(y ~ b)); auto.
         simpl_env.
         clear Wfa H H0 IHWfa Uniq Disj EQ2 Disj' Sub' Sub.
         fsetdec.

         rewrite asubst_atoms__dom_codom in H0.
         clear Wfa Uniq H IHWfa Uniq' Disj EQ2.
         solve_uniq.
Qed.

Lemma subst_atoms_lenv_disjdom : forall AE lE,
  wf_atom_subst AE ->
  uniq lE ->
  dom AE [<=] dom lE ->
  disjdom (atom_subst_codom AE) (dom lE) ->
  disjdom (dom AE) (dom (subst_atoms_lenv AE lE)).
Proof.
  intros asubst lE Wfa Uniq Sub Disj.
  generalize dependent lE.
  induction Wfa; intros.
  simpl. auto.

  simpl. 
  assert (dom AE [<=] dom lE) as Sub'.
    simpl in Sub. fsetdec.
  assert (disjdom (atom_subst_codom AE) (dom lE)) as Disj'.
    destruct Disj as [Disj1 Disj2].
    rewrite asubst_atoms__dom_codom in H0.
    rewrite asubst_atoms__dom_codom in H.
    split; intros.
      assert (x0 <> y) as x0ny.        
        fsetdec.
      assert (x0 `in` atom_subst_codom ([(x,y)]++AE)) as J. simpl. auto. 
      apply Disj1 in J. 
      simpl_env in J. simpl_env. auto.

      destruct (x0 == y); subst.
        fsetdec.
  
        apply Disj2 in H1. simpl in H1. auto.
   assert (J:=Uniq).
   apply IHWfa in J; auto.
   assert (x `in` dom lE) as JJ.
     simpl in Sub. fsetdec.
   apply binds_In_inv in JJ.
   destruct JJ as [b JJ].
   apply subst_atom_lenv_in_inv with (y:=y) in JJ; eauto.
   destruct JJ as [lE1 [lE2 [EQ1 EQ2]]]; subst.
   rewrite EQ2.
   rewrite subst_atoms_lenv_app.
   rewrite subst_atoms_lenv_app.
   simpl_env.
   rewrite subst_atoms_lenv_app in J.
   rewrite subst_atoms_lenv_app in J.
   rewrite asubst_atoms__dom_codom in H0.
   rewrite asubst_atoms__dom_codom in H.
   rewrite <- subst_atoms_lenv_notin_inv with (lE:=(y~b)); auto.
   rewrite <- subst_atoms_lenv_notin_inv with (lE:=(x~b)) in J; auto.
   destruct J as [J1 J2].
   assert (x `notin` dom (subst_atoms_lenv AE (lE1++lE2))) as xnoin.
     assert (dom (subst_atoms_lenv AE (lE1++lE2)) [<=] dom (lE1++lE2) `union` atom_subst_codom AE) as Sub''.
       apply subst_atoms_lenv__dom_upper; auto.
          solve_uniq.

          apply disjdom_sub with (D1:=dom(lE1++[(x,b)]++lE2)); auto.
            simpl_env. clear Sub Disj Disj' Sub' H H0 IHWfa J1 J2 EQ2. fsetdec.
     assert (x `notin` dom (lE1++lE2) `union` atom_subst_codom AE) as xnotin'.          
       assert (x `notin` dom lE1) as xnotinlE1.
         apply fresh_mid_head in Uniq; auto.
       assert (x `notin` dom lE2) as xnotinlE2.
         apply fresh_mid_tail in Uniq; auto.
         clear Sub Disj Disj' Sub' H0 IHWfa J1 J2 EQ2. simpl_env. fsetdec.
     clear Sub Disj Disj' Sub' H0 IHWfa J1 J2 EQ2 H. fsetdec.
   split; intros.
     destruct (x0 == x); subst.
       simpl_env. rewrite subst_atoms_lenv_app in xnoin. simpl_env in xnoin.
       clear Sub Disj Disj' Sub' IHWfa J1 J2 EQ2 H1 H. fsetdec.

       assert (x0 `in` dom AE) as x0inAE.
         clear Sub Disj Disj' Sub' IHWfa J1 J2 EQ2 H. fsetdec.
       assert (x0 <> y) as x0ny.
         clear Sub Disj Disj' Sub' IHWfa J1 J2 EQ2 H. fsetdec.
       apply J1 in x0inAE. simpl_env in x0inAE. simpl_env.
       clear Sub Disj Disj' Sub' IHWfa J1 J2 EQ2 H1 H. fsetdec.

     destruct (x0 == x); subst.
       destruct (x == y); subst.
          clear Sub Disj Disj' Sub' IHWfa J1 J2 EQ2.
          destruct_notin. contradict NotInTac; auto.

          clear Sub Disj Disj' Sub' IHWfa J1 J2 EQ2 H H0.
          rewrite subst_atoms_lenv_app in xnoin.
          simpl_env in H1. simpl_env in xnoin.
          contradict H1. clear H1. fsetdec.
       destruct (x0 == y); subst.
          clear Sub Disj Disj' Sub' IHWfa J1 J2 EQ2 H H1.
          fsetdec.     

          assert (x0 `in` dom (subst_atoms_lenv AE lE1 ++ [(x,b)] ++ subst_atoms_lenv AE lE2)) as x0in.
            clear Sub Disj Disj' Sub' IHWfa J1 J2 EQ2 H H0.
            simpl_env in *. fsetdec.
          apply J2 in x0in.
          clear Sub Disj Disj' Sub' IHWfa J1 J2 EQ2 H H0.
          fsetdec.
Qed.           

Lemma id_rev_subst_atoms_lenv : forall asubst lE,
  wf_atom_subst asubst ->
  uniq lE ->
  dom asubst [<=] dom lE ->
  disjdom (atom_subst_codom asubst) (dom lE) ->
  lE = (rev_subst_atoms_lenv asubst (subst_atoms_lenv asubst lE)).
Proof.
  intros asubst lE Wfa Uniq Sub Disj.
  generalize dependent lE.
  induction Wfa; intros.
  simpl. auto.

  simpl.
  rewrite subst_atoms_lenv_swap; auto.
    rewrite <- IHWfa.
      apply id_rev_subst_atom_lenv; auto.
        simpl in Sub. fsetdec.

        destruct Disj as [Disj1 Disj2].
        apply Disj1. simpl. auto.

      apply uniq_renaming; auto.
        destruct Disj as [Disj1 Disj2].
        apply Disj1. simpl. auto.

      assert (x `in` dom lE) as J.
        simpl in Sub. fsetdec.
      apply binds_In_inv in J.
      destruct J as [b J].
      apply subst_atom_lenv_in_inv with (y:=y) in J; eauto.
      destruct J as [lE1 [lE2 [EQ1 EQ2]]]; subst.
      rewrite EQ2.
      rewrite asubst_atoms__dom_codom in H.
      assert (dom AE [=] AtomSetImpl.diff (dom ([(x,y)]++AE)) {{x}}) as EQ'.
        simpl. clear Sub EQ2 H0. fsetdec.
      assert (x `notin` dom lE1) as xnotinlE1.
        apply fresh_mid_head in Uniq; auto.
      assert (x `notin` dom lE2) as xnotinlE2.
        apply fresh_mid_tail in Uniq; auto.
      assert (dom lE1 `union` dom lE2 [=] AtomSetImpl.diff (dom (lE1++[(x,b)]++lE2)) {{x}}) as EQ''.
        simpl_env. clear Sub EQ2 H0 H. fsetdec.
      assert (dom AE [<=] dom lE1 `union` dom lE2) as Sub'.
        rewrite EQ'. rewrite EQ''.
        clear EQ2 H0 H EQ' EQ''. 
        fsetdec.
      assert (dom lE1 `union` dom lE2 [<=] dom (lE1++[(y,b)]++lE2)) as Sub''.
        simpl_env. clear Sub EQ2 H0 H EQ' EQ''. fsetdec.
      clear Sub EQ2 H0 H EQ' EQ'' xnotinlE1 xnotinlE2. 
      fsetdec.

      assert (x `in` dom lE) as J.
        simpl in Sub. fsetdec.
      apply binds_In_inv in J.
      destruct J as [b J].
      apply subst_atom_lenv_in_inv with (y:=y) in J; eauto.
      destruct J as [lE1 [lE2 [EQ1 EQ2]]]; subst.
      rewrite EQ2. clear EQ2.
      rewrite asubst_atoms__dom_codom in H.
      rewrite asubst_atoms__dom_codom in H0.
      destruct Disj as [Disj1 Disj2].
      split; intros.
        assert (x0 <> y) as x0ny.        
          fsetdec.
        assert (x0 `in` atom_subst_codom ([(x,y)]++AE)) as J. simpl. auto. 
        apply Disj1 in J. 
        simpl_env in J. simpl_env. auto.

        destruct (x0 == y); subst.
          fsetdec.
  
          assert (x0 `in` dom (lE1++[(x,b)]++lE2)) as J. 
            simpl_env. simpl_env in H1. 
            clear H H0 IHWfa Uniq Sub Disj1 Disj2.
            fsetdec.
          apply Disj2 in J. simpl in J. auto.
    apply uniq_renamings with (asubst:=([(x,y)]++AE)) in Uniq; auto.

    assert (x  `in` dom lE) as xinlE.
       simpl in Sub. clear H H0 IHWfa Disj. fsetdec.
    apply binds_In_inv in xinlE.
    destruct xinlE as [b xinlE].
    apply subst_atom_lenv_in_inv with (y:=y) in xinlE; eauto.
    destruct xinlE as [lE1 [lE2 [EQ1 EQ2]]]; subst.
    rewrite EQ2. 
    assert (dom (subst_atoms_lenv AE (lE1++[(y,b)]++lE2)) [<=] dom (lE1++[(y,b)]++lE2) `union` atom_subst_codom AE) as Sub'.
      apply subst_atoms_lenv__dom_upper; auto. 
        assert (y `notin` dom (lE1++[(x,b)]++lE2)) as yntlE1.
          destruct Disj as [Disj1 Disj2].
          apply Disj1. simpl. auto.
        clear H H0 IHWfa Sub Disj EQ2.
        simpl_env in yntlE1. solve_uniq.

        destruct Disj as [Disj1 Disj2].
        rewrite asubst_atoms__dom_codom in H.
        rewrite asubst_atoms__dom_codom in H0.
        split; intros.
          assert (x0 <> y) as x0ny.
            clear H IHWfa Uniq Sub Disj1 Disj2 EQ2. solve_uniq.
          assert (x0 `in` atom_subst_codom ([(x,y)]++AE)) as x0in. simpl. auto.
          apply Disj1 in x0in.
          simpl_env in x0in. simpl_env. auto.

          destruct (x0==y); subst.
            fsetdec.

            assert (x0 `in` dom (lE1++[(x,b)]++lE2)) as x0in. 
              simpl_env. simpl_env in H1. 
              clear H IHWfa Uniq Sub Disj1 Disj2 EQ2 H0.
              fsetdec.
            apply Disj2 in x0in.
            simpl in x0in. auto.
    assert (x `notin` dom (lE1++[(y,b)]++lE2) `union` atom_subst_codom AE) as xnotin.
      simpl_env.
      assert (x `notin` dom lE1) as xnotinlE1.
        apply fresh_mid_head in Uniq; auto.
      assert (x `notin` dom lE2) as xnotinlE2.
        apply fresh_mid_tail in Uniq; auto.
      rewrite asubst_atoms__dom_codom in H.
      clear IHWfa Uniq Sub Disj Sub' EQ2.
      fsetdec.
    clear IHWfa Uniq Sub Disj H H0 EQ2.
    fsetdec.

    assert (x  `in` dom lE) as xinlE.
       simpl in Sub. clear H H0 IHWfa Disj. fsetdec.
    apply binds_In_inv in xinlE.
    destruct xinlE as [b xinlE].
    apply subst_atom_lenv_in_inv with (y:=y) in xinlE; eauto.
    destruct xinlE as [lE1 [lE2 [EQ1 EQ2]]]; subst.
    rewrite EQ2. 
    rewrite asubst_atoms__dom_codom in H0.
    rewrite asubst_atoms__dom_codom in H.
    assert (y `notin` dom (lE1++[(x,b)]++lE2)) as ynoin.
       destruct Disj as [Disj1 Disj2].
       apply Disj1. simpl. auto.
    apply subst_atoms_lenv__dom_lower; auto.
      clear EQ2 Disj Sub IHWfa H. solve_uniq.

      assert (dom AE [<=] dom (lE1++lE2))  as Sub'.
        clear EQ2 Disj IHWfa H0 ynoin.
        assert (x `notin` dom lE1) as xnotinlE1.
          apply fresh_mid_head in Uniq; auto.
        assert (x `notin` dom lE2) as xnotinlE2.
          apply fresh_mid_tail in Uniq; auto.
        simpl_env in Sub. simpl_env. fsetdec.
      assert (dom (lE1++lE2) [<=] dom (lE1++[(y,b)]++lE2))  as Sub''.
        simpl_env. clear EQ2 Disj Sub IHWfa H H0 Sub'. fsetdec.
      clear EQ2 Disj Sub IHWfa H H0 ynoin. fsetdec.

      destruct Disj as [Disj1 Disj2].
      split; intros.
        assert (x0 <> y) as x0ny.
          clear H IHWfa Uniq Sub Disj1 Disj2 EQ2. solve_uniq.
        assert (x0 `in` atom_subst_codom ([(x,y)]++AE)) as x0in. simpl. auto.
        apply Disj1 in x0in.
        simpl_env in x0in. simpl_env. auto.

        destruct (x0==y); subst.
          fsetdec.

          assert (x0 `in` dom (lE1++[(x,b)]++lE2)) as x0in. 
            simpl_env. simpl_env in H1. 
            clear H IHWfa Uniq Sub Disj1 Disj2 EQ2 H0.
            fsetdec.
          apply Disj2 in x0in.
          simpl in x0in. auto.
       
    assert (x  `in` dom lE) as xinlE.
       simpl in Sub. clear H H0 IHWfa Disj. fsetdec.
    apply binds_In_inv in xinlE.
    destruct xinlE as [b xinlE].
    apply subst_atom_lenv_in_inv with (y:=y) in xinlE; eauto.
    destruct xinlE as [lE1 [lE2 [EQ1 EQ2]]]; subst.
    rewrite EQ2. 
    rewrite asubst_atoms__dom_codom in H0.
    rewrite asubst_atoms__dom_codom in H.
    assert (y `notin` dom (lE1++[(x,b)]++lE2)) as ynoin.
       destruct Disj as [Disj1 Disj2].
       apply Disj1. simpl. auto.
    apply subst_atoms_lenv_disjdom; auto.
      clear EQ2 Disj Sub IHWfa H. solve_uniq.

      assert (dom AE [<=] dom (lE1++lE2))  as Sub'.
        clear EQ2 Disj IHWfa H0 ynoin.
        assert (x `notin` dom lE1) as xnotinlE1.
          apply fresh_mid_head in Uniq; auto.
        assert (x `notin` dom lE2) as xnotinlE2.
          apply fresh_mid_tail in Uniq; auto.
        simpl_env in Sub. simpl_env. fsetdec.
      assert (dom (lE1++lE2) [<=] dom (lE1++[(y,b)]++lE2))  as Sub''.
        simpl_env. clear EQ2 Disj Sub IHWfa H H0 Sub'. fsetdec.
      clear EQ2 Disj Sub IHWfa H H0 ynoin. fsetdec.

      destruct Disj as [Disj1 Disj2].
      split; intros.
        assert (x0 <> y) as x0ny.
          clear H IHWfa Uniq Sub Disj1 Disj2 EQ2. solve_uniq.
        assert (x0 `in` atom_subst_codom ([(x,y)]++AE)) as x0in. simpl. auto.
        apply Disj1 in x0in.
        simpl_env in x0in. simpl_env. auto.

        destruct (x0==y); subst.
          fsetdec.

          assert (x0 `in` dom (lE1++[(x,b)]++lE2)) as x0in. 
            simpl_env. simpl_env in H1. 
            clear H IHWfa Uniq Sub Disj1 Disj2 EQ2 H0.
            fsetdec.
          apply Disj2 in x0in.
          simpl in x0in. auto.
Qed.

Lemma rev_subst_atoms_exp_swap :  forall AE e x y, 
  wf_atom_subst AE ->  
  x `notin` atom_subst_atoms AE ->
  y `notin` atom_subst_atoms AE ->
  x <> y ->
  x `notin` fv_ee e ->
  (atom_subst_codom AE) [<=] fv_ee e ->
  disjdom (dom AE) (fv_ee e) ->
  rev_subst_atoms_exp AE (subst_ee y x e) = subst_ee y x (rev_subst_atoms_exp AE e).
Proof.
  intros AE e x y Wfa xnotinAE ynotinAE xny xnotine Sub Disj.
  generalize dependent e.
  generalize dependent x.
  generalize dependent y.
  induction Wfa; intros.
    simpl. auto.

    simpl in xnotinAE. simpl in ynotinAE.
    rewrite asubst_atoms__dom_codom in xnotinAE.
    rewrite asubst_atoms__dom_codom in ynotinAE.
    simpl in *.
    assert (x  `notin` fv_ee e) as xne.
      destruct Disj as [Disj1 Disj2].
      apply Disj1. auto.
    assert (y `in` fv_ee e) as yine.
      clear xnotinAE ynotinAE xny xnotine IHWfa.
      fsetdec.
    assert (y <> x) as ynx.
      clear xnotinAE ynotinAE xny xnotine IHWfa.
      fsetdec.
    rewrite subst_ee_commute; auto.
      rewrite IHWfa; auto.
        rewrite asubst_atoms__dom_codom. auto.
        rewrite asubst_atoms__dom_codom. auto.

        assert (J:=@subst_ee_fv_ee_sub e y x).
        assert (x0 `notin` union (fv_ee e) (fv_ee x)) as x0notin.
           clear ynotinAE xny IHWfa Sub yine ynx J H H0 xne.
           destruct_notin.
           clear Disj NotInTac NotInTac0 NotInTac1 NotInTac2 NotInTac3.
           simpl. fsetdec.
        clear ynotinAE xny IHWfa Sub yine ynx H H0 xne xnotinAE.
        fsetdec.

        assert (J:=@subst_ee_fv_ee_in e y x yine).
        rewrite J. clear J.
        rewrite asubst_atoms__dom_codom in H.
        rewrite asubst_atoms__dom_codom in H0.
        assert (atom_subst_codom AE [=] AtomSetImpl.diff (union {{y}} (atom_subst_codom AE)) {{y}}) as EQ.
          clear ynotinAE xnotinAE xny IHWfa Sub yine ynx H xne xne xnotine.
          destruct_notin. clear NotInTac0 NotInTac Disj.
          fsetdec.
        assert (atom_subst_codom AE [<=] AtomSetImpl.diff (fv_ee e) {{y}}) as Sub'.
          rewrite EQ. 
          clear ynotinAE xnotinAE xny IHWfa EQ yine ynx H xne xne xnotine H0.
          fsetdec.
        clear ynotinAE xnotinAE xny IHWfa EQ yine ynx H xne xne xnotine H0.
        fsetdec.

        assert (J:=@subst_ee_fv_ee_in e y x yine).
        rewrite asubst_atoms__dom_codom in H.
        rewrite asubst_atoms__dom_codom in H0.
        apply disjdom_sym_1.
        apply disjdom_eq with (D1:=union (AtomSetImpl.diff (fv_ee e) {{y}}) (fv_ee x)); auto.
          destruct Disj as [Disj1 Disj2].
          split; intros.
            destruct (x1==x); subst.
              clear ynotinAE xnotinAE xny IHWfa yine ynx H0 xne xne xnotine.
              auto.

              assert (x1 `in` fv_ee e) as x1in. 
                clear ynotinAE xnotinAE xny IHWfa yine ynx H0 xne xne xnotine J H Sub Disj1 Disj2.
                simpl in H1. fsetdec.
              apply Disj2 in x1in. auto. 

            destruct (x1==x); subst.
              clear ynotinAE xnotinAE xny IHWfa yine ynx H0 xne xne xnotine.
              auto.

              assert (x1 `in` add x (dom AE)) as x1in. auto.
              apply Disj1 in x1in.
              clear ynotinAE xnotinAE xny IHWfa yine ynx H0 xne xne xnotine. 
              simpl. auto.            

          rewrite J. clear ynotinAE xnotinAE xny IHWfa Sub yine ynx H xne xne xnotine. fsetdec.
Qed.

Lemma subst_atoms_exp__dom_upper : forall asubst e,
  wf_atom_subst asubst ->
  disjdom (atom_subst_codom asubst) (fv_ee e) ->
  fv_ee (subst_atoms_exp asubst e) [<=] (fv_ee e) `union` atom_subst_codom asubst.
Proof.
  intros asubst e Wfa Disj.
  generalize dependent e.
  induction Wfa; intros.
    simpl. fsetdec.

    simpl.
    rewrite asubst_atoms__dom_codom in H.
    rewrite asubst_atoms__dom_codom in H0.
    destruct (in_dec x (fv_ee e)) as [J | J].
      assert (disjdom (atom_subst_codom AE) (fv_ee (subst_ee x y e)))  as Disj'.
        assert (JJ:=@subst_ee_fv_ee_in e x y J).
        destruct Disj as [Disj1 Disj2].
        split; intros.
          rewrite JJ.
          destruct (x0 == y); subst.
            clear H IHWfa Disj1 Disj2 J JJ.
            contradict H1; auto.
          
            assert (x0 `in` atom_subst_codom ([(x,y)]++AE)) as x0in. simpl. auto.
            apply Disj1 in x0in.
            clear H IHWfa Disj1 Disj2 J JJ H1 H0. simpl. fsetdec.
        
          rewrite JJ in H1. clear JJ.
          destruct (x0 == y); subst.
            clear H IHWfa Disj1 Disj2 J H1.
            fsetdec.

            assert (x0 `in` fv_ee e) as x0in. 
              clear H IHWfa Disj1 Disj2 J H0. simpl in H1. fsetdec.
            apply Disj2 in x0in.
            simpl in x0in. auto.
      apply IHWfa in Disj'. clear H H0 Disj IHWfa. 
      assert (JJ:=@subst_ee_fv_ee_sub e x y). simpl in JJ. fsetdec.

      rewrite <- subst_ee_fresh with (e:=e); auto.
      assert (disjdom (atom_subst_codom AE) (fv_ee e)) as Disj'.
        simpl in Disj.
        apply disjdom_app_l in Disj. destruct Disj as [Disj1 Disj2]. auto.
      apply IHWfa in Disj'. clear H H0 Disj IHWfa J.
      fsetdec.
Qed.

Lemma subst_atoms_exp_in_fv_ee : forall asubst y e,
  y `in` fv_ee e ->
  y `notin` dom asubst ->
  y `in` fv_ee (subst_atoms_exp asubst e).
Proof.
  induction asubst; intros; simpl; auto.
    destruct a. simpl in H0. 
    assert (y `in` fv_ee (subst_ee a a0 e)) as yin.
       apply subst_ee_in_fv_ee; auto.
    apply IHasubst in yin; auto.
Qed.

Lemma subst_atoms_exp__dom_lower : forall asubst e,
  wf_atom_subst asubst ->
  dom asubst [<=] (fv_ee e) ->
  disjdom (atom_subst_codom asubst) (fv_ee e) ->
  atom_subst_codom asubst [<=] fv_ee (subst_atoms_exp asubst e).
Proof.
  intros asubst e Wfa Sub Disj.
  generalize dependent e.
  induction Wfa; intros.
    simpl. fsetdec.

    simpl.
    rewrite asubst_atoms__dom_codom in H.
    rewrite asubst_atoms__dom_codom in H0.
    assert (x `in` (fv_ee e)) as J.
      clear Wfa H H0 Disj.
      simpl in Sub. fsetdec.
    assert (disjdom (atom_subst_codom AE) (fv_ee (subst_ee x y e)))  as Disj'.
      assert (JJ:=@subst_ee_fv_ee_in e x y J).
      destruct Disj as [Disj1 Disj2].
      split; intros.
        rewrite JJ.
        destruct (x0 == y); subst.
          clear H IHWfa Disj1 Disj2 J JJ.
          contradict H1; auto.
        
          assert (x0 `in` atom_subst_codom ([(x,y)]++AE)) as x0in. simpl. auto.
          apply Disj1 in x0in.
          clear H IHWfa Disj1 Disj2 J JJ H1 H0. simpl. fsetdec.
      
        rewrite JJ in H1. clear JJ.
        destruct (x0 == y); subst.
          clear H IHWfa Disj1 Disj2 J H1.
          fsetdec.
          assert (x0 `in` fv_ee e) as x0in. 
            clear H IHWfa Disj1 Disj2 J H0. simpl in H1. fsetdec.
          apply Disj2 in x0in.
          simpl in x0in. auto.
    assert (dom (AE) [<=] (fv_ee (subst_ee x y e))) as Sub'.
      assert (JJ:=@subst_ee_fv_ee_in e x y J). rewrite JJ. clear JJ.
      assert (dom AE [=] AtomSetImpl.diff (dom ([(x, y)]++AE)) {{x}}) as EQ.
        simpl.
        clear IHWfa Disj Sub J H0. fsetdec.
      rewrite EQ. clear EQ.
      assert (AtomSetImpl.diff (dom ([(x, y)]++AE)) {{x}} [<=] AtomSetImpl.diff (fv_ee e) {{x}}) as Sub'.
        clear IHWfa Disj J H0. fsetdec.
      clear IHWfa Disj J H0 Sub. fsetdec.
    apply IHWfa in Disj'; auto. 
    assert (JJ:=@subst_ee_fv_ee_in e x y J).
    assert (y `in` fv_ee (subst_atoms_exp AE (subst_ee x y e))) as yin.
      apply subst_atoms_exp_in_fv_ee; auto.
        rewrite JJ. clear IHWfa Disj J H0 Sub' Sub. simpl. fsetdec.
    assert ({{y}} [<=] fv_ee (subst_atoms_exp AE (subst_ee x y e))) as ysub.
      clear IHWfa Disj J H0 Sub' Sub JJ H Disj'. fsetdec.
    assert (fv_ee (subst_atoms_exp AE (subst_ee x y e)) [=] {{y}} `union` (fv_ee (subst_atoms_exp AE (subst_ee x y e)))) as EQ.
      clear H H0 Disj Sub IHWfa Sub' J JJ Disj'. fsetdec.
    rewrite EQ. clear EQ JJ yin ysub Disj H H0 H Sub' Sub. fsetdec.    
Qed.

Lemma subst_atoms_exp_swap :  forall AE e x y, 
  wf_atom_subst AE ->  
  x `notin` atom_subst_atoms AE ->
  y `notin` atom_subst_atoms AE ->
  x <> y ->
  y `notin` fv_ee e ->
  (dom AE) [<=] fv_ee e ->
  disjdom (atom_subst_codom AE) (fv_ee e) ->
  subst_atoms_exp AE (subst_ee x y e) = subst_ee x y (subst_atoms_exp AE e).
Proof.
  intros AE e x y Wfa xnotinAE ynotinAE ynx ynotine Sub Disj.
  generalize dependent e.
  generalize dependent x.
  generalize dependent y.
  induction Wfa; intros.
    simpl. auto.

    simpl in xnotinAE. simpl in ynotinAE.
    rewrite asubst_atoms__dom_codom in xnotinAE.
    rewrite asubst_atoms__dom_codom in ynotinAE.
    simpl in *.
    assert (x  `in` fv_ee e) as xine.
      clear xnotinAE ynotinAE ynx ynotine IHWfa.
      fsetdec.
    assert (y `notin` fv_ee e) as yne.
      destruct Disj as [Disj1 Disj2].
      apply Disj1. auto.
    assert (y <> x) as ynx'.
      clear xnotinAE ynotinAE ynx ynotine IHWfa.
      fsetdec.
    rewrite subst_ee_commute; auto.
    rewrite IHWfa; auto.
        rewrite asubst_atoms__dom_codom. auto.
        rewrite asubst_atoms__dom_codom. auto.

        assert (J:=@subst_ee_fv_ee_sub e x y).
        assert (y0 `notin` union (fv_ee e) (fv_ee y)) as y0notin.
           clear xnotinAE ynx IHWfa Sub xine ynx' J H H0 xine.
           destruct_notin.
           clear Disj NotInTac0 NotInTac1 NotInTac2 NotInTac3.
           simpl. fsetdec.
        clear xnotinAE ynx IHWfa Sub xine ynx' H H0 yne ynotinAE.
        fsetdec.

        assert (J:=@subst_ee_fv_ee_in e x y xine).
        rewrite J. clear J.
        rewrite asubst_atoms__dom_codom in H.
        rewrite asubst_atoms__dom_codom in H0.
        assert (dom AE [=] AtomSetImpl.diff (union {{x}} (dom AE)) {{x}}) as EQ.
          clear ynotinAE xnotinAE ynx IHWfa Sub xine ynx' H0 yne yne ynotine.
          destruct_notin. clear Disj.
          fsetdec.
        assert (dom AE [<=] AtomSetImpl.diff (fv_ee e) {{x}}) as Sub'.
          rewrite EQ. 
          clear ynotinAE xnotinAE ynx IHWfa EQ xine ynx' H yne yne ynotine H.
          fsetdec.
        clear ynotinAE xnotinAE ynx IHWfa EQ xine ynx' H yne yne ynotine H0.
        fsetdec.

        assert (J:=@subst_ee_fv_ee_in e x y xine).
        rewrite asubst_atoms__dom_codom in H.
        rewrite asubst_atoms__dom_codom in H0.
        apply disjdom_sym_1.
        apply disjdom_eq with (D1:=union (AtomSetImpl.diff (fv_ee e) {{x}}) (fv_ee y)); auto.
          destruct Disj as [Disj1 Disj2].
          split; intros.
            destruct (x1==y); subst.
              clear ynotinAE xnotinAE ynx IHWfa xine ynx' H yne ynotine.
              auto.

              assert (x1 `in` fv_ee e) as x1in. 
                clear ynotinAE xnotinAE ynx IHWfa xine ynx' H0 yne ynotine J H Sub Disj1 Disj2.
                simpl in H1. fsetdec.
              apply Disj2 in x1in. auto. 

            destruct (x1==y); subst.
              clear ynotinAE xnotinAE ynx IHWfa xine ynx' H yne ynotine.
              auto.

              assert (x1 `in` union {{y}} (atom_subst_codom AE)) as x1in. auto.
              apply Disj1 in x1in.
              clear ynotinAE xnotinAE ynx IHWfa xine ynx' H0 yne ynotine. 
              simpl. auto.            

          rewrite J. clear ynotinAE xnotinAE ynx IHWfa Sub xine ynx' H yne ynotine. fsetdec.
Qed.

Lemma subst_atoms_exp_disjdom : forall AE e,
  wf_atom_subst AE ->
  dom AE [<=] fv_ee e ->
  disjdom (atom_subst_codom AE) (fv_ee e) ->
  disjdom (dom AE) (fv_ee (subst_atoms_exp AE e)).
Proof.
  intros AE e Wfa Sub Disj.
  generalize dependent e.
  induction Wfa; intros.
  simpl. auto.

  simpl. 
  assert (dom AE [<=] fv_ee e) as Sub'.
    simpl in Sub. fsetdec.
  assert (disjdom (atom_subst_codom AE) (fv_ee e)) as Disj'.
    destruct Disj as [Disj1 Disj2].
    rewrite asubst_atoms__dom_codom in H0.
    rewrite asubst_atoms__dom_codom in H.
    split; intros.
      assert (x0 <> y) as x0ny.        
        fsetdec.
      assert (x0 `in` atom_subst_codom ([(x,y)]++AE)) as J. simpl. auto. 
      apply Disj1 in J. 
      simpl_env in J. simpl_env. auto.

      destruct (x0 == y); subst.
        fsetdec.
  
        apply Disj2 in H1. simpl in H1. auto.
   assert (J:=Sub').
   apply IHWfa in J; auto.
   assert (x `in` fv_ee e) as JJ.
     simpl in Sub. fsetdec.
   apply subst_ee_in_inv with (y:=y) in JJ; eauto.
   rewrite asubst_atoms__dom_codom in H0.
   rewrite asubst_atoms__dom_codom in H.
   destruct J as [J1 J2].
   assert (x `notin` fv_ee (subst_atoms_exp AE (subst_ee x y e))) as xnoin.
     assert (fv_ee (subst_atoms_exp AE (subst_ee x y e)) [<=] fv_ee (subst_ee x y e) `union` atom_subst_codom AE) as Sub''.
       apply subst_atoms_exp__dom_upper; auto.
         destruct Disj' as [Disj1 Disj2].
         split; intros.
           destruct (x0 == y); subst.
             clear H Disj1 Disj2 J1 J2 JJ. contradict H1; auto.

             rewrite JJ.  apply Disj1 in H1.
             clear H Disj1 Disj2 J1 J2 JJ. auto.

           destruct (x0 == y); subst; auto.
             apply Disj2. rewrite JJ in H1.
            clear H Disj1 Disj2 J1 J2 JJ Disj Sub' Sub. fsetdec.
     assert (x `notin` fv_ee (subst_ee x y e) `union` atom_subst_codom AE) as xnotin'.          
       rewrite JJ.
       clear JJ Sub Disj Disj' Sub' Sub'' IHWfa J1 J2. fsetdec.
     clear JJ Sub Disj Disj' Sub' IHWfa J1 J2. fsetdec.
   split; intros.
     destruct (x0 == x); subst.
       simpl_env. clear Sub Disj Disj' Sub' IHWfa J1 J2 H1 H. fsetdec.

       assert (x0 `in` dom AE) as x0inAE.
         clear Sub Disj Disj' Sub' IHWfa J1 J2 H. fsetdec.
       assert (x0 <> y) as x0ny.
         clear Sub Disj Disj' Sub' IHWfa J1 J2 H. fsetdec.
       apply J1 in x0inAE.
       rewrite subst_atoms_exp_swap; auto.
         assert (K:=@subst_ee_fv_ee_sub (subst_atoms_exp AE e) x y).        
         clear Sub Disj Disj' Sub' IHWfa J1 J2 H1 H JJ H0. simpl in K.  fsetdec. 

         rewrite asubst_atoms__dom_codom. auto.
         rewrite asubst_atoms__dom_codom. auto.
          
         destruct Disj as [K1 K2].
         apply K1.  simpl. auto.

     destruct (x0 == x); subst.
       destruct (x == y); subst.
          clear Sub Disj Disj' Sub' IHWfa J1 J2.
          destruct_notin. contradict NotInTac; auto.

          rewrite subst_atoms_exp_swap in H1; auto.
          rewrite subst_atoms_exp_swap in xnoin; auto.
            rewrite asubst_atoms__dom_codom. auto.
            rewrite asubst_atoms__dom_codom. auto.
          
            destruct Disj as [K1 K2].
            apply K1.  simpl. auto.
       destruct (x0 == y); subst.
          clear Sub Disj Disj' Sub' IHWfa J1 J2 H H1.
          fsetdec.     

          assert (x `notin` atom_subst_atoms AE) as xnotin1.
             rewrite asubst_atoms__dom_codom. auto.
          assert (y `notin` atom_subst_atoms AE) as ynotin1.
             rewrite asubst_atoms__dom_codom. auto.
          assert (y `notin` fv_ee e) as yne.
            destruct Disj as [K1 K2].
            apply K1.  simpl. auto.
          rewrite subst_atoms_exp_swap in H1; auto.
          rewrite subst_atoms_exp_swap in xnoin; auto.
          assert (K:=@subst_ee_fv_ee_sub (subst_atoms_exp AE e) x y).       
          simpl in K.
          assert (x0 `in` union (fv_ee (subst_atoms_exp AE e)) {{y}}) as x0in.
            clear Sub Disj Disj' Sub' IHWfa J1 J2 H H0. fsetdec.
          assert (x0 `in` fv_ee (subst_atoms_exp AE e)) as x0in'.
            clear Sub Disj Disj' Sub' IHWfa J1 J2 H H0 K xnotin1 ynotin1 yne.
            fsetdec.
          apply J2 in x0in'.
          clear Sub Disj Disj' Sub' IHWfa J1 J2 H H0.
          clear n0 JJ H1 JJ K xnotin1 ynotin1 yne.
          fsetdec.
Qed.           

Lemma id_rev_subst_atoms_exp : forall asubst e,
  wf_atom_subst asubst ->
  dom asubst [<=] (fv_ee e) ->
  disjdom (atom_subst_codom asubst) (fv_ee e) ->
  e = (rev_subst_atoms_exp asubst (subst_atoms_exp asubst e)).
Proof.
  intros asubst e Wfa Sub Disj.
  generalize dependent e.
  induction Wfa; intros; simpl; auto.
  rewrite rev_subst_atoms_exp_swap; auto.
    rewrite <- IHWfa.
      apply id_rev_subst_atom_exp; auto.
        simpl in Sub. fsetdec.

        destruct Disj as [Disj1 Disj2].
        apply Disj1. simpl. auto.

      assert (x `in` fv_ee e) as J.
        simpl in Sub. fsetdec.
      apply subst_ee_in_inv with (y:=y) in J; eauto.
      rewrite asubst_atoms__dom_codom in H.
      rewrite asubst_atoms__dom_codom in H0.
      assert (dom AE [=] AtomSetImpl.diff (dom ([(x,y)]++AE)) {{x}}) as EQ'.
        simpl. clear J Sub H0. fsetdec.
      assert (dom AE [<=] AtomSetImpl.diff (fv_ee e) {{x}}) as Sub'.
        rewrite EQ'. clear EQ'.
        clear J H0. fsetdec.
      assert (AtomSetImpl.diff (fv_ee e) {{x}} [<=] union (AtomSetImpl.diff (fv_ee e) {{x}}) {{y}}) as Sub''.
        clear J EQ' Sub Sub' H0. fsetdec.
      clear EQ'. 
      rewrite J. clear J. 
      clear Disj IHWfa Sub. fsetdec.

      assert (x `in` fv_ee e) as J.
        simpl in Sub. fsetdec.
      assert (JJ:=J).
      apply subst_ee_in_inv with (y:=y) in J; eauto.
      rewrite asubst_atoms__dom_codom in H.
      rewrite asubst_atoms__dom_codom in H0.
      destruct Disj as [Disj1 Disj2].
      split; intros.
        assert (x0 <> y) as x0ny.        
          fsetdec.
        assert (x0 `in` atom_subst_codom ([(x,y)]++AE)) as J'. simpl. auto. 
        apply Disj1 in J'.
        rewrite J. clear JJ H1 J Sub H H0. fsetdec. 

        destruct (x0 == y); subst.
          fsetdec.
  
          assert (x0 `in` fv_ee e) as IN.
            rewrite J in H1. clear J.
            clear JJ H Sub H0. fsetdec. 
          apply Disj2 in IN. simpl in  IN. auto.

     assert (x `in` fv_ee e) as J.
       simpl in Sub. fsetdec.
     apply subst_ee_in_inv with (y:=y) in J; eauto.
     rewrite asubst_atoms__dom_codom in H.
     rewrite asubst_atoms__dom_codom in H0.
     assert (fv_ee (subst_atoms_exp AE (subst_ee x y e)) [<=] fv_ee (subst_ee x y e) `union` atom_subst_codom AE) as Sub'.
       apply subst_atoms_exp__dom_upper; auto.

        destruct Disj as [Disj1 Disj2].
        split; intros.
          assert (x0 <> y) as x0ny.        
            fsetdec.
          assert (x0 `in` atom_subst_codom ([(x,y)]++AE)) as J'. simpl. auto. 
          apply Disj1 in J'.
          rewrite J. clear H1 J Sub H H0. fsetdec. 

          destruct (x0 == y); subst.
            fsetdec.
   
            assert (x0 `in` fv_ee e) as IN.
              rewrite J in H1. clear J.
              clear H Sub H0. fsetdec. 
            apply Disj2 in IN. simpl in  IN. auto.
     assert (x `notin` fv_ee (subst_ee x y e) `union` atom_subst_codom AE) as xnotin.
       rewrite J. clear J Sub Disj Sub Disj J Sub'.
       destruct_notin. clear H H0 NotInTac0 IHWfa. fsetdec. 
     clear J Sub Disj Sub Disj J H H0. fsetdec.

     assert (x `in` fv_ee e) as J.
       simpl in Sub. fsetdec.
     apply subst_ee_in_inv with (y:=y) in J; eauto.
     rewrite asubst_atoms__dom_codom in H.
     rewrite asubst_atoms__dom_codom in H0.
     apply subst_atoms_exp__dom_lower; auto.
       rewrite J. clear J.
       assert (dom AE [=] AtomSetImpl.diff (dom ([(x,y)]++AE)) {{x}}) as EQ'.
         simpl. clear Sub H0. fsetdec.
       assert (dom AE [<=] AtomSetImpl.diff (fv_ee e) {{x}}) as Sub'.
         rewrite EQ'. clear EQ'.
         clear H0. fsetdec.
       assert (AtomSetImpl.diff (fv_ee e) {{x}} [<=] union (AtomSetImpl.diff (fv_ee e) {{x}}) {{y}}) as Sub''.
         clear EQ' Sub Sub' H0. fsetdec.
       clear EQ' Disj IHWfa Sub H H0. fsetdec.

        destruct Disj as [Disj1 Disj2].
        split; intros.
          assert (x0 <> y) as x0ny.        
            fsetdec.
          assert (x0 `in` atom_subst_codom ([(x,y)]++AE)) as J'. simpl. auto. 
          apply Disj1 in J'.
          rewrite J. clear H1 J Sub H H0. fsetdec. 

          destruct (x0 == y); subst.
            fsetdec.
   
            assert (x0 `in` fv_ee e) as IN.
              rewrite J in H1. clear J.
              clear H Sub H0. fsetdec. 
            apply Disj2 in IN. simpl in  IN. auto.
     assert (x `in` fv_ee e) as J.
       simpl in Sub. fsetdec.
     apply subst_ee_in_inv with (y:=y) in J; eauto.
     rewrite asubst_atoms__dom_codom in H.
     rewrite asubst_atoms__dom_codom in H0.
    apply subst_atoms_exp_disjdom; auto.
       rewrite J. clear J.
       assert (dom AE [=] AtomSetImpl.diff (dom ([(x,y)]++AE)) {{x}}) as EQ'.
         simpl. clear Sub H0. fsetdec.
       assert (dom AE [<=] AtomSetImpl.diff (fv_ee e) {{x}}) as Sub'.
         rewrite EQ'. clear EQ'.
         clear H0. fsetdec.
       assert (AtomSetImpl.diff (fv_ee e) {{x}} [<=] union (AtomSetImpl.diff (fv_ee e) {{x}}) {{y}}) as Sub''.
         clear EQ' Sub Sub' H0. fsetdec.
       clear EQ' Disj IHWfa Sub H H0. fsetdec.

        destruct Disj as [Disj1 Disj2].
        split; intros.
          assert (x0 <> y) as x0ny.        
            fsetdec.
          assert (x0 `in` atom_subst_codom ([(x,y)]++AE)) as J'. simpl. auto. 
          apply Disj1 in J'.
          rewrite J. clear H1 J Sub H H0. fsetdec. 

          destruct (x0 == y); subst.
            fsetdec.
   
            assert (x0 `in` fv_ee e) as IN.
              rewrite J in H1. clear J.
              clear H Sub H0. fsetdec. 
            apply Disj2 in IN. simpl in  IN. auto.
Qed.

Lemma subst_atoms_lenv__dom_eq : forall asubst lEnv,
  wf_atom_subst asubst ->
  uniq lEnv ->
  dom lEnv [=] dom asubst ->
  dom (subst_atoms_lenv asubst lEnv) [=] atom_subst_codom asubst.
Proof.
  intros asubst lEnv Wfa Uniq Deq.
  generalize dependent lEnv.
  induction Wfa; intros.
    simpl in Deq.
    apply empty_dom__empty_ctx in Deq. subst. simpl. auto.

    assert (x `in` dom lEnv) as xbinds. 
      rewrite Deq. simpl. auto.
    apply binds_In_inv in xbinds. 
    destruct xbinds as [a xbinds].
    apply subst_atoms_lenv_inv with (y:=y)(asubst:=([(x, y)]++AE)) in xbinds; auto.
    destruct xbinds as [lE1 [lE2 [EQ1 EQ2]]]; subst.
    rewrite EQ2.
    rewrite asubst_atoms__dom_codom in H.
    rewrite asubst_atoms__dom_codom in H0.
    assert (x `notin` dom lE1) as xnotinlE1.
      apply fresh_mid_head in Uniq; auto.
    assert (x `notin` dom lE2) as xnotinlE2.
      apply fresh_mid_tail in Uniq; auto.
    simpl_env in Deq. simpl_env.            
    assert (AtomSetImpl.diff (union {{x}} (dom AE)) {{x}}[=] dom AE) as EQ. 
      clear Deq. fsetdec.
    assert (AtomSetImpl.diff (union (dom lE1) (union {{x}} (dom lE2))) {{x}}[=] union (dom lE1) (dom lE2)) as EQ'. 
      clear Deq EQ. fsetdec.
    assert (dom (lE1++lE2) [=] dom (AE)) as EQ''.
      simpl. simpl_env.
      rewrite <- EQ. clear EQ. 
      rewrite <- EQ'. clear EQ'. 
      clear H xnotinlE1 xnotinlE2. 
      clear H0 IHWfa Uniq EQ2.
      fsetdec.
    apply IHWfa in EQ''.
      simpl. rewrite <- EQ''.
      rewrite subst_atoms_lenv_app.
      apply subst_atom_lenv_notin_inv with (y:=y) in xnotinlE1.
      apply subst_atom_lenv_notin_inv with (y:=y) in xnotinlE2.
      rewrite <- xnotinlE1. rewrite <- xnotinlE2.
      clear EQ EQ' EQ'' xnotinlE1 xnotinlE2 EQ2 Deq H H0 IHWfa.
      simpl_env. fsetdec.

      clear EQ EQ' EQ'' xnotinlE1 xnotinlE2 EQ2 Deq H H0 IHWfa.
      solve_uniq.
Qed.

Lemma rev_subst_atoms_lenv_notin_inv : forall asubst lE,
  wf_atom_subst asubst ->
  disjdom (atom_subst_codom asubst) (dom lE) -> 
  lE = rev_subst_atoms_lenv asubst lE.
Proof.
  intros asubst lE Wfa.
  induction Wfa; intros.
    simpl. auto.
 
    simpl.
    rewrite <- subst_atom_lenv_notin_inv.
      rewrite <- IHWfa. 
        auto.
        
        destruct H1 as [H11 H12].
        split; intros.
           apply H11. simpl. fsetdec.
           apply H12 in H1. simpl in H1. auto.

      destruct H1 as [H11 H12].
      apply H11. simpl. fsetdec.
Qed.

Lemma rev_subst_atoms_lenv_app : forall asubst lE1 lE2,
  rev_subst_atoms_lenv asubst (lE1++lE2) =
    rev_subst_atoms_lenv asubst lE1 ++ rev_subst_atoms_lenv asubst lE2.
Proof.
  induction asubst; intros; simpl; auto.
    destruct a. 
    rewrite subst_atom_lenv_app; auto.
Qed.      

Lemma expr_renaming: forall e1 asubst,
  expr e1 ->
  expr (rev_subst_atoms_exp asubst e1).
Proof.
  intros e1 asubst Expr.
  generalize dependent e1.
  induction asubst; intros; simpl; auto.
    destruct a.
    apply IHasubst.
    apply subst_ee_expr; auto.
Qed.  

Lemma red_renaming : forall e e' (x y:atom),
  red e e' ->
  red (subst_ee x y e) (subst_ee x y e').  
Proof.
  intros e e' x y Red.
  generalize dependent x.
  generalize dependent y.
  induction Red; intros; simpl; eauto.
    apply subst_ee_expr with (z:=x) (e2:=y) in H; auto.
    rewrite subst_ee_open_ee; auto.

    apply subst_ee_expr with (z:=x) (e2:=y) in H; auto.
    rewrite subst_ee_open_te; auto.

    apply subst_ee_expr with (z:=x) (e2:=y) in H; auto.

    apply subst_ee_expr with (z:=x) (e2:=y) in H; auto.
    rewrite subst_ee_open_ee; auto.
Qed.

Lemma red_rev_renamings : forall e e' asubst,
  red e e' ->
  red (rev_subst_atoms_exp asubst e) (rev_subst_atoms_exp asubst e').  
Proof.
  intros e e' asubst Red.
  generalize dependent e.
  generalize dependent e'.
  induction asubst; intros; simpl; auto.
    destruct a.
    apply IHasubst.
      apply red_renaming; try solve [assumption].
Qed.

Lemma bigstep_red_rev_renamings : forall e e' asubst,
  bigstep_red e e' ->
  bigstep_red (rev_subst_atoms_exp asubst e) (rev_subst_atoms_exp asubst e').  
Proof.
  intros e e' asubst Red.
  generalize dependent asubst.
  induction Red; intros; auto.
    apply bigstep_red_trans with (e':=rev_subst_atoms_exp asubst e'); eauto using red_rev_renamings.
Qed.  

Lemma value_rev_renamings: forall e1 asubst,
  value e1 ->
  value (rev_subst_atoms_exp asubst e1).
Proof.
  intros e1 asubst Val.
  generalize dependent e1.
  induction asubst; intros; simpl; auto.
    destruct a.
    apply IHasubst.
    apply value_through_subst_ee with (x:=a0) (u:=a) in Val; auto.
Qed.  

Lemma normalize_rev_renamings : forall e v asubst,
  normalize e v ->
  normalize (rev_subst_atoms_exp asubst e) (rev_subst_atoms_exp asubst v).  
Proof.
  intros e v asubst norm.
  unfold normalize in *.
  destruct norm.
  apply bigstep_red_rev_renamings with (asubst:=asubst) in b; auto.
  apply value_rev_renamings with (asubst:=asubst) in v0; auto.
Qed.

Lemma rev_subst_atoms_exp__app : forall asubst e1 e2,
  rev_subst_atoms_exp asubst (exp_app e1 e2) = 
    exp_app (rev_subst_atoms_exp asubst e1) (rev_subst_atoms_exp asubst e2).
Proof.
  induction asubst; intros.
    simpl. auto.
    destruct a. simpl. apply IHasubst.
Qed.

Lemma rev_wf_asubst_id : forall asubst e,
  wf_atom_subst asubst ->
  disjdom (atom_subst_codom asubst) (fv_ee e) ->
  e = (rev_subst_atoms_exp asubst e).
Proof.
  intros asubst e Wfa Disj.
  generalize dependent e.
  induction Wfa; intros.
    simpl. auto.
    simpl. rewrite <- subst_ee_fresh with (e:=e); auto.
      apply IHWfa.
        destruct Disj as [J1 J2].
        split; intros.
          apply J1. simpl. auto.
          apply J2 in H1. simpl in H1. auto.
      destruct Disj as [J1 J2].  
      apply J1. simpl. auto. 
Qed.

Lemma red_renamings : forall e e' asubst,
  red e e' ->
  red (subst_atoms_exp asubst e) (subst_atoms_exp asubst e').  
Proof.
  intros e e' asubst Red.
  generalize dependent e.
  generalize dependent e'.
  induction asubst; intros; simpl; auto.
    destruct a.
    apply IHasubst.
      apply red_renaming; try solve [assumption].
Qed.

Lemma bigstep_red_renamings : forall e e' asubst,
  bigstep_red e e' ->
  bigstep_red (subst_atoms_exp asubst e) (subst_atoms_exp asubst e').  
Proof.
  intros e e' asubst Red.
  generalize dependent asubst.
  induction Red; intros; auto.
    apply bigstep_red_trans with (e':=subst_atoms_exp asubst e'); eauto using red_renamings.
Qed.  

Lemma value_renamings: forall e1 asubst,
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

Lemma normalize_renamings : forall e v asubst,
  normalize e v ->
  normalize (subst_atoms_exp asubst e) (subst_atoms_exp asubst v).  
Proof.
  intros e v asubst norm.
  unfold normalize in *.
  destruct norm.
  apply bigstep_red_renamings with (asubst:=asubst) in b; auto.
  apply value_renamings with (asubst:=asubst) in v0; auto.
Qed.