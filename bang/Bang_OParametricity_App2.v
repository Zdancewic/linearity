(** Authors: Jianzhou Zhao. *)

Require Export Metatheory.
Require Import Bang_Definitions.
Require Import Bang_Infrastructure.
Require Import Bang_Lemmas.
Require Import Bang_Soundness.
Require Import Bang_OParametricity.
Require Import Bang_Renaming.
Require Import Bang_OParametricity_App.
Require Import Bang_ContextualEq_Def.
Require Import Bang_ContextualEq_Infrastructure.

Export OParametricity.

(***************************************************************)
(** *                           Relations                      *)
(***************************************************************)

Definition Req Env lEnv (v0:exp) (A:typ) (v v':exp) : Prop := 
  exists asubst,
    disjdom (dom asubst) (dom Env) /\
    beta_eta_eq Env (subst_atoms_lenv asubst lEnv) v (subst_atoms_exp asubst v0) A /\ 
    beta_eta_eq Env (subst_atoms_lenv asubst lEnv) v' (subst_atoms_exp asubst v0) A.

Lemma unfold_subst_atoms_exp : forall asubst x y e,
  subst_atoms_exp (asubst++[(x,y)]) e =
    subst_ee x y (subst_atoms_exp asubst e).
Proof.
  induction asubst; intros; simpl; auto.
  destruct a. rewrite IHasubst. auto.
Qed.

Lemma unfold_subst_atoms_lenv : forall asubst x y lE,
  subst_atoms_lenv (asubst++[(x,y)]) lE =
    subst_atom_lenv (subst_atoms_lenv asubst lE) x y.
Proof.
  induction asubst; intros; simpl; auto.
  destruct a. rewrite IHasubst. auto.
Qed.

Lemma Req_admissible : forall Env lEnv v0 A,
  admissible Env (Req Env lEnv v0 A).
Proof.
  intros Env lEnv v0 A.
  intros v v' R x y Frx Frx' Fry.
    destruct (x==y); subst.
      rewrite subst_ee_id. rewrite subst_ee_id. auto.

    destruct R as [asubst [Hdisj [Hbee Hbee']]]. 
    exists (asubst++[(x,y)]).
    assert (x `notin` dom Env) as xnEnv.
      apply bee_ldom in Hbee.
      destruct Hbee.
      rewrite H in Frx.
      apply bee_disjoint in Hbee'.
      clear - Hbee' Frx. solve_uniq.
    assert (y `notin` dom Env) as ynEnv.
      destruct_notin; auto.
        fsetdec.
    assert (y `notin` dom (subst_atoms_lenv asubst lEnv)) as ynlEnv.
      apply bee_ldom in Hbee.
      destruct Hbee.
      rewrite <- H.
      destruct_notin; auto.
        contradict NotInTac; auto.
    rewrite unfold_subst_atoms_lenv.
    rewrite unfold_subst_atoms_exp.
    split. apply disjdom_eq with (D1:=dom asubst `union` {{x}}).
             apply disjdom_app_3; auto.
               apply disjdom_one_2; auto.
             simpl_env. fsetdec.
    split. apply bee_lin_renaming with (x:=x) (y:=y); auto.
           apply bee_lin_renaming with (x:=x) (y:=y); auto.
Qed.

Lemma Req_wfor : forall Env lEnv v0 A,
  wf_typ Env A -> 
  wfor Env (Req Env lEnv v0 A) A A.
Proof.
  intros.
  split; auto.
  split; auto.
    apply Req_admissible.
Qed.

(***************************************************************)
(** *        Linear Identification with closed contexts        *)
(***************************************************************)

Lemma subst_atoms_exp_fresh : forall asubst e,
  fv_ee e [=] {} ->
  e = (subst_atoms_exp asubst e).
Proof.
  induction asubst; intros e Fre; simpl; auto.
    destruct a. 
    rewrite <- subst_ee_fresh with (e:=e); auto.
    rewrite Fre. auto.
Qed.

Corollary BehaveLike_LIdentificationC : forall Id A x, 
  typing nil nil Id (typ_all (typ_arrow (typ_bvar 0) (typ_bvar 0))) ->
  typing nil nil x A ->
  beta_eta_eq nil nil (exp_app (exp_tapp Id A) x) x A.
Proof.
  intros Id A x Htypingid Htypingx.
  assert (exists x0, normalize x x0) as Hn_xx0.
    apply strong_normalization with (t:=A); auto.
  destruct Hn_xx0 as [x0 [Hbrc_xx0 Hx0]]. 

  assert (wf_typ nil A) as HwftA. auto.
  destruct (@LIdentificationC Id A A Htypingid x x (Req nil nil x0 A)) as [X JJ].

  (* x and x are related as Req*)
  assert (wf_typ ((X, bind_kn)::nil) (typ_fvar X)) as WFT.
    apply wf_typ_var; unfold binds; simpl; auto.

  assert (F_Related_oterms (typ_fvar X) 
                                 ([(X,(Req nil nil x0 A))])
                                 ([(X, A)])
                                 ([(X, A)])
                                  x x nil nil).
    Case "Fterms".
    exists (x0). exists (x0).
      split; simpl.
      SCase "Typing".
      destruct (X==X); auto; contradict n; auto.
    
      split; simpl.
      SCase "Typing".
      destruct (X==X); auto; contradict n; auto.

      unfold normalize.
      split; auto.
      split; auto.
      SCase "Fvalues".
        apply F_Related_ovalues_fvar_req. simpl.
        exists(Req nil nil x0 A).
        repeat(split; auto).
           SSCase "admin". apply Req_admissible.

           exists nil. simpl.
           split. split; auto.
           split.
             apply bee_refl with (lE:=nil); auto.
             apply preservation_bigstep_red with (e':=x0) in Htypingx; auto.
     
             apply bee_refl with (lE:=nil); auto.
             apply preservation_bigstep_red with (e':=x0) in Htypingx; auto.

  (* Id[A] x and  Id[A] x are related as Req*)
  apply JJ in H; auto using Req_wfor.
  subst.
  destruct H as [v [v' [Htypingv [Htypingv' [[Hbrc Hv] [[Hbrc' Hv'] [R [Hb [_ [_ [Hadmin Hrel]]]]]]]]]]]; subst.
  unfold Rid.
  assert ((if X==X then A else typ_fvar X) = A) as HeqA.
    destruct (X==X); auto. contradict n; auto.
  simpl in *. simpl_env in *.
  rewrite HeqA in *. clear HeqA.
  analyze_binds Hb; subst.
  destruct Hrel as [asubst Hrel].
  decompose [and] Hrel. clear Hrel.
  rewrite subst_atoms_lenv_nil in *. 
  apply bee_trans with (e':=v); auto.
    apply bee_red with (lE:=nil); auto.

   apply bee_trans with (e':=x0); auto.
      rewrite <- subst_atoms_exp_fresh in H1; auto.
      apply preservation_bigstep_red with (e':=x0) in Htypingx; auto.
      apply typing_fv_ee_upper in Htypingx. 
      clear - Htypingx. fsetdec.

      apply bee_sym.
      apply bee_red with (lE:=nil); auto.
Qed.

(***************************************************************)
(** *    Linear Identification with open contexts              *)
(***************************************************************)

Lemma typing_linctx_domeq' : forall E E' lE lE' e t t',
  typing E lE e t ->
  typing E' lE' e t' ->
  gdom_env E [=] gdom_env E' ->
  dom lE [=] dom lE'.
Proof.
  intros.
  apply typing_ldom in H.
  apply typing_ldom in H0.
  rewrite <- H. rewrite <- H0.
  fsetdec.
Qed.

Lemma subst_atom_lenv_cons : forall lE x b m n,
  exists y, 
    subst_atom_lenv ([(x,b)]++lE) m n =
      [(y,b)]++subst_atom_lenv lE m n.
Proof.
  intros.
  simpl. 
  destruct (m==x); subst.
    exists n. auto.
    exists x. auto.
Qed.

Lemma subst_atom_lenv_singleton : forall asubst x b,
  exists y, 
    subst_atoms_lenv asubst ([(x,b)]) = [(y, b)].
Proof.
  induction asubst; intros; simpl.
    exists x. auto.

    destruct a.
    destruct (a==x); subst; simpl_env; auto.
Qed.

Lemma subst_atoms_lenv_singleton : forall asubst x b lE,
  exists y, 
    subst_atoms_lenv asubst ([(x,b)]++lE) =
      [(y,b)]++subst_atoms_lenv asubst lE.
Proof.
  induction asubst; intros; simpl.
    exists x. auto.

    destruct a.
    destruct (a==x); subst; simpl_env.
      rewrite subst_atoms_lenv_app.
      destruct (@subst_atom_lenv_singleton asubst a0 b) as [y H].
      rewrite H. exists y. auto.

      rewrite subst_atoms_lenv_app.
      destruct (@subst_atom_lenv_singleton asubst x b) as [y H].
      rewrite H. exists y. auto.
Qed.   

Corollary BehaveLike_LIdentification : forall Id A x0 E lE, 
  typing nil nil Id (typ_all (typ_arrow (typ_bvar 0) (typ_bvar 0))) ->
  typing E lE x0 A ->
  value x0 ->
  exists asubst, beta_eta_eq E lE (exp_app (exp_tapp Id A) x0) (subst_atoms_exp asubst x0) A.
Proof.
  intros Id A x0 E lE Htypingid Typingx0 Hvx0.
  destruct (@LIdentification Id A A E lE x0 x0 (Req E lE x0 A) Htypingid) as [X JJ]; auto using Req_wfor.
  
  assert (wf_typ ((X, bind_kn)::nil) (typ_fvar X)) as WFT.
    apply wf_typ_var.
       unfold binds. simpl. auto. 
       simpl_env. apply binds_one_3; auto.

  assert (F_Related_oterms (typ_fvar X) 
                                 ([(X,(Req E lE x0 A))])
                                 ([(X, A)])
                                 ([(X, A)])
                                  x0 x0 E lE).
    exists x0. exists x0. simpl.
    destruct (X==X); try solve [contradict n; auto].
    repeat(split; auto).
      apply F_Related_ovalues_fvar_req. simpl.
      exists(Req E lE x0 A).
      repeat(split; auto).
        apply Req_admissible.
        exists nil. simpl.
        split. apply disjdom_nil_1.
        split.
          apply bee_refl with (lE:=lE); auto.
            apply typing_uniqlE in Typingx0; auto.
            fsetdec.
          apply bee_refl with (lE:=lE); auto.
            apply typing_uniqlE in Typingx0; auto.
            fsetdec.

  apply JJ in H; auto using Req_wfor. subst.
  destruct H as [v [v' [Htypingv [Htypingv' [[Hbrc Hv] [[Hbrc' Hv'] [R [Hb [_ [_ [Hadmin Hrel]]]]]]]]]]]; subst.
  assert ((if X==X then A else typ_fvar X) = A) as HeqA.
    destruct (X==X); auto. contradict n; auto.
  simpl in *. simpl_env in *.
  rewrite HeqA in *. clear HeqA.
  analyze_binds Hb; subst.
  destruct Hrel as [asubst Hrel].
  decompose [and] Hrel. clear Hrel.
  exists asubst.
  apply bee_trans with (e':=v); auto.
    apply bee_red with (lE:=lE); auto.
      apply typing_regular in Typingx0.
      decompose [and] Typingx0. apply uniq_from_wf_lenv in H4; auto.
      fsetdec.
    apply bee_domeq with (lE:=subst_atoms_lenv asubst lE); auto.
      apply preservation_bigstep_red with (e':=v) in Htypingv; auto.
      apply typing_ldom in Htypingv.
      rewrite <- Htypingv.
      apply bee_ldom in H1.
      destruct H1 as [J1 J2].
      rewrite <- J1. fsetdec.

      apply typing_uniqlE in Typingx0; auto.
Qed.

(***************************************************************)
(** *        Intuitionistic Identification                     *)
(***************************************************************)

Lemma subst_atom_asubst_exp_id : forall asubst e,
  disjdom (dom asubst) (fv_ee e) ->
  e = (subst_atoms_exp asubst e).
Proof.
  induction asubst; intros e Disj; simpl; auto.
    destruct a.
    simpl in Disj.
    apply disjdom_cons_l in Disj.
    destruct Disj as [J1 J2].
    rewrite <- subst_ee_fresh with (e:=e); auto.
Qed.

Corollary BehaveLike_IIdentification2 : forall Id A x0 E, 
  typing nil nil Id (typ_all (typ_arrow (typ_bang (typ_bvar 0)) (typ_bvar 0))) ->
  typing E lempty x0 A ->
  value x0 ->
  beta_eta_eq E lempty (exp_app (exp_tapp Id A) (exp_bang x0)) x0 A.
Proof.
  intros Id A x0 E Htypingid Typingx0 Hvx0.
  destruct (@IIdentification Id A A E x0 x0 (Req E nil x0 A) Htypingid) as [X JJ]; auto using Req_wfor.
  
  assert (wf_typ ((X, bind_kn)::nil) (typ_fvar X)) as WFT.
    apply wf_typ_var.
       unfold binds. simpl. auto. 
       simpl_env. apply binds_one_3; auto.

  assert (F_Related_oterms (typ_fvar X) 
                                 ([(X,(Req E nil x0 A))])
                                 ([(X, A)])
                                 ([(X, A)])
                                  x0 x0 E lempty).
    exists x0. exists x0. simpl.
    destruct (X==X); try solve [contradict n; auto].
    repeat(split; auto).
      apply F_Related_ovalues_fvar_req. simpl.
      exists(Req E nil x0 A).
      repeat(split; auto).
        apply Req_admissible.
        exists nil. simpl.
        split. apply disjdom_nil_1.
        split.
          apply bee_refl with (lE:=nil); auto.
          apply bee_refl with (lE:=nil); auto.

  apply JJ in H; auto using Req_wfor. subst.
  destruct H as [v [v' [Htypingv [Htypingv' [[Hbrc Hv] [[Hbrc' Hv'] [R [Hb [_ [_ [Hadmin Hrel]]]]]]]]]]]; subst.
  assert ((if X==X then A else typ_fvar X) = A) as HeqA.
    destruct (X==X); auto. contradict n; auto.
  simpl in *. simpl_env in *.
  rewrite HeqA in *. clear HeqA.
  analyze_binds Hb; subst.
  destruct Hrel as [asubst Hrel].
  decompose [and] Hrel. clear Hrel.
  rewrite subst_atoms_lenv_nil in *. 
  apply bee_trans with (e':=v); auto.
    apply bee_red with (lE:=nil); auto.

    rewrite <- subst_atom_asubst_exp_id in H1; auto.
    apply typing_fv_ee_upper in Typingx0.   
    clear - Typingx0 H.
    apply disjdom_sub with (D1:=dom E `union` {}); auto.
      apply disjdom_sym_1.
      apply disjdom_app_3.
        apply disjdom_sym_1; auto.
        apply disjdom_nil_1.
Qed.

(***************************************************************)
(** *                Linear Nat                                *)
(***************************************************************)

(*
The free thm is that 
  if .;.|-M:\/a. (a -o a) -o a -o a, then
  forall R in T<->T'-| G,
  forall (z, z') in a, 
  forall (s, s') in a -o a,
    (Msz, Ms'z') in a
    where a->R

Consider
  G;Dz|-z:T, G;Ds|-s:T-oT, Dz and Ds are disjoint
Let R = {(e, e') |
           ex n, ex </ sub_i /0-n/>,
           G;sub_0 Dz|- sub_0 z:T /\
           </ G;sub_i Ds|- sub_i s:T-oT /1-n/> /\
           G;</sub_i Ds/1-n/>,sub_0 Dz|-</sub_i s/1-n/> (sub_0 z)=e=e':T
        }

When n=0, sub_0=nil, we have
  G;Dz|-z:T
  G;Dz|-z=z=z:T
so (z,z) in R

Now suppose (v, v') in R, with 
  G;Dv|-v:T and Dv and Ds are disjoint.
then there are n and </ sub_i /0-n/>, s.t.
H1:  G;sub_0 Dz|- sub_0 z:T 
H2:  </ G;sub_i Ds|- sub_i s:T-oT /1-n/> 
H3:  G;</sub_i Ds/1-n/>,sub_0 Dz|-</sub_i s/1-n/> (sub_0 z)=v=v':T
From H3, dom(</sub_i Ds/1-n/>,sub_0 Dz)=dom Dv,
So Ds is also disjoint with </sub_i Ds/1-n/>,sub_0 Dz.
Pick sub_{n+1} be nil, we have
  G;Ds|-s:T-oT and
  G;Ds, </sub_i Ds/1-n/>,sub_0 Dz|-s (</sub_i s/1-n/> (sub_0 z))=sv=sv':T
Therefore,
  (sv, sv') in R,
So (s, s) in R

By the free thm, there are n and </ sub_i /0-n/>, s.t.
H1:  G;sub_0 Dz|- sub_0 z:T 
H2:  </ G;sub_i Ds|- sub_i s:T-oT /1-n/> 
H3:  G;</sub_i Ds/1-n/>,sub_0 Dz|-</sub_i s/1-n/> (sub_0 z)=Msz:T
We also have len(sub D)=len D, 
From H3,  n*len Ds + len Dz=len Ds + len Dz
In the case Ds are nonempty, n=1.  
*)

Fixpoint lEnv_from_list_subs lE (l:list atom_subst) : lenv :=
match l with
| nil => nil
| asub::l' => (subst_atoms_lenv asub lE)++(lEnv_from_list_subs lE l')
end.

Fixpoint typing_from_list_subst E lE e t (l:list atom_subst) : Prop :=
match l with
| nil => True
| asub::l' => (typing_from_list_subst E lE e t l') /\
              disjdom (dom asub) (dom E) /\
              (*wf_asubst asub /\*)
              typing E (subst_atoms_lenv asub lE) (subst_atoms_exp asub e) t
end.

Fixpoint nats_from_list_subs s z (ls:list atom_subst) lz : exp :=
match ls with
| nil => (subst_atoms_exp lz z)
| asub::ls' => exp_app (subst_atoms_exp asub s) (nats_from_list_subs s z ls' lz)
end.

Fixpoint lEnv_from_list lE (l:list atom_subst) : lenv :=
match l with
| nil => nil
| asub::l' => lE++(lEnv_from_list lE l')
end.

Definition Rlnat Env lEnvs lEnvz (s z:exp) (A:typ) (v v':exp) : Prop := 
  exists asubsts, exists asubstz, 
    disjdom (dom asubstz) (dom Env) /\
    typing_from_list_subst Env lEnvs s (typ_arrow A A) asubsts /\
    typing Env (subst_atoms_lenv asubstz lEnvz) (subst_atoms_exp asubstz z) A /\
    beta_eta_eq Env ((lEnv_from_list_subs lEnvs asubsts)++subst_atoms_lenv asubstz lEnvz)
                (nats_from_list_subs s z asubsts asubstz) v A /\
    beta_eta_eq Env ((lEnv_from_list_subs lEnvs asubsts)++subst_atoms_lenv asubstz lEnvz)
                (nats_from_list_subs s z asubsts asubstz) v' A.

Fixpoint cons_list_subst x y (l:list atom_subst) : (list atom_subst) :=
match l with
| nil => nil
| asub::l' => (asub++[(x,y)])::cons_list_subst x y l'
end.

Fixpoint atom_list_subst_atoms asubsts : atoms :=
match asubsts with
| nil => {}
| a::asubsts' => atom_subst_atoms a `union` atom_list_subst_atoms asubsts'
end.

Lemma notin_subst_atom_lenv : forall lE y a b,
  y `notin` dom lE ->
  y <> b ->
  y `notin` dom (subst_atom_lenv lE a b).
Proof.
  induction lE; intros; simpl; auto.
  destruct a.
  destruct (a0==a); subst; auto.
Qed.
  
Lemma notin_subst_atoms_lenv : forall asubst lE y,
  y `notin` dom lE ->
  y `notin` atom_subst_codom asubst ->
  y `notin` dom (subst_atoms_lenv asubst lE).
Proof.
  induction asubst; intros lE y ynlE ynasubst; simpl; auto.
    simpl in *. destruct a. 
    apply IHasubst; auto.
    apply notin_subst_atom_lenv; auto.
Qed.

Fixpoint atom_list_subst_codoms asubsts : atoms :=
match asubsts with
| nil => {}
| a::asubsts' => atom_subst_codom a `union` atom_list_subst_codoms asubsts'
end.

Lemma typing_from_list_subst_lin_renaming : forall asubsts Env lEnv e A x y,
  typing_from_list_subst Env lEnv e A asubsts ->
  x `notin` dom Env ->
  y `notin` dom Env ->
  y `notin` dom (lEnv_from_list_subs lEnv asubsts) ->
  typing_from_list_subst Env lEnv e A (cons_list_subst x y asubsts).
Proof.
  induction asubsts; intros Env lEnv e A x y H xnEnv ynEnv ynlEnv; simpl in *; auto.
  decompose [and] H. clear H.

  split. apply IHasubsts; auto.
  split. apply disjdom_eq with (D1:=dom a `union` {{x}}).
           apply disjdom_app_3; auto.
             apply disjdom_one_2; auto.
             simpl_env. fsetdec.

         rewrite unfold_subst_atoms_exp.
         rewrite unfold_subst_atoms_lenv.
         apply typing_lin_renaming; auto.
Qed.

Lemma nats_from_list_subs__subst : forall ls s z lz x y,
  nats_from_list_subs s z (cons_list_subst x y ls) (lz++[(x,y)]) =
  subst_ee x y (nats_from_list_subs s z ls lz).
Proof.
  induction ls; intros s z lz x y; simpl; auto.
    rewrite unfold_subst_atoms_exp. auto.

    simpl in *.
    rewrite unfold_subst_atoms_exp. 
    rewrite IHls; auto.
Qed.

Lemma lEnv_from_list_subs__cons_list_subst : forall asubsts lEnvs x y,
  subst_atom_lenv (lEnv_from_list_subs lEnvs asubsts) x y =
  (lEnv_from_list_subs lEnvs (cons_list_subst x y asubsts)).
Proof.
  induction asubsts; intros lEnvs x y; simpl; auto.
    rewrite subst_atom_lenv_app.
    simpl in *.
    rewrite IHasubsts; auto.
    rewrite unfold_subst_atoms_lenv. auto.
Qed.
  
Lemma lEnv_from_list_subs__cons_list_subst' : forall asubsts lEnvs lEnvz x y,
  x `notin` dom lEnvz ->
  subst_atom_lenv (lEnv_from_list_subs lEnvs asubsts ++ lEnvz) x y =
  (lEnv_from_list_subs lEnvs (cons_list_subst x y asubsts) ++ lEnvz).
Proof.
  intros asubsts lEnvs lEnvz x y Hxnlz.
  rewrite subst_atom_lenv_app.
  rewrite lEnv_from_list_subs__cons_list_subst; auto.
  rewrite <- subst_atom_lenv_notin_inv; auto. 
Qed.

Lemma Rlnat_admissible : forall Env lEnvs lEnvz s z A,
  admissible Env (Rlnat Env lEnvs lEnvz s z A).
Proof.
  intros Env lEnvs lEnvz s z A.
  intros v v' R x y Frx Frx' Fry.
    destruct (x==y); subst.
      rewrite subst_ee_id. rewrite subst_ee_id. auto.

    destruct R as [asubsts [asubstz [Disj_lEnvz_Env [Typings [Typingz [Bee Bee']]]]]].
    exists (cons_list_subst x y asubsts).
    exists (asubstz++[(x,y)]). simpl.
    assert (x `notin` dom Env) as xnEnv.
      apply bee_ldom in Bee.
      destruct Bee as [J1 J2].
      rewrite J2 in Frx.
      apply bee_disjoint in Bee'.
      clear - Bee' Frx. 
      destruct_uniq. simpl_env in Frx.
      solve_uniq.
    assert (y `notin` dom Env) as ynEnv.
      destruct_notin; auto.
        fsetdec.
    assert (y `notin` dom (lEnv_from_list_subs lEnvs asubsts++subst_atoms_lenv asubstz lEnvz)) as ynlEnv.
      apply bee_ldom in Bee.
      destruct Bee as [J1 J2].
      rewrite <- J2. clear J2.
      destruct_notin; auto.
        contradict NotInTac; auto.
    assert (y `notin` dom (subst_atoms_lenv asubstz lEnvz)) as ynlEnvz.
      simpl_env in *. auto.
    rewrite unfold_subst_atoms_exp. 
    rewrite unfold_subst_atoms_lenv. 
    split. apply disjdom_eq with (D1:=dom asubstz `union` {{x}}).
             apply disjdom_app_3; auto.
               apply disjdom_one_2; auto.
             simpl_env. fsetdec.
    split. apply typing_from_list_subst_lin_renaming; auto.
    split. apply typing_lin_renaming; auto.
    rewrite nats_from_list_subs__subst; auto.
    rewrite <- lEnv_from_list_subs__cons_list_subst; auto.
    split. apply bee_lin_renaming with (x:=x) (y:=y) in Bee; auto.
           rewrite subst_atom_lenv_app in Bee; auto.

           apply bee_lin_renaming with (x:=x) (y:=y) in Bee'; auto.
           rewrite subst_atom_lenv_app in Bee'; auto.
Qed.

Lemma Rlnat_wfor : forall Env lEnvs lEnvz s z A,
  wf_typ Env A -> 
  wfor Env (Rlnat Env lEnvs lEnvz s z A) A A.
Proof.
  intros.
  split; auto.
  split; auto.
    apply Rlnat_admissible.
Qed.

Lemma subst_atom_lenv_length :  forall lEnv x y,
  length (subst_atom_lenv lEnv x y) = length lEnv.
Proof.
  induction lEnv; intros; simpl; auto.
    destruct a.
    destruct (x==a); subst; simpl; auto.
Qed.

Lemma subst_atoms_lenv_length :  forall asubst lEnv,
  length (subst_atoms_lenv asubst lEnv) = length lEnv.
Proof.
  induction asubst; simpl; intros; auto.
    destruct a. rewrite IHasubst.
    apply subst_atom_lenv_length.
Qed.  

Lemma lEnv_from_list_subs_length :  forall lEnv asubsts,
  length (lEnv_from_list_subs lEnv asubsts) = 
    length asubsts * length lEnv.
Proof.
  induction asubsts; simpl; auto.
    rewrite app_length.
    rewrite IHasubsts. 
    rewrite subst_atoms_lenv_length. auto.
Qed.

Lemma lEnv_from_list_subs_nil :  forall asubsts,
  lEnv_from_list_subs nil asubsts = nil.
Proof.
  induction asubsts; simpl; auto.
    rewrite subst_atoms_lenv_nil. 
    rewrite IHasubsts. auto.
Qed.

Lemma lEnv_from_list_nil :  forall asubsts,
  lEnv_from_list nil asubsts = nil.
Proof.
  induction asubsts; simpl; auto.
Qed.

Fixpoint nats s z n : exp :=
match n with
| 0 => z
| S n' => exp_app s (nats s z n')
end.

Lemma bigstep_red_app : forall e1 e1' e2,
  bigstep_red e1 e1' ->
  expr e2 ->
  bigstep_red (exp_app e1 e2) (exp_app e1' e2).
Proof.
  intros e1 e1' e2 Hrel Expr.
  induction Hrel; auto.
    apply bigstep_red_trans with (e':=exp_app e' e2); auto.
Qed. 

Fixpoint dom_list_subst_atoms (asubsts:list atom_subst) : atoms :=
match asubsts with
| nil => {}
| a::asubsts' => dom a `union` dom_list_subst_atoms asubsts'
end.

Lemma nats_from_list_subst__nats : forall ls s z lz,
  disjdom (dom_list_subst_atoms ls) (fv_ee s) ->
  nats_from_list_subs s z ls lz = nats s (subst_atoms_exp lz z) (length ls).
Proof.
  induction ls; intros s z lz Hdisjs; simpl; auto.
    simpl in *. 
    rewrite IHls; auto.
      rewrite <- subst_atom_asubst_exp_id; auto.
      apply disjdom_app_1 in Hdisjs; auto.

      apply disjdom_app_2 in Hdisjs; auto.
Qed.

Lemma typing_from_list_subst__disjdom : forall l E lE e t,
  typing_from_list_subst E lE e t l ->
  disjdom (dom_list_subst_atoms l) (dom E).
Proof.
  induction l; intros E lE e t H; simpl; auto.
    apply disjdom_nil_1.

    simpl in H. decompose [and] H. clear H.
    apply IHl in H0.
    apply disjdom_app_3; auto.
Qed.

Lemma zero_length__nil : forall A (l:list A),
  length l = 0 ->
  l = nil.
Proof.
  induction l; intros; auto.
    simpl in H. inversion H.
Qed.

Lemma app_inv_length : forall A (l1 l2 l1' l2':list A),
  length l1 = length l1' ->
  l1 ++ l2 = l1' ++ l2' ->
  l1 = l1' /\ l2 = l2'.
Proof.
  intros A l1.
  induction l1; intros l2 l1' l2' H1 H2.
    simpl in *.
    symmetry in H1.
    apply zero_length__nil in H1.
    subst. auto.

    simpl in *.
    apply cons_eq_app in H2.
    destruct H2 as [[qs [J1 J2]] | [J1 J2]]; subst.
      simpl in H1.
      apply IHl1 in J2; auto.
      destruct J2; subst; auto.
    
      simpl in H1.
      inversion H1.
Qed.

Lemma renamings_length : forall asubst lEnv,
  length lEnv = length (subst_atoms_lenv asubst lEnv).
Proof.
  induction asubst; intros lEnv; simpl; auto.
    destruct a. rewrite <- IHasubst; auto.
    rewrite <- renaming_length; auto.
Qed.    

Lemma id_multplication : forall a b,
  a * b = b ->
  b <> 0 ->
  a = 1.
Proof.
  induction a; intros.
    assert (b=0) as b_is_0. 
      clear H0. omega.
    rewrite b_is_0 in H0.
    contradict H0; auto.

    destruct a; auto.
      simpl in H.
      assert (b+a*b=0) as b_ab_is_0.
        clear - H. omega.
      assert (b+a*b>0) as b_ab_lt_0.
        clear - H0. 
        assert (b+a*b>=b) as b_ab_le_b.
          destruct (a*b); omega.
        omega.
      rewrite b_ab_is_0 in b_ab_lt_0.
      contradict b_ab_lt_0; auto.
        omega.
Qed.
 
Corollary LNat_Identification : forall Nat, 
  typing nil nil Nat (typ_all (typ_arrow (typ_arrow 0 0) (typ_arrow (typ_bvar 0) (typ_bvar 0)))) ->
  (forall E lEs lEz es ez vs vz A, 
    normalize es vs ->
    (forall v2, exists v, normalize (exp_app vs v2) v) ->
    normalize ez vz ->
    typing E lEs es (typ_arrow A A) ->
    typing E lEz ez A ->
    disjoint lEs lEz ->
    (
      (lEs = nil -> exists n, exists asubstz,
         beta_eta_eq E (lEs++lEz) 
           (exp_app (exp_app (exp_tapp Nat A) es) ez) 
           (nats es (subst_atoms_exp asubstz ez) n) 
           A
      ) /\
      (lEs <> nil -> exists asubsts, exists asubstz,
         beta_eta_eq E (lEs++lEz) 
           (exp_app (exp_app (exp_tapp Nat A) es) ez)
           (nats_from_list_subs es ez asubsts asubstz)
           A
      )
    )
  ).
Proof.
  intros Nat Htyping_nat E lEs lEz es ez vs vz A Hns Hvs Hnz 
    Htypinges Htypingez Disj.

  destruct (@LNat Nat A A E lEs lEz es es ez ez (Rlnat E lEs lEz es ez A) Htyping_nat) as [X JJ]; auto using Rlnat_wfor.
  
  assert (wfor E (Rlnat E lEs lEz es ez A) A A) as wfor.
    apply Rlnat_wfor; auto.

  assert (wf_typ ((X, bind_kn)::nil) (typ_fvar X)) as WFT.
    apply wf_typ_var.
       unfold binds. simpl. auto. 
       simpl_env. apply binds_one_3; auto.

  assert ((if X==X then A else typ_fvar X) = A) as HeqA.
    destruct (X==X); auto. contradict n; auto.

  assert (F_Related_oterms (typ_arrow X X) 
                                 ([(X,(Rlnat E lEs lEz es ez A))])
                                 ([(X, A)])
                                 ([(X, A)])
                                  es es E lEs).
    exists vs. exists vs. simpl.
    destruct (X==X); try solve [contradict n; auto].
    split; auto.    
    split; auto.    
    split; auto.    
    split; auto.    
      apply F_Related_ovalues_arrow_req.
      split. destruct Hns; auto.
      split. destruct Hns; auto.
        exists (dom lEs).
        intros lEnv1 x x' Htypingx Htypingx' Hwflenv Hdisj Herelxx'.
        destruct Herelxx' as [w [w' [Hnxw [Hnx'w' Hvrelww']]]].
        destruct (@Hvs x) as [u Hn_vsx_u].
        destruct (@Hvs x') as [u' Hn_vsx'_u'].
        exists u. exists u'.
        split; auto.
        split; auto.
        apply F_Related_ovalues_fvar_leq in Hvrelww'.
        destruct Hvrelww' as [R [HbindR [Hvaluew [Hvaluew' [Hadmim HRww']]]]].
        analyze_binds HbindR.
        destruct HRww' as [asubsts [asubstz [Disj_asubstz_E [Htypings [Htypingz [Hbee_w_sz Hbee_w'_sz]]]]]].
        clear HeqA.
        assert ((if X==X then A else typ_fvar X) = A) as HeqA.
          destruct (X==X); auto. contradict n; auto.
        simpl in Htypingx. rewrite HeqA in Htypingx.
        simpl in Htypingx'. rewrite HeqA in Htypingx'.
        assert (dom (lEnv_from_list_subs lEs asubsts++subst_atoms_lenv asubstz lEz) [=] dom lEnv1) as lEnv1Eq.
          apply bee_ldom in Hbee_w_sz.
          destruct Hbee_w_sz as [J1 J2].
          rewrite <- J2.
          apply preservation_normalization with (v:=w) in Htypingx; auto.
          apply typing_ldom in Htypingx.
          rewrite <- Htypingx.
          fsetdec.
        assert (uniq lEs) as UniqlEs.
          apply typing_uniqlE in Htypinges; auto.
        assert (uniq (lEnv_from_list_subs lEs asubsts++subst_atoms_lenv asubstz lEz)) as Uniq1.
          apply bee_uniqlE in Hbee_w_sz; auto.
        assert (uniq (lEs ++ lEnv_from_list_subs lEs asubsts++subst_atoms_lenv asubstz lEz)) as Uniq2.
          clear - Uniq1 lEnv1Eq Hdisj UniqlEs.
          apply disjdom__disjoint in Hdisj.
          solve_uniq.
        apply F_Related_ovalues_fvar_req. simpl.
        exists(Rlnat E lEs lEz es ez A).
        repeat(split; auto).
          destruct Hn_vsx_u; auto.
          destruct Hn_vsx'_u'; auto.
          exists (nil::asubsts). exists asubstz. simpl.
          split; auto.
          split; auto.         
            split; auto.
            split; auto.
              apply disjdom_nil_1.
          split; auto.
          split.
            apply bee_trans with (e':=exp_app es x).
              apply bee_congr_app with (lA1:=lEs)(lA2:=lEnv_from_list_subs lEs asubsts++subst_atoms_lenv asubstz lEz)(t1:=A); simpl_env; auto.
                apply bee_refl with (lE:=lEs); auto.
                  fsetdec.
                apply bee_trans with (e':=w); auto.
                  apply bee_sym.
                  apply bee_red with (lE:=lEnv1); auto.
                    fsetdec.
                    destruct Hnxw; auto.
                fsetdec.
 
              apply bee_trans with (e':=exp_app vs x).
                apply bee_red with (lE:=lEs++lEnv1); simpl_env; auto.
                  rewrite <- lEnv1Eq. simpl_env. fsetdec.

                  apply typing_app with (D1:=lEs)(D2:=lEnv1)(T1:=A); auto.
                    apply disjoint__lenv_split; auto.
                      apply disjdom__disjoint in Hdisj; auto.
                    
                  apply bigstep_red_app; auto.
                    destruct Hns; auto.

                apply bee_red with (lE:=lEs++lEnv1); simpl_env; auto.
                  rewrite <- lEnv1Eq. simpl_env. fsetdec.

                  simpl_env.
                  apply typing_app with (D1:=lEs)(D2:=lEnv1)(T1:=A); auto.
                    apply preservation_normalization with (e:=es); auto.
                    apply disjoint__lenv_split; auto.
                      apply disjdom__disjoint in Hdisj; auto.
                  destruct Hn_vsx_u; auto.

            apply bee_trans with (e':=exp_app es x').
              apply bee_congr_app with (lA1:=lEs)(lA2:=lEnv_from_list_subs lEs asubsts++subst_atoms_lenv asubstz lEz)(t1:=A); simpl_env; auto.
                apply bee_refl with (lE:=lEs); auto.
                  fsetdec.
                apply bee_trans with (e':=w'); auto.
                  apply bee_sym.
                  apply bee_red with (lE:=lEnv1); auto.
                    fsetdec.
                    destruct Hnx'w'; auto.
                fsetdec.
 
              apply bee_trans with (e':=exp_app vs x').
                apply bee_red with (lE:=lEs++lEnv1); simpl_env; auto.
                  rewrite <- lEnv1Eq. simpl_env. fsetdec.

                  apply typing_app with (D1:=lEs)(D2:=lEnv1)(T1:=A); auto.
                    apply disjoint__lenv_split; auto.
                      apply disjdom__disjoint in Hdisj; auto.
                    
                  apply bigstep_red_app; auto.
                    destruct Hns; auto.

                apply bee_red with (lE:=lEs++lEnv1); simpl_env; auto.
                  rewrite <- lEnv1Eq. simpl_env. fsetdec.

                  simpl_env.
                  apply typing_app with (D1:=lEs)(D2:=lEnv1)(T1:=A); auto.
                    apply preservation_normalization with (e:=es); auto.
                    apply disjoint__lenv_split; auto.
                      apply disjdom__disjoint in Hdisj; auto.
                  destruct Hn_vsx'_u'; auto.

  assert (F_Related_oterms (typ_fvar X) 
                                 ([(X,(Rlnat E lEs lEz es ez A))])
                                 ([(X, A)])
                                 ([(X, A)])
                                  ez ez E lEz).
    exists vz. exists vz. simpl.
    destruct (X==X); try solve [contradict n; auto].    
    repeat(split; auto).
        apply F_Related_ovalues_fvar_req. simpl.
        exists(Rlnat E lEs lEz es ez A).
        repeat(split; auto).
          destruct Hnz; auto.
          destruct Hnz; auto.
          apply Rlnat_admissible.
          exists (nil). exists nil. simpl.
          split; auto.
            apply disjdom_nil_1.
          split; auto.
          split; auto.
          split.
            apply bee_red with (lE:=lEz); auto.
              apply typing_uniqlE in Htypingez; auto.
              fsetdec.
              destruct Hnz; auto.
            apply bee_red with (lE:=lEz); auto.
              apply typing_uniqlE in Htypingez; auto.
              fsetdec.
              destruct Hnz; auto.

  apply JJ in H; auto using Rlnat_wfor.
  destruct H as [v [v' [Htypingv [Htypingv' [[Hbrc Hv] [[Hbrc' Hv'] [R [Hb [_ [_ [Hadmin Hrel]]]]]]]]]]].
  simpl in *.  rewrite HeqA in *.
  
  analyze_binds Hb.
  unfold Rlnat in Hrel. 
  destruct Hrel as [asubsts [asubstz [Disjz [Htypings [Htypingz [Hbee_sz_v Hbee_sz_v']]]]]].
  split.
   intro HlEs_is_empty.
   subst lEs. 
   rewrite lEnv_from_list_subs_nil in *.
   simpl_env in *.
   exists (length asubsts). exists asubstz.
   apply bee_trans with (e':=v).  
     apply bee_red with (lE:=lEz); auto.
       apply typing_uniqlE in Htypingez; auto.
       fsetdec.

     rewrite nats_from_list_subst__nats in Hbee_sz_v; auto.
       apply bee_sym.
       apply bee_domeq with (lE:=subst_atoms_lenv asubstz lEz); auto.
         apply bee_eq_lenv_right with (lE':=lEz) in Hbee_sz_v; auto.
           apply preservation_bigstep_red with (e':=v) in Htypingv; auto.

         apply typing_uniqlE in Htypingez; auto.

       apply typing_from_list_subst__disjdom in Htypings; auto.
         clear - Htypings Htypinges.
         apply typing_fv_ee_upper in Htypinges. 
         simpl in Htypinges.
         apply disjdom_sub with (D1:=dom E); auto.
         fsetdec.

   intro HlEs_is_nonempty.
   exists asubsts. exists asubstz.
   apply bee_trans with (e':=v).  
    apply bee_red with (lE:=lEs++lEz); auto.
      clear - Htypingez Htypinges Disj.
      apply typing_uniqlE in Htypingez.
      apply typing_uniqlE in Htypinges.
      solve_uniq. 

      fsetdec.

    apply bee_sym.
      apply preservation_bigstep_red with (e':=v) in Htypingv; auto.
      assert (dom (lEnv_from_list_subs lEs asubsts ++ subst_atoms_lenv asubstz lEz) [=] dom (lEs++lEz)) as EQ.
        apply bee_eq_lenv_right with (lE':=lEs++lEz) in Hbee_sz_v; auto. 
      assert (disjoint (lEnv_from_list_subs lEs asubsts) (subst_atoms_lenv asubstz lEz)) as Disj'.
        apply bee_uniqlE in Hbee_sz_v.
        solve_uniq.
      assert (length (lEnv_from_list_subs lEs asubsts ++ subst_atoms_lenv asubstz lEz) = length (lEs++lEz)) as EQ'.
        apply uniq_domeq__lengtheq in EQ; auto.
          apply bee_uniqlE in Hbee_sz_v; auto.
          apply typing_uniqlE in Htypingv; auto.
      rewrite app_length in EQ'.
      rewrite app_length in EQ'.
      rewrite lEnv_from_list_subs_length in EQ'.
      rewrite subst_atoms_lenv_length in EQ'.
      assert (length lEs <> 0) as HlEs_nonempty.
        clear - HlEs_is_nonempty.
        destruct lEs; simpl; auto.
      assert (length asubsts=1) as Hasubst_one.   
        clear - EQ' HlEs_nonempty.
        assert (length asubsts * length lEs = length lEs) as EQ.
          omega.
        apply id_multplication in EQ; auto.
      assert (exists asubst, asubsts=asubst::nil) as Hasubst_singleton.
        clear - Hasubst_one.
        destruct asubsts.
          simpl in Hasubst_one. inversion Hasubst_one.
          destruct asubsts.
            exists l. auto.
            simpl in Hasubst_one. inversion Hasubst_one.
      destruct Hasubst_singleton as [asubst H]; subst asubsts.
      simpl in *. 
      simpl_env in *.
      assert (typing E (lEs++lEz) (exp_app es ez) A) as Htyping_es_ez.
        apply typing_app with (T1:=A)(D1:=lEs)(D2:=lEz); auto.
          apply disjoint__lenv_split; auto.
      apply bee_domeq with (lE:=subst_atoms_lenv asubst lEs ++ subst_atoms_lenv asubstz lEz); auto.
        simpl_env. assumption.
        apply typing_uniqlE in Htypingv; auto.
Qed.

(*
*** Local Variables: ***
*** coq-prog-name: "coqtop" ***
*** coq-prog-args: ("-emacs-U" "-I" "../../../metatheory" "-I" "../Bang") ***
*** End: ***
 *)

