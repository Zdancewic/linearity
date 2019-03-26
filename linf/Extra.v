Require Import Metatheory.

Lemma cons_inv_head: forall A (l1 l2:list A) x y,
  l1 ++ [x] = l2 ++ [y] ->
  l1 = l2.
Proof.
  intros A l1 l2 x y EQ. 
  assert (l1 = l2 /\ x = y) as H.
    apply app_inj_tail. auto.
  tauto.
Qed.

Lemma cons_inv_tail: forall A (l1 l2:list A) x y,
  [x] ++ l1 = [y] ++ l2 ->
  l1 = l2.
Proof.
  intro A.
  induction l1; intros l2 x y EQ; 
    simpl in EQ; inversion EQ; subst; auto.
Qed.

Lemma concat_inv_head: forall A (l1 l2 l3 l4:list A),
  l1 = l3 -> 
  l1 ++ l2 = l3 ++ l4 ->
  l2 = l4.
Proof.
  intros A l1 l2 l3 l4 EQ13 EQ1234; subst.
  induction l3; simpl in EQ1234; auto.
    apply IHl3. 
      simpl_env in EQ1234.
      eapply cons_inv_tail; eauto.
Qed.

Lemma concat_inv_tail: forall A (l1 l2 l3 l4:list A),
  l2 = l4 -> 
  l1 ++ l2 = l3 ++ l4 ->
  l1 = l3.
Proof.
  intros A l1 l2 l3 l4 EQ24 EQ1234.
  assert (rev (l1 ++ l2) = rev (l3 ++ l4)) as H.
    rewrite EQ1234. auto.
  rewrite distr_rev in H. rewrite distr_rev in H.
  assert (rev l1 = rev l3) as H'.
    eapply concat_inv_head. 
      assert (rev l2 = rev l4) as J.
        rewrite EQ24. auto.
      eapply J. auto. 
  rewrite <- rev_involutive. 
  rewrite <- (rev_involutive l1).
  rewrite H'. auto.
Qed.

Lemma uniq_eq_inv2: forall A (E1:list (atom*A)) x a E2 F1 F2 b,
  uniq (E1 ++ [(x, a)] ++ E2) ->
  E1 ++ [(x, a)] ++ E2 = F1 ++ [(x, b)] ++ F2 ->
   E1 = F1 /\ E2 = F2 /\ a = b
.
Proof.
  intros A E1 x a E2.
  remember (E1 ++ [(x, a)] ++ E2) as G.
  generalize dependent G. generalize dependent E2. generalize dependent a. generalize dependent x.
  induction E1; intros x a1 E2 G EQG F1 F2 b Uniq EQ; auto.
  subst.
    destruct F1. simpl in *. inversion EQ; subst. repeat split; auto.
    simpl in *. inversion EQ. rewrite EQ in Uniq. subst p. simpl_env in Uniq.  
    assert (x `notin` dom [(x, a1)]). 
    inversion Uniq. simpl_env in *. fsetdec.
    inversion Uniq. simpl_env in *. fsetdec.
    subst. 
    destruct F1. subst. simpl in EQ.  inversion EQ. subst a.
    assert (x `notin` dom [(x, b)]). 
    inversion Uniq. simpl_env in *. fsetdec.
    inversion Uniq. simpl_env in *. fsetdec.
    rewrite_env (a :: (E1 ++ [(x, a1)] ++ E2)) in EQ.
    rewrite_env (p :: (F1 ++ [(x, b)] ++ F2)) in EQ.
    inversion EQ. subst a.
    assert (E1 = F1 /\ E2 = F2 /\ a1 = b). apply (IHE1 x a1 E2 (E1 ++ [(x, a1)] ++ E2)). auto.
    eapply uniq_app_2. rewrite_env ([p] ++ E1 ++ [(x, a1)] ++ E2) in Uniq. eauto. auto.
    destruct H as [Q1 [Q2 Q3]]. subst. repeat split; auto.
Qed.

Lemma uniq_eq_inv: forall A (E1:list (atom*A)) E2 F1 F2 Y,
  uniq (E1 ++ [Y] ++ E2) ->
  E1 ++ [Y] ++ E2 = F1 ++ [Y] ++ F2 ->
   E1 = F1 /\ E2 = F2
.
Proof.
  intros A E1 E2 F1 F2 Y Uniq EQ.
  destruct Y as [x a].
  apply uniq_eq_inv2 in EQ; auto.
  decompose [and] EQ; auto.
Qed.

Lemma uniq_distinct: forall B A (E1:list (atom*B)) X E2,
  uniq ((A :: E1) ++ [X] ++ E2) ->
  A <> X.
Proof.
  intros B A E1 X E2 H.
  inversion H; subst. 
  destruct X; subst.
  rewrite dom_app in H3. 
  simpl in H3.
  intros J. inversion J; subst. 
  apply H3. fsetdec.
Qed.

Lemma uniq_eq_cases: forall A (E1:list (atom*A)) E2 F1 F2 X Y,
  X <> Y ->
  uniq (E1 ++ [X] ++ E2) ->
  uniq (F1 ++ [Y] ++ F2) ->
  E1 ++ [X] ++ E2 = F1 ++ [Y] ++ F2 ->
  (exists M,
    (E2 =  M ++ [Y] ++ F2  /\ 
     F1 = E1 ++ [X] ++ M))
  \/
  (exists M,
    (E1 = F1 ++ [Y] ++ M /\
     F2 = M ++ [X] ++ E2))
.    
Proof.
  intros A E1.
  induction E1. intros.
    destruct F1. simpl in *. inversion H2. contradiction.
       simpl in H2.  inversion H2. subst p. left. exists F1. simpl. auto.
    (* cons case *)
    intros.
    destruct F1. simpl in *. inversion H2. subst a. right. exists E1. auto.
    (* hard case. *)
    assert (a <> X).  
    eapply uniq_distinct. eapply H0.
    assert (p <> Y).
    eapply uniq_distinct. eapply H1.
    inversion H2.
    subst a.
    assert (uniq (E1 ++ [X] ++ E2)).
    rewrite_env ([p] ++ (E1 ++ [X] ++ E2)) in H0.
    eapply  uniq_app_2. eapply H0.
    rewrite_env ([p] ++ (F1 ++ [Y] ++ F2)) in H1.
    assert (uniq (F1 ++ [Y] ++ F2)).
    eapply uniq_app_2. eapply H1.
    destruct (IHE1 E2 F1 F2 X Y H H5 H6 H7).
    left. destruct H8. exists x. destruct H8. subst. auto.
    right. destruct H8. exists x. destruct H8. subst. auto.
Qed.

Lemma uniq_eq_mid: forall A,
   (forall (x y:(atom * A)%type), {x = y}+{~x = y}) ->
   forall (E1:list (atom*A)) X E2 F1 F2,
   uniq (E1 ++ [X] ++ E2) -> 
   E1 ++ [X] ++ E2 = F1 ++ F2 ->
      (* X is in F1 *)
   (exists F12, F1 = E1 ++ [X] ++ F12 /\ E2 = F12 ++ F2) \/
      (* X is in F2 *)
   (exists F21, E1 = F1 ++ F21 /\ F2 = F21 ++ [X] ++ E2).
Proof with auto.
  intros A Eq_binding_dec E1 X E2 F1 F2 Uniq EQ.
  destruct F2.
  left. exists E2. simpl in *. rewrite <- app_nil_end. rewrite <- app_nil_end in EQ. auto.
  destruct (Eq_binding_dec X p).
  subst p. rewrite_env (F1 ++ [X] ++ F2) in EQ.
  right. exists nil. rewrite <- app_nil_end. rewrite_env ([X] ++ E2).
  assert (E1 = F1 /\ E2 = F2).
  eapply uniq_eq_inv. eapply Uniq.
  auto. destruct H. subst; auto.
  rewrite_env (F1 ++ [p] ++ F2) in EQ.
  lapply (uniq_eq_cases A E1 E2 F1 F2 X p n Uniq).  intros.
  destruct (H EQ).
  left. destruct H0. exists x. tauto.
  right. destruct H0. exists ([p] ++ x). simpl in H0. simpl. destruct H0. subst. tauto.
  rewrite EQ in Uniq. auto.
Qed.

Lemma uniq_join: forall A (E:list (atom*A)) F G,
  uniq (F ++ E) ->
  uniq (G ++ E) ->
  uniq (G ++ F) ->
  uniq (G ++ F ++ E).
Proof.
  intros A E F G Uniq1 Uniq2 Uniq3.
  solve_uniq.
Qed.
  
Lemma uniq_commute: forall A (E:list (atom*A)) G,
  uniq (E ++ G) ->
  uniq (G ++ E).
Proof.
  intros A E G H.
  solve_uniq.
Qed.

Lemma binds_weaken_at_tail : forall A (x:atom) (a:A) F G,
  binds x a F ->
  binds x a (F ++ G).
Proof.
  auto.
Qed.

(* Decidability results: *)
Lemma in_dom_dec: forall A x (E:list (atom*A)),
  {x `in` dom E} + {~ x `in` dom E}.
Proof.
  intros A x; induction E.
  right. fsetdec.
  destruct a. destruct IHE.
    left. rewrite_env ([(a, a0)] ++ E). rewrite dom_app. simpl. fsetdec.
    destruct (x == a).
    subst. left. simpl. fsetdec. right. simpl. fsetdec.
Qed.

Lemma uniq_dec: forall A (E:list (atom*A)),
  {uniq E} + {~uniq E}.
Proof.
  induction E; auto.
  destruct a.
  destruct (in_dom_dec A a E).
  destruct IHE. right. unfold not. intros. inversion H. contradiction.
  right. unfold not; intros; inversion H; contradiction.
  destruct IHE. left. apply uniq_cons; auto.
  right. unfold not. intros; inversion H; contradiction.
Qed.

Lemma nil_eq_one_mid_false : forall A (E:list (atom*A)) X G,
  nil = E ++ [X] ++ G -> False.
Proof.
  intros A E X G EQ.
  eapply nil_neq_one_mid; eauto.
Qed.

Lemma one_mid_eq_nil_false : forall A (E:list (atom*A)) X G,
  E ++ [X] ++ G = nil -> False.
Proof.
  intros A E X G EQ.
  eapply one_mid_neq_nil; eauto.
Qed.

Lemma fresh_tail_In : forall A (F G : list (atom*A)) x,
  uniq (F ++ G) -> x `in` (dom F) -> x `notin` (dom G).
Proof with auto.
  induction F as [|(y,b)]; intros G x H J; simpl_env in *.
  assert False by fsetdec. intuition.
  assert (x `in` singleton y \/ x `in` dom F) as K.
    fsetdec.
  destruct K as [K | K].
    assert (x = y) by fsetdec; subst.
      inversion H; subst...
    assert (uniq (F ++ G)) by eauto using uniq_app_2...
Qed.

Lemma fresh_mid_tail_In : forall A (E F G:list (atom*A)) (x:atom),
  uniq (G ++ F ++ E) -> x `in` (dom F) -> x `notin` (dom E).
Proof with auto.
  induction E as [|(y,b)]; intros F G x Ok J; simpl_env in *...
  assert (uniq (G ++ F ++ E)).
    rewrite_env ((G ++ F) ++ E).
    rewrite_env ((G ++ F) ++ [(y,b)] ++ E) in Ok.
    eauto using uniq_remove_mid.
  assert (uniq (F ++ [(y,b)] ++ E)) by eauto using uniq_app_2.
  assert (x `notin` (dom ([(y,b)] ++ E))).
    eapply fresh_tail_In. apply H0. auto.
  auto.
Qed.

Lemma uniq_map_app_l_inv : forall A (E:list (atom*A)) F f,
  uniq (map f F ++ E) -> uniq (F ++ E).
Proof with auto.
  intros. solve_uniq.
Qed.

(* Auxilliary definitions to add enough structure about permutations! *)

Inductive permute {A}: list (atom*A) -> list (atom*A) -> Prop :=
| permute_empty: permute nil nil
| permute_cons: forall D DL DR x b,
    permute D (DL ++ DR) ->
    permute ([(x, b)] ++ D) (DL ++ [(x, b)] ++ DR).

Lemma permute_refl: forall A (D:list (atom*A)),
  permute D D.
Proof.
  induction D.
  apply permute_empty.
  destruct a.
  assert ((permute ((a, a0)::D) 
                  ((a, a0)::D)) = 
         (permute ([(a, a0)] ++ D) 
                  (nil ++ [(a, a0)] ++ D))).
  simpl_env; auto.
  rewrite -> H.
  apply permute_cons. simpl_env. auto.
Qed.

Lemma dom_permute: forall A (D1 D2:list (atom*A)),
  permute D1 D2 ->
  dom D1 [=] dom D2.
Proof.
  induction D1.
  intros.
  inversion H. simpl_env in *. auto. fsetdec.
  intros.
  inversion H. subst. simpl_env in *.
  rewrite (IHD1 (DL ++ DR)). rewrite dom_app. fsetdec. auto.
Qed.

Lemma uniq_exchange: forall A (D1 D2:list (atom*A)) x b,
  uniq ([(x, b)] ++ D1 ++ D2) ->
  uniq (D1 ++ [(x, b)] ++ D2).
Proof.
  induction D1; intros; simpl_env in *.
  auto.
  simpl_env. destruct a.
  simpl_env in *. simpl. apply uniq_cons; auto.
  simpl_env. apply IHD1; auto.
  eapply uniq_remove_mid. apply H.
  inversion H. inversion H2. rewrite dom_app in *.
  simpl_env in *. subst. auto.
Qed.

Lemma uniq_env_permute: forall A (D1 D2:list (atom*A)),
  uniq D1 ->
  permute D1 D2 ->
  uniq D2.
Proof.
  induction D1; intros D2 OK P.
  inversion P. auto.
  inversion P. subst.
  apply uniq_exchange. simpl. apply uniq_cons. apply IHD1; auto.
  inversion OK; auto. rewrite <- (dom_permute A D1). 
  inversion OK; auto. auto.
Qed.

Lemma permute_weakening: forall A,
  (forall (x y:(atom * A)%type), {x = y}+{~x = y})->
  forall (D1L:list (atom*A)) D1R D2L D2R x b,
  uniq (D1L ++ [(x, b)] ++ D1R) ->
  permute (D1L ++ D1R) (D2L ++ D2R) ->
  permute (D1L ++ [(x, b)] ++ D1R) (D2L ++ [(x, b)] ++ D2R).
Proof.
  intros A Eq_lbinding_dec.
  induction D1L; intros D1R D2L D2R x b OK P; simpl_env in *; auto.
  Case "emtpy".
    apply permute_cons; auto.
  Case "cons".
  destruct a. simpl_env in *.
  inversion P.
  subst.
  lapply (uniq_eq_mid _ Eq_lbinding_dec DL (a, a0) DR D2L D2R). intros.
  destruct H as [LEFT | RIGHT]. simpl_env in H3. auto.
  destruct LEFT as [F12 [Q1 Q2]].
  subst.  simpl_env in *.
  apply permute_cons. rewrite_env ((DL ++ F12) ++ [(x, b)] ++ D2R).
  apply IHD1L; auto. simpl_env. auto.
  eapply uniq_app_2. apply OK. simpl_env. auto.
  destruct RIGHT as [F21 [Q1 Q2]].
  subst. simpl_env in *.
  rewrite_env ((D2L ++ [(x, b)] ++ F21) ++ [(a, a0)] ++ DR).
  apply permute_cons. simpl_env. apply IHD1L; auto.
  eapply uniq_app_2. apply OK.
  inversion OK. subst.
  apply uniq_exchange. simpl. apply uniq_cons. apply (uniq_env_permute A (D1L ++ D1R)).
  eapply uniq_remove_mid. simpl_env in H2. apply H2. auto.
  rewrite <- (dom_permute _ (D1L ++ D1R)).
  rewrite dom_app in *. simpl_env  in *. fsetdec. auto.
Qed.

Lemma permute_sym: forall A,
  (forall (x y:(atom * A)%type), {x = y}+{~x = y})->
  forall (D1 D2:list (atom*A)),
  uniq D1 ->
  permute D1 D2 ->
  permute D2 D1.
Proof.
  intros A Eq_lbinding_dec.
  induction D1; intros D2 OK PERM.
  inversion PERM. apply permute_empty.
  inversion PERM. subst.
  rewrite_env (nil ++ [(x, b)] ++ D1).
  apply permute_weakening; auto. inversion OK.
  subst. apply uniq_exchange. simpl. apply uniq_cons. apply (uniq_env_permute _ D1); auto.
  rewrite <- (dom_permute _ D1). auto. auto. 
  simpl_env. apply IHD1. auto. inversion OK; auto. auto.
Qed.

