(** Authors: Jianzhou Zhao. *)

Require Export Bang_ExtraLemmas.
Require Export ExtraMetalib.

(* ********************************************************************** *)
(*                                             Definition                                             *)
(* ********************************************************************** *)
(** * Size *)

Fixpoint typ_size (T : typ) {struct T} : nat :=
  match T with
    | typ_bvar i => 1
    | typ_fvar x => 1
    | typ_arrow T1 T2 => 1 + (typ_size T1) + (typ_size T2)
    | typ_all T1 => 1 + (typ_size T1)
    | typ_bang T1 => 1 + (typ_size T1)
    | typ_with T1 T2 => 1 + (typ_size T1) + (typ_size T2)
  end.

Lemma open_tt_rec_typ_size_eq : forall (X : atom) T k,
  typ_size (open_tt_rec k (typ_fvar X) T) = typ_size T.
Proof.
  (typ_cases (induction T) Case); intros kk; simpl; auto.
  Case "typ_bvar".
    destruct (kk == n); simpl; auto.
Qed.

Lemma open_tt_typ_size_eq : forall (X : atom) T,
  typ_size (open_tt T X) = typ_size T.
Proof.
  unfold open_tt.
  auto using open_tt_rec_typ_size_eq.
Qed.

(* ********************************************************************** *)
(** * The Env is seperated into two parts, one is for type vars,
        called Delta, the other is for expr vars, called Gamma.
      But the lin Env is not seperated, since it only contains expr vars.
*)

Fixpoint ddom_env (E : env) : atoms :=
  match E with
    | nil => {}
    | (X, bind_kn) :: E' => (singleton X) `union` (ddom_env E')
    | (x, bind_typ t) :: E' => (ddom_env E')
  end.

Fixpoint gdom_env (E : env) : atoms :=
  match E with
    | nil => {}
    | (X, bind_kn) :: E' => (gdom_env E')
    | (x, bind_typ t) :: E' => (singleton x) `union` (gdom_env E')
  end.

Fixpoint lgdom_env (E : lenv) : atoms :=
  match E with
    | nil => {}
    | (x, lbind_typ t) :: E' => (singleton x) `union` (lgdom_env E')
  end.

(* ********************************************************************** *)
(** * Substitutee
       1) Substitutee on Delta, maping typ vars into typ terms, delta_subst
       2) Substitutee on Gamma, maping expr vars into expr terms, gamma_subst
       3) Substitutee on lin context, maping expr vars into expr terms, lgamma_subst
       4) Substitutee on Rho, maping typ vars into relations, rho_subst
*)

(* Substitutee on Delta, map from typ vars to closed types *)

Definition delta_binding := typ.

Notation delta_subst := (list (atom * delta_binding)).
Notation delta_nil := (@nil (atom * delta_binding)).

Fixpoint apply_delta_subst (dsubst: delta_subst) (e:exp) {struct dsubst} :=
  match dsubst with
  | nil => e
  | (X, T)::dsubst' => apply_delta_subst dsubst' (subst_te X T e)
  end
  .

Fixpoint apply_delta_subst_typ (dsubst: delta_subst) (t:typ) {struct dsubst} :=
  match dsubst with
  | nil => t
  | (X, T)::dsubst' => apply_delta_subst_typ dsubst' (subst_tt X T t)
  end
  .

Fixpoint apply_delta_subst_env (dsubst:delta_subst) (E:env) {struct E} :=
  match E with
  | nil => nil
  | pair x (bind_typ T)::E' =>
      pair x (bind_typ (apply_delta_subst_typ dsubst T))::(apply_delta_subst_env dsubst E')
  | pair X (bind_kn)::E' =>
      pair X (bind_kn)::(apply_delta_subst_env dsubst E')
  end.

Fixpoint apply_delta_subst_lenv (dsubst:delta_subst) (E:lenv) {struct E} :=
  match E with
  | nil => nil
  | pair x (lbind_typ T)::E' =>
      pair x (lbind_typ (apply_delta_subst_typ dsubst T))::(apply_delta_subst_lenv dsubst E')
  end.

(*  Substitutee on Gamma, map from exp vars to exprs(closed) *)

Definition gamma_binding := exp.

Notation gamma_subst := (list (atom * gamma_binding)).
Notation gamma_nil := (@nil (atom * gamma_binding)).

Fixpoint apply_gamma_subst (gsubst: gamma_subst) (e:exp) {struct gsubst} :=
  match gsubst with
  | nil => e
  | (x, E)::gsubst' => apply_gamma_subst gsubst' (subst_ee x E e)
  end
  .

Definition apply_gamma_subst_typ (gsubst: gamma_subst) (t:typ) :=
  t .

(** * Relations *)

Definition rel := exp -> exp -> Prop.

Definition In_rel (r : rel) (v v' : exp)  : Prop :=
  (value v) /\ (value v') /\ (r v v').

(*  Substitutee on Rho, map from typ vars to relation *)
(* ********************************************************************** *)

Definition rho_binding := rel.

Notation rho_subst := (list (atom * rho_binding)).
Notation rho_nil := (@nil (atom * rho_binding)).

Inductive wf_rho_subst : env -> rho_subst -> Prop :=
  | wf_rho_subst_empty :
      wf_rho_subst nil rho_nil
  | wf_rho_subst_srel : forall E rsubst X R,
      wf_rho_subst E rsubst -> X `notin` dom E ->
      wf_rho_subst ([(X, bind_kn)]++E) ([(X, R)]++rsubst)
  | wf_rho_subst_skip : forall E rsubst x T,
      wf_rho_subst E rsubst -> x `notin` dom E -> wf_typ E T->
      wf_rho_subst ([(x, bind_typ T)]++E) rsubst
  .

Tactic Notation "wf_rho_subst_cases" tactic(first) tactic(c) :=
  first;
  [ c "wf_rho_subst_empty" |
    c "wf_rho_subst_srel" |
    c "wf_rho_subst_skip"].

(* ********************************************************************** *)
(** * Big-step Reduction *)

Inductive bigstep_red : exp -> exp -> Prop :=
  | bigstep_red_refl : forall e,
    bigstep_red e e
  | bigstep_red_trans : forall e e' e'',
    red e e' -> bigstep_red e' e'' -> bigstep_red e e''
  .

Tactic Notation "bigstep_red_cases" tactic(first) tactic(c) :=
  first;
  [ c "bigstep_red_refl" |
    c "bigstep_red_trans"].

(* ********************************************************************** *)
(** * Normal Form *)

Definition normalize (e e' : exp) :=
  ((bigstep_red e e') * (value e'))%type.

Hint Constructors bigstep_red wf_rho_subst.

(* ********************************************************************** *)
(*                                            Properties                                             *)
(* ********************************************************************** *)
(** * Properties about the free variables of terms *)

Lemma notin_fv_tt_open_tt_typ_rec : forall (X : atom) T T' k,
  X `notin` fv_tt T ->
  X `notin` fv_tt T' ->
  X `notin` fv_tt (open_tt_rec k T' T).
Proof.
  (typ_cases (induction T) Case); intros T' kk; simpl in *; auto.
  Case "typ_bvar".
    destruct (kk == n); simpl; auto.
Qed.

Lemma notin_fv_tt_open_typ_tt : forall (X : atom) T T',
  X `notin` fv_tt T ->
  X `notin` fv_tt T' ->
  X `notin` fv_tt (open_tt T T').
Proof.
  unfold open_tt.
  auto using notin_fv_tt_open_tt_typ_rec.
Qed.     

Lemma notin_fv_te_open_ee_exp_rec : forall (X : atom) e e' k,
  X `notin` fv_te e ->
  X `notin` fv_te e' ->
  X `notin` fv_te (open_ee_rec k e' e).
Proof.
  (exp_cases (induction e) Case); intros e' kk; simpl in *; auto.
  Case "exp_bvar".
    destruct (kk == n); simpl; auto.
Qed.

Lemma notin_fv_te_open_ee_exp : forall (X : atom) e e',
  X `notin` fv_te e ->
  X `notin` fv_te e' ->
  X `notin` fv_te (open_ee e e').
Proof.
  unfold open_ee.
  auto using notin_fv_te_open_ee_exp_rec.
Qed.

Lemma notin_fv_te_open_te_exp_rec : forall (X : atom) e T' k,
  X `notin` fv_te e ->
  X `notin` fv_tt T' ->
  X `notin` fv_te (open_te_rec k T' e).
Proof.
  (exp_cases (induction e) Case); intros T' kk; simpl in *; auto.
  Case "exp_abs".
    intros; auto using notin_fv_tt_open_tt_typ_rec.
  Case "exp_tapp".
    intros; auto using notin_fv_tt_open_tt_typ_rec.
Qed.

Lemma notin_fv_te_open_te_exp : forall (X : atom) e T',
  X `notin` fv_te e ->
  X `notin` fv_tt T' ->
  X `notin` fv_te (open_te e T').
Proof.
  unfold open_te.
  auto using notin_fv_te_open_te_exp_rec.
Qed.

Lemma notin_fv_te_red : forall e e' X,
  red e e' ->
  X `notin` fv_te e ->
  X `notin` fv_te e'.
Proof.
  intros e e' X Red FrX.
  induction Red; simpl in *; auto.
    apply notin_fv_te_open_ee_exp; auto.
    apply notin_fv_te_open_te_exp; auto.
    apply notin_fv_te_open_ee_exp; auto.
Qed.

Lemma notin_fv_tt_open_tt_rec_inv : forall (Y X : atom) T k,
  X `notin` fv_tt (open_tt_rec k Y T) ->
  X `notin` fv_tt T.
Proof.
  induction T; intros kk Fr; simpl in *; destruct_notin; eauto.
Qed.

Lemma notin_fv_tt_open_tt_inv : forall (Y X : atom) T,
  X `notin` fv_tt (open_tt T Y) ->
  X `notin` fv_tt T.
Proof.
  unfold open_tt.
  eauto using notin_fv_tt_open_tt_rec_inv.
Qed.

Lemma notin_fv_te_open_te_rec_inv : forall (Y X : atom) e k,
  X `notin` fv_te (open_te_rec k Y e) ->
  X `notin` fv_te e.
Proof.
  (exp_cases (induction e) Case); intros kk Fr;
    simpl in *; destruct_notin;
    eauto 6 using notin_fv_tt_open_tt_rec_inv.
Qed.

Lemma notin_fv_te_open_te_inv : forall (Y X : atom) e,
  X `notin` fv_te (open_te e Y) ->
  X `notin` fv_te e.
Proof.
  unfold open_te.
  eauto using notin_fv_te_open_te_rec_inv.
Qed.

Lemma notin_fv_te_open_ee_inv : forall (Y X : atom) e,
  X `notin` fv_te (open_ee e Y) ->
  X `notin` fv_te e.
Proof.
 intros Y X e. unfold open_ee. generalize 0.
 (exp_cases (induction e) Case); intros kk Fr;
     simpl in *; destruct_notin; eauto 6.
Qed.

Lemma notin_fv_ee_open_ee_inv : forall (y x: atom) e,
  x `notin` fv_ee (open_ee e y) ->
  x `notin` fv_ee e.
Proof.
  intros y x e. unfold open_ee. generalize 0.
  (exp_cases (induction e) Case); intros kk Fr;
      simpl in *; destruct_notin; eauto 6.
Qed.

Lemma notin_fv_ee_open_te_inv : forall (Y x : atom) e,
  x `notin` fv_ee (open_te e Y) ->
  x `notin` fv_ee e.
Proof.
 intros Y x e. unfold open_te. generalize 0.
 (exp_cases (induction e) Case); intros kk Fr;
     simpl in *; destruct_notin; eauto 6.
Qed.

Lemma notin_fv_tt_subst_tt : forall (X Y : atom) T1 T2,
  Y `notin` fv_tt T1 ->
  Y `notin` fv_tt T2 ->
  Y `notin` fv_tt (subst_tt X T1 T2).
Proof.
  intros X Y T1 T2 H J.
  (typ_cases (induction T2) Case); simpl in *; auto.
  Case "typ_fvar".
    destruct (a==X); auto.
Qed.

Lemma notin_fv_tt_subst_tt_var : forall (X : atom) T1 T2,
  X `notin` fv_tt T1 ->
  X `notin` fv_tt (subst_tt X T1 T2).
Proof.
  (typ_cases (induction T2) Case); simpl; intros Fr; auto.
  Case "typ_fvar".
    destruct (a == X); simpl; auto.
Qed.

Lemma notin_fv_tt_open_tt_rec : forall (X Y : atom) T k,
  X `notin` fv_tt T ->
  X <> Y ->
  X `notin` fv_tt (open_tt_rec k Y T).
Proof.
  (typ_cases (induction T) Case); intros kk; simpl in *; auto.
  Case "typ_bvar".
    destruct (kk == n); simpl; auto.
Qed.

Lemma notin_fv_tt_open_tt : forall (X Y : atom) T,
  X `notin` fv_tt T ->
  X <> Y ->
  X `notin` fv_tt (open_tt T Y).
Proof.
  unfold open_tt.
  auto using notin_fv_tt_open_tt_rec.
Qed.

Lemma notin_fv_te_mred : forall e e' X,
  bigstep_red e e' ->
  X `notin` fv_te e ->
  X `notin` fv_te e'.
Proof.
  intros e e' X Red FrX.
  induction Red; simpl in *; eauto using notin_fv_te_red.
Qed.

Lemma notin_fv_te_typing : forall E D T (X : atom) e,
  typing E D e T ->
  X `notin` dom E ->
  X `notin` fv_te e.
Proof.
  intros E D T X e H.
  (typing_cases (induction H) Case); intros NIE; simpl; auto.
  Case "typing_abs".
    pick fresh y.
    lapply (H1 y); [ intros J | auto ].
    assert (X `notin` fv_tt T1) by eauto using notin_fv_wf.
    assert (X `notin` fv_te e1) by auto using (@notin_fv_te_open_ee_inv y)...
    clear Fr. auto.
  Case "typing_tabs".
    pick fresh y.
    lapply (H0 y); [ intros J | auto ].
    apply (@notin_fv_te_open_te_inv y)...
      apply J; auto.
  Case "typing_tapp".
    eauto using notin_fv_wf.
  Case "typing_let".
    pick fresh y.
    lapply (H1 y); [ intros J | auto ].
    assert (X `notin` fv_te e2) by auto using (@notin_fv_te_open_ee_inv y)...
    clear Fr. auto.
Qed.

Lemma empty_typing__empty_fv : forall e T X,
  typing nil nil e T ->
  X `notin` fv_ee e /\ X `notin` fv_te e /\ X `notin` fv_tt T.
Proof with auto.
  intros.
  repeat split.
  eauto using typing_fv.
  eauto using notin_fv_te_typing.
  assert (wf_typ nil T)...
  eauto using notin_fv_wf.
Qed.

(* ********************************************************************** *)
(** * Commuting properties about substitution and opening *)

Lemma subst_tt_commute : forall X X' T T' S,
  X `notin` fv_tt T' ->
  X' `notin` fv_tt T ->
  X <> X' ->
  subst_tt X T (subst_tt X' T' S) = subst_tt X' T' (subst_tt X T S).
Proof with repeat progress
             (rewrite <- subst_tt_fresh; [auto | solve [auto]]).
  intros X X' T T' S WfT WfT' Neq.
  (typ_cases (induction S) Case); simpl in *;
    try solve [ auto |
                rewrite IHS; auto |
                rewrite IHS1; rewrite IHS2; auto ]...
  Case "typ_fvar".
    destruct (a == X'); destruct (a == X); subst; simpl in *...
    congruence.
    destruct (X' == X'); intuition.
    destruct (X == X); intuition...
    destruct (a == X); destruct (a == X'); intuition...
Qed.

Lemma subst_te_ee_commute : forall (x X : atom) T e1 e2,
  X `notin` fv_te e2 ->
  subst_ee x e2 (subst_te X T e1) = subst_te X T (subst_ee x e2 e1).
Proof.
  intros x X T e1 e2 Fr.
  (exp_cases (induction e1) Case); simpl in *;
    try solve [ auto |
                rewrite IHe1; auto |
                rewrite IHe1_1; auto; rewrite IHe1_2; auto |
                rewrite IHe1_1; auto; rewrite IHe1_2; auto ; rewrite IHe1_3; auto ].
  Case "exp_fvar".
    destruct (a == x); auto.
    rewrite <- subst_te_fresh; auto.
Qed.

Lemma subst_ee_commute : forall (x y : atom) e0 e1 e2,
  y `notin` fv_ee e2 `union` fv_ee e0 ->
  x `notin` fv_ee e2 `union` fv_ee e0 ->
  x <> y ->
  subst_ee x e2 (subst_ee y e0 e1) = subst_ee y e0 (subst_ee x e2 e1).
Proof.
  intros x y e0 e1 e2 Fry Frx xny.
  (exp_cases (induction e1) Case); simpl in *;
    try solve [ auto |
                rewrite IHe1; auto |
                rewrite IHe1_1; auto; rewrite IHe1_2; auto |
                rewrite IHe1_1; auto; rewrite IHe1_2; auto ; rewrite IHe1_3; auto ].
  Case "exp_fvar".
    destruct (a == x); subst; simpl; auto.
      destruct (x == y); subst; simpl; auto.
        tauto.        
        destruct (x == x); subst; simpl; auto.
          rewrite <- subst_ee_fresh; auto.
          tauto.        
      destruct (a == y); subst; simpl; auto.
        rewrite <- subst_ee_fresh; auto.
        destruct (a == x); subst; simpl; auto.
          tauto.        
Qed.

Lemma swap_dubst_tt : forall (X X' : atom) T1 T2 T,
  X `notin` fv_tt T1 ->
  subst_tt X T1 (subst_tt X' (subst_tt X T1 T2) T) =
  subst_tt X T1 (subst_tt X' T2 T).
Proof.
  intros X X' T1 T2 T Fr.
  (typ_cases (induction T) Case); simpl;
    try solve [ auto |
                rewrite IHT; auto |
                rewrite IHT1; auto; rewrite IHT2; auto ].
  Case "typ_fvar".
    destruct (a == X'); subst; auto.
    rewrite <- subst_tt_fresh; auto.
    auto using notin_fv_tt_subst_tt_var.
Qed.

Lemma open_tt_rec_commute : forall T T' (X : atom) k1 k2,
  k1 <> k2 ->
  type T' ->
  (open_tt_rec k1 X (open_tt_rec k2 T' T) =
    open_tt_rec k2 T' (open_tt_rec k1 X T)).
Proof with repeat progress (rewrite <- open_tt_rec_type; [auto | solve [auto]]).
  intros T T' X k1 k2 Neq Typ.
  generalize dependent k1.
  generalize dependent k2.
  (typ_cases (induction T) Case); intros k2 k1 Neq; simpl in *;
    try solve [ auto |
                rewrite IHT; auto |
                rewrite IHT1; auto; rewrite IHT2; auto ].
  Case "typ_bvar".
    destruct (k2 == n); destruct (k1 == n); subst; simpl in *...
    intuition.
    destruct (n == n); subst; intuition.
    destruct (n == n); subst; intuition.
    destruct (k1 == n); destruct (k2 == n); subst; simpl in *; intuition.
Qed.

Lemma open_te_rec_commute : forall (X : atom) e T k1 k2,
  k1 <> k2 ->
  type T ->
  X `notin` fv_te e ->
  (open_te_rec k1 X (open_te_rec k2 T e) =
    open_te_rec k2 T (open_te_rec k1 X e)).
Proof with auto.
  intros X e T k1 k2 Neq Typ Fr.
  generalize dependent k1.
  generalize dependent k2.
  (exp_cases (induction e) Case); intros k1 k2 Neq; simpl in *;
    try solve [ auto |
                rewrite IHe; auto |
                rewrite IHe1; auto; rewrite IHe2; auto |
                rewrite IHe1; auto; rewrite IHe2; auto ; rewrite IHe3; auto ].
  Case "exp_abs".
    rewrite IHe...
    rewrite open_tt_rec_commute...
  Case "exp_tapp".
    rewrite IHe...
    rewrite open_tt_rec_commute...
Qed.

(* ********************************************************************** *)
(** * Lemmas and Auto of Env *)

Lemma ddom_single : forall x,
  ddom_env [(x,bind_kn)] [=] singleton x.
Proof.
  simpl. intros. fsetdec.
Qed.

Lemma ddom_push : forall x E,
  ddom_env ([(x,bind_kn)] ++ E) = (singleton x) `union` (ddom_env E).
Proof.
  simpl. intros. reflexivity.
Qed.

Lemma ddom_concat : forall E F,
  ddom_env (F ++ E) [=] (ddom_env F) `union` (ddom_env E).
Proof.
  induction F as [|(x,a) F IH]; simpl.
  fsetdec.
  destruct a; fsetdec.
Qed.

Lemma ddom_cons : forall x E,
  ddom_env ((x,bind_kn) :: E) [=] (singleton x) `union` (ddom_env E).
Proof.
  simpl. intros. fsetdec.
Qed.

Lemma free_env_concat : forall E F,
  fv_env (F ++ E) [=] (fv_env F) `union` (fv_env E).
Proof.
  induction F as [|(x,a) F IH]; simpl.
  fsetdec.
  destruct a; fsetdec.
Qed.

Lemma free_env_typ_cons : forall x t E,
  fv_env ((x,bind_typ t) :: E) [=] (singleton x)  `union` (fv_tt t) `union` (fv_env E).
Proof.
  simpl. intros. fsetdec.
Qed.

Lemma free_env_typ_push : forall x t E,
  fv_env ([(x,bind_typ t)] ++ E) [=] (singleton x) `union` (fv_tt t)  `union` (fv_env E).
Proof.
  simpl. intros. fsetdec.
Qed.

Lemma free_env_kind_push : forall X E,
  fv_env ([(X,bind_kn)] ++ E) [=] (singleton X) `union` (fv_env E).
Proof.
  simpl. intros. fsetdec.
Qed.

Lemma free_env_kind_cons : forall X E,
  fv_env ((X,bind_kn) :: E) [=] (singleton X)  `union` (fv_env E).
Proof.
  simpl. intros. fsetdec.
Qed.

Lemma gdom_single : forall x t,
  gdom_env [(x,bind_typ t)] [=] singleton x.
Proof.
  simpl. intros. fsetdec.
Qed.

Lemma gdom_push : forall x t E,
  gdom_env ([(x,bind_typ t)] ++ E) [=] (singleton x) `union` (gdom_env E).
Proof.
  simpl. intros. fsetdec.
Qed.

Lemma gdom_cons : forall x t E,
  gdom_env ((x,bind_typ t) :: E) [=] (singleton x) `union` (gdom_env E).
Proof.
  simpl. intros. fsetdec.
Qed.

Lemma gdom_concat : forall E F,
  gdom_env (F ++ E) [=] (gdom_env F) `union` (gdom_env E).
Proof.
  induction F as [|(x,a) F IH]; simpl.
  fsetdec.
  destruct a; fsetdec.
Qed.

Lemma free_lenv_concat : forall E F,
  fv_lenv (F ++ E) [=] (fv_lenv F) `union` (fv_lenv E).
Proof.
  induction F as [|(x,a) F IH]; simpl.
  fsetdec.
  destruct a; fsetdec.
Qed.

Lemma free_lenv_typ_cons : forall x t E,
  fv_lenv ((x,lbind_typ t) :: E) [=] (singleton x)  `union` (fv_tt t) `union` (fv_lenv E).
Proof.
  simpl. intros. fsetdec.
Qed.

Lemma free_lenv_typ_push : forall x t E,
  fv_lenv ([(x,lbind_typ t)] ++ E) [=] (singleton x) `union` (fv_tt t)  `union` (fv_lenv E).
Proof.
  simpl. intros. fsetdec.
Qed.

Lemma lgdom_single : forall x t,
  lgdom_env [(x,lbind_typ t)] [=] singleton x.
Proof.
  simpl. intros. fsetdec.
Qed.

Lemma lgdom_push : forall x t E,
  lgdom_env ([(x,lbind_typ t)] ++ E) [=] (singleton x) `union` (lgdom_env E).
Proof.
  simpl. intros. fsetdec.
Qed.

Lemma lgdom_cons : forall x t E,
  lgdom_env ((x,lbind_typ t) :: E) [=] (singleton x) `union` (lgdom_env E).
Proof.
  simpl. intros. fsetdec.
Qed.

Lemma lgdom_concat : forall E F,
  lgdom_env (F ++ E) [=] (lgdom_env F) `union` (lgdom_env E).
Proof.
  induction F as [|(x,a) F IH]; simpl.
  fsetdec.
  destruct a; fsetdec.
Qed.

Hint Rewrite ddom_single ddom_push ddom_cons ddom_concat : rewr_ddom.
Hint Rewrite gdom_single gdom_push gdom_cons gdom_concat : rewr_gdom.
Hint Rewrite free_env_typ_push free_env_typ_cons free_env_kind_push free_env_kind_cons free_env_concat : rewr_fdom.
Hint Rewrite lgdom_single lgdom_push lgdom_cons lgdom_concat : rewr_lgdom.
Hint Rewrite free_lenv_typ_push free_lenv_typ_cons free_lenv_concat : rewr_lfdom.

Ltac simpl_env :=
    autorewrite with rewr_list rewr_list_in rewr_map rewr_dom rewr_ddom rewr_gdom rewr_fdom rewr_lgdom rewr_lfdom.
Tactic Notation "simpl_env" "in" hyp(H) :=
    autorewrite with rewr_list rewr_list_in rewr_map rewr_dom rewr_ddom rewr_gdom rewr_fdom rewr_lgdom rewr_lfdom in H.
Tactic Notation "simpl_env" "in" "*" :=
    autorewrite with rewr_list rewr_list_in rewr_map rewr_dom rewr_ddom rewr_gdom rewr_fdom rewr_lgdom rewr_lfdom in *.

Lemma ddom_dom__inv : forall A (sE : list (atom * A)) E X b,
  ddom_env ([(X, bind_kn)]++E) [=] dom ([(X, b)]++sE) ->
  X `notin` ddom_env E ->
  X `notin` dom sE ->
  ddom_env E [=] dom sE.
Proof.
  intros.
  simpl in *.
  fsetdec.
Qed.

Lemma free_env__free_ddom : forall x E,
  x `notin` fv_env E ->
  x `notin` ddom_env E.
Proof.
  induction E as [ | [x1 b1] E ]; simpl; intros H; auto.
  destruct b1; auto.
Qed.

Lemma dom__ddom: forall x E,
  x `notin` dom E ->
  x `notin` ddom_env E.
Proof.
  induction E as [ | [x1 b1] E ]; simpl; intros H; auto.
  destruct b1; auto.
Qed.

Lemma free_env__free_dom: forall x E,
  x `notin` fv_env E ->
  x `notin` dom E.
Proof.
  induction E as [ | [x1 b1] E ]; simpl; intros H; auto.
  destruct b1; auto.
Qed.

Lemma free_lenv__free_dom: forall x E,
  x `notin` fv_lenv E ->
  x `notin` dom E.
Proof.
  induction E as [ | [x1 b1] E ]; simpl; intros H; auto.
  destruct b1; auto.
Qed.

(* XXX fsetdec *)
Lemma dom_empty_inv: forall  A E,
  dom E [=] {} -> E = (@nil (atom * A)).
Proof.
  intros.
  induction E as [ | [x1 a1] E' ]; simpl_env in *; auto.
  assert (x1 `notin` (singleton x1 `union` dom E')) by fsetdec.
  fsetdec.
Qed.

Hint Resolve free_env__free_dom free_lenv__free_dom free_env__free_ddom dom__ddom (*wftS__wft*).

(********************************************************)
(* well found subst give envs *)

Lemma dom_rho_subst : forall E rsubst,
  wf_rho_subst E rsubst -> ddom_env E [=] dom rsubst.
Proof.
  intros E rsubst Hwfd.
  induction Hwfd; simpl_env; fsetdec.
Qed.

Lemma wf_rho_subst__uniq : forall E rsubst,
  wf_rho_subst E rsubst -> wf_env E /\ uniq E /\ uniq rsubst.
Proof.
  intros E rsubst H.
  (wf_rho_subst_cases (induction H) Case); auto.
  Case "wf_rho_subst_srel".
    decompose [and] IHwf_rho_subst.
    split; eauto.
    split; eauto.
      apply dom_rho_subst in H.
      apply dom__ddom in H0. 
      rewrite H in H0; auto.
  Case "wf_rho_subst_skip".
    split; decompose [and] IHwf_rho_subst; auto.
Qed.

(*******************************************************************************)
(** subst under delta/gamma *)

Lemma delta_subst_closed_typ : forall dsubst t,
   wf_typ nil t ->
   apply_delta_subst_typ dsubst t = t.
Proof.
  induction dsubst; intros; auto.
  Case "cons".
    destruct a; simpl.
    rewrite <- subst_tt_fresh; eauto using notin_fv_wf.
Qed.

Lemma gamma_subst_closed_exp : forall gsubst e t,
   typing nil nil e t ->
   apply_gamma_subst gsubst e = e.
Proof.
  induction gsubst; intros e t Htyping; simpl; auto.
    destruct a.
    rewrite <- subst_ee_fresh; eauto.
      apply empty_typing__empty_fv with (X:=a) in Htyping; eauto.
Qed.

Lemma gamma_subst_closed_typ : forall gsubst t,
   wf_typ nil t ->
   apply_gamma_subst_typ gsubst t = t.
intros. unfold apply_gamma_subst_typ. auto.
Qed.

Lemma delta_subst_closed_exp : forall dsubst e t,
   typing nil nil e t ->
   apply_delta_subst dsubst e = e.
Proof.
  induction dsubst; intros e t Htyping; simpl; auto.
    destruct a.
    rewrite <- subst_te_fresh; eauto.
      apply empty_typing__empty_fv with (X:=a) in Htyping; eauto.
Qed.

Lemma delta_subst_closed_typing : forall dsubst e t,
   typing nil nil e t ->
   apply_delta_subst_typ dsubst t = t.
Proof.
  induction dsubst; intros e t Htyping; simpl; auto.
    destruct a.
    rewrite <- subst_tt_fresh; eauto.
      apply empty_typing__empty_fv with (X:=a) in Htyping; eauto.
Qed.

Lemma gamma_subst_var : forall gsubst x t e,
   uniq gsubst ->
   binds x e gsubst -> 
   typing nil nil e t ->
   apply_gamma_subst gsubst (exp_fvar x) = e.
Proof.
  induction gsubst; intros x t e Huniq Hbinds Htyping.
    inversion Hbinds.

    simpl. destruct a.
    destruct (x==a); subst; simpl_env in *.
      analyze_binds_uniq Hbinds; subst.
        rewrite gamma_subst_closed_exp with (t:=t); auto.

      eapply IHgsubst; eauto.
        inversion Huniq; auto.
        analyze_binds_uniq Hbinds.
Qed.

Lemma apply_gamma_subst_nfv: forall gsubst x,
  x `notin` dom gsubst ->
  apply_gamma_subst gsubst (exp_fvar x) = (exp_fvar x).
Proof.
  induction gsubst; intros; simpl; auto.
  destruct a.
    simpl_env in *. destruct_notin.
    destruct (x==a).
      contradict e; auto.
      apply IHgsubst; auto.
Qed.

Lemma apply_delta_subst_nfv: forall dsubst x,
  apply_delta_subst dsubst (exp_fvar x) = (exp_fvar x).
induction dsubst; intros; simpl; auto.
  destruct a; auto.
Qed.

Lemma apply_gamma_subst_typ_nfv: forall gsubst x,
  apply_gamma_subst_typ gsubst (typ_fvar x) = (typ_fvar x).
induction gsubst; intros; simpl; auto.
Qed.

Lemma apply_delta_subst_typ_nfv: forall dsubst x,
  x `notin` dom dsubst ->
  apply_delta_subst_typ dsubst (typ_fvar x) = (typ_fvar x).
induction dsubst; intros x Fr; simpl_env; simpl; auto.
  destruct a.
  destruct (x==a); subst; simpl_env in Fr; destruct_notin; auto.
      contradict NotInTac0; auto.
Qed.

Lemma delta_subst_binds_typ: forall E x T dsubst,
  binds x (bind_typ T) E ->
  binds x (bind_typ (apply_delta_subst_typ dsubst T)) (apply_delta_subst_env dsubst E).
Proof.
  induction E; intros x T dsubst Hbinds; simpl.
    inversion Hbinds.
    destruct a. destruct b; simpl_env in *; analyze_binds Hbinds.
        inversion BindsTacVal; subst; auto.
Qed.

Lemma delta_subst_lbinds_typ: forall E x T dsubst,
  binds x (lbind_typ T) E ->
  binds x (lbind_typ (apply_delta_subst_typ dsubst T)) (apply_delta_subst_lenv dsubst E).
Proof.
  induction E; intros x T dsubst Hbinds; simpl.
    inversion Hbinds.
    destruct a. destruct l; simpl_env in *; analyze_binds Hbinds.
        inversion BindsTacVal; subst; auto.
Qed.

Lemma delta_subst_binds_kind: forall E X dsubst,
  binds X bind_kn E ->
  binds X bind_kn (apply_delta_subst_env dsubst E).
Proof.
  induction E; intros X dsubst Hbinds; simpl.
    inversion Hbinds.
    destruct a; destruct b;
      simpl_env in *; analyze_binds Hbinds.
Qed.

Lemma delta_subst_var : forall dsubst X T,
   uniq dsubst ->
   binds X (T) dsubst -> wf_typ nil T ->
   apply_delta_subst_typ dsubst (typ_fvar X) = T.
Proof.
  induction dsubst; intros X T Huniq Hbinds Hwft.
    inversion Hbinds.

    simpl. destruct a.
    destruct (X==a); subst; simpl_env in *.
      analyze_binds_uniq Hbinds; subst.
        erewrite delta_subst_closed_typ; eauto.

      eapply IHdsubst; eauto.
        inversion Huniq; auto.
        analyze_binds Hbinds; auto.
Qed.

Lemma subst_ee_value : forall e e' x,
  value e ->
  expr e' ->
  value (subst_ee x e' e).
Proof.
  intros e e' x Hv He.
  induction Hv; intros; simpl; auto.
    inversion H; subst.
    apply value_abs.
        apply expr_abs with (L:=L `union` singleton x); auto.
        intros. rewrite subst_ee_open_ee_var; auto.

    inversion H; subst.
    apply value_tabs.
        apply expr_tabs with (L:=L `union` singleton x); auto.
        intros. rewrite subst_ee_open_te_var; auto.
Qed.

Lemma subst_te_value : forall e t x,
  value e ->
  type t ->
  value (subst_te x t e).
Proof.
  intros e t x Hv Ht.
  induction Hv; simpl; auto.
    inversion H; subst.
    apply value_abs.
        apply expr_abs with (L:=L `union` singleton x); auto.
        intros. rewrite subst_te_open_ee_var; auto.

    inversion H; subst.
    apply value_tabs.
        apply expr_tabs with (L:=L `union` singleton x); auto.
        intros. rewrite subst_te_open_te_var; auto.
Qed.

(* ********************************************************************** *)
(* commut and subst *)

Lemma commut_gamma_subst_app: forall gsubst e1 e2,
   apply_gamma_subst gsubst (exp_app e1 e2)
= exp_app (apply_gamma_subst gsubst e1) (apply_gamma_subst gsubst e2).
Proof.
  induction gsubst; intros; simpl; auto.
    destruct  a. destruct  g; auto.
Qed.

Lemma commut_gamma_subst_tapp: forall gsubst e1 t2,
   apply_gamma_subst gsubst (exp_tapp e1 t2)
= exp_tapp (apply_gamma_subst gsubst e1) (apply_gamma_subst_typ gsubst t2).
Proof.
  induction gsubst; intros; simpl; auto.
    unfold apply_gamma_subst_typ in *.
    destruct  a. destruct  g; auto.
Qed.

Lemma commut_gamma_subst_abs: forall gsubst V e,
   apply_gamma_subst gsubst (exp_abs V e)
= exp_abs (apply_gamma_subst_typ gsubst V) (apply_gamma_subst gsubst e).
Proof.
  induction gsubst; intros; simpl; auto.
    unfold apply_gamma_subst_typ in *.
    destruct  a. destruct  g; auto.
Qed.

Lemma commut_gamma_subst_tabs: forall gsubst e,
   apply_gamma_subst gsubst (exp_tabs e)
= exp_tabs (apply_gamma_subst gsubst e).
Proof.
  induction gsubst; intros; simpl; auto.
    destruct  a. destruct  g; auto.
Qed.

Lemma commut_gamma_subst_bang: forall gsubst e,
   apply_gamma_subst gsubst (exp_bang e)
= exp_bang (apply_gamma_subst gsubst e).
Proof.
  induction gsubst; intros; simpl; auto.
    destruct  a. destruct  g; auto.
Qed.

Lemma commut_gamma_subst_let: forall gsubst e1 e2,
   apply_gamma_subst gsubst (exp_let e1 e2)
= exp_let (apply_gamma_subst gsubst e1) (apply_gamma_subst gsubst e2).
Proof.
  induction gsubst; intros; simpl; auto.
    destruct  a. destruct  g; auto.
Qed.

Lemma commut_gamma_subst_apair: forall gsubst e1 e2,
   apply_gamma_subst gsubst (exp_apair e1 e2)
= exp_apair (apply_gamma_subst gsubst e1) (apply_gamma_subst gsubst e2).
Proof.
  induction gsubst; intros; simpl; auto.
    destruct  a. destruct  g; auto.
Qed.

Lemma commut_gamma_subst_fst: forall gsubst e,
   apply_gamma_subst gsubst (exp_fst e)
= exp_fst (apply_gamma_subst gsubst e).
Proof.
  induction gsubst; intros; simpl; auto.
    destruct  a. destruct  g; auto.
Qed.

Lemma commut_gamma_subst_snd: forall gsubst e,
   apply_gamma_subst gsubst (exp_snd e)
= exp_snd (apply_gamma_subst gsubst e).
Proof.
  induction gsubst; intros; simpl; auto.
    destruct  a. destruct  g; auto.
Qed.

Lemma commut_delta_subst_app: forall dsubst e1 e2,
   apply_delta_subst dsubst (exp_app e1 e2)
= exp_app (apply_delta_subst dsubst e1) (apply_delta_subst dsubst e2).
Proof.
  induction dsubst; intros; simpl; auto.
    destruct  a. destruct  d; auto.
Qed.

Lemma commut_delta_subst_tapp: forall dsubst e1 t2,
   apply_delta_subst dsubst (exp_tapp e1 t2)
= exp_tapp (apply_delta_subst dsubst e1) (apply_delta_subst_typ dsubst t2).
Proof.
  induction dsubst; intros; simpl; auto.
    destruct  a. destruct  d; auto.
Qed.

Lemma commut_delta_subst_abs: forall dsubst e V,
   apply_delta_subst dsubst (exp_abs V e)
= exp_abs (apply_delta_subst_typ dsubst V) (apply_delta_subst dsubst e).
Proof.
  induction dsubst; intros; simpl; auto.
    destruct  a. destruct  d; auto.
Qed.

Lemma commut_delta_subst_tabs: forall dsubst e,
   apply_delta_subst dsubst (exp_tabs e)
= exp_tabs (apply_delta_subst dsubst e).
Proof.
  induction dsubst; intros; simpl; auto.
    destruct  a. destruct  d; auto.
Qed.

Lemma commut_delta_subst_ebang: forall dsubst e,
   apply_delta_subst dsubst (exp_bang e)
= exp_bang (apply_delta_subst dsubst e).
Proof.
  induction dsubst; intros; simpl; auto.
    destruct  a. destruct  d; auto.
Qed.

Lemma commut_delta_subst_let: forall dsubst e1 e2,
   apply_delta_subst dsubst (exp_let e1 e2)
= exp_let (apply_delta_subst dsubst e1) (apply_delta_subst dsubst e2).
Proof.
  induction dsubst; intros; simpl; auto.
    destruct  a. destruct  d; auto.
Qed.

Lemma commut_delta_subst_apair: forall dsubst e1 e2,
   apply_delta_subst dsubst (exp_apair e1 e2)
= exp_apair (apply_delta_subst dsubst e1) (apply_delta_subst dsubst e2).
Proof.
  induction dsubst; intros; simpl; auto.
    destruct  a. destruct  d; auto.
Qed.

Lemma commut_delta_subst_fst: forall dsubst e,
   apply_delta_subst dsubst (exp_fst e)
= exp_fst (apply_delta_subst dsubst e).
Proof.
  induction dsubst; intros; simpl; auto.
    destruct  a. destruct  d; auto.
Qed.

Lemma commut_delta_subst_snd: forall dsubst e,
   apply_delta_subst dsubst (exp_snd e)
= exp_snd (apply_delta_subst dsubst e).
Proof.
  induction dsubst; intros; simpl; auto.
    destruct  a. destruct  d; auto.
Qed.

Lemma commut_gamma_subst_open_tt: forall gsubst T X,
   apply_gamma_subst_typ gsubst (open_tt T X)
= open_tt (apply_gamma_subst_typ gsubst T) (apply_gamma_subst_typ gsubst X).
intros. unfold apply_gamma_subst_typ in *.  auto.
Qed.

Lemma commut_delta_subst_arrow: forall dsubst T1 T2,
   apply_delta_subst_typ dsubst (typ_arrow T1 T2)
= typ_arrow (apply_delta_subst_typ dsubst T1) (apply_delta_subst_typ dsubst T2).
Proof.
  induction dsubst; intros; simpl; auto.
    destruct  a. destruct  d; auto.
Qed.

Lemma commut_delta_subst_all: forall dsubst T,
   apply_delta_subst_typ dsubst (typ_all T)
= typ_all (apply_delta_subst_typ dsubst T).
Proof.
  induction dsubst; intros; simpl; auto.
    destruct  a. destruct  d; auto.
Qed.

Lemma commut_delta_subst_tbang: forall dsubst T1,
   apply_delta_subst_typ dsubst (typ_bang T1)
= typ_bang (apply_delta_subst_typ dsubst T1).
Proof.
  induction dsubst; intros; simpl; auto.
    destruct  a. destruct  d; auto.
Qed.

Lemma commut_delta_subst_with: forall dsubst T1 T2,
   apply_delta_subst_typ dsubst (typ_with T1 T2)
= typ_with (apply_delta_subst_typ dsubst T1) (apply_delta_subst_typ dsubst T2).
Proof.
  induction dsubst; intros; simpl; auto.
    destruct  a. destruct  d; auto.
Qed.

Lemma wft_strengthen_ex : forall E F T,
 wf_typ (F++E) T -> ddom_env F [=] {} -> wf_typ E T.
Proof.
  intros E F T Hwft Heq.
  induction F; auto.
    destruct a. destruct b; simpl in Heq.
      assert (a `notin` (singleton a `union` ddom_env F)). fsetdec.
      fsetdec.

      simpl_env in *. apply IHF; auto.
      apply  wf_typ_strengthening with (E:=F++E) (x:=a) (U:=t) (F:=(@nil (atom*binding))); auto.
Qed.

(******************************************************************)
(*                                     AutoDB                                             *)
(******************************************************************)
Hint Rewrite 
    commut_gamma_subst_abs commut_delta_subst_abs
    commut_delta_subst_arrow 
    commut_gamma_subst_app commut_delta_subst_app
    commut_gamma_subst_tabs commut_delta_subst_tabs
    commut_delta_subst_all
    commut_gamma_subst_bang commut_delta_subst_ebang
    commut_gamma_subst_let commut_delta_subst_let
    commut_gamma_subst_tapp commut_delta_subst_tapp
    commut_gamma_subst_apair commut_delta_subst_apair
    commut_delta_subst_tbang
    commut_delta_subst_with
    commut_gamma_subst_fst commut_delta_subst_fst
    commut_gamma_subst_snd commut_delta_subst_snd
    : rewr_commut_subst.

Ltac simpl_commut_subst :=
    autorewrite with rewr_commut_subst.
Tactic Notation "simpl_commut_subst" "in" hyp(H) :=
    autorewrite with rewr_commut_subst in H.
Tactic Notation "simpl_commut_subst" "in" "*" :=
    autorewrite with rewr_commut_subst in *.

(* *************** *)
(* red expr value typ *)

Lemma value_unred: forall v,
  value v ->
  ~exists e, red v e.
Proof.
  intros v Hv.
  induction Hv; unfold not; intros; try solve [
    destruct H as [e H]; inversion H |
    destruct H0 as [e H0]; inversion H0 |
    destruct H1 as [e H1]; inversion H1 |
    destruct H0 as [ee H0]; inversion H0 ].
Qed.

Lemma unique_red: forall e e1 e2,
  red e e1 -> red e e2 -> e1 = e2.
intros.
  generalize dependent e2.
  induction H; intros; try solve
    [inversion H1; subst; try solve [apply IHred in H6; subst; auto | inversion H0] |
     inversion H1; subst; auto; inversion H6 |
     inversion H0; subst; auto; inversion H6 |
     inversion H0; subst; auto; inversion H2 |
     inversion H0; subst; try solve [apply IHred in H2; subst; auto | inversion H]  |
     inversion H1; subst; try solve [apply IHred in H7; subst; auto | inversion H0]
    ].

  inversion H0; subst; auto.
    assert (value (exp_bang e1)) as Val.
      inversion H; subst.
      inversion H4; subst; auto.
    apply value_unred in Val.
    assert (False) as F.
      apply Val. exists e1'. auto.
    tauto.

  inversion H1; subst; auto.
    inversion H3.

  inversion H1; subst; auto.
    inversion H3.
Qed.

Lemma unique_normal_form: forall u v v',
  normalize u v -> normalize u v' -> v = v'.
Proof.
  intros u v v' norm norm'. 
  destruct norm as [Hbrc Hv].
  destruct norm' as [Hbrc' Hv'].
  generalize dependent v'.
  induction Hbrc; intros.
     inversion Hbrc'; subst; auto.
       inversion H; subst; inversion Hv; subst.

     apply IHHbrc; auto.
     inversion Hbrc'; subst.
       inversion H; subst; inversion Hv'; subst.

       apply unique_red with (e2:=e'0) in H; subst; auto.
Qed.

Lemma bigstep_red__trans: forall e e' e'',
  bigstep_red e e' ->
  bigstep_red e' e'' ->
  bigstep_red e e''.
Proof.
  intros.
  generalize dependent e''.
  induction H; intros; eauto.
Qed.

Lemma _congr_app_fun : forall e1 e2 v1 u,
  expr e2 ->
  bigstep_red e1 v1 ->
  bigstep_red (exp_app v1 e2)  u ->
  bigstep_red (exp_app e1 e2) u.
Proof.
  intros e1 e2 v1 u He Hbrc Hbrc'.
  generalize dependent e2.
  generalize dependent u.
  induction Hbrc; intros; eauto.
Qed.

Lemma _congr_let_arg : forall e1 e2 e1',
  expr (exp_let e1 e2) ->
  bigstep_red e1 e1' ->
  bigstep_red (exp_let e1 e2) (exp_let e1' e2).
Proof.
  intros e1 e2 e1' He Hbrc.
  generalize dependent e2.
  induction Hbrc; intros; eauto.
    apply bigstep_red_trans with (e':=exp_let e' e2); auto.
      apply IHHbrc; auto.
        inversion He; subst.
        apply expr_let with (L:=L); auto.
Qed.

Lemma _congr_tapp : forall e1 t2 v1 u,
  type t2 ->
  bigstep_red e1 v1 ->
  bigstep_red (exp_tapp v1 t2)  u ->
  bigstep_red (exp_tapp e1 t2) u.
Proof.
  intros e1 t2 v1 u He Hbrc Hbrc'.
  generalize dependent t2.
  generalize dependent u.
  induction Hbrc; intros; eauto.
Qed.

Lemma _congr_app : forall e1 e2 v1 u,
  value v1 ->
  expr e1 ->
  expr e2 ->
  bigstep_red e1 v1 ->
  bigstep_red (exp_app v1 e2) u ->
  bigstep_red (exp_app e1 e2) u.
Proof.
  intros e1 e2 v1 u Hv1 He1 He2 Hbrc1 Hbrc.
  generalize dependent e2.
  generalize dependent u.
  induction Hbrc1; intros; auto.
    apply bigstep_red__trans with (e':=exp_app e'' e2); auto.
      eapply _congr_app_fun with (v1:=e''); eauto.
Qed.

Lemma _congr_let : forall e1 e2 v1 u,
  value v1 ->
  expr (exp_let e1 e2) ->
  bigstep_red e1 v1 ->
  bigstep_red (exp_let v1 e2) u ->
  bigstep_red (exp_let e1 e2) u.
Proof.
  intros e1 e2 v1 u Hv1 He Hbrc1 Hbrc.
  generalize dependent e2.
  generalize dependent u.
  induction Hbrc1; intros; auto.
    apply bigstep_red__trans with (e':=exp_let e'' e2); auto.
      eapply _congr_let_arg with (e1':=e''); eauto.
Qed.

Lemma congr_app_fun : forall e1 e2 v1 u,
  expr e2 ->
  normalize e1 v1 ->
  normalize (exp_app v1 e2)  u ->
  normalize (exp_app e1 e2) u.
Proof.
  intros e1 e2 v1 u He Hnorm Hnorm'.
  destruct Hnorm. destruct Hnorm'.
  split; auto.
    apply _congr_app_fun with (v1:=v1); auto.
Qed.

Lemma congr_tapp : forall e1 t2 v1 u,
  type t2 ->
  normalize e1 v1 ->
  normalize (exp_tapp v1 t2)  u ->
  normalize (exp_tapp e1 t2) u.
Proof.
  intros e1 t2 v1 u Ht norm norm'.
  destruct norm. destruct norm'.
  split; auto.
    apply _congr_tapp with (v1:=v1); auto.
Qed.

Lemma congr_app : forall e1 e2 v1 u,
  expr e1 ->
  expr e2 ->
  normalize e1 v1 ->
  normalize (exp_app v1 e2) u ->
  normalize (exp_app e1 e2) u.
Proof.
  intros e1 e2 v1 u He1 He2 Hnorm1 Hnorm.
  destruct Hnorm1. destruct Hnorm.
  split; auto.
    apply _congr_app with (v1:=v1); auto.
Qed.

Lemma congr_let : forall e1 e2 v1 u,
  expr (exp_let e1 e2) ->
  normalize e1 v1 ->
  normalize (exp_let v1 e2) u ->
  normalize (exp_let e1 e2) u.
Proof.
  intros e1 e2 v1 u He Hnorm1 Hnorm.
  destruct Hnorm1. destruct Hnorm.
  split; auto.
    apply _congr_let with (v1:=v1); auto.
Qed.

Lemma congr_fst : forall e v T1 T2,
  typing nil nil e (typ_with T1 T2) ->
  normalize e v ->
  exists e1, exists e2, bigstep_red (exp_fst e) e1 /\ v = exp_apair e1 e2.
Proof.
  intros e v T1 T2 Htyping Hnorm.
  destruct Hnorm as [Hbrc Hv].
  induction Hbrc; intros.
    apply canonical_form_with in Htyping; auto.
    destruct Htyping as [e1 [e2 Htyping]]; subst. 
    inversion Hv; subst.
    exists(e1). exists(e2).
    split; eauto.

    destruct (@IHHbrc) as [e1 [e2 [Hbrc' Heq]]]; auto.
       apply preservation with (e:=e); auto.
    exists (e1). exists(e2).
    split; auto.
         apply bigstep_red_trans with (e':=exp_fst e'); auto.
Qed.

Lemma congr_snd : forall e v T1 T2,
  typing nil nil e (typ_with T1 T2) ->
  normalize e v ->
  exists e1, exists e2, bigstep_red (exp_snd e) e2 /\ v = exp_apair e1 e2.
Proof.
  intros e v T1 T2 Htyping Hnorm.
  destruct Hnorm as [Hbrc Hv].
  induction Hbrc; intros.
    apply canonical_form_with in Htyping; auto.
    destruct Htyping as [e1 [e2 Htyping]]; subst. 
    inversion Hv; subst.
    exists(e1). exists(e2).
    split; eauto.

    destruct (@IHHbrc) as [e1 [e2 [Hbrc' Heq]]]; auto.
       apply preservation with (e:=e); auto.
    exists (e1). exists(e2).
    split; auto.
         apply bigstep_red_trans with (e':=exp_snd e'); auto.
Qed.

Lemma red_value__eq_value : forall v v',
  value v ->
  normalize v v' ->
  v = v'.
Proof.
  intros v v' Hv Hnorm.
  destruct Hnorm as [Hbrc Hv'].
  induction Hbrc; auto.
    apply value_unred in Hv.
    contradict Hv; auto.
      exists(e'). auto.
Qed.

Lemma red_preserved_under_typsubst: forall X T e1 e2,
   red e1 e2 ->
   type T ->
   red (subst_te X T e1) (subst_te X T e2).
Proof.
  intros X T e1 e2 Hrc Ht.
  generalize dependent T.
  induction Hrc; intros; simpl; auto.
    rewrite subst_te_open_ee. apply red_abs; auto.
      assert (exp_abs (subst_tt X T0 T) (subst_te X T0 e1) = (subst_te X T0 (exp_abs T e1))). auto.
      rewrite H1.
      apply subst_te_expr; auto.
    rewrite subst_te_open_te; auto. apply red_tabs; auto.
      assert (exp_tabs (subst_te X T0 e1) = (subst_te X T0 (exp_tabs e1))). auto.
      rewrite H1.
      apply subst_te_expr; auto.
    apply red_let_cong; auto.
      assert (exp_let (subst_te X T e1) (subst_te X T e2) = (subst_te X T (exp_let e1 e2))). auto.
      rewrite H0.
      apply subst_te_expr; auto.
    rewrite subst_te_open_ee; auto. 
    apply red_let_beta; auto.
      assert (exp_let (exp_bang (subst_te X T e1)) (subst_te X T e2) = (subst_te X T (exp_let (exp_bang e1) e2))). auto.
      rewrite H0.
      apply subst_te_expr; auto.
Qed.

Lemma red_preserved_under_expsubst: forall x e0 e1 e2,
   red e1 e2 ->
   expr e0 ->
   red (subst_ee x e0 e1) (subst_ee x e0 e2).
Proof.
  intros x e0 e1 e2 Hrc He.
  generalize dependent e0.
  induction Hrc; intros; simpl; auto.
    rewrite subst_ee_open_ee; auto. apply red_abs; auto.
      assert (exp_abs T (subst_ee x e0 e1) = (subst_ee x e0 (exp_abs T e1))). auto.
      rewrite H1.
      apply subst_ee_expr; auto.
    rewrite subst_ee_open_te; auto. apply red_tabs; auto.
      assert (exp_tabs (subst_ee x e0 e1) = (subst_ee x e0 (exp_tabs e1))). auto.
      rewrite H1.
      apply subst_ee_expr; auto.
    apply red_let_cong; auto.
      assert (exp_let (subst_ee x e0 e1) (subst_ee x e0 e2) = (subst_ee x e0 (exp_let e1 e2))). auto.
      rewrite H0.
      apply subst_ee_expr; auto.
    rewrite subst_ee_open_ee; auto. 
    apply red_let_beta; auto.
      assert (exp_let (exp_bang (subst_ee x e0 e1)) (subst_ee x e0 e2) = (subst_ee x e0 (exp_let (exp_bang e1) e2))). auto.
      rewrite H0.
      apply subst_ee_expr; auto.
Qed.

Lemma preservation_normalization : forall E D e v T,
  typing E D e T ->
  normalize e v ->
  typing E D v T.
Proof.
  intros E D e v T typ norm.
  generalize dependent T.
  destruct norm as [Hbrc Hv].
  induction Hbrc; intros T typ; inversion typ; subst; auto; try solve [inversion H].
    apply IHHbrc; auto. apply preservation with (e:=exp_app e1 e2); auto.
    apply IHHbrc; auto. apply preservation with (e:=exp_tapp e1 T0); auto.
    apply IHHbrc; auto. apply preservation with (e:=exp_let e1 e2); auto.
    apply IHHbrc; auto. apply preservation with (e:=exp_fst e0); auto.
    apply IHHbrc; auto. apply preservation with (e:=exp_snd e0); auto.
Qed.

Lemma FrTyping__absvalue : forall L V E D e1 T1,
  wf_typ E V ->
  (forall x : atom, x `notin` L -> typing ([(x, bind_typ V)] ++ E) D (open_ee e1 x) T1) ->
  value (exp_abs V e1).
Proof.
  intros.
  apply value_abs.
     apply expr_abs with (L:=L); auto.
          eapply type_from_wf_typ with (E:=E); eauto.
          intros x Hfv_L. apply H0 in Hfv_L.
            apply typing_regular in Hfv_L. decompose [and] Hfv_L. auto.
Qed.

Lemma FrTyping__labsvalue : forall L V E D e1 T1,
  wf_typ E V ->
  (forall x : atom, x `notin` L -> typing E ([(x, lbind_typ V)] ++ D) (open_ee e1 x) T1) ->
  value (exp_abs V e1).
Proof.
  intros.
  apply value_abs.
     apply expr_abs with (L:=L); auto.
          eapply type_from_wf_typ with (E:=E); eauto.
          intros x Hfv_L. apply H0 in Hfv_L.
            apply typing_regular in Hfv_L. decompose [and] Hfv_L. auto.
Qed.

Lemma FrTyping__tabsvalue : forall L E D e1 T1,
  (forall X : atom,  X `notin` L -> typing ([(X, bind_kn)] ++ E) D (open_te e1 X) (open_tt T1 X)) ->
  value (exp_tabs e1).
Proof.
  intros.
  apply value_tabs.
    apply expr_tabs with (L:=L); auto.
        intros. apply H in H0.
            apply typing_regular in H0. decompose [and] H0; auto.
Qed.

(* ********************************************************************** *)
(* weaken stronger *)

Lemma rsubst_stronger : forall E E' rsubst rsubst' X R,
  wf_rho_subst (E'++[(X,bind_kn)]++E) (rsubst'++[(X,R)]++rsubst) ->
  ddom_env E [=] dom rsubst ->
  ddom_env E' [=] dom rsubst' ->
  X `notin` (fv_env E `union` fv_env E')->
  wf_rho_subst (E'++E) (rsubst'++rsubst).
Proof.
  intros E E' rsubst rsubst' X R Hwf_rsubst HdomE HdomE' HX.
  remember (E'++[(X,bind_kn)]++E) as G.
  remember (rsubst'++[(X,R)]++rsubst) as rG.
  generalize dependent E'.
  generalize dependent rsubst'.
  (wf_rho_subst_cases (induction Hwf_rsubst) Case); intros; subst.
  Case "wf_rho_subst_empty".
    contradict HeqG; auto.
  Case "wf_rho_subst_srel".
    apply one_eq_app in HeqG. destruct HeqG as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      apply one_eq_app in HeqrG. destruct HeqrG as [[rE'' [rEQ1 rEQ2]] | [rEQ1 rEQ2]]; subst.
        simpl_env.
        apply wf_rho_subst_srel; auto.
          apply IHHwf_rsubst; simpl in *; auto.
            apply dom_rho_subst in Hwf_rsubst.
            apply ddom_dom__inv with (X:=X0)(b:=R); auto.
              apply dom__ddom in H. rewrite Hwf_rsubst in H. simpl_env in H. auto.

        inversion rEQ2; subst. 
        simpl_env in H. destruct_notin.
        contradict NotInTac0; auto.

      apply one_eq_app in HeqrG. destruct HeqrG as [[rE'' [rEQ1 rEQ2]] | [rEQ1 rEQ2]]; subst.
        simpl_env in HdomE'.
        assert (X0 `notin` (singleton X0 `union` dom rE'') -> False).
          intro. destruct_notin. contradict NotInTac0; auto.
        rewrite <- HdomE' in H0.
        contradict H0; auto.

        inversion EQ2. inversion rEQ2. subst. auto.
  Case "wf_rho_subst_skip".
    apply one_eq_app in HeqG. destruct HeqG as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      simpl in HX. simpl_env in *. 
      apply wf_rho_subst_skip; auto.
        apply IHHwf_rsubst; auto.
          rewrite <- HdomE'. simpl. clear. fsetdec.
        apply wf_typ_strengthening_typ in H0; auto.

      inversion EQ2.
Qed.

Lemma rsubst_weaken : forall E E' rsubst rsubst' X R,
  wf_rho_subst (E'++E) (rsubst'++rsubst) ->
  ddom_env E [=] dom rsubst ->
  ddom_env E' [=] dom rsubst' ->
  X `notin` (dom E `union` dom E')->
  wf_rho_subst (E'++[(X,bind_kn)]++E) (rsubst'++[(X,R)]++rsubst).
Proof.
  intros E E' rsubst rsubst' X R Hwf_rsubst HdomE HdomE' HX.
  remember (E'++E) as G.
  remember (rsubst'++rsubst) as rG.
  generalize dependent E'.
  generalize dependent rsubst'.
  (wf_rho_subst_cases (induction Hwf_rsubst) Case); intros; subst.
  Case "wf_rho_subst_empty".
    destruct rsubst.
      destruct rsubst'; inversion HeqrG.
         destruct E.
            destruct E'; inversion HeqG.
              rewrite_env ([(X, bind_kn)]++nil).
              rewrite_env ([(X, R)]++nil).
              eapply wf_rho_subst_srel with (E:=(@nil (atom*binding))) (X:=X) (rsubst:=rho_nil) (R:=R); eauto.
          destruct E'; inversion HeqG.
      destruct rsubst'; inversion HeqrG.
  Case "wf_rho_subst_srel".
    apply one_eq_app in HeqG. destruct HeqG as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      apply one_eq_app in HeqrG. destruct HeqrG as [[rE'' [rEQ1 rEQ2]] | [rEQ1 rEQ2]]; subst.
        simpl_env.
        apply wf_rho_subst_srel; auto.
          apply IHHwf_rsubst; auto.
            apply ddom_dom__inv with (X:=X0)(b:=R); auto.
               apply dom__ddom in H.
               apply dom_rho_subst in Hwf_rsubst.
               rewrite Hwf_rsubst in H. simpl_env in H. destruct_notin. auto.

        simpl_env in HdomE'.
        assert (X0 `notin` (singleton X0 `union` ddom_env E'') -> False).
          intro. destruct_notin. contradict NotInTac0; auto.
        rewrite HdomE' in H0.
        contradict H0; auto.

    apply one_eq_app in HeqrG. destruct HeqrG as [ [rE'' [rEQ1 rEQ2]] | [rEQ1 rEQ2]]; subst.
      simpl_env in HdomE'.
      assert (X0 `notin` (singleton X0 `union` dom rE'') -> False).
          intro. destruct_notin. contradict NotInTac0; auto.
      rewrite <- HdomE' in H0.
      contradict H0; auto.

      simpl. simpl_env.
      apply wf_rho_subst_srel; auto.
  Case "wf_rho_subst_skip".
    apply one_eq_app in HeqG. destruct HeqG as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      simpl_env. apply wf_rho_subst_skip; auto.
        apply wf_typ_weakening; auto.
          apply uniq_insert_mid; auto.
            apply wf_rho_subst__uniq in Hwf_rsubst.
            decompose [and] Hwf_rsubst; auto.    

      assert (dom rsubst' [=] ddom_env nil). fsetdec.
      apply dom_empty_inv in H1. subst.
      simpl_env in *. apply wf_rho_subst_srel; auto.
Qed.

Lemma rsubst_weaken_head : forall E rsubst X R,
  wf_rho_subst E rsubst ->
  ddom_env E [=] dom rsubst ->
  X `notin` (dom E)->
  wf_rho_subst ([(X,bind_kn)]++E) ([(X,R)]++rsubst).
Proof.
  intros E rsubst X R Hwf_rsubst HdomE HX.
    apply rsubst_weaken with (E:=E) (E':=(@nil (atom*binding))) (rsubst:=rsubst) (rsubst':=rho_nil) (R:=R) (X:=X); simpl_env; eauto.
Qed.  

(* ********************************************************************** *)
(** * Inversion *)

Lemma wft_arrow_inv : forall E T1 T2,
  wf_typ E (typ_arrow T1 T2) ->
  wf_typ E T1 /\ wf_typ E T2.
Proof.
  intros E T1 T2 Wft.
  remember (typ_arrow T1 T2) as T.
  generalize dependent T1.
  generalize dependent T2.
  induction Wft; intros; subst; try solve [inversion HeqT].
    inversion HeqT; subst; auto.
Qed.

Lemma wft_all_inv : forall E T1,
  wf_typ E (typ_all T1) ->
  uniq E ->
  (forall X,
    X `notin` dom E `union` fv_tt T1 ->
    wf_typ ([(X, bind_kn)]++E) (open_tt T1 X)).
Proof.
  intros E T1 Wft.
  remember (typ_all T1) as T.
  generalize dependent T1.
  induction Wft; intros; subst; try solve [inversion HeqT].
    inversion HeqT; subst.
    pick fresh Y.
    assert (Y `notin` L) as J. auto.
    apply H in J.
    apply wf_typ_rename with (y:=X) in J; auto.
Qed.

Lemma wft_bang_inv : forall E T1,
  wf_typ E (typ_bang T1)->
  wf_typ E T1.
Proof.
  intros E T1 Wft.
  remember (typ_bang T1) as T.
  generalize dependent T1.
  induction Wft; intros; subst; try solve [inversion HeqT].
    inversion HeqT; subst; auto.
Qed.

Lemma wft_with_inv : forall E T1 T2,
  wf_typ E (typ_with T1 T2)->
  wf_typ E T1 /\ wf_typ E T2.
Proof.
  intros E T1 T2 Wft.
  remember (typ_with T1 T2) as T.
  generalize dependent T1.
  generalize dependent T2.
  induction Wft; intros; subst; try solve [inversion HeqT].
    inversion HeqT; subst; auto.
Qed.

Lemma wf_typ_from_lbinds_typ : forall x U E lE,
  wf_lenv E lE ->
  binds x (lbind_typ U) lE ->
  wf_typ E U.
Proof with auto using wf_typ_weaken_head.
  induction 1; intros J; analyze_binds_uniq J...
    apply uniq_push; auto.
      apply uniq_from_wf_lenv in H; auto.
  inversion BindsTacVal. subst...
Qed.

Lemma wf_env_strengthening_typ : forall X E F,
  wf_env (F ++ [(X, bind_kn)] ++ E) ->
  X `notin` fv_env F ->
  wf_env (F ++ E).
Proof with eauto using wf_typ_strengthening_typ.
  induction F; intros Wf_env XnF; inversion Wf_env; subst; simpl_env in *...
    simpl in XnF.
    eapply wf_env_typ; eauto using wf_typ_strengthening_typ.
Qed.

Lemma lenv_split_strengthening_typ: forall E X G D1 D2 D3,
  lenv_split (E ++ [(X, bind_kn)] ++ G) D1 D2 D3 ->
  X `notin` fv_env E `union` fv_lenv D3 ->
  lenv_split (E ++ G) D1 D2 D3.
Proof.
  intros E X G D1 D2 D3 S.
  remember (E ++ [(X, bind_kn)] ++ G) as G0.
  generalize dependent E. generalize dependent G. generalize dependent X.
  (lenv_split_cases (induction S) Case); intros X G1 E1 EQ NIN; subst.
  Case "lenv_split_empty".
    apply lenv_split_empty.
     apply wf_env_strengthening_typ in H; auto.
  Case "lenv_split_left".
    simpl in NIN.
    apply lenv_split_left; eauto.
      apply wf_typ_strengthening_typ in H1; auto.
  Case "lenv_split_right".
    simpl in NIN.
    apply lenv_split_right; eauto.
      apply wf_typ_strengthening_typ in H1; auto.
Qed.

Lemma lenv_split_strengthening_typ_tail: forall X G D1 D2 D3,
  lenv_split ([(X, bind_kn)] ++ G) D1 D2 D3 ->
  X `notin` fv_lenv D3 ->
  lenv_split G D1 D2 D3.
Proof.
  intros X G D1 D2 D3 S NIN.
  rewrite_env (nil++[(X, bind_kn)] ++ G) in S.
  apply lenv_split_strengthening_typ in S; auto.
Qed.

Lemma fv_lenv_split: forall G E1 E2 E3,
  lenv_split G E1 E2 E3  -> 
  fv_lenv E3 [=] fv_lenv E1 `union` fv_lenv E2.
Proof.
  intros E1 E2 E3 G S.
  induction S; simpl; try fsetdec. 
Qed.

Lemma lenv_split_strengthening_tail: forall G1 x T D1 D2 D3,
  lenv_split ([(x, bind_typ T)] ++ G1) D1 D2 D3 ->
  lenv_split (G1) D1 D2 D3.
Proof.
  intros G1 x T D1 D2 D3 H.
  rewrite_env (nil ++ [(x, bind_typ T)] ++ G1) in H.
  apply lenv_split_strengthening in H; auto.
Qed.

Lemma subst_te_commute : forall X X' T T' e,
  X `notin` fv_tt T' ->
  X' `notin` fv_tt T ->
  X <> X' ->
  subst_te X T (subst_te X' T' e) = subst_te X' T' (subst_te X T e).
Proof with repeat progress
             (rewrite <- subst_te_fresh; [auto | solve [auto]]).
  intros X X' T T' e WfT WfT' Neq.
  (exp_cases (induction e) Case); simpl in *;
    try solve [ auto |
                rewrite IHe; auto |
                rewrite IHe1; rewrite IHe2; auto ]...
  Case "exp_abs".
    rewrite IHe; auto.
    rewrite subst_tt_commute; auto.
  Case "exp_tapp".
    rewrite IHe; auto.
    rewrite subst_tt_commute; auto.
Qed.

Lemma notin_fv_lenv_wfle : forall E lE (X : atom),
  wf_lenv E lE ->
  X `notin` dom E ->
  X `notin` dom lE ->
  X `notin` fv_lenv lE.
Proof.
  intros E lE X Wfle XnE XnlE.
  (wf_lenv_cases (induction Wfle) Case); simpl; auto.
  Case "wf_lenv_typ".
    apply notin_fv_wf with (X:=X) in H1; auto.
Qed.

Lemma gamma_subst_disjoint_exp : forall gsubst e,
   (forall x, x `in` dom gsubst -> x `notin` fv_ee e) ->
   apply_gamma_subst gsubst e = e.
Proof.
  induction gsubst; intros e FV; simpl; auto.
    destruct a.
    rewrite <- subst_ee_fresh; eauto.
      rewrite IHgsubst; auto.
        intros x Fvx.
        apply FV. simpl. fsetdec.
      apply FV. simpl. fsetdec.
Qed.

Lemma lenv_split_in_left: forall G D1 D2 D3 x,
  lenv_split G D1 D2 D3 ->
  x `in` dom D1 ->
  x `in` dom D3.
Proof.
  intros G D1 D2 D3 x Split Fv.
  (lenv_split_cases (induction Split) Case); intros; simpl; auto.
  Case "lenv_split_left".
    simpl_env in *.
    assert (x `in` singleton x0 \/ x `in` dom D1) as J. fsetdec.
    destruct J as [J | J]; simpl in J; fsetdec.
Qed.

Lemma lenv_split_in_right: forall G D1 D2 D3 x,
  lenv_split G D1 D2 D3 ->
  x `in` dom D2 ->
  x `in` dom D3.
Proof.
  intros G D1 D2 D3 x Split Fv.
  (lenv_split_cases (induction Split) Case); intros; simpl; auto.
  Case "lenv_split_right".
    simpl_env in *.
    assert (x `in` singleton x0 \/ x `in` dom D2) as J. fsetdec.
    destruct J as [J | J]; simpl in J; fsetdec.
Qed.

Lemma apply_delta_subst_env_dom : forall dsubst E,
  dom E [=] dom (apply_delta_subst_env dsubst E).
Proof.
  induction E; intros; simpl; auto.
    destruct a. 
    destruct b; simpl; rewrite <- IHE; fsetdec.
Qed.

Lemma apply_delta_subst_lenv_dom : forall dsubst D,
  dom D [=] dom (apply_delta_subst_lenv dsubst D).
Proof.
  induction D; intros; simpl; auto.
    destruct a. 
    destruct l; simpl; rewrite <- IHD; fsetdec.
Qed.

(********** disjdom **************)
Definition disjdom (E : atoms) (F : atoms) : Prop :=
  (forall x, x `in` E -> x `notin` F) /\ (forall x, x `in` F -> x `notin` E).

Lemma disjdom_sym_1 :
  forall E F,
  disjdom E F ->
  disjdom F E.
Proof. 
  unfold disjdom. 
  intros; split; intros; destruct H; auto.
Qed.

Lemma disjdom_sym :
  forall E F,
  disjdom E F <-> disjdom F E.
Proof. intuition auto using disjdom_sym_1. Qed.

Lemma disjdom_nil_1 :
  forall E,
  disjdom {} E.
Proof. 
   unfold disjdom. 
   intro; split; intros; auto.
     contradict H; auto.
Qed.

Lemma disjdom_one_1 :
  forall x F,
  disjdom {{x}} F ->
  x `notin` F.
Proof. 
  unfold disjdom. simpl. intros.
  destruct H. auto.
Qed.

Lemma disjdom_one_2 :
  forall x F,
  x `notin` F ->
  disjdom {{x}} F.
Proof. 
  unfold disjdom. simpl. intros.
  split; intros; fsetdec.
Qed.

Lemma disjdom_one_l :
  forall x E,
  disjdom {{x}} E <-> x `notin` E.
Proof. unfold disjdom. simpl. 
  split; intros.
    destruct H; auto.
    split; intros; fsetdec.
Qed.

Lemma disjdom_one_r :
  forall x E,
  disjdom E {{x}} <-> x `notin` E.
Proof. intros. rewrite disjdom_sym. apply disjdom_one_l. Qed.

Lemma disjdom_cons_1 :
  forall x E F,
  disjdom (add x E) F ->
  x `notin` F.
Proof. unfold disjdom. 
  intros. destruct H; auto.
Qed.

Lemma disjdom_cons_2 :
  forall x E F,
  disjdom (add x E) F ->
  disjdom E F.
Proof. unfold disjdom. simpl. 
  intros; split; intros.
    destruct H; auto.
    destruct H. apply H1 in H0. fsetdec.
Qed.

Lemma disjdom_cons_3 :
  forall x E F,
  disjdom E F ->
  x `notin` F ->
  disjdom (add x E) F.
Proof. unfold disjdom. simpl. 
  intros; split; intros.
    destruct H. 
    assert (x0 `in` {{x}} \/ x0 `in` E) as J. fsetdec.
    destruct J as [J | J].
      fsetdec.
      apply H. fsetdec.
    destruct H.
      destruct (x0 == x); subst.
        contradict H1; auto.
        apply H2 in H1; auto.
Qed.

Lemma disjdom_cons_l :
  forall x E F,
  disjdom (add x E) F <-> x `notin` F /\ disjdom E F.
Proof.
  split.
  eauto using disjdom_cons_1, disjdom_cons_2.
  intros [? ?]. auto using disjdom_cons_3.
Qed.

Lemma disjdom_cons_r :
  forall x E F,
  disjdom F (add x E) <-> x `notin` F /\ disjdom E F.
Proof. intros. rewrite disjdom_sym. apply disjdom_cons_l. Qed.

Lemma disjdom_app_1 :
  forall E F G,
  disjdom (E `union` F) G ->
  disjdom E G.
Proof. unfold disjdom. intros. 
  destruct H as [H1 H2].
  split; intros; auto.
    apply H2 in H. fsetdec.  
Qed.

Lemma disjdom_app_2 :
  forall E F G,
  disjdom (E `union` F) G ->
  disjdom F G.
Proof. unfold disjdom. intros. 
  destruct H as [H1 H2].
  split; intros; auto.
    apply H2 in H. fsetdec.  
Qed.

Lemma disjdom_app_3 :
  forall E F G,
  disjdom E G ->
  disjdom F G ->
  disjdom (E `union` F) G.
Proof. unfold disjdom. intros.
  destruct H as [H1 H2].
  destruct H0 as [H01 H02].
  split; intros; auto.
    assert (x `in` E \/ x `in` F) as J. fsetdec.
    destruct J as [J | J].
    apply H1 in J. auto.
    apply H01 in J. auto.
Qed.

Lemma disjdom_app_l :
  forall E F G,
  disjdom (E `union` F) G <-> disjdom E G /\ disjdom F G.
Proof.
  intuition eauto 2 using
    disjdom_app_1, disjdom_app_2, disjdom_app_3.
Qed.

Lemma disjdom_app_r :
  forall E F G,
  disjdom G (E `union` F) <-> disjdom E G /\ disjdom F G.
Proof. intros. rewrite disjdom_sym. apply disjdom_app_l. Qed.

(* ********************************************************************** *)
(*                                            Properties                                             *)
(* ********************************************************************** *)
(** * Properties about the free variables of terms *)

Lemma notin_dom__notin_fv_lenv : forall E lE X,
  wf_lenv E lE ->
  X `notin` dom E `union` dom lE ->
  X `notin` fv_lenv lE.
Proof.
  intros E lE X Wfg Xnotin.
  induction Wfg; auto.
    simpl in *. eauto using notin_fv_wf.
Qed.

Lemma disjoint_wf_lenv : forall E lE,
  wf_lenv E lE ->
  disjoint E lE.
Proof.
  intros E lE Wfle.
  induction Wfle; auto.
Qed.

Lemma in_dec : forall x A,
  {x `in` A} + {x `notin` A}.
Proof. 
  intros x A.
  apply AtomSetProperties.In_dec.
Qed. 

Lemma in_fv_wf : forall E (X : atom) T,
  wf_typ E T ->
  X `in` fv_tt T ->
  X `in` dom E.
Proof.
  intros E X T Wft Fv.
  destruct (@in_dec X (dom E)); auto.
    apply notin_fv_wf with (X:=X) in Wft; auto.
    contradict Fv; auto.
Qed.

Lemma notin_fv_ee_typing : forall E D T (y : atom) e,
  typing E D e T ->
  y `notin` dom E `union` dom D ->
  y `notin` fv_ee e.
Proof with auto.
  (typing_cases (induction 1) Case); intros Fr; simpl...
  Case "typing_var".
    assert (x `in` dom E) by eauto using binds_In...
    fsetdec.
  Case "typing_abs".
    pick fresh x.
    apply (@notin_fv_ee_open_ee_inv x)...
  Case "typing_app".
    assert (dom D3 [=] dom D1 `union` dom D2) as EQ.
      apply dom_lenv_split in H1; auto.
    fsetdec.
  Case "typing_tabs".
    pick fresh x.
    apply (@notin_fv_ee_open_te_inv x)...
  Case "typing_let".
    pick fresh x.
    assert (dom D3 [=] dom D1 `union` dom D2) as EQ.
      apply dom_lenv_split in H2; auto.
    rewrite EQ in Fr.
    assert (x `notin` L) as xnL. auto.
    assert (y `notin` union (dom ([(x, bind_typ T1)]++E)) (dom D2)) as J. 
      simpl_env. destruct_notin. clear - NotInTac Fr NotInTac16. fsetdec.
    apply H1 in xnL; auto.
    apply notin_fv_ee_open_ee_inv in xnL; auto.
Qed.

Lemma notin_fv_tt_typing : forall E D T (X : atom) e,
  typing E D e T ->
  X `notin` dom E ->
  X `notin` fv_tt T.
Proof with auto.
  (typing_cases (induction 1) Case); intros Fr; simpl...
  Case "typing_var".
    apply wf_typ_from_binds_typ with (E:=E) in H0; auto.
    apply notin_fv_wf with (X:=X) in H0; auto.
  Case "typing_lvar".
    inversion H; subst.
    apply notin_fv_wf with (X:=X) in H7; auto.
  Case "typing_abs".
    pick fresh y.
    lapply (H1 y); [ intros J | auto ].
    assert (X `notin` fv_tt T1) by eauto using notin_fv_wf.
    eauto.
  Case "typing_app".
    apply IHtyping1 in Fr.
    simpl in Fr. auto.
  Case "typing_tabs".
    pick fresh y.
    apply (@notin_fv_tt_open_tt_inv y)...
  Case "typing_tapp".
    apply notin_fv_wf with (X:=X) in H0; auto.
    apply IHtyping in Fr. simpl in Fr.
    apply notin_fv_tt_open_typ_tt; auto.
  Case "typing_let".
    pick fresh y.
    lapply (H1 y); [ intros J | auto ].
    assert (X `notin` fv_tt T1) by eauto using notin_fv_wf.
    eauto.
  Case "typing_fst".
    apply IHtyping in Fr.
    simpl in Fr. auto.
  Case "typing_snd".
    apply IHtyping in Fr.
    simpl in Fr. auto.
Qed.

Lemma in_fv_te_typing : forall E lE T (X : atom) e,
  typing E lE e T ->
  X `in` fv_te e ->
  X `in` dom E.
Proof with auto.
  intros E lE T X e Typ Xnotin.
  destruct (@in_dec X (dom E)); auto.
    apply notin_fv_te_typing with (X:=X) in Typ; auto.
    contradict Xnotin; auto.
Qed.

Lemma in_fv_ee_typing : forall E lE T (x : atom) e,
  typing E lE e T ->
  x `in` fv_ee e ->
  x `in` dom E `union` dom lE.
Proof with auto.
  intros E lE T x e Typ xnotin.
  destruct (@in_dec x (dom E `union` dom lE)); auto.
    apply notin_fv_ee_typing with (y:=x) in Typ; auto.
    contradict xnotin; auto.
Qed.

Lemma in_fv_tt_typing : forall E lE T (X : atom) e,
  typing E lE e T ->
  X `in` fv_tt T ->
  X `in` dom E.
Proof with auto.
  intros E lE T X e Typ Xnotin.
  destruct (@in_dec X (dom E)); auto.
    apply notin_fv_tt_typing with (X:=X) in Typ; auto.
    contradict Xnotin; auto.
Qed.

Lemma fv_in_open_ee_inv : forall e (x y:atom) k,
  y `in` fv_ee (open_ee_rec k x e) ->
  y <> x ->
  y `in` fv_ee e.
Proof.
  induction e; simpl; intros x y kk Fr Notin; eauto.
    destruct (kk==n); subst; simpl in *; auto.
      contradict Fr; auto.

    assert (y `in` (fv_ee (open_ee_rec kk x e1)) \/y `in` (fv_ee (open_ee_rec kk x e2))) as J.
      fsetdec.
    destruct J as [J | J]; eauto.

    assert (y `in` (fv_ee (open_ee_rec kk x e1)) \/y `in` (fv_ee (open_ee_rec (S kk) x e2))) as J.
      fsetdec.
    destruct J as [J | J]; eauto.

    assert (y `in` (fv_ee (open_ee_rec kk x e1)) \/y `in` (fv_ee (open_ee_rec kk x e2))) as J.
      fsetdec.
    destruct J as [J | J]; eauto.
Qed.

Lemma fv_in_open_te_inv : forall e (X y:atom) k,
  y `in` fv_ee (open_te_rec k X e) ->
  y <> X ->
  y `in` fv_ee e.
Proof.
  induction e; simpl; intros X y kk Fr Notin; eauto.
    assert (y `in` (fv_ee (open_te_rec kk X e1)) \/y `in` (fv_ee (open_te_rec kk X e2))) as J.
      fsetdec.
    destruct J as [J | J]; eauto.

    assert (y `in` (fv_ee (open_te_rec kk X e1)) \/y `in` (fv_ee (open_te_rec kk X e2))) as J.
      fsetdec.
    destruct J as [J | J]; eauto.

    assert (y `in` (fv_ee (open_te_rec kk X e1)) \/y `in` (fv_ee (open_te_rec kk X e2))) as J.
      fsetdec.
    destruct J as [J | J]; eauto.
Qed.

Lemma in_lfv_ee_typing : forall E D T (y : atom) e,
  typing E D e T ->
  y `in` dom D ->
  y `in` fv_ee e.
Proof with auto.
  (typing_cases (induction 1) Case); intros Fr; simpl...
  Case "typing_var".
    contradict Fr; auto.
  Case "typing_lvar".
    simpl in Fr. fsetdec.
  Case "typing_abs".
    pick fresh x.
    assert (x `notin` L) as xnotinL. auto.
    apply H1 in xnotinL; auto.
      apply fv_in_open_ee_inv in xnotinL; auto.
      simpl. fsetdec. 
  Case "typing_app".
    apply dom_lenv_split in H1.
     rewrite H1 in Fr.
     assert (y `in` dom D1 \/ y `in` dom D2) as J. fsetdec.
     destruct J as [J | J]; auto.
  Case "typing_tabs".
    pick fresh X.
    assert (X `notin` L) as XnotinL. auto.
    apply H0 in XnotinL; auto.
      apply fv_in_open_te_inv in XnotinL; auto.
  Case "typing_let".
    apply dom_lenv_split in H2.
    rewrite H2 in Fr.
    assert (y `in` dom D1 \/ y `in` dom D2) as J. fsetdec.
    destruct J as [J | J]; auto.
      pick fresh x.
      assert (x `notin` L) as xnotinL. auto.
      apply H1 in xnotinL; auto.
      apply fv_in_open_ee_inv in xnotinL; auto.
Qed.

Lemma in_fv_tt_subst_tt : forall (X Y : atom) T1 T2,
  Y `in` fv_tt T2 ->
  X <> Y ->
  Y `in` fv_tt (subst_tt X T1 T2).
Proof.
  intros X Y T1 T2 H J.
  (typ_cases (induction T2) Case); simpl in *; auto.
  Case "typ_fvar".
    destruct (a==X); auto.
      subst. contradict H; auto.
  Case "typ_arrow".
    assert (Y `in` fv_tt T2_1 \/ Y `in` fv_tt T2_2) as JJ.
      fsetdec.
    destruct JJ as [JJ | JJ]; auto.
  Case "typ_with".
    assert (Y `in` fv_tt T2_1 \/ Y `in` fv_tt T2_2) as JJ.
      fsetdec.
    destruct JJ as [JJ | JJ]; auto.
Qed.

Lemma dom__gdom: forall x E,
  x `notin` dom E ->
  x `notin` gdom_env E.
Proof.
  induction E as [ | [x1 b1] E ]; simpl; intros H; auto.
  destruct b1; auto.
Qed.

Lemma fv_ee_open_ee_rec_sub_left : forall e e' k,
  fv_ee (open_ee_rec k e' e) [<=] (fv_ee e `union` fv_ee e').
Proof.
  induction e; simpl; intros; try solve [auto | fsetdec].
    destruct (k == n); subst; simpl; fsetdec.

    assert (J1:=@IHe1 e' k).
    assert (J2:=@IHe2 e' k).
    fsetdec.

    assert (J1:=@IHe1 e' k).
    assert (J2:=@IHe2 e' (S k)).
    fsetdec.

    assert (J1:=@IHe1 e' k).
    assert (J2:=@IHe2 e' k).
    fsetdec.
Qed.

Lemma fv_ee_open_ee_sub_left : forall e e',
  fv_ee (open_ee e e') [<=] (fv_ee e `union` fv_ee e').
Proof.
  intros; unfold open_ee.
  apply fv_ee_open_ee_rec_sub_left; auto.
Qed.  

Lemma fv_ee_open_ee_rec_sub_right : forall e e' k,
  (fv_ee e) [<=] fv_ee (open_ee_rec k e' e).
Proof.
  induction e; simpl; intros; try solve [auto | fsetdec].
    assert (J1:=@IHe1 e' k).
    assert (J2:=@IHe2 e' k).
    fsetdec.

    assert (J1:=@IHe1 e' k).
    assert (J2:=@IHe2 e' (S k)).
    fsetdec.

    assert (J1:=@IHe1 e' k).
    assert (J2:=@IHe2 e' k).
    fsetdec.
Qed.

Lemma fv_ee_open_ee_sub_right : forall e e',
  (fv_ee e) [<=] fv_ee (open_ee e e').
Proof.
  intros; unfold open_ee.
  apply fv_ee_open_ee_rec_sub_right; auto.
Qed.  

Lemma fv_ee_open_te_rec_eq : forall e T k,
  fv_ee (open_te_rec k T e) [=] (fv_ee e).
Proof.
  induction e; simpl; intros; try solve [auto | fsetdec].
Qed.

Lemma fv_ee_open_te_eq : forall e T,
  fv_ee (open_te e T) [=] (fv_ee e).
Proof.
  intros; unfold open_te.
  apply fv_ee_open_te_rec_eq; auto.
Qed.  

Lemma dom_sub_left : forall A (D1 D2:list (atom*A)),
  dom D1 [<=] dom D1 `union` dom D2.
Proof.
  intros. fsetdec.
Qed. 

Lemma dom_sub_right : forall A (D1 D2:list (atom*A)),
  dom D2 [<=] dom D1 `union` dom D2.
Proof.
  intros. fsetdec.
Qed.

Lemma open_ee_rec_inv : forall e e' i (x:atom),
  x `notin` ((fv_ee e) `union` (fv_ee e')) ->
  open_ee_rec i x e = open_ee_rec i x e' ->
  e = e'.
Proof.
  intros e e' n x Hfv Heq.
  generalize dependent x.
  generalize dependent n.
  generalize dependent e'.
  induction e; intros; destruct e'; simpl in *; 
    try solve [
       inversion Heq |
       destruct (n0===n); inversion Heq |
       destruct (n===n0); inversion Heq |
       inversion Heq; subst;
         rewrite IHe1 with (e':=e'1) (n:=n) (x:=x); auto;
         rewrite IHe2 with (e':=e'2) (n:=n) (x:=x); auto|
       inversion Heq; subst;
         rewrite IHe with (e':=e') (n:=n) (x:=x); auto|
       auto
       ].

    destruct (n0===n); subst; auto.
      destruct (n===n1); subst; auto.
        inversion Heq.
      destruct (n0===n1); subst; auto.
        inversion Heq.
    destruct (n0===n); subst; auto.
      injection Heq. intro J. rewrite J in Hfv.
      destruct_notin. contradict NotInTac; auto.
    destruct (n===n0); subst; auto.
      injection Heq. intro J. rewrite J in Hfv.
      destruct_notin. contradict NotInTac; auto.

    inversion Heq; subst;
      rewrite IHe with (e':=e') (n:=S n) (x:=x); auto.

    inversion Heq; subst.
      rewrite IHe1 with (e':=e'1) (n:=n) (x:=x); auto.
      rewrite IHe2 with (e':=e'2) (n:=S n) (x:=x); auto.
Qed.

Lemma open_tt_rec_inv : forall t t' i (X:atom),
  X `notin` ((fv_tt t) `union` (fv_tt t')) ->
  open_tt_rec i X t = open_tt_rec i X t' ->
  t = t'.
Proof.
  intros t t' n X Hfv Heq.
  generalize dependent X.
  generalize dependent n.
  generalize dependent t'.
  induction t; intros; destruct t'; simpl in *; 
    try solve [
       inversion Heq |
       destruct (n0===n); inversion Heq |
       destruct (n===n0); inversion Heq |
       inversion Heq; subst;
         rewrite IHt1 with (t':=t'1) (n:=n) (X:=X); auto;
         rewrite IHt2 with (t':=t'2) (n:=n) (X:=X); auto |
       auto
       ].

    destruct (n0===n); subst; auto.
      destruct (n===n1); subst; auto.
        inversion Heq.
      destruct (n0===n1); subst; auto.
        inversion Heq.
    destruct (n0===n); subst; auto.
      injection Heq. intro J. rewrite J in Hfv.
      destruct_notin. contradict NotInTac; auto.
    destruct (n===n0); subst; auto.
      injection Heq. intro J. rewrite J in Hfv.
      destruct_notin. contradict NotInTac; auto.
   inversion Heq; subst;
      rewrite IHt with (t':=t') (n:=S n) (X:=X); auto.
   inversion Heq; subst;
      rewrite IHt with (t':=t') (n:=n) (X:=X); auto.
Qed.

Lemma open_te_rec_inv : forall e e' i (X:atom),
  X `notin` ((fv_te e) `union` (fv_te e')) ->
  open_te_rec i X e = open_te_rec i X e' ->
  e = e'.
Proof.
  intros e e' n x Hfv Heq.
  generalize dependent x.
  generalize dependent n.
  generalize dependent e'.
  induction e; intros; destruct e'; simpl in *; 
    try solve [
       inversion Heq |
       destruct (n0===n); inversion Heq |
       destruct (n===n0); inversion Heq |
       inversion Heq; subst;
         rewrite IHe1 with (e':=e'1) (n:=n) (x:=x); auto;
         rewrite IHe2 with (e':=e'2) (n:=n) (x:=x); auto|
       inversion Heq; subst;
         rewrite IHe with (e':=e') (n:=n) (x:=x); auto|
       auto
       ].

    inversion Heq; subst.
      apply open_tt_rec_inv in H0; auto. 
      rewrite IHe with (e':=e') (n:=n) (x:=x); auto.
      subst; auto.

    inversion Heq; subst.
      rewrite IHe with (e':=e') (n:=S n) (x:=x); auto.

    inversion Heq; subst.
      rewrite IHe with (e':=e') (n:=n) (x:=x); auto.
      apply open_tt_rec_inv in H1; auto. 
      subst; auto.
Qed.

Lemma open_ee_expr : forall u e,
  expr e ->
  e = open_ee e u.
Proof.
  intros e He.
  unfold open_ee.
  apply open_ee_rec_expr; auto.
Qed.

Lemma bind_typ__in_gdom : forall E x T,
  binds x (bind_typ T) E ->
  x `in` gdom_env E.
Proof.
  induction E; intros x T Binds.
    inversion Binds.
    destruct a. destruct b; simpl.
       analyze_binds Binds. eauto.         
       analyze_binds Binds. eauto.
Qed.

Lemma in_fv_ee_typing' : forall E lE T (x : atom) e,
  typing E lE e T ->
  x `in` fv_ee e ->
  x `in` gdom_env E `union` dom lE.
Proof with auto.
  (typing_cases (induction 1) Case); intros Fr; simpl in Fr; simpl...
  Case "typing_var".
    assert (x0 `in` gdom_env E) by eauto using bind_typ__in_gdom...
    fsetdec.
  Case "typing_lvar".
    fsetdec.
  Case "typing_abs".
    pick fresh y.
    assert (y `notin` L) as ynL. auto.
    apply H1 in ynL.
      simpl in ynL. 
      destruct_notin.
      clear Fr NotInTac0 NotInTac2 NotInTac3 NotInTac4 NotInTac5 NotInTac6 NotInTac7 NotInTac8.
      fsetdec.

      apply fv_in_open_ee; auto.
  Case "typing_app".
    assert (dom D3 [=] dom D1 `union` dom D2) as EQ.
      apply dom_lenv_split in H1; auto.
    fsetdec.
  Case "typing_tabs".
    pick fresh y.
    assert (y `notin` L) as ynL. auto.
    apply H0 in ynL.
      simpl in ynL. 
      destruct_notin.
      clear Fr NotInTac0 NotInTac2 NotInTac3 NotInTac4 NotInTac5 NotInTac6 NotInTac7.
      fsetdec.

      apply fv_in_open_te; auto.
  Case "typing_let".
    assert (dom D3 [=] dom D1 `union` dom D2) as EQ.
      apply dom_lenv_split in H2; auto.
    rewrite EQ.
    assert (x `in` fv_ee e1 \/ x `in` fv_ee e2) as xine12. fsetdec.
    destruct xine12.
      apply IHtyping in H3. fsetdec.
      pick fresh y. 
      assert (y `notin` L) as ynL. auto.
      apply H1 in ynL; auto.
        simpl in ynL. 
        destruct_notin.
        clear Fr NotInTac0 NotInTac2 NotInTac3 NotInTac4 NotInTac5 NotInTac6 NotInTac7 NotInTac8.
        fsetdec.

        apply fv_in_open_ee; auto.
  Case "typing_apair".
    assert (x `in` fv_ee e1 \/ x `in` fv_ee e2) as xine12. fsetdec.
    destruct xine12; auto.
Qed.

Lemma gbinds_In_inv : forall x E,
  x `in` (gdom_env E) ->
  exists a, binds x (bind_typ a) E.
Proof.
  induction E as [ | y b F IH ]; intros J.
    simpl_alist in J. fsetdec.
    simpl_alist in J. destruct y.  destruct b0; simpl in J.
      apply F in J. destruct J as [t J].
      exists t. auto.

      assert (x `in` {{a}} \/ x `in` gdom_env b) as J'. fsetdec.
      destruct J' as [J' | J'].
        exists t.
        destruct (x==a); subst; auto.
          contradict J'; auto.

          apply F in J'. destruct J' as [t' J'].
          exists t'. auto.
Qed.

Lemma dbinds_In : forall E X,
  binds X (bind_kn) E ->
  X `in` ddom_env E.
Proof.
  induction E; intros X Binds.
    inversion Binds.

    destruct a.
    destruct b; simpl.
      analyze_binds Binds; eauto.       
      analyze_binds Binds; eauto.
Qed.

Lemma dnotin_fv_wf : forall E (X : atom) T,
  wf_typ E T ->
  X `notin` ddom_env E ->
  X `notin` fv_tt T.
Proof with auto.
  intros E X T Wf_typ.
  (wf_typ_cases (induction Wf_typ) Case); intros Fr; simpl...
  Case "wf_typ_var".
    assert (X0 `in` (ddom_env E)).
      eapply dbinds_In; eauto.     
    fsetdec.
  Case "wf_typ_all".
    pick fresh Y.
    apply (notin_fv_tt_open Y).
    apply H0; auto.
      simpl. fsetdec.
Qed.

Lemma notin_ddom_env: forall E y t,
  wf_env E ->
  binds y (bind_typ t) E ->
  y `notin` ddom_env E.
Proof.
  intros E y t Wfe Binds.
  generalize dependent y.
  generalize dependent t.
  induction Wfe; intros t y Binds; simpl.
    inversion Binds.
     
    destruct (y==X); subst.
      analyze_binds_uniq Binds.

      analyze_binds Binds.
      apply IHWfe in BindsTac. auto.

      analyze_binds Binds. eauto.
Qed.

Lemma wfe_dom_fv_env : forall E x,
  wf_env E ->
  x `notin` dom E ->
  x `notin` fv_env E.
Proof.
  intros E x Wfe.
  generalize dependent x.
  induction Wfe; intros; simpl in *; auto.
    destruct_notin.
    apply IHWfe in NotInTac0.
    apply notin_fv_wf with (X:=x0) in H; auto.
Qed.

Lemma wf_lenv_notin_fv_lenv : forall E D x T,
  wf_lenv E D ->
  binds x (bind_typ T) E ->
  x `notin` fv_lenv D.
Proof.
  intros E D x T Wfle Binds.
  generalize dependent x.
  generalize dependent T.
  induction Wfle; intros; simpl.
    fsetdec.

    destruct (x==x0); subst.
      apply binds_In in Binds.
      contradict Binds; auto.

      assert (x0 `notin` fv_tt T) as x0nT.
        apply dnotin_fv_wf with (E:=E); auto.
           eapply notin_ddom_env; eauto.
      apply IHWfle in Binds. auto.
Qed.

Lemma din_fv_wf : forall E (X : atom) T,
  wf_typ E T ->
  X `in` fv_tt T ->
  X `in` ddom_env E.
Proof with auto.
  intros E X T Wf_typ XinT.
  destruct (in_dec X (ddom_env E)); auto.
    apply dnotin_fv_wf with (X:=X) in Wf_typ; auto.
    contradict XinT; auto.
Qed.

(* ********************************************************************** *)
(** * Commuting properties about substitution and opening *)

Lemma open_tt_rec_commute' : forall T T' T'' (X : atom) k1 k2,
  k1 <> k2 ->
  type T' ->
  type T'' ->
  (open_tt_rec k1 T'' (open_tt_rec k2 T' T) =
    open_tt_rec k2 T' (open_tt_rec k1 T'' T)).
Proof with repeat progress (rewrite <- open_tt_rec_type; [auto | solve [auto]]).
  intros T T' T'' X k1 k2 Neq Typ Typ'.
  generalize dependent k1.
  generalize dependent k2.
  (typ_cases (induction T) Case); intros k2 k1 Neq; simpl in *;
    try solve [ auto |
                rewrite IHT; auto |
                rewrite IHT1; auto; rewrite IHT2; auto ].
  Case "typ_bvar".
    destruct (k2 == n); destruct (k1 == n); subst; simpl in *...
    intuition.
    destruct (n == n); subst; intuition.
    destruct (n == n); subst; intuition.
    destruct (k1 == n); destruct (k2 == n); subst; simpl in *; intuition.
Qed.

(********************************************************)
(* well found subst give envs *)

Lemma disjoint_lenv_split : forall A E D1 D2 D (F : list (atom*A)),
  lenv_split E D1 D2 D ->
  disjoint F D1 ->
  disjoint F D2 ->
  disjoint F D.
Proof.
  intros A E D1 D2 D F Split Disj1 Disj2.
  induction Split; auto.
    assert (disjoint F D3) as J.
      apply IHSplit; auto.
      destruct_uniq; auto.
    solve_uniq.

    assert (disjoint F D3) as J.
      apply IHSplit; auto.
      destruct_uniq; auto.
    solve_uniq.
Qed.

Lemma disjoint_lenv_split' : forall E lE1 lE2 lE3,
  lenv_split E lE1 lE2 lE3 ->
  disjoint lE1 lE2.
Proof.
  intros E lE1 lE2 lE3 Split.
  induction Split; auto.
    apply dom_lenv_split in Split.
    rewrite Split in H0.
    solve_uniq.

    apply dom_lenv_split in Split.
    rewrite Split in H0.
    solve_uniq.
Qed.

Lemma disjoint__lenv_split : forall E lE1 lE2,
  wf_lenv E lE1 ->
  wf_lenv E lE2 ->
  disjoint lE1 lE2 ->
  lenv_split E lE1 lE2 (lE1++lE2).
Proof.
  intros E lE1 lE2 Wfle1 Wfle2 Disj.
  induction lE1.
    simpl. apply wf_lenv_trivial_split; auto.

    destruct a. destruct l. 
    inversion Wfle1; subst.
    simpl_env in *. 
    apply lenv_split_left; auto.
      apply IHlE1; auto.
        solve_uniq.
      solve_uniq.
Qed.

Lemma disjoint_eq : forall A B C (E : list (atom * A)) (D1 : list (atom * B)) (D2: list (atom * C)),
  disjoint D1 E ->
  dom D1 [=] dom D2 ->
  disjoint D2 E.
Proof.
  induction E; intros D1 D2 Disj EQ; solve_uniq.
Qed.

Lemma disjoint_sub : forall A B C (E : list (atom * A)) (D1 : list (atom * B)) (D2: list (atom * C)),
  disjoint D1 E ->
  dom D2 [<=] dom D1 ->
  disjoint D2 E.
Proof.
  induction E; intros D1 D2 Disj Sub; solve_uniq.
Qed.

Lemma dom__ddom_gdom : forall E,
  dom E [=] ddom_env E `union` gdom_env E.
Proof.
  induction E; simpl; auto.
    fsetdec.
    destruct a. destruct b; fsetdec.
Qed.

Lemma lenv_split_notin: forall G D1 D2 D3 x,
  lenv_split G D1 D2 D3 ->
  x `notin` dom D3 ->
  x `notin` dom D1 /\ x `notin` dom D2.
Proof.
  intros G D1 D2 D3 x Split Fv.
  (lenv_split_cases (induction Split) Case); intros; simpl; auto.
Qed.

(*******************************************************************************)
(** subst under delta/gamma *)

Lemma delta_osubst_closed_typ : forall dsubst t,
   disjdom (fv_tt t) (dom dsubst) ->
   apply_delta_subst_typ dsubst t = t.
Proof.
  induction dsubst; intros; auto.
  Case "cons".
    destruct a; simpl.
    simpl in H.
    apply disjdom_cons_r in H. destruct H as [H1 H2].
    apply disjdom_sym in H2.
    apply IHdsubst in H2.
    rewrite <- subst_tt_fresh; eauto using notin_fv_wf.
Qed.

Lemma gamma_osubst_closed_exp : forall gsubst e,
   disjdom (fv_ee e) (dom gsubst) ->
   apply_gamma_subst gsubst e = e.
Proof.
  induction gsubst; intros e Hdisj; simpl; auto.
    destruct a.
    simpl in Hdisj.
    apply disjdom_cons_r in Hdisj. destruct Hdisj as [Hdisj1 Hdisj2].
    apply disjdom_sym in Hdisj2.
    apply IHgsubst in Hdisj2.
    rewrite <- subst_ee_fresh; eauto.
Qed.

Lemma gamma_osubst_closed_typ : forall gsubst t,
   apply_gamma_subst_typ gsubst t = t.
intros. unfold apply_gamma_subst_typ. auto.
Qed.

Lemma delta_osubst_closed_exp : forall dsubst e,
   disjdom (fv_te e) (dom dsubst) ->
   apply_delta_subst dsubst e = e.
Proof.
  induction dsubst; intros e Hdisj; simpl; auto.
    destruct a.
    simpl in Hdisj.
    apply disjdom_cons_r in Hdisj. destruct Hdisj as [Hdisj1 Hdisj2].
    apply disjdom_sym in Hdisj2.
    apply IHdsubst in Hdisj2.
    rewrite <- subst_te_fresh; eauto.
Qed.

Lemma gamma_osubst_var : forall gsubst x e,
   uniq gsubst ->
   binds x e gsubst -> 
   disjdom (fv_ee e) (dom gsubst) ->
   apply_gamma_subst gsubst (exp_fvar x) = e.
Proof.
  induction gsubst; intros x e Huniq Hbinds Hdisj.
    inversion Hbinds.

    simpl. destruct a.
    simpl in Hdisj. apply disjdom_cons_r in Hdisj. destruct Hdisj as [Hdisj1 Hdisj2].
    apply disjdom_sym in Hdisj2.
    destruct (x==a); subst; simpl_env in *.
      analyze_binds_uniq Hbinds; subst.
        rewrite gamma_osubst_closed_exp; auto.

      eapply IHgsubst; eauto.
        inversion Huniq; auto.
        analyze_binds_uniq Hbinds.
Qed.

Lemma delta_osubst_var : forall dsubst X T,
   uniq dsubst ->
   binds X (T) dsubst ->
   disjdom (fv_tt T) (dom dsubst) ->
   apply_delta_subst_typ dsubst (typ_fvar X) = T.
Proof.
  induction dsubst; intros X T Huniq Hbinds Hdisj.
    inversion Hbinds.

    simpl. destruct a.
    simpl in Hdisj. apply disjdom_cons_r in Hdisj. destruct Hdisj as [Hdisj1 Hdisj2].
    apply disjdom_sym in Hdisj2.
    destruct (X==a); subst; simpl_env in *.
      analyze_binds_uniq Hbinds; subst.
        rewrite delta_osubst_closed_typ; auto.

      apply IHdsubst; auto.
        inversion Huniq; auto.
        analyze_binds Hbinds; auto.
Qed.

Lemma apply_delta_subst_env_id : forall E dsubst,
  wf_env E ->
  disjoint dsubst E ->
  E = apply_delta_subst_env dsubst E.
Proof with auto.
  intros E dsubst Wfe Disj.
  (wf_env_cases (induction Wfe) Case); simpl; simpl_env...
  Case "wf_env_kn".
    rewrite <- IHWfe...
      solve_uniq.
  Case "wf_env_typ".
    rewrite <- IHWfe...
      rewrite delta_osubst_closed_typ... 
        unfold disjdom.
        split; intros x0 x0notin.
          apply in_fv_wf with (X:=x0) in H; auto.
            solve_uniq.
          apply notin_fv_wf with (X:=x0) in H; auto.
            solve_uniq.
     solve_uniq.
Qed.

Lemma apply_delta_subst_env_cons : forall dsubst E1 E2,
  apply_delta_subst_env dsubst (E1 ++ E2) =
    apply_delta_subst_env dsubst E1 ++ apply_delta_subst_env dsubst E2.
Proof.
  induction E1; intros; simpl; auto.
    destruct a. destruct b; rewrite IHE1; auto.
Qed.

Lemma apply_delta_subst_lenv_cons : forall dsubst E1 E2,
  apply_delta_subst_env dsubst (E1 ++ E2) =
    apply_delta_subst_env dsubst E1 ++ apply_delta_subst_env dsubst E2.
Proof.
  induction E1; intros; simpl; auto.
    destruct a. destruct b; rewrite IHE1; auto.
Qed.

(* *************** *)
(* red expr value typ *)

Lemma ocanonical_form_with : forall Env lEnv e U1 U2,
  value e ->
  typing Env lEnv e (typ_with U1 U2) ->
  exists e1, exists e2, e = exp_apair e1 e2.
Proof.
  intros Env lEnv e U1 U2 Val Typ.
  remember (typ_with U1 U2) as T.
  revert U1 U2 HeqT.
  (typing_cases (induction Typ) Case); 
    intros U1 U2 EQT; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
Qed.

Lemma preservation_bigstep_red : forall D G e e' T,
  typing D G e T ->
  bigstep_red e e' ->
  typing D G e' T.
Proof.
  intros D G e e' T typ Hbrc.
  generalize dependent T.
  induction Hbrc; intros T typ; inversion typ; subst; auto; try solve [inversion H].
    apply IHHbrc; auto. apply  preservation with (e:=exp_app e1 e2); auto.
    apply IHHbrc; auto. apply  preservation with (e:=exp_tapp e1 T0); auto.
    apply IHHbrc; auto. apply  preservation with (e:=exp_let e1 e2); auto.
    apply IHHbrc; auto. apply  preservation with (e:=exp_fst e0); auto.
    apply IHHbrc; auto. apply  preservation with (e:=exp_snd e0); auto.
Qed.

(* ********************************************************************** *)
(** * Inversion *)

Lemma empty_dom__empty_ctx : forall A (D : list (atom*A)),
  dom D [=] {} ->
  D = nil.
Proof.
  induction D; intros; auto.
    simpl in H. destruct a.
    assert (a `in` add a (dom D)) as J. auto.
    rewrite H in J. 
    contradict J; auto.
Qed.

Lemma wf_lenv_lin_strengthening': forall G D1 D2 D3,
  wf_lenv G (D1 ++ D2 ++ D3) ->
  wf_lenv G (D1 ++ D3).
Proof.
  intros.
  remember (D1 ++ D2 ++ D3) as D.
  generalize dependent D1. generalize dependent D2. generalize dependent D3.
  (wf_lenv_cases (induction H) Case);  
    intros D3 D2 D1 EQ.
  Case "wf_lenv_empty".
    destruct D1; destruct D2; destruct D3; inversion EQ; auto.
  Case "wf_lenv_typ".
    destruct D1; destruct D2; simpl_env in *; inversion EQ; subst; auto.
    SCase "D1=nil, D2=con".
      rewrite_env (D2 ++ D3 ++ nil) in H.
      apply wf_lenv_lin_strengthening in H; auto.
    SCase "D1=con, D2=con".
      apply wf_lenv_typ; auto.
        apply (IHwf_lenv D3 (p0 :: D2) D1); auto.

        simpl_env in *. auto.
Qed.

Lemma wf_lenv_merge : forall E lE1 lE2,
  wf_lenv E lE1 ->
  wf_lenv E lE2 ->
  disjoint lE1 lE2 ->
  wf_lenv E (lE1++lE2).
Proof.
  intros E lE1 lE2 Wfle1 Wfle2 Disj.
  induction lE1; auto.
    destruct a. destruct l. simpl_env.
    inversion Wfle1; subst.
    apply wf_lenv_typ; auto.
      apply IHlE1; auto.
        solve_uniq.
      solve_uniq.
Qed.

Lemma lenv_split_lin_weakening_right: forall E F D1 D2 D3,
  lenv_split E D1 D2 D3 ->
  wf_lenv E (F ++ D3) ->
  lenv_split E D1 (F ++ D2)(F ++ D3).
Proof.
  intros E F. 
  induction F; intros D1 D2 D3 S WFL; simpl_env in *; auto.
  Case "con".
    destruct a. simpl_env in *.
    inversion WFL; subst.
    apply lenv_split_right; auto.
Qed.

(* ********************)
(*** typing lin ctx is derministic *)

Lemma bindsxE__in_gdom : forall x t E,
 binds x (bind_typ t) E ->
 x `in` gdom_env E.
Proof.
 intros x t E Binds.
 induction E.
   inversion Binds.
   destruct a. destruct b; simpl_env in *.
     analyze_binds Binds.
     analyze_binds Binds.
Qed.

Lemma typing_ldom : forall E lE e t,
  typing E lE e t ->
  AtomSetImpl.diff (fv_ee e) (gdom_env E) [=] dom lE.
Proof.
  intros E lE e t Typing.
  (typing_cases (induction Typing) Case); simpl; auto.
  Case "typing_var".
    apply bindsxE__in_gdom in H0.
    fsetdec.    
  Case "typing_lvar".
    apply disjoint_wf_lenv in H.
    assert (x `notin` dom E) as xnotinE.
      solve_uniq.
    assert (x `notin` gdom_env E) as xnotingE.
      auto using dom__gdom.
    fsetdec.    
  Case "typing_abs".
    pick fresh x.
    assert (x `notin` L) as xnotinL. auto.
    apply H1 in xnotinL.
    simpl in xnotinL.
    assert (x `notin` gdom_env E) as xnotingE.
      auto using dom__gdom.
    assert (Jl:=@fv_ee_open_ee_sub_left e1 x). simpl in Jl.
    assert (Jr:=@fv_ee_open_ee_sub_right e1 x).
    destruct_notin. 
    fsetdec.    
  Case "typing_app".
    apply dom_lenv_split in H.
    rewrite H. 
    rewrite <- IHTyping1.
    rewrite <- IHTyping2.
    fsetdec.
  Case "typing_tabs".
    pick fresh X.
    assert (X `notin` L) as XnotinL. auto.
    apply H0 in XnotinL.
    simpl in XnotinL.
    rewrite <- XnotinL.
    assert (X `notin` gdom_env E) as XnotingE.
      auto using dom__gdom.
    assert (J:=@fv_ee_open_te_eq e1 X).
    destruct_notin. clear H H0 Fr NotInTac NotInTac1 NotInTac2 NotInTac3 NotInTac4 NotInTac5 XnotinL.
    fsetdec.    
  Case "typing_let".
    apply dom_lenv_split in H1.
    rewrite H1. 
    rewrite <- IHTyping.
    pick fresh x.
    rewrite <- H0; auto.
    assert (x `notin` gdom_env E) as xnotingE.
      auto using dom__gdom.
    assert (Jl:=@fv_ee_open_ee_sub_left e2 x). simpl in Jl.
    assert (Jr:=@fv_ee_open_ee_sub_right e2 x).
    simpl_env. destruct_notin. fsetdec.    
  Case "typing_apair".
    rewrite <- IHTyping1.
    fsetdec.
Qed.

Lemma lenv_split_spice_left : forall E D1L D1R D2 D,
  lenv_split E (D1L++D1R) D2 D ->
  exists D2L, exists D2R, exists DL, exists DR,
    D2 = (D2L++D2R) /\
    D = (DL++DR) /\
    lenv_split E D1L D2L DL /\
    lenv_split E D1R D2R DR.
Proof.
  intros E D1L D1R D2 D Split.
  remember (D1L ++ D1R).
  generalize dependent D1L.
  generalize dependent D1R.
  induction Split; intros; auto.
    symmetry in Heql. 
    apply app_eq_nil in Heql.
    destruct Heql; subst.
    exists (@nil (atom*lbinding)). exists (@nil (atom*lbinding)). exists (@nil (atom*lbinding)). exists (@nil (atom*lbinding)).
      split; auto.
    
    apply one_eq_app in Heql.
    destruct Heql as [[D1L' [EQ1 EQ2]]|[EQ1 EQ2]]; subst.
      destruct (@IHSplit D1R D1L') as [D2L [D2R [DL [DR [EQ1 [EQ2 [J1 J2]]]]]]]; subst; auto.
      clear IHSplit.
      exists D2L. exists D2R. exists ([(x, lbind_typ T)]++DL). exists DR.
      split; auto.  split; auto. split; auto.
        simpl_env. apply lenv_split_left; auto.
 
      exists (@nil (atom*lbinding)). exists D2. exists (@nil (atom*lbinding)). exists ([(x, lbind_typ T)]++D3).
      split; auto.  split; auto. split; auto.
        apply lenv_split_empty.
          apply wf_lenv_split in Split; auto.
        simpl_env. apply lenv_split_left; auto. 
   
  subst.      
  destruct (@IHSplit D1R D1L) as [D2L [D2R [DL [DR [EQ1 [EQ2 [J1 J2]]]]]]]; subst; auto.
  clear IHSplit.
  exists ([(x, lbind_typ T)]++D2L). exists D2R. exists ([(x, lbind_typ T)]++DL). exists DR.
  split; auto.  
Qed.

Lemma uniq_binds_inv : forall A x (E:list (atom*A)),
  uniq E ->
  x `in` dom E ->
  exists E1, exists E2, exists b,
    E = E1 ++ [(x, b)] ++ E2 /\
    uniq (E1++E2).
Proof.
  intros A x E Uniq xinE.
  induction E.
    contradict xinE; auto.

    destruct a.
    inversion Uniq; subst. simpl_env in *.
    assert (x `in` {{a}} \/ x `in` dom E) as J. fsetdec.
    destruct J as [J | J].
      assert (x=a) as EQ. fsetdec. 
      subst.
      exists (@nil (atom*A)). exists E. exists a0. 
      split; auto.

      destruct IHE as [E1 [E2 [b [EQ1 EQ2]]]]; subst; auto.
      exists ([(a,a0)]++E1). exists E2. exists b.
      split; auto.
        simpl_env. auto.
Qed.
  
Lemma lenv_split_domeq_left : forall E lE1 lE2 lE3 lE1',
  lenv_split E lE1 lE2 lE3 ->
  dom lE1 [=] dom lE1' ->
  wf_lenv E lE1' ->
  exists lE3',
    lenv_split E lE1' lE2 lE3' /\
    dom lE3 [=] dom lE3'.
Proof.
  intros E lE1 lE2 lE3 lE1' Split DomEq Wfle.
  generalize dependent lE1'.
  induction Split; intros; auto.
    inversion Wfle; subst.
      exists (@nil (atom*lbinding)). auto.

      assert (x `in` dom ([(x,lbind_typ T)]++D)) as J. simpl. auto.
      rewrite <- DomEq in J.
      contradict J; auto.

    assert (x `in` dom ([(x,lbind_typ T)]++D1)) as J. simpl. auto.
    rewrite DomEq in J.
    assert (uniq lE1') as Uniq.
      apply uniq_from_wf_lenv in Wfle; auto.
    assert (JJ:=Uniq).
    apply uniq_binds_inv with (x:=x) in JJ; auto.
    destruct JJ as [E1 [E2 [b [EQ1 EQ2]]]]; subst.
    assert (x `notin` dom E1) as xnotinE1.
      apply fresh_mid_head in Uniq; auto.
    assert (x `notin` dom E2) as xnotinE2.
      apply fresh_mid_tail in Uniq; auto.
    simpl_env in DomEq.
    assert (x `notin` dom D1) as xnotinD1.
      apply dom_lenv_split in Split.
      rewrite Split in H0. auto.
    assert (dom D1 [=] dom E1 `union` dom E2) as EQ.
      clear Split H H0 H1 IHSplit EQ2 Uniq J.
      fsetdec.
    destruct (@IHSplit  (E1++E2)) as [D3' [Split' EQ']]; simpl_env; auto.
      apply wf_lenv_lin_strengthening' in Wfle; auto.
    assert (JJ:=Split').
    apply lenv_split_spice_left in Split'.
    destruct Split' as [D2L [D2R [DL0 [DR0  [EQ1' [EQ2' [J1 J2]]]]]]]; subst.
    clear IHSplit.
    destruct b.
    exists (DL0++[(x, lbind_typ t)]++DR0).
    split.
      apply lenv_split_weakening_left; auto.
        apply wf_lenv_lin_weakening; auto.
          apply wf_typ_from_lbinds_typ with (x:=x) (U:=t) in Wfle; auto.
          rewrite EQ' in H0. auto.   
       simpl_env. rewrite EQ'. simpl_env. 
       clear xnotinE1 xnotinE2 xnotinD1 H H0 EQ' EQ DomEq J Uniq EQ2. 
       fsetdec.
  
    apply IHSplit in Wfle; auto.
    destruct Wfle as [lE3' [IHSplit' Wfle']].
    exists ([(x, lbind_typ T)]++lE3').
    split.
      apply lenv_split_right; auto.
         rewrite Wfle' in H0. auto.
      simpl_env. rewrite Wfle'.
      clear H H0 DomEq.
      fsetdec.
Qed.

Lemma lenv_split_permute_left : forall E lE1 lE2 lE3 lE1',
  lenv_split E lE1 lE2 lE3 ->
  permute lE1 lE1' ->
  exists lE3',
    lenv_split E lE1' lE2 lE3' /\
    permute lE3 lE3'.
Proof.
  intros E lE1 lE2 lE3 lE1' Split Perm.
  generalize dependent lE1'.
  induction Split; intros; auto.
    inversion Perm; subst.
    exists (@nil (atom*lbinding)). auto.

    inversion Perm; subst.
    apply IHSplit in H6.
    destruct H6 as [lE3' [IHSplit' Perm']].
    assert (J:=IHSplit').
    apply lenv_split_spice_left in IHSplit'.
    destruct IHSplit' as [D2L [D2R [DL0 [DR0  [EQ1 [EQ2 [J1 J2]]]]]]]; subst.
    clear IHSplit.
    exists (DL0++[(x, lbind_typ T)]++DR0).
    split.
      apply lenv_split_weakening_left; auto.
        apply wf_lenv_lin_weakening; auto.
          apply dom_permute in Perm'.
          rewrite <- Perm'. auto.
      apply permute_cons; auto.

    apply IHSplit in Perm.
    destruct Perm as [lE3' [IHSplit' Perm']].
    exists ([(x, lbind_typ T)]++lE3').
    split.
      apply lenv_split_right; auto.
        apply dom_permute in Perm'.
        rewrite <- Perm'. auto.
      rewrite_env (nil ++ [(x, lbind_typ T)] ++ lE3').
      apply permute_cons; auto.
Qed.

Lemma indom_inv : forall A (E: list (atom*A)) x,
  x `in` dom E ->
  exists a, exists E1, exists E2,
    E = E1 ++ [(x, a)] ++ E2.
Proof.
  intros A E x xinE.
  induction E.
    contradict xinE; auto.

    destruct a.
    destruct (x == a); subst.
      exists a0. exists nil. exists E. auto.
 
      assert (x `in` dom E) as J. 
        simpl in xinE. fsetdec.
      apply IHE in J.
      destruct J as [a' [E1 [E2 J]]]; subst.
      exists a'. exists ((a,a0)::E1). exists E2.
      auto.
Qed.


Lemma domeq_lengtheq : forall A (l1 l2: list (atom*A)),
  uniq l1 ->
  uniq l2 ->
  dom l1 [=] dom l2 ->
  length l1 = length l2.
Proof.
  intros A l1 l2 Uniq1 Uniq2 DomEq.
  generalize dependent l2.
  induction Uniq1; intros.
    inversion Uniq2; subst; simpl; auto.
      assert (x `in` dom ([(x,a)]++E)) as xin.
        simpl. auto.
      rewrite <- DomEq in xin.
      contradict xin; auto.
    inversion Uniq2; subst; simpl.
      assert (x `in` dom ([(x,a)]++E)) as xin.
        simpl. auto.
      rewrite DomEq in xin.
      contradict xin; auto.

      simpl in DomEq.
      destruct (x == x0); subst.
        assert (dom E [=] dom E0) as EQ.
          fsetdec.
        apply IHUniq1 in H0; auto.

        assert (x `in` dom E0) as J.
          fsetdec.
        apply indom_inv in J.
        destruct J as [a' [E1 [E2 J]]]; subst.
        assert (uniq (E1++[(x0,a0)]++E2)) as J.
          assert (uniq (E1++E2)) as J'.
           solve_uniq.
          solve_uniq.
        apply IHUniq1 in J.
          rewrite J. 
          repeat(rewrite app_length).
          simpl. auto.

          simpl_env in *.
          assert (x `notin` dom E1 `union` dom E2) as xnotin.
            clear J Uniq2 n DomEq H1.
            solve_uniq.
          clear J H0 Uniq2.
          assert (dom E [=] AtomSetImpl.diff (add x (dom E)) {{x}}) as J.
            clear n H1 DomEq. fsetdec.
          assert (dom E1 `union` dom E2 [=] AtomSetImpl.diff (add x0 (union (dom E1) (dom E2))) {{x0}}) as J'.
            clear n DomEq J. fsetdec.
          assert ({{x0}} `union` dom E1 `union` dom E2 [=] dom E1 `union` {{x0}} `union` dom E2) as J''.
            clear n J J' H1 DomEq. fsetdec.
          assert (dom E [=] AtomSetImpl.diff (add x0 (dom E1 `union` {{x}} `union` dom E2)) {{x}}) as J'''.
            rewrite J. rewrite DomEq. clear J J' J'' H1 n. fsetdec.
          rewrite J'''. rewrite <- J''. rewrite J'.
          clear J J' J'' J''' DomEq.
          assert (AtomSetImpl.diff (add x0 (union (dom E1) (dom E2))) {{x0}} [=] dom E1 `union` dom E2) as J.
            fsetdec.
          rewrite J. clear J.
          assert (add x0 ((dom E1) `union` {{x}} `union` (dom E2)) [=] add x ((dom E1) `union` {{x0}} `union` (dom E2))) as J.
            fsetdec.
          rewrite J. clear J.
          assert (AtomSetImpl.diff (add x ((dom E1) `union` {{x0}} `union` (dom E2))) {{x}} [=] (dom E1) `union` {{x0}} `union` (dom E2)) as J.
            fsetdec.
          rewrite J. clear J.
          fsetdec.
Qed.

Lemma app_lengtheq_inv_head: forall A (l3 l4 l1 l2 : list (atom*A)),
  l3 ++ l1 = l4 ++ l2 -> 
  length l3 = length l4 ->
  l1 = l2.
Proof.
  intros A l3 l4 l1 l2 Listeq Lengtheq.
  remember (l3 ++ l1) as l.
  generalize dependent l1.
  generalize dependent l2.
  generalize dependent l3.
  generalize dependent l4.
  induction l; intros.
    symmetry in Listeq. apply app_eq_nil in Listeq. destruct Listeq; subst.
    symmetry in Heql. apply app_eq_nil in Heql. destruct Heql; subst.
    auto.

    destruct a. simpl_env in *.
    apply one_eq_app in Listeq.
    apply one_eq_app in Heql.
    destruct Listeq as [[l4' [EQ1 EQ2]]|[EQ1 EQ2]]; subst.
    Case "1".
      destruct Heql as [[l3' [EQ1 EQ2]]|[EQ1 EQ2]]; subst.
      SCase "11".
        apply IHl with (l3:=l3') (l4:=l4'); auto.
      SCase "12".
        simpl in Lengtheq. inversion Lengtheq.
    Case "2".
      destruct Heql as [[l3' [EQ1 EQ2]]|[EQ1 EQ2]]; subst; auto.
      SCase "11".
        simpl in Lengtheq. inversion Lengtheq.
Qed.

Lemma typing_linctx_domeq : forall E lE lE' e t t',
  typing E lE e t ->
  typing E lE' e t' ->
  dom lE [=] dom lE'.
Proof.
  intros.
  apply typing_ldom in H.
  apply typing_ldom in H0.
  rewrite <- H. rewrite <- H0.
  fsetdec.
Qed.

Lemma lenv_split_weakening_tail : forall F E lE1 lE2 lE,
  lenv_split E lE1 lE2 lE ->
  wf_env (F ++ E) ->
  disjoint F lE ->
  lenv_split (F++E) lE1 lE2 lE.
Proof.
  intros F E lE1 lE2 lE Split Wfe Disj.
  rewrite_env(nil++F++E).
  apply lenv_split_weakening; simpl_env; auto.
Qed.

(* *************** *)
(* free variables *)

Lemma notin_fv_ee_open_ee_exp_rec : forall (x : atom) e e' k,
  x `notin` fv_ee e ->
  x `notin` fv_ee e' ->
  x `notin` fv_ee (open_ee_rec k e' e).
Proof.
  (exp_cases (induction e) Case); intros e' kk; simpl in *; auto.
  Case "exp_bvar".
    destruct (kk == n); simpl; auto.
Qed.

Lemma notin_fv_ee_open_ee_exp : forall (x : atom) e e',
  x `notin` fv_ee e ->
  x `notin` fv_ee e' ->
  x `notin` fv_ee (open_ee e e').
Proof.
  unfold open_ee.
  auto using notin_fv_ee_open_ee_exp_rec.
Qed.

Lemma notin_fv_ee_open_te_exp_rec : forall (x : atom) e t k,
  x `notin` fv_ee e ->
  x `notin` fv_ee (open_te_rec k t e).
Proof.
  (exp_cases (induction e) Case); intros e' kk; simpl in *; auto.
Qed.

Lemma notin_fv_ee_open_te_exp : forall (x : atom) e t,
  x `notin` fv_ee e ->
  x `notin` fv_ee (open_te e t).
Proof.
  unfold open_te.
  auto using notin_fv_ee_open_te_exp_rec.
Qed.

Lemma notin_fv_ee_red : forall e e' x,
  red e e' ->
  x `notin` fv_ee e ->
  x `notin` fv_ee e'.
Proof.
  intros e e' x Red Frx.
  induction Red; simpl in *; auto.
    apply notin_fv_ee_open_ee_exp; auto.
    apply notin_fv_ee_open_te_exp; auto.
    apply notin_fv_ee_open_ee_exp; auto.
Qed.

Lemma notin_fv_ee_mred : forall e e' x,
  bigstep_red e e' ->
  x `notin` fv_ee e ->
  x `notin` fv_ee e'.
Proof.
  intros e e' x Red Frx.
  induction Red; simpl in *; eauto using notin_fv_ee_red.
Qed.

Lemma red_renaming_one : forall e e' x y,
  red e e' ->
  y `notin` (fv_ee e) ->
  red (subst_ee x y e) (subst_ee x y e').  
Proof.
  intros e e' x y Red Fr.
  generalize dependent x.
  generalize dependent y.
  induction Red; intros; simpl; simpl in Fr; auto.
    apply subst_ee_expr with (z:=x) (e2:=y) in H; auto.
    rewrite subst_ee_open_ee; auto.

    apply subst_ee_expr with (z:=x) (e2:=y) in H; auto.
    rewrite subst_ee_open_te; auto.

    apply subst_ee_expr with (z:=x) (e2:=y) in H; auto.

    apply subst_ee_expr with (z:=x) (e2:=y) in H; auto.
    rewrite subst_ee_open_ee; auto.
Qed.

Lemma bigstep_red_renaming_one : forall e e' x y,
  bigstep_red e e' ->
  y `notin` (fv_ee e) ->
  bigstep_red (subst_ee x y e) (subst_ee x y e').  
Proof.
  intros e e' x y Red Fr.
  generalize dependent x.
  generalize dependent y.
  induction Red; intros; auto.
    assert (y `notin` fv_ee e') as Fr'.
      apply notin_fv_ee_red with (x:=y) in H; auto.
    apply bigstep_red_trans with (e':=subst_ee x y e'); eauto using red_renaming_one.
Qed.  

Lemma normalize_renaming_one : forall e v x y,
  normalize e v ->
  y `notin` (fv_ee e) ->
  normalize (subst_ee x y e) (subst_ee x y v).  
Proof.
  intros e v x y norm Fr.
  unfold normalize in *.
  destruct norm.
  apply bigstep_red_renaming_one with (x:=x)(y:=y) in b; auto.
  apply value_through_subst_ee with (x:=x) (u:=y) in v0; auto.
Qed.

Lemma subst_ee_id : forall e x,
  subst_ee x x e = e.
Proof.
  induction e; intro; simpl; try solve [
      auto |
      rewrite IHe; auto |
      rewrite IHe1; rewrite IHe2; auto
      ].
    destruct (a == x); subst; auto.
Qed.

Lemma open_ee_rec_fv_ee_sub : forall e e' kk,
  fv_ee (open_ee_rec kk e' e) [<=] fv_ee e `union` fv_ee e'.
Proof.
  induction e; intros e' kk; simpl; try solve [eauto | fsetdec].
    destruct (kk==n); try solve [fsetdec].
    
    assert (J1:=@IHe1 e' kk).
    assert (J2:=@IHe2 e' kk).
    fsetdec.

    assert (J1:=@IHe1 e' kk).
    assert (J2:=@IHe2 e' (S kk)).
    fsetdec.

    assert (J1:=@IHe1 e' kk).
    assert (J2:=@IHe2 e' kk).
    fsetdec.
Qed.

Lemma open_ee_fv_ee_sub : forall e e',
  fv_ee (open_ee e e') [<=] fv_ee e `union` fv_ee e'.
Proof.
  intros. unfold open_ee. apply open_ee_rec_fv_ee_sub.
Qed.

Lemma open_ee_fv_ee_sub' : forall e e',
  fv_ee (open_ee e e') [<=] fv_ee e' `union` fv_ee e.
Proof.
  intros.
  assert (fv_ee e `union` fv_ee e' [=] fv_ee e' `union` fv_ee e) as EQ. fsetdec.
  rewrite <- EQ. apply open_ee_fv_ee_sub.
Qed.

Lemma open_te_rec_fv_ee_sub : forall e t kk,
  fv_ee (open_te_rec kk t e) [<=] fv_ee e.
Proof.
  induction e; intros s kk; simpl; try solve [eauto | fsetdec].
    assert (J1:=@IHe1 s kk).
    assert (J2:=@IHe2 s kk).
    fsetdec.

    assert (J1:=@IHe1 s kk).
    assert (J2:=@IHe2 s kk).
    fsetdec.

    assert (J1:=@IHe1 s kk).
    assert (J2:=@IHe2 s kk).
    fsetdec.
Qed.

Lemma open_te_fv_ee_sub : forall e t,
  fv_ee (open_te e t) [<=] fv_ee e.
Proof.
  intros. apply open_te_rec_fv_ee_sub.
Qed.

Lemma red_fv_ee_sub : forall e e',
  red e e' ->
  fv_ee e' [<=] fv_ee e.
Proof.
  intros e e' Red.
  induction Red; simpl in *; try solve [fsetdec].
    apply open_ee_fv_ee_sub.
    apply open_te_fv_ee_sub.
    apply open_ee_fv_ee_sub'.
Qed.

Lemma bigstep_red_fv_ee_sub : forall e e',
  bigstep_red e e' ->
  fv_ee e' [<=] fv_ee e.
Proof.
  intros e e' Red.
  induction Red.
    fsetdec.
    apply red_fv_ee_sub in H. fsetdec.
Qed.

Lemma open_tt_rec_fv_tt_upper : forall t1 t2 kk,
  fv_tt (open_tt_rec kk t2 t1) [<=] fv_tt t1 `union` fv_tt t2.
Proof.
  induction t1; intros t2 kk; simpl; try solve [eauto | fsetdec].
    destruct (kk==n); try solve [fsetdec].

    assert (J1:=@IHt1_1 t2 kk).
    assert (J2:=@IHt1_2 t2 kk).
    fsetdec.
    
    assert (J1:=@IHt1_1 t2 kk).
    assert (J2:=@IHt1_2 t2 kk).
    fsetdec.
Qed.

Lemma open_tt_fv_tt_upper : forall t1 t2,
  fv_tt (open_tt t1 t2) [<=] fv_tt t1 `union` fv_tt t2.
Proof.
  intros. apply open_tt_rec_fv_tt_upper.
Qed.

Lemma open_tt_rec_fv_tt_lower : forall t1 t2 kk,
  fv_tt t1 [<=] fv_tt (open_tt_rec kk t2 t1).
Proof.
  induction t1; intros t2 kk; simpl; try solve [eauto | fsetdec].
    assert (J1:=@IHt1_1 t2 kk).
    assert (J2:=@IHt1_2 t2 kk).
    fsetdec.
    
    assert (J1:=@IHt1_1 t2 kk).
    assert (J2:=@IHt1_2 t2 kk).
    fsetdec.
Qed.

Lemma open_tt_fv_tt_lower : forall t1 t2,
  fv_tt t1 [<=] fv_tt (open_tt t1 t2).
Proof.
  intros. apply open_tt_rec_fv_tt_lower.
Qed.

Lemma wft_fv_tt_sub : forall E t,
  wf_typ E t ->
  fv_tt t [<=] dom E.
Proof.
  intros E t Wft.
  induction Wft; simpl.
    apply binds_In in H0. fsetdec.
    fsetdec.

    pick fresh X.
    assert (X `notin` L) as XnL. auto.
    apply H0 in XnL.
    assert (fv_tt T1 [<=] fv_tt (open_tt T1 X)) as sub.
      apply open_tt_fv_tt_lower; auto.
    assert (fv_tt T1 [<=] dom ([(X, bind_kn)]++E)) as sub'.
      fsetdec.
    assert (AtomSetImpl.diff (fv_tt T1) {{X}} [<=] AtomSetImpl.diff (dom ([(X, bind_kn)]++E)) {{X}}) as sub''.
      fsetdec.
    assert (AtomSetImpl.diff (fv_tt T1) {{X}}[=](fv_tt T1)) as eq.
      clear XnL sub sub' sub''. fsetdec.
    assert (AtomSetImpl.diff (dom ([(X, bind_kn)]++E)) {{X}}[=]dom E) as eq'.
      clear XnL sub sub' sub''. simpl_env. fsetdec.
    rewrite <- eq. rewrite <- eq'.
    assumption.

    fsetdec.

    fsetdec.
Qed.

Lemma wf_lenv_fv_lenv_sub : forall E lE,
  wf_lenv E lE ->
  fv_lenv lE [<=] dom E `union` dom lE.
Proof.
  intros E lE Wfle.
  induction Wfle; simpl.
    fsetdec.

    apply wft_fv_tt_sub in H1.
    fsetdec.
Qed.

Lemma disjdom__disjoint : forall A B (E:list (atom*A)) (D:list (atom*B)),
  disjdom (dom E) (dom D) ->
  disjoint E D.
Proof.
  intros A B E D Disj.
  induction E.
    auto.

    destruct a as [x a].
    destruct Disj as [J1 J2].
    assert (disjoint (x ~ a) D).
      apply disjoint_one_2.
      apply J1. simpl. auto.
    assert (disjoint E D).
      apply IHE.
      split; intros.
        apply J1. simpl. auto.
        apply J2 in H0. simpl in H0. auto.
    solve_uniq.
Qed.

Lemma disjdom_sub : forall D D1 D2,
  disjdom D D1 ->
  D2 [<=] D1 ->
  disjdom D D2.
Proof.
  intros D D1 D2 Disj Sub.
  destruct Disj as [J1 J2].
  split; intros.
    apply J1 in H. fsetdec.
    apply J2. fsetdec.
Qed.

(*******************************************************************************)
(** misc *)

Lemma fv_lenv__includes__dom : forall lEnv,
  dom lEnv [<=] fv_lenv lEnv.
Proof.
  intros lEnv.
  induction lEnv; simpl.
    fsetdec.
    destruct a. destruct l. fsetdec.
Qed.

Lemma mid_list_inv : forall lE1 x (b:lbinding) lE2 lE1' lE2',
  uniq (lE1++[(x,b)]++lE2) ->
  lE1++[(x,b)]++lE2 = lE1'++[(x,b)]++lE2' ->
  (lE1 = lE1' /\ lE2 = lE2').
Proof.
  intros lE1 x b lE2 lE1' lE2' Uniq EQ.
  generalize dependent lE1'.
  induction lE1; intros.
    simpl_env in EQ.
    apply one_eq_app in EQ.
    destruct EQ as [[lE1'' [EQ1 EQ2]]|[EQ1 EQ2]]; subst.
      simpl_env in Uniq.
      inversion Uniq; subst.
      simpl_env in H3.
      destruct_notin.
      contradict NotInTac; auto.

      simpl_env in EQ2.
      apply app_inv_head in EQ2.
      subst. auto.

    destruct a.
    simpl_env in EQ.
    apply one_eq_app in EQ.
    destruct EQ as [[lE1'' [EQ1 EQ2]]|[EQ1 EQ2]]; subst.
      simpl_env in Uniq.
      inversion Uniq; subst.
      simpl_env in H1.
      apply IHlE1 with (lE1':=lE1'') in H1; auto.
      destruct H1; subst. auto.

      simpl_env in EQ2.
      inversion EQ2; subst.
      simpl_env in Uniq.
      inversion Uniq; subst.
      simpl_env in H3.
      destruct_notin.
      contradict NotInTac; auto.
Qed.

Lemma disjoint__disjdom : forall A B (E:list (atom*A)) (D:list (atom*B)),
  disjoint E D ->
  disjdom (dom E) (dom D).
Proof.
  intros A B E D Disj.
  induction E.
    split; intros; auto.
       contradict H; auto.

    destruct a as [x a].
    assert (disjoint E D). solve_uniq.
    apply IHE in H.
    destruct H as [H0 H1].
    split; intros; auto.
      destruct (x0==x); subst.
        clear IHE H0 H1 H.
        solve_uniq.
 
        apply H0. 
        clear IHE H0 H1 Disj. 
        simpl in H.
        fsetdec.

      destruct (x0==x); subst.
        clear IHE H0 H1.
        solve_uniq.
 
        apply H1 in H.
        simpl. fsetdec.
Qed.

Lemma uniq_renaming_one : forall A lE' lE x0 y0 (b:A),
  uniq (lE'++[(x0, b)]++lE) ->
  x0 `notin` dom lE' `union` dom lE ->
  y0 `notin` dom lE' `union` dom lE ->
  uniq (lE'++[(y0, b)]++lE).
Proof with auto.
  intros A lE' lE x0 y0 b Uniq Fvx0 Fvy0.
  solve_uniq.
Qed.  

Lemma id_rev_subst_atom_exp : forall e x y,
  x `in` (fv_ee e)  ->
  y `notin` (fv_ee e)  ->
  e = (subst_ee y x (subst_ee x y e)).
Proof.
  induction e; intros x y xine ynotine; simpl; auto.
    destruct (a==x); subst; simpl.
      destruct (y==y); auto.
        contradict n; auto.
      destruct (a==y); subst; auto.
        simpl in ynotine. contradict ynotine; auto.

    rewrite <- IHe; auto.

    simpl in xine. simpl in ynotine.
    destruct (in_dec x (fv_ee e1)) as [Je1 | Je1'].
      destruct (in_dec x (fv_ee e2)) as [Je2 | Je2'].
         rewrite <- IHe1; auto.
         rewrite <- IHe2; auto.

         rewrite <- IHe1; auto.
         rewrite <- subst_ee_fresh with (e:=e2); auto.
         rewrite <- subst_ee_fresh with (e:=e2); auto.
      destruct (in_dec x (fv_ee e2)) as [Je2 | Je2'].
         rewrite <- IHe2; auto.
         rewrite <- subst_ee_fresh with (e:=e1); auto.
         rewrite <- subst_ee_fresh with (e:=e1); auto.
       rewrite <- subst_ee_fresh with (e:=e1); auto.
       rewrite <- subst_ee_fresh with (e:=e1); auto.
       rewrite <- subst_ee_fresh with (e:=e2); auto.
       rewrite <- subst_ee_fresh with (e:=e2); auto.

    rewrite <- IHe; auto.
 
    rewrite <- IHe; auto.

    rewrite <- IHe; auto.

    simpl in xine. simpl in ynotine.
    destruct (in_dec x (fv_ee e1)) as [Je1 | Je1'].
      destruct (in_dec x (fv_ee e2)) as [Je2 | Je2'].
         rewrite <- IHe1; auto.
         rewrite <- IHe2; auto.

         rewrite <- IHe1; auto.
         rewrite <- subst_ee_fresh with (e:=e2); auto.
         rewrite <- subst_ee_fresh with (e:=e2); auto.
      destruct (in_dec x (fv_ee e2)) as [Je2 | Je2'].
         rewrite <- IHe2; auto.
         rewrite <- subst_ee_fresh with (e:=e1); auto.
         rewrite <- subst_ee_fresh with (e:=e1); auto.
       rewrite <- subst_ee_fresh with (e:=e1); auto.
       rewrite <- subst_ee_fresh with (e:=e1); auto.
       rewrite <- subst_ee_fresh with (e:=e2); auto.
       rewrite <- subst_ee_fresh with (e:=e2); auto.

    simpl in xine. simpl in ynotine.
    destruct (in_dec x (fv_ee e1)) as [Je1 | Je1'].
      destruct (in_dec x (fv_ee e2)) as [Je2 | Je2'].
         rewrite <- IHe1; auto.
         rewrite <- IHe2; auto.

         rewrite <- IHe1; auto.
         rewrite <- subst_ee_fresh with (e:=e2); auto.
         rewrite <- subst_ee_fresh with (e:=e2); auto.
      destruct (in_dec x (fv_ee e2)) as [Je2 | Je2'].
         rewrite <- IHe2; auto.
         rewrite <- subst_ee_fresh with (e:=e1); auto.
         rewrite <- subst_ee_fresh with (e:=e1); auto.
       rewrite <- subst_ee_fresh with (e:=e1); auto.
       rewrite <- subst_ee_fresh with (e:=e1); auto.
       rewrite <- subst_ee_fresh with (e:=e2); auto.
       rewrite <- subst_ee_fresh with (e:=e2); auto.

    rewrite <- IHe; auto.
 
    rewrite <- IHe; auto.
Qed.

Lemma subst_ee_in_inv : forall e (x y:atom),
  x `in` fv_ee e ->
  fv_ee (subst_ee x y e) [=] ((AtomSetImpl.diff (fv_ee e) {{x}}) `union` {{y}}).
Proof.
  induction e; intros x y xin; simpl in *; auto.
    contradict xin; auto.

    destruct (a == x); subst.
      fsetdec.
      contradict xin; auto.

    destruct (in_dec x (fv_ee e1)) as [Je1 | Je1'].
      destruct (in_dec x (fv_ee e2)) as [Je2 | Je2'].
         apply IHe1 with (y:=y) in Je1.
         apply IHe2 with (y:=y) in Je2.
         rewrite Je1. rewrite Je2.
         clear IHe1 IHe2 xin Je1 Je2.
         fsetdec.

         apply IHe1 with (y:=y) in Je1.
         rewrite <- subst_ee_fresh with (e:=e2); auto.
         rewrite Je1. 
         clear IHe1 IHe2 xin Je1.
         fsetdec.
      destruct (in_dec x (fv_ee e2)) as [Je2 | Je2'].
         apply IHe2 with (y:=y) in Je2.
         rewrite <- subst_ee_fresh with (e:=e1); auto.
         rewrite Je2. 
         clear IHe1 IHe2 xin Je2.
         fsetdec.

         contradict xin; auto.

    destruct (in_dec x (fv_ee e1)) as [Je1 | Je1'].
      destruct (in_dec x (fv_ee e2)) as [Je2 | Je2'].
         apply IHe1 with (y:=y) in Je1.
         apply IHe2 with (y:=y) in Je2.
         rewrite Je1. rewrite Je2.
         clear IHe1 IHe2 xin Je1 Je2.
         fsetdec.

         apply IHe1 with (y:=y) in Je1.
         rewrite <- subst_ee_fresh with (e:=e2); auto.
         rewrite Je1. 
         clear IHe1 IHe2 xin Je1.
         fsetdec.
      destruct (in_dec x (fv_ee e2)) as [Je2 | Je2'].
         apply IHe2 with (y:=y) in Je2.
         rewrite <- subst_ee_fresh with (e:=e1); auto.
         rewrite Je2. 
         clear IHe1 IHe2 xin Je2.
         fsetdec.

         contradict xin; auto.

    destruct (in_dec x (fv_ee e1)) as [Je1 | Je1'].
      destruct (in_dec x (fv_ee e2)) as [Je2 | Je2'].
         apply IHe1 with (y:=y) in Je1.
         apply IHe2 with (y:=y) in Je2.
         rewrite Je1. rewrite Je2.
         clear IHe1 IHe2 xin Je1 Je2.
         fsetdec.

         apply IHe1 with (y:=y) in Je1.
         rewrite <- subst_ee_fresh with (e:=e2); auto.
         rewrite Je1. 
         clear IHe1 IHe2 xin Je1.
         fsetdec.
      destruct (in_dec x (fv_ee e2)) as [Je2 | Je2'].
         apply IHe2 with (y:=y) in Je2.
         rewrite <- subst_ee_fresh with (e:=e1); auto.
         rewrite Je2. 
         clear IHe1 IHe2 xin Je2.
         fsetdec.

         contradict xin; auto.
Qed.

Lemma subst_te_fv_ee_eq : forall e X T,
  fv_ee (subst_te X T e) [=] fv_ee e.
Proof.
  induction e; intros X T; simpl; try solve [eauto | fsetdec].
Qed.

Lemma subst_ee_fv_ee_sub : forall e x e',
  fv_ee (subst_ee x e' e) [<=] fv_ee e `union` fv_ee e'.
Proof.
  induction e; intros x e'; simpl; try solve [eauto | fsetdec].
    destruct (a==x); simpl; try solve [fsetdec].
    
    assert (J1:=@IHe1 x e').
    assert (J2:=@IHe2 x e').
    fsetdec.

    assert (J1:=@IHe1 x e').
    assert (J2:=@IHe2 x e').
    fsetdec.

    assert (J1:=@IHe1 x e').
    assert (J2:=@IHe2 x e').
    fsetdec.
Qed.

Lemma subst_ee_fv_ee_in : forall e x e',
  x `in` fv_ee e ->
  fv_ee (subst_ee x e' e) [=] (AtomSetImpl.diff (fv_ee e) {{x}}) `union` fv_ee e'.
Proof.
  induction e; intros x e' Fv; simpl in *; try solve [eauto | fsetdec].
    destruct (a==x); simpl; try solve [fsetdec].
    
    destruct (in_dec x (fv_ee e1)) as [Je1 | Je1'].
      destruct (in_dec x (fv_ee e2)) as [Je2 | Je2'].
         rewrite (IHe1 x e'); auto.
         rewrite (IHe2 x e'); auto.
         fsetdec.

         rewrite (IHe1 x e'); auto.
         rewrite <- subst_ee_fresh with (e:=e2); auto.
         fsetdec.
      destruct (in_dec x (fv_ee e2)) as [Je2 | Je2'].
         rewrite (IHe2 x e'); auto.
         rewrite <- subst_ee_fresh with (e:=e1); auto.
         fsetdec.

         rewrite <- subst_ee_fresh with (e:=e1); auto.
         rewrite <- subst_ee_fresh with (e:=e2); auto.
         fsetdec.

    destruct (in_dec x (fv_ee e1)) as [Je1 | Je1'].
      destruct (in_dec x (fv_ee e2)) as [Je2 | Je2'].
         rewrite (IHe1 x e'); auto.
         rewrite (IHe2 x e'); auto.
         fsetdec.

         rewrite (IHe1 x e'); auto.
         rewrite <- subst_ee_fresh with (e:=e2); auto.
         fsetdec.
      destruct (in_dec x (fv_ee e2)) as [Je2 | Je2'].
         rewrite (IHe2 x e'); auto.
         rewrite <- subst_ee_fresh with (e:=e1); auto.
         fsetdec.

         rewrite <- subst_ee_fresh with (e:=e1); auto.
         rewrite <- subst_ee_fresh with (e:=e2); auto.
         fsetdec.

    destruct (in_dec x (fv_ee e1)) as [Je1 | Je1'].
      destruct (in_dec x (fv_ee e2)) as [Je2 | Je2'].
         rewrite (IHe1 x e'); auto.
         rewrite (IHe2 x e'); auto.
         fsetdec.

         rewrite (IHe1 x e'); auto.
         rewrite <- subst_ee_fresh with (e:=e2); auto.
         fsetdec.
      destruct (in_dec x (fv_ee e2)) as [Je2 | Je2'].
         rewrite (IHe2 x e'); auto.
         rewrite <- subst_ee_fresh with (e:=e1); auto.
         fsetdec.

         rewrite <- subst_ee_fresh with (e:=e1); auto.
         rewrite <- subst_ee_fresh with (e:=e2); auto.
         fsetdec.
Qed.

Lemma disjdom_eq : forall D D1 D2,
  disjdom D1 D ->
  D1 [=] D2 ->
  disjdom D2 D.
Proof.
  intros D D1 D2 Disj EQ.
  destruct Disj as [J1 J2].
  split; intros.
    apply J1. fsetdec.
    apply J2 in H. fsetdec.
Qed.

Lemma subst_ee_in_fv_ee : forall e x a y,
  y `in` fv_ee e ->
  y <> x ->
  y `in` fv_ee (subst_ee x a e).
Proof.
  induction e; intros; simpl; auto.
    destruct (a==x); subst; auto.
      contradict H; auto.
    
    simpl in H.
    destruct (in_dec y (fv_ee e1)) as [Je1 | Je1'].
      assert (J1:=@IHe1 x a y Je1 H0); auto.
      destruct (in_dec y (fv_ee e2)) as [Je2 | Je2'].
         assert (J2:=@IHe2 x a y Je2 H0); auto.
         contradict H; auto.
    
    simpl in H.
    destruct (in_dec y (fv_ee e1)) as [Je1 | Je1'].
      assert (J1:=@IHe1 x a y Je1 H0); auto.
      destruct (in_dec y (fv_ee e2)) as [Je2 | Je2'].
         assert (J2:=@IHe2 x a y Je2 H0); auto.
         contradict H; auto.

    simpl in H.
    destruct (in_dec y (fv_ee e1)) as [Je1 | Je1'].
      assert (J1:=@IHe1 x a y Je1 H0); auto.
      destruct (in_dec y (fv_ee e2)) as [Je2 | Je2'].
         assert (J2:=@IHe2 x a y Je2 H0); auto.
         contradict H; auto.
Qed.

Lemma open_ee_rec_fv_ee_lower : forall e1 e2 kk,
  fv_ee e1 [<=] fv_ee (open_ee_rec kk e2 e1).
Proof.
  induction e1; intros e2 kk; simpl; try solve [eauto | fsetdec].
    assert (J1:=@IHe1_1 e2 kk).
    assert (J2:=@IHe1_2 e2 kk).
    fsetdec.
    
    assert (J1:=@IHe1_1 e2 kk).
    assert (J2:=@IHe1_2 e2 (S kk)).
    fsetdec.

    assert (J1:=@IHe1_1 e2 kk).
    assert (J2:=@IHe1_2 e2 kk).
    fsetdec.
Qed.

Lemma open_ee_fv_ee_lower : forall e1 e2,
  fv_ee e1 [<=] fv_ee (open_ee e1 e2).
Proof.
  intros. apply open_ee_rec_fv_ee_lower.
Qed.

Lemma open_te_rec_fv_ee_eq : forall e1 t2 kk,
  fv_ee e1 [=] fv_ee (open_te_rec kk t2 e1).
Proof.
  induction e1; intros t2 kk; simpl; try solve [eauto | fsetdec].
Qed.

Lemma open_te_fv_ee_eq : forall e1 t2,
  fv_ee e1 [=] fv_ee (open_te e1 t2).
Proof.
  intros. apply open_te_rec_fv_ee_eq.
Qed.

Lemma typing_fv_ee_upper : forall E lE e t,
  typing E lE e t ->
  fv_ee e [<=] dom E `union` dom lE.
Proof.
  intros E lE e t Typing.
  (typing_cases (induction Typing) Case); intros; subst; simpl.
  Case "typing_var".
    apply binds_In in H0.
    fsetdec.
  Case "typing_lvar".
    fsetdec.
  Case "typing_abs".
    pick fresh x.
    assert (x `notin` L) as xnL. auto.
    apply H1 in xnL.
    assert (J:=@open_ee_fv_ee_lower e1 x).
    simpl in xnL.
    assert (fv_ee e1 [<=] union (dom E) (add x (dom D))) as JJ.
      fsetdec.
    assert (AtomSetImpl.diff (union (dom E) (add x (dom D))) {{x}} [=] union (dom E) (dom D)) as EQ.
      destruct_notin.
      clear NotInTac NotInTac0 NotInTac1 NotInTac2 NotInTac4 NotInTac6 J JJ Fr xnL.
      fsetdec.    
    assert (AtomSetImpl.diff (fv_ee e1) {{x}} [=] (fv_ee e1)) as EQ'.
      destruct_notin.
      clear NotInTac NotInTac3 NotInTac3 NotInTac1 NotInTac2 NotInTac4 NotInTac6 J JJ Fr xnL.
      fsetdec.    
    rewrite <- EQ. rewrite <- EQ'.
    clear EQ EQ' J Fr H0 H1 xnL.
    fsetdec.
  Case "typing_app".
    apply dom_lenv_split in H.
    rewrite H.
    fsetdec.
  Case "typing_tabs".
    pick fresh X.
    assert (X `notin` L) as XnL. auto.
    apply H0 in XnL.
    assert (J:=@open_te_fv_ee_eq e1 X).
    simpl in XnL.
    assert (fv_ee e1 [<=] union (add X (dom E)) (dom D)) as JJ.
      clear - J XnL. fsetdec.
    assert (AtomSetImpl.diff (union (add X (dom E)) (dom D)) {{X}} [=] union (dom E) (dom D)) as EQ.
      destruct_notin.
      clear NotInTac NotInTac0 NotInTac1 NotInTac3 NotInTac5 J JJ Fr XnL.
      fsetdec.    
    assert (AtomSetImpl.diff (fv_ee e1) {{X}} [=] (fv_ee e1)) as EQ'.
      destruct_notin.
      clear NotInTac NotInTac3 NotInTac5 NotInTac1 NotInTac2 NotInTac4 J JJ Fr XnL.
      fsetdec.    
    rewrite <- EQ. rewrite <- EQ'.
    clear EQ EQ' J Fr H0 XnL.
    fsetdec.
  Case "typing_tapp". auto.
  Case "typing_bang". auto.
  Case "typing_let".
    pick fresh x.
    assert (x `notin` L) as xnL. auto.
    apply H0 in xnL.
    assert (J:=@open_ee_fv_ee_lower e2 x).
    simpl in xnL.
    apply dom_lenv_split in H1.
    rewrite H1.
    assert (fv_ee e1 [<=] union (add x (dom E)) (union (dom D1) (dom D2))) as JJ1.
      clear - xnL IHTyping. fsetdec.
    assert (fv_ee e2 [<=] union (add x (dom E)) (union (dom D1) (dom D2))) as JJ2.
      clear - xnL J. fsetdec.
    assert (AtomSetImpl.diff (union (add x (dom E)) (union (dom D1) (dom D2))) {{x}} [=] union (dom E) (union (dom D1) (dom D2))) as EQ.
      destruct_notin.
      clear NotInTac NotInTac0 NotInTac1 NotInTac2 NotInTac4 NotInTac6 J JJ1 JJ2 Fr xnL.
      fsetdec.    
    assert (AtomSetImpl.diff (fv_ee e2) {{x}} [=] (fv_ee e2)) as EQ2.
      destruct_notin.
      clear - NotInTac2.
      fsetdec.    
    assert (AtomSetImpl.diff (fv_ee e1) {{x}} [=] (fv_ee e1)) as EQ1.
      destruct_notin.
      clear - NotInTac1.
      fsetdec.    
    rewrite <- EQ. rewrite <- EQ1. rewrite <- EQ2.
    clear EQ EQ1 EQ2 J Fr H0 H1 xnL.
    fsetdec.
  Case "typing_apair". fsetdec.
  Case "typing_fst". auto.
  Case "typing_snd". auto.
Qed.
     
Lemma open_ee_rec_fv_ee_upper : forall e1 e2 kk,
  fv_ee (open_ee_rec kk e2 e1) [<=] fv_ee e1 `union` fv_ee e2.
Proof.
  induction e1; intros e2 kk; simpl; try solve [eauto | fsetdec].
    destruct (kk==n); simpl.
      fsetdec.
      fsetdec.

    assert (J1:=@IHe1_1 e2 kk).
    assert (J2:=@IHe1_2 e2 kk).
    fsetdec.
    
    assert (J1:=@IHe1_1 e2 kk).
    assert (J2:=@IHe1_2 e2 (S kk)).
    fsetdec.

    assert (J1:=@IHe1_1 e2 kk).
    assert (J2:=@IHe1_2 e2 kk).
    fsetdec.
Qed.

Lemma open_ee_fv_ee_upper : forall e1 e2,
  fv_ee (open_ee e1 e2) [<=] fv_ee e1 `union` fv_ee e2.
Proof.
  intros. apply open_ee_rec_fv_ee_upper.
Qed.

Lemma typing_fv_ee_lower : forall E lE e t,
  typing E lE e t ->
  dom lE [<=] fv_ee e.
Proof.
  intros E lE e t Typing.
  (typing_cases (induction Typing) Case); intros; subst; simpl.
  Case "typing_var".
    apply binds_In in H0.
    fsetdec.
  Case "typing_lvar".
    fsetdec.
  Case "typing_abs".
    pick fresh x.
    assert (x `notin` L) as xnL. auto.
    apply H1 in xnL.
    assert (J:=@open_ee_fv_ee_upper e1 x).
    simpl in J, xnL.
    assert (add x (dom D) [<=] union (fv_ee e1) {{x}}) as JJ.
      clear Fr. fsetdec.
    assert (AtomSetImpl.diff (union (fv_ee e1) {{x}}) {{x}} [=] fv_ee e1) as EQ.
      destruct_notin.
      clear NotInTac NotInTac1 NotInTac2 NotInTac4 NotInTac6 J JJ Fr xnL.
      fsetdec.    
    assert (AtomSetImpl.diff (add x (dom D)) {{x}} [=] (dom D)) as EQ'.
      destruct_notin.
      clear NotInTac NotInTac1 NotInTac2 NotInTac4 NotInTac6 J JJ Fr xnL.
      fsetdec.    
    rewrite <- EQ. rewrite <- EQ'.
    clear EQ EQ' J Fr H0 H1 xnL.
    fsetdec.
  Case "typing_app".
    apply dom_lenv_split in H.
    rewrite H.
    fsetdec.
  Case "typing_tabs".
    pick fresh X.
    assert (X `notin` L) as XnL. auto.
    apply H0 in XnL.
    assert (J:=@open_te_fv_ee_eq e1 X).
    simpl in J.
    assert (dom D [<=] union (fv_ee e1) {{X}}) as JJ.
      clear Fr. fsetdec.
    assert (AtomSetImpl.diff (union (fv_ee e1) {{X}}) {{X}} [=] fv_ee e1) as EQ.
      destruct_notin.
      clear NotInTac5 NotInTac1 NotInTac2 NotInTac4 J JJ Fr XnL.
      fsetdec.    
    assert (AtomSetImpl.diff (dom D) {{X}} [=] (dom D)) as EQ'.
      destruct_notin.
      clear NotInTac NotInTac1 NotInTac2 NotInTac5 NotInTac3 J JJ Fr XnL.
      fsetdec.    
    rewrite <- EQ. rewrite <- EQ'.
    clear EQ EQ' J Fr H0 XnL.
    fsetdec.
  Case "typing_tapp". auto.
  Case "typing_bang". auto.
  Case "typing_let".
    pick fresh x.
    assert (x `notin` L) as xnL. auto.
    apply H0 in xnL.
    assert (J:=@open_ee_fv_ee_upper e2 x).
    simpl in J, xnL.
    apply dom_lenv_split in H1.
    rewrite H1.
    assert (add x (dom D2) [<=] union (fv_ee e2) {{x}}) as JJ2.
      clear Fr. fsetdec.
    assert (add x (dom D1) [<=] union (fv_ee e1) {{x}}) as JJ1.
      clear Fr. fsetdec.
    assert (AtomSetImpl.diff (union (fv_ee e1) {{x}}) {{x}} [=] fv_ee e1) as EQ1.
      destruct_notin.
      clear NotInTac NotInTac2 NotInTac4 NotInTac6 J JJ1 JJ2 Fr xnL.
      fsetdec.    
    assert (AtomSetImpl.diff (union (fv_ee e2) {{x}}) {{x}} [=] fv_ee e2) as EQ2.
      destruct_notin.
      clear NotInTac NotInTac1 NotInTac4 NotInTac6 J JJ1 JJ2 Fr xnL.
      fsetdec.    
    assert (AtomSetImpl.diff (add x (union (dom D1) (dom D2))) {{x}} [=] (union (dom D1) (dom D2))) as EQ'.
      destruct_notin. clear - NotInTac7 NotInTac8. fsetdec.
    rewrite <- EQ1. rewrite <- EQ2. rewrite <- EQ'.
    clear EQ1 EQ2 EQ' J Fr H0 H1 xnL.
    fsetdec.
  Case "typing_apair". fsetdec.
  Case "typing_fst". auto.
  Case "typing_snd". auto.
Qed.


