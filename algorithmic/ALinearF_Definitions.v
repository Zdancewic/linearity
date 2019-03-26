(** 
    Definitions of Algorithmic Lightweight Linear F
    Authors: Aileen Zhang, Jianzhou Zhao, and Steve Zdancewic.
*)

Require Export LinearF_Definitions.
Require Export LinearF_Infrastructure.

(* ********************************************************************** *)
(** * #<a name="env"></a># Algo Environments *)

(** In our presentation of System F with subtyping, we use a single
    environment for both typing and subtyping assumptions.  We
    formalize environments by representing them as association lists
    (lists of pairs of keys and values) whose keys are atoms.

    The [Metatheory] and [Environment] libraries provide functions,
    predicates, tactics, notations and lemmas that simplify working
    with environments.  The [Environment] library treats environments
    as lists of type [list (atom * A)].

    Since environments map [atom]s, the type [A] should encode whether
    a particular binding is a typing or subtyping assumption.  Thus,
    we instantiate [A] with the type [binding], defined below. *)

Inductive gbinding : Set :=
  | gbind_kn :  kn -> gbinding
  | gbind_typ : typ -> gbinding.

Notation genv := (list (atom * gbinding)).
Notation gempty := (@nil (atom * gbinding)).

Inductive dbinding : Set :=
  | dbind_typ : typ -> dbinding.

Notation denv := (list (atom * dbinding)).
Notation dempty := (@nil (atom * dbinding)).

(* ********************************************************************** *)
(** * #<a name="wf"></a># Well-formedness *)

(** A type [T] is well-formed with respect to an environment [E],
    denoted [(wf_typ E T)], when [T] is locally-closed and its free
    variables are bound in [E].  We need this relation in order to
    restrict the subtyping and typing relations, defined below, to
    contain only well-formed types.  (This relation is missing in the
    original statement of the POPLmark Challenge.)

    Note: It is tempting to define the premise of [wf_typ_var] as [(X
    `in` dom E)], since that makes the rule easier to apply (no need
    to guess an instantiation for [U]).  Unfortunately, this is
    incorrect.  We need to check that [X] is bound as a type-variable,
    not an expression-variable; [(dom E)] does not distinguish between
    the two kinds of bindings. *)
Inductive kn_order : kn -> kn -> Prop :=
  | kn_order_base :
     kn_order kn_nonlin kn_lin
  | kn_order_refl : forall K,
     kn_order K K
 .

Inductive wf_atyp : genv -> typ -> kn -> Prop :=
  | wf_atyp_var : forall K G (X : atom),
      ok G ->
      binds X (gbind_kn K) G ->
      wf_atyp G (typ_fvar X) K
  | wf_atyp_arrow : forall G K1 K2 K T1 T2,
      wf_atyp G T1 K1 ->
      wf_atyp G T2 K2 ->
      wf_atyp G (typ_arrow K T1 T2) K
  | wf_atyp_all : forall L G K1 K2 T2,
      (forall X : atom, X `notin` L ->
        wf_atyp ([(X, gbind_kn K1)] ++ G) (open_tt T2 X) K2) ->
      wf_atyp G (typ_all K1 T2) K2
  .

(** An environment E is well-formed, denoted [(wf_env E)], if each
    atom is bound at most at once and if each binding is to a
    well-formed type.  This is a stronger relation than the [ok]
    relation defined in the [Environment] library.  We need this
    relation in order to restrict the subtyping and typing relations,
    defined below, to contain only well-formed environments.  (This
    relation is missing in the original statement of the POPLmark
    Challenge.)  *)


Inductive wf_genv : genv -> Prop :=
  | wf_genv_empty :
      wf_genv gempty
  | wf_genv_kn : forall (G : genv) (X : atom) (K : kn),
      wf_genv G ->
      X `notin` dom G ->
      wf_genv ([(X, gbind_kn K)] ++ G)
  | wf_genv_typ : forall (G : genv) (x : atom) (T : typ) ,
      wf_genv G ->
      wf_atyp G T kn_nonlin ->
      x `notin` dom G ->
      wf_genv ([(x, gbind_typ T)] ++ G)
.

Inductive wf_denv : genv -> denv -> Prop :=
  | wf_denv_empty : forall G,
     wf_genv G ->
     wf_denv G dempty
  | wf_denv_typ : forall G D T x,
    wf_denv G D ->
    wf_atyp G T kn_lin ->
    x `notin` dom G ->
    x `notin` dom D ->
    wf_denv G ([(x, dbind_typ T)] ++ D)
.


Fixpoint dminus_var (x : atom) (l : list (atom*dbinding)){struct l} : list (atom*dbinding) :=
  match l with
  | nil => nil
  | (y, b)::tl => if (eq_atom_dec x y) then dminus_var x tl else (y, b)::(dminus_var x tl)
  end.

Notation "D [-] x" := (dminus_var x D) (at level 70, no associativity).

Fixpoint dminus (D : denv) (D' : denv) {struct D'} : denv :=
  match D' with 
  | nil => D
  | (y, b)::tl => dminus (D [-] y) tl
  end.

Notation "D -- D'" := (dminus D D') (at level 70, no associativity).

(* ********************************************************************** *)
(** * #<a name="typing_doc"></a># Algo Typing *)

Inductive atyping : genv -> denv -> exp -> typ -> denv -> Prop :=
  | atyping_uvar : forall G D x T,
      binds x (gbind_typ T) G ->
      wf_denv G D ->
      atyping G D x T D
  | atyping_lvar : forall G D x T,
      binds x (dbind_typ T) D ->
      wf_denv G D ->
      atyping G D x T (D [-] x)
   | atyping_uabs : forall L K G D V e1 T1 D',
      wf_atyp G V kn_nonlin ->
      (forall x : atom, x `notin` L ->
        atyping ([(x, gbind_typ V)] ++ G) D  (open_ee e1 x) T1 D') ->
      (K = kn_nonlin -> D = D') ->
      atyping G D (exp_abs K V e1) (typ_arrow K V T1) D' 
   | atyping_labs : forall L K G D V e1 T1 D',
      wf_atyp G V kn_lin ->
      (forall x : atom, x `notin` L ->
        atyping G ([(x, dbind_typ V)] ++ D)  (open_ee e1 x) T1 D') ->
      (K = kn_nonlin -> D = D') -> 
      atyping G D (exp_abs K V e1) (typ_arrow K V T1) D'
  | atyping_app : forall G T1 K D1 D2 D3 e1 e2 T2,
      atyping G D1 e1 (typ_arrow K T1 T2) D2->
      atyping G D2 e2 T1 D3 ->
      atyping G D1 (exp_app e1 e2) T2 D3
  | atyping_tabs : forall L G K e1 T1 D D' K',
      value e1 ->
      (forall X : atom, X `notin` L ->
	wf_atyp ([(X,gbind_kn K)] ++ G) (open_tt T1 X) K') ->
      (forall X : atom, X `notin` L ->
        atyping ([(X,gbind_kn K)] ++ G) D (open_te e1 X) (open_tt T1 X) D')->
      atyping G D (exp_tabs K e1) (typ_all K T1) D'
  | atyping_tapp : forall K K'  G e1 T T2 D D',
      atyping G D e1 (typ_all K T2) D' ->
      wf_atyp G T K' ->
      kn_order K' K -> 
      atyping G D (exp_tapp e1 T) (open_tt T2 T) D'
.

(* ********************************************************************** *)
(** * #<a name="auto"></a># Automation *)

(** We declare most constructors as [Hint]s to be used by the [auto]
    and [eauto] tactics.  We exclude constructors from the subtyping
    and typing relations that use cofinite quantification.  It is
    unlikely that [eauto] will find an instantiation for the finite
    set [L], and in those cases, [eauto] can take some time to fail.
    (A priori, this is not obvious.  In practice, one adds as hints
    all constructors and then later removes some constructors when
    they cause proof search to take too long.) *)

Hint Constructors wf_atyp wf_genv wf_denv ok.
Hint Resolve atyping_uvar atyping_lvar atyping_app atyping_tapp.

(* ********************************************************************** *)
(** * #<a name="cases"></a># Cases Tactic *)

Tactic Notation "typ_cases" tactic(first) tactic(c) :=
  first;
  [ c "typ_bvar" |  c "typ_fvar" | 
    c "typ_arrow" | c "typ_all" ].

Tactic Notation "exp_cases" tactic(first) tactic(c) :=
  first;
  [ c "exp_bvar" |  c "exp_fvar" | 
    c "exp_abs" | c "exp_app" |
    c "exp_tabs" | c "exp_tapp" ].

Tactic Notation "type_cases" tactic(first) tactic(c) :=
  first;
  [ c "type_var" | c "type_arrow" | c "type_all" ].

Tactic Notation "expr_cases" tactic(first) tactic(c) :=
  first;
  [ c "expr_var" | 
    c "expr_abs" | c "expr_app" |
    c "expr_tabs" | c "expr_tapp" ].

Tactic Notation "wf_atyp_cases" tactic(first) tactic(c) :=
  first;
  [ c "wf_atyp_var" | c "wf_atyp_arrow" | c "wf_typS_all" ].

Tactic Notation "wf_genv_cases" tactic(first) tactic(c) :=
  first;
  [ c "wf_genv_empty" | c "wf_genv_kn" | c "wf_genv_typ" ].

Tactic Notation "wf_denv_cases" tactic(first) tactic(c) :=
  first;
  [ c "wf_denv_empty" | c "wf_denv_typ" ].

Tactic Notation "value_cases" tactic(first) tactic(c) :=
  first;
  [ c "value_abs" | c "value_tabs" ].

Tactic Notation "red_cases" tactic(first) tactic(c) :=
  first;
  [ c "red_app_1" |  c "red_app_2" | 
    c "red_tapp" | c "red_abs" | c "red_tabs" ].

Tactic Notation "atyping_cases" tactic(first) tactic(c) :=
  first;
  [ c "atyping_uvar" | c "atyping_lvar" |
    c "atyping_uabs" | c "atyping_labs" | c "atyping_app" | 
    c "atyping_tabs" | c "atyping_tapp" ].

