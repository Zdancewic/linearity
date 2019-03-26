(** 
    Lightweight Linear F
    Steve Zdancewic and Karl Mazurak
*)

Require Export Metatheory.

(* ********************************************************************** *)
(** * #<a name="syntax"></a># Syntax (pre-terms) *)

Inductive kn : Set :=
  | kn_lin
  | kn_nonlin
.

Inductive typ : Set :=
  | typ_bvar : nat -> typ
  | typ_fvar : atom -> typ
  | typ_arrow : kn -> typ -> typ -> typ
  | typ_all : kn -> typ -> typ
.

Inductive exp : Set :=
  | exp_bvar : nat -> exp
  | exp_fvar : atom -> exp
  | exp_abs : kn -> typ -> exp -> exp
  | exp_app : exp -> exp -> exp
  | exp_tabs : kn -> exp -> exp
  | exp_tapp : exp -> typ -> exp
.

(** We declare the constructors for indices and variables to be
    coercions.  For example, if Coq sees a [nat] where it expects an
    [exp], it will implicitly insert an application of [exp_bvar];
    similar behavior happens for [atom]s.  Thus, we may write
    [(exp_abs typ_top (exp_app 0 x))] instead of [(exp_abs typ_top
    (exp_app (exp_bvar 0) (exp_fvar x)))]. *)

Coercion typ_bvar : nat >-> typ.
Coercion typ_fvar : atom >-> typ.
Coercion exp_bvar : nat >-> exp.
Coercion exp_fvar : atom >-> exp.


(* ********************************************************************** *)
(** * #<a name="open"></a># Opening terms *)

(** Opening replaces an index with a term.  This operation is required
    if we wish to work only with locally closed terms when going under
    binders (e.g., the typing rule for [exp_abs]).  It also
    corresponds to informal substitution for a bound variable, which
    occurs in the rule for beta reduction.

    We need to define three functions for opening due the syntax of
    Fsub, and we name them according to the following convention.
      - [tt]: Denotes an operation involving types appearing in types.
      - [te]: Denotes an operation involving types appearing in
        expressions.
      - [ee]: Denotes an operation involving expressions appearing in
        expressions.

    The notation used below for decidable equality on atoms and
    natural numbers (e.g., [K === J]) is defined in the [Metatheory]
    library.  The order of arguments to each "open" function is the
    same.  For example, [(open_tt_rec K U T)] can be read as
    "substitute [U] for index [K] in [T]."

    Note that we assume that [U] is locally closed (and similarly for
    the other opening functions).  This assumption simplifies the
    implementations of opening by letting us avoid shifting.  Since
    bound variables are indices, there is no need to rename variables
    to avoid capture.  Finally, we assume that these functions are
    initially called with index zero and that zero is the only unbound
    index in the term.  This eliminates the need to possibly subtract
    one in the case of indices. *)

Fixpoint open_tt_rec (K : nat) (U : typ) (T : typ)  {struct T} : typ :=
  match T with
  | typ_bvar J => if K === J then U else (typ_bvar J)
  | typ_fvar X => typ_fvar X
  | typ_arrow k T1 T2 => typ_arrow k (open_tt_rec K U T1) (open_tt_rec K U T2)
  | typ_all k T2 => typ_all k (open_tt_rec (S K) U T2)
  end.

Fixpoint open_te_rec (K : nat) (U : typ) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x => exp_fvar x
  | exp_abs k V e1 => exp_abs  k (open_tt_rec K U V)  (open_te_rec K U e1)
  | exp_app e1 e2 => exp_app  (open_te_rec K U e1) (open_te_rec K U e2)
  | exp_tabs k e1 => exp_tabs k  (open_te_rec (S K) U e1)
  | exp_tapp e1 V => exp_tapp (open_te_rec K U e1) (open_tt_rec K U V)
  end.

Fixpoint open_ee_rec (k : nat) (f : exp) (e : exp)  {struct e} : exp :=
  match e with
  | exp_bvar i => if k === i then f else (exp_bvar i)
  | exp_fvar x => exp_fvar x
  | exp_abs K V e1 => exp_abs K V (open_ee_rec (S k) f e1)
  | exp_app e1 e2 => exp_app (open_ee_rec k f e1) (open_ee_rec k f e2)
  | exp_tabs K e1 => exp_tabs K (open_ee_rec k f e1)
  | exp_tapp e1 V => exp_tapp (open_ee_rec k f e1) V
  end.

(** Many common applications of opening replace index zero with an
    expression or variable.  The following definitions provide
    convenient shorthands for such uses.  Note that the order of
    arguments is switched relative to the definitions above.  For
    example, [(open_tt T X)] can be read as "substitute the variable
    [X] for index [0] in [T]" and "open [T] with the variable [X]."
    Recall that the coercions above let us write [X] in place of
    [(typ_fvar X)], assuming that [X] is an [atom]. *)

Definition open_tt T U := open_tt_rec 0 U T.
Definition open_te e U := open_te_rec 0 U e.
Definition open_ee e1 e2 := open_ee_rec 0 e2 e1.


(* ********************************************************************** *)
(** * #<a name="lc"></a># Local closure *)

(** Recall that [typ] and [exp] define pre-terms; these datatypes
    admit terms that contain unbound indices.  A term is locally
    closed, or syntactically well-formed, when no indices appearing in
    it are unbound.  The proposition [(type T)] holds when a type [T]
    is locally closed, and [(expr e)] holds when an expression [e] is
    locally closed.

    The inductive definitions below formalize local closure such that
    the resulting induction principles serve as structural induction
    principles over (locally closed) types and (locally closed)
    expressions.  In particular, unlike the situation with pre-terms,
    there are no cases for indices.  Thus, these induction principles
    correspond more closely to informal practice than the ones arising
    from the definitions of pre-terms.

    The interesting cases in the inductive definitions below are those
    that involve binding constructs, e.g., [typ_all].  Intuitively, to
    check if the pre-term [(typ_all T1 T2)] is locally closed we much
    check that [T1] is locally closed, and that [T2] is locally closed
    when opened with a variable.  However, there is a choice as to how
    many variables to quantify over.  One possibility is to quantify
    over only one variable ("existential" quantification), as in
<<
  type_all : forall X T1 T2,
      type T1 ->
      type (open_tt T2 X) ->
      type (typ_all T1 T2)
>>  or we could quantify over as many variables as possible ("universal"
    quantification), as in
<<
  type_all : forall T1 T2,
      type T1 ->
      (forall X : atom, type (open_tt T2 X)) ->
      type (typ_all T1 T2)
>>  It is possible to show that the resulting relations are equivalent.
    The former makes it easy to build derivations, while the latter
    provides a strong induction principle.  McKinna and Pollack used
    both forms of this relation in their work on formalizing Pure Type
    Systems.

    We take a different approach here and use "cofinite
    quantification": we quantify over all but finitely many variables.
    This approach provides a convenient middle ground: we can build
    derivations reasonably easily and get reasonably strong induction
    principles.  With some work, one can show that the definitions
    below are equivalent to ones that use existential, and hence also
    universal, quantification. *)

Inductive type : typ -> Prop :=
  | type_var : forall X,
      type (typ_fvar X)
  | type_arrow : forall K T1 T2,
      type T1 ->
      type T2 ->
      type (typ_arrow K T1 T2)
  | type_all : forall L K T2,
      (forall X : atom, X `notin` L -> type (open_tt T2 X)) ->
      type (typ_all K T2)
.

Inductive expr : exp -> Prop :=
  | expr_var : forall x,
      expr (exp_fvar x)
  | expr_abs : forall L K T e1,
      type T ->
      (forall x : atom, x `notin` L -> expr (open_ee e1 x)) ->
      expr (exp_abs K T e1)
  | expr_app : forall e1 e2,
      expr e1 ->
      expr e2 ->
      expr (exp_app e1 e2)
  | expr_tabs : forall L K e1,
      (forall X : atom, X `notin` L -> expr (open_te e1 X)) ->
      expr (exp_tabs K e1)
  | expr_tapp : forall e1 V,
      expr e1 ->
      type V ->
      expr (exp_tapp e1 V)
.


(* ********************************************************************** *)
(** * #<a name="env"></a># Environments *)

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

Inductive binding : Set :=
  | bind_kn :  kn -> binding
  | bind_typ : typ -> binding.

Notation env := (list (atom * binding)).
Notation empty := (@nil (atom * binding)).

(** We also define a notation that makes it convenient to write one
    element lists.  This notation is useful because of our convention
    for building environments; see the examples below. *)

Notation "[ x ]" := (x :: nil).


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

Inductive wf_typ : env -> typ -> kn -> Prop :=
  | wf_typ_var : forall K E (X : atom),
      ok E ->
      binds X (bind_kn K) E ->
      wf_typ E (typ_fvar X) K
  | wf_typ_arrow : forall E K1 K2 K T1 T2,
      wf_typ E T1 K1 ->
      wf_typ E T2 K2 ->
      wf_typ E (typ_arrow K T1 T2) K
  | wf_typ_all : forall L E K1 K2 T2,
      (forall X : atom, X `notin` L ->
        wf_typ ([(X, bind_kn K1)] ++ E) (open_tt T2 X) K2) ->
      wf_typ E (typ_all K1 T2) K2
  | wf_typ_sub : forall E T,
      wf_typ E T kn_nonlin ->
      wf_typ E T kn_lin
.

(** An environment E is well-formed, denoted [(wf_env E)], if each
    atom is bound at most at once and if each binding is to a
    well-formed type.  This is a stronger relation than the [ok]
    relation defined in the [Environment] library.  We need this
    relation in order to restrict the subtyping and typing relations,
    defined below, to contain only well-formed environments.  (This
    relation is missing in the original statement of the POPLmark
    Challenge.)  *)

Inductive wf_env : env -> Prop :=
  | wf_env_empty :
      wf_env empty
  | wf_env_kn : forall (E : env) (X : atom) (K : kn),
      wf_env E ->
      X `notin` dom E ->
      wf_env ([(X, bind_kn K)] ++ E)
  | wf_env_typ : forall (E : env) (x : atom) (T : typ) (K : kn),
      wf_env E ->
      wf_typ E T K->
      x `notin` dom E ->
      wf_env ([(x, bind_typ T)] ++ E).

Inductive env_below_kn : env -> env -> kn -> Prop :=
  | env_below_empty : forall E K,
      wf_env E -> 
      env_below_kn E empty K
  | env_below_bind_kn   : forall E G X K1 K,
      env_below_kn E G K ->
      wf_env ([(X, bind_kn K1)] ++ G ++ E) ->
      env_below_kn E ([(X, bind_kn K1)]++G) K
  | env_below_bind_typ  : forall E G x T K,
      env_below_kn E G K ->
      wf_env ([(x, bind_typ T)] ++ G ++ E) ->
      wf_typ (G ++ E) T K ->
      env_below_kn E ([(x, bind_typ T)] ++ G) K
.

(* env_split E1 E2 E3 G  ==  G |- E1 \join E2 = E3 *)
Inductive env_split : env -> env -> env -> env -> Prop :=
  | env_split_empty:  forall G, wf_env G -> env_split empty empty empty G
  | env_split_kn:  forall E1 E2 E3 X K G, 
       env_split E1 E2 E3 G ->
       X `notin` dom E3 -> X `notin` dom G -> 
       env_split ([(X, bind_kn K)]++E1) ([(X, bind_kn K)]++E2) ([(X, bind_kn K)]++E3) G
  | env_split_nonlin:  forall E1 E2 E3 T x G, 
       env_split E1 E2 E3 G -> wf_typ (E3 ++ G) T kn_nonlin ->
       x `notin` dom E3 -> x `notin` dom G -> 
       env_split ([(x, bind_typ T)]++E1) ([(x, bind_typ T)]++E2) ([(x, bind_typ T)]++E3) G
  | env_split_lin_left: forall E1 E2 E3 T x G, 
       env_split E1 E2 E3 G -> wf_typ (E3 ++ G) T kn_lin ->
       x `notin` dom E2 -> x `notin` dom E3 -> x `notin` dom G ->
       env_split ([(x, bind_typ T)]++E1) E2 ([(x, bind_typ T)]++E3) G
  | env_split_lin_right: forall E1 E2 E3 T x G, 
       env_split E1 E2 E3 G -> wf_typ (E3 ++ G) T kn_lin ->
       x `notin` dom E1 -> x `notin` dom E3 -> x `notin` dom G ->
       env_split E1 ([(x, bind_typ T)]++E2) ([(x, bind_typ T)]++E3) G
.

(* ********************************************************************** *)
(** * #<a name="values"></a># Values *)

Inductive value : exp -> Prop :=
  | value_abs : forall K T e1,
      expr (exp_abs K T e1) ->
      value (exp_abs K T e1)
  | value_tabs : forall K e1,
      expr (exp_tabs K e1) ->
      value (exp_tabs K e1)
.

(* ********************************************************************** *)
(** * #<a name="typing_doc"></a># Typing *)

Inductive typing : env -> exp -> typ -> Prop :=
  | typing_var : forall E1 E2 x T,
      wf_env (E2 ++ ([(x, bind_typ T)] ++ E1)) ->
      env_below_kn empty (E2 ++ E1) kn_nonlin ->
      typing (E2 ++ ([(x, bind_typ T)] ++ E1)) (exp_fvar x) T
  | typing_abs : forall L K E V e1 T1 K1,
      env_below_kn empty E K ->
      wf_typ E V K1 -> 
      (forall x : atom, x `notin` L ->
        typing ([(x, bind_typ V)] ++ E) (open_ee e1 x) T1) ->
      typing E (exp_abs K V e1) (typ_arrow K V T1)
  | typing_app : forall T1 K E1 E2 E3 e1 e2 T2,
      typing E1 e1 (typ_arrow K T1 T2) ->
      typing E2 e2 T1 ->
      env_split E1 E2 E3 empty ->
      typing E3 (exp_app e1 e2) T2
  | typing_tabs : forall L E K e1 T1,
      value e1 ->
      (forall X : atom, X `notin` L ->
        typing ([(X, bind_kn K)] ++ E) (open_te e1 X) (open_tt T1 X)) ->
      typing E (exp_tabs K e1) (typ_all K T1)
  | typing_tapp : forall K E e1 T T2,
      typing E e1 (typ_all K T2) ->
      wf_typ E T K ->
      typing E (exp_tapp e1 T) (open_tt T2 T)
.




(* ********************************************************************** *)
(** * #<a name="reduction"></a># Reduction *)

Inductive red : exp -> exp -> Prop :=
  | red_app_1 : forall e1 e1' e2,
      expr e2 ->
      red e1 e1' ->
      red (exp_app e1 e2) (exp_app e1' e2)
  | red_app_2 : forall e1 e2 e2',
      value e1 ->
      red e2 e2' ->
      red (exp_app e1 e2) (exp_app e1 e2')
  | red_tapp : forall e1 e1' V,
      type V ->
      red e1 e1' ->
      red (exp_tapp e1 V) (exp_tapp e1' V)
  | red_abs : forall K T e1 v2,
      expr (exp_abs K T e1) ->
      value v2 ->
      red (exp_app (exp_abs K T e1) v2) (open_ee e1 v2)
  | red_tabs : forall K e1 T,
      expr (exp_tabs K e1) ->
      type T ->
      red (exp_tapp (exp_tabs K e1) T) (open_te e1 T)
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

Hint Constructors type expr wf_typ wf_env value red.
Hint Resolve typing_var typing_app typing_tapp.
