# Coq Developments for Linear Types

This repository contains some Coq developments for type systems related to
linear logic.  Some of the developments have been reported on in the following papers:

- [ Relational Parametricity for Polymorphic Linear Lambda Calculus ](http://www.cis.upenn.edu/~stevez/papers/ZZZ10.pdf)
- [ Lightweight linear types in System F^o ](http://www.cis.upenn.edu/~stevez/papers/MZZ10.pdf)
- [ Lolliproc: to Concurrency from Classical Linear Logic via Curry-Howard and Control ](http://www.cis.upenn.edu/~stevez/papers/MZ10.pdf)
- [ A Linear/Producer/Consumer model of Classical Linear Logic ](http://www.cis.upenn.edu/~stevez/papers/PZ14tr.pdf)

## Note:

This repository is quite old and the Coq code hasn't been compiled in quite a
while.  The bulk of the Coq development took place using Coq v. 8.2 and some of
the developments rely on Penn's
[Metatheory Library](http://www.cis.upenn.edu/~plclub/metalib/).  (See
'Dependencies' below.)


# Contents

##                        GENERAL DESCRIPTION

The formalism includes:
  * Proofs about the safety, logical relations, parametricity, contextual 
    equivalence, and applications of PDILL (a term calculus of Polymorphic 
    Dual Intuitionistic Linear Logic), and Linear System F^o (LinF) with 
    additive products type [1], 
    
  * Proofs about the safety, logical relations, parametricity, and applications 
    of (CBV and CBN) System F.

  * Some experiments with other formulations of linear type systems.

The code run with Coq 8.2pl1 (July. 2009).


## 

* DIRECTORY   : linf                          Contents
  -                Extra.v                            general metalib lemmas
  -                LinF_Definitions.v                 syntax and typings
  -                LinF_Infrastructure.v              metalib lemmas for linf
  -                LinF_Lemmas.v                      supporting lemmas
  -                LinF_Soundness.v                   preservation and progress
  -                LinF_ExtraLemmas.v                 additional lemmas

DESCRIPTION : Proofs of the safety of LinF with additive products type
  
* DIRECTORY   : parametricity                 Contents
  -                ExtraMetalib.v                     general metalib lemmas
  -	                LinF_PreLib.v                      supporting lemmas of metalib
  -                LinF_Parametricity_Pre.v           supporting lemmas of relations
  -                LinF_Parametricity_Interface.v     signature of logical relations
  -                LinF_Parametricity_Macro.v         macro lemmas
  -                LinF_Parametricity.v               parametricity
  -                LinF_Parametricity_App.v           applications
  -                LinF_ContextualEq_Def.             definitions of contexts
  -	               LinF_ContextualEq_Lemmas.v         supporting lemmas of contexts
  -                LinF_ContextualEq_Sound.v          sound to contextual equivalence
  -	               LinF_ContextualEq_Prop.v           properties of contextual equivalence
  -                LinF_ContextualEq_Complete.v       complete to contextual equivalence

DESCRIPTION : Proofs about the standard parametricity of LinF, which
                interprets types on closed relations.

* DIRECTORY   : parametricity                 Contents
  -                LinF_Renaming.v                    lemmas for variables renaming
  -                LinF_OParametricity_Pre.v          supporting lemmas of relations
  -                LinF_OParametricity_Interface.v    signature of logical relations
  -                LinF_OParametricity_Macro.v        macro lemmas
  -                LinF_OParametricity.v              parametricity
  -                LinF_OParametricity_App.v          applications
  -                LinF_OContextualEq_Lemmas.v        supporting lemmas of
  contexts
  -                LinF_OContextualEq_Sound.v         sound to contextual equivalence                                                                                                            

DESCRIPTION : Proofs about the novel parametricity of LinF, which
                interprets types on open relations.
                
* DIRECTORY   : bang                          Contents
  -                Extra.v                            general metalib lemmas
  -                Bang_Definitions.v                 syntax and typings
  -                Bang_Infrastructure.v              metalib lemmas for linf
  -                Bang_Lemmas.v                      supporting lemmas
  -                Bang_Soundness.v                   preservation and progress
  -                Bang_ExtraLemmas.v                 additional lemmas
  -                ExtraMetalib.v                     general metalib lemmas
  -                Bang_PreLib.v                      supporting lemmas of metalib
  -                Bang_Parametricity_Pre.v           supporting lemmas of relations
  -                Bang_Parametricity_Interface.v     signature of logical relations
  -                Bang_Parametricity_Macro.v         macro lemmas
  -                Bang_Parametricity.v               parametricity
  -                Bang_Parametricity_App.v           applications
  -                Bang_ContextualEq_Def.             definitions of contexts
  -                Bang_ContextualEq_Lemmas.v         supporting lemmas of contexts
  -                Bang_ContextualEq_Sound.v          sound to contextual equivalence
  -                Bang_ContextualEq_Prop.v           properties of contextual equivalence
  -                Bang_ContextualEq_Complete.v       complete to contextual equivalence
  -                Bang_Renaming.v                    lemmas for variables renaming
  -                Bang_OParametricity_Pre.v          supporting lemmas of relations
  -                Bang_OParametricity_Interface.v    signature of logical relations
  -                Bang_OParametricity_Macro.v        macro lemmas
  -                Bang_OParametricity.v              parametricity
  -                Bang_OParametricity_App.v          applications
  -                Bang_OParametricity_App2.v         applications
  -                Bang_OContextualEq_Lemmas.v        supporting lemmas of contexts
  -                Bang_OContextualEq_Sound.v         sound to contextual equivalence

DESCRIPTION : Proofs of the safety, closed parametricity, and
                  open parametricity for Bang.

* DIRECTORIES:  `algorithmic` and `setalgo`

DESCRIPTION : Experimental formulation of "standard" linear type system using
algorithmic typing judgments that compute the "residual" resources. 


##                              DEPENDENCIES

You will probably need 
* Coq 8.2pl1 (June. 2009) [2].
* A Coq library for programming language metatheory (20090714) [3].

This directory contains a corresponding metatheory library. So you can compile 
the code without additional installations.

[1] Karl Mazurak, Jianzhou Zhao, and Steve Zdancewic. Lightweight linear types in system F^o.
    2009. Unpublished Draft.
[2] http://coq.inria.fr/
[3] http://www.plclub.org/metalib


##                              COMPILING

Compiling and using this software:

- Run 'make' in ll/coq/linf
- Run 'make' in ll/coq/parametricity
- Run 'make' in ll/coq/bang
- Run 'make' in ll/sf/cbv, ll/sf/cbn and ll/sf/ocbv


##                              NOTES

1) The code in ll/coq/linf formalizes LinF with additive products type. It
does not formalize Boolean types at section 3.3, and multiplicative products 
type at section 4.3. The corresponding parametricity proofs do not cover
these two types either. 

Our contextual equivalence observes outcomes of complete programs by values of
a base type, $[[Bool]]$, containing two constants, $[[true]]$ and $[[false]]$. Two 
values are logically related with type $[[Bool]]$ iff they are both $[[true]]$ or $[[false]]$:

\[
\begin{array}{rll}
[[ GG ; 0 |- v ~~ v' isin Bool : s ]]
  & \triangleq & ([[v]] = [[true]] \land [[v']] = [[true]]) \lor ([[v]] = [[false]] \land [[v']] = [[false]]) \\ 
\end{array}
\]

We assume the following encodings to represent $[[Bool]]$ (in LinF_ContextualEq_Def.v):

Definition Two := (typ_all kn_nonlin (typ_arrow kn_nonlin (typ_bvar 0) (typ_arrow kn_nonlin (typ_bvar 0) (typ_bvar 0)))).
Definition tt := (exp_tabs kn_nonlin (exp_abs kn_nonlin (typ_bvar 0) (exp_abs kn_nonlin (typ_bvar 0) (exp_bvar 1)))).
Definition ff := (exp_tabs kn_nonlin (exp_abs kn_nonlin (typ_bvar 0) (exp_abs kn_nonlin (typ_bvar 0) (exp_bvar 0)))).

Also, we assume that logical relations are consistent at type $[[Bool]]$:

```
LinF_ContextualEq_Sound.v:
Axiom F_related_values__consistent : forall v v',
  F_related_values Two nil nil nil v v' ->
  ((v = tt /\ v' =tt) \/ (v = ff /\ v' =ff)).

LinF_OContextualEq_Sound.v:
Axiom F_Related_ovalues__consistent : forall v v',
  F_Related_ovalues Two nil nil nil v v' nil nil->
  ((v = tt /\ v' =tt) \/ (v = ff /\ v' =ff)).
```

The Bang formalism in ll/coq/bang uses the follow encodings for $[[Bool]]$
with the same above logical relation assumptions:

```
Definition Two := (typ_all (typ_arrow (typ_bang (typ_bvar 0)) (typ_arrow (typ_bang (typ_bvar 0)) (typ_bang (typ_bvar 0))))).
Definition tt := (exp_tabs 
                   (exp_abs 
                      (typ_bang (typ_bvar 0)) 
                      (exp_let
                        (exp_bvar 0)
                        (exp_abs 
                           (typ_bang (typ_bvar 0)) 
                           (exp_let
                            (exp_bvar 0)
                             (exp_bang 2)
                           )
                         )
                      )
                   )
                ).
Definition ff := (exp_tabs 
                  (exp_abs 
                     (typ_bang (typ_bvar 0)) 
                     (exp_let
                       (exp_bvar 0)
                       (exp_abs 
                          (typ_bang (typ_bvar 0)) 
                          (exp_let
                           (exp_bvar 0)
                            (exp_bang 0)
                          )
                        )
                     )
                  )
               ).
```

2) When proving Compositionality', another subtlety is that the relation   
  $\{ ([[v]], [[v']]) | \, \exists [[DD]], [[GG; DD |- v ~~ v' isin t : s]] \}$ 
must satisfy weakening on $[[s]]$.

\begin{lemma}[Compositionality']
\label{lem-osubst'}
  $$[[GG; DD |- v ~~ v' isin t' : (s1, a :-> (R, sl{t}, sr{t}), s2)]]$$
iff 
  $$[[GG; DD |- v ~~ v' isin (t'{t/a}) : (s1,s2)]],$$
where $[[R isin (s1l,s2l){t} <-> (s1r,s2r){t} : k -| GG]]$ is a relation such that 
$[[v relates v' by R]]$ iff $\exists [[DD]], \, [[GG; DD |- v ~~ v' isin t : (s1,s2)]]$.
\end{lemma}

By induction on the type structure of $[[t']]$, at case $\ottdrulename{ORV\_All}$ with 
type $[[forall a':k. t]]$, suppose picking a relation 
  $[[R' isin t2 <-> t2' : k -| GG]]$ 
for $[[a']]$, we should show that 
  $\{ ([[v]], [[v']]) | \, \exists [[DD]], [[GG; DD |- v ~~ v' isin t : (s, (a' :-> (R', t2, t2')))]] \}$ 
is equivalent to 
  $\{ ([[v]], [[v']]) | \, \exists [[DD]], [[GG; DD |- v ~~ v' isin t : (s)]] \}$. 
Here $[[a']]$ is free to existing variables. However, we do not know which $[[DD]]$ the 
relation takes before picking a free $[[a']]$, it is highly possible that $[[a']]$ is 
captured by $[[DD]]$ because $[[R]]$ is defined for arbitrary linear contexts. Fortunately, 
$[[a']]$ is a type variable and the domain of $[[DD]]$ consists of only term variables. 
Assuming that type variables and term variables are in different name spaces, we can always
pick an $[[a']]$ that is free for arbitrary $[[DD]]$.  

The current version of metatheory [3] does not support name spaces separation. Therefore, 
we assume two axioms in LinF_OParametricity.v:

```
Axiom ddom_gdom_disjoint : forall X x E,
  X `in` ddom_env E ->
  x `in` gdom_env E ->
  X <> x.
```

```
Axiom ddom_ldom_disjoint : forall X x E (lE:lenv),
  X `in` ddom_env E ->
  x `in` dom lE ->
  X <> x.
```

They state exactly the idea that type variables and term variables are in different name 
spaces, and the proofs only use these axioms at the above case to show that relation can be 
weaken. 

The Bang formalism in ll/coq/bang also makes the same assumptions.
