Require Import List.

Section Linear.

  Parameter a : Type.
  Parameter b : Type.

  Parameter a_to_b : a -> b.
  Parameter b_to_a : b -> a.
  
  (* Idea: index types by the base interpretation.  How do we handle duality?*)
  Inductive tp :=
  | base : a -> tp         (* A *)
  | dual : b -> tp         (* A^ *)
  | asum : list tp -> tp   (* A1 + ... + An *)
  | aprd : list tp -> tp   (* A1 & ... & An *)
  | msum : list tp -> tp   (* A1 # ... # An *)                         
  | mprd : list tp -> tp   (* A1 * ... * An *)                           
  .

  Definition zer := asum nil.
  Definition top := aprd nil.
  Definition bot := msum nil.
  Definition one := mprd nil.

  Fixpoint dualize (t:tp) : tp :=
    match t with
      | base x => dual (a_to_b x)
      | dual x => base (b_to_a x)
      | asum ts => aprd (map dualize ts)
      | aprd ts => asum (map dualize ts)
      | msum ts => mprd (map dualize ts)
      | mprd ts => msum (map dualize ts)
    end.

End Linear.

Section Context.

  Parameter elt : Type.
  Parameter ctx : Type.

  Parameter empty : ctx.
  Parameter singleton : elt -> ctx.

  Parameter 

End Context.

(* 

G |- D     vs.     |- G


Indices: i, j ::= 
    o
    1 i
    2 i
    (i,j)


-----------
o:A |- o:A


G1 |- i:A ++ D1    G2 ++ j:A |- D2
----------------------------------
1.G1 ++ 2.G2 |- 1.D1 



G1 |- i:A ++ D1                 G2 |- j:B ++ D2
-----------------------------------------------
1.G1 ++ 2.G2 |-  (i,j):A*B ++ 1.D1 ++ 2.D2


i:A ++ j:B ++ G |- D
--------------------
(i,j):A*B ++ G |- D


G |- i:A ++ j:B ++ D
-----------------------
G |- (i,j) : A # B ++ D


G1 |- i:A ++ D1   G2 |- j:B ++ D2
-----------------------------------------
zip , G1 G2 |- (i,j) : A&B ++ zip , D1 D2



----------      ----------
o:A |- o:A      o:B |- o:B
--------------------------
1o:A, 2o:B |- (o,o):A*B



*)
  