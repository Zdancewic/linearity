(** Authors: Jianzhou Zhao. *)

Require Import Bang_PreLib.
Require Import Coq.Arith.Max.

(* ********************************************************************** *)
(** * Closing terms *)

Fixpoint close_tt_rec (K : nat) (X : atom) (T : typ) {struct T} : typ :=
  match T with
    | typ_bvar J => typ_bvar J
    | typ_fvar Y => if X == Y then K else typ_fvar Y    
    | typ_arrow T1 T2 => typ_arrow (close_tt_rec K X T1) (close_tt_rec K X T2)
    | typ_all T1 => typ_all (close_tt_rec (S K) X T1)
    | typ_bang T1 => typ_bang (close_tt_rec K X T1)
    | typ_with T1 T2 => typ_with (close_tt_rec K X T1) (close_tt_rec K X T2)
  end.

Fixpoint close_te_rec (K : nat) (X : atom) (e : exp) {struct e} : exp :=
  match e with
    | exp_bvar i => exp_bvar i
    | exp_fvar x => exp_fvar x
    | exp_abs V e1 => exp_abs  (close_tt_rec K X V)  (close_te_rec K X e1)
    | exp_app e1 e2 => exp_app  (close_te_rec K X e1) (close_te_rec K X e2)
    | exp_tabs e1 => exp_tabs (close_te_rec (S K) X e1)
    | exp_tapp e1 V => exp_tapp (close_te_rec K X e1) (close_tt_rec K X V)
    | exp_bang e => exp_bang (close_te_rec K X e)
    | exp_let e1 e2 => exp_let  (close_te_rec K X e1) (close_te_rec K X e2)
    | exp_apair e1 e2 => exp_apair (close_te_rec K X e1) (close_te_rec K X e2)
    | exp_fst e => exp_fst (close_te_rec K X e)
    | exp_snd e => exp_snd (close_te_rec K X e)
  end.

Fixpoint close_ee_rec (k : nat) (x : atom) (e : exp) {struct e} : exp :=
  match e with
    | exp_bvar i => exp_bvar i
    | exp_fvar y => if x == y then k else exp_fvar y    
    | exp_abs V e1 => exp_abs V (close_ee_rec (S k) x e1)
    | exp_app e1 e2 => exp_app (close_ee_rec k x e1) (close_ee_rec k x e2)
    | exp_tabs e1 => exp_tabs (close_ee_rec k x e1)
    | exp_bang e => exp_bang (close_ee_rec k x e)
    | exp_let e1 e2 => exp_let (close_ee_rec k x e1) (close_ee_rec (S k) x e2)
    | exp_tapp e1 V => exp_tapp (close_ee_rec k x e1) V
    | exp_apair e1 e2 => exp_apair (close_ee_rec k x e1) (close_ee_rec k x e2)
    | exp_fst e => exp_fst (close_ee_rec k x e)
    | exp_snd e => exp_snd (close_ee_rec k x e)
  end.

Definition close_tt T X := close_tt_rec 0 X T.
Definition close_te e X := close_te_rec 0 X e.
Definition close_ee e x := close_ee_rec 0 x e.

Inductive ctx : Set :=
  | ctx_hole  : ctx
  | ctx_abs_free  :  typ -> ctx ->  ctx 
  | ctx_abs_capture : atom -> typ -> ctx ->  ctx 
  | ctx_app1  : ctx -> exp -> ctx
  | ctx_app2  : exp -> ctx ->  ctx
  | ctx_tabs_free  :  ctx ->  ctx 
  | ctx_tabs_capture  :  atom -> ctx ->  ctx 
  | ctx_tapp  : ctx -> typ -> ctx
  | ctx_bang : ctx -> ctx
  | ctx_let1 : ctx -> exp -> ctx
  | ctx_let2_free : exp -> ctx -> ctx
  | ctx_let2_capture : exp -> atom -> ctx -> ctx
  | ctx_apair1 : ctx -> exp -> ctx
  | ctx_apair2 : exp -> ctx -> ctx
  | ctx_fst : ctx -> ctx
  | ctx_snd : ctx -> ctx
  .

Tactic Notation "ctx_cases" tactic(first) tactic(c) :=
  first;
  [ c "ctx_hole" | 
    c "ctx_abs_free" | c "ctx_abs_capture" | c "ctx_app1" | c "ctx_app2" |
    c "ctx_tabs_free" | c "ctx_tabs_capture" |c "ctx_tapp" | 
    c "ctx_bang" | c "ctx_let1" | c "ctx_let2_free" |  c "ctx_let2_capture" | 
    c "ctx_apair1" | c "ctx_apair2" | c "ctx_fst" | c "ctx_snd" ].

Fixpoint open_tc_rec (K : nat) (U : typ) (C : ctx)  {struct C} : ctx :=
  match C with
  | ctx_hole  => ctx_hole
  | ctx_abs_free V C1 => ctx_abs_free (open_tt_rec K U V) (open_tc_rec K U C1) 
  | ctx_abs_capture x V C1 => ctx_abs_capture x (open_tt_rec K U V) (open_tc_rec K U C1) 
  | ctx_app1  C1 e2 => ctx_app1 (open_tc_rec K U C1) (open_te_rec K U e2)
  | ctx_app2  v1 C2 => ctx_app2 (open_te_rec K U v1) (open_tc_rec K U C2)
  | ctx_tabs_free C1 => ctx_tabs_free (open_tc_rec (S K) U C1)  
  | ctx_tabs_capture X C1 => ctx_tabs_capture X (open_tc_rec (S K) U C1)  
  | ctx_tapp C1 V => ctx_tapp (open_tc_rec K U C1) (open_tt_rec K U V)
  | ctx_bang C1 => ctx_bang (open_tc_rec K U C1)
  | ctx_let1 C1 e2 => ctx_let1 (open_tc_rec K U C1) (open_te_rec K U e2)
  | ctx_let2_free e1 C2 => ctx_let2_free (open_te_rec K U e1) (open_tc_rec K U C2) 
  | ctx_let2_capture e1 x C2 => ctx_let2_capture (open_te_rec K U e1) x (open_tc_rec K U C2) 
  | ctx_apair1 C1 e2 => ctx_apair1 (open_tc_rec K U C1) (open_te_rec K U e2)
  | ctx_apair2 e1 C2 => ctx_apair2 (open_te_rec K U e1) (open_tc_rec K U C2)
  | ctx_fst C1 => ctx_fst (open_tc_rec K U C1)
  | ctx_snd C1 => ctx_snd (open_tc_rec K U C1)
  end.

Fixpoint open_ec_rec (K : nat) (f : exp) (C : ctx)  {struct C} : ctx :=
  match C with
  | ctx_hole  => ctx_hole
  | ctx_abs_free V C1 => ctx_abs_free V (open_ec_rec (S K) f C1) 
  | ctx_abs_capture x V C1 => ctx_abs_capture x V (open_ec_rec (S K) f C1) 
  | ctx_app1  C1 e2 => ctx_app1 (open_ec_rec K f C1) (open_ee_rec K f e2)
  | ctx_app2  v1 C2 => ctx_app2 (open_ee_rec K f v1) (open_ec_rec K f C2)
  | ctx_tabs_free C1 => ctx_tabs_free (open_ec_rec K f C1)  
  | ctx_tabs_capture X C1 => ctx_tabs_capture X (open_ec_rec K f C1)  
  | ctx_tapp C1 V => ctx_tapp (open_ec_rec K f C1) V
  | ctx_bang C1 => ctx_bang (open_ec_rec K f C1)
  | ctx_let1 C1 e2 => ctx_let1 (open_ec_rec K f C1) (open_ee_rec (S K) f e2)
  | ctx_let2_free e1 C2 => ctx_let2_free (open_ee_rec K f e1) (open_ec_rec (S K) f C2) 
  | ctx_let2_capture e1 x C2 => ctx_let2_capture (open_ee_rec K f e1) x (open_ec_rec (S K) f C2) 
  | ctx_apair1 C1 e2 => ctx_apair1 (open_ec_rec K f C1) (open_ee_rec K f e2)
  | ctx_apair2 e1 C2 => ctx_apair2 (open_ee_rec K f e1) (open_ec_rec K f C2)
  | ctx_fst C1 => ctx_fst (open_ec_rec K f C1)
  | ctx_snd C1 => ctx_snd (open_ec_rec K f C1)
  end.

Fixpoint close_tc_rec (K : nat)(X : atom) (C : ctx)  {struct C} : ctx :=
  match C with
  | ctx_hole  => ctx_hole
  | ctx_abs_free V C1 => ctx_abs_free (close_tt_rec K X V) (close_tc_rec K X C1) 
  | ctx_abs_capture x V C1 => ctx_abs_capture x (close_tt_rec K X V) (close_tc_rec K X C1) 
  | ctx_app1  C1 e2 => ctx_app1 (close_tc_rec K X C1) (close_te_rec K X e2)
  | ctx_app2  v1 C2 => ctx_app2 (close_te_rec K X v1) (close_tc_rec K X C2)
  | ctx_tabs_free C1 => ctx_tabs_free (close_tc_rec (S K) X C1)  
  | ctx_tabs_capture Y C1 => ctx_tabs_capture Y (close_tc_rec (S K) X C1)  
  | ctx_tapp C1 V => ctx_tapp (close_tc_rec K X C1) (close_tt_rec K X V)
  | ctx_bang C1 => ctx_bang (close_tc_rec K X C1)
  | ctx_let1 C1 e2 => ctx_let1 (close_tc_rec K X C1) (close_te_rec K X e2)
  | ctx_let2_free e1 C2 => ctx_let2_free (close_te_rec K X e1) (close_tc_rec K X C2)
  | ctx_let2_capture e1 x C2 => ctx_let2_capture (close_te_rec K X e1) x (close_tc_rec K X C2)
  | ctx_apair1 C1 e2 => ctx_apair1 (close_tc_rec K X C1) (close_te_rec K X e2)
  | ctx_apair2 e1 C2 => ctx_apair2 (close_te_rec K X e1) (close_tc_rec K X C2)
  | ctx_fst C1 => ctx_fst (close_tc_rec K X C1)
  | ctx_snd C1 => ctx_snd (close_tc_rec K X C1)
  end.

Fixpoint close_ec_rec (K : nat) (x : atom) (C : ctx)  {struct C} : ctx :=
  match C with
  | ctx_hole  => ctx_hole
  | ctx_abs_free V C1 => ctx_abs_free V (close_ec_rec (S K) x C1) 
  | ctx_abs_capture y V C1 => ctx_abs_capture y V (close_ec_rec (S K) x C1) 
  | ctx_app1  C1 e2 => ctx_app1 (close_ec_rec K x C1) (close_ee_rec K x e2)
  | ctx_app2  v1 C2 => ctx_app2 (close_ee_rec K x v1) (close_ec_rec K x C2)
  | ctx_tabs_free C1 => ctx_tabs_free (close_ec_rec K x C1)  
  | ctx_tabs_capture X C1 => ctx_tabs_capture X (close_ec_rec K x C1)  
  | ctx_tapp C1 V => ctx_tapp (close_ec_rec K x C1) V
  | ctx_bang C1 => ctx_bang (close_ec_rec K x C1)
  | ctx_let1 C1 e2 => ctx_let1 (close_ec_rec K x C1) (close_ee_rec (S K) x e2)
  | ctx_let2_free e1 C2 => ctx_let2_free (close_ee_rec K x e1) (close_ec_rec (S K) x C2)
  | ctx_let2_capture e1 y C2 => ctx_let2_capture (close_ee_rec K x e1) y (close_ec_rec (S K) x C2)
  | ctx_apair1 C1 e2 => ctx_apair1 (close_ec_rec K x C1) (close_ee_rec K x e2)
  | ctx_apair2 e1 C2 => ctx_apair2 (close_ee_rec K x e1) (close_ec_rec K x C2)
  | ctx_fst C1 => ctx_fst (close_ec_rec K x C1)
  | ctx_snd C1 => ctx_snd (close_ec_rec K x C1)
  end.

Definition open_tc C U := open_tc_rec 0 U C.
Definition open_ec C e := open_ec_rec 0 e C.
Definition close_tc C X := close_tc_rec 0 X C.
Definition close_ec C x := close_ec_rec 0 x C.

Inductive context : ctx -> Prop :=
  | context_hole  : context ctx_hole
  | context_abs_free  :  forall L T C1,
      type T ->
      (forall x : atom, x `notin` L -> context (open_ec C1 x)) ->
      context (ctx_abs_free T C1) 
  | context_abs_capture  :  forall L y T C1,
      type T ->
      (forall x : atom, x `notin` L -> context (open_ec C1 x)) ->
      context (ctx_abs_capture y T C1) 
  | context_app1  : forall C1 e2, context C1 -> expr e2 -> context (ctx_app1 C1 e2)
  | context_app2  : forall e1 C2, expr e1 -> context C2 -> context (ctx_app2 e1 C2)
  | context_tabs_free  :  forall L C1,
      (forall X : atom, X `notin` L -> context (open_tc C1 X)) ->
      context (ctx_tabs_free C1) 
  | context_tabs_capture :  forall L Y C1,
      (forall X : atom, X `notin` L -> context (open_tc C1 X)) ->
      context (ctx_tabs_capture Y C1) 
  | context_tapp  : forall C1 V, context C1 -> type V -> context (ctx_tapp C1 V)
  | context_bang : forall C1, context C1 -> context (ctx_bang C1)
  | context_let1  : forall L C1 e2, 
       context C1 -> 
       (forall x : atom, x `notin` L -> expr (open_ee e2 x)) ->
       context (ctx_let1 C1 e2)
  | context_let2_free  : forall L e1 C2, 
       expr e1 -> 
      (forall x : atom, x `notin` L -> context (open_ec C2 x)) ->
       context (ctx_let2_free e1 C2)
  | context_let2_capture  : forall L y e1 C2, 
       expr e1 -> 
      (forall x : atom, x `notin` L -> context (open_ec C2 x)) ->
       context (ctx_let2_capture e1 y C2)
  | context_apair1 : forall C1 e2, context C1 -> expr e2 -> context (ctx_apair1 C1 e2)
  | context_apair2 : forall e1 C2,  expr e1 -> context C2 -> context (ctx_apair2 e1 C2)
  | context_fst : forall C1, context C1 -> context (ctx_fst C1)
  | context_snd : forall C1, context C1 -> context (ctx_snd C1)
  .

Inductive vcontext : ctx -> Prop :=
  | vcontext_abs_free : forall T C,  context (ctx_abs_free T C) -> vcontext (ctx_abs_free T C)
  | vcontext_abs_capture  : forall x T C,  context (ctx_abs_capture x T C) -> vcontext (ctx_abs_capture x T C)
  | vcontext_tabs_free  :  forall C,  context (ctx_tabs_free C) -> vcontext (ctx_tabs_free C)
  | vcontext_tabs_capture  :  forall X C,  context (ctx_tabs_capture X C) -> vcontext (ctx_tabs_capture X C)
  | vcontext_bang : forall C, context (ctx_bang C) -> vcontext (ctx_bang C)
  | vcontext_apair1 : forall C1 e2, context (ctx_apair1 C1 e2) -> vcontext (ctx_apair1 C1 e2)
  | vcontext_apair2 : forall v1 C2, context (ctx_apair2 v1 C2) -> vcontext (ctx_apair2 v1 C2)
  .

Hint Constructors ctx vcontext context.

Fixpoint shift_ee_rec (k : nat) (b : nat) (e : exp) {struct e} : exp :=
  match e with
    | exp_bvar i =>
        match (le_lt_dec b i) with
        | left _   (* b <= i *) => exp_bvar (i + k)
        | right _ (* b > i *)  => exp_bvar i
        end
    | exp_fvar x => exp_fvar x
    | exp_abs V e1 => exp_abs V (shift_ee_rec k (S b) e1)
    | exp_app e1 e2 => exp_app (shift_ee_rec k b e1) (shift_ee_rec k b e2)
    | exp_tabs e1 => exp_tabs (shift_ee_rec k b e1)
    | exp_tapp e1 V => exp_tapp (shift_ee_rec k b e1) V
    | exp_bang e => exp_bang (shift_ee_rec k b e)
    | exp_let e1 e2 => exp_let (shift_ee_rec k b e1) (shift_ee_rec k (S b) e2)
    | exp_apair e1 e2 => exp_apair (shift_ee_rec k b e1) (shift_ee_rec k b e2)
    | exp_fst e => exp_fst (shift_ee_rec k b e)
    | exp_snd e => exp_snd (shift_ee_rec k b e)
  end.

Fixpoint shift_tt_rec (k : nat) (b : nat) (t : typ) {struct t} : typ :=
  match t with
    | typ_bvar i =>
        match (le_lt_dec b i) with
        | left _   (* b <= i *) => typ_bvar (i + k)
        | right _ (* b > i *)  => typ_bvar i
        end
    | typ_fvar x => typ_fvar x
    | typ_arrow t1 t2 => typ_arrow (shift_tt_rec k b t1) (shift_tt_rec k b t2)
    | typ_all t1 => typ_all (shift_tt_rec k (S b) t1)
    | typ_bang t1 => typ_bang (shift_tt_rec k b t1)
    | typ_with t1 t2 => typ_with (shift_tt_rec k b t1) (shift_tt_rec k b t2)
  end.

Fixpoint shift_te_rec (k : nat) (b : nat) (e : exp) {struct e} : exp :=
  match e with
    | exp_bvar i => exp_bvar i
    | exp_fvar x => exp_fvar x
    | exp_abs V e1 => exp_abs (shift_tt_rec k b V) (shift_te_rec k b e1)
    | exp_app e1 e2 => exp_app (shift_te_rec k b e1) (shift_te_rec k b e2)
    | exp_tabs e1 => exp_tabs (shift_te_rec k (S b) e1)
    | exp_tapp e1 V => exp_tapp (shift_te_rec k b e1) (shift_tt_rec k b V)
    | exp_bang e => exp_bang (shift_te_rec k b e)
    | exp_let e1 e2 => exp_let (shift_te_rec k b e1) (shift_te_rec k b e2)
    | exp_apair e1 e2 => exp_apair (shift_te_rec k b e1) (shift_te_rec k b e2)
    | exp_fst e => exp_fst (shift_te_rec k b e)
    | exp_snd e => exp_snd (shift_te_rec k b e)
  end.

Definition shift_ee e := shift_ee_rec 1 0 e.
Definition shift_tt t := shift_tt_rec 1 0 t.
Definition shift_te e := shift_te_rec 1 0 e.

Fixpoint plug (C : ctx) (u : exp) {struct C} : exp :=
  match C  with 
  | ctx_hole  => u
  | ctx_abs_free V C1   => exp_abs V (plug C1 (shift_ee u))
  | ctx_abs_capture x V C1   => exp_abs V (plug C1 (close_ee (shift_ee u )x))
  | ctx_app1 C1 e2   => exp_app (plug C1 u) e2
  | ctx_app2  v1 C2  => exp_app v1 (plug C2 u)
  | ctx_tabs_free C1   => exp_tabs (plug C1 (shift_te u)) 
  | ctx_tabs_capture X C1   => exp_tabs (plug C1 (close_te (shift_te u) X)) 
  | ctx_tapp C1 V   => exp_tapp (plug C1 u) V
  | ctx_bang C1       => exp_bang (plug C1 u)
  | ctx_let1 C1 e2   => exp_let (plug C1 u) e2
  | ctx_let2_free e1 C2  => exp_let e1 (plug C2 (shift_ee u ))
  | ctx_let2_capture e1 x C2  => exp_let e1 (plug C2 (close_ee (shift_ee u )x))
  | ctx_apair1 C1 e2   => exp_apair (plug C1 u) e2
  | ctx_apair2 e1 C2  => exp_apair e1 (plug C2 u)
  | ctx_fst C1       => exp_fst (plug C1 u)
  | ctx_snd C1       => exp_snd (plug C1 u)
  end.

Fixpoint remove_gdom (E:env) {struct E } : env :=
  match E with
  | nil => nil
  | (X, bind_kn)::E => (X, bind_kn)::(remove_gdom E)
  | (x, bind_typ T)::E => (remove_gdom E)
  end.

Fixpoint shift_ec_rec (k : nat) (b : nat) (C : ctx) {struct C} : ctx :=
  match C with
  | ctx_hole => ctx_hole
  | ctx_abs_free V C1 => ctx_abs_free V (shift_ec_rec k (S b) C1)
  | ctx_abs_capture x V C1 => ctx_abs_capture x V (shift_ec_rec k (S b) C1)
  | ctx_app1 C1 e2 => ctx_app1 (shift_ec_rec k b C1) (shift_ee_rec k b e2)
  | ctx_app2 e1 C2 => ctx_app2 (shift_ee_rec k b e1) (shift_ec_rec k b C2)
  | ctx_tabs_free C1 => ctx_tabs_free (shift_ec_rec k b C1)
  | ctx_tabs_capture x C1 => ctx_tabs_capture x (shift_ec_rec k b C1)
  | ctx_tapp C1 V => ctx_tapp (shift_ec_rec k b C1) V
  | ctx_bang C1 => ctx_bang (shift_ec_rec k b C1)
  | ctx_let1 C1 e2 => ctx_let1 (shift_ec_rec k b C1) (shift_ee_rec k (S b) e2)
  | ctx_let2_free e1 C2 => ctx_let2_free (shift_ee_rec k b e1) (shift_ec_rec k (S b) C2)
  | ctx_let2_capture e1 x C2 => ctx_let2_capture (shift_ee_rec k b e1) x (shift_ec_rec k (S b) C2)
  | ctx_apair1 C1 e2 => ctx_apair1 (shift_ec_rec k b C1) (shift_ee_rec k b e2)
  | ctx_apair2 e1 C2 => ctx_apair2 (shift_ee_rec k b e1) (shift_ec_rec k b C2)
  | ctx_fst C1 => ctx_fst (shift_ec_rec k b C1)
  | ctx_snd C1 => ctx_snd (shift_ec_rec k b C1)
  end.

Fixpoint shift_tc_rec (k : nat) (b : nat) (C : ctx) {struct C} : ctx :=
  match C with
  | ctx_hole => ctx_hole
  | ctx_abs_free V C1 => ctx_abs_free (shift_tt_rec k b V) (shift_tc_rec k b C1)
  | ctx_abs_capture x V C1 => ctx_abs_capture x (shift_tt_rec k b V) (shift_tc_rec k b C1)
  | ctx_app1 C1 e2 => ctx_app1 (shift_tc_rec k b C1) (shift_te_rec k b e2)
  | ctx_app2 e1 C2 => ctx_app2 (shift_te_rec k b e1) (shift_tc_rec k b C2)
  | ctx_tabs_free C1 => ctx_tabs_free (shift_tc_rec k (S b) C1)
  | ctx_tabs_capture x C1 => ctx_tabs_capture x (shift_tc_rec k (S b) C1)
  | ctx_tapp C1 V => ctx_tapp (shift_tc_rec k b C1) (shift_tt_rec k b V)
  | ctx_bang C1 => ctx_bang (shift_tc_rec k b C1)
  | ctx_let1 C1 e2 => ctx_let1 (shift_tc_rec k b C1) (shift_te_rec k b e2)
  | ctx_let2_free e1 C2 => ctx_let2_free (shift_te_rec k b e1) (shift_tc_rec k b C2)
  | ctx_let2_capture e1 x C2 => ctx_let2_capture (shift_te_rec k b e1) x (shift_tc_rec k b C2)
  | ctx_apair1 C1 e2 => ctx_apair1 (shift_tc_rec k b C1) (shift_te_rec k b e2)
  | ctx_apair2 e1 C2 => ctx_apair2 (shift_te_rec k b e1) (shift_tc_rec k b C2)
  | ctx_fst C1 => ctx_fst (shift_tc_rec k b C1)
  | ctx_snd C1 => ctx_snd (shift_tc_rec k b C1)
  end.

Definition shift_ec C := shift_ec_rec 1 0 C.
Definition shift_tc C := shift_tc_rec 1 0 C.

Fixpoint plugC (C0 C:ctx) {struct C0} : ctx :=
  match C0  with 
  | ctx_hole  => C
  | ctx_abs_free V C1   => ctx_abs_free V (plugC C1 (shift_ec C ))
  | ctx_abs_capture x V C1   => ctx_abs_capture x V (plugC C1 (close_ec (shift_ec C ) x))
  | ctx_app1 C1 e2   => ctx_app1 (plugC C1 C) e2
  | ctx_app2  v1 C2  => ctx_app2 v1 (plugC C2 C)
  | ctx_tabs_free C1   => ctx_tabs_free (plugC C1 (shift_tc C)) 
  | ctx_tabs_capture X C1   => ctx_tabs_capture X (plugC C1 (close_tc (shift_tc C) X)) 
  | ctx_tapp C1 V   => ctx_tapp (plugC C1 C) V
  | ctx_bang C1       => ctx_bang (plugC C1 C)
  | ctx_let1 C1 e2   => ctx_let1 (plugC C1 C) e2
  | ctx_let2_free e1 C2  => ctx_let2_free e1 (plugC C2 (shift_ec C ))
  | ctx_let2_capture e1 x C2  => ctx_let2_capture e1 x (plugC C2 (close_ec (shift_ec C ) x))
  | ctx_apair1 C1 e2   => ctx_apair1 (plugC C1 C) e2
  | ctx_apair2 e1 C2  => ctx_apair2 e1 (plugC C2 C)
  | ctx_fst C1       => ctx_fst (plugC C1 C)
  | ctx_snd C1       => ctx_snd (plugC C1 C)
  end.

Fixpoint cbn_ctx (C : ctx)  {struct C} : Prop :=
  match C with
  | ctx_hole  => True
  | ctx_app1 C1 e2 => cbn_ctx C1 /\ expr e2 
  | ctx_tapp C1 V => cbn_ctx C1 /\ type V
  | ctx_let1 C1 e2 => cbn_ctx C1
  | ctx_fst C1 => cbn_ctx C1
  | ctx_snd C1 => cbn_ctx C1
  | _ => False
  end.

Fixpoint fv_tc (C : ctx) {struct C} : atoms :=
  match C with
  | ctx_hole  => {}
  | ctx_abs_free V C1 => (fv_tt V) `union` fv_tc C1
  | ctx_abs_capture x V C1 => (fv_tt V) `union` fv_tc C1
  | ctx_app1  C1 e2 => (fv_tc C1) `union` (fv_te e2)
  | ctx_app2  v1 C2 => (fv_te v1) `union` (fv_tc C2)
  | ctx_tabs_free C1 => fv_tc C1
  | ctx_tabs_capture X C1 => fv_tc C1
  | ctx_tapp C1 V => (fv_tc C1) `union` (fv_tt V)
  | ctx_bang C1 => (fv_tc C1)
  | ctx_let1 C1 e2 => (fv_tc C1) `union` (fv_te e2)
  | ctx_let2_free e1 C2 => (fv_te e1) `union` (fv_tc C2)
  | ctx_let2_capture e1 x C2 => (fv_te e1) `union` (fv_tc C2)
  | ctx_apair1 C1 e2 => (fv_tc C1) `union` (fv_te e2)
  | ctx_apair2 e1 C2 => (fv_te e1) `union` (fv_tc C2)
  | ctx_fst C1 => (fv_tc C1)
  | ctx_snd C1 => (fv_tc C1)
  end.

Fixpoint remove_typvar (E:env) {struct E} : env :=
  match E with
  | nil => nil 
  | (X, bind_kn)::E' => (remove_typvar E')
  | (x, bind_typ T)::E' => (x, bind_typ T)::remove_typvar E'
  end.


Fixpoint ftv_env (E : env) : atoms :=
  match E with
  | nil => Metatheory.empty
  | pair X (bind_kn) :: l => (ftv_env l)
  | pair x (bind_typ T) :: l => (fv_tt T) `union` (ftv_env l)
  end.

Fixpoint ftv_lenv (D : lenv) : atoms :=
  match D with
  | nil => Metatheory.empty
  | pair x (lbind_typ T) :: l => (union (fv_tt T) (ftv_lenv l))
  end.

Fixpoint remove_tmvar (E:env) {struct E} : env :=
  match E with
  | nil => nil 
  | (X, bind_kn)::E' => (X, bind_kn)::(remove_tmvar E')
  | (x, bind_typ T)::E' => remove_tmvar E'
  end.

Definition env_remove b E := Coq.Lists.List.remove eq_binding_dec b E.
Definition lenv_remove b lE := Coq.Lists.List.remove eq_lbinding_dec b lE.
Fixpoint env_remove2 (x:atom) (E:env) {struct E}: env :=
  match E with
  | nil => nil
  | (y, b)::E' =>
    if (x == y )
    then env_remove2 x E'
    else (y,b)::env_remove2 x E'
   end.  

Fixpoint cv_ec (C : ctx) {struct C} : atoms :=
  match C with
  | ctx_hole  => {}
  | ctx_abs_free V C1 => cv_ec C1
  | ctx_abs_capture x V C1 => {{x}} `union` cv_ec C1
  | ctx_app1  C1 e2 => (cv_ec C1)
  | ctx_app2  v1 C2 => (cv_ec C2)
  | ctx_tabs_free C1 => cv_ec C1
  | ctx_tabs_capture X C1 => {{X}} `union`  cv_ec C1
  | ctx_tapp C1 V => (cv_ec C1)
  | ctx_bang C1 => (cv_ec C1)
  | ctx_let1  C1 e2 => (cv_ec C1)
  | ctx_let2_free e1 C2 => (cv_ec C2)
  | ctx_let2_capture e1 x C2 => {{x}} `union` (cv_ec C2)
  | ctx_apair1 C1 e2 => (cv_ec C1)
  | ctx_apair2 e1 C2 => (cv_ec C2)
  | ctx_fst C1 => (cv_ec C1)
  | ctx_snd C1 => (cv_ec C1)
  end.

Fixpoint cv_tc (C : ctx) : atoms :=
  match C with
  | ctx_hole => Metatheory.empty
  | ctx_abs_free _ C1 => (cv_tc C1)
  | ctx_abs_capture x _ C1 => (cv_tc C1)
  | ctx_app1 C1 _ => cv_tc C1
  | ctx_app2 _ C2 => cv_tc C2
  | ctx_tabs_free C1 => (cv_tc C1)
  | ctx_tabs_capture X C1 => union (singleton X) (cv_tc C1)
  | ctx_tapp C1 _ => cv_tc C1
  | ctx_bang C1 => cv_tc C1
  | ctx_let1 C1 _ => cv_tc C1
  | ctx_let2_free _ C2 => cv_tc C2
  | ctx_let2_capture _ x C2 => cv_tc C2
  | ctx_apair1 C1 _ => cv_tc C1
  | ctx_apair2 _ C2 => cv_tc C2
  | ctx_fst C1 => cv_tc C1
  | ctx_snd C1 => cv_tc C1
  end.

Fixpoint exp_size (e : exp) {struct e} : nat :=
  match e with
  | exp_bvar i => 1
  | exp_fvar x => 1
  | exp_abs T e => 1 + exp_size e
  | exp_app e1 e2 => 1 + exp_size e1 + exp_size e2
  | exp_tabs e => 1 + exp_size e
  | exp_tapp e T => 1 + exp_size e
  | exp_bang e => 1 + exp_size e
  | exp_let e1 e2 => 1 + exp_size e1 + exp_size e2
  | exp_apair e1 e2 => 1 + exp_size e1 + exp_size e2
  | exp_fst e => 1 + exp_size e
  | exp_snd e => 1 + exp_size e
  end.

Fixpoint ctx_size (C : ctx) {struct C} : nat :=
  match C with
  | ctx_hole => 1
  | ctx_abs_free _ C1 => 1 +  ctx_size C1
  | ctx_abs_capture x _ C1 => 1 +  ctx_size C1
  | ctx_app1 C1 _ => 1 + ctx_size C1
  | ctx_app2 _ C2 => 1 + ctx_size C2
  | ctx_tabs_free C1 => 1 + ctx_size C1
  | ctx_tabs_capture X C1 => 1 + ctx_size C1
  | ctx_tapp C1 _ => 1 + ctx_size C1
  | ctx_bang C1 => 1 + ctx_size C1
  | ctx_let1 C1 _ => 1 + ctx_size C1
  | ctx_let2_free _ C2 => 1 + ctx_size C2
  | ctx_let2_capture _ x C2 => 1 + ctx_size C2
  | ctx_apair1 C1 _ => 1 + ctx_size C1
  | ctx_apair2 _ C2 => 1 + ctx_size C2
  | ctx_fst C1 => 1 + ctx_size C1
  | ctx_snd C1 => 1 + ctx_size C1
  end.
Fixpoint bexp_eupper (e : exp) {struct e} : nat :=
  match e with
  | exp_bvar i => i+1
  | exp_fvar x => 0
  | exp_abs T e => bexp_eupper e - 1
  | exp_app e1 e2 => max (bexp_eupper e1) (bexp_eupper e2)
  | exp_tabs e => bexp_eupper e
  | exp_tapp e T => bexp_eupper e
  | exp_bang e => bexp_eupper e
  | exp_let e1 e2 => max (bexp_eupper e1) ((bexp_eupper e2) - 1)
  | exp_apair e1 e2 => max (bexp_eupper e1) (bexp_eupper e2)
  | exp_fst e => bexp_eupper e
  | exp_snd e => bexp_eupper e
  end.

Fixpoint btyp_upper (t : typ) {struct t} : nat :=
  match t with
  | typ_bvar i => i+1
  | typ_fvar x => 0
  | typ_arrow t1 t2 => max (btyp_upper t1) (btyp_upper t2)
  | typ_all t => btyp_upper t - 1
  | typ_bang t => btyp_upper t
  | typ_with t1 t2 => max (btyp_upper t1) (btyp_upper t2)
  end.

Fixpoint bexp_tupper (e : exp) {struct e} : nat :=
  match e with
  | exp_bvar i => 0
  | exp_fvar x => 0
  | exp_abs T e => max (btyp_upper T) (bexp_tupper e)
  | exp_app e1 e2 => max (bexp_tupper e1) (bexp_tupper e2)
  | exp_tabs e => bexp_tupper e - 1
  | exp_tapp e T => max (bexp_tupper e) (btyp_upper T)
  | exp_bang e => bexp_tupper e
  | exp_let e1 e2 => max (bexp_tupper e1) (bexp_tupper e2)
  | exp_apair e1 e2 => max (bexp_tupper e1) (bexp_tupper e2)
  | exp_fst e => bexp_tupper e
  | exp_snd e => bexp_tupper e
  end.

Fixpoint fv_ec (C : ctx) {struct C} : atoms :=
  match C with
  | ctx_hole  => {}
  | ctx_abs_free V C1 => fv_ec C1
  | ctx_abs_capture x V C1 => fv_ec C1
  | ctx_app1  C1 e2 => (fv_ec C1) `union` (fv_ee e2)
  | ctx_app2  v1 C2 => (fv_ee v1) `union` (fv_ec C2)
  | ctx_tabs_free C1 => fv_ec C1
  | ctx_tabs_capture X C1 => fv_ec C1
  | ctx_tapp C1 V => (fv_ec C1)
  | ctx_bang C1 => (fv_ec C1)
  | ctx_let1 C1 e2 => (fv_ec C1) `union` (fv_ee e2)
  | ctx_let2_free e1 C2 => (fv_ee e1) `union` (fv_ec C2)
  | ctx_let2_capture e1 x C2 => (fv_ee e1) `union` (fv_ec C2)
  | ctx_apair1 C1 e2 => (fv_ec C1) `union` (fv_ee e2)
  | ctx_apair2 e1 C2 => (fv_ee e1) `union` (fv_ec C2)
  | ctx_fst C1 => (fv_ec C1)
  | ctx_snd C1 => (fv_ec C1)
  end.

Fixpoint subst_tc (Z : atom) (U : typ) (C : ctx) {struct C} : ctx :=
  match C with
  | ctx_hole => ctx_hole
  | ctx_abs_free V C1 => ctx_abs_free (subst_tt Z U V)  (subst_tc Z U C1)
  | ctx_abs_capture x V C1 => ctx_abs_capture x (subst_tt Z U V)  (subst_tc Z U C1)
  | ctx_app1 C1 e2 => ctx_app1  (subst_tc Z U C1) (subst_te Z U e2)
  | ctx_app2 v1 C2 => ctx_app2  (subst_te Z U v1) (subst_tc Z U C2)
  | ctx_tabs_free C1 => ctx_tabs_free  (subst_tc Z U C1)
  | ctx_tabs_capture x C1 => ctx_tabs_capture x  (subst_tc Z U C1)
  | ctx_tapp C1 V => ctx_tapp (subst_tc Z U C1) (subst_tt Z U V)
  | ctx_bang C1 => ctx_bang  (subst_tc Z U C1)
  | ctx_let1 C1 e2 => ctx_let1  (subst_tc Z U C1) (subst_te Z U e2)
  | ctx_let2_free e1 C2 => ctx_let2_free  (subst_te Z U e1) (subst_tc Z U C2)
  | ctx_let2_capture e1 x C2 => ctx_let2_capture  (subst_te Z U e1) x (subst_tc Z U C2)
  | ctx_apair1 C1 e2 => ctx_apair1  (subst_tc Z U C1) (subst_te Z U e2)
  | ctx_apair2 e1 C2 => ctx_apair2  (subst_te Z U e1) (subst_tc Z U C2)
  | ctx_fst C1 => ctx_fst  (subst_tc Z U C1)
  | ctx_snd C1 => ctx_snd  (subst_tc Z U C1)
  end.

Fixpoint subst_ec (z : atom) (u : exp) (C : ctx) {struct C} : ctx :=
  match C with
  | ctx_hole => ctx_hole
  | ctx_abs_free V C1 => ctx_abs_free V (subst_ec z u C1)
  | ctx_abs_capture x V C1 => ctx_abs_capture x V (subst_ec z u C1)
  | ctx_app1 C1 e2 => ctx_app1 (subst_ec z u C1) (subst_ee z u e2)
  | ctx_app2 e1 C2 => ctx_app2 (subst_ee z u e1) (subst_ec z u C2)
  | ctx_tabs_free C1 => ctx_tabs_free (subst_ec z u C1)
  | ctx_tabs_capture x C1 => ctx_tabs_capture x (subst_ec z u C1)
  | ctx_tapp C1 V => ctx_tapp (subst_ec z u C1) V
  | ctx_bang C1 => ctx_bang (subst_ec z u C1)
  | ctx_let1 C1 e2 => ctx_let1 (subst_ec z u C1) (subst_ee z u e2)
  | ctx_let2_free e1 C2 => ctx_let2_free (subst_ee z u e1) (subst_ec z u C2)
  | ctx_let2_capture e1 x C2 => ctx_let2_capture (subst_ee z u e1) x (subst_ec z u C2)
  | ctx_apair1 C1 e2 => ctx_apair1 (subst_ec z u C1) (subst_ee z u e2)
  | ctx_apair2 e1 C2 => ctx_apair2 (subst_ee z u e1) (subst_ec z u C2)
  | ctx_fst C1 => ctx_fst (subst_ec z u C1)
  | ctx_snd C1 => ctx_snd (subst_ec z u C1)
  end.

Fixpoint apply_delta_subst_ctx (dsubst: delta_subst) (C:ctx) {struct dsubst} :=
  match dsubst with
  | nil => C
  | (X, T)::dsubst' => apply_delta_subst_ctx dsubst' (subst_tc X T C)
  end
  .

Fixpoint apply_gamma_subst_ctx (gsubst: gamma_subst) (C:ctx) {struct gsubst} :=
  match gsubst with
  | nil => C
  | (x, E)::gsubst' => apply_gamma_subst_ctx gsubst' (subst_ec x E C)
  end
  .

Fixpoint bctx_eupper (C : ctx) {struct C} : nat :=
  match C with
  | ctx_hole  => 0
  | ctx_abs_free V C1 => bctx_eupper C1 - 1
  | ctx_abs_capture x V C1 => bctx_eupper C1 - 1
  | ctx_app1  C1 e2 => max (bctx_eupper C1) (bexp_eupper e2)
  | ctx_app2  v1 C2 => max (bexp_eupper v1) (bctx_eupper C2)
  | ctx_tabs_free C1 =>  bctx_eupper C1
  | ctx_tabs_capture X C1 =>  bctx_eupper C1
  | ctx_tapp C1 V => bctx_eupper C1
  | ctx_bang C1 => bctx_eupper C1
  | ctx_let1 C1 e2 => max (bctx_eupper C1) ((bexp_eupper e2) - 1)
  | ctx_let2_free e1 C2 => max (bexp_eupper e1) ((bctx_eupper C2) - 1)
  | ctx_let2_capture e1 x C2 => max (bexp_eupper e1) ((bctx_eupper C2) - 1)
  | ctx_apair1 C1 e2 => max (bctx_eupper C1) (bexp_eupper e2)
  | ctx_apair2 e1 C2 => max (bexp_eupper e1) (bctx_eupper C2)
  | ctx_fst C1 => bctx_eupper C1
  | ctx_snd C1 => bctx_eupper C1
  end.

Fixpoint bctx_tupper (C : ctx) {struct C} : nat :=
  match C with
  | ctx_hole  => 0
  | ctx_abs_free V C1 =>max (btyp_upper V) (bctx_tupper C1)
  | ctx_abs_capture x V C1 =>max (btyp_upper V) (bctx_tupper C1)
  | ctx_app1 C1 e2 => max (bctx_tupper C1) (bexp_tupper e2)
  | ctx_app2 v1 C2 => max (bexp_tupper v1) (bctx_tupper C2)
  | ctx_tabs_free C1 =>  bctx_tupper C1 -1
  | ctx_tabs_capture X C1 =>  bctx_tupper C1 -1
  | ctx_tapp C1 V => max (bctx_tupper C1) (btyp_upper V)
  | ctx_bang C1 => bctx_tupper C1
  | ctx_let1 C1 e2 => max (bctx_tupper C1) (bexp_tupper e2)
  | ctx_let2_free v1 C2 => max (bexp_tupper v1) (bctx_tupper C2)
  | ctx_let2_capture v1 x C2 => max (bexp_tupper v1) (bctx_tupper C2)
  | ctx_apair1 C1 e2 => max (bctx_tupper C1) (bexp_tupper e2)
  | ctx_apair2 e1 C2 => max (bexp_tupper e1) (bctx_tupper C2)
  | ctx_fst C1 => bctx_tupper C1
  | ctx_snd C1 => bctx_tupper C1
  end.

(*
  E lE t => C => E' lE' t'
*)
Inductive contexting : env -> lenv -> typ -> ctx -> env -> lenv -> typ -> Prop :=
  | contexting_hole : forall E D T,
      wf_lenv E D ->
      wf_typ E T ->
      contexting E D T ctx_hole E D T
  | contexting_abs_free : forall L E D T T1' C1 T2' E' D',
      wf_typ E' T1' -> 
      (forall x : atom, x `notin` L ->     
        contexting E D T (open_ec C1 x) E' ([(x, lbind_typ T1')] ++ D') T2') ->
      contexting E D T (ctx_abs_free T1' C1) E' D' (typ_arrow T1' T2')
  | contexting_abs_capture : forall E D T y T1' C1 T2' E' D',
      wf_typ E' T1' -> 
      binds y (lbind_typ T1') D' ->
      y `notin` gdom_env E `union` cv_ec C1 ->
      contexting E D T C1 E' D' T2' ->
      contexting E D T (ctx_abs_capture y T1' (close_ec C1 y)) E' (lenv_remove (y, (lbind_typ T1')) D') (typ_arrow T1' T2')
  | contexting_app1 : forall T1' E D T E' D1' D2' D3' C1 e2 T2',
      contexting E D T C1 E' D1' (typ_arrow T1' T2') ->
      typing E' D2' e2 T1' ->
      lenv_split E' D1' D2' D3' ->
      disjdom (fv_ee e2) (dom D) ->
      contexting E D T (ctx_app1 C1 e2) E' D3' T2'
  | contexting_app2 : forall T1' E D T E' D1' D2' D3' e1 C2 T2',
      typing E' D1' e1 (typ_arrow T1' T2') ->
      contexting E D T C2 E' D2' T1' ->
      lenv_split E' D1' D2' D3' ->
      disjdom (fv_ee e1) (dom D) ->
      contexting E D T (ctx_app2 e1 C2) E' D3' T2'
  | contexting_tabs_free : forall L E D T C1 T1' E' D',
      (forall X : atom, X `notin` L->   
        contexting E D T (open_tc C1 X) ([(X, bind_kn)] ++ E') D' (open_tt T1' X)) ->
      contexting E D T (ctx_tabs_free C1) E' D' (typ_all T1')
  | contexting_tabs_capture : forall E D T Y C1 T1' E' D',
      binds Y (bind_kn) E' ->
      Y `notin` cv_ec C1 ->
      contexting E D T C1 E' D' T1' ->
      wf_lenv (env_remove (Y, (bind_kn )) E') D'  ->
      contexting E D T (ctx_tabs_capture Y (close_tc C1 Y)) (env_remove (Y, (bind_kn)) E') D' (typ_all (close_tt T1' Y))
  | contexting_tapp : forall E D T C1 T' T2' E' D',
      contexting E D T C1 E' D' (typ_all T2') ->
      wf_typ E' T' ->
      contexting E D T (ctx_tapp C1 T') E' D' (open_tt T2' T')
  | contexting_bang : forall E D T C1 T1' E',
      contexting E D T C1 E' lempty T1' ->
      contexting E D T (ctx_bang C1) E' lempty (typ_bang T1')
  | contexting_let1 : forall L T1' E D T E' D1' D2' D3' C1 e2 T2',
      contexting E D T C1 E' D1' (typ_bang T1') ->
      (forall x : atom, x `notin` L ->     
        typing ([(x, bind_typ T1')] ++ E') D2' (open_ee e2 x) T2') ->      
      lenv_split E' D1' D2' D3' ->
      disjdom (fv_ee e2) (dom D) ->
      contexting E D T (ctx_let1 C1 e2) E' D3' T2'
  | contexting_let2_free : forall L E D T T1' e1 C2 T2' E' D1' D2' D3',
      typing E' D1' e1 (typ_bang T1') ->
      (forall x : atom, x `notin` L ->     
        contexting E D T (open_ec C2 x) ([(x, bind_typ T1')] ++ E') D2' T2') ->
      lenv_split E' D1' D2' D3' ->
      disjdom (fv_ee e1) (dom D) ->
      contexting E D T (ctx_let2_free e1 C2) E' D3' T2'
  | contexting_let2_capture : forall E D T y T1' e1 C2 T2' E' D1' D2' D3',
      typing (env_remove (y, (bind_typ T1')) E') D1' e1 (typ_bang T1') ->
      binds y (bind_typ T1') E' ->
      y `notin` dom D `union` cv_ec C2 ->
      contexting E D T C2 E' D2' T2' ->
      lenv_split (env_remove (y, (bind_typ T1')) E') D1' D2' D3' ->
      disjdom (fv_ee e1) (dom D) ->
      contexting E D T (ctx_let2_capture e1 y (close_ec C2 y)) (env_remove (y, (bind_typ T1')) E') D3' T2'
  | contexting_apair1 : forall E D T C1 e2 T1' T2' E' D',
      contexting E D T C1 E' D' T1' ->
      typing E' D' e2 T2' ->
      contexting E D T (ctx_apair1 C1 e2) E' D' (typ_with T1' T2')
  | contexting_apair2 : forall E D T e1 C2 T1' T2' E' D',
      typing E' D' e1 T1' ->
      contexting E D T C2 E' D' T2' ->
     contexting E D T (ctx_apair2 e1 C2) E' D' (typ_with T1' T2')
  | contexting_fst : forall E D T C1 T1' T2' E' D',
      contexting E D T C1 E' D' (typ_with T1' T2') ->
      contexting E D T (ctx_fst C1) E' D' T1'
  | contexting_snd : forall E D T C1 T1' T2' E' D',
      contexting E D T C1 E' D' (typ_with T1' T2') ->
      contexting E D T (ctx_snd C1) E' D' T2'
  .

Tactic Notation "contexting_cases" tactic(first) tactic(c) :=
  first;
  [ c "contexting_hole" |
     c "contexting_abs_free" |   c "contexting_abs_capture" |
     c "contexting_app1" | c "contexting_app2" | 
    c "contexting_tabs_free" |  c "contexting_tabs_capture" |   
     c "contexting_tapp" | 
     c "contexting_bang" | 
     c "contexting_let1" |
     c "contexting_let2_free" |   c "contexting_let2_capture" |
     c "contexting_apair1" | c "contexting_apair2" | 
     c "contexting_fst" | c "contexting_snd" ].

Hint Resolve contexting_hole contexting_app1 contexting_app2 contexting_tapp contexting_apair1 contexting_apair2 contexting_fst contexting_snd.

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
  let J := ltac_map (fun x : ctx => cv_ec x) in
  let K := ltac_map (fun x : ctx => fv_ec x) in
  let L := ltac_map (fun x : ctx => fv_tc x) in
  simplify_list_of_atom_sets (A ++ B ++ C ++ D ++ E ++ F ++ G ++ H ++ I ++ J ++ K ++ L).

Tactic Notation "pick" "fresh" ident(x) :=
  let L := gather_atoms in (pick fresh x for L).

Lemma vcontext__context : forall C,
  vcontext C -> context C.
Proof.
  intros C H.
  induction H; auto.
Qed.

Lemma env_remove_notin : forall E x b,
  x `notin` dom E ->
  env_remove (x, b) E = E.
Proof.
  induction E; intros; simpl; auto.
    destruct a; simpl in H.
    destruct (eq_binding_dec (x, b) (a, b0)); simpl.
      inversion e; subst.
      destruct_notin.
      contradict NotInTac; auto.

      rewrite IHE; auto.
Qed.

Lemma env_remove2_notin : forall E x,
  x `notin` dom E ->
  env_remove2 x E = E.
Proof.
  induction E; intros; simpl; auto.
    destruct a; simpl in H.
    destruct (x == a); simpl.
      inversion e; subst.
      destruct_notin.
      contradict NotInTac; auto.

      rewrite IHE; auto.
Qed.

Lemma env_remove_inv : forall E y b,
  wf_env E ->
  binds y b E ->
  exists E1, exists E2,
    env_remove (y, b) E = E1 ++ E2 /\
    E = E1 ++ [(y, b)] ++ E2.
Proof.
  intros E y b Wfe.
  generalize dependent y.
  generalize dependent b.
  induction Wfe; intros; simpl.
    inversion H.

    destruct b.
      analyze_binds H0.
        inversion BindsTacVal; subst.
          destruct (eq_binding_dec (X, bind_kn) (X, bind_kn)).
            exists nil. exists E.
            split; simpl; auto.
               apply env_remove_notin; auto.

            contradict n; auto.

          destruct (eq_binding_dec (y, bind_kn) (X, bind_kn)).
            inversion e; subst.
            exists nil. exists E.
            split; simpl; auto.
               apply env_remove_notin; auto.
              
            apply IHWfe in BindsTac.
            destruct BindsTac as [E1 [E2 [EQ1 EQ2]]]; subst.
            exists ((X, bind_kn)::E1). exists E2.
            split; simpl; auto.
               simpl_env. rewrite EQ1. auto.

      analyze_binds H0.
        apply IHWfe in BindsTac.
        destruct BindsTac as [E1 [E2 [EQ1 EQ2]]]; subst.
        destruct (eq_binding_dec (y, bind_typ t) (X, bind_kn)).
          inversion e.

          exists ((X, bind_kn)::E1). exists E2.
          split; simpl; auto.
            simpl_env. rewrite EQ1. auto.

    destruct b.
      analyze_binds H1.
        apply IHWfe in BindsTac.
        destruct BindsTac as [E1 [E2 [EQ1 EQ2]]]; subst.
        destruct (eq_binding_dec (y, bind_kn) (x, bind_typ T)).
          inversion e.

          exists ((x, bind_typ T)::E1). exists E2.
          split; simpl; auto.
            simpl_env. rewrite EQ1. auto.

      analyze_binds H1.
        inversion BindsTacVal; subst.
          destruct (eq_binding_dec (x, bind_typ T) (x, bind_typ T)).
            exists nil. exists E.
            split; simpl; auto.
               apply env_remove_notin; auto.

            contradict n; auto.

          destruct (eq_binding_dec (y, bind_typ t) (x, bind_typ T)).
            inversion e; subst.
            exists nil. exists E.
            split; simpl; auto.
               apply env_remove_notin; auto.
              
            apply IHWfe in BindsTac.
            destruct BindsTac as [E1 [E2 [EQ1 EQ2]]]; subst.
            exists ((x, bind_typ T)::E1). exists E2.
            split; simpl; auto.
               simpl_env. rewrite EQ1. auto.
Qed.

Lemma env_remove2_inv : forall E y b,
  wf_env E ->
  binds y b E ->
  exists E1, exists E2,
    env_remove2 y E = E1 ++ E2 /\
    E = E1 ++ [(y, b)] ++ E2.
Proof.
  intros E y b Wfe.
  generalize dependent y.
  generalize dependent b.
  induction Wfe; intros; simpl.
    inversion H.

    destruct b.
      analyze_binds H0.
        inversion BindsTacVal; subst.
          destruct (X==X).
            exists nil. exists E.
            split; simpl; auto.
               apply env_remove2_notin; auto.

            contradict n; auto.

          destruct (y==X).
            inversion e; subst.
            apply IHWfe in BindsTac.
            destruct BindsTac as [E1 [E2 [EQ1 EQ2]]]; subst.
            simpl_env in H. contradict H; auto.
              
            apply IHWfe in BindsTac.
            destruct BindsTac as [E1 [E2 [EQ1 EQ2]]]; subst.
            exists ((X, bind_kn)::E1). exists E2.
            split; simpl; auto.
               simpl_env. rewrite EQ1. auto.

      analyze_binds H0.
        apply IHWfe in BindsTac.
        destruct BindsTac as [E1 [E2 [EQ1 EQ2]]]; subst.
        destruct (y==X).
          subst.
          simpl_env in H.
          contradict H; auto.

          exists ((X, bind_kn)::E1). exists E2.
          split; simpl; auto.
            simpl_env. rewrite EQ1. auto.

    destruct b.
      analyze_binds H1.
        apply IHWfe in BindsTac.
        destruct BindsTac as [E1 [E2 [EQ1 EQ2]]]; subst.
        destruct (y == x).
          subst.
          simpl_env in H0.
          contradict H0; auto.

          exists ((x, bind_typ T)::E1). exists E2.
          split; simpl; auto.
            simpl_env. rewrite EQ1. auto.

      analyze_binds H1.
        inversion BindsTacVal; subst.
          destruct (x == x).
            exists nil. exists E.
            split; simpl; auto.
               apply env_remove2_notin; auto.

            contradict n; auto.

          destruct (y == x).
            inversion e; subst.
            apply IHWfe in BindsTac.
            destruct BindsTac as [E1 [E2 [EQ1 EQ2]]]; subst.
            simpl_env in H0. contradict H0; auto.
              
            apply IHWfe in BindsTac.
            destruct BindsTac as [E1 [E2 [EQ1 EQ2]]]; subst.
            exists ((x, bind_typ T)::E1). exists E2.
            split; simpl; auto.
               simpl_env. rewrite EQ1. auto.
Qed.

Lemma max_injective : forall a1 a2 b1 b2,
  a1 <= b1 ->
  a2 <= b2 ->
  max a1 a2 <= max b1 b2.
Proof.
  intros a1 a2 b1 b2 a1_le_b1 a2_le_b2.
  destruct (le_lt_dec  b1 b2).
    rewrite max_r with (n:=b1) (m:=b2); auto.
    destruct (le_lt_dec a1 a2).
      rewrite max_r with (n:=a1) (m:=a2); auto.
      rewrite max_l with (n:=a1) (m:=a2); omega.

    rewrite max_l with (n:=b1) (m:=b2); try solve [omega].
    destruct (le_lt_dec a1 a2).
      rewrite max_r with (n:=a1) (m:=a2); omega.
      rewrite max_l with (n:=a1) (m:=a2); omega.
Qed.

Lemma wf_lenv_notin_dom : forall E D x T,
  wf_lenv E D ->
  binds x (lbind_typ T) D ->
  x `notin` dom E.
Proof.
  intros E D x T Wfle Binds.
  generalize dependent x.
  generalize dependent T.
  induction Wfle; intros; simpl.
    fsetdec.

    destruct (x==x0); subst; auto.
      analyze_binds Binds.
      apply IHWfle in BindsTac; auto.
Qed.

Lemma mid_list_inv' : forall A E1 x (b b': A) E2 E1' E2',
  uniq (E1++[(x,b)]++E2) ->
  E1++[(x,b)]++E2 = E1'++[(x,b')]++E2' ->
  (E1 = E1' /\ E2 = E2' /\ b = b').
Proof.
  intros A E1 x b b' E2 E1' E2' Uniq EQ.
  generalize dependent E1'.
  induction E1; intros.
    simpl_env in EQ.
    apply one_eq_app in EQ.
    destruct EQ as [[E1'' [EQ1 EQ2]]|[EQ1 EQ2]]; subst.
      simpl_env in Uniq.
      inversion Uniq; subst.
      simpl_env in H3.
      destruct_notin.
      contradict NotInTac; auto.

      simpl_env in EQ2.
      inversion EQ2; subst. auto.

    destruct a.
    simpl_env in EQ.
    apply one_eq_app in EQ.
    destruct EQ as [[E1'' [EQ1 EQ2]]|[EQ1 EQ2]]; subst.
      simpl_env in Uniq.
      inversion Uniq; subst.
      simpl_env in H1.
      apply IHE1 with (E1':=E1'') in H1; auto.
      destruct H1; subst. auto.

      simpl_env in EQ2.
      inversion EQ2; subst.
      simpl_env in Uniq.
      inversion Uniq; subst.
      simpl_env in H3.
      destruct_notin.
      contradict NotInTac; auto.
Qed.

Lemma app_mid_inv : forall A (E1 E2 F1 F2:list (atom*A)) x b,
  uniq (E1 ++ E2) ->
  E1 ++ E2 = F1 ++ [(x, b)] ++ F2 ->
  (exists D, E1 = F1 ++ [(x, b)] ++ D /\ F2 = D ++ E2) \/
  (exists D, F1 = E1 ++ D /\ E2 = D ++ [(x, b)] ++ F2).
Proof.
  intros A E1 E2 F1 F2 x b Uniq EQ.
  remember (E1++E2) as E.
  generalize dependent E1.
  generalize dependent E2.
  generalize dependent F1.
  generalize dependent F2.
  induction Uniq; intros; subst.
    symmetry in EQ.
    contradict EQ.
    simpl.
    apply app_cons_not_nil.

    assert (uniq (F1++[(x, b)]++F2)) as Uniq'.
      rewrite <- EQ. auto.
    assert (x `notin` dom F2) as xnF2.
      apply fresh_mid_tail in Uniq'; auto.
    apply one_eq_app in HeqE. destruct HeqE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst.
      apply one_eq_app in EQ. destruct EQ as [[F0' [fEQ1' fEQ2']] | [fEQ1' fEQ2']]; subst; auto.
        apply IHUniq with (F2:=F2) (F1:=F0') (E1:=E0') (E3:=E2) in fEQ2'; auto.
        destruct fEQ2' as [[D [dEQ1 dEQ2]] | [D [dEQ1 dEQ2]]]; subst.
          left. exists D. split; auto.
          right. exists D. split; auto.    

        simpl_env in *.
        inversion fEQ2'; subst.
        left. exists E0'. split; auto.
      apply one_eq_app in EQ. destruct EQ as [[F0' [fEQ1' fEQ2']] | [fEQ1' fEQ2']]; subst; auto.
        right. exists ((x0,a)::F0'). split; auto.
 
        simpl_env in fEQ2'. 
        inversion fEQ2'; subst.
         right. exists nil. split; auto.
Qed.

Lemma env_remove_sub : forall E y b,
  fv_env (env_remove (y, b) E) [<=] fv_env E.
Proof.
  induction E; intros y b; simpl.
    fsetdec.

    destruct a.   
    destruct b0. 
      destruct (eq_binding_dec (y,b)  (a, bind_kn)); simpl.
        inversion e; subst. 
        assert (J:=@IHE a (bind_kn)). 
        fsetdec.

        assert (J:=@IHE y b). 
        fsetdec.

      destruct (eq_binding_dec (y,b)  (a, bind_typ t)); simpl.
        inversion e; subst. 
        assert (J:=@IHE a (bind_typ t)). 
        fsetdec.

        assert (J:=@IHE y b). 
        fsetdec.
Qed.

Lemma env_remove2_sub : forall E y,
  fv_env (env_remove2 y E) [<=] fv_env E.
Proof.
  induction E; intros y; simpl.
    fsetdec.

    destruct a.
    destruct b.   
      destruct (y == a); simpl.
        inversion e; subst. 
        assert (J:=@IHE a). 
        fsetdec.

        assert (J:=@IHE y). 
        fsetdec.

      destruct (y == a); simpl.
        inversion e; subst. 
        assert (J:=@IHE a). 
        fsetdec.

        assert (J:=@IHE y). 
        fsetdec.
Qed.

Lemma env_remove_ddom_sub : forall E y b,
  ddom_env (env_remove (y, b) E) [<=] ddom_env E.
Proof.
  induction E; intros y b; simpl.
    fsetdec.

    destruct a.   
    destruct b0. 
      destruct (eq_binding_dec (y,b)  (a, bind_kn)); simpl.
        inversion e; subst. 
        assert (J:=@IHE a (bind_kn)). 
        fsetdec.

        assert (J:=@IHE y b). 
        fsetdec.

      destruct (eq_binding_dec (y,b)  (a, bind_typ t)); simpl.
        inversion e; subst. 
        assert (J:=@IHE a (bind_typ t)). 
        fsetdec.

        assert (J:=@IHE y b). 
        fsetdec.
Qed.

Lemma env_remove2_ddom_sub : forall E y,
  ddom_env (env_remove2 y E) [<=] ddom_env E.
Proof.
  induction E; intros y b; simpl.
    fsetdec.

    destruct a.   
    destruct b0. 
      destruct (y == a); simpl.
        inversion e; subst. 
        assert (J:=@IHE a). 
        fsetdec.

        assert (J:=@IHE y). 
        fsetdec.

      destruct (y == a); simpl.
        inversion e; subst. 
        assert (J:=@IHE a). 
        fsetdec.

        assert (J:=@IHE y). 
        fsetdec.
Qed.

Lemma notin_fv_env : forall E y t,
  wf_env E ->
  binds y (bind_typ t) E ->
  y `notin` fv_env (env_remove (y, bind_typ t) E).
Proof.
  intros E y t Wfe Binds.
  generalize dependent y.
  generalize dependent t.
  induction Wfe; intros t y Binds; simpl.
    inversion Binds.
     
    analyze_binds_uniq Binds.
    destruct (eq_binding_dec (y, bind_typ t) (X, bind_kn)); simpl.
      inversion e; subst.
      apply IHWfe in BindsTac. auto.

    analyze_binds Binds.
      inversion BindsTacVal; subst.
      destruct (eq_binding_dec (x, bind_typ T) (x, bind_typ T)); simpl.
        assert (J:=@env_remove_sub E x (bind_typ T)).
        assert (x `notin` fv_env E) as J'.
          apply wfe_dom_fv_env with (x:=x) in Wfe; auto.
        fsetdec.

        contradict n; auto.

      assert (y `notin` ddom_env E) as J.
        eapply notin_ddom_env; eauto.
      assert (y `notin` fv_tt T) as J'.
        apply dnotin_fv_wf with (X:=y) in H; auto.
      assert (y `in` dom E) as J''.
        apply binds_In in BindsTac; auto.
      apply IHWfe in BindsTac.
      destruct (eq_binding_dec (y, bind_typ t) (x, bind_typ T)); simpl.
        inversion e; subst.
        assert (J1:=@env_remove_sub E x (bind_typ T)).
        assert (x `notin` fv_env E) as J2.
          apply wfe_dom_fv_env with (x:=x) in Wfe; auto.
        fsetdec.

        destruct (y == x); subst.
          contradict H0; auto.
          fsetdec.
Qed.

Lemma notin_fv_env2 : forall E y t,
  wf_env E ->
  binds y (bind_typ t) E ->
  y `notin` fv_env (env_remove2 y E).
Proof.
  intros E y t Wfe Binds.
  generalize dependent y.
  generalize dependent t.
  induction Wfe; intros t y Binds; simpl.
    inversion Binds.
     
    analyze_binds_uniq Binds.
    destruct (y == X); simpl.
      inversion e; subst.
      simpl_env in H0. contradict H0; auto.

      apply IHWfe in BindsTac. auto.

    analyze_binds Binds.
      inversion BindsTacVal; subst.
      destruct (x == x); simpl.
        assert (J:=@env_remove2_sub E x).
        assert (x `notin` fv_env E) as J'.
          apply wfe_dom_fv_env with (x:=x) in Wfe; auto.
        fsetdec.

        contradict n; auto.

      assert (y `notin` ddom_env E) as J.
        eapply notin_ddom_env; eauto.
      assert (y `notin` fv_tt T) as J'.
        apply dnotin_fv_wf with (X:=y) in H; auto.
      assert (y `in` dom E) as J''.
        apply binds_In in BindsTac; auto.
      apply IHWfe in BindsTac.
      destruct (y == x); simpl.
        inversion e; subst.
        assert (J1:=@env_remove2_sub E x).
        assert (x `notin` fv_env E) as J2.
          apply wfe_dom_fv_env with (x:=x) in Wfe; auto.
        fsetdec.

        destruct (y == x); subst.
          contradict H0; auto.
          fsetdec.
Qed.

Lemma wft_fv_tt_dsub : forall E t,
  wf_typ E t ->
  fv_tt t [<=] ddom_env E.
Proof.
  intros E t Wft.
  induction Wft; simpl.
    apply dbinds_In in H0. fsetdec.
    fsetdec.

    pick fresh X.
    assert (X `notin` L) as XnL. auto.
    apply H0 in XnL.
    assert (fv_tt T1 [<=] fv_tt (open_tt T1 X)) as sub.
      apply open_tt_fv_tt_lower; auto.
    assert (fv_tt T1 [<=] ddom_env ([(X, bind_kn)]++E)) as sub'.
      fsetdec.
    assert (AtomSetImpl.diff (fv_tt T1) {{X}} [<=] AtomSetImpl.diff (ddom_env ([(X, bind_kn)]++E)) {{X}}) as sub''.
      fsetdec.
    assert (AtomSetImpl.diff (fv_tt T1) {{X}}[=](fv_tt T1)) as eq.
      clear XnL sub sub' sub''. fsetdec.
    assert (X `notin` ddom_env E) as XnE.
      apply free_env__free_ddom; auto.
    assert (AtomSetImpl.diff (ddom_env ([(X, bind_kn)]++E)) {{X}}[=]ddom_env E) as eq'.
      clear - XnE. simpl_env. fsetdec.
    rewrite <- eq. rewrite <- eq'.
    assumption.

    fsetdec.

    fsetdec.
Qed.

Lemma env_remove_typ_inv : forall E y T,
  wf_env E ->
  binds y (bind_typ T) E ->
  exists E1, exists E2,
    env_remove (y, bind_typ T) E = E1 ++ E2 /\
    E = E1 ++ [(y, bind_typ T)] ++ E2 /\
    fv_tt T [<=] ddom_env E2.
Proof.
  intros E y T Wfe.
  generalize dependent y.
  generalize dependent T.
  induction Wfe; intros; simpl.
    inversion H.

    analyze_binds H0.
        apply IHWfe in BindsTac.
        destruct BindsTac as [E1 [E2 [EQ1 [EQ2 Fv]]]]; subst.
        destruct (eq_binding_dec (y, bind_typ T) (X, bind_kn)).
          inversion e.

          exists ((X, bind_kn)::E1). exists E2.
          split; simpl; auto.
            simpl_env. rewrite EQ1. auto.

    analyze_binds H1.
        inversion BindsTacVal; subst.
        destruct (eq_binding_dec (x, bind_typ T) (x, bind_typ T)).
            exists nil. exists E.
            split.
               apply env_remove_notin; auto.
            split; simpl; auto.
               eapply wft_fv_tt_dsub; eauto.

            contradict n; auto.

            apply IHWfe in BindsTac.
            destruct BindsTac as [E1 [E2 [EQ1 [EQ2 Fv]]]]; subst.
            destruct (eq_binding_dec (y, bind_typ T0) (x, bind_typ T)).
              inversion e; subst.
              simpl_env in H0. destruct_notin.
              contradict NotInTac; auto.

              exists ((x, bind_typ T)::E1). exists E2.
              split.
                 simpl_env. rewrite EQ1. auto.
              split; simpl; auto.
Qed.              

Lemma env_remove2_typ_inv : forall E y T,
  wf_env E ->
  binds y (bind_typ T) E ->
  exists E1, exists E2,
    env_remove2 y E = E1 ++ E2 /\
    E = E1 ++ [(y, bind_typ T)] ++ E2 /\
    fv_tt T [<=] ddom_env E2.
Proof.
  intros E y T Wfe.
  generalize dependent y.
  generalize dependent T.
  induction Wfe; intros; simpl.
    inversion H.

    analyze_binds H0.
        apply IHWfe in BindsTac.
        destruct BindsTac as [E1 [E2 [EQ1 [EQ2 Fv]]]]; subst.
        destruct (y == X).
          subst.
          simpl_env in H. contradict H; auto.

          exists ((X, bind_kn)::E1). exists E2.
          split; simpl; auto.
            simpl_env. rewrite EQ1. auto.

    analyze_binds H1.
        inversion BindsTacVal; subst.
        destruct (x == x).
            exists nil. exists E.
            split.
               apply env_remove2_notin; auto.
            split; simpl; auto.
               eapply wft_fv_tt_dsub; eauto.

            contradict n; auto.

            apply IHWfe in BindsTac.
            destruct BindsTac as [E1 [E2 [EQ1 [EQ2 Fv]]]]; subst.
            destruct (y == x).
              inversion e; subst.
              simpl_env in H0. destruct_notin.
              contradict NotInTac; auto.

              exists ((x, bind_typ T)::E1). exists E2.
              split.
                 simpl_env. rewrite EQ1. auto.
              split; simpl; auto.
Qed.              

Lemma lenv_remove_kind_notin : forall E x b,
  x `notin` dom E ->
  lenv_remove (x, b) E = E.
Proof.
  induction E; intros; simpl; auto.
    destruct a; simpl in H.
    destruct (eq_lbinding_dec (x, b) (a, l)); simpl.
      inversion e; subst.
      destruct_notin.
      contradict NotInTac; auto.

      rewrite IHE; auto.
Qed.

Lemma lenv_remove_inv : forall E lE y b,
  wf_lenv E lE ->
  binds y b lE ->
  exists lE1, exists lE2,
    lenv_remove (y, b) lE = lE1 ++ lE2 /\
    lE = lE1 ++ [(y, b)] ++ lE2.
Proof.
  intros E lE y b Wfle.
  generalize dependent y.
  generalize dependent b.
  induction Wfle; intros; simpl.
    inversion H0.

    destruct b.
    analyze_binds H2.
        inversion BindsTacVal; subst.
          destruct (eq_lbinding_dec (x, lbind_typ T) (x, lbind_typ T)).
            exists nil. exists D.
            split; simpl; auto.
               apply lenv_remove_kind_notin; auto.

            contradict n; auto.

          destruct (eq_lbinding_dec (y, lbind_typ t) (x, lbind_typ T)).
            inversion e; subst.
            exists nil. exists D.
            split; simpl; auto.
               apply lenv_remove_kind_notin; auto.
              
            apply IHWfle in BindsTac.
            destruct BindsTac as [lE1 [lE2 [EQ1 EQ2]]]; subst.
            exists ((x, lbind_typ T)::lE1). exists lE2.
            split; simpl; auto.
               simpl_env. rewrite EQ1. auto.
Qed.              


Lemma gdom_dom__inv : forall A (sE : list (atom * A)) E x b t,
  gdom_env ([(x, bind_typ t)]++E) [=] dom ([(x, b)]++sE) ->
  x `notin` gdom_env E ->
  x `notin` dom sE ->
  gdom_env E [=] dom sE.
Proof.
  intros.
  simpl in *.
  fsetdec.
Qed.

Lemma free_env__free_gdom : forall x E,
  x `notin` fv_env E ->
  x `notin` gdom_env E.
Proof.
  induction E as [ | [x1 b1] E ]; simpl; intros H; auto.
  destruct b1; auto.
Qed.

Lemma wft_strengthen_sub : forall E F T,
  wf_env (F++E) ->
  wf_typ (F++E) T -> 
  fv_tt T [<=] ddom_env E -> 
  wf_typ E T.
Proof.
  intros E F T Hwfe Hwft Hsub.
  induction F; auto.
    simpl_env in Hwfe.
    destruct a. destruct b; simpl_env in Hwft.
      inversion Hwfe; subst.
      apply IHF; auto.
      assert (a `notin` ddom_env E) as J.
        simpl_env in H2.
        destruct_notin.
        apply dom__ddom; auto.
      rewrite_env (nil ++ [(a, bind_kn)] ++ (F++E)) in Hwft.
      apply wf_typ_strengthening_typ in Hwft; auto.
      
      inversion Hwfe; subst.
      apply IHF; auto.
      apply wft_strengthen_ex in Hwft; auto.
Qed.

Lemma env_remove_opt : forall E1 x b E2,
  uniq (E1++[(x, b)]++E2) ->
  env_remove (x, b) (E1++[(x, b)]++E2) = E1 ++ E2.
Proof.
  intros E1 x b E2 Uniq.
  remember (E1++[(x, b)]++E2) as E.
  generalize dependent E1.
  induction Uniq; intros.
    simpl in HeqE.
    symmetry in HeqE.
    contradict HeqE.
    apply app_cons_not_nil.

    apply one_eq_app in HeqE.
    destruct HeqE as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      simpl. 
      destruct (eq_binding_dec (x, b) (x0, a)).
         inversion e; subst.
         simpl_env in H.
         destruct_notin.
         contradict NotInTac1; auto.

         simpl_env.
         rewrite IHUniq with (E1:=E''); auto.

      simpl_env in EQ2.
      inversion EQ2; subst.
      simpl.
      destruct (eq_binding_dec (@pair atom binding x0 a) (@pair AtomSetImpl.elt binding x0 a)).
        apply env_remove_notin; auto.

        contradict n; auto.
Qed.

Lemma env_remove2_opt : forall E1 x b E2,
  uniq (E1++[(x, b)]++E2) ->
  env_remove2 x (E1++[(x, b)]++E2) = E1 ++ E2.
Proof.
  intros E1 x b E2 Uniq.
  remember (E1++[(x, b)]++E2) as E.
  generalize dependent E1.
  induction Uniq; intros.
    simpl in HeqE.
    symmetry in HeqE.
    contradict HeqE.
    apply app_cons_not_nil.

    apply one_eq_app in HeqE.
    destruct HeqE as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      simpl. 
      destruct (x == x0).
         inversion e; subst.
         simpl_env in H.
         destruct_notin.
         contradict NotInTac1; auto.

         simpl_env.
         rewrite IHUniq with (E1:=E''); auto.

      simpl_env in EQ2.
      inversion EQ2; subst.
      simpl.
      destruct (@eq_dec atom _ x0 x0).
        apply env_remove2_notin; auto.

        contradict n; auto.
Qed.

Lemma lenv_remove_opt : forall E1 x b E2,
  uniq (E1++[(x, b)]++E2) ->
  lenv_remove (x, b) (E1++[(x, b)]++E2) = E1 ++ E2.
Proof.
  intros E1 x b E2 Uniq.
  remember (E1++[(x, b)]++E2) as E.
  generalize dependent E1.
  induction Uniq; intros.
    simpl in HeqE.
    symmetry in HeqE.
    contradict HeqE.
    apply app_cons_not_nil.

    apply one_eq_app in HeqE.
    destruct HeqE as [[E'' [EQ1 EQ2]] | [EQ1 EQ2]]; subst.
      simpl. 
      destruct (eq_lbinding_dec (x, b) (x0, a)).
         inversion e; subst.
         simpl_env in H.
         destruct_notin.
         contradict NotInTac1; auto.

         simpl_env.
         rewrite IHUniq with (E1:=E''); auto.

      simpl_env in EQ2.
      inversion EQ2; subst.
      simpl.
      destruct (eq_lbinding_dec (@pair atom lbinding x0 a) (@pair AtomSetImpl.elt lbinding x0 a)).
        apply lenv_remove_kind_notin; auto.

        contradict n; auto.
Qed.

Lemma wf_env_notin_fv_env : forall E1 X E2,
  wf_env (E1++[(X,bind_kn)]++E2) ->
  wf_env (E1++E2) ->
  X `notin` fv_env E1 `union` fv_env E2.
Proof.
  intros E1 X E2 Wfe Wfe'.  
  remember (E1++[(X, bind_kn)]++E2) as E.
  generalize dependent E1.
  induction Wfe; intros; subst.
    symmetry in HeqE.
    contradict HeqE.
    simpl.
    apply app_cons_not_nil.

    apply one_eq_app in HeqE. destruct HeqE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst; auto.
      simpl_env. simpl.
      apply uniq_from_wf_env in Wfe.
      assert (X `notin` dom (E0'++E2)) as XnE. solve_uniq.
      simpl_env in Wfe'.
      inversion Wfe'; subst.
      apply wfe_dom_fv_env with (x:=X) in Wfe'; auto.
      simpl_env in Wfe'; auto.

      simpl_env in eEQ2'.
      inversion eEQ2'; subst.
      apply wfe_dom_fv_env with (x:=X0) in Wfe; auto.       

    apply one_eq_app in HeqE. destruct HeqE as [[E0' [eEQ1' eEQ2']] | [eEQ1' eEQ2']]; subst; auto.
      simpl_env. simpl.
      apply uniq_from_wf_env in Wfe.
      assert (X `notin` dom (E0'++E2)) as XnE. solve_uniq.
      simpl_env in Wfe'.
      inversion Wfe'; subst.
      apply wfe_dom_fv_env with (x:=X) in Wfe'; auto.
      simpl_env in Wfe'. simpl in Wfe'. auto.

      simpl_env in eEQ2'.
      inversion eEQ2'.
Qed.

Lemma wf_lenv_notin_fv_env : forall E1 X E2 D,
  wf_lenv (E1++[(X,bind_kn)]++E2) D ->
  wf_lenv (E1++E2) D ->
  X `notin` fv_env E1 `union` fv_env E2 `union` fv_lenv D.
Proof.
  intros E1 X E2 D Wfle Wfle'.  
  remember (E1++[(X, bind_kn)]++E2) as E.
  generalize dependent E1.
  induction Wfle; intros; subst.
    apply wf_env_notin_fv_env with (E1:=E1) (E2:=E2) (X:=X) in H; auto.

    inversion Wfle'; subst.
    simpl_env. simpl.
    apply IHWfle in H5; auto.
    apply notin_fv_wf with (X:=X) in H9; auto.
Qed.

Lemma map_subst_tlb_id : forall G D Z P,
  wf_lenv G D ->
  Z `notin` dom G ->
  D = map (subst_tlb Z P) D.
Proof with auto.
  intros G D Z P H.
  (wf_lenv_cases (induction H) Case); simpl; intros Fr; simpl_env...
  Case "wf_lenv_typ".
    rewrite <- IHwf_lenv...
    rewrite <- subst_tt_fresh... 
    eapply notin_fv_wf; eauto.
Qed.

Lemma map_subst_tb_id' : forall G G' Z P,
  wf_env (G++G') ->
  Z `notin` dom (G++G') ->
  G = map (subst_tb Z P) G.
Proof with auto.
  induction G; intros G' Z P H Fr...
    destruct a.
    destruct b; simpl; simpl_env.
      simpl_env in H. inversion H; subst.
      rewrite <- IHG with (G':=G'); auto. 
 
      simpl_env in H. inversion H; subst.
      rewrite <- IHG with (G':=G'); auto. 
      rewrite <- subst_tt_fresh... 
      eapply notin_fv_wf; eauto.
Qed.

Lemma subst_tt_eq__inv : forall T (X Y:atom) t,
  Y `notin` fv_tt t `union` fv_tt T ->
  subst_tt X Y T = subst_tt X Y t ->
  T = t.
Proof.
  induction T; intros X Y t Yn EQ; simpl in EQ.
    destruct t; simpl in EQ; try solve [inversion EQ | auto].
      destruct (a==X); subst; auto.
        inversion EQ.

    destruct (a==X); subst; auto.
      destruct t; simpl in EQ; try solve [inversion EQ | auto].
        destruct (a==X); subst; auto.
          simpl in Yn.
          injection EQ. intros.
          contradict Yn; auto.
      destruct t; simpl in EQ; try solve [inversion EQ | auto].
        destruct (a0==X); subst; auto.
          simpl in Yn.
          injection EQ. intros.
          contradict Yn; auto.

    destruct t; simpl in EQ; try solve [inversion EQ | auto].
      destruct (a==X); subst; try solve [inversion EQ | auto].

      simpl in Yn.
      inversion EQ; subst.
      apply IHT1 in H0; auto.
      apply IHT2 in H1; auto.
      subst. auto.

    destruct t; simpl in EQ; try solve [inversion EQ | auto].
      destruct (a==X); subst; try solve [inversion EQ | auto].

      simpl in Yn.
      inversion EQ; subst.
      apply IHT in H0; auto.
      subst. auto.

    destruct t; simpl in EQ; try solve [inversion EQ | auto].
      destruct (a==X); subst; try solve [inversion EQ | auto].

      simpl in Yn.
      inversion EQ; subst.
      apply IHT in H0; auto.
      subst. auto.

    destruct t; simpl in EQ; try solve [inversion EQ | auto].
      destruct (a==X); subst; try solve [inversion EQ | auto].

      simpl in Yn.
      inversion EQ; subst.
      apply IHT1 in H0; auto.
      apply IHT2 in H1; auto.
      subst. auto.
Qed.

Lemma map_lenv_remove : forall D y T X Y,
  uniq D ->
  Y `notin` fv_lenv D `union` fv_tt T ->
  map (subst_tlb X Y) (lenv_remove (y, lbind_typ T) D) =
    lenv_remove (y, lbind_typ (subst_tt X Y T)) (map (subst_tlb X Y) D).
Proof.
  intros D y T X Y Uniq YnD.
  induction Uniq; intros; simpl; auto.
    destruct a.
    destruct (eq_lbinding_dec (y, lbind_typ T) (x, lbind_typ t)).
      inversion e; subst.
      simpl.
      destruct (eq_lbinding_dec (@pair atom lbinding x (lbind_typ (subst_tt X Y t))) (@pair atom lbinding x (lbind_typ (subst_tt X Y t)))).
        simpl_env in YnD.
        rewrite IHUniq; auto.

        contradict n; auto.

      simpl.
      destruct (eq_lbinding_dec (@pair atom lbinding y (lbind_typ (subst_tt X Y T))) (@pair atom lbinding x (lbind_typ (subst_tt X Y t)))).
        inversion e; subst.
        simpl_env in YnD. simpl in YnD.
        apply subst_tt_eq__inv in H2; auto.
        subst. 
        contradict n; auto.

        simpl_env in YnD.
        simpl_env.
        rewrite IHUniq; auto.
Qed.

Lemma gdom_map : forall E X Y, 
  gdom_env (map (subst_tb X Y) E) [=] gdom_env E.
Proof. 
  intros.
  induction E as [ | [? ?] ]; simpl. 
    fsetdec. 
   
    destruct b; auto.
    simpl. fsetdec.
Qed.

Lemma subst_tt_id : forall T X,
  subst_tt X X T = T.
Proof.
  induction T; intros X; simpl; auto.
    destruct (a==X); subst; auto.
  
    rewrite IHT1. rewrite IHT2. auto.

    rewrite IHT. auto.

    rewrite IHT. auto.

    rewrite IHT1. rewrite IHT2. auto.
Qed.

Lemma subst_tb_id : forall E X,
  map (subst_tb X X) E = E.
Proof.
  induction E; intros X; simpl; auto.
    destruct a. 
    destruct b; simpl. 
      rewrite IHE; auto.

      rewrite IHE.
      rewrite subst_tt_id; auto.
Qed.

Lemma dom_dom__inv : forall A B (E : list (atom * A)) (E' : list (atom * B)) x b b',
  dom ([(x, b)]++E) [=] dom ([(x, b')]++E') ->
  x `notin` dom E ->
  x `notin` dom E' ->
  dom E [=] dom E'.
Proof.
  intros.
  simpl in *.
  fsetdec.
Qed.

Lemma empty_typing_disjdom : forall e t D,
  typing nil nil e t ->
  disjdom (fv_ee e) D.
Proof.
  intros e t0 D Htyp.
  split; intros x Fx.
    apply notin_fv_ee_typing with (y:=x) in Htyp; auto.
    apply notin_fv_ee_typing with (y:=x) in Htyp; auto.
Qed.    

Lemma empty_typing_disjdom' : forall e t D,
  typing nil nil e t ->
  disjdom (fv_te e) D.
Proof.
  intros e t0 D Htyp.
  split; intros x Fx.
    apply notin_fv_te_typing with (X:=x) in Htyp; auto.
    apply notin_fv_te_typing with (X:=x) in Htyp; auto.
Qed.    

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

Lemma expr_tt : 
  expr tt.
Proof.
  unfold tt.
  apply expr_tabs with (L:={}).
    intros X Xn.
    unfold open_te. simpl.
    apply expr_abs with (L:={{X}}); auto.
      intros x xn.
      unfold open_ee. simpl.
      apply expr_let with (L:={{X}} `union` {{x}}); auto.
        intros y yn.
        unfold open_ee. simpl.
        apply expr_abs with (L:={{X}} `union` {{x}} `union` {{y}}); auto.
          intros x0 x0n.
          unfold open_ee. simpl.
          apply expr_let with (L:={{X}} `union` {{x}} `union` {{y}} `union` {{x0}}); auto.
            intros y0 y0n.
            unfold open_ee. simpl. auto.
Qed.

Lemma type_Two :
  type Two.
Proof.
  unfold Two.
  apply type_all with (L:={}).
    intros X Xn.
    unfold open_tt. simpl.
    apply type_arrow; auto.
Qed.
 
Lemma typing_tt : forall E,
  wf_env E ->
  typing E nil tt Two.
Proof.
  intros E Wfe.
  unfold tt.
  apply typing_tabs with (L:=dom E).
    intros X Xn.
    unfold open_te. simpl.
    apply typing_abs with (L:=dom E `union` {{X}}); auto.
      destruct (0 == 0); simpl_env; auto.
        contradict n; auto.

      intros x xn.
      unfold open_ee. simpl.
      apply typing_let with (L:=dom E `union` {{X}} `union` {{x}})(D1:=[(x,lbind_typ (typ_bang X))])(D2:=lempty)(T1:=X); simpl_env; auto.
        apply typing_lvar; auto.
          rewrite_env ([(x,lbind_typ (typ_bang X))]++nil).
          rewrite_env ([(X,bind_kn)]++E).
          apply wf_lenv_typ; auto.

        intros x0 x0n.
        unfold open_ee. simpl.
        apply typing_abs with (L:=dom E `union` {{X}} `union` {{x}} `union` {{x0}}); auto.
          apply wf_typ_bang; auto.

          intros y yn.
          unfold open_ee. simpl. simpl_env.
          apply typing_let with (L:=dom E `union` {{X}} `union` {{x}} `union` {{x0}} `union` {{y}})(D1:=[(y,lbind_typ (typ_bang X))])(D2:=lempty)(T1:=X); simpl_env; auto.
            apply typing_lvar; auto.
              rewrite_env ([(y,lbind_typ (typ_bang X))]++nil).
              apply wf_lenv_typ; auto.
                apply wf_lenv_empty.
                  apply wf_env_typ; auto.
                apply wf_typ_bang; auto.

            intros y1 y1n.
            unfold open_ee. simpl. simpl_env.
            apply typing_bang; auto.
              apply typing_var; auto.
                apply wf_env_typ; auto.
           
            rewrite_env ([(y,lbind_typ (typ_bang X))]++nil).
            apply lenv_split_left; auto.
              apply lenv_split_empty.
                apply wf_env_typ; auto.
              apply wf_typ_bang; auto.
            
        rewrite_env ([(x,lbind_typ (typ_bang X))]++nil).
        apply lenv_split_left; auto.
Qed.

Lemma typing_ff : forall E,
  wf_env E ->
  typing E nil ff Two.
Proof.
  intros E Wfe.
  unfold tt.
  apply typing_tabs with (L:=dom E).
    intros X Xn.
    unfold open_te. simpl.
    apply typing_abs with (L:=dom E `union` {{X}}); auto.
      destruct (0 == 0); simpl_env; auto.
        contradict n; auto.

      intros x xn.
      unfold open_ee. simpl.
      apply typing_let with (L:=dom E `union` {{X}} `union` {{x}})(D1:=[(x,lbind_typ (typ_bang X))])(D2:=lempty)(T1:=X); simpl_env; auto.
        apply typing_lvar; auto.
          rewrite_env ([(x,lbind_typ (typ_bang X))]++nil).
          rewrite_env ([(X,bind_kn)]++E).
          apply wf_lenv_typ; auto.

        intros x0 x0n.
        unfold open_ee. simpl.
        apply typing_abs with (L:=dom E `union` {{X}} `union` {{x}} `union` {{x0}}); auto.
          apply wf_typ_bang; auto.

          intros y yn.
          unfold open_ee. simpl. simpl_env.
          apply typing_let with (L:=dom E `union` {{X}} `union` {{x}} `union` {{x0}} `union` {{y}})(D1:=[(y,lbind_typ (typ_bang X))])(D2:=lempty)(T1:=X); simpl_env; auto.
            apply typing_lvar; auto.
              rewrite_env ([(y,lbind_typ (typ_bang X))]++nil).
              apply wf_lenv_typ; auto.
                apply wf_lenv_empty.
                  apply wf_env_typ; auto.
                apply wf_typ_bang; auto.

            intros y1 y1n.
            unfold open_ee. simpl. simpl_env.
            apply typing_bang; auto.
              apply typing_var; auto.
                apply wf_env_typ; auto.
           
            rewrite_env ([(y,lbind_typ (typ_bang X))]++nil).
            apply lenv_split_left; auto.
              apply lenv_split_empty.
                apply wf_env_typ; auto.
              apply wf_typ_bang; auto.
            
        rewrite_env ([(x,lbind_typ (typ_bang X))]++nil).
        apply lenv_split_left; auto.
Qed.


Definition Kleene_eq e e' : Prop :=
  typing nil nil e Two /\
  typing nil nil e' Two /\
  ((normalize e tt /\ normalize e' tt)
    \/
    (normalize e ff /\ normalize e' ff)).
   
Lemma notin_wf_env : forall E x,
  wf_env E ->
  x `notin` dom E ->
  x `notin` fv_env E.
Proof.
  intros E x Hwfe Xnotin.
  induction Hwfe; auto.
    simpl_env in Xnotin. simpl. auto.

    simpl_env in Xnotin. simpl.
    apply notin_fv_wf with (X:=x) in H; auto.
Qed.

Definition F_observational_eq E lE e e' t : Prop :=
  typing E lE e t /\
  typing E lE e' t /\
  forall C,
   contexting E lE t C nil nil Two ->
   Kleene_eq (plug C e) (plug C e').

Lemma plug_vcontext__value : forall C e,
  vcontext C ->
  expr (plug C e) ->
  value (plug C e).
Proof.
  intros C e VC.
  induction VC; simpl; intros; auto.
    inversion H0; auto.
    inversion H0; auto.
    inversion H0; auto.
Qed.

Lemma bind_kn__in_ddom : forall E X,
  binds X (bind_kn) E ->
  X `in` ddom_env E.
Proof.
  induction E; intros X Binds.
    inversion Binds.
    destruct a. destruct b; simpl.
       analyze_binds Binds. eauto.         
       analyze_binds Binds.
Qed.

Lemma fv_in_open_tt:  forall X t1 t2 k,
   X `in` fv_tt t1 -> 
   X `in` fv_tt (open_tt_rec k t2 t1).
Proof.
  intros X. induction t1; intros t2 k1 IN; simpl in IN; simpl; 
    try solve [fsetdec |
               apply IHt1; auto].
  assert ((X `in` fv_tt t1_1) \/ (X `in` fv_tt t1_2)) as H.
    fsetdec. 
  destruct H as [H | H].
    assert (X `in` fv_tt (open_tt_rec k1 t2 t1_1)).
      apply IHt1_1; auto. 
    fsetdec.
    assert (X `in` fv_tt (open_tt_rec k1 t2 t1_2)).
      apply IHt1_2; auto. 
    fsetdec.

  assert ((X `in` fv_tt t1_1) \/ (X `in` fv_tt t1_2)) as H.
    fsetdec. 
  destruct H as [H | H].
    assert (X `in` fv_tt (open_tt_rec k1 t2 t1_1)).
      apply IHt1_1; auto. 
    fsetdec.
    assert (X `in` fv_tt (open_tt_rec k1 t2 t1_2)).
      apply IHt1_2; auto. 
    fsetdec.
Qed.

Lemma in_fv_wf' : forall E (X : atom) T,
  wf_typ E T ->
  X `in` fv_tt T ->
  X `in` ddom_env E.
Proof.
  (wf_typ_cases (induction 1) Case); intros Fr; simpl in Fr; simpl...
  Case "wf_typ_var".
    apply bind_kn__in_ddom in H0.
    fsetdec.
  Case "wf_typ_arrow".
    assert (X `in` fv_tt T1 \/ X `in` fv_tt T2) as J. fsetdec.
    destruct J as [ J | J ]; auto.
  Case "wf_typ_all".
    pick fresh Y.
    assert (Y `notin` L) as YnL. auto.
    apply H0 in YnL.
      simpl in YnL. 
      destruct_notin.
      clear Fr NotInTac0 NotInTac2 NotInTac3 .
      fsetdec.

      apply fv_in_open_tt; auto.
  Case "wf_typ_bang".
    auto.
  Case "wf_typ_with".
    assert (X `in` fv_tt T1 \/ X `in` fv_tt T2) as J. fsetdec.
    destruct J as [ J | J ]; auto.
Qed.

Lemma fv_te_in_open_ee:  forall X e1 e2 k,
   X `in` fv_te e1 -> 
   X `in` fv_te (open_ee_rec k e2 e1).
Proof.
  intros X. induction e1; intros e2 k1 IN; simpl in IN; simpl;
    try solve [fsetdec |
               apply IHe1; auto].
  assert ((X `in` fv_tt t) \/ (X `in` fv_te e1)) as H.
    fsetdec. 
  destruct H as [H | H]; auto.

  assert ((X `in` fv_te e1_1) \/ (X `in` fv_te e1_2)) as H.
    fsetdec. 
  destruct H as [H | H].
    assert (X `in` fv_te (open_ee_rec k1 e2 e1_1)).
      apply IHe1_1; auto. 
    fsetdec.
    assert (X `in` fv_te (open_ee_rec k1 e2 e1_2)).
      apply IHe1_2; auto. 
    fsetdec.

  assert ((X `in` fv_tt t) \/ (X `in` fv_te e1)) as H.
    fsetdec. 
  destruct H as [H | H]; auto.

  assert ((X `in` fv_te e1_1) \/ (X `in` fv_te e1_2)) as H.
    fsetdec. 
  destruct H as [H | H].
    assert (X `in` fv_te (open_ee_rec k1 e2 e1_1)).
      apply IHe1_1; auto. 
    fsetdec.
    assert (X `in` fv_te (open_ee_rec (S k1) e2 e1_2)).
      apply IHe1_2; auto. 
    fsetdec.

  assert ((X `in` fv_te e1_1) \/ (X `in` fv_te e1_2)) as H.
    fsetdec. 
  destruct H as [H | H].
    assert (X `in` fv_te (open_ee_rec k1 e2 e1_1)).
      apply IHe1_1; auto. 
    fsetdec.
    assert (X `in` fv_te (open_ee_rec k1 e2 e1_2)).
      apply IHe1_2; auto. 
    fsetdec.
Qed.

Lemma fv_te_in_open_te:  forall X e1 t2 k,
   X `in` fv_te e1 -> 
   X `in` fv_te (open_te_rec k t2 e1).
Proof.
  intros X. induction e1; intros t2 k1 IN; simpl in IN; simpl;
    try solve [fsetdec |
               apply IHe1; auto].
  assert ((X `in` fv_tt t) \/ (X `in` fv_te e1)) as H.
    fsetdec. 
  destruct H as [H | H]; auto.
    apply fv_in_open_tt with (t2:=t2) (k:=k1) in H; auto.

  assert ((X `in` fv_te e1_1) \/ (X `in` fv_te e1_2)) as H.
    fsetdec. 
  destruct H as [H | H].
    assert (X `in` fv_te (open_te_rec k1 t2 e1_1)).
      apply IHe1_1; auto. 
    fsetdec.
    assert (X `in` fv_te (open_te_rec k1 t2 e1_2)).
      apply IHe1_2; auto. 
    fsetdec.

  assert ((X `in` fv_tt t) \/ (X `in` fv_te e1)) as H.
    fsetdec. 
  destruct H as [H | H]; auto.
    apply fv_in_open_tt with (t2:=t2) (k:=k1) in H; auto.

  assert ((X `in` fv_te e1_1) \/ (X `in` fv_te e1_2)) as H.
    fsetdec. 
  destruct H as [H | H].
    assert (X `in` fv_te (open_te_rec k1 t2 e1_1)).
      apply IHe1_1; auto. 
    fsetdec.
    assert (X `in` fv_te (open_te_rec k1 t2 e1_2)).
      apply IHe1_2; auto. 
    fsetdec.

  assert ((X `in` fv_te e1_1) \/ (X `in` fv_te e1_2)) as H.
    fsetdec. 
  destruct H as [H | H].
    assert (X `in` fv_te (open_te_rec k1 t2 e1_1)).
      apply IHe1_1; auto. 
    fsetdec.
    assert (X `in` fv_te (open_te_rec k1 t2 e1_2)).
      apply IHe1_2; auto. 
    fsetdec.
Qed.

Lemma in_fv_te_typing' : forall E lE T (X : atom) e,
  typing E lE e T ->
  X `in` fv_te e ->
  X `in` ddom_env E.
Proof with auto.
  (typing_cases (induction 1) Case); intros Fr; simpl in Fr; simpl...
  Case "typing_var".
    contradict Fr; auto.
  Case "typing_lvar".
    contradict Fr; auto.
  Case "typing_abs".
    pick fresh y.
    assert (y `notin` L) as ynL. auto.
    assert (X `in` fv_tt T1 \/ X `in` fv_te e1) as J. fsetdec.
    destruct J as [J | J].
      apply in_fv_wf' with (X:=X) in H; auto.

      apply H1 in ynL.
        simpl in ynL. 
        destruct_notin.
        clear Fr NotInTac0 NotInTac2 NotInTac3 NotInTac4 NotInTac5 NotInTac6 NotInTac7 NotInTac8.
        fsetdec.

        apply fv_te_in_open_ee; auto.
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

      apply fv_te_in_open_te; auto.
  Case "typing_tapp".
    assert (X `in` fv_tt T \/ X `in` fv_te e1) as J. fsetdec.
    destruct J as [J | J]; auto.
      apply in_fv_wf' with (X:=X) in H0; auto.
  Case "typing_let".
    pick fresh y.
    assert (y `notin` L) as ynL. auto.
    assert (X `in` fv_te e1 \/ X `in` fv_te e2) as J. clear - Fr. fsetdec.
    destruct J as [J | J]; auto.
      apply H1 in ynL.
        simpl in ynL. 
        destruct_notin.
        clear Fr NotInTac0 NotInTac2 NotInTac3 NotInTac4 NotInTac5 NotInTac6 NotInTac7 NotInTac8.
        fsetdec.

        apply fv_te_in_open_ee; auto.
  Case "typing_apair".
    assert (X `in` fv_te e1 \/ X `in` fv_te e2) as xine12. fsetdec.
    destruct xine12; auto.
Qed.

Lemma dbinds_In_inv : forall X E,
  X `in` (ddom_env E) ->
  binds X (bind_kn) E.
Proof.
  induction E as [ | y b F IH ]; intros J.
    simpl_alist in J. fsetdec.
    simpl_alist in J. destruct y.  destruct b0; simpl in J.
      assert (X `in` {{a}} \/ X `in` ddom_env b) as J'. fsetdec.
      destruct J' as [J' | J'].
        destruct (X==a); subst; auto.
          contradict J'; auto.

        apply F in J'. auto.

      apply F in J. auto.
Qed.

Lemma empty_wft_disjdom : forall t D,
  wf_typ nil t ->
  disjdom (fv_tt t) D.
Proof.
  intros t0 D Htyp.
  split; intros x Fx.
    apply notin_fv_wf with (X:=x) in Htyp; auto.
    apply notin_fv_wf with (X:=x) in Htyp; auto.
Qed.    

Lemma subst_tt_tt : forall T (X Y:atom) t,
  wf_typ nil t ->
  Y `notin` fv_tt T ->
  subst_tt Y t (subst_tt X Y T) = subst_tt X t T.
Proof.
  induction T; intros X Y t Wft Fv; simpl; auto.
    destruct (a == X); subst; simpl.
      destruct (Y == Y); subst; simpl; auto.
         contradict n; auto.
      destruct (a == Y); subst; simpl; auto.
         simpl in Fv.
         contradict Fv; auto.

    simpl in Fv.
    rewrite IHT1; auto.
    rewrite IHT2; auto.

    simpl in Fv.
    rewrite IHT; auto.

    simpl in Fv.
    rewrite IHT; auto.

    simpl in Fv.
    rewrite IHT1; auto.
    rewrite IHT2; auto.
Qed.

Lemma env_remove_notin' : forall E x b,
  ~binds x b E ->
  env_remove (x, b) E = E.
Proof.
  induction E; intros; simpl; auto.
    destruct a; simpl in H.
    destruct (eq_binding_dec (x, b) (a, b0)); simpl.
      inversion e; subst.
      contradict H; auto.

      rewrite IHE; auto.
Qed.


Lemma env_remove2_inv' : forall E y,
  wf_env E ->
  y `in` dom E ->
  exists E1, exists E2, exists b,
    env_remove2 y E = E1 ++ E2 /\
    E = E1 ++ [(y, b)] ++ E2.
Proof.
  intros E y Wfe.
  generalize dependent y.
  induction Wfe; intros; simpl.
    contradict H; auto.

    assert (y `in` {{X}} \/ y `in` dom E) as yin.
      simpl_env in H0. fsetdec.
    destruct yin as [yin | yin].
      destruct (y==X).
        inversion e; subst.
        exists nil. exists E. exists (bind_kn).
        split; auto.
        apply env_remove2_notin; auto.

        contradict yin; auto.
      destruct (y==X).
        inversion e; subst.
        contradict yin; auto.        

        apply IHWfe in yin.
        destruct yin as [E1 [E2 [b [EQ1 EQ2]]]]; subst.
        exists ((X, bind_kn)::E1). exists E2. exists b.
        split; simpl; auto.
          simpl_env. rewrite EQ1. auto.

    assert (y `in` {{x}} \/ y `in` dom E) as yin.
      simpl_env in H1. fsetdec.
    destruct yin as [yin | yin].
      destruct (y==x).
        inversion e; subst.
        exists nil. exists E. exists (bind_typ T).
        split; auto.
        apply env_remove2_notin; auto.

        contradict yin; auto.
      destruct (y==x).
        inversion e; subst.
        contradict yin; auto.        

        apply IHWfe in yin.
        destruct yin as [E1 [E2 [b [EQ1 EQ2]]]]; subst.
        exists ((x, bind_typ T)::E1). exists E2. exists b.
        split; simpl; auto.
          simpl_env. rewrite EQ1. auto.
Qed.

Lemma env_remove2_dom_sub : forall E y,
  dom (env_remove2 y E) [<=] dom E.
Proof.
  induction E; intros y b; simpl.
    fsetdec.

    destruct a.   
    destruct b0. 
      destruct (y == a); simpl.
        inversion e; subst. 
        assert (J:=@IHE a). 
        fsetdec.

        assert (J:=@IHE y). 
        fsetdec.

      destruct (y == a); simpl.
        inversion e; subst. 
        assert (J:=@IHE a). 
        fsetdec.

        assert (J:=@IHE y). 
        fsetdec.
Qed.

Lemma remove_gdom__gdom_nil : forall E,
  gdom_env (remove_gdom E) [=] {}.
Proof.
  induction E; simpl; auto.
    destruct a.
    destruct b; simpl; auto.
Qed.

Lemma remove_gdom_sub : forall E X,
  X `notin` dom E ->
  X `notin` dom (remove_gdom E).
Proof.
  induction E; intros X Xn; simpl; auto.  
  destruct a.
  destruct b;simpl; auto.
Qed.

