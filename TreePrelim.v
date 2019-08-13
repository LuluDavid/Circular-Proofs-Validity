Require Import Defs.
Require Import StringUtils.
Require DecimalString.
Import ListNotations.
Require Import Arith.
Import Bool.
Require Import Defs Debruijn Occurrences Suboccurrences FLSuboccurrences.
Local Open Scope eqb_scope.

Inductive Tree: Type :=
  | leaf: Occurrence -> Tree
  | unary: Tree -> Occurrence -> Tree
  | binary: Tree -> Tree -> Occurrence -> Tree.

Definition getOccurrence (T:Tree): Occurrence :=
  match T with
  | leaf o => o
  | unary _ o => o
  | binary _ _ o => o
  end.

(* This property juste traduces the fact that: 
      -> Addresses are well connected between nodes.
      -> Binary nodes are only bound to Op formulas
      -> Unary nodes are only bound to Quant formulas
      -> Leaf nodes are only bound to Nullary formulas
 *)
Inductive ValidTree:Tree -> Prop :=
  | VLeaf (F:formula)(A:address): In F [⊤;⊥;°; !] \/ (exists v, In F [Var v;Covar v]) -> ValidTree (leaf { F, A })
  | VUnary (o:Occurrence)(T:Tree): ValidTree T
                                                                    -> (o ⇀ (getOccurrence T)) 
                                                                    -> ValidTree (unary T o)
  | VBinary (o:Occurrence)(T1 T2: Tree): ValidTree T1 -> ValidTree T2 
                                                                                 -> (o ⇀ (getOccurrence T1)) 
                                                                                 -> (o ⇀ (getOccurrence T2))
                                                                                 -> ValidTree (binary T1 T2 o)
  .

Definition Psi: formula := €($((%0 # %1) & ° ))
.

Definition TreeExample: Tree :=
  unary (
                unary ( 
                               binary (
                                              binary ( 
                                                              leaf { (%0), [l;l;i;i] } ) 
                                                          ( 
                                                              leaf { (%1), [r;l;i;i] } )
                                               { (%0 # %1)%form, [l;i;i] }
                                               ) 
                                              (
                                              leaf { °, [r;i;i] }
                                              ) 
                               { ((%0 # %1) & ° )%form, [i;i] }
                               ) 
                { ($((%0 # %1) & ° ))%form, [i] }
                )
  { Psi,[] }.

(*                                       -> Y
                                -> # 
                                          -> X
nu X -> mu Y -> &
                                -> °
                    
*)

Theorem ValidExample: ValidTree TreeExample.
Proof.
  constructor; constructor; constructor; constructor; constructor; intuition.
  - right; exists (BVar 0); left; reflexivity.
  - right; exists (BVar 1); left; reflexivity.
Qed.

(* Number of operators in the tree *)
Fixpoint TSize(T:Tree): nat :=
  match T with
  | leaf _ => 0
  | unary T' _ => 1 + (TSize T')
  | binary T1 T2 _ => 1 + Nat.max (TSize T1)(TSize T2)
  end.

(* This property juste traduces the fact that: 
      -> Addresses are well connected between nodes.
      -> Binary nodes are only bound to Op formulas
      -> Unary nodes are only bound to Quant formulas
      -> Leaf nodes are only bound to Nullary formulas
  The difference with ValidTree is that bound variables are not anymore present in leafs, as they have 
  to point to their binders in the tree.
 *)
 
Inductive ValidFLTree:Tree -> Prop :=
  | VFLLeaf (F:formula)(A:address): In F [⊤;⊥;°; !] \/ (exists v, In F [(@v)%form;(¬@v)%form]) -> ValidFLTree (leaf { F, A })
  | VFLUnary (o:Occurrence)(T:Tree): ValidTree T ->(o ↪ (getOccurrence T)) -> ValidFLTree (unary T o)
  | VFLBinary (o:Occurrence)(T1 T2: Tree): ValidFLTree T1 -> ValidFLTree T2 
                                                                                 -> (o ↪ (getOccurrence T1)) 
                                                                                 -> (o ↪ (getOccurrence T2))
                                                                                 -> ValidFLTree (binary T1 T2 o)
.