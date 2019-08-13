Require Import Defs.
Require Import StringUtils.
Require DecimalString.
Import ListNotations.
Require Import Arith.
Import Bool.
Require Import Defs Debruijn Occurrences Address Suboccurrences.
Local Open Scope string_scope.
Local Open Scope eqb_scope.
 
(* PreSuboccurrence F G => G is a 'one step away' suboccurrence of F *)
CoInductive PreFLSuboccurrence: Occurrence -> Occurrence -> Prop :=
  | PBinL (F1 F2:formula)(o:op)(A:address): PreFLSuboccurrence { (Op o F1 F2), A }  { F1, l::A}
  | PBinR (F1 F2:formula)(o:op)(A:address): PreFLSuboccurrence { (Op o F1 F2), A }  { F2, r::A}
  | PUn (F:formula)(q:quant)(A:address): 
      PreFLSuboccurrence { (Quant q F), A }  { bsubst 0 (Quant q F) F, i::A}
  .

Notation "F ↪ G" := (PreFLSuboccurrence F G) (at level 100).

CoInductive FLSuboccurrence: Occurrence -> Occurrence -> Prop :=
  | BinL (F1 F2:formula)(o:op)(A:address): FLSuboccurrence { (Op o F1 F2), A }  { F1, l::A}
  | BinR (F1 F2:formula)(o:op)(A:address): FLSuboccurrence { (Op o F1 F2), A }  { F2, r::A}
  | Un (F:formula)(q:quant)(A:address): 
      FLSuboccurrence { (Quant q F), A }  { bsubst 0 (Quant q F) F, i::A }
  | Refl (F:Occurrence): FLSuboccurrence F F
  | Trans (F G H:Occurrence): FLSuboccurrence F G -> FLSuboccurrence G H -> FLSuboccurrence F H
  .

Notation "F ⋘ G" := (FLSuboccurrence F G) (at level 100).

Inductive ValidFLTree:Tree -> Prop :=
  | FLVLeaf (F:formula)(A:address): In F [⊤;⊥;°; !] \/ (exists v, F = (@v)%form) -> ValidFLTree (leaf { F, A })
  | FLVUnary (o:Occurrence)(T:Tree): ValidFLTree T
                                                                    -> (o ⇀ (getOccurrence T)) 
                                                                    -> ValidFLTree (unary T o)
  | FLVBinary (o:Occurrence)(T1 T2: Tree): ValidTree T1 -> ValidFLTree T2 
                                                                                 -> (o ⇀ (getOccurrence T1)) 
                                                                                 -> (o ⇀ (getOccurrence T2))
                                                                                 -> ValidFLTree (binary T1 T2 o).
