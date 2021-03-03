Require Export Occurrences.

(* PreSuboccurrence F G => G is a 'one step away' suboccurrence of F *)

Local Open Scope formula_scope.

CoInductive PreFLSuboccurrence: Occurrence -> Occurrence -> Prop :=
  | PBinL (F1 F2:formula)(o:op)(A:address): PreFLSuboccurrence { (Op o F1 F2), A }  { F1, l::A}
  | PBinR (F1 F2:formula)(o:op)(A:address): PreFLSuboccurrence { (Op o F1 F2), A }  { F2, r::A}
  | PUn (F:formula)(q:quant)(a:Atom)(A:address): 
      PreFLSuboccurrence { (Quant q a F), A }  { F[[ %0 := Quant q a F ]], i::A}
  .

Notation "F ↪ G" := (PreFLSuboccurrence F G) (at level 100).

CoInductive FLSuboccurrence: Occurrence -> Occurrence -> Prop :=
  | BinL (F1 F2:formula)(o:op)(A:address): FLSuboccurrence { (Op o F1 F2), A }  { F1, l::A}
  | BinR (F1 F2:formula)(o:op)(A:address): FLSuboccurrence { (Op o F1 F2), A }  { F2, r::A}
  | Un (F:formula)(q:quant)(a:Atom)(A:address): 
      FLSuboccurrence { (Quant q a F), A }  { F[[ %0 := Quant q a F ]], i::A }
  | Refl (F:Occurrence): FLSuboccurrence F F
  | Trans (F G H:Occurrence): FLSuboccurrence F G -> FLSuboccurrence G H -> FLSuboccurrence F H
  .

Notation "F ⋘ G" := (FLSuboccurrence F G) (at level 100).
