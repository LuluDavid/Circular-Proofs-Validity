Require Export Suboccurrences.
Import ListNotations Arith Bool.

Local Open Scope eqb_scope.

(** STRUCTURE *)

Inductive Tree: Type :=
  | leaf: Occurrence -> Tree
  | unary: Tree -> Occurrence -> Tree
  | binary: Tree -> Tree -> Occurrence -> Tree.

Instance tree_eqb: Eqb Tree :=
  fix tree_eqb T1 T2 :=
  match T1, T2 with
  | leaf o1, leaf o2 => (o1 =? o2)
  | unary T1 o1, unary T2 o2 => (o1 =? o2) &&& (tree_eqb T1 T2)
  | binary T1 T1' o1, binary T2 T2' o2 => (o1 =? o2) &&& (tree_eqb T1 T2) &&& (tree_eqb T1' T2')
  | _, _ => false
  end.

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
  | VLeaf (F:formula)(A:address): In F [⊤;⊥;ø; !] \/ (exists v, F = Var v) -> ValidTree (leaf { F, A })
  | VUnary (o:Occurrence)(T:Tree): ValidTree T
                                                                    -> (o ⇀ (getOccurrence T)) 
                                                                    -> ValidTree (unary T o)
  | VBinary (o:Occurrence)(T1 T2: Tree): ValidTree T1 -> ValidTree T2 
                                                                                 -> (o ⇀ (getOccurrence T1)) 
                                                                                 -> (o ⇀ (getOccurrence T2))
                                                                                 -> ValidTree (binary T1 T2 o)
  .

Definition Psi: formula := ν(µ((%0 # %1) & ø ))
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
                                              leaf { ø, [r;i;i] }
                                              ) 
                               { ((%0 # %1) & ø )%form, [i;i] }
                               ) 
                { (µ((%0 # %1) & ø ))%form, [i] }
                )
  { Psi,[] }.

(*                                       -> Y
                                -> # 
                                          -> X
nu X -> mu Y -> &
                                -> ø
                    
*)

Theorem ValidExample: ValidTree TreeExample.
Proof.
  constructor; constructor; constructor; constructor; constructor; intuition.
  - right; exists (BVar 0); reflexivity.
  - right; exists (BVar 1); reflexivity.
Qed.


(** THE TREE OF A FORMULA *)

Fixpoint formulaTreeRec (F:formula)(A:address): Tree:=
  match F with
  | ⊤ | ⊥ | ø | ! | Var _ => leaf { F, A }
  | Quant q F' => unary (formulaTreeRec F' (i::A)) { F, A }
  | Op o F1 F2 => binary (formulaTreeRec F1 (l::A)) (formulaTreeRec F2 (r::A)) { F, A }
  end.

Definition formulaTree (F:formula) := formulaTreeRec F [].

Definition TreeExampleBis := formulaTree Psi.

Compute TreeExampleBis =? TreeExample.







(** COMPUTING THE ACCESS TO BOUND VARIABLES DEFINITIONS **)

(* RETURNS THE LIST(ADDRESS*FORMULA) OF ALL BINDING OCCURRENCES IN [T] *)
Fixpoint BindingOccurrences (T:Tree) : list (address*formula) :=
  match T with
  | leaf _ => []
  | unary T' o => let '{ F, A }:=o in ( BindingOccurrences T' ++ [(A,F)] )
  | binary T1 T2 _ => BindingOccurrences T1 ++ BindingOccurrences T2
  end.

(* GET ALL SUB-ADDRESSES OF [a0] IN [D] *)
Fixpoint filter_sub_addresses (a0:address)(D:list(address*formula)) : list(address*formula) :=
  match D with
    | (a,F)::D' => if (sub_addressb a a0) then (a,F)::(filter_sub_addresses a0 D') 
                                                              else filter_sub_addresses a0 D'
    | nil        => []
    end.

(* GET ALL SUB-ADDRESSES OF [a0] IN T's OCCURRENCE ADDRESSES *)
Definition tree_filter (a0:address)(T:Tree) : list(address*formula) := filter_sub_addresses a0 (BindingOccurrences T).

Local Open Scope string_scope.

Definition Example_sub_filtering : formula := µ (//"X" # ν(%1 & (%2 & !))).

Definition Tree_Prev := formulaTree Example_sub_filtering.

Compute Tree_Prev.

Compute tree_filter [l; r; i; r; i] Tree_Prev.

(* GET THE DEFINITION OF [%n] KNOWING ITS ADDRESS [a] *)
Definition getDef (a:address)(n:nat)(T:Tree) := nth_error (tree_filter a T) (pred n).

Compute getDef [l; i; r; i] 1 Tree_Prev.
Compute getDef [l; r; i; r; i] 2 Tree_Prev.





