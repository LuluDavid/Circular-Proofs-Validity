Require Import Defs.
Require Import Wf.
Require Import StringUtils.
Require DecimalString.
Import ListNotations.
Require Import Arith.
Import Bool.
Require Import Defs Debruijn Occurrences Address Utils.

Local Open Scope eqb_scope.

(* PreSuboccurrence F G => G is a 'one step away' suboccurrence of F *)
Inductive PreSuboccurrence: Occurrence -> Occurrence -> Prop :=
  | PBinL (F1 F2:formula)(o:op)(A:address): PreSuboccurrence { (Op o F1 F2), A }  { F1, l::A}
  | PBinR (F1 F2:formula)(o:op)(A:address): PreSuboccurrence { (Op o F1 F2), A }  { F2, r::A}
  | PUn (F:formula)(q:quant)(A:address): PreSuboccurrence { (Quant q F), A }  { F, i::A}
  .

Notation "F ⇀ G" := (PreSuboccurrence F G) (at level 100).

(** SUBOCCURRENCE *)

Inductive Suboccurrence: Occurrence -> Occurrence -> Prop :=
  | BinL (F1 F2:formula)(o:op)(A:address): Suboccurrence { (Op o F1 F2), A }  { F1, l::A}
  | BinR (F1 F2:formula)(o:op)(A:address): Suboccurrence { (Op o F1 F2), A }  { F2, r::A}
  | Un (F:formula)(q:quant)(A:address): Suboccurrence { (Quant q F), A }  { F, i::A}
  | Refl (F:Occurrence): Suboccurrence F F
  | Trans (F G H:Occurrence): Suboccurrence F G -> Suboccurrence G H -> Suboccurrence F H
  .
Hint Constructors Suboccurrence.

Fixpoint suboccurrence_b_rec ( F:formula )(a:address)(G:Occurrence){ struct F } : bool :=
  match F, G with 
  | Var V, { Var W, a' } => (V =? W) && (a =? a')
  | Zero, { Zero, a' } => a =? a'
  | One, { One, a' } => a =? a'
  | Bot, { Bot, a' } => a =? a'
  | Top, { Top, a' } => a =? a' 
  | (Op o F1 F2), G => ({ F, a } =? G) || (suboccurrence_b_rec F1 (l::a) G) || (suboccurrence_b_rec F2 (r::a) G)
  | (Quant q F'), G => ({ F, a } =? G) || (suboccurrence_b_rec F' (i::a) G)
  | _, _ => false
  end.
  
  
Definition suboccurrence_b (F G:Occurrence) : bool := 
  let '{ F', a} := F in (suboccurrence_b_rec F' a G).  

Lemma suboccurrence_b_refl : forall (F: Occurrence), suboccurrence_b F F = true.
Proof.
  intros; destruct F; destruct F as [ | | | | V | o F1 F2| q F']; 
  simpl; try(intros; apply eqb_eq; trivial); intuition.
Qed.

Lemma suboccurrence_b_trans : forall (F G H: Occurrence), 
  suboccurrence_b F G = true -> suboccurrence_b G H = true -> suboccurrence_b F H = true.
Proof.
Admitted.

Theorem Suboccurrence_is_suboccurrence_b: forall (F G: Occurrence), 
  Suboccurrence F G <-> suboccurrence_b F G = true.
Proof.
  split.
  - destruct F; destruct G; intros. induction H as [F1 F2 o a'|F1 F2 o a'|F' q a'|F'|F' G' H' IH1 IH2 IH3 IH4]; simpl; 
    try (apply orb_true_iff); try (rewrite orb_true_iff).
    + left; right; destruct F1; simpl; intuition.
    + right; destruct F2; simpl; intuition.
    + right; destruct F'; simpl; intuition.
    + apply suboccurrence_b_refl.
    + apply (suboccurrence_b_trans _ G' _); assumption.
 - destruct F; destruct G; generalize dependent a; generalize dependent a0; 
     induction F as [ | | | | V | o F1 IH1 F2 IH2 | q F' IH];
     induction F0 as [ | | | | V' | o' G1 IH1' G2 IH2' | q' F'' IH']; intros; try discriminate H;
     simpl in H; try apply eqb_eq in H; try subst; trivial;
     try (apply orb_true_iff in H; destruct H); try(econstructor; try constructor; apply IH1 in H; assumption);
     try (apply Trans with (G:={F2, r::a}); try constructor; apply IH2 in H; assumption);
     try (econstructor; try constructor; apply IH in H; assumption).
     -- apply andb_true_iff in H; destruct H; apply eqb_eq in H; apply eqb_eq in H0; subst; constructor.
     -- apply orb_true_iff in H; destruct H.
      ++ apply eqb_eq in H. injection H as Ho H1 H2 Ha; subst; trivial.
      ++ apply IH1 in H. econstructor; try constructor. assumption.
    -- apply eqb_eq in H; injection H as Hq HF Ha; subst; trivial. 
Qed.
  
Local Open Scope string_scope.

Notation "F ≪ G" := (Suboccurrence F G) (at level 100).

Definition f1 : Occurrence := { @ "X", [r;i;i] }.
Definition f2 : Occurrence := { $ (%1 & (@ "X")), [i] }.

Lemma example_suboccurrence: Suboccurrence f2 f1.
Proof.
  unfold f1; unfold f2. repeat econstructor. 
Qed.

(** TREE OF A FORMULA *)

Local Open Scope eqb_scope.

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
  | VLeaf (F:formula)(A:address): In F [⊤;⊥;°; !] \/ (exists v, F = Var v) -> ValidTree (leaf { F, A })
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
  - right; exists (BVar 0); reflexivity.
  - right; exists (BVar 1); reflexivity.
Qed.

Fixpoint TSize(T:Tree): nat :=
  match T with
  | leaf _ => 0
  | unary T' _ => 1 + (TSize T')
  | binary T1 T2 _ => 1 + Nat.max (TSize T1)(TSize T2)
  end.

Fixpoint formulaTreeRec (F:formula)(A:address): Tree:=
  match F with
  | ⊤ | ⊥ | ° | ! | Var _ => leaf { F, A }
  | Quant q F' => unary (formulaTreeRec F' (i::A)) { F, A }
  | Op o F1 F2 => binary (formulaTreeRec F1 (l::A)) (formulaTreeRec F2 (r::A)) { F, A }
  end.

Definition formulaTree (F:formula) := formulaTreeRec F [].

Definition TreeExampleBis := formulaTree Psi.

Compute TreeExampleBis =? TreeExample.

Fixpoint getAddresses (f:formula)(T:Tree): list address :=
  match T with
  | leaf { F, a } => if f =? F then [a] else []
  | unary T' { F, a } => if f =? F then a::(getAddresses f T') else getAddresses f T'
  | binary T1 T2 { F, a } => if f =? F then a::app (getAddresses f T1)(getAddresses f T2) 
                                                          else app (getAddresses f T1)(getAddresses f T2) 
  end.






(** COMPUTING THE ACCESS TO BOUND VARIABLES DEFINITIONS **)

Fixpoint FirstAttempt (T:Tree) : list Occurrence :=
  match T with
  | leaf _ => []
  | unary T' o => FirstAttempt T'++[o]
  | binary T1 T2 _ => FirstAttempt T1 ++ FirstAttempt T2 (* There might be a problem here *)
  end.

Definition pbForm : formula := (€ %1) # ($ %1).
Definition pbTree := formulaTree pbForm.

Compute FirstAttempt (pbTree).

(* In the case of a binary Op, if we just append the variables, we might not find 
back the good definition for a bound variable on one side. 
Except if we look in the addresses to find the good one ? 

The idea at first was to get the first back element of the list to get (%1)'s definition, etc.
But appending prevents from doing that. What we could imagine is to get the closest
sub-address for (%1), the 2nd closest for (%2), etc...
It forces us to define a sort, or some kind of dictionary/hashmap structure. *)

(* RETURNS THE LIST(ADDRESS*FORMULA) OF ALL BINDING OCCURRENCES IN [T] *)
Fixpoint BindingOccurrences (T:Tree) : list (address*formula) :=
  match T with
  | leaf _ => []
  | unary T' o => let '{ F, A }:=o in ( BindingOccurrences T' ++ [(A,F)] )
  | binary T1 T2 _ => BindingOccurrences T1 ++ BindingOccurrences T2
  end.

Compute BindingOccurrences (pbTree).

(* We would now like to use these utilities to get for a given n the n-th closest binder of an address a0. 
    The easiest idea seems to first filtrate all a0 subaddresses (and then take the n-th one ?)*)

(* GET ALL SUB-ADDRESSES OF [a0] IN [D] *)
Fixpoint filter_sub_addresses (a0:address)(D:list(address*formula)) : list(address*formula) :=
  match D with
    | (a,F)::D' => if (sub_addressb a a0) then (a,F)::(filter_sub_addresses a0 D') 
                                                              else filter_sub_addresses a0 D'
    | nil        => []
    end.

(* GET ALL SUB-ADDRESSES OF [a0] IN T's OCCURRENCE ADDRESSES *)
Definition tree_filter (a0:address)(T:Tree) : list(address*formula) := filter_sub_addresses a0 (BindingOccurrences T).

Definition Example_sub_filtering : formula := $ (@"X" # €(%1 & (%2 & !))).

Definition Tree_Prev := formulaTree Example_sub_filtering.

Compute Tree_Prev.

Compute tree_filter [l; r; i; r; i] Tree_Prev.

(* GET THE DEFINITION OF [%n] KNOWING ITS ADDRESS [a] *)
Definition getDef (a:address)(n:nat)(T:Tree) := nth_error (tree_filter a T) (pred n).

Compute getDef [l; i; r; i] 1 Tree_Prev.
Compute getDef [l; r; i; r; i] 2 Tree_Prev.

(* If, at one point, the bound variable decides either it goes left or right, then the above sorting 
    function will remove all the other part of the happen, so the order of closest to furthest binder should 
    be conserved by this sort. Thus, we just have to take the first element for %1, the second for %2, etc..
    We can conclude that for a given bound variable %n at a given address a, we can get back its 
    definition in the tree *)

Definition freeVar (a:address)(n:nat)(T:Tree): Prop := (getDef a n T) = None.








(** RECURSIVE SUBSTITUTION **)


















