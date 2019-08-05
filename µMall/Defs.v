
(** * Initial definitions for Natural Deduction *)

(** The NatDed development, Pierre Letouzey, 2019.
    This file is released under the CC0 License, see the LICENSE file *)

Require Export Setoid Morphisms RelationClasses Arith Omega Bool String
               MSetRBT StringOrder List Utils.
Require DecimalString.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope string_scope.
Local Open Scope eqb_scope.

(** Names *)

(** Names are coded as string. They will be used both for
    variables and function symbols and predicate symbols.

    During proofs, these strings may be arbitrary. In case of
    formula parsing, we'll use the usual syntactic conventions
    for identifiers : a letter first, then letters or digits or "_".
    Some symbols will also be accepted as function or predicate
    symbols, such as "+" "*" "=" "∈". In fact, pretty much
    anything that doesn't contain the parenthesis characters
    or the comma. *)

Definition name := string.
Bind Scope string_scope with name.

(** Variables *)

Definition variable := name.
Bind Scope string_scope with name.

(** Signatures *)

(** A signature is a set of function symbols and predicate symbols
    (with their arities). These sets are usually finite, but we'll
    use an infinite signature at least once (during the proof of
    the completeness theorem).
    Note : Functions of arity zero are also called constants. *)

Definition function_symbol := name.
Definition predicate_symbol := name.
Definition arity := nat.

Bind Scope string_scope with function_symbol.
Bind Scope string_scope with predicate_symbol.

Record signature :=
  make_infinite_sign
  { funsymbs : function_symbol -> option arity;
    predsymbs : predicate_symbol -> option arity }.

(** A finite version (using lists) *)

Module Finite.

Record signature :=
  make_finite_sign
  { funsymbs : list (function_symbol * arity);
    predsymbs : list (predicate_symbol * arity) }.

Definition to_infinite sign :=
  make_infinite_sign
    (fun s => list_assoc s sign.(funsymbs))
    (fun s => list_assoc s sign.(predsymbs)).

End Finite.

Definition peano_sign :=
  {| Finite.funsymbs := [("O",0);("S",1);("+",2);("*",2)];
     Finite.predsymbs := [("=",2)] |}.

Definition zf_sign :=
  {| Finite.funsymbs := [];
     Finite.predsymbs := [("=",2);("∈",2)] |}.


(** Sets of names *)

Module Names.
 Include MSetRBT.Make (StringOT).

 Definition of_list : list name -> t :=
   fold_right add empty.

 Fixpoint unions (l: list t) :=
   match l with
   | [] => empty
   | vs::l => union vs (unions l)
   end.

 Definition unionmap {A} (f: A -> t) :=
   fix unionmap (l:list A) :=
     match l with
     | [] => empty
     | a::l => union (f a) (unionmap l)
     end.

 Definition map (f:name->name) (s : t) :=
   fold (fun v => add (f v)) s empty.

 Definition flatmap (f:name->t) (s : t) :=
   fold (fun v => union (f v)) s empty.

End Names.

(* Prevent incomplete reductions *)
Arguments Names.singleton !_.
Arguments Names.add !_ !_.
Arguments Names.remove !_ !_.
Arguments Names.union !_ !_.
Arguments Names.inter !_ !_.
Arguments Names.diff !_ !_.

(** [fresh names] : gives a new name not in the set [names]. *)

Fixpoint fresh_loop (names:Names.t) (id:string) n : variable :=
  match n with
  | O => id
  | S n => if negb (Names.mem id names) then id
           else fresh_loop names (id++"x") n
  end.

Definition fresh names := fresh_loop names "x" (Names.cardinal names).

(** Misc types : operators, quantificators *)

Inductive op := Or_add | Or_mult | And_add | And_mult.

Inductive quant := µ | ν.

Instance op_eqb : Eqb op :=
 fun o1 o2 =>
  match o1, o2 with
  | Or_add, Or_add | Or_mult, Or_mult | And_add, And_add | And_mult, And_mult => true
  | _, _ => false
  end.

Instance quant_eqb : Eqb quant :=
 fun q1 q2 =>
  match q1, q2 with
  | µ, µ| ν, ν => true
  | _, _ => false
  end.

Definition pr_op o :=
  match o with
  | Or_add => "⊕"
  | Or_mult => "#"
  | And_add => "&"
  | And_mult => "⊗"
  end.

Definition pr_quant q :=
  match q with
  | µ => "µ"
  | ν => "ν"
  end.

Instance : EqbSpec op.
Proof.
 intros [ ] [ ]; now constructor.
Qed.

Instance : EqbSpec quant.
Proof.
 intros [ ] [ ]; now constructor.
Qed.
