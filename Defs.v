Require Export Setoid Morphisms RelationClasses Arith Omega Bool String
               MSetRBT StringOrder List Utils.
Require DecimalString.
Import ListNotations.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope string_scope.
Local Open Scope eqb_scope.

(** Names *)

(** Names are coded as string. They will be used for
    free variables, as we do not consider precise predicate 
    or function symbols in this library *)

Definition name := string.
Bind Scope string_scope with name.

(** Variables *)

Definition variable := name.
Bind Scope string_scope with name.

(** Misc types : operators, quantificators *)

Inductive op := Or_add | Or_mult | And_add | And_mult.

Inductive quant := mu | nu.

Instance op_eqb : Eqb op :=
 fun o1 o2 =>
  match o1, o2 with
  | Or_add, Or_add | Or_mult, Or_mult | And_add, And_add | And_mult, And_mult => true
  | _, _ => false
  end.

Instance quant_eqb : Eqb quant :=
 fun q1 q2 =>
  match q1, q2 with
  | mu, mu| nu, nu => true
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
  | mu => "µ"
  | nu => "ν"
  end.

Instance : EqbSpec op.
Proof.
 intros [ ] [ ]; now constructor.
Qed.

Instance : EqbSpec quant.
Proof.
 intros [ ] [ ]; now constructor.
Qed.
