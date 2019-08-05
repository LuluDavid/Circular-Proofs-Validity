
(** * Ordering of the String datatype *)

(** The NatDed development, Pierre Letouzey, 2019.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Bool Orders Ascii AsciiOrder String.
Local Open Scope string_scope.

Inductive string_lt : string -> string -> Prop :=
 | LtEmpty a s : "" < String a s
 | LtHead a a' s s' : (a < a')%char -> String a s < String a' s'
 | LtTail a s s' : s < s' -> String a s < String a s'
where "u < v" := (string_lt u v) : string_scope.
Hint Constructors string_lt.

Lemma string_lt_strorder : StrictOrder string_lt.
Proof.
 split.
 - intros s. red. induction s; inversion_clear 1; auto.
   now apply ascii_lt_strorder in H0.
 - red. intros x y z H; revert z. induction H; inversion_clear 1; auto.
   constructor. eapply ascii_lt_strorder; eauto.
Qed.

Definition string_le s s' := s<s' \/ s=s'.
Infix "<=" := string_le : string_scope.

Lemma string_le_lteq s s' : s<=s' <-> s<s' \/ s=s'.
Proof.
 reflexivity.
Qed.

Fixpoint string_compare s s' :=
  match s, s' with
  | "", "" => Eq
  | "", _ => Lt
  | _, "" => Gt
  | String a s, String a' s' =>
    match (a ?= a')%char with
    | Eq => string_compare s s'
    | Lt => Lt
    | Gt => Gt
    end
  end.

Infix "?=" := string_compare (at level 70) : string_scope.

Lemma string_compare_spec s s' :
 CompareSpec (s=s') (s<s') (s'<s) (s?=s').
Proof.
 revert s'.
 induction s as [|a s IH]; destruct s' as [|a' s']; simpl; auto.
 case ascii_compare_spec; intros H; subst; simpl; auto.
 case IH; intros H; subst; auto.
Qed.

Definition string_eqb s s' :=
 match s ?= s' with
 | Eq => true
 | _ => false
 end.

Definition string_ltb s s' :=
 match s ?= s' with
 | Lt => true
 | _ => false
 end.

Definition string_leb s s' :=
 match s ?= s' with
 | Gt => false
 | _ => true
 end.
 
Infix "=?" := string_eqb : string_scope.
Infix "<?" := string_ltb : string_scope.
Infix "<=?" := string_leb : string_scope.


Lemma string_eqb_spec (s s' : string) : reflect (s = s') (s =? s').
Proof.
 unfold string_eqb.
 assert (H := string_compare_spec s s').
 destruct string_compare; constructor; inversion H; auto.
 intros <-. assert (~(s < s)) by apply string_lt_strorder. auto.
 intros <-. assert (~(s < s)) by apply string_lt_strorder. auto.
Qed.


Theorem string_eqb_refl : forall s,
  (s =? s) = true.
Proof.
Admitted.

Lemma string_ltb_spec (s s' : string) : BoolSpec (s < s') (s' <= s) (s <? s').
Proof.
 unfold string_ltb, string_le.
 assert (H := string_compare_spec s s').
 destruct string_compare; constructor; inversion H; auto.
Qed.

Lemma string_leb_spec (s s' : string) : BoolSpec (s <= s') (s' < s) (s <=? s').
Proof.
 unfold string_leb, string_le.
 assert (H := string_compare_spec s s').
 destruct string_compare; constructor; inversion H; auto.
Qed.


Module StringOT <: UsualOrderedType.
 Definition t := string.
 Definition eq := @Logic.eq string.
 Definition eq_equiv := @eq_equivalence string.
 Definition lt := string_lt.
 Lemma lt_compat : Proper (eq==>eq==>iff) lt.
 Proof. now intros ? ? -> ? ? ->. Qed.
 Definition lt_strorder := string_lt_strorder.
 Definition compare := string_compare.
 Definition compare_spec := string_compare_spec.
 Definition eq_dec := string_dec.
End StringOT.
