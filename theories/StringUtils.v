
(** * Utilities about the String datatypes *)

(** The NatDed development, Pierre Letouzey, 2019.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Ascii String.
Local Open Scope string_scope.

Inductive Prefix : string -> string -> Prop :=
| PrefNil s : Prefix "" s
| PrefCons a s s' : Prefix s s' -> Prefix (String a s) (String a s').
Hint Constructors Prefix : string.

Fixpoint string_mult (s:string)(n:nat) : string :=
  match n with
  | 0 => ""
  | S n' => s ++ (string_mult s n')
  end.
  
Lemma Prefix_refl s : Prefix s s.
Proof.
 induction s; auto with string.
Qed.

Lemma prefix_spec s s' : prefix s s' = true <-> Prefix s s'.
Proof.
 split.
 - revert s'.
   induction s; destruct s'; simpl; auto with string.
   + intros [=].
   + destruct Ascii.ascii_dec; subst; auto with string. intros [=].
 - induction 1.
   + now destruct s.
   + simpl; now destruct (Ascii.ascii_dec a a).
Qed.

Lemma Prefix_more s s' : Prefix s (s++s').
Proof.
 induction s; simpl; auto with string.
Qed.

Lemma Prefix_alt s s' : Prefix s s' <-> exists u, s ++ u = s'.
Proof.
 split.
 - induction 1.
   + now exists s.
   + destruct IHPrefix as (u,IH). exists u. simpl; now f_equal.
 - intros (u,<-). apply Prefix_more.
Qed.

Lemma Prefix_app_l s s1 s2 : Prefix s1 s2 -> Prefix (s++s1) (s++s2).
Proof.
 induction s; simpl; auto with string.
Qed.

Lemma Prefix_length s s' :
  Prefix s s' -> (String.length s <= String.length s')%nat.
Proof.
 induction 1; simpl; auto with arith.
Qed.

Lemma Prefix_app_r s s1 s2 :
  Prefix s (s1++s2) <->
  (Prefix s s1 \/ exists s', s1++s'=s /\ Prefix s' s2).
Proof.
 revert s1 s2.
 induction s as [|a s IH].
 - intuition.
 - intros [|a1 s1] s2; simpl in *.
   + split.
     * inversion_clear 1. right. exists (String a s); auto with string.
     * intros [H|(s' & -> & H)]; auto. inversion H.
   + split.
     * inversion_clear 1. apply IH in H0.
       destruct H0 as [H0|(s' & <- & H0)]; [left|right]; auto with string.
       exists s'; auto.
     * intros [H|(s' & H & H')]; auto.
       inversion_clear H. constructor. rewrite IH; auto.
       inversion_clear H. constructor. now apply Prefix_app_l.
Qed.
