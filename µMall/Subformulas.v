Require Import List.
Import ListNotations.
Require String.
(* Import Decidable PeanoNat. *)
Require Import Eqdep_dec.
Require Import Peano_dec.
Require Import PeanoNat.
Require Import Arith.
Import Bool.
Require Import Defs Debruijn Suboccurrences.
Local Open Scope eqb_scope.
(** SUBFORMULAS **)

(* In [subform F G], the second argument G is a subformula of the first argument F.
This way, [subform F] is the set of the subformulas of F *)

Inductive Subform: formula -> formula -> Prop :=
| SRefl (F:formula): Subform F F
| OpL (F G F':formula)(o:op): Subform F G -> Subform (Op o F' F) G
| OpR (F G F':formula)(o:op): Subform F G -> Subform (Op o F F') G
| SFQuant (F G:formula)(q:quant): Subform F G -> Subform (Quant q F) G
.

Notation "F ⧼ G" := (Subform F G) (at level 100).

Fixpoint subform_b (F G : formula) := match F,G with
|(Var V), (Var W) => V =? W
|Zero, Zero => true
|One, One => true
|Bot, Bot => true
|Top, Top => true
|(Op o F1 F2), G => if (Op o F1 F2) =? G then true else (subform_b F1 G) || (subform_b F2 G)
|(Quant q F), G => if (Quant q F) =? G then true else (subform_b F G)
| _, _ => false
end.

Theorem V_eqb_refl : forall (v:V), V_eqb v v = true.
Proof.
  intros. apply Utils.eqb_refl.
Qed.


Theorem subform_b_refl : forall F,
  subform_b F F = true.
Proof.
  destruct F; simpl; try apply Utils.eqb_refl;
  try (rewrite Utils.eqb_refl); trivial.
Qed.

Theorem subform_b_trans : forall F G H,
  subform_b F G = true -> subform_b G H = true -> subform_b F H = true.
Proof.
Admitted.

Theorem subform_b_is_subform : forall F G, (Subform F G) <-> (subform_b F G) = true.
Proof.
intros. split; intros. 
  + induction H as [F | F G F' o IH IH'| F G F' o IH IH'| F G q H IH]; trivial;
    try(apply subform_b_refl);
    try(induction G; trivial; try(simpl; apply orb_true_iff; right; assumption);
      simpl; apply orb_true_iff; right; apply orb_true_iff; right; assumption).
    try(induction G; trivial; try(simpl; apply orb_true_iff; left; assumption);
      simpl; apply orb_true_iff; right; apply orb_true_iff; left; assumption).
  + induction F as [ | | | | V | o F1 IH1 F2 IH2 | q F IH]; 
     induction G as [ | | | | V' | o' G1 IH1' G2 IH2' | q' F' IH'];
     try (constructor; reflexivity); try discriminate H;
     try (constructor; simpl in H; apply IH; assumption);
     try (apply V_eqb_eq in H; rewrite H; constructor);
     try(simpl in H; apply orb_true_iff in H; destruct H); try apply IH1 in H; try apply IH2 in H; 
       try (apply OpL; assumption); try (apply OpR; assumption).
     - simpl in H; apply eqb_eq in H; subst; constructor.
     - apply andb_true_iff in H; destruct H as [H1 H3]; apply andb_true_iff in H1; destruct H1 as [H1 H2];
       apply Utils.eqb_eq in H1; apply Utils.eqb_eq in H2; apply Utils.eqb_eq in H3; subst; apply SRefl.
     - apply orb_true_iff in H; destruct H.
      -- apply OpR; apply IH1 in H; assumption.
      -- apply OpL; apply IH2 in H; assumption.
    - apply andb_true_iff in H; destruct H; apply Utils.eqb_eq in H; apply Utils.eqb_eq in H0; subst; apply SRefl.
    - apply IH in H; constructor; assumption.
Qed.

Theorem subform_dec : forall F G, {Subform F G} + {~ (Subform F G)}.
Proof.
intros.
case_eq (subform_b F G) ; intros.
apply subform_b_is_subform in H ; left ; assumption.
right ; intro ; apply subform_b_is_subform in H0 ; rewrite H in H0 ; apply diff_false_true in H0 ; contradiction.
Qed.


(** LINK WITH SUBOCCURRENCES *)

Require Import Occurrences.

Theorem Subform_Suboccurrences_forget : forall (F G: Occurrence),
  (Suboccurrence F G) -> (Subform (occ_forget F)(occ_forget G)).
Proof.
  destruct F;
  induction F as [ | | | | V | o F1 IH1 F2 IH2 | q F IH]; destruct G;
     induction G as [ | | | | V' | o' G1 IH1' G2 IH2' | q' F' IH']; trivial; intros.
  - destruct (a =? a0).
Abort.































