Require Import Arith.
Import Bool.

Require Import Defs Debruijn Subformulas.
 
(** FL-SUBFORMULAS **)

(** definition + decidability **)

(** in [FLsubform F G], the second argument G is a FL-subformula of the first argument F.
This way, [FL-subform F] is the set of the FL-subformulas of F **)

Inductive FLSubform: formula -> formula -> Prop :=
| FLSame (F:formula): FLSubform F F
| FLOpL (F G F':formula)(o:op): FLSubform F G -> FLSubform (Op o F' F) G
| FLOpR (F G F':formula)(o:op): FLSubform F G -> FLSubform (Op o F F') G
(*| FLQuant (F G:formula)(q:quant): FLSubform (form_bsubst 0 (Quant q F) F) G -> FLSubform (Quant q F) G*)
| FLQuant (Phi G:formula)(q:quant): (FLSubform Phi G) -> Subform (Quant q Phi) Phi -> FLSubform (Quant q Phi) G 
(* Reformulate the criteria on the last one :
[FLSubform Phi G] /\ [In (µX.Phi) Phi] /\ [X BVar dans Phi] => FLSubform µX.Phi G ???
*)
.
(*
Fixpoint FLsubform_b (F G : formula) := match F,G with
|(Var V), (Var W) => (V_eqb V W)
|(Covar V), (Covar W) => (V_eqb V W)
|Zero, Zero => true
|One, One => true
|Bot, Bot => true
|Top, Top => true
|Op o F1 F2, G => if (form_eqb (Op o F1 F2) G) then true else (FLsubform_b F1 G) || (FLsubform_b F2 G)
|Quant q F, G => if form_eqb (Quant q F) G then true else 
                                 if form_eqb (form_bsubst 0 (Quant q F) F) G then true else (FLsubform_b (bsubst 0 (Quant q F) F) G)
| _, _ => false
end.

Theorem subform_b_is_subform : forall F G, (subform F G) <-> (subform_b F G) = true.
Proof.
Admitted.
*)

Theorem subform_dec : forall F G, {FLSubform F G} + {~ (FLSubform F G)}.
Proof.
intros. induction F as [ | | | | V | o F1 IH1 F2 IH2 | q F IH]; induction G as [ | | | | V' | o' G1 IH1' G2 IH2' | q' F' IH'];
try (left; constructor; reflexivity); try (right; unfold not; intros; inversion H; reflexivity);
try(destruct (V_eqb V V') eqn:Hv); try(apply Utils.eqb_eq in Hv; left; rewrite Hv; constructor); 
try(apply Utils.eqb_neq in Hv; right; unfold not; intros; inversion H; destruct Hv; assumption);
try (destruct IH1; destruct IH2); try (left; constructor; assumption; reflexivity); 
try (right; unfold not; intros; inversion H; subst; destruct n0; try assumption; destruct n; try assumption; reflexivity).
+ right; unfold not; intros. destruct n.
Abort.

(* Nécessité d'une version booléenne pour destruct des cases sur les sous-formules *)















