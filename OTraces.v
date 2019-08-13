Require Import List.
Import ListNotations.
Require String Bool Streams.
Require Import Eqdep_dec.
Require Import Peano_dec.
Require Import PeanoNat.
Require Import Arith.
Import Bool.
Require Import Defs Debruijn ODerivations Address Occurrences.
Local Open Scope eqb_scope.

(** Preleminary approach: finite traces *)

Definition OFTraceType := list osequent.

Inductive preOFTrace : OFTraceType -> oderivation -> Prop :=
 | Leaf (d:oderivation)(s:osequent): (premisses d = []) -> OClaim d s -> preOFTrace [s] d 
 | ConsOne (d:oderivation)(t:OFTraceType)(R:orule_kind)(ls:list osequent)(s:osequent): 
                          preOFTrace t d -> preOFTrace (s::t) (ORule ls R s [d])
 | ConsLeft (d d': oderivation)(R:orule_kind)(ls:list osequent)(t:OFTraceType)(s:osequent): 
                          preOFTrace t d -> preOFTrace (s::t) (ORule ls R s [d;d'])
 | ConsRight (d d': oderivation)(R:orule_kind)(ls:list osequent)(t:OFTraceType)(s:osequent): 
                          preOFTrace t d -> preOFTrace (s::t) (ORule ls R s [d';d]).
Hint Constructors preOFTrace.

Definition OFTrace (t:OFTraceType)(d:oderivation) : Prop := (OValid d) /\ (preOFTrace t d). 

Definition oderiv_example :=
ORule [] Nu (⊢ [{ (€ (%0)⊕(%0)), [] }]) 
          [
          (
          ORule [(⊢ [{ (€ (%0)⊕(%0)), [] }])] Or_add_l (⊢ [ { ((€ (%0)⊕(%0)) ⊕ (€ (%0)⊕(%0))), [i] } ] )
            [
            (
            ORule [(⊢ [{ (€ (%0)⊕(%0)), [] }])] (BackEdge (⊢ [{ (€ (%0)⊕(%0)), [] }])) (⊢ [ { € (%0)⊕(%0), [l;i] } ] ) []
            )
            ] 
          ) 
          ].

(*
    ----------------------------------------------------- (BackEdge (⊢vX. X⊕X))
     [(⊢{ vX. X⊕X, [] })] ⊢ { (vX.X#X), [l,i] }
    ----------------------------------------------------- (⊕l)
     [(⊢{ vX. X⊕X, [] })] ⊢ { (vX.X⊕X) ⊕ (vX.X⊕X) , [i] } 
    ----------------------------------------------------- (v)
                        [] ⊢{ vX. X⊕X, [] }
    *)

Definition OFTrace_example := 
  [(⊢ [{ (€ (%0)⊕(%0)), [] }]);(⊢ [ { ((€ (%0)⊕(%0)) ⊕ (€ (%0)⊕(%0))), [i] } ] );(⊢ [ { € (%0)⊕(%0), [l;i] } ] )].

Lemma OFTrace_example_lemma : OFTrace OFTrace_example oderiv_example.
Proof.
  unfold oderiv_example; unfold OFTrace_example; repeat constructor; unfold not; intros; discriminate H.
Qed.

Fixpoint OrList (l:list bool) :=
  match l with
  | [] => false
  | h::l' => h ||| (OrList l')
  end.

Lemma OrListTrue : forall l, (exists x, x = true /\ In x l) <-> (OrList l = true).
Proof.
  induction l; split; intros.
  - repeat destruct H. destruct H0.
  - discriminate H.
  - destruct H; destruct H; simpl; destruct a; trivial;
    apply IHl; exists x; split; try assumption; simpl in H0;
    destruct H0; subst; try discriminate H0; assumption.
  - simpl; simpl in H; destruct a eqn:Heq.
    -- exists a; split; try assumption; left; symmetry; assumption.
    -- apply IHl in H; destruct H; exists x; destruct H; split; try assumption; right; assumption.
Qed.

Compute OrList [false; false; false; true].

Fixpoint preOFTraceb (t:OFTraceType)(d:oderivation) : bool :=
  let '(ORule ls R s ld) := d in
  match t with
  | [s'] => (s =? s')
  | s'::ls' => (s =? s') &&& OrList(map (preOFTraceb ls') ld)
  | _ => false
  end.

Definition OFTraceb (t:OFTraceType)(d:oderivation) : bool := (ovalid_deriv d) &&& (preOFTraceb t d). 

Compute OFTraceb OFTrace_example oderiv_example.

Theorem OFTrace_is_OFTraceb : forall t d, OFTrace t d <-> OFTraceb t d = true.
Proof.
Admitted.

(** For the infinite trace, the idea would be to link multiple *)

CoInductive OTraceType: Type := 
  | Cons : OFTraceType -> OTraceType -> OTraceType
  .

CoInductive OTrace: OTraceType -> oderivation -> Prop := 
  | TraceCons (t:OFTraceType)(T:OTraceType)(d:oderivation): 
                                                  OFTrace t d -> OTrace T d -> OTrace (Cons t T) d.






























