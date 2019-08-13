Require Import List.
Import ListNotations.
Require String Bool Streams.
Require Import Eqdep_dec.
Require Import Peano_dec.
Require Import PeanoNat.
Require Import Arith.
Import Bool.
Require Import Defs Debruijn ODerivations Address Occurrences OTraces.
Local Open Scope eqb_scope.

(** Preleminary approach: finite traces *)

Definition FTraceType := list sequent.

Inductive preFTrace : FTraceType -> oderivation -> Prop :=
 | Leaf (d:oderivation)(s:sequent): (premisses d = []) -> OClaim' d s -> preFTrace [s] d 
 | ConsOne (d:oderivation)(t:FTraceType)(R:orule_kind)(ls:list osequent)(s:osequent)(s':sequent): 
                          preFTrace t d -> s' = oseq_forget s -> preFTrace (s'::t) (ORule ls R s [d])
 | ConsLeft (d d': oderivation)(R:orule_kind)(ls:list osequent)(t:FTraceType)(s:osequent)(s':sequent): 
                          preFTrace t d -> s' = oseq_forget s -> preFTrace (s'::t) (ORule ls R s [d;d'])
 | ConsRight (d d': oderivation)(R:orule_kind)(ls:list osequent)(t:FTraceType)(s:osequent)(s':sequent): 
                          preFTrace t d -> s' = oseq_forget s -> preFTrace (s'::t) (ORule ls R s [d';d]).
Hint Constructors preFTrace.

Definition FTrace (t:FTraceType)(d:oderivation) : Prop := (OValid d) /\ (preFTrace t d). 

Definition deriv_example :=
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

Local Open Scope form.

Definition FTrace_example: FTraceType := 
  [(⊦ [(€ (%0)⊕(%0))]);(⊦ [((€ (%0)⊕(%0)) ⊕ (€ (%0)⊕(%0)))] );(⊦ [€ (%0)⊕(%0)] )].

Lemma FTrace_example_lemma : FTrace FTrace_example deriv_example.
Proof.
  unfold deriv_example; unfold FTrace_example; repeat constructor; unfold not; intros; discriminate H.
Qed.

Fixpoint preFTraceb (t:FTraceType)(d:oderivation) : bool :=
  let '(ORule ls R s ld) := d in
  match t with
  | [s'] => (oseq_forget s =? s')
  | s'::ls' => (oseq_forget s =? s') &&& OrList(map (preFTraceb ls') ld)
  | _ => false
  end.

Definition FTraceb (t:FTraceType)(d:oderivation) : bool := (ovalid_deriv d) &&& (preFTraceb t d). 

Compute FTraceb FTrace_example deriv_example.

Theorem FTrace_is_FTraceb : forall t d, FTrace t d <-> FTraceb t d = true.
Proof.
Admitted.

(** For the infinite trace, the idea would be to link multiple *)

CoInductive TraceType: Type := 
  | Cons : FTraceType -> TraceType -> TraceType
  .

CoInductive Trace: TraceType -> oderivation -> Prop := 
  | TraceCons (t:FTraceType)(T:TraceType)(d:oderivation): 
                                                  FTrace t d -> Trace T d -> Trace (Cons t T) d.






























