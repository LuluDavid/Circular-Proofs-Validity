Require Import List.
Import ListNotations.

Require Import Debruijn Derivations Occurrences FLSubformulas.
Local Open Scope eqb_scope.
Local Open Scope form.


(** DEFINITION *)

(** Finite Paths *)

Definition FPathType := list sequent.

Inductive preFPath : FPathType -> derivation -> Prop :=
 | Lf s s' ls R: s = (oseq_forget s') -> preFPath [s] (ORule ls R s' []) 
 | COne d t R ls s s': 
                          preFPath t d -> s' = oseq_forget s -> preFPath (s'::t) (ORule ls R s [d])
 | CLeft d d' R ls t s s': 
                          preFPath t d -> s' = oseq_forget s -> preFPath (s'::t) (ORule ls R s [d;d'])
 | CRight d d' R ls t s s': 
                          preFPath t d -> s' = oseq_forget s -> preFPath (s'::t) (ORule ls R s [d';d]).

Definition preFPathNode (t:FPathType)(d:derivation)(a:address) :=
  match subderiv d a with
  | None       => False
  | Some d'  => preFPath t d'
  end.

Definition FPath (t:FPathType)(d:derivation)(a:address) : Prop := (Valid d) /\ (preFPathNode t d a). 

(** FInite Traces *)

Definition FTraceType := list (formula*sequent).

Inductive preFTrace : FTraceType -> derivation -> Prop :=
 | Leaf f s s' ls R: s = (oseq_forget s') -> In f s -> preFTrace [(f,s)] (ORule ls R s' []) 
 | ConsOne d t R ls s0 s s' f1 f2: 
                          preFTrace ((f1,s0)::t) d -> s' = oseq_forget s 
                          -> In f2 s' -> In f1 (FL f2) 
                          -> preFTrace ((f2,s')::(f1,s0)::t) (ORule ls R s [d])
 | ConsLeft d d' t R ls s0 s s' f1 f2: 
                          preFTrace ((f1,s0)::t) d -> s' = oseq_forget s 
                          -> In f2 s' -> In f1 (FL f2) 
                          -> preFTrace ((f2,s')::(f1,s0)::t) (ORule ls R s [d;d'])
 | ConsRight d d' t R ls s0 s s' f1 f2: 
                          preFTrace ((f1,s0)::t) d -> s' = oseq_forget s 
                          -> In f2 s' -> In f1 (FL f2) 
                          -> preFTrace ((f2,s')::(f1,s0)::t) (ORule ls R s [d';d])
                        .

Definition preFTraceNode (t:FTraceType)(d:derivation)(a:address) :=
  match subderiv d a with
  | None       => False
  | Some d'  => preFTrace t d'
  end.

Definition FTrace (t:FTraceType)(d:derivation)(a:address) : Prop := (Valid d) /\ (preFTraceNode t d a). 


(** Link between both*)

Definition IsFTrace (t:FTraceType)(p:FPathType): Prop := map snd t = p. 


(** Example *)

Definition FTrace_example: FTraceType := 
  [( ν (%0)⊕(%0), ⊦ [(ν (%0)⊕(%0))]);
   (((ν (%0)⊕(%0)) ⊕ (ν (%0)⊕(%0))), ⊦ [((ν (%0)⊕(%0)) ⊕ (ν (%0)⊕(%0)))] );
   (ν (%0)⊕(%0), ⊦ [ν (%0)⊕(%0)] )].

Lemma FTrace_example_lemma : FTrace FTrace_example oderiv_example' [].
Proof.
  split;
  repeat (constructor; simpl; intuition).
Qed.

(** Infinite Paths/Traces *)

Definition PathType: Type := nat -> FPathType.

Definition TraceType: Type := nat -> FTraceType.

(** Link between both *)

Definition IsTrace (T:TraceType)(P:PathType): Prop := forall n, map snd (T n) = P n. 

(** Example *)

Definition PathRepeat (t:FPathType) := (fun (n:nat) => t).

Definition TraceRepeat (t:FTraceType) := (fun (n:nat) => t).

Definition Trace_Example := TraceRepeat FTrace_example.







(** PATH & TRACE VALIDITY *)

Local Open Scope eqb_scope.

(** Access to the last rule used in [d] (following address [a] in [d]) *)

Definition last_trace_rule (d:derivation)(a:address) : option rule_kind :=
  match subderiv d a with
  | None => None
  | Some d' => let '(ORule ls R s ld) := d' in match ld with 
                                                                   | [] => Some R
                                                                   | _ => None
                                                                   end
  end.

(** Linking condition between Stream's elements *)

