Require Export Derivations Subformulas FLSubformulas.

Import ListNotations.

Module Inductive_attempt.

(** DEFINITION *)

(** Finite Paths *)

Definition FPathType := list sequent.

Inductive preFPath : FPathType -> derivation -> nat -> Prop :=
 | CLeaf s s' ls n: s = (oseq_forget s') -> preFPath [s] (ORule ls (BackEdge n) s' []) n 
 | COne d t R ls s s' n: 
                          preFPath t d n -> s' = oseq_forget s -> preFPath (s'::t) (ORule ls R s [d]) n
 | CLeft d d' R ls t s s' n: 
                          preFPath t d n -> s' = oseq_forget s -> preFPath (s'::t) (ORule ls R s [d;d']) n
 | CRight d d' R ls t s s' n: 
                          preFPath t d n -> s' = oseq_forget s -> preFPath (s'::t) (ORule ls R s [d';d]) n.

Definition preFPathNode t d n a :=
  match subderiv d a with
  | None       => False
  | Some d'  => preFPath t d' n
  end.

Definition FPath t d n a : Prop := (Valid d) /\ (preFPathNode t d n a). 

(** FInite Traces *)

Definition FTraceType := list (formula*sequent).

Inductive preFTrace : FTraceType -> derivation -> nat -> Prop :=
 | Leaf f s s' ls n: s = (oseq_forget s') -> In f s -> preFTrace [(f,s)] (ORule ls (BackEdge n) s' []) n 
 | ConsOne d t R ls s0 s s' f1 f2 n: 
                          preFTrace ((f1,s0)::t) d n -> s' = oseq_forget s 
                          -> In f2 s' -> In f1 (FL f2) 
                          -> preFTrace ((f2,s')::(f1,s0)::t) (ORule ls R s [d]) n
 | ConsLeft d d' t R ls s0 s s' f1 f2 n: 
                          preFTrace ((f1,s0)::t) d n -> s' = oseq_forget s 
                          -> In f2 s' -> In f1 (FL f2) 
                          -> preFTrace ((f2,s')::(f1,s0)::t) (ORule ls R s [d;d']) n
 | ConsRight d d' t R ls s0 s s' f1 f2 n: 
                          preFTrace ((f1,s0)::t) d n -> s' = oseq_forget s 
                          -> In f2 s' -> In f1 (FL f2) 
                          -> preFTrace ((f2,s')::(f1,s0)::t) (ORule ls R s [d';d]) n
                        .

Definition preFTraceNode t d n a :=
  match subderiv d a with
  | None       => False
  | Some d'  => preFTrace t d' n
  end.

Definition FTrace t d n a : Prop := (Valid d) /\ (preFTraceNode t d n a). 


(** Link between both*)

Definition IsFTrace (t:FTraceType)(p:FPathType): Prop := map snd t = p. 


(** Example *)

Local Open Scope form.

Definition FTrace_example: FTraceType := 
  [( ν (%0)⊕(%0), ⊦ [(ν (%0)⊕(%0))]);
   (((ν (%0)⊕(%0)) ⊕ (ν (%0)⊕(%0))), ⊦ [((ν (%0)⊕(%0)) ⊕ (ν (%0)⊕(%0)))] );
   (ν (%0)⊕(%0), ⊦ [ν (%0)⊕(%0)] )].

Lemma FTrace_example_lemma : FTrace FTrace_example oderiv_example' 2 [].
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

End Inductive_attempt.


(** Fixpoint version *)

Module fixpoint_attempt.

(** DEFINITION *)

(** Finite Paths *)

Definition FPathType := list sequent.

Fixpoint preFPath p d n: Prop :=
  let '(ORule ls R s ld) := d in 
  match p with
  | []       => False
  | s'::p' => s' = (oseq_forget s) /\
                  match ld, R, p' with
                  | [], BackEdge n', [] =>  n = n' 
                  | [d'], _, _                  => preFPath p' d' n
                  | [d1;d2], _, _           => preFPath p' d1 n \/ preFPath p' d2 n
                  | _, _, _                     => False
                  end
  end.

Definition preFPathNode t d n a :=
  match subderiv d a with
  | None       => False
  | Some d'  => preFPath t d' n
  end.

Definition FPath t d n a : Prop := (Valid d) /\ (preFPathNode t d n a). 

(** FInite Traces *)

Definition FTraceType := list (formula*sequent).

Fixpoint preFTrace p d n: Prop :=
  let '(ORule ls R s ld) := d in 
  match p with
  | []       => False
  | (f1,s')::p' => s' = (oseq_forget s) /\
                            match ld, R, p' with
                            | [], BackEdge n', [] =>  (In f1 s') /\ (n = n') 
                            | [d'], _, (f2,_)::p'' => In f1 s' /\ In f2 (FL f1) /\ preFTrace p' d' n
                            | [d1;d2], _, (f2, _)::p''  => In f1 s' /\ In f2 (FL f1) /\ (preFTrace p' d1 n \/ preFTrace p' d2 n)
                            | _, _, _                     => False
                            end
  end.

Definition preFTraceNode t d n a :=
  match subderiv d a with
  | None       => False
  | Some d'  => preFTrace t d' n
  end.

Definition FTrace t d n a : Prop := (Valid d) /\ (preFTraceNode t d n a). 


(** Link between both*)

Definition IsFTrace (t:FTraceType)(p:FPathType): Prop := map snd t = p. 


(** Example *)

Local Open Scope form.

Definition FTrace_example: FTraceType := 
  [( ν (%0)⊕(%0), ⊦ [(ν (%0)⊕(%0))]);
   (((ν (%0)⊕(%0)) ⊕ (ν (%0)⊕(%0))), ⊦ [((ν (%0)⊕(%0)) ⊕ (ν (%0)⊕(%0)))] );
   (ν (%0)⊕(%0), ⊦ [ν (%0)⊕(%0)] )].

Lemma FTrace_example_lemma : FTrace FTrace_example oderiv_example' 2 [].
Proof.
  split.
  - repeat (constructor; simpl; intuition).
  - cbn; intuition.
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

(** Linking condition between Stream's elements *)

Definition Path (P:PathType)(d:derivation): Prop := 
  exists a m, FPath (P 0) d m a /\
  forall n, exists an aSn mn mSn, 
    (FPath (P n) d mn an) /\ (npop mn an = Some aSn) /\ (FPath (P (S n)) d mSn aSn).


Definition Trace (P:TraceType)(d:derivation): Prop := 
  exists a m, FTrace (P 0) d m a /\
  forall n, exists an aSn mn mSn, 
    (FTrace (P n) d mn an) /\ (npop mn an = Some aSn) /\ (FTrace (P (S n)) d mSn aSn).

(* Very hard to work with inductive notions. *)

End fixpoint_attempt.












