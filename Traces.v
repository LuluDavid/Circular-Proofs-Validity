Require Export Derivations Subformulas FLSubformulas.

Import ListNotations.

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

Print oderiv_example'.

(*
    ----------------------------------------------------- (BackEdge (⊢vX. X⊕X))
     [(⊢{ vX. X⊕X, [] })] ⊢ { (vX.X⊕X), [l,i] }
    ----------------------------------------------------- (⊕l)
     [(⊢{ vX. X⊕X, [] })] ⊢ { (vX.X⊕X) ⊕ (vX.X⊕X) , [i] } 
    ----------------------------------------------------- (v)
                        [] ⊢{ vX. X⊕X, [] }
    *)

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




Require Import  Streams.

Notation "t ;; T" := (Cons t T) (at level 60, right associativity).

(** Infinite Paths/Traces *)

Definition PathType: Type := Stream FPathType.

Definition TraceType: Type := Stream FTraceType.

(** Link between both *)

Definition IsTrace (T:TraceType)(P:PathType): Prop := map (List.map snd) T = P. 

(** Example *)

CoFixpoint PathRepeat (t:FPathType) := t ;; (PathRepeat t).

CoFixpoint TraceRepeat (t:FTraceType) := t ;; (TraceRepeat t).

Definition Trace_Example := TraceRepeat FTrace_example.

Lemma Str_nth_ex : forall n, Str_nth n Trace_Example = FTrace_example.
Proof.
  unfold Trace_Example; induction n; simpl.
  - unfold Str_nth; simpl; trivial.
  - unfold Str_nth in *; simpl; rewrite IHn; trivial.
Qed.







(** PATH & TRACE VALIDITY *)

Local Open Scope eqb_scope.

(** Linking condition between Stream's elements *)

CoInductive Path: PathType -> derivation -> Prop := 
  | PathCons p1 p2 n n' P d a1 a2: 
                                              Path (p2 ;; P) d
                                              -> FPath p1 d n a1 -> FPath p2 d n' a2 
                                              -> npop n a1 = Some a2
                                              -> Path (p1 ;; p2 ;; P) d.

CoInductive Trace: TraceType -> derivation -> Prop := 
  | TraceCons t1 t2 n n' T d a1 a2: 
                                              Trace (t2 ;; T) d
                                              -> FTrace t1 d n a1 -> FTrace t2 d n' a2 
                                              -> npop n a1 = Some a2
                                              -> Trace (t1 ;; t2 ;; T) d.


(** Infinite Appearances *)

Definition preInf (f:formula)(T:TraceType): Prop := 
  forall n, exists m, (n <= m) 
                                      /\ 
                        In f (List.map fst (Str_nth m T)).

Definition Inf (f:formula)(t:TraceType)(d:derivation): Prop := Trace t d /\ preInf f t.

(** Minimum of Infinite Appearances *)

Definition InfMin (f:formula)(T:TraceType)(d:derivation) : Prop := Inf f T d /\ (forall G, Inf G T d -> f ⧼ G).

Lemma ExistsMin : forall t d, 
  exists f, InfMin f t d.
Proof.
Admitted.

Lemma UniqueMin : forall f1 f2 t d, 
  InfMin f1 t d -> InfMin f2 t d -> f1 = f2.
Proof.
  intros; destruct H; destruct H0; apply subform_antisymmetric; try apply H1; try apply H2; assumption.
Qed.

(** Validity Criteria *)

(** For a Trace *)

Definition ValidTrace (T:TraceType)(d:derivation) : Prop :=
  exists f, (InfMin f T d /\ NuFormula f).


Lemma ValidTraceExample: ValidTrace Trace_Example oderiv_example'.
Proof.
  unfold Trace_Example, TraceRepeat; exists (ν % 0 ⊕ % 0); split.
  + split.
    ++ split.
      +++ cofix proof. fold TraceRepeat in *. admit.
      +++ unfold preInf; intros; exists n; simpl; intuition.
              rewrite Str_nth_ex; simpl; left; trivial.
    ++ intros; destruct H. unfold preInf in H0. pose proof (H0 0); destruct H1; destruct H1.
       rewrite Str_nth_ex in H2; simpl in H2; destruct H2.
       +++ subst; constructor.
       +++ destruct H2.
        * subst. simpl. repeat constructor.
        * destruct H2; try contradiction; subst; constructor.
  + reflexivity.
Admitted.

(** For a Path *)

Definition ValidPath (P:PathType)(d:derivation) : Prop :=
  exists T, (IsTrace T P /\ ValidTrace T d).

(** For a Derivation *)

Definition ValidityCriteria (d:derivation): Prop :=
  forall (P:PathType), Path P d -> ValidPath P d.

Lemma ValidExample: ValidityCriteria oderiv_example'.
Proof.
Admitted.
 
(** Decidability *)

Definition DecidableValidity : Prop :=
  forall (d:derivation), (ValidityCriteria d) \/ ~ (ValidityCriteria d).


