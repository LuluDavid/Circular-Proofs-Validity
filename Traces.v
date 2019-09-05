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
 | Leaf f s s' ls R: s = (oseq_forget s') -> InSeq f s -> preFTrace [(f,s)] (ORule ls R s' []) 
 | ConsOne d t R ls s0 s s' f1 f2: 
                          preFTrace ((f1,s0)::t) d -> s' = oseq_forget s 
                          -> InSeq f2 s' -> In f1 (FL f2) 
                          -> preFTrace ((f2,s')::(f1,s0)::t) (ORule ls R s [d])
 | ConsLeft d d' t R ls s0 s s' f1 f2: 
                          preFTrace ((f1,s0)::t) d -> s' = oseq_forget s 
                          -> InSeq f2 s' -> In f1 (FL f2) 
                          -> preFTrace ((f2,s')::(f1,s0)::t) (ORule ls R s [d;d'])
 | ConsRight d d' t R ls s0 s s' f1 f2: 
                          preFTrace ((f1,s0)::t) d -> s' = oseq_forget s 
                          -> InSeq f2 s' -> In f1 (FL f2) 
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

Lemma FTrace_example_lemma : FTrace FTrace_example oderiv_example' [].
Proof.
  split;
  repeat (constructor; simpl; intuition).
Qed.

(* 
Lemma FTraceComp: forall f g T d a, (FTrace T d a) -> In f (map fst T) -> In g (map fst T) -> (f ≪ g) \/ (g ≪ f).
Proof.
   intros. destruct H. clear H.
   unfold preFTraceNode in H2. destruct (subderiv d a); try contradiction.
   induction H2.
   - simpl in *; destruct H0; destruct H1; try contradiction; subst; left; apply FL_refl.
   - simpl in H0; simpl in H1.
      destruct H0.
      -- destruct H1.
        + subst; left; apply FL_refl.
        + subst. 
Admitted. *)





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

(** Access to the last rule used in [d] (following address [a] in [d]) *)

Definition last_trace_rule (d:derivation)(a:address) : option rule_kind :=
  match subderiv d a with
  | None => None
  | Some d' => let '(ORule ls R s ld) := d' in match ld with 
                                                                   | [] => Some R
                                                                   | _ => None
                                                                   end
  end.

Compute last_trace_rule oderiv_example' [i;i].

(** Linking condition between Stream's elements *)

CoInductive Path: PathType -> derivation -> Prop := 
  | PathCons p1 p2 n P d a1 a2: 
                                              Path (p2 ;; P) d
                                              -> FPath p1 d a1 -> FPath p2 d a2 
                                              -> last_trace_rule d a1 = Some (BackEdge n)
                                              -> npop n a1 = Some a2
                                              -> Path (p1 ;; p2 ;; P) d.

CoInductive Trace: TraceType -> derivation -> Prop := 
  | TraceCons t1 t2 n T d a1 a2: 
                                              Trace (t2 ;; T) d
                                              -> FTrace t1 d a1 -> FTrace t2 d a2 
                                              -> last_trace_rule d a1 = Some (BackEdge n)
                                              -> npop n a1 = Some a2
                                              -> Trace (t1 ;; t2 ;; T) d.


(** Infinite Appearances *)

Definition preInf (f:formula)(T:TraceType): Prop := 
  forall n, exists m, (n <= m) 
                                      /\ 
                        In f (List.map fst (Str_nth m T)).

Definition Inf (f:formula)(t:TraceType)(d:derivation): Prop := Trace t d /\ preInf f t.

(** Minimum of Infinite Appearances *)

Definition InfMin (f:formula)(T:TraceType)(d:derivation) : Prop := Inf f T d /\ (forall G, Inf G T d -> f ≪ G).

Lemma ExistsMin : forall t d, 
  exists f, InfMin f t d.
Proof.
Admitted.

Lemma UniqueMin : forall f1 f2 t d, 
  InfMin f1 t d -> InfMin f2 t d -> f1 = f2.
Proof.
Admitted.

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
       +++ subst; apply FL_refl.
       +++ destruct H2.
        * subst. simpl. right; left; trivial.
        * destruct H2; try contradiction; subst; apply FL_refl.
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


