Require Import List.
Import ListNotations.

Require Import Defs Debruijn ODerivations Address Occurrences FLSubformulas.
Local Open Scope eqb_scope.

(** PRELIMINARY APPROACH: FINITE TRACES FROM THE ROOT TO A LEAF  *)

Definition FTraceType := list (formula*sequent).

Definition InSeq (f:formula)(s:sequent):= let '( ⊦ Γ) := s in In f Γ. 

Definition InSeqb (f:formula)(s:sequent):= let '( ⊦ Γ) := s in list_mem f Γ. 

Inductive preFTrace : FTraceType -> oderivation -> Prop :=
 | Leaf f s s' ls R: s = (oseq_forget s') -> InSeq f s -> preFTrace [(f,s)] (ORule ls R s' []) 
 | ConsOne d t R ls s0 s s' f1 f2: 
                          preFTrace ((f1,s0)::t) d -> s' = oseq_forget s 
                          -> InSeq f2 s' -> In f2 (FL f1) 
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

Definition preFTraceNode (t:FTraceType)(d:oderivation)(a:address) :=
  match subderiv d a with
  | None       => False
  | Some d'  => preFTrace t d'
  end.

Definition FTrace (t:FTraceType)(d:oderivation)(a:address) : Prop := (OValid d) /\ (preFTraceNode t d a). 

Definition deriv_example :=
ORule [] Nu (⊢ [{ ν ((%0)⊕(%0)), [] }]) 
          [
          (
          ORule [(1, ⊢ [{ (ν (%0)⊕(%0)), [] }])] Or_add_l (⊢ [ { ((ν (%0)⊕(%0)) ⊕ (ν (%0)⊕(%0))), [i] } ] )
            [
            (
            ORule [(2, ⊢ [{ (ν (%0)⊕(%0)), [] }])] (BackEdge 2) (⊢ [ { ν (%0)⊕(%0), [l;i] } ] ) []
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
  [( ν (%0)⊕(%0), ⊦ [(ν (%0)⊕(%0))]);
   (((ν (%0)⊕(%0)) ⊕ (ν (%0)⊕(%0))), ⊦ [((ν (%0)⊕(%0)) ⊕ (ν (%0)⊕(%0)))] );
   (ν (%0)⊕(%0), ⊦ [ν (%0)⊕(%0)] )].

Lemma FTrace_example_lemma : FTrace FTrace_example deriv_example [].
Proof.
  unfold deriv_example; unfold FTrace_example. split;
  repeat (constructor; simpl; intuition).
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

Local Open Scope eqb_scope.

Fixpoint preFTraceb (t:FTraceType)(d:oderivation) : bool :=
  let '(ORule ls R s ld) := d in
  match t with
  | [(f,s')] => (oseq_forget s =? s') &&& (InSeqb f s')
  | (f,s')::(g,s'')::ls' => (oseq_forget s =? s') &&& (InSeqb f s') 
                                    &&& InFormula g (FL f) &&& OrList(map (preFTraceb ((g,s'')::ls')) ld)
  | _ => false
  end.

Definition FTraceb (t:FTraceType)(d:oderivation)(a:address) :=
  match subderiv d a with
  | None       => false
  | Some d'  => (ovalid_deriv d') &&& preFTraceb t d'
  end.

Compute FTraceb FTrace_example deriv_example [].

Theorem FTrace_is_FTraceb : forall t d a, FTrace t d a <-> FTraceb t d a = true.
Proof.
Admitted.

(** AN INFINITE TRACE IS A STREAM OF FINITE TRACES *)

CoInductive TraceType: Type :=
  | TCons : FTraceType -> TraceType -> TraceType
  .

Notation "t ;; T" := (TCons t T) (at level 60, right associativity).

(* We give a few properties on streams *)
Section TraceType.

Definition hd (x:TraceType) := match x with
                            | a ;; _ => a
                            end.

Definition tl (x:TraceType) := match x with
                            | _ ;; s => s
                            end.

Fixpoint Str_nth_tl (n:nat) (s:TraceType) : TraceType :=
  match n with
  | O => s
  | S m => Str_nth_tl m (tl s)
  end.

Definition Str_nth (n:nat) (s:TraceType) := hd (Str_nth_tl n s).

Lemma unfold_TraceType :
 forall x:TraceType, x = match x with
                      | a ;; s => a ;; s
                      end.
Proof.
  intros; destruct x; trivial.
Qed.

Lemma tl_nth_tl :
 forall (n:nat) (s:TraceType), tl (Str_nth_tl n s) = Str_nth_tl n (tl s).
Proof.
  induction n; intros; simpl; trivial.
Qed.

Lemma Str_nth_tl_plus :
 forall (n m:nat) (s:TraceType),
   Str_nth_tl n (Str_nth_tl m s) = Str_nth_tl (n + m) s.
Proof.
  induction m; intros; induction n; simpl; trivial.
  - rewrite <- plus_n_O; trivial.
  - rewrite <- plus_n_Sm, <- plus_Sn_m. rewrite <- IHm; simpl; reflexivity.
Qed.

Lemma Str_nth_plus :
 forall (n m:nat) (s:TraceType), Str_nth n (Str_nth_tl m s) = Str_nth (n + m) s.
Proof.
  intros; simpl; unfold Str_nth; rewrite Str_nth_tl_plus; trivial.
Qed.

CoInductive EqSt (s1 s2: TraceType) : Prop :=
    eqst :
        hd s1 = hd s2 -> EqSt (tl s1) (tl s2) -> EqSt s1 s2.

Ltac coinduction proof :=
  cofix proof; intros; constructor;
   [ clear proof | try (apply proof; clear proof) ].

Theorem EqSt_reflex : forall s:TraceType, EqSt s s.
Proof.
  coinduction EqSt_reflex.
  reflexivity.
Qed.

Theorem sym_EqSt : forall s1 s2:TraceType, EqSt s1 s2 -> EqSt s2 s1.
Proof.
  coinduction sym_EqSt; inversion H.
  - symmetry; assumption.
  - assumption.
Qed.

Theorem trans_EqSt :
 forall s1 s2 s3:TraceType, EqSt s1 s2 -> EqSt s2 s3 -> EqSt s1 s3.
Proof.
  coinduction trans_EqSt; inversion H; inversion H0.
  - rewrite H1, <- H3; trivial.
  - eapply trans_EqSt; eassumption.
Qed.

Theorem eqst_ntheq :
 forall (n:nat) (s1 s2:TraceType), EqSt s1 s2 -> Str_nth n s1 = Str_nth n s2.
Proof.
  unfold Str_nth in |- *; simple induction n.
  intros s1 s2 H; case H; trivial with datatypes.
  intros m hypind.
  simpl in |- *.
  intros s1 s2 H.
  apply hypind.
  case H; trivial with datatypes.
Qed.

Theorem ntheq_eqst :
 forall s1 s2:TraceType,
   (forall n:nat, Str_nth n s1 = Str_nth n s2) -> EqSt s1 s2.
Proof.
  coinduction Equiv2.
  apply (H 0).
  intros n; apply (H (S n)).
Qed.

Section TraceType_Properties.

Variable P : TraceType -> Prop.


Inductive Exists ( x: TraceType ) : Prop :=
  | Here : P x -> Exists x
  | Further : Exists (tl x) -> Exists x.

CoInductive ForAll (x: TraceType) : Prop :=
    HereAndFurther : P x -> ForAll (tl x) -> ForAll x.

Lemma ForAll_Str_nth_tl : forall m x, ForAll x -> ForAll (Str_nth_tl m x).
Proof.
  unfold Str_nth in |- *; simple induction m.
  intros x H; case H; trivial with datatypes.
  intros n hypind.
  simpl in |- *.
  intros x H.
  apply hypind.
  case H; trivial with datatypes.
Qed.

Section Co_Induction_ForAll.
Variable Inv : TraceType -> Prop.
Hypothesis InvThenP : forall x:TraceType, Inv x -> P x.
Hypothesis InvIsStable : forall x:TraceType, Inv x -> Inv (tl x).

Theorem ForAll_coind : forall x:TraceType, Inv x -> ForAll x.
Proof.
  coinduction ForAll_coind; auto.
Qed.

End Co_Induction_ForAll.
End TraceType_Properties.

Variable f : FTraceType -> FTraceType.
CoFixpoint map (s:TraceType) : TraceType := (f (hd s)) ;; (map (tl s)).

Lemma Str_nth_tl_map : forall n s, Str_nth_tl n (map s)= map (Str_nth_tl n s).
Proof.
  unfold Str_nth in |- *; simple induction n.
  intros s; trivial with datatypes.
  intros n0 hypind.
  simpl in |- *.
  intros x.
  apply hypind.
Qed.

Lemma Str_nth_map : forall n s, Str_nth n (map s)= f (Str_nth n s).
Proof.
  unfold Str_nth in |- *; simple induction n.
  intros s; trivial with datatypes.
  intros n0 hypind.
  simpl in |- *.
  intros s.
  apply hypind.
Qed. 

Lemma ForAll_map : forall (P:TraceType -> Prop) (S:TraceType), 
                                    ForAll (fun s => P(map s)) S <-> ForAll P (map S).
Proof.
Admitted. 

Lemma Exists_map : forall (P:TraceType -> Prop) (S:TraceType), 
                                    Exists (fun s => P(map s)) S -> Exists P (map S).
Proof.
Admitted.

End TraceType.









(** A TRACE OF [d] IS A STREAM OF FINITE TRACES OF [d] *)

Definition In' (f:formula)(c:formula*sequent) : Prop := let '( g, s ) := c in f = g.

Local Open Scope eqb_scope.

(* Accéder à la règle d'axiome qui clot la trace, si celle-ci est valide *)
Fixpoint last_trace_rule (d:oderivation)(a:address) : option orule_kind :=
  match subderiv d a with
  | None => None
  | Some d' => let '(ORule ls R s ld) := d' in match ld with 
                                                                   | [] => Some R
                                                                   | _ => None
                                                                   end
  end.

Compute last_trace_rule deriv_example [i;i].

(* We define here traces as unstoppable structures, which means every finite trace has to finish by
    a backedge *)

CoInductive Trace: TraceType -> oderivation -> Prop := 
  | TraceCons t1 t2 n T d a1 a2: FTrace t1 d a1 -> FTrace t2 d a2 
                                              -> last_trace_rule d a1 = Some (BackEdge n)
                                              -> Some a2 = npop n a2
                                              -> Trace (t2 ;; T) d
                                              -> Trace (t1 ;; t2 ;; T) d.

(* f appears an infinite amount of time in trace t: the problem is that a same formula can appear
    an infinite amount of time in different occurrences. By the way, if it appears an infinite amount of time
    in different occurrences, it has to appear infinitely in at least one occurrence. Thus, because we just 
    care about the formulas appearing an infinite amount of time, checking for the formulas is enough ? *)
    
Definition preInf (f:formula)(t:TraceType): Prop := 
  forall n, exists m, (n <= m /\ List.Exists (In' f) (Str_nth m t)).

(* Same + t is a trace for oderivation d *)
Definition Inf (f:formula)(t:TraceType)(d:oderivation): Prop := Trace t d /\ preInf f t.

Definition InfMin (f:formula)(t:TraceType)(d:oderivation) : Prop := 
  Inf f t d -> forall G, Inf G t d -> In f (FL G).





























