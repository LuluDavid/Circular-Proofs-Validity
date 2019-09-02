Require Import List.
Import ListNotations.

Require Import Utils Defs Debruijn ODerivations Address Occurrences Subformulas FLSubformulas.
Local Open Scope eqb_scope.
Local Open Scope form.

(** PRELIMINARY APPROACH: FINITE TRACES FROM THE ROOT TO A LEAF  *)

Definition FTraceType := list (formula*sequent).

Definition InSeq (f:formula)(s:sequent):= let '( ⊦ Γ) := s in In f Γ. 

Definition InSeqb (f:formula)(s:sequent):= let '( ⊦ Γ) := s in list_mem f Γ. 

Lemma InSeq_is_InSeqb: forall s l, InSeq s l <-> InSeqb s l = true.
Proof.
  unfold InSeq, InSeqb; destruct l; symmetry; apply list_mem_in.
Qed.




Inductive preFTrace : FTraceType -> oderivation -> Prop :=
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


(** RELATIVELY TO SOME NODE *)

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

Local Open Scope eqb_scope.



(** BOOLEAN VERSION *)

Fixpoint preFTraceb (t:FTraceType)(d:oderivation) : bool :=
  let '(ORule ls R s ld) := d in
  match t, ld with
  | [(f,s')], [] => (oseq_forget s =? s') &&& (InSeqb f s')
  | (f,s')::(g,s'')::ls', [d'] => (oseq_forget s =? s') &&& (InSeqb f s') 
                                    &&& list_mem g (FL f) &&& preFTraceb ((g,s'')::ls') d'
  | (f,s')::(g,s'')::ls', [d1;d2] => (oseq_forget s =? s') &&& (InSeqb f s') 
                                    &&& list_mem g (FL f) 
                                    &&& (preFTraceb ((g,s'')::ls') d1 ||| preFTraceb ((g,s'')::ls') d2)
  | _, _ => false
  end.

Definition FTraceb (t:FTraceType)(d:oderivation)(a:address) :=
  (ovalid_deriv d) && 
  match subderiv d a with
  | None       => false
  | Some d'  => preFTraceb t d'
  end.

Compute FTraceb FTrace_example deriv_example [].

Lemma preFTrace_is_preFtraceb : forall t d, preFTrace t d <-> preFTraceb t d = true.
Proof.
  split; generalize dependent d; induction t; intros.
  - inversion H.
  - induction t.
    -- destruct d; destruct a; simpl in *; inversion H; subst; rewrite Utils.eqb_refl. 
        rewrite <- InSeq_is_InSeqb; assumption.
    -- destruct d; destruct a; destruct a0; simpl in *; inversion H; subst.
      + rewrite Utils.eqb_refl; apply InSeq_is_InSeqb in H11; rewrite H11; apply list_mem_in in H12; rewrite H12;
         simpl; rewrite IHt; trivial.
      + rewrite Utils.eqb_refl; apply InSeq_is_InSeqb in H11; rewrite H11; apply list_mem_in in H12; rewrite H12;
         simpl; rewrite lazy_orb_iff; left; rewrite IHt; trivial.
      + rewrite Utils.eqb_refl; apply InSeq_is_InSeqb in H11; rewrite H11; apply list_mem_in in H12; rewrite H12;
         simpl; repeat rewrite lazy_orb_iff; right; rewrite IHt; trivial.
  - destruct d; discriminate H.
  - induction t.
    -- destruct d; destruct a; simpl in *; destruct l0; try discriminate H; 
        rewrite lazy_andb_iff in H; destruct H; apply Utils.eqb_eq in H; apply InSeq_is_InSeqb in H0; subst; constructor; trivial.
    -- destruct d; destruct a; destruct a0; simpl in *; destruct l0; try discriminate H; destruct l0.
      + repeat (rewrite lazy_andb_iff in H; destruct H); apply Utils.eqb_eq in H; 
         apply list_mem_in in H1; apply InSeq_is_InSeqb in H2; subst.
         constructor; trivial; apply IHt; trivial.
      + destruct l0.
        ++ repeat (rewrite lazy_andb_iff in H; destruct H); rewrite lazy_orb_iff in H0; destruct H0;
             apply Utils.eqb_eq in H; apply list_mem_in in H1; apply InSeq_is_InSeqb in H2; subst.
          --- constructor; try apply IHt; trivial.
          --- apply ConsRight; try apply IHt; trivial.
        ++ discriminate H.
Qed.

Theorem FTrace_is_FTraceb : forall a d t, FTrace t d a <-> FTraceb t d a = true.
Proof.
  unfold FTrace, FTraceb. split; intros.
  - destruct H; rewrite andb_true_iff; rewrite ovalid_deriv_is_OValid; split; try assumption; 
    unfold preFTraceNode in H0. 
    destruct (subderiv d a) eqn:Heq.
    -- apply preFTrace_is_preFtraceb; assumption.
    -- destruct H0.
  - apply andb_true_iff in H; destruct H; rewrite <- ovalid_deriv_is_OValid; split; try assumption;
    unfold preFTraceNode.
    destruct (subderiv d a) eqn:Heq.
    -- apply preFTrace_is_preFtraceb; assumption.
    -- discriminate H0.
Qed.











(** AN INFINITE TRACE IS A STREAM OF FINITE TRACES *)

CoInductive TraceType: Type :=
  | TCons : FTraceType -> TraceType -> TraceType
  .

Notation "t ;; T" := (TCons t T) (at level 60, right associativity).




(** Properties on these streams *)
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

Definition Str_nth (n:nat) (s:TraceType): FTraceType := hd (Str_nth_tl n s).

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
   | HereAndFurther : P x -> ForAll (tl x) -> ForAll x.

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

End TraceType.











Local Open Scope eqb_scope.

(* Access to the last rule used in [d] following [a] *)

Definition last_trace_rule (d:oderivation)(a:address) : option orule_kind :=
  match subderiv d a with
  | None => None
  | Some d' => let '(ORule ls R s ld) := d' in match ld with 
                                                                   | [] => Some R
                                                                   | _ => None
                                                                   end
  end.

Compute last_trace_rule deriv_example [i;i].



(** TRACE VALIDITY *)

CoInductive Trace: TraceType -> oderivation -> Prop := 
  | TraceCons t1 t2 n T d a1 a2: 
                                              Trace (t2 ;; T) d
                                              -> FTrace t1 d a1 -> FTrace t2 d a2 
                                              -> last_trace_rule d a1 = Some (BackEdge n)
                                              -> npop n a1 = Some a2
                                              -> Trace (t1 ;; t2 ;; T) d.


(** INFINITE APPEARANCES *)

Definition preInf (f:formula)(t:TraceType): Prop := 
  forall n, exists m, (n <= m) 
                                      /\ 
                        In f (List.map fst (Str_nth m t)).

Definition Inf (f:formula)(t:TraceType)(d:oderivation): Prop := Trace t d /\ preInf f t.

(** MINIMUM FOR A GIVEN PATH [t]*)

Definition InfMin (f:formula)(t:TraceType)(d:oderivation) : Prop := Inf f t d /\ (forall G, Inf G t d -> f ≪ G).

(* Existence and Unicity *)

Lemma ExistsMin : forall t d, 
  exists f, InfMin f t d.
Proof.
Admitted.

Lemma UniqueMin : forall f1 f2 t d, 
  InfMin f1 t d -> InfMin f2 t d -> f1 = f2.
Proof.
Admitted.


(** VALIDITY CRITERIA FOR A PATH *)

Definition ValidTrace (t:TraceType)(d:oderivation) : Prop :=
  Trace t d /\ exists f, (InfMin f t d /\ NuFormula f).

(** FOR A DERIVATION *)

Definition ValidityCriteria (d:oderivation): Prop :=
  forall (t:TraceType), Trace t d -> exists f, (InfMin f t d /\ NuFormula f).

(** DECIDABILITY *)

Definition DecidableValidity : Prop :=
  forall (d:oderivation), (ValidityCriteria d) \/ ~ (ValidityCriteria d).




