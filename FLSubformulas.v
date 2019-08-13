Require Import Arith.
Require Export Setoid Morphisms RelationClasses Arith Omega Bool String
               MSetRBT StringOrder List Utils.
Require DecimalString.
Import ListNotations.
Import Bool.
Require Import Defs Debruijn Subformulas.
Local Open Scope eqb_scope.
Local Open Scope list_scope.
Local Open Scope formula_scope.
(** FL-SUBFORMULAS **)

(** definition + decidability **)

(** in [FLsubform F G], the second argument G is a FL-subformula of the first argument F.
This way, [FL-subform F] is the set of the FL-subformulas of F **)

Inductive FLSubform: formula -> formula -> Prop :=
| FLSame (F:formula): FLSubform F F
| FLOpL (F G F':formula)(o:op): FLSubform F G -> FLSubform (Op o F' F) G
| FLOpR (F G F':formula)(o:op): FLSubform F G -> FLSubform (Op o F F') G
| FLQuant (F G:formula)(q:quant): FLSubform (bsubst 1 (Quant q F) F) G -> FLSubform (Quant q F) G
(* | FLQuant (Phi G:formula)(q:quant): (FLSubform Phi G) -> Subform (Quant q Phi) Phi -> FLSubform (Quant q Phi) G *) 
.

Hint Constructors FLSubform.

Definition Subst := list (nat*formula).

Fixpoint get (i:nat)(s:Subst): option formula :=
  match s with
  | [] => None
  | (j, F)::s' => if (i =? j) then (Some F) else (get  i s')
  end.

Fixpoint remove (i:nat)(s:Subst): Subst :=
  match s with
  | [] => []
  | (j, F)::s' => if (i =? j) then s' else (j, F)::(remove i s')
  end.

Fixpoint lift (s:Subst): Subst :=
  match s with
  | [] => []
  | (j, F)::s' => (j+1, F)::(lift s')
  end.

Fixpoint lower (s:Subst): Subst :=
   match s with
    | [] => []
    | (j, F)::s' => (j-1, F)::(lower s')
    end.
  
(* Fixpoint MSubst (f:formula)(s:Subst) : formula :=
  match f with
  | ⊥ | ⊤ | ! | ° => f
  | (// s) => f
  | (% k)%form => match (get k s) with
                              | Some g => g
                              | None     => f
                              end
  | Op o G1 G2 => Op o (MSubst G1 s)(MSubst G2 s) 
  | Quant q F => Quant q (MSubst F (lift s))
  end. *)
  
Definition example_formula : formula := %2 &((%1 # € (%1 & %2)) # °).
Definition example_subst : Subst := [(1, ⊥);(2, ⊤)].

(* Definition example := MSubst example_formula example_subst. 

Compute example. Unchanged *)

Fixpoint MSubst(f:formula)(s:Subst) : formula :=
  match s with
  | [] => f
  | (j, F)::s' => MSubst (form_bsubst j F f) s'
  end.
  
Definition example := MSubst example_formula example_subst.

Compute example.

(* Lemma MSubst_is_MSubst': forall f s, (MSubst f s) = (MSubst' f s).
Proof.
  assert (Hloc: forall n, 0 =? n+1 = false). 
    { intros; apply eqb_neq; unfold not; intros; destruct n; discriminate H. }
     assert  (Hloc': forall n, (S n) = n+1).
    { induction n; trivial. rewrite IHn, <- plus_Sn_m, IHn; reflexivity.  }
  induction f as [ | | | | v | o f1 IH1 f2 IH2| q f IH]; induction s as [|f' s'];  simpl; intuition.
  - destruct v; trivial.
  - admit.
  - rewrite IH1, IH2; simpl; trivial.
  - rewrite IH1, IH2; simpl. admit.
  - rewrite IH; trivial.
  - admit.
Admitted. *)

Fixpoint preFL (f:formula)(s:Subst) : list formula :=
  match f with
  | ⊥ | ⊤ | ! | ° => [f]
  | (// s) => [f] 
  | (% k) => let F := get k s in (match F with
                                                 | None => [f]
                                                 | Some F' => [F']
                                                 end
                                                 )
  | Op o F G => (MSubst f s) :: (preFL F s) ++ (preFL G s) 
  | Quant q F => (MSubst f s) :: (preFL F ( (1, (MSubst f s)) :: (lift s)))
  end.

Definition FL (f:formula) := preFL f [].

Fixpoint nodup (l : list formula) : list formula :=
    match l with
      | [] => []
      | f::fs => if (Inb' f fs) then (nodup fs) else (f::(nodup fs))
    end.

Definition FLSet (f:formula) := nodup (FL f).

Lemma FL_refl: forall f, In f (FL f).
Proof.
  induction f; simpl; try destruct v; try (left; reflexivity).
Qed.

Local Open Scope string_scope.
Definition exampleFL1: formula :=  ° & (! # (// "X")).
Definition exampleFL2: formula := $(€(%2 & %1)).
Compute FL exampleFL1.
Compute FL exampleFL2.
Local Open Scope eqb_scope.

Lemma CheckFL: forall F q, BClosed F -> In (bsubst 1 (Quant q F) F) (FL (Quant q F)).
Proof.
  intros. induction F as [ | | | | V | o F1 IH1 F2 IH2 | q' F IH]; try (simpl; intuition; reflexivity).
  simpl. destruct V eqn: Heq; simpl; intuition. unfold bsubst.
    destruct (n=?1) eqn:Heq'; simpl.
    -- left. rewrite Heq'; trivial.
    -- discriminate H.
Qed.

Local Open Scope nat_scope.
Local Open Scope eqb_scope.

Theorem FLSubform_is_In_preFL: forall F G, BClosed F -> FLSubform F G -> (exists l, In G (preFL F l)).
Proof.
  intros. induction H0 as [ F | F G F' o H' IH | F G F' o H' IH | F G q H' IH].
  - exists []. apply FL_refl.
  - simpl. apply BClosed_op in H. destruct H. inversion H'; subst.
Abort.

Theorem FLSubform_is_In_FL: forall F G, BClosed F -> (FLSubform F G <-> In G (FL F)).
Proof.
  split; intros.
  + generalize dependent G; induction F as [ | | | | V | o F1 IH1 F2 IH2 | q F IH]; intros; simpl;
     try(inversion H0; subst; intuition).
     - destruct V eqn:Heq; simpl; intuition; discriminate H.
     - right. apply IH2 in H5. apply in_app_iff. right; assumption. 
        unfold BClosed in H. unfold level in H. simpl in H.
        assert (Hloc: forall (n m:nat), (Nat.max n m) = 0 -> m = 0). { admit. }
        apply Hloc in H. assumption.
     - right. apply IH1 in H5. apply in_app_iff. left; assumption. 
        unfold BClosed in H. unfold level in H. simpl in H.
        assert (Hloc: forall (n m:nat), (Nat.max n m) = 0 -> n = 0). { admit. }
        apply Hloc in H. assumption.
     - inversion H0; subst; intuition.
       admit.
  + generalize dependent G; induction F as [ | | | | V | o F1 IH1 F2 IH2 | q F IH]; intros; simpl;
     try(simpl in H0; destruct H0; subst; try constructor; destruct H0).
     - destruct V; simpl; try(simpl in H0; destruct H0; subst; try constructor; destruct H0).
     - assert (Hloc: BClosed (Op o F1 F2) -> (BClosed F1) /\ (BClosed F2)). { admit. }
       simpl in H0; destruct H0; subst; try (constructor; reflexivity). apply Hloc in H. destruct H.
       apply in_app_iff in H0; destruct H0. 
       ++ apply FLOpR; apply IH1; assumption.
       ++ apply FLOpL; apply IH2; assumption.
     - admit.
Admitted.

(* Useless if we prove the property above, because In is decidable *)
(* Theorem subform_dec : forall F G, {FLSubform F G} + {~ (FLSubform F G)}.
Proof.
intros. induction F as [ | | | | V | o F1 IH1 F2 IH2 | q F IH]; induction G as [ | | | | V' | o' G1 IH1' G2 IH2' | q' F' IH'];
try (left; constructor; reflexivity); try (right; unfold not; intros; inversion H; reflexivity);
try(destruct (V_eqb V V') eqn:Hv); try(apply Utils.eqb_eq in Hv; left; rewrite Hv; constructor); 
try(apply Utils.eqb_neq in Hv; right; unfold not; intros; inversion H; destruct Hv; assumption);
try (destruct IH1; destruct IH2); try (left; constructor; assumption; reflexivity); 
try (right; unfold not; intros; inversion H; subst; destruct n0; try assumption; destruct n; try assumption; reflexivity).
+ admit.
Abort.
*)















