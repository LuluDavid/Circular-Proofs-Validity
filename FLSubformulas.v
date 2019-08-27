Require Import Arith.
Require Export Setoid Morphisms RelationClasses Arith Omega Bool String MSetRBT StringOrder List Utils.
Require DecimalString.
Import ListNotations.
Require Import Defs Debruijn Subformulas.
Local Open Scope eqb_scope.
Local Open Scope list_scope.
Local Open Scope formula_scope.

(** FL-SUBFORMULAS **)

(* List of association between bound variables and formulas *)

Definition SubstType := list (nat*formula).

Instance eqb_c : Eqb (nat*formula) :=
  fix eqb_c c1 c2 :=
    let (n1, f1) := c1 in let (n2, f2) := c2 in (n1 =? n2) && (f1 =? f2).

Definition InSubstForm (f:formula)(s:SubstType) : Prop := In f (map snd s).

Fixpoint lift (s:SubstType): SubstType :=
  match s with
  | [] => []
  | (j, F)::s' => (S j, F)::(lift s')
  end.

Notation "↑ s" := (lift s) (at level 50).

Fixpoint Subst (s:SubstType) : Prop :=
  match s with
  | [] => False
  | (n, F)::s' => list_assoc n s' = None /\ Subst s'
  end.
  
Lemma list_assoc_lift : forall n s, list_assoc (S n) (↑s) = list_assoc n s.
Proof.
  induction s; simpl; trivial.
  destruct a; simpl; subst; simpl; destruct (n =? n0) eqn:Heq.
  - simpl; apply eqb_eq in Heq; subst; repeat rewrite eqb_refl; trivial. 
  - destruct (S n =? S n0) eqn:Heq'; simpl.
    + apply eqb_eq in Heq'; injection Heq' as Heq'; 
       apply eqb_neq in Heq; destruct Heq; assumption.
    + assumption.
Qed.

Lemma InSubstForm_lift: forall F l, InSubstForm F l <-> InSubstForm F (lift l).
Proof.
  induction l; split; intros; simpl; try assumption.
  - destruct a; unfold InSubstForm; simpl; unfold InSubstForm in H; simpl in H.
    destruct H; try(left; assumption).
    right. apply IHl; assumption.
  - unfold InSubstForm; unfold InSubstForm in H; destruct a; simpl; simpl in H.
    destruct H; try (left; assumption); right; apply IHl; assumption.
Qed.

Lemma lenght_lift : forall s, length (↑ s) = length s.
Proof.
  induction s; trivial; destruct a; simpl; rewrite IHs; trivial.
Qed.


(* SubstTypeitution of several bound variables in f (by their associated formulas in s) *)

Fixpoint MSubst(f:formula)(s:SubstType) : formula :=
  match s with
  | [] => f
  | (j, F)::s' => MSubst (f[[ %j := F ]]) s'
  end.

Definition example_formula : formula := %1 &((%0 # ν (%0 & %1)) # ø).
Definition example_subst : SubstType := [(0, ⊥);(1, ⊤)].
  
Definition example := MSubst example_formula example_subst.

Compute example.

Lemma MSubst_Op: forall F1 F2 o s, MSubst (Op o F1 F2) s = Op o (MSubst F1 s) (MSubst F2 s).
Proof.
  intros; generalize dependent F2; generalize dependent F1; induction s; simpl; trivial; intros.
  destruct a; simpl. apply IHs.
Qed.

Lemma MSubst_Quant: forall f q s a b,
        MSubst (Quant q (form_bsubst a b f)) s = Quant q (MSubst f ((a, b) :: ↑ s)).
Proof.
  intros; generalize dependent f; generalize dependent a; generalize dependent b; 
  induction s; simpl; trivial; intros.
  destruct a; simpl. 
  assert (Hloc: forall n, S n = n+1). 
  { induction n0; trivial; rewrite plus_Sn_m, <- IHn0; trivial. }
  unfold bsubst. simpl. rewrite Hloc. apply IHs.
Qed.

Lemma le_level_MSubst_Cons : forall (G f: formula) l n, 
  form_level G <= n -> MSubst G ((n, f)::l) = MSubst G l.
Proof.
  intros. simpl. apply (le_level_BSubst_unchanged G f n) in H; try assumption. rewrite H; trivial.
Qed.

Lemma le_level_MSubst_All : forall G l n, 
  form_level G <= n -> (forall c, In c l -> n <= fst c) -> MSubst G l = G.
Proof.
  induction l; trivial; intros; destruct a.
  rewrite (le_level_MSubst_Cons G f l n0); try assumption.
  - eapply IHl; try eassumption; intros;
    apply H0; simpl; right; assumption.
  - assert (n <= fst (n0, f)). apply H0; left; trivial.
    eapply le_trans; eassumption.
Qed.

Lemma BClosed_MSubst : forall G l, BClosed G -> MSubst G l = G.
Proof.
  induction l; intros; simpl; trivial.
  destruct a. rewrite le_level_BSubst_unchanged.
  - apply IHl; assumption.
  - rewrite H; apply le_0_n.
Qed.



(* FL f returns the list of FL-subformulas of F *)

Fixpoint preFL (f:formula)(s:SubstType) : list formula :=
  match f with
  | ⊥ | ⊤ | ! | ø => [f]
  | (// s) => [f] 
  | (% k) => let F := list_assoc k s in (match F with
                                                             | None => [f]
                                                             | Some F' => [F']
                                                             end
                                                             )
  | Op o F G => (MSubst f s) :: (preFL F s) ++ (preFL G s) 
  | Quant q F => (MSubst f s) :: (preFL F ( (0, (MSubst f s)) :: (↑s)))
  end.

Fixpoint preGetSubst (f:formula)(s:SubstType) : SubstType :=
  match f with
  | ⊥ | ⊤ | ! | ø => []
  | (// p) => []
  | (% k) => let F := list_assoc k s in (match F with
                                                 | None => []
                                                 | Some F' => s
                                                 end
                                                 )
  | Op o F G => (preGetSubst F s) ++ (preGetSubst G s) 
  | Quant q F => (preGetSubst F ( (0, (MSubst f s)) :: (↑ s)))
  end.

Definition FL (f:formula) := preFL f [].

Definition list_assocSubst (f:formula) := preGetSubst f [].

Fixpoint InSubst (p:nat*formula) lp : bool :=
  match lp with
  | [] => false
  | (n,f)::fs => let (m,g) := p in ((m =? n) && (f =? g))  || InSubst p fs
  end.
  
Fixpoint noDupFormula (l : list formula) : list formula :=
    match l with
      | [] => []
      | f::fs => if (list_mem f fs) then (noDupFormula fs) else (f::(noDupFormula fs))
    end.

Fixpoint noDupSubst (s:SubstType) : SubstType :=
    match s with
      | [] => []
      | f::fs => if (list_mem f fs) then (noDupSubst fs) else (f::(noDupSubst fs))
    end.

Definition FLSet (f:formula) := rev (noDupFormula (FL f)).

Definition list_assocSubstSet (f:formula) := noDupSubst (list_assocSubst f).

Local Open Scope string_scope.
Definition exampleFL1: formula :=  (%1) & (! # (// "X")).
Definition exampleFL2: formula := µ(ν(%2 & %1)). (* µX. vY. (X & Y) *)
Compute FLSet exampleFL1.
Compute FLSet exampleFL2.

Local Open Scope eqb_scope.
Definition G': formula := µ((ν(%1 & %0))#%0).
Definition F': formula := (ν(G' & %0))#G'.

Compute FLSet F'.
Compute map level (FLSet F'). (* It seems that the subformulas of a closed formula are all closed *)

Compute (FLSet F') =? (FLSet G').



Lemma FL_refl: forall f, In f (FL f).
Proof.
  induction f; simpl; try destruct v; try (left; reflexivity).
Qed.

Local Open Scope eqb_scope.

Lemma FL_Op: forall o F1 F2 G, In G (FL (Op o F1 F2)) -> G = Op o F1 F2 \/ In G (FL F1) \/ In G (FL F2).
Proof.
  intros; simpl in H; destruct H; intuition.
Qed.

Local Open Scope nat_scope.
(* We first check that F[X/µX.F] is in FL(µX.F) *)
Lemma FL_Quant: forall q F, BClosed (Quant q F) -> In (F [[ %0 := Quant q F ]]) (FL (Quant q F)).
Proof. 
  induction F; unfold bsubst; simpl; intros; simpl; try destruct v;
  try (right; left; reflexivity).
  - destruct (n =? 0)%eqb eqn:Heq.
    -- apply eqb_eq in Heq; subst; simpl;
        left; trivial.
    -- apply BClosed_quant in H. inversion H. 
      + apply eqb_neq in Heq; destruct Heq; assumption.
      + inversion H1.
Qed.

Lemma FL_BClosed : forall F G l, BClosed F -> (forall n H, list_assoc n l = Some H -> BClosed H) 
                                                          -> In G (preFL F l) -> BClosed G.
Proof.
  intros; generalize dependent l; induction F; intros; try destruct v;
  try(inversion H1; subst; trivial; inversion H2).
  + simpl in H1. destruct (list_assoc n l) eqn:Heq.
    - apply H0 in Heq; inversion H1; subst; try assumption; inversion H2.
    -  inversion H1; subst; try assumption; inversion H2.
  + admit.
  + admit.
Admitted.

Lemma FL_Closed: forall k F l, level F <= k -> list_assoc k l = None  -> ~ In (% k ) (preFL F l).
Proof.
Admitted.










