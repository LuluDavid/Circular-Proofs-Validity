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

Lemma le_level_MSubst_Cons : forall (G f: formula) l k n, 
  form_level G <= n -> n <= k -> MSubst G ((k, f)::l) = MSubst G l.
Proof.
  intros. simpl. apply (le_level_BSubst_unchanged G f k n) in H; try assumption. rewrite H; trivial.
Qed.

Lemma le_level_MSubst_All : forall G l n, 
  form_level G <= n -> (forall c, In c l -> n <= fst c) -> MSubst G l = G.
Proof.
  induction l; trivial; intros; destruct a.
  rewrite (le_level_MSubst_Cons G f l n0 n); try assumption.
  - eapply IHl; try eassumption; intros;
    apply H0; simpl; right; assumption.
  - assert (n <= fst (n0, f)). apply H0; left; trivial.
    simpl in H1; assumption.
Qed.

Lemma eq_level_MSubst_Cons : forall (G f: formula) l k n, 
  form_level G = n -> n <= k -> MSubst G ((k, f)::l) = MSubst G l.
Proof.
  intros. eapply le_level_MSubst_Cons; try eassumption; rewrite H; trivial.
Qed.

Lemma eq_level_MSubst_All : forall G l n, 
  form_level G <= n -> (forall c, In c l -> n <= fst c) -> MSubst G l = G.
Proof.
  intros. eapply le_level_MSubst_All; try eassumption; rewrite H; trivial.
Qed.

Lemma BClosed_MSubst : forall G l, BClosed G -> MSubst G l = G.
Proof.
  induction l; intros; simpl; trivial.
  destruct a; rewrite (le_level_BSubst_unchanged G f n 0); try apply le_0_n. 
  - apply IHl in H; assumption.
  - inversion H; unfold level; trivial. 
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

Lemma preFl_Fl_fst : forall F G l, InSubstForm G l -> In G (FL F) -> In G (preFL F l).
Proof.
Admitted.

Lemma preFl_Fl_snd : forall F G l, In G (preFL F l) -> InSubstForm G l \/ In G (FL F).
Proof.
  induction F; simpl; intros; try destruct v;
  try (destruct H; destruct H; right; left; reflexivity).
  - destruct (list_assoc n l) eqn:Heq.
    -- left. induction l; try discriminate Heq.
       simpl; simpl in Heq; destruct a. simpl in H; try destruct H.
       + destruct (n=?n0)%eqb; subst; unfold InSubstForm; simpl.
          ++ injection Heq as Heq; subst; left; trivial.
          ++ right; apply IHl; assumption.
       + destruct H.
   -- simpl in H; destruct H.
      + simpl; right; left; assumption.
      + destruct H.
 - destruct H.
    -- admit.
    -- apply in_app_iff in H; rewrite in_app_iff; destruct H.
      + apply IHF1 in H. destruct H.
        ++ left; assumption.
        ++ right; right; left; assumption.
      + apply IHF2 in H. destruct H.
        ++ left; assumption.
        ++ right; right; right; assumption.
 - destruct H.
    -- admit.
    --  apply IHF in H; destruct H.
      + simpl in H. destruct ((G =? MSubst (Quant q F) l)%eqb) eqn:Heq.
        ++ apply eqb_eq in Heq. admit.
        ++ admit.
      + admit.
Admitted.





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
Lemma FL_Quant: forall q F l, BClosed (Quant q F) -> In (F [[ %0 := Quant q F ]]) (preFL (Quant q F) l).
Proof.
  assert (BClosed_Quant_Op: forall F1 F2 o q, BClosed (Quant q (Op o F1 F2)) 
                                                    -> BClosed (Quant q F1) /\ BClosed (Quant q F2)). admit. 
  induction F; unfold bsubst; simpl; intros; simpl; try destruct v;
  try (right; left; reflexivity).
  - destruct (n =? 0)%eqb eqn:Heq.
    -- apply eqb_eq in Heq; subst; simpl;
        left; apply BClosed_MSubst; assumption.
    -- apply BClosed_quant in H. inversion H. 
      + apply eqb_neq in Heq; destruct Heq; assumption.
      + inversion H1.
  - inversion H; apply BClosed_Quant_Op in H; destruct H. rewrite H1. 
    rewrite in_app_iff. eapply IHF1 in H; eapply IHF2 in H0. 
    unfold bsubst in H0; simpl in H0. 
    unfold bsubst in H; simpl in H. right. 
    destruct H0; destruct H; admit.
 - rewrite BClosed_MSubst; try assumption.
   right. unfold bsubst; simpl. left. apply BClosed_quant_bsubst in H. unfold bsubst in H; simpl in H.
   rewrite BClosed_MSubst; trivial.
Admitted.

Lemma FL_Closed: forall k F l, 1 <= k -> BClosed F -> list_assoc k l = None  -> ~ In (%k) (preFL F l).
Proof.
  induction F; intros; simpl; try destruct v;
    try (unfold not; intros; destruct H2; try discriminate H2; destruct H2; reflexivity); try discriminate H0.
    -- unfold not; intros; destruct H2.
      + rewrite MSubst_Op in H2; discriminate H2.
      + apply BClosed_op in H0; destruct H0; 
         apply in_app_iff in H2. destruct H2.
        ++ destruct (IHF1 l); assumption.
        ++ destruct (IHF2 l); assumption.
   -- unfold not; intro. destruct H2.
    + admit. (* Faisable de discriminer H2 *)
    + apply BClosed_quant in H0. inversion H0.
       ++ admit.
       ++ subst. inversion H4. admit. 
Admitted.










