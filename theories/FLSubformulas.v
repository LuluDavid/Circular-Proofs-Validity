Require Export FLSuboccurrences.
Import ListNotations RelationClasses.


Local Open Scope eqb_scope.
Local Open Scope form.

(** DEFINITIONS *)

(** List: bound variables <-> formulas *)

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


(** Multiple Substitution *)

Fixpoint MSubst(f:formula)(s:SubstType) : formula :=
  match s with
  | [] => f
  | (j, F)::s' => MSubst (f[[ %j := F ]]) s'
  end.

Definition ClosedMSubst l := forall H, InSubstForm H l -> BClosed H.

Definition LevelMSubst l n := forall H, InSubstForm H l -> level H <= n.

(** Example *)

Definition example_formula : formula := %1 &((%0 # ν (%0 & %1)) # ø).
Definition example_subst : SubstType := [(0, ⊥);(1, ⊤)].
  
Definition example := MSubst example_formula example_subst.

Compute example.


(** FL-Subformulas *)

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

Definition FL (f:formula) := preFL f [].

Fixpoint noDupFormula (l : list formula) : list formula :=
    match l with
      | [] => []
      | f::fs => if (list_mem f fs) then (noDupFormula fs) else (f::(noDupFormula fs))
    end.

Definition FLSet (f:formula) := noDupFormula (FL f).

Notation "F ≪ G" := (In F (FL G)) (at level 100).

(** Get the final binding list *)

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

Definition getSubst (f:formula) := preGetSubst f [].


Fixpoint noDupSubst (s:SubstType) : SubstType :=
    match s with
      | [] => []
      | f::fs => if (list_mem f fs) then (noDupSubst fs) else (f::(noDupSubst fs))
    end.

Definition getSubstSet (f:formula) := noDupSubst (getSubst f).

(** Example *)

Local Open Scope string_scope.
Definition exampleFL1: formula :=  (%0) & (! # (// "X")).
Definition exampleFL2: formula := µ(ν(%1 & %0)#ø). (* µX. vY. (X & Y) *)
Compute FLSet exampleFL1.
Compute FLSet exampleFL2.

Local Open Scope eqb_scope.

Definition G': formula := µ((ν(%1 & %0))#%0).
Definition F': formula := (ν(G' & %0))#G'.

Compute FLSet F'.
Compute map level (FLSet F'). 

Compute (FLSet F') =? (FLSet G').


(** FL Minimum in a list *)

Fixpoint FLMinRec (l:list formula)(min:formula): option formula :=
  match l with  
  | []     => Some min
  | f::fs => if list_mem f (FL min) then FLMinRec fs min else 
                                                      if list_mem min (FL f) then FLMinRec fs f else None
  end.

Definition FLMin (l:list formula) : option formula :=
  match l with 
  | []     => None
  | f::fs => FLMinRec fs f
  end.

Compute FLMin (FLSet exampleFL1).
Compute FLMin (FLSet exampleFL2).


(** Comparability *)

Definition FLComp F G := (F ≪ G) \/ (G ≪ F).

Definition FLCompList l := forall F G, In F l -> In G l -> FLComp F G.

(** META *)

(** Lift *)

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

Lemma list_assoc_lift_zero : forall l, list_assoc 0 (↑ l) = None.
Proof.
  induction l; trivial.
  simpl; destruct a; simpl; assumption.
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

Lemma InSubstForm_In: forall F l, InSubstForm F l <-> exists n, In (n, F) l.
Proof.
  split; induction l; intros; cbn in *; simpl in *.
  - inversion H.
  - destruct H.
    + destruct a; simpl in *; subst; exists n; left; trivial.
    + apply IHl in H; destruct H; exists x; right; trivial.
  - destruct H; contradiction.
  - do 2 (destruct H).
    + left; subst; trivial.
    + right; apply IHl; exists x; trivial.
Qed.


Lemma InSubstForm_list_assoc: forall l F, (exists n, list_assoc n l = Some F) -> InSubstForm F l.
Proof.
  induction l; intros; cbn in *; simpl in *.
  - destruct H; discriminate H.
  - destruct a; simpl in *; destruct H; destruct (x =? n).
    + injection H as H; subst; left; trivial.
    + right; apply IHl; exists x; trivial. 
Qed.

Lemma lenght_lift : forall s, length (↑ s) = length s.
Proof.
  induction s; trivial; destruct a; simpl; rewrite IHs; trivial.
Qed.

Local Open Scope list_scope.

Lemma app_lift : forall s1 s2, ↑ (s1 ++ s2) = ↑ s1 ++ ↑ s2.
Proof.
  intros; induction s1; trivial; destruct a; simpl. rewrite IHs1; trivial.
Qed.

(** MSubst *)

Lemma MSubst_Op: forall F1 F2 o s, MSubst (Op o F1 F2) s = Op o (MSubst F1 s) (MSubst F2 s).
Proof.
  intros; generalize dependent F2; generalize dependent F1; induction s; simpl; trivial; intros.
  destruct a; simpl. apply IHs.
Qed.

Lemma MSubst_Quant: forall f q s,
        (MSubst (Quant q f) s) = Quant q (MSubst f (↑ s)).
Proof.
  intros; generalize dependent f;
  induction s; simpl; trivial; intros.
  destruct a; simpl. 
  assert (Hloc: forall n, S n = n+1). 
  { induction n0; trivial; rewrite plus_Sn_m, <- IHn0; trivial. }
  unfold bsubst. simpl. rewrite Hloc. apply IHs.
Qed.

Lemma MSubst_app: forall l1 l2 f,
  MSubst f (l1 ++ l2) = MSubst (MSubst f l1) l2.
Proof.
  induction l1; intros.
  - auto.
  - simpl; destruct a; apply IHl1.
Qed.

Local Open Scope nat_scope.

Lemma level_MSubst_max : forall l F, 
                        form_level (MSubst F l) <= Nat.max (form_level F) (list_max (map form_level (map snd l))).
Proof.
  assert (forall n, Nat.max n 0 = n). { destruct n; trivial. }
  induction l; intros; simpl.
  + unfold list_max; simpl; lia.
  + destruct a; simpl. pose proof (le_level_BSubst F f n (form_level F)(form_level f)).
     rewrite (Nat.max_comm (form_level f) _), Nat.max_assoc.
     pose proof (IHl (F [[ % n := f]])). lia.
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

Lemma BClosed_MSubst_Level : forall F G q l,
  BClosed (Quant q F) -> BClosed G -> BClosed (MSubst F ((0, G)::(lift l))).
Proof.
  intros; simpl. rewrite BClosed_MSubst; apply (BClosed_quant_bsubst q F G) in H; trivial.
Qed. 

Lemma BClosed_MSubst_Unchanged: forall q F G l,
  BClosed (Quant q F) -> BClosed G -> MSubst F ((0, G)::(lift l)) = (F [[ % 0 := G]]).
Proof.
  intros. inversion H. rewrite H2. 
  simpl. apply (BClosed_quant_bsubst q F G) in H; trivial.
  apply BClosed_MSubst; trivial.
Qed.

Lemma MSubst_Swap: forall F G l, ClosedMSubst l -> BClosed G ->
                                                                 MSubst F ((0, G):: ↑ l) = ((MSubst F (↑ l ))[[ %0 := G ]]).
Proof.
   intros; revert dependent F; revert dependent G; induction l; intros.
   - reflexivity.
   - destruct a; simpl. unfold ClosedMSubst, InSubstForm in H; simpl in H. rewrite switch_BSubst; trivial.
    + rewrite <- IHl; trivial.
      ++ unfold ClosedMSubst; intros; apply H; right; trivial.
    + apply H; left; trivial.
Qed.

(** FL-Subformulas *)


Lemma FL_refl: forall f, f ≪ f.
Proof.
  induction f; simpl; try destruct v; try (left; reflexivity).
Qed.

Lemma preFL_refl: forall f l, BClosed f -> In f (preFL f l).
Proof.
  induction f; simpl; try destruct v; try (left; reflexivity); intros; try discriminate H;
  left; apply BClosed_MSubst; trivial.
Qed.

Local Open Scope eqb_scope.

Lemma FL_Op: forall o F1 F2 G, (G ≪ Op o F1 F2) -> (G = Op o F1 F2) \/ (G ≪ F1) \/ (G ≪ F2).
Proof.
  intros; simpl in H; destruct H; intuition.
Qed.

Local Open Scope nat_scope.

Lemma FL_Quant: forall q F, BClosed (Quant q F) -> (F [[ %0 := Quant q F ]]) ≪ (Quant q F).
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

Theorem FLsubform_dec : forall F G, (F ≪ G) \/ (~ (F ≪ G)).
Proof.
  intros; pose proof (@InDec formula);
  eapply H; apply eqbspec_formula. 
Qed.

Local Open Scope list_scope.

Local Open Scope eqb_scope.

(* BClosed Conservation *)

Lemma preFL_BClosed : forall F G l, BClosed (MSubst F l) -> ClosedMSubst l
                                                          -> In G (preFL F l) -> BClosed G.
Proof.
  unfold ClosedMSubst; induction F; intros; try destruct v;
  try(simpl in H1; destruct H1; try contradiction; subst; reflexivity).
  - simpl in H1; destruct (list_assoc n l) eqn:Heq.
    + simpl in H1; destruct H1; try contradiction; subst; 
       eapply H0; apply InSubstForm_list_assoc; exists n; trivial.
    + simpl in H1; destruct H1; try contradiction; subst. 
       induction l.
       ++ inversion H.
       ++ simpl in H; simpl in Heq; destruct a; unfold bsubst in H; simpl in H;
            destruct (n=?n0) eqn:Heq'; try discriminate Heq.
            apply IHl; trivial; intros;
            apply H0; cbn; right; trivial.
   - simpl in H1. destruct H1.
    + subst; trivial.
    + rewrite MSubst_Op in H; apply BClosed_op in H; destruct H. 
      apply in_app_iff in H1; destruct H1.
      ++ eapply IHF1; eassumption. 
      ++ eapply IHF2; eassumption. 
   - simpl in H1. destruct H1.
    + subst; trivial.
    + apply (IHF _ ((0, MSubst (Quant q F) l) :: ↑ l)); trivial.
      ++ rewrite MSubst_Swap; trivial.
           eapply BClosed_quant_bsubst; try eassumption.
           rewrite MSubst_Quant in H. eassumption.
      ++ intros. cbn in H3. destruct H3.
        +++ subst; trivial.
        +++ fold (InSubstForm H2 (↑ l)) in H3. 
                apply H0; apply InSubstForm_lift; trivial.
Qed.

(* Not generalizable to level n: for instance, 
      F = µ.(%1)#ø -> level F = 1, but In (%1) (FL F) and level (%1) = 2  *)

Corollary FL_BClosed : forall F G, BClosed F -> (G ≪ F) -> BClosed G.
Proof.
    intros; apply (preFL_BClosed F G []); simpl; trivial; unfold ClosedMSubst; intros; inversion H2.
Qed.

(* No free variables appearing *)

Corollary FL_FVars : forall F, BClosed F -> forall k, ~ In (% k)(FL F).
Proof.
  intros; unfold not; intros; apply (FL_BClosed F (% k)) in H; trivial; discriminate H.
Qed.

Lemma FL_Forget : forall F G, (F ⋘ G) -> occ_forget F ≪ occ_forget G.
Proof.
Admitted.

(** FLComparable *)

Lemma FLComp_Rev : forall F G, FLComp F G <-> FLComp G F.
Proof.
  intros; unfold FLComp; rewrite or_comm; reflexivity.
Qed.

Lemma FLComp_Comm : forall f1 f2 l1 l2, FLCompList (l1 ++ f1 :: f2 :: l2) = FLCompList (l1 ++ f2 :: f1 :: l2).
Proof.
Admitted.

Lemma FLComp_Trans : forall F G H, FLComp F G -> FLComp G H -> FLComp F H.
Proof.
Admitted.

Lemma FLComp_List l F: FLCompList l -> (exists G, In G l /\ FLComp F G) -> FLCompList (F::l).
Proof.
  unfold FLCompList. do 3 intro. do 2 destruct H0.
  intros. simpl in *. destruct H2; destruct H3; subst; intuition; try (left; apply FL_refl).
  + eapply FLComp_Trans; try eassumption; apply H; trivial.
  + apply FLComp_Rev; apply (FLComp_Trans _ x _); trivial; apply H; trivial.
Qed.

Lemma FLComp_List_Bis l F: FLCompList (F::l) -> FLCompList l.
Proof.
  unfold FLCompList; intros;
  apply H; simpl; right; trivial.
Qed.

















