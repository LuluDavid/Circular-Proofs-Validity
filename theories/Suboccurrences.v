Require Export Occurrences.
Import ListNotations.
Local Open Scope eqb_scope.

(** DEFINITIONS *)

(* PreSuboccurrence F G => G is a 'one step away' suboccurrence of F *)
Inductive PreSuboccurrence: Occurrence -> Occurrence -> Prop :=
  | PBinL (F1 F2:formula)(o:op)(A:address): PreSuboccurrence { (Op o F1 F2), A }  { F1, l::A}
  | PBinR (F1 F2:formula)(o:op)(A:address): PreSuboccurrence { (Op o F1 F2), A }  { F2, r::A}
  | PUn (F:formula)(q:quant)(A:address): PreSuboccurrence { (Quant q F), A }  { F, i::A}
  .

Notation "F ⇀ G" := (PreSuboccurrence F G) (at level 100).

(** Suboccurrence: Inductive version *)

Inductive Suboccurrence: Occurrence -> Occurrence -> Prop :=
  | BinL (F1 F2:formula)(o:op)(A:address): Suboccurrence { (Op o F1 F2), A }  { F1, l::A}
  | BinR (F1 F2:formula)(o:op)(A:address): Suboccurrence { (Op o F1 F2), A }  { F2, r::A}
  | Un (F:formula)(q:quant)(A:address): Suboccurrence { (Quant q F), A }  { F, i::A}
  | Refl (F:Occurrence): Suboccurrence F F
  | Trans (F G H:Occurrence): Suboccurrence F G -> Suboccurrence G H -> Suboccurrence F H
  .
Hint Constructors Suboccurrence.


(** Suboccurrence: Boolean version *)
 
Fixpoint suboccurrence_b_rec ( F:formula )(a:address)(G:Occurrence){ struct F } := 
  ({F,a} =? G) ||
  match F, G with 
  | (Op o F1 F2), G => (suboccurrence_b_rec F1 (l::a) G) || (suboccurrence_b_rec F2 (r::a) G)
  | (Quant q F'), G => (suboccurrence_b_rec F' (i::a) G)
  | _, _ => false
  end.

Definition suboccurrence_b (F G:Occurrence) : bool := 
  let '{ F', a} := F in (suboccurrence_b_rec F' a G).  

(** Example *)

Local Open Scope string_scope.

Definition f1 : Occurrence := { // "X", [r;i;i] }.
Definition f2 : Occurrence := { µ (%0 & (// "X")), [i] }.

Lemma example_suboccurrence: Suboccurrence f2 f1.
Proof.
  unfold f1; unfold f2. repeat econstructor. 
Qed.





(** META *)

Lemma suboccurrence_b_refl : forall (F: Occurrence), suboccurrence_b F F = true.
Proof.
  intros; destruct F; destruct F as [ | | | | V | o F1 F2| q F']; 
  simpl; try(intros; apply eqb_eq; trivial); intuition.
Qed.

Lemma suboccurrence_b_trans : forall (F G H: Occurrence), 
  suboccurrence_b F G = true -> suboccurrence_b G H = true -> suboccurrence_b F H = true.
Proof.
  intro; destruct F; destruct G; generalize dependent a; generalize dependent a0.
  induction F; intro; induction H; intros;
  simpl; simpl in H; simpl in H0;
  try(apply orb_true_iff in H; destruct H; try discriminate H;
    apply eqb_eq in H; injection H as H1; subst; simpl in H0; assumption);
  try(repeat rewrite orb_true_iff; 
    repeat rewrite orb_true_iff in H; destruct H;
    try(apply eqb_eq in H; injection H as H1; subst; simpl in H0; repeat rewrite orb_true_iff in H0; assumption);
    try(right; destruct H; try(left; apply (IHF1 a0 (l :: a) {F, a1}); assumption);
                                        try(right; apply (IHF2 a0 (r :: a) {F, a1}); assumption)); reflexivity);
  try(apply orb_true_iff; apply orb_true_iff in H; destruct H; try (right; apply (IHF a0 (i :: a) {F1, a1}); assumption);
    apply eqb_eq in H; injection H as H1; subst; simpl in H0; apply orb_true_iff in H0; destruct H0; 
      try (right; assumption); apply eqb_eq in H; injection H as H1; subst; left; apply eqb_refl).
Qed.

Theorem Suboccurrence_is_suboccurrence_b: forall (F G: Occurrence), 
  Suboccurrence F G <-> suboccurrence_b F G = true.
Proof.
  split.
  - destruct F; destruct G; intros. induction H as [F1 F2 o a'|F1 F2 o a'|F' q a'|F'|F' G' H' IH1 IH2 IH3 IH4]; simpl; 
    try (apply orb_true_iff); try (rewrite orb_true_iff).
    + right; left; destruct F1; simpl; intuition.
    + right; destruct F2; simpl; intuition.
    + right; destruct F'; simpl; intuition.
    + apply suboccurrence_b_refl.
    + apply (suboccurrence_b_trans _ G' _); assumption.
 - destruct F; destruct G; generalize dependent a; generalize dependent a0; 
     induction F as [ | | | | V | o F1 IH1 F2 IH2 | q F' IH];
     induction F0 as [ | | | | V' | o' G1 IH1' G2 IH2' | q' F'' IH']; intros;
     simpl in H; try apply eqb_eq in H; try subst; trivial;
     try (apply orb_true_iff in H; destruct H); try(econstructor; try constructor; apply IH1 in H; assumption);
     try (apply Trans with (G:={F2, r::a}); try constructor; apply IH2 in H; assumption);
     try(apply eqb_eq in H; injection H as H'; subst; constructor);
     try (econstructor; try constructor; apply IH in H; assumption); try discriminate H.
     apply orb_true_iff in H; destruct H.
     -- eapply (Trans _ {F1,(l :: a)} _).
      + constructor.
      + apply IH1; simpl; assumption.
    -- eapply (Trans _ {F2,(r :: a)} _).
      + constructor.
      + apply IH2; simpl; assumption.
Qed.

