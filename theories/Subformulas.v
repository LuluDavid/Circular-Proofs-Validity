Require Export Utils Suboccurrences.
Import ListNotations Arith.

Local Open Scope eqb_scope.

(** DEFINITIONS *)

(** Subformulas **)

(* In [subform F G], the second argument G is a subformula of the first argument F.
    This way, [subform F] is the set of the subformulas of F *)

(** Inductive version *)

Inductive Subform: formula -> formula -> Prop :=
| SRefl (F:formula): Subform F F
| OpL (F G F':formula)(o:op): Subform F G -> Subform (Op o F' F) G
| OpR (F G F':formula)(o:op): Subform F G -> Subform (Op o F F') G
| SFQuant (F G:formula)(q:quant): Subform F G -> Subform (Quant q F) G
.

Hint Constructors Subform.
Notation "F ⧼ G" := (Subform G F) (at level 100).

(** Boolean version *)

Fixpoint subform_b (F G : formula) := 
(F =? G) ||
    match F,G with
    |(Op o F1 F2), G => (subform_b F1 G) || (subform_b F2 G)
    |(Quant q F), G => (subform_b F G)
    | _, _ => false
    end.






(** META *)

Theorem subform_b_refl : forall F,
  subform_b F F = true.
Proof.
  destruct F; simpl; try apply Utils.eqb_refl;
  try (rewrite Utils.eqb_refl); trivial.
Qed.

Theorem subform_b_trans : forall F G H,
  subform_b F G = true -> subform_b G H = true -> subform_b F H = true.
Proof.
  intro; induction F; intro; induction G; intro; induction H; intros; trivial; try discriminate H0; try discriminate H1;
  simpl; simpl in H; simpl in H0; intuition;
  try(rewrite orb_false_r in H0; apply eqb_eq in H0; injection H0 as H0'; subst; assumption; reflexivity);
  try(apply orb_true_iff in H0; apply orb_true_iff; destruct H0;repeat rewrite orb_true_iff in H; destruct H;
    try(apply eqb_eq in H; injection H as H1 H2 H3; subst; left ; assumption);
    try(apply eqb_eq in H; injection H as H1 H2 H3; subst; right ; assumption);
    try(destruct H); 
    try(left; eapply (IHF1 G1 _); try assumption; eapply IHF1; try eassumption; simpl; 
             repeat rewrite orb_true_iff; right; left; apply subform_b_refl);
   try(right; eapply (IHF2 G1 _); try assumption; eapply IHF2; try eassumption; simpl; 
             repeat rewrite orb_true_iff; right; left; apply subform_b_refl);
   try(left; eapply (IHF1 G2 _); try assumption; eapply IHF1; try eassumption; simpl; 
             repeat rewrite orb_true_iff; right; right; apply subform_b_refl);
   try(right; eapply (IHF2 G2 _); try assumption; eapply IHF2; try eassumption; simpl; 
             repeat rewrite orb_true_iff; right; right; apply subform_b_refl);
             reflexivity);
  try(apply orb_true_iff; apply orb_true_iff in H; destruct H;
            try(left; eapply (IHF1 G _); try assumption; try eapply (IHF1 (Quant q G) _); try assumption;
            simpl; rewrite orb_true_iff; right; apply subform_b_refl);
            try(right; eapply (IHF2 G _); try assumption; try eapply (IHF2 (Quant q G) _); try assumption;
               simpl; rewrite orb_true_iff; right; apply subform_b_refl);
               reflexivity);
  try( apply orb_true_iff in H0; destruct H0; 
          try (apply (IHF G1 _); try assumption; apply (IHF (Op o G1 G2) _); try assumption;
          simpl; repeat rewrite orb_true_iff; right; left; apply subform_b_refl); 
          try (apply (IHF G2 _); try assumption; apply (IHF (Op o G1 G2) _); try assumption;
          simpl; repeat rewrite orb_true_iff; right; right; apply subform_b_refl); reflexivity);
  try (apply orb_true_iff in H; destruct H; try (apply eqb_eq in H; injection H as H'; subst; assumption);
  eapply (IHF G _); try assumption; eapply (IHF (Quant q0 G) _); try assumption;
  simpl; rewrite orb_true_iff; right; apply subform_b_refl; reflexivity).
  
  - repeat rewrite orb_true_iff; simpl in H1; simpl in H2; 
    repeat rewrite orb_true_iff in H1; repeat rewrite orb_true_iff in H2.
    destruct H1; destruct H2; 
    try(apply eqb_eq in H1; injection H1 as H1'); try(apply eqb_eq in H2; injection H2 as H2').
     -- subst; left; apply eqb_refl.
     -- subst; destruct H2; right; try (left; assumption); try (right; assumption).
     -- subst; destruct H1; right; try (left; assumption); try (right; assumption).
     -- destruct H1; destruct H2; right; 
        try(left; 
          try (eapply (IHF1 G1 _);try assumption; eapply (IHF1 (Op o0 G1 G2) _); try assumption;
          simpl; repeat rewrite orb_true_iff; right; left; apply subform_b_refl);
          try (eapply (IHF1 G2 _);try assumption; eapply (IHF1 (Op o0 G1 G2) _); try assumption;
          simpl; repeat rewrite orb_true_iff; right; right; apply subform_b_refl);
          reflexivity
        );
        try(right; 
          try (eapply (IHF2 G1 _);try assumption; eapply (IHF2 (Op o0 G1 G2) _); try assumption;
          simpl; repeat rewrite orb_true_iff; right; left; apply subform_b_refl);
          try (eapply (IHF2 G2 _);try assumption; eapply (IHF2 (Op o0 G1 G2) _); try assumption;
          simpl; repeat rewrite orb_true_iff; right; right; apply subform_b_refl)
        ).
   - apply orb_true_iff; repeat rewrite orb_true_iff in H0; simpl in H1; repeat rewrite orb_true_iff in H1.
    destruct H0; destruct H1; 
    try (apply eqb_eq in H0; injection H0 as H0'); try(subst; left; assumption); try(subst; right; assumption);
    try(destruct H0;
      try(left; 
          try (eapply (IHF1 G1 _);try assumption; eapply (IHF1 (Op o0 G1 G2) _); try assumption;
          simpl; repeat rewrite orb_true_iff; right; left; apply subform_b_refl);
          try (eapply (IHF1 G2 _);try assumption; eapply (IHF1 (Op o0 G1 G2) _); try assumption;
          simpl; repeat rewrite orb_true_iff; right; right; apply subform_b_refl);
          reflexivity
        );
        try(right; 
          try (eapply (IHF2 G1 _);try assumption; eapply (IHF2 (Op o0 G1 G2) _); try assumption;
          simpl; repeat rewrite orb_true_iff; right; left; apply subform_b_refl);
          try (eapply (IHF2 G2 _);try assumption; eapply (IHF2 (Op o0 G1 G2) _); try assumption;
          simpl; repeat rewrite orb_true_iff; right; right; apply subform_b_refl)
        )
      ).
    - simpl in H1; simpl in H2; apply orb_true_iff in H1; repeat rewrite orb_true_iff.
      destruct H1.
      -- right; left; eapply (IHF1 G _); try assumption; eapply (IHF1 (Quant q G) _); try assumption;
         simpl; apply orb_true_iff; right; apply subform_b_refl.
      -- right; right; eapply (IHF2 G _); try assumption; eapply (IHF2 (Quant q G) _); try assumption;
         simpl; apply orb_true_iff; right; apply subform_b_refl.
    - simpl in H1; simpl in H2; apply orb_true_iff in H0; apply orb_true_iff in H1; repeat rewrite orb_true_iff;
      destruct H1; try (apply eqb_eq in H1; injection H1 as H1'; subst; assumption);
      destruct H0.
      -- left; eapply (IHF1 G _); try assumption; eapply (IHF1 (Quant q G) _); try assumption;
         simpl; apply orb_true_iff; right; apply subform_b_refl.
      -- right; eapply (IHF2 G _); try assumption; eapply (IHF2 (Quant q G) _); try assumption;
         simpl; apply orb_true_iff; right; apply subform_b_refl.
  - simpl in H1; simpl in H2; repeat rewrite orb_true_iff in H2; destruct H2.
    -- apply eqb_eq in H2; injection H2 as H2'; subst; assumption.
    -- destruct H2.
      + eapply (IHF G1 _); try assumption; eapply (IHF (Op o G1 G2) _); try assumption;
        simpl; repeat rewrite orb_true_iff; right; left; apply subform_b_refl.
      + eapply (IHF G2 _); try assumption; eapply (IHF (Op o G1 G2) _); try assumption;
        simpl; repeat rewrite orb_true_iff; right; right; apply subform_b_refl.
 - apply orb_true_iff; right; simpl in H1; apply orb_true_iff in H1; destruct H1.
  -- eapply (IHF G1 _); try assumption; eapply (IHF (Op o G1 G2) _); try assumption;
      simpl; repeat rewrite orb_true_iff; right; left; apply subform_b_refl.
  -- eapply (IHF G2 _); try assumption; eapply (IHF (Op o G1 G2) _); try assumption;
      simpl; repeat rewrite orb_true_iff; right; right; apply subform_b_refl.
 - simpl in H1; simpl in H2; apply orb_true_iff in H1; destruct H1.
  -- apply eqb_eq in H1; injection H1 as H1'; subst; assumption.
  -- eapply (IHF G _); try assumption; eapply (IHF (Quant q0 G) _); try assumption; 
     simpl; rewrite orb_true_iff; right; apply subform_b_refl.
- apply orb_true_iff; apply orb_true_iff in H0; simpl in H1; repeat rewrite orb_true_iff in H1;
  destruct H0; destruct H1;
  try( apply eqb_eq in H0; injection H0 as H0'); try (apply eqb_eq in H1; injection H1 as H1').
  -- left; subst; apply eqb_refl.
  -- right; subst; assumption.
  -- right; subst; assumption.
  -- right; eapply (IHF G); try assumption; eapply (IHF (Quant q0 G)); try assumption;
     simpl; rewrite orb_true_iff; right; apply subform_b_refl.
Qed.

Theorem subform_b_is_subform : forall F G, (Subform F G) <-> (subform_b F G) = true.
Proof.
intros. split; intros. 
  + induction H as [F | F G F' o IH IH'| F G F' o IH IH'| F G q H IH]; trivial;
    try(apply subform_b_refl);
    try(induction G; trivial; try(simpl; apply orb_true_iff; right; assumption);
      simpl; apply orb_true_iff; right; apply orb_true_iff; right; assumption).
    try(induction G; trivial; try(simpl; apply orb_true_iff; left; assumption);
      simpl; apply orb_true_iff; right; apply orb_true_iff; left; assumption).
  + induction F as [ | | | | V | o F1 IH1 F2 IH2 | q F IH]; 
     induction G as [ | | | | V' | o' G1 IH1' G2 IH2' | q' F' IH'];
     try (constructor; reflexivity); 
     try (constructor; simpl in H; apply IH; assumption);
     try (apply V_eqb_eq in H; rewrite H; constructor);
     try(simpl in H; apply orb_true_iff in H; destruct H); try apply IH1 in H; try apply IH2 in H; 
       try (apply OpL; assumption); try (apply OpR; assumption);
       try discriminate H.
     - simpl in H; apply eqb_eq in H; injection H as H'; subst; constructor.
     - apply andb_true_iff in H; destruct H as [H1 H3]; apply andb_true_iff in H1; destruct H1 as [H1 H2];
       apply Utils.eqb_eq in H1; apply Utils.eqb_eq in H2; apply Utils.eqb_eq in H3; subst; apply SRefl.
     - apply orb_true_iff in H; destruct H.
      -- apply OpR; apply IH1 in H; assumption.
      -- apply OpL; apply IH2 in H; assumption.
    - apply andb_true_iff in H; destruct H; apply Utils.eqb_eq in H; apply Utils.eqb_eq in H0; subst; apply SRefl.
    - apply IH in H; constructor; assumption.
Qed.

Theorem subform_trans : Transitive Subform.
Proof.
  red; intros. apply subform_b_is_subform. 
  apply subform_b_is_subform in H. apply subform_b_is_subform in H0.
  apply (subform_b_trans x y z); assumption.
Qed.
  
Theorem subform_dec : forall F G, (F ⧼ G) \/ (~ (F ⧼ G)).
Proof.
  intros.
  case_eq (subform_b G F) ; intros.
  apply subform_b_is_subform in H ; left ; assumption.
  right ; intro ; apply subform_b_is_subform in H0 ; rewrite H in H0 ; apply diff_false_true in H0 ; contradiction.
Qed.

Lemma subform_size: forall G F, (F ⧼ G) -> (fsize F <= fsize G).
Proof.
  induction G; intros; 
  try(inversion H; subst; reflexivity);
  induction H; trivial; simpl in *; lia.
Qed.

Lemma subform_op_l: forall F1 F2 o, ~ (Op o F1 F2 ⧼ F1).
Proof.
  intros; unfold not; intro; apply subform_size in H; simpl in H; lia.
Qed.

Lemma subform_op_r: forall F1 F2 o, ~ (Op o F1 F2 ⧼ F2).
Proof.
  intros; unfold not; intro; apply subform_size in H; simpl in H; lia.
Qed.

Lemma subform_quant: forall F q, ~ (Quant q F ⧼ F).
Proof.
  intros; unfold not; intro; apply subform_size in H; simpl in H; lia.
Qed.

Theorem subform_antisymmetric: Antisymmetric formula _ Subform.
Proof.
  assert (Hloc: forall x x' o, (x ⧼ Op o x x') /\ (x' ⧼ Op o x x')). { eauto. }
  assert (HlocBis: forall x q, (x ⧼ Quant q x)). { auto. }
  red. induction x; destruct y; intros; trivial; try (inversion H; reflexivity); try (inversion H0; reflexivity).
  - rewrite subform_b_is_subform in *; simpl in *.
    repeat rewrite orb_true_iff in *; destruct H; try (apply eqb_eq; assumption); 
    destruct H0; try (symmetry; apply eqb_eq; assumption).
       destruct (Hloc y1 y2 o0); destruct (Hloc x1 x2 o).
    destruct H; destruct H0; rewrite <- subform_b_is_subform in *.
    + assert (Hloc': (y1 ⧼ x1) /\ (x1 ⧼ y1)). 
      { split; eapply subform_trans; eassumption. }
      destruct Hloc'; apply IHx1 in H5; trivial. clear H6. subst.
      destruct (subform_op_l y1 y2 o0); trivial.
    + assert (Hloc': (y2 ⧼ x1) /\ (x1 ⧼ y2)). 
      { split; eapply subform_trans; eassumption. }
      destruct Hloc'; apply IHx1 in H5; trivial. clear H6. subst.
      destruct (subform_op_r y1 y2 o0); trivial.
    + assert (Hloc': (y1 ⧼ x2) /\ (x2 ⧼ y1)). 
      { split; eapply subform_trans; eassumption. }
      destruct Hloc'; apply IHx2 in H5; trivial. clear H6. subst.
      destruct (subform_op_l y1 y2 o0); trivial.
    + assert (Hloc': (y2 ⧼ x2) /\ (x2 ⧼ y2)). 
      { split; eapply subform_trans; eassumption. }
      destruct Hloc'; apply IHx2 in H5; trivial. clear H6. subst.
      destruct (subform_op_r y1 y2 o0); trivial.
  - rewrite subform_b_is_subform in *; simpl in *.
    destruct (Hloc x1 x2 o). 
    rewrite orb_true_iff in H; destruct H; rewrite <- subform_b_is_subform in *.
    + assert (Hloc': (y ⧼ x1) /\ (x1 ⧼ y)). 
      { split; eapply subform_trans; try eassumption; apply HlocBis. }
      destruct Hloc'.
      apply IHx1 in H3; trivial; subst; destruct (subform_op_l y x2 o); trivial.
    + assert (Hloc': (y ⧼ x2) /\ (x2 ⧼ y)). 
      { split; eapply subform_trans; try eassumption; apply HlocBis. }
      destruct Hloc'.
      apply IHx2 in H3; trivial; subst; destruct (subform_op_r x1 y o); trivial.
  - rewrite subform_b_is_subform in *; simpl in *.
    destruct (Hloc y1 y2 o). 
    rewrite orb_true_iff in H0; destruct H0; rewrite <- subform_b_is_subform in *.
    + assert (Hloc': (x ⧼ y1) /\ (y1 ⧼ x)). 
      { split; eapply subform_trans; try eassumption; apply HlocBis. }
      destruct Hloc'.
      apply IHx in H3; trivial; subst; destruct (subform_op_l y1 y2 o); trivial.
    + assert (Hloc': (x ⧼ y2) /\ (y2 ⧼ x)). 
      { split; eapply subform_trans; try eassumption; apply HlocBis. }
      destruct Hloc'.
      apply IHx in H3; trivial; subst; destruct (subform_op_r y1 y2 o); trivial.
 - rewrite subform_b_is_subform in *; simpl in *. rewrite orb_true_iff in *.
   destruct H; destruct H0.
   + rewrite eqb_eq in H; trivial.
   + rewrite eqb_eq in H; trivial.
   + rewrite eqb_eq in H0; symmetry; trivial.
   + rewrite <- subform_b_is_subform in *.
      assert (Hloc': (y ⧼ x) /\ (x ⧼ y)). 
      { split; eapply subform_trans; try eassumption; apply HlocBis. }
      destruct Hloc'; apply IHx in H1; trivial; subst.
      destruct (subform_quant y q); trivial.
Qed.

(** Link with suboccurrences *)

Require Import Occurrences.

Theorem Subform_Suboccurrences_forget : forall (F G: Occurrence),
  (Suboccurrence F G) -> (Subform (occ_forget F)(occ_forget G)).
Proof.
  destruct F; destruct G. intros.
  induction H as [F1 F2 o a'|F1 F2 o a'|F' q a'|F'|F' G' H' IH1 IH2 IH3 IH4]; simpl; try (constructor; reflexivity).
  - apply OpR; apply SRefl.
  - apply OpL; apply SRefl.
  - apply SFQuant; apply SRefl.
  - destruct F'; destruct G'; destruct H'; simpl; simpl in IH2; simpl in IH4.
    eapply subform_trans; eassumption.
Qed.
