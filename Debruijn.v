Require Export StringUtils Defs.
Import ListNotations Ascii.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope string_scope.
Local Open Scope eqb_scope.

(** VARIABLES *)

Inductive V :=
  | FVar : variable -> V (** Free 2nd Order Variable (global name) *)
  | BVar : nat -> V (** Bounded 2nd Order variable (de Bruijn indices) *)
  .

Instance V_eqb : Eqb V :=
 fix v_eqb V1 V2 :=
  match V1, V2 with
  | FVar v1, FVar v2 => v1 =? v2
  | BVar n1, BVar n2 => n1 =? n2
  | _, _ => false
  end.

Delimit Scope V_scope with V.
Bind Scope V_scope with V.





(** FORMULAS *)

Inductive formula :=
  | Top
  | Bot
  | One
  | Zero
  | Var: V -> formula
  | Op : op -> formula -> formula -> formula
  | Quant : quant -> formula -> formula.

Fixpoint fsize (F : formula) := match F with
| Var _ => 1
| Zero | One | Top | Bot => 1
| Op _ G H => S ((fsize G) + (fsize H))
| Quant _ G => S (fsize G)
end.

Local Open Scope nat_scope.

Lemma fsize_pos : forall (F:formula), 0 < fsize F.
Proof.
induction F ; simpl; intuition.
Qed.

(* Notations *)

Delimit Scope formula_scope with form.
Bind Scope formula_scope with formula.

Notation "⊥" := Bot.
Notation "⊤" := Top.
Notation "!" := One.
Notation "'ø'" := Zero.
Infix "⊕" := (Op Or_add) (at level 85, right associativity) : formula_scope.
Infix "#" := (Op Or_mult) (at level 85, right associativity) : formula_scope.
Infix "&" := (Op And_add) (at level 85, right associativity) : formula_scope.
Infix "⊗" := (Op And_mult) (at level 85, right associativity) : formula_scope.

Notation "// V" := (Var (FVar V)) (at level 20) : formula_scope.
Notation "% n" := (Var (BVar n)) (at level 20) : formula_scope.

Notation "'µ' A " := (Quant mu A)
 (at level 200, right associativity) : formula_scope.
Notation "'ν' A" := (Quant nu A)
 (at level 200, right associativity) : formula_scope.

Local Open Scope form.


Definition Naturals:formula := (µ (!⊕(%0))).


(* Dual *)

Fixpoint dual (F : formula) : formula := match F with
| Var X => Var X
| Zero => ⊤
| One => ⊥
| ⊥ => One
| ⊤ => Zero
| Op Or_add G  H => Op And_add (dual G) (dual H)
| Op Or_mult G H => Op Or_mult (dual G) (dual H)
| Op And_add G H => Op Or_add (dual G) (dual H)
| Op And_mult G H => Op And_mult (dual G) (dual H)
| Quant mu G => Quant nu (dual G)
| Quant nu G => Quant mu (dual G)
end.

Notation "~ F" := (dual F) (at level 75, right associativity).

Lemma dual_inv : forall F, dual(dual F) = F.
Proof.
  intros. induction F as [ | | | |V|Op F1 IH1 F2 IH2|Quant F' IH]; intuition; try discriminate H.
  + destruct Op; simpl; rewrite IH1, IH2; trivial.
  + destruct Quant; simpl; rewrite IH; trivial.
Qed.

Lemma codual : forall (A B:formula), dual A = B <-> A = dual B. 
Proof.
intros A B ; split ; intro H.
- rewrite <- dual_inv at 1.
  rewrite H.
  reflexivity.
- rewrite <- dual_inv.
  rewrite H.
  reflexivity.
Qed.

Lemma dual_inj : forall (A B:formula), dual A = dual B -> A = B.
Proof.
intros.
rewrite <-  (dual_inv A).
rewrite <- (dual_inv B).  
rewrite H.
reflexivity.
Qed.

Lemma fsize_dual : forall (F:formula), fsize (dual F) = fsize F.
Proof.
induction F ; simpl ;
  try (rewrite IHF1 ; rewrite IHF2) ;
  try rewrite IHF ;
  try reflexivity.
- destruct o; simpl; intuition.
- destruct q; simpl; intuition.
Qed.

Definition NaturalsDual := dual Naturals.







(** Some generic functions, meant to be overloaded
    with instances for variables, formulas, context, sequent, ... **)

(** Replace a bound variable with a formula, useful for unfolding **)
Class BSubst (A : Type) := bsubst : nat -> formula -> A -> A.
Arguments bsubst {_} {_} _ _ !_.

(** Level : succ of max bounded variable *)
Class Level (A : Type) := level : A -> nat.
Arguments level {_} {_} !_.

Hint Unfold BSubst Level.

(** Some generic definitions based on the previous ones *)

Definition BClosed {A}`{Level A} (a:A) := level a = 0.

Hint Unfold BClosed.

Notation "f [[ % n := F ]]" := (bsubst n F f) (at level 150, right associativity).







Local Open Scope eqb_scope.
 
(** Some structural extensions of these generic functions *)

Instance bsubst_list {A}`{BSubst A} : BSubst (list A) :=
 fun n t => List.map (bsubst n t).

Instance level_list {A}`{Level A} : Level (list A) :=
 fun l => list_max (List.map level l).
 
Instance bsubst_pair {A B}`{BSubst A}`{BSubst B} : BSubst (A*B) :=
 fun n t '(a,b) => (bsubst n t a, bsubst n t b).

Instance level_pair {A B}`{Level A}`{Level B} : Level (A*B) :=
 fun '(a,b) => Nat.max (level a) (level b).





(** Neutral [formula] *)

Definition neutral (f:formula) : Prop := In f [ ⊥ ; ⊤ ; ! ; ø ].

(** Atomic [formula] *)
Inductive atomic : formula -> Prop :=
| atomic_var : forall x, atomic (Var x).







(** VARIABLES *)

Instance V_level : Level V :=
 fix V_level v :=
 match v with
 | BVar n => S n
 | FVar v' => 0
 end.

Definition V_bsubst (n:nat)(u:formula)(v:V): formula :=
  match v with
  | FVar v' => Var v
  | BVar k => if (k =? n) then u else (Var v)
  end.
 

Fixpoint print_formula (f:formula) :=
  match f with
  | Bot => "⊥"
  | Top => "⊤"
  | One => "1"
  | Zero => "0"
  | (% n)%form => "%" ++ (String (ascii_of_nat (48 + n)) "")
  | (// V)%form => V
  | Op o f f' =>
    "{ " ++ print_formula f ++ " }" ++ pr_op o ++ "{ " ++ print_formula f' ++ " }"
  | Quant q f => pr_quant q ++ "{ " ++ print_formula f ++ " }"
  end.

Compute print_formula (Naturals).
Compute print_formula (NaturalsDual).

(** Utilities about formula *)

(* A formula level is the maximum number of missings binders for a binded variable.
    It means that for a formula F, you need at least level F binders to close the formula.
*)
  
Instance form_level : Level formula :=
  fix form_level (f:formula) :=
  match f with
  | Top | Bot | One | Zero => 0
  | Var X  => V_level X 
  | Op _ f1 f2 => Nat.max (form_level f1) (form_level f2)
  | Quant _ f' => Nat.pred (form_level f')
  end.

Compute form_level (µ((% 0)&(!#(% 0))))%form.

Lemma BClosed_quant: forall F q, BClosed (Quant q F) -> form_level F <= 1.
Proof.
  intros. unfold BClosed, level in H; simpl; simpl in H.
  assert (forall n, Nat.pred n = 0 <-> n <= 1). 
  { split; induction n; intro; trivial.
    - constructor; trivial.
    - simpl in H0; subst; trivial.
    - inversion H0; subst; trivial; inversion H2; subst.
  }
  apply H0; assumption.
Qed. 

Lemma BClosed_op: forall (F1 F2: formula) (o:op), BClosed (Op o F1 F2) <-> (BClosed F1) /\ (BClosed F2).
Proof.
  intros. split; intro. unfold BClosed in H; unfold level in H; simpl in H.
  assert (Hloc: forall n m, Nat.max n m = 0 -> n = 0 /\ m = 0).
  { intros; generalize dependent m; induction n; induction m; intros; split; trivial;
    try (discriminate H0).
   }
   apply Hloc in H; destruct H; split; assumption.
   destruct H. unfold BClosed, level; simpl. rewrite H, H0; trivial.
Qed.

Lemma level_quant: forall F q n, form_level (Quant q F) <= n -> form_level F <= S n.
Proof.
  intros; simpl in H; apply le_pred_S in H; assumption.
Qed.

Lemma level_quant_eq: forall F q n, form_level (Quant q F) = n -> form_level F <= S n.
Proof.
  intros. eapply level_quant. erewrite H. trivial.
Qed.

(** Important note : [bsubst] below is only intended to be
    used with a replacement formula [f] which is closed *)

(* bsubst n F f <=> f[%n := F] <=> the free var with debruijn index n replaced by F in f*)
Instance form_bsubst : BSubst formula :=
 fix form_bsubst n F f :=
 match f with
  | Top | Bot | One | Zero  => f
  | Var V =>  V_bsubst n F V
  | Op o f1 f2 => Op o (form_bsubst n F f1) (form_bsubst n F f2)
  | Quant q f' => Quant q (form_bsubst (S n) F f')
 end.
 
Definition example1: formula := µ (%1 # (ν %1 & %0)).
Definition example2:formula := example1[[ %0 := //"A" ]].
Compute example1.
Compute example2.


Instance form_eqb : Eqb formula :=
 fix form_eqb f1 f2 :=
  match f1, f2 with
  | Top, Top | Bot, Bot | One, One | Zero, Zero=> true
  | Var X, Var Y => (X =? Y)%V 
  | Op o1 f1 f1', Op o2 f2 f2' =>
    (o1 =? o2) &&&
    form_eqb f1 f2 &&&
    form_eqb f1' f2'
  | Quant q1 f1', Quant q2 f2' =>
    (q1 =? q2) &&& form_eqb f1' f2'
  | _,_ => false
  end.
  
(* Difference between bounded and free variables *)
Compute    (µ((% 0)&(!#(% 0))))%form 
                                   =?
                   (µ((// "V")&(!#(// "V"))))%form.

Lemma le_level_BSubst_unchanged : forall G f k n, 
  form_level G <= n -> n <= k -> G[[ %k := f ]] = G.
Proof.
  induction G; intros; try destruct v; try (inversion H0; reflexivity); cbn; simpl.
 - destruct (n0 =? k) eqn:Heq; try apply eqb_eq in Heq; subst; trivial; simpl in H;
    omega with *.
 -  apply max_le in H; destruct H;
    try (rewrite (IHG1 _ _ n));
    try (rewrite (IHG2 _ _ n)); try assumption;
    trivial.
- simpl in H;
  rewrite (IHG f (S k) (S n)); trivial.
  -- apply le_pred_S in H; assumption.
  -- apply le_n_S in H0; assumption.
Qed.

Lemma eq_level_BSubst_unchanged : forall G f k n, 
  form_level G = n -> n <= k -> G[[ %k := f ]] = G.
Proof.
  intros; eapply le_level_BSubst_unchanged; try eassumption; rewrite H; trivial.
Qed.

Lemma le_level_BSubst : forall (G f:formula) k n1 n2, 
  form_level G <= n1 -> form_level f <= n2 -> form_level (G[[ %k := f ]]) <= Nat.max n1 n2.
Proof.
  induction G; intros; try destruct v; simpl; try apply le_0_n.
  - unfold bsubst; simpl. 
    destruct (le_max n1 n2).
    destruct (n =? k);
    eapply le_trans; eassumption.
  - simpl in H. apply max_le in H. destruct H. 
    apply (IHG1 f k n1 n2) in H; try assumption.
    apply (IHG2 f k n1 n2) in H1; try assumption.
    destruct (le_max_bis (form_level (G1 [[ % k := f]])) (form_level (G2 [[ % k := f]]))).
    -- apply (le_trans _ (form_level (G1 [[ % k := f]])) _); assumption.
    -- apply (le_trans _ (form_level (G2 [[ % k := f]])) _); assumption.
  - apply le_pred_S. rewrite (max_S n1 n2).
    apply IHG; try assumption; apply (level_quant G q n1) in H; try assumption.
    eapply le_trans; try eassumption; apply le_S; trivial.
Qed.

Lemma eq_level_BSubst : forall (G f:formula) k n1 n2, 
  form_level G = n1 -> form_level f = n2 -> form_level (G[[ %k := f ]]) <= Nat.max n1 n2.
Proof.
  intros; eapply le_level_BSubst; try eassumption; try rewrite H; try rewrite H0; trivial.
Qed.

Lemma BClosed_level_bsubst: forall F G k, 
  BClosed F -> F [[ %k := G ]] = F.
Proof.
  intros. apply (eq_level_BSubst_unchanged F G _ 0); try assumption; apply le_0_n.
Qed.

Lemma BClosed_quant_bsubst : forall q F,
  BClosed (Quant q F) -> BClosed (F[[ %0 := Quant q F ]]).
Proof.
  assert (Hloc: forall q o F1 F2, BClosed (F1 [[ %0 := Quant q F1 ]]) -> BClosed (F2 [[ %0 := Quant q F2 ]])
                              -> BClosed (F1 [[ %0 := Quant q (Op o F1 F2) ]]) /\  BClosed (F2 [[ %0 := Quant q (Op o F1 F2) ]])). 
  admit.
  intros.
  apply BClosed_quant in H. inversion H.
  - unfold BClosed, level. 
    induction F; unfold bsubst; try destruct v; simpl; trivial.
    -- simpl in H1. injection H1 as H1. subst. rewrite eqb_refl. trivial.
    -- simpl in H. apply max_le in H. destruct H. 
       simpl in H1. inversion H; inversion H0.
       + apply IHF1 in H; try assumption. apply IHF2 in H0; try assumption. 
          unfold bsubst in H; simpl in H. unfold bsubst in H0; simpl in H0.
          pose proof eq_level_BSubst as Lemma.
          destruct (Lemma F1 (Quant q (Op o F1 F2)) 0 1 0); try assumption.
          ++ simpl. omega with *.
          ++ apply (Hloc q o F1 F2) in H; try assumption. destruct H. rewrite H, H2; trivial.
          ++ apply (Hloc q o F1 F2) in H; try assumption. destruct H. rewrite H, H2; trivial.
       + inversion H4. rewrite H6. apply IHF1 in H3; try assumption. 
          apply (BClosed_level_bsubst F2 (Quant q F2) 0) in H6.
          apply (Hloc q o F1 F2) in H3.
          ++ destruct H3. fold level; rewrite H3. rewrite H5. trivial.
          ++ rewrite H6. inversion H4; assumption.
       + inversion H3. rewrite H6. apply IHF2 in H0; try assumption. 
          apply (BClosed_level_bsubst F1 (Quant q F1) 0) in H6.
          apply (Hloc q o F1 F2) in H0.
          ++ destruct H0. fold level; rewrite H0. rewrite H4. trivial.
          ++ rewrite H6. inversion H3; assumption.
       + inversion H3; inversion H5. rewrite H7. destruct (Hloc q o F1 F2).
          ++ apply (BClosed_level_bsubst F1 (Quant q F1) 0) in H7.
                rewrite H7. inversion H3; assumption.
          ++ apply (BClosed_level_bsubst F2 (Quant q F2) 0) in H8.
                rewrite H8. inversion H5; assumption.
          ++ rewrite H6, H9; trivial.
    -- admit.
  - rewrite BClosed_level_bsubst; inversion H1; assumption. 
Admitted.

(** Contexts *)


Definition context := list formula.

Definition print_ctx Γ :=
  String.concat ", " (List.map print_formula Γ).

(** bsubst, level, eqb : given by instances
    on lists. *)

(** Sequent *)

Inductive sequent :=
| Seq : context -> sequent.

Notation "⊦ F" := (Seq F) (at level 100).

Definition print_seq '(⊦ Γ) :=
  " ⊦ " ++ print_ctx Γ.

Instance bsubst_seq : BSubst sequent :=
 fun n u '(⊦ Γ ) => (⊦ (Γ[[ %n := u ]]) ).

Instance level_seq : Level sequent :=
 fun '(⊦ Γ ) => level Γ .

Instance seq_eqb : Eqb sequent :=
 fun '(⊦ Γ1) '(⊦ Γ2) => (Γ1 =? Γ2).

Definition ctx_example : context := [(µ((% 0)&(!#(% 0)))); (ν(µ((% 1)&(!#(% 0)))))].

Compute level ctx_example.

Instance : EqbSpec V.
Proof.
  red.
  fix IH 1. destruct x as [v|n], y as [v'|n']; cbn; try cons.
 - case eqbspec; cons.
 - case eqbspec; cons.
Qed.

Instance : EqbSpec formula.
Proof.
  red.
  fix IH 1. induction x as [ | | | |V|Op F1 IH1 F2 IH2|Quant F IH']; destruct y eqn: Hy; 
  cbn; try cons; try (case eqbspec; cons).
  - case eqbspec; [ intros <- | cons ]. case IH1; try cons. case IH2; try cons.
  - case eqbspec; [ intros <- | cons ]. case IH; cons. 
Qed.

Instance : EqbSpec context.
Proof.
 apply eqbspec_list.
Qed.

Instance : EqbSpec sequent.
Proof.
 intros [] []. cbn. repeat (case eqbspec; try cons).
Qed.
