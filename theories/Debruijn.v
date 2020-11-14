Require Export StringUtils Defs Lia.
Import ListNotations Ascii.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope string_scope.
Local Open Scope eqb_scope.

(** DEFINITIONS *)

(** Variables *)

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





(** Formulas *)

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

Definition NuFormula (f:formula) : Prop :=
  match f with
  | (ν _) => True
  | _ => False
  end.


(** Neutral [formula] *)

Definition neutral (f:formula) : Prop := In f [ ⊥ ; ⊤ ; ! ; ø ].

(** Atomic [formula] *)
Inductive atomic : formula -> Prop :=
| atomic_var : forall x, atomic (Var x).


Definition Naturals:formula := (µ (!⊕(%0))).





(** Dual *)

Fixpoint dual (F : formula) : formula := match F with
| Var X => Var X
| Zero => ⊤
| One => ⊥
| ⊥ => One
| ⊤ => Zero
| Op Or_add G  H => Op And_add (dual G) (dual H)
| Op Or_mult G H => Op And_mult (dual G) (dual H)
| Op And_add G H => Op Or_add (dual G) (dual H)
| Op And_mult G H => Op Or_mult (dual G) (dual H)
| Quant mu G => Quant nu (dual G)
| Quant nu G => Quant mu (dual G)
end.

Notation "~ F" := (dual F) (at level 75, right associativity).


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

Notation "f [[ % n := F ]]" := (bsubst n F f) (at level 150, right associativity) : formula_scope.

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







(** Vars Instances *)

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






(** Formula Instances *)

(** A formula level is the maximum number of missings binders for a binded variable.
    It means that for a formula F, you need at least level F binders to close the formula. *)
  
Instance form_level : Level formula :=
  fix form_level (f:formula) :=
  match f with
  | Top | Bot | One | Zero => 0
  | Var X  => V_level X 
  | Op _ f1 f2 => Nat.max (form_level f1) (form_level f2)
  | Quant _ f' => Nat.pred (form_level f')
  end.

Compute form_level (µ((% 0)&(!#(% 0))))%form.

(** Important note : [bsubst] below is only intended to be
    used with a replacement formula [f] which is closed *)

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




(** CONTEXTS *)

Notation context := (list formula).

Definition print_ctx Γ :=
  String.concat ", " (List.map print_formula Γ).

(** bsubst, level, eqb : given by instances
    on lists. *)



(** SEQUENTS *)

Inductive sequent :=
| Seq : context -> sequent.

Notation "⊦ F" := (Seq F) (at level 100).

Definition seq_to_ctx  '( ⊦ Γ) :=  Γ.

Coercion seq_to_ctx : sequent >-> context.

Definition print_seq '(⊦ Γ) :=
  " ⊦ " ++ print_ctx Γ.

Instance bsubst_seq : BSubst sequent :=
 fun n u '(⊦ Γ ) => (⊦ (Γ[[ %n := u ]]) ).

Instance level_seq : Level sequent :=
 fun '(⊦ Γ ) => level Γ .

Instance seq_eqb : Eqb sequent :=
 fun '(⊦ Γ1) '(⊦ Γ2) => (Γ1 =? Γ2).

Definition ctx_example : context := [(µ((% 0)&(!#(% 0)))); (ν(µ((% 1)&(!#(% 0)))))].

(** Number of binders in a formula *)

Fixpoint FixBinders (f:formula) :=
  match f with
  | Quant _ G => S (FixBinders G)
  | Op _ F1 F2 => Nat.max (FixBinders F1) (FixBinders F2)
  | _ => 0
  end.

Inductive IndBinders: formula -> nat -> Prop :=
  | NulBot: IndBinders ⊥ 0
  | NulTop: IndBinders ⊤ 0
  | NulZero: IndBinders ø 0
  | NulOne: IndBinders ! 0
  | NulVar v: IndBinders (Var v) 0
  | CaseOp F1 F2 n1 n2 n o: IndBinders F1 n1 -> IndBinders F2 n2 
                                            -> n = Nat.max n1 n2 -> IndBinders (Op o F1 F2) n
  | Binding F q n: IndBinders F n -> IndBinders (Quant q F) (S n)
  .










(** META *)

Local Open Scope nat_scope.

(** EqbSpec *)

Instance : EqbSpec V.
Proof.
  red.
  fix IH 1. destruct x as [v|n], y as [v'|n']; cbn; try cons.
 - case eqbspec; cons.
 - case eqbspec; cons.
Qed.

Instance eqbspec_formula: EqbSpec formula.
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

(** Fsize *)

Lemma fsize_pos : forall (F:formula), 0 < fsize F.
Proof.
induction F ; simpl; intuition.
Qed.

(** Dual *)

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

Lemma op_dual : forall F1 F2 o, Op o F1 F2 <> dual (Op o F1 F2).
Proof.
  intros; destruct o; simpl; unfold not; intros; discriminate H.
Qed.

Lemma quant_dual : forall F q, Quant q F <> dual (Quant q F).
Proof.
  intros; destruct q; simpl; unfold not; intros; discriminate H.
Qed.

Lemma dual_var : forall F, F = dual F -> exists v, F = Var v.
Proof.
  destruct F; intros; try discriminate H. 
  - simpl in H; exists v; trivial.
  - destruct (op_dual F1 F2 o); assumption.
  - destruct (quant_dual F q); assumption.
Qed.

(** Level *)

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

Lemma level_op: forall n (F1 F2: formula) (o:op), form_level (Op o F1 F2) <= n 
                                                                                                    <->   
                                                                  (form_level F1 <= n ) /\ (form_level F2 <= n).
Proof.
  split; intros.
  - simpl in H. apply max_le in H; trivial.
  - simpl; apply max_le; trivial.
Qed.

Lemma level_quant: forall F q n, form_level (Quant q F) <= n -> form_level F <= S n.
Proof.
  intros; simpl in H; apply le_pred_S in H; assumption.
Qed.

Lemma level_quant_eq: forall F q n, form_level (Quant q F) = n -> form_level F <= S n.
Proof.
  intros. eapply level_quant. erewrite H. trivial.
Qed.

(** BSubst *)
Local Open Scope eqb_scope.

Lemma level_bsubst n (f g:formula) :
 level f <= S n -> level g <= n ->
 level (f[[ %n := g ]]) <= n.
Proof.
  revert n.
  induction f; intros; try destruct v; cbn; auto with arith.
  - destruct (n0 =? n) eqn:Heq.
    + assumption.
    + cbn in *. inversion H; subst.
       -- apply Utils.eqb_neq in Heq; destruct Heq; trivial.
       -- assumption.
  - cbn in H; simpl in H; apply max_le in H; destruct H; apply max_le; split.
    + apply IHf1; assumption.
    + apply IHf2; assumption.
  - unfold level in H; simpl in H. rewrite le_pred_S in H. apply IHf in H.
    + apply le_pred_S; assumption.
    + constructor; assumption.
Qed.

Lemma le_level_BSubst_unchanged : forall (G f: formula) n, 
  form_level G <= n -> G[[ %n := f ]] = G.
Proof.
  induction G; intros; try destruct v; try (inversion H0; reflexivity); cbn; simpl; trivial.
 - destruct (n0 =? n) eqn:Heq; try apply Utils.eqb_eq in Heq; subst; trivial; simpl in H; lia.
 -  apply max_le in H; destruct H;
    try (rewrite (IHG1 _ n));
    try (rewrite (IHG2 _ n)); try assumption;
    trivial.
- simpl in H;
  rewrite (IHG f (S n)); trivial; apply le_pred_S in H; assumption.
Qed.

Lemma le_level_BSubst : forall (G f:formula) k n1 n2, 
  form_level G <= n1 -> form_level f <= n2 -> form_level (G[[ %k := f ]]) <= Nat.max n1 n2.
Proof.
  induction G; intros; try destruct v; simpl; try apply le_0_n.
  - unfold bsubst; simpl. 
    destruct (le_max n1 n2).
    destruct (n =? k);
    eapply le_trans; try eassumption.
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

Lemma BClosed_bsubst: forall (F G: formula) k, 
  BClosed F -> F [[ %k := G ]] = F.
Proof.
  intros. apply (le_level_BSubst_unchanged F G _); rewrite H; apply le_0_n.
Qed.

Lemma BClosed_quant_bsubst : forall q (F G: formula),
  BClosed G -> BClosed (Quant q F) ->  BClosed (F[[ %0 := G ]]).
Proof.
  intros. unfold BClosed in *. assert (forall n, n <= 0 <-> n = 0). 
   { split; intros; subst; trivial; inversion H1; trivial. }
   apply H1; apply H1 in H0. 
   cbn in H0; apply le_pred_S in H0; apply level_bsubst; try assumption;
   rewrite H; trivial.
Qed.

Lemma switch_BSubst : forall (F G H:formula) a b, 
  BClosed G -> BClosed H -> a <> b -> ((F[[ %a := G ]]) [[ %b := H ]]) = ((F[[ %b := H ]]) [[ %a := G ]]).
Proof.
  induction F; try destruct v; unfold bsubst; simpl; intros; trivial.
  - destruct (n =? a) eqn:Heqa; destruct (n =? b) eqn:Heqb; 
    try rewrite Utils.eqb_eq in Heqa; try rewrite Utils.eqb_eq in Heqb.
    + subst; destruct H2; trivial.
    + subst; simpl; rewrite Utils.eqb_refl; apply BClosed_bsubst; trivial.
    + subst; simpl; rewrite Utils.eqb_refl; symmetry; apply BClosed_bsubst; trivial.
    + subst; simpl; rewrite Heqa, Heqb; trivial.
  - rewrite IHF1, IHF2; trivial.
  - rewrite IHF; intuition.
Qed.

Theorem bsubst_prop: forall P (f g:formula), 
  (forall k, P (f[[%k := g]]) ) -> P f.
Proof.
  intros. assert (f [[ % level f := g]] = f). { rewrite le_level_BSubst_unchanged; trivial. }
  rewrite <- H. apply X.
Qed. 

(** Boolean <-> Inductive *)


Theorem FixBinders_is_IndBinders: forall n f, 
  FixBinders f = n <-> IndBinders f n.
Proof.
  split; generalize dependent n; induction f; induction n; intros; 
  try (constructor); try (discriminate H); try (inversion H; reflexivity).
  - simpl in H; apply max_0 in H; destruct H; apply IHf1 in H; apply IHf2 in H0;
    econstructor; try eassumption; trivial.
 - simpl in H. inversion H. destruct (le_max (FixBinders f1) (FixBinders f2)); 
   apply max_eq in H. rewrite H1 in *. 
   apply (CaseOp f1 f2 (FixBinders f1) (FixBinders f2) (S n) o). 
   -- apply (IHf1 (FixBinders f1)); trivial.
   -- apply (IHf2 (FixBinders f2)); trivial.
   -- symmetry; assumption.
 - apply IHf; simpl in H; injection H as H; subst; trivial.
 - inversion H; subst. apply IHf1 in H3; apply IHf2 in H5.
   simpl; subst; symmetry; assumption.
- inversion H; subst; apply IHf1 in H3; apply IHf2 in H5; simpl; subst; symmetry; assumption.
- inversion H; subst; apply IHf in H1; simpl; subst; trivial.
Qed.








