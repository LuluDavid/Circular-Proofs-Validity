Require Export StringUtils Defs Lia.
Import ListNotations Ascii.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope string_scope.
Local Open Scope eqb_scope.

(** DEFINITIONS *)

(** Variables *)

Definition Atom := nat.

(** Formulas *)

Inductive formula :=
| Top
| Bot
| One
| Zero
| Var: Atom -> formula
| Op : op -> formula -> formula -> formula
| Quant : quant -> Atom -> formula -> formula.


Fixpoint fsize (F : formula) := match F with
| Var _ => 1
| Zero | One | Top | Bot => 1
| Op _ G H => S ((fsize G) + (fsize H))
| Quant _ _ G => S (fsize G)
end.

Declare Scope formula_scope.

Notation "⊥" := Bot : formula_scope.
Notation "⊤" := Top : formula_scope.
Notation "!" := One : formula_scope.
Notation "'ø'" := Zero : formula_scope.
Infix "⊕" := (Op Or_add) (at level 85, right associativity) : formula_scope.
Infix "#" := (Op Or_mult) (at level 85, right associativity) : formula_scope.
Infix "&" := (Op And_add) (at level 85, right associativity) : formula_scope.
Infix "⊗" := (Op And_mult) (at level 85, right associativity) : formula_scope.

Notation "% n" := (Var n) (at level 20) : formula_scope.

Notation "'µ'" := (Quant mu) (at level 200) : formula_scope.

Notation "'ν'" := (Quant nu) (at level 200) : formula_scope.

Local Open Scope formula_scope.
Definition test := µ O Bot.

(** Neutral [formula] *)

Definition neutral (f:formula) : Prop := In f [ ⊥ ; ⊤ ; ! ; ø ].

(** Atomic [formula] *)
Inductive atomic : formula -> Prop :=
| atomic_var : forall x, atomic (Var x).

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
| Quant mu X G => Quant nu X (dual G)
| Quant nu X G => Quant mu X (dual G)
end.

Notation "~ F" := (dual F) (at level 75, right associativity).





(** Some generic functions, meant to be overloaded
    with instances for variables, formulas, context, sequent, ... **)

(** Replace a bound variable with a formula, useful for unfolding **)
Class BSubst (A : Type) := bsubst : Atom -> formula -> A -> A.
Arguments bsubst {_} {_} _ _ !_.

(** Level : succ of max bounded variable *)
Class Level (A : Type) := level : A -> nat.
Arguments level {_} {_} !_.

(** Some generic definitions based on the previous ones *)

Definition BClosed {A}`{Level A} (a:A) := level a = 0.

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


Fixpoint print_formula (f:formula) :=
  match f with
  | Bot => "⊥"
  | Top => "⊤"
  | One => "1"
  | Zero => "0"
  | % n => "%" ++ (String (ascii_of_nat (48 + n)) "")
  | Op o f f' =>
    "{ " ++ print_formula f ++ " }" ++ pr_op o ++ "{ " ++ print_formula f' ++ " }"
  | Quant q n f => pr_quant q ++ "%" ++ (String (ascii_of_nat (48 + n)) "") ++ "{ " ++ print_formula f ++ " }"
  end.

(** Formula Instances *)

(** A formula level is the maximum number of missings binders for a binded variable.
    It means that for a formula F, you need at least level F binders to close the formula. *)

Fixpoint form_level_rec(f:formula)(l:@list nat) :=
  match f with
  | Top | Bot | One | Zero => 0
  | Var n  => if list_mem n l then 0 else 1
  | Op _ f1 f2 => Nat.max (form_level_rec f1 l) (form_level_rec f2 l)
  | Quant _ n f' => form_level_rec f' (n::l)
  end.

Instance form_level : Level formula := fun f => form_level_rec f [].

Compute form_level (µ 0 ((% 0)&(!#(% 0)))).
Compute form_level (µ 1 ((% 0)&(!#(% 0)))).

(** Important note : [bsubst] below is only intended to be
    used with a replacement formula [f] which is closed *)

Instance form_bsubst : BSubst formula :=
 fix form_bsubst n F f :=
 match f with
  | Top | Bot | One | Zero  => f
  | Var m =>  if (n =? m) then F else f
  | Op o f1 f2 => Op o (form_bsubst n F f1) (form_bsubst n F f2)
  | Quant q m f' => Quant q m (form_bsubst n F f')
 end.

Definition example1: formula := µ 0 (%0 # (ν 1 (%0 & %1))).
Definition example2:formula := example1[[ %0 := Bot ]].
Compute example2.

Instance form_eqb : Eqb formula :=
 fix form_eqb f1 f2 :=
  match f1, f2 with
  | Top, Top | Bot, Bot | One, One | Zero, Zero=> true
  | Var X, Var Y => X =? Y
  | Op o1 f1 f1', Op o2 f2 f2' =>
    (o1 =? o2) &&&
    form_eqb f1 f2 &&&
    form_eqb f1' f2'
  | Quant n1 q1 f1', Quant n2 q2 f2' =>
    (n1 =? n2) &&& (q1 =? q2) &&& form_eqb f1' f2'
  | _,_ => false
  end.

(* We could say they are equivalent, but is it the goal of eqb ? *)

Compute µ 0 ((% 0)&(!#(% 0))) =? µ 1 ((% 1)&(!#(% 1))).



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

Definition ctx_example : context := [(µ 0 ((% 0)&(!#(% 0)))); (ν 0 (µ 1 ((% 1)&(!#(% 0)))))].










(** META *)

Local Open Scope nat_scope.

(** EqbSpec *)

Instance eqbspec_formula: EqbSpec formula.
Proof.
  red.
  fix IH 1. induction x as [ | | | |V|Op F1 IH1 F2 IH2|Quant n F IH']; destruct y eqn: Hy; 
  cbn; try cons; try (case eqbspec; cons).
  - case eqbspec; [ intros <- | cons ]. case IH1; try cons. case IH2; try cons.
  - case eqbspec; [ intros <- | cons ].
    case IH'; intros; case eqbspec; try cons; intros; cons.
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
  intros. induction F as [ | | | |V|Op F1 IH1 F2 IH2|Quant n F' IH]; intuition; try discriminate H.
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

Lemma quant_dual : forall F q n, Quant q n F <> dual (Quant q n F).
Proof.
  intros; destruct q; simpl; unfold not; intros; discriminate H.
Qed.

Lemma dual_var : forall F, F = dual F -> exists v, F = Var v.
Proof.
  destruct F; intros; try discriminate H. 
  - exists a; trivial.
  - destruct (op_dual F1 F2 o); assumption.
  - destruct (quant_dual F q a); assumption.
Qed.

(** Level *)

Lemma BClosed_op: forall (F1 F2: formula) (o:op), BClosed (Op o F1 F2) <-> (BClosed F1) /\ (BClosed F2).
Proof.
  intros. split; intro. unfold BClosed in H; unfold level in H; simpl in H.
  assert (Hloc: forall n m, Nat.max n m = 0 -> n = 0 /\ m = 0).
  { intros; generalize dependent m; induction n; induction m; intros; split; trivial;
    try (discriminate H0).
   }
   apply Hloc in H; destruct H; split; assumption.
   destruct H. unfold BClosed, level, form_level; simpl.
   rewrite H, H0; trivial.
Qed.

(** BSubst *)

Local Open Scope eqb_scope.

Lemma level_bsubst_swap : forall F a b l1 l2,
  form_level_rec F (l1++a::b::l2) = form_level_rec F (l1++b::a::l2).
Proof.
  induction F; simpl; trivial.
  {
  induction l1; simpl.
    { destruct (a =? a0); destruct (a =? b); trivial. }
    { destruct (a =? a1); trivial. }
  }
  {
  intros.
  rewrite IHF1, IHF2; trivial.
  }
  {
  intros.
  apply (IHF a0 b (a :: l1) l2).
  }
Qed.

Local Open Scope list_scope.

Lemma level_bsubst_swap_head :  forall F h l1 l2,
  form_level_rec F (h::l1++l2) = form_level_rec F (l1++h::l2).
Proof.
  intros. revert l2 h.
  induction l1 using rev_ind; intros; simpl; trivial.
  rewrite <- app_assoc, <- app_assoc.
  rewrite IHl1.
  apply level_bsubst_swap.
Qed.

Lemma level_bsubst_cons : forall F l1 l2,
  form_level_rec F l1 = 0 -> form_level_rec F (l2 ++ l1) = 0.
Proof.
  induction F; simpl; trivial.
  {
  intros.
  destruct (list_mem a l1) eqn:Heq1;
  destruct (list_mem a (l2 ++ l1)) eqn:Heq2; trivial.
  apply list_mem_in in Heq1.
  assert (In a (l2 ++ l1)).
  apply in_or_app; right; trivial.
  apply list_mem_in in H0.
  rewrite Heq2 in H0; discriminate H0.
  }
  {
  intros. apply max_0 in H; destruct H;
  rewrite IHF1, IHF2; trivial.
  }
  {
  intros.
  destruct (IHF (a::l1) l2); trivial.
  apply level_bsubst_swap_head.
  }
Qed.

Lemma level_bsubst_lemma : forall F G n q l,
  form_level_rec (Quant q n F) l = 0 -> form_level_rec G l = 0 
  -> form_level_rec (F[[ %n := G ]]) l = 0.
Proof.
  intros F G n q.
  induction F; intros; trivial.
  {
  unfold bsubst; simpl; destruct (n =? a) eqn:Heq; trivial.
  unfold level, form_level in H; simpl in H;
  rewrite Utils.eqb_sym in H; rewrite Heq in H.
  trivial.
  }
  {
  unfold BClosed, level, form_level in H; simpl in H.
  apply max_0 in H; destruct H; apply max_0; 
  split; [apply IHF1|apply IHF2]; trivial.
  }
  {
  unfold BClosed, level, form_level in H; simpl in H.
  apply IHF.
  {
  simpl; rewrite <- (app_nil_l (n::a::l)), <- H.
  apply (level_bsubst_swap F n a [] l).
  }
  {
  apply (level_bsubst_cons G l [a]) in H0. apply H0.
  }
  }
Qed.

Lemma level_bsubst n q (F G:formula) :
 BClosed (Quant q n F) -> BClosed G -> BClosed (F[[ %n := G ]]).
Proof.
  intros.
  unfold BClosed, level, form_level.
  apply (level_bsubst_lemma _ _ _ q []); trivial.
Qed.








