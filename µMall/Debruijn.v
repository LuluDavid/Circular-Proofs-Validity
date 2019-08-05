Require Import Defs.
Require Import StringUtils.
Require DecimalString.
Import ListNotations.
Import Logic.
Local Open Scope bool_scope.
Local Open Scope lazy_bool_scope.
Local Open Scope string_scope.
Local Open Scope eqb_scope.

(** A 2nd order variable is defined as bound or free from the beginning *)

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

(* Formulas *)

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
Notation "°" := Zero.
Infix "⊕" := (Op Or_add) (at level 85, right associativity) : formula_scope.
Infix "#" := (Op Or_mult) (at level 85, right associativity) : formula_scope.
Infix "&" := (Op And_add) (at level 85, right associativity) : formula_scope.
Infix "⊗" := (Op And_mult) (at level 85, right associativity) : formula_scope.

Notation "@ V" := (Var (FVar V)) (at level 20) : formula_scope.
Notation "% n" := (Var (BVar n)) (at level 20) : formula_scope.

Notation "$ A" := (Quant µ A)
 (at level 200, right associativity) : formula_scope.
Notation "€ A" := (Quant ν A)
 (at level 200, right associativity) : formula_scope.

Definition Naturals:formula := ($ (!⊕(%0))).

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
| Quant µ G => Quant ν (dual G)
| Quant ν G => Quant µ (dual G)
end.

Notation "~ F" := (dual F) (at level 75, right associativity).

Lemma dual_inv (F : formula) : forall F, dual(dual F) = F.
Proof.
  intros. induction F0 as [ | | | |V|Op F1 IH1 F2 IH2|Quant F' IH]; intuition; try discriminate H.
  + destruct Op; simpl; rewrite IH1, IH2; trivial.
  + destruct Quant; simpl; rewrite IH; trivial.
Qed.

Definition NaturalsDual := dual Naturals.

(** Some generic functions, meant to be overloaded
    with instances for terms, formulas, context, sequent, ... 
    VMap and Check not necessary anymore because we 
    work here with 2nd order variables.
 **)

(** Replace a bound variable with a formula, useful for unfolding **)
Class BSubst (A : Type) := bsubst : nat -> formula -> A -> A.
Arguments bsubst {_} {_} _ _ !_.

(** Level : succ of max bounded variable *)
Class Level (A : Type) := level : A -> nat.
Arguments level {_} {_} !_.

(** Compute the set of free variables *)
Class FVars (A : Type) := fvars : A -> Names.t.
Arguments fvars {_} {_} !_.

(** Some generic definitions based on the previous ones *)

Definition BClosed {A}`{Level A} (a:A) := level a = 0.

Definition FClosed {A}`{FVars A} (a:A) := Names.Empty (fvars a).

Hint Unfold BClosed FClosed.

(** Substitution of a free variable in a variable :
    in [V], free var [X] is replaced by [U]. *)

Definition varsubst (V U X:V) := if (V =? X)%V then U else X.

 
(** Some structural extensions of these generic functions *)

Instance bsubst_list {A}`{BSubst A} : BSubst (list A) :=
 fun n t => List.map (bsubst n t).

Instance level_list {A}`{Level A} : Level (list A) :=
 fun l => list_max (List.map level l).

Instance fvars_list {A}`{FVars A} : FVars (list A) :=
 Names.unionmap fvars.
 
Instance bsubst_pair {A B}`{BSubst A}`{BSubst B} : BSubst (A*B) :=
 fun n t '(a,b) => (bsubst n t a, bsubst n t b).

Instance level_pair {A B}`{Level A}`{Level B} : Level (A*B) :=
 fun '(a,b) => Nat.max (level a) (level b).

Instance fvars_pair {A B}`{FVars A}`{FVars B} : FVars (A*B) :=
 fun '(a,b) => Names.union (fvars a) (fvars b).

 
(** With respect to a particular signature, a term is valid
    iff it only refer to known function symbols and use them
    with the correct arity. *)

Instance V_fvars : FVars V :=
 fix term_fvars v :=
 match v with
 | BVar _ => Names.empty
 | FVar v' => Names.singleton v'
 end.

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
  | (% n)%form => "%" (* Eventuellement paramétrer avec n si possible *)
  | (@ V)%form => V
  | Op o f f' =>
    "{" ++ print_formula f ++ "}" ++ pr_op o ++ "{" ++ print_formula f' ++ "}"
  | Quant q f => pr_quant q ++ "{" ++ print_formula f ++ "}"
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

Compute form_level ($((% 1)&(!#(% 1))))%form.

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

Compute form_bsubst 0 (@ "A")%form ($((% 1)&(!#(% 1))))%form.

Definition F: formula := ! # (% 0).
Definition G:formula := bsubst 0 ($ F)%form F.
Compute F.
Compute G.

(*
   F[X/µX.F] avec F = 1 # X => F' = 1 + µX.(1 # X)
*)

Instance form_fvars : FVars formula :=
 fix form_fvars f :=
  match f with
  | Top | Bot | One | Zero => Names.empty
  | Var V =>  match V with
                                    | FVar X => Names.singleton X
                                    | BVar _ => Names.empty
                                    end
  | Op _ f1 f2 => Names.union (form_fvars f1) (form_fvars f2)
  | Quant _ f' => form_fvars f'
  end.
  
   
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
Compute    ($((% 0)&(!#(% 0))))%form 
                                   =?
                   ($((@ "V")&(!#(@ "V"))))%form.
(** Contexts *)

Definition context := list formula.
  
Definition print_ctx Γ :=
  String.concat ", " (List.map print_formula Γ).

(** check, bsubst, level, fvars, eqb : given by instances
    on lists. *)

(** Sequent *)

Inductive sequent :=
| Seq : context -> sequent.

Notation "⊦ F" := (Seq F) (at level 100).

Definition print_seq '(⊦ Γ) :=
  " ⊦ " ++ print_ctx Γ.

Instance bsubst_seq : BSubst sequent :=
 fun n u '(⊦ Γ ) => (⊦ (bsubst n u Γ) ).

Instance level_seq : Level sequent :=
 fun '(⊦ Γ ) => level Γ .

Instance seq_fvars : FVars sequent :=
 fun '(⊦ Γ ) => fvars Γ.

Instance seq_eqb : Eqb sequent :=
 fun '(⊦ Γ1) '(⊦ Γ2) => (Γ1 =? Γ2).

Definition ctx_example := [($((% 0)&(!#(% 0))))%form; (€($((% 2)&(!#(% 1)))))%form].

Compute level ctx_example.

(** Derivation *)

Inductive rule_kind :=
  | Ax
  | Cut
  | Ex
  | Or_add_l | Or_add_r
  | Or_mult
  | And_add
  | And_mult
  | TopR| BotR| OneR
  | Mu | Nu
  | BackEdge (S:sequent)
  .

Definition print_rule (r:rule_kind) :=
  match r with
  | Ax => "(Ax)"
  | Cut => "(Cut)"
  | Ex => "(Ex)"
  | TopR => "(⊤)"
  | BotR => "(⊥)"
  | OneR => "(1)"
  | Or_add_l => "(⊕_l)"
  | Or_add_r => "(⊕_r)"
  | Or_mult => "(#)"
  | And_add => "(&)"
  | And_mult => "(⊗)"
  | Mu => "(µ)"
  | Nu => "(ν)"
  | BackEdge s => "(BackEdge"++print_seq s++")"
  end.
  
Instance rule_eqb : Eqb rule_kind :=
 fix rule_eqb r1 r2 :=
  match r1, r2 with
  | Ax, Ax | Cut, Cut | Ex, Ex | TopR, TopR | BotR, BotR | OneR, OneR | Mu, Mu | Nu, Nu
  | Or_add_l, Or_add_l | Or_add_r, Or_add_r | Or_mult, Or_mult | And_add, And_add | And_mult, And_mult => true
  | BackEdge Se, BackEdge Se' => Se=?Se'
  | _, _ => false
 end.
  
Inductive derivation :=
  | Rule : list sequent -> rule_kind -> sequent -> list derivation -> derivation.

(** Returns the current sequent/bottom sequent *)

Definition claim '(Rule _ _ s _) := s.

(** Utility functions on derivations:
    - bounded-vars level (used by the [BClosed] predicate),
    - check w.r.t. signature *)

Instance level_derivation : Level derivation :=
 fix level_derivation d :=
  let '(Rule ls r s ds) := d in
  list_max (level s :: List.map level_derivation ds).

Instance fvars_derivation : FVars derivation :=
 fix fvars_derivation d :=
  let '(Rule ls r s ds) := d in
  Names.unions [fvars s; Names.unionmap fvars_derivation ds].

Instance bsubst_deriv : BSubst derivation :=
 fix bsubst_deriv n u d :=
 let '(Rule ls r s ds) := d in
 Rule ls r (bsubst n u s ) (map (bsubst_deriv n u) ds).

(* A Fixpoint for validity. Complicated to describe the exchange rule because we require a boolean  
  permutation indicator for two lists. *)

Fixpoint Inb (s : sequent) (l : list sequent) : bool :=
    match l with
       | [] => false
       | s' :: m => (s' =? s) || (Inb s m)
     end.

Fixpoint Inb' (s : formula) (l : context) : bool :=
    match l with
       | [] => false
       | s' :: m => (s' =? s) || (Inb' s m)
     end.

Notation "[ x ; y ; .. ; z ]" := (cons x (cons y .. (cons z nil) ..)) : list_scope.

Inductive CPermutation {A} : list A -> list A -> Prop :=
| cperm : forall l1 l2, CPermutation (l1 ++ l2) (l2 ++ l1).

Definition valid_deriv_step '(Rule ls r s ld) :=
  match ls, r, s, List.map claim ld with
  | _, Ax,    (⊦ [A;A']), _ => (A' =? (dual A))
  | _, TopR,  (⊦ ⊤::Γ ), _ => true 
  | _, OneR,  (⊦ [!]), _ => true
  | _, BotR,  (⊦ ⊥::Γ), [s] => s =? (⊦ Γ)
  | _, Or_add_l, (⊦ (F⊕G)%form::Γ), [s] => s =? (⊦ F::Γ)
  |  _, Or_add_r, (⊦ (F⊕G)%form::Γ), [s] => s =? (⊦ G::Γ)
  | _, Or_mult,  (⊦ (F#G)%form::Γ), [s] => s =? (⊦F::G::Γ)
  | _, And_add,  (⊦ (F&G)%form::Γ), [(⊦ F'::Γ1);(⊦ G'::Γ2)] => (F =? F') &&& (G =? G') &&& (Γ1 =? Γ) &&& (Γ2 =? Γ)
  | _, And_mult,  (⊦ (F⊗G)%form::Γ), [(⊦ F'::Γ1);(⊦ G'::Γ2)] => (F =? F') &&& (G =? G') &&& ((app Γ1 Γ2) =? Γ)
  | _, Cut,   (⊦ [A1;A2]), [(⊦ [B1;C1]);(⊦ [B2;C2])] => (A1 =? C1) &&& (A2 =? C2) &&& (B1 =? (dual B2))
  | _, Ex,  (⊦ Γ), [(⊦F::Γ')] => (Inb' F Γ) (* &&& list_equivb Γ (F::Γ') *)
  (* To be precised: exists i such as insert F at ith position in Γ' = Γ *)
  | _, Mu, (⊦ ($ F)%form::Γ), [(⊦G::Γ')] => (G =? bsubst 0 ($ F) F) &&& (Γ =? Γ')
  | _, Nu, (⊦ (€ F)%form::Γ), [(⊦G::Γ')] => (G =? bsubst 0 (€ F) F) &&& (Γ =? Γ')
  | ls, (BackEdge s'), s, _ => (Inb s' ls) &&& (s' =? s)
  | _,_,_,_ => false
  end.

Fixpoint valid_deriv d :=
  valid_deriv_step d &&&
   (let '(Rule _ _ _ ld) := d in
    List.forallb (valid_deriv) ld).

Definition deriv_example :=
  Rule [] Or_mult (⊦[((@ "A")#(dual (@ "A")))%form]) [Rule [] Ax (⊦[(@ "A")%form;dual (@ "A")%form]) []].
 Print deriv_example.
Compute 
  bsubst_deriv 0 (@ "B")%form deriv_example.
  
  
 (*
  ----------------------------------------------------- (Ax)
                      [] ⊦@A,¬@A 
  ----------------------------------------------------- (#)
                      [] ⊦@A#¬@A
  *)
  
Compute valid_deriv deriv_example.
(** Some examples of derivations *)

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

(** Induction principle on derivations with correct
    handling of sub-derivation lists. *)

Lemma derivation_ind' (P: derivation -> Prop) :
  (forall ls r s ds, Forall P ds -> P (Rule ls r s ds)) ->
  forall d, P d.
Proof.
 intros Step.
 fix IH 1. destruct d as (ls,r,s,ds).
 apply Step.
 revert ds.
 fix IH' 1. destruct ds; simpl; constructor.
 apply IH.
 apply IH'.
Qed.

(** 
Claim d s => d's conclusion sequent is s. It means:

                                                                                                 .
                                                                                                 .
                                                                                                 .
                                                                                                d
                                                                                          -------------
                                                                                                s
 *)

Definition Claim d s := claim d = s.
Arguments Claim _ _ /.
Hint Extern 1 (Claim _ _) => cbn.

(* Adds the sequent s in the list of back-edgeable sequents of derivation d *)
Definition app_deriv (s:sequent) (d:derivation) := 
  let '(Rule ls r s ds) := d in (Rule (s::ls) r s ds).

(** An inductive Prop Valid, easier to describe all expected patterns *)

Inductive Valid : derivation -> Prop :=
 | V_Ax Γ A ls : In A Γ -> In (dual A) Γ -> Valid (Rule ls Ax (⊦ Γ) [])
 | V_Tr Γ ls: In ⊤ Γ -> Valid (Rule ls TopR (⊦ Γ) [])
 | V_One ls: Valid (Rule ls OneR (⊦ [!%form]) [])
 | V_Bot d Γ ls: Valid d -> Claim d (⊦Γ) -> Valid (Rule ls BotR (⊦⊥::Γ) [d])
 | V_Or_add_l d F G Γ ls: 
   Valid d -> Claim d (⊦F::Γ) -> Valid (Rule ls Or_add_l (⊦(F⊕G)%form::Γ) [d])
 | V_Or_add_r d F G Γ ls  : 
   Valid d -> Claim d (⊦G::Γ) -> Valid (Rule ls Or_add_r (⊦(F⊕G)%form::Γ) [d])
 | V_Or_mult d F G Γ ls :
     Valid d -> Claim d (⊦F::G::Γ) -> Valid (Rule ls Or_mult (⊦ (F#G)%form::Γ) [d])
 | V_And_add d1 d2 F G Γ ls :
     Valid d1 -> Valid d2 -> Claim d1 (⊦ F::Γ) -> Claim d2 (⊦ G::Γ) ->
     Valid (Rule ls And_add (⊦ (F&G)%form::Γ) [d1;d2])
 | V_And_mult d1 d2 F G Γ1 Γ2 ls :
     Valid d1 -> Valid d2 -> Claim d1 (⊦ F::Γ1) -> Claim d2 (⊦ G::Γ2) ->
     Valid (Rule ls And_mult (⊦ (F⊗G)%form::(app Γ1 Γ2)) [d1;d2])
 | V_Cut d1 d2 A Γ1 Γ2 ls :
     Valid d1 -> Valid d2 -> Claim d1 (⊦ (dual A)::Γ1) -> Claim d2 (⊦ A::Γ2) ->
     Valid (Rule ls Cut (⊦app Γ1 Γ2) [d1;d2])
     
     
 | V_Ex d F G Γ1 Γ2 ls :
      Valid d -> Claim d (⊦ app Γ1 (G::F::Γ2)) -> Valid (Rule ls Ex (⊦app Γ1 (F::G::Γ2)) [d])
      
      
 | V_Mu d F Γ ls :
      Valid d -> Claim d (⊦ (bsubst 0 ($ F)%form F)::Γ) -> Valid (Rule ls Mu (⊦ ($ F)%form::Γ) [d])
      
      
 | V_Nu d F Γ ls :
      Valid d -> Claim d (⊦ (bsubst 0 (€ F)%form F)::Γ) -> Valid (Rule ls Nu (⊦ (€ F)%form::Γ) [d])
      
      
 | V_BackEdge ls s : In s ls -> Valid (Rule ls (BackEdge s) s []) 
 
 | V_Keep s ls R ld: Valid (Rule ls R s ld) -> Valid (Rule ls R s (map (app_deriv s) ld)) 
 (* For all upper derivations, it is ok to add the current sequent in their back-edgeable sequents list *)
 .

Definition deriv_example' :=
Rule [] Nu (⊦ [(€ (%0)⊕(%0))%form]) 
          [
          (
          Rule [(⊦ [(€ (%0)⊕(%0))%form])] Or_add_l (⊦ [ ((€ (%0)⊕(%0)) ⊕ (€ (%0)⊕(%0)))%form ] )
            [
            (
            Rule [⊦ [(€ (%0)⊕(%0))%form]] (BackEdge (⊦ [(€ (%0)⊕(%0))%form])) (⊦ [(€ (%0)⊕(%0))%form]) []
            )
            ] 
          ) 
          ].
  (*
    ----------------------------------------------------- (BackEdge (⊦vX. X⊕X))
     [(⊦vX. X⊕X)] ⊦ (vX.X⊕X)
    ----------------------------------------------------- (⊕l)
     [(⊦vX. X⊕X)] ⊦ (vX.X⊕X) ⊕ (vX.X⊕X) 
    ----------------------------------------------------- (v)
                        [] ⊦vX. X⊕X
    *)
Compute level deriv_example'.

Theorem thm_example: 
  Valid (deriv_example').
Proof.
  repeat constructor.
Qed.

Definition context_example := [(€ (%0)⊕(%0))%form; ($ (%1)#(%0))%form].
Compute (print_ctx context_example).

Definition sequent_example := Seq context_example.
Compute (print_seq sequent_example).

Fixpoint print_list_seq (ls:list sequent) :=
  match ls with
  | [] => ""
  | s::ls => (print_seq s)
  end.

Fixpoint print_deriv_list (d:derivation): list string :=
  let '(Rule ls r s ds) := d in
  concat (map print_deriv_list ds) ++ 
  [string_mult "-" (String.length (print_list_seq ls ++ print_seq s)) ++ print_rule r; 
  print_list_seq ls ++ print_seq s].

Compute print_deriv_list deriv_example'.
(** Let's prove now that [valid_deriv] is equivalent to [Valid] *)
Hint Constructors Valid.

Ltac break :=
 match goal with
 | H : match _ with true => _ | false => _ end = true |- _ =>
   rewrite !lazy_andb_iff in H
 | H : match claim ?x with _ => _ end = true |- _ =>
   destruct x; simpl in H; try easy; break
 | H : match map _ ?x with _ => _ end = true |- _ =>
   destruct x; simpl in H; try easy; break
 | H : match ?x with _ => _ end = true |- _ =>
   destruct x; simpl in H; try easy; break
 | _ => idtac
 end.

Ltac rewr :=
 unfold Claim, BClosed in *;
 match goal with
 | H: _ = _ |- _ => rewrite H in *; clear H; rewr
 | _ => rewrite ?eqb_refl
 end.

(* Sequent provable if it is the conclusion of an existing Valid derivation *)

Definition Provable (s : sequent) :=
  exists d, Valid d /\ Claim d s.

(* Provability on sequent without any list of sequents, rule and list of premisses
  => provability without back-edges.
*)

Inductive Pr : sequent -> Prop :=
 | R_Ax Γ A : In A Γ -> In (dual A) Γ -> Pr (⊦ Γ)
 | R_Top Γ : In ⊤ Γ -> Pr (⊦ Γ)
 | R_Bot Γ : Pr (⊦ Γ) ->
                  Pr (⊦ ⊥::Γ)
 | R_One : Pr (⊦ [!%form])
 | R_Or_add_l Γ F G : Pr (⊦ F::Γ) -> Pr (⊦ (F⊕G)%form::Γ)
 | R_Or_add_r Γ F G : Pr (⊦ G::Γ) -> Pr (⊦ (F⊕G)%form::Γ)
 | R_Or_mult Γ F G : Pr (⊦ F::G::Γ) -> Pr (⊦ (F#G)%form::Γ)
 | R_And_add Γ F G : Pr (⊦ F::Γ) -> Pr (⊦ G::Γ) -> Pr (⊦ (F&G)%form::Γ)
 | R_And_mult Γ1 Γ2 F G : Pr (⊦ F::Γ1) -> Pr (⊦ G::Γ2) -> Pr (⊦ (F⊗G)%form::(app Γ1 Γ2))
 | R_Cut A Γ1 Γ2 : Pr (⊦ (dual A)::Γ1) -> Pr (⊦ A::Γ2) -> Pr (⊦ app Γ1 Γ2)
 | R_Ex F G Γ1 Γ2 : Pr (⊦ app Γ1 (F::G::Γ2)) -> Pr (⊦ app Γ1 (G::F::Γ2))
 | R_Mu F Γ :
      Pr (⊦ (bsubst 0 ($ F)%form F)::Γ) -> Pr ((⊦ ($ F)%form::Γ))
 | R_Nu F Γ :
      Pr (⊦ (bsubst 0 (€ F)%form F)::Γ) -> Pr ((⊦ (€ F)%form::Γ))
  .
Hint Constructors Pr.

Theorem thm_example_bis:
  Pr (⊦[((@ "A")#(dual (@ "A")))%form]).
Proof.
  apply R_Or_mult. apply (R_Ax [(@ "A")%form; ~ @ "A"] (@ "A")%form).
  - simpl; left; trivial.
  - simpl; right; left; trivial.
Qed.

(* Not necessary to define alpha-equivalence for a Debruyne representation, as variables are not named anymore 
    => no deb_rec, no alpha_eq
    => useful to code appear_in/appear_in_b ?
*)