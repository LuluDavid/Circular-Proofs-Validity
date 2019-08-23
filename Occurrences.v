Require Export Defs Debruijn Address StringUtils Utils Ascii.
Require DecimalString.
Import ListNotations.
Require Import Arith.
Import Bool.
Local Open Scope string_scope.
Local Open Scope eqb_scope.


(** DEFINING OCCURRENCES **)
  

Inductive Occurrence :=
  | Occ (F:formula)(a:address).
 
Notation "{ F , A }" := (Occ F A).

Class OBSubst (A : Type) := obsubst : nat -> Occurrence -> A -> A.
Arguments obsubst {_} {_} _ _ !_.
Hint Extern 1 (OBSubst _ _ _) => cbn.

Instance obsubst_list {A}`{OBSubst A} : OBSubst (list A) :=
 fun n t => List.map (obsubst n t).

Instance obsubst_pair {A B}`{OBSubst A}`{OBSubst B} : OBSubst (A*B) :=
 fun n t '(a,b) => (obsubst n t a, obsubst n t b).

Definition print_occurrence (o:Occurrence) :=
  let '(Occ F a) := o in ("{ " ++ print_formula F ++ ", " ++ print_address a ++ " }").

Local Open Scope eqb_scope.

(* Redefining eqb, level, bsubst. 
    bsubst is not anymore instance because we substitute occurrences in occurrences here *)

Instance occ_eqb : Eqb Occurrence :=
 fix occ_eqb o o' :=
  let '{ F, A} := o in (let '{ G, B} := o' in (F =? G) && (A =? B)).
  
Instance occ_level : Level Occurrence :=
  fix occ_level o := let '{ F, A} := o in level F.

Instance occ_bsubst: BSubst Occurrence :=
  fix occ_obsubst n f o := 
  let '{ F, A} := o in ({  F[[ %n := f ]], A }).
  
Instance occ_obsubst: OBSubst Occurrence :=
  fix occ_obsubst n o' o := 
  let '{ F, A} := o in (let '{ G, B} := o in {  F[[ %n := G ]], A }).

Instance: EqbSpec Occurrence.
Proof.
  red. destruct x; destruct y. cbn; case eqbspec; try cons.
  intros; subst. case eqbspec; try cons.
Qed.



(** DEFINING THE DUAL OF AN OCCURRENCE **)

Fixpoint occ_dual (o:Occurrence): Occurrence :=
  let '(Occ F a) := o in
  { (dual F), (addr_dual a)}.

Lemma occ_dual_inv: forall o, occ_dual (occ_dual o) = o.
Proof.
  intros; destruct o; simpl; rewrite dual_inv, addr_dual_inj; trivial.
Qed.

Definition occ_forget (o:Occurrence): formula :=
  let '{ F, A} := o in F.
  
Definition occ_addr (o:Occurrence): address :=
  let '{ F, A} := o in A.

Definition equiv (F G:Occurrence) : Prop := 
  occ_forget F = occ_forget G.

Definition equivb (F G:Occurrence) : bool := 
  occ_forget F =? occ_forget G.

Lemma equiv_is_equivb: forall (F G:Occurrence), equiv F G <-> equivb F G = true.
Proof.
intros; split; intros; destruct F; destruct G; cbn.
- try rewrite Utils.eqb_eq. unfold equiv in H; simpl in H; assumption.
- unfold equivb in H; unfold equiv; simpl; simpl in H; apply Utils.eqb_eq in H; assumption.
Qed.

Notation "F == G" := (equiv F G) (at level 100). 

Lemma equiv_refl: Reflexive equiv.
Proof.
  intuition.
Qed.

Lemma equiv_sym: Symmetric equiv.
Proof.
  red; unfold equiv; destruct x; destruct y; simpl; intros; subst; trivial.
Qed.

Lemma equiv_trans: Transitive equiv.
Proof.
  red; unfold equiv; destruct x; destruct y; destruct z; simpl; intros; subst; trivial.
Qed.

Instance: Equivalence equiv.
Proof.
  split; try apply equiv_refl; try apply equiv_sym; try apply equiv_trans.
Qed.

Definition disjoint_set_occ (l1 l2: list Occurrence) : Prop := forall (o1 o2: Occurrence),
  In o1 l1 -> In o2 l2 -> disjoint (occ_addr o1)(occ_addr o2).


(** ADAPTATION OF DERIVATIONS FOR OCCURRENCES **)

Definition ocontext := list Occurrence.
  
Definition print_octx Γ :=
  String.concat ", " (List.map print_occurrence Γ).

Instance: EqbSpec ocontext.
Proof.
  apply eqbspec_list.
Qed.
(** Sequent *)

Fixpoint ocontext_forget Γ : list formula := map occ_forget Γ.

Fixpoint ocontext_addr Γ : list address := map occ_addr Γ.

Inductive osequent :=
| SeqO : ocontext -> osequent.

Notation "⊢ Γ" := (SeqO Γ) (at level 100).

Fixpoint oseq_forget (s:osequent): sequent := let '(⊢ Γ) := s in (⊦ (ocontext_forget Γ)).

Fixpoint oseq_addr (s:osequent): list address := let '(⊢ Γ) := s in ocontext_addr Γ.


Local Open Scope string_scope.

Definition print_oseq '(⊢ Γ) :=
  " ⊢ " ++ print_octx Γ.

Instance oseq_level : Level osequent :=
 fun '(⊢ Γ ) => level Γ.
 
Instance bsubst_seq : BSubst osequent :=
 fun n u '(⊢ Γ ) => (⊢ (Γ[[ %n := u ]]) ).

Instance obsubst_seq : OBSubst osequent :=
 fun n o '(⊢ Γ ) => (⊢ (obsubst n o Γ) ).

Local Open Scope eqb_scope.

Instance oseq_eqb : Eqb osequent :=
 fun '(⊢ Γ1) '(⊢ Γ2) => (Γ1 =? Γ2).
 
Instance: EqbSpec osequent.
Proof.
  intros [] []. cbn. repeat (case eqbspec; try cons).
Qed.

(* A prop asserting that 2 sequents have the same formulas in the same order *)

Definition oseq_equiv (s1 s2: osequent) : Prop := (oseq_forget s1) = (oseq_forget s2).
  
Definition oseq_equivb (s1 s2: osequent) : bool := (oseq_forget s1) =? (oseq_forget s2).

Lemma oseq_equiv_is_oseq_equivb: forall (s1 s2: osequent), 
  oseq_equiv s1 s2 <-> oseq_equivb s1 s2 = true.
Proof.
  split;
  unfold oseq_equiv, oseq_equivb;
  apply Utils.eqb_eq.
Qed.

Definition octx_example := [{ (µ((% 0)&(!#(% 0)))), [i;l;r] };{ (ν(µ((% 1)&(!#(% 0))))), [] }].

Compute level ctx_example.

(** Derivation: circular approach **)

Inductive orule_kind :=
  | Ax
  | Cut
  | Ex
  | Or_add_l | Or_add_r
  | Or_mult
  | And_add
  | And_mult
  | TopR| BotR| OneR
  | Mu | Nu
  | BackEdge (n:nat)
  .

Definition print_orule (r:orule_kind) :=
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
  | BackEdge n => "(BackEdge " ++ (String (ascii_of_nat (48 + n)) "") ++ ")" 
    (* Only works for numbers between 0 and 9 *)
  end.

Instance orule_eqb : Eqb orule_kind :=
 fix orule_eqb r1 r2 :=
  match r1, r2 with
  | Ax, Ax | Cut, Cut | Ex, Ex | TopR, TopR | BotR, BotR | OneR, OneR | Mu, Mu | Nu, Nu
  | Or_add_l, Or_add_l | Or_add_r, Or_add_r | Or_mult, Or_mult | And_add, And_add 
  | And_mult, And_mult => true
  | BackEdge n, BackEdge n' => (n =? n')
  | _, _ => false
 end.

Instance: EqbSpec orule_kind.
Proof.
  red.
  fix IH 1. destruct x; destruct y; try cons; cbn.
  case eqbspec; [ intros <- | cons ]. intuition.
Qed.

Inductive oderivation :=
  | ORule : list (nat*osequent) -> orule_kind -> osequent -> list oderivation -> oderivation.

(** Returns the current sequent/bottom sequent *)

Definition oclaim '(ORule _ _ s _) := s.

Definition oclaim' := (fun (d:oderivation) => oseq_forget (oclaim d)).

Definition backedges '(ORule ls _ _ _) := ls.

Definition rule '(ORule _ R _ _) := R.

Definition premisses '(ORule _ _ _ ld) := ld.

(** Utility functions on derivations:
    - bounded-vars level (used by the [BClosed] predicate),
    - check w.r.t. signature *)

Instance level_oderivation : Level oderivation :=
 fix level_oderivation d :=
  let '(ORule _ _ s ds) := d in
  list_max (level s :: List.map level_oderivation ds).

Fixpoint combine_eq_length (l l' : list oderivation) := 
      match ((length l) =? (length l')) with
        | true => Some (combine l l')
        | false => None
      end.

Fixpoint AndList (l:list bool) :=
  match l with
  | [] => true
  | x::l' => x && AndList l'
  end.

(* Instance eqb_oderivation : Eqb oderivation :=
  fix eqb_oderivation d1 d2 :=
    let '(ORule ls1 R1 s1 ld1) := d1 in 
    let '(ORule ls2 R2 s2 ld2) := d2 in 
     (ls1 =? ls2) && (R1 =? R2) && (s1 =? s2) && 
     let lco := (combine_eq_length ld1 ld2) in
     match lco with
     | Some l' => AndList (map (prod_curry eqb_oderivation) l')
     | None   => false
     end. *)
     
Instance bsubst_oderiv : BSubst oderivation :=
 fix bsubst_oderiv n f d :=
 let '(ORule ls R s ds) := d in
 ORule ls R (s [[ %n := f ]]) (map (bsubst_oderiv n f) ds).
 
Instance obsubst_oderiv : OBSubst oderivation :=
 fix obsubst_oderiv n o d :=
 let '(ORule ls R s ds) := d in
 ORule ls R (obsubst n o s ) (map (obsubst_oderiv n o) ds).

(** Induction principle on derivations with correct
    handling of sub-derivation lists. *)

Lemma oderivation_ind' (P: oderivation -> Prop) :
  (forall ls r s ds, Forall P ds -> P (ORule ls r s ds)) ->
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

Definition OClaim d s := oclaim d = s.
Arguments OClaim _ _ /.
Hint Extern 1 (OClaim _ _) => cbn.

Definition Backedges d ls := backedges d = ls.
Arguments Backedges _ _ /.
Hint Extern 1 (Backedges _ _) => cbn.



















