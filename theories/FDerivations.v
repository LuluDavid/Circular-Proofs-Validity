Require Export Debruijn.
Import String Ascii.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope form.
Local Open Scope eqb_scope.

(** Contexts *)

Definition context := list formula.
  
Definition print_ctx Γ :=
  String.concat ", " (List.map print_formula Γ).

(** check, bsubst, level, fvars, eqb : given by instances
    on lists. *)

(** Sequent *)

Inductive sequent :=
| Seq : context -> sequent.

Notation "|- F" := (Seq F) (at level 100).

Instance bsubst_seq : BSubst sequent :=
 fun n u '(|- Γ ) => (|- (bsubst n u Γ) ).

Instance level_seq : Level sequent :=
 fun '(|- Γ ) => level Γ .

Instance seq_eqb : Eqb sequent :=
 fun '(|- Γ1) '(|- Γ2) => (Γ1 =? Γ2).

Definition print_seq '(|- Γ) :=
  "|- " ++ print_ctx Γ.

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
  | BackEdge (n:nat)
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
  | BackEdge n => "(BackEdge " ++ (String (ascii_of_nat (48 + n)) "") ++ ")" 
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
  | Rule : list (nat*sequent) -> rule_kind -> sequent -> list derivation -> derivation.

(** Returns the current sequent/bottom sequent *)

Definition claim '(Rule _ _ s _) := s.
Definition backedges '(Rule ls _ _ _) := ls.
Definition rule '(Rule _ R _ _) := R.
Definition premisses '(Rule _ _ _ ld) := ld.

Definition Claim d s := claim d = s.
Arguments Claim _ _ /.
Hint Extern 1 (Claim _ _) => cbn.

Definition Backedges d ls := backedges d = ls.
Arguments Backedges _ _ /.
Hint Extern 1 (Backedges _ _) => cbn.


(** Utility functions on derivations:
    - bounded-vars level (used by the [BClosed] predicate),
    - check w.r.t. signature *)

Instance level_derivation : Level derivation :=
 fix level_derivation d :=
  let '(Rule ls r s ds) := d in
  list_max (level s :: List.map level_derivation ds).

Instance bsubst_deriv : BSubst derivation :=
 fix bsubst_deriv n u d :=
 let '(Rule ls r s ds) := d in
 Rule ls r (bsubst n u s ) (map (bsubst_deriv n u) ds).

Definition binary_or_more {A:Type} (l:list A): bool :=
  match l with
  | x::y::l' => true
  | _ => false
  end.

Fixpoint lift (l:list (nat*sequent)): list (nat*sequent) :=
  match l with
  | [] => []
  | (j, F)::ls => (j+1, F)::(lift ls)
  end.

Local Open Scope list_scope.

Definition valid_deriv_step '(Rule ls r s ld) :=
  match List.map claim ld with
  | [] => match r, s with
          | Ax,  (|- A::Γ ) => list_mem (dual A) Γ
          | TopR,  (|- Γ )  => list_mem ⊤ Γ
          | OneR,  (|- [!]) => true
          | BackEdge n, s   => match list_assoc n ls with
                               | None    => false
                               | Some s' => s =? s'
                               end
          | _, _            => false
          end
  | [(|- Γ')] => match r, s with
                 | BotR,  (|- ⊥::Γ)        => (Γ' =? Γ)
                 | Or_add_l, (|- (F⊕G)::Γ) => (Γ' =? F::Γ) 
                 | Or_add_r, (|- (F⊕G)::Γ) => (Γ' =? G::Γ)
                 | Or_mult,  (|- (F#G)::Γ) => (Γ' =? F::G::Γ) 
                 | Ex,  (|- Γ)             => swapb Γ Γ' &&& (binary_or_more Γ')
                 | Mu, (|- (µ F)::Γ)       => (Γ' =? (F[[ %0 := µ F ]])::Γ)
                 | Nu, (|- (ν F)::Γ)       => (Γ' =? (F[[ %0 := ν F ]])::Γ)
                 | _, _                    => false
                 end
   | [(|- F'::Γ1);(|- G'::Γ2)]
              => match r, s with
                 | And_add,  (|- (F&G)::Γ)  => (F =? F') &&& (G =? G') &&&
                                               (Γ1 =? Γ) &&& (Γ2 =? Γ)
                 | And_mult,  (|- (F⊗G)::Γ) => (F =? F') &&& (G =? G') &&& 
                                               ((app Γ1 Γ2) =? Γ)
                 | Cut,  (|-  Γ)            => ( Γ =? Γ1 ++  Γ2 ) &&& (G' =? (dual F'))
                 | _, _                     => false
                 end
   | _ => false
   end.

Fixpoint valid_deriv d :=
  valid_deriv_step d &&&
   (let '(Rule _ _ _ ld) := d in
    List.forallb (valid_deriv) ld).

Definition deriv_example :=
  Rule [] Or_mult (|-[((// "A")#(dual (// "A")))%form]) [Rule [] Ax (|-[(// "A")%form;dual (// "A")%form]) [] ].
 Print deriv_example. 
Compute 
  bsubst_deriv 0 (// "B")%form deriv_example.
  
  
 (*
  ----------------------------------------------------- (Ax)
                      [] |-//A,¬//A 
  ----------------------------------------------------- (#)
                      [] |-//A#¬//A
  *)
  
Compute valid_deriv deriv_example.

(** Inductive Validity *)

Inductive Valid : derivation -> Prop :=
 | V_Ax Γ A ls :           In (dual A) Γ 
                           -> Valid (Rule ls Ax (|- A::Γ) [])
 | V_Tr Γ ls:              In ⊤ Γ 
                           -> Valid (Rule ls TopR (|- Γ) [])
 | V_One ls:               Valid (Rule ls OneR (|- [!]) [])
 | V_Bot d Γ ls:           Valid d 
                            -> Claim d (|-Γ) 
                            -> Backedges d (lift ls) \/ Backedges d ( (1, |-⊥::Γ) :: lift ls)
                            -> Valid (Rule ls BotR (|-⊥::Γ) [d])
 | V_Or_add_l d F G Γ ls:  Valid d 
                            -> Claim d (|-F::Γ) 
                            -> Backedges d (lift ls) \/ Backedges d ( (1, |-(F⊕G)::Γ) :: lift ls)
                            -> Valid (Rule ls Or_add_l (|-(F⊕G)::Γ) [d])
 | V_Or_add_r d F G Γ ls  : Valid d 
                            -> Claim d (|-G::Γ)
                            -> Backedges d (lift ls) \/ Backedges d ( (1, |- (F⊕G)::Γ) :: lift ls)
                            -> Valid (Rule ls Or_add_r (|- (F⊕G)::Γ) [d])
 | V_Or_mult d F G Γ ls :   Valid d
                            -> Claim d (|- F :: G :: Γ) 
                            -> Backedges d (lift ls) \/ Backedges d ( (1, |- (F#G)::Γ) :: lift ls)
                            -> Valid (Rule ls Or_mult (|- (F#G)::Γ) [d])
 | V_And_add d1 d2 F G Γ ls :
                            Valid d1 -> Valid d2 
                            -> Claim d1 (|- F::Γ) -> Claim d2 (|- G::Γ) 
                            -> Backedges d1 (lift ls) \/ Backedges d1 ( (1, |- (F&G)::Γ) :: lift ls)
                            -> Backedges d2 (lift ls) \/ Backedges d2 ( (1, |- (F&G)::Γ) :: lift ls)
                            -> Valid (Rule ls And_add (|- (F&G) :: Γ) [d1;d2])
 | V_And_mult d1 d2 F G Γ1 Γ2 ls :
                            Valid d1 -> Valid d2 
                            -> Claim d1 (|- F :: Γ1) -> Claim d2 (|- G :: Γ2) 
                            -> Backedges d1 (lift ls) \/ Backedges d1 ( (1, |- (F⊗G) :: (app Γ1 Γ2)) :: lift ls)
                            -> Backedges d2 (lift ls) \/ Backedges d2 ( (1, |- (F⊗G) :: (app Γ1 Γ2)) :: lift ls)
                            -> Valid (Rule ls And_mult (|- (F⊗G) :: (app Γ1 Γ2)) [d1;d2])
 | V_Cut d1 d2 A Γ1 Γ2 ls : Valid d1 -> Valid d2 
                            -> Claim d1 (|- A::Γ1) -> Claim d2 (|- (dual A)::Γ2) 
                            -> Backedges d1 (lift ls) \/ Backedges d1 ( (1, |- app Γ1 Γ2) :: lift ls) 
                            -> Backedges d2 (lift ls) \/ Backedges d2 ( (1, |- app Γ1 Γ2) :: lift ls)
                            -> Valid (Rule ls Cut (|- app Γ1 Γ2) [d1;d2])
 | V_Ex d F G Γ1 Γ2 ls :    Valid d 
                            -> Claim d (|- app Γ1 (G::F::Γ2)) 
                            -> Backedges d (lift ls) \/ Backedges d ( (1, |-app Γ1 (F::G::Γ2)) :: lift ls)
                            -> Valid (Rule ls Ex (|- app Γ1 (F::G::Γ2)) [d])
 | V_Mu d F Γ ls :          Valid d 
                            -> Claim d (|- (F[[ %0 := µ F ]]) :: Γ) 
                            -> Backedges d (lift ls) \/ Backedges d ( (1, |- (µ F)::Γ) :: lift ls)
                            -> Valid (Rule ls Mu (|- (µ F)::Γ) [d])
 | V_Nu d F Γ ls :          Valid d 
                            -> Claim d (|- (F[[ %0 := ν F ]]) :: Γ) 
                            -> Backedges d (lift ls) \/ Backedges d ( (1, |- (ν F)::Γ) :: lift ls)
                            -> Valid (Rule ls Nu (|- (ν F)::Γ) [d])

 | V_BackEdge ls s n: (Some s = list_assoc n ls)
                            -> Valid (Rule ls (BackEdge n) s [])
 .

Hint Constructors Valid.

(** META *)

(** Easier Induction principles for derivations *)

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

(** Tactics for proof below *)

Ltac break_step :=
 rewrite ?lazy_andb_iff, ?andb_true_iff, ?lazy_andb_false in *;
 match goal with
 | H : match claim ?x with _ => _ end = true |- _ =>
   destruct x; simpl in H; try easy 
 | H : match map _ ?x with _ => _ end = true |- _ =>
   destruct x; simpl in H; try easy
 | H : _ /\ _ |- _ => destruct H as [?H H] 
 | H : match ?x with _ => _ end = true |- _ =>
   destruct x; simpl in H; try easy
 | _ => idtac
 end.

Ltac break :=
 rewrite ?lazy_andb_iff, ?andb_true_iff, ?lazy_andb_false in *;
 match goal with
 | H : match claim ?x with _ => _ end = true |- _ =>
   destruct x; simpl in H; try easy; break
 | H : match map _ ?x with _ => _ end = true |- _ =>
   destruct x; simpl in H; try easy; break
 | H : _ /\ _ |- _ => destruct H as [?H H]; break
 | H : match ?x with _ => _ end = true |- _ =>
    destruct x; simpl in H; try easy; break
 | _ => idtac
 end.

Ltac mytac :=
 cbn in *;
 rewrite ?lazy_andb_iff, ?andb_true_iff, ?lazy_andb_false in *;
 repeat match goal with H : _ /\ _ |- _ => destruct H end;
 repeat match goal with IH : Forall _ _  |- _ => inversion_clear IH end;
 unfold Claim, BClosed;
 rewrite ?lazy_orb_iff in *;
 rewrite ?@Utils.eqb_eq in * by auto with typeclass_instances; subst;
 simpl in *; trivial.

Ltac rewr :=
 unfold Claim, BClosed in *;
 match goal with
 | H: _ = _ |- _ => rewrite H in *; clear H; rewr
 | _ => rewrite ?eqb_refl
 end.

Local Open Scope list_scope.

(** Boolea <-> Inductive *)

Theorem valid_deriv_is_Valid: forall (d:derivation),
  valid_deriv d = true <-> Valid d.
Proof.
Admitted.

