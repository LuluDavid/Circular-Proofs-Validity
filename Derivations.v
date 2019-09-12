Require Export Occurrences.
Import ListNotations Arith Bool.

Local Open Scope form.

(** DEFINITIONS *)

(** Subderiv *)

Fixpoint subderiv (d:derivation)(a:address): option derivation :=
  let '(ORule ls R s ld) := d in
  match a, ld with
  | [], _               => Some d
  | i::a', [d']        => subderiv d' a'  
  | l::a', [d1;d2] => subderiv d1 a'
  | r::a', [d1;d2] => subderiv d2 a'
  | _, _ => None
  end.

Definition is_subderiv (d1 d2: derivation): Prop := exists a, subderiv d2 a = Some d1. 

(** Example *)

Local Open Scope string_scope.

Definition Subderiv_example: derivation := 
  ORule [] And_mult (⊢[{ (//"A"#~//"A")⊗!, [] }]) 
              [
              ORule [] Or_mult (⊢[{ //"A"#~//"A", [l] }]) [
                                                                            ORule [] Ax (⊢[{ //"A", [l;l] }; { ~//"A", [r;l] }]) []
                                                                            ];
              ORule [] OneR (⊢[{ !, [r] }]) []
              ].

(*
  --------------------------------------------------------- (Ax),(1)
   [] ⊢{ //A, [l,l] } ,{ ¬//A, [l,r] }         [] ⊢{ !, [r] }
  --------------------------------------------------------- (#)
   [] ⊢{ (//A#¬//A), [l] }         [] ⊢{ !, [r] }
  --------------------------------------------------------- (⊗)
                      [] ⊢{ (//A#¬//A)⊗!, [] }
  *)
  
Compute subderiv Subderiv_example [l;i].



Local Open Scope list_scope.
Local Open Scope eqb_scope.

(** Lift *)

Fixpoint lift (l:list (nat*osequent)): list (nat*osequent) :=
  match l with
  | [] => []
  | (j, F)::ls => (j+1, F)::(lift ls)
  end.

(** Transition between backedgeable sequent lists *)

Definition valid_next_sequent_unary (l1 l2:list(nat*osequent))(s:osequent) := 
  (l1 =? lift l2) ||| (l1 =? (1, s):: (lift l2)).

Definition valid_next_sequent_binary (l1 l2 l3:list(nat*osequent))(s:osequent) := 
  ((l2 =? (lift l1)) ||| (l2 =? ((1, s) :: (lift l1))))
  &&& ((l3 =? (lift l1)) ||| (l3 =? ((1, s) :: (lift l1)))).

(** Explicit pattern matching for 2 <= length l*)

Definition binary_or_more {A:Type} (l:list A): bool :=
  match l with
  | x::y::l' => true
  | _ => false
  end.




(** Boolean Validity *)

Definition valid_deriv_step '(ORule ls R s ld) :=
  match List.map claim ld, List.map backedges ld with
  | [], _ => match R, s with
             | Ax,  (⊢ {A,_}::Γ )   => list_mem (dual A) (map occ_forget Γ)
             | TopR,  (⊢ Γ )         => list_mem ⊤ (map occ_forget Γ)
             | OneR,  (⊢ [{! ,_}]) => true
             | BackEdge n, s      => match list_assoc n ls with 
                                                  | None      => false
                                                  | Some s' => oseq_equivb s s'
                                                  end
             | _, _                         => false
             end
  | [(⊢ Γ')], [ls'] => valid_next_sequent_unary ls' ls s &&&
                               match R, s with
                               | BotR,  (⊢ {⊥, _}::Γ)              => (Γ' =? Γ)
                               | Or_add_l, (⊢ {(F⊕G), a}::Γ) => (Γ' =? {F, (l::a)}::Γ) 
                               | Or_add_r, (⊢ { F⊕G, a }::Γ) => (Γ' =? {G, (r::a)}::Γ)
                               | Or_mult,  (⊢ { F#G, a }::Γ)   => (Γ' =? {F, (l::a)}::{G, (r::a)}::Γ) 
                               | Ex,  (⊢ Γ)                              => swapb Γ Γ' &&& (binary_or_more Γ')
                               | Mu, (⊢ { µ F, a }::Γ)              => (Γ' =? {F[[ %0 := µ F ]], i::a}::Γ)
                               | Nu, (⊢ { ν F, a }::Γ)              => (Γ' =? {F[[ %0 := ν F ]], i::a}::Γ)
                               | _, _                                        => false
                               end
   | [(⊢ {F',a1}::Γ1);(⊢ {G',a2}::Γ2)], [ls1;ls2]
                          => valid_next_sequent_binary ls ls1 ls2 s &&&
                               match R, s with 
                               | And_add,  (⊢ { F&G, a }::Γ) => (F =? F') &&& (G =? G') &&& 
                                                                                    (a1 =? l::a) &&& (a2 =? r::a) &&& 
                                                                                    (Γ1 =? Γ) &&& (Γ2 =? Γ)
                               | And_mult,  (⊢ { F⊗G, a }::Γ) => (F =? F') &&& (G =? G') &&& 
                                                                                      (a1 =? l::a) &&& (a2 =? r::a) &&& 
                                                                                      ((app Γ1 Γ2) =? Γ) 
                               | Cut,  (⊢  Γ)                             => ( Γ =? Γ1 ++  Γ2 ) &&& (G' =? (dual F'))  
                                                                                      &&& disjoint_addr_listb a1 (ocontext_addr Γ1)
                                                                                      &&& disjoint_addr_listb a2 (ocontext_addr Γ2)
                               | _, _                                          => false
                               end
   | _, _ => false
   end.

Fixpoint pre_valid_deriv d :=
  valid_deriv_step d &&&
   (let '(ORule _ _ _ ld) := d in
    List.forallb (pre_valid_deriv) ld).


Definition valid_deriv d := disjoint_listb (ocontext_addr (claim d)) &&& pre_valid_deriv d.


(** Example *)

Local Open Scope string_scope.

Compute valid_deriv_step Subderiv_example.

Definition oderiv_example :=
  ORule [] Or_mult (⊢[{ (//"A"#(dual (//"A"))), [r] }]) [ORule [] Ax (⊢[{ //"A", [l;r] }; {dual (//"A"), [r;r]}]) [] ].
 Print oderiv_example.
Compute 
  obsubst 0 ({//"B", []})%form oderiv_example.
  
  
 (*
  ----------------------------------------------------- (Ax)
                      [] ⊢{ //A, [l] } ,{ ¬//A, [r] } 
  ----------------------------------------------------- (#)
                      [] ⊢{ (//A#¬//A), [] }
  *)
  
Compute valid_deriv oderiv_example.




(** Inductive Validity *)
 
Inductive preValid : derivation -> Prop :=
 | V_Ax Γ A ls a a': In { dual A, a' } Γ
                                -> preValid (ORule ls Ax (⊢ {A, a}::Γ) [])
 | V_Tr Γ ls a: In {⊤, a} Γ 
                       -> preValid (ORule ls TopR (⊢ Γ) [])
 | V_One ls a: preValid (ORule ls OneR (⊢ [{!, a}]) [])
 | V_Bot d Γ ls a: preValid d 
                             -> Claim d (⊢Γ) 
                             -> Backedges d (lift ls) \/ Backedges d ( (1, ⊢{⊥, a}::Γ) :: lift ls)
                             -> preValid (ORule ls BotR (⊢{⊥, a}::Γ) [d])
 | V_Or_add_l d F G Γ a ls: 
                            preValid d 
                            -> Claim d (⊢{F,l::a}::Γ) 
                            -> Backedges d (lift ls) \/ Backedges d ( (1, ⊢{ F⊕G, a }::Γ) :: lift ls)
                            -> preValid (ORule ls Or_add_l (⊢{ F⊕G, a }::Γ) [d])
 | V_Or_add_r d F G Γ a ls  : 
                            preValid d 
                            -> Claim d (⊢{G,r::a}::Γ)
                            -> Backedges d (lift ls) \/ Backedges d ( (1, ⊢{ F⊕G, a }::Γ) :: lift ls)
                            -> preValid (ORule ls Or_add_r (⊢{ F⊕G, a }::Γ) [d])
 | V_Or_mult d F G Γ a ls :
                            preValid d 
                            -> Claim d (⊢{ F, l::a } :: { G, r::a } :: Γ) 
                            -> Backedges d (lift ls) \/ Backedges d ( (1, ⊢{ F#G, a }::Γ) :: lift ls)
                            -> preValid (ORule ls Or_mult (⊢ { F#G, a}::Γ) [d])
 | V_And_add d1 d2 F G Γ a ls :
                            preValid d1 -> preValid d2 
                            -> Claim d1 (⊢ { F, l::a }::Γ) -> Claim d2 (⊢ { G, r::a }::Γ) 
                            -> Backedges d1 (lift ls) \/ Backedges d1 ( (1, ⊢{ F&G, a }::Γ) :: lift ls)
                            -> Backedges d2 (lift ls) \/ Backedges d2 ( (1, ⊢{ F&G, a }::Γ) :: lift ls)
                            -> preValid (ORule ls And_add (⊢ { F&G, a } :: Γ) [d1;d2])
 | V_And_mult d1 d2 F G Γ1 Γ2 a ls :
                            preValid d1 -> preValid d2 
                            -> Claim d1 (⊢ { F, l::a } :: Γ1) -> Claim d2 (⊢ { G, r::a } :: Γ2) 
                            -> Backedges d1 (lift ls) \/ Backedges d1 ( (1, ⊢ { F⊗G, a } :: (app Γ1 Γ2)) :: lift ls)
                            -> Backedges d2 (lift ls) \/ Backedges d2 ( (1, ⊢ { F⊗G, a } :: (app Γ1 Γ2)) :: lift ls)
                            -> preValid (ORule ls And_mult (⊢ { F⊗G, a } :: (app Γ1 Γ2)) [d1;d2])
 | V_Cut d1 d2 A Γ1 Γ2 ls a1 a2 :
                            preValid d1 -> preValid d2 
                            -> Claim d1 (⊢ { A, a1}::Γ1) -> Claim d2 (⊢ { dual A, a2 }::Γ2) 
                            -> disjoint_addr_list a1 (ocontext_addr Γ1) -> disjoint_addr_list a2 (ocontext_addr Γ2)
                            -> Backedges d1 (lift ls) \/ Backedges d1 ( (1, ⊢app Γ1 Γ2) :: lift ls) 
                            -> Backedges d2 (lift ls) \/ Backedges d2 ( (1, ⊢app Γ1 Γ2) :: lift ls)
                            -> preValid (ORule ls Cut (⊢app Γ1 Γ2) [d1;d2])
 | V_Ex d F G Γ1 Γ2 ls :
                            preValid d 
                            -> Claim d (⊢ app Γ1 (G::F::Γ2)) 
                            -> Backedges d (lift ls) \/ Backedges d ( (1, ⊢app Γ1 (F::G::Γ2)) :: lift ls)
                            -> preValid (ORule ls Ex (⊢app Γ1 (F::G::Γ2)) [d])
 | V_Mu d F Γ ls a :
                            preValid d 
                            -> Claim d (⊢ { F[[ %0 := µ F ]], i::a }::Γ) 
                            -> Backedges d (lift ls) \/ Backedges d ( (1, ⊢ { (µ F), a }::Γ) :: lift ls)
                            -> preValid (ORule ls Mu (⊢ { (µ F), a }::Γ) [d])
 | V_Nu d F Γ ls a :
                            preValid d 
                            -> Claim d (⊢ {F[[ %0 := ν F ]], i::a}::Γ) 
                            -> Backedges d (lift ls) \/ Backedges d ( (1, ⊢ { (ν F), a }::Γ) :: lift ls)
                            -> preValid (ORule ls Nu (⊢ { (ν F), a }::Γ) [d])

 | V_BackEdge ls s n: option_oseq_equiv (Some s) (list_assoc n ls)
                                                -> preValid (ORule ls (BackEdge n) s [])
 .

Hint Constructors preValid.

Definition Valid (d:derivation) := disjoint_list (ocontext_addr (claim d)) /\ preValid d.
(** Two Examples *)

Definition oderiv_example' :=
ORule [] Nu (⊢ [{ (ν (%0)⊕(%0)), [] }]) 
          [
          (
          ORule [(1, ⊢ [{ (ν (%0)⊕(%0)), [] }])] Or_add_l (⊢ [ { ((ν (%0)⊕(%0)) ⊕ (ν (%0)⊕(%0))), [i] } ] )
            [
            (
            ORule [(2, ⊢ [{ (ν (%0)⊕(%0)), [] }])] (BackEdge 2) (⊢ [ { ν (%0)⊕(%0), [l;i] } ] ) []
            )
            ] 
          ) 
          ].
  (*
    ----------------------------------------------------- (BackEdge (⊢vX. X⊕X))
     [(⊢{ vX. X⊕X, [] })] ⊢ { (vX.X⊕X), [l,i] }
    ----------------------------------------------------- (⊕l)
     [(⊢{ vX. X⊕X, [] })] ⊢ { (vX.X⊕X) ⊕ (vX.X⊕X) , [i] } 
    ----------------------------------------------------- (v)
                        [] ⊢{ vX. X⊕X, [] }
    *)


Theorem thm_oexample: 
  preValid (oderiv_example').
Proof.
  repeat (constructor; intuition).
Qed.

Definition cut_example (F:formula): derivation :=
ORule [] Cut (⊢ [{ F#(~F), [r] }]) 
          [
          ORule [] Or_mult (⊢ [{ F#(~F), [l] }]) [ ORule [] Ax (⊢ [{ F, [l;l] }; { ~ F, [r;l] }]) [] ];
          ORule [] Ex (⊢ [{ ~(F#(~F)), [l] };{ F#(~F), [r] }]) [ORule [] Ax (⊢ [{ F#(~F), [r] }; { ~(F#(~F)), [l] }]) [] ]
          ].

(* 
    ------------------------------- (Ax)     -------------------------------------------- (Ax)
    [] ⊢ { F, [l;l] }, {~F, [r;l]             [] ⊢ { F#~F, [r] }, { ~(F#~F), [l] }
    -------------------------------- (#)      ------------------------------------------ (Ex)
     [] ⊢ { F#~F, [l] }                       [] ⊢ { ~(F#~F), [l] }, { F#~F, [r] }
    --------------------------------------------------------------------------- (Cut)
                        [] ⊢{ F#~F, [r] }
*)

Theorem thm_cut_example (F:formula): 
  Valid (cut_example F).
Proof.
  constructor; simpl; try(split; trivial; unfold disjoint_addr_list; intros; inversion H);
  apply (V_Cut _ _  (F#(~F)) [] [{ F#(~F), [r] }] _ [l] [l]); repeat constructor; intuition.
  - eapply V_Ax; intuition.
  - eapply (V_Ex _ _ _ [] []); repeat constructor.
    eapply V_Ax; intuition.
  - inversion H; try contradiction; simpl in H1; subst; inversion H0.
  - inversion H; try contradiction; simpl in H1; subst; inversion H0.
Qed.

Compute (valid_deriv (cut_example (// "X"))).



(** Printing functions *)

Definition context_example : context := [(ν (%0)⊕(%0))%form; (µ (%1)#(%0))%form].
Compute (print_ctx context_example).

Definition sequent_example := Seq context_example.
Compute (print_seq sequent_example).

Fixpoint print_list_oseq (ls:list (nat*osequent)) :=
  match ls with
  | [] => ""
  | (n, s)::ls => (print_oseq s)
  end.

Local Open Scope string_scope.

Fixpoint print_oderiv_list (d:derivation): list string :=
  let '(ORule ls R s ds) := d in
  concat (map print_oderiv_list ds) ++ 
  [string_mult "-" (String.length (print_list_oseq ls ++ print_oseq s)) ++ print_rule R; 
  print_list_oseq ls ++ print_oseq s].

Fixpoint print_list_string (l:list string): string :=
  match l with
  | [] => ""
  | s::ls => s++(String "010" (print_list_string ls))
  end.
  
Definition print_oderiv (d:derivation) : string := print_list_string (print_oderiv_list d).

Compute print_list_string (print_oderiv_list oderiv_example').








(** META *)

Local Open Scope eqb_scope.

(** EqbSpec *)

Instance : EqbSpec (nat*osequent).
Proof.
  red.
  destruct x; destruct y; cbn. 
  case eqbspec; [ intros <- | cons ]; case eqbspec; [ intros <- | cons ]; simpl.
  constructor; trivial.
Qed.

(** NextSequent *)

Lemma valid_next_sequent_unary_prop : forall l1 l2 s,
  valid_next_sequent_unary l1 l2 s = true <-> (l1 = lift l2) \/ (l1 = (1, s):: (lift l2)).
Proof.
  unfold valid_next_sequent_unary; intros.
  repeat rewrite <- Utils.eqb_eq; rewrite lazy_orb_iff; apply iff_refl.
Qed.

Lemma valid_next_sequent_binary_prop : forall l1 l2 l3 s,
  valid_next_sequent_binary l1 l2 l3 s = true <->
  ((l2 = (lift l1)) \/ (l2 = ((1, s) :: (lift l1)))) /\ ((l3 = (lift l1)) \/ (l3 = ((1, s) :: (lift l1)))).
Proof.
  unfold valid_next_sequent_binary; intros.
  repeat rewrite <- Utils.eqb_eq; rewrite lazy_andb_iff, lazy_orb_iff, lazy_orb_iff; apply iff_refl.
  Qed.

(** Easier Induction principles for derivations *)

Lemma derivation_ind' (P: derivation -> Prop) :
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
 unfold Claim, BClosed, valid_next_sequent_unary, valid_next_sequent_binary in *; 
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

Theorem pre_valid_deriv_is_preValid: forall (d:derivation), 
  pre_valid_deriv d = true <-> preValid d.
Proof.
  split.
 - induction d as [ls r s ds IH] using derivation_ind'.
   cbn - [valid_deriv_step]. rewrite lazy_andb_iff. intros (H,H').
   assert (IH' : Forall (fun d => preValid d) ds).
   { rewrite Forall_forall in *. rewrite forallb_forall in *. auto. }
   clear IH H'.
   cbn in *.
   break_step; break_step;
   try(econstructor; simpl; destruct (list_assoc n ls); try discriminate H; apply oseq_equiv_is_oseq_equivb; trivial); 
   break; try (mytac; constructor; mytac; reflexivity).
   + apply list_mem_in_occ in H; destruct H; econstructor; eassumption.
   + apply list_mem_in_occ in H; destruct H; econstructor; eassumption.
   + discriminate H.
   + apply swapb_is_swap in H1; do 5 destruct H1; subst; econstructor; mytac;
         rewrite H2; trivial.
   + mytac. apply (V_Cut _ _ F l1 l4 _ a a0); mytac; apply disjoint_addr_list_is_disjoint_addr_listb; trivial.
 - induction 1; simpl; trivial;
   try (apply lazy_orb_iff; left; apply list_mem_in_occ; eauto);
   try(apply lazy_andb_iff; split; try (auto with *);
         rewr; destruct Γ; try (destruct o); apply valid_next_sequent_unary_prop in H1;
         rewrite Utils.eqb_refl, lazy_andb_iff; split; trivial);
   try(apply lazy_andb_iff; split; try (auto with *);
         rewr; rewrite lazy_andb_iff; split; repeat rewrite Utils.eqb_refl; trivial;
         apply valid_next_sequent_binary_prop; split; trivial).
   + rewr; repeat rewrite lazy_andb_iff; split; auto.
      split; try(apply valid_next_sequent_binary_prop; split; trivial);
           repeat rewrite Utils.eqb_refl; repeat (split; trivial); 
           apply disjoint_addr_list_is_disjoint_addr_listb; trivial.
    + rewr; rewrite lazy_andb_iff; split; auto; destruct (Γ1 ++ G :: F :: Γ2) eqn:Heq; 
       try(destruct Γ1; discriminate Heq);
       destruct o; repeat rewrite lazy_andb_iff; split; 
       try apply valid_next_sequent_unary_prop; trivial;
       destruct l; 
       try(destruct Γ1; try discriminate Heq; injection Heq as _ Hd; destruct Γ1; discriminate Hd);
       split; trivial; rewrite <- Heq; apply swapb_pattern.
     + rewrite lazy_orb_false; simpl in H; destruct (list_assoc n ls); 
        try contradiction; apply oseq_equiv_is_oseq_equivb; trivial.
Qed.

Theorem valid_deriv_is_Valid : forall d, valid_deriv d = true <-> Valid d.
Proof.
  unfold Valid, valid_deriv; split; intros.
  - apply lazy_andb_iff in H; 
    rewrite disjoint_list_is_disjoint_listb, <- pre_valid_deriv_is_preValid; trivial.
  - apply lazy_andb_iff; 
    rewrite disjoint_list_is_disjoint_listb, <- pre_valid_deriv_is_preValid in H; trivial.
Qed.













