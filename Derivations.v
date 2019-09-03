Require Import Utils Defs Debruijn Occurrences Address.
Require Import StringUtils Datatypes.
Require DecimalString.
Import ListNotations.
Require Import Arith.
Import Bool.

Local Open Scope form.

(** SUBDERIV *)

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

(* list_mem for sequents *)

Fixpoint InOSequent (s : osequent) (l : list osequent) : bool :=
    match l with
       | [] => false
       | s' :: m => (s' =? s) || (InOSequent s m)
     end.







(** FUNCTIONS ON LIST OF BACKEDGEABLE SEQUENTS *)

Fixpoint get (n:nat)(l:list (nat*osequent)): osequent :=
  match l with
  | [] => ⊢ []
  | (n', s)::ls => if (n =? n') then s else get n ls
  end.

Fixpoint lift (l:list (nat*osequent)): list (nat*osequent) :=
  match l with
  | [] => []
  | (j, F)::ls => (j+1, F)::(lift ls)
  end.

Lemma list_assoc_get_Some : forall n l s, list_assoc n l = Some s -> get n l = s.
Proof.
  intros; induction l.
  -- inversion H.
  -- simpl in *; destruct a; destruct (n=?n0).
    + injection H as H; subst; trivial.
    + apply IHl; assumption.
Qed.

Lemma list_assoc_get_None : forall n l, list_assoc n l = None -> get n l = (⊢ []).
Proof.
  intros; induction l; intros; simpl in *; trivial; destruct a; destruct (n =? n0); 
  try discriminate H; apply IHl; assumption.
Qed.

Instance : EqbSpec (nat*osequent).
Proof.
  red.
  destruct x; destruct y; cbn. 
  case eqbspec; [ intros <- | cons ]; case eqbspec; [ intros <- | cons ]; simpl.
  constructor; trivial.
Qed.

Local Open Scope eqb_scope.





(** COUNT_OCC' *)

Fixpoint count_occ' (l : list Occurrence) (x : formula) : nat := 
  match l with
  | [] => 0
  | { y, a } :: l' => if (x =? y) then 1 + (count_occ' l' x) else (count_occ' l' x)
  end.

Local Open Scope list_scope.

Lemma count_occ'_app :  forall l1 l2 f, count_occ' (l1 ++ l2) f = count_occ' l1 f + count_occ' l2 f.
Proof.
  induction l1; intros; simpl in *; trivial.
  destruct a; destruct (f =? F); trivial.
  rewrite plus_Sn_m; rewrite IHl1; trivial.
Qed.

Lemma count_occ'_permut : forall o1 o2 l1 l2 f, 
                                        count_occ' (l1 ++ o1 :: o2 :: l2) f = count_occ' (l1 ++ o2 :: o1 :: l2) f.
Proof.
  intros.
  destruct o1; destruct o2.
  rewrite count_occ'_app, count_occ'_app; simpl; destruct (f =? F); destruct (f =? F0); trivial.
Qed.

Lemma count_occ'_in : forall f a l, In {f, a} l -> (1 <= count_occ' l f)%nat.
Proof.
  intros. induction l.
  - inversion H.
  - simpl; simpl in H. destruct H.
    + rewrite H, Utils.eqb_refl; omega.
    + destruct a0; destruct (f =? F)%eqb.
      ++ constructor; apply IHl; assumption.
      ++ apply IHl; assumption.
Qed.









(** BOOLEAN VERSION OF DERIVATION VALIDITY *)

Definition valid_deriv_step '(ORule ls R s ld) :=
  match ls, R, s, List.map claim ld, List.map backedges ld with
  | ls1, Ax, (⊢ {A,_}::Γ ), [], _               => list_mem (dual A) (map occ_forget Γ)
  | _, TopR,  (⊢ Γ ), [], _           => list_mem ⊤ (map occ_forget Γ)
  | _, OneR,  (⊢ [{! ,_}]), [], _               => true
  | ls1, BotR,  (⊢ {⊥, _}::Γ), [s'], [ls2]  => (s' =? (⊢ Γ)) 
                                                                       &&& 
                                                                  ((ls2 =? (lift ls1)) ||| (ls2 =? (1, s):: (lift ls1)))

  | ls1, Or_add_l, (⊢ {(F⊕G), a}::Γ), [s'], [ls2] 
                                                            => (s' =? (⊢ {F, (l::a)}::Γ)) 
                                                                      &&& 
                                                                 ((ls2 =? (lift ls1)) ||| (ls2 =? (1, s) :: (lift ls1)))

  | ls1, Or_add_r, (⊢ { F⊕G, a }::Γ), [s'], [ls2] 
                                                            => (s' =? (⊢ {G, (r::a)}::Γ))  
                                                                      &&& 
                                                                 ((ls2 =? (lift ls1)) ||| (ls2 =? (1, s) :: (lift ls1)))

  | ls1, Or_mult,  (⊢ { F#G, a }::Γ), [s'], [ls2] 
                                                            => (s' =? (⊢{F, (l::a)}::{G, (r::a)}::Γ)) 
                                                                     &&& 
                                                                ((ls2 =? (lift ls1)) ||| (ls2 =? (1, s) :: (lift ls1)))

  | ls1, And_add,  (⊢ { F&G, a }::Γ), [(⊢ {F',a1}::Γ1);(⊢ {G',a2}::Γ2)], [ls2;ls3] 
                                                          => (F =? F') &&& (G =? G') 
                                                                              &&& (a1 =? l::a) &&& (a2 =? r::a) 
                                                                              &&& (Γ1 =? Γ) &&& (Γ2 =? Γ) 
                                                                              &&& ((ls2 =? (lift ls1)) ||| (ls2 =? ((1, s) :: (lift ls1))))
                                                                              &&& ((ls3 =? (lift ls1)) ||| (ls3 =? ((1, s) :: (lift ls1))))

  | ls1, And_mult,  (⊢ { F⊗G, a }::Γ), [(⊢ {F',a1}::Γ1);(⊢ {G',a2}::Γ2)], [ls2;ls3]
                                                          => (F =? F') &&& (G =? G') 
                                                                              &&& (a1 =? l::a) &&& (a2 =? r::a) 
                                                                              &&& ((app Γ1 Γ2) =? Γ) 
                                                                              &&& ((ls2 =? (lift ls1)) ||| (ls2 =? ((1, s) :: (lift ls1))))
                                                                              &&& ((ls3 =? (lift ls1)) ||| (ls3 =? ((1, s) :: (lift ls1))))

  | ls1, Cut,  (⊢  Γ), [(⊢ {A,a1}:: Γ1);(⊢ {B,a2}:: Γ2)], [ls2;ls3]
                                                          => ( Γ =? Γ1 ++  Γ2 ) &&& (B =? (dual A))  
                                                                                            &&& disjoint_addr_listb a1 (ocontext_addr Γ1)
                                                                                            &&& disjoint_addr_listb a2 (ocontext_addr Γ2)
                                                                                            &&& ((ls2 =? (lift ls1)) ||| (ls2 =? ((1, s) :: (lift ls1))))
                                                                                            &&& ((ls3 =? (lift ls1)) ||| (ls3 =? ((1, s) :: (lift ls1))))

  | ls1, Ex,  (⊢ Γ), [(⊢Γ')], [ls2]         => (list_permutb Γ Γ') 
                                                                      &&& 
                                                                (2 <=? length Γ)%nat
                                                                      &&&
                                                              ((ls2 =? (lift ls1)) ||| (ls2 =? ((1, s) :: (lift ls1))))

  | ls1, Mu, (⊢ { µ F, a }::Γ), [(⊢{G,a'}::Γ')], [ls2] 
                                                        => (G =? (F[[ %0 := µ F ]]) ) &&& (Γ =? Γ') &&& (a' =? i::a)
                                                                                        &&& 
                                                             ((ls2 =? (lift ls1)) ||| (ls2 =? (1, s) :: (lift ls1)))

  | ls1, Nu, (⊢ { ν F, a }::Γ), [(⊢{G,a'}::Γ')], [ls2] 
                                                       => (G =? (F[[ %0 := ν F ]])) &&& (Γ =? Γ') &&& (a' =? i::a)
                                                                                        &&& 
                                                            ((ls2 =? (lift ls1)) ||| (ls2 =? (1, s) :: (lift ls1)))

  | ls, BackEdge n, s, [], _ => match list_assoc n ls with
                                                | None => false
                                                | Some s' => oseq_equivb s s'
                                                end
  | _,_,_,_,_ => false
  end.

Fixpoint valid_deriv d :=
  valid_deriv_step d &&&
   (let '(ORule _ _ _ ld) := d in
    List.forallb (valid_deriv) ld).

Compute valid_deriv_step Subderiv_example.

(* Easier Induction principles for derivations *)

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

Local Open Scope string_scope.

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








(** INDUCTIVE VALIDITY *)

Local Open Scope nat_scope.
 
Inductive Valid : derivation -> Prop :=
  
 | V_Ax Γ A ls a a': In { dual A, a' } Γ
                                -> Valid (ORule ls Ax (⊢ {A, a}::Γ) [])
 | V_Tr Γ ls a: In {⊤, a} Γ 
                       -> Valid (ORule ls TopR (⊢ Γ) [])
 | V_One ls a: Valid (ORule ls OneR (⊢ [{!%form, a}]) [])
 | V_Bot d Γ ls a: Valid d 
                             -> Claim d (⊢Γ) 
                             -> Backedges d (lift ls) \/ Backedges d ( (1, ⊢{⊥, a}::Γ) :: lift ls)
                             -> Valid (ORule ls BotR (⊢{⊥, a}::Γ) [d])
 | V_Or_add_l d F G Γ a ls: 
                            Valid d 
                            -> Claim d (⊢{F,l::a}::Γ) 
                            -> Backedges d (lift ls) \/ Backedges d ( (1, ⊢{ F⊕G, a }::Γ) :: lift ls)
                            -> Valid (ORule ls Or_add_l (⊢{ F⊕G, a }::Γ) [d])
 | V_Or_add_r d F G Γ a ls  : 
                            Valid d 
                            -> Claim d (⊢{G,r::a}::Γ)
                            -> Backedges d (lift ls) \/ Backedges d ( (1, ⊢{ F⊕G, a }::Γ) :: lift ls)
                            -> Valid (ORule ls Or_add_r (⊢{ F⊕G, a }::Γ) [d])
 | V_Or_mult d F G Γ a ls :
                            Valid d 
                            -> Claim d (⊢{ F, l::a } :: { G, r::a } :: Γ) 
                            -> Backedges d (lift ls) \/ Backedges d ( (1, ⊢{ F#G, a }::Γ) :: lift ls)
                            -> Valid (ORule ls Or_mult (⊢ { F#G, a}::Γ) [d])
 | V_And_add d1 d2 F G Γ a ls :
                            Valid d1 -> Valid d2 
                            -> Claim d1 (⊢ { F, l::a }::Γ) -> Claim d2 (⊢ { G, r::a }::Γ) 
                            -> Backedges d1 (lift ls) \/ Backedges d1 ( (1, ⊢{ F&G, a }::Γ) :: lift ls)
                            -> Backedges d2 (lift ls) \/ Backedges d2 ( (1, ⊢{ F&G, a }::Γ) :: lift ls)
                            -> Valid (ORule ls And_add (⊢ { F&G, a } :: Γ) [d1;d2])
 | V_And_mult d1 d2 F G Γ1 Γ2 a ls :
                            Valid d1 -> Valid d2 
                            -> Claim d1 (⊢ { F, l::a } :: Γ1) -> Claim d2 (⊢ { G, r::a } :: Γ2) 
                            -> Backedges d1 (lift ls) \/ Backedges d1 ( (1, ⊢ { F⊗G, a } :: (app Γ1 Γ2)) :: lift ls)
                            -> Backedges d2 (lift ls) \/ Backedges d2 ( (1, ⊢ { F⊗G, a } :: (app Γ1 Γ2)) :: lift ls)
                            -> Valid (ORule ls And_mult (⊢ { F⊗G, a } :: (app Γ1 Γ2)) [d1;d2])
 | V_Cut d1 d2 A Γ1 Γ2 ls a1 a2 :
                            Valid d1 -> Valid d2 
                            -> Claim d1 (⊢ { A, a1}::Γ1) -> Claim d2 (⊢ { dual A, a2 }::Γ2) 
                            -> disjoint_addr_list a1 (ocontext_addr Γ1) -> disjoint_addr_list a2 (ocontext_addr Γ2)
                            -> Backedges d1 (lift ls) \/ Backedges d1 ( (1, ⊢app Γ1 Γ2) :: lift ls) 
                            -> Backedges d2 (lift ls) \/ Backedges d2 ( (1, ⊢app Γ1 Γ2) :: lift ls)
                            -> Valid (ORule ls Cut (⊢app Γ1 Γ2) [d1;d2])
 | V_Ex d F G Γ1 Γ2 ls :
                            Valid d 
                            -> Claim d (⊢ app Γ1 (G::F::Γ2)) 
                            -> Backedges d (lift ls) \/ Backedges d ( (1, ⊢app Γ1 (F::G::Γ2)) :: lift ls)
                            -> Valid (ORule ls Ex (⊢app Γ1 (F::G::Γ2)) [d])
 | V_Mu d F Γ ls a :
                            Valid d 
                            -> Claim d (⊢ { F[[ %0 := µ F ]], i::a }::Γ) 
                            -> Backedges d (lift ls) \/ Backedges d ( (1, ⊢ { (µ F), a }::Γ) :: lift ls)
                            -> Valid (ORule ls Mu (⊢ { (µ F), a }::Γ) [d])
 | V_Nu d F Γ ls a :
                            Valid d 
                            -> Claim d (⊢ {F[[ %0 := ν F ]], i::a}::Γ) 
                            -> Backedges d (lift ls) \/ Backedges d ( (1, ⊢ { (ν F), a }::Γ) :: lift ls)
                            -> Valid (ORule ls Nu (⊢ { (ν F), a }::Γ) [d])
 
 (** FINALLY, THE BACK-EDGE RULE **)
 
 | V_BackEdge ls s n: option_oseq_equiv (Some s) (list_assoc n ls)
                                                -> Valid (ORule ls (BackEdge n) s [])
 .

Hint Constructors Valid.

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
     [(⊢{ vX. X⊕X, [] })] ⊢ { (vX.X#X), [l,i] }
    ----------------------------------------------------- (⊕l)
     [(⊢{ vX. X⊕X, [] })] ⊢ { (vX.X⊕X) ⊕ (vX.X⊕X) , [i] } 
    ----------------------------------------------------- (v)
                        [] ⊢{ vX. X⊕X, [] }
    *)


Theorem thm_oexample: 
  Valid (oderiv_example').
Proof.
  constructor.
  - repeat constructor.
  - repeat constructor.
  - right; repeat constructor.
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
  apply (V_Cut _ _  (F#(~F)) [] [{ F#(~F), [r] }] _ [l] [l]); repeat constructor; intuition.
  - eapply V_Ax; intuition.
  - eapply (V_Ex _ _ _ [] []); repeat constructor.
    eapply V_Ax; intuition.
  - inversion H; try contradiction; simpl in H1; subst; inversion H0.
  - inversion H; try contradiction; simpl in H1; subst; inversion H0.
Qed.

Compute (valid_deriv (cut_example (// "X"))).


(** PRINTING FUNCTIONS *)

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
  | s::ls => s++"
  " ++ (print_list_string ls)
  end.
  
Definition print_oderiv (d:derivation) : string := print_list_string (print_oderiv_list d).

Compute print_oderiv_list oderiv_example'.





(** PROVABILITY *)

(* Sequent provable if it is the conclusion of an existing Valid derivation *)

Definition OProvable (s : osequent) :=
  exists d, Valid d /\ Claim d s.

(* OPr s => Provability without backedges *)

Inductive OPr : osequent -> Prop :=
 | R_Ax Γ A a1 a2 : In { A, a1 } Γ -> In { dual A, a2 } Γ -> OPr (⊢ Γ)
 | R_Top Γ a : In { ⊤, a } Γ -> OPr (⊢ Γ)
 | R_Bot Γ a : OPr (⊢ Γ) ->
                      OPr (⊢ { ⊥, a } :: Γ)
 | R_One a: OPr (⊢ [{ !, a }])
 | R_Or_add_l Γ F G a : OPr (⊢ { F, l::a } :: Γ) -> OPr (⊢ { F⊕G, a } :: Γ)
 | R_Or_add_r Γ F G a : OPr (⊢ { G, r::a } :: Γ) -> OPr (⊢ { F⊕G, a } :: Γ)
 | R_Or_mult Γ F G a: OPr (⊢ { F, l::a } :: { G, r::a } :: Γ) -> OPr (⊢ { F#G, a} :: Γ)
 | R_And_add Γ F G a: OPr (⊢ { F, l::a } :: Γ) -> OPr (⊢ { G, r::a } :: Γ) -> OPr (⊢ { F&G, a } :: Γ)
 | R_And_mult Γ1 Γ2 F G a: OPr (⊢ { F, l::a } :: Γ1) -> OPr (⊢ { G, r::a } :: Γ2) -> OPr (⊢ { F⊗G, a } :: (app Γ1 Γ2))
 | R_Cut A Γ1 Γ2 a1 a2: OPr (⊢ { dual A, a1 } :: Γ1) -> OPr (⊢ { A, a2 } :: Γ2) 
                                        -> disjoint_addr_list a1 (ocontext_addr Γ1)
                                        -> disjoint_addr_list a2 (ocontext_addr Γ2)
                                        -> OPr (⊢ app Γ1 Γ2)
 | R_Ex F G Γ1 Γ2 : OPr (⊢ app Γ1 (F::G::Γ2)) -> OPr (⊢ app Γ1 (G::F::Γ2))
 | R_Mu F Γ a :
      OPr (⊢ { F[[ %0 := µ F ]], i::a } :: Γ) -> OPr ((⊢ { (µ F), a }::Γ))
 | R_Nu F Γ a :
      OPr (⊢ { F[[ %0 := ν F ]], i::a } :: Γ) -> OPr ((⊢ { (ν F), a }::Γ))
  .
Hint Constructors OPr.

Theorem thm_example_bis:
  OPr (⊢[{((// "A")#(dual (// "A"))), []}]).
Proof.
  repeat constructor. apply (R_Ax _ (// "A") [l] [r]); intuition.
Qed.






(** TACTICS *)

Ltac break_step :=
 match goal with
 | H : match _ with true => _ | false => _ end = true |- _ =>
   rewrite !lazy_andb_iff in H
 | H : match claim ?x with _ => _ end = true |- _ =>
   destruct x; simpl in H; try easy
 | H : match map _ ?x with _ => _ end = true |- _ =>
   destruct x; simpl in H; try easy
 | H : match ?x with _ => _ end = true |- _ =>
   destruct x; simpl in H; try easy
 | _ => idtac
 end.
 
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
 
Ltac mytac :=
 cbn in *;
  break;
 rewrite ?andb_true_r, ?andb_true_iff, ?lazy_andb_iff in *;
 repeat match goal with H : _ /\ _ |- _ => destruct H end;
 repeat match goal with IH : Forall _ _  |- _ => inversion_clear IH end;
 rewrite ?@Utils.eqb_eq in * by auto with typeclass_instances.

Ltac rewr :=
 unfold Claim, BClosed in *;
 match goal with
 | H: _ = _ |- _ => rewrite H in *; clear H; rewr
 | _ => rewrite ?eqb_refl
 end.
 
Local Open Scope eqb_scope.

Theorem valid_deriv_is_Valid: forall (d:derivation), 
  valid_deriv d = true <-> Valid d.
Proof.
  split.
 - induction d as [ls r s ds IH] using derivation_ind'.
   cbn - [valid_deriv_step]. rewrite lazy_andb_iff. intros (H,H').
   assert (IH' : Forall (fun d => Valid d) ds).
   { rewrite Forall_forall in *. rewrite forallb_forall in *. auto. }
   clear IH H'.
   cbn in *;
   break_step; break_step; 
   try (destruct (list_assoc n ls) eqn:Heq; try discriminate H; 
   apply oseq_equiv_is_oseq_equivb in H; constructor; rewrite Heq; assumption); break.
   + destruct o0; cbn in H; simpl in H; try discriminate H; apply lazy_orb_iff in H; destruct o.
      destruct H.
      ++ apply Utils.eqb_eq in H. 
           simpl in H; subst; apply (V_Ax _ _ _ a a0); simpl; left; trivial.
      ++ apply list_mem_in_occ in H; destruct H; apply (V_Ax _ _ _ a x); trivial; simpl; right; trivial.
   + destruct H; destruct H; destruct H; destruct H; destruct H.
      apply Utils.eqb_eq in H; apply Utils.eqb_eq in H4; subst. 
      inversion_clear IH'; subst.  inversion_clear H4; subst. rewrite lazy_orb_iff in H0. destruct H0.
     ++ apply lazy_orb_iff in H1. destruct H1; 
          eapply (V_Cut _ _ F _ _ _ a); simpl; trivial; try (left; apply Utils.eqb_eq; assumption);
          try (right; apply Utils.eqb_eq; assumption); 
          rewrite disjoint_addr_list_is_disjoint_addr_listb; assumption.
     ++ apply lazy_orb_iff in H1. destruct H1; 
          eapply (V_Cut _ _ F _ _ _ a); simpl; trivial; try (left; apply Utils.eqb_eq; assumption);
          try (right; apply Utils.eqb_eq; assumption); 
          rewrite disjoint_addr_list_is_disjoint_addr_listb; assumption.
   + destruct H; apply lazy_orb_iff in H0; inversion_clear IH'; clear H2.
      destruct H; apply list_permutb_is_list_permut in H; destruct H.
      destruct H; destruct H; destruct H; destruct H; subst. constructor; simpl; trivial.
      repeat rewrite Utils.eqb_eq in H0; assumption. 
   + mytac; constructor; try assumption; apply lazy_orb_iff in H0; destruct H0; 
      try (left; apply Utils.eqb_eq; assumption); right; apply Utils.eqb_eq; assumption.
   + mytac; constructor; try assumption; apply lazy_orb_iff in H0; destruct H0; 
      try (left; apply Utils.eqb_eq; assumption); right; apply Utils.eqb_eq; assumption.
   + mytac; constructor; try assumption; apply lazy_orb_iff in H0; destruct H0; 
      try (left; apply Utils.eqb_eq; assumption); right; apply Utils.eqb_eq; assumption.
   + mytac. rewrite Utils.eqb_eq in H5; rewrite Utils.eqb_eq in H4; subst.
     eapply V_And_add; simpl; trivial.
     ++ apply lazy_orb_iff in H1; destruct H1; try (left; apply Utils.eqb_eq; assumption); 
          right; apply Utils.eqb_eq; assumption.
     ++ apply lazy_orb_iff in H0; destruct H0; try (left; apply Utils.eqb_eq; assumption); 
          right; apply Utils.eqb_eq; assumption.
   + mytac; rewrite Utils.eqb_eq in H4; rewrite Utils.eqb_eq in H3; subst.
     constructor; simpl; trivial.
     ++ apply lazy_orb_iff in H1; destruct H1; try (left; apply Utils.eqb_eq; assumption); 
          right; apply Utils.eqb_eq; assumption.
     ++ apply lazy_orb_iff in H0; destruct H0; try (left; apply Utils.eqb_eq; assumption); 
          right; apply Utils.eqb_eq; assumption.
   + apply list_mem_in_occ in H; destruct H; apply (V_Tr _ _ x); trivial. 
   + inversion IH'; subst; constructor; try assumption; destruct H. apply Utils.eqb_eq in H; assumption.
      apply lazy_orb_iff in H0. destruct H0; try (left; apply Utils.eqb_eq; assumption);
      right; apply Utils.eqb_eq; assumption.
   + inversion IH'; subst. 
      destruct H; destruct H; destruct H. econstructor; try assumption;
      simpl; apply Utils.eqb_eq in H; apply Utils.eqb_eq in H4; rewrite Utils.eqb_eq in H1; subst; trivial.
      apply lazy_orb_iff in H0; destruct H0; try (left; apply Utils.eqb_eq; assumption); 
      right; apply Utils.eqb_eq; assumption.
   + inversion IH'; subst. 
      destruct H; destruct H; destruct H. econstructor; try assumption;
      simpl; apply Utils.eqb_eq in H; apply Utils.eqb_eq in H4; rewrite Utils.eqb_eq in H1; subst; trivial.
      apply lazy_orb_iff in H0; destruct H0; try (left; apply Utils.eqb_eq; assumption); 
      right; apply Utils.eqb_eq; assumption.
- induction 1; simpl; trivial;
  try(repeat rewrite lazy_andb_iff; split; try(rewrite IHValid; trivial); split; 
      try(apply Utils.eqb_eq; trivial); apply lazy_orb_iff; rewrite Utils.eqb_eq, Utils.eqb_eq; trivial);
  try(rewrite H1; rewrite H2; repeat rewrite Utils.eqb_refl; repeat rewrite lazy_andb_iff;
         repeat rewrite lazy_orb_iff; split; try(split; repeat rewrite Utils.eqb_eq; assumption);
         rewrite IHValid1, IHValid2; trivial);
  try (rewrite H0; repeat rewrite Utils.eqb_refl; rewrite lazy_andb_iff; split; try(rewrite IHValid; trivial);
     rewrite lazy_orb_iff; repeat rewrite Utils.eqb_eq; trivial).
  + rewrite lazy_orb_false. destruct Γ; try (inversion H; reflexivity); destruct o eqn:Heq.
     apply list_mem_in_occ; exists a'; trivial.
  + rewrite lazy_orb_false; apply list_mem_in_occ; exists a; trivial.
  + rewrite H1; rewrite H2; repeat rewrite Utils.eqb_refl; 
     repeat rewrite lazy_andb_iff; repeat rewrite lazy_orb_iff; repeat rewrite lazy_andb_iff. 
     repeat split; try (apply disjoint_addr_list_is_disjoint_addr_listb); trivial;
     repeat rewrite Utils.eqb_eq; trivial; rewrite IHValid1, IHValid2; trivial.
  + rewrite H0; repeat rewrite lazy_andb_iff; repeat split.
    ++ apply list_permutb_pattern.
    ++ destruct (length (Γ1 ++ F :: G :: Γ2)) eqn:Heq.
      +++ apply length_zero_iff_nil in Heq; destruct Γ1; inversion Heq.
      +++ destruct n; trivial. destruct Γ1; simpl in Heq.
        -- discriminate Heq.
        -- injection Heq as Heq; apply length_zero_iff_nil in Heq; destruct Γ1; discriminate Heq.
    ++ apply lazy_orb_iff; repeat rewrite Utils.eqb_eq; trivial.
    ++ rewrite IHValid; trivial.
  + destruct (list_assoc n ls) eqn:Heq.
    ++ destruct (list_assoc_get_Some n ls o); try assumption; rewrite lazy_orb_false; 
          apply oseq_equiv_is_oseq_equivb; trivial.
    ++ destruct (list_assoc_get_None n ls); try assumption. inversion H.
Qed.


