Require Import Utils Defs Debruijn Occurrences Address.
Require Import StringUtils Datatypes.
Require DecimalString.
Import ListNotations.
Require Import Arith.
Import Bool.

(** UP TO THIS POINT, EVERYTHING IS WELL DEFINED **)

(* Return the optional derivation rooted at node of address a *)

Fixpoint subderiv (d:oderivation)(a:address): option oderivation :=
  let '(ORule ls R s ld) := d in
  match a, ld with
  | [], _               => Some d
  | i::a', [d']        => subderiv d' a'  
  | l::a', [d1;d2] => subderiv d1 a'
  | r::a', [d1;d2] => subderiv d2 a'
  | _, _ => None
  end.

Definition is_subderiv (d1 d2: oderivation): Prop := exists a, subderiv d2 a = Some d1. 
Local Open Scope string_scope.

Definition Subderiv_example: oderivation := 
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

(* Boolean versions of In *)

Fixpoint InOSequent (s : osequent) (l : list osequent) : bool :=
    match l with
       | [] => false
       | s' :: m => (s' =? s) || (InOSequent s m)
     end.

Fixpoint InOSequent' (s : Occurrence) (l : ocontext) : bool :=
    match l with
       | [] => false
       | s' :: m => (s' =? s) || (InOSequent' s m)
     end.

(* Same lists with 2 switched occurrences for the exchange rule *)

Fixpoint list_permut (l1 l2: list Occurrence): bool :=
  match l1, l2 with
  | [], [] => true
  | (x1::l1'), (x2::l2') => if (x1 =? x2) then (list_permut l1' l2')
                                     else match l1', l2' with
                                             | [], [] => false
                                             | (x1'::l1''), (x2'::l2'') => (x1 =? x2') &&& (x1' =? x2) &&& (l1'' =? l2'')
                                             | _, _ => false
                                             end 
  | _, _ => false
  end.

(* Get, Lift and Eqb for the list of backedgeables sequents *)

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

Instance ls_eqb : Eqb (nat*osequent) :=
  fix ls_eqb ls1 ls2 :=
    let (n1, s1) := ls1 in (let (n2, s2) := ls2 in (n1 =? n2) && (s1 =? s2)).

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

(* Boolean version of valid inference structure for one step *)

Definition ovalid_deriv_step '(ORule ls R s ld) :=
  match ls, R, s, List.map oclaim ld, List.map backedges ld with
  | ls1, Ax, (⊢ A::A'::Γ ), [], _                => equivb A' (occ_dual A)
  | _, TopR,  (⊢ {⊤, _}::Γ ), [], _           => true 
  | _, OneR,  (⊢ [{! ,_}]), [], _               => true
  | ls1, BotR,  (⊢ {⊥, _}::Γ), [s], [ls2]  => (s =? (⊢ Γ)) 
                                                                       &&& 
                                                                  ((ls2 =? (lift ls1)) ||| (ls2 =? (1, s):: (lift ls1)))

  | ls1, Or_add_l, (⊢ {(F⊕G), a}::Γ), [s], [ls2] 
                                                            => (s =? (⊢ {F, (l::a)}::Γ)) 
                                                                      &&& 
                                                                 ((ls2 =? (lift ls1)) ||| (ls2 =? (1, s) :: (lift ls1)))

  | ls1, Or_add_r, (⊢ { F⊕G, a }::Γ), [s], [ls2] 
                                                            => (s =? (⊢ {G, (r::a)}::Γ))  
                                                                      &&& 
                                                                 ((ls2 =? (lift ls1)) ||| (ls2 =? (1, s) :: (lift ls1)))

  | ls1, Or_mult,  (⊢ { F#G, a }::Γ), [s], [ls2] 
                                                            => (s =? (⊢{F, (l::a)}::{G, (r::a)}::Γ)) 
                                                                     &&& 
                                                                ((ls2 =? (lift ls1)) ||| (ls2 =? (1, s) :: (lift ls1)))

  | ls1, And_add,  (⊢ { F&G, a }::Γ), [(⊢ {F',a1}::Γ1);(⊢ {G',a2}::Γ2)], [ls2;ls3] 
                                                          => (F =? F') &&& (G =? G') 
                                                                              &&& (a1 =? l::a) &&& (a2 =? r::a) 
                                                                              &&& (Γ1 =? Γ) &&& (Γ2 =? Γ) 
                                                                              &&& ((ls2 =? (lift ls1)) ||| (ls2 =? ((0, s) :: (lift ls1))))
                                                                              &&& ((ls3 =? (lift ls1)) ||| (ls3 =? ((0, s) :: (lift ls1))))

  | ls1, And_mult,  (⊢ { F⊗G, a }::Γ), [(⊢ {F',a1}::Γ1);(⊢ {G',a2}::Γ2)], [ls2;ls3]
                                                          => (F =? F') &&& (G =? G') 
                                                                              &&& (a1 =? l::a) &&& (a2 =? r::a) 
                                                                              &&& ((app Γ1 Γ2) =? Γ) 
                                                                              &&& ((ls2 =? (lift ls1)) ||| (ls2 =? ((0, s) :: (lift ls1))))
                                                                              &&& ((ls3 =? (lift ls1)) ||| (ls3 =? ((0, s) :: (lift ls1))))

  | ls1, Cut,   (⊢  Γ), [(⊢ A:: Γ1);(⊢ B:: Γ2)], [ls2;ls3]
                                                          => ( Γ =? Γ1 ++  Γ2 ) &&& (B =? (occ_dual A))  
                                                                                            &&& disjoint_addr_listb (occ_addr A)(ocontext_addr Γ1)
                                                                                            &&& disjoint_addr_listb (occ_addr B)(ocontext_addr Γ2)
                                                                                            &&& (((ls2 =? (lift ls1)) &&& (ls3 =? (lift ls1))) |||
                                                                                            (((ls2 =? ((0, s) :: (lift ls1))) &&& (ls3 =? ((0, s) :: (lift ls1))))))

  | ls1, Ex,  (⊢ Γ), [(⊢Γ')], [ls2]         => (list_permut Γ Γ') 
                                                                      &&& 
                                                              ((ls2 =? (lift ls1)) ||| (ls2 =? ((0, s) :: (lift ls1))))

  | ls1, Mu, (⊢ { µ F, a }::Γ), [(⊢{G,a'}::Γ')], [ls2] 
                                                        => (G =? (F[[ %0 := µ F ]]) ) &&& (Γ =? Γ') &&& (a' =? i::a)
                                                                                        &&& 
                                                             ((ls2 =? (lift ls1)) ||| (ls2 =? (0, s) :: (lift ls1)))

  | ls1, Nu, (⊢ { ν F, a }::Γ), [(⊢{G,a'}::Γ')], [ls2] 
                                                       => (G =? (F[[ %0 := ν F ]])) &&& (Γ =? Γ') &&& (a' =? i::a)
                                                                                        &&& 
                                                            ((ls2 =? (lift ls1)) ||| (ls2 =? (0, s) :: (lift ls1)))

  | ls, BackEdge n, s, [], _ => match list_assoc n ls with
                                                | None => false
                                                | Some s' => oseq_equivb s s'
                                                end
  | _,_,_,_,_ => false
  end.

Fixpoint ovalid_deriv d :=
  ovalid_deriv_step d &&&
   (let '(ORule _ _ _ ld) := d in
    List.forallb (ovalid_deriv) ld).

Compute ovalid_deriv_step Subderiv_example.

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

Lemma oderivation_ind'' (P: oderivation -> Prop) :
  (forall d d', is_subderiv d' d -> d <> d' -> P d') ->
  forall d, P d.
Proof.
Admitted.
  
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
  
Compute ovalid_deriv oderiv_example.

(** 
Claim d s => d's conclusion sequent is s. It means:

                                                                                                 .
                                                                                                 .
                                                                                                 .
                                                                                                d
                                                                                          -------------
                                                                                                s
 *)

(* Adds the sequent s in the list of back-edgeable sequents of derivation d *)
Definition app_oderiv (s:osequent) (d:oderivation) := 
  let '(ORule ls R s' ds) := d in (ORule ((1, s)::ls) R s' ds).

Local Open Scope eqb_scope.

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


Local Open Scope nat_scope.
 
Inductive OValid : oderivation -> Prop :=

  (** THE "UNKEEPING" VERSION OF THE RULES **) 
  
 | V_Ax_Var Γ v ls: 2 <= count_occ' Γ (Var v)
                                 -> OValid (ORule ls Ax (⊢ Γ) [])
 | V_Ax Γ A ls a a': A <> dual A 
                                -> In {A, a} Γ 
                                -> In { dual A, a' } Γ
                                -> OValid (ORule ls Ax (⊢ Γ) [])
 | V_Tr Γ ls a: In {⊤, a} Γ 
                       -> OValid (ORule ls TopR (⊢ Γ) [])
 | V_One ls a: OValid (ORule ls OneR (⊢ [{!%form, a}]) [])
 | V_Bot d Γ ls a: OValid d 
                             -> OClaim d (⊢Γ) 
                             -> OValid (ORule ls BotR (⊢{⊥, a}::Γ) [d])
 | V_Or_add_l d F G Γ a ls: 
                            OValid d 
                            -> OClaim d (⊢{F,l::a}::Γ) 
                            -> OValid (ORule ls Or_add_l (⊢{ F⊕G, a }::Γ) [d])
 | V_Or_add_r d F G Γ a ls  : 
                            OValid d 
                            -> OClaim d (⊢{G,r::a}::Γ)
                            -> OValid (ORule ls Or_add_r (⊢{ F⊕G, a }::Γ) [d])
 | V_Or_mult d F G Γ a ls :
                            OValid d 
                            -> OClaim d (⊢{ F, l::a } :: { G, r::a } :: Γ) 
                            -> OValid (ORule ls Or_mult (⊢ { F#G, a}::Γ) [d])
 | V_And_add d1 d2 F G Γ a ls :
                            OValid d1 -> OValid d2 
                            -> OClaim d1 (⊢ { F, l::a }::Γ) -> OClaim d2 (⊢ { G, r::a }::Γ) 
                            -> OValid (ORule ls And_add (⊢ { F&G, a } :: Γ) [d1;d2])
 | V_And_mult d1 d2 F G Γ1 Γ2 a ls :
                            OValid d1 -> OValid d2 
                            -> OClaim d1 (⊢ { F, l::a } :: Γ1) -> OClaim d2 (⊢ { G, r::a } :: Γ2) 
                            -> OValid (ORule ls And_mult (⊢ { F⊗G, a } :: (app Γ1 Γ2)) [d1;d2])
 | V_Cut d1 d2 A Γ1 Γ2 ls a1 a2 :
                            OValid d1 -> OValid d2 
                            -> OClaim d1 (⊢ { A, a1}::Γ1) -> OClaim d2 (⊢ { dual A, a2 }::Γ2) 
                            -> disjoint_addr_list a1 (ocontext_addr Γ1) -> disjoint_addr_list a2 (ocontext_addr Γ2)
                            -> OValid (ORule ls Cut (⊢app Γ1 Γ2) [d1;d2])
 | V_Ex d F G Γ1 Γ2 ls :
                            OValid d 
                            -> OClaim d (⊢ app Γ1 (G::F::Γ2)) 
                            -> OValid (ORule ls Ex (⊢app Γ1 (F::G::Γ2)) [d])
 | V_Mu d F Γ ls a :
                            OValid d 
                            -> OClaim d (⊢ { F[[ %0 := µ F ]], i::a }::Γ) 
                            -> OValid (ORule ls Mu (⊢ { (µ F), a }::Γ) [d])
 | V_Nu d F Γ ls a :
                            OValid d 
                            -> OClaim d (⊢ {F[[ %0 := ν F ]], i::a}::Γ) 
                            -> OValid (ORule ls Nu (⊢ { (ν F), a }::Γ) [d])
                      
 (** THE "KEEPING" VERSION OF THE RULES **)
 
 | V_Bot' d Γ ls a: OValid d
                                ->  OClaim d (⊢Γ) 
                                -> Backedges d ( (0, ⊢{⊥, a}::Γ) :: lift ls)
                                -> OValid (ORule ls BotR (⊢{⊥, a}::Γ) [d])
  | V_Or_add_l' d F G Γ a ls: 
                             OValid d 
                             -> OClaim d (⊢{F,l::a}::Γ) 
                             -> Backedges d ( (0, ⊢{ F⊕G, a }::Γ) :: lift ls)
                             -> OValid (ORule ls Or_add_l (⊢{ F⊕G, a }::Γ) [d])
 | V_Or_add_r' d F G Γ a ls: 
                             OValid d 
                             -> OClaim d (⊢{G,r::a}::Γ) 
                             -> Backedges d ( (0, ⊢{ F⊕G, a }::Γ) :: lift ls)
                             -> OValid (ORule ls Or_add_l (⊢{ F⊕G, a }::Γ) [d])
 | V_Or_mult' d F G Γ a ls :
                            OValid d
                            -> OClaim d (⊢{ F, l::a } :: { G, r::a } :: Γ) 
                            -> Backedges d ( (0, ⊢{ F#G, a }::Γ) :: lift ls)
                            -> OValid (ORule ls Or_mult (⊢ { F#G, a}::Γ) [d])
 | V_And_add' d1 d2 F G Γ a ls :
                            OValid d1 -> OValid d2 
                            -> OClaim d1 (⊢ { F, l::a }::Γ) -> OClaim d2 (⊢ { G, r::a }::Γ) 
                            -> Backedges d1 ( (0, ⊢{ F&G, a }::Γ) :: lift ls)
                            -> Backedges d2 ( (0, ⊢{ F&G, a }::Γ) :: lift ls)
                            -> OValid (ORule ls And_add (⊢ { F&G, a } :: Γ) [d1;d2])
 | V_And_mult' d1 d2 F G Γ1 Γ2 a ls :
                            OValid d1 -> OValid d2 
                            -> OClaim d1 (⊢ { F, l::a } :: Γ1) -> OClaim d2 (⊢ { G, r::a } :: Γ2) 
                            -> Backedges d1 ( (0, ⊢{ F⊗G, a }::(app Γ1 Γ2)) :: lift ls)
                            -> Backedges d2 ( (0, ⊢{ F⊗G, a }::(app Γ1 Γ2)) :: lift ls)
                            -> OValid (ORule ls And_mult (⊢ { F⊗G, a } :: (app Γ1 Γ2)) [d1;d2])
 | V_Cut' d1 d2 A Γ1 Γ2 ls a1 a2 :
                            OValid d1 -> OValid d2 
                             -> OClaim d1 (⊢ { A, a1}::Γ1) -> OClaim d2 (⊢ { dual A, a2 }::Γ2) 
                             -> disjoint_addr_list a1 (ocontext_addr Γ1) -> disjoint_addr_list a2 (ocontext_addr Γ2)
                             -> Backedges d1 ( (0, ⊢app Γ1 Γ2) :: lift ls) 
                            -> Backedges d2 ( (0, ⊢app Γ1 Γ2) :: lift ls)
                             -> OValid (ORule ls Cut (⊢app Γ1 Γ2) [d1;d2])
 | V_Ex' d F G Γ1 Γ2 ls :
                            OValid d 
                            -> OClaim d (⊢ app Γ1 (G::F::Γ2)) 
                            -> Backedges d ( (0, ⊢app Γ1 (F::G::Γ2)) :: lift ls)
                            -> OValid (ORule ls Ex (⊢app Γ1 (F::G::Γ2)) [d])
 | V_Mu' d F Γ ls a :
                           OValid d 
                           -> OClaim d (⊢ { F[[ %0 := µ F ]], i::a }::Γ)
                           -> Backedges d ( (0, ⊢ { (µ F), a }::Γ) :: lift ls)
                           -> OValid (ORule ls Mu (⊢ { (µ F), a }::Γ) [d])
 | V_Nu' d F Γ ls a :
                           OValid d 
                           -> OClaim d (⊢ { F[[ %0 := ν F ]], i::a }::Γ)
                           -> Backedges d ( (0, ⊢ { (ν F), a }::Γ) :: lift ls)
                           -> OValid (ORule ls Mu (⊢ { (ν F), a }::Γ) [d])
 
 (** FINALLY, THE BACK-EDGE RULE **)
 
 | V_BackEdge ls s n: oseq_equiv s (get n ls)
                                                         -> OValid (ORule ls (BackEdge n) s [])
 .

Hint Constructors OValid.

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
Compute level oderiv_example'.

Theorem thm_oexample: 
  OValid (oderiv_example').
Proof.
  repeat constructor.
Qed.

(* A few printing functions *)

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

Fixpoint print_oderiv_list (d:oderivation): list string :=
  let '(ORule ls R s ds) := d in
  concat (map print_oderiv_list ds) ++ 
  [string_mult "-" (String.length (print_list_oseq ls ++ print_oseq s)) ++ print_orule R; 
  print_list_oseq ls ++ print_oseq s].

Fixpoint print_list_string (l:list string): string :=
  match l with
  | [] => ""
  | s::ls => s++"
  " ++ (print_list_string ls)
  end.
  
Definition print_oderiv (d:oderivation) : string := print_list_string (print_oderiv_list d).

Compute print_oderiv_list oderiv_example'.





(* Sequent provable if it is the conclusion of an existing Valid derivation *)

Definition OProvable (s : osequent) :=
  exists d, OValid d /\ OClaim d s.

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

Ltac break :=
 match goal with
 | H : match _ with true => _ | false => _ end = true |- _ =>
   rewrite !lazy_andb_iff in H
 | H : match oclaim ?x with _ => _ end = true |- _ =>
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
 unfold OClaim, BClosed in *;
 match goal with
 | H: _ = _ |- _ => rewrite H in *; clear H; rewr
 | _ => rewrite ?eqb_refl
 end.
 
Local Open Scope eqb_scope.

Theorem ovalid_deriv_is_OValid: forall (d:oderivation), 
  ovalid_deriv d = true <-> OValid d.
Proof.
  split.
 - induction d as [ls r s ds IH] using oderivation_ind'.
   cbn - [ovalid_deriv_step]. rewrite lazy_andb_iff. intros (H,H').
   assert (IH' : Forall (fun d => OValid d) ds).
   { rewrite Forall_forall in *. rewrite forallb_forall in *. auto. }
   clear IH H'.
   cbn in *; break.
   + destruct o; destruct o0; cbn in H; simpl in H; apply Utils.eqb_eq in H;
      destruct F; try(subst; eapply V_Ax; intuition; discriminate H).
      ++ subst; apply (V_Ax_Var _ v); simpl; rewrite Utils.eqb_refl;
           omega.
      ++ apply (V_Ax _ (Op o F1 F2) _ a a0).
        +++ apply op_dual.
        +++ left; trivial.
        +++ subst; right; left; trivial.
     ++ apply (V_Ax _ (Quant q F) _ a a0).
       +++ apply quant_dual.
       +++ left; trivial.
       +++ subst; right; left; trivial. 
  + repeat destruct H. destruct (o =? (o2 ++ o5)%list) eqn:Heq.
     ++ apply Utils.eqb_eq in Heq; apply Utils.eqb_eq in H3; subst. 
          inversion_clear IH'; subst.  inversion_clear H3; subst. rewrite lazy_orb_iff in H0. destruct H0.
        +++ apply lazy_andb_iff in H0. destruct H0. destruct o1. 
               eapply (V_Cut _ _ F _ _ _ a); try eassumption; simpl; trivial;
               rewrite disjoint_addr_list_is_disjoint_addr_listb; assumption.
        +++ apply lazy_andb_iff in H0. destruct H0. destruct o1. 
               eapply (V_Cut' _ _ F _ _ _ a); try eassumption; simpl; trivial;
               try (rewrite disjoint_addr_list_is_disjoint_addr_listb; assumption);
               apply Utils.eqb_eq; assumption.
     ++ admit.
  + admit.
  + mytac; constructor; try assumption.
  + mytac; constructor; try assumption.
  + mytac; constructor; try assumption.
  + mytac. rewrite Utils.eqb_eq in H5; rewrite Utils.eqb_eq in H4; subst.
     eapply V_And_add; simpl; trivial.
  + mytac; rewrite Utils.eqb_eq in H4; rewrite Utils.eqb_eq in H3; subst.
    constructor; simpl; trivial.
  + econstructor; intuition.
  + inversion IH'; subst; constructor; try assumption; destruct H; apply Utils.eqb_eq in H; assumption.
  + inversion IH'; subst; repeat destruct H; econstructor; try assumption;
     simpl; destruct (F0 =? (F [[ % 0 := µ F]])) eqn:Heq.
     -- rewrite Utils.eqb_eq in Heq; rewrite Utils.eqb_eq in H4; rewrite Utils.eqb_eq in H1; subst; trivial.
     -- admit.
  + inversion IH'; subst; repeat destruct H; econstructor; try assumption;
     simpl; destruct (F0 =? (F [[ % 0 := ν F]])) eqn:Heq.
     -- rewrite Utils.eqb_eq in Heq; rewrite Utils.eqb_eq in H4; rewrite Utils.eqb_eq in H1; subst; trivial.
     -- admit.
  + apply oseq_equiv_is_oseq_equivb in H. constructor; simpl. admit.
- induction 1; simpl; rewr; auto; admit.
Admitted.

Lemma OValid_subderiv:
  forall d1 d2, OValid d1 -> is_subderiv d2 d1 -> OValid d2.
Proof.
Admitted.










