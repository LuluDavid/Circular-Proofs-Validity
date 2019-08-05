Require Import Defs.
Require Import StringUtils.
Require DecimalString.
Import ListNotations.
Require Import Arith.
Import Bool.
Require Import Defs Debruijn Occurrences Address.
Local Open Scope list_scope.
Local Open Scope eqb_scope.

(** UP TO THIS POINT, EVERYTHING IS WELL DEFINED **)

(* A Fixpoint for validity. Complicated to describe the exchange rule because we require a boolean  
  permutation indicator for two lists. *)

Fixpoint InOb (s : osequent) (l : list osequent) : bool :=
    match l with
       | [] => false
       | s' :: m => (s' =? s) || (InOb s m)
     end.

Fixpoint InOb' (s : Occurrence) (l : ocontext) : bool :=
    match l with
       | [] => false
       | s' :: m => (s' =? s) || (InOb' s m)
     end.

Definition ovalid_deriv_step '(ORule ls R s ld) :=
  match ls, R, s, List.map oclaim ld with
  | _, Ax,    (⊢ [A;A']), _ => equivb A' (occ_dual A) (* Nouvelle règle d'axiome *)
  | _, TopR,  (⊢ {⊤, _}::Γ ), _ => true 
  | _, OneR,  (⊢ [{! ,_}]), _ => true
  | _, BotR,  (⊢ {⊥, _}::Γ), [s] => s =? (⊢ Γ)
  | _, Or_add_l, (⊢ {(F⊕G), a}::Γ), [s] => s =? (⊢ {F, (l::a)}::Γ)
  |  _, Or_add_r, (⊢ {(F⊕G), a}::Γ), [s] => s =? (⊢ {G, (r::a)}::Γ)
  | _, Or_mult,  (⊢ {(F#G),a}::Γ), [s] => s =? (⊢{F, (l::a)}::{G, (r::a)}::Γ)
  | _, And_add,  (⊢ {(F&G),a}::Γ), [(⊢ {F',a1}::Γ1);(⊢ {G',a2}::Γ2)] 
                            => (F =? F') &&& (G =? G') &&& (a1 =? l::a) &&& (a2 =? r::a) &&& (Γ1 =? Γ) &&& (Γ2 =? Γ)
  | _, And_mult,  (⊢ {(F⊗G),a}::Γ), [(⊢ {F',a1}::Γ1);(⊢ {G',a2}::Γ2)] 
                            => (F =? F') &&& (G =? G') &&& (a1 =? l::a) &&& (a2 =? r::a) &&& ((app Γ1 Γ2) =? Γ)
  | _, Cut,   (⊢  Γ), [(⊢ A:: Γ1);(⊢ B:: Γ2)] 
                            => ( Γ =? Γ1 ++  Γ2 ) &&& (B =? (occ_dual A))  
                                  &&& disjoint_addr_listb (occ_addr A)(ocontext_addr Γ1)
                                  &&& disjoint_addr_listb (occ_addr B)(ocontext_addr Γ2)
  | _, Ex,  (⊢ Γ), [(⊢F::Γ')] => (InOb' F Γ) (* &&& list_equivb Γ (F::Γ') *)
  (* To be precised: exists i such as insert F at ith position in Γ' = Γ *)
  | _, Mu, (⊢ {($ F),a}::Γ), [(⊢{G,a'}::Γ')] => (G =? bsubst 0 ($ F) F) &&& (Γ =? Γ') &&& (a' =? i::a)
  | _, Nu, (⊢ {(€ F),a}::Γ), [(⊢{G,a'}::Γ')] => (G =? bsubst 0 (€ F) F) &&& (Γ =? Γ') &&& (a' =? i::a)
  | ls, BackEdge s', s, _ => (InOb s' ls) &&& (oseq_equivb s s') (* s' =? renommage s ???*)
  | _,_,_,_ => false
  end.


Fixpoint ovalid_deriv d :=
  ovalid_deriv_step d &&&
   (let '(ORule _ _ _ ld) := d in
    List.forallb (ovalid_deriv) ld).

Local Open Scope string_scope.

Definition oderiv_example :=
  ORule [] Or_mult (⊢[{ (@"A"#(dual (@"A"))), [r] }]) [ORule [] Ax (⊢[{ @"A", [l;r] }; {dual (@"A"), [r;r]}]) []].
 Print deriv_example.
Compute 
  obsubst 0 ({@"B", []})%form oderiv_example.
  
  
 (*
  ----------------------------------------------------- (Ax)
                      [] ⊢{ @A, [l] } ,{ ¬@A, [r] } 
  ----------------------------------------------------- (#)
                      [] ⊢{ (@A#¬@A), [] }
  *)
  
Compute ovalid_deriv oderiv_example.
(** Some examples of derivations *)

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
  let '(ORule ls R s' ds) := d in (ORule (s::ls) R s' ds).

(* osequent s in ls up to renaming 
    Necessary to define renamings aside in Renaming.v => maybe not because our addresses are already 
    disjoint by construction.
    Or just say that there exists a sequent s' in ls containing all the FORMULAS of the current sequent s
    with different addresses ?
*)



(* There is a sequent in [ls] with the same formulas than [s] up to renaming *)

Inductive InUpTR : osequent -> list osequent -> Prop :=
  | UpTR (s s':osequent)(ls:list osequent): 
    In s' ls 
    -> (forall (o:Occurrence), In_oseq o s -> exists (o':Occurrence), (In_oseq o' s') /\ equiv o o') 
    -> InUpTR s ls
.

Fixpoint InUpTRb (s:osequent)(ls:list osequent): bool :=
  match ls with
  | [] => false
  | s'::ls' => (oseq_equivb s s') || (InUpTRb s ls') 
  end.

Lemma InUpTR_is_InUpTRb : forall s ls,
  InUpTR s ls <-> InUpTRb s ls = true.
Proof.
Admitted.

(* Returns the sequent equal to s up to renaming, if not found, returns the empty sequent 
    (the only unbackedgeable sequent) *) 
Fixpoint UpTRSeq (s:osequent)(ls:list osequent): osequent :=
  match ls with
  | [] => (⊢ [])
  | s'::ls' => match (oseq_equivb s s') with
                   | true => s'
                   | false => (UpTRSeq s' ls') 
                   end
  end.


Inductive OValid : oderivation -> Prop :=

  (** THE "UNKEEPING" VERSION OF THE RULES **) 
  
 | V_Ax Γ A ls a a': In {A, a} Γ 
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
                            -> OClaim d1 (⊢ { dual A, a1}::Γ1) -> OClaim d2 (⊢ { A, a2 }::Γ2) 
                            -> disjoint_addr_list a1 (ocontext_addr Γ1) -> disjoint_addr_list a2 (ocontext_addr Γ2)
                            -> OValid (ORule ls Cut (⊢app Γ1 Γ2) [d1;d2])
 | V_Ex d F G Γ1 Γ2 ls :
                            OValid d 
                            -> OClaim d (⊢ app Γ1 (G::F::Γ2)) 
                            -> OValid (ORule ls Ex (⊢app Γ1 (F::G::Γ2)) [d])
 | V_Mu d F Γ ls a :
                            OValid d 
                            -> OClaim d (⊢ { bsubst 0 ($ F) F, i::a }::Γ) 
                            -> OValid (ORule ls Mu (⊢ { ($ F), a }::Γ) [d])
 | V_Nu d F Γ ls a :
                            OValid d 
                            -> OClaim d (⊢ { bsubst 0 (€ F) F, i::a}::Γ) 
                            -> OValid (ORule ls Nu (⊢ { (€ F), a }::Γ) [d])
                      
 (** THE "KEEPING" VERSION OF THE RULES **)
 
 | V_Bot' d Γ ls a: OValid d
                                ->  OClaim d (⊢Γ) 
                                -> Backedges d ((⊢{⊥, a}::Γ) :: ls)
                                -> OValid (ORule ls BotR (⊢{⊥, a}::Γ) [d])
  | V_Or_add_l' d F G Γ a ls: 
                             OValid d 
                             -> OClaim d (⊢{F,l::a}::Γ) 
                             -> Backedges d ((⊢{ F⊕G, a }::Γ) :: ls)
                             -> OValid (ORule ls Or_add_l (⊢{ F⊕G, a }::Γ) [d])
 | V_Or_add_r' d F G Γ a ls: 
                             OValid d 
                             -> OClaim d (⊢{G,r::a}::Γ) 
                             -> Backedges d ((⊢{ F⊕G, a }::Γ) :: ls)
                             -> OValid (ORule ls Or_add_l (⊢{ F⊕G, a }::Γ) [d])
 | V_Or_mult' d F G Γ a ls :
                            OValid d
                            -> OClaim d (⊢{ F, l::a } :: { G, r::a } :: Γ) 
                            -> Backedges d ((⊢{ F#G, a }::Γ) :: ls)
                            -> OValid (ORule ls Or_mult (⊢ { F#G, a}::Γ) [d])
 | V_And_add' d1 d2 F G Γ a ls :
                            OValid d1 -> OValid d2 
                            -> OClaim d1 (⊢ { F, l::a }::Γ) -> OClaim d2 (⊢ { G, r::a }::Γ) 
                            -> Backedges d1 ((⊢{ F&G, a }::Γ) :: ls)
                            -> Backedges d2 ((⊢{ F&G, a }::Γ) :: ls)
                            -> OValid (ORule ls And_add (⊢ { F&G, a } :: Γ) [d1;d2])
 | V_And_mult' d1 d2 F G Γ1 Γ2 a ls :
                            OValid d1 -> OValid d2 
                            -> OClaim d1 (⊢ { F, l::a } :: Γ1) -> OClaim d2 (⊢ { G, r::a } :: Γ2) 
                            -> Backedges d1 ((⊢{ F⊗G, a }::(app Γ1 Γ2)) :: ls)
                            -> Backedges d2 ((⊢{ F⊗G, a }::(app Γ1 Γ2)) :: ls)
                            -> OValid (ORule ls And_mult (⊢ { F⊗G, a } :: (app Γ1 Γ2)) [d1;d2])
 | V_Cut' d1 d2 A Γ1 Γ2 ls a1 a2 :
                            OValid d1 -> OValid d2 
                             -> OClaim d1 (⊢ { dual A, a1}::Γ1) -> OClaim d2 (⊢ { A, a2 }::Γ2) 
                             -> disjoint_addr_list a1 (ocontext_addr Γ1) -> disjoint_addr_list a2 (ocontext_addr Γ2)
                             -> Backedges d1 ((⊢app Γ1 Γ2) :: ls)
                            -> Backedges d2 ((⊢app Γ1 Γ2) :: ls)
                             -> OValid (ORule ls Cut (⊢app Γ1 Γ2) [d1;d2])
 | V_Ex' d F G Γ1 Γ2 ls :
                            OValid d 
                            -> OClaim d (⊢ app Γ1 (G::F::Γ2)) 
                            -> Backedges d ((⊢app Γ1 (F::G::Γ2)) :: ls)
                            -> OValid (ORule ls Ex (⊢app Γ1 (F::G::Γ2)) [d])
                            (* Is it pre-valid to switch twice and back-edge ? 
                            (thus no risk once the validity criteria introduced) *)
 | V_Mu' d F Γ ls a :
                           OValid d 
                           -> OClaim d (⊢ { bsubst 0 ($ F) F, i::a }::Γ)
                           -> Backedges d ((⊢ { ($ F), a }::Γ) :: ls)
                           -> OValid (ORule ls Mu (⊢ { ($ F), a }::Γ) [d])
 | V_Nu' d F Γ ls a :
                           OValid d 
                           -> OClaim d (⊢ { bsubst 0 (€ F) F, i::a }::Γ)
                           -> Backedges d ((⊢ { (€ F), a }::Γ) :: ls)
                           -> OValid (ORule ls Mu (⊢ { (€ F), a }::Γ) [d])
 
 (** FINALLY, THE BACK-EDGE RULE **)
 
 | V_BackEdge ls s s': s' = UpTRSeq s ls -> s' <> (⊢ [])
                                  -> OValid (ORule ls (BackEdge (s')) s [])
 .

Hint Constructors OValid.

Definition oderiv_example' :=
ORule [] Nu (⊢ [{ (€ (%0)⊕(%0)), [] }]) 
          [
          (
          ORule [(⊢ [{ (€ (%0)⊕(%0)), [] }])] Or_add_l (⊢ [ { ((€ (%0)⊕(%0)) ⊕ (€ (%0)⊕(%0))), [i] } ] )
            [
            (
            ORule [(⊢ [{ (€ (%0)⊕(%0)), [] }])] (BackEdge (⊢ [{ (€ (%0)⊕(%0)), [] }])) (⊢ [ { € (%0)⊕(%0), [l;i] } ] ) []
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
  repeat constructor; unfold not; intros; discriminate H.
Qed.

Definition context_example := [(€ (%0)⊕(%0))%form; ($ (%1)#(%0))%form].
Compute (print_ctx context_example).

Definition sequent_example := Seq context_example.
Compute (print_seq sequent_example).

Fixpoint print_list_oseq (ls:list osequent) :=
  match ls with
  | [] => ""
  | s::ls => (print_oseq s)
  end.

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

Compute print_deriv_list deriv_example'.
Hint Constructors Valid.

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
      OPr (⊢ { bsubst 0 ($ F) F, i::a } :: Γ) -> OPr ((⊢ { ($ F), a }::Γ))
 | R_Nu F Γ a :
      OPr (⊢ { bsubst 0 (€ F) F, i::a } :: Γ) -> OPr ((⊢ { (€ F), a }::Γ))
  .
Hint Constructors OPr.

Theorem thm_example_bis:
  OPr (⊢[{((@ "A")#(dual (@ "A"))), []}]).
Proof.
  repeat constructor. apply (R_Ax _ (@ "A") [l] [r]); intuition.
Qed.

(* We just built the Trees for pre-circular derivations, and their pre-validity with the property
    OValid. We would like now to prove their validity, but we would first have to introduce paths and
    traces, thus we have to define infinite structure.
    - build infinite derivations with circular ones defining unfolding 
    - define a trace on a circular proof as a thread on its unfolding
    - define Inf(t) for t a thread or a trace
    - characterize the min of Inf(t)
    - give the validity criteria
    *)































    