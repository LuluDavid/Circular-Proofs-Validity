Require Import Defs StringUtils.
Require DecimalString.
Import ListNotations.
Require Import Arith.
Import Bool.
Local Open Scope string_scope.
Local Open Scope eqb_scope.

Inductive allowed_chars : Type := l | r | i.
Definition address : Type := list allowed_chars. 
(* For a matter of complexity, we will work here with reversed order addresses *)

Fixpoint print_address (a:address) := 
  match a with
  | [] => ""
  | l::a' => "l" ++ (print_address a')
  | r::a' => "r" ++ (print_address a')
  | i::a' => "i" ++ (print_address a')
  end.
  
Instance chars_eqb : Eqb allowed_chars :=
 fix chars_eqb c c' :=
 match c, c' with
 | l, l => true
 | r, r => true
 | i, i => true
 | _, _ => false
 end.

Instance : EqbSpec allowed_chars.
Proof.
red; intros; destruct x; destruct y; try cons. 
Qed.

Delimit Scope chars_scope with ac.
Bind Scope chars_scope with allowed_chars.

Fixpoint addr_dual (a:address): address :=
  match a with
  | [] => []
  | l :: a' => r :: (addr_dual a')
  | r :: a' => l :: (addr_dual a')
  | i :: a' => i :: (addr_dual a')
  end.

Lemma addr_dual_inj: forall a, addr_dual(addr_dual a) = a.
Proof.
  intros. induction a; trivial.
  induction a0.
  - destruct a; trivial.
  - destruct a; destruct a0;
    assert (Hloc: forall c c', addr_dual (addr_dual (c :: c' :: a1)) = c :: addr_dual (addr_dual (c' :: a1)));
       try rewrite Hloc, IHa; trivial; destruct c; destruct c'; try reflexivity.
Qed.


(** BASIC PROPERTIES ON ADDRESSES **)

(* a sub-adress of a'
   CARREFUL: Prefix becomes Suffix here because we reversed the address order
 *)
 
Local Open Scope list_scope.

(* Inductive sub_address_rev: address -> address -> Prop :=
  | SRevEmpty (a': address) : sub_address_rev [] a'
  | SRevCons (c:allowed_chars)(a a':address) : sub_address_rev a a' -> sub_address_rev (c::a) (c::a')
  .

Definition sub_address (a a': address) := sub_address_rev (rev a)(rev a'). *)
  
  
Inductive sub_address: address -> address -> Prop :=
| SEmpty (a': address) : sub_address [] a'
| SCons (a a' a'':address) : sub_address a a' -> sub_address (a++a'') (a'++a'')
.
Hint Constructors sub_address.

Notation "a ⊑ b" := (sub_address a b) (at level 100). 

Lemma sub_address_refl: Reflexive sub_address.
Proof.
  red; intros; induction x; try constructor.
  apply (SCons [a] [a] x); apply (SCons [] [] [a]); constructor.
Qed.


Lemma sub_address_nil: forall (a:address), (a ⊑ []) -> a = [].
Proof.
Admitted.

Lemma sub_address_trans: Transitive sub_address.
Proof.
Admitted.

Fixpoint sub_addressb (a a': address): bool :=
  match a, a' with
  | [], _ => true
  | (c::b), (c'::b') => ((c::b) =? (c'::b')) || sub_addressb (c::b) b'
  | _, _ => false
  end.

Lemma sub_addressb_refl: forall a, sub_addressb a a = true.
Proof.
  destruct a; trivial.
  simpl. apply orb_true_iff. left. apply Utils.eqb_refl.
Qed.

Lemma sub_address_app_char: forall a a' c, sub_addressb a a' = true -> sub_addressb (a++[c]) (a'++[c]) = true.
Proof.
  induction a; induction a'; intros; simpl.
  - apply orb_true_iff; left; apply Utils.eqb_refl.
  - apply orb_true_iff; right; apply IHa'; destruct a'; trivial.
  - inversion H.
  - apply orb_true_iff. simpl in H. apply orb_true_iff in H. destruct H.
    + apply Utils.eqb_eq in H. injection H as H1; subst. left; apply Utils.eqb_refl.
    + right. apply IHa'. assumption.
Qed.
 
Lemma sub_address_is_sub_addressb: forall (a a':address), 
  sub_address a a' <-> (sub_addressb a a' = true).
Proof.
  split.
  - intros. induction H as [a|a a' a'' H]; simpl.
    -- destruct a; trivial. 
    -- generalize dependent a; generalize dependent a'; induction a''; intros.
      --- rewrite app_nil_r, app_nil_r; assumption.
      --- rewrite cons_app, app_assoc, app_assoc.
          apply (IHa'' (a' ++ [a]) (a0 ++ [a])).
          + constructor; assumption.
          + apply sub_address_app_char; assumption.
  - intros. generalize dependent a; induction a'; induction a; intros; 
    try (constructor; reflexivity); try (inversion H);
    try(destruct a; simpl in H; try constructor; apply orb_true_iff in H; destruct H; 
          try(apply Utils.eqb_eq in H; rewrite H; apply sub_address_refl);
          apply IHa' in H; eapply sub_address_trans; try eassumption;
            rewrite <- (app_nil_l a'); try (apply (SCons _ [l] a'); constructor);
                                                     try (apply (SCons _ [r] a'); constructor);
                                                     try (apply (SCons _ [i] a'); constructor)).
Qed.

Definition disjoint (a a': address): Prop := ~(sub_address a a') /\ ~(sub_address a' a).

Lemma disjoint_not_refl: forall a a', a = a' -> ~(disjoint a a).
Proof.
  intros; unfold not; intros; inversion H0; destruct H1; apply sub_address_refl.
Qed.

Lemma disjoint_not_refl_contra: forall a a', disjoint a a' -> a <> a' .
Proof.
  intros; unfold not; intros; inversion H; subst; destruct H1; apply sub_address_refl.
Qed.



Definition disjointb (a a': address): bool := (negb (sub_addressb a a')) && (negb (sub_addressb a' a)).

Lemma disjoint_is_disjointb: forall a a', disjoint a a' <-> (disjointb a a' = true).
Proof.
  assert (Hloc1: forall b, b <> true -> b = false).
    { intros; destruct b; trivial; destruct H; trivial. }
  assert (Hloc2: forall a1 a2, sub_addressb a1 a2 = false <-> ~(sub_address a1 a2)).
       { intros; split; intros.
         - unfold not; intros. rewrite sub_address_is_sub_addressb in H0. rewrite H in H0; discriminate H0.
         - rewrite sub_address_is_sub_addressb in H. apply Hloc1 in H; assumption.
       }
  split.
  - intros. destruct H. rewrite sub_address_is_sub_addressb in H. rewrite sub_address_is_sub_addressb in H0.
    unfold disjointb. apply andb_true_iff. 
    apply Hloc1 in H; apply Hloc1 in H0; rewrite <- negb_true_iff in H; rewrite <- negb_true_iff in H0.
    split; try apply H; try apply H0.
  - intros.
    unfold disjointb in H. apply andb_true_iff in H. destruct H. split;
     unfold not; intros; 
     rewrite sub_address_is_sub_addressb in H1; rewrite negb_true_iff in H; rewrite negb_true_iff in H0; 
     try rewrite H in H1; try rewrite H0 in H1; discriminate H1.
Qed.
       
Definition address1 := [l;i;r;r;i;l;i;r].
Definition address2 := [r;r;i;l;i;r].
Definition address3 := [r;r;r;i;l;i;r].

Example test_True: disjoint address1 address3.
Proof.
  apply disjoint_is_disjointb; reflexivity.
Qed.

Example test_False: ~(disjoint address1 address2).
Proof.
  unfold not; intros; apply disjoint_is_disjointb in H; discriminate H.
Qed.

Definition disjoint_lists (l1 l2:list address) : Prop  := forall (a1 a2: address),
  In a1 l1 -> In a2 l2 -> disjoint a1 a2.

Inductive disjoint_list : list address -> Prop :=
 | DEmpty: disjoint_list []
 | DCons(a:address)(l:list address): (forall a', In a' l -> disjoint a a') -> disjoint_list (a::l).

Definition disjoint_addr_list (a:address)(l:list address) : Prop := forall (a':address),
  In a' l -> disjoint a a'.

Fixpoint disjoint_addr_listb (a:address)(l:list address) : bool :=
  match l with
  | [] => true
  | a'::l' => disjointb a a' &&& disjoint_addr_listb a l'
  end.

Lemma disjoint_addr_list_is_disjoint_addr_listb: forall a l,
  disjoint_addr_list a l <-> disjoint_addr_listb a l = true.
Proof.
  split; intros.
  - induction l0 as [|a' l0' IH]; trivial; simpl.
    apply andb_true_iff; split.
    -- unfold disjoint_addr_list in H; apply disjoint_is_disjointb; apply H; left; trivial.
    -- apply IH; unfold disjoint_addr_list in H; unfold disjoint_addr_list; intros; apply H; right; assumption.
  - unfold disjoint_addr_list. intros. induction l0 as [|a0' l0' IH].
    -- inversion H0.
    -- simpl in H0. simpl in H. apply andb_true_iff in H. destruct H. destruct H0.
      + subst; apply disjoint_is_disjointb in H; assumption.
      +  apply IH; assumption.
Qed.
  
(* Generate an address that would conserve the disjointness of the set if apppended :
    As the addresses are already disjoint, it is just necessary to take the longest one 
    and change the last character.
    You just have to notice that if an address (c::list) has length n, you cannot have the same 
    sub-addresses (r::list)(l::list)(i::list) at the same time in the list of addresses.
     *)

Compute (map (@length allowed_chars) [[l;r;i];[];[l]]).


Definition max_length (l: list address) : nat := list_max (map (@length allowed_chars) l).
 
Print filter.
Print length.

Definition max_length_subset (l: list address) : list address :=
  let M := (max_length l) in 
  filter (fun (a:address) => (@length allowed_chars a) =? M) l.

Compute max_length_subset [[l;r;i];[];[l]].
  
Fixpoint fresh_address (la: list address) : address :=
  match (max_length_subset la) with
  | [] => []
  | a :: la' => match a with
                  | [] => [] (* cannot happen ! *)
                  | (i :: a') => (l :: a') (* default left *)
                  | (_ :: a')=> (i :: a') 
                  end
  end.

Compute fresh_address [[i];[r;i];[l;i];[l;r;i]].

Fixpoint npop (n:nat)(a:address): option address :=
  match n, a with
  | 0, a' => Some a'
  | S n', c::a' => npop n' a'
  | S n', [] => None
  end.





















