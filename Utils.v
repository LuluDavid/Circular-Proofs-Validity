
(** * Utilities : boolean equalities, list operators, ... *)

(** The NatDed development, Pierre Letouzey, 2019.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Bool Arith Omega Ascii String AsciiOrder StringOrder List.
Import ListNotations.
Open Scope lazy_bool_scope.
Add Search Blacklist "OrdersEx.Nat_as".

Lemma lazy_andb_iff (b b' : bool) :
 b &&& b' = true <-> b = true /\ b' = true.
Proof.
 now destruct b, b'.
Qed.

Lemma lazy_andb_false (a:bool) : a &&& false = false.
Proof.
 now destruct a.
Qed.

Lemma lazy_orb_true (a:bool) : a ||| true = true.
Proof.
 now destruct a.
Qed.


Lemma cons_app {A} (x:A) l : x::l = [x]++l.
Proof.
 reflexivity.
Qed.

(** Generic boolean equalities (via Coq Classes) *)

Delimit Scope eqb_scope with eqb.
Local Open Scope eqb_scope.

Class Eqb (A : Type) := eqb : A -> A -> bool.
Infix "=?" := eqb : eqb_scope.
Arguments eqb {A} {_} !_ !_.

Class EqbSpec A `{Eqb A} :=
 eqbspec : forall x y:A, reflect (x=y) (x =? y).

Hint Extern 10 => case eqbspec : eqb.

Instance eqb_inst_nat : Eqb nat := Nat.eqb.
Instance eqbspec_nat : EqbSpec nat := Nat.eqb_spec.

Instance eqb_inst_ascii : Eqb ascii := AsciiOrder.ascii_eqb.
Instance eqbspec_ascii : EqbSpec ascii := AsciiOrder.ascii_eqb_spec.

Instance eqb_inst_string : Eqb string := StringOrder.string_eqb.
Instance eqbspec_string : EqbSpec string := StringOrder.string_eqb_spec.

Arguments eqb_inst_nat !_ !_.
Arguments eqb_inst_ascii !_ !_.
Arguments eqb_inst_string !_ !_.

Lemma eqb_refl {A} `{EqbSpec A} (x:A) : (x =? x) = true.
Proof.
 now case eqbspec.
Qed.

Lemma eqb_eq {A} `{EqbSpec A} (x y:A) : (x =? y) = true <-> x = y.
Proof.
 now case eqbspec.
Qed.

Lemma eqb_neq {A} `{EqbSpec A} (x y:A) : (x =? y) = false <-> x <> y.
Proof.
 now case eqbspec.
Qed.

Lemma eqb_sym {A} `{EqbSpec A} (x y:A) : (x =? y) = (y =? x).
Proof.
 case (eqbspec y x); intros.
 - apply eqb_eq. auto.
 - apply eqb_neq. auto.
Qed.

Lemma eqb_trans {A} `{EqbSpec A} (x y z:A) : (x =? y) = true -> (y =? z) = true -> (x =? z) = true.
Proof.
  intros; apply eqb_eq in H1; apply eqb_eq in H2; apply eqb_eq; subst; trivial.
Qed.

(** List stuff *)

Fixpoint list_assoc {A B}`{Eqb A} x (l:list (A*B)) :=
 match l with
 | [] => None
 | (y,z)::l => if x =? y then Some z else list_assoc x l
 end.

Fixpoint list_assoc_dft {A B}`{Eqb A} x (l:list (A*B)) (d:B) :=
 match l with
 | [] => d
 | (y,z)::l => if x =? y then z else list_assoc_dft x l d
 end.

Definition list_unassoc {A B}`{Eqb A} x : list (A*B) -> list (A*B) :=
 filter (fun '(y,_) => negb (y =? x)).

Fixpoint list_mem {A}`{Eqb A} x (l:list A) :=
  match l with
  | [] => false
  | y::l => (x =? y) ||| list_mem x l
  end.

Definition list_forallb2 {A B} (f: A -> B -> bool) :=
 fix forallb2 l1 l2 :=
 match l1, l2 with
 | [], [] => true
 | x1::l1, x2::l2 => f x1 x2 &&& forallb2 l1 l2
 | _, _ => false
 end.

Fixpoint list_index {A} `{Eqb A} (x:A) l : option nat :=
  match l with
  | [] => None
  | y::l => if x =? y then Some 0
            else option_map S (list_index x l)
  end.

Fixpoint list_max l :=
  match l with
  | [] => 0
  | n::l => Nat.max n (list_max l)
  end.

Ltac cons := constructor; congruence.

Instance eqb_inst_list {A}`{Eqb A} : Eqb (list A) := list_forallb2 eqb.

Instance eqbspec_list {A}`{EqbSpec A} : EqbSpec (list A).
Proof.
 red.
 induction x; destruct y; simpl; try cons.
 cbn.
 case eqbspec; [ intros <- | cons ].
 case IHx; cons.
Defined.

Lemma list_mem_in {A}`{EqbSpec A} (l : list A) x :
 list_mem x l = true <-> In x l.
Proof.
 induction l as [|a l IH]; simpl.
 - easy.
 - case eqbspec.
   + intros <-. intuition discriminate.
   + rewrite IH. intuition.
Qed.

Lemma list_assoc_in {A B}`{EqbSpec A} (l : list (A*B)) x :
 list_assoc x l <> None <-> In x (map fst l).
Proof.
 induction l as [|(a,b) l IH]; simpl.
 - easy.
 - case eqbspec.
   + intros <-. intuition discriminate.
   + rewrite IH. intuition.
Qed.

Lemma list_assoc_notin {A B}`{EqbSpec A} (l : list (A*B)) x :
 list_assoc x l = None <-> ~In x (map fst l).
Proof.
 induction l as [|(a,b) l IH]; simpl.
 - easy.
 - case eqbspec.
   + intros <-. intuition discriminate.
   + rewrite IH. intuition.
Qed.

Lemma list_assoc_in2 {A B}`{EqbSpec A} (l : list (A*B)) x y :
 list_assoc x l = Some y -> In (x,y) l.
Proof.
 induction l as [|(a,b) l IH]; simpl.
 - easy.
 - case eqbspec.
   + intros <- [= <-]. now left.
   + intuition.
Qed.

Lemma list_assoc_app_l {A B}`{EqbSpec A}
 (l l' : list (A*B)) x :
 In x (map fst l) -> list_assoc x (l++l') = list_assoc x l.
Proof.
 induction l as [|(a,b) l IH]; simpl; try easy.
 - case eqbspec; auto.
   intros NE [->|IN]; [easy|auto].
Qed.

Lemma list_assoc_app_r {A B}`{EqbSpec A}
 (l l' : list (A*B)) x :
 ~In x (map fst l) -> list_assoc x (l++l') = list_assoc x l'.
Proof.
 induction l as [|(a,b) l IH]; simpl; try easy.
 - case eqbspec; auto. intros <-. intuition.
Qed.

Lemma list_assoc_dft_alt {A B}`{EqbSpec A} (l : list (A*B)) x d :
 list_assoc_dft x l d =
 match list_assoc x l with
 | None => d
 | Some b => b
 end.
Proof.
 induction l as [|(a,b) l IH]; simpl; auto.
 rewrite IH. now case eqbspec.
Qed.

Lemma list_index_in {A}`{EqbSpec A} (l : list A) x :
  list_index x l <> None <-> In x l.
Proof.
 induction l as [|a l IH]; simpl.
 - easy.
 - case eqbspec.
   + intros <-. intuition discriminate.
   + destruct list_index; simpl. intuition easy. intuition.
Qed.

Lemma list_index_notin {A}`{EqbSpec A} (l : list A) x :
  list_index x l = None <-> ~In x l.
Proof.
 induction l as [|a l IH]; simpl.
 - easy.
 - case eqbspec.
   + intros <-. intuition discriminate.
   + destruct list_index; simpl. intuition easy. intuition.
Qed.

Lemma list_index_nth {A}`{EqbSpec A} (l : list A) n d :
 NoDup l ->
 n < List.length l ->
 list_index (nth n l d) l = Some n.
Proof.
 revert n.
 induction l; simpl.
 - inversion 2.
 - intros n. inversion_clear 1.
   destruct n.
   + now rewrite eqb_refl.
   + intros Hn.
     rewrite IHl; auto with arith; simpl.
     case eqbspec; auto.
     intros <-. destruct H2. apply nth_In. auto with arith.
Qed.

Lemma list_index_lt_length {A}`{EqbSpec A} (l : list A) x n :
  list_index x l = Some n -> n < List.length l.
Proof.
 revert n.
 induction l; simpl. easy.
 intros n.
 case eqbspec.
 - intros <- [= <-]. auto with arith.
 - destruct list_index; simpl in *; intros NE [= <-].
   specialize (IHl n0 eq_refl). auto with arith.
Qed.

Lemma list_index_app_l {A}`{EqbSpec A} x (l l' : list A) :
 In x l ->
 list_index x (l++l') = list_index x l.
Proof.
 induction l; simpl; try easy.
 case eqbspec; auto.
 intros NE Hl. rewrite IHl; auto. intuition. congruence.
Qed.

Lemma list_index_app_l' {A}`{EqbSpec A} x (l l' : list A) :
 ~In x l' ->
 list_index x (l++l') = list_index x l.
Proof.
 induction l; simpl.
 - apply list_index_notin.
 - case eqbspec; auto.
   intros NE Hl. now rewrite IHl.
Qed.

Lemma list_index_app_r {A}`{EqbSpec A} x (l l' : list A) :
 ~In x l ->
 list_index x (l++l') =
  option_map (Nat.add (length l)) (list_index x l').
Proof.
 induction l; simpl.
 - now destruct (list_index x l').
 - case eqbspec.
   + intros ->. intuition.
   + intros NE Hl. rewrite IHl by intuition. now destruct (list_index x l').
Qed.

Lemma list_assoc_index_none {A B}`{EqbSpec A} x (l:list (A*B)) :
  list_assoc x l = None <-> list_index x (map fst l) = None.
Proof.
 induction l as [|(a,b) l IH]; simpl; auto.
 intuition.
 case eqbspec; try easy.
 intros NE. rewrite IH.
 destruct list_index; simpl; intuition congruence.
Qed.

Lemma filter_app {A} (f:A->bool) l l' :
  filter f (l++l') = filter f l ++ filter f l'.
Proof.
 induction l as [|a l IH]; simpl; auto.
 destruct (f a); [simpl; f_equal|]; auto.
Qed.

Lemma unassoc_app {A B}`{Eqb A} x (l1 l2 : list (A*B)) :
 list_unassoc x (l1++l2) = list_unassoc x l1 ++ list_unassoc x l2.
Proof.
 unfold list_unassoc.
 apply filter_app.
Qed.

Lemma unassoc_in {A B}`{EqbSpec A} x a b (l : list (A*B)) :
 In (a,b) (list_unassoc x l) <-> In (a,b) l /\ a <> x.
Proof.
 unfold list_unassoc.
 now rewrite filter_In, <- eqb_neq, negb_true_iff.
Qed.

(** Max and lists *)

Lemma max_le n m p : Nat.max n m <= p <-> n <= p /\ m <= p.
Proof.
 omega with *.
Qed.

Lemma max_lt n m p : Nat.max n m < p <-> n < p /\ m < p.
Proof.
 omega with *.
Qed.

Lemma max_0 n m : Nat.max n m = 0 <-> n=0 /\ m=0.
Proof.
 omega with *.
Qed.

Lemma max_mono a a' b b' :
 a <= a' -> b <= b' -> Nat.max a b <= Nat.max a' b'.
Proof.
 omega with *.
Qed.

Lemma list_max_le l p :
 list_max l <= p <-> (forall n, In n l -> n <= p).
Proof.
 induction l; simpl; rewrite ?max_le in *; intuition.
Qed.

(** /!\ The other direction is only true for non-empty lists *)

Lemma list_max_lt l p :
 list_max l < p -> (forall n, In n l -> n < p).
Proof.
 induction l; simpl; rewrite ?max_lt in *; intuition.
Qed.

Lemma list_max_0 l :
 list_max l = 0 <-> forall n, In n l -> n = 0.
Proof.
 induction l; simpl; rewrite ?max_0 in *; intuition.
Qed.

Lemma list_max_map_le {A} (f:A->nat) l p :
 list_max (map f l) <= p <-> (forall a : A, In a l -> f a <= p).
Proof.
 rewrite list_max_le. split.
 - intros H a Ha. now apply H, in_map.
 - intros H n. rewrite in_map_iff. intros (a & <- & Ha). auto.
Qed.

Lemma list_max_map_0 {A} (f:A->nat) l :
 list_max (map f l) = 0 <-> (forall a : A, In a l -> f a = 0).
Proof.
 rewrite list_max_0. split.
 - intros H a Ha. now apply H, in_map.
 - intros H n. rewrite in_map_iff. intros (a & <- & Ha). auto.
Qed.

Lemma list_max_map_incr {A} (f g : A->nat) l :
 (forall a, In a l -> f a <= g a) ->
 list_max (map f l) <= list_max (map g l).
Proof.
 intros H.
 induction l; cbn in *; auto.
 apply max_mono; auto.
Qed.

(** Map *)

Lemma map_ext_iff {A B} (f g : A -> B) l :
  (forall a : A, In a l -> f a = g a) <-> map f l = map g l.
Proof.
 induction l; cbn.
 - intuition.
 - split.
   + intros H. f_equal; auto. apply IHl; auto.
   + intros [= H H'] b [->|Hb]; rewrite <-?IHl in H'; auto.
Qed.

Lemma map_id_iff {A} (f : A -> A) l :
  (forall a : A, In a l -> f a = a) <-> map f l = l.
Proof.
 rewrite <- (map_id l) at 2. apply map_ext_iff.
Qed.

Lemma forallb_map {A B} (f: B -> bool) (g: A -> B) l :
 forallb f (map g l) = forallb (fun x => f (g x)) l.
Proof.
 induction l; simpl; f_equal; auto.
Qed.

Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q. intros Hi. intros Hf. unfold not. unfold not in Hf. intros Hg.
  apply Hf.  apply Hi. apply Hg.
Qed.
