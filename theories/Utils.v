
(** * Utilities : boolean equalities, list operators, ... *)

(** The NatDed development, Pierre Letouzey, 2019.
    This file is released under the CC0 License, see the LICENSE file *)

Require Import Bool Arith Lia Ascii String AsciiOrder StringOrder List.
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

Lemma lazy_orb_false (a:bool) : a ||| false = a.
Proof.
 now destruct a.
Qed.

Lemma lazy_orb_iff (a b:bool) : a ||| b = true <-> a = true \/ b = true.
Proof.
 split; destruct a; destruct b; simpl; intuition.
Qed.

Lemma cons_app {A} (x:A) l : x::l = [x]++l.
Proof.
 reflexivity.
Qed.

(** Generic boolean equalities (via Coq Classes) *)

Declare Scope eqb_scope.
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

Fixpoint OrList (l:list bool) :=
  match l with
  | [] => false
  | h::l' => h ||| (OrList l')
  end.

Lemma OrListTrue : forall l, (exists x, x = true /\ In x l) <-> (OrList l = true).
Proof.
  induction l; split; intros.
  - repeat destruct H. destruct H0.
  - discriminate H.
  - destruct H; destruct H; simpl; destruct a; trivial;
    apply IHl; exists x; split; try assumption; simpl in H0;
    destruct H0; subst; try discriminate H0; assumption.
  - simpl; simpl in H; destruct a eqn:Heq.
    -- exists a; split; try assumption; left; symmetry; assumption.
    -- apply IHl in H; destruct H; exists x; destruct H; split; try assumption; right; assumption.
Qed.

Fixpoint AndList (l:list bool) :=
  match l with
  | [] => true
  | x::l' => x && AndList l'
  end.

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
(* rename swap *)
Fixpoint swapb {A} `{EqbSpec A} (l1 l2: list A): bool :=
  match l1, l2 with
  | [], [] => false
  | [_], [_] => false
  | (x1::l1'), (x2::l2') => match l1', l2' with
                                       | (x1'::l1''), (x2'::l2'') 
                                                => ((x1 =? x2') &&& (x1' =? x2) &&& (l1'' =? l2'')) ||| ((x1 =? x2) &&& swapb l1' l2')
                                       | _, _ => false
                                      end 
  | _, _ => false
  end.

Lemma swapb_pattern {A} `{EqbSpec A}: forall l1 l2 a1 a2,
  swapb (l1 ++ a1 :: a2 :: l2)(l1 ++ a2 :: a1 :: l2) = true.
Proof.
  intros. generalize dependent l1.
  induction l2; intros; induction l1.
  - simpl; repeat rewrite eqb_refl; trivial.
  - simpl. destruct (l1 ++ [a1; a2]) eqn:Heq.
    + destruct l1; inversion Heq.
    + destruct (l1 ++ [a2; a1]) eqn:Heq'.
      ++ destruct l1; inversion Heq'.
      ++ apply lazy_orb_iff; right; rewrite eqb_refl; assumption.
  - repeat rewrite app_nil_l; simpl; rewrite lazy_orb_iff; left; repeat rewrite eqb_refl; trivial.
  - simpl. destruct (l1 ++ a1 :: a2 :: a :: l2) eqn:Heq.
    + destruct l1; inversion Heq.
    + destruct (l1 ++ a2 :: a1 :: a :: l2) eqn:Heq'.
      ++ destruct l1; inversion Heq'.
      ++ rewrite lazy_orb_iff; right; rewrite eqb_refl; assumption.
Qed.
  
Definition swap {A} `{EqbSpec A} (l1 l2:list A): Prop :=
  exists a1 a2 h t, l1 = h ++ a1 :: a2 :: t /\ l2 = h ++ a2 :: a1 :: t.

Lemma swapb_is_swap {A} `{EqbSpec A}:
  forall (l1 l2: list A), swapb l1 l2 = true <->  swap l1 l2.
Proof.
  split.
  - destruct l1; destruct l2; intros; try discriminate H1.
    + destruct l1; discriminate H1.
    + simpl in H1. revert dependent l2; revert a; revert a0. induction l1; destruct l2;
       try (intro; discriminate H1);
       intro; rewrite lazy_orb_iff in H1; destruct H1.
       * repeat rewrite lazy_andb_iff in H1; repeat rewrite eqb_eq in H1.
            destruct H1; destruct H1; subst; exists a2, a0, [], l2; intuition.
       * simpl in H1; rewrite lazy_andb_iff in H1; destruct H1; apply IHl1 in H2;
         apply eqb_eq in H1; subst;
         destruct H2; destruct H1; destruct H1; destruct H1; destruct H1; rewrite H1; rewrite H2;
         exists x, x0, (a0 :: x1), x2; intuition.
  - unfold swap; intros; destruct H1; destruct H1; destruct H1; destruct H1; destruct H1; subst;
    apply swapb_pattern.
Qed.

Lemma app_one_nil{A}: forall (c:A) (a:list A), not (a ++ [c] = []).
Proof.
  intros; unfold not; intros; destruct (app_cons_not_nil a [] c); symmetry; assumption.
Qed.

Lemma injection_rev{A}: forall (c1 c2:A) (a1 a2:list A), 
      a1 ++ [c1] = a2 ++ [c2] -> a1 = a2 /\ c1 = c2.
Proof.
  induction a1; induction a2; intros; split; injection H as H; subst; trivial;
  try(destruct (app_one_nil c2 a2); symmetry; assumption);
  try(destruct (app_one_nil c1 a1); assumption);
  apply IHa1 in H0; destruct H0; subst; trivial.
Qed.

Lemma list_mem_in {A}`{EqbSpec A} (l : list A) x :
 list_mem x l = true <-> In x l.
Proof.
 induction l as [|a l IH]; simpl.
 - easy.
 - case eqbspec.
   + intros <-. intuition discriminate.
   + rewrite IH. intuition.
Qed.

Lemma InDec {A}`{EqbSpec A}: forall (l: list A)(a:A), (In a l) \/ ~ (In a l).
Proof.
  intros; destruct (list_mem a l) eqn:Heq.
  - apply list_mem_in in Heq; left; trivial.
  - right; unfold not; intro; apply list_mem_in in H1; rewrite H1 in Heq; discriminate Heq.
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

Lemma max_S : forall n m, (S(Nat.max n m) = Nat.max (S n) (S m)).
Proof.
  induction n; induction m; simpl; trivial.
Qed.

Lemma max_pred : forall n m, (Nat.pred(Nat.max n m) = Nat.max (Nat.pred n) (Nat.pred m)).
Proof.
  induction n; induction m; simpl; trivial; rewrite Nat.max_0_r; trivial.
Qed.

Lemma le_max: forall n m, n <= Nat.max n m /\ m <= Nat.max n m.
Proof.
   intros; lia.
Qed.

Lemma le_max_bis: forall n m, Nat.max n m <= n \/ Nat.max n m <= m.
Proof.
  intros; lia.
Qed.
  
Lemma max_le n m p : Nat.max n m <= p <-> n <= p /\ m <= p.
Proof.
 lia.
Qed.

Lemma max_eq n m p : Nat.max n m = p -> n = p \/ m = p.
Proof.
  intros.
  generalize dependent p; generalize dependent m; induction n; intros.
  + simpl in H; right; assumption.
  + destruct m.
    ++ simpl in H; left; trivial.
    ++ rewrite <- max_S in H; destruct p.
      +++ discriminate H.
      +++ injection H as H. apply IHn in H. destruct H; subst; intuition.
Qed.

Lemma max_lt n m p : Nat.max n m < p <-> n < p /\ m < p.
Proof.
 lia.
Qed.

Lemma max_0 n m : Nat.max n m = 0 <-> n=0 /\ m=0.
Proof.
 lia.
Qed.

Lemma le_pred_S : forall n m, Nat.pred n <= m <-> n <= S m.
Proof.
  intros; lia.
Qed.

Lemma eq_pred_S : forall n m, Nat.pred n = m -> n <= S m.
Proof.
  induction n; intros.
  - simpl in H; subst; constructor; trivial.
  - simpl in H; subst; trivial.
Qed.

Lemma eq_pred_S' : forall n m, 1 <= n -> (Nat.pred n = m <-> n = S m).
Proof.
  split; induction n; intros.
  - inversion H.
  - simpl in H0; subst; trivial.
  - discriminate H0.
  - simpl; injection H0 as H0; assumption.
Qed.

Lemma max_mono a a' b b' :
 a <= a' -> b <= b' -> Nat.max a b <= Nat.max a' b'.
Proof.
 lia.
Qed.

Lemma list_max_le l p :
 list_max l <= p <-> (forall n, In n l -> n <= p).
Proof.
 induction l; simpl; rewrite ?max_le in *; intuition; lia.
Qed.

(** /!\ The other direction is only true for non-empty lists *)

Lemma list_max_lt l p :
 list_max l < p -> (forall n, In n l -> n < p).
Proof.
 induction l; simpl; rewrite ?max_lt in *; intuition; lia.
Qed.

Lemma list_max_0 l :
 list_max l = 0 <-> forall n, In n l -> n = 0.
Proof.
 induction l; simpl; rewrite ?max_0 in *; intuition; lia.
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

(** Logic *)

Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q. intros Hi. intros Hf. unfold not. unfold not in Hf. intros Hg.
  apply Hf.  apply Hi. apply Hg.
Qed.

Lemma not_inv:
  forall (P:Prop), P-> ~~P.
Proof.
  intros; unfold not; intros; destruct H0; assumption.
Qed.