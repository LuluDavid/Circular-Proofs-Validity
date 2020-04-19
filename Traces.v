Require Export Derivations Subformulas FLSubformulas.

Import ListNotations.

Require Import Streams.

(** DEFINITION *)

(** Finite Paths *)

Definition FPathType := list sequent.

(* Ici, l'addresse représente le chemin de la feuille jusqu'à la base du chemin élémentaire *)

Inductive preFPath : FPathType -> derivation -> nat -> address -> Prop :=
 | CLeaf s s' ls n: s = (oseq_forget s') -> preFPath [s] (ORule ls (BackEdge n) s' []) n []
 | COne d t R ls s s' n a:
                          preFPath t d n a -> s' = oseq_forget s -> preFPath (s'::t) (ORule ls R s [d]) n (i::a)
 | CLeft d d' R ls t s s' n a: 
                          preFPath t d n a -> s' = oseq_forget s -> preFPath (s'::t) (ORule ls R s [d;d']) n (l::a)
 | CRight d d' R ls t s s' n a: 
                          preFPath t d n a -> s' = oseq_forget s -> preFPath (s'::t) (ORule ls R s [d';d]) n (r::a).

(* a_bottom ++ a_top donne le chemin de la racine jusqu'au backedge *)

Definition preFPathNode p d n a_top a_bottom :=
  match subderiv d a_bottom with
  | None       => False
  | Some d'  => preFPath p d' n a_top
  end.

Definition PathType := Stream FPathType.

Notation "t ;; T" := (Cons t T) (at level 60, right associativity).

CoInductive PathCoind : PathType -> derivation -> Prop :=
| Raccordement t1 t2 n1 n2 at1 at2 ab1 ab2 P d :
  PathCoind (t2 ;; P) d
  -> preFPathNode t2 d n2 at2 ab2
  -> preFPathNode t1 d n1 at1 ab1
  -> npop n1 (ab1 ++ at1) = Some ab2
  -> PathCoind (t1 ;; t2 ;; P) d.

Definition Path (P:PathType)(d:derivation) :=
  match P with
  | p ;; P' => exists n a, preFPath p d n a /\ PathCoind P d
  end.

CoFixpoint StreamRepeat {A:Type} (t:A) := t ;; StreamRepeat t.

Local Open Scope form.

Definition FPathExample: FPathType := 
  [(⊦ [ν % 0 ⊕ % 0]); (⊦ [(ν % 0 ⊕ % 0) ⊕ (ν % 0 ⊕ % 0)]); (⊦ [ν % 0 ⊕ % 0])].

Lemma FPathExample_valid : preFPathNode FPathExample oderiv_example' 2 [i;i] [].
Proof.
  cbv.
  repeat (constructor; trivial).
Qed.

Definition PathExample := StreamRepeat FPathExample.

Definition ident {A:Type} (s:Stream A) :=
  match s with Cons n s' => Cons n s' end.

Lemma ident_eq : forall A, forall (s:Stream A), s = ident s.
Proof.
  intros; destruct s; simpl; reflexivity.
Qed.

Lemma unfoldStreamRepeat : forall A (s:A), (StreamRepeat s) = s ;; (StreamRepeat s).
Proof.
  intros.
  pattern (@StreamRepeat A) at 2. rewrite (ident_eq _ (StreamRepeat s)); simpl; reflexivity.
Qed.

Lemma Path_example_lemma : Path PathExample oderiv_example'.
Proof.
exists 2, [i;i]; split.
apply FPathExample_valid.
cbv.
cofix proof.
do 2 rewrite unfoldStreamRepeat.
apply (Raccordement _ _ 2 2 [i;i] [i;i] [] []); simpl; trivial.
{
rewrite <- unfoldStreamRepeat; apply proof.
}
{
cbv.
apply FPathExample_valid.
}
{
cbv.
apply FPathExample_valid.
}
Qed.

(** FTraceType *)

Definition FTraceType := list formula.

(* Ici, l'addresse représente le chemin de la feuille jusqu'à la base du chemin élémentaire *)

Fixpoint preFTraceRec (t:FTraceType) (p:FPathType) : Prop :=
  match p, t with
  | s :: p', f :: t' => In f s /\ (preFTraceRec t' p')
  | [], []             => True
  | _, _             => False
  end.

Definition preFTraceNode (t:FTraceType) (p:FPathType) (d:derivation) a_top a_bottom : Prop :=
  preFPath p d  a_top a_bottom /\ preFTraceRec t p.

Definition TraceType := Stream FTraceType.

(* TODO: ajouter le fait que la trace peut commencer en milieu de branche *)

CoInductive TraceCoind : TraceType -> PathType -> Prop :=
  | Cons T P t p : TraceCoind T P -> preFTraceRec t p -> TraceCoind (t ;; T)(p ;; P)
  .

Definition Trace (T:TraceType)(P:PathType)(d:derivation) :=
  Path P d /\ TraceCoind T P.

Definition FTraceExample: FTraceType := 
  [ν (%0)⊕(%0); (ν (%0)⊕(%0)) ⊕ (ν (%0)⊕(%0)); ν (%0)⊕(%0)].

Definition TraceExample := StreamRepeat FTraceExample.

Definition Trace_example_lemma : Trace TraceExample PathExample oderiv_example'.
Proof.
  split.
  apply Path_example_lemma.
  cofix proof.
  unfold TraceExample, PathExample.
  rewrite (unfoldStreamRepeat _ FTraceExample).
  rewrite (unfoldStreamRepeat _ FPathExample).
  constructor.
  apply proof.
  cbv; intuition.
Qed.

Definition appearsInfinitely (f:formula)(T:TraceType): Prop := 
  forall n, exists m, (n <= m) /\ In f (Str_nth m T).

Definition infMin (f:formula)(T:TraceType) : Prop := 
  appearsInfinitely f T /\ (forall G, appearsInfinitely G T -> f ⧼ G).

Definition ValidPath (P:PathType)(d:derivation) :=
  exists (T:TraceType)(f:formula), Trace T P d /\ infMin f T /\ NuFormula f.

Lemma repeatStrNth : forall A (s:A) n, Str_nth n (StreamRepeat s) = s.
Proof.
  intros.
  induction n; cbv; simpl; trivial.
Qed.

Definition infMin_example_lemma : infMin (ν (%0)⊕(%0)) TraceExample.
Proof.
  split.
  {
  intro.
  exists n; split; trivial.
  unfold TraceExample.
  rewrite repeatStrNth.
  simpl; intuition.
  }
  {
  intros.
  unfold appearsInfinitely in H.
  destruct (H 0).
  unfold TraceExample in H0.
  rewrite repeatStrNth in H0.
  destruct H0; simpl in H1.
  destruct H1; [subst; trivial|].
  destruct H1; [subst; constructor; trivial|].
  destruct H1; [subst; trivial|].
  destruct H1.
  }
Qed.

Definition validPath_example_lemma : ValidPath PathExample oderiv_example'.
Proof.
  unfold ValidPath.
  exists TraceExample, (ν (%0)⊕(%0)).
  split.
  apply Trace_example_lemma.
  split.
  apply infMin_example_lemma.
  cbv; reflexivity.
Qed.

Definition ValidCircularProof (d:derivation) :=
  Valid d /\ forall P, Path P d -> ValidPath P d.

Definition ValidCircularProof_example_lemma : ValidCircularProof oderiv_example'.
Proof.
  unfold ValidCircularProof; split.
  {
  split; [| apply thm_oexample].
  split; simpl; trivial.
  cbv; intros; destruct H.
  }
  intros.
  unfold Path in H.
  destruct P.
  do 3 destruct H.
  assert (f = FPathExample).
  {
  clear H0.
  inversion_clear H; subst; simpl.
  inversion_clear H0; subst; simpl.
  inversion_clear H; subst; simpl.
  trivial.
  }
  unfold ValidPath.
  exists TraceExample, (ν (%0)⊕(%0)).
  split; [| split ; [apply infMin_example_lemma |cbv; simpl; trivial ] ].
  split.
  - unfold Path.
    exists x, x0; split; trivial.
  - revert H0. generalize dependent P. subst. cofix proof; intros.
    unfold TraceExample. rewrite unfoldStreamRepeat.
    constructor.
    {
    inversion_clear H0; subst.
    assert (Heq: t2 = FPathExample).
    {
    assert (n1 = 2).
    {
    clear H1 H2 H4.
    cbv in H3.
    destruct ab1.
    - inversion_clear H3; subst.
      inversion_clear H0; subst.
      inversion_clear H2; subst.
      trivial.
    - destruct a; [destruct H3|destruct H3|].
      destruct ab1.
      -- inversion_clear H3; subst.
         inversion_clear H0; subst.
      -- destruct a; [destruct H3|destruct H3|].
         destruct ab1.
         + inversion_clear H3; subst.
         + destruct a; destruct H3.
    }
    subst.
    assert (ab1 = []).
    {
    clear H1 H2 H4.
    cbv in H3.
    destruct ab1; trivial.
    destruct a; [destruct H3|destruct H3|].
    destruct ab1.
    - inversion_clear H3; subst.
      simpl in H1; discriminate H1.
    - destruct a; [destruct H3|destruct H3|].
      destruct ab1.
      -- inversion_clear H3; subst.
      -- destruct a; destruct H3.
    }
    subst.
    assert (at1 = [i;i]).
    {
    clear H1 H2 H4.
    inversion_clear H3; subst.
    inversion_clear H0; subst.
    inversion_clear H2; subst; trivial.
    }
    subst; simpl in *. injection H4; clear H4; intros; subst.
    inversion_clear H2; subst.
    inversion_clear H0; subst.
    inversion_clear H2; subst.
    simpl; trivial.
    }
    subst; apply proof; assumption. }
    simpl; intuition.
Qed.










