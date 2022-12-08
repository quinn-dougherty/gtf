(*
From Coq Require Import String.
From mathcomp Require Import classical_sets all_ssreflect all_algebra order.
*)
From ExtLib Require Import Functor FunctorLaws Applicative Monad MonadLaws.
Import ApplicativeNotation.

Module Type VariableType.
  Parameter letters : Type.
End VariableType.

Module Sentence (V : VariableType).
  (*| Proceed classically, by which the only primitive connectives are the nullary bot and the binary arrow, and the other connectives are derived. |*)
  Inductive t : Type :=
  | Letter : V.letters -> t
  | Bottom : t
  | Arrow : t -> t -> t
  | Box : t -> t
  .
  Coercion Letter : V.letters >-> t.

  Notation "'(' A ')'" := A.
  Notation "⊥" := Bottom.
  Notation "A '⟶' B" := (Arrow A B) (at level 10).
  Notation "'◻' A" := (Box A) (at level 9).
  Definition Not (x : t) := x ⟶ ⊥.
  Definition Top := ⊥ ⟶ ⊥.
  Definition Or (x y : t) := Not x ⟶ y.
  Definition And (x y : t) := Not (Or (Not x) (Not y)).
  Notation "A '∨' B" := (Or A B) (at level 11).
  Notation "A '∧' B" := (And A B) (at level 12).

  Fixpoint letterless (x : t) : bool :=
    match x with
    | Letter _ => false
    | ⊥ => true
    | A ⟶ B => letterless A && letterless B
    | ◻ A => letterless A
    end.
End Sentence.

Module NatLetters : VariableType.
  Definition letters : Type := nat.
End NatLetters.

Module ModalLogic := Sentence NatLetters.



Module LiftProp.
  (*| In this approach I look at making modal operators augmentations of the basic coq's Prop |*)
  Inductive Modal (A : Type) : Type :=
    | lift : A -> Modal A
    | box : Modal A -> Modal A.

  (* Coercion lift Prop : Prop >-> Modal Prop. *)
  #[export] Instance ModalFunctor : Functor Modal.
  Proof.
    constructor.
    intros A B f MA.
    generalize dependent f.
    induction MA; intros f.
    - apply (lift _ (f a)).
    - apply (IHMA f).
  Defined.

  #[export] Instance ModalLawfulFunctor : FunctorLaws ModalFunctor.
  Proof.
    constructor.
    - intros A x.
      induction x; auto.
      admit.
    - intros A B C f g x.
      induction x; auto.
  Admitted.

  (*| This applicative instance violates the interchange law: u <*> pure v = pure (fun f => f v) <*> u |*)
  #[export] Instance ModalApplicative : Applicative Modal.
  Proof.
    constructor.
    - intros A x; apply (lift A x).
    - intros A B Mf Mx.
      induction Mf.
      + apply (fmap a Mx).
      + apply IHMf.
  Defined.

  Section LawfulApplicative.
    Parameter (A B C : Type).
    Theorem applicativeIdentity (x : Modal A) : pure id <*> x = x.
    Proof. induction x; compute. Admitted.
    Theorem applicativeHomomorphism (f : A -> B) (x : A) : (pure f) <*> (pure x) = pure (f x).
    Proof. reflexivity. Qed.

    Definition compose (f : B -> C) (g : A -> B) : A -> C := fun x => f (g x).
    Theorem applicativeComposition u v w : pure compose <*> u <*> v <*> w = u <*> (v <*> w).
    Proof. induction u; induction v; induction w; auto. Qed.

  End LawfulApplicative.

  Definition join (A : Type) (MMx : Modal (Modal A)) : Modal A.
  Proof.
    induction MMx eqn:E. apply a.
  Admitted.

  Definition not__modal (x : Modal Prop) : Modal Prop := lift _ not <*> x.
  Check @fmap.
  Definition diamond : Modal Prop -> Modal Prop :=
    fun x => match x with
          | lift _ x => fmap not (box _ (lift _ (not x)))
          | box _ x => fmap not x (* these are incorrect. *)
          end.
  Definition or__modal (x y : Modal Prop) : Modal Prop := lift _ or <*> x <*> y.
  Definition and__modal (x y : Modal Prop) : Modal Prop := lift _ and <*> x <*> y.

  Module ModalNotation.
    Notation "x '∧' y" := (and__modal x y) (at level 12).
    Notation "x '∨' y" := (or__modal x y) (at level 11).
    Notation "'⋄' x" := (diamond x) (at level 9).
    Notation "'¬' x" := (not__modal x) (at level 8).
    Notation "x '⟶' y" := (¬ x ∨ y) (at level 13).
  End ModalNotation.

  Inductive subsentence : Modal Prop -> Modal Prop -> Prop :=
    | subsentence_self : forall P, subsentence P P
    | subsentence_arrowDomain : forall P Q R, subsentence (lift _ (fun (x y : Prop) => x -> y) <*> P <*> Q) R -> subsentence P R
    | subsentence_arrowCodomain : forall P Q R, subsentence (lift _ (fun (x y : Prop) => x -> y) <*> P <*> Q) R -> subsentence Q R
    | subsentence_box : forall P Q, subsentence (box _ P) Q -> subsentence P Q.

End LiftProp.
