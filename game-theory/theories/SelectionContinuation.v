From mathcomp.analysis Require Import reals.

From GTF.ExtLibMod Require Import Functions.
From GTF.ExtLibMod Require Functor Applicative Monad.

Module Type Return.
  Parameter t : realType.
End Return.

Module Arrow (R : Return).
  Definition t (A : Type) := R.t -> A.

  Module Functor <: Functor.T.
    Definition F : Type -> Type := t.
    Definition fmap {A B : Type} (f : A -> B) (x : F A) : F B.
    Proof.
      unfold F in *.
      intros r.
      apply f.
      apply x.
      apply r.
    Defined.
  End Functor.

  Module Applicative <: Applicative.T.
    Definition F : Type -> Type := t.
    Definition pure {A : Type} (x : A) : F A.
    Proof.
      intros _.
      apply x.
    Defined.
    Definition ap {A B : Type} (f : F (A -> B)) (x : F A) : F B.
    Proof.
      intros y.
      apply (f y).
      apply (x y).
    Defined.
  End Applicative.

  Module Monad <: Monad.T.
    Definition F : Type -> Type := t.
    Definition ret {A : Type} := @Applicative.pure A.
    Definition bind {A B : Type} (x : F A) (f : A -> F B) : F B.
    Proof.
      intros r.
      specialize (x r).
      apply (f x r).
    Defined.
  End Monad.

  Module FunctorNotations := Functor.Notations Functor.
  Module ApplicativeNotations := Applicative.Notations Applicative.
  Module MonadNotations := Monad.Notations Monad.
  Import FunctorNotations ApplicativeNotations MonadNotations.

  Module LawfulFunctor : Functor.Lawful Functor.
    Theorem fmap_id : forall {A : Type} (x : t A), id <$> x = x.
    Proof. reflexivity. Qed.
    Theorem fmap_compose : forall {A B C : Type} (f : A -> B) (g : B -> C) (x : t A), compose g f <$> x = g <$> (f <$> x).
    Proof. reflexivity. Qed.
  End LawfulFunctor.

  Module LawfulApplicative : Applicative.Lawful Applicative.
    Module ApplicativeNotations := ApplicativeNotations.
    Theorem ap_identity : forall {A : Type} (x : t A), (Applicative.pure id) <*> x = x.
    Proof. reflexivity. Qed.
    Theorem ap_homomorphism : forall {A B : Type} (f : A -> B) (x : A), (Applicative.pure f) <*> (Applicative.pure x) = Applicative.pure (f x).
    Proof. reflexivity. Qed.
    Theorem ap_composition : forall {A B C : Type} (u : t (A -> B -> C)) (v : t (B -> A)) w,
        Applicative.pure compose <*> u <*> v <*> w = u <*> (v <*> w).
    Proof. reflexivity. Qed.
  End LawfulApplicative.

  Module LawfulMonad : Monad.Lawful Monad.
    Module MonadNotations := MonadNotations.
    Theorem bind_of_return : forall {A B : Type} (x : A) (f : A -> t B), Monad.ret x >>= f = f x.
    Proof. reflexivity. Qed.
    Theorem return_of_bind : forall {A : Type} (x : t A), x >>= Monad.ret = x.
    Proof. reflexivity. Qed.
    Theorem bind_associativity : forall {A B C : Type} (x : t A) (f : A -> t B) (g : B -> t C),
      x >>= f >>= g = x >>= (fun x' => f x' >>= g).
    Proof. reflexivity. Qed.
  End LawfulMonad.

End Arrow.

Module Continuation (R : Return).
  Definition t (A : Type) : Type := (A -> R.t) -> R.t.

  Module Functor <: Functor.T.
    Definition F : Type -> Type := t.
    Definition fmap {A B : Type} (f : A -> B) (x : F A) : F B.
    Proof.
      intros r.
      unfold F, t in x.
      apply x.
      intros x'.
      apply r.
      apply f.
      apply x'.
    Defined.
  End Functor.

  Module Applicative <: Applicative.T.
    Definition F : Type -> Type := t.
    Definition pure {A : Type} (x : A) : F A.
    Proof.
      intros k.
      apply k.
      apply x.
    Defined.
    Definition ap {A B : Type} (f : F (A -> B)) (x : F A) : F B.
    Proof.
      intros y.
      unfold F, t in *.
      apply f.
      intros f'.
      apply x.
      intros x'.
      specialize (f' x').
      apply (y f').
    Defined.
  End Applicative.

  Module Monad <: Monad.T.
    Definition F : Type -> Type := t.
    Definition ret {A : Type} := @Applicative.pure A.
    Definition bind {A B : Type} (x : F A) (f : A -> F B) : F B.
    Proof.
      intros r.
      unfold F, t in *.
      apply x.
      intros x'.
      apply (f x').
      intros y.
      apply (r y).
    Defined.
  End Monad.

  Module FunctorNotations := Functor.Notations Functor.
  Module ApplicativeNotations := Applicative.Notations Applicative.
  Module MonadNotations := Monad.Notations Monad.
  Import FunctorNotations ApplicativeNotations MonadNotations.

  Module LawfulFunctor : Functor.Lawful Functor.
    Theorem fmap_id : forall {A : Type} (x : t A), id <$> x = x.
    Proof. reflexivity. Qed.
    Theorem fmap_compose : forall {A B C : Type} (f : A -> B) (g : B -> C) (x : t A), compose g f <$> x = g <$> (f <$> x).
    Proof. reflexivity. Qed.
  End LawfulFunctor.

  Module LawfulApplicative : Applicative.Lawful Applicative.
    Module ApplicativeNotations := ApplicativeNotations.
    Theorem ap_identity : forall {A : Type} (x : t A), (Applicative.pure id) <*> x = x.
    Proof. reflexivity. Qed.
    Theorem ap_homomorphism : forall {A B : Type} (f : A -> B) (x : A), (Applicative.pure f) <*> (Applicative.pure x) = Applicative.pure (f x).
    Proof. reflexivity. Qed.
    Theorem ap_composition : forall {A B C : Type} (u : t (A -> B -> C)) (v : t (B -> A)) w,
        Applicative.pure compose <*> u <*> v <*> w = u <*> (v <*> w).
    Proof. reflexivity. Qed.
  End LawfulApplicative.

  Module LawfulMonad : Monad.Lawful Monad.
    Module MonadNotations := MonadNotations.
    Theorem bind_of_return : forall {A B : Type} (x : A) (f : A -> t B), Monad.ret x >>= f = f x.
    Proof. reflexivity. Qed.
    Theorem return_of_bind : forall {A : Type} (x : t A), x >>= Monad.ret = x.
    Proof. reflexivity. Qed.
    Theorem bind_associativity : forall {A B C : Type} (x : t A) (f : A -> t B) (g : B -> t C),
      x >>= f >>= g = x >>= (fun x' => f x' >>= g).
    Proof. reflexivity. Qed.
  End LawfulMonad.
End Continuation.

Module Selection (R : Return).
  Definition t (A : Type) : Type := (A -> R.t) -> A.

  Module Functor <: Functor.T.
    Definition F : Type -> Type := t.
    Definition fmap {A B : Type} (f : A -> B) (x : F A) : F B.
    Proof.
      intros r.
      unfold F, t in x.
      apply f.
      apply x.
      intros x'.
      apply r.
      apply f.
      apply x'.
    Defined.
  End Functor.

  Module Applicative <: Applicative.T.
    Definition F : Type -> Type := t.
    Definition pure {A : Type} (x : A) : F A.
    Proof.
      intros _.
      apply x.
    Defined.
    Definition ap {A B : Type} (f : F (A -> B)) (x : F A) : F B.
    Proof.
      intros y.
      unfold F, t in *.
      apply f.
      - intros f'.
        apply y.
        apply f'.
        apply x.
        intros x'.
        apply y.
        apply f'.
        apply x'.
      - apply x.
        intros x'.
        apply y.
        apply f.
        + intros f'.
          apply y.
          apply f'.
          apply x'.
        + apply x'.
    Defined.
  End Applicative.

  Module Monad <: Monad.T.
    Definition F : Type -> Type := t.
    Definition ret {A : Type} := @Applicative.pure A.
    Definition bind {A B : Type} (x : F A) (f : A -> F B) : F B.
    Proof.
      intros r.
      unfold F, t in *.
      apply f.
      - apply x.
        intros x'.
        apply r.
        apply (f x').
        intros y.
        apply r.
        apply y.
      - apply r.
    Defined.
  End Monad.

  Module FunctorNotations := Functor.Notations Functor.
  Module ApplicativeNotations := Applicative.Notations Applicative.
  Module MonadNotations := Monad.Notations Monad.
  Import FunctorNotations ApplicativeNotations MonadNotations.

  Module LawfulFunctor : Functor.Lawful Functor.
    Theorem fmap_id : forall {A : Type} (x : t A), id <$> x = x.
    Proof. reflexivity. Qed.
    Theorem fmap_compose : forall {A B C : Type} (f : A -> B) (g : B -> C) (x : t A), compose g f <$> x = g <$> (f <$> x).
    Proof. reflexivity. Qed.
  End LawfulFunctor.
(*| Selections are not lawful applicatives. |*)
  (*
  Module LawfulApplicative : Applicative.Lawful Applicative.
    Module ApplicativeNotations := ApplicativeNotations.
    Theorem ap_identity : forall {A : Type} (x : t A), (Applicative.pure id) <*> x = x.
    Proof. reflexivity. Qed.
    Theorem ap_homomorphism : forall {A B : Type} (f : A -> B) (x : A), (Applicative.pure f) <*> (Applicative.pure x) = Applicative.pure (f x).
    Proof. reflexivity. Qed.
    Theorem ap_composition : forall {A B C : Type} (u : t (A -> B -> C)) (v : t (B -> A)) (w : t B),
        Applicative.pure compose <*> u <*> v <*> w = u <*> (v <*> w).
    Proof.
      unfold Applicative.F, t, compose, Applicative.pure.
      intros A B C u v w.
      From Coq Require Import FunctionalExtensionality.
      apply functional_extensionality.
      intros k.
      reflexivity.
    Qed.
  End LawfulApplicative.
  *)
  Module LawfulMonad : Monad.Lawful Monad.
    Module MonadNotations := MonadNotations.
    Theorem bind_of_return : forall {A B : Type} (x : A) (f : A -> t B), Monad.ret x >>= f = f x.
    Proof. reflexivity. Qed.
    Theorem return_of_bind : forall {A : Type} (x : t A), x >>= Monad.ret = x.
    Proof. reflexivity. Qed.
    Theorem bind_associativity : forall {A B C : Type} (x : t A) (f : A -> t B) (g : B -> t C),
      x >>= f >>= g = x >>= (fun x' => f x' >>= g).
    Proof. reflexivity. Qed.
  End LawfulMonad.

  Definition product {A B : Type} (x : t A) (y : t B) : t (A * B).
  Proof.
    intros j.
    split.
    - apply x.
      intros x'.
      apply j.
      split; try assumption.
      apply y.
      intros y'.
      apply j.
      split; assumption.
    - apply y.
      intros y'.
      apply j.
      split; try assumption.
      apply x.
      intros x'.
      apply j.
      split; assumption.
  Defined.
End Selection.

Module Attainability (R : Return).
  Module Selection := Selection R.
  Module Continuation := Continuation R.
  Definition attainedBy {A : Type} (epsilon : Selection.t A) : Continuation.t A := fun k => k (epsilon k).
End Attainability.
