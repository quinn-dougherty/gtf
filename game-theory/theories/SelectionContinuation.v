From ExtLib Require Import Functor FunctorLaws Applicative Monad MonadLaws.

Definition K (B A : Type) : Type := (A -> B) -> B.
Definition J (B A : Type) : Type := (A -> B) -> A.

Section Arrow.
  Context (A : Type).

  Instance CodArrowFunctor : Functor (fun B => A -> B).
  Proof.
    constructor.
    intros B B' f x x'.
    apply f.
    apply x.
    apply x'.
  Defined.

  Instance CodArrowLawfulFunctor : FunctorLaws CodArrowFunctor.
  Proof.
    constructor; intros; reflexivity.
  Defined.

  Instance CodArrowApplicative : Applicative (fun B => A -> B).
  Proof.
    constructor.
    - intros B y x.
      apply y.
    - intros B B' f f' x.
      apply (f x).
      apply (f' x).
  Defined.

  Instance CodArrowMonad : Monad (fun B => A -> B).
  Proof.
    constructor.
    - intros B y x.
      apply y.
    - intros B C alpha Beta x.
      specialize (alpha x).
      apply (Beta alpha x).
  Defined.

  Instance CodArrowLawfulMonad : MonadLaws CodArrowMonad.
  Proof.
    constructor; intros; reflexivity.
  Defined.

End Arrow.

Section Continuation.
  (* Although `ExtLib` exports a `ContMonad`, we're going to reimplement here. *)
  Context (S : Type).

  Instance ContinuationFunctor : Functor (K S).
  Proof.
    constructor.
    unfold K.
    intros A B f KA k.
    apply KA.
    intros x.
    apply k.
    apply f.
    apply x.
  Defined.

  Instance ContinuationLawfulFunctor : FunctorLaws ContinuationFunctor.
  Proof.
    constructor; unfold K; intros; reflexivity.
  Defined.

  Instance ContinuationApplicative : Applicative (K S).
  Proof.
    constructor; unfold K.
    - intros A x f.
      apply (f x).
    - intros A B KfA KA k.
      apply KA.
      intros x.
      apply KfA.
      intros f.
      apply k.
      apply f.
      apply x.
  Defined.

  Instance ContinuationMonad : Monad (K S).
  Proof.
    constructor.
    - intros B y f; apply (f y).
    - unfold K.
      intros X Y Kx Kf f.
      apply Kx.
      intros x.
      apply (Kf x f).
  Defined.

  Instance ContinuationLawfulMonad : MonadLaws ContinuationMonad.
  Proof.
    constructor; unfold K; intros; reflexivity.
  Defined.

End Continuation.

Section Selection.
  Context (S : Type).

  Instance SelectionFunctor : Functor (J S).
  Proof.
    constructor.
    unfold J.
    intros A B f x g.
    apply f.
    apply x.
    intros x'.
    apply g.
    apply f.
    apply x'.
  Defined.

  Instance SelectionLawfulFunctor : FunctorLaws SelectionFunctor.
  Proof.
    constructor; unfold J; intros; compute; reflexivity.
  Defined.

  Instance SelectionApplicative : Applicative (J S).
  Proof.
    constructor; unfold J.
    - intros A x f.
      apply x.
    - intros A B f g h.
      apply f.
      + intros i.
        apply h.
        apply i.
        apply g.
        intros x.
        apply h.
        apply i.
        apply x.
      + apply g.
        intros x.
        apply h.
        apply f.
        * intros i.
          apply h.
          apply i.
          apply x.
        * apply x.
  Defined.

  Instance SelectionMonad : Monad (J S).
  Proof.
    constructor.
    - intros B y _; apply y.
    - unfold J; intros X Y Xf Yg h.
      apply Yg; try assumption.
      apply Xf.
      intros x.
      apply h.
      apply Yg; assumption.
  Defined.

  Instance SelectionLawfulMonad : MonadLaws SelectionMonad.
  Proof.
    constructor; unfold J; intros; reflexivity.
  Defined.

  Definition selectionProd {A B : Type} (x : J S A) (y : J S B) : J S (A * B).
  Proof.
    unfold J in *.
    intros f.
    split.
    - apply x.
      intros x'.
      apply f.
      split.
      + apply x'.
      + apply y.
        intros y'.
        apply f.
        split; assumption.
    - apply y.
      intros y'.
      apply f.
      split.
      + apply x.
        intros x'.
        apply f.
        split; assumption.
      + apply y'.
  Defined.

End Selection.

Section Attainability.
  Context (S X : Type).

  Definition attainedBy (epsilon : J S X) : K S X :=
    fun k => k (epsilon k).

End Attainability.
