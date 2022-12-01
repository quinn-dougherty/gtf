From ExtLib Require Import Monad.

Definition K (B A : Type) : Type := (A -> B) -> B.
Definition J (B A : Type) : Type := (A -> B) -> A.

Section ArrowMonad.
  Context (A : Type).

  Instance CodArrowMonad : Monad (fun B => A -> B).
  Proof.
    constructor.
    - intros B y x.
      apply y.
    - intros B C alpha Beta x.
      specialize (alpha x).
      apply (Beta alpha x).
  Defined.

End ArrowMonad.

Section ContinuationMonad.
  (* Although `ExtLib` exports a `ContMonad`, we're going to reimplement here. *)
  Context (S : Type).

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

End ContinuationMonad.

Section SelectionMonad.
  Context (S : Type).

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

End SelectionMonad.
