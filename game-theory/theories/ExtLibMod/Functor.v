From GTF.ExtLibMod Require Import Functions.

Module Type T.
  Parameter F : Type -> Type.
  Parameter fmap : forall {A B : Type}, (A -> B) -> F A -> F B.
End T.

Module Notations (Functor : T).
  Notation "f '<$>' x" := (Functor.fmap f x) (at level 49).
End Notations.

Module Type Lawful (Functor : T).
  Import Functor.
  Parameter fmap_id : forall {A : Type} (x : F A), fmap id x = x.
  Parameter fmap_compose : forall {A B C : Type} (f : A -> B) (g : B -> C) (x : F A),
     fmap (compose g f) x = fmap g (fmap f x).
End Lawful.
