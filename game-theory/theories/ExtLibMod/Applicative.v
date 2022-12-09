From GTF.ExtLibMod Require Import Functions.

Module Type T.
  Parameter F : Type -> Type.
  Parameter pure : forall {A : Type}, A -> F A.
  Parameter ap : forall {A B : Type}, F (A -> B) -> F A -> F B.
End T.

Module Notations (Applicative : T).
  Notation "ff '<*>' fx" := (Applicative.ap ff fx) (at level 10, left associativity).
End Notations.

Module Type Lawful (Applicative : T).
  Module ApplicativeNotations := Notations Applicative.
  Import ApplicativeNotations.
  Parameter ap_identity : forall {A : Type} (x : Applicative.F A), (Applicative.pure id) <*> x = x.
  Parameter ap_homomorphism : forall {A B : Type} (f : A -> B) (x : A), (Applicative.pure f) <*> (Applicative.pure x) = Applicative.pure (f x).
  Parameter ap_composition : forall {A B C : Type} (u : Applicative.F (A -> B -> C)) (v : Applicative.F (B -> A)) w,
      Applicative.pure compose <*> u <*> v <*> w = u <*> (v <*> w).

End Lawful.
