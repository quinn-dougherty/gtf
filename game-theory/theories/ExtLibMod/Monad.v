From GTF.ExtLibMod Require Import Functions.

Module Type T.
  Parameter F : Type -> Type.
  Parameter ret : forall {A : Type}, A -> F A.
  Parameter bind : forall {A B : Type}, F A -> (A -> F B) -> F B.
End T.

Module Notations (Monad : T).

  Notation "c >>= f" := (Monad.bind c f) (at level 58, left associativity).
  Notation "f =<< c" := (Monad.bind _ _ _ _ c f) (at level 61, right associativity).
  (*Notation "f >=> g" := (mcompose _ _ _ _ _ f g) (at level 61, right associativity).*)

  Notation "e1 ;; e2" := (Monad.bind e1 (fun _ => e2)) (at level 61, right associativity).

End Notations.

Module Type Lawful (Monad : T).
  Module MonadNotations := Notations Monad.
  Import MonadNotations.

  Parameter bind_of_return : forall {A B : Type} (x : A) (f : A -> Monad.F B), Monad.ret x >>= f = f x.
  Parameter return_of_bind : forall {A : Type} (x : Monad.F A), x >>= Monad.ret = x.
  Parameter bind_associativity : forall {A B C : Type} (x : Monad.F A) (f : A -> Monad.F B) (g : B -> Monad.F C),
      x >>= f >>= g = x >>= (fun x' => f x' >>= g).
End Lawful.
