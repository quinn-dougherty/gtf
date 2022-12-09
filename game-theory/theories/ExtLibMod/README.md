# `coq-ext-lib-mod`

A modular answer to the mighty [`coq-ext-lib`](https://github.com/coq-community/coq-ext-lib/), factoring out typeclasses.

Bob Harper, in [Modules Matter Most](https://existentialtype.wordpress.com/2011/04/16/modules-matter-most/):

> There are two fundamental problems with type classes. The first is that they insist that a type can implement a type class in exactly one way. For example, according to the philosophy of type classes, the integers can be ordered in precisely one way (the usual ordering), but obviously there are many orderings (say, by divisibility) of interest. The second is that they confound two separate issues: specifying how a type implements a type class and specifying when such a specification should be used during type inference.

## Example: `list`

Lists can be thought of as (unlawfullly) applicative in more than one way.

```coq
From Coq Require Import List.
Import ListNotations.

From GTF.ExtLibMod Require Applicative.

(* You can interpret the applicative list as ziplist *)
Module ZipList <: Applicative.T.
  Definition F := list. (* Confused about exporting *)
  Definition pure {A : Type} (x : A) : F A := [x].
  Definition ap {A B : Type} (fs : F (A -> B)) (xs : F A) : F B := map (fun t => fst t (snd t)) (combine fs xs).
End ZipList.

(* Or as cartesian product. *)
Module CartesianProductList <: Applicative.T.
  Definition F := list.
  Definition pure {A : Type} (x : A) : F A := [x].
  Definition ap {A B : Type} (fs : F (A -> B)) (xs : F A) : F B := map (fun t => (fst t) (snd t)) (list_prod fs xs).
End CartesianProductList.
```

For your modules which are lawful, showing lawfulness would look like this.

```coq
From Coq Require Import List.
Import ListNotations.

From GTF.ExtLibMod Require Monad.

Module TMonad <: Monad.T.
  Definition F := list.
  Definition ret {A : Type} (x : A) : F A := [x].
  Definition bind {A B : Type} (x : F A) (f : A -> F B) : F B := concat (map f x).
End TMonad.

Module MonadNotations := Monad.Notations TMonad.

Module TLawfulMonad : Monad.Lawful TMonad.
  Import MonadNotations.

  Theorem bind_of_return : forall {A B : Type} (x : A) (f : A -> TMonad.F B), TMonad.ret x >>= f = f x.
  Proof.
    intros A B x f.
    unfold TMonad.ret, TMonad.bind.
    apply app_nil_r.
  Qed.
  Theorem return_of_bind : forall {A : Type} (x : TMonad.F A), x >>= TMonad.ret = x.
  Proof.
    unfold TMonad.F, TMonad.ret, TMonad.bind.
    intros A xs.
    induction xs; auto.
    simpl.
    rewrite IHxs.
    reflexivity.
  Qed.
  Theorem bind_associativity : forall {A B C : Type} (x : TMonad.F A) (f : A -> TMonad.F B) (g : B -> TMonad.F C),
      x >>= f >>= g = x >>= (fun x' => f x' >>= g).
  Proof.
    unfold TMonad.F, TMonad.bind.
    intros A B C x f g.
    induction x; auto.
    simpl.
    repeat rewrite <- concat_app.
    induction (f a).
    - repeat rewrite app_nil_l.
      rewrite IHx.
      reflexivity.
    - simpl.
      rewrite IHl.
      reflexivity.
  Qed.
End TL
```
