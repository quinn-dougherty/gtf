From mathcomp Require Import classical_sets interval all_ssreflect all_algebra order.
From mathcomp.analysis Require Import reals topology measure.

From GTF Require Import SelectionContinuation.
From GTF.ExtLibMod Require Functor Applicative Monad.

Module Type Accept.
  Parameter (t : finType).
End Accept.

Module Probability (R : Return) (A : Accept).

  Local Open Scope ring_scope.
  Module Intervals.
    Local Open Scope classical_set_scope.
    Definition unit_compact : Type := subspace `[0 : R.t, 1 : R.t].
    Inductive convex : seq unit_compact -> Type :=
      | sums_to_one : forall w, foldr (@GRing.add R.t) (0 : R.t) w = 1 -> convex w.
    Definition unit_left_half_open : Type := subspace `]0 : R.t, 1 : R.t].
    Definition unit_open : Type := subspace `]0 : R.t, 1 : R.t[.
  End Intervals.

  Module RV.
    Definition t (A : Type) : Type := A -> R.t.
    Definition leq {A : Type} (f g : t A) : Prop := forall (x : A), f x <= g x.
    Definition scale {A : Type} (k : R.t) (f : t A) : t A := fun x => k * f x.
    Definition add {A : Type} (f g : t A) : t A := fun x => f x + g x.
    Definition constant {A : Type} (rv : t A) : Prop := forall (x1 x2 : A), rv x1 = rv x2.
  End RV.

  Module Continuation := Continuation R.
  Definition t : Type -> Type := Continuation.t.

  Module Type ExpectationLawful.
    Parameter monotone : forall {A : Type} (f : t A) (rv1 rv2 : RV.t A), RV.leq rv1 rv2 -> f rv1 <= f rv2.
    Parameter homogeneous : forall {A : Type} (f : t A) (k : R.t) (rv : RV.t A), f (RV.scale k rv) = k * f rv.
    Parameter additive : forall {A : Type} (f : t A) (rv1 rv2 : RV.t A), f rv1 + f rv2 = f (RV.add rv1 rv2).
    Parameter sendsConstantsToOne : forall {A : Type} (f : t A) (rv : RV.t A), RV.constant rv -> f rv = 1.
  End ExpectationLawful.

  Module GiryOperations (EV : ExpectationLawful).
    Definition flatten {X : Type} (eev : t (t X)) : t X := fun f => eev (fun mu => mu f).
    Definition tensorialStrength {X Y : Type} (inp : X * t Y) : t (X * Y) := let x := fst inp in let v := snd inp in fun f => v (fun y => f (x, y)).
    Definition fmap {X Y : Type} (f : X -> Y) (E : t X) : t Y := Continuation.Functor.fmap f E.
    Definition semidirectProduct {X Y : Type} (f : X -> t Y) (x : t X) : t (X * Y).
    Proof.
      intros j.
      unfold t, Continuation.t in *.
      apply x.
      intros x'.
      apply (f x').
      intros y'.
      apply j.
      apply (x', y').
    Defined.
  End GiryOperations.

End Probability.

(*| Example |*)
