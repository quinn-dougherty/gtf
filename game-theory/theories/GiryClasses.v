(*| Legacy |*)
From Paco Require Import paco.
From ExtLib Require Import Functor Applicative Monad MonadLaws CoMonad.
From mathcomp Require Import classical_sets interval all_ssreflect all_algebra order.
From mathcomp.analysis Require Import reals topology measure.
Definition swap {A B C : Type} (f : A -> B -> C) : B -> A -> C.
Proof. intros y x. apply (f x y). Defined.

Module Type Interval.
  Local Open Scope ring_scope.
  Local Open Scope classical_set_scope.
  Parameter (t : realType).
  Definition unit_compact : Type := subspace `[0 : t, 1 : t].
  Definition fin_unit_compact : Type := seq unit_compact.
  Class convex (ps : fin_unit_compact) : Type := {
      sums_to_one : foldr (@GRing.add t) (0 : t) ps = 1
    }.
  Definition unit_left_half_open : Type := subspace `]0 : t, 1 : t].
  Definition unit_open : Type := subspace `]0 : t, 1 : t[.
End Interval.

(*| A probability distribution knows how to turn a random variable (a value assignment) to an expected value. |*)
Module Probability (Number : Interval).

  Local Open Scope ring_scope.

  Section RandomVariable.
    Context {X : Type}.
    Definition RV : Type := X -> Number.t.
    Definition rvLeq : RV -> RV -> Prop := fun g g' => forall (x : X), g x <= g' x.
    Definition rvScale : Number.t -> RV -> RV := fun k f x => k * f x.
    Definition rvAdd  : RV -> RV -> RV := fun f g x => f x + g x.
  End RandomVariable.

  Section Expectation.
    Context {X : Type}.
    Definition EV : Type := @RV X -> Number.t.
    Definition monotone (f : EV) : Prop := forall g g', rvLeq g g' -> f g <= f g'.
    Definition scaleative (f : EV) : Prop := forall (k : Number.t) (rv : RV), f (rvScale k rv) = k * f rv.
    Definition additive (f : EV) : Prop := forall (rv1 rv2 : RV), f rv1 + f rv2 = f (rvAdd rv1 rv2).
    Definition constant (rv : RV) : Prop := forall (x1 x2 : X), rv x1 = rv x2.
    Definition sendsConstantsToOne (f : EV) : Prop
      := forall (rv : RV), constant rv -> f rv = 1.

    Class EVLaws (E : EV) : Type := {
      EV_monotone : monotone E;
      EV_scaleative : scaleative E;
      EV_rvAdditive : additive E;
      EV_sendsConstantsToOne : sendsConstantsToOne E
    }.

  End Expectation.

  (*| Expected value is a monad. |*)
  #[export] Instance EVMonad : Monad (@EV).
  Proof.
    constructor.
    - intros X x.
      unfold EV, RV.
      intros rv.
      apply (rv x).
    - intros X Y mx mf.
      unfold EV, RV in *.
      intros rv.
      remember (swap mf) as mf'; clear Heqmf'.
      specialize (mf' rv).
      specialize (mx mf').
      apply mx.
  Defined.

  (*| Correctness of monad proof. |*)
  #[export] Instance EVLawfulMonad : MonadLaws EVMonad.
  Proof.
    constructor; intros; unfold bind, ret, EVMonad, swap; reflexivity.
  Qed.

  Definition dirac {X : Type} (x : X) : EV := fun f => f x. (* monadic return, in theory *)

  Section Giry.
    Context {X Y : Type} (E : @EV X) (E' : @EV Y).
    Context `{EVLaws (@EV X)} `{EVLaws (@EV Y)}.

    Definition flatten (eev : @EV (@EV X)) : @EV X := fun f => eev (fun mu => mu f).
    Definition tensorialStrength (inp : X * (@EV Y)) : @EV (X * Y) := let x := fst inp in let v := snd inp in fun f => v (fun y => f (x, y)).
    (* Definition semidirectProduct (f : X -> @EV Y) (x : @EV X) : @EV (X * Y) := fun f => x (fun mu => f mu (fun y => mu(x,y))). *)
    Definition fmap__giry (f : X -> Y) (x : @EV X) : @EV Y.
      Proof.
        unfold EV, RV in *.
        intros y.
        apply x; intros f'.
        apply y; apply f; apply f'.
      Defined.

  End Giry.

End Probability.
