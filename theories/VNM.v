(* https://en.wikipedia.org/wiki/Von_Neumann%E2%80%93Morgenstern_utility_theorem *)
From Paco Require Import paco.
From mathcomp Require Import classical_sets interval all_ssreflect all_algebra order.
From mathcomp.analysis Require Import reals topology measure.
Import Order.Theory.

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

Module Stream.
  CoInductive t {A : Type} : Type := cons (x : A) (y : t) : t.
  Definition hd {A : Type} (stream : t) : A := match stream with | cons x _ => x end.
  Definition tl {A : Type} (stream : t) : @t A := match stream with | cons _ y => y end.
  CoFixpoint map {A B : Type} (f : A -> B) (stream : @t A) : @t B
    := match stream with | cons x y => cons (f x) (map f y) end.
End Stream.

Module Type DiscreteDistribution (Number : Interval).

  Context (O : finPOrderType tt).

  Local Open Scope ring_scope.

  Class rv : Type := {
      pmf :> {ffun O -> Number.unit_compact};
      convex : foldr (@GRing.add Number.t) (0 : Number.t) (map pmf (enum O)) = 1;
    }.

End DiscreteDistribution.

Module Type Lottery (Number : Interval) (Dist : DiscreteDistribution Number).
  Local Open Scope order_scope.
  Notation "o1 == o2" := (o1 <= o2 && o2 <= o1) : order_scope.
  Close Scope order_scope.

  Parameter (O : finPOrderType tt).
  Definition t : Type := seq (Number.unit_compact * O).

  Definition lottery (ps : Number.fin_unit_compact) `{Number.convex ps} {H : length ps = #|O|} : t
    := zip ps (enum O).
  Local Open Scope ring_scope.
  Definition singletonOutcome (o : O) : t := nseq Nat.one ((1 : Number.t), o).
  Declare Scope lottery_scope.
  Delimit Scope lottery_scope with lottery.
  Notation "'.|' o '|'" := (singletonOutcome o) : lottery_scope.

  Parameter (o1 : O).
  Check {ffun O -> Number.unit_compact}.
  Check .|o1|%lottery.

End Lottery.

Module Type Rationality
  (Number : Interval)
  (Dist : DiscreteDistribution Number)
  (Lott : Lottery Number Dist)
.
  Local Open Scope order_scope.

  Local Open Scope lottery_scope.
  Class axioms : Type := {
      completeness : forall (o1 o2 : Lott.O), (o1 <= o2) || (o2 <= o1) || (o1 == o2);
      transitivity : forall (o1 o2 o3 : Lott.O), o1 <= o2 -> o2 <= o3 -> o1 <= o3;
    }.
End Rationality.
