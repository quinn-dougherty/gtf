(* https://en.wikipedia.org/wiki/Von_Neumann%E2%80%93Morgenstern_utility_theorem *)

From Coq Require Streams.

From Paco Require Import paco.
From mathcomp Require Import classical_sets interval all_ssreflect all_algebra order.
From mathcomp.analysis Require Import reals topology measure.
Import Order.Theory.

From GTF Require Import GiryClasses.

Module VNM (Number : Interval).
  Module P := Probability Number.
  Import P.
End VNM.

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
