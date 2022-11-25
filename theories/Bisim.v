From mathcomp Require Import all_ssreflect order.

Section LTS.
  Context {states actions : finType}.
  Definition transition : Type := states -> actions -> states -> Prop.
End LTS.
(*
Inductive bisimulation {states actions : finType} (F : @transition states actions) : states -> states -> Prop :=
  | bisimulation_start (P Q : states) : bisimulation F P Q
  | bisimulation_forward1 (P Q : states) :
    bisimulation F P Q -> forall (mu : actions) (P' : states), F P mu P' -> exists (Q' : states), F Q mu Q' -> bisimulation F P' Q'.
*)
(*
Record LTS : Type :=
  mkLTS
    {
      states : finType;
      actions : finType;
      transition : states -> actions -> states -> Prop
    }.

CoInductive bisimulation (L : LTS) : states L -> states L -> Prop :=
  | bisim_start (P Q : states L) : bisimulation L P Q
  | bisim_forward1 (P Q : states L) :
    bisimulation L P Q
    -> forall (mu : actions L) (P' : states L),
        transition L P mu P'
        -> exists (Q' : states L), transition L Q mu Q' -> bisimulation L P' Q'.

Inductive bisimulation (L : LTS) : states L -> states L -> Prop :=
  | bisim_start (P Q : states L) : bisimulation L P Q
  | bisim_forward1 (P Q : states L) (_ : bisimulation L P Q) :
    forall (mu : actions L) (P' : states L), transition L P mu P' -> exists Q', transition L Q mu Q' -> bisimulation L P' Q'
  | bisim_forward2 (P Q : states L) (_ : bisimulation L P Q) :
    forall (mu : actions L) (Q' : states L), transition L Q mu Q' -> exists P', transition L P mu P' -> bisimulation L P' Q'.
*)
