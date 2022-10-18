From Coq Require Import Reals Lra Relations ssreflect ssrbool.

(** Game theory with agents who like to gain something called utility.

We will accumulate properties of this "utility" thing over time. To begin, we only need the structure of a decidable ordering relation.
 *)

Module Type decType.
  Parameter T : Type.
  Parameter R : relation T.
  Axiom decR : forall (x y : T), decidable (R x y).
End decType.

Module RelToBool (M : decType).
  Definition decide (x y : M.T) : bool
    := match M.decR x y with
       | left _ => true
       | right _ => false
       end.
End RelToBool.

Module TwoByTwo (M : decType).

  Module Lattice := RelToBool M.

  Inductive playerOne : Type := Up | Down.
  Inductive playerTwo : Type := Left | Right.

  Definition Game : Type := playerOne -> playerTwo -> M.T * M.T.

  Definition dominantOne (game : Game) : option playerOne :=
    if Lattice.decide (fst (game Up Left)) (fst (game Up Right)) then Some Up else
      if Lattice.decide (fst (game Down Left)) (fst (game Down Right)) then Some Down else None.

  Definition dominantTwo (game : Game) : option playerTwo :=
    if Lattice.decide (snd (game Up Left)) (snd (game Down Left)) then Some Left else
      if Lattice.decide (snd (game Up Right)) (snd (game Down Right)) then Some Right else None.

End TwoByTwo.

(* Real numbers *)

Module RgeDec : decType.
  Definition T := R.
  Definition R := Rge.
  Theorem decR : forall (x y : T), decidable (R x y).
  Proof.
    intros x y.
    unfold decidable, R.
    apply Rge_dec.
  Qed.

End RgeDec.

Module RTwoByTwo := TwoByTwo RgeDec.
