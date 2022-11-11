(** Coq takes on many identities, with two in particular that you need to be comfortable with.

 On the one hand, Coq is a _dependently typed programming language_. In other words, we use it to reason about functions that consume things and produce data types.

 On the other hand, Coq is a _proof scripting language_. In other words, we use it to compute terms of particular types.

 Of course the only sensible way to proceed is by example
 *)

(** Natural numbers are a type *)
Print nat.
Check nat_ind. (* recall induction*)
(** Ordered collections tagged with their fixed length are a dependent type. *)
From Coq Require Import Vector.
Check t.
(** The point here is that the type `t` is a function that lands in `Type`. It's not a type yet until it is applied to some type (the elements) and some nat (the length) *)

(** We also reason about vectors t A n (for type A and nat n) with induction *)
Check t_ind.
(** The general story of which natural number induction is a special case is called _structural induction_. *)

(** We can do structural induction every time an `_ind` is generated, which is anytime we use the `Inductive` keyword. *)
Inductive tree (A : Type) : Type := Leaf (x : A) | Node (t1 : tree A) (t2 : tree A).

(** So if we want to prove that a function from A to B can turn a tree A into a tree B, *)
Theorem fmap_tree {A B : Type} (f : A -> B) (x : tree A) : tree B.
Proof.
  (* we apply the induction principle *)
  induction x. (*the _tactic_ induction invokes the term `tree_ind` under the hood *)
  - apply (Leaf _ (f x)). (*construct the exact term for the base case*)
  - apply (Node _ IHx1 IHx2). (* construct the exact term for the recursive step. *)
Defined.
(* This is the _proof script_ version of implementing `fmap_tree`.

equivalently, we can provide a direct definition *)
Fixpoint fmap_tree' {A B : Type} (f : A -> B) (x : tree A) : tree B
  := match x with
     | Leaf _ x => Leaf _ (f x)
     | Node _ t1 t2 => Node _ (fmap_tree' f t1) (fmap_tree' f t2)
     end.

(** Bool and Prop

NOTE: I WROTE THIS BEFORE I DECIDED TO USE MATHCOMP, SO IT'LL BE DELETED

We will leverage the property of _decidability_, which some propositions have.

Coq takes place in _constructive logic_, meaning _law of excluded middle (LEM) is omitted_.

In many elementary logic courses, bool - the values of boolean algebra - and prop - the set of propositions - are strictly equivalent. One of the reasons they're able to do this is LEM
 *)

Module LEM_test.
  Axiom LEM : forall (P : Prop), P \/ ~ P.
End LEM_test.
(* The "middle" in the name is the idea of indeterminacy, we don't know if the proposition is true or false. With this axiom, we _exclude_ the middle, we exclude the ability for propositions to be indeterminate *)

(* In constructivism, with it's primary logic called _intuitionism_, we do not have such an axiom. For many propositions, we simply don't know if they're true or false. *)

(* One thing we like to do even in intuitionism is distinguish a class of propositions for which we can recover the equivalence between bool and prop*)

(* The functional account of this lives in the standard library *)
From Coq.Logic Require Import Decidable.
Check decidable.
Print decidable.

(* We may, toward the middle or the end of the book, rely on the typeclass account of this, but idk yet.*)

From Coq Require Import Lia.
From Coq.Arith Require Import PeanoNat.
Check Nat.Even.
Print Nat.Even.

Lemma L1 : forall n, ~ (Nat.Even n /\ Nat.Even (S n)).
Proof.
  intros n contra.
  destruct contra.
  induction n as [| n' IHn'].
  - unfold Nat.Even in H0.
    destruct H0 as [m H0].
    lia.
  - inversion H.
    unfold Nat.Even in H, H0.
    destruct H as [m H].
    destruct H0 as [m0 H0].
    rewrite H in H1.
    lia.
Qed.

Theorem even_dec : forall n, decidable (Nat.Even n).
Proof.
  intros n.
  unfold decidable.
  induction n.
  - left.
    unfold Nat.Even.
    exists 0.
    reflexivity.
  - destruct IHn.
    + right.
      intros contra.
      unfold Nat.Even in H, contra.
      destruct H as [m H].
      destruct contra as [m' contra].
      subst.
      assert (G : Nat.Even (2 * m)). { unfold Nat.Even. exists m. reflexivity. }
      assert (G0 : Nat.Even (2 * m')). { unfold Nat.Even. exists m'. reflexivity. }
      apply Nat.Odd_succ in G. rewrite contra in G.
      apply (Nat.Even_Odd_False (2 * m') G0 G).
    + left.
      assert (G : Nat.Odd n). {
        unfold Nat.Odd. induction n.
        * exfalso. apply H. unfold Nat.Even. exists 0. reflexivity.
        * rewrite Nat.Even_succ in H. exfalso. apply H. apply IHn. intros contra. unfold Nat.Even in contra. destruct contra as [m' contra]. subst. apply H. unfold Nat.Odd. apply IHn. intros contra'.
      }
      rewrite Nat.Even_succ.
      apply G.
