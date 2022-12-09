From Coq Require Import List.
Import ListNotations.

From GTF.ExtLibMod Require Import Functions.
From GTF.ExtLibMod Require Functor Applicative Monad.

Module TFunctor <: Functor.T.
  Definition F := fun A => list A.
  Definition fmap {A B : Type} (f : A -> B) (x : F A) : F B := map f x.
End TFunctor.

Module FunctorNotations := Functor.Notations TFunctor.

Module TLawfulFunctor : Functor.Lawful TFunctor.
  Import FunctorNotations.
  Theorem fmap_id : forall {A : Type} (x : TFunctor.F A), id <$> x = x.
  Proof.
    intros A x.
    unfold TFunctor.F in x.
    unfold TFunctor.fmap.
    apply map_id.
  Defined.

  Theorem fmap_compose : forall {A B C : Type} (f : A -> B) (g : B -> C) (x : TFunctor.F A),
      (compose g f) <$> x = g <$> (f <$> x).
  Proof.
    intros A B C f g x.
    unfold TFunctor.fmap.
    unfold compose.
    unfold TFunctor.F in x.
    induction x; auto.
    simpl. rewrite <- IHx.
    reflexivity.
  Defined.
End TLawfulFunctor.

Module TZip <: Applicative.T.
  Export TFunctor.
  Definition F := F. (* Confused about exporting *)
  Definition pure {A : Type} (x : A) : F A := [x].
  Definition ap {A B : Type} (fs : F (A -> B)) (xs : F A) : F B := map (fun t => fst t (snd t)) (combine fs xs).
End TZip.

Module TCartesian <: Applicative.T.
  Export TFunctor.
  Definition F := F.
  Definition pure {A : Type} (x : A) : F A := [x].
  Definition ap {A B : Type} (fs : F (A -> B)) (xs : F A) : F B := map (fun t => (fst t) (snd t)) (list_prod fs xs).
End TCartesian.

(*| Neither are lawful. |*)
(*
Module TLawfulCartesian : Applicative.Lawful TCartesian.
  Module ApplicativeNotations := Applicative.Notations TCartesian.
  Import ApplicativeNotations.
  Theorem ap_identity : forall {A : Type} (x : list A), (TCartesian.pure id) <*> x = x.
  Proof.
    intros A xs.
    unfold TCartesian.pure, TCartesian.ap.
    simpl.
    rewrite app_nil_r.
    induction xs; auto; simpl.
    rewrite IHxs.
    reflexivity.
  Qed.
  Theorem ap_homomorphism : forall {A B : Type} (f : A -> B) (x : A), (TCartesian.pure f) <*> (TCartesian.pure x) = TCartesian.pure (f x).
  Proof. compute; reflexivity. Defined.
  Lemma empty_map {A B : Type} (f : A -> B) : map f [] = []. Proof. reflexivity. Qed.
  Lemma empty_product_r {A B : Type} (xs : list A) : list_prod xs (@nil B) = []. Proof. induction xs; auto. Qed.
  Lemma empty_product_l {A B : Type} (ys : list B) : list_prod (@nil A) ys = []. Proof. induction ys; auto. Qed.
  Lemma map_empty {A B : Type} (f : A -> B) (xs : list A) : map f xs = [] -> xs = [].
  Proof.
    intros H.
    induction xs; auto.
    inversion H.
  Qed.
  Lemma prod_cons_l {A B : Type} (xs : list A) (ys : list B) (x : A) : list_prod (x :: xs) ys = map (pair x) ys ++ list_prod xs ys.
  Proof. induction ys; auto. Qed.
  Lemma app_eq_l {A : Type} (xs1 xs2 ys : list A) : ys ++ xs1 = ys ++ xs2 -> xs1 = xs2.
  Proof. intros H. rewrite app_inv_head_iff in H. apply H. Qed.
  Lemma app_eq_r {A : Type} (xs1 xs2 ys : list A) : xs1 ++ ys = xs2 ++ ys -> xs1 = xs2.
  Proof. intros H. rewrite app_inv_tail_iff in H. apply H. Qed.
  Hint Resolve empty_map empty_product_r empty_product_l map_empty prod_cons_l app_eq_l app_eq_r.

  (* _ordered_ cartesian product may be impossible to implement applicative. *)
  Theorem ap_composition : forall {A B C : Type} (u : TCartesian.F (A -> B -> C)) (v : TCartesian.F (B -> A)) (w : TCartesian.F B),
      TCartesian.pure compose <*> u <*> v <*> w = u <*> (v <*> w).
  Proof.
    unfold TCartesian.F, TFunctor.F.
    intros A B C u v w.
    unfold TCartesian.pure.
    generalize dependent w; generalize dependent v; induction u; intros v; induction v; intros w; induction w; auto.
    - unfold TCartesian.ap.
      repeat rewrite empty_product_r.
      repeat rewrite empty_map.
      rewrite empty_product_r.
      rewrite empty_map.
      reflexivity.
    - unfold TCartesian.ap.
      repeat rewrite empty_product_l.
      repeat rewrite empty_map.
      repeat rewrite empty_product_r.
      repeat rewrite empty_map.
      rewrite empty_product_l.
      rewrite empty_map.
      reflexivity.
    - unfold TCartesian.ap.
      repeat rewrite empty_product_r.
      repeat rewrite empty_map.
      rewrite empty_product_r.
      rewrite empty_map.
      reflexivity.
    - specialize (IHu (a0 :: v) (a1 :: w)).
      unfold TCartesian.ap.
      simpl.
      repeat rewrite app_nil_r.



End TLawfulCartesian.
*)

Module TMonad <: Monad.T.
  Definition F := list.
  Definition ret {A : Type} (x : A) : F A := [x].
  Definition bind {A B : Type} (x : F A) (f : A -> F B) : F B := concat (map f x).
End TMonad.

Module MonadNotations := Monad.Notations TMonad.

Module TLawfulMonad : Monad.Lawful TMonad.

  Module MonadNotations := MonadNotations.
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
End TLawfulMonad.
