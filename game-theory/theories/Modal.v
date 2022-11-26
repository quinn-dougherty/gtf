
(** Reading Blackburn, De Rijke, Venema *)
(*
From Coq Require Import String.
From mathcomp Require Import classical_sets all_ssreflect all_algebra order.
*)
From ExtLib Require Import Functor.

Module Type Formulae.
  Parameter (base : Type).
  Inductive syntax : Type :=
  | Var : base -> syntax
  | Bottom : syntax
  | Not : syntax -> syntax
  | Or : syntax -> syntax -> syntax
  | Diamond : syntax -> syntax
  .
  Coercion Var : base >-> syntax.
  Definition dual (operator : syntax -> syntax) : syntax -> syntax := fun phi => Not (operator (Not phi)).
  Definition Box : syntax -> syntax := dual Diamond.
  Definition And (phi phi' : syntax) : syntax := Not (Or (Not phi) (Not phi')).
  Definition Arrow (phi phi' : syntax) : syntax := Or (Not phi) phi'.
  Definition Iff (phi phi' : syntax) : syntax := And (Arrow phi phi') (Arrow phi phi').
End Formulae.

Module Temporal (Form : Formulae).
  Import Form.
  Inductive language : Type :=
    | Formula : syntax -> language
    | Future : language -> language
    | Past : language -> language.

  Coercion Formula : syntax >-> language.
  (*
    Definition Going : language -> language := dual Future
    Definition Has : language -> language := dual Past
   *)
End Temporal.

(*
  Declare Scope modal_scope.
  Delimit Scope modal_scope with modal.
  Notation "⊥" := Bottom : modal_scope.
  Notation "¬ p" := (Not p) (at level 90) : modal_scope.
  Notation "p \/ q" := (Or p q) : modal_scope.
  Notation "⋄ p" := (Diamond p) (at level 90) : modal_scope.
  Notation "◻ p" := (Box p) (at level 90) : modal_scope.
  Notation "p --> q" := (Arrow p q) (at level 80) : modal_scope.
  Notation "p <--> q" := (Iff p q) (at level 79) : modal_scope.
*)






(** Lob
Local Open Scope modal_scope.
Definition lob (p : syntax) : syntax := ◻ (◻ p --> p) --> ◻ p.
*)
