Definition id {A : Type} (x : A) : A := x.
Definition compose {A B C : Type} (f : B -> C) (g : A -> B) : A -> C := fun (x : A) => f (g x).
