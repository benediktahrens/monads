
Set Implicit Arguments.
Unset Strict Implicit.

Axiom functional_extensionality : forall (A B : Type)(f g : A -> B),
  (forall x, f x = g x) -> f = g.


      