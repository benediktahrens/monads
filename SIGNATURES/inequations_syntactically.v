Require Export CatSem.PROP_untyped.prop_arities_initial_variant.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Automatic Introduction.
Unset Transparent Obligations.

Section type_of_inequations.

Variable S : Signature.
Print Signature.



Inductive inequation : [nat] -> nat -> Type :=
 | subst : inequation [[1;0]] 0.
 | ident : 

with
  inequation_product : 

Print inequation.