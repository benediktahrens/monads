
Set Implicit Arguments.
Unset Strict Implicit.

Unset Automatic Introduction.

Module PCF.

Inductive Sorts := 
  | Nat : Sorts
  | Bool : Sorts
  | Arrow : Sorts -> Sorts -> Sorts.

Notation "a '~>' b" := (Arrow a b) (at level 60, right associativity).

End PCF.