
Set Implicit Arguments.
Unset Strict Implicit.

Unset Automatic Introduction.

Module PCF.

Inductive types := 
  | Nat : types
  | Bool : types
  | arrow : types -> types -> types.

End PCF.