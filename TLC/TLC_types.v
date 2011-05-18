Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Inductive TLCtypes : Type := 
  | TLCbase : TLCtypes
  | TLCarrow : TLCtypes -> TLCtypes -> TLCtypes.


