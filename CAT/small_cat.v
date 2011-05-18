Require Export CatSem.CAT.CatFunct.
Require Export CatSem.CAT.functor_leibniz_eq.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Automatic Introduction.

Class SmallCat := {
  sobj: Set;
  smor: sobj -> sobj -> Set;
  sstruct:> Cat_struct smor
}.

Definition Cat_from_SmallCat (C: SmallCat) : Cat := Build_Cat
  (obj := sobj) (mor := smor) sstruct.

Coercion Cat_from_SmallCat: SmallCat >-> Cat.

Obligation Tactic := simpl; intros; 
       try apply Equal_hom_refl;
       try apply CompF_oid.

Program Instance SMALLCAT_struct : 
      @Cat_struct SmallCat (fun a b => FunctCat a b) := {
  mor_oid a b := EXT_Functor_oid a b;
  id a := Id a;
  comp a b c f g := CompF f g
}.

Definition SMALLCAT := Build_Cat SMALLCAT_struct.
 

