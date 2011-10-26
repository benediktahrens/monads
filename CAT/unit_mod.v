Require Export CatSem.CAT.monad_h_morphism_gen.
Require Export CatSem.CAT.cat_TYPE.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.


Section unit_mod.
(*
Variable obC : Type.
Variable morC : obC -> obC -> Type.
Variable C : Cat morC.

Variable obD : Type.
Variable morD : obD -> obD -> Type.
Variable D : Cat morD.
*)
Variables C D : Cat.
Variable P : Monad C.
Variable R : Monad D.
Variable F : Functor C D.

Variable M : colax_Monad_Hom P R F.


Program Instance unit_mod_s : Module_Hom_struct
  (S:=Term (C:=MOD P TYPE)) 
  (T:=PModule M (Term (C:=MOD R TYPE)))
  (fun V y => y).

Definition unit_mod := Build_Module_Hom unit_mod_s.

End unit_mod.
