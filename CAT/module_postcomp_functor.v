Require Export CatSem.CAT.monad_h_module.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Section postcomp_functor.
(*
Variable obC : Type.
Variable morC : obC -> obC -> Type.
Variable C : Cat morC.
*)
Variable C : Cat.

Variable P : Monad C.
(*
Variable obD : Type.
Variable morD : obD -> obD -> Type.
Variable D : Cat morD.
*)
Variables D E : Cat.
(*
Variable obE : Type.
Variable morE : obE -> obE -> Type.
Variable E : Cat morE.
*)
Variable F : Functor D E.

Section on_modules.

Variable M : Module P D.


Obligation Tactic := idtac.

Program Instance Mod_postcomp_F_struct : Module_struct P  
     (fun x => F (M x)) := {
  mkleisli a b f := #F (mkleisli f)
}.
Next Obligation.
Proof.
  unfold Proper; red;
  intros;
  rew_all;
  cat.
Qed.
Next Obligation.
Proof.
  intros.
  rewrite <- FComp.
  rew mklmkl.
  cat.
Qed.
Next Obligation.
Proof.
  intros.
  simpl.
  rew mklweta.
  cat.
Qed.

Definition Mod_postcomp_F := Build_Module Mod_postcomp_F_struct.

End on_modules.

Section on_module_morphisms.

Variables M N : Module P D.

Variable S : M ---> N.

Obligation Tactic := idtac.

Program Instance Mod_postcomp_F_mor_struct : Module_Hom_struct
  (S := Mod_postcomp_F M)
  (T := Mod_postcomp_F N) (fun x => #F (S x)).
Next Obligation.
Proof.
  simpl; intros.
  repeat rewrite <- FComp.
  rew (mod_hom_mkl).
  cat.
  app_all.
Qed.

Definition Mod_postcomp_F_mor : Mod_postcomp_F M ---> 
                                Mod_postcomp_F N := 
   Build_Module_Hom Mod_postcomp_F_mor_struct.

End on_module_morphisms.

Obligation Tactic := simpl; intros; try unf_Proper;
                 cat; rew_all; cat.

Program Instance MOD_pc_F : 
  Functor_struct (Fobj := Mod_postcomp_F) 
  Mod_postcomp_F_mor. 

End postcomp_functor.






















