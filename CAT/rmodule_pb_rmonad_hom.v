Require Export CatSem.CAT.rmonad.
Require Export CatSem.CAT.rmonad_hom.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

(** pullback *)


Section pullback.
Variables obC obD : Type.
Variable morC : obC -> obC -> Type.
Variable morD : obD -> obD -> Type.
Variable C : Cat_struct morC.
Variable D : Cat_struct morD.
Variable F : Functor C D.

Variables P Q : RMonad F.
Variable h : RMonad_Hom P Q.

Section pb_def.

Variable obE : Type.
Variable morE : obE -> obE -> Type.
Variable E : Cat_struct morE.

Section PbRMod.

Variable N : RMOD Q E.

Obligation Tactic := idtac.

Program Instance PbRMod_struct : RModule_struct P E N := {
  rmkleisli c d f := rmkleisli (f ;; h d )
}.
Next Obligation.
Proof.
  intros c d.
  unfold Proper; red.
  intros x y H. 
  rewrite H.
  rmonad.
Qed.
Next Obligation.
Proof.
  rmonad.
  apply h.
Qed.
Next Obligation.
Proof.
  rmonad.
  apply h.
Qed.

Definition PbRMod : RMOD P E := Build_RModule PbRMod_struct.

End PbRMod.

Section PbRMod_Hom.

Variables M N : RMOD Q E.
Variable S : M ---> N.

Obligation Tactic := rmonad.

Program Instance PbRMod_Hom_struct : RModule_Hom_struct 
       (M := PbRMod M) (N:=PbRMod N) S.
(*Next Obligation.
Proof.
  simpl.
  rewrite (rmod_hom_rmkl);
  try cat.
  apply S.
Qed.
*)
Definition PbRMod_Hom : PbRMod M ---> PbRMod N := 
      Build_RModule_Hom PbRMod_Hom_struct.

End PbRMod_Hom.

Obligation Tactic := unfold Proper; red; simpl; rmonad.

Program Instance PbRMOD_struct : Functor_struct PbRMod_Hom.

Canonical Structure PbRMOD := Build_Functor PbRMOD_struct.

Section pb_prod.

Variable H : Cat_Prod E.

Existing Instance RMOD_PROD.

Variables M N : RModule Q E.

Notation "a 'x' b" := (product a b)(at level 60).

Obligation Tactic := cat.

Program Instance PROD_RPB_s : RModule_Hom_struct
  (M:= product (C:=RMOD P E) (PbRMod M) (PbRMod N))
  (N:=PbRMod (product (C:=RMOD Q E) M N))
  (fun c => id (M c x N c) ).

Definition PROD_RPB : 
   (PbRMod M x PbRMod N) ---> PbRMod (M x N) := 
       Build_RModule_Hom PROD_RPB_s.

End pb_prod.

End pb_def.

Program Instance PbRMod_ind_Hom_struct :
  RModule_Hom_struct (M:= P) (N:=PbRMOD _ Q) (fun x => h x).
Next Obligation.
Proof.
  rmonad;
  try apply h.
Qed.

Definition PbRMod_ind_Hom : Taut_RMod P ---> PbRMod Q := 
     Build_RModule_Hom PbRMod_ind_Hom_struct.


End pullback.

Coercion PbRMod_ind_Hom : RMonad_Hom >-> mor.
