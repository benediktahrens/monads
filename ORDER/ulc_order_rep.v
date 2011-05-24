Require Export CatSem.CAT.rmodule_TYPE.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Section ULC_rep.

(** a lot of notation to make things readable *)

Notation "a 'x' b" := (product (C:=RMOD _ _) a b) (at level 30).
Notation "'d' M" := (DER_RMOD_not _ _ M) (at level 25).
Notation "'*'" := (Term (C:=RMOD _ PO)).

Notation "f 'X' g" := (product_mor _ f g)(at level 30).

Notation "'PRPB'":= (PROD_RPB _ _ _ _ ).
Notation "'PBM'":= (#(PbRMOD _ _ )).
Notation "'DM'":= (#(DER_RMOD_not _ _ )).
Notation "'DPB'":= (DER_RPB_not _ _ ).

(* this might be changed for the module-morphism-version,
   if we decide to use it *)
Notation "y [* := z ]":= (Rsubstar_not z y)(at level 55).

(** a monad is a representation if it is accompagnied by 
    - a lot of morphisms of modules 
    - beta-reduction
*)

Class ULCPO_rep_struct (P : RMonad SM_po) := {
  app : P x P ---> P;
  abs : d P ---> P;
  beta_red : forall V y z, 
        app V (abs V y, z) << y[*:= z] 
}.


Record ULCPO_rep := {
  ulcpo_rep_monad :> RMonad SM_po ;
  ulcpo_rep_struct :> ULCPO_rep_struct ulcpo_rep_monad
}.

Existing Instance ulcpo_rep_struct.

(** morphisms of representations *)

Section ULCPO_rep_Hom.

Variables P R : ULCPO_rep.

Section Rep_Hom_Class.

Variable S : RMonad_Hom P R.

Notation "'ST'":= (PbRMod_ind_Hom S).


Class ULCPO_rep_Hom_struct := {

  app_Hom:
        app ;; ST  == 
          ST X ST ;; PRPB ;; PBM (app)
;
 
  abs_Hom:  
         abs ;; ST  ==
          DM ST ;; DPB ;; PBM (abs) 

}.

End Rep_Hom_Class.

(** the type of morphismes of representations P -> R *)

Record ULCPO_rep_Hom := {
  rep_Hom_monad :> RMonad_Hom P R ;
  rep_Hom_monad_struct :> ULCPO_rep_Hom_struct rep_Hom_monad
}.

End ULCPO_rep_Hom.

End ULC_rep.
Existing Instance rep_Hom_monad_struct.
Existing Instance ulcpo_rep_struct.

