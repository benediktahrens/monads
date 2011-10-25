Require Export CatSem.CAT.rmodule_TYPE.
Require Export CatSem.TLC.TLC_types.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Section TLC_rep.

(** a lot of notation to make things readable *)

(*Notation "'TY'" := PCF.types.*)

Notation "'TY'" := TLCtypes. 

Notation "'IP'" := (IPO TY).
Notation "a '~>' b" := (TLCarrow a b) 
   (at level 69, right associativity).
Notation "a 'x' b" := (product a b) (at level 30).
Notation "M [ z ]" := (FIB_RMOD _ z M) (at level 35).
Notation "'d' M // s" := (DER_RMOD _ _ s M) (at level 25).
Notation "'*'" := (Term (C:=RMOD _ Ord)).

Notation "f 'X' g" := (product_mor _ f g)(at level 30).

Notation "'FM'" := (#(FIB_RMOD _ _ )).
Notation "'FPB'":= (FIB_RPB _ _ _ ).
Notation "'PRPB'":= (PROD_RPB _ _ _ _ ).
Notation "'PBM'":= (#(PbRMOD _ _ )).
Notation "'DM'":= (#(DER_RMOD _ _ _ )).
Notation "'DPB'":= (DER_RPB _ _ _ ).

(* this might be changed for the module-morphism-version,
   if we decide to use it *)
Notation "y [* := z ]":= (Rsubstar z _ y)(at level 55).

(** a monad is a representation if it is accompagnied by 
    - a lot of morphisms of modules 
    - beta-reduction
*)

Class TLCPO_rep_struct (P : RMonad (IDelta TY)) := {
  App : forall r s, (P[r~>s]) x (P[r]) ---> P[s];
  Abs : forall r s, (d P // r)[s] ---> P[r ~> s];

  beta_red : forall r s V y z, 
        App r s V (Abs r s V y, z) << y[*:= z] 
(*;
     these are already verified since App and Abs
     are module morphisms in (RMOD P PO)
  propag_App1: forall r s V y y' z,
        y << y' -> App r s V (y,z) << App _ _ _ (y',z) ;

  propag_App2: forall r s V y z z',
        z << z' -> App r s V (y,z) << App _ _ _ (y,z') ;

  propag_Abs: forall r s V y y',
        y << y' -> Abs r s V y << Abs _ _ _ y' 
*)
}.


Record TLCPO_rep := {
  tlcpo_rep_monad :> RMonad (IDelta TY) ;
  tlcpo_rep_struct :> TLCPO_rep_struct tlcpo_rep_monad
}.

Existing Instance tlcpo_rep_struct.

(** morphisms of representations *)

Section TLCPO_rep_Hom.

Variables P R : TLCPO_rep.

Section Rep_Hom_Class.

Variable S : RMonad_Hom P R.

Notation "'SS'":= (PbRMod_ind_Hom S).


Class TLCPO_rep_Hom_struct := {

  App_Hom: forall r s,  
        App r s ;; FM SS ;; FPB == 
          (FM SS ;; FPB) X (FM SS ;; FPB);; 
                   PRPB ;; PBM (App r s)
;
 
  Abs_Hom: forall r s, 
         Abs r s ;; FM SS ;; FPB ==
          FM (DM SS ;; DPB) ;; FPB ;; PBM (Abs r s) 

}.

End Rep_Hom_Class.

(** the type of morphismes of representations P -> R *)

Record TLCPO_rep_Hom := {
  rep_Hom_monad :> RMonad_Hom P R ;
  rep_Hom_monad_struct :> TLCPO_rep_Hom_struct rep_Hom_monad
}.

End TLCPO_rep_Hom.

End TLC_rep.
Existing Instance rep_Hom_monad_struct.
Existing Instance tlcpo_rep_struct.

