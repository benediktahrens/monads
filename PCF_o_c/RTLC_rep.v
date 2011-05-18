Require Export CatSem.CAT.retype_functor_po.
Require Export CatSem.CAT.rmonad_gen_type_po.
Require Export CatSem.CAT.TLC_types.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Definition TY := TLC.types.

Notation "'IP'" := (IPO TY).
Notation "a '~>' b" := (TLC.arrow a b) 
   (at level 69, right associativity).
Notation "a 'x' b" := (product a b) (at level 30).
Notation "M [ z ]" := (FIB_RMOD _ z M) (at level 35).
Notation "'d' M // s" := (DER_RMOD _ _ s M) (at level 25).
Notation "'*'" := (Term (C:=RMOD _ PO)).

Notation "f 'X' g" := (product_mor _ f g)(at level 30).

Notation "'FM'" := (#(FIB_RMOD _ _ )).
Notation "'FPB'":= (FIB_RPB _ _ _ ).
Notation "'PRPB'":= (PROD_RPB _ _ _ _ ).
(*Notation "'PBF'":= (PB_FIB _ _ _ ).*)
Notation "'PBM'":= (#(PbRMOD _ _ )).
Notation "'DM'":= (#(DER_RMOD _ _ _ )).
Notation "'DPB'":= (DER_RPB _ _ _ ).

Notation "y [* := z ]":= (Rsubstar z _ y)(at level 55).



Section TLC_rep.

Variable U : Type.
Variable P : RMonad (SM_ipo U).
Variable f : TY -> U.

(** a monad is a representation if it is accompagnied by 
    - a lot of morphisms of modules 
    - beta-reduction
*)

Class TLCPO_rep_struct := {
  App : forall r s, (P[f (r~>s)]) x (P[f r]) ---> P[f s];
  Abs : forall r s, (d P //(f r))[f s] ---> P[f (r ~> s)];

  beta_red : forall r s V y z, 
        App r s V (Abs r s V y, z) << y[*:= z] ;
  
  propag_App1: forall r s V y y' z,
        y << y' -> App r s V (y,z) << App _ _ _ (y',z) ;

  propag_App2: forall r s V y z z',
        z << z' -> App r s V (y,z) << App _ _ _ (y,z') ;

  propag_Abs: forall r s V y y',
        y << y' -> Abs r s V y << Abs _ _ _ y' 
 }.

End TLC_rep.

Record TLCPO_rep := {
  type_type : Type;
  tlc_rep_monad :> RMonad (SM_ipo type_type);
  type_mor : TY -> type_type;
  tlc_rep_struct :> TLCPO_rep_struct tlc_rep_monad type_mor
}.


Existing Instance tlc_rep_struct.

(** morphisms of representations *)

Section rep_hom.

Variables P R : TLCPO_rep.



Section Rep_Hom_Class.

(** a morphism of representations 
        - (U, f, P, Rep)
        - (U', f', Q, Rep')
   is given by 
        - g : U -> U'
        - H : f ; g = f'
        - generalized monad morphism P -> Q (with F = RETYPE g)
        - properties
*)

Variable f : type_type P -> type_type R.
Variable H : forall t, f (type_mor P t) = type_mor R t.
Check gen_RMonad_Hom.
Variable M : gen_RMonad_Hom P R 
    (G1:=RETYPE f)
    (G2:=RETYPE_PO f) (NNNT1 f).

Definition MM := gen_PbRMod_ind_Hom M.
Check FFib_Mod_Hom. Check FIB_RMOD_HOM.
Print FIB_RMOD_eq.
Check (fun r s => FIB_RMOD_eq (gen_PbRMod M R) (H (r ~> s))).
Check (fun r s => App (P:=P) r s ;; 
                  FIB_RMOD_HOM M _  ).
Check (fun r s => App (P:=P) r s ;; 
                  FIB_RMOD_HOM M _  ;;
                  FIB_RMOD_eq (gen_PbRMod M R) (H _) ;;
                  gen_pb_fib _ _ _ ).

Check (fun r s => 
           product_mor _ 
             (FIB_RMOD_HOM M (type_mor _ (r~>s)) ;;
              FIB_RMOD_eq _ (H _ );;
              gen_pb_fib _ _ _ )
             (FIB_RMOD_HOM M (type_mor _ r) ;;
              FIB_RMOD_eq _ (H _ );;
              gen_pb_fib _ _ _ )
            ;;
           gen_PROD_PM _ _ _ _ 
            ;;
           gen_PbRMod_Hom _ (App r s)).
              

Check FFib_DER_Mod_Hom_eqrect.
Check der_fib_hom.

Check (fun r  s => der_fib_hom _ _ (H _ ) ;;
                  FIB_RMOD_eq _ (H s);;
                  gen_pb_fib _ _ _ ;;
                  gen_PbRMod_Hom M (Abs r s)).
                  
Check (fun r s => Abs r s ;; 
                  FIB_RMOD_HOM M _ ;;
                  FIB_RMOD_eq _ (H _ );;
                  gen_pb_fib _ _ _ ).

Class TLCPO_rep_Hom_struct := {
  App_Hom : forall r s, 
          App (P:=P) r s ;; 
                  FIB_RMOD_HOM M _  ;;
                  FIB_RMOD_eq (gen_PbRMod M R) (H _) ;;
                  gen_pb_fib _ _ _  
              ==
          product_mor _ 
             (FIB_RMOD_HOM M (type_mor _ (r~>s)) ;;
              FIB_RMOD_eq _ (H _ );;
              gen_pb_fib _ _ _ )
             (FIB_RMOD_HOM M (type_mor _ r) ;;
              FIB_RMOD_eq _ (H _ );;
              gen_pb_fib _ _ _ )
            ;;
           gen_PROD_PM _ _ _ _ 
            ;;
           gen_PbRMod_Hom _ (App r s)
;
  Abs_Hom : forall r s,
       der_fib_hom _ _ (H _ ) ;;
                  FIB_RMOD_eq _ (H s);;
                  gen_pb_fib _ _ _ ;;
                  gen_PbRMod_Hom M (Abs r s)
       ==
       Abs r s ;; 
                  FIB_RMOD_HOM M _ ;;
                  FIB_RMOD_eq _ (H _ );;
                  gen_pb_fib _ _ _ 
}.

End Rep_Hom_Class.


(** the type of morphismes of representations P -> R *)

Record TLCPO_rep_Hom := {
  tcomp : type_type P -> type_type R ;
  ttriag : forall t, tcomp (type_mor P t) = type_mor R t;
  rep_Hom_monad :> gen_RMonad_Hom P R (NNNT1 tcomp);
  rep_gen_Hom_monad_struct :> TLCPO_rep_Hom_struct ttriag rep_Hom_monad
}.

End rep_hom.

Existing Instance rep_gen_Hom_monad_struct.





