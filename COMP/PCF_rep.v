Require Import Coq.Logic.FunctionalExtensionality.
(*Require Import Coq.Program.Equality.*)

Require Export CatSem.CAT.cat_INDEXED_TYPE.
Require Export CatSem.CAT.retype_functor.
Require Export CatSem.CAT.monad_h_morphism_gen.
Require Export CatSem.CAT.monad_h_module.
Require Export CatSem.PCF.PCF_types.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Notation "'TY'" := PCF.types.
Notation "'Bool'":= PCF.Bool.
Notation "'Nat'":= PCF.Nat.

Section rep.

Notation "'IT'" := (ITYPE TY).
Notation "a '~>' b" := (PCF.arrow a b) 
     (at level 69, right associativity).
Notation "a 'x' b" := (product (*C:= MOD _ _*) a b) (at level 30).
Notation "P [ z ]" := (ITFIB_MOD _ z P) (at level 35).
Notation "'d' P // s" := (ITDER_MOD _ _ s P) (at level 25).
Notation "'*'" := (Term (C:=MOD _ TYPE)).
Notation "f 'X' g" := (product_mor _ f g)(at level 30).




Class PCF_rep_s U (f : TY -> U) (P : Monad (ITYPE U)) := {
  app : forall r s, (P[f (r~>s)]) x (P[f r]) ---> P[f s];
  abs : forall r s, (d P // (f r))[f s] ---> P[f (r~> s)];
  rec : forall t, P[f (t ~> t)] ---> P[f t];
  tttt :  * ---> P[f Bool];
  ffff :  * ---> P[f Bool];
  nats : forall m:nat, * ---> P[f Nat];
  Succ : * ---> P[f (Nat ~> Nat)];
  Zero : * ---> P[f (Nat ~> Bool)];
  CondN: * ---> P[f (Bool ~> Nat ~> Nat ~> Nat)];
  CondB: * ---> P[f (Bool ~> Bool ~> Bool ~> Bool)];
  bottom: forall t, * ---> P[f t];
  Pred : * ---> P[f (Nat ~> Nat)]
}.

Record PCF_rep := {
  type_type : Type;
  type_mor : TY -> type_type;
  pcf_rep_monad :> Monad (ITYPE type_type);
  pcf_rep_struct :> PCF_rep_s type_mor pcf_rep_monad
}.

Existing Instance pcf_rep_struct.

Section PCF_rep_Hom.

Variables P R : PCF_rep.

Section Rep_Hom_Class.

Variable f : type_type P -> type_type R.
Variable H : forall t, f (type_mor P t) = type_mor R t.
Variable M : gen_Monad_Hom P R (RETYPE (fun t => f t)).

Definition MM := PMod_ind_Hom M.



Program Instance unit_mod_s : Module_Hom_struct
      (S:= Term (C:=MOD P TYPE)) (T:=PModule M (Term (C:=MOD R TYPE)))
      (fun V y => y).

Canonical Structure unit_mod : * ---> PModule M * := 
             Build_Module_Hom unit_mod_s.



Class PCF_rep_Hom_struct := {
    
  Succ_Hom : Succ (P:=P) ;;  
        FFib_Mod_Hom M (type_mor P (Nat ~> Nat)) ;; 
        eq_type_fibre_mod (PModule M (E:=ITYPE (type_type R)) R) 
             (H _)
          == 
        unit_mod ;; 
        PMod_Hom M (Succ (P:=R)) ;;
        FIB_PM M R (type_mor R (Nat ~> Nat)) ;

  Zero_Hom : Zero (P:=P) ;; 
        FFib_Mod_Hom M (type_mor P (Nat ~> Bool)) ;; 
        eq_type_fibre_mod (PModule M (E:=ITYPE (type_type R)) R) 
             (H _)
          == 
        unit_mod ;; 
        PMod_Hom M (Zero (P:=R)) ;;
        FIB_PM M R (type_mor R (Nat ~> Bool))  ;

  CondB_Hom : CondB (P:=P) ;; 
        FFib_Mod_Hom M _ ;; 
        eq_type_fibre_mod (PModule M (E:=ITYPE (type_type R)) R) 
             (H _)
          == 
        unit_mod ;; 
        PMod_Hom M (CondB (P:=R)) ;;
        FIB_PM _ _ _  ;

  CondN_Hom : CondN (P:=P) ;; 
        FFib_Mod_Hom M _ ;; 
        eq_type_fibre_mod (PModule M (E:=ITYPE (type_type R)) R) 
             (H _)
          == 
        unit_mod ;; 
        PMod_Hom M (CondN (P:=R)) ;;
        FIB_PM _ _ _  ;

 
  ttt_Hom : tttt (P:=P) ;; 
        FFib_Mod_Hom M _ ;; 
        eq_type_fibre_mod (PModule M (E:=ITYPE (type_type R)) R) 
             (H _)
          == 
        unit_mod ;; 
        PMod_Hom M (tttt (P:=R)) ;;
        FIB_PM _ _ _  ;
        
  fff_Hom : ffff (P:=P) ;; 
        FFib_Mod_Hom M _ ;; 
        eq_type_fibre_mod (PModule M (E:=ITYPE (type_type R)) R) 
             (H _)
          == 
        unit_mod ;; 
        PMod_Hom M (ffff (P:=R)) ;;
        FIB_PM _ _ _ ;

  nats_Hom : forall m, 
        nats m (P:=P) ;; 
        FFib_Mod_Hom M _ ;; 
        eq_type_fibre_mod (PModule M (E:=ITYPE (type_type R)) R) 
             (H _)
          == 
        unit_mod ;; 
        PMod_Hom M (nats m (P:=R)) ;;
        FIB_PM _ _ _  ;
 
  Bottom_Hom : forall t, 
        bottom t (P:=P) ;; 
        FFib_Mod_Hom M _ ;; 
        eq_type_fibre_mod (PModule M (E:=ITYPE (type_type R)) R) 
             (H _)
          == 
        unit_mod ;; 
        PMod_Hom M (bottom t (P:=R)) ;;
        FIB_PM _ _ _  ;
  
  Rec_Hom : forall t,
        rec (P:=P) t ;;
        FFib_Mod_Hom M _ ;;
        eq_type_fibre_mod (PModule M (E:=ITYPE (type_type R)) R) 
             (H _)
          == 
        FFib_Mod_Hom M (type_mor _ (t ~> t)) ;;
        eq_type_fibre_mod _ (H _ ) ;;
        PM_FIB _ _ _ ;;
        PMod_Hom M (rec (P:=R) t) ;; 
        FIB_PM M R _ ;

  App_Hom : forall r s,  
         app (P:=P) r s ;; 
         FFib_Mod_Hom M _ ;; 
         eq_type_fibre_mod (PModule M (E:=ITYPE (type_type R)) R) 
             (H _)
                                          ==
         product_mor (MOD_PROD _ TYPE_prod)
            (FFib_Mod_Hom M (type_mor _ (r ~> s)) ;; 
             eq_type_fibre_mod _ (H _) ;;
             PM_FIB M R _  ) 
        
            (FFib_Mod_Hom M (type_mor _ r) ;; 
             eq_type_fibre_mod _ (H _) ;;
             PM_FIB M R _ ) ;;
         PROD_PM _ _ _ _ ;; 
         PMod_Hom M (app r s);; FIB_PM M R (type_mor R s) ;


  Abs_Hom : forall r s,  
          FFib_DER_Mod_Hom_eqrect M (type_mor _ s) 
          (H r ) ;; eq_type_fibre_mod _ (H _ ) ;;
          PM_FIB _ _ _ ;;
          PMod_Hom M (abs r s);;
          FIB_PM _ _ _ 
                                      ==
          abs (P:=P) r s ;; 
          FFib_Mod_Hom M _ ;;
          eq_type_fibre_mod _ (H _ );
 
  Pred_Hom : Pred (P:=P) ;;  
        FFib_Mod_Hom M (type_mor P (Nat ~> Nat)) ;; 
        eq_type_fibre_mod (PModule M (E:=ITYPE (type_type R)) R) 
             (H _)
          == 
        unit_mod ;; 
        PMod_Hom M (Pred (P:=R)) ;;
        FIB_PM M R (type_mor R (Nat ~> Nat)) 
}. 


End Rep_Hom_Class.

(** the type of morphismes of representations P -> R *)

Record PCF_rep_Hom := {
  tcomp : type_type P -> type_type R ;
  ttriag : forall t, tcomp (type_mor P t) = type_mor R t;
  rep_Hom_monad :> gen_Monad_Hom P R (RETYPE (fun t => tcomp t));
  rep_gen_Hom_monad_struct :> PCF_rep_Hom_struct ttriag rep_Hom_monad
}.

End PCF_rep_Hom.
End rep.

Existing Instance rep_gen_Hom_monad_struct.






















