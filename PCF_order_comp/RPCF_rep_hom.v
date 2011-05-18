
Require Export CatSem.PCF_order_comp.RPCF_rep.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

(** morphisms of representations *)

Section rep_hom.

Variables P R : PCFPO_rep.

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

Variable M : gen_RMonad_Hom P R 
    (G1:=RETYPE (fun t => f t))
    (G2:=RETYPE_PO (fun t => f t)) (NNNT1 (fun t => f t)).

(*
Definition MM := gen_PbRMod_ind_Hom M.
Check FFib_Mod_Hom. Check FIB_RMOD_HOM.
Print FIB_RMOD_eq.
*)
(*Check (fun r s => FIB_RMOD_eq (gen_PbRMod M R) (H (r ~> s))).
Check (fun r s => app (P:=P) r s ;; 
                  FIB_RMOD_HOM M _  ).
Check (fun r s => app (P:=P) r s ;; 
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
           gen_PbRMod_Hom _ (app r s)).
              

Check FFib_DER_Mod_Hom_eqrect.
Check der_fib_hom.
*)
(*
Print gen_pb_fib.
Check (fun s => gen_pb_fib M s R).
Check (der_fib_hom).


Check (fun r s =>   der_fib_hom M _ (H _ ) ;;
                    FIB_RMOD_eq _ (H _ ) ;;
                    gen_pb_fib M (type_mor R s) (d R // type_mor R r) ;; 
                    gen_PbRMod_Hom M (abs r s)).
*)
(*
Check (fun r  s => der_fib_hom _ _ (H r ) ;;
                  FIB_RMOD_eq M (H s) ). ;;
                  gen_PbRMod_Hom M (abs r s)).
  *)   
(*             
Check (fun r s => abs r s ;; 
                  FIB_RMOD_HOM M _ ;;
                  FIB_RMOD_eq _ (H _ );;
                  gen_pb_fib _ _ _ ).

Check (fun t => unit_rmod M  ;; gen_PbRMod_Hom _ (bottom t )).
Check (fun t => bottom t ;; 
                FIB_RMOD_HOM M _ ;;
                FIB_RMOD_eq _ (H _ );;
                gen_pb_fib _ _ _ ).

Check (tttt (PCFPO_rep_struct := P) ;; FIB_RMOD_HOM M _ ).

Check Term.

Print gen_pb_fib.

*)
Class PCFPO_rep_Hom_struct := {

  CondB_hom : CondB (PCFPO_rep_struct := P) ;;
                FIB_RMOD_HOM M _ ;;
                FIB_RMOD_eq _ (H _ );;
                gen_pb_fib _ _ _ 
           ==
           unit_rmod M  ;; 
           gen_PbRMod_Hom M (CondB (PCFPO_rep_struct := R))
;
  CondN_hom : CondN (PCFPO_rep_struct := P) ;;
                FIB_RMOD_HOM M _ ;;
                FIB_RMOD_eq _ (H _ );;
                gen_pb_fib _ _ _ 
           ==
           unit_rmod M  ;; 
           gen_PbRMod_Hom M (CondN (PCFPO_rep_struct := R))
;
  Pred_hom : Pred (PCFPO_rep_struct := P) ;;
                FIB_RMOD_HOM M _ ;;
                FIB_RMOD_eq _ (H _ );;
                gen_pb_fib _ _ _ 
           ==
           unit_rmod M  ;; 
           gen_PbRMod_Hom M (Pred (PCFPO_rep_struct := R)) 
;
  Zero_hom : Zero (PCFPO_rep_struct := P) ;;
                FIB_RMOD_HOM M _ ;;
                FIB_RMOD_eq _ (H _ );;
                gen_pb_fib M _ _ 
           ==
           unit_rmod M  ;; 
           gen_PbRMod_Hom M (Zero (PCFPO_rep_struct := R))
;
  Succ_hom : Succ (PCFPO_rep_struct := P) ;;
                FIB_RMOD_HOM M _ ;;
                FIB_RMOD_eq _ (H _ );;
                gen_pb_fib M _ _ 
           ==
           unit_rmod M  ;; 
           gen_PbRMod_Hom M (Succ (PCFPO_rep_struct := R))
;
  fff_hom : ffff (PCFPO_rep_struct := P) ;;
                FIB_RMOD_HOM M _ ;;
                FIB_RMOD_eq _ (H _ );;
                gen_pb_fib M _ _ 
           ==
           unit_rmod M  ;; 
           gen_PbRMod_Hom M (ffff (PCFPO_rep_struct := R))

;
  ttt_hom : tttt (PCFPO_rep_struct := P) ;;
                FIB_RMOD_HOM M _ ;;
                FIB_RMOD_eq _ (H _ );;
                gen_pb_fib M _ _ 
           ==
           unit_rmod M  ;; 
           gen_PbRMod_Hom M (tttt (PCFPO_rep_struct := R))
; 
  bottom_hom : forall t,
           bottom t ;; 
                FIB_RMOD_HOM M _ ;;
                FIB_RMOD_eq _ (H _ );;
                gen_pb_fib M _ _ 
           ==
           unit_rmod M  ;; 
           gen_PbRMod_Hom _ (bottom t)
;
  nats_hom : forall m,
           nats m ;;
                FIB_RMOD_HOM M _ ;;
                FIB_RMOD_eq _ (H _ );;
                gen_pb_fib M _ _ 
           ==
           unit_rmod M  ;; 
           gen_PbRMod_Hom _ (nats m)
;
  app_hom : forall r s, 
          app (P:=P) r s ;; 
                  FIB_RMOD_HOM M _  ;;
                  FIB_RMOD_eq (gen_PbRMod M R) (H _) ;;
                  gen_pb_fib M _ _  
              ==
          product_mor _ 
             (FIB_RMOD_HOM M (type_mor _ (r~>s)) ;;
              FIB_RMOD_eq _ (H _ );;
              gen_pb_fib M _ _ )
             (FIB_RMOD_HOM M (type_mor _ r) ;;
              FIB_RMOD_eq _ (H _ );;
              gen_pb_fib M _ _ )
            ;;
           gen_PROD_PM _ _ _ _ 
            ;;
           gen_PbRMod_Hom _ (app r s)
;
  abs_hom : forall r s,
       abs r s ;; 
           FIB_RMOD_HOM M _ ;;
           FIB_RMOD_eq _ (H _ );;
           gen_pb_fib M _ _ 
      ==
       der_fib_hom M _ (H _ ) ;;
        FIB_RMOD_eq (Q:=P) _
             (*gen_PbRMod M (d R // type_mor R r)*) (H _);;
           gen_pb_fib M (*type_mor R s*) (*d R // type_mor R r*) _ _  ;; 
           gen_PbRMod_Hom M (abs (PCFPO_rep_struct := R) r s)
;
  rec_hom : forall t,
      rec t ;; 
        FIB_RMOD_HOM M _ ;;
        FIB_RMOD_eq _ (H _ );;
        gen_pb_fib M _ _ 
      ==
      FIB_RMOD_HOM M _ ;;
      FIB_RMOD_eq _ (H _ ) ;;
      gen_pb_fib M _ _ ;;
      gen_PbRMod_Hom M (rec t)
   
}.

End Rep_Hom_Class.


(** the type of morphismes of representations P -> R *)

Record PCFPO_rep_Hom := {
  tcomp : type_type P -> type_type R ;
  ttriag : forall t, tcomp (type_mor P t) = type_mor R t;
  rep_Hom_monad :> gen_RMonad_Hom P R (NNNT1 (fun t => tcomp t));
  rep_gen_Hom_monad_struct :> PCFPO_rep_Hom_struct ttriag rep_Hom_monad
}.

End rep_hom.

Existing Instance rep_gen_Hom_monad_struct.

