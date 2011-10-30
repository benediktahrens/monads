(*Require Import Coq.Relations.Relations.*)
Require Import Coq.Program.Equality.

Require Export CatSem.COMP.PCF_rep_quant.
Require Export CatSem.ULC.ULC_Monad.
Require Export CatSem.ULC.ULC_terms.
Require Export CatSem.CAT.unit_type_monad.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Automatic Introduction.

Unset Printing Implicit Defensive.
(* this will suppress printing
  of implicit arguments of Var *)

Definition PCF_ULC_type_mor : TY -> unit := fun _ => tt.

Definition uULC := unit_Monad ULCM.

Program Instance ULCApp_s u v : 
Module_Hom_struct 
  (S:=Prod_Mod TYPE_prod (ITFibre_Mod uULC tt) (ITFibre_Mod uULC u))
  (T:=ITFibre_Mod uULC v)  (fun V y => App (fst y) (snd y)).

Definition ULCApp  r s := Build_Module_Hom (ULCApp_s r s).

(*
Definition bla r s :
(forall x : ITYPE unit,
  (ITFibre_Mod (IT_Der_Mod uULC (PCF_ULC_type_mor r)) 
 (PCF_ULC_type_mor s)) x --->
  (ITFibre_Mod uULC (PCF_ULC_type_mor (PCF.arrow r s))) x).
simpl.
intros.
apply Abs.
apply (lift (M:=ULCM) (@unit_passing _ _ _ ) X).
Defined.
*)

Lemma unit_passing_shift u t (V W : ITYPE unit) 
 (f : V ---> uULC W)
  (y : opt u V t):
shift f y //- (@unit_passing _ _ _ )= unit_passing y >- f tt.
Proof.
  destruct y;
  unfold unit_weta_car;
  repeat elim_unit;
  simpl; auto.
  unfold inj;
  simpl.
  rewrite <- lift_rename.
  unfold lift. simpl.
  unfold unit_kleisli.
  simpl.
  rewrite subst_subst.
  simpl.
  rewrite lift_rename.
  auto.
Qed.


Program Instance ULCAbs_s u v : 
Module_Hom_struct
  (S:=ITFibre_Mod (IT_Der_Mod uULC u) v) 
  (T:=ITFibre_Mod uULC tt)
  (fun V y => Abs (lift (M:=ULCM) (@unit_passing _ _ _ ) y)).
Next Obligation.
Proof.
  unfold unit_kleisli.
  simpl.
  apply f_equal.
  simpl.
  unfold lift.
  simpl.
  repeat rewrite subst_subst.
  apply subst_eq.
  simpl in *; intros.
  rewrite lift_rename.
  rew unit_passing_shift.
Qed.

Definition ULCAbs r s := Build_Module_Hom (ULCAbs_s r s).


Program Instance ULCRec_s t :
  Module_Hom_struct 
  (S:=ITFibre_Mod uULC tt) 
  (T:=ITFibre_Mod uULC t)
      (fun V y => App (ULC_theta _ ) y).


Definition ULCRec t := Build_Module_Hom (ULCRec_s t).


Program Instance ULCttt_s :
Module_Hom_struct 
  (S:=MOD_Term uULC TYPE_term)
  (T:=ITFibre_Mod uULC (PCF_ULC_type_mor PCF.Bool))

  (fun V _ => ULC_True (sunit V)).

Definition ULCttt :=
 Build_Module_Hom ULCttt_s.

Program Instance ULCfff_s :
Module_Hom_struct 
  (S:=MOD_Term uULC TYPE_term)
  (T:=ITFibre_Mod uULC (PCF_ULC_type_mor PCF.Bool))
  (fun V _ => ULC_False (sunit V)).

Definition ULCfff :
Term ---> (ITFIB_MOD uULC (PCF_ULC_type_mor Bool)) uULC :=
 Build_Module_Hom ULCfff_s.

Program Instance ULCNat_s m :
Module_Hom_struct (S:=MOD_Term uULC TYPE_term)
  (T:=ITFibre_Mod uULC (PCF_ULC_type_mor Nat))
  (fun V _ => ULC_Nat m (sunit V)).
Next Obligation.
Proof.
  unfold unit_kleisli;
  simpl.
  rewrite <- ulc_nats_subst.
  auto.
Qed.


Definition ULCNat m :
 Term ---> (ITFIB_MOD uULC (PCF_ULC_type_mor Nat)) uULC :=
  Build_Module_Hom (ULCNat_s m).
 
Program Instance ULCSucc_s :
Module_Hom_struct (S:=MOD_Term uULC TYPE_term)
  (T:=ITFibre_Mod uULC (PCF_ULC_type_mor (PCF.Arrow Nat Nat)))
  (fun V _ => ULCsucc (sunit V)).

Definition ULCSucc :
Term ---> (ITFIB_MOD uULC (PCF_ULC_type_mor (PCF.Arrow Nat Nat))) uULC :=
 Build_Module_Hom ULCSucc_s.

Program Instance ULCCondN_s :
Module_Hom_struct (S:=MOD_Term uULC TYPE_term)
  (T:=ITFibre_Mod uULC (PCF_ULC_type_mor (PCF.Arrow Nat Bool)))
  (fun V _ => ULC_cond (sunit V)).


Definition ULCCondN :
Term ---> (ITFIB_MOD uULC (PCF_ULC_type_mor (PCF.Arrow Nat Bool))) uULC :=
Build_Module_Hom ULCCondN_s.

Obligation Tactic := simpl; intros; repeat elim_unit; auto.

Program Instance ULCBottom_s t :
 Module_Hom_struct 
   (S:=MOD_Term uULC TYPE_term) 
   (T:=(ITFibre_Mod uULC t))
  (fun V _ => match t with tt => ULC_omega (sunit V) end).

Definition ULCBottom t := Build_Module_Hom (ULCBottom_s t).  

Program Instance ULCZero_s : 
Module_Hom_struct 
  (S:=MOD_Term uULC TYPE_term) 
  (T:=ITFibre_Mod uULC tt)
  (fun V _ => ULC_zero (sunit V)).

Definition ULCZero := Build_Module_Hom ULCZero_s.

Program Instance ULCPred_s : 
Module_Hom_struct 
  (S:=MOD_Term uULC TYPE_term) 
  (T:=ITFibre_Mod uULC tt)
  (fun V _ => ULC_pred_alt (sunit V)).

Definition ULCPred := Build_Module_Hom ULCPred_s.

   
(*

Program Instance ULCzero_pos :
forall V : unit -> Type,
PO_mor_struct (a:=PO_TERM) 
  (b:=ipo_proj (ULCBETAM V) (PCF_ULC_type_mor 
                         (Nat ~> Bool)))
  (fun _ => ULC_zero (sunit V)).

Definition ULCzero_car V :
Term (C:=RMOD ULCBETAM _ ) V ---> 
 (ULCBETAM [PCF_ULC_type_mor (Nat ~> Nat)]) V :=
  Build_PO_mor (ULCzero_pos V).

Program Instance ulc_zero_s : RModule_Hom_struct 
  (M:= Term (C := RMOD ULCBETAM PO))
  (N:= ULCBETAM [PCF_ULC_type_mor (Nat ~> Bool)])
  ULCzero_car.

Definition ulc_zero := Build_RModule_Hom ulc_zero_s.

Program Instance ULCpred_pos :
forall V : unit -> Type,
PO_mor_struct (a:=PO_TERM) 
  (b:=ipo_proj (ULCBETAM V) (PCF_ULC_type_mor 
                         (Nat ~> Nat)))
  (fun _ => ULC_pred_alt (sunit V)).

Definition ULCpred_car V :
Term (C:=RMOD ULCBETAM _ ) V ---> 
 (ULCBETAM [PCF_ULC_type_mor (Nat ~> Nat)]) V :=
  Build_PO_mor (ULCpred_pos V).

Program Instance ulc_pred_s : RModule_Hom_struct 
  (M:= Term (C := RMOD ULCBETAM PO))
  (N:= ULCBETAM [PCF_ULC_type_mor (Nat ~> Nat)])
  ULCpred_car.

Definition ulc_pred := Build_RModule_Hom ulc_pred_s.

Ltac sim := unfold substar; simpl ;
            unfold inj; simpl.
*)

Obligation Tactic := idtac.

Program Instance PCF_ULC_rep_s : 
 PCF_rep_struct (U:=unit) uULC (PCF_ULC_type_mor) (fun _ _ => tt) := {
  app r s := ULCApp r s
;
  abs r s := ULCAbs r s 
;
  rec t := ULCRec t 
;
  tttt := ULCttt;
  ffff := ULCfff;
  nats m := ULCNat m ;
  Succ := ULCSucc ;
  CondN := ULCCondN ;
  CondB := ULCCondN ;
  bottom t := ULCBottom t ;
  Zero := ULCZero ;
  Pred := ULCPred
}.

Definition PCF_ULC : PCF_rep := Build_PCF_rep 
      (type_type:=unit) (type_arrow := fun _ _ => tt)
      (pcf_rep_monad:=uULC)
      (type_mor:=fun t => tt)
      (fun _ _ => eq_refl)
      PCF_ULC_rep_s.



