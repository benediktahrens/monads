
Require Export CatSem.PCF.PCF_RMonad.
Require Export CatSem.PCF_o_c.RPCF_rep.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.


Program Instance PCFE_rep_struct : 
       PCFPO_rep_struct PCFEM (fun t => t) (PCF.arrow):= {
  app r s := PCFApp r s;
  abs r s := PCFAbs r s;
  rec t := PCFRec t ;
  tttt := PCFconsts ttt ;
  ffff := PCFconsts fff;
  Succ := PCFconsts succ;
  Pred := PCFconsts preds;
  CondN := PCFconsts condN;
  CondB := PCFconsts condB;
  Zero := PCFconsts zero ;
  nats m := PCFconsts (Nats m);
  bottom t := PCFbottom t
}.
Next Obligation.
Proof.
  unfold Rsubst_star_map.
  simpl.
  apply clos_refl_trans_1n_contains.
  apply relorig.
  apply app_abs.
Qed.
(*
Next Obligation.
Proof.
  apply cp_App1.
  auto.
Qed.
Next Obligation.
Proof.
  apply cp_App2.
  auto.
Qed.
Next Obligation.
Proof.
  apply cp_Lam.
  auto.
Qed.
Next Obligation.
Proof.
  apply cp_Rec.
  auto.
Qed.
*)
Next Obligation.
Proof.
  apply clos_refl_trans_1n_contains.
  apply relorig.
  constructor.
Qed.
Next Obligation.
Proof.
  apply clos_refl_trans_1n_contains.
  apply relorig.
  constructor.
Qed.
Next Obligation.
Proof.
  apply clos_refl_trans_1n_contains.
  apply relorig.
  constructor.
Qed.
Next Obligation.
Proof.
  apply clos_refl_trans_1n_contains.
  apply relorig.
  constructor.
Qed.
Next Obligation.
Proof.
  apply clos_refl_trans_1n_contains.
  apply relorig.
  constructor.
Qed.
Next Obligation.
Proof.
  apply clos_refl_trans_1n_contains.
  apply relorig.
  constructor.
Qed.
Next Obligation.
Proof.
  apply clos_refl_trans_1n_contains.
  apply relorig.
  constructor.
Qed.
Next Obligation.
Proof.
  apply clos_refl_trans_1n_contains.
  apply relorig.
  constructor.
Qed.
Next Obligation.
Proof.
  apply clos_refl_trans_1n_contains.
  apply relorig.
  constructor.
Qed.
Next Obligation.
Proof.
  apply clos_refl_trans_1n_contains.
  apply relorig.
  constructor.
Qed.


Definition PCFE_rep : PCFPO_rep := 
  Build_PCFPO_rep (type_type:=TY) (type_arrow:=PCF.arrow)
   (pcf_rep_monad:=PCFEM)(type_mor:=fun t => t)
   (fun s t => eq_refl)
   PCFE_rep_struct.











