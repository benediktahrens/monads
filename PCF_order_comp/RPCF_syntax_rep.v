(*Require Export CatSem.PCF_order_comp.RPCF_syntax.*)
Require Export CatSem.PCF.PCF_RMonad.
Require Export CatSem.PCF_order_comp.RPCF_rep.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.


Program Instance PCFE_rep_struct : 
       PCFPO_rep_struct PCFEM (fun t => t) := {
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

Definition PCFE_rep : PCFPO_rep := Build_PCFPO_rep PCFE_rep_struct.











