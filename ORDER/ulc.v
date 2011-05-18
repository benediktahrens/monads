Require Import Coq.Relations.Relations.

Require Export CatSem.ORDER.ulc_order_rep_eq.
Require Export CatSem.ULC.ULC_RMonad.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Obligation Tactic := simpl; intros.

Program Instance ULC_rep : ULCPO_rep_struct ULCBETA := {
  app := ulc_app ;
  abs := ulc_abs
}.
Next Obligation.
Proof.
  simpl; intros.
  apply clos_refl_trans_1n_contains.
  apply relorig.
  constructor.
Qed.

Canonical Structure ULC_Rep : ULCPO_REP := Build_ULCPO_rep ULC_rep.










