Require Import Coq.Relations.Relations.

Require Export CatSem.ORDER.tlc_order_rep_eq.
Require Export CatSem.TLC.TLC_RMonad.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Obligation Tactic := simpl; intros.

Program Instance TLC_rep : TLCPO_rep_struct TLCB := {
  App := tlc_app ;
  Abs := tlc_abs
}.
Next Obligation.
Proof.
  simpl; intros.
  apply clos_refl_trans_1n_contains.
  apply relorig.
  constructor.
Qed.

Canonical Structure TLC_Rep : TLCPO_REP := Build_TLCPO_rep TLC_rep.










