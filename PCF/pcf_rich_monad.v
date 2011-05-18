Require Export rich_monads pcfpo_mod.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Automatic Introduction.

Section pcf_is_rich.

Program Instance PCF_enriched : Enriched_Monad (T:=PCF.TY) (P:=PCF_monad)
         (fun V =>  @PCF.betaS V).
Next Obligation.
Proof.
  assert (H:= PCF.BETA_struct X).
  assert (H':=Clos_RT_1n_prf).
  destruct H.
  simpl.
  constructor; unfold itrel.
  unfold PCF.betaS.
  apply H'.
  apply H'.
Qed.
Next Obligation.
Proof.
  assert (H':=PCF.subst_h (f:=f)).
  unfold ITproper in *.
  unfold itrel.
  apply H'.
  constructor.
  auto.
Qed.
Next Obligation.
Proof.
  unfold ITproper.
  unfold Proper; repeat red.
  intros t x y H.
  constructor 2 with (PCF.Var y); 
  try constructor.
  constructor. auto.
Qed.
End pcf_is_rich.
        





















