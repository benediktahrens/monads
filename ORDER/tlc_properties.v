Require Export CatSem.ORDER.tlc.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.


Lemma subst_monotone_on_functions (V : IT) 
    (t : TY)(y : TLCB V t) W (f g : V ---> TLCB W)
    (H : forall t v, f t v <<< g t v) :
     beta (y >>= f) (y >>= g).
Proof.
  intros V t y.
  induction y;
  simpl;
  intros.
  apply H.
  apply cp_Lam.
  apply IHy.
  induction v;
  simpl.
  unfold _inj.
  apply beta_rename.
  auto.
  reflexivity.
  transitivity (
    app (y1 >>= f) (y2 >>= g)).
  apply cp_App2.
  apply IHy2.
  auto.
  apply cp_App1.
  apply IHy1.
  auto.
Qed.








