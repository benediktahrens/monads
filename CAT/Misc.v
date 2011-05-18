Require Export Coq.Setoids.Setoid.
Require Export Coq.Classes.SetoidClass.
Require Export Coq.Classes.Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Automatic Introduction.

Ltac app P := let H:= fresh "YMCA" in
     assert (H := P);
     simpl in H;
     apply H;
     clear H; simpl; auto.

Ltac rew P := let H:=fresh "YMCA" in
     assert (H := P);
     simpl in H;
     rewrite H;
     clear H;
     simpl;
     auto.

Ltac rerew P := let H:=fresh "YMCA" in
     assert (H := P);
     simpl in H;
     rewrite <- H;
     clear H;
     simpl;
     auto.

Ltac app_all := match goal with
        | [H:_|-_] => apply H end.

Ltac unf_Proper := match goal with
        | [ |- Proper _ _ ] => unfold Proper; repeat red end.

Ltac rew_hyp_2 := match goal with
        | [ H : forall _ _ , _ = _ |- _ ] => rewrite H end.

Ltac rew_hyp := match goal with
        | [ H : forall _ , _ = _ |- _ ] => rewrite H end.

Ltac rew_setoid := match goal with
	| [H : forall _ , _ == _ |- _ ] => rewrite H end.

Ltac rew_all := match goal with
        | [H : _ |- _ ] => rewrite H end.

Ltac rerew_all := match goal with
        | [H : _ |- _ ] => rewrite <- H end.

Ltac rew_set := match goal with
        | [H : _ == _ |- _ ] => rewrite H end.
 
Ltac elim_unit := match goal with
        | [ H : unit |- _ ] => destruct H end.

Ltac elim_conj := match goal with 
        | [ H : _ /\ _  |- _  ] => destruct H; intros end.

Ltac elim_conjs := repeat elim_conj.

Ltac mauto := simpl; intros; try unf_Proper; simpl; intros;
              elim_conjs; auto.


Section setoid_lemmata.

Variable A:Type.
Variable R: Setoid A.

Lemma setoid_refl : forall a, a == a.
Proof.
  destruct R.
  apply setoid_equiv.
Qed.

Lemma setoid_sym : forall a b, a == b -> b == a.
Proof.
  destruct R.
  apply setoid_equiv.
Qed.

Lemma setoid_trans : forall a b c,
           a == b -> b == c -> a == c.
Proof.
  destruct R.
  apply setoid_equiv.
Qed.

End setoid_lemmata.

Hint Resolve setoid_refl setoid_sym setoid_trans : setoid.
Hint Rewrite setoid_trans : setoid.

Ltac setoid := intros; mauto; eauto with setoid.

Lemma eq_trans_2 (A:Type)(a b c : A) : a = b -> b = c -> c = a.
Proof.
  congruence.
Qed.


Lemma eq_eq_rect A (z : A) (P : A -> Type) 
       (f g : P z) (y : A) (e : z = y):
   f = g -> eq_rect z P f y e = eq_rect z P g y e.
Proof.
  intros;
  subst;
  auto.
Qed.



