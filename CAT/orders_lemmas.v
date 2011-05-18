Require Export CatSem.CAT.orders.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Instance Rel_Trans (A : PO_obj) : Transitive (Rel (T:=A)).
Proof.
  intros;
  apply POprf.
Qed.

Lemma Rel_refl (V : PO_obj) (x : V) : x << x.
Proof.
  reflexivity.
Qed.

Lemma Rel_eq (V : PO_obj) (x y : V) : x = y -> x << y.
Proof.
  intros;
  subst;
  reflexivity.
Qed.

Lemma Rel_eq_r (V : PO_obj) (x y z : V) : 
    x << y -> y = z -> x << z.
Proof.
  intros;
  subst;
  auto.
Qed. 

Lemma IRel_eq_l (V : PO_obj) (x y z : V) : 
    x << z -> x = y -> y << z.
Proof.
  intros; subst; auto.
Qed. 

Lemma Rel_trans (V : PO_obj) (x y z : V) : 
       x << y -> y << z -> x << z.
Proof.
  intros;
  etransitivity; 
  eauto.
Qed.
 
Lemma Rel_trans_2 (V : PO_obj) (x y z : V) : 
       x << z -> y << x -> y << z.
Proof.
  intros;
  etransitivity;
  eauto.
Qed.
