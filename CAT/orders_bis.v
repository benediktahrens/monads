
Require Export CatSem.CAT.orders.


Set Implicit Arguments.
Unset Strict Implicit.

Unset Automatic Introduction.


Inductive smallest_rel (V : TYPE) : relation V :=
  | t_eq : forall (x : V), smallest_rel x x.

Program Instance sm_po_struct (V : TYPE) : PO_obj_struct V := {
  Rel := smallest_rel (V:=V)
}.
Next Obligation.
Proof.
  constructor.
  unfold Reflexive.
  constructor.
  unfold Transitive.
  intros x y z H H'.
  induction H.
  auto.
Qed.

Canonical Structure sm_po (V : TYPE) : Ord := 
      Build_PO_obj (sm_po_struct V).

Section sm_po_mor.

Variables V W : TYPE.
Variable f : V ---> W.

Program Instance sm_po_mor_s : 
  PO_mor_struct (a:=sm_po V) (b:=sm_po W) f.
Next Obligation.
Proof.
  unfold Proper.
  red.
  intros x y H.
  induction H.
  constructor.
Qed.

Canonical Structure sm_po_mor : sm_po V ---> sm_po W := 
        Build_PO_mor sm_po_mor_s.

End sm_po_mor.

Program Instance SM_po_s : Functor_struct sm_po_mor.
Next Obligation.
Proof.
  unfold Proper.
  red.
  intros.
  simpl.
  auto.
Qed.

Definition SM_po := Build_Functor SM_po_s.
Definition Delta := SM_po.

Section Sm_ind.

Variable V : TYPE.
Variable W : Ord.

Variable f : V -> W.

Program Instance Sm_ind_s : PO_mor_struct 
  (a:=SM_po V) (b:=W) f.
Next Obligation.
Proof.
  unfold Proper;
  red.
  intros x y H.
  induction H.
  reflexivity.
Qed.

Canonical Structure Sm_ind := Build_PO_mor Sm_ind_s.

End Sm_ind.
