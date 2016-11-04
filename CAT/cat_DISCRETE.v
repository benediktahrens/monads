Require Export CatSem.CAT.category.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Section DISCRETE_CAT.

Variable T : Type.

(* Definition Discrete_hom (a b:T) := a = b.
*)
Lemma Discrete_hom_equiv (a b : T) : @Equivalence (a = b) 
       (fun p q => True).
Proof.
  intros a b; 
  constructor; simpl; auto.
Qed.

Instance Discrete_hom_oid a b : Setoid (a = b) := 
     Build_Setoid (Discrete_hom_equiv a b).
(*
Obligation Tactic := intuition; auto.
*)
Program Instance DISCRETE_struct : Cat_struct (obj:=T) (fun a b => a = b).
(*
Next Obligation. 
  apply (Discrete_hom_oid).
Defined.
*)
Next Obligation.
Proof.
  unfold Proper; repeat red. 
  auto.
Qed.

Definition DISCRETE := Build_Cat DISCRETE_struct.

End DISCRETE_CAT.








