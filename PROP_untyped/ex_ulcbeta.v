Require Export CatSem.PROP_untyped.prop_arities_initial.

Require Import Coq.Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Automatic Introduction.
Unset Transparent Obligations.


Inductive Lambda_index := ABS | APP.

Definition Lambda : Signature := {|
  sig_index := Lambda_index ;
  sig := fun x => match x with 
                  | ABS => [[ 1 ]] 
                  | APP => [[ 0 ; 0]]
                  end
|}.

(*Definition Lambda_subst := subst_half_eq Lambda.
Check Lambda_subst.
*)

Section App_Abs_half_eq.


Section for_a_representation.

Variable R : REP Lambda.

Definition beta_carrier :
(forall c : TYPE, (S_Mod_classic_ob [[1; 0]] R) c ---> (S_Mod_classic_ob [[0]] R) c) .
simpl.
intros.
simpl in *.
inversion X.
simpl in *.
inversion X1.
simpl in X2.
constructor.
simpl.
destruct R as [Rr Repr].
simpl in *.
apply (Repr APP).
simpl.
simpl in *.
constructor.
simpl.
apply (Repr ABS).
simpl.
constructor.
simpl.
apply X0.
constructor.
constructor.
simpl.
apply X2.
constructor.
constructor.
Defined.

Program Instance beta_struct  : RModule_Hom_struct 
  (M:=S_Mod_classic_ob [[1;0]] R) (N:=S_Mod_classic_ob [[0]] R) beta_carrier.
Next Obligation.
Proof.
  dependent destruction x.
  simpl.
  dependent destruction x.
  simpl in *.
  apply CONSTR_eq; auto.
  destruct R.
  simpl in *.
  rerew (rmhom_rmkl (repr APP)).
  apply f_equal.
  simpl in *.
  apply CONSTR_eq; auto.
  clear x.
  clear p0.
  rerew (rmhom_rmkl (repr ABS)).
Qed.

Definition beta_module_mor := Build_RModule_Hom beta_struct.

End for_a_representation.

Program Instance beta_half_s : half_equation_struct 
      (U:=Build_S_Module (S_Mod_classic Lambda [[1 ; 0]])) 
      (V:=S_Mod_classic Lambda [[0]]) 
      beta_module_mor.
Next Obligation.
Proof.
  
  dependent destruction x.
  dependent destruction x.
  dependent destruction x.
  
  simpl.
  apply CONSTR_eq; auto.
  destruct S; simpl.
  destruct R; simpl.
  assert (H:=@repr_hom_s _ _ _ _ f).
  simpl in *.
  assert (Habs := H ABS).
  simpl in *.
  unfold commute in Habs; simpl in *.
  assert (Happ := H APP).
  simpl in *.
  unfold commute in Happ; simpl in *.
  rewrite <- Happ.
  apply f_equal.
  simpl in *.
  apply CONSTR_eq; auto.
  rewrite <- Habs.
  auto.
Qed.
  

Definition beta_half_eq := Build_half_equation beta_half_s.


End App_Abs_half_eq.


Definition beta_rule : eq_classic Lambda := {|
   eq1 := beta_half_eq ;
   eq2 := subst_half_eq Lambda |}.

Print beta_rule.


















