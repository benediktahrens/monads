Require Export CatSem.PROP_untyped.prop_arities_initial.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Automatic Introduction.
Unset Transparent Obligations.

Check sub.

Print Signature.

Inductive Lambda_index := ABS | APP.

Definition Lambda : Signature := {|
  sig_index := Lambda_index ;
  sig := fun x => match x with 
                  | ABS => [[ 1 ]] 
                  | APP => [[ 0 ; 0]]
                  end
|}.

Print half_eq_classic.
Check subst_half.
Definition Lambda_subst := subst_half Lambda.
Check Lambda_subst.

Section App_Abs_half_eq.

Variable R : REP Lambda.

Definition blubb1  :
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
set (HH := Repr APP).
simpl in HH.
destruct HH.
simpl in *.
apply rmodule_hom.
simpl in *.
constructor.
simpl.
set (HH1 := Repr ABS).
apply HH1.
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


End App_Abs_half_eq.

