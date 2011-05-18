Require Import Coq.Relations.Relations.

Require Export CatSem.CAT.Misc.
Require Export CatSem.CAT.product.
Require Export CatSem.CAT.initial_terminal.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.

Unset Automatic Introduction.

Section TYPE.

Section TYPE_data.

Variable A B:Type.
(*Definition TYPE_hom := A -> B.*)
(*Definition TYPE_hom_equiv:
   relation  := fun f g => forall x, f x = g x.*)

Lemma TYPE_hom_oid_prf: 
    Equivalence (A:= A -> B) (fun f g => forall x, f x = g x).
Proof.
  constructor;
  unfold Reflexive; 
  unfold Symmetric; 
  unfold Transitive;
  intros;
  etransitivity;
  eauto.
Qed.

Definition TYPE_hom_oid := Build_Setoid TYPE_hom_oid_prf.

End TYPE_data.

Obligation Tactic := cat; try unf_Proper;
  intros; repeat rew_hyp; auto.

Program Instance TYPE_struct : Cat_struct (fun a b => a -> b) := {
   mor_oid a b := TYPE_hom_oid a b;
   id a := fun x: a => x;
   comp a b c := fun (f:a -> b) (g:b -> c) => fun x => g (f x)
}.

Definition TYPE: Cat := Build_Cat
   TYPE_struct.

End TYPE.

Canonical Structure TYPE.

Obligation Tactic := simpl; intros;
   try unf_Proper;
   intros; elim_conjs;   
   repeat rew_hyp;
   cat.

Hint Extern 1 (_ = _ ) => apply injective_projections; simpl.


Program Instance TYPE_prod : Cat_Prod TYPE := {
  product := prod;
  prl a b := fst;
  prr a b := snd;
  prod_mor a b c f g := fun z => (f z, g z)
}.

Inductive TEMPTY : Type := .

Obligation Tactic := simpl; intros;
  repeat match goal with [H:TEMPTY |- _ ] => elim H end; 
      cat.

Program Instance TYPE_init :  Initial TYPE := {
  Init := TEMPTY
}.

Hint Extern 3 (?a = ?b) => elim a.

Program Instance TYPE_term : Terminal TYPE := {
  Term := unit;
  TermMor a := fun x => tt
}.

Existing Instance TYPE_struct.






