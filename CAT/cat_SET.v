
Require Import Coq.Relations.Relations.

Require Export Misc.
Require Export CatSem.CAT.category.
Require Import CatSem.CAT.product.
Require Import CatSem.CAT.initial_terminal.
Require Import CatSem.CAT.coproduct.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.


Section SET.

Section SET_data.

Variable A B:Set.

Definition SET_hom_equiv:
   relation (A -> B) := fun f g => forall x, f x = g x.

Lemma SET_hom_oid_prf: @Equivalence (A -> B) 
                       (fun f g => forall x, f x = g x).
Proof.
  constructor;
  unfold Reflexive; 
  unfold Symmetric; 
  unfold Transitive;
  intros;
  etransitivity;
  eauto.
Qed.

Definition SET_hom_oid := Build_Setoid SET_hom_oid_prf.

End SET_data.

Obligation Tactic := cat; try unf_Proper;
  intros; repeat rew_hyp; auto.

Program Instance SET_catstruct : Cat_struct (fun a b : Set => a -> b) := {
   mor_oid a b := SET_hom_oid a b;
   id a := fun x: a => x;
   comp a b c f g := fun x => g (f x)
}.

Definition SET := Build_Cat SET_catstruct.

End SET.

Section SET_INIT_TERM.

Inductive Empty : Set := .

Obligation Tactic := simpl; intros;
  repeat match goal with [H:Empty |- _ ] => elim H end; 
      cat.

Program Instance SET_INIT : Initial SET := {
   Init := Empty }.

Hint Extern 3 (?a = ?b) => elim a.

Program Instance SET_TERM : Terminal SET := {
    Term := unit;
    TermMor A := fun x => tt
}.

End SET_INIT_TERM.

Section SET_COPROD.

Inductive SET_COPROD_ob (A B: Set): Set := 
  | INL : A -> SET_COPROD_ob A B
  | INR : B -> SET_COPROD_ob A B.

Obligation Tactic := simpl; intros;
  repeat unf_Proper;
  intros;
  repeat match goal with 
      [x : SET_COPROD_ob _ _ |- _ ] => destruct x end;
  elim_conjs;
  auto.

Program Instance SET_COPROD : Cat_Coprod SET := {
  coprod a b := SET_COPROD_ob a b;
  inl a b x := INL (A:=a) b x;
  inr a b x := INR a x;
  coprod_mor a b d f g := 
         fun x => match x with INL a => f a | 
                               INR b => g b end
}.

End SET_COPROD.

Section SET_PROD.

Obligation Tactic := simpl; intros;
   try unf_Proper;
   intros; elim_conjs;   
   repeat rew_hyp;
   cat.

Hint Extern 1 (_ = _ ) => apply injective_projections; simpl.

Program Instance SET_PRODUCT: Cat_Prod (SET) := {
  product a b := prod a b;
  prl a b x := fst x;
  prr a b x := snd x;
  prod_mor a c d f g := fun x => (f x, g x)
}.

End SET_PROD.

















