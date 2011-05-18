Require Export CatSem.CAT.monad_haskell.
Require Export CatSem.CAT.orders.
Require Import Coq.Relations.Relations.

Set Implicit Arguments.
Unset Strict Implicit.

Inductive F (V : PO) : Type :=
   | Var : V -> F V
   | Ar : F V -> F V -> F V.


Inductive FPO V : relation (F V) := 
   | arp1 : forall s s' t, FPO s s' -> FPO (Ar s' t) (Ar s t)
   | arp2 : forall s t t', FPO t t' -> FPO (Ar s t) (Ar s t')
(*   | arp : forall s t s' t', FPO s s' -> FPO t t' -> FPO (Ar s' t) (Ar s t') *)
   | varp: forall v v', v << v' -> FPO (Var v) (Var v').

Definition FP (V : PO) := Clos_RT_1n_prf ((@FPO V)).


Instance FPP (V : PO)  : PO_obj_struct (F V) := {
  POprf := FP V
}.

Definition FF (V : PO) : PO := Build_PO_obj (FPP V).

Lemma Ar2 V (s t t' : FF V) : t << t' -> (Ar s t) << (Ar s t').
Proof.
  intro.
  generalize dependent s.
  induction H.
  reflexivity.
  intros.
  constructor 2 with (Ar s y).
  Focus 2. apply IHclos_refl_trans_1n.
  constructor.
  auto.
Qed.

Lemma nnn V (x z : F V):
clos_refl_trans_1n  (F V) (@FPO V) z  x -> 
     clos_refl_trans_n1 (F V) (@FPO V) z x.
Proof.
intro H.
apply clos_rt_rtn1.
apply clos_rt1n_rt.
auto.
Qed.

Lemma kkk V (x z : F V):
clos_refl_trans_n1  (F V) (@FPO V) z  x -> 
     clos_refl_trans_1n (F V) (@FPO V) z x.
Proof.
intro H.
apply clos_rt_rt1n.
apply clos_rtn1_rt.
auto.
Qed.


Lemma Ar1 V (s s' t : FF V) : s' << s -> (Ar s t) << (Ar s' t).
Proof.
  intro.
  generalize dependent t.
  induction H.
  reflexivity.
  intros.
  simpl.
  apply kkk.
  constructor 2 with (Ar y t).
  constructor.
  auto.
  apply nnn.
  apply IHclos_refl_trans_1n.
Qed.
  

Lemma bla : forall V (s t s' t' : FF V) , s << s' -> t << t' -> 
      Ar s' t << Ar s t'.
Proof.
  intros.
  transitivity (Ar s' t').
  apply Ar2.
  auto.
  apply Ar1.
  auto.
Qed.


Fixpoint subst (V W : PO) (f : V ---> FF W) (x : FF V) : FF W := 
  match x with 
  | Var v => f v
  | Ar s t => Ar (subst f s) (subst f t)
 end .

Program Instance _subst V W (f : V ---> FF W) : PO_mor_struct (subst f).
Next Obligation.
Proof.
  unfold Proper; red.
  intros.
  induction H.
  reflexivity.
  transitivity (subst f y);
  auto.
  clear dependent z.
  induction H; simpl.
  apply Ar1.
  auto.
  apply Ar2.
  auto.
  apply f.
  auto.
Qed.

Definition subst_po V W (f : V ---> FF W) := Build_PO_mor (_subst V W f).

Program Instance var V : PO_mor_struct (b:=FF V) (@Var V).
Next Obligation.
Proof.
  unfold Proper; red.
  intros.
  apply clos_refl_trans_1n_contains.
  constructor.
  auto.
Qed.

Definition VAR V := Build_PO_mor (var V).

Program Instance FFMonad : Monad_struct FF := {
  weta := VAR;
  kleisli := subst_po
}.
Next Obligation.
Proof.
  unfold Proper; red.
  simpl.
  intros f g H x.
  induction x; simpl.
  auto.
  rewrite IHx1.
  rewrite IHx2.
  auto.
Qed.
Next Obligation.
Proof.
  induction x;
  simpl.
  auto.
  rewrite IHx2.
  rewrite IHx1.
  auto.
Qed.
Next Obligation.
Proof.
  induction x;
  simpl.
  auto.
  rewrite IHx1.
  rewrite IHx2.
  auto.
Qed.
  
(*
Definition subst V W f : FF V ---> FF W
  
  Focus 2.
  apply f.
  auto.
  
  simpl.
  
  transitivit
  
  apply clos_refl_trans_1n_contains.
  simpl.
  apply 
  apply clos_refl_trans_1n_contains.
  induction H.
  simpl in *.
  constructor;
  auto.
  simpl.
  apply PO_mor_monotone.
  apply f.
  apply 
  constructor.
  apply clos_refl_trans_1n_contains.
  constructor. 
  app
  simpl.
  apply reflexivity.
  apply PO_refl.
  simpl.

*)























