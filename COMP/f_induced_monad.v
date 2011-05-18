Require Import CatSem.CAT.monad_h_module.
Require Import CatSem.CAT.cat_INDEXED_TYPE.
Require Import CatSem.CAT.retype_functor.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Automatic Introduction.

Section f.

Variables T U : Type.

Variable f : T -> U.

Variable P : Monad (ITYPE U).

Inductive f_P (V : ITYPE T)(t : T) : Type :=
  | copy : P (retype f V) (f t) -> f_P V t.

Definition inv : forall V t, f_P V t -> P (retype f V) (f t). 
intros.
destruct X.
apply f0.
Defined.

Hint Resolve copy ctype.

Notation "' V" := (retype _ V) (at level 20).



Definition bla  V W (x : forall t : T, V t -> f_P W t):
    forall t : U, (retype f V) t -> P (retype f W) t.
intros.
destruct X.
apply inv.
auto.
Defined.

Obligation Tactic := idtac.

Program Instance f_P_Mon_s : Monad_struct (ITYPE T)(f_P).
Next Obligation.
  simpl.
  intros.
  apply copy.
  apply (weta (Monad_struct := P)).
  apply ctype.
  apply X.
Defined.
Next Obligation.
  simpl.
  intros V W x.
  set (Z := kleisli (Monad_struct := P)).
  set (z := Z (retype f V) (retype f W)).
  simpl in *.
  set (z':= z (bla x)).
  intros.
  
  destruct X.
  apply copy.
  apply z'.
  apply f0.
Defined.
Next Obligation.
Proof.
  unfold Proper,f_P_Mon_s_obligation_2.
  red.
  intros V W g g' H.
  intros t x.
  induction x.
  apply f_equal.
  apply (kleisli_oid (Monad_struct := P)).
  simpl.
  intros t0 x.
  induction x.
  simpl.
  rewrite H.
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros.
  assert (H:=etakl P).
  simpl in *.
  rewrite H.
  simpl.
  generalize (f0 t x).
  intros.
  induction f1.
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros V t x.
  induction x.
  simpl.
  apply f_equal.
  assert (H:=kleta P).
  simpl in H.
  unfold f_P_Mon_s_obligation_1.
  simpl in *.
  rewrite <- H.
  apply (kl_eq P).
  simpl.
  intros.
  induction x.
  simpl.
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros.
  induction x.
  simpl.
  apply f_equal.
  assert (H:=dist (Monad_struct := P)).
  simpl in H.
  rewrite H.
  apply (kl_eq P).
  simpl.
  intros.
  induction x.
  simpl.
  generalize (f0 t0 v).
  intros f2.
  induction f2.
  simpl.
  auto.
Qed.

Definition f_P_Mon := Build_Monad f_P_Mon_s.


Definition bla2:
(forall c : ITYPE T,
  (RETYPE (U:=T) (U':=U) f) (f_P_Mon c) ---> 
       P ((RETYPE (U:=T) (U':=U) f) c)).
intros V u x.
simpl in *.
induction x.
induction v.
apply f0.
Defined.

Program Instance pb_mon_s : 
   gen_Monad_Hom_struct (P:=f_P_Mon) (Q:=P) (F0:=RETYPE f) bla2.
Next Obligation.
Proof.
  simpl.
  intros V W g u x.
  induction x.
  simpl.
  induction v.
  simpl.
  apply (kl_eq P).
  simpl.
  intros t0 x.
  induction x.
  simpl.
  generalize (g t0 v).
  intros.
  induction f1.
  simpl.
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros V t x.
  induction x.
  simpl.
  auto.
Qed.

Definition pb_mon := Build_gen_Monad_Hom pb_mon_s.

Variable W : Monad (ITYPE T).

Variable r : gen_Monad_Hom W P (RETYPE f).

Definition car : (forall c : ITYPE T, W c ---> f_P_Mon c).
simpl.
intros.
set (r' := r c).
simpl in *.
apply copy.
apply r. simpl.
apply (ctype _ X).
Defined.
(*
Program Instance fac : Monad_Hom_struct 
      (P := W) (Q := f_P_Mon) car.
Next Obligation.
Proof.
  simpl.
  intros.
  unfold car.
  apply f_equal.
  assert (H:=gen_monad_hom_kl (gen_Monad_Hom_struct := r)).
  simpl in H.
  unfold retype_map in H.
  simpl in H.
  rewrite <- H.
  simpl.
*)
End f.
