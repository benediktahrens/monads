Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Eqdep.

Require Export CatSem.RPCF.RPCF_rep_hom.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Section id_rep.

Variable P : PCFPO_rep.

Definition id_rep_car c:
(forall t : type_type P,
  (retype_ipo (fun u : type_type P => u) (P c)) t ->
  (P (retype (fun u : type_type P => u) c)) t) :=
fun  t y => 
   match y with ctype _ z => 
     rlift P (@id_retype _ c) _ z end.

Obligation Tactic := idtac.

Program Instance id_rep_pos c:
ipo_mor_struct (a:=retype_ipo (fun u : type_type P => u) (P c))
  (b:=P (retype (fun u : type_type P => u) c)) (@id_rep_car c).
Next Obligation.
Proof.
  intros c t.
  unfold Proper;
  red.
  intros y z H;
  simpl in *.
  induction H.
  simpl.
  apply (rlift P (id_retype (V:=c))).
  auto.
Qed.

Definition id_rep_po c := Build_ipo_mor (id_rep_pos c).

Definition id_rep_c :
(forall c : ITYPE (type_type P),
  (RETYPE_PO (fun u : type_type P => u)) (P c) --->
  P ((RETYPE (fun u : type_type P => u)) c)) :=
      id_rep_po.


Program Instance RMon_id_s :
  gen_RMonad_Hom_struct (P:=P) (Q:=P) 
   (G1:=RETYPE (fun u : type_type P => u))
   (G2:=RETYPE_PO (fun u : type_type P => u))
   (NNNT1 (fun u : type_type P => u)) id_rep_c.
Next Obligation.
Proof.
  simpl.
  intros V t y.
  destruct y as [t y];
  simpl.
  rew (rlift_rweta P).
Qed.
Next Obligation.
Proof.
  simpl.
  intros V W f t z.
  destruct z as [t z];
  simpl.
  rew (rlift_rkleisli (M:=P)).
  rew (rkleisli_rlift (M:=P)).
  apply (rkl_eq P).
  simpl.
  auto.
Qed.

Definition RMon_id := Build_gen_RMonad_Hom RMon_id_s.

Lemma id_arrow_dist:
forall u v : type_type P,
  (fun u0 : type_type P => u0) (u ~~> v) =
  (fun u0 : type_type P => u0) u ~~> (fun u0 : type_type P => u0) v.
Proof.
  simpl.
  reflexivity.
Qed.

Check PCFPO_rep_Hom_struct.

Program Instance PCFPO_id_struct : PCFPO_rep_Hom_struct 
   (P:=P) (R:=P) 
   (f:=fun u => u) (fun u v => eq_refl) (eq_refl) eq_refl RMon_id.
Next Obligation.
Proof.
  unfold CondB_hom'; 
  simpl.
  intros c y.
  intros.
  unfold rlift.
  simpl.
  rerew  (rmod_hom_rmkl  (CondB (PCFPO_rep_struct:=P))).
Qed.
Next Obligation.
Proof.
  unfold CondN_hom';
  simpl.
  intros c y.
  unfold rlift.
  rerew  (rmod_hom_rmkl  (CondN (PCFPO_rep_struct:=P))).
Qed.
Next Obligation.
Proof.
  unfold Pred_hom';
  simpl.
  intros c y.
  unfold rlift.
  rerew  (rmod_hom_rmkl  (Pred (PCFPO_rep_struct:=P))).
Qed.
Next Obligation.
Proof.
  unfold Zero_hom';
  simpl.
  intros c y.
  unfold rlift.
  rerew  (rmod_hom_rmkl  (Zero (PCFPO_rep_struct:=P))).
Qed.
Next Obligation.
Proof.
  unfold Succ_hom';
  simpl.
  intros c y.
  unfold rlift.
  rerew  (rmod_hom_rmkl  (Succ (PCFPO_rep_struct:=P))).
Qed.
Next Obligation.
Proof.
  unfold fff_hom';
  simpl.
  intros c y.
  unfold rlift.
  rerew  (rmod_hom_rmkl  (ffff (PCFPO_rep_struct:=P))).
Qed.
Next Obligation.
Proof.
  unfold ttt_hom';
  simpl.
  intros c y.
  unfold rlift.
  rerew  (rmod_hom_rmkl  (tttt (PCFPO_rep_struct:=P))).
Qed.
Next Obligation.
Proof.
  unfold bottom_hom';
  simpl.
  intros t c y.
  unfold rlift.
  rerew  (rmod_hom_rmkl  (bottom t (PCFPO_rep_struct:=P))).
Qed.
Next Obligation.
Proof.
  unfold nats_hom';
  simpl.
  intros m c y.
  unfold rlift.
  rerew  (rmod_hom_rmkl  (nats m (PCFPO_rep_struct:=P))).
Qed.
Next Obligation.
Proof.
  unfold app_hom';
  simpl.
  intros r s c y.
  unfold rlift.
  rerew  (rmod_hom_rmkl  (app r s (PCFPO_rep_struct:=P))).
Qed.
(*
Next Obligation.
Proof.
  simpl.
  intros r s c y.
  unfold rlift.
  rerew  (rmod_hom_rmkl  (abs r s (PCFPO_rep_struct:=P))).
  rewrite (UIP_refl _ _ (id_arrow_dist r s)).
  simpl.
  apply f_equal.
  rew (rklkl P).
  apply (rkl_eq P).
  simpl.
  intros t z.
  rew (retakl P).
  destruct z as [t z | ];
  simpl.
  rew (rlift_rweta P).
  auto.
Qed.
*)
Next Obligation.
Proof.
  unfold rec_hom';
  simpl.
  intros t c y.
  unfold rlift.
  simpl.
  rew (rmod_hom_rmkl  (rec t (PCFPO_rep_struct:=P))).
Qed.
Next Obligation.
Proof.
  unfold abs_hom2';
  simpl.
  intros u v c y.
  unfold rlift.
  rerew  (rmod_hom_rmkl  (abs u v (PCFPO_rep_struct:=P))).
(*  rewrite (UIP_refl _ _ (id_arrow_dist u v)).*)
  simpl.
  apply f_equal.
  rew (rklkl P).
  apply (rkl_eq P).
  simpl.
  intros t z.
  rew (retakl P).
  destruct z as [t z | ];
  simpl.
  rew (rlift_rweta P).
  auto.
Qed.


Definition PCFPO_id := Build_PCFPO_rep_Hom PCFPO_id_struct.

End id_rep.



