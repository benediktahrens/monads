Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Eqdep.

Require Export CatSem.PCF_o_c.RPCF_rep_hom.

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


Program Instance PCFPO_id_struct : PCFPO_rep_Hom_struct 
   (P:=P) (R:=P) 
   (f:=fun u => u) (fun u => eq_refl) id_arrow_dist RMon_id.
Next Obligation.
Proof.
  simpl.
  intros c y.
  intros.
  unfold rlift. 
  rerew  (rmod_hom_rmkl  (CondB (PCFPO_rep_struct:=P))).
  rewrite (UIP_refl _ _ (
  (arrow_dist_ct4 (Uar:=type_arrow (p:=P)) (U'ar:=type_arrow (p:=P))
     (g:=fun u : type_type P => u) id_arrow_dist 
               (f:=type_mor P) (f':=type_mor P)
     (fun u : TY => eq_refl) Bool Bool Bool Bool))).
     simpl.
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros c y.
  unfold rlift.
  rerew  (rmod_hom_rmkl  (CondN (PCFPO_rep_struct:=P))).
  rewrite (UIP_refl _ _ 
  (arrow_dist_ct4 (Uar:=type_arrow (p:=P)) (U'ar:=type_arrow (p:=P))
     (g:=fun u : type_type P => u) id_arrow_dist 
           (f:=type_mor P) (f':=type_mor P)
     (fun u : TY => eq_refl) Bool Nat Nat Nat)).
  simpl;
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros c y.
  unfold rlift.
  rerew  (rmod_hom_rmkl  (Pred (PCFPO_rep_struct:=P))).
  rewrite (UIP_refl _ _ 
   (arrow_dist_ct2 (Uar:=type_arrow (p:=P)) (U'ar:=type_arrow (p:=P))
     (g:=fun u : type_type P => u) id_arrow_dist 
        (f:=type_mor P) (f':=type_mor P)
     (fun u : TY => eq_refl) Nat Nat)).
  simpl;
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros c y.
  unfold rlift.
  rerew  (rmod_hom_rmkl  (Zero (PCFPO_rep_struct:=P))).
  rewrite (UIP_refl _ _ 
    (arrow_dist_ct2 (Uar:=type_arrow (p:=P)) (U'ar:=type_arrow (p:=P))
     (g:=fun u : type_type P => u) id_arrow_dist 
        (f:=type_mor P) (f':=type_mor P)
     (fun u : TY => eq_refl) Nat Bool)).
  simpl;
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros c y.
  unfold rlift.
  rerew  (rmod_hom_rmkl  (Succ (PCFPO_rep_struct:=P))).
  rewrite (UIP_refl _ _ 
    (arrow_dist_ct2 (Uar:=type_arrow (p:=P)) (U'ar:=type_arrow (p:=P))
     (g:=fun u : type_type P => u) id_arrow_dist 
      (f:=type_mor P) (f':=type_mor P)
     (fun u : TY => eq_refl) Nat Nat)).
  simpl;
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros c y.
  unfold rlift.
  rerew  (rmod_hom_rmkl  (ffff (PCFPO_rep_struct:=P))).
Qed.
Next Obligation.
Proof.
  simpl.
  intros c y.
  unfold rlift.
  rerew  (rmod_hom_rmkl  (tttt (PCFPO_rep_struct:=P))).
Qed.
Next Obligation.
Proof.
  simpl.
  intros t c y.
  unfold rlift.
  rerew  (rmod_hom_rmkl  (bottom t (PCFPO_rep_struct:=P))).
Qed.
Next Obligation.
Proof.
  simpl.
  intros m c y.
  unfold rlift.
  rerew  (rmod_hom_rmkl  (nats m (PCFPO_rep_struct:=P))).
Qed.
Next Obligation.
Proof.
  simpl.
  intros r s c y.
  unfold rlift.
  rerew  (rmod_hom_rmkl  (app r s (PCFPO_rep_struct:=P))).
  rewrite (UIP_refl _ _ (id_arrow_dist r s)).
  simpl.
  auto.
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
  simpl.
  intros t c y.
  unfold rlift.
  simpl.
  rewrite (UIP_refl _ _ (id_arrow_dist t t)).
  simpl.
  rew (rmod_hom_rmkl  (rec t (PCFPO_rep_struct:=P))).
Qed.
Next Obligation.
Proof.
  simpl.
  intros u v c y.
  unfold rlift.
  rerew  (rmod_hom_rmkl  (abs u v (PCFPO_rep_struct:=P))).
  rewrite (UIP_refl _ _ (id_arrow_dist u v)).
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



