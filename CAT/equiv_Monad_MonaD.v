Require Import CatSem.CAT.monad_morphism.
Require Import CatSem.CAT.monad_h_morphism.

Require Import CatSem.CAT.monic_epi.
Require Import CatSem.CAT.nat_iso.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Let MON := CatSem.CAT.monad_morphism.MONAD.

Let mon := CatSem.CAT.monad_h_morphism.MONAD.

Section equivalence.

Variable C : Cat.

(** Functor mon -> MON *)

Section mon_to_MON_ob.

Variable M : mon C.

Obligation Tactic := simpl; intros; 
     unfold subst_ax, eta_mu_ax1, eta_mu_ax2;
     simpl; intros; monad.

Program Instance mon_to_MON_struct : MonaD_struct M := {
 Eta := (weta_NT M) ;
 Mu := join_NT M
}.

Canonical Structure mon_to_MON := Build_MonaD mon_to_MON_struct.

End mon_to_MON_ob.

Section mon_to_MON_mor.

Variables M N : mon C.

Variable f : M ---> N.

Program Instance mon_to_MON_f_s : MonaD_Hom_struct (Monad_Hom_NT f).
Next Obligation.
Proof.
  unfold eta_tau_def.
  simpl; intros; monad; try apply f.
Qed. 
Next Obligation.
Proof.
  unfold tau_tau_def.
  simpl; intros; monad; try apply f.
Qed.
Next Obligation.
Proof.
  unfold mu_tau_def.
  simpl; intros; monad; try apply f.
Qed.

Canonical Structure mon_to_MON_f := Build_MonaD_Hom mon_to_MON_f_s.

End mon_to_MON_mor.

Program Instance mon_to_MON_func : Functor_struct (Fobj:= mon_to_MON) mon_to_MON_f.
Next Obligation.
Proof.
  unfold Proper, respectful.
  simpl; intros.
  auto.
Qed.
Next Obligation.
Proof.
  reflexivity.
Qed.
Next Obligation.
Proof.
  unfold vcompNT1.
  simpl.
  reflexivity.
Qed.

Definition mon_2_MON := Build_Functor mon_to_MON_func.

Section MON_to_mon_ob.

Variable M : MON C.

Obligation Tactic := simpl; intros; 
     unfold subst_ax, eta_mu_ax1, eta_mu_ax2;
     simpl; intros; monad.

Obligation Tactic := unfold Proper, respectful;
            simpl; intros; repeat 
              (apply bind_bind || apply bind_eta || 
                     apply eta_bind).

Program Instance MON_to_mon_struct : Monad_struct M := {
 weta := Eta (MonaD_struct:=M);
 kleisli := bind (M:=M)
}.
Next Obligation.
Proof.
  unfold bind.
  rewrite H.
  reflexivity.
Qed.
(*
Next Obligation.
  apply (eta_bind f).
Qed.
Next Obligation.
Proof.
  apply (bind_eta _ a).
Qed.
*)

Canonical Structure MON_to_mon := Build_Monad MON_to_mon_struct.

End MON_to_mon_ob.


Section MON_to_mon_mor.

Variables P Q : MON C.

Variable M : P ---> Q.

Program Instance MON_to_mon_f_s : Monad_Hom_struct
    (P:= MON_to_mon P) (Q:=MON_to_mon Q) M.
Next Obligation.
Proof.
  unfold bind; simpl.
  assert (H:=Eta_Tau (MonaD_Hom_struct:=M)).
  unfold eta_tau_def in H; simpl in H.
  assert (H':=Mu_Tau(MonaD_Hom_struct:=M)).
  unfold mu_tau_def in H'; simpl in H'.
  rewrite assoc.
  rewrite H'.
  repeat rewrite <- assoc.
  apply postcomp.
  assert (H2:=NTcomm (Mu (MonaD_struct:=P))).
  simpl in H2.
  assert (H3:=NTcomm M).
  simpl in H3.
  rewrite H3.
  rewrite FComp.
  repeat rewrite assoc.
  apply praecomp.
  rewrite H3.
  reflexivity.
Qed.
Next Obligation.
Proof.
  rew (@Eta_Tau _ _ _ _ _ M M c).
  reflexivity.
Qed.

Canonical Structure MON_to_mon_f := Build_Monad_Hom MON_to_mon_f_s.

End MON_to_mon_mor.

 Instance MONAD_struct' : Cat_struct (Monad_Hom (C:=C)) := (MONAD_struct C).

Program Instance MON_to_mon_func : Functor_struct (Fobj:= MON_to_mon) MON_to_mon_f.
Next Obligation.
Proof.
  unfold Proper, respectful.
  simpl; intros.
  auto.
Qed.
Next Obligation.
Proof.
  reflexivity.
Qed.
Next Obligation.
Proof.
  unfold vcompNT1.
  simpl.
  reflexivity.
Qed.

Definition MON_2_mon : Functor (MON C) (mon C) := Build_Functor MON_to_mon_func.

Section mon_2_MON__then__MON_2_mon.

Variable P : mon C.

Program Instance lb : Monad_Hom_struct (P:=P)(Q:=MON_2_mon (mon_2_MON P)) (fun c => id _ ).
Next Obligation.
Proof.
  cat.
  unfold bind.
  simpl.
  unfold lift, join.
  simpl.
  rewrite klkl.
  apply kl_eq.
  cat.
  rewrite assoc.
  rewrite etakl.
  cat.
Qed.
Next Obligation.
Proof.
  cat.
Qed.

Definition lbx : P ---> MON_2_mon (mon_2_MON P) := Build_Monad_Hom lb.

Program Instance bl : Monad_Hom_struct (P:=MON_2_mon (mon_2_MON P))(Q:=P) (fun c => id _ ).
Next Obligation.
Proof.
  cat.
  unfold bind.
  simpl.
  unfold lift, join.
  simpl.
  rewrite klkl.
  apply kl_eq.
  cat.
  rewrite assoc.
  rewrite etakl.
  cat.
Qed.
Next Obligation.
Proof.
  cat.
Qed.

Definition blx : MON_2_mon (mon_2_MON P) ---> P := Build_Monad_Hom bl. 

Obligation Tactic := cat.

Program Instance tt : Invertible lbx := {
  inverse := blx
}.

End mon_2_MON__then__MON_2_mon.

(*
Definition xy : forall c : mon C, (Id (mon C)) c ---> (MON_2_mon O mon_2_MON) c.
simpl.
apply lb.
*)

Obligation Tactic := cat.

Program Instance lb_NT_s : 
     NT_struct (F:= Id _ ) (G:=  MON_2_mon O mon_2_MON) (fun P => Build_Monad_Hom (lb P)).
Program Instance bl_NT_s : 
     NT_struct (F:=  MON_2_mon O mon_2_MON)(G:= Id _ ) (fun P => Build_Monad_Hom (bl P)).

Program Instance lb_niso : NISO_struct (Build_NT lb_NT_s) := {
  NT_inv := fun c => tt c
}.


(** we omit the other nat isomorphism *)

End equivalence.

(*
Record NISO := {
  tra :> NT F G;
  niso_struct :> NISO_struct tra
}.

Definition lb_NT := Build_NT lb_NT_s.
Definition bl_NT := Build_NT bl_NT_s.



Section mon_2_MON__then__MON_2_mon.

Variable P : mon C.

Program Instance lb : Monad_Hom_struct (P:=P)(Q:=MON_2_mon (mon_2_MON P)) (fun c => id _ ).
Next Obligation.
Proof.
  cat.
  unfold bind.
  simpl.
  unfold lift, join.
  simpl.
  rewrite klkl.
  apply kl_eq.
  cat.
  rewrite assoc.
  rewrite etakl.
  cat.
Qed.
Next Obligation.
Proof.
  cat.
Qed.

End mon_2_MON__then__MON_2_mon.

(*
Definition xy : forall c : mon C, (Id (mon C)) c ---> (MON_2_mon O mon_2_MON) c.
simpl.
apply lb.
*)

Obligation Tactic := cat.

Program Instance lb_NT_s : 
     NT_struct (F:= Id _ ) (G:=  MON_2_mon O mon_2_MON) (fun P => Build_Monad_Hom (lb P)).

*)




