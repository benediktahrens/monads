Require Import Coq.Logic.Eqdep.
Require Import Coq.Logic.FunctionalExtensionality.

Require Export CatSem.COMP.PCF_rep.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.



(** on our way to a category of representations:
    - an equality on morphisms of reps
*)

Inductive eq_Rep (P R : PCF_rep) : relation (PCF_rep_Hom P R) :=
 | eq_rep : forall (a c : PCF_rep_Hom P R), 
            forall H : (forall t, tcomp c t = tcomp a t),
            (forall V, rep_Hom_monad a V ;; lift (M:=R) (Transp H V)
                                    == 
                       Transp H (P V) ;; rep_Hom_monad c V ) ->
             
             eq_Rep a c.
  
(** the defined relation is an equivalence and 
    may hence serve as equality 
*)

Lemma eq_Rep_equiv (P R: PCF_rep) : 
   @Equivalence (PCF_rep_Hom P R) 
     (@eq_Rep P R).
Proof.
 intros P R.
 split.
 
 unfold Reflexive.
 intro M. 
 assert (H': forall t, tcomp M t = tcomp M t) by 
       (intros; reflexivity).

 apply (eq_rep (H:=H')).
 
 simpl.
 intros V t y.
 destruct y as [t y].
 
 simpl. 
 rewrite (UIP_refl _ _ (H' t)).
 simpl.
 assert (H:= lift_transp_id).
 simpl in *.
 rewrite H.
 auto.

  (* now symmetric *)
 
 unfold Symmetric.
 intros M N H.
 destruct H.
  assert (H': forall t, tcomp a t = tcomp c t) by auto.
 apply (eq_rep (H:=H')). 
 simpl; intros V t y.
 destruct a.
 destruct c.
 simpl in *.
 assert (H3 : tcomp = tcomp0).
 apply (functional_extensionality).
 auto.
 
 generalize dependent y. 
 generalize dependent H'.
 generalize dependent rep_Hom_monad0.
 generalize dependent rep_Hom_monad.
 generalize dependent ttriag.
 generalize dependent ttriag0.
 generalize dependent H.
 rewrite  H3.
 intros; simpl in *.
 rewrite transp_id. 
 assert (H2:= lift_transp_id).
 simpl in H2.
 rewrite H2.
 assert (H4 := H0 V t y).
 rewrite transp_id in H4.
 rewrite H2 in H4.
 simpl in *; auto.

  (* finally transitive *)

  unfold Transitive.
  intros a b c H H'.
  destruct H;
  destruct H'.
  assert (Ht : forall t, tcomp c t = tcomp a t).
    intro t. transitivity (tcomp a0 t); auto.
    
  apply (eq_rep (H:=Ht)).
  simpl; intros V t y.
  destruct a;
  destruct a0;
  destruct c.
  simpl in *.
  assert (H5 : tcomp0 = tcomp1) by
    (apply functional_extensionality; intro; auto).

  assert (H6 : tcomp1 = tcomp) by
    (apply functional_extensionality; intro; auto).
  
  generalize dependent H2. 
  generalize dependent H1. 
  generalize dependent rep_Hom_monad.
  generalize dependent rep_Hom_monad1.
  generalize dependent rep_Hom_monad0.
  generalize dependent ttriag.
  generalize dependent ttriag1.
  generalize dependent ttriag0.
  generalize dependent H.
  generalize dependent Ht.
  rewrite  H5.
  rewrite  H6.
  
  clear H6 H5.
  clear tcomp0.
  clear tcomp1.
  
  intros.
  assert (H7:=H0 V t y).
  assert (H9:=H2 V t y).
  rewrite transp_id in *.
  simpl in *.
  assert (H8 := lift_transp_id).
  simpl in H8.
  rewrite H8 in *.
  transitivity (rep_Hom_monad0 V t y); 
  auto.
Qed.
  
Definition eq_Rep_oid (P R : PCF_rep) := Build_Setoid (eq_Rep_equiv P R).


(** Identity Representation *)

Section id_rep.

Variable P : PCF_rep.

Definition id_rep_car:
(forall c : ITYPE (type_type P),
  (RETYPE (fun t : type_type P => t)) (P c) --->
  P ((RETYPE (fun t : type_type P => t)) c)) :=
    
 fun V t y => 
   match y with ctype _ z => 
     lift (M:=P) (@id_retype _ V) _ z end.


Obligation Tactic := idtac.

Program Instance blalala : 
       colax_Monad_Hom_struct (P:=P) (Q:=P) (F0:=RETYPE (fun t => t))
       id_rep_car.
Next Obligation.
Proof.
  simpl.
  intros V W f t y.
  destruct y.
  simpl.
  assert (H:=lift_kleisli (M:= P)).
  simpl in *.
  rewrite H. simpl.
  assert (H':=kleisli_lift (M:=P)).
  simpl in H'.
  rewrite H'.
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros V t y.
  destruct y.
  simpl.
  assert (H:=lift_weta P).
  simpl in H.
  rewrite H.
  auto.
Qed.

Definition id_Rep_monad := Build_colax_Monad_Hom blalala.

Program Instance Rep_id_struct : 
         PCF_rep_Hom_struct (f := fun t => t) 
         (fun t => eq_refl) id_Rep_monad. 
Next Obligation.
Proof.
  simpl.
  intros V y.
  assert (H := mod_hom_mkl 
      (Module_Hom_struct :=(Succ(PCF_rep_s:=P)))).
  unfold lift.
  simpl in *.
  rewrite <- H.
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros V y.
  assert (H := mod_hom_mkl 
      (Module_Hom_struct :=(Zero(PCF_rep_s:=P)))).
  unfold lift.
  simpl in *.
  rewrite <- H.
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros V y.
  assert (H := mod_hom_mkl 
      (Module_Hom_struct :=(CondB(PCF_rep_s:=P)))).
  unfold lift.
  simpl in *.
  rewrite <- H.
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros V y.
  assert (H := mod_hom_mkl 
      (Module_Hom_struct :=(CondN(PCF_rep_s:=P)))).
  unfold lift.
  simpl in *.
  rewrite <- H.
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros V y.
  assert (H := mod_hom_mkl 
      (Module_Hom_struct :=(tttt(PCF_rep_s:=P)))).
  unfold lift.
  simpl in *.
  rewrite <- H.
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros V y.
  assert (H := mod_hom_mkl 
      (Module_Hom_struct :=(ffff(PCF_rep_s:=P)))).
  unfold lift.
  simpl in *.
  rewrite <- H.
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros m V y.
  assert (H := mod_hom_mkl 
      (Module_Hom_struct :=(nats m(PCF_rep_s:=P)))).
  unfold lift.
  simpl in *.
  rewrite <- H.
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros t V y.
  assert (H := mod_hom_mkl 
      (Module_Hom_struct :=(bottom t(PCF_rep_s:=P)))).
  unfold lift.
  simpl in *.
  rewrite <- H.
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros t V y.
  assert (H := mod_hom_mkl 
      (Module_Hom_struct :=(rec t(PCF_rep_s:=P)))).
  unfold lift.
  simpl in *.
  rewrite <- H.
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros r s V y.
  assert (H := mod_hom_mkl 
      (Module_Hom_struct :=(app(PCF_rep_s:=P) r s ))).
  unfold lift.
  simpl in *.
  rewrite <- H.
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros r s V y.
  assert (H := mod_hom_mkl 
     (Module_Hom_struct :=(abs(PCF_rep_s:=P) r s))).
  unfold lift.
  simpl in *.
  rewrite <- H.
  apply f_equal.
  assert (H' := klkl P).
  simpl in H'.
  rewrite H'.
  assert (H'':= kl_eq P).
  simpl in *.
  apply H''.
  clear y.
  
  intros t y.
  assert (H4 := etakl P).
  simpl in H4.
  rewrite H4.
  simpl.
  destruct y as [t y | ].
  simpl.
  unfold lift.
  rewrite H4.
  simpl.
  auto.
  simpl.
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros V y.
  assert (H := mod_hom_mkl 
      (Module_Hom_struct :=(Pred(PCF_rep_s:=P)))).
  unfold lift.
  simpl in *.
  rewrite <- H.
  auto.
Qed.

Definition Rep_id := Build_PCF_rep_Hom (Rep_id_struct).

End id_rep.


Existing Instance eq_Rep_oid.
Existing Instance pcf_rep_struct.
Existing Instance rep_gen_Hom_monad_struct.
