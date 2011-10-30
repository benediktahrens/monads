Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Eqdep.

Require Export CatSem.COMP.PCF_eq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Notation "'IT'" := (ITYPE TY).
Notation "a '~>' b" := (PCF.Arrow a b) 
     (at level 69, right associativity).
Notation "a 'x' b" := (product a b) (at level 30).
Notation "P [ z ]" := (ITFIB_MOD _ z P) (at level 35).
Notation "'d' P // s" := (ITDER_MOD _ _ s P) (at level 25).
Notation "f 'X' g" := (product_mor _ f g)(at level 30).

(** the base types *)


Section comp_red.


Variables P Q R : PCF_rep.
Variable M : PCF_rep_Hom P Q.
Variable N : PCF_rep_Hom Q R.

Lemma functy t : 
   tcomp N (tcomp M (type_mor P t)) = 
                 type_mor R t.
Proof.
  intros.
  simpl.
  rewrite (ttriag M).
  rewrite (ttriag N).
  auto.
Qed.

Obligation Tactic := idtac.

Program Instance Rep_comp_struct : 
  PCF_rep_Hom_struct (f := fun t => tcomp N (tcomp M t)) 
      functy (comp_Rep_monad M N).
Next Obligation.
Proof.
  simpl.
  intros V TT.
  elim TT.
  simpl.
  assert (HM:= Succ_Hom (PCF_rep_Hom_struct := M)).
  simpl in HM.
  assert (HN:= Succ_Hom (PCF_rep_Hom_struct := N)).
  simpl in HN.
  generalize functy.
  destruct M.
  destruct N.
  simpl in *.
  clear M.
  clear N.
  destruct R.
  clear R.
  destruct Q.
  clear Q.
  destruct P.
  clear P.
  simpl in *.
  
  assert (H' : (fun t => tcomp0 (tcomp (type_mor1 t))) 
           = type_mor).
     apply functional_extensionality.
     intros; 
     rewrite ttriag;
     rewrite ttriag0;
     auto.
  assert (H1 : (fun t => tcomp (type_mor1 t)) = type_mor0).
    apply functional_extensionality; auto.
  assert (H2 : (fun t => tcomp0 (type_mor0 t)) = type_mor).
    apply functional_extensionality; auto.

     
  generalize dependent rep_gen_Hom_monad_struct.
  generalize dependent rep_gen_Hom_monad_struct0.
  generalize dependent pcf_rep_struct.
  generalize dependent rep_Hom_monad0.
  generalize dependent pcf_rep_monad.
  generalize dependent rep_Hom_monad.
  generalize dependent pcf_rep_monad1.
  generalize dependent ttriag.
  generalize dependent pcf_rep_struct0.
  generalize dependent pcf_rep_monad0.
  generalize dependent ttriag0.
  rewrite <- H'.
  rewrite <- H1.
  
  intros;
  simpl.

  
  rewrite (UIP_refl _ _ (e _)).
  simpl.
  
  rewrite (UIP_refl _ _ (ttriag _ )) in HM.
  simpl in HM.
  rewrite (UIP_refl _ _ (ttriag0 _ )) in HN.
  simpl in HN.
  
  rewrite HM.
  rewrite HN.
  simpl.
  
  unfold lift.
  simpl.
  assert (H := mod_hom_mkl 
      (Module_Hom_struct :=
            (Succ (PCF_rep_s := pcf_rep_struct)))).
  simpl in H.
  rewrite <- H.
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros V TT.
  elim TT.
  simpl.
  assert (HM:= Zero_Hom (PCF_rep_Hom_struct := M)).
  simpl in HM.
  assert (HN:= Zero_Hom (PCF_rep_Hom_struct := N)).
  simpl in HN.
  generalize functy.
  destruct M.
  destruct N.
  simpl in *.
  clear M.
  clear N.
  destruct R.
  clear R.
  destruct Q.
  clear Q.
  destruct P.
  clear P.
  simpl in *.
  
  assert (H' : (fun t => tcomp0 (tcomp (type_mor1 t))) 
           = type_mor).
     apply functional_extensionality.
     intros; 
     rewrite ttriag;
     rewrite ttriag0;
     auto.
  assert (H1 : (fun t => tcomp (type_mor1 t)) = type_mor0).
    apply functional_extensionality; auto.
  assert (H2 : (fun t => tcomp0 (type_mor0 t)) = type_mor).
    apply functional_extensionality; auto.

     
  generalize dependent rep_gen_Hom_monad_struct.
  generalize dependent rep_gen_Hom_monad_struct0.
  generalize dependent pcf_rep_struct.
  generalize dependent rep_Hom_monad0.
  generalize dependent pcf_rep_monad.
  generalize dependent rep_Hom_monad.
  generalize dependent pcf_rep_monad1.
  generalize dependent ttriag.
  generalize dependent pcf_rep_struct0.
  generalize dependent pcf_rep_monad0.
  generalize dependent ttriag0.
  rewrite <- H'.
  rewrite <- H1.
  
  intros;
  simpl.

  
  rewrite (UIP_refl _ _ (e _)).
  simpl.
  rewrite (UIP_refl _ _ (ttriag _ )) in HM.
  simpl in HM.
  rewrite (UIP_refl _ _ (ttriag0 _ )) in HN.
  simpl in HN.
  
  rewrite HM.
  rewrite HN.
  simpl.
  
  unfold lift.
  simpl.
  assert (H := mod_hom_mkl 
      (Module_Hom_struct :=
            (Zero (PCF_rep_s := pcf_rep_struct)))).
  simpl in H.
  rewrite <- H.
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros V TT.
  elim TT.
  simpl.
  assert (HM:= CondB_Hom (PCF_rep_Hom_struct := M)).
  simpl in HM.
  assert (HN:= CondB_Hom (PCF_rep_Hom_struct := N)).
  simpl in HN.
  generalize functy.
  destruct M.
  destruct N.
  simpl in *.
  clear M.
  clear N.
  destruct R.
  clear R.
  destruct Q.
  clear Q.
  destruct P.
  clear P.
  simpl in *.
  
  assert (H' : (fun t => tcomp0 (tcomp (type_mor1 t))) 
           = type_mor).
     apply functional_extensionality.
     intros; 
     rewrite ttriag;
     rewrite ttriag0;
     auto.
  assert (H1 : (fun t => tcomp (type_mor1 t)) = type_mor0).
    apply functional_extensionality; auto.
  assert (H2 : (fun t => tcomp0 (type_mor0 t)) = type_mor).
    apply functional_extensionality; auto.

     
  generalize dependent rep_gen_Hom_monad_struct.
  generalize dependent rep_gen_Hom_monad_struct0.
  generalize dependent pcf_rep_struct.
  generalize dependent rep_Hom_monad0.
  generalize dependent pcf_rep_monad.
  generalize dependent rep_Hom_monad.
  generalize dependent pcf_rep_monad1.
  generalize dependent ttriag.
  generalize dependent pcf_rep_struct0.
  generalize dependent pcf_rep_monad0.
  generalize dependent ttriag0.
  rewrite <- H'.
  rewrite <- H1.
  
  intros;
  simpl.

  
  rewrite (UIP_refl _ _ (e _)).
  simpl.
  
  rewrite (UIP_refl _ _ (ttriag _ )) in HM.
  simpl in HM.
  rewrite (UIP_refl _ _ (ttriag0 _ )) in HN.
  simpl in HN.
  
  rewrite HM.
  rewrite HN.
  simpl.
  
  unfold lift.
  simpl.
  assert (H := mod_hom_mkl 
      (Module_Hom_struct :=
            (CondB (PCF_rep_s := pcf_rep_struct)))).
  simpl in H.
  rewrite <- H.
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros V TT.
  elim TT.
  simpl.
  assert (HM:= CondN_Hom (PCF_rep_Hom_struct := M)).
  simpl in HM.
  assert (HN:= CondN_Hom (PCF_rep_Hom_struct := N)).
  simpl in HN.
  generalize functy.
  destruct M.
  destruct N.
  simpl in *.
  clear M.
  clear N.
  destruct R.
  clear R.
  destruct Q.
  clear Q.
  destruct P.
  clear P.
  simpl in *.
  
  assert (H' : (fun t => tcomp0 (tcomp (type_mor1 t))) 
           = type_mor).
     apply functional_extensionality.
     intros; 
     rewrite ttriag;
     rewrite ttriag0;
     auto.
  assert (H1 : (fun t => tcomp (type_mor1 t)) = type_mor0).
    apply functional_extensionality; auto.
  assert (H2 : (fun t => tcomp0 (type_mor0 t)) = type_mor).
    apply functional_extensionality; auto.

     
  generalize dependent rep_gen_Hom_monad_struct.
  generalize dependent rep_gen_Hom_monad_struct0.
  generalize dependent pcf_rep_struct.
  generalize dependent rep_Hom_monad0.
  generalize dependent pcf_rep_monad.
  generalize dependent rep_Hom_monad.
  generalize dependent pcf_rep_monad1.
  generalize dependent ttriag.
  generalize dependent pcf_rep_struct0.
  generalize dependent pcf_rep_monad0.
  generalize dependent ttriag0.
  rewrite <- H'.
  rewrite <- H1.
  
  intros;
  simpl.

  
  rewrite (UIP_refl _ _ (e _)).
  simpl.
  
  
  rewrite (UIP_refl _ _ (ttriag _ )) in HM.
  simpl in HM.
  rewrite (UIP_refl _ _ (ttriag0 _ )) in HN.
  simpl in HN.
  
  rewrite HM.
  rewrite HN.
  simpl.
  
  unfold lift.
  simpl.
  assert (H := mod_hom_mkl 
      (Module_Hom_struct :=
            (CondN (PCF_rep_s := pcf_rep_struct)))).
  simpl in H.
  rewrite <- H.
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros V TT.
  elim TT.
  simpl.
  assert (HM:= ttt_Hom (PCF_rep_Hom_struct := M)).
  simpl in HM.
  assert (HN:= ttt_Hom (PCF_rep_Hom_struct := N)).
  simpl in HN.
  generalize functy.
  destruct M.
  destruct N.
  simpl in *.
  clear M.
  clear N.
  destruct R.
  clear R.
  destruct Q.
  clear Q.
  destruct P.
  clear P.
  simpl in *.
  
  assert (H' : (fun t => tcomp0 (tcomp (type_mor1 t))) 
           = type_mor).
     apply functional_extensionality.
     intros; 
     rewrite ttriag;
     rewrite ttriag0;
     auto.
  assert (H1 : (fun t => tcomp (type_mor1 t)) = type_mor0).
    apply functional_extensionality; auto.
  assert (H2 : (fun t => tcomp0 (type_mor0 t)) = type_mor).
    apply functional_extensionality; auto.

     
  generalize dependent rep_gen_Hom_monad_struct.
  generalize dependent rep_gen_Hom_monad_struct0.
  generalize dependent pcf_rep_struct.
  generalize dependent rep_Hom_monad0.
  generalize dependent pcf_rep_monad.
  generalize dependent rep_Hom_monad.
  generalize dependent pcf_rep_monad1.
  generalize dependent ttriag.
  generalize dependent pcf_rep_struct0.
  generalize dependent pcf_rep_monad0.
  generalize dependent ttriag0.
  rewrite <- H'.
  rewrite <- H1.
  
  intros;
  simpl.

  
  rewrite (UIP_refl _  _ (e _)).
  simpl.
  
  
  rewrite (UIP_refl _ _ (ttriag _ )) in HM.
  simpl in HM.
  rewrite (UIP_refl _ _ (ttriag0 _ )) in HN.
  simpl in HN.
  
  rewrite HM.
  rewrite HN.
  simpl.
  
  unfold lift.
  simpl.
  assert (H := mod_hom_mkl 
      (Module_Hom_struct :=
            (tttt (PCF_rep_s := pcf_rep_struct)))).
  simpl in H.
  rewrite <- H.
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros V TT.
  elim TT.
  simpl.
  assert (HM:= fff_Hom (PCF_rep_Hom_struct := M)).
  simpl in HM.
  assert (HN:= fff_Hom (PCF_rep_Hom_struct := N)).
  simpl in HN.
  generalize functy.
  destruct M.
  destruct N.
  simpl in *.
  clear M.
  clear N.
  destruct R.
  clear R.
  destruct Q.
  clear Q.
  destruct P.
  clear P.
  simpl in *.
  
  assert (H' : (fun t => tcomp0 (tcomp (type_mor1 t))) 
           = type_mor).
     apply functional_extensionality.
     intros; 
     rewrite ttriag;
     rewrite ttriag0;
     auto.
  assert (H1 : (fun t => tcomp (type_mor1 t)) = type_mor0).
    apply functional_extensionality; auto.
  assert (H2 : (fun t => tcomp0 (type_mor0 t)) = type_mor).
    apply functional_extensionality; auto.

     
  generalize dependent rep_gen_Hom_monad_struct.
  generalize dependent rep_gen_Hom_monad_struct0.
  generalize dependent pcf_rep_struct.
  generalize dependent rep_Hom_monad0.
  generalize dependent pcf_rep_monad.
  generalize dependent rep_Hom_monad.
  generalize dependent pcf_rep_monad1.
  generalize dependent ttriag.
  generalize dependent pcf_rep_struct0.
  generalize dependent pcf_rep_monad0.
  generalize dependent ttriag0.
  rewrite <- H'.
  rewrite <- H1.
  
  intros;
  simpl.

  
  rewrite (UIP_refl _  _ (e _)).
  simpl.
  
  rewrite (UIP_refl _ _ (ttriag _ )) in HM.
  simpl in HM.
  rewrite (UIP_refl _ _ (ttriag0 _ )) in HN.
  simpl in HN.
  
  rewrite HM.
  rewrite HN.
  simpl.
  
  unfold lift.
  simpl.
  assert (H := mod_hom_mkl 
      (Module_Hom_struct :=
            (ffff (PCF_rep_s := pcf_rep_struct)))).
  simpl in H.
  rewrite <- H.
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros m V TT.
  elim TT.
  simpl.
  assert (HM:= nats_Hom m (PCF_rep_Hom_struct := M)).
  simpl in HM.
  assert (HN:= nats_Hom m (PCF_rep_Hom_struct := N)).
  simpl in HN.
  generalize functy.
  destruct M.
  destruct N.
  simpl in *.
  clear M.
  clear N.
  destruct R.
  clear R.
  destruct Q.
  clear Q.
  destruct P.
  clear P.
  simpl in *.
  
  assert (H' : (fun t => tcomp0 (tcomp (type_mor1 t))) 
           = type_mor).
     apply functional_extensionality.
     intros; 
     rewrite ttriag;
     rewrite ttriag0;
     auto.
  assert (H1 : (fun t => tcomp (type_mor1 t)) = type_mor0).
    apply functional_extensionality; auto.
  assert (H2 : (fun t => tcomp0 (type_mor0 t)) = type_mor).
    apply functional_extensionality; auto.

     
  generalize dependent rep_gen_Hom_monad_struct.
  generalize dependent rep_gen_Hom_monad_struct0.
  generalize dependent pcf_rep_struct.
  generalize dependent rep_Hom_monad0.
  generalize dependent pcf_rep_monad.
  generalize dependent rep_Hom_monad.
  generalize dependent pcf_rep_monad1.
  generalize dependent ttriag.
  generalize dependent pcf_rep_struct0.
  generalize dependent pcf_rep_monad0.
  generalize dependent ttriag0.
  rewrite <- H'.
  rewrite <- H1.
  
  intros;
  simpl.

  rewrite (UIP_refl _  _ (e _)).
  simpl.
  
  
  rewrite (UIP_refl _ _ (ttriag _ )) in HM.
  simpl in HM.
  rewrite (UIP_refl _ _ (ttriag0 _ )) in HN.
  simpl in HN.
  
  rewrite HM.
  rewrite HN.
  simpl.
  
  unfold lift.
  simpl.
  assert (H := mod_hom_mkl 
      (Module_Hom_struct :=
            (nats m (PCF_rep_s := pcf_rep_struct)))).
  simpl in H.
  rewrite <- H.
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros t V TT.
  elim TT.
  simpl.
  assert (HM:= Bottom_Hom t (PCF_rep_Hom_struct := M)).
  simpl in HM.
  assert (HN:= Bottom_Hom t (PCF_rep_Hom_struct := N)).
  simpl in HN.
  generalize functy.
  destruct M.
  destruct N.
  simpl in *.
  clear M.
  clear N.
  destruct R.
  clear R.
  destruct Q.
  clear Q.
  destruct P.
  clear P.
  simpl in *.
  
  assert (H' : (fun t => tcomp0 (tcomp (type_mor1 t))) 
           = type_mor).
     apply functional_extensionality.
     intros; 
     rewrite ttriag;
     rewrite ttriag0;
     auto.
  assert (H1 : (fun t => tcomp (type_mor1 t)) = type_mor0).
    apply functional_extensionality; auto.
  assert (H2 : (fun t => tcomp0 (type_mor0 t)) = type_mor).
    apply functional_extensionality; auto.

     
  generalize dependent rep_gen_Hom_monad_struct.
  generalize dependent rep_gen_Hom_monad_struct0.
  generalize dependent pcf_rep_struct.
  generalize dependent rep_Hom_monad0.
  generalize dependent pcf_rep_monad.
  generalize dependent rep_Hom_monad.
  generalize dependent pcf_rep_monad1.
  generalize dependent ttriag.
  generalize dependent pcf_rep_struct0.
  generalize dependent pcf_rep_monad0.
  generalize dependent ttriag0.
  rewrite <- H'.
  rewrite <- H1.
  
  intros;
  simpl.
  
  rewrite (UIP_refl _  _ (e _)).
  simpl.
  
  
  rewrite (UIP_refl _ _ (ttriag _ )) in HM.
  simpl in HM.
  rewrite (UIP_refl _ _ (ttriag0 _ )) in HN.
  simpl in HN.
  
  rewrite HM.
  rewrite HN.
  simpl.
  
  unfold lift.
  simpl.
  assert (H := mod_hom_mkl 
      (Module_Hom_struct :=
            (bottom t (PCF_rep_s := pcf_rep_struct)))).
  simpl in H.
  rewrite <- H.
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros t V y.
  simpl.
  assert (HM:= Rec_Hom (t:=t) (PCF_rep_Hom_struct := M)).
  simpl in HM.
  assert (HN:= Rec_Hom (t:=t) (PCF_rep_Hom_struct := N)).
  simpl in HN.
  generalize functy.
  destruct M.
  destruct N.
  simpl in *.
  clear M.
  clear N.
  destruct R.
  clear R.
  destruct Q.
  clear Q.
  destruct P.
  clear P.
  simpl in *.
  
  assert (H' : (fun t => tcomp0 (tcomp (type_mor1 t))) 
           = type_mor).
     apply functional_extensionality.
     intros; 
     rewrite ttriag;
     rewrite ttriag0;
     auto.
  assert (H1 : (fun t => tcomp (type_mor1 t)) = type_mor0).
    apply functional_extensionality; auto.
  assert (H2 : (fun t => tcomp0 (type_mor0 t)) = type_mor).
    apply functional_extensionality; auto.

     
  generalize dependent rep_gen_Hom_monad_struct.
  generalize dependent rep_gen_Hom_monad_struct0.
  generalize dependent pcf_rep_struct.
  generalize dependent rep_Hom_monad0.
  generalize dependent pcf_rep_monad.
  generalize dependent rep_Hom_monad.
  generalize dependent pcf_rep_monad1.
  generalize dependent ttriag.
  generalize dependent pcf_rep_struct0.
  generalize dependent pcf_rep_monad0.
  generalize dependent ttriag0.
  rewrite <- H'.
  rewrite <- H1.
  
  intros;
  simpl.

  rewrite (UIP_refl _  _ (e _)).
  rewrite (UIP_refl _ _ (e _ )).
  simpl.
    
  rewrite (UIP_refl _ _ (ttriag _ )) in HM.
  rewrite (UIP_refl _ _ (ttriag _ )) in HM.
  simpl in HM.
  rewrite (UIP_refl _ _ (ttriag0 _ )) in HN.
  rewrite (UIP_refl _ _ (ttriag0 _ )) in HN.  
  simpl in HN.
  
  rewrite HM.
  rewrite HN.
  simpl.
  
  unfold lift.
  simpl.
  assert (H := mod_hom_mkl 
      (Module_Hom_struct :=
            (rec t (PCF_rep_s := pcf_rep_struct)))).
  simpl in H.
  rewrite <- H.
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros r s V y.
  simpl in *.
  assert (HM:= App_Hom (PCF_rep_Hom_struct := M) 
                         (r:=r) (s:=s)).
  simpl in HM.
  assert (HN:= App_Hom (PCF_rep_Hom_struct := N) 
                            (r:=r) (s:=s)).
  simpl in HN.

  generalize functy.
  destruct M.
  destruct N.
  simpl in *.
  clear M.
  clear N.
  destruct R.
  clear R.
  destruct Q.
  clear Q.
  destruct P.
  clear P.
  simpl in *.
  
  assert (H' : (fun t => tcomp0 (tcomp (type_mor1 t))) 
           = type_mor).
     apply functional_extensionality.
     intros; 
     rewrite ttriag;
     rewrite ttriag0;
     auto.
  assert (H1 : (fun t => tcomp (type_mor1 t)) = type_mor0).
    apply functional_extensionality; auto.
  assert (H2 : (fun t => tcomp0 (type_mor0 t)) = type_mor).
    apply functional_extensionality; auto.

     
  generalize dependent rep_gen_Hom_monad_struct.
  generalize dependent rep_gen_Hom_monad_struct0.
  generalize dependent pcf_rep_struct.
  generalize dependent rep_Hom_monad0.
  generalize dependent pcf_rep_monad.
  generalize dependent rep_Hom_monad.
  generalize dependent pcf_rep_monad1.
  generalize dependent ttriag.
  generalize dependent pcf_rep_struct0.
  generalize dependent pcf_rep_monad0.
  generalize dependent ttriag0.
  rewrite <- H'.
  rewrite <- H1.
  
  intros;
  simpl.

  
  rewrite (UIP_refl _ _ (e s)).
  rewrite (UIP_refl _ _ (e r)).
  rewrite (UIP_refl _ _ (e (r ~> s))).
  simpl in *.
  
  rewrite (UIP_refl _ _ (ttriag s)) in HM.
  rewrite (UIP_refl _ _ (ttriag r)) in HM.
  rewrite (UIP_refl _ _ (ttriag (r ~> s))) in HM.
  simpl in HM.

  rewrite (UIP_refl _ _ (ttriag0 s)) in HN.
  rewrite (UIP_refl _ _ (ttriag0 r)) in HN.
  rewrite (UIP_refl _ _ (ttriag0 (r ~> s))) in HN.
  simpl in HN. 
  
  rewrite HM.
  rewrite HN.
  simpl.
  
  unfold lift.
  simpl.
  assert (H := mod_hom_mkl 
      (Module_Hom_struct :=
            (app (PCF_rep_s := pcf_rep_struct) r s))).
  simpl in H.
  rewrite <- H.
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros r s V y.
  assert (HM:= Abs_Hom (PCF_rep_Hom_struct := M) 
            (r:=r) (s:=s)).
  simpl in HM.
  assert (HN:= Abs_Hom (PCF_rep_Hom_struct := N) 
            (r:=r) (s:=s)).
  simpl in HN.

  generalize functy.
  destruct M.
  destruct N.
  simpl in *.
  clear M.
  clear N.
  destruct R.
  clear R.
  destruct Q.
  clear Q.
  destruct P.
  clear P.
  simpl in *.
  
  assert (H' : (fun t => tcomp0 (tcomp (type_mor1 t))) 
                 = type_mor).
     apply functional_extensionality.
     intros; 
     rewrite ttriag;
     rewrite ttriag0;
     auto.
  assert (H1 : (fun t => tcomp (type_mor1 t)) = type_mor0).
    apply functional_extensionality; auto.
  assert (H2 : (fun t => tcomp0 (type_mor0 t)) = type_mor).
    apply functional_extensionality; auto.

     
  generalize dependent rep_gen_Hom_monad_struct.
  generalize dependent rep_gen_Hom_monad_struct0.
  generalize dependent pcf_rep_struct.
  generalize dependent rep_Hom_monad0.
  generalize dependent pcf_rep_monad.
  generalize dependent rep_Hom_monad.
  generalize dependent pcf_rep_monad1.
  generalize dependent ttriag.
  generalize dependent pcf_rep_struct0.
  generalize dependent pcf_rep_monad0.
  generalize dependent ttriag0.
  rewrite <- H'.
  rewrite <- H1.
  
  intros;
  simpl.

  rewrite (UIP_refl _ _ (e s)).
  rewrite (UIP_refl _ _ (e r)).
  rewrite (UIP_refl _ _ (e (r ~> s))).
  simpl in *.
  
  rewrite (UIP_refl _ _ (ttriag s)) in HM.
  rewrite (UIP_refl _ _ (ttriag r)) in HM.
  rewrite (UIP_refl _ _ (ttriag (r ~> s))) in HM.
  simpl in HM.

  rewrite (UIP_refl _ _ (ttriag0 s)) in HN.
  rewrite (UIP_refl _ _ (ttriag0 r)) in HN.
  rewrite (UIP_refl _ _ (ttriag0 (r ~> s))) in HN.
  simpl in HN.  
  
  rewrite <- HM.
  rewrite <- HN.
  simpl.
  clear HM.
  clear HN.
  
  unfold lift.
  simpl.

    assert (H := mod_hom_mkl 
      (Module_Hom_struct :=
            (abs (PCF_rep_s := pcf_rep_struct) r s))).
      simpl in H.
      rewrite <- H.
  auto.
  apply f_equal.
  assert (H4:= klkl pcf_rep_monad).
  simpl in H4.
  
  rewrite H4.
  rewrite H4.
  simpl.
  
  rewrite (MonadHomKl rep_Hom_monad0).
  simpl.

  rewrite H4.
  simpl.
  apply (kl_eq pcf_rep_monad ).
  simpl.
  clear y.
  intros t y.
  assert (H6:= (etakl pcf_rep_monad)).
  simpl in H6.
  rewrite H6.
  simpl.
  clear H.
  clear rep_gen_Hom_monad_struct.
  clear rep_gen_Hom_monad_struct0.
  simpl.
  destruct y as [t y].
  simpl in *.
  rewrite (MonadHomWe rep_Hom_monad0).
  simpl.
  rewrite H6.
  simpl.
  rewrite H6.
  simpl.
  destruct y as [t y].
  simpl.
  destruct y as [t y | ];
  simpl; auto.
  assert (H:=lift_weta pcf_rep_monad).
  simpl in H.
  rewrite H.
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros V TT.
  elim TT.
  simpl.
  assert (HM:= Pred_Hom (PCF_rep_Hom_struct := M)).
  simpl in HM.
  assert (HN:= Pred_Hom (PCF_rep_Hom_struct := N)).
  simpl in HN.
  generalize functy.
  destruct M.
  destruct N.
  simpl in *.
  clear M.
  clear N.
  destruct R.
  clear R.
  destruct Q.
  clear Q.
  destruct P.
  clear P.
  simpl in *.
  
  assert (H' : (fun t => tcomp0 (tcomp (type_mor1 t))) 
           = type_mor).
     apply functional_extensionality.
     intros; 
     rewrite ttriag;
     rewrite ttriag0;
     auto.
  assert (H1 : (fun t => tcomp (type_mor1 t)) = type_mor0).
    apply functional_extensionality; auto.
  assert (H2 : (fun t => tcomp0 (type_mor0 t)) = type_mor).
    apply functional_extensionality; auto.

     
  generalize dependent rep_gen_Hom_monad_struct.
  generalize dependent rep_gen_Hom_monad_struct0.
  generalize dependent pcf_rep_struct.
  generalize dependent rep_Hom_monad0.
  generalize dependent pcf_rep_monad.
  generalize dependent rep_Hom_monad.
  generalize dependent pcf_rep_monad1.
  generalize dependent ttriag.
  generalize dependent pcf_rep_struct0.
  generalize dependent pcf_rep_monad0.
  generalize dependent ttriag0.
  rewrite <- H'.
  rewrite <- H1.
  
  intros;
  simpl.

  
  rewrite (UIP_refl _ _ (e _)).
  simpl.
  
  rewrite (UIP_refl _ _ (ttriag _ )) in HM.
  simpl in HM.
  rewrite (UIP_refl _ _ (ttriag0 _ )) in HN.
  simpl in HN.
  
  rewrite HM.
  rewrite HN.
  simpl.
  
  unfold lift.
  simpl.
  assert (H := mod_hom_mkl 
      (Module_Hom_struct :=
            (Pred (PCF_rep_s := pcf_rep_struct)))).
  simpl in H.
  rewrite <- H.
  auto.
Qed.

Definition Rep_comp := Build_PCF_rep_Hom Rep_comp_struct.

End comp_red.
