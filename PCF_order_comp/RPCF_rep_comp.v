Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Eqdep.

Require Export CatSem.PCF_order_comp.RPCF_rep_hom.
Require Export CatSem.CAT.rmonad_gen_comp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Section rep_comp.

Variables P Q R : PCFPO_rep.
Variable M : PCFPO_rep_Hom P Q.
Variable N : PCFPO_rep_Hom Q R.

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
  PCFPO_rep_Hom_struct (P:=P) (R:=R)(f := fun t => tcomp N (tcomp M t)) 
      functy (RMon_comp M N).
Next Obligation.
Proof.
  simpl.
  intros V TT.
  elim TT.
  simpl.
  assert (HM:= CondB_hom (PCFPO_rep_Hom_struct := M)).
  simpl in HM.
  assert (HN:= CondB_hom (PCFPO_rep_Hom_struct := N)).
  simpl in HN.
(*  unfold eq_type_c in *.*)
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
  
  unfold rlift.
  simpl. 
  rerew (rmod_hom_rmkl (CondB (PCFPO_rep_struct := pcf_rep_struct))).
Qed.
Next Obligation.
Proof.
  simpl.
  intros V TT.
  elim TT.
  simpl.
  assert (HM:= CondN_hom (PCFPO_rep_Hom_struct := M)).
  simpl in HM.
  assert (HN:= CondN_hom (PCFPO_rep_Hom_struct := N)).
  simpl in HN.
(*  unfold eq_type_c in *.*)
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
  
  unfold rlift.
  simpl. 
  rerew (rmod_hom_rmkl (CondN (PCFPO_rep_struct := pcf_rep_struct))).
Qed.
Next Obligation.
Proof.
  simpl.
  intros V TT.
  elim TT.
  simpl.
  assert (HM:= Pred_hom (PCFPO_rep_Hom_struct := M)).
  simpl in HM.
  assert (HN:= Pred_hom (PCFPO_rep_Hom_struct := N)).
  simpl in HN.
(*  unfold eq_type_c in *.*)
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
  
  unfold rlift.
  simpl. 
  rerew (rmod_hom_rmkl (Pred (PCFPO_rep_struct := pcf_rep_struct))).
Qed.
Next Obligation.
Proof.
  simpl.
  intros V TT.
  elim TT.
  simpl.
  assert (HM:= Zero_hom (PCFPO_rep_Hom_struct := M)).
  simpl in HM.
  assert (HN:= Zero_hom (PCFPO_rep_Hom_struct := N)).
  simpl in HN.
(*  unfold eq_type_c in *.*)
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
  
  unfold rlift.
  simpl. 
  rerew (rmod_hom_rmkl (Zero (PCFPO_rep_struct := pcf_rep_struct))).
Qed.
Next Obligation.
Proof.
  simpl.
  intros V TT.
  elim TT.
  simpl.
  assert (HM:= Succ_hom (PCFPO_rep_Hom_struct := M)).
  simpl in HM.
  assert (HN:= Succ_hom (PCFPO_rep_Hom_struct := N)).
  simpl in HN.
(*  unfold eq_type_c in *.*)
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
  
  unfold rlift.
  simpl. 
  rerew (rmod_hom_rmkl (Succ (PCFPO_rep_struct := pcf_rep_struct))).
Qed.
Next Obligation.
Proof.
  simpl.
  intros V TT.
  elim TT.
  simpl.
  assert (HM:= fff_hom (PCFPO_rep_Hom_struct := M)).
  simpl in HM.
  assert (HN:= fff_hom (PCFPO_rep_Hom_struct := N)).
  simpl in HN.
(*  unfold eq_type_c in *.*)
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
  
  unfold rlift.
  simpl. 
  rerew (rmod_hom_rmkl (ffff (PCFPO_rep_struct := pcf_rep_struct))).
Qed.
Next Obligation.
Proof.
  simpl.
  intros V TT.
  elim TT.
  simpl.
  assert (HM:= ttt_hom (PCFPO_rep_Hom_struct := M)).
  simpl in HM.
  assert (HN:= ttt_hom (PCFPO_rep_Hom_struct := N)).
  simpl in HN.
(*  unfold eq_type_c in *.*)
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
  
  unfold rlift.
  simpl. 
  rerew (rmod_hom_rmkl (tttt (PCFPO_rep_struct := pcf_rep_struct))).
Qed.
Next Obligation.
Proof.
  simpl.
  intros t V TT.
  elim TT.
  simpl.
  assert (HM:= bottom_hom t (PCFPO_rep_Hom_struct := M)).
  simpl in HM.
  assert (HN:= bottom_hom t (PCFPO_rep_Hom_struct := N)).
  simpl in HN.
(*  unfold eq_type_c in *.*)
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
  
  unfold rlift.
  simpl. 
  rerew (rmod_hom_rmkl (bottom t (PCFPO_rep_struct := pcf_rep_struct))).
Qed.
Next Obligation.
Proof.
  simpl.
  intros m V TT.
  elim TT.
  simpl.
  assert (HM:= nats_hom m (PCFPO_rep_Hom_struct := M)).
  simpl in HM.
  assert (HN:= nats_hom m (PCFPO_rep_Hom_struct := N)).
  simpl in HN.
(*  unfold eq_type_c in *.*)
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
  
  unfold rlift.
  simpl. 
  rerew (rmod_hom_rmkl (nats m (PCFPO_rep_struct := pcf_rep_struct))).
Qed.
Next Obligation.
Proof.
  simpl.
  intros r s V y.
  assert (HM:= app_hom (PCFPO_rep_Hom_struct := M) 
                         (r:=r) (s:=s)).
  simpl in HM.
  assert (HN:= app_hom (PCFPO_rep_Hom_struct := N) 
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
  
  unfold rlift.
  simpl.
  rerew (rmod_hom_rmkl (app r s 
              (PCFPO_rep_struct := pcf_rep_struct))).
Qed.
Next Obligation.
Proof.
  simpl.
  intros r s V y.
  assert (HM:= abs_hom (PCFPO_rep_Hom_struct := M) 
            (r:=r) (s:=s)).
  simpl in HM.
  assert (HN:= abs_hom (PCFPO_rep_Hom_struct := N) 
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
  
  clear e.
  rewrite HM.
  rewrite HN.
  clear HM HN.
  simpl.
  unfold rlift. 
  simpl.
  rerew (rmhom_rmkl (abs r s (PCFPO_rep_struct := pcf_rep_struct))).
  
  apply f_equal.
  assert (H4:=rklkl pcf_rep_monad).
  simpl in H4.
  rewrite H4.
  rewrite H4.
  simpl.

  rew (gen_rh_rkl rep_Hom_monad0).
  rewrite H4.

  apply (rkl_eq pcf_rep_monad).

  simpl.
  clear y.
  intros t y.
  rew (retakl pcf_rep_monad).

  destruct y as [t y].
  simpl in *.
  rew (gen_rh_rweta rep_Hom_monad0).
  rew (retakl pcf_rep_monad).
  rew (retakl pcf_rep_monad).
  destruct y as [t y];
  simpl.
  destruct y as [t y | ];
  simpl; auto.
  rew (rlift_rweta pcf_rep_monad).
Qed.
Next Obligation.
Proof.
  simpl.
  intros t V y.
  assert (HM:= rec_hom (t:=t) (PCFPO_rep_Hom_struct := M)).
  simpl in HM.
  assert (HN:= rec_hom  (t:=t)(PCFPO_rep_Hom_struct := N)).
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
  rewrite (UIP_refl _ _ (e _ )).
  
  rewrite (UIP_refl _ _ (ttriag _)) in HM.
  rewrite (UIP_refl _ _ (ttriag _)) in HM.
  simpl in HM.

  rewrite (UIP_refl _ _ (ttriag0 _)) in HN.
  rewrite (UIP_refl _ _ (ttriag0 _)) in HN.
  simpl in HN. 
  
  rewrite HM.
  rewrite HN.
  simpl.
  
  unfold rlift.
  simpl.
  rerew (rmod_hom_rmkl (rec t 
              (PCFPO_rep_struct := pcf_rep_struct))).
Qed.

Definition Rep_comp :
  PCFPO_rep_Hom P R := Build_PCFPO_rep_Hom Rep_comp_struct.

End rep_comp.




















