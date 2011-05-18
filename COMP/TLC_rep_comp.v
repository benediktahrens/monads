Require Import Coq.Logic.Eqdep.
Require Import Coq.Logic.FunctionalExtensionality.

Require Export CatSem.COMP.TLC_rep.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Notation "'TY'" := TLCtypes.
Notation "'IT'" := (ITYPE TY).
Notation "a '~>' b" := (TLCarrow a b) 
     (at level 69, right associativity).
Notation "a 'x' b" := (product a b) (at level 30).
Notation "P [ z ]" := (ITFIB_MOD _ z P) (at level 35).
Notation "'d' P // s" := (ITDER_MOD _ _ s P) (at level 25).
Notation "f 'X' g" := (product_mor _ f g)(at level 30).

(** the base types *)
Variable B : Type.

Section comp_rep.

Variables P Q R : TLC_rep.
Variable M : TLC_rep_Hom P Q.
Variable N : TLC_rep_Hom Q R.

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
  TLC_rep_Hom_struct (f := fun t => tcomp N (tcomp M t)) 
      functy (comp_Rep_monad M N). 
Next Obligation.
Proof.
  simpl.
  intros r s V y.
  simpl in *.
  assert (HM:= App_Hom (TLC_rep_Hom_struct := M) 
                         (r:=r) (s:=s)).
  simpl in HM.
  assert (HN:= App_Hom (TLC_rep_Hom_struct := N) 
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
  generalize dependent tlc_rep_struct.
  generalize dependent rep_Hom_monad0.
  generalize dependent tlc_rep_monad.
  generalize dependent rep_Hom_monad.
  generalize dependent tlc_rep_monad1.
  generalize dependent ttriag.
  generalize dependent tlc_rep_struct0.
  generalize dependent tlc_rep_monad0.
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
            (App (TLC_rep_s := tlc_rep_struct) r s))).
  simpl in H.
  rewrite <- H.
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros r s V y.
  assert (HM:= Abs_Hom (TLC_rep_Hom_struct := M) 
            (r:=r) (s:=s)).
  simpl in HM.
  assert (HN:= Abs_Hom (TLC_rep_Hom_struct := N) 
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
  generalize dependent tlc_rep_struct.
  generalize dependent rep_Hom_monad0.
  generalize dependent tlc_rep_monad.
  generalize dependent rep_Hom_monad.
  generalize dependent tlc_rep_monad1.
  generalize dependent ttriag.
  generalize dependent tlc_rep_struct0.
  generalize dependent tlc_rep_monad0.
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
            (Abs (TLC_rep_s := tlc_rep_struct) r s))).
      simpl in H.
      rewrite <- H.
  auto.
  apply f_equal.
  assert (H4:=dist (Monad_struct := tlc_rep_monad)).
  simpl in H4.
  
  rewrite H4.
  rewrite H4.
  simpl.
  
  rewrite (MonadHomKl rep_Hom_monad0).
  simpl.

  rewrite H4.
  simpl.
  apply (kl_eq tlc_rep_monad ).
  simpl.
  clear y.
  intros t y.
  assert (H6:= (etakl tlc_rep_monad)).
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
  assert (H:=lift_weta tlc_rep_monad).
  simpl in H.
  rewrite H.
  auto.
Qed.

Definition Rep_comp := Build_TLC_rep_Hom Rep_comp_struct.

End comp_rep.
