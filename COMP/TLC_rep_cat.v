Require Import Coq.Logic.Eqdep.
Require Import Coq.Logic.FunctionalExtensionality.

Require Export CatSem.COMP.TLC_rep_comp.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Automatic Introduction.


Obligation Tactic := idtac.

Program Instance REP_s : 
     Cat_struct (obj := TLC_rep) TLC_rep_Hom := {
  mor_oid P R := eq_Rep_oid P R ;
  id R := Rep_id R ;
  comp a b c f g := Rep_comp f g
}.
Next Obligation.
Proof.
  intros a b c.
  unfold Proper; do 2 red.
  intros M N H.
  induction H.
  simpl in *.
  intros S T H'.
  induction H'.
  simpl in *.
  
  assert (He : (forall t, tcomp (Rep_comp c0 c1) t = 
                          tcomp (Rep_comp a0 a1) t)).
    simpl.
    intro t.
    rewrite H;
    rewrite H1; auto.
  apply (eq_rep (H:=He)).
  
  destruct c1.
  destruct a1.
  destruct c0.
  destruct a0.
  
  simpl in *.
  intros V t y.
  assert (K1 : tcomp = tcomp0).
    apply functional_extensionality. auto.
  assert (K2 : tcomp1 = tcomp2).
    apply functional_extensionality. auto.

  generalize dependent He.
  subst.
  
  intro He.
  
  assert (Hl := lift_transp_id).
  assert (Hl':= Hl _ _ _ c He).
  assert (Hll := Hl' _ _ 
  (comp_rep_car (f:=tcomp2) (f':=tcomp0) 
          rep_Hom_monad2 rep_Hom_monad0 (c:=V)
     (t:=t) y)).
  simpl in *.
  rewrite Hll.
  simpl.
  
  assert (Hk := transp_id He).
  simpl in Hk.
  rewrite Hk.
  simpl.
  
  clear Hk Hll Hl' Hl.
  
  destruct y as [t y].
  simpl in *.
  apply f_equal.
  
  assert (H0spec := H0 _ _ (ctype _ y)).
  assert (H0r := lift_transp_id (Q:=b) H
               (rep_Hom_monad2 V (tcomp2 t)
        (ctype (fun t : type_type a => tcomp2 t) 
                (V:=a V) (t:=t) y))).
  simpl in *.
  
  rewrite H0r in H0spec. simpl in *.
  rewrite (UIP_refl _ _ (H t)) in H0spec.
  simpl in *.
  rewrite H0spec.
  simpl.
  
  clear H0r.
  clear H0spec.
  clear H0.
  
  assert (H2spec := H2 _ _ 
  ((ctype (fun t0 : type_type b => tcomp0 t0)
   (V:=b (retype (fun t0 : type_type a => tcomp2 t0) V)) 
          (t:=tcomp2 t)
     (rep_Hom_monad1 V (tcomp2 t)
        (ctype (fun t0 : type_type a => tcomp2 t0) 
   (V:=a V) (t:=t) y))))).
   simpl.
  
  assert (H2r := lift_transp_id (Q:=c) H1).
  simpl in H2r.
  rewrite H2r in H2spec.
  simpl in *.
  rewrite H2spec.
  
  apply f_equal.
  rewrite (UIP_refl _ _ (H1 (tcomp2 t))).
  simpl.
  auto.
Qed.
  
Next Obligation.
Proof.
  simpl.
  intros a b f.
  assert (H : forall t, tcomp f t = 
    tcomp (Rep_comp f (Rep_id b)) t)
    by (simpl; auto).
  
  apply (eq_rep (H:=H)); simpl.
  
  intros V t y.
  destruct y as [t y].
  simpl.
  
  destruct f.
  simpl in *.
  
  rewrite (UIP_refl _ _ (H t)).
  simpl.
  
  assert (HH:=lift_transp_id (Q:=b) H).
  simpl in *.
  rewrite HH.
  simpl.
  
  assert (Hl := lift_lift b).
  simpl in Hl.
  rewrite Hl.
  simpl.
  assert (He := lift_eq_id b).
  simpl in He.
  apply He.
  
  clear t y.
  intros t y.
  destruct y as [t y];
  simpl; auto.
Qed.
Next Obligation.
  simpl.
  intros a b f.
  assert (H : forall t, tcomp f t = 
    tcomp (Rep_comp (Rep_id a) f) t)
    by (simpl; auto).
  
  apply (eq_rep (H:=H)); simpl.
  
  intros V t y.
  destruct y as [t y].
  simpl.
  
  destruct f.
  simpl in *.
  rewrite (UIP_refl _ _ (H t)).
  simpl.
  
  assert (HH:=lift_transp_id (Q:=b) H).
  simpl in *.
  rewrite HH.
  simpl.
  
  rewrite <- (MonadHomLift rep_Hom_monad).
    
  assert (Hl := lift_lift b).
  simpl in Hl.
  rewrite Hl.
  simpl.
  assert (He := lift_eq_id b).
  simpl in He.
  apply He.
  
  clear t y.
  intros t y.
  destruct y as [t y];
  simpl; auto.
Qed.
Next Obligation.
Proof.
  intros a b c c' f g h.
  assert (H : forall t, 
    tcomp (Rep_comp f (Rep_comp g h)) t =
    tcomp (Rep_comp (Rep_comp f g) h) t) by
          (simpl; auto).
  apply (eq_rep (H:=H)).
  simpl.
  intros V t y.
  destruct h.
  destruct g.
  destruct f.
  simpl in *.
  
  assert (Hl:=lift_transp_id (Q:=c') H).
  simpl in Hl.
  rewrite Hl.
  
  assert (Ht := transp_id H).
  simpl in Ht.
  rewrite Ht.
  
  destruct y as [t y].
  simpl in *.
  
  assert (Hc' := lift_lift c').
  simpl in Hc'.
  rewrite Hc'.
  
  rewrite <- (MonadHomLift rep_Hom_monad).
  rewrite Hc'.

  apply (lift_eq c').
  simpl.
  
  clear t y.
  intros t y.
  destruct y as [t y].
  simpl.
  destruct y as [t y].
  simpl.
  destruct y as [t y].
  simpl;
  auto.
Qed.

Canonical Structure REP : Cat := Build_Cat REP_s.


















