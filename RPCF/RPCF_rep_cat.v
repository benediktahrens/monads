Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Eqdep.

Require Export CatSem.RPCF.RPCF_rep_comp.
Require Export CatSem.RPCF.RPCF_rep_id.
Require Export CatSem.RPCF.RPCF_rep_eq.

Set Implicit Arguments.
Unset Strict Implicit.
Set Transparent Obligations.
Unset Automatic Introduction.


Obligation Tactic := idtac.

Program Instance REP_s : 
     Cat_struct (obj := PCFPO_rep) (PCFPO_rep_Hom) := {
  mor_oid P R := eq_Rep_oid P R ;
  id R := PCFPO_id R ;
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
  
  assert (He : (forall t, Sorts_map (Rep_comp c0 c1) t = 
                          Sorts_map (Rep_comp a0 a1) t)).
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
  assert (K1 : Sorts_map = Sorts_map0).
    apply functional_extensionality. auto.
  assert (K2 : Sorts_map1 = Sorts_map2).
    apply functional_extensionality. auto.

  generalize dependent He.
  subst.
  
  intro He.
  
  assert (Hl := rlift_transp_id).
  assert (Hl':= Hl _ _ _ c He). 
  assert (Hll := Hl' _ _ 
  (RMon_car (f:=Sorts_map2) (f':=Sorts_map0) 
          rep_Hom_monad2 rep_Hom_monad0 V t y)). 
  
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
  assert (H0r := rlift_transp_id (Q:=b) H
               (rep_Hom_monad2 V (Sorts_map2 t)
        (ctype (fun t : Sorts a => Sorts_map2 t) 
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
  ((ctype (fun t0 : Sorts b => Sorts_map0 t0)
   (V:=b (retype (fun t0 : Sorts a => Sorts_map2 t0) V)) 
          (t:=Sorts_map2 t)
     (rep_Hom_monad1 V (Sorts_map2 t)
        (ctype (fun t0 : Sorts a => Sorts_map2 t0) 
   (V:=a V) (t:=t) y))))).
   simpl.
  
  assert (H2r := rlift_transp_id (Q:=c) H1).
  simpl in H2r.
  rewrite H2r in H2spec.
  simpl in *.
  rewrite H2spec.
  
  apply f_equal.
  rewrite (UIP_refl _ _ (H1 (Sorts_map2 t))).
  simpl.
  auto.
Qed.
  
Next Obligation.
Proof.
  simpl.
  intros a b f.
  assert (H : forall t, Sorts_map f t = 
    Sorts_map (Rep_comp f (PCFPO_id b)) t)
    by (simpl; auto).
  
  apply (eq_rep (H:=H)); simpl.
  
  intros V t y.
  destruct y as [t y].
  simpl.
  
  destruct f.
  simpl in *.
  
  rewrite (UIP_refl _ _ (H t)).
  simpl.
  
  assert (HH:=rlift_transp_id (Q:=b) H).
  simpl in *.
  rewrite HH.
  simpl.
  
  assert (Hl := rlift_rlift b).
  simpl in Hl.
  rewrite Hl.
  simpl.
  assert (He := rlift_eq_id b).
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
  assert (H : forall t, Sorts_map f t = 
    Sorts_map (Rep_comp (PCFPO_id a) f) t)
    by (simpl; auto).
  
  apply (eq_rep (H:=H)); simpl.
  
  intros V t y.
  destruct y as [t y].
  simpl.
  
  destruct f.
  simpl in *.
  
  rewrite (UIP_refl _ _ (H t)).
  simpl.
  
  assert (HH:=rlift_transp_id (Q:=b) H).
  simpl in *.
  rewrite HH.
  simpl.
  
  assert (H3:=gen_rh_rlift rep_Hom_monad).
  simpl in *.
  assert (H4 :=H3 _ _ (id_retype(V:=V))).
  simpl in H4.
  rewrite <- H4.
  clear H4.
    
  assert (Hl := rlift_rlift b).
  simpl in Hl.
  rewrite Hl.
  simpl.
  assert (He := rlift_eq_id b).
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
    Sorts_map (Rep_comp f (Rep_comp g h)) t =
    Sorts_map (Rep_comp (Rep_comp f g) h) t) by
          (simpl; auto).
  apply (eq_rep (H:=H)).
  simpl.
  intros V t y.
  destruct h.
  destruct g.
  destruct f.
  simpl in *.
  
  assert (Hl:=rlift_transp_id (Q:=c') H).
  simpl in Hl.
  rewrite Hl.
  
  assert (Ht := transp_id H).
  simpl in Ht.
  rewrite Ht.
  
  destruct y as [t y].
  simpl in *.
  
  assert (Hc' := rlift_rlift c').
  simpl in Hc'.
  rewrite Hc'.
  
  assert (H3:=gen_rh_rlift rep_Hom_monad).
  rewrite <- (H3 _ _ (double_retype_1 (f:=Sorts_map1) 
                             (f':=Sorts_map0)(V:= V))).

  rewrite Hc'.

  apply (rlift_eq c').
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

Print Assumptions REP_s.

Canonical Structure REP : Cat := Build_Cat REP_s.

