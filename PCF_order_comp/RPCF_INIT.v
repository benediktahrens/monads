Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Eqdep.

Require Export CatSem.PCF_order_comp.RPCF_rep_cat.
Require Export CatSem.PCF_order_comp.RPCF_syntax_init.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.


Section unique.

Variable R : REP.

Variable g : PCFE_rep ---> R.

Lemma initR_unique : g == initR R.
Proof.
  simpl.
  assert (H : forall t, tcomp (initR R) t = tcomp g t).
  assert (H':= ttriag g).
  simpl in *.
  auto.
  apply (eq_rep (H:=H)).
  simpl.
  intros V t y.
  destruct y as [t y].
  simpl.
  
  destruct g.
  simpl in *.
  
  assert (H' : type_mor R = tcomp) by
     (apply functional_extensionality;
         intros; auto).
  
  generalize dependent rep_Hom_monad.
  generalize dependent ttriag.
  generalize dependent H.
  
  rewrite <- H'.
  
  simpl.
  intros.
  
  assert (Hl := rlift_transp_id (Q:=R) H).
  simpl in *.
  rewrite Hl.
  rewrite (UIP_refl _ _ (H t)).
  simpl.
  
  induction y;
  simpl.
  
  assert (Hb:=bottom_hom (PCFPO_rep_Hom_struct := 
            rep_gen_Hom_monad_struct) t (c:=V) tt).
  simpl in *.

  rewrite (UIP_refl _ _ (ttriag _)) in Hb.
  simpl in *.
  auto.
  
  destruct c.
    
    assert (Hb:=nats_hom n (PCFPO_rep_Hom_struct := 
            rep_gen_Hom_monad_struct)  (c:=V) tt).
    simpl in *.

    rewrite (UIP_refl _ _ (ttriag _)) in Hb.
    simpl in * ; auto.
    
    assert (Hb:=ttt_hom (PCFPO_rep_Hom_struct := 
            rep_gen_Hom_monad_struct)  (c:=V) tt).
    simpl in *.

    rewrite (UIP_refl _ _ (ttriag _)) in Hb.
    simpl in * ; auto.
    
    assert (Hb:=fff_hom (PCFPO_rep_Hom_struct := 
            rep_gen_Hom_monad_struct)  (c:=V) tt).
    simpl in *.

    rewrite (UIP_refl _ _ (ttriag _)) in Hb.
    simpl in * ; auto.
    
    assert (Hb:=Succ_hom (PCFPO_rep_Hom_struct := 
            rep_gen_Hom_monad_struct) (c:=V) tt).
    simpl in *.

    rewrite (UIP_refl _ _ (ttriag _)) in Hb.
    simpl in * ; auto.
        
    assert (Hb:=Pred_hom (PCFPO_rep_Hom_struct := 
            rep_gen_Hom_monad_struct)  (c:=V) tt).
    simpl in *.

    rewrite (UIP_refl _ _ (ttriag _)) in Hb.
    simpl in * ; auto.

    assert (Hb:=Zero_hom (PCFPO_rep_Hom_struct := 
            rep_gen_Hom_monad_struct)  (c:=V) tt).
    simpl in *.

    rewrite (UIP_refl _ _ (ttriag _)) in Hb.
    simpl in * ; auto.
    
    assert (Hb:=CondN_hom (PCFPO_rep_Hom_struct := 
            rep_gen_Hom_monad_struct)  (c:=V) tt).
    simpl in *.

    rewrite (UIP_refl _ _ (ttriag _)) in Hb.
    simpl in * ; auto.
    
    assert (Hb:=CondB_hom (PCFPO_rep_Hom_struct := 
            rep_gen_Hom_monad_struct)  (c:=V) tt).
    simpl in *.

    rewrite (UIP_refl _ _ (ttriag _)) in Hb.
    simpl in * ; auto.

  
  (*1*)
  assert (Hw:=gen_rmonad_hom_rweta 
     ((*gen_RMonad_Hom_struct := *)rep_Hom_monad)).
     simpl in Hw.
  assert (Hw' := Hw _ _ (ctype _ v)).
  simpl in Hw'.
  auto.
  
  rewrite <- IHy1.
  rewrite <- IHy2.
  assert (Happ:=app_hom (PCFPO_rep_Hom_struct := 
            rep_gen_Hom_monad_struct) (r:=s) (s:=t) (y1,y2)).
  simpl in *.

  rewrite (UIP_refl _ _ (ttriag s)) in Happ.
  rewrite (UIP_refl _ _ (ttriag t)) in Happ.
  rewrite (UIP_refl _ _ (ttriag (s ~> t))) in Happ.
  simpl in *.
  simpl in *.
  auto.
  (*2*)
  rewrite <- IHy.
  assert (Habs:=abs_hom (PCFPO_rep_Hom_struct := 
            rep_gen_Hom_monad_struct) (r:=t) (s:=s)  y ).
  simpl in *.

  rewrite (UIP_refl _ _ (ttriag s)) in Habs.
  rewrite (UIP_refl _ _ (ttriag t)) in Habs.
  rewrite (UIP_refl _ _ (ttriag _)) in Habs.
  simpl in *.
  auto.
    
  rewrite <- IHy.
  assert (Happ:=rec_hom (PCFPO_rep_Hom_struct := 
            rep_gen_Hom_monad_struct) (t:=t) y).
  simpl in *.

  rewrite (UIP_refl _ _ (ttriag t)) in Happ.
  rewrite (UIP_refl _ _ (ttriag (t ~> t))) in Happ.
  simpl in *.
  auto.
Qed.

End unique.

Hint Resolve initR_unique : fin.

Obligation Tactic := fin.

Program Instance PCF_initial : Initial REP := {
  Init := PCFE_rep ;
  InitMor R := initR R ;
  InitMorUnique R := @initR_unique R
}.

Print Assumptions PCF_initial.
