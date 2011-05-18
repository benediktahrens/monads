Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Eqdep.

Require Export CatSem.PCF_o_c.RPCF_rep_cat.
Require Export CatSem.PCF_o_c.RPCF_syntax_init.

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
  destruct g as [f Hfarrow Hfcomm T Ts]; 
  simpl in *.
  clear g.
  
  assert (H' : type_mor R = f) by
     (apply functional_extensionality;
         intros; auto).
  generalize (H t).
  generalize H.
  generalize dependent T.
  clear H. 
  generalize dependent Hfarrow.
  generalize dependent Hfcomm.
  rewrite <- H'.
  intros.
  rewrite (UIP_refl _ _ e).
  simpl.
  
  assert (Hl := rlift_transp_id (Q:=R) H).
  simpl in *.
  rewrite Hl.
  clear Hl.
  clear e H.
  
  induction y.
  simpl.
  
  assert (Hb:=bottom_hom (PCFPO_rep_Hom_struct := Ts) 
            t (c:=V) tt).
  simpl in *.
  auto.
  
  destruct c.
    
    assert (Hb:=nats_hom n (PCFPO_rep_Hom_struct := 
            Ts)  (c:=V) tt).
    simpl in *.
    rewrite (UIP_refl _ _ (Hfcomm _)) in Hb.
    simpl in * ; auto.
    
    assert (Hb:=ttt_hom (PCFPO_rep_Hom_struct := 
            Ts)  (c:=V) tt).
    simpl in *.
    rewrite (UIP_refl _ _ (Hfcomm _)) in Hb.
    simpl in * ; auto.
    
    assert (Hb:=fff_hom (PCFPO_rep_Hom_struct := 
            Ts)  (c:=V) tt).
    simpl in *.
    rewrite (UIP_refl _ _ (Hfcomm _)) in Hb.
    simpl in * ; auto.
    
    assert (Hb:=Succ_hom (PCFPO_rep_Hom_struct := 
            Ts) (c:=V) tt).
    simpl in *.
    rewrite <- Hb.
    clear Hb.
    symmetry.
    apply double_eq_rect.
        
    assert (Hb:=Pred_hom (PCFPO_rep_Hom_struct := 
            Ts)  (c:=V) tt).
    simpl in *.
    rewrite <- Hb.
    symmetry.
    apply double_eq_rect.

    assert (Hb:=Zero_hom (PCFPO_rep_Hom_struct := 
            Ts)  (c:=V) tt).
    simpl in *.
    rewrite <- Hb.
    clear Hb.
    symmetry.
    apply double_eq_rect.
    
    assert (Hb:=CondN_hom (PCFPO_rep_Hom_struct := 
            Ts)  (c:=V) tt).
    simpl in *.
    rewrite <- Hb.
    clear Hb.
    symmetry.
    apply double_eq_rect.
    
    assert (Hb:=CondB_hom (PCFPO_rep_Hom_struct := 
            Ts)  (c:=V) tt).
    simpl in *.
    rewrite <- Hb.
    clear Hb.
    symmetry.
    apply double_eq_rect.

  (*1*)
  assert (Hw:=gen_rmonad_hom_rweta 
     ((*gen_RMonad_Hom_struct := *)T)).
     simpl in Hw.
  assert (Hw' := Hw _ _ (ctype _ v)).
  simpl in Hw'.
  auto.
  (*2*)
  simpl.
  rewrite <- IHy1.
  rewrite <- IHy2.
  assert (Happ:=app_hom (PCFPO_rep_Hom_struct := 
            Ts) (u:=s) (v:=t) (y1,y2)).
  simpl in *.
  rewrite <- Happ.
  clear Happ.
  apply f_equal.
  simpl.
  apply injective_projections;
  simpl;
  auto.
  rewrite (UIP _ _ _ 
    (type_arrow_dist R s t)(Hfarrow s t)).
  auto.

  (*3*)
  simpl.
  rewrite <- IHy.
  clear IHy.
  assert (Habs:=abs_hom2 (PCFPO_rep_Hom_struct := 
            Ts) (u:=t) (v:=s)  y ).
  simpl in *.
  rewrite Habs.
  rewrite (UIP _ _ _ (eq_sym (Hfarrow t s))
                     (eq_sym (type_arrow_dist R t s))).
  reflexivity.                     
  
  simpl.
  rewrite <- IHy.
  assert (Happ:=rec_hom (PCFPO_rep_Hom_struct := 
            Ts) (t:=t) y).
  simpl in *.
  rewrite Happ.
  rewrite (UIP _ _ _ (Hfarrow t t)
                     (type_arrow_dist R t t)).
  reflexivity.
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
