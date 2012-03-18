(*Require Import Coq.Logic.FunctionalExtensionality.*)
Require Import Coq.Logic.Eqdep.

Require Import CatSem.AXIOMS.functional_extensionality.

Require Export CatSem.RPCF.RPCF_rep_cat.
Require Export CatSem.RPCF.RPCF_syntax_init.

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
  assert (H : forall t, Sorts_map (initR R) t = Sorts_map g t).
  simpl. 
  induction t; simpl;   
  destruct g; simpl in *;
  try rerew_all; auto.
  repeat rew_all; auto.
  apply (eq_rep (H:=H)).
   
  intros V t y.
  destruct y as [t y];
  simpl in *. 
(*  generalize (H t). *)
  assert (H' : Init_Sorts_map R = Sorts_map g).
   apply functional_extensionality; intros.
   destruct g.
   rew_all. auto.
  destruct g as [f garrow gnat gbool gM gMs];
  simpl in *.
  generalize (H t).
  generalize H.
  generalize dependent gM.
  clear H.
  generalize dependent gnat.
  generalize dependent gbool.
  generalize dependent garrow.
  rewrite <- H'.
  intros; simpl.
  rewrite (UIP_refl _ _ _ ).
  simpl.
  clear g.
  assert (Hl := rlift_transp_id (Q:=R) H).
  simpl in *.
  rewrite Hl.
  clear Hl.
  clear e H.
    induction y;
  simpl.

  assert (Hb:=bottom_hom (PCFPO_rep_Hom_struct := gMs) 
            t (c:=V) tt).
  simpl in *.
  auto.
  
  destruct c.
    
    assert (Hb:=nats_hom n (PCFPO_rep_Hom_struct := 
            gMs)  (c:=V) tt).
    simpl in *.
    rewrite (UIP_refl _ _ _) in Hb.
    simpl in * ; auto.
    
    assert (Hb:=ttt_hom (PCFPO_rep_Hom_struct := 
            gMs)  (c:=V) tt).
    simpl in *.
    rewrite (UIP_refl _ _ _) in Hb.
    simpl in * ; auto.
    
    assert (Hb:=fff_hom (PCFPO_rep_Hom_struct := 
            gMs)  (c:=V) tt).
    simpl in *.
    rewrite (UIP_refl _ _ _) in Hb.
    simpl in * ; auto.
    
    assert (Hb:=Succ_hom (PCFPO_rep_Hom_struct := 
            gMs) (c:=V) tt).
    simpl in *.
    rewrite (UIP_refl _ _ _ ) in Hb.
    simpl in Hb.
    auto.
        
    assert (Hb:=Pred_hom (PCFPO_rep_Hom_struct := 
            gMs)  (c:=V) tt).
    simpl in *.
    rewrite (UIP_refl _ _ _ ) in Hb.
    simpl in Hb.
    auto.

    assert (Hb:=Zero_hom (PCFPO_rep_Hom_struct := 
            gMs)  (c:=V) tt).
    simpl in *.
    rewrite (UIP_refl _ _ _ ) in Hb.
    simpl in Hb.
    auto.

    assert (Hb:=CondN_hom (PCFPO_rep_Hom_struct := 
            gMs)  (c:=V) tt).
    simpl in *.
    rewrite (UIP_refl _ _ _ ) in Hb.
    simpl in Hb.
    auto.
    
    assert (Hb:=CondB_hom (PCFPO_rep_Hom_struct := 
            gMs)  (c:=V) tt).
    simpl in *.
    rewrite (UIP_refl _ _ _ ) in Hb.
    simpl in Hb.
    auto.
    
     (*1*)
  assert (Hw:=gen_rmonad_hom_rweta 
     ((*gen_RMonad_Hom_struct := *)gM)).
     simpl in Hw.
  assert (Hw' := Hw _ _ (ctype _ v)).
  simpl in Hw'.
  auto.
  (*2*)
  simpl.
  rewrite <- IHy1.
  rewrite <- IHy2.
  assert (Happ:=app_hom (PCFPO_rep_Hom_struct := 
            gMs) (u:=s) (v:=t) (y1,y2)).
  simpl in *.
  rewrite <- Happ.
  clear Happ.
  apply f_equal.
  simpl.
  apply injective_projections;
  simpl;
  auto.
  rewrite (UIP_refl _ _ (garrow s t)).
  auto.

  (*3*)
  simpl.
  rewrite <- IHy.
  clear IHy.
  assert (Habs:=abs_hom (PCFPO_rep_Hom_struct := 
            gMs) (u:=t) (v:=s)  y ).
  simpl in *.
  rewrite Habs.
  rewrite (UIP_refl _ _ _ ).
  reflexivity.                     
  
  simpl.
  rewrite <- IHy.
  assert (Happ:=rec_hom (PCFPO_rep_Hom_struct := 
            gMs) (t:=t) y).
  simpl in *.
  rewrite Happ.
  rewrite (UIP_refl _ _ _ ).
  reflexivity.
Qed.

End unique.

Hint Resolve initR_unique : fin.

Program Instance PCF_initial : Initial REP := {
  Init := PCFE_rep ;
  InitMor R := initR R ;
  InitMorUnique R := @initR_unique R
}.

(* Print Assumptions PCF_initial. *)
