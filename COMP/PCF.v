Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Eqdep.

Require Export CatSem.COMP.PCF_rep_cat.
Require Export CatSem.PCF.PCF_Monad.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.
(*
Program Instance app_hom_s r s : 
Module_Hom_struct
  (S:=Prod_Mod (P:=PCFM) TYPE_prod (ITFibre_Mod (P:=PCFM) PCFM (r ~> s))
     (ITFibre_Mod (P:=PCFM) PCFM r)) 
  (T:=ITFibre_Mod (P:=PCFM) PCFM s)
  (fun V y => App (fst y) (snd y)).


Canonical Structure PCFapp r s := Build_Module_Hom
    (app_hom_s r s).

Obligation Tactic := fin.

Program Instance abs_hom_s r s : 
Module_Hom_struct
  (S:=ITFibre_Mod (P:=PCFM) (IT_Der_Mod (P:=PCFM) 
      (D:=ITYPE TY) PCFM r) s)
  (T:=ITFibre_Mod (P:=PCFM) PCFM (r ~> s))
  (fun V y => Lam y).

Canonical Structure PCFabs r s := Build_Module_Hom (abs_hom_s r s).

Program Instance rec_hom_s t : Module_Hom_struct
  (S:= PCFM [t ~> t]) (T:= PCFM [t])
  (fun V y => Rec y).

Canonical Structure PCFrec t := Build_Module_Hom (rec_hom_s t).

Program Instance ttt_hom_s : Module_Hom_struct 
  (S:=Term (C:=MOD PCFM TYPE)) (T:= PCFM [Bool])
  (fun V t => Const V ttt).

Canonical Structure PCFttt := Build_Module_Hom ttt_hom_s.

Program Instance fff_hom_s : Module_Hom_struct 
  (S:=Term (C:=MOD PCFM TYPE)) (T:= PCFM [Bool])
  (fun V t => Const V fff).

Canonical Structure PCFfff := Build_Module_Hom fff_hom_s.

Program Instance succ_hom_s : Module_Hom_struct 
  (S:=Term (C:=MOD PCFM TYPE)) (T:= PCFM [Nat ~> Nat])
  (fun V t => Const V succ).

Canonical Structure PCFsucc := Build_Module_Hom succ_hom_s.

Program Instance pred_hom_s : Module_Hom_struct 
  (S:=Term (C:=MOD PCFM TYPE)) (T:= PCFM [Nat ~> Nat])
  (fun V t => Const V preds).

Canonical Structure PCFpred := Build_Module_Hom pred_hom_s.

Program Instance zero_hom_s : Module_Hom_struct 
  (S:=Term (C:=MOD PCFM TYPE)) (T:= PCFM [Nat ~> Bool])
  (fun V t => Const V zero).

Canonical Structure PCFzero := Build_Module_Hom zero_hom_s.

Program Instance condN_hom_s : Module_Hom_struct 
  (S:=Term (C:=MOD PCFM TYPE)) (T:= PCFM [ _ ])
  (fun V t => Const V condN).

Canonical Structure PCFcondN := Build_Module_Hom condN_hom_s.

Program Instance condB_hom_s : Module_Hom_struct 
  (S:=Term (C:=MOD PCFM TYPE)) (T:= PCFM [ _ ])
  (fun V t => Const V condB).

Canonical Structure PCFcondB := Build_Module_Hom condB_hom_s.

Program Instance nats_hom_s m : Module_Hom_struct 
  (S:=Term (C:=MOD PCFM TYPE)) (T:= PCFM [ Nat ])
  (fun V t => Const V (Nats m)).

Canonical Structure PCFNats m := Build_Module_Hom (nats_hom_s m).

Program Instance bottom_hom_s t : Module_Hom_struct 
  (S:=Term (C:=MOD PCFM TYPE)) (T:= PCFM [ t ])
  (fun V _ => Bottom V t).

Canonical Structure PCFBottom t := Build_Module_Hom (bottom_hom_s t).
*)

(** the initial representation over the identity morphism of types *)

Program Instance PCF_init_s : PCF_rep_s (fun t => t) PCFM := {
  app r s := PCFapp r s ;
  abs r s := PCFabs r s ;
  rec t := PCFrec t ;
  bottom t := PCFBottom t;
  nats m := PCFNats m ;
  Succ := PCFsucc ;
  Zero := PCFzero ;
  CondN := PCFcondN;
  CondB := PCFcondB;
  tttt := PCFttt;
  ffff := PCFfff;
  Pred := PCFpred
}.

Canonical Structure PCF_init : REP := Build_PCF_rep PCF_init_s.

(** now for any representation R a morphism PCF_init -> R *)

Section initiality.

Variable R : PCF_rep.

(** the initial morphism STS -> R *)

Fixpoint init V t (v : PCF V t) : 
    R (retype (fun t0 => type_mor R t0) V) (type_mor R t) :=
  match v in PCF _ t return 
        R (retype (fun t0 => type_mor R t0) V) (type_mor R t) with
  | Var t v => weta (Monad_struct := R) _ _ (ctype _ v)
  | App _ _ u v => app (PCF_rep_s := R) _ _ _ (init u, init v)
  | Lam _ _ v => abs (PCF_rep_s := R) _ _ _ 
        (lift (M:=R) 
            (@der_comm TY (type_type R) (fun t => type_mor R t) _ V ) 
                   _ (init v))
  | Rec _ v => rec (PCF_rep_s := R) _ _ (init v)
  | Bottom _  => bottom (PCF_rep_s := R) _ _ tt
  | Const _ y => match y in Consts t1 return 
                    R (retype (fun t2 => type_mor R t2) V) (type_mor R t1) 
                 with
                 | Nats m => nats (PCF_rep_s := R) m (retype _ V) tt
                 | succ => Succ (PCF_rep_s := R) _ tt
                 | preds => Pred (PCF_rep_s := R) _ tt
                 | condN => CondN (PCF_rep_s := R) _ tt
                 | condB => CondB (PCF_rep_s := R) _ tt
                 | zero => Zero (PCF_rep_s := R) _ tt
                 | ttt => tttt (PCF_rep_s := R) _ tt
                 | fff => ffff (PCF_rep_s := R) _ tt
                 end
  end.


Obligation Tactic := idtac.
Notation "v //- f" := (@rename _ _ f _ v)(at level 43, left associativity).
Lemma init_lift (V : IT) t (y : PCF V t) W (f : V ---> W) : 
   (init (y //- f)) = 
      lift (M:=R) (retype_map f) _ (init y).
Proof.
  intros V t y.
  induction y;
  simpl;
  unfold lift;
  intros.
  
  assert (H':=mod_hom_mkl 
      (Module_Hom_struct:=bottom (PCF_rep_s := R) t)).
      simpl in H'; auto.
  
  destruct c.
    
      assert (H':=mod_hom_mkl 
      (Module_Hom_struct:=nats n (PCF_rep_s := R))).
      simpl in H'; auto.
      
      assert (H':=mod_hom_mkl 
      (Module_Hom_struct:=tttt (PCF_rep_s := R))).
      simpl in H'; auto.
      
      assert (H':=mod_hom_mkl 
      (Module_Hom_struct:=ffff (PCF_rep_s := R))).
      simpl in H'; auto.
      
      assert (H':=mod_hom_mkl 
      (Module_Hom_struct:=Succ (PCF_rep_s := R))).
      simpl in H'; auto.
      
      assert (H':=mod_hom_mkl 
      (Module_Hom_struct:=Pred (PCF_rep_s := R))).
      simpl in H'; auto.
      
      assert (H':=mod_hom_mkl 
      (Module_Hom_struct:=Zero (PCF_rep_s := R))).
      simpl in H'; auto.
      
      assert (H':=mod_hom_mkl 
      (Module_Hom_struct:=CondN (PCF_rep_s := R))).
      simpl in H'; auto.
      
      assert (H':=mod_hom_mkl 
      (Module_Hom_struct:=CondB (PCF_rep_s := R))).
      simpl in H'; auto.
    
  assert (H:=etakl R).
  simpl in H.
  rewrite H. auto.
  
  rewrite IHy1.
  rewrite IHy2.
  assert (H':=mod_hom_mkl 
      (Module_Hom_struct:=app (PCF_rep_s := R) s t)).
      simpl in H'.
  unfold lift.
  rewrite <- H'.
  auto.


  rewrite IHy.
  clear IHy.
  assert (H':=mod_hom_mkl 
      (Module_Hom_struct:=abs (PCF_rep_s := R) t s)).
      simpl in H'.
  unfold lift.
  rewrite <- H'.
  clear H'.
  apply f_equal.
  assert (H:=klkl R).
  simpl in H.
  rewrite H. simpl.
  rewrite H. simpl.
  apply (kl_eq R).
  simpl.
  clear y.
  intros r z.
  destruct z as [r z];
  simpl.
  assert (H':=etakl R).
  simpl in H'.
  rewrite H'.
  rewrite H'.
  simpl.
  
  destruct z as [r z | ];
  simpl; auto.
  
  assert (Ht:=lift_weta R).
  simpl in Ht.
  rewrite Ht. auto.
  
  rewrite IHy.
  assert (H':=mod_hom_mkl 
      (Module_Hom_struct:=rec (PCF_rep_s := R) t)).
      simpl in H'.
  unfold lift.
  rewrite <- H'.
  auto.
Qed.
  
Program Instance init_mon_s : 
     colax_Monad_Hom_struct (P:=PCFM) (Q:=R)
             (F0:=RETYPE (fun t => type_mor R t)) 
     (fun V t v => match v with ctype _ y => init y end).
Next Obligation.
Proof.
  simpl.
  intros V W f t y.
  destruct y as [t y].
  simpl.
  generalize dependent W.
  induction y;
  simpl; intros.

  assert (H':=mod_hom_mkl 
  (Module_Hom_struct:=bottom (PCF_rep_s := R) t)).
  simpl in H'. auto.
  
  destruct c.
    
    assert (H':=mod_hom_mkl 
      (Module_Hom_struct:=nats n (PCF_rep_s := R))).
      simpl in H'; auto.
      
      assert (H':=mod_hom_mkl 
      (Module_Hom_struct:=tttt (PCF_rep_s := R))).
      simpl in H'; auto.
      
      assert (H':=mod_hom_mkl 
      (Module_Hom_struct:=ffff (PCF_rep_s := R))).
      simpl in H'; auto.
      
      assert (H':=mod_hom_mkl 
      (Module_Hom_struct:=Succ (PCF_rep_s := R))).
      simpl in H'; auto.

      assert (H':=mod_hom_mkl 
      (Module_Hom_struct:=Pred (PCF_rep_s := R))).
      simpl in H'; auto.
      
      assert (H':=mod_hom_mkl 
      (Module_Hom_struct:=Zero (PCF_rep_s := R))).
      simpl in H'; auto.
      
      assert (H':=mod_hom_mkl 
      (Module_Hom_struct:=CondN (PCF_rep_s := R))).
      simpl in H'; auto.
      
      assert (H':=mod_hom_mkl 
      (Module_Hom_struct:=CondB (PCF_rep_s := R))).
      simpl in H'; auto.
  
  
  assert (H:=etakl R).
  simpl in H.
  rewrite H.
  simpl. auto.
  
  
  assert (H':=mod_hom_mkl 
  (Module_Hom_struct:=app (PCF_rep_s := R) s t)).
  simpl in H'.
  rewrite <- H'.
  apply f_equal.
  rewrite IHy1.
  rewrite IHy2.
  auto.
  
  assert (H':=mod_hom_mkl 
      (Module_Hom_struct:=abs (PCF_rep_s := R) t s)).
  simpl in H'.
  rewrite <- H'.
  apply f_equal.
  assert (H1:=lift_kleisli (M:=R)).
  simpl in H1.
  rewrite H1.
  rewrite IHy.
  simpl.
  assert (Hk := klkl R).
  simpl in Hk.
  unfold lift.
  rewrite Hk.
  apply (kl_eq R).
  simpl.
  
  intros r z.
  destruct z as [r z].
  simpl in *.
  
  destruct z as [r z | ];
  simpl. 
  generalize (f r z).
  clear z.
  intro z.
  unfold inj.
  rewrite init_lift.
  rewrite H1.
  unfold lift. simpl.
  apply (kl_eq R).
  clear z r.
  simpl.
  intros r z.
  destruct z as [r z];
  simpl. auto.
  
  assert (Hw:=etakl R).
  simpl in Hw.
  rewrite Hw.
  auto.
  
  assert (H':=mod_hom_mkl 
  (Module_Hom_struct:=rec (PCF_rep_s := R) t)).
  simpl in H'.
  rewrite <- H'.
  apply f_equal.
  rewrite IHy.
  auto.
  
Qed.
Next Obligation.
Proof.
  simpl.
  intros V t y.
  destruct y  as [t y].
  simpl.
  auto.
Qed.

Canonical Structure init_mon := Build_colax_Monad_Hom init_mon_s.

Obligation Tactic := simpl; intros; repeat elim_unit; auto.

Program Instance init_rep_s : PCF_rep_Hom_struct 
     (f:=fun t => type_mor R t) (fun t => eq_refl)
     init_mon.

Canonical Structure init_rep : PCF_init ---> R := 
      Build_PCF_rep_Hom init_rep_s.

Variable f : PCF_init ---> R.

Lemma init_unique : f == init_rep.
Proof.
  simpl in *.
  assert (H : forall t, tcomp init_rep t = tcomp f t).
    simpl.
    assert (H':= ttriag f).
    simpl in H'.
    auto.
  
  apply (eq_rep (H:=H)).
  simpl.
  intros V t y.
  destruct y as [t y].
  simpl.
  
  destruct f.
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
  
  assert (Hl := lift_transp_id (Q:=R) H).
  simpl in *.
  rewrite Hl.
  rewrite (UIP_refl _ _ (H t)).
  simpl.
  
  induction y;
  simpl.
  
  assert (Hb:=Bottom_Hom (PCF_rep_Hom_struct := 
            rep_gen_Hom_monad_struct) t (c:=V) tt).
  simpl in *.
  rewrite (UIP_refl _ _ (ttriag _)) in Hb.
  simpl in *.
  auto.
  
  destruct c.
    
    assert (Hb:=nats_Hom n (PCF_rep_Hom_struct := 
            rep_gen_Hom_monad_struct)  (c:=V) tt).
    simpl in *.
    rewrite (UIP_refl _ _ (ttriag _)) in Hb.
    simpl in * ; auto.
    
    assert (Hb:=ttt_Hom (PCF_rep_Hom_struct := 
            rep_gen_Hom_monad_struct)  (c:=V) tt).
    simpl in *.

    rewrite (UIP_refl _ _ (ttriag _)) in Hb.
    simpl in * ; auto.
    
    assert (Hb:=fff_Hom (PCF_rep_Hom_struct := 
            rep_gen_Hom_monad_struct)  (c:=V) tt).
    simpl in *.

    rewrite (UIP_refl _ _ (ttriag _)) in Hb.
    simpl in * ; auto.
    
    assert (Hb:=Succ_Hom (PCF_rep_Hom_struct := 
            rep_gen_Hom_monad_struct) (c:=V) tt).
    simpl in *.

    rewrite (UIP_refl _ _ (ttriag _)) in Hb.
    simpl in * ; auto.
    
    assert (Hb:=Pred_Hom (PCF_rep_Hom_struct := 
            rep_gen_Hom_monad_struct) (c:=V) tt).
    simpl in *.

    rewrite (UIP_refl _ _ (ttriag _)) in Hb.
    simpl in * ; auto.
        
    assert (Hb:=Zero_Hom (PCF_rep_Hom_struct := 
            rep_gen_Hom_monad_struct)  (c:=V) tt).
    simpl in *.

    rewrite (UIP_refl _ _ (ttriag _)) in Hb.
    simpl in * ; auto.
    
    assert (Hb:=CondN_Hom (PCF_rep_Hom_struct := 
            rep_gen_Hom_monad_struct)  (c:=V) tt).
    simpl in *.

    rewrite (UIP_refl _ _ (ttriag _)) in Hb.
    simpl in * ; auto.
    
    assert (Hb:=CondB_Hom (PCF_rep_Hom_struct := 
            rep_gen_Hom_monad_struct)  (c:=V) tt).
    simpl in *.

    rewrite (UIP_refl _ _ (ttriag _)) in Hb.
    simpl in * ; auto.

  
  (*1*)
  assert (Hw:=gen_monad_hom_weta 
     (colax_Monad_Hom_struct := rep_Hom_monad)).
     simpl in Hw.
  assert (Hw' := Hw _ _ (ctype _ v)).
  simpl in Hw'.
  auto.
  
  rewrite <- IHy1.
  rewrite <- IHy2.
  assert (Happ:=App_Hom (PCF_rep_Hom_struct := 
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
  assert (Habs:=Abs_Hom (PCF_rep_Hom_struct := 
            rep_gen_Hom_monad_struct) (r:=t) (s:=s)  y ).
  simpl in *.

  rewrite (UIP_refl _ _ (ttriag s)) in Habs.
  rewrite (UIP_refl _ _ (ttriag t)) in Habs.
  rewrite (UIP_refl _ _ (ttriag _)) in Habs.
  simpl in *.
  auto.
    
  rewrite <- IHy.
  assert (Happ:=Rec_Hom (PCF_rep_Hom_struct := 
            rep_gen_Hom_monad_struct) (t:=t) y).
  simpl in *.

  rewrite (UIP_refl _ _ (ttriag t)) in Happ.
  rewrite (UIP_refl _ _ (ttriag (t ~> t))) in Happ.
  simpl in *.
  auto.
Qed.

End initiality.

Hint Resolve init_unique : fin.
(*
Obligation Tactic := fin.
*)
Program Instance PCF_initial : Initial REP := {
  Init := PCF_init ;
  InitMor R := init_rep R ;
  InitMorUnique R := @init_unique R
}.




















