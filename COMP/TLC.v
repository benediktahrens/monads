Require Import Coq.Logic.Eqdep.
Require Import Coq.Logic.FunctionalExtensionality.

Require Export CatSem.COMP.TLC_rep_cat.
Require Export CatSem.TLC.TLC_Monad.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Program Instance app_hom_s r s : 
Module_Hom_struct
  (S:=Prod_Mod (P:=TLCM) TYPE_prod (ITFibre_Mod (P:=TLCM) TLCM (r ~> s))
     (ITFibre_Mod (P:=TLCM) TLCM r)) 
  (T:=ITFibre_Mod (P:=TLCM) TLCM s)
  (fun V y => app (fst y) (snd y)).


Canonical Structure TLCapp r s := Build_Module_Hom
    (app_hom_s r s).

Program Instance abs_hom_s r s : 
Module_Hom_struct
  (S:=ITFibre_Mod (P:=TLCM) (IT_Der_Mod (P:=TLCM) 
      (D:=ITYPE TY) TLCM r) s)
  (T:=ITFibre_Mod (P:=TLCM) TLCM (r ~> s))
  (fun V y => abs y).

Canonical Structure TLCabs r s := Build_Module_Hom (abs_hom_s r s).

Program Instance TLC_init_s : TLC_rep_s (fun t => t) TLCM := {
  App r s := TLCapp r s ;
  Abs r s := TLCabs r s
}.

Canonical Structure TLC_init : REP := Build_TLC_rep TLC_init_s.


Section initiality.

Variable R : TLC_rep.

(** the initial morphism STS -> R *)

Fixpoint init V t (v : TLC V t) : 
    R (retype (fun t0 => type_mor R t0) V) (type_mor R t) :=
  match v in TLC _ t return 
        R (retype (fun t0 => type_mor R t0) V) (type_mor R t) with
  | var t v => weta (Monad_struct := R) _ _ (ctype _ v)
  | app _ _ u v => App (TLC_rep_s := R) _ _ _ (init u, init v)
  | abs _ _ v => Abs (TLC_rep_s := R) _ _ _ 
        (lift (M:=R) 
            (@der_comm TY (type_type R) (fun t => type_mor R t) _ V ) 
                   _ (init v))
  end.


Obligation Tactic := idtac.

Lemma init_lift (V : IT) t (y : TLC V t) W (f : V ---> W) : 
   (init (y //- f)) = 
      lift (M:=R) (retype_map f) _ (init y).
Proof.
  intros V t y.
  induction y;
  simpl;
  intros.
  assert (H:=lift_weta R).
  simpl in H.
  rewrite H. auto.
  
  Focus 1.
  rewrite IHy.
  clear IHy.
  assert (H':=mod_hom_mkl 
      (Module_Hom_struct:=Abs (TLC_rep_s := R) r s)).
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
  intros t z.
  destruct z as [t z];
  simpl.
  assert (H':=etakl R).
  simpl in H'.
  rewrite H'.
  rewrite H'.
  simpl.
  
  destruct z as [t z | ];
  simpl; auto.
  
  assert (Ht:=lift_weta R).
  simpl in Ht.
  rewrite Ht. auto.
  
  rewrite IHy1.
  rewrite IHy2.
  assert (H':=mod_hom_mkl 
      (Module_Hom_struct:=App (TLC_rep_s := R) r s)).
      simpl in H'.
  unfold lift.
  rewrite <- H'.
  auto.
Qed.
  
Program Instance init_mon_s : 
     colax_Monad_Hom_struct (P:=TLCM) (Q:=R)
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
  assert (H:=etakl R).
  simpl in H.
  rewrite H.
  simpl. auto.
  
  (* focus to have more space *)
  
  Focus 1.
  
  assert (H':=mod_hom_mkl 
      (Module_Hom_struct:=Abs (TLC_rep_s := R) r s)).
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
  
  intros t z.
  destruct z as [t z].
  simpl in *.
  
  destruct z as [t z | ];
  simpl. 
  generalize (f t z).
  clear z.
  intro z.
  unfold _inj.
  rewrite init_lift.
  rewrite H1.
  unfold lift. simpl.
  apply (kl_eq R).
  clear z t.
  simpl.
  intros t z.
  destruct z as [t z];
  simpl. auto.
  
  assert (Hw:=etakl R).
  simpl in Hw.
  rewrite Hw.
  auto.
  
  assert (H':=mod_hom_mkl 
  (Module_Hom_struct:=App (TLC_rep_s := R) r s)).
  simpl in H'.
  rewrite <- H'.
  apply f_equal.
  rewrite IHy1.
  rewrite IHy2.
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

Obligation Tactic := simpl; auto.

Program Instance init_rep_s : TLC_rep_Hom_struct 
     (f:=fun t => type_mor R t) (fun t => eq_refl)
     init_mon.

Canonical Structure init_rep : TLC_init ---> R := 
      Build_TLC_rep_Hom init_rep_s.

Variable f : TLC_init ---> R.

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
  (*1*)
  assert (Hw:=gen_monad_hom_weta 
     (colax_Monad_Hom_struct := rep_Hom_monad)).
     simpl in Hw.
  assert (Hw' := Hw _ _ (ctype _ v)).
  simpl in Hw'.
  auto.
  
  (*2*)
  rewrite <- IHy.
  assert (Habs:=Abs_Hom (TLC_rep_Hom_struct := 
            rep_gen_Hom_monad_struct) (r:=r) (s:=s)  y ).
  simpl in *.
  
  rewrite (UIP_refl _ _ (ttriag s)) in Habs.
  rewrite (UIP_refl _ _ (ttriag r)) in Habs.
  rewrite (UIP_refl _ _ (ttriag (r ~> s))) in Habs.
  simpl in *.
  auto.
    
  (*3*)
  rewrite <- IHy1.
  rewrite <- IHy2.
  assert (Happ:=App_Hom (TLC_rep_Hom_struct := 
            rep_gen_Hom_monad_struct) (r:=r) (s:=s) (y1,y2)).
  simpl in *.

  rewrite (UIP_refl _ _ (ttriag s)) in Happ.
  rewrite (UIP_refl _ _ (ttriag r)) in Happ.
  rewrite (UIP_refl _ _ (ttriag (r ~> s))) in Happ.
  simpl in *.
  auto.
Qed.

End initiality.

Hint Resolve init_unique : fin.

Obligation Tactic := fin.

Program Instance TLC_initial : Initial REP := {
  Init := TLC_init ;
  InitMor R := init_rep R ;
  InitMorUnique R := @init_unique R
}.






