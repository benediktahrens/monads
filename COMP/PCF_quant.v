Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Eqdep.

Require Export CatSem.COMP.PCF_rep_cat_quant.
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

Program Instance PCF_init_s : 
 PCF_rep_struct PCFM (fun t => t) (PCF.Arrow) := {
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

Canonical Structure PCF_init : REP := 
   Build_PCF_rep (type_type:=TY)(type_arrow:=PCF.Arrow)
   (fun _ _ => eq_refl) PCF_init_s.

(** now for any representation R a morphism PCF_init -> R *)

Section initiality.

Variable R : PCF_rep.

(** the initial morphism STS -> R *)

Fixpoint init V t (v : PCF V t) : 
    R (retype (fun t0 => type_mor R t0) V) (type_mor R t) :=
  match v in PCF _ t return 
        R (retype (fun t0 => type_mor R t0) V) (type_mor R t) with
  | Var t v => weta (Monad_struct := R) _ _ (ctype _ v)
  | App r s u v => app (PCF_rep_struct := R) _ _ _ 
           (eq_rect (A:=type_type R)
              _
              (fun t1 : type_type R =>
                (R (retype (fun t2 : TY => type_mor R t2) _)) t1) 
               (init u) _
               ( (type_arrow_dist R _ _ )), 
                         init v)
  | Lam _ _ v => 
        eq_rect (A:=type_type R) _
             (fun t1 : type_type R =>
                (R (retype (fun t2 : TY => type_mor R t2) _)) t1) 
            (abs (PCF_rep_struct := R) _ _ _ 
                  (lift (M:=R) 
            (@der_comm TY (type_type R) (fun t => type_mor R t) _ V ) 
                   _ (init v)))
               _ (eq_sym (type_arrow_dist R _ _ ))
  | Rec _ v => rec (PCF_rep_struct := R) _ _ 
                  (eq_rect (A:=type_type R) _ 
                   (fun t1 : type_type R =>
                (R (retype (fun t2 : TY => type_mor R t2) _)) t1)
                 (init v) _ (type_arrow_dist R _ _ ))
  | Bottom _  => bottom (PCF_rep_struct := R) _ _ tt
  | Const _ y => match y in Consts t1 return 
                    R (retype (fun t2 => type_mor R t2) V) (type_mor R t1) 
                 with
                 | Nats m => nats (PCF_rep_struct := R) m 
                      (retype _ V) tt
                 | succ => eq_rect
           (type_mor R Nat ~~> type_mor R Nat)
           (fun t1 : type_type R =>
            (R (retype (fun t2 : TY => type_mor R t2) _)) t1)
           ((Succ (retype (fun t1 : TY => type_mor R t1) _)) tt)
           (type_mor R (Nat ~> Nat))
           (eq_sym (type_arrow_dist R Nat Nat))
                 | condN => eq_rect
           (type_mor R Bool ~~> type_mor R Nat ~~>
            type_mor R Nat ~~> type_mor R Nat)
           (fun t1 : type_type R =>
            (R (retype (fun t2 : TY => type_mor R t2) _)) t1)
           ((CondN (retype (fun t1 : TY => type_mor R t1) _)) tt)
           (type_mor R
              (Bool ~> Nat ~> Nat ~> Nat))
           (eq_sym
              (arrow_distrib4 (Uar:=PCF.Arrow) (U'ar:=type_arrow (p:=R))
                 (g:=type_mor R) (type_arrow_dist R) Bool
                 Nat Nat Nat))
                 | condB => eq_rect
           (type_mor R Bool ~~> type_mor R Bool ~~> 
            type_mor R Bool ~~> type_mor R Bool)
           (fun t1 : type_type R =>
            (R (retype (fun t2 : TY => type_mor R t2) _)) t1)
           ((CondB (retype (fun t1 : TY => type_mor R t1) _)) tt)
           (type_mor R
              (Bool ~> Bool ~> Bool ~> Bool))
           (eq_sym
              (arrow_distrib4 (Uar:=PCF.Arrow) (U'ar:=type_arrow (p:=R))
                 (g:=type_mor R) (type_arrow_dist R) Bool
                 Bool Bool Bool))
                 | zero => eq_rect
           (type_mor R Nat ~~> type_mor R Bool)
           (fun t1 : type_type R =>
            (R (retype (fun t2 : TY => type_mor R t2) _)) t1)
           ((Zero (retype (fun t1 : TY => type_mor R t1) _)) tt)
           (type_mor R (Nat ~> Bool))
           (eq_sym (type_arrow_dist R Nat Bool))
                 | ttt => tttt (PCF_rep_struct := R) _ tt
                 | fff => ffff (PCF_rep_struct := R) _ tt
                 | preds => eq_rect
           (type_mor R Nat ~~> type_mor R Nat)
           (fun t1 : type_type R =>
            (R (retype (fun t2 : TY => type_mor R t2) _)) t1)
           ((Pred (retype (fun t1 : TY => type_mor R t1) _)) tt)
           (type_mor R (Nat ~> Nat))
           (eq_sym (type_arrow_dist R Nat Nat))
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
  intros.

  unfold lift.
  assert (H':=mod_hom_mkl
      (Module_Hom_struct :=bottom (PCF_rep_struct := R) (type_mor R t))).
      simpl in H'; auto.

  destruct c.

      unfold lift.
      assert (H':=mod_hom_mkl
      (Module_Hom_struct := nats n (PCF_rep_struct := R))).
      simpl in H'; auto.

      unfold lift.
      assert (H':=mod_hom_mkl
      (Module_Hom_struct:=tttt (PCF_rep_struct := R))).
      simpl in H'; auto.

      unfold lift.
      assert (H':=mod_hom_mkl
      (Module_Hom_struct:=ffff (PCF_rep_struct := R))).
      simpl in H'; auto.

      unfold lift.
      destruct R as [TR Rar RM Rmor Rdist Rrep];
      simpl.
      generalize (eq_sym (Rdist Nat Nat)).
      destruct Rrep as
       [Rapp Rabs Rrec tttt
      ffff nats RSucc Pred Zero CondN CondB bottom].
      simpl in *.
      clear Rapp Rabs Rrec tttt ffff nats Pred Zero
        CondN CondB bottom.
      generalize RSucc.
      simpl in *.
      rewrite <- Rdist.
      intros RSucc0 e.
      rewrite (UIP_refl _ _ e).
      simpl.
      assert (H':=mod_hom_mkl (Module_Hom_struct := RSucc0 )).
      simpl in H'.
      auto.

     unfold lift.
     destruct R as [TR Rar RM Rmor Rdist Rrep];
     simpl.
     generalize (eq_sym (Rdist Nat Nat)).
      destruct Rrep as
       [Rapp Rabs Rrec tttt
      ffff nats Succ RPred Zero CondN CondB bottom].
      simpl in *.
      clear Rapp Rabs Rrec tttt ffff nats Zero
        CondN CondB bottom Succ.
      generalize RPred.
      simpl in *.
      rewrite <- Rdist.
      intros RPred0 e.
      rewrite (UIP_refl _ _ e).
      simpl.
      assert (H':=mod_hom_mkl (Module_Hom_struct := RPred0)).
      simpl in H'.
      auto.

      unfold lift.
      destruct R as [TR Rar RM Rmor Rdist Rrep];
      simpl.
      generalize (eq_sym (Rdist Nat Bool)).
      destruct Rrep as
       [Rapp Rabs Rrec tttt
      ffff nats Succ Pred RZero CondN CondB bottom].
      simpl in *.
      clear Rapp Rabs Rrec tttt ffff nats Succ Pred
        CondN CondB bottom.
      generalize RZero.
      simpl in *.
      rewrite <- Rdist.
      intros RZero0 e.
      rewrite (UIP_refl _ _ e).
      simpl.
      assert (H':=mod_hom_mkl (Module_Hom_struct := RZero0)).
      simpl in H'.
      auto.

      unfold lift.
      destruct R as [TR Rar RM Rmor Rdist Rrep];
      simpl.
      generalize (eq_sym
        (arrow_distrib4 (Uar:=PCF.Arrow) (U'ar:=Rar) (g:=Rmor)
           Rdist Bool Nat Nat Nat)).
      destruct Rrep as
       [Rapp Rabs Rrec tttt
      ffff nats Succ Pred Zero RCondN CondB bottom].
      simpl in *.
      clear Rapp Rabs Rrec tttt ffff nats Pred Zero
        Succ CondB bottom.
      generalize RCondN.
      simpl in *.
      do 3 rewrite <- Rdist.
      intros RCondN0 e.
      rewrite (UIP_refl _ _ e).
      simpl.
      assert (H':=mod_hom_mkl (Module_Hom_struct:=RCondN0)).
      simpl in H'.
      auto.

      unfold lift.
      destruct R as [TR Rar RM Rmor Rdist Rrep];
      simpl.
      generalize (eq_sym
        (arrow_distrib4 (Uar:=PCF.Arrow) (U'ar:=Rar) (g:=Rmor)
           Rdist Bool Bool Bool Bool)).
      destruct Rrep as
       [Rapp Rabs Rrec tttt
      ffff nats Succ Pred Zero CondN RCondB bottom].
      simpl in *.
      clear Rapp Rabs Rrec tttt ffff nats Pred Zero
        Succ CondN bottom.
      generalize RCondB.
      simpl in *.
      do 3 rewrite <- Rdist.
      intros RCondB0 e.
      rewrite (UIP_refl _ _ e).
      simpl.
      assert (H':=mod_hom_mkl (Module_Hom_struct:=RCondB0)).
      simpl in H'.
      auto.

      unfold lift.
      rew (etakl R).

      rewrite IHy1.
      rewrite IHy2.
      clear IHy1 IHy2.
      generalize (type_arrow_dist R s t).
      intro e.
      simpl.
      unfold lift.
      assert (H':= mod_hom_mkl (Module_Hom_struct :=
                    app (type_mor R s) (type_mor R t))).
      simpl in H'.
      rewrite <- H'.
      simpl.
      apply f_equal.
      generalize dependent e.
      rewrite <- type_arrow_dist.
      intro e.
      rewrite (UIP_refl _ _ e).
      simpl.
      auto.

      rewrite IHy.
      clear IHy.
      generalize (eq_sym (type_arrow_dist R t s)).
      rewrite type_arrow_dist.
      intro e.
      rewrite (UIP_refl _ _ e).
      simpl.
      unfold lift.
      assert (H':= mod_hom_mkl 
         (Module_Hom_struct := abs (type_mor R t) (type_mor R s))).
      simpl in *.
      rewrite <- H'.
      apply f_equal.
      rew (klkl R).
      rew (klkl R).
      apply (kl_eq R).
      simpl.
      intros t0 z.
      rew (etakl R).
      rew (etakl R).
      destruct z as [t0 z];
      simpl.
      destruct z as [t0 z | ];
      simpl; auto.
      unfold lift;
      rew (etakl R).

      rewrite IHy.
      clear IHy.
      generalize (type_arrow_dist R t t).
      intro e.
      simpl.
      unfold lift.
      assert (H':= mod_hom_mkl 
          (Module_Hom_struct := rec (type_mor R t))).
      simpl in H'.
      rewrite <- H'.
      simpl.
      apply f_equal.
      generalize dependent e.
      rewrite <- type_arrow_dist.
      intro e.
      rewrite (UIP_refl _ _ e).
      simpl.
      auto.
Qed.

Notation "y >>= f" := (@subst _ _ f _ y) (at level 42).
Lemma init_subst V t (y : PCF V t) W (f : V ---> PCF W):
init (y >>= f) =
kleisli (a:=retype (fun t0 : TY => type_mor R t0) V)
  (b:=retype (fun t0 : TY => type_mor R t0) W)
  (fun (t0 : type_type R) (y : retype (fun t1 : TY => type_mor R t1) V t0) =>
   match
     retype_map (W:=PCF W) f y in (retype _ _ t1)
     return (R (retype (fun t2 : TY => type_mor R t2) W) t1)
   with
   | ctype t1 y0 => init y0
   end) (type_mor R t) (init y).
Proof.
  intros V t y.
  induction y;
  simpl;
  intros.

  rerew (mod_hom_mkl (Module_Hom_struct := bottom (type_mor R t)
            (PCF_rep_struct := R))).

  destruct c.
  simpl. intros.
  rerew (mod_hom_mkl (Module_Hom_struct :=nats n (PCF_rep_struct := R))).

  simpl. intros.
  rerew (mod_hom_mkl (Module_Hom_struct :=tttt (PCF_rep_struct := R))).

  simpl. intros.
  rerew (mod_hom_mkl (Module_Hom_struct :=ffff (PCF_rep_struct := R))).

  simpl in *.
  intros.
  generalize (eq_sym (type_arrow_dist R Nat Nat)).
  intro e.
  generalize (Succ (PCF_rep_struct := R)).
  generalize e.
  rewrite e.
  intros.
  rewrite (UIP_refl _ _ e0).
  simpl.
  rerew (mod_hom_mkl (Module_Hom_struct:=m)).

  simpl. intros.
  generalize (eq_sym (type_arrow_dist R Nat Nat)).
  generalize (Pred (PCF_rep_struct := R)).
  rewrite <- type_arrow_dist.
  intros m e.
  rewrite (UIP_refl _ _ e).
  simpl.
  rerew (mod_hom_mkl (Module_Hom_struct:=m)).

  simpl. intros.
  generalize (eq_sym (type_arrow_dist R Nat Bool)).
  generalize (Zero (PCF_rep_struct := R)).
  rewrite <- type_arrow_dist.
  intros m e.
  rewrite (UIP_refl _ _ e).
  simpl.
  rerew (mod_hom_mkl (Module_Hom_struct := m)).

  simpl. intros.
  generalize (eq_sym (arrow_distrib4
         (type_arrow_dist R) Bool Nat Nat Nat)).
  generalize (CondN (PCF_rep_struct := R)).
  do 3 rewrite <- type_arrow_dist.
  intros m e.
  rewrite (UIP_refl _ _ e).
  simpl.
  rerew (mod_hom_mkl (Module_Hom_struct := m)).

  simpl. intros.
  generalize (eq_sym (arrow_distrib4
         (type_arrow_dist R) Bool Bool Bool Bool)).
  generalize (CondB (PCF_rep_struct := R)).
  do 3 rewrite <- type_arrow_dist.
  intros m e.
  rewrite (UIP_refl _ _ e).
  simpl.
  rerew (mod_hom_mkl (Module_Hom_struct := m)).

  simpl. intros.
  rew (etakl R).

  simpl; intros.
  rewrite IHy1.
  rewrite IHy2.
  clear IHy1 IHy2.
  generalize (type_arrow_dist R s t).
  intro e.
  assert (H:=mod_hom_mkl (Module_Hom_struct := 
       app (type_mor R s) (type_mor R t)
              (PCF_rep_struct := R))).
  simpl in H.
  rewrite <- H.
  apply f_equal.
  simpl.
  generalize dependent e.
  rewrite <- type_arrow_dist.
  intro e.
  rewrite (UIP_refl _ _ e).
  simpl.
  auto.

  simpl; intros.
  generalize (eq_sym (type_arrow_dist R t s)).
  rewrite type_arrow_dist.
  intro e.
  rewrite (UIP_refl _ _ e).
  simpl.
  assert (H := IHy _ (shift (P:=PCFM) f)).
  simpl in *.
  rerew (mod_hom_mkl (Module_Hom_struct := abs (type_mor R t) (type_mor R s)
         (PCF_rep_struct := R))).
  apply f_equal.
  assert (H1:=lift_kleisli (M:=R)).
  simpl in H1.
  rewrite H1.
  transitivity
( (lift (M:=R) (a:=retype (fun t0 : TY => type_mor R t0) (opt t W))
   (b:=opt (type_mor R t) (retype (fun t0 : TY => type_mor R t0) W))
            (@der_comm _ _ _ _ _ )) (type_mor R s)
      (init (y >>= shift (P:=PCFM) (W:=W) f))).
  repeat apply f_equal.
  apply subst_eq.
  intros.
  rewrite shift_shift.
  auto.
(*
  rew H.
*)
  simpl.
  rew (IHy).
  rew (kleisli_lift (M:=R)).
  apply (kl_eq R).
  clear dependent y.
  simpl.
  intros t0 z.
  destruct z as [t0 z];
  simpl.
  destruct z as [t0 z | ];
  simpl.
  unfold inj.
  generalize (f t0 z).
  clear dependent z.
  intro z.
  assert (H := init_lift z (some t (A:=W))).
  rewrite lift_rename in H.
  simpl in *.
  unfold lift at 2.
  simpl.
  transitivity (lift (@der_comm _ _ _ _ _ )(type_mor R t0)
      (lift (retype_map (W:=opt t W) (some t (A:=W))) 
            (type_mor R t0) (init z))).
  apply f_equal.
  apply H.
  rew (lift_lift R).
  apply (lift_eq R).
  simpl.
  intros t1 y.
  destruct y;
  auto.

  rew (lift_weta R).

  simpl; intros.
  rewrite IHy.
  clear IHy.
  generalize (type_arrow_dist R t t).
  intro e.
  rerew (mod_hom_mkl (Module_Hom_struct := 
              rec (type_mor R t) (PCF_rep_struct := R))).
  apply f_equal.
  simpl.
  generalize dependent e.
  rewrite <- type_arrow_dist.
  intro e.
  rewrite (UIP_refl _ _ e).
  simpl.
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
  apply init_subst.
Qed.
Next Obligation.
Proof.
  simpl. intros V t y.
  destruct y;
  simpl.
  auto.
Qed.
 
Canonical Structure init_mon := Build_colax_Monad_Hom init_mon_s.

Ltac eq_elim := match goal with
      | [ H : ?a = ?a |- _ ] => rewrite (UIP_refl _ _ H)
      | [ H : _ = _ |- _ ] => destruct H end.

Lemma double_eq_rect A (t : A) P (y : P t) s
      (e: t = s) (e': s = t) :
   eq_rect s P (eq_rect t P y _ e) _ e' = y.
Proof.
  intros; repeat eq_elim; simpl; auto.
Qed.

Hint Resolve double_eq_rect.
Obligation Tactic := simpl; intros; repeat elim_unit; auto.

Program Instance init_rep_s : PCF_rep_Hom_struct 
     (f:=fun t => type_mor R t) (fun t => eq_refl)
      (type_arrow_dist R )
     init_mon.

Canonical Structure init_rep : PCF_init ---> R := 
      Build_PCF_rep_Hom init_rep_s.

Variable g : PCF_init ---> R.

Lemma init_unique : g == init_rep.
Proof.
  simpl.
  assert (H : forall t, tcomp (init_rep) t = tcomp g t).
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
  
  assert (Hl := lift_transp_id (Q:=R) H).
  simpl in *.
  rewrite Hl.
  clear Hl.
  clear e H.
  
  induction y.
  simpl.
  
  assert (Hb:=Bottom_Hom (PCF_rep_Hom_struct := Ts) 
            t (c:=V) tt).
  simpl in *.
  auto.
  
  destruct c.
    
    assert (Hb:=nats_Hom n (PCF_rep_Hom_struct := 
            Ts)  (c:=V) tt).
    simpl in *.
    rewrite (UIP_refl _ _ (Hfcomm _)) in Hb.
    simpl in * ; auto.
    
    assert (Hb:=ttt_Hom (PCF_rep_Hom_struct := 
            Ts)  (c:=V) tt).
    simpl in *.
    rewrite (UIP_refl _ _ (Hfcomm _)) in Hb.
    simpl in * ; auto.
    
    assert (Hb:=fff_Hom (PCF_rep_Hom_struct := 
            Ts)  (c:=V) tt).
    simpl in *.
    rewrite (UIP_refl _ _ (Hfcomm _)) in Hb.
    simpl in * ; auto.
    
    assert (Hb:=Succ_Hom (PCF_rep_Hom_struct := 
            Ts) (c:=V) tt).
    simpl in *.
    rewrite <- Hb.
    clear Hb.
    symmetry.
    apply double_eq_rect.
        
    assert (Hb:=Pred_Hom (PCF_rep_Hom_struct := 
            Ts)  (c:=V) tt).
    simpl in *.
    rewrite <- Hb.
    symmetry.
    apply double_eq_rect.

    assert (Hb:=Zero_Hom (PCF_rep_Hom_struct := 
            Ts)  (c:=V) tt).
    simpl in *.
    rewrite <- Hb.
    clear Hb.
    symmetry.
    apply double_eq_rect.
    
    assert (Hb:=CondN_Hom (PCF_rep_Hom_struct := 
            Ts)  (c:=V) tt).
    simpl in *.
    rewrite <- Hb.
    clear Hb.
    symmetry.
    apply double_eq_rect.
    
    assert (Hb:=CondB_Hom (PCF_rep_Hom_struct := 
            Ts)  (c:=V) tt).
    simpl in *.
    rewrite <- Hb.
    clear Hb.
    symmetry.
    apply double_eq_rect.

  (*1*)
  assert (Hw:=gen_monad_hom_weta 
     ((*gen_RMonad_Hom_struct := *)colax_Monad_Hom_struct := T)).
     simpl in Hw.
  assert (Hw' := Hw _ _ (ctype _ v)).
  simpl in Hw'.
  auto.
  (*2*)
  simpl.
  rewrite <- IHy1.
  rewrite <- IHy2.
  assert (Happ:=App_Hom (PCF_rep_Hom_struct := 
            Ts) (u:=s) (v:=t) (y1,y2)).
  simpl in *.
  rewrite Happ.
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
  assert (Habs:=Abs_Hom (PCF_rep_Hom_struct := 
            Ts) (u:=t) (v:=s)  y ).
  simpl in *.
  rewrite Habs.
  rewrite (UIP _ _ _ (eq_sym (Hfarrow t s))
                     (eq_sym (type_arrow_dist R t s))).
  reflexivity.                     
  
  simpl.
  rewrite <- IHy.
  assert (Happ:=Rec_Hom (PCF_rep_Hom_struct := 
            Ts) (t:=t) y).
  simpl in *.
  rewrite Happ.
  rewrite (UIP _ _ _ (Hfarrow t t)
                     (type_arrow_dist R t t)).
  reflexivity.
Qed.

End initiality.

Hint Resolve init_unique : fin.



Program Instance PCF_initial : Initial REP := {
  Init := PCF_init ;
  InitMor R := init_rep R ;
  InitMorUnique R := @init_unique R
}.




















