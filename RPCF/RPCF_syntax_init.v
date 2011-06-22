Require Import Coq.Logic.Eqdep.

Require Export CatSem.PCF_o_c.RPCF_syntax_rep.
Require Export CatSem.PCF_o_c.RPCF_rep_hom.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.


Section weak_init.

Variable R : PCFPO_rep.
(*
Fixpoint init_tac V t (v : PCF V t) : 
    R (retype (fun t0 => type_mor R t0) V) (type_mor R t).
intros V t v.
induction v.
apply (bottom (PCFPO_rep_struct := R) _ _ tt).

destruct c.
apply (nats (PCFPO_rep_struct:=R) n _ tt).
apply (tttt (PCFPO_rep_struct:=R) _ tt).
apply (ffff (PCFPO_rep_struct:=R) _ tt).
rewrite <- (eq_sym (type_arrow_dist _ _ _)).
apply (Succ (PCFPO_rep_struct:=R) _ tt).

rewrite <- (eq_sym (type_arrow_dist _ _ _)).
apply (Pred (PCFPO_rep_struct:=R) _ tt).

rewrite <- (eq_sym (type_arrow_dist _ _ _)).
apply (Zero (PCFPO_rep_struct:=R) _ tt).

Check arrow_distrib4.
rewrite <- (eq_sym (arrow_distrib4 (type_arrow_dist R) _ _ _ _ )).
apply (CondN (PCFPO_rep_struct:=R) _ tt).
rewrite <- (eq_sym (arrow_distrib4 (type_arrow_dist R) _ _ _ _ )).
apply (CondB (PCFPO_rep_struct:=R) _ tt).
apply (rweta (RMonad_struct := R) _ _ 
         (ctype (fun t => type_mor R t) v)).
rewrite <- (eq_sym (type_arrow_dist R _ _ )) in IHv1.
exact ( app (PCFPO_rep_struct:=R) _ _ _ (IHv1,IHv2)).
rewrite <- (eq_sym (type_arrow_dist _ _ _ )).
apply (abs (PCFPO_rep_struct:=R) ).
apply (rlift R (@der_comm _ _ _ _ _ ) _ (IHv)).

rewrite <- (eq_sym (type_arrow_dist _ _ _ ))in IHv.
apply (rec (PCFPO_rep_struct:=R) _ _ IHv).
Defined.

Print init_tac.
*)

(** the initial morphism STS -> R *)

Fixpoint init V t (v : PCF V t) : 
    R (retype (fun t0 => type_mor R t0) V) (type_mor R t) :=
  match v in PCF _ t return 
        R (retype (fun t0 => type_mor R t0) V) (type_mor R t) with
  | Var t v => rweta (RMonad_struct := R) _ _ (ctype _ v)
  | App r s u v => app (PCFPO_rep_struct := R) _ _ _ 
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
            (abs (PCFPO_rep_struct := R) _ _ _ 
                  (rlift R 
            (@der_comm TY (type_type R) (fun t => type_mor R t) _ V ) 
                   _ (init v)))
               _ (eq_sym (type_arrow_dist R _ _ ))
  | Rec _ v => rec (PCFPO_rep_struct := R) _ _ 
                  (eq_rect (A:=type_type R) _ 
                   (fun t1 : type_type R =>
                (R (retype (fun t2 : TY => type_mor R t2) _)) t1)
                 (init v) _ (type_arrow_dist R _ _ ))
  | Bottom _  => bottom (PCFPO_rep_struct := R) _ _ tt
  | Const _ y => match y in Consts t1 return 
                    R (retype (fun t2 => type_mor R t2) V) (type_mor R t1) 
                 with
                 | Nats m => nats (PCFPO_rep_struct := R) m 
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
              (arrow_distrib4 (Uar:=PCF.arrow) (U'ar:=type_arrow (p:=R))
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
              (arrow_distrib4 (Uar:=PCF.arrow) (U'ar:=type_arrow (p:=R))
                 (g:=type_mor R) (type_arrow_dist R) Bool
                 Bool Bool Bool))
                 | zero => eq_rect
           (type_mor R Nat ~~> type_mor R Bool)
           (fun t1 : type_type R =>
            (R (retype (fun t2 : TY => type_mor R t2) _)) t1)
           ((Zero (retype (fun t1 : TY => type_mor R t1) _)) tt)
           (type_mor R (Nat ~> Bool))
           (eq_sym (type_arrow_dist R Nat Bool))
                 | ttt => tttt (PCFPO_rep_struct := R) _ tt
                 | fff => ffff (PCFPO_rep_struct := R) _ tt
                 | preds => eq_rect
           (type_mor R Nat ~~> type_mor R Nat)
           (fun t1 : type_type R =>
            (R (retype (fun t2 : TY => type_mor R t2) _)) t1)
           ((Pred (retype (fun t1 : TY => type_mor R t1) _)) tt)
           (type_mor R (Nat ~> Nat))
           (eq_sym (type_arrow_dist R Nat Nat))
                 end
  end.


Lemma init_lift (V : IT) t (y : PCF V t) W (f : V ---> W) : 
   (init (y //- f)) = 
      rlift R (retype_map f) _ (init y).
Proof.
  intros V t y.
  induction y;
  simpl;
  intros.
  
  unfold rlift.
  assert (H':=rmod_hom_rmkl 
      (bottom (PCFPO_rep_struct := R) (type_mor R t))).
      simpl in H'; auto.
  
  destruct c.
    
      unfold rlift.
      assert (H':=rmod_hom_rmkl 
      (nats n (PCFPO_rep_struct := R))).
      simpl in H'; auto.
      
      unfold rlift.
      assert (H':=rmod_hom_rmkl 
      (tttt (PCFPO_rep_struct := R))).
      simpl in H'; auto.
      
      unfold rlift.
      assert (H':=rmod_hom_rmkl 
      (ffff (PCFPO_rep_struct := R))).
      simpl in H'; auto.
      
      unfold rlift.
      destruct R as [TR Rar RM Rmor Rdist Rrep];
      simpl.
      generalize (eq_sym (Rdist Nat Nat)).
      destruct Rrep as 
       [Rapp Rabs Rrec tttt 
      ffff nats RSucc Pred Zero CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 propag_rec*)
       CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn Pred_Z
        Rec_A ].
      simpl in *.
      clear Rapp Rabs Rrec tttt ffff nats Pred Zero
        CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
        propag_rec*) 
        CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn 
        Pred_Z Rec_A.
      generalize RSucc.
      simpl in *.
      rewrite <- Rdist.
      intros RSucc0 e.
      rewrite (UIP_refl _ _ e).
      simpl.
      assert (H':=rmod_hom_rmkl RSucc0 ).
      simpl in H'.
      auto.

     unfold rlift.
     destruct R as [TR Rar RM Rmor Rdist Rrep];
     simpl.
     generalize (eq_sym (Rdist Nat Nat)).
      destruct Rrep as 
       [Rapp Rabs Rrec tttt 
      ffff nats Succ RPred Zero CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 propag_rec*)
       CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn Pred_Z
        Rec_A ].
      simpl in *.
      clear Rapp Rabs Rrec tttt ffff nats Zero
        CondN CondB bottom Succ
        beta_red 
        (*propag_app1 propag_abs propag_app2 
        propag_rec*)
        CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn 
        Pred_Z Rec_A.
      generalize RPred.
      simpl in *.
      rewrite <- Rdist.
      intros RPred0 e.
      rewrite (UIP_refl _ _ e).
      simpl.
      assert (H':=rmod_hom_rmkl RPred0 ).
      simpl in H'.
      auto.
      
      unfold rlift.
      destruct R as [TR Rar RM Rmor Rdist Rrep];
      simpl.
      generalize (eq_sym (Rdist Nat Bool)).
      destruct Rrep as 
       [Rapp Rabs Rrec tttt 
      ffff nats Succ Pred RZero CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 propag_rec*)
       CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn Pred_Z
        Rec_A ].
      simpl in *.
      clear Rapp Rabs Rrec tttt ffff nats Succ Pred 
        CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
        propag_rec*) 
        CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn 
        Pred_Z Rec_A.
      generalize RZero.
      simpl in *.
      rewrite <- Rdist.
      intros RZero0 e.
      rewrite (UIP_refl _ _ e).
      simpl.
      assert (H':=rmod_hom_rmkl RZero0 ).
      simpl in H'.
      auto.
      
      unfold rlift.
      destruct R as [TR Rar RM Rmor Rdist Rrep];
      simpl.
      generalize (eq_sym
        (arrow_distrib4 (Uar:=PCF.arrow) (U'ar:=Rar) (g:=Rmor) 
           Rdist Bool Nat Nat Nat)).
      destruct Rrep as 
       [Rapp Rabs Rrec tttt 
      ffff nats Succ Pred Zero RCondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 propag_rec*)
       CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn Pred_Z
        Rec_A ].
      simpl in *.
      clear Rapp Rabs Rrec tttt ffff nats Pred Zero
        Succ CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
        propag_rec*)
        CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn 
        Pred_Z Rec_A.
      generalize RCondN.
      simpl in *.
      do 3 rewrite <- Rdist.
      intros RCondN0 e.
      rewrite (UIP_refl _ _ e).
      simpl.
      assert (H':=rmod_hom_rmkl RCondN0 ).
      simpl in H'.
      auto.
      
      unfold rlift.
      destruct R as [TR Rar RM Rmor Rdist Rrep];
      simpl.
      generalize (eq_sym
        (arrow_distrib4 (Uar:=PCF.arrow) (U'ar:=Rar) (g:=Rmor) 
           Rdist Bool Bool Bool Bool)).
      destruct Rrep as 
       [Rapp Rabs Rrec tttt 
      ffff nats Succ Pred Zero CondN RCondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 propag_rec*)
       CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn Pred_Z
        Rec_A ].
      simpl in *.
      clear Rapp Rabs Rrec tttt ffff nats Pred Zero
        Succ CondN bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
        propag_rec*)
        CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn 
        Pred_Z Rec_A.
      generalize RCondB.
      simpl in *.
      do 3 rewrite <- Rdist.
      intros RCondB0 e.
      rewrite (UIP_refl _ _ e).
      simpl.
      assert (H':=rmod_hom_rmkl RCondB0 ).
      simpl in H'.
      auto.
      
      unfold rlift.
      rew (retakl R).
      
      rewrite IHy1.
      rewrite IHy2.
      clear IHy1 IHy2.
      generalize (type_arrow_dist R s t).
      intro e.
      simpl.
      unfold rlift.
      assert (H':= rmod_hom_rmkl (app (type_mor R s) (type_mor R t))).
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
      unfold rlift.
      assert (H':= rmod_hom_rmkl (abs (type_mor R t) (type_mor R s))).
      simpl in *.
      rewrite <- H'.
      apply f_equal.
      rew (rklkl R).
      rew (rklkl R).
      apply (rkl_eq R).
      simpl.
      intros t0 z.
      rew (retakl R).
      rew (retakl R).
      destruct z as [t0 z];
      simpl.
      destruct z as [t0 z | ];
      simpl; auto.
      unfold rlift;
      rew (retakl R).
      
      rewrite IHy.
      clear IHy.
      generalize (type_arrow_dist R t t).
      intro e.
      simpl.
      unfold rlift.
      assert (H':= rmod_hom_rmkl (rec (type_mor R t))).
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


Lemma init_subst V t (y : PCF V t) W (f : SM_ipo _ V ---> PCFE W):
      init (y >>= f) = 
        rkleisli (RMonad_struct := R) 
           (SM_ind (V:= retype (fun t => type_mor R t)  V) 
                   (W:= R (retype (fun t => type_mor R t)  W))
              (fun t v => match v with 
                          | ctype t p => init (f t p)
                          end)) _ (init y).
Proof.
  intros V t y.
  induction y;
  simpl; 
  intros.
  
  rerew (rmhom_rmkl (bottom (type_mor R t) 
            (PCFPO_rep_struct := R))).
  
  destruct c.
  simpl. intros.
  rerew (rmhom_rmkl (nats n (PCFPO_rep_struct := R))).

  simpl. intros.
  rerew (rmhom_rmkl (tttt (PCFPO_rep_struct := R))).
  
  simpl. intros.
  rerew (rmhom_rmkl (ffff (PCFPO_rep_struct := R))).
  
  simpl in *. 
  intros.
  generalize (eq_sym (type_arrow_dist R Nat Nat)).
  intro e.
  generalize (Succ (PCFPO_rep_struct := R)).
  generalize e.
  rewrite e.
  intros.
  rewrite (UIP_refl _ _ e0).
  simpl.
  rerew (rmhom_rmkl m).
  
  simpl. intros.
  generalize (eq_sym (type_arrow_dist R Nat Nat)).
  generalize (Pred (PCFPO_rep_struct := R)).
  rewrite <- type_arrow_dist.
  intros m e.
  rewrite (UIP_refl _ _ e).
  simpl.
  rerew (rmhom_rmkl m).
  
  simpl. intros.
  generalize (eq_sym (type_arrow_dist R Nat Bool)).
  generalize (Zero (PCFPO_rep_struct := R)).
  rewrite <- type_arrow_dist.
  intros m e.
  rewrite (UIP_refl _ _ e).
  simpl.
  rerew (rmhom_rmkl m).
  
  simpl. intros.
  generalize (eq_sym (arrow_distrib4 
         (type_arrow_dist R) Bool Nat Nat Nat)).
  generalize (CondN (PCFPO_rep_struct := R)).       
  do 3 rewrite <- type_arrow_dist.
  intros m e.
  rewrite (UIP_refl _ _ e).
  simpl.
  rerew (rmhom_rmkl m).
  
  simpl. intros.
  generalize (eq_sym (arrow_distrib4 
         (type_arrow_dist R) Bool Bool Bool Bool)).
  generalize (CondB (PCFPO_rep_struct := R)).       
  do 3 rewrite <- type_arrow_dist.
  intros m e.
  rewrite (UIP_refl _ _ e).
  simpl.
  rerew (rmhom_rmkl m).
  
  simpl. intros.
  rew (retakl R).
  
  simpl; intros.
  rewrite IHy1.
  rewrite IHy2.
  clear IHy1 IHy2.
  generalize (type_arrow_dist R s t).
  intro e.
  assert (H:=rmhom_rmkl (app (type_mor R s) (type_mor R t) 
              (PCFPO_rep_struct := R))).
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
  assert (H := IHy _ (sshift (P:=PCFEM) t f)).
  simpl in *.
  rerew (rmhom_rmkl (abs (type_mor R t) (type_mor R s) 
         (PCFPO_rep_struct := R))).
  apply f_equal.
  assert (H1:=rlift_rkleisli (M:=R)).
  simpl in H1.
  rewrite H1.
  transitivity 
( (rlift R (a:=retype (fun t0 : TY => type_mor R t0) (opt t W))
   (b:=opt (type_mor R t) (retype (fun t0 : TY => type_mor R t0) W)) 
            (@der_comm _ _ _ _ _ )) (type_mor R s) 
      (init (y >>= sshift_ (P:=PCFEM) (W:=W) f))).
  repeat apply f_equal.
  apply subst_eq.
  intros.
  rewrite shift_shift. 
  auto.
  
  rewrite H.
  simpl.
  rew (rkleisli_rlift (M:=R)).
  apply (rkl_eq R).
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
  simpl in H.
  rewrite H.
  rew (rlift_rlift R).
  apply (rlift_eq R).
  simpl.
  intros t1 y.
  destruct y;
  auto.
  
  rew (rlift_rweta R).

  simpl; intros.
  rewrite IHy.
  clear IHy.
  generalize (type_arrow_dist R t t).
  intro e.
  rerew (rmhom_rmkl (rec (type_mor R t) (PCFPO_rep_struct := R))).
  apply f_equal.
  simpl.
  generalize dependent e.
  rewrite <- type_arrow_dist.
  intro e.
  rewrite (UIP_refl _ _ e).
  simpl.
  auto.
Qed.

Ltac eq_elim := match goal with
      | [ H : ?a = ?a |- _ ] => rewrite (UIP_refl _ _ H)
      | [ H : _ = _ |- _ ] => destruct H end.

Lemma double_eq_rect A (t : A) P (y : P t) s 
      (e: t = s) (e': s = t) :
   eq_rect s P (eq_rect t P y _ e) _ e' = y.
Proof.
  intros; repeat eq_elim; simpl; auto.
Qed.
   
Lemma double_eq_rect_one A (t : A) P (y : P t) s r 
      (e: t = s) (e': s = r) (e'': t = r) :
   eq_rect s P (eq_rect t P y _ e) _ e' = 
    eq_rect t P y _ e''.
Proof.
  intros; repeat eq_elim; auto.
Qed.


Lemma eq_eq_rect A (z : A) (P : A -> Type) 
       (f g : P z) (y : A) (e : z = y):
   f = g -> eq_rect z P f y e = eq_rect z P g y e.
Proof.
  intros; subst; auto.
Qed.


Lemma init_eval V t (v v' : PCF V t) :
     eval v v' -> init v <<< init v'.
Proof.
  intros V t v v' H.
  induction H.
  unfold substar.
  assert (H3:= beta_red (PCFPO_rep_struct := R)).

  assert (H2 := H3 _ _ _ (rlift R 
      (a:=retype (fun t0 : TY => type_mor R t0) (opt s V))
         (b:=opt (type_mor R s) (retype (fun t0 : TY => type_mor R t0) V))
         (@der_comm _ _ _ _ _) (type_mor R t) (init M))).
  assert (H4:=H2 (init N)).
  simpl in *.
  generalize (eq_sym (type_arrow_dist R s t)).
  rewrite type_arrow_dist.
  intro e.
  rewrite (UIP_refl _ _ e).
  simpl.
  apply (IRel_eq_r H4).
  
  assert (H':=init_subst M 
      (SM_ind (V:=(opt s V))(W:=PCFEM V)
  ((fun (t0 : TY) (x0 : opt s V t0) =>
    match x0 in (opt _ _ r) return (PCF V r) with
    | some t1 v0 => Var (V:=V) (t:=t1) v0
    | none => N
    end)))).
  simpl in H'.
  apply (eq_trans_2 H').
  unfold Rsubstar.
  rew (rlift_rkleisli (M:=R)).
  apply (rkl_eq R).
  simpl.
  intros t0 z;
  destruct z as [t0 z];
  simpl.
  destruct z as [t0 z | ];
  simpl; auto.
 
  simpl.
  assert (H:=CondN_t (PCFPO_rep_struct := R)
              (init n) (init m)).
  apply (IRel_trans_2 H).
  clear H.
  apply IRel_eq.
  apply f_equal.
  simpl in *.
  apply (injective_projections);
  simpl; auto.
  generalize (eq_sym (arrow_distrib4 
            (type_arrow_dist R) Bool Nat Nat Nat)).
  intro e.
  assert (H:=double_eq_rect_one 
      (P:=fun t => R (retype (fun t1 => type_mor R t1) V) t)
      ((CondN (retype (fun t1 : TY => type_mor R t1) V)) tt)
              e 
            (type_arrow_dist R Bool (Nat ~> Nat ~> Nat))).
  assert (H':type_mor R Bool ~~>
            type_mor R Nat ~~> type_mor R Nat ~~> type_mor R Nat =
            type_mor R Bool ~~> type_mor R (Nat ~> Nat ~> Nat)).
  do 2 rewrite type_arrow_dist. auto.
  assert (H2:= H H').
  clear H.
  simpl in *.
  
transitivity (eq_rect (type_mor R (Nat ~> Nat))
  (fun t1 : type_type R => (R (retype (fun t2 : TY => type_mor R t2) V)) t1)
  (((app (type_mor R Nat) (type_mor R (Nat ~> Nat)))
      (retype (fun t2 : TY => type_mor R t2) V))
     (eq_rect (type_mor R (Nat ~> Nat ~> Nat))
        (fun t1 : type_type R =>
         (R (retype (fun t2 : TY => type_mor R t2) V)) t1)
        (((app (type_mor R Bool) (type_mor R (Nat ~> Nat ~> Nat)))
            (retype (fun t2 : TY => type_mor R t2) V))
           (

eq_rect
       (type_mor R Bool ~~>
        type_mor R Nat ~~> type_mor R Nat ~~> type_mor R Nat)
       (fun t : type_type R =>
        (R (retype (fun t1 : TY => type_mor R t1) V)) t)
       ((CondN (retype (fun t1 : TY => type_mor R t1) V)) tt)
       (type_mor R Bool ~~> type_mor R (Nat ~> Nat ~> Nat)) H'

,
           (tttt (retype (fun t2 : TY => type_mor R t2) V)) tt))
        (type_mor R Nat ~~> type_mor R (Nat ~> Nat))
        (type_arrow_dist R Nat (Nat ~> Nat)), init n))
  (type_mor R Nat ~~> type_mor R Nat) (type_arrow_dist R Nat Nat)
).
  apply eq_eq_rect.
  apply f_equal.
  simpl.
  apply (injective_projections);
  simpl; auto.
  apply eq_eq_rect.
  apply f_equal.
  simpl.
  apply (injective_projections);
  simpl; auto.
  clear H2.
  generalize H'.
  rewrite type_arrow_dist.
  rewrite type_arrow_dist.
  intro H'0.
  rewrite (UIP_refl _ _ H'0).
  simpl.
  auto.
  
  simpl.
  assert (H:=CondN_f (PCFPO_rep_struct := R)
              (init n) (init m)).
  apply (IRel_trans_2 H).
  clear H.
  apply IRel_eq.
  apply f_equal.
  simpl in *.
  apply (injective_projections);
  simpl; auto.
  generalize (eq_sym (arrow_distrib4 
            (type_arrow_dist R) Bool Nat Nat Nat)).
  intro e.
  assert (H:=double_eq_rect_one 
      (P:=fun t => R (retype (fun t1 => type_mor R t1) V) t)
      ((CondN (retype (fun t1 : TY => type_mor R t1) V)) tt)
              e 
            (type_arrow_dist R Bool (Nat ~> Nat ~> Nat))).
  assert (H':type_mor R Bool ~~>
            type_mor R Nat ~~> type_mor R Nat ~~> type_mor R Nat =
            type_mor R Bool ~~> type_mor R (Nat ~> Nat ~> Nat)).
  do 2 rewrite type_arrow_dist. auto.
  assert (H2:= H H').
  clear H.
  simpl in *.
  
transitivity (eq_rect (type_mor R (Nat ~> Nat))
  (fun t1 : type_type R => (R (retype (fun t2 : TY => type_mor R t2) V)) t1)
  (((app (type_mor R Nat) (type_mor R (Nat ~> Nat)))
      (retype (fun t2 : TY => type_mor R t2) V))
     (eq_rect (type_mor R (Nat ~> Nat ~> Nat))
        (fun t1 : type_type R =>
         (R (retype (fun t2 : TY => type_mor R t2) V)) t1)
        (((app (type_mor R Bool) (type_mor R (Nat ~> Nat ~> Nat)))
            (retype (fun t2 : TY => type_mor R t2) V))
           (

eq_rect
       (type_mor R Bool ~~>
        type_mor R Nat ~~> type_mor R Nat ~~> type_mor R Nat)
       (fun t : type_type R =>
        (R (retype (fun t1 : TY => type_mor R t1) V)) t)
       ((CondN (retype (fun t1 : TY => type_mor R t1) V)) tt)
       (type_mor R Bool ~~> type_mor R (Nat ~> Nat ~> Nat)) H'

,
           (ffff (retype (fun t2 : TY => type_mor R t2) V)) tt))
        (type_mor R Nat ~~> type_mor R (Nat ~> Nat))
        (type_arrow_dist R Nat (Nat ~> Nat)), init n))
  (type_mor R Nat ~~> type_mor R Nat) (type_arrow_dist R Nat Nat)
).
  apply eq_eq_rect.
  apply f_equal.
  simpl.
  apply (injective_projections);
  simpl; auto.
  apply eq_eq_rect.
  apply f_equal.
  simpl.
  apply (injective_projections);
  simpl; auto.
  clear H2.
  generalize H'.
  rewrite type_arrow_dist.
  rewrite type_arrow_dist.
  intro H'0.
  rewrite (UIP_refl _ _ H'0).
  simpl.
  auto.
  
  simpl.
  assert (H:=CondB_t (PCFPO_rep_struct := R)
              (init u) (init v)).
  apply (IRel_trans_2 H).
  clear H.
  apply IRel_eq.
  apply f_equal.
  simpl in *.
  apply (injective_projections);
  simpl; auto.
  generalize (eq_sym
                    (arrow_distrib4 (Uar:=PCF.arrow)
               (U'ar:=type_arrow (p:=R)) (g:=type_mor R)
                (type_arrow_dist R) Bool Bool Bool Bool)).
  intro e.
  assert (H:=double_eq_rect_one 
      (P:=fun t => R (retype (fun t1 => type_mor R t1) V) t)
      ((CondB (retype (fun t1 : TY => type_mor R t1) V)) tt)
              e 
            (type_arrow_dist R Bool (Bool ~> Bool ~> Bool))).
  assert (H':type_mor R Bool ~~>
            type_mor R Bool ~~> type_mor R Bool ~~> type_mor R Bool =
            type_mor R Bool ~~> type_mor R (Bool ~> Bool ~> Bool)).
  do 2 rewrite type_arrow_dist. auto.
  assert (H2:= H H').
  clear H.
  simpl in *.
  
transitivity (
eq_rect (type_mor R (Bool ~> Bool))
  (fun t1 : type_type R => (R (retype (fun t2 : TY => type_mor R t2) V)) t1)
  (((app (type_mor R Bool) (type_mor R (Bool ~> Bool)))
      (retype (fun t2 : TY => type_mor R t2) V))
     (eq_rect (type_mor R (Bool ~> Bool ~> Bool))
        (fun t1 : type_type R =>
         (R (retype (fun t2 : TY => type_mor R t2) V)) t1)
        (((app (type_mor R Bool) (type_mor R (Bool ~> Bool ~> Bool)))
            (retype (fun t2 : TY => type_mor R t2) V))
           (
eq_rect
       (type_mor R Bool ~~>
        type_mor R Bool ~~> type_mor R Bool ~~> type_mor R Bool)
       (fun t : type_type R =>
        (R (retype (fun t1 : TY => type_mor R t1) V)) t)
       ((CondB (retype (fun t1 : TY => type_mor R t1) V)) tt)
       (type_mor R Bool ~~> type_mor R (Bool ~> Bool ~> Bool)) H'
,
           (tttt (retype (fun t2 : TY => type_mor R t2) V)) tt))
        (type_mor R Bool ~~> type_mor R (Bool ~> Bool))
        (type_arrow_dist R Bool (Bool ~> Bool)), init u))
  (type_mor R Bool ~~> type_mor R Bool) (type_arrow_dist R Bool Bool)
).
  apply eq_eq_rect.
  apply f_equal.
  simpl.
  apply (injective_projections);
  simpl; auto.
  apply eq_eq_rect.
  apply f_equal.
  simpl.
  apply (injective_projections);
  simpl; auto.
  clear H2.
  generalize H'.
  rewrite type_arrow_dist.
  rewrite type_arrow_dist.
  intro H'0.
  rewrite (UIP_refl _ _ H'0).
  simpl.
  auto.

  simpl.
  assert (H:=CondB_f (PCFPO_rep_struct := R)
              (init u) (init v)).
  apply (IRel_trans_2 H).
  clear H.
  apply IRel_eq.
  apply f_equal.
  simpl in *.
  apply (injective_projections);
  simpl; auto.
  generalize (eq_sym
                    (arrow_distrib4 (Uar:=PCF.arrow)
               (U'ar:=type_arrow (p:=R)) (g:=type_mor R)
                (type_arrow_dist R) Bool Bool Bool Bool)).
  intro e.
  assert (H:=double_eq_rect_one 
      (P:=fun t => R (retype (fun t1 => type_mor R t1) V) t)
      ((CondB (retype (fun t1 : TY => type_mor R t1) V)) tt)
              e 
            (type_arrow_dist R Bool (Bool ~> Bool ~> Bool))).
  assert (H':type_mor R Bool ~~>
            type_mor R Bool ~~> type_mor R Bool ~~> type_mor R Bool =
            type_mor R Bool ~~> type_mor R (Bool ~> Bool ~> Bool)).
  do 2 rewrite type_arrow_dist. auto.
  assert (H2:= H H').
  clear H.
  simpl in *.
  
transitivity (
eq_rect (type_mor R (Bool ~> Bool))
  (fun t1 : type_type R => (R (retype (fun t2 : TY => type_mor R t2) V)) t1)
  (((app (type_mor R Bool) (type_mor R (Bool ~> Bool)))
      (retype (fun t2 : TY => type_mor R t2) V))
     (eq_rect (type_mor R (Bool ~> Bool ~> Bool))
        (fun t1 : type_type R =>
         (R (retype (fun t2 : TY => type_mor R t2) V)) t1)
        (((app (type_mor R Bool) (type_mor R (Bool ~> Bool ~> Bool)))
            (retype (fun t2 : TY => type_mor R t2) V))
           (
eq_rect
       (type_mor R Bool ~~>
        type_mor R Bool ~~> type_mor R Bool ~~> type_mor R Bool)
       (fun t : type_type R =>
        (R (retype (fun t1 : TY => type_mor R t1) V)) t)
       ((CondB (retype (fun t1 : TY => type_mor R t1) V)) tt)
       (type_mor R Bool ~~> type_mor R (Bool ~> Bool ~> Bool)) H'
,
           (ffff (retype (fun t2 : TY => type_mor R t2) V)) tt))
        (type_mor R Bool ~~> type_mor R (Bool ~> Bool))
        (type_arrow_dist R Bool (Bool ~> Bool)), init u))
  (type_mor R Bool ~~> type_mor R Bool) (type_arrow_dist R Bool Bool)
).
  apply eq_eq_rect.
  apply f_equal.
  simpl.
  apply (injective_projections);
  simpl; auto.
  apply eq_eq_rect.
  apply f_equal.
  simpl.
  apply (injective_projections);
  simpl; auto.
  clear H2.
  generalize H'.
  rewrite type_arrow_dist.
  rewrite type_arrow_dist.
  intro H'0.
  rewrite (UIP_refl _ _ H'0).
  simpl.
  auto.


  (*

  assert (H:=CondN_f (PCFPO_rep_struct := R)).
  simpl in *.
  generalize (eq_sym (arrow_distrib4 
            (type_arrow_dist R) Bool Nat Nat Nat)).
  do 3 rewrite type_arrow_dist.
  intro e.
  rewrite (UIP_refl _ _ e).
  simpl.
  apply H.
  
  assert (H:=CondB_t (PCFPO_rep_struct := R)).
  simpl in *.
  generalize (eq_sym (arrow_distrib4 
            (type_arrow_dist R) Bool Bool Bool Bool)).
  do 3 rewrite type_arrow_dist.
  intro e.
  rewrite (UIP_refl _ _ e).
  simpl.
  apply H.
  
  assert (H:=CondB_f (PCFPO_rep_struct := R)).
  simpl in *.
  generalize (eq_sym (arrow_distrib4 
            (type_arrow_dist R) Bool Bool Bool Bool)).
  do 3 rewrite type_arrow_dist.
  intro e.
  rewrite (UIP_refl _ _ e).
  simpl.
  apply H.
*)
  assert (H:=Succ_red (PCFPO_rep_struct := R)
           (retype (fun t => type_mor R t) V) n).
  simpl in *.
  apply (IRel_trans_2 H).
  clear H.
  apply IRel_eq.
  apply f_equal.
  rewrite double_eq_rect.
  auto.
    
  assert (H:=Zero_t (PCFPO_rep_struct := R)
           (retype (fun t => type_mor R t) V)).
  simpl in *.
  apply (IRel_trans_2 H).
  clear H.
  apply IRel_eq.
  apply f_equal.
  rewrite double_eq_rect.
  auto.
  
  assert (H:=Zero_f (PCFPO_rep_struct := R)
           (retype (fun t => type_mor R t) V)n).
  simpl in *.
  apply (IRel_trans_2 H).
  clear H.
  apply IRel_eq.
  apply f_equal.
  rewrite double_eq_rect.
  auto.

  assert (H:=Pred_Succ (PCFPO_rep_struct := R)
      (retype (fun t => type_mor R t) V)n).
  simpl in *.
  apply (IRel_trans_2 H).
  clear H.
  apply IRel_eq.
  apply f_equal.
  rewrite double_eq_rect.
  rewrite double_eq_rect.
  auto.

    
  assert (H:=Pred_Z (PCFPO_rep_struct := R)
       (retype (fun t => type_mor R t) V)).
  simpl in *.
  apply (IRel_trans_2 H).
  clear H.
  apply IRel_eq.
  apply f_equal.
  rewrite double_eq_rect.
  auto.

  simpl.
  
  assert (H:=Rec_A (PCFPO_rep_struct := R)
        (V:=retype (fun t => type_mor R t) V)
        (t:=type_mor R t) (eq_rect (type_mor R (t ~> t))
       (fun t1 : type_type R =>
        (R (retype (fun t2 : TY => type_mor R t2) V)) t1) (init g)
       (type_mor R t ~~> type_mor R t) (type_arrow_dist R t t))).
  auto.
Qed.

Lemma eq_rect_rel T (V : IPO T) (r s : T)(p:r = s)
   (y z : V r) : y <<< z -> 
     eq_rect r V y _ p <<< eq_rect r V z _ p.
Proof.
  intros; subst; auto.
Qed.

Lemma init_eval_star V t (y z : PCF V t) :
  eval_star y z -> init y <<< init z.
Proof.
  intros V t y z H.
  induction H.
  apply init_eval;
  auto.
  simpl.
  apply (PO_mor_monotone 
  (app (PCFPO_rep_struct := R) (type_mor R s)  
         (type_mor R t) 
         (retype (fun t => type_mor R t) V))).
  simpl in *.
  constructor.
  apply (eq_rect_rel (type_arrow_dist R s t) IHpropag).
  reflexivity.
  
  simpl.
  apply (PO_mor_monotone 
  (app (PCFPO_rep_struct := R) (type_mor R s)  
         (type_mor R t) 
         (retype (fun t => type_mor R t) V))).
  simpl in *.
  constructor.
  simpl. 
  assert (H': init M <<< init M) 
       by reflexivity.
  apply (eq_rect_rel (type_arrow_dist R s t) H').
  auto.
  
  simpl.
  generalize (eq_sym (type_arrow_dist R s t)).
  rewrite type_arrow_dist.
  intro e.
  rewrite (UIP_refl _ _ e).
  simpl.
  apply (PO_mor_monotone 
  (abs (PCFPO_rep_struct := R) (type_mor R s)  
         (type_mor R t) 
         (retype (fun t => type_mor R t) V))).
  simpl.
  apply (rlift R (@der_comm _ _ (fun t0 => type_mor R t0) _ _ )).
  auto.
  
  simpl.
  apply (PO_mor_monotone 
  (rec (PCFPO_rep_struct := R) (type_mor R t)  
         (retype (fun t => type_mor R t) V))).
  apply (eq_rect_rel (type_arrow_dist R t t) IHpropag).
Qed.

Lemma init_mono c t (y z : PCFE c t):
   y <<< z -> init y <<< init z.
Proof.
  intros c t y z H.
  induction H.
  reflexivity.
  transitivity (init y);
  auto.
  apply init_eval_star;
  auto.
Qed.

Obligation Tactic := idtac.

Program Instance init_car_pos :
forall c : TY -> Type,
ipo_mor_struct 
  (a:=retype_ipo (fun t : TY => type_mor R t) (PCFE c))
  (b:=R (retype (fun t : TY => type_mor R t) c))
  (fun t y => match y with
     | ctype _ p => init  p
     end).
Next Obligation.
Proof.
  intros.
  unfold Proper;
  red.
  simpl.
  intros y z H.
  induction H.
  apply init_mono;
  auto.
Qed.


Definition init_c:
(forall c : ITYPE TY,
  (RETYPE_PO (fun t : TY => type_mor R t)) (PCFEM c) --->
  R ((RETYPE (fun t : TY => type_mor R t)) c)) :=
  fun c => Build_ipo_mor (init_car_pos c).

Obligation Tactic := idtac.

Program Instance init_rmon_s:
  gen_RMonad_Hom_struct (P:=PCFEM) (Q:=R)
    (G1:=RETYPE (fun t => type_mor R t))
    (G2:=RETYPE_PO (fun t => type_mor R t))
    (NNNT1 (fun t => type_mor R t)) init_c.
Next Obligation.
Proof.
  simpl.
  intros c t z.
  destruct z as [t z];
  simpl.
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros V W f t z.
  destruct z as [t z];
  simpl.
  assert (H:=init_subst z f).
  simpl in *.
  transitivity
  ((rkleisli (RMonad_struct := R)(a:=retype (fun t : TY => type_mor R t) V)
       (b:=retype (fun t : TY => type_mor R t) W)
       (SM_ind (V:=retype (fun t : TY => type_mor R t) V)
          (W:=R (retype (fun t : TY => type_mor R t) W))
          (fun (t : type_type R)
             (v : retype (fun t0 : TY => type_mor R t0) V t) =>
           match
             v in (retype _ _ t0)
             return ((R (retype (fun t1 : TY => type_mor R t1) W)) t0)
           with
           | ctype t0 p => init (f t0 p)
           end))) (type_mor R t) (init z)).
           auto.
  apply (rkl_eq R).
  simpl.
  clear dependent z.
  clear t.
  intros t z.
  destruct z as [t z];
  simpl.
  auto.
Qed.

Definition initM : gen_RMonad_Hom PCFEM R
    (G1:=RETYPE (fun t => type_mor R t))
    (G2:=RETYPE_PO (fun t => type_mor R t))
    (NNNT1 (fun t => type_mor R t)) :=
Build_gen_RMonad_Hom init_rmon_s.

Hint Resolve double_eq_rect.

Obligation Tactic := simpl; intros; repeat elim_unit; auto.

Program Instance initR_s : 
        PCFPO_rep_Hom_struct (P:=PCFE_rep)(R:=R) 
        (f:=fun t => type_mor R t) 
        (fun _ => eq_refl) (type_arrow_dist R) (initM).

Definition initR : PCFPO_rep_Hom PCFE_rep R := 
        Build_PCFPO_rep_Hom initR_s.


End weak_init.










