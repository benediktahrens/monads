Require Export CatSem.PCF_order_comp.RPCF_syntax_rep.
Require Export CatSem.PCF_order_comp.RPCF_rep_hom.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.


Section weak_init.

Variable R : PCFPO_rep.

(** the initial morphism STS -> R *)

Fixpoint init V t (v : PCF V t) : 
    R (retype (fun t0 => type_mor R t0) V) (type_mor R t) :=
  match v in PCF _ t return 
        R (retype (fun t0 => type_mor R t0) V) (type_mor R t) with
  | Var t v => rweta (RMonad_struct := R) _ _ (ctype _ v)
  | App _ _ u v => app (PCFPO_rep_struct := R) _ _ _ (init u, init v)
  | Lam _ _ v => abs (PCFPO_rep_struct := R) _ _ _ 
        (rlift R 
            (@der_comm TY (type_type R) (fun t => type_mor R t) _ V ) 
                   _ (init v))
  | Rec _ v => rec (PCFPO_rep_struct := R) _ _ (init v)
  | Bottom _  => bottom (PCFPO_rep_struct := R) _ _ tt
  | Const _ y => match y in Consts t1 return 
                    R (retype (fun t2 => type_mor R t2) V) (type_mor R t1) 
                 with
                 | Nats m => nats (PCFPO_rep_struct := R) m (retype _ V) tt
                 | succ => Succ (PCFPO_rep_struct := R) _ tt
                 | condN => CondN (PCFPO_rep_struct := R) _ tt
                 | condB => CondB (PCFPO_rep_struct := R) _ tt
                 | zero => Zero (PCFPO_rep_struct := R) _ tt
                 | ttt => tttt (PCFPO_rep_struct := R) _ tt
                 | fff => ffff (PCFPO_rep_struct := R) _ tt
                 | preds => Pred (PCFPO_rep_struct := R) _ tt
                 end
  end.


Obligation Tactic := idtac.

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
      (bottom (PCFPO_rep_struct := R) t)).
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
      assert (H':=rmod_hom_rmkl 
      (Succ (PCFPO_rep_struct := R))).
      simpl in H'; auto.
      
      unfold rlift.
      assert (H':=rmod_hom_rmkl 
      (Pred (PCFPO_rep_struct := R))).
      simpl in H'; auto.
      
      unfold rlift.
      assert (H':=rmod_hom_rmkl 
      (Zero (PCFPO_rep_struct := R))).
      simpl in H'; auto.
      
      unfold rlift.
      assert (H':=rmod_hom_rmkl 
      (CondN (PCFPO_rep_struct := R))).
      simpl in H'; auto.
      
      unfold rlift.
      assert (H':=rmod_hom_rmkl 
      (CondB (PCFPO_rep_struct := R))).
      simpl in H'; auto.
    
  assert (H:=rlift_rweta R).
  simpl in H.
  rewrite H. auto.
  
  unfold rlift; simpl.
  rewrite IHy1.
  rewrite IHy2.
  assert (H':=rmod_hom_rmkl 
      (app (PCFPO_rep_struct := R) s t)).
      simpl in H'.
  unfold rlift.
  rewrite <- H'.
  auto.

  unfold rlift.
  assert (H':=rmod_hom_rmkl 
      (abs (PCFPO_rep_struct := R) t s)).
      simpl in H'.
  rewrite <- H'.
  apply f_equal.
  rewrite IHy.
  unfold rlift.
  simpl.
  rew (rklkl R).
  rew (rklkl R).
  simpl.
  apply (rkl_eq R).
  simpl.
  clear dependent y.
  intros r z.
  destruct z as [r z];
  simpl.
  assert (H2:=retakl R).
  simpl in H2.
  rewrite H2.
  rewrite H2.
  simpl.
  
  destruct z as [r z | ];
  simpl; auto.
  
  assert (Ht:=rlift_rweta R).
  simpl in Ht.
  rewrite Ht. auto.
  
  rewrite IHy.
  assert (H':=rmod_hom_rmkl 
      (rec (PCFPO_rep_struct := R) t)).
      simpl in H'.
  unfold rlift.
  rewrite <- H'.
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
  induction y.
  simpl. intros.
  rerew (rmhom_rmkl (bottom t (PCFPO_rep_struct := R))).
  
  destruct c.
  simpl. intros.
  rerew (rmhom_rmkl (nats n (PCFPO_rep_struct := R))).

  simpl. intros.
  rerew (rmhom_rmkl (tttt (PCFPO_rep_struct := R))).
  
  simpl. intros.
  rerew (rmhom_rmkl (ffff (PCFPO_rep_struct := R))).
  
  simpl. intros.
  rerew (rmhom_rmkl (Succ (PCFPO_rep_struct := R))).
  
  simpl. intros.
  rerew (rmhom_rmkl (Pred (PCFPO_rep_struct := R))).
  
  simpl. intros.
  rerew (rmhom_rmkl (Zero (PCFPO_rep_struct := R))).
  
  simpl. intros.
  rerew (rmhom_rmkl (CondN (PCFPO_rep_struct := R))).
  
  simpl. intros.
  rerew (rmhom_rmkl (CondB (PCFPO_rep_struct := R))).
  
  simpl. intros.
  rew (retakl R).
  
  simpl; intros W f.
  rewrite IHy1.
  rewrite IHy2.
  rerew (rmhom_rmkl (app s t (PCFPO_rep_struct := R))).
  
  simpl; intros W f. 
  assert (H := IHy _ (sshift (P:=PCFEM) t f)).
  simpl in *.
  rerew (rmhom_rmkl (abs t s (PCFPO_rep_struct := R))).
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
  
  simpl; intros W f.
  rewrite IHy.
  rerew (rmhom_rmkl (rec t (PCFPO_rep_struct := R))).
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
  apply (IRel_eq_r H4).
  unfold Rsubstar.
  rew (rlift_rkleisli (M:=R)).
  assert (H':=init_subst M 
      (SM_ind (V:=(opt s V))(W:=PCFEM V)
  ((fun (t0 : TY) (x0 : opt s V t0) =>
    match x0 in (opt _ _ r) return (PCF V r) with
    | some t1 v0 => Var (V:=V) (t:=t1) v0
    | none => N
    end)))).
  simpl in *.
  apply (eq_trans_2 H').
  apply (rkl_eq R).
  simpl.
  intros t0 z;
  destruct z as [t0 z];
  simpl.
  opt.
 
  assert (H:=CondN_t (PCFPO_rep_struct := R)).
  simpl in *.
  apply H.

  assert (H:=CondN_f (PCFPO_rep_struct := R)).
  simpl in *.
  apply H.
  
  assert (H:=CondB_t (PCFPO_rep_struct := R)).
  simpl in *.
  apply H.
  
  assert (H:=CondB_f (PCFPO_rep_struct := R)).
  simpl in *.
  apply H.

  assert (H:=Succ_red (PCFPO_rep_struct := R)).
  simpl in *.
  apply H.
  
  assert (H:=Zero_t (PCFPO_rep_struct := R)).
  simpl in *.
  apply H.
  
  assert (H:=Zero_f (PCFPO_rep_struct := R)).
  simpl in *.
  apply H.

  assert (H:=Pred_Succ (PCFPO_rep_struct := R)).
  simpl in *.
  apply H.
  
  assert (H:=Pred_Z (PCFPO_rep_struct := R)).
  simpl in *.
  apply H.
  
  assert (H:=Rec_A (PCFPO_rep_struct := R)).
  simpl in *.
  apply H.
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
      (app (PCFPO_rep_struct := R) s t 
         (retype (fun t => type_mor R t) V))).
  simpl.
  constructor.
  auto.
  reflexivity.
  simpl.
  apply (PO_mor_monotone
      (app (PCFPO_rep_struct := R) s t 
         (retype (fun t => type_mor R t) V))).
  simpl.
  constructor.
  reflexivity.
  auto.

  simpl.
  apply (PO_mor_monotone
      (abs (PCFPO_rep_struct := R) s t 
         (retype (fun t => type_mor R t) V))).
  simpl.
  apply (rlift R (@der_comm _ _ (fun t0 => type_mor R t0) _ _ )).
  auto.
  simpl.
  apply (PO_mor_monotone
      (rec (PCFPO_rep_struct := R) t 
         (retype (fun t => type_mor R t) V))).
  simpl.
  auto.
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
  intros c t.
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


Obligation Tactic := simpl; intros; repeat elim_unit; auto.

Program Instance initR_s : 
        PCFPO_rep_Hom_struct (P:=PCFE_rep)(R:=R) 
        (f:=fun t => type_mor R t) 
        (fun _ => eq_refl) initM.

Definition initR : PCFPO_rep_Hom PCFE_rep R := 
        Build_PCFPO_rep_Hom initR_s.

End weak_init.










