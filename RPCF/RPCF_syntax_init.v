Require Import Coq.Logic.Eqdep.

Require Export CatSem.RPCF.RPCF_syntax_rep.
Require Export CatSem.RPCF.RPCF_rep_hom.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Notation "a '~>' b" := (PCF.Arrow a b) (at level 60, right associativity).
Notation "'TY'" := PCF.Sorts.
Notation "'IT'" := (ITYPE TY).
Notation "v //- f" := (@rename _ _ f _ v)(at level 42, left associativity).
Notation "y >>= f" := (@subst _ _ f _ y) (at level 42, left associativity).
Notation "a @ b" := (App a b)(at level 20, left associativity).
Notation "M '" := (Const _ M) (at level 15).

Section weak_init.

Variable R : PCFPO_rep.

(** the initial type morphism T(STS) -> T(R) *)

Fixpoint Init_Sorts_map (t : Sorts PCFE_rep) : Sorts R := 
    match t with
    | PCF.Nat => Nat R 
    | PCF.Bool => Bool R
    | u ~> v => (Init_Sorts_map u) ~~> (Init_Sorts_map v)
    end.

(*Obligation Tactic := reflexivity.*)

Implicit Arguments rweta [obC obD morC morD C D F T].

(** the initial morphism STS -> R *)

Fixpoint init V t (v : PCF V t) : 
    R (retype (fun t0 => Init_Sorts_map t0) V) (Init_Sorts_map t)  :=
  match v (*in PCF _ t return 
        R (retype (fun t0 => Init_Sorts_map t0) V) (Init_Sorts_map t)*) with
  | Var t v => rweta (*RMonad_struct := R*) R _ _ (ctype _ v)
  | u @ v => app (*PCFPO_rep_struct := R*) _ _ _ (init u, init v)
  | Lam _ _ v => abs (*PCFPO_rep_struct := R*) _ _ _ 
                  (rlift R 
                     (@der_comm TY (Sorts R) (fun t => Init_Sorts_map t) _ V ) 
                      _ (init v))
  | Rec _ v => rec (*PCFPO_rep_struct := R*) _ _ (init v) 
  | Bottom _  => bottom (*PCFPO_rep_struct := R*) _ _ tt
  | y ' => match y in Consts t1 return 
                       R (retype (fun t2 => Init_Sorts_map t2) V) (Init_Sorts_map t1) 
                 with
                 | Nats m => nats (*PCFPO_rep_struct := R*) m (*retype _ V*) _ tt
                 | succ => Succ (*retype (fun t1 : TY => _  t1) _*) _ tt
                 | condN => CondN (*retype (fun t1 : TY => _ t1) _*) _ tt
                 | condB => CondB (*retype (fun t1 : TY => _ t1) _*) _ tt
                 | zero => Zero (*retype (fun t1 : TY => _ t1) _*) _ tt
                 | ttt => tttt (*PCFPO_rep_struct := R*) _ tt
                 | fff => ffff (*PCFPO_rep_struct := R*) _ tt
                 | preds => Pred (*retype (fun t1 : TY => _ t1) _*) _ tt
                 end
  end.

(*

Program Fixpoint init V t (v : PCF V t) : 
    R (retype (fun t0 => type_mor t0) V) (type_mor t) :=
  match v in PCF _ t return 
        R (retype (fun t0 => type_mor t0) V) (type_mor t) with
  | Var t v => rweta (RMonad_struct := R) _ _ (ctype _ v)
  | App r s u v => app (PCFPO_rep_struct := R) _ _ _ 
           (eq_rect (A:=type_type R)
              _
              (fun t1 : type_type R =>
                (R (retype (fun t2 : TY => type_mor  t2) _)) t1) 
               (init u) _
               ( ( _ )), 
                         init v)
  | Lam _ _ v => 
        eq_rect (A:=type_type R) _
             (fun t1 : type_type R =>
                (R (retype (fun t2 : TY => type_mor  t2) _)) t1) 
            (abs (PCFPO_rep_struct := R) _ _ _ 
                  (rlift R 
            (@der_comm TY (type_type R) (fun t => type_mor  t) _ V ) 
                   _ (init v)))
               _ ( _ )
  | Rec _ v => rec (PCFPO_rep_struct := R) _ _ 
                  (eq_rect (A:=type_type R) _ 
                   (fun t1 : type_type R =>
                (R (retype (fun t2 : TY => type_mor  t2) _)) t1)
                 (init v) _ ( _ ))
  | Bottom _  => bottom (PCFPO_rep_struct := R) _ _ tt
  | Const _ y => match y in Consts t1 return 
                    R (retype (fun t2 => type_mor t2) V) (type_mor t1) 
                 with
                 | Nats m => nats (PCFPO_rep_struct := R) m 
                      (retype _ V) tt
                 | succ => eq_rect
           (type_mor Nat ~~> type_mor  Nat)
           (fun t1 : type_type R =>
            (R (retype (fun t2 : TY => type_mor  t2) _)) t1)
           ((Succ (retype (fun t1 : TY => type_mor  t1) _)) tt)
           (type_mor  (Nat ~> Nat))
           ( _ )
                 | condN => eq_rect
           (type_mor  Bool ~~> type_mor  Nat ~~>
            type_mor  Nat ~~> type_mor  Nat)
           (fun t1 : type_type R =>
            (R (retype (fun t2 : TY => type_mor  t2) _)) t1)
           ((CondN (retype (fun t1 : TY => type_mor  t1) _)) tt)
           (type_mor 
              (Bool ~> Nat ~> Nat ~> Nat))
           ( _ )
                 | condB => eq_rect
           (type_mor  Bool ~~> type_mor  Bool ~~> 
            type_mor  Bool ~~> type_mor  Bool)
           (fun t1 : type_type R =>
            (R (retype (fun t2 : TY => type_mor  t2) _)) t1)
           ((CondB (retype (fun t1 : TY => type_mor  t1) _)) tt)
           (type_mor 
              (Bool ~> Bool ~> Bool ~> Bool))
           ( _ )
                 | zero => eq_rect
           (type_mor  Nat ~~> type_mor  Bool)
           (fun t1 : type_type R =>
            (R (retype (fun t2 : TY => type_mor  t2) _)) t1)
           ((Zero (retype (fun t1 : TY => type_mor  t1) _)) tt)
           (type_mor  (Nat ~> Bool))
           ( _ )
                 | ttt => tttt (PCFPO_rep_struct := R) _ tt
                 | fff => ffff (PCFPO_rep_struct := R) _ tt
                 | preds => eq_rect
           (type_mor  Nat ~~> type_mor  Nat)
           (fun t1 : type_type R =>
            (R (retype (fun t2 : TY => type_mor  t2) _)) t1)
           ((Pred (retype (fun t1 : TY => type_mor  t1) _)) tt)
           (type_mor  (Nat ~> Nat))
           ( _ )
                 end
  end.
*)

(*
Print rlift.
Implicit Arguments rlift [[obC] [obD] morC morD C D F M [a] [b]].
Print rlift.
*)

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
      (bottom (PCFPO_rep_struct := R) (Init_Sorts_map t))).
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

      
      unfold rlift.
      rew (retakl R).
      
      rewrite IHy1.
      rewrite IHy2.
      clear IHy1 IHy2.
      assert (H':= rmod_hom_rmkl 
        (app (Init_Sorts_map s) (Init_Sorts_map t))).
        simpl in H'.
      unfold rlift.
      rewrite <- H'.
      simpl.
      apply f_equal.
      auto.
      
      rewrite IHy.
      clear IHy.
      simpl.
      unfold rlift.
      assert (H':= rmod_hom_rmkl 
        (abs (Init_Sorts_map t) (Init_Sorts_map s))).
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
      unfold rlift.
      assert (H':= rmod_hom_rmkl 
        (rec (Init_Sorts_map t))).
      simpl in H'.
      rewrite <- H'.
      simpl.
      apply f_equal.
      auto.
Qed.


Lemma init_subst V t (y : PCF V t) W (f : IDelta _ V ---> PCFE W):
      init (y >>= f) = 
        rkleisli (RMonad_struct := R) 
           (SM_ind (V:= retype (fun t => _ t)  V) 
                   (W:= R (retype (fun t => _ t)  W))
              (fun t v => match v with 
                          | ctype t p => init (f t p)
                          end)) _ (init y).
Proof.
  intros V t y.
  induction y;
  simpl; 
  intros.
  
  rerew (rmhom_rmkl (bottom (Init_Sorts_map t) 
            (PCFPO_rep_struct := R))).
  
  destruct c.
  simpl. intros.
  rerew (rmhom_rmkl (nats n (PCFPO_rep_struct := R))).

  simpl. intros.
  rerew (rmhom_rmkl (tttt (PCFPO_rep_struct := R))).
  
  simpl. intros.
  rerew (rmhom_rmkl (ffff (PCFPO_rep_struct := R))).
  
  simpl in *; intros.
  rerew (rmhom_rmkl (Succ (PCFPO_rep_struct := R))).
  
  simpl; intros.
  rerew (rmhom_rmkl (Pred (PCFPO_rep_struct := R))).
  
  simpl; intros.
  generalize (Zero (PCFPO_rep_struct := R)).
  intros m.
  rerew (rmhom_rmkl m).
  
  simpl. intros.
  generalize (CondN (PCFPO_rep_struct := R)).       
  simpl; intros.
  rerew (rmhom_rmkl m).
  
  simpl. intros.
  generalize (CondB (PCFPO_rep_struct := R)).       
  intros m.
  rerew (rmhom_rmkl m).
  
  simpl. intros.
  rew (retakl R).
  
  simpl; intros.
  rewrite IHy1.
  rewrite IHy2.
  clear IHy1 IHy2.
  assert (H:=rmhom_rmkl (app (Init_Sorts_map s) (Init_Sorts_map t) 
              (PCFPO_rep_struct := R))).
  simpl in H.
  rewrite <- H.
  apply f_equal.
  simpl.
  auto.
  

  simpl; intros.
  
  assert (H := IHy _ (sshift (P:=PCFEM) t f)).
  simpl in *.
  rerew (rmhom_rmkl (abs (Init_Sorts_map t) (Init_Sorts_map s) 
         (PCFPO_rep_struct := R))).
  apply f_equal.
  assert (H1:=rlift_rkleisli (M:=R)).
  simpl in H1.
  rewrite H1.
  transitivity 
( (rlift R (a:=retype (fun t0 : TY => _ t0) (opt t W))
   (b:=opt (_ t) (retype (fun t0 : TY => _ t0) W)) 
            (@der_comm _ _ _ _ _ )) (_ s) 
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
  rerew (rmhom_rmkl (rec (Init_Sorts_map t) (PCFPO_rep_struct := R))).
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
      (a:=retype (fun t0 : TY => _ t0) (opt s V))
         (b:=opt (_ s) (retype (fun t0 : TY => _ t0) V))
         (@der_comm _ _ _ _ _) (_ t) (init M))).
  assert (H4:=H2 (init N)).
  simpl in *.
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
  
  simpl.
  assert (H:=Succ_red (PCFPO_rep_struct := R)
           (retype (fun t => Init_Sorts_map t) V) n).
  simpl in *.
  apply (IRel_trans_2 H).
  clear H.
  apply IRel_eq.
  apply f_equal.
  auto.
    
  assert (H:=Zero_t (PCFPO_rep_struct := R)
           (retype (fun t => Init_Sorts_map t) V)).
  simpl in *.
  apply (IRel_trans_2 H).
  clear H.
  apply IRel_eq.
  apply f_equal.
  auto.
  
  assert (H:=Zero_f (PCFPO_rep_struct := R)
           (retype (fun t => Init_Sorts_map t) V) n).
  simpl in *.
  apply (IRel_trans_2 H).
  clear H.
  apply IRel_eq.
  apply f_equal.
  auto.

  assert (H:=Pred_Succ (PCFPO_rep_struct := R)
      (retype (fun t => Init_Sorts_map t) V)n).
  simpl in *.
  apply (IRel_trans_2 H).
  clear H.
  apply IRel_eq.
  apply f_equal.
  auto.

    
  assert (H:=Pred_Z (PCFPO_rep_struct := R)
       (retype (fun t => Init_Sorts_map t) V)).
  simpl in *.
  apply (IRel_trans_2 H).
  clear H.
  apply IRel_eq.
  apply f_equal.
  auto.

  simpl.
  assert (H:=Rec_A (PCFPO_rep_struct := R)
       (V:=retype (fun t => Init_Sorts_map t) V)).
  simpl in H.
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
  (app (PCFPO_rep_struct := R) (Init_Sorts_map s)  
         (Init_Sorts_map t) 
         (retype (fun t => Init_Sorts_map t) V))).
  simpl in *.
  constructor.
  apply IHpropag.
  reflexivity.
  
  simpl.
  apply (PO_mor_monotone 
  (app (PCFPO_rep_struct := R) (Init_Sorts_map s)  
         (Init_Sorts_map t) 
         (retype (fun t => Init_Sorts_map t) V))).
  simpl in *.
  constructor.
  simpl. 
  assert (H': init M <<< init M) 
       by reflexivity.
  apply ( H').
  auto.
  
  simpl.
  apply (PO_mor_monotone 
  (abs (PCFPO_rep_struct := R) (Init_Sorts_map s)  
         (Init_Sorts_map t) 
         (retype (fun t => Init_Sorts_map t) V))).
  simpl.
  apply (rlift R (@der_comm _ _ (fun t0 => _ t0) _ _ )).
  auto.
  
  simpl.
  apply (PO_mor_monotone 
  (rec (PCFPO_rep_struct := R) (Init_Sorts_map t)  
         (retype (fun t => Init_Sorts_map t) V))).
  apply (IHpropag).
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
  (a:=retype_ipo (fun t : TY => _ t) (PCFE c))
  (b:=R (retype (fun t : TY => _ t) c))
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
  (RETYPE_PO (fun t : TY => _ t)) (PCFEM c) --->
  R ((RETYPE (fun t : TY => _ t)) c)) :=
  fun c => Build_ipo_mor (init_car_pos c).

Obligation Tactic := idtac.

Program Instance init_rmon_s:
  colax_RMonad_Hom_struct (P:=PCFEM) (Q:=R)
    (G1:=RETYPE (fun t => _ t))
    (G2:=RETYPE_PO (fun t => _ t))
    (RT_NT (fun t => _)) init_c.
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
  ((rkleisli (RMonad_struct := R)(a:=retype (fun t : TY => _ t) V)
       (b:=retype (fun t : TY => _ t) W)
       (SM_ind (V:=retype (fun t : TY => _ t) V)
          (W:=R (retype (fun t : TY => _ t) W))
          (fun (t : _ R)
             (v : retype (fun t0 : TY => _ t0) V t) =>
           match
             v in (retype _ _ t0)
             return ((R (retype (fun t1 : TY => Init_Sorts_map t1) W)) t0)
           with
           | ctype t0 p => init (f t0 p)
           end))) (_ t) (init z)).
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

Definition initM : colax_RMonad_Hom PCFEM R
    (G1:=RETYPE (fun t => _ t))
    (G2:=RETYPE_PO (fun t => _ t))
    (RT_NT (fun t => _ t)) :=
  Build_colax_RMonad_Hom init_rmon_s.

Hint Resolve double_eq_rect.

Obligation Tactic := unfold
                       CondB_hom' ,
                       CondN_hom' ,
                       Pred_hom'  ,
                       Zero_hom'  ,
                       Succ_hom'  ,
                       fff_hom'   ,
                       ttt_hom'   ,
                       bottom_hom',
                       nats_hom'  , 
                       app_hom'   ,
                       rec_hom'   , 
                       abs_hom'  ;
   simpl; intros; repeat elim_unit; auto.

Program Instance initR_s : 
        PCFPO_rep_Hom_struct (P:=PCFE_rep)(R:=R) 
        (Sorts_map:=fun t => _ t) 
        (fun _ _ => eq_refl) eq_refl eq_refl (initM).

Definition initR : PCFPO_rep_Hom PCFE_rep R := 
        Build_PCFPO_rep_Hom initR_s.

End weak_init.










