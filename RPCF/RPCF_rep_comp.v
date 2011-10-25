Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Eqdep.

Require Export CatSem.RPCF.RPCF_rep_hom.
Require Export CatSem.CAT.rmonad_gen_comp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Ltac gendep H := generalize dependent H.

Section rep_comp.

Variables P Q R : PCFPO_rep.
Variable M : PCFPO_rep_Hom P Q.
Variable N : PCFPO_rep_Hom Q R.
(*
Lemma functy t : 
   tcomp N (tcomp M (type_mor P t)) = 
                 type_mor R t.
Proof.
  intros.
  simpl.
  rewrite (ttriag M).
  rewrite (ttriag N).
  auto.
Qed.

Lemma comp_arrow_dist:
forall u v : type_type P,
  (fun t : type_type P => tcomp N (tcomp M t)) (u ~~> v) =
  (fun t : type_type P => tcomp N (tcomp M t)) u ~~>
  (fun t : type_type P => tcomp N (tcomp M t)) v.
Proof.
  simpl.
  intros.
  rewrite tcomp_arrow.
  rewrite tcomp_arrow.
  reflexivity.
Qed.
*)


Lemma SM_ind_comp T (V : ITYPE T) (W : IPO T) (Z : IPO T)
        (f: forall t, V t -> W t) (g: W ---> Z) :
    SM_ind f ;; g == SM_ind (fun t z => g t (f t z)).
Proof.
  simpl.
  auto.
Qed.

Lemma SM_ipo_mor_comp T (V : ITYPE T) (W : ITYPE T) 
        (f: V ---> W)(Z : IPO T) (g: sm_ipo W ---> Z) :
    sm_ipo_mor f ;; g == SM_ind (fun t z => g t (f t z)).
Proof.
  simpl.
  auto.
Qed.


Lemma eq_eq_rect A (z : A) (P : A -> Type) 
       (f g : P z) (y : A) (e : z = y):
   f = g -> eq_rect z P f y e = eq_rect z P g y e.
Proof.
  intros.
  subst.
  auto.
Qed.


Obligation Tactic := idtac.

Lemma exsimio:
forall u v : type_type P,
  (fun t : type_type P => tcomp N (tcomp M t)) (u ~~> v) =
  (fun t : type_type P => tcomp N (tcomp M t)) u ~~>
  (fun t : type_type P => tcomp N (tcomp M t)) v.
Proof.
  simpl; intros.
  
(*  
  assert (H:=tcomp_arrow M u v).
  assert (H':=tcomp_arrow N (tcomp M u) (tcomp M v)).
*)
  
  destruct (tcomp_arrow N (tcomp M u) (tcomp M v)).
  destruct (tcomp_arrow M u v).
  reflexivity.
Defined.
(*
Print exsimio.
*)
Lemma exsimio_bool:
(fun t : type_type P => tcomp N (tcomp M t)) (type_bool P) = type_bool R.
Proof.
  destruct (tcomp_bool N).
  destruct (tcomp_bool M).
  reflexivity.
Qed.

Lemma exsimio_nat:
(fun t : type_type P => tcomp N (tcomp M t)) (type_nat P) = type_nat R.
Proof.
  destruct (tcomp_nat N).
  destruct (tcomp_nat M).
  reflexivity.
Qed.


Program Instance Rep_comp_struct : 
  PCFPO_rep_Hom_struct (P:=P) (R:=R)
        (f := fun t => tcomp N (tcomp M t)) 
        exsimio
        exsimio_bool
        exsimio_nat
      (*comp_arrow_commute (ttriag M) (ttriag N)*)
      (*comp_arrow_dist (tcomp_arrow M) (tcomp_arrow N)*)
      (RMon_comp M N).
Obligation 12.
Proof. (* abs 2 *)
  unfold abs_hom2';
  simpl.
  intros u v c y.
  assert (HM:=abs_hom2 (u:=u)(v:=v) 
        (PCFPO_rep_Hom_struct :=M) (*c:=c)y*)).
  assert (HN:=abs_hom2 (u:=tcomp M u)
                      (v:=tcomp M v)
          (PCFPO_rep_Hom_struct :=N)
          (*(c:=retype(fun t => tcomp M t) c)*)).
  simpl in HM ,HN.
  simpl in *.
(*

  Check eq_rect_eq.
  Check (eq_sym (exsimio u v)).

*)

  generalize (@eq_sym (type_type R) (@tcomp Q R N (@tcomp P Q M (@type_arrow P u v)))
        (@type_arrow R (@tcomp Q R N (@tcomp P Q M u))
           (@tcomp Q R N (@tcomp P Q M v))) (exsimio u v)).

(*
  generalize (eq_sym (exsimio u v)).
  
  generalize ( eq_sym (
    comp_arrow_dist (Uar:=type_arrow (p:=P)) 
      (U'ar:=type_arrow (p:=Q))
        (g:=tcomp M) (tcomp_arrow M) (g':=tcomp N) 
      (U''ar:=type_arrow (p:=R))
        (tcomp_arrow N) u v)
).
*) 
  destruct N as [gN HNarrow HNnat HNbool TN TNs].
  destruct M as [gM HMarrow HMnat HMbool TM TMs].

  clear M N.
  simpl in *.
  clear TNs.
  clear TMs.
  intro e.
  
  
  (*destruct TM.*)
  destruct P as [U Uarrow PM fP HP Prep].
  destruct Q as [U' U'arrow QM fQ HQ Qrep];
  destruct R as [U'' U''arrow RM fR HR Rrep];
  clear P Q R;
  simpl in *.
  destruct Prep as [Papp Pabs Prec tttt 
    ffff nats Succ Pred Zero CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
    propag_rec *)
    CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn 
      Pred_Z Rec_A ].
  simpl in *.
  clear Prec Papp tttt ffff nats Succ Pred Zero CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 propag_rec *)
        CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn Pred_Z
       Rec_A.
  destruct Qrep as [Qapp Qabs Qrec tttt 
      ffff nats Succ Pred Zero CondN CondB bottom
        beta_red (*propag_app1 propag_abs propag_app2 
       propag_rec*) CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn Pred_Z
        Rec_A ].
  simpl in *.
  clear Qrec Qapp tttt ffff nats Succ Pred Zero
      CondN CondB bottom
        beta_red (*propag_app1 propag_abs propag_app2 
      propag_rec*) CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn 
     Pred_Z Rec_A.
 destruct Rrep as [Rapp Rabs Rrec tttt 
      ffff nats Succ Pred Zero CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 propag_rec*)
       CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn Pred_Z
        Rec_A ].
  simpl in *.
  clear Rapp Rrec tttt ffff nats Succ Pred Zero
      CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
       propag_rec*) 
       CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn 
    Pred_Z Rec_A.

rewrite HM.

gendep e.
generalize (eq_sym (HMarrow u v)).
rewrite HMarrow.
intros.
rewrite (UIP_refl _ _ e).
simpl.
rewrite HN.
clear e.
gendep e0.
generalize (eq_sym (HNarrow (gM u) (gM v))).
rewrite HNarrow.
intros.
rewrite (UIP_refl _ _ e).
rewrite (UIP_refl _ _ e0).
simpl.

clear HN HM e e0.
assert (H:=rmod_hom_rmkl 
    (Rabs (gN (gM u)) (gN (gM v)))).
simpl in H.
unfold rlift at 1.
rewrite <- H.
apply f_equal.
fold (rlift HR).
rew (rlift_rkleisli (M:= HR)).
rew (rlift_rlift HR).
assert (H':= gen_rh_rlift TN).
assert (H2 := H' 
   (retype (fun t : U => gM t) (opt u c))
   (opt (gM u) (retype (fun t : U => gM t) c))
    (@der_comm _ _ _ _ _ )).
rewrite <- H2.
rew (rlift_rkleisli (M:=HR)).

unfold rlift.
apply (rkl_eq HR).
simpl.
intros t z.
destruct z as [t z];
simpl.
destruct z as [t z];
simpl.
destruct z as [t z | ];
simpl;
auto.
unfold rlift.
simpl.
rew (retakl HR).
Qed.
(*
Obligation 11.
Proof. (* abs *)
  simpl.
  intros u v c y.
  assert (HM:=abs_hom (u:=u)(v:=v) 
        (PCFPO_rep_Hom_struct :=M) (*c:=c)y*)).
  assert (HN:=abs_hom (u:=tcomp M u)
                      (v:=tcomp M v)
          (PCFPO_rep_Hom_struct :=N)
          (*(c:=retype(fun t => tcomp M t) c)*)).
  simpl in HM ,HN.
  
  generalize (
    comp_arrow_dist (Uar:=type_arrow (p:=P)) 
      (U'ar:=type_arrow (p:=Q))
        (g:=tcomp M) (tcomp_arrow M) (g':=tcomp N) 
      (U''ar:=type_arrow (p:=R))
        (tcomp_arrow N) u v
).
  
  destruct N as [gN HNarrow HNcommute TN TNs].
  destruct M as [gM HMarrow HMcommute TM TMs].

  clear M N.
  simpl in *.
  clear TNs.
  clear TMs.
  intro e.
  
  
  (*destruct TM.*)
  destruct P as [U Uarrow PM fP HP Prep].
  destruct Q as [U' U'arrow QM fQ HQ Qrep];
  destruct R as [U'' U''arrow RM fR HR Rrep];
  clear P Q R;
  simpl in *.
  destruct Prep as [Papp Pabs Prec tttt 
    ffff nats Succ Pred Zero CondN CondB bottom
        beta_red propag_app1 propag_abs propag_app2 
    propag_rec CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn 
      Pred_Z Rec_A ].
  simpl in *.
  clear Prec Papp tttt ffff nats Succ Pred Zero CondN CondB bottom
        beta_red propag_app1 propag_abs propag_app2 propag_rec CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn Pred_Z
        Rec_A.
  destruct Qrep as [Qapp Qabs Qrec tttt 
      ffff nats Succ Pred Zero CondN CondB bottom
        beta_red propag_app1 propag_abs propag_app2 
       propag_rec CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn Pred_Z
        Rec_A ].
  simpl in *.
  clear Qrec Qapp tttt ffff nats Succ Pred Zero
      CondN CondB bottom
        beta_red propag_app1 propag_abs propag_app2 
      propag_rec CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn 
     Pred_Z Rec_A.
 destruct Rrep as [Rapp Rabs Rrec tttt 
      ffff nats Succ Pred Zero CondN CondB bottom
        beta_red propag_app1 propag_abs propag_app2 propag_rec
       CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn Pred_Z
        Rec_A ].
  simpl in *.
  clear Rapp Rrec tttt ffff nats Succ Pred Zero
      CondN CondB bottom
        beta_red propag_app1 propag_abs propag_app2 
       propag_rec CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn 
    Pred_Z Rec_A.
Check HP.
assert (HHP:=rmod_hom_rmkl (Pabs u v)).
assert (HHQ:=rmod_hom_rmkl (Qabs (gM u) (gM v))).
assert (HHR:=rmod_hom_rmkl 
    (Rabs (gN (gM u)) (gN (gM v)))).
simpl in *.
unfold rlift at 2.
simpl.
Check sshift_rweta.
assert (r':=gen_rh_rkl TN).

rewrite <- 
  (sshift_rweta RM (u:=gN (gM u))
            (opt (gN (gM u)) 
            (retype (fun t : U => gN (gM t)) c))).
Check (ipo_comp
         (sm_ipo_mor (T:=U'') (V:=retype (fun t : U => gN (gM t)) (opt u c))
            (W:=opt (gN (gM u)) (retype (fun t : U => gN (gM t)) c)) 
(@der_comm _ _ _ _ _ ))
         (rweta (opt (gN (gM u)) (retype (fun t : U => gN (gM t)) c))
)).
rew (rlift_rlift RM).
simpl in *.
unfold rlift at 2.
simpl. Check sshift.
rewrite <- HN.
unfold rlift in *.
simpl.
Check (double_retype_1 (f:=gM)(f':=gN)(V:=opt u c)
         ;; (@der_comm _ _ _ _ _ )).
Check (double_retype_1(f:=gM)(f':=gN)(V:=c)).
Check sm_ipo_mor. Check SM_ipo_mor_comp.

assert (H:=SM_ipo_mor_comp 
 (double_retype_1 (f:=gM)(f':=gN)(V:=c))
 (rweta (RMonad_struct:=RM) _ )).

transitivity (
eq_rect (gN (gM (Uarrow u v)))
  (fun t : U'' => (RM (retype (fun t0 : U => gN (gM t0)) c)) t)
  ((rkleisli (RMonad_struct := RM)
    (a:=retype (fun t : U' => gN t) 
        (retype (fun t : U => gM t) c))
      (b:=retype (fun t : U => gN (gM t)) c)

 (SM_ind 
  (V:=retype (fun t : U' => gN t) (retype (fun t : U => gM t) c))
(W:=RM (retype (fun t : U => gN (gM t)) c))
(fun t z => rweta (RMonad_struct := RM) 
         (retype (fun t0 : U => gN (gM t0)) c) t
   (double_retype_1(f:=gM)(f':=gN)(V:=c) z))))  
(gN (gM (Uarrow u v)))
     ((TN (retype (fun t : U => gM t) c)) (gN (gM (Uarrow u v)))
        (ctype (fun t : U' => gN t) (V:=QM (retype (fun t : U => gM t) c))
           (t:=gM (Uarrow u v))
           ((TM c) (gM (Uarrow u v))
              (ctype (fun t : U => gM t) (V:=PM c) (t:=Uarrow u v)
                 (((Pabs u v) c) y)))))) (U''arrow (gN (gM u)) (gN (gM v))) e

).
apply eq_eq_rect.
apply (rkl_eq RM).
simpl.
auto.

assert (r:=rmod_hom_rmkl (Rabs (gN (gM u)) (gN (gM v)))).
simpl in r.
assert (r':=gen_rh_rkl TN).
simpl in r'.
Check (fun c c' (g : ipo_mor (sm_ipo (T:=U') c) (QM c')) => 
ipo_comp
           (ipo_comp (id_cc (fun t0 : U' => gN t0) c)
              (retype_po_mor (fun t0 : U' => gN t0) (V:=sm_ipo (T:=U') c)
                 (W:=QM c') g)) (TN c')).

assert (H:= 

clear H.

rewrite <- H.
simpl.
Check eq_rect_eq.


assert (H':=SM_ipo_mor_comp 
      (V:=retype (fun t : U' => gN t) (retype (fun t : U => gM t) c))
      (W:=sm_ipo (retype (fun t : U => gN (gM t)) c))
      (double_retype_1(f:=gM)(f':=gN)(V:=c))).
simpl in H'.
assert (H'' := H' _
      (rweta (RMonad_struct := RM) (retype (fun t => gN (gM t)) c))).
simpl in H''.
unfold ipo_comp;
simpl.
rerew (gen_rmonad_hom_rweta TM).
rew HHR.
rerew (rklkl RM).

rewrite (assoc (Cat:=ITYPE U)).
rew (rkleta  PM).

gendep e.
generalize (
(Rabs (gN (gM u)) (gN (gM v))) (retype (fun t : U => gN (gM t)) c)
).
intro Rabs1.
destruct Rabs1 as [RAbs RAbss].
simpl in *.
clear RAbss.
gendep RAbs.

rewrite <- HNarrow.
rewrite <- HMarrow.
intros.
rewrite (UIP_refl _ _ e).
simpl.
assert (HHP':= HHP _ _ 
 (SM_ind (fun 

rewrite <- HHP.
rew (gen_rh_rkl ).
rew (retakl PM).
rewrite <- HN.


gendep HN.
generalize (HNarrow (gM u) (gM v)).

rewrite <- HNarrow.
intros RAbs HMarrow0.
gendep RAbs.
gendep HMarrow0.
(*rewrite <- HMarrow.*)

Check (
fun u0 : U' =>
 forall (HMarrow0 : forall u v : U, gM (Uarrow u v) = U'arrow (gM u) (gM v))
   (RAbs : (RM (opt (gN (gM u)) (retype (fun t : U => gN (gM t)) c)))
             (gN (gM v)) -> (RM (retype (fun t : U => gN (gM t)) c)) (gN u0)),
 eq_rect (gM (Uarrow u v))
   (fun t : U' => (QM (retype (fun t0 : U => gM t0) c)) t)
   ((TM c) (gM (Uarrow u v))
      (ctype (fun t : U => gM t) (V:=PM c) (t:=Uarrow u v) (((Pabs u v) c) y)))
   u0 (HMarrow0 u v) =
 ((Qabs (gM u) (gM v)) (retype (fun t : U => gM t) c))
   ((rlift QM (a:=retype (fun t : U => gM t) (opt u c))
       (b:=opt (gM u) (retype (fun t : U => gM t) c)) der_comm) (gM v)
      ((TM (opt u c)) (gM v)
         (ctype (fun t : U => gM t) (V:=PM (opt u c)) (t:=v) y))) ->
 forall e : gN (gM (Uarrow u v)) = gN u0,
 eq_rect (gN (gM (Uarrow u v)))
   (fun t : U'' => (RM (retype (fun t0 : U => gN (gM t0)) c)) t)
   ((rkleisli (a:=retype (fun t : U' => gN t) (retype (fun t : U => gM t) c))
       (b:=retype (fun t : U => gN (gM t)) c)
       (ipo_comp
          (sm_ipo_mor (T:=U'')
             (V:=retype (fun t : U' => gN t) (retype (fun t : U => gM t) c))
             (W:=retype (fun t : U => gN (gM t)) c)
             (double_retype_1 (f:=gM) (f':=gN)))
          (rweta (retype (fun t : U => gN (gM t)) c))))
      (gN (gM (Uarrow u v)))
      ((TN (retype (fun t : U => gM t) c)) (gN (gM (Uarrow u v)))
         (ctype (fun t : U' => gN t) (V:=QM (retype (fun t : U => gM t) c))
            (t:=gM (Uarrow u v))
            ((TM c) (gM (Uarrow u v))
               (ctype (fun t : U => gM t) (V:=PM c) (t:=Uarrow u v)
                  (((Pabs u v) c) y)))))) (gN u0) e =
 RAbs
   ((rkleisli
       (a:=retype (fun t : U' => gN t) (retype (fun t : U => gM t) (opt u c)))
       (b:=opt (gN (gM u)) (retype (fun t : U => gN (gM t)) c))
       (ipo_comp
          (ipo_comp
             (sm_ipo_mor (T:=U'')
                (V:=retype (fun t : U' => gN t)
                      (retype (fun t : U => gM t) (opt u c)))
                (W:=retype (fun t : U => gN (gM t)) (opt u c))
                (double_retype_1 (f:=gM) (f':=gN)))
             (rweta (retype (fun t : U => gN (gM t)) (opt u c))))
          (rkleisli (a:=retype (fun t : U => gN (gM t)) (opt u c))
             (b:=opt (gN (gM u)) (retype (fun t : U => gN (gM t)) c))
             (ipo_comp
                (sm_ipo_mor (T:=U'')
                   (V:=retype (fun t : U => gN (gM t)) (opt u c))
                   (W:=opt (gN (gM u)) (retype (fun t : U => gN (gM t)) c))
                   der_comm)
                (rweta (opt (gN (gM u)) (retype (fun t : U => gN (gM t)) c)))))))
      (gN (gM v))
      ((TN (retype (fun t : U => gM t) (opt u c))) (gN (gM v))
         (ctype (fun t : U' => gN t)
            (V:=QM (retype (fun t : U => gM t) (opt u c))) (t:=gM v)
            ((TM (opt u c)) (gM v)
               (ctype (fun t : U => gM t) (V:=PM (opt u c)) (t:=v) y)))))
).

intros.
rewrite (UIP_refl _ _ e).
simpl.

unfold rlift in HM, HN.
simpl in *.
rewrite HM.

Check (
fun u0 : U'' =>
 forall e : gN (gM (Uarrow u v)) = u0,
 eq_rect (gN (gM (Uarrow u v)))
   (fun t : U'' => (RM (retype (fun t0 : U => gN (gM t0)) c)) t)
   ((rkleisli (RMonad_struct := RM)
   (a:=retype (fun t : U' => gN t) (retype (fun t : U => gM t) c))
       (b:=retype (fun t : U => gN (gM t)) c)
       (ipo_comp
          (sm_ipo_mor (T:=U'')
             (V:=retype (fun t : U' => gN t) (retype (fun t : U => gM t) c))
             (W:=retype (fun t : U => gN (gM t)) c)
             (double_retype_1 (f:=gM) (f':=gN)(V:= _ )))
          (rweta (retype (fun t : U => gN (gM t)) c))))
      (gN (gM (Uarrow u v)))
      ((TN (retype (fun t : U => gM t) c)) (gN (gM (Uarrow u v)))
         (ctype (fun t : U' => gN t) (V:=QM (retype (fun t : U => gM t) c))
            (t:=gM (Uarrow u v))
            ((TM c) (gM (Uarrow u v))
               (ctype (fun t : U => gM t) (V:=PM c) (t:=Uarrow u v)
                  (((Pabs u v) c) y)))))) u0 e =
 ((Rabs (gN (gM u)) (gN (gM v))) (retype (fun t : U => gN (gM t)) c))
   ((rkleisli (RMonad_struct := RM)
       (a:=retype (fun t : U' => gN t) (retype (fun t : U => gM t) (opt u c)))
       (b:=opt (gN (gM u)) (retype (fun t : U => gN (gM t)) c))
       (ipo_comp
          (ipo_comp
             (sm_ipo_mor (T:=U'')
                (V:=retype (fun t : U' => gN t)
                      (retype (fun t : U => gM t) (opt u c)))
                (W:=retype (fun t : U => gN (gM t)) (opt u c))
                (double_retype_1 (f:=gM) (f':=gN)(V:=_)))
             (rweta (retype (fun t : U => gN (gM t)) (opt u c))))
          (rkleisli (a:=retype (fun t : U => gN (gM t)) (opt u c))
             (b:=opt (gN (gM u)) (retype (fun t : U => gN (gM t)) c))
             (ipo_comp
                (sm_ipo_mor (T:=U'')
                   (V:=retype (fun t : U => gN (gM t)) (opt u c))
                   (W:=opt (gN (gM u)) (retype (fun t : U => gN (gM t)) c))
                   (@der_comm _ _ _ _ _ ))
                (rweta (opt (gN (gM u)) (retype (fun t : U => gN (gM t)) c)))))))
      (gN (gM v))
      ((TN (retype (fun t : U => gM t) (opt u c))) (gN (gM v))
         (ctype (fun t : U' => gN t)
            (V:=QM (retype (fun t : U => gM t) (opt u c))) (t:=gM v)
            ((TM (opt u c)) (gM v)
               (ctype (fun t : U => gM t) (V:=PM (opt u c)) (t:=v) y)))))

).
rewrite <- HNarrow.


assert (r:=rmod_hom_rmkl (Rabs (gN (gM u)) (gN (gM v)))).
simpl in r.
simpl.
assert (q:=rmod_hom_rmkl (Qabs (gM u) (gM v))).
simpl in q.
assert (p:=rmod_hom_rmkl (Pabs u v)).
simpl in p.
rewrite p.

rewrite <- q.
rewrite <-r.
rew (rklkl RM). Check (@der_comm).
rewrite <- HN. 
rewrite <- HN.
rerew (gen_rh_rkl TM).
rewrite  r.
apply f_equal.
simpl.
clear r Rapp Papp Qapp.
destruct y as [y1 y2];
simpl in *.

gendep e.
rewrite <- HNarrow.
rewrite <- HMarrow.

intros.
rewrite (UIP_refl _ _ e).
simpl.
auto.
Qed.
*)
Obligation 10.
Proof. (* app *)
  unfold app_hom';
  simpl.
  intros u v c y.
  assert (HM:=app_hom (u:=u)(v:=v) 
        (PCFPO_rep_Hom_struct :=M) (c:=c)y).
  assert (HN:=app_hom (u:=tcomp M u)
                      (v:=tcomp M v)
          (PCFPO_rep_Hom_struct :=N)
           (c:=retype(fun t => tcomp M t) c)).
  simpl in HM ,HN.

  generalize (exsimio u v) as e.
(*
  generalize (
    comp_arrow_dist (Uar:=type_arrow (p:=P)) 
      (U'ar:=type_arrow (p:=Q))
        (g:=tcomp M) (tcomp_arrow M) (g':=tcomp N) 
      (U''ar:=type_arrow (p:=R))
        (tcomp_arrow N) u v
).
*)  

  destruct N as [gN HNarrow HNnat HNbool TN TNs].
  destruct M as [gM HMarrow HMnat HMbool TM TMs].

  clear M N.
  simpl in *.
  clear TNs.
  clear TMs.
  clear HMnat HMbool.
  clear HNnat HNbool.
  rewrite <- HM.
  rewrite <- HN.
  simpl.
  clear HM.
  clear HN.
  
  (*destruct TM.*)
  destruct P as [U Uarrow PM fP HP Prep].
  destruct Q as [U' U'arrow QM fQ HQ Qrep];
  destruct R as [U'' U''arrow RM fR HR Rrep];
  clear P Q R;
  simpl in *.
  destruct Prep as [Papp Pabs Prec tttt 
    ffff nats Succ Pred Zero CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
    propag_rec*) 
    CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn 
      Pred_Z Rec_A ].
  simpl in *.
  clear Prec Pabs tttt ffff nats Succ Pred Zero CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 propag_rec*) 
        CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn Pred_Z
        Rec_A.
  destruct Qrep as [Qapp Qabs Qrec tttt 
      ffff nats Succ Pred Zero CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
       propag_rec*) 
       CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn Pred_Z
        Rec_A ].
  simpl in *.
  clear Qrec Qabs Qrec tttt ffff nats Succ Pred Zero
      CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
      propag_rec*) 
      CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn 
     Pred_Z Rec_A.
 destruct Rrep as [Rapp Rabs Rrec tttt 
      ffff nats Succ Pred Zero CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 propag_rec*)
       CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn Pred_Z
        Rec_A ].
  simpl in *.
  clear Rabs Rrec tttt ffff nats Succ Pred Zero
      CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
       propag_rec*) 
       CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn 
    Pred_Z Rec_A.

intro e.
assert (r:=rmod_hom_rmkl (Rapp (gN (gM u)) (gN (gM v)))).
simpl in r. 
unfold rlift.
rewrite <- r.
apply f_equal.
simpl.
clear r Rapp Papp Qapp.
destruct y as [y1 y2];
simpl in *.

gendep e.
rewrite <- HNarrow.
rewrite <- HMarrow.

intros.
rewrite (UIP_refl _ _ e).
simpl.
auto.
Qed.

Obligation 9.
Proof. (* nat *)
  unfold nats_hom';
  simpl.
  intros m c t.
  elim t.
  clear t.
  assert (HM:=nats_hom m (PCFPO_rep_Hom_struct :=M)(c:=c) tt).
  assert (HN:=nats_hom m (PCFPO_rep_Hom_struct :=N)
           (c:=retype(fun t => tcomp M t) c)tt).
  simpl in HM ,HN.
  
  generalize (nats_hom'_obligation_1 (P:=P) (R:=R)
     (f:=fun t : type_type P => tcomp N (tcomp M t)) exsimio_nat m) as e.
  
(*
  generalize (
comp_arrow_commute (g:=tcomp M) (f:=type_mor P) 
  (f':=type_mor Q)
     (ttriag M) (f'':=type_mor R) (g':=tcomp N) 
  (ttriag N) Nat
).
*)
  destruct N as [gN HNarrow HNbool HNnat TN TNs].
  destruct M as [gM HMarrow HMbool HMnat TM TMs].

  clear M N.
  simpl in *.
  clear TNs.
  clear TMs.
  
  generalize HM.
  generalize (nats_hom'_obligation_1 HMbool m) .
  intros. clear HM.

  generalize HN.
  generalize (nats_hom'_obligation_1 HNbool m) .
  intros. clear HN.

  
(*  destruct P as [U Uarrow PM fP HP Prep].*)
  destruct P as [U Uarrow Unat Ubool PM Prep].
  destruct Q as [U' U'arrow QM fQ HQ Qrep];
  destruct R as [U'' U''arrow RM fR HR Rrep];
  clear P Q R;
  simpl in *.
  
destruct Prep as [Papp Pabs Prec tttt 
    ffff Pnats Succ Pred Zero CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
    propag_rec*) 
    CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn 
      Pred_Z
        Rec_A ].
  simpl in *.

  clear Papp Pabs Prec tttt ffff Succ Pred Zero 
     CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
     propag_rec*) 
     CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn 
     Pred_Z Rec_A.
  destruct Qrep as [Qapp Qabs Qrec tttt 
      ffff Qnats Succ Pred Zero CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
       propag_rec*) 
       CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn Pred_Z
        Rec_A ].
  simpl in *.
  clear Qapp Qabs Qrec tttt ffff Succ Pred Zero
      CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
      propag_rec*) 
      CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn 
     Pred_Z Rec_A.
 destruct Rrep as [Rapp Rabs Rrec tttt 
      ffff Rnats Succ Pred Zero CondN CondB bottom
      beta_red 
      (*propag_app1 propag_abs propag_app2 propag_rec*)
        CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn Pred_Z
        Rec_A ].
  simpl in *.
  clear Rapp Rabs Rrec tttt ffff Succ Pred Zero
      CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
       propag_rec*) 
       CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn 
    Pred_Z Rec_A.

assert (HH:=rmod_hom_rmkl (Rnats m)).
simpl in HH.
assert (HH':= HH 
(retype (fun t : U' => gN t) (retype (fun t : U => gM t) c))
(retype (fun t : U => gN (gM t)) c)).
simpl in HH'.

gendep HH'.

generalize (Rnats m (retype (fun t : U => gN (gM t)) c)).
intro Rnats1.
destruct Rnats1 as [RNat RNats].
simpl in *.
clear RNats.
gendep RNat.

gendep HN0.
generalize (e1).
gendep HM0.
generalize (e).


generalize (Qnats m (retype (fun t => gM t) c)).
intro Qnats1.
destruct Qnats1 as [QNat QNats].
simpl in *.
clear QNats.
gendep QNat.

generalize (Rnats m (retype (fun t => gN t)
   (retype (fun t => gM t) c))).
intro Rnats1.
destruct Rnats1 as [RNat RNats].
simpl in *.
clear RNats.
gendep RNat.
rewrite <- e0.
rewrite <- e.

(*
rewrite <- (HNcommute).
rewrite <- (HMcommute).
*)
intros.
rewrite (UIP_refl _ _ _) in HM0.
simpl in HM0.
rewrite (UIP_refl _ _ _) in HN0.
simpl in HN0.
simpl.
(*
rewrite (UIP_refl _ _ _).
*)
simpl.
rewrite  HM0.
rewrite HN0.
simpl.
unfold rlift.
simpl.

rewrite <- HH'.
auto.
Qed.
Obligation 8.
Proof. (* bottom *)
  unfold bottom_hom';
  simpl.
  intros u c t.
  elim t.
  clear t.
  assert (HM:=bottom_hom (PCFPO_rep_Hom_struct :=M)
        (c:=c) u tt).
  assert (HN:=bottom_hom (PCFPO_rep_Hom_struct :=N)
           (c:=retype(fun t => tcomp M t) c) (tcomp M u) tt).
  simpl in HM ,HN.
  
  rewrite HM.
  rewrite HN.
  unfold rlift;
  simpl.
  assert (h:=rmod_hom_rmkl 
    (bottom (PCFPO_rep_struct := R)
      (tcomp N (tcomp M u)))).
  simpl in h.
  rewrite <- h.
  auto.
Qed.
Obligation 7.
Proof. (* tttt *)
  unfold ttt_hom';
  simpl.
  intros c t.
  elim t.
  clear t.
  assert (HM:=ttt_hom (PCFPO_rep_Hom_struct :=M)(c:=c) tt).
  assert (HN:=ttt_hom (PCFPO_rep_Hom_struct :=N)
           (c:=retype(fun t => tcomp M t) c)tt).
  simpl in HM ,HN.
  
  generalize (ttt_hom'_obligation_1 (P:=P) (R:=R)
     (f:=fun t : type_type P => tcomp N (tcomp M t)) exsimio_bool).
  
(*
  generalize (
comp_arrow_commute (g:=tcomp M) (f:=type_mor P) 
  (f':=type_mor Q)
     (ttriag M) (f'':=type_mor R) (g':=tcomp N) 
  (ttriag N) Bool
).
*)
  destruct N as [gN HNarrow HNbool HNnat TN TNs].
  destruct M as [gM HMarrow HMbool HMnat TM TMs].

  clear M N.
  simpl in *.
  clear TNs.
  clear TMs.
  
  generalize HM.
  generalize (ttt_hom'_obligation_1 HMnat) .
  intros. clear HM.

  generalize HN.
  generalize (ttt_hom'_obligation_1 HNnat) .
  intros. clear HN.
  
  
  destruct P as [U Uarrow PM fP HP Prep].
  destruct Q as [U' U'arrow QM fQ HQ Qrep];
  destruct R as [U'' U''arrow RM fR HR Rrep];
  clear P Q R;
  simpl in *.
destruct Prep as [Papp Pabs Prec Ptttt 
    ffff nats Succ Pred Zero CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
    propag_rec*) 
    CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn 
      Pred_Z
        Rec_A ].
  simpl in *.
  clear Papp Pabs Prec ffff nats Succ Pred Zero 
     CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
     propag_rec*) 
     CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn 
     Pred_Z Rec_A.
  destruct Qrep as [Qapp Qabs Qrec Qtttt 
      ffff nats Succ Pred Zero CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
       propag_rec*)
       CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn Pred_Z
        Rec_A ].
  simpl in *.
  clear Qapp Qabs Qrec ffff nats Succ Pred Zero
      CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
      propag_rec*) 
      CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn 
     Pred_Z Rec_A.
 destruct Rrep as [Rapp Rabs Rrec Rtttt 
      ffff nats Succ Pred Zero CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 propag_rec*) 
        CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn Pred_Z
        Rec_A ].
  simpl in *.
  clear Rapp Rabs Rrec ffff nats Succ Pred Zero
      CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
       propag_rec*)
       CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn 
    Pred_Z Rec_A.

assert (HH:=rmod_hom_rmkl Rtttt).
simpl in HH.
assert (HH':= HH 
(retype (fun t : U' => gN t) (retype (fun t : U => gM t) c))
(retype (fun t : U => gN (gM t)) c)).
simpl in HH'.

gendep HH'.

generalize (Rtttt (retype (fun t : U => gN (gM t)) c)).
intro Rtttt1.
destruct Rtttt1 as [Rttt Rttts].
simpl in *.
clear Rttts.
gendep Rttt.

gendep HN0.
generalize (e1).
gendep HM0.
generalize e.

generalize (Qtttt (retype (fun t => gM t) c)).
intro Qtttt1.
destruct Qtttt1 as [Qttt Qttts].
simpl in *.
clear Qttts.
gendep Qttt.

generalize (Rtttt (retype (fun t => gN t)
   (retype (fun t => gM t) c))).

intro Rtttt1.
destruct Rtttt1 as [Rttt Rttts].
simpl in *.
clear Rttts.
gendep Rttt.

destruct e.
destruct e1.
(*
rewrite <- (HNcommute).
rewrite <- (HMcommute).
*)
intros.
rewrite (UIP_refl _ _ e) in HM0.
simpl in HM0.
rewrite (UIP_refl _ _ _) in HN0.
simpl in HN0.
rewrite (UIP_refl _ _ _).
simpl.
rewrite  HM0.
rewrite HN0.
simpl.
unfold rlift.
simpl.

rewrite <- HH'.
auto.
Qed.
Obligation 6.
Proof. (* ffff *)
  unfold fff_hom';
  simpl.
  intros c t.
  elim t.
  clear t.
  assert (HM:=fff_hom (PCFPO_rep_Hom_struct :=M)(c:=c) tt).
  assert (HN:=fff_hom (PCFPO_rep_Hom_struct :=N)
           (c:=retype(fun t => tcomp M t) c)tt).
  simpl in HM ,HN.
  
  generalize (fff_hom'_obligation_1 (P:=P) (R:=R)
     (f:=fun t : type_type P => tcomp N (tcomp M t)) exsimio_bool).
  
(*
  generalize (
comp_arrow_commute (g:=tcomp M) (f:=type_mor P) 
  (f':=type_mor Q)
     (ttriag M) (f'':=type_mor R) (g':=tcomp N) 
  (ttriag N) Bool
).
*)
  destruct N as [gN HNarrow HNbool HNnat TN TNs].
  destruct M as [gM HMarrow HMbool HMnat TM TMs].

  clear M N.
  simpl in *.
  clear TNs.
  clear TMs.
  
    generalize HM.
  generalize (fff_hom'_obligation_1 HMnat) .
  intros. clear HM.

  generalize HN.
  generalize (fff_hom'_obligation_1 HNnat) .
  intros. clear HN.
  
  
  destruct P as [U Uarrow PM fP HP Prep].
  destruct Q as [U' U'arrow QM fQ HQ Qrep];
  destruct R as [U'' U''arrow RM fR HR Rrep];
  clear P Q R;
  simpl in *.
destruct Prep as [Papp Pabs Prec tttt 
      Pffff nats Succ Pred Zero CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
        propag_rec*)
        CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn 
      Pred_Z
        Rec_A ].
  simpl in *.
  clear Papp Pabs Prec tttt nats Succ Pred Zero 
     CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
     propag_rec*)
     CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn 
     Pred_Z Rec_A.
  destruct Qrep as [Qapp Qabs Qrec tttt 
      Qffff nats Succ Pred Zero CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
       propag_rec*)
       CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn Pred_Z
        Rec_A ].
  simpl in *.
  clear Qapp Qabs Qrec tttt nats Succ Pred Zero
      CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
      propag_rec*)
      CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn 
     Pred_Z Rec_A.
 destruct Rrep as [Rapp Rabs Rrec tttt 
      Rffff nats Succ Pred Zero CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 propag_rec*)
        CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn Pred_Z
        Rec_A ].
  simpl in *.
  clear Rapp Rabs Rrec tttt nats Succ Pred Zero
      CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
        propag_rec*) 
        CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn 
    Pred_Z Rec_A.

assert (HH:=rmod_hom_rmkl Rffff).
simpl in HH.
assert (HH':= HH 
(retype (fun t : U' => gN t) (retype (fun t : U => gM t) c))
(retype (fun t : U => gN (gM t)) c)).
simpl in HH'.

gendep HH'.

generalize (Rffff (retype (fun t : U => gN (gM t)) c)).
intro Rffff1.
destruct Rffff1 as [Rfff Rfffs].
simpl in *.
clear Rfffs.
gendep Rfff.

gendep HN0.
generalize e1.
gendep HM0.
generalize e.

generalize (Qffff (retype (fun t => gM t) c)).
intro Qffff1.
destruct Qffff1 as [Qfff Qfffs].
simpl in *.
clear Qfffs.
gendep Qfff.

generalize (Rffff (retype (fun t => gN t)
   (retype (fun t => gM t) c))).

intro Rffff1.
destruct Rffff1 as [Rfff Rfffs].
simpl in *.
clear Rfffs.
gendep Rfff.

destruct e.
destruct e1.
(*
rewrite <- (HNcommute).
rewrite <- (HMcommute).
*)
intros.
rewrite (UIP_refl _ _ e) in HM0.
simpl in HM0.
rewrite (UIP_refl _ _ _) in HN0.
simpl in HN0.
rewrite (UIP_refl _ _ _).
simpl.
rewrite  HM0.
rewrite HN0.
simpl.
unfold rlift.
simpl.

rewrite <- HH'.
auto.
Qed.
Obligation 5.
Proof. (* succ *)
  unfold Succ_hom';
  simpl.
  intros c t.
  elim t.
  clear t.
  assert (HM:=Succ_hom (PCFPO_rep_Hom_struct :=M)(c:=c) tt).
  assert (HN:=Succ_hom (PCFPO_rep_Hom_struct :=N)
           (c:=retype(fun t => tcomp M t) c)tt).
  simpl in HM ,HN.
  
  generalize (Succ_hom'_obligation_1 (P:=P) (R:=R)
     (f:=fun t : type_type P => tcomp N (tcomp M t)) exsimio exsimio_nat).

  destruct N as [gN HNarrow HNbool HNnat TN TNs].
  destruct M as [gM HMarrow HMbool HMnat TM TMs].

  clear M N.
  simpl in *.
  clear TNs.
  clear TMs.
  
    generalize HM.
  generalize (Succ_hom'_obligation_1 HMarrow HMbool) .
  intros. clear HM.

  generalize HN.
  generalize (Succ_hom'_obligation_1 HNarrow HNbool) .
  intros. clear HN.
  
  
  
  
  destruct P as [U Uarrow PM fP HP Prep].
  destruct Q as [U' U'arrow QM fQ HQ Qrep];
  destruct R as [U'' U''arrow RM fR HR Rrep];
  clear P Q R;
  simpl in *.
destruct Prep as [Papp Pabs Prec tttt 
      ffff nats PSucc Pred Zero CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
    propag_rec*) 
    CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn 
      Pred_Z
        Rec_A ].
  simpl in *.
  clear Papp Pabs Prec tttt ffff nats Pred Zero 
     CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
     propag_rec*) 
     CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn 
     Pred_Z Rec_A.
  destruct Qrep as [Qapp Qabs Qrec tttt 
      ffff nats QSucc Pred Zero CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
       propag_rec*) 
       CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn Pred_Z
        Rec_A ].
  simpl in *.
  clear Qapp Qabs Qrec tttt ffff nats Pred Zero
      CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
      propag_rec*)
      CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn 
     Pred_Z Rec_A.
 destruct Rrep as [Rapp Rabs Rrec tttt 
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

assert (HH:=rmod_hom_rmkl RSucc).
simpl in HH.
assert (HH':= HH 
(retype (fun t : U' => gN t) (retype (fun t : U => gM t) c))
(retype (fun t : U => gN (gM t)) c)).
simpl in HH'.

gendep HH'.

generalize (RSucc (retype (fun t : U => gN (gM t)) c)).
intro RSucc1.
destruct RSucc1 as [Rsucc Rsuccs].
simpl in *.
clear Rsuccs.
gendep Rsucc.

gendep HN0.
generalize e1. 
gendep HM0.
generalize e. 

generalize (QSucc (retype (fun t => gM t) c)).
intro QSucc1.
destruct QSucc1 as [Qsucc Qsuccs].
simpl in *.
clear Qsuccs.
gendep Qsucc.

generalize (RSucc (retype (fun t => gN t)
   (retype (fun t => gM t) c))).

intro RSucc1.
destruct RSucc1 as [Rsucc Rsuccs].
simpl in *.
clear Rsuccs.
gendep Rsucc.

rewrite <- e.
rerew_all.
(*
rewrite <- 
rewrite e1.

rewrite <- (HNcommute).
rewrite <- (HNarrow).
rewrite <- (HMcommute).
rewrite <- (HMarrow).
*)
intros.
rewrite (UIP_refl _ _ _) in HM0.
simpl in HM0.
rewrite (UIP_refl _ _ _) in HN0.
simpl in HN0.
simpl.
rew_all.
rew_all.
(*
rewrite  HM.
rewrite HN.
*)
simpl.
unfold rlift.
simpl.

rewrite <- HH'.
auto.
Qed.
Obligation 4.
Proof. (* zero *)
  unfold Zero_hom';
  simpl.
  intros c t.
  elim t.
  clear t.
  assert (HM:=Zero_hom (PCFPO_rep_Hom_struct :=M)(c:=c) tt).
  assert (HN:=Zero_hom (PCFPO_rep_Hom_struct :=N)
           (c:=retype(fun t => tcomp M t) c)tt).
  simpl in HM ,HN.
  
  generalize (Zero_hom'_obligation_1 (P:=P) (R:=R)
     (f:=fun t : type_type P => tcomp N (tcomp M t)) exsimio exsimio_bool
     exsimio_nat).
   
  destruct N as [gN HNarrow HNnat HNbool TN TNs].
  destruct M as [gM HMarrow HMnat HMbool TM TMs].

  clear M N.
  simpl in *.
  clear TNs.
  clear TMs.
  
      generalize HM.
  generalize (Zero_hom'_obligation_1 HMarrow HMbool HMnat) .
  intros. clear HM.

  generalize HN.
  generalize (Zero_hom'_obligation_1 HNarrow HNbool HNnat) .
  intros. clear HN.
  
  
  destruct P as [U Uarrow PM fP HP Prep].
  destruct Q as [U' U'arrow QM fQ HQ Qrep];
  destruct R as [U'' U''arrow RM fR HR Rrep];
  clear P Q R;
  simpl in *.
destruct Prep as [Papp Pabs Prec tttt 
      ffff nats Succ Pred PZero CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
    propag_rec*)
    CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn 
      Pred_Z
        Rec_A ].
  simpl in *.
  clear Papp Pabs Prec tttt ffff nats Succ Pred 
     CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
     propag_rec*)
     CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn 
     Pred_Z Rec_A.
  destruct Qrep as [Qapp Qabs Qrec tttt 
      ffff nats Succ Pred QZero CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
       propag_rec*)
       CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn Pred_Z
        Rec_A ].
  simpl in *.
  clear Qapp Qabs Qrec tttt ffff nats Succ Pred
      CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
      propag_rec*)
      CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn 
     Pred_Z Rec_A.
 destruct Rrep as [Rapp Rabs Rrec tttt 
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

assert (HH:=rmod_hom_rmkl RZero).
simpl in HH.
assert (HH':= HH 
(retype (fun t : U' => gN t) (retype (fun t : U => gM t) c))
(retype (fun t : U => gN (gM t)) c)).
simpl in HH'.

gendep HH'.

generalize (RZero (retype (fun t : U => gN (gM t)) c)).
intro RZero1.
destruct RZero1 as [Rzero Rzeros].
simpl in *.
clear Rzeros.
gendep Rzero.

gendep HN0.
generalize e1.
gendep HM0.
generalize e.

generalize (QZero (retype (fun t => gM t) c)).
intro QZero1.
destruct QZero1 as [Qzero Qzeros].
simpl in *.
clear Qzeros.
gendep Qzero.

generalize (RZero (retype (fun t => gN t)
   (retype (fun t => gM t) c))).

intro RZero1.
destruct RZero1 as [Rzero Rzeros].
simpl in *.
clear Rzeros.
gendep Rzero.

rerew_all.
rerew_all.
repeat rerew_all.

(*
rewrite <- (HNcommute).
rewrite <- HNcommute.
rewrite <- (HNarrow).
rewrite <- (HMcommute).
rewrite <- HMcommute.
rewrite <- (HMarrow).
*)
intros.
rewrite (UIP_refl _ _ _) in HM0.
simpl in HM0.
rewrite (UIP_refl _ _ _) in HN0.
simpl in HN0.
simpl.
rewrite  HM0.
rewrite HN0.
simpl.
unfold rlift.
simpl.

rewrite <- HH'.
auto.
Qed.
Obligation 3.
Proof. (* pred *)
  unfold Pred_hom';
  simpl.
  intros c t.
  elim t.
  clear t.
  assert (HM:=Pred_hom (PCFPO_rep_Hom_struct :=M)(c:=c) tt).
  assert (HN:=Pred_hom (PCFPO_rep_Hom_struct :=N)
           (c:=retype(fun t => tcomp M t) c)tt).
  simpl in HM ,HN.
  
  generalize (Pred_hom'_obligation_1 (P:=P) (R:=R)
     (f:=fun t : type_type P => tcomp N (tcomp M t)) exsimio exsimio_nat).

  destruct N as [gN HNarrow HNnat HNbool TN TNs].
  destruct M as [gM HMarrow HMnat HMbool TM TMs].

  clear M N.
  simpl in *.
  clear TNs.
  clear TMs.
  
       generalize HM.
  generalize (Pred_hom'_obligation_1 HMarrow HMnat) .
  intros. clear HM.

  generalize HN.
  generalize (Pred_hom'_obligation_1 HNarrow HNnat) .
  intros. clear HN.
  
  
  destruct P as [U Uarrow PM fP HP Prep].
  destruct Q as [U' U'arrow QM fQ HQ Qrep];
  destruct R as [U'' U''arrow RM fR HR Rrep];
  clear P Q R;
  simpl in *.
destruct Prep as [Papp Pabs Prec tttt 
      ffff nats Succ PPred Zero CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
    propag_rec*)
    CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn 
      Pred_Z
        Rec_A ].
  simpl in *.
  clear Papp Pabs Prec tttt ffff nats Succ Zero CondN 
     CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
        propag_rec*) 
        CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn 
     Pred_Z
        Rec_A.
  destruct Qrep as [Qapp Qabs Qrec tttt 
      ffff nats Succ QPred Zero CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
       propag_rec *)
       CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn Pred_Z
        Rec_A ].
  simpl in *.
  clear Qapp Qabs Qrec tttt ffff nats Succ Zero 
      CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
      propag_rec*)
      CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn 
     Pred_Z Rec_A.
 destruct Rrep as [Rapp Rabs Rrec tttt 
      ffff nats Succ RPred Zero CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 propag_rec*)
        CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn Pred_Z
        Rec_A ].
  simpl in *.
  clear Rapp Rabs Rrec tttt ffff nats Succ Zero 
      CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
       propag_rec*)
       CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn 
    Pred_Z Rec_A.

assert (HH:=rmod_hom_rmkl RPred).
simpl in HH.
assert (HH':= HH 
(retype (fun t : U' => gN t) (retype (fun t : U => gM t) c))
(retype (fun t : U => gN (gM t)) c)).
simpl in HH'.

gendep HH'.

generalize (RPred (retype (fun t : U => gN (gM t)) c)).
intro RPred1.
destruct RPred1 as [Rpred Rpreds].
simpl in *.
clear Rpreds.
gendep Rpred.

gendep HN0.
generalize e1 . 
gendep HM0.
generalize e.
generalize (QPred (retype (fun t => gM t) c)).
intro QPred1.
destruct QPred1 as [Qpred Qpreds].
simpl in *.
clear Qpreds.
gendep Qpred.

generalize (RPred (retype (fun t => gN t)
   (retype (fun t => gM t) c))).

intro RPred1.
destruct RPred1 as [Rpred Rpreds].
simpl in *.
clear Rpreds.
gendep Rpred.

repeat (rerew_all).

intros.
rewrite (UIP_refl _ _ _) in HM0.
simpl in HM0.
rewrite (UIP_refl _ _ _) in HN0.
simpl in HN0.
simpl.
rewrite  HM0.
rewrite HN0.
simpl.
unfold rlift.
simpl.

rewrite <- HH'.
auto.
Qed.
Obligation 2.
Proof. (* condN *)
  unfold CondN_hom';
  simpl.
  intros c t.
  elim t.
  clear t.
  assert (HM:=CondN_hom (PCFPO_rep_Hom_struct :=M)(c:=c) tt).
  assert (HN:=CondN_hom (PCFPO_rep_Hom_struct :=N)
           (c:=retype(fun t => tcomp M t) c)tt).
  simpl in HM ,HN.
  
  generalize (CondN_hom'_obligation_1 (P:=P) (R:=R)
     (f:=fun t : type_type P => tcomp N (tcomp M t)) exsimio exsimio_bool
     exsimio_nat).
  
  destruct N as [gN HNarrow HNbool HNnat TN TNs].
  destruct M as [gM HMarrow HMbool HMnat TM TMs].

  clear M N.
  simpl in *.
  clear TNs.
  clear TMs.
  
   generalize HM.
  generalize (CondN_hom'_obligation_1 HMarrow HMnat HMbool) .
  clear HM.
  intros e HM.

  generalize HN.
  generalize (CondN_hom'_obligation_1 HNarrow HNnat HNbool) .
  clear HN.
  intros.
  
  
  destruct P as [U Uarrow PM fP HP Prep].
  destruct Q as [U' U'arrow QM fQ HQ Qrep];
  destruct R as [U'' U''arrow RM fR HR Rrep];
  clear P Q R;
  simpl in *.
destruct Prep as [Papp Pabs Prec tttt 
      ffff nats Succ Pred Zero PCondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 propag_rec*)
    CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn Pred_Z
        Rec_A ].
  simpl in *.
  clear Papp Pabs Prec tttt ffff nats Succ Pred Zero 
    CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
    propag_rec*)
    CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn Pred_Z
        Rec_A.
  destruct Qrep as [Qapp Qabs Qrec tttt 
      ffff nats Succ Pred Zero QCondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
    propag_rec*)
    CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn Pred_Z
        Rec_A ].
  simpl in *.
  clear Qapp Qabs Qrec tttt ffff nats Succ Pred Zero 
   CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
        propag_rec*)
        CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn 
   Pred_Z Rec_A.
 destruct Rrep as [Rapp Rabs Rrec tttt 
      ffff nats Succ Pred Zero RCondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
        propag_rec*)
        CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn Pred_Z
        Rec_A ].
  simpl in *.
  clear Rapp Rabs Rrec tttt ffff nats Succ Pred 
  Zero CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 
        propag_rec*)
        CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn 
  Pred_Z Rec_A.

assert (HH:=rmod_hom_rmkl RCondN).
simpl in HH.
assert (HH':= HH 
(retype (fun t : U' => gN t) (retype (fun t : U => gM t) c))
(retype (fun t : U => gN (gM t)) c)).
simpl in HH'.

gendep HH'.

generalize (RCondN (retype (fun t : U => gN (gM t)) c)).
intro RCondN1.
destruct RCondN1 as [RcondN RcondNs].
simpl in *.
clear RcondNs.
gendep RcondN.

gendep HN.
generalize e1. 
gendep HM.
generalize e. 

generalize (QCondN (retype (fun t => gM t) c)).
intro QCondN1.
destruct QCondN1 as [QcondN QcondNs].
simpl in *.
clear QcondNs.
gendep QcondN.

generalize (RCondN (retype (fun t => gN t)
   (retype (fun t => gM t) c))).

intro RCondN1.
destruct RCondN1 as [RcondN RcondNs].
simpl in *.
clear RcondNs.
gendep RcondN.

repeat (rerew_all).

intros.
rewrite (UIP_refl _ _ _) in HM.
simpl in HM, HN.
simpl in HN.
rewrite (UIP_refl _ _ _).
simpl.
rewrite  HM.
rewrite HN.
simpl.
unfold rlift.
simpl.

rewrite <- HH'.
auto.
Qed.
Next Obligation.
Proof.
  unfold CondB_hom';
  simpl.
  intros c t.
  elim t.
  clear t.
  assert (HM:=CondB_hom (PCFPO_rep_Hom_struct :=M)(c:=c) tt).
  assert (HN:=CondB_hom (PCFPO_rep_Hom_struct :=N)
           (c:=retype(fun t => tcomp M t) c)tt).
  simpl in HM ,HN.
  
  generalize (CondB_hom'_obligation_1 (P:=P) (R:=R)
     (f:=fun t : type_type P => tcomp N (tcomp M t)) exsimio exsimio_bool).
  
destruct N as [gN HNarrow HNbool HNnat TN TNs].
  destruct M as [gM HMarrow HMbool HMnat TM TMs].

  clear M N.
  simpl in *.
  clear TNs.
  clear TMs.
  
     generalize HM.
  generalize (CondB_hom'_obligation_1 HMarrow HMnat) .
  clear HM.
  intros e HM.

  generalize HN.
  generalize (CondB_hom'_obligation_1 HNarrow HNnat) .
  clear HN.
  intros.
  
  destruct P as [U Uarrow PM fP HP Prep].
  destruct Q as [U' U'arrow QM fQ HQ Qrep];
  destruct R as [U'' U''arrow RM fR HR Rrep];
  clear P Q R;
  simpl in *.
destruct Prep as [Papp Pabs Prec tttt 
      ffff nats Succ Pred Zero CondN PCondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 propag_rec*)
        CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn Pred_Z
        Rec_A ].
  simpl in *.
  clear Papp Pabs Prec tttt ffff nats Succ Pred Zero CondN bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 propag_rec*)
        CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn Pred_Z
        Rec_A.
  destruct Qrep as [Qapp Qabs Qrec tttt 
      ffff nats Succ Pred Zero CondN QCondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 propag_rec*)
        CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn Pred_Z
        Rec_A ].
  simpl in *.
  clear Qapp Qabs Qrec tttt ffff nats Succ Pred Zero CondN bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 propag_rec*)
        CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn Pred_Z Rec_A.
 destruct Rrep as [Rapp Rabs Rrec tttt 
      ffff nats Succ Pred Zero CondN RCondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 propag_rec*)
        CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn Pred_Z
        Rec_A ].
  simpl in *.
  clear Rapp Rabs Rrec tttt ffff nats Succ Pred Zero CondN bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 propag_rec*)
        CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn Pred_Z Rec_A.

assert (HH:=rmod_hom_rmkl RCondB).
simpl in HH.
assert (HH':= HH 
(retype (fun t : U' => gN t) (retype (fun t : U => gM t) c))
(retype (fun t : U => gN (gM t)) c)).
simpl in HH'.

gendep HH'.

generalize (RCondB (retype (fun t : U => gN (gM t)) c)).
intro RCondB1.
destruct RCondB1 as [RcondB RcondBs].
simpl in *.
clear RcondBs.
gendep RcondB.

gendep HN.
generalize e1. 
gendep HM.
generalize e.

generalize (QCondB (retype (fun t => gM t) c)).
intro QCondB1.
destruct QCondB1 as [QcondB QcondBs].
simpl in *.
clear QcondBs.
gendep QcondB.

generalize (RCondB (retype (fun t => gN t)
   (retype (fun t => gM t) c))).

intro RCondB1.
destruct RCondB1 as [RcondB RcondBs].
simpl in *.
clear RcondBs.
gendep RcondB.

repeat (rerew_all).

intros.
rewrite (UIP_refl _ _ _) in HM.
simpl in HM.
simpl in HN.
rewrite (UIP_refl _ _ _).
simpl.
rewrite  HM.
rewrite HN.
simpl.
unfold rlift.
simpl.

rewrite <- HH'.
auto.
Qed.

Obligation 11. (* rec *)
Proof. (* rec *)
  unfold rec_hom';
  simpl.
  intros t c y.
  assert (HM:=rec_hom (t:=t) (PCFPO_rep_Hom_struct :=M) (c:=c)y).
  assert (HN:=rec_hom (t:=tcomp M t) (PCFPO_rep_Hom_struct :=N)
           (c:=retype(fun t => tcomp M t) c)).
  simpl in HM ,HN.
  
  generalize (exsimio t t).
  
  destruct N as [gN HNarrow HNnat HNbool TN TNs].
  destruct M as [gM HMarrow HMnat HMbool TM TMs].

  clear M N.
  simpl in *.
  clear TNs.
  clear TMs.
  rewrite HM.
  rewrite HN.

(*
  clear HMcommute.
  clear HNcommute.
*)
  clear HM.
  clear HN.
  
  (*destruct TM.*)
  destruct P as [U Uarrow PM fP HP Prep].
  destruct Q as [U' U'arrow QM fQ HQ Qrep];
  destruct R as [U'' U''arrow RM fR HR Rrep];
  clear P Q R;
  simpl in *.
destruct Prep as [Papp Pabs Prec tttt 
      ffff nats Succ Pred Zero CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 propag_rec*)
        CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn Pred_Z
        Rec_A ].
  simpl in *.
  clear Papp Pabs  tttt ffff nats Succ Pred Zero CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 propag_rec*)
        CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn Pred_Z
        Rec_A.
  destruct Qrep as [Qapp Qabs Qrec tttt 
      ffff nats Succ Pred Zero CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 propag_rec*)
        CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn Pred_Z
        Rec_A ].
  simpl in *.
  clear Qapp Qabs tttt ffff nats Succ Pred Zero CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 propag_rec*)
        CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn Pred_Z Rec_A.
 destruct Rrep as [Rapp Rabs Rrec tttt 
      ffff nats Succ Pred Zero CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 propag_rec*)
        CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn Pred_Z
        Rec_A ].
  simpl in *.
  clear Rapp Rabs tttt ffff nats Succ Pred Zero CondN CondB bottom
        beta_red 
        (*propag_app1 propag_abs propag_app2 propag_rec*)
        CondN_t CondN_f
        CondB_t CondB_f Succ_red Zero_t Zero_f Pred_Sn Pred_Z Rec_A.
 
intro e.
assert (r:=rmod_hom_rmkl (Rrec (gN (gM t)))).
simpl in r. 
unfold rlift at 1.
rewrite <- r.
apply f_equal.
simpl.
(*
assert (HRrect:= rmod_hom_rmkl (Rrec (gN (gM t)))
 (c:=retype (fun t => gN t) (retype (fun t => gM t) c))).
assert (HRrecta:=rmod_hom_rmkl (Rrec (gN (gM t)))
 (c:=retype (fun t => gN (gM t))c)).
gendep HRrect.
gendep HRrecta.
simpl.
*)
generalize (Rrec (gN (gM t))
  (retype (fun t : U' => gN t) (retype (fun t : U => gM t) c)))
   as RRec.
simpl in *.
intro RRec.
destruct RRec as [RRec po_mor_s].
simpl in *.
clear po_mor_s.
generalize RRec.
generalize (Rrec (gN (gM t)) (retype (fun t : U => gN (gM t)) c))
   as RRec1.
simpl.
intro RRec1.
destruct RRec1 as [RRec1 po_mor_s].
simpl in *.
clear po_mor_s.
generalize RRec1.
gendep e. 
 rewrite <- HNarrow.
 rewrite <- HMarrow.

simpl.
intros.

rewrite (UIP_refl _ _ e).
simpl.
unfold rlift.
simpl.
assert (H':= rkl_eq HR).
simpl in H'.
apply H'.
simpl.
auto.
Qed.
 
 
Definition Rep_comp :
  PCFPO_rep_Hom P R := Build_PCFPO_rep_Hom Rep_comp_struct.

End rep_comp.




















