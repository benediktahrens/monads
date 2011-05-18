Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Eqdep.

Require Export CatSem.COMP.PCF_rep_eq_quant.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Notation "'IT'" := (ITYPE TY).
Notation "a '~>' b" := (PCF.arrow a b) 
     (at level 69, right associativity).
Notation "a 'x' b" := (product a b) (at level 30).
Notation "P [ z ]" := (ITFIB_MOD _ z P) (at level 35).
Notation "'d' P // s" := (ITDER_MOD _ _ s P) (at level 25).
Notation "f 'X' g" := (product_mor _ f g)(at level 30).

(** the base types *)


Section comp_red.


Variables P Q R : PCF_rep.
Variable M : PCF_rep_Hom P Q.
Variable N : PCF_rep_Hom Q R.
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
*)
Ltac gendep H := generalize dependent H.

Obligation Tactic := idtac.

Program Instance Rep_comp_struct : 
  PCF_rep_Hom_struct (f := fun t => tcomp N (tcomp M t)) 
     (comp_arrow_commute (ttriag M) (ttriag N))
     (comp_arrow_dist (tcomp_arrow M) (tcomp_arrow N))  
     (comp_Rep_monad M N).
Next Obligation.
Proof.
 simpl.
  intros c t.
  elim t.
  clear t.
  assert (HM:=Succ_Hom (PCF_rep_Hom_struct :=M)(c:=c) tt).
  assert (HN:=Succ_Hom (PCF_rep_Hom_struct :=N)
           (c:=retype(fun t => tcomp M t) c)tt).
  simpl in HM ,HN.

  generalize (
arrow_dist_ct2 (Uar:=type_arrow (p:=P)) (U'ar:=type_arrow (p:=R))
     (g:=fun t : type_type P => tcomp N (tcomp M t))
     (comp_arrow_dist (Uar:=type_arrow (p:=P))
(U'ar:=type_arrow (p:=Q))
        (g:=tcomp M) (tcomp_arrow M) (g':=tcomp N)
(U''ar:=type_arrow (p:=R))
        (tcomp_arrow N)) (f:=type_mor P) (f':=type_mor R)
     (comp_arrow_commute (g:=tcomp M) (f:=type_mor P)
(f':=type_mor Q)
        (ttriag M) (f'':=type_mor R) (g':=tcomp N)
(ttriag N)) Nat Nat
).
  destruct N as [gN HNarrow HNcommute TN TNs].
  destruct M as [gM HMarrow HMcommute TM TMs].

  clear M N.
  simpl in *.
  clear TNs.
  clear TMs.



  destruct P as [U Uarrow PM fP HP Prep].
  destruct Q as [U' U'arrow QM fQ HQ Qrep];
  destruct R as [U'' U''arrow RM fR HR Rrep];
  clear P Q R;
  simpl in *.
  destruct Prep as [Papp Pabs Prec tttt
      ffff nats PSucc Pred Zero CondN CondB bottom].
  simpl in *.
  clear Papp Pabs Prec tttt ffff nats Pred Zero
     CondN CondB bottom.
  destruct Qrep as [Qapp Qabs Qrec tttt
      ffff nats QSucc Pred Zero CondN CondB bottom].
  simpl in *.
  clear Qapp Qabs Qrec tttt ffff nats Pred Zero
      CondN CondB bottom.
 destruct Rrep as [Rapp Rabs Rrec tttt
      ffff nats RSucc Pred Zero CondN CondB bottom].
  simpl in *.
  clear Rapp Rabs Rrec tttt ffff nats Pred Zero
      CondN CondB bottom.
  assert (HH:=mod_hom_mkl (Module_Hom_struct :=RSucc)).
simpl in HH.
assert (HH':= HH
(retype (fun t : U' => gN t) (retype (fun t : U => gM t) c))
(retype (fun t : U => gN (gM t)) c)).
simpl in HH'.

generalize dependent HH'.

generalize (RSucc (retype (fun t : U => gN (gM t)) c)).
intro RSucc1.
simpl in *.
generalize dependent RSucc1.

gendep HN.
generalize (
arrow_dist_ct2 (Uar:=U'arrow) (U'ar:=U''arrow) (g:=gN)
  HNarrow (f:=fQ)
     (f':=fR) HNcommute Nat Nat
).
gendep HM.
generalize (
arrow_dist_ct2 (Uar:=Uarrow) (U'ar:=U'arrow) (g:=gM)
 HMarrow (f:=fP)
     (f':=fQ) HMcommute Nat Nat
).

generalize (QSucc (retype (fun t => gM t) c)).
simpl.

generalize (RSucc (retype (fun t => gN t)
   (retype (fun t => gM t) c))).

intro RSucc1.
simpl in *.
gendep RSucc1.

rewrite <- (HNcommute).
rewrite <- (HNarrow).
rewrite <- (HMcommute).
rewrite <- (HMarrow).
intros.
rewrite (UIP_refl _ _ e) in HM.
simpl in HM.
rewrite (UIP_refl _ _ e0) in HN.
simpl in HN.
rewrite (UIP_refl _ _ e1).
simpl.
rewrite HM.
rewrite HN.
simpl.
unfold lift.
simpl.

rewrite <- HH'.
auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros c t.
  elim t.
  clear t.
  assert (HM:=Zero_Hom (PCF_rep_Hom_struct :=M)(c:=c) tt).
  assert (HN:=Zero_Hom (PCF_rep_Hom_struct :=N)
           (c:=retype(fun t => tcomp M t) c)tt).
  simpl in HM ,HN.

  generalize (
arrow_dist_ct2 (Uar:=type_arrow (p:=P)) (U'ar:=type_arrow (p:=R))
     (g:=fun t : type_type P => tcomp N (tcomp M t))
     (comp_arrow_dist (Uar:=type_arrow (p:=P))
(U'ar:=type_arrow (p:=Q))
        (g:=tcomp M) (tcomp_arrow M) (g':=tcomp N)
(U''ar:=type_arrow (p:=R))
        (tcomp_arrow N)) (f:=type_mor P) (f':=type_mor R)
     (comp_arrow_commute (g:=tcomp M) (f:=type_mor P)
(f':=type_mor Q)
        (ttriag M) (f'':=type_mor R) (g':=tcomp N)
(ttriag N)) Nat Bool
).
  destruct N as [gN HNarrow HNcommute TN TNs].
  destruct M as [gM HMarrow HMcommute TM TMs].

  clear M N.
  simpl in *.
  clear TNs.
  clear TMs.

  destruct P as [U Uarrow PM fP HP Prep].
  destruct Q as [U' U'arrow QM fQ HQ Qrep];
  destruct R as [U'' U''arrow RM fR HR Rrep];
  clear P Q R;
  simpl in *.
destruct Prep as [Papp Pabs Prec tttt
      ffff nats Succ Pred PZero CondN CondB bottom].
  simpl in *.
  clear Papp Pabs Prec tttt ffff nats Succ Pred
     CondN CondB bottom.
  destruct Qrep as [Qapp Qabs Qrec tttt
      ffff nats Succ Pred QZero CondN CondB bottom].
  simpl in *.
  clear Qapp Qabs Qrec tttt ffff nats Succ Pred
      CondN CondB bottom.
 destruct Rrep as [Rapp Rabs Rrec tttt
      ffff nats Succ Pred RZero CondN CondB bottom].
  simpl in *.
  clear Rapp Rabs Rrec tttt ffff nats Succ Pred
      CondN CondB bottom.
assert (HH:=mod_hom_mkl (Module_Hom_struct :=RZero)).
simpl in HH.
assert (HH':= HH
(retype (fun t : U' => gN t) (retype (fun t : U => gM t) c))
(retype (fun t : U => gN (gM t)) c)).
simpl in HH'.

gendep HH'.

generalize (RZero (retype (fun t : U => gN (gM t)) c)).
intro RZero1.
simpl in *.
gendep RZero1.

gendep HN.
generalize (
arrow_dist_ct2 (Uar:=U'arrow) (U'ar:=U''arrow) (g:=gN)
  HNarrow (f:=fQ)
     (f':=fR) HNcommute Nat Bool
).
gendep HM.
generalize (
arrow_dist_ct2 (Uar:=Uarrow) (U'ar:=U'arrow) (g:=gM)
 HMarrow (f:=fP)
     (f':=fQ) HMcommute Nat Bool
).

generalize (QZero (retype (fun t => gM t) c)).
intro QZero1.
simpl in *.
gendep QZero1.

generalize (RZero (retype (fun t => gN t)
   (retype (fun t => gM t) c))).

intro RZero1.
simpl in *.
gendep RZero1.

rewrite <- (HNcommute).
rewrite <- HNcommute.
rewrite <- (HNarrow).
rewrite <- (HMcommute).
rewrite <- HMcommute.
rewrite <- (HMarrow).
intros.
rewrite (UIP_refl _ _ e) in HM.
simpl in HM.
rewrite (UIP_refl _ _ e0) in HN.
simpl in HN.
rewrite (UIP_refl _ _ e1).
simpl.
rewrite HM.
rewrite HN.
simpl.
unfold lift.
simpl.

rewrite <- HH'.
auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros c t.
  elim t.
  clear t.
  assert (HM:=CondB_Hom (PCF_rep_Hom_struct :=M)(c:=c) tt).
  assert (HN:=CondB_Hom (PCF_rep_Hom_struct :=N)
           (c:=retype(fun t => tcomp M t) c)tt).
  simpl in HM ,HN.

  generalize (
arrow_dist_ct4 (Uar:=type_arrow (p:=P)) (U'ar:=type_arrow (p:=R))
     (g:=fun t : type_type P => tcomp N (tcomp M t))
     (comp_arrow_dist (Uar:=type_arrow (p:=P)) (U'ar:=type_arrow (p:=Q))
        (g:=tcomp M) (tcomp_arrow M) (g':=tcomp N)
(U''ar:=type_arrow (p:=R))
        (tcomp_arrow N)) (f:=type_mor P) (f':=type_mor R)
     (comp_arrow_commute (g:=tcomp M) (f:=type_mor P)
 (f':=type_mor Q)
        (ttriag M) (f'':=type_mor R) (g':=tcomp N) (ttriag N))
Bool Bool Bool
     Bool)
.
destruct N as [gN HNarrow HNcommute TN TNs].
  destruct M as [gM HMarrow HMcommute TM TMs].

  clear M N.
  simpl in *.
  clear TNs.
  clear TMs.



  destruct P as [U Uarrow PM fP HP Prep].
  destruct Q as [U' U'arrow QM fQ HQ Qrep];
  destruct R as [U'' U''arrow RM fR HR Rrep];
  clear P Q R;
  simpl in *.
destruct Prep as [Papp Pabs Prec tttt
      ffff nats Succ Pred Zero CondN PCondB bottom].
       
  simpl in *.
  clear Papp Pabs Prec tttt ffff nats Succ Pred Zero CondN bottom.
  destruct Qrep as [Qapp Qabs Qrec tttt
      ffff nats Succ Pred Zero CondN QCondB bottom].
  simpl in *.
  clear Qapp Qabs Qrec tttt ffff nats Succ Pred Zero CondN bottom.
 destruct Rrep as [Rapp Rabs Rrec tttt
      ffff nats Succ Pred Zero CondN RCondB bottom].
  simpl in *.
  clear Rapp Rabs Rrec tttt ffff nats Succ Pred Zero CondN bottom.

assert (HH:=mod_hom_mkl (Module_Hom_struct := RCondB)).
simpl in HH.
assert (HH':= HH
(retype (fun t : U' => gN t) (retype (fun t : U => gM t) c))
(retype (fun t : U => gN (gM t)) c)).
simpl in HH'.

gendep HH'.

generalize (RCondB (retype (fun t : U => gN (gM t)) c)).
intro RCondB1.
simpl in *.
gendep RCondB1.

gendep HN.
generalize (arrow_dist_ct4 (Uar:=U'arrow)
(U'ar:=U''arrow) (g:=gN) HNarrow (f:=fQ)
     (f':=fR) HNcommute Bool Bool Bool Bool).
gendep HM.
generalize (arrow_dist_ct4 (Uar:=Uarrow)
(U'ar:=U'arrow) (g:=gM) HMarrow (f:=fP)
     (f':=fQ) HMcommute Bool Bool Bool Bool).

generalize (QCondB (retype (fun t => gM t) c)).
intro QCondB1.
simpl in *.
gendep QCondB1.

generalize (RCondB (retype (fun t => gN t)
   (retype (fun t => gM t) c))).

intro RCondB1.
simpl in *.
gendep RCondB1.

rewrite <- (HNcommute).
rewrite <- (HNarrow).
rewrite <- (HNarrow).
rewrite <- (HNarrow).
rewrite <- (HMcommute).
rewrite <- (HMarrow).
rewrite <- (HMarrow).
rewrite <- (HMarrow).
intros.
rewrite (UIP_refl _ _ e) in HM.
simpl in HM.
rewrite (UIP_refl _ _ e0) in HN.
simpl in HN.
rewrite (UIP_refl _ _ e1).
simpl.
rewrite HM.
rewrite HN.
simpl.
unfold lift.
simpl.

rewrite <- HH'.
auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros c t.
  elim t.
  clear t.
  assert (HM:=CondN_Hom (PCF_rep_Hom_struct :=M)(c:=c) tt).
  assert (HN:=CondN_Hom (PCF_rep_Hom_struct :=N)
           (c:=retype(fun t => tcomp M t) c)tt).
  simpl in HM ,HN.

  generalize (
arrow_dist_ct4 (Uar:=type_arrow (p:=P)) (U'ar:=type_arrow (p:=R))
     (g:=fun t : type_type P => tcomp N (tcomp M t))
     (comp_arrow_dist (Uar:=type_arrow (p:=P))
   (U'ar:=type_arrow (p:=Q))
        (g:=tcomp M) (tcomp_arrow M) (g':=tcomp N)
(U''ar:=type_arrow (p:=R))
        (tcomp_arrow N)) (f:=type_mor P) (f':=type_mor R)
     (comp_arrow_commute (g:=tcomp M) (f:=type_mor P)
 (f':=type_mor Q)
        (ttriag M) (f'':=type_mor R) (g':=tcomp N) (ttriag N))
Bool Nat Nat Nat).
  destruct N as [gN HNarrow HNcommute TN TNs].
  destruct M as [gM HMarrow HMcommute TM TMs].

  clear M N.
  simpl in *.
  clear TNs.
  clear TMs.



  destruct P as [U Uarrow PM fP HP Prep].
  destruct Q as [U' U'arrow QM fQ HQ Qrep];
  destruct R as [U'' U''arrow RM fR HR Rrep];
  clear P Q R;
  simpl in *.
destruct Prep as [Papp Pabs Prec tttt
      ffff nats Succ Pred Zero PCondN CondB bottom].
       
  simpl in *.
  clear Papp Pabs Prec tttt ffff nats Succ Pred Zero
    CondB bottom.
  destruct Qrep as [Qapp Qabs Qrec tttt
      ffff nats Succ Pred Zero QCondN CondB bottom].
  simpl in *.
  clear Qapp Qabs Qrec tttt ffff nats Succ Pred Zero
   CondB bottom.
 destruct Rrep as [Rapp Rabs Rrec tttt
      ffff nats Succ Pred Zero RCondN CondB bottom].
  simpl in *.
  clear Rapp Rabs Rrec tttt ffff nats Succ Pred
  Zero CondB bottom.

assert (HH:=mod_hom_mkl (Module_Hom_struct := RCondN)).
simpl in HH.
assert (HH':= HH
(retype (fun t : U' => gN t) (retype (fun t : U => gM t) c))
(retype (fun t : U => gN (gM t)) c)).
simpl in HH'.

gendep HH'.

generalize (RCondN (retype (fun t : U => gN (gM t)) c)).
intro RCondN1.
simpl in *.
gendep RCondN1.

gendep HN.
generalize (arrow_dist_ct4 (Uar:=U'arrow)
(U'ar:=U''arrow) (g:=gN) HNarrow (f:=fQ)
     (f':=fR) HNcommute Bool Nat Nat Nat).
gendep HM.
generalize (arrow_dist_ct4 (Uar:=Uarrow)
(U'ar:=U'arrow) (g:=gM) HMarrow (f:=fP)
     (f':=fQ) HMcommute Bool Nat Nat Nat).

generalize (QCondN (retype (fun t => gM t) c)).
intro QCondN1.
simpl in *.
gendep QCondN1.

generalize (RCondN (retype (fun t => gN t)
   (retype (fun t => gM t) c))).

intro RCondN1.
simpl in *.
gendep RCondN1.

rewrite <- (HNcommute).
rewrite <- HNcommute.
rewrite <- (HNarrow).
rewrite <- (HNarrow).
rewrite <- (HNarrow).
rewrite <- (HMcommute).
rewrite <- HMcommute.
rewrite <- (HMarrow).
rewrite <- (HMarrow).
rewrite <- (HMarrow).
intros.
rewrite (UIP_refl _ _ e) in HM.
simpl in HM.
rewrite (UIP_refl _ _ e0) in HN.
simpl in HN.
rewrite (UIP_refl _ _ e1).
simpl.
rewrite HM.
rewrite HN.
simpl.
unfold lift.
simpl.

rewrite <- HH'.
auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros c t.
  elim t.
  clear t.
  assert (HM:=ttt_Hom (PCF_rep_Hom_struct :=M)(c:=c) tt).
  assert (HN:=ttt_Hom (PCF_rep_Hom_struct :=N)
           (c:=retype(fun t => tcomp M t) c)tt).
  simpl in HM ,HN.

  generalize (
comp_arrow_commute (g:=tcomp M) (f:=type_mor P)
  (f':=type_mor Q)
     (ttriag M) (f'':=type_mor R) (g':=tcomp N)
  (ttriag N) Bool
).
  destruct N as [gN HNarrow HNcommute TN TNs].
  destruct M as [gM HMarrow HMcommute TM TMs].

  clear M N.
  simpl in *.
  clear TNs.
  clear TMs.



  destruct P as [U Uarrow PM fP HP Prep].
  destruct Q as [U' U'arrow QM fQ HQ Qrep];
  destruct R as [U'' U''arrow RM fR HR Rrep];
  clear P Q R;
  simpl in *.
destruct Prep as [Papp Pabs Prec Ptttt
    ffff nats Succ Pred Zero CondN CondB bottom].
        
  simpl in *.
  clear Papp Pabs Prec ffff nats Succ Pred Zero
     CondN CondB bottom.
  destruct Qrep as [Qapp Qabs Qrec Qtttt
      ffff nats Succ Pred Zero CondN CondB bottom].
  simpl in *.
  clear Qapp Qabs Qrec ffff nats Succ Pred Zero
      CondN CondB bottom.
 destruct Rrep as [Rapp Rabs Rrec Rtttt
      ffff nats Succ Pred Zero CondN CondB bottom].
  simpl in *.
  clear Rapp Rabs Rrec ffff nats Succ Pred Zero
      CondN CondB bottom.

assert (HH:=mod_hom_mkl (Module_Hom_struct := Rtttt)).
simpl in HH.
assert (HH':= HH
(retype (fun t : U' => gN t) (retype (fun t : U => gM t) c))
(retype (fun t : U => gN (gM t)) c)).
simpl in HH'.

gendep HH'.

generalize (Rtttt (retype (fun t : U => gN (gM t)) c)).
intro Rtttt1.
simpl in *.
gendep Rtttt1.

gendep HN.
generalize (HNcommute Bool).
gendep HM.
generalize (HMcommute Bool).

generalize (Qtttt (retype (fun t => gM t) c)).
intro Qtttt1.
simpl in *.
gendep Qtttt1.

generalize (Rtttt (retype (fun t => gN t)
   (retype (fun t => gM t) c))).

intro Rtttt1.
simpl in *.
gendep Rtttt1.

rewrite <- (HNcommute).
rewrite <- (HMcommute).

intros.
rewrite (UIP_refl _ _ e) in HM.
simpl in HM.
rewrite (UIP_refl _ _ e0) in HN.
simpl in HN.
rewrite (UIP_refl _ _ e1).
simpl.
rewrite HM.
rewrite HN.
simpl.
unfold lift.
simpl.

rewrite <- HH'.
auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros c t.
  elim t.
  clear t.
  assert (HM:=fff_Hom (PCF_rep_Hom_struct :=M)(c:=c) tt).
  assert (HN:=fff_Hom (PCF_rep_Hom_struct :=N)
           (c:=retype(fun t => tcomp M t) c)tt).
  simpl in HM ,HN.

  generalize (
comp_arrow_commute (g:=tcomp M) (f:=type_mor P)
  (f':=type_mor Q)
     (ttriag M) (f'':=type_mor R) (g':=tcomp N)
  (ttriag N) Bool
).
  destruct N as [gN HNarrow HNcommute TN TNs].
  destruct M as [gM HMarrow HMcommute TM TMs].

  clear M N.
  simpl in *.
  clear TNs.
  clear TMs.



  destruct P as [U Uarrow PM fP HP Prep].
  destruct Q as [U' U'arrow QM fQ HQ Qrep];
  destruct R as [U'' U''arrow RM fR HR Rrep];
  clear P Q R;
  simpl in *.
destruct Prep as [Papp Pabs Prec tttt
      Pffff nats Succ Pred Zero CondN CondB bottom].
  simpl in *.
  clear Papp Pabs Prec tttt nats Succ Pred Zero
     CondN CondB bottom.
  destruct Qrep as [Qapp Qabs Qrec tttt
      Qffff nats Succ Pred Zero CondN CondB bottom].
  simpl in *.
  clear Qapp Qabs Qrec tttt nats Succ Pred Zero
      CondN CondB bottom.
 destruct Rrep as [Rapp Rabs Rrec tttt
      Rffff nats Succ Pred Zero CondN CondB bottom].
  simpl in *.
  clear Rapp Rabs Rrec tttt nats Succ Pred Zero
      CondN CondB bottom.

assert (HH:=mod_hom_mkl (Module_Hom_struct := Rffff)).
simpl in HH.
assert (HH':= HH
(retype (fun t : U' => gN t) (retype (fun t : U => gM t) c))
(retype (fun t : U => gN (gM t)) c)).
simpl in HH'.

gendep HH'.

generalize (Rffff (retype (fun t : U => gN (gM t)) c)).
intro Rffff1.
simpl in *.
gendep Rffff1.

gendep HN.
generalize (HNcommute Bool).
gendep HM.
generalize (HMcommute Bool).

generalize (Qffff (retype (fun t => gM t) c)).
intro Qffff1.
simpl in *.
gendep Qffff1.

generalize (Rffff (retype (fun t => gN t)
   (retype (fun t => gM t) c))).

intro Rffff1.
simpl in *.
gendep Rffff1.

rewrite <- (HNcommute).
rewrite <- (HMcommute).

intros.
rewrite (UIP_refl _ _ e) in HM.
simpl in HM.
rewrite (UIP_refl _ _ e0) in HN.
simpl in HN.
rewrite (UIP_refl _ _ e1).
simpl.
rewrite HM.
rewrite HN.
simpl.
unfold lift.
simpl.

rewrite <- HH'.
auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros m c t.
  elim t.
  clear t.
  assert (HM:=nats_Hom m (PCF_rep_Hom_struct :=M)(c:=c) tt).
  assert (HN:=nats_Hom m (PCF_rep_Hom_struct :=N)
           (c:=retype(fun t => tcomp M t) c)tt).
  simpl in HM ,HN.

  generalize (
comp_arrow_commute (g:=tcomp M) (f:=type_mor P)
  (f':=type_mor Q)
     (ttriag M) (f'':=type_mor R) (g':=tcomp N)
  (ttriag N) Nat
).
  destruct N as [gN HNarrow HNcommute TN TNs].
  destruct M as [gM HMarrow HMcommute TM TMs].

  clear M N.
  simpl in *.
  clear TNs.
  clear TMs.

  destruct P as [U Uarrow PM fP HP Prep].
  destruct Q as [U' U'arrow QM fQ HQ Qrep];
  destruct R as [U'' U''arrow RM fR HR Rrep];
  clear P Q R;
  simpl in *.
  destruct Prep as [Papp Pabs Prec tttt
    ffff Pnats Succ Pred Zero CondN CondB bottom].
  
  simpl in *.
  clear Papp Pabs Prec tttt ffff Succ Pred Zero
     CondN CondB bottom.
  destruct Qrep as [Qapp Qabs Qrec tttt
      ffff Qnats Succ Pred Zero CondN CondB bottom].
  simpl in *.
  clear Qapp Qabs Qrec tttt ffff Succ Pred Zero
      CondN CondB bottom.
 destruct Rrep as [Rapp Rabs Rrec tttt
      ffff Rnats Succ Pred Zero CondN CondB bottom].
  simpl in *.
  clear Rapp Rabs Rrec tttt ffff Succ Pred Zero
      CondN CondB bottom.

assert (HH:=mod_hom_mkl (Module_Hom_struct := Rnats m)).
simpl in HH.
assert (HH':= HH
(retype (fun t : U' => gN t) (retype (fun t : U => gM t) c))
(retype (fun t : U => gN (gM t)) c)).
simpl in HH'.

gendep HH'.

generalize (Rnats m (retype (fun t : U => gN (gM t)) c)).
intro Rnats1.
simpl in *.
gendep Rnats1.

gendep HN.
generalize (HNcommute Nat).
gendep HM.
generalize (HMcommute Nat).

generalize (Qnats m (retype (fun t => gM t) c)).
intro Qnats1.
simpl in *.
gendep Qnats1.

generalize (Rnats m (retype (fun t => gN t)
   (retype (fun t => gM t) c))).
intro Rnats1.
simpl in *.
gendep Rnats1.

rewrite <- (HNcommute).
rewrite <- (HMcommute).

intros.
rewrite (UIP_refl _ _ e) in HM.
simpl in HM.
rewrite (UIP_refl _ _ e0) in HN.
simpl in HN.
rewrite (UIP_refl _ _ e1).
simpl.
rewrite HM.
rewrite HN.
simpl.
unfold lift.
simpl.

rewrite <- HH'.
auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros u c t.
  elim t.
  clear t.
  assert (HM:=Bottom_Hom (PCF_rep_Hom_struct :=M)
        (c:=c) u tt).
  assert (HN:=Bottom_Hom (PCF_rep_Hom_struct :=N)
           (c:=retype(fun t => tcomp M t) c) (tcomp M u) tt).
  simpl in HM ,HN.

  rewrite HM.
  rewrite HN.
  unfold lift;
  simpl.
  assert (h:=mod_hom_mkl
    (Module_Hom_struct :=bottom (PCF_rep_struct := R)
      (tcomp N (tcomp M u)))).
  simpl in h.
  rewrite <- h.
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros t c y.
  assert (HM:=Rec_Hom (t:=t) (PCF_rep_Hom_struct :=M) (c:=c)y).
  assert (HN:=Rec_Hom (t:=tcomp M t) (PCF_rep_Hom_struct :=N)
           (c:=retype(fun t => tcomp M t) c)).
  simpl in HM ,HN.

  generalize (comp_arrow_dist (Uar:=type_arrow (p:=P))
      (U'ar:=type_arrow (p:=Q))
        (g:=tcomp M) (tcomp_arrow M) (g':=tcomp N)
      (U''ar:=type_arrow (p:=R))
        (tcomp_arrow N) t t).

  destruct N as [gN HNarrow HNcommute TN TNs].
  destruct M as [gM HMarrow HMcommute TM TMs].

  clear M N.
  simpl in *.
  clear TNs.
  clear TMs.
  clear HMcommute.
  clear HNcommute.
  rewrite HM.
  rewrite HN.
  clear HM.
  clear HN.

  destruct P as [U Uarrow PM fP HP Prep].
  destruct Q as [U' U'arrow QM fQ HQ Qrep];
  destruct R as [U'' U''arrow RM fR HR Rrep];
  clear P Q R;
  simpl in *.
destruct Prep as [Papp Pabs Prec tttt
      ffff nats Succ Pred Zero CondN CondB bottom].
  simpl in *.
  clear Papp Pabs tttt ffff nats Succ Pred Zero CondN CondB bottom.
  destruct Qrep as [Qapp Qabs Qrec tttt
      ffff nats Succ Pred Zero CondN CondB bottom].
  simpl in *.
  clear Qapp Qabs tttt ffff nats Succ Pred Zero CondN CondB bottom.
 destruct Rrep as [Rapp Rabs Rrec tttt
      ffff nats Succ Pred Zero CondN CondB bottom].
  simpl in *.
  clear Rapp Rabs tttt ffff nats Succ Pred Zero CondN CondB bottom.

intro e.
assert (r:=mod_hom_mkl (Module_Hom_struct := Rrec (gN (gM t)))).
simpl in r.
unfold lift at 1.
rewrite <- r.
apply f_equal.
simpl.
generalize (Rrec (gN (gM t))
  (retype (fun t : U' => gN t) (retype (fun t : U => gM t) c)))
   as RRec.
simpl in *.
intro RRec.
simpl in *.
generalize RRec.
generalize (Rrec (gN (gM t)) (retype (fun t : U => gN (gM t)) c))
   as RRec1.
simpl.
intro RRec1.
simpl in *.
generalize RRec1.
gendep e.
 rewrite <- HNarrow.
 rewrite <- HMarrow.

simpl.
intros.

rewrite (UIP_refl _ _ e).
simpl.
unfold lift.
simpl.
assert (H':= kl_eq RM).
simpl in H'.
apply H'.
simpl.
auto.
Qed.
Next Obligation.
Proof.

 simpl.
  intros u v c y.
  assert (HM:=App_Hom (u:=u)(v:=v)
        (PCF_rep_Hom_struct :=M) (c:=c)y).
  assert (HN:=App_Hom (u:=tcomp M u)
                      (v:=tcomp M v)
          (PCF_rep_Hom_struct :=N)
           (c:=retype(fun t => tcomp M t) c)).
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
  clear HMcommute.
  clear HNcommute.
  rewrite HM.
  rewrite  HN.
  simpl.
  clear HM.
  clear HN.

  destruct P as [U Uarrow PM fP HP Prep].
  destruct Q as [U' U'arrow QM fQ HQ Qrep];
  destruct R as [U'' U''arrow RM fR HR Rrep];
  clear P Q R;
  simpl in *.
  destruct Prep as [Papp Pabs Prec tttt
    ffff nats Succ Pred Zero CondN CondB bottom].
  simpl in *.
  clear Prec Pabs tttt ffff nats Succ Pred Zero CondN CondB bottom.
  destruct Qrep as [Qapp Qabs Qrec tttt
      ffff nats Succ Pred Zero CondN CondB bottom].
  simpl in *.
  clear Qrec Qabs Qrec tttt ffff nats Succ Pred Zero
      CondN CondB bottom.
 destruct Rrep as [Rapp Rabs Rrec tttt
      ffff nats Succ Pred Zero CondN CondB bottom].
  simpl in *.
  clear Rabs Rrec tttt ffff nats Succ Pred Zero
      CondN CondB bottom.

intro e.
assert (r:=mod_hom_mkl (Module_Hom_struct :=Rapp (gN (gM u)) (gN (gM v)))).
simpl in r.
unfold lift.
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
Next Obligation.
Proof.
simpl.
  intros u v c y.
  assert (HM:=Abs_Hom (u:=u)(v:=v)
        (PCF_rep_Hom_struct :=M) ).
  assert (HN:=Abs_Hom (u:=tcomp M u)
                      (v:=tcomp M v)
          (PCF_rep_Hom_struct :=N)
          ).
  simpl in HM ,HN.

  generalize ( eq_sym (
    comp_arrow_dist (Uar:=type_arrow (p:=P))
      (U'ar:=type_arrow (p:=Q))
        (g:=tcomp M) (tcomp_arrow M) (g':=tcomp N)
      (U''ar:=type_arrow (p:=R))
        (tcomp_arrow N) u v)
).

  destruct N as [gN HNarrow HNcommute TN TNs].
  destruct M as [gM HMarrow HMcommute TM TMs].

  clear M N.
  simpl in *.
  clear TNs.
  clear TMs.
  intro e.


  destruct P as [U Uarrow PM fP HP Prep].
  destruct Q as [U' U'arrow QM fQ HQ Qrep];
  destruct R as [U'' U''arrow RM fR HR Rrep];
  clear P Q R;
  simpl in *.
  destruct Prep as [Papp Pabs Prec tttt
    ffff nats Succ Pred Zero CondN CondB bottom].
  simpl in *.
  clear Prec Papp tttt ffff nats Succ Pred Zero CondN CondB bottom.
  destruct Qrep as [Qapp Qabs Qrec tttt
      ffff nats Succ Pred Zero CondN CondB bottom].
  simpl in *.
  clear Qrec Qapp tttt ffff nats Succ Pred Zero
      CondN CondB bottom.
 destruct Rrep as [Rapp Rabs Rrec tttt
      ffff nats Succ Pred Zero CondN CondB bottom].
  simpl in *.
  clear Rapp Rrec tttt ffff nats Succ Pred Zero
      CondN CondB bottom.

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
assert (H:=mod_hom_mkl
    (Module_Hom_struct := Rabs (gN (gM u)) (gN (gM v)))).
simpl in H.
unfold lift at 1.
rewrite <- H.
apply f_equal.
fold (lift (M:=RM)).
rew (lift_kleisli (M:= RM)).
rew (lift_lift RM).
assert (H':= MonadHomLift TN).
assert (H2 := H'
   (retype (fun t : U => gM t) (opt u c))
   (opt (gM u) (retype (fun t : U => gM t) c)) ).
(*    (@der_comm _ _ _ _ _ )). *)
rewrite <- H2.
rew (lift_kleisli (M:=RM)).

unfold lift.
apply (kl_eq RM).
simpl.
intros t z.
destruct z as [t z];
simpl.
destruct z as [t z];
simpl.
destruct z as [t z | ];
simpl;
auto.
unfold lift.
simpl.
rew (etakl RM).
Qed.
Next Obligation.
Proof.
  simpl.
  intros c t.
  elim t.
  clear t.
  assert (HM:=Pred_Hom (PCF_rep_Hom_struct :=M)(c:=c) tt).
  assert (HN:=Pred_Hom (PCF_rep_Hom_struct :=N)
           (c:=retype(fun t => tcomp M t) c)tt).
  simpl in HM ,HN.

  generalize (
arrow_dist_ct2 (Uar:=type_arrow (p:=P)) (U'ar:=type_arrow (p:=R))
     (g:=fun t : type_type P => tcomp N (tcomp M t))
     (comp_arrow_dist (Uar:=type_arrow (p:=P))
(U'ar:=type_arrow (p:=Q))
        (g:=tcomp M) (tcomp_arrow M) (g':=tcomp N)
(U''ar:=type_arrow (p:=R))
        (tcomp_arrow N)) (f:=type_mor P) (f':=type_mor R)
     (comp_arrow_commute (g:=tcomp M) (f:=type_mor P)
(f':=type_mor Q)
        (ttriag M) (f'':=type_mor R) (g':=tcomp N)
(ttriag N)) Nat Nat
).
  destruct N as [gN HNarrow HNcommute TN TNs].
  destruct M as [gM HMarrow HMcommute TM TMs].

  clear M N.
  simpl in *.
  clear TNs.
  clear TMs.



  destruct P as [U Uarrow PM fP HP Prep].
  destruct Q as [U' U'arrow QM fQ HQ Qrep];
  destruct R as [U'' U''arrow RM fR HR Rrep];
  clear P Q R;
  simpl in *.
destruct Prep as [Papp Pabs Prec tttt
      ffff nats Succ PPred Zero CondN CondB bottom].
  simpl in *.
  clear Papp Pabs Prec tttt ffff nats Succ Zero CondN
     CondB bottom.
  destruct Qrep as [Qapp Qabs Qrec tttt
      ffff nats Succ QPred Zero CondN CondB bottom].
  simpl in *.
  clear Qapp Qabs Qrec tttt ffff nats Succ Zero
      CondN CondB bottom.
 destruct Rrep as [Rapp Rabs Rrec tttt
      ffff nats Succ RPred Zero CondN CondB bottom].
  simpl in *.
  clear Rapp Rabs Rrec tttt ffff nats Succ Zero
      CondN CondB bottom.

assert (HH:=mod_hom_mkl (Module_Hom_struct :=RPred)).
simpl in HH.
assert (HH':= HH
(retype (fun t : U' => gN t) (retype (fun t : U => gM t) c))
(retype (fun t : U => gN (gM t)) c)).
simpl in HH'.

gendep HH'.

generalize (RPred (retype (fun t : U => gN (gM t)) c)).
intro RPred1.
simpl in *.
gendep RPred1.

gendep HN.
generalize (
arrow_dist_ct2 (Uar:=U'arrow) (U'ar:=U''arrow) (g:=gN)
  HNarrow (f:=fQ)
     (f':=fR) HNcommute Nat Nat
).
gendep HM.
generalize (
arrow_dist_ct2 (Uar:=Uarrow) (U'ar:=U'arrow) (g:=gM)
 HMarrow (f:=fP)
     (f':=fQ) HMcommute Nat Nat
).

generalize (QPred (retype (fun t => gM t) c)).
intro QPred1.
simpl in *.
gendep QPred1.

generalize (RPred (retype (fun t => gN t)
   (retype (fun t => gM t) c))).

intro RPred1.
simpl in *.
gendep RPred1.

rewrite <- (HNcommute).
rewrite <- (HNarrow).

rewrite <- (HMcommute).
rewrite <- (HMarrow).
intros.
rewrite (UIP_refl _ _ e) in HM.
simpl in HM.
rewrite (UIP_refl _ _ e0) in HN.
simpl in HN.
rewrite (UIP_refl _ _ e1).
simpl.
rewrite HM.
rewrite HN.
simpl.
unfold lift.
simpl.

rewrite <- HH'.
auto.
Qed.

Definition Rep_comp := Build_PCF_rep_Hom Rep_comp_struct.

End comp_red.
