Require Export pcf_sub_rep.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Automatic Introduction.

Existing Instance pcfpo_rep_struct.

Section initial_rep.

Notation "'TY'" := PCF.TY.
Notation "'IP'" := (IO TY).
Notation "a '~>' b" := (PCF.arrow a b) (at level 69, right associativity).
(* Notation "a ~> b" := (Module_Hom a b) (at level 50).*)
(*Notation "a 'x' b" := (Prod_Mod _ a b) (at level 30).*)

Notation "a 'x' b" := (product (*C:= MOD _ _*) a b) (at level 30).

(* Notation "P ^ z" := (FIB_MOD _ z P). *)
Notation "P [ z ]" := (FIB_MOD _ z P) (at level 35).

(*Notation "P ''' s" := (DER_MOD _ _ s P ) (at level 25).*)
Notation "'d' P // s" := (DER_MOD _ _ s P) (at level 25).
(*Notation " '*' " := (Term (*C:=MOD _ _*)).*)
Notation "'*'" := (Term (C:=MOD _ SO)).
Notation "'Bool'" := PCF.Bool.
Notation "'Nat'" := PCF.Nat.

Notation "f 'X' g" := (product_mor (*C:= MOD _ _ *) _ f g)(at level 30).

Notation "'FM'" := (#(FIB_MOD _ _ )).
Notation "'FPB'":= (FIB_PB _ _ _ ).
Notation "'PRPB'":= (PROD_PB _ _ _ _ ).
Notation "'PBF'":= (PB_FIB _ _ _ ).
Notation "'PBM'":= (#(PB_MOD _ _ )).
Notation "'DM'":= (#(DER_MOD _ _ _ )).
Notation "'DPB'":= (DER_PB _ _ _ ).


(** need to have PCF.BETA as an object in PCFPO_REP *)

Definition PCFinit : Monad IP := PCFPO_monad.

(** a very boring part : definition of all the module morphisms we need *)
(*Lemma bla r s : 
(forall V : IP,
  (Prod_Mod (P:=PCFinit) SO_prod (Fibre_Mod (P:=PCFinit) PCFinit (r ~> s))
     (Fibre_Mod (P:=PCFinit) PCFinit r)) V --->
  (Fibre_Mod (P:=PCFinit) PCFinit s) V).
intros r s V.
simpl.
apply (fun y => PCF.App (fst y) (snd y)).*)

Program Instance PCFApp_struct (r s: TY): Module_Hom_struct
  (S:=Prod_Mod (P:=PCFinit) SO_prod 
 (Fibre_Mod (P:=PCFinit) PCFinit (r ~> s))
     (Fibre_Mod (P:=PCFinit) PCFinit r)) 
 (T:=Fibre_Mod (P:=PCFinit) PCFinit s) 
    (fun V y => PCF.App  (fst y) (snd y)).

Definition PCFApp (r s: TY) := Build_Module_Hom (PCFApp_struct r s).

Program Instance PCFLam_struct (r s: TY): Module_Hom_struct
  (S:= Fibre_Mod (P:=PCFinit)
     (IO_Der_Mod (P:=PCFinit)  PCFinit r) s)
  (T:=Fibre_Mod (P:=PCFinit) PCFinit (r ~> s))
    (fun V => PCF.Lam (V:=V) (t:=r)(s:=s) ).
Next Obligation.
Proof.
  apply f_equal.
  apply PCF.subst_eq.
  simpl.
  intros u y.
  destruct y; simpl; auto.
  unfold PCF.inj_. simpl.
  set (H:= PCF.subst_eq_rename).
  apply eq_sym. 
  apply H.
Qed.

Definition PCFLam (r s: TY) := Build_Module_Hom (PCFLam_struct r s).

Program Instance PCFRec_struct (t: TY) : Module_Hom_struct 
  (S:= Fibre_Mod (P:=PCFinit) PCFinit (t ~> t))
  (T:= Fibre_Mod (P:=PCFinit) PCFinit t)
   (fun V => PCF.Rec (V:=V) (t:=t)).

Definition PCFRec (t: TY) := Build_Module_Hom (PCFRec_struct t).

Program Instance PCFttt_struct : Module_Hom_struct 
  (S:=MOD_Term PCFinit SO_Terminal) 
  (T:=Fibre_Mod (P:=PCFinit) PCFinit Bool)
    (fun V _ => PCF.Const V PCF.ttt).

Definition PCFttt := Build_Module_Hom PCFttt_struct.

Program Instance PCFfff_struct : Module_Hom_struct 
  (S:=MOD_Term PCFinit SO_Terminal) 
  (T:=Fibre_Mod (P:=PCFinit) PCFinit Bool)
    (fun V _ => PCF.Const V PCF.fff).

Definition PCFfff := Build_Module_Hom PCFfff_struct.

Program Instance PCFsucc_struct : Module_Hom_struct 
  (S:=MOD_Term PCFinit SO_Terminal) 
  (T:=Fibre_Mod (P:=PCFinit) PCFinit (Nat ~> Nat))
    (fun V _ => PCF.Const V PCF.succ).

Definition PCFsucc := Build_Module_Hom PCFsucc_struct.

Program Instance PCFnats_struct (m: nat) : Module_Hom_struct
   (S:=MOD_Term PCFinit SO_Terminal) 
   (T:=Fibre_Mod (P:=PCFinit) PCFinit Nat)
    (fun V _ => PCF.Const V (PCF.Nats m)).

Definition PCFnats (m:nat) := Build_Module_Hom (PCFnats_struct m).

Program Instance PCFzero_struct : Module_Hom_struct 
  (S:=MOD_Term PCFinit SO_Terminal) 
  (T:=Fibre_Mod (P:=PCFinit) PCFinit (Nat ~> Bool))
    (fun V _ => PCF.Const V PCF.zero).

Definition PCFzero := Build_Module_Hom PCFzero_struct.

Program Instance PCFcondN_struct : Module_Hom_struct 
  (S:=MOD_Term PCFinit SO_Terminal) 
  (T:=Fibre_Mod (P:=PCFinit) PCFinit (Bool ~> Nat ~> Nat ~> Nat))
    (fun V _ => PCF.Const V PCF.condN).

Definition PCFcondN := Build_Module_Hom PCFcondN_struct.

Program Instance PCFcondB_struct : Module_Hom_struct 
  (S:=MOD_Term PCFinit SO_Terminal) 
  (T:=Fibre_Mod (P:=PCFinit) PCFinit (Bool ~> Bool ~> Bool ~> Bool))
    (fun V _ => PCF.Const V PCF.condB).

Definition PCFcondB := Build_Module_Hom PCFcondB_struct.

Program Instance PCFBottom_struct (t: TY) : Module_Hom_struct 
  (S:=MOD_Term PCFinit SO_Terminal) 
  (T:=Fibre_Mod (P:=PCFinit) PCFinit t)
    (fun V _ => PCF.Bottom V t).

Definition PCFBottom t:= Build_Module_Hom (PCFBottom_struct t).

(** finally PCF has a structure as a representation *)

Program Instance PCF_rep_struct : PCFPO_rep_struct PCFinit := { 
  App := PCFApp;
  Abs := PCFLam;
  Rec := PCFRec;
  ttt := PCFttt;
  fff := PCFfff;
  succ := PCFsucc;
  nats := PCFnats;
  zero := PCFzero;
  condN := PCFcondN;
  condB := PCFcondB;
  Bottom := PCFBottom
}.
Next Obligation.
Proof.
  apply PCF.clos.
  constructor.
  constructor.
Qed.
Next Obligation.
Proof.
  apply PCF.cp_App1.
  auto.
Qed.
Next Obligation.
Proof.
  apply PCF.cp_App2.
  auto.
Qed.
Next Obligation.
Proof.
  apply PCF.cp_Lam.
  auto.
Qed.
Next Obligation.
Proof.
  apply PCF.cp_Rec.
  auto.
Qed.

 

(** PCF is a representation of PCFPO *)

Definition PCF_rep : PCFPO_REP := Build_PCFPO_rep PCF_rep_struct.

(** for any representation R, we need PCFPO_rep_Hom PCF_rep R 
    [ PCF_rep ---> R ]
*)
(** let's get a monad morphism first, add rep structure later *)

Section monad_hom.


Variable R: PCFPO_rep.

(**   the function [(PCF V t) -> (R V t)] *)
(**   no structure of morphism yet, i.e. later we should prove that
      this is a monotone map (in each fibre) *)

Definition init_d (V:IP) : PCF.BETA V ---> R V.
intros V t v.
simpl.
induction v; simpl.
apply (Bottom t V tt).
destruct c.
apply (nats n V tt).
apply (ttt V tt).
apply (fff V tt).
apply (succ V tt).
apply (zero V tt).
apply (condN V tt).
apply (condB V tt).
(*apply (weta (Monad_struct := R)).*)
apply (weta (Monad_struct := R) V t i).
apply (App s t  V (IHv1, IHv2)).
apply (Abs _ _ V IHv).
apply (Rec _ V IHv).
Defined.


(*
Definition init_d (V:IP) (t:TY):
 (PCF.PCF V t) -> (R V t).
intros V t v.
simpl.
induction v; simpl.
apply (Bottom t V tt).
destruct c.
apply (nats n V tt).
apply (ttt V tt).
apply (fff V tt).
apply (succ V tt).
apply (zero V tt).
apply (condN V tt).
apply (condB V tt).
(*apply (weta (Monad_struct := R)).*)
apply (weta (Monad_struct := R) V t i).
apply (App s t  V (IHv1, IHv2)).
apply (Abs _ _ V IHv).
apply (Rec _ V IHv).
Defined.

*)


(** a lemma *)

Lemma UARGH (s t:TY) (RR: * ---> R [t]) (V: IP) 
                 (f:opt_TP s V ---> R V): 
RR V tt = (kleisli f t) (((RR) (opt_TP s V)) tt).
Proof.
  intros.
  set (H:= @mod_hom_mkl _ _ _ R _ _ _ 
       (Term (C:=MOD _ SO)) (FIB_MOD R t R) _ 
         RR  ).
  simpl in *.
  rewrite (H (opt_TP s V) V f).
  auto.
Qed.
(**   would require init_d to be a morphism... :-)


 this lemma says
    [ i (M >>= f) = iM >>= (i o f) ] 
   but of course it is not accepted by coq
*)
(*
Lemma kleisli_PCFsubst V t (M : PCF.BETA V t) W (f : V ---> PCF.BETA W):
        init_d (PCF.subst f M) =     
     kleisli (Monad_struct := R) (f;; init_d (V:= W) ) _ (init_d M).
Proof.
  intros V t M.
  induction M;
  simpl; intros.
  rewrite <- (@UARGH _ _ (Bottom t)).
  assert (H:=mod_hom_kl).

Lemma kleisli_PCFsubst V (s t:TY) (M: PCF.PCF (opt_TP s V) t) f:
       init_d (PCF.subst f M) = 
        kleisli (fun t => fun e => init_d (f t e))
                          (init_d M).
 *)
(**   this lemma is the same as preceding, but only for substitution of 
      the additional variable *

     [ i (M [* := N] ) = iM [* := iN] ]

but the assertion is not strong enough for induction

*)
(*

Lemma helper (s t:TY) (V:PCF.ipo) N:
 (opt_TP_def_varinj (P:=R) t (V:=opt_TP s V) (W:=V)
      (IPsubst_map (R:=R) (V:=V) (r:=s) (init_d (V:=V) (t:=s) N))) ==
  IPsubst_map (init_d  (? N)).
*)

(*
Lemma substar_IPsubstar 
(V : IP)
(s : TY)
(t : TY)
(M : PCF.PCF (opt_TP s V) t)
(N : PCF.PCF V s) : 
 
 init_d (V:=V) (t:=t) (PCF.substar N M) = 
         IPsubstar (R:=R) (r:=s) (init_d N) _ (init_d M).
Proof.
(*  unfold PCF.substar.
  unfold IPsubstar.*)
  intros V s t M.
  dependent induction M.
  
    simpl; intros.
    unfold IPsubstar.
    apply (@UARGH s t(Bottom t) V).
    
    simpl; intro N.
      destruct c; simpl;
      unfold IPsubstar;
      simpl.
      apply (@UARGH s Nat (nats n) V).
      apply (@UARGH s Bool ttt V).
      apply (@UARGH s Bool fff V).
      apply (@UARGH s _ succ V).
      apply (@UARGH s _ zero V).
      apply (@UARGH s _ condN V).
      apply (@UARGH s _ condB V).
 
    intros. 
    unfold IPsubstar.
    set (H:= eta_kl (Monad_struct := R)).
    simpl in *.
    unfold PCF.substar.
    unfold ind_po_comp,PreOrder_comp,
       eq_ind_po,eq_PreOrder in *.
    simpl in *.
    rewrite H.
    simpl.
    destruct p; simpl; auto.
    
    intros N.
    simpl in *.
    unfold PCF.substar in IHM1,IHM2.
    rewrite IHM1.
    rewrite IHM2.
    unfold IPsubstar.
    set (H:= @mod_hom_mkl _ _ _ R _ _ _ 
                _ _ _ (App s0 t)).
    simpl in H.
    unfold eq_PreOrder,PreOrder_comp in H.
    simpl in H.
    set (H1 := H _ _ (IPsubst_map (init_d N))
               (init_d M1, init_d M2)).
    simpl in H1.
    simpl.
    rewrite H1. auto.

    intros N.
    simpl in *.
    set (H':= @mod_hom_mkl _ _ _ R _ _ _ 
              _ _ _ (Abs t s0)).
     simpl in H'.
     unfold eq_PreOrder,PreOrder_comp in H'.
     simpl in *.
     unfold IPsubstar.
     rewrite <- H'.
     apply f_equal.
     unfold der_mkl.
     simpl.
     unfold IPsubstar in IHM.
    
     unfold IPsubst_map.
     simpl.
     (*rewrite <- IHM.
(*   assert (H': opt_TP_def_varinj (IPsubst_map (init_d N)) =
                 IPsubst_map (init_d  (opt_TP_def_varinj ( N))).
*)
      (*  
    intros N.
    simpl.
    unfold PCF.substar in IHM;
    simpl in IHM.
    rewrite IHM.
   *) 
Admitted.
(*    
rewrite  IHM.
    unfold IPsubst_map.
 unfold IPsubst_map_.
 unfold kleisli.
 simpl.

 N.
 unfold PCF.substar.
 unfold IPsubstar.
 simpl.
 unfold kleisli.

H' := beta
   : forall (r s : TY) (V : ind_po_obj TY) (y : R (opt_TP r V) s) (z : R V r),
     ((App r s) V) (((Abs r s) V) y, z) <<
     (IPsubstar (R:=R) (r:=r) (V:=V) z s) y
______________________________________(1/6)
((App s t) V)
  (((Abs s t) V) (bla1 (V:=opt_TP s V) (t:=t) M), bla1 (V:=V) (t:=s) N) <<
bla1 (V:=V) (t:=t) (PCF.substar M N)

*)
*)

(** IMPORTANT LEMMA: our function i: PCF -> R is a morphism *)

(*
Program Instance init_struct (V:IP) (t:TY):
PO_mor_struct (*PCF.BETA V t*) (*R V t*) (@init_d V t).
Next Obligation.
Proof.
  unfold Proper; red.
  intros y z H; simpl.
  induction H.
  apply POprf.
  transitivity (init_d y); auto.
  clear H0.
  clear IHclos_refl_trans_1n.
  clear z.
  induction H; simpl.
  induction H; simpl.
  
  Focus 2.
  set (H':= @weta _ _ _ _ R V t).
  apply H'; auto.

  Focus 2.
  apply (propag_App1 _  IHpropag).
  
  Focus 2.

  apply (propag_App2 (init_d (V:=V) (t:=s ~> t) M) IHpropag).

  Focus 2.
  apply (propag_Abs IHpropag).
  
  Focus 2.
  apply (propag_Rec IHpropag).
  
  rewrite substar_IPsubstar.
  set (H:= beta (PCFPO_rep_struct:=R)).
  simpl in *.
  apply H.
Qed.

Definition init V t := Build_PO_mor (init_struct V t).
*)
(*
R : PCFPO_rep
V : PCF.ipo
t : TY
Y : ind_po_obj TY
f : ind_po_mor (T:=TY) V (PCF.BETA Y)
______________________________________(1/6)
((Bottom t) Y) tt =
(kleisli (fun t0 : TY => PreOrder_comp (f t0) (init Y t0)) t)
  (((Bottom t) V) tt)

Lemma UARGH (s t:TY) (RR: * ---> R [t]) (V: IP) 
                 (f:opt_TP s V ---> R V): 
RR V tt = (kleisli f t) (((RR) (opt_TP s V)) tt).
*)
*)

(**  lemma, not important *)
Lemma UARGH2 (t:TY) (RR: * ---> R [t])
         (V Y:IP) (f: V ---> PCF.BETA Y) : 
RR  Y  tt = (kleisli (f ;; init_d (V:=Y))) t (RR V tt).
Proof.
  intros; simpl.
  set (H:= @mod_hom_mkl _ _ _ R _ _ _ 
               _ _ _ (RR)).
  simpl in *.
  apply H.
Qed.
(** lemma, not important *)

Lemma UARGH3 (t t0: TY) (RR: * ---> R[t0]) (V:IP) (f:V ---> (opt_TP t V)):
((RR) (opt_TP t V)) tt =
(lift (f) t0) (((RR) V) tt).
intros t t0 RR V f.
  set (H:= @mod_hom_mkl _ _ _ R _ _ _ 
                _ _ _ (RR)).
  simpl in *.
  simpl in H.
  unfold lift.
  apply H.
Qed.


Lemma init_d_lift V t (v : PCF.PCF V t) W (f : V ---> W) :
      init_d (PCF.rename f v) = lift f t (init_d v).
Proof.
 intros V t v.
  induction v. intros; simpl.
   unfold lift.
   assert (H:= @mod_hom_mkl _ _ _ R _ _ _ 
               _ _ _ (Bottom t)).
   simpl in H.
   rewrite <- H.
   auto.
    
   intros; destruct c; simpl.
     assert (H:= @mod_hom_mkl _ _ _ R _ _ _ 
               _ _ _ (nats n)).
               simpl in H.
               unfold lift.
               rewrite <- H.
               auto.

     assert (H:= @mod_hom_mkl _ _ _ R _ _ _ 
               _ _ _ (ttt)).
               simpl in H.
               unfold lift.
               rewrite <- H.
               auto.

     assert (H:= @mod_hom_mkl _ _ _ R _ _ _ 
               _ _ _ (fff)).
               simpl in H.
               unfold lift.
               rewrite <- H.
               auto.

     assert (H:= @mod_hom_mkl _ _ _ R _ _ _ 
               _ _ _ (succ)).
               simpl in H.
               unfold lift.
               rewrite <- H.
               auto.

     assert (H:= @mod_hom_mkl _ _ _ R _ _ _ 
               _ _ _ (zero)).
               simpl in H.
               unfold lift.
               rewrite <- H.
               auto.

     assert (H:= @mod_hom_mkl _ _ _ R _ _ _ 
               _ _ _ (condN)).
               simpl in H.
               unfold lift.
               rewrite <- H.
               auto.

     assert (H:= @mod_hom_mkl _ _ _ R _ _ _ 
               _ _ _ (condB)).
               simpl in H.
               unfold lift.
               rewrite <- H.
               auto.
               
    intros W f;
    simpl. 
    assert (H:=lift_weta R).
    simpl in *.
    rewrite H.
    auto.
    
    intros W f.
    simpl.
    rewrite IHv1.
    rewrite IHv2.
    assert (H:= @mod_hom_mkl _ _ _ R _ _ _ 
               _ _ _ (App s t)).
               simpl in *.
               unfold lift.
               rewrite <- H.
               auto.

    intros W f.
    simpl in *.
    rewrite IHv.
    assert (H:= @mod_hom_mkl _ _ _ R _ _ _ 
               _ _ _ (Abs t s)).
               simpl in *.
               unfold lift.
               rewrite <- H.
               auto.
    apply f_equal.
    assert (H':=kleisli_oid (Monad_struct := R)).
    unfold Proper in H'.
    red in H'.
    simpl in *.
    apply H'.
      intros t1 y1.
      destruct y1;
      simpl;
      auto.
      assert (H2:=lift_weta R).
    simpl in *.
    rewrite H2.
    auto.
    
    intros W f.
    simpl in *.
    rewrite IHv.
    assert (H:= @mod_hom_mkl _ _ _ R _ _ _ 
               _ _ _ (Rec t)).
               simpl in *.
               unfold lift.
               rewrite <- H.
               auto.
Qed.

Lemma UARGH4 (t t0 : TY) Y v : 
init_d (V:=opt_TP t Y) (t:=t0) (PCF.inj_ t v) =
(lift (@Some_TP _ t Y) t0) (init_d (V:=Y) (t:=t0) v).
Proof.
  intros.
  unfold PCF.inj_.
  assert (H:= init_d_lift).
  simpl in *.
  rewrite <- H.
  auto.
Qed.

Obligation Tactic := idtac.

Program Instance Init_mor_Monad_rep_struct : Monad_Hom_struct 
      (P:=PCF_rep) (Q:=R) (@init_d).
(*    (fun V t => init V t).*)

Next Obligation.
Proof.
  intros V W f t v.
  generalize dependent W.
  simpl in *.
  induction v.
  intros Y f; simpl.
  apply (@UARGH2 t (Bottom t) _ _ f  ).
  
  intros Y f. simpl.
  destruct c; simpl.
    apply (@UARGH2 Nat (nats n) _ _ f).
    apply (@UARGH2 _ (ttt) _ _ f).
    apply (@UARGH2 _ fff _ _ f).
    apply (@UARGH2 _ succ _ _ f).
    apply (@UARGH2 _ zero _ _ f).
    apply (@UARGH2 _ condN _ _ f).
    apply (@UARGH2 _ condB _ _ f).

  intros Y f; simpl.
  set (H:= eta_kl (Monad_struct := R)).
  simpl in H.
  rewrite H. auto.
  
  intros Y f; simpl in *.
  rewrite IHv1.
  rewrite IHv2.
  set (H:= @mod_hom_mkl _ _ _ R _ _ _ 
                _ _ _ (App s t)).
  simpl in H.
  rewrite <- H.
  auto.
  
  intros Y f. 
  simpl in *.
  rewrite  IHv.
  
  set (H2:=@mod_hom_mkl _ _ _ R _ _ _ 
                _ _ _ (Abs t s)).
    simpl in *.

    rewrite <- H2.
    apply f_equal.
    set (H'':= kleisli_oid (Monad_struct := R)).
    unfold Proper in H''.
    red in H''.
    simpl in H''.
    simpl in *.
    apply H''.
    
    intros t1 y1.
    simpl in *.
    destruct y1;
    simpl;
    auto.
    unfold lift.
    simpl.
    unfold PCF.inj_.
    simpl in *.
  simpl.
  simpl in IHv.
  assert (H4:=UARGH4).
  unfold PCF.inj_ in H4.
  rewrite H4.
  auto.
  
  intros Y f; simpl in *.
  rewrite IHv.
  set (H:= @mod_hom_mkl _ _ _ R _ _ _ 
                _ _ _ (Rec t)).
  simpl in H.
  rewrite <- H.
  auto.
Qed.
Next Obligation.
Proof.
  intros V t v.
  simpl.
  auto.
Qed.

Definition INIT_monad_hom := Build_Monad_Hom Init_mor_Monad_rep_struct.

Lemma IRel_equal (V : IP) t (y z : V t) : y = z -> IRel (A:=V)(t:=t) y z.
Proof.
  intros V t y z H.
  rewrite H.
  reflexivity.
Qed.

Section INIT_monotone.

Hypothesis weta_monotone : forall V, 
     iMonotone (weta (Monad_struct := R) V).


Instance INIT_monotone V : iMonotone (init_d (V:=V)).
Proof.
  unfold iMonotone,Proper.
  red.
  intros V t y z H.
  induction H.
  reflexivity.
  
  transitivity (init_d y);
  auto.
  
  clear IHclos_refl_trans_1n.
  clear H0.
  clear z.
  
  induction H.
  
  induction H. simpl.
  assert (H:=monad_hom_kl (Monad_Hom_struct:=INIT_monad_hom)).
  simpl in *.
  unfold PCF.substar.
  assert (H':=@IRel_Trans _ (R V) t).
  unfold Transitive in H'.
  apply H' with (init_d (PCF.subst (fun (t0 : TY) (x0 : (opt_TP s V) t0) =>
         match x0 in (opt _ _ r) return (PCF.PCF V r) with
         | some t1 v0 => PCF.Var (V:=V) (t:=t1) v0
         | none => N
         end) M)); try reflexivity.

  rewrite H. simpl.
  assert (H2:=beta (PCFPO_rep_struct:=R)).
  simpl in H2.
  unfold IOsubstar in H2.
  
  unfold IPsubst_map in H2.
  unfold opt_TP_default,opt_default in H2.
  assert (H3:=H2 s t V (init_d M) (init_d N)).
  apply H' with (kleisli (Monad_struct := R)
          (fun (t : TY) (v : opt_TP s V t) =>
           match v in (opt _ _ t0) return ((R V) t0) with
           | some t' v' => weta (Monad_struct := R) V t' v'
           | none => init_d (V:=V) (t:=s) N
           end) t (init_d (V:=opt_TP s V) (t:=t) M)).
           auto.
  apply IRel_equal.
  assert (Hk:=kleisli_oid (Monad_struct := R)).
  unfold Proper in Hk. red in Hk.
  simpl in Hk.
  apply Hk.
   intros t1 y1.
   simpl in *.
   destruct y1;
   simpl; auto.

 
(*  simpl in *.
  unfold weta in H2.
  rewrite <- H.
  apply H2.
  unfold PCF.substar.
  simpl.
  unfold P
*)

Focus 2.
  simpl.
  assert (H':=propag_App1 (PCFPO_rep_struct := R)). 
    simpl in *. apply H'.
    auto.
Focus 2.
  simpl.
  assert (H':=propag_App2 (PCFPO_rep_struct := R)). 
    simpl in *. apply H'.
    auto.
Focus 2.
  simpl.
  assert (H':=propag_Abs (PCFPO_rep_struct := R)). 
    simpl in *. apply H'.
    auto.
Focus 2.
  simpl.
  assert (H':=propag_Rec (PCFPO_rep_struct := R)). 
    simpl in *. apply H'.
    auto.

   simpl.
   apply weta_monotone.
   auto.
Qed.

End INIT_monotone.


Obligation Tactic := simpl; intros V y; try elim y; auto.

Program Instance INIT_repr_hom_s : 
       PCFPO_rep_Hom_struct INIT_monad_hom.
Next Obligation.
Proof.
  intros t s z;
  elim z;
  simpl; auto.
Qed.
Next Obligation.
Proof.
  intros t s z;
  elim z;
  simpl; auto.
Qed.


Definition INIT_repr_hom := Build_PCFPO_rep_Hom INIT_repr_hom_s.

Lemma INIT_unique : forall f : PCF_rep ---> R,
           f == INIT_repr_hom.
Proof.
  simpl.
  intros f V t v.
  simpl in *.
  
  induction v.
  simpl.
  
  assert (H:= Bottom_Hom (PCFPO_rep_Hom_struct := f)).
  simpl in H.
  apply H.
  destruct c; simpl.
    set (H:= nats_Hom (PCFPO_rep_Hom_struct := f)n).
    simpl in H.
    apply H.
    set (H:= ttt_Hom (PCFPO_rep_Hom_struct := f)).
    simpl in H.
    apply H.
    set (H:= fff_Hom (PCFPO_rep_Hom_struct := f)).
    simpl in H.
    apply H.
    set (H:= succ_Hom (PCFPO_rep_Hom_struct := f)).
    simpl in H.
    apply H.
    set (H:= zero_Hom (PCFPO_rep_Hom_struct := f)).
    simpl in H.
    apply H.
    set (H:= condN_Hom (PCFPO_rep_Hom_struct := f)).
    simpl in H.
    apply H.
    set (H:= condB_Hom (PCFPO_rep_Hom_struct := f)).
    simpl in H.
    apply H.
  assert (H:=monad_hom_weta (Monad_Hom_struct := f)).
  simpl in H.
  apply H.
  set (H:= App_Hom (PCFPO_rep_Hom_struct := f)).
  simpl in *.
  rewrite <- IHv1.
  rewrite <- IHv2.
  apply (H _ _ _ (v1, v2)).
  
  simpl.
  rewrite <- (IHv).
  set (H:= Abs_Hom (PCFPO_rep_Hom_struct := f)).
  simpl in H.
  apply H.
  
  simpl in *.
  rewrite <- IHv.
  set (H:= Rec_Hom (PCFPO_rep_Hom_struct := f)).
  simpl in H.
  apply H.

Qed.

End monad_hom.

Program Instance PCFPO_INIT : Initial PCFPO_REP := {
  Init := PCF_rep;
  InitMor R := INIT_repr_hom R ;
  InitMorUnique R := @INIT_unique R
}.

End initial_rep.



(*
rogram Instance PCFPO_INIT : Initial PCFPO_REP := {
  InPit := PCF_rep
}.
Next Obligation.
simpl.
constructor.

*)



