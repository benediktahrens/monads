
Require Import pcfpo_rep.

Require Export Coq.Program.Equality. (* for dependent induction *)


Set Implicit Arguments.
Unset Strict Implicit.

Unset Automatic Introduction.

Existing Instance pcfpo_rep_struct.


Section initial_rep.

Notation "'TY'" := PCF.TY.
Notation "'IP'" := (IPO TY).
Notation "a '~>' b" := (PCF.arrow a b) (at level 69, right associativity).
(* Notation "a ~> b" := (Module_Hom a b) (at level 50).*)
(*Notation "a 'x' b" := (Prod_Mod _ a b) (at level 30).*)
Notation "a 'x' b" := (product (*C:= MOD _ _*) a b) (at level 30).

(* Notation "P ^ z" := (FIB_MOD _ z P). *)
Notation "P [ z ]" := (FIB_MOD _ z P) (at level 35).

(*Notation "P ''' s" := (DER_MOD _ _ s P ) (at level 25).*)
Notation "'d' P // s" := (DER_MOD _ _ s P) (at level 25).
(*Notation " '*' " := (Term (*C:=MOD _ _*)).*)
Notation "'*'" := (Term (C:=MOD _ PO)).
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

Program Instance PCFApp_struct (r s: TY): Module_Hom_struct
  (S:=Prod_Mod (P:=PCFinit) PO_prod 
 (Fibre_Mod (P:=PCFinit) PCFinit (r ~> s))
     (Fibre_Mod (P:=PCFinit) PCFinit r)) 
 (T:=Fibre_Mod (P:=PCFinit) PCFinit s) (fun V => PCF.AppPO V r s).

Definition PCFApp (r s: TY) := Build_Module_Hom (PCFApp_struct r s).

Program Instance PCFLam_struct (r s: TY): Module_Hom_struct
  (S:= Fibre_Mod (P:=PCFinit)
     (IPO_Der_Mod (P:=PCFinit) (D:=IPO_struct TY) PCFinit r) s)
  (T:=Fibre_Mod (P:=PCFinit) PCFinit (r ~> s))
    (fun V => PCF.LamPO V r s).
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
   (fun V => PCF.RecPO V t).

Definition PCFRec (t: TY) := Build_Module_Hom (PCFRec_struct t).

Program Instance PCFttt_struct : Module_Hom_struct 
  (S:=MOD_Term PCFinit PO_Terminal) 
  (T:=Fibre_Mod (P:=PCFinit) PCFinit Bool)
    (fun V => PCF.ConstsPO PCF.ttt V).

Definition PCFttt := Build_Module_Hom PCFttt_struct.

Program Instance PCFfff_struct : Module_Hom_struct 
  (S:=MOD_Term PCFinit PO_Terminal) 
  (T:=Fibre_Mod (P:=PCFinit) PCFinit Bool)
    (fun V => PCF.ConstsPO PCF.fff V).

Definition PCFfff := Build_Module_Hom PCFfff_struct.

Program Instance PCFsucc_struct : Module_Hom_struct 
  (S:=MOD_Term PCFinit PO_Terminal) 
  (T:=Fibre_Mod (P:=PCFinit) PCFinit (Nat ~> Nat))
    (fun V => PCF.ConstsPO PCF.succ V).

Definition PCFsucc := Build_Module_Hom PCFsucc_struct.

Program Instance PCFnats_struct (m: nat) : Module_Hom_struct
   (S:=MOD_Term PCFinit PO_Terminal) 
   (T:=Fibre_Mod (P:=PCFinit) PCFinit Nat)
    (fun V => PCF.ConstsPO (PCF.Nats m) V).

Definition PCFnats (m:nat) := Build_Module_Hom (PCFnats_struct m).

Program Instance PCFzero_struct : Module_Hom_struct 
  (S:=MOD_Term PCFinit PO_Terminal) 
  (T:=Fibre_Mod (P:=PCFinit) PCFinit (Nat ~> Bool))
    (fun V => PCF.ConstsPO PCF.zero V).

Definition PCFzero := Build_Module_Hom PCFzero_struct.

Program Instance PCFcondN_struct : Module_Hom_struct 
  (S:=MOD_Term PCFinit PO_Terminal) 
  (T:=Fibre_Mod (P:=PCFinit) PCFinit (Bool ~> Nat ~> Nat ~> Nat))
    (fun V => PCF.ConstsPO PCF.condN V).

Definition PCFcondN := Build_Module_Hom PCFcondN_struct.

Program Instance PCFcondB_struct : Module_Hom_struct 
  (S:=MOD_Term PCFinit PO_Terminal) 
  (T:=Fibre_Mod (P:=PCFinit) PCFinit (Bool ~> Bool ~> Bool ~> Bool))
    (fun V => PCF.ConstsPO PCF.condB V).

Definition PCFcondB := Build_Module_Hom PCFcondB_struct.

Program Instance PCFBottom_struct (t: TY) : Module_Hom_struct 
  (S:=MOD_Term PCFinit PO_Terminal) 
  (T:=Fibre_Mod (P:=PCFinit) PCFinit t)
    (fun V => PCF.BottomPO V t).

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

Definition PCF_rep := Build_PCFPO_rep PCF_rep_struct.

(** for any representation R, we need PCFPO_rep_Hom PCF_rep R 
    [ PCF_rep ---> R ]
*)
(** let's get a monad morphism first, add rep structure later *)

Section monad_hom.


Variable R: PCFPO_rep.

(**   the function [(PCF V t) -> (R V t)] *)
(**   no structure of morphism yet, i.e. later we should prove that
      this is a monotone map (in each fibre) *)


Definition init_d (V:IP) (t:TY):
 (PCF.PCF2 V t) -> (R V t).
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
Definition init_d2 := 
fun (V : TY -> Type) (t : TY) (v : PCF.PCF V t) =>
PCF.PCF_rect
  (P:=fun (V0 : TY -> Type) (t0 : TY) (_ : PCF.PCF V0 t0) => (ipo_obj_carrier (R V0)) t0)
  (fun (V0 : TY -> Type) (t0 : TY) => ((Bottom t0) V0) tt)
  (fun (V0 : TY -> Type) (t0 : TY) (c : PCF.Consts t0) =>
   match c in (PCF.Consts t1) return ((R V0) t1) with
   | PCF.Nats n => ((nats n) V0) tt
   | PCF.ttt => (ttt V0) tt
   | PCF.fff => (fff V0) tt
   | PCF.succ => (succ V0) tt
   | PCF.zero => (zero V0) tt
   | PCF.condN => (condN V0) tt
   | PCF.condB => (condB V0) tt
   end) (fun (V0 : TY -> Type) (t0 : TY) (i : V0 t0) => (weta V0) t0 i)
  (fun (V0 : TY -> Type) (t0 s : TY) (_ : PCF.PCF V0 (s ~> t0))
     (IHv1 : (R V0) (s ~> t0)) (_ : PCF.PCF V0 s) (IHv2 : (R V0) s) =>
   ((App s t0) V0) (IHv1, IHv2))
  (fun (V0 : ipo_obj TY) (t0 s : TY) (_ : PCF.PCF (opt_T t0 V0) s)
     (IHv : (R (opt_T t0 V0)) s) => ((Abs t0 s) V0) IHv)
  (fun (V0 : TY -> Type) (t0 : TY) (_ : PCF.PCF V0 (t0 ~> t0))
     (IHv : (R V0) (t0 ~> t0)) => ((Rec t0) V0) IHv) v. 

     : forall (V : IP) (t : TY), PCF.PCF2 V t -> (R V) t

*)

Definition init_d2 (V:IP) (t:TY):
 (PCF.PCF2 V t) -> (R V t).
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



(** a lemma *)

Lemma UARGH (s t:TY) (RR: * ---> R [t]) (V: IP) 
                 (f:opt_TP s V ---> R V): 
RR V tt = (kleisli f t) (((RR) (opt_TP s V)) tt).
Proof.
  intros.
  set (H:= @mod_hom_mkl _ _ _ R _ _ _ 
       (Term (C:=MOD _ PO)) (FIB_MOD R t R) _ 
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

(**
[Lemma kleisli_PCFsubst (V:PCF.ipo) (s t:TY) (M: PCF.PCF (opt_TP s V) t) f:
       init_d (PCF.subst_ f M) = kleisli (fun s t => fun e => init_d (f e))
                          (init_d M).]
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

     unfold der_mkl in IHM.
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
*)
(*
Program Instance init_struct (V:IP) (t:TY):
PO_mor_struct (a:=PCF.BETA V t) (b:=R V t) (@init_d V t).
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
*)
(*
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

(*
(**  lemma, not important *)
Lemma UARGH2 (t:TY) (RR: * ---> R [t])
         (V Y:IP) (f: V ---> PCF.BETA Y) : 
RR  Y  tt = (kleisli (f ;; init Y)) t (RR V tt).
Proof.
  intros; simpl.
  set (H:= @mod_hom_mkl _ _ _ R _ _ _ 
               _ _ _ (RR)).
  simpl in *.
  unfold eq_PreOrder in H.
  simpl in H.
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
  unfold eq_PreOrder in H.
  simpl in H.
  unfold lift.
  apply H.
Qed.
*)
(*
Lemma UARGH3 (t t0: TY) (RR: * ---> R[t0]) (V:IP) f:
((RR) (opt_TP t V)) tt =
(lift (opt_TP_weta t V) t0) (((RR) V) tt).
Proof.
  intros t t0 RR V.
  set (H:= @mod_hom_mkl _ _ _ R _ _ _ 
                _ _ _ (RR)).
  simpl in *.
  unfold eq_PreOrder in H.
  simpl in H.
  unfold lift.
  apply H.
Qed.
*)

(*

Lemma UARGH5 (t t0: TY) Y v f: 
 init_d (V:= opt_TP t Y) (t:= t0) (PCF.rename_ (V:=Y) f v) = 
   (lift f t0) (init_d v).
Proof.
  intros t t0 Y v.
  generalize dependent t.
  induction v. intros; simpl.
   
    apply (@UARGH3 _ _ (Bottom t) _ f).
    
    intros; destruct c; simpl.
      apply (@UARGH3 _ _ (nats n) _ f).
      apply (@UARGH3 _ _ (ttt) _ f).
      apply (@UARGH3 _ _ (fff) _ f).
      apply (@UARGH3 _ _ (succ) _ f).
      apply (@UARGH3 _ _ (zero) _ f).
      apply (@UARGH3 _ _ (condN) _ f).
      apply (@UARGH3 _ _ (condB) _ f).
      
   intros; simpl.
   set (H:= eta_kl (Monad_struct := R)).
   simpl in H.
   unfold eq_ind_po,eq_PreOrder in H. 
   simpl in H. 
   unfold lift. rewrite H. auto.
   
   intros; simpl.
   rewrite IHv1.
   rewrite IHv2.
   unfold lift.
   set (H:= @mod_hom_mkl _ _ _ R _ _ _ 
                _ _ _ (App s t)).
   simpl in H.
   unfold eq_PreOrder,PreOrder_comp in H.
   simpl in H.
   
   rewrite( H _ _ _ (init_d v1, init_d v2)). auto.

   intros; simpl.
  
   simpl.
   unfold lift.
   simpl.
   set (H':= @mod_hom_mkl _ _ _ R _ _ _ 
               _ _ _ (Abs t s)).
    simpl in H'.
   unfold eq_PreOrder,PreOrder_comp,der_mkl in H'.
   simpl in H'.
   rewrite <- H'.
   apply f_equal.
   simpl.
   simpl in
   set (H:= eta_kl (Monad_struct := R)).
   simpl in H. unfold eq_ind_po,eq_PreOrder in H.
   simpl in H.
   rewrite (H.
   set (H':= IHv t (opt_TP_map t (A:=V) (B:=opt_TP t0 V) f)).
   rewrite (IHv t (opt_TP_map t (A:=V) (B:=opt_TP t0 V) f)).
   unfold lift. simpl.
   
   rewrite IHv.

      apply (@UARGH3 _ _ (nats n) _ f).
    set (H:= @mod_hom_mkl _ _ _ R _ _ _ 
                _ _ _ (Bottom t)).
    simpl in H.
    unfold eq_PreOrder in H; simpl in H.
    unfold lift.
    apply H.


*)
(*
Lemma UARGH4 (t t0 : TY) Y v : 
init_d (V:=opt_TP t Y) (t:=t0) (PCF.inj_ t v) =
(lift (opt_TP_weta t Y) t0) (init_d (V:=Y) (t:=t0) v).
Proof.
  intros.
  unfold PCF.inj_.
  unfold opt_TP_weta.
 
  dependent induction v; simpl.
  apply (@UARGH3 t t0 (Bottom t0) V).
  
  destruct c; simpl.
    apply (@UARGH3 t Nat (nats n) V).
    apply (@UARGH3 t _ (ttt) V).
    apply (@UARGH3 t _ fff V).
    apply (@UARGH3 t _ succ V).
    apply (@UARGH3 t _ zero V).
    apply (@UARGH3 t _ condN V).
    apply (@UARGH3 t _ condB V).
    
  set (H:= eta_kl (Monad_struct := R)).
  simpl in *.
  unfold eq_ind_po,eq_PreOrder in H;
  simpl in *.
  unfold lift. simpl.
  rewrite H. simpl. auto.
  
  unfold PCF.inj_ in IHv1,IHv2.
  rewrite IHv1.
  rewrite IHv2.
  unfold lift.
  set (H:= @mod_hom_mkl _ _ _ R _ _ _ 
                _ _ _ (App s t0)).
    simpl in H.
    unfold eq_PreOrder,PreOrder_comp in H.
    simpl in H.
    rewrite (H _ _ _ ((init_d v1, init_d v2))).
    auto.
   
  unfold PCF.inj_ in IHv.
  Admitted.
*)
  
(*
Program Instance Init_mor_Monad_rep_struct : Monad_Hom_struct 
      (P:=PCF_rep) (Q:=R) (@init).
(*    (fun V t => init V t).*)

Next Obligation.
Proof.
(*  unfold eq_ind_po.
  unfold eq_PreOrder.*)
(*  simpl.*)
  intros t v.
  generalize dependent Y.
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
  unfold ind_po_comp.
  simpl.
  set (H:= eta_kl (Monad_struct := R)).
  simpl in H.
  unfold eq_ind_po,eq_PreOrder in H.
  simpl in *.
  rewrite H. auto.
  
  intros Y f; simpl in *.
  rewrite IHv1.
  rewrite IHv2.
  set (H:= @mod_hom_mkl _ _ _ R _ _ _ 
                _ _ _ (App s t)).
  simpl in H.
  unfold eq_PreOrder,PreOrder_comp in H.
  simpl in H.
  rewrite <- H.
  auto.
  
  intros Y f. simpl.
  simpl in IHv.
  (*rewrite <- IHv.*)
(*  do 2 red. simpl.*)
(*  set (H':= IHv (opt_TP t Y) (PCF.shift _ f)).*)
  transitivity ((Abs t s Y) (init_d 
       (PCF.subst_ (fun t0 => PCF.shift t (V:=V) (W:=Y) f t0)v))).
       repeat apply f_equal. auto.
    rewrite IHv.
    set (H2:=@mod_hom_mkl _ _ _ R _ _ _ 
                _ _ _ (Abs t s)).
    simpl in *.
    unfold eq_PreOrder in *.
    unfold PCF.shift.
    unfold PCF.shift_.
    unfold der_mkl in *.
    simpl in *.
    
    rewrite <- H2.
    repeat apply f_equal.
    set (H'':= kleisli_oid (Monad_struct := R)).
    unfold Proper in H''.
    red in H''.
    simpl in H''.
    apply H''.
    unfold eq_ind_po,eq_PreOrder.
    simpl.
    intros t0 z.
    destruct z; simpl; auto.
    
    generalize (f t0 p).
    
      intro y.
      induction y; simpl.
      unfold PCF.inj_.
      unfold lift. simpl.
      unfold kleisli.
Admitted.

Next Obligation.
Admitted.
*)

End monad_hom.

(*
Program Instance PCFPO_INIT : Initial PCFPO_REP := {
  Init := PCF_rep
}.
Next Obligation.
simpl.
constructor.

*)

End initial_rep.


