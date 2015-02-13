
Require Export pcf_rep initial_terminal.

Require Export Coq.Program.Equality. (* for dependent induction *)


Set Implicit Arguments.
Unset Strict Implicit.

Unset Automatic Introduction.

Section initial_rep.


Notation "'TY'" := PCF.TY.
(*Notation "'IP'" := (IPO TY).*)
Notation "'IT'" := (ITYPE TY).
Notation "a '~>' b" := (PCF.arrow a b) (at level 69, right associativity).
(* Notation "a ~> b" := (Module_Hom a b) (at level 50).*)
(*Notation "a 'x' b" := (Prod_Mod _ a b) (at level 30).*)

(*Notation "a 'x' b" := (product (*C:= MOD _ _*) a b) (at level 30).*)

(* Notation "P ^ z" := (FIB_MOD _ z P). *)
Notation "P [ z ]" := (ITFIB_MOD _ z P) (at level 35).

(*Notation "P ''' s" := (DER_MOD _ _ s P ) (at level 25).*)
Notation "'d' P // s" := (ITDER_MOD _ _ s P) (at level 25).
(*Notation " '*' " := (Term (*C:=MOD _ _*)).*)
Notation "'*'" := (Term (C:=MOD _ TYPE)).
Notation "'Bool'" := PCF.Bool.
Notation "'Nat'" := PCF.Nat.

Notation "f 'X' g" := (product_mor (*C:= MOD _ _ *) _ f g)(at level 30).

Notation "'FM'" := (#(ITFIB_MOD _ _ )).
Notation "'FPB'":= (ITFIB_PB _ _ _ ).
Notation "'PRPB'":= (PROD_PB _ _ _ _ ). 
Notation "'PBF'":= (ITPB_FIB _ _ _ ).
Notation "'PBM'":= (#(PB_MOD _ _ )).
Notation "'DM'":= (#(ITDER_MOD _ _ _ )).
Notation "'DPB'":= (ITDER_PB _ _ _ ).
Notation "y [* := z ]":= (ITsubstar z y)(at level 55).


Definition PCFinit : Monad IT := PCF_monad.


(** a very boring part : definition of all the module morphisms we need *)

Program Instance PCFApp_struct (r s : TY) : 
Module_Hom_struct
  (S:=Prod_Mod (P:=PCFinit) TYPE_prod
     (ITFibre_Mod (P:=PCFinit) PCFinit (r ~> s))
     (ITFibre_Mod (P:=PCFinit) PCFinit r))
  (T:=ITFibre_Mod (P:=PCFinit) PCFinit s)
  (fun v z => PCF.App (fst z) (snd z)).

Definition PCFApp (r s: TY) := Build_Module_Hom (PCFApp_struct r s).

Program Instance PCFLam_struct (r s: TY): Module_Hom_struct
  (S:=ITFibre_Mod (P:=PCFinit)
     (IT_Der_Mod (P:=PCFinit) (D:=ITYPE_struct TY) PCFinit r) s)
  (T:=ITFibre_Mod (P:=PCFinit) PCFinit (r ~> s))
   (fun v z => PCF.Lam z).
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
  (S:= ITFibre_Mod (P:=PCFinit) PCFinit (t ~> t))
  (T:= ITFibre_Mod (P:=PCFinit) PCFinit t)
   (fun V z => PCF.Rec z).

Definition PCFRec (t: TY) := Build_Module_Hom (PCFRec_struct t).

Program Instance PCFttt_struct : Module_Hom_struct 
  (S:= MOD_Term PCFinit TYPE_term)
  (T:=ITFibre_Mod (P:=PCFinit) PCFinit Bool)
   (fun v _ => PCF.Const v PCF.ttt).

Definition PCFttt := Build_Module_Hom PCFttt_struct.

Program Instance PCFfff_struct : Module_Hom_struct 
  (S:= MOD_Term PCFinit TYPE_term)
  (T:=ITFibre_Mod (P:=PCFinit) PCFinit Bool)
   (fun v _ => PCF.Const v PCF.fff).

Definition PCFfff := Build_Module_Hom PCFfff_struct.

Program Instance PCFsucc_struct : Module_Hom_struct 
  (S:= MOD_Term PCFinit TYPE_term)
  (T:=ITFibre_Mod (P:=PCFinit) PCFinit _ )
   (fun v _ => PCF.Const v PCF.succ).

Definition PCFsucc := Build_Module_Hom PCFsucc_struct.

Program Instance PCFnats_struct (m: nat) : Module_Hom_struct
   (S:= MOD_Term PCFinit TYPE_term)
  (T:=ITFibre_Mod (P:=PCFinit) PCFinit _)
   (fun v _ => PCF.Const v (PCF.Nats m)).

Definition PCFnats (m:nat) := Build_Module_Hom (PCFnats_struct m).

Program Instance PCFzero_struct : Module_Hom_struct 
  (S:= MOD_Term PCFinit TYPE_term)
  (T:=ITFibre_Mod (P:=PCFinit) PCFinit _ )
   (fun v _ => PCF.Const v PCF.zero).

Definition PCFzero := Build_Module_Hom PCFzero_struct.

Program Instance PCFcondN_struct : Module_Hom_struct 
  (S:=MOD_Term PCFinit TYPE_term) 
  (T:=ITFibre_Mod (P:=PCFinit) PCFinit (Bool ~> Nat ~> Nat ~> Nat))
    (fun V _ => PCF.Const V PCF.condN).

Definition PCFcondN := Build_Module_Hom PCFcondN_struct.

Program Instance PCFcondB_struct : Module_Hom_struct 
  (S:=MOD_Term PCFinit _ ) 
  (T:=ITFibre_Mod (P:=PCFinit) PCFinit (Bool ~> Bool ~> Bool ~> Bool))
    (fun V _ => PCF.Const V PCF.condB).

Definition PCFcondB := Build_Module_Hom PCFcondB_struct.

Program Instance PCFBottom_struct (t: TY) : Module_Hom_struct 
  (S:=MOD_Term PCFinit _ ) 
  (T:=ITFibre_Mod (P:=PCFinit) PCFinit t)
    (fun V _ => PCF.Bottom V t).

Definition PCFBottom t:= Build_Module_Hom (PCFBottom_struct t).


Program Instance PCF_rep_struct : PCF_rep_struct PCFinit:= { 
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


(** PCF is a representation of PCFPO *)

Definition PCF_PCF_rep := Build_PCF_rep PCF_rep_struct.


Section monad_hom.


Variable R: PCF_rep.

(**   the function [(PCF V t) -> (R V t)] *)


Definition init_d (V:IT) (t:TY):
 (PCF.PCF V t) -> (R V t).
intros V t v.

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
apply (weta (Monad_struct := R) V t v).
apply (App s t  V (IHv1, IHv2)).
apply (Abs _ _ V IHv).
apply (Rec _ V IHv).
Defined.


(** some lemmata about how compilation commutes with 
    - rename (lift)
    - substitution (kleisli) (hidden in the instance declaration)
*)

Lemma init_d_rename (V : IT) t (v : PCF.PCF V t) W (f : V ---> W) : 
      init_d (PCF.rename_ f v) = 
        lift f _ (init_d v).
Proof.
  intros V t v.
  induction v; unfold lift; 
  simpl; intros.
  
  set (H:= @mod_hom_mkl _ _ _ R _ _ _ _ _ _  (Bottom t)).
  simpl in H.
  apply H.
  
  destruct c; intros; simpl.
    set (H:= @mod_hom_mkl _ _ _ R _ _ _ _ _ _  (nats n)).
    simpl in H.
    apply H.
    set (H:= @mod_hom_mkl _ _ _ R _ _ _ _ _ _  (ttt)).
    simpl in H.
    apply H.
    set (H:= @mod_hom_mkl _ _ _ R _ _ _ _ _ _  (fff)).
    simpl in H.
    apply H.
    set (H:= @mod_hom_mkl _ _ _ R _ _ _ _ _ _  (succ)).
    simpl in H.
    apply H.
    set (H:= @mod_hom_mkl _ _ _ R _ _ _ _ _ _  (zero)).
    simpl in H.
    apply H.
    set (H:= @mod_hom_mkl _ _ _ R _ _ _ _ _ _  (condN)).
    simpl in H.
    apply H.
    set (H:= @mod_hom_mkl _ _ _ R _ _ _ _ _ _  (condB)).
    simpl in H.
    apply H.
    set (H:= eta_kl (Monad_struct := R) ).
    simpl in H.
    rewrite H; auto.
    rewrite  IHv1.
    rewrite IHv2. 
        set (H:= @mod_hom_mkl _ _ _ R _ _ _ _ _ _  (App s t)).
        simpl in *.
        rewrite <- H.
        simpl. apply f_equal.
        unfold lift in *. simpl. auto.
     simpl.
    unfold lift in IHv.
    rewrite IHv.
    set (H:= @mod_hom_mkl _ _ _ R _ _ _ _ _ _  (Abs t s)).
        simpl in *.
        rewrite <- H.
        apply f_equal.
        assert (H':= kleisli_oid (Monad_struct := R)).
        unfold Proper in H'.  red in H'. 
        simpl in H'.
        unfold shift.
        simpl.
        apply H'.
        intros t0 x0; simpl.
        destruct x0; simpl; intros; auto.
        unfold lift.
        assert (H2:= eta_kl (Monad_struct:= R)).
        simpl in H2.
        rewrite H2. simpl. auto.
        
   rewrite IHv.
   set (H:= @mod_hom_mkl _ _ _ R _ _ _ _ _ _  (Rec t)).
   simpl in H.
   rewrite <- H.
   simpl; auto.
Qed.
        
    

Lemma init_d_inj (Y : IT) t t0 (v : PCF.PCF Y t0) : init_d (PCF.inj_ t v) =
kleisli (Monad_struct := R)
  (some t (A:=Y);; weta (opt t Y)) t0 (init_d v).
Proof.
  intros; simpl.
  unfold PCF.inj_.
  apply init_d_rename.
Qed.

(**  init_d is a monad morphism *)

Program Instance Init_Rep_mor : Monad_Hom_struct (P:=PCF_monad)
                                                 (Q:= R)
      (fun V t z => init_d  z).
Next Obligation.
Proof.
  generalize dependent Y.
  induction x; simpl;
  intros.
    set (H:= @mod_hom_mkl _ _ _ R _ _ _ _ _ _  (Bottom t)).
    simpl in H.
    apply H.
  
  destruct c; intros; simpl.
    set (H:= @mod_hom_mkl _ _ _ R _ _ _ _ _ _  (nats n)).
    simpl in H.
    apply H.
    set (H:= @mod_hom_mkl _ _ _ R _ _ _ _ _ _  (ttt)).
    simpl in H.
    apply H.
    set (H:= @mod_hom_mkl _ _ _ R _ _ _ _ _ _  (fff)).
    simpl in H.
    apply H.
    set (H:= @mod_hom_mkl _ _ _ R _ _ _ _ _ _  (succ)).
    simpl in H.
    apply H.
    set (H:= @mod_hom_mkl _ _ _ R _ _ _ _ _ _  (zero)).
    simpl in H.
    apply H.
    set (H:= @mod_hom_mkl _ _ _ R _ _ _ _ _ _  (condN)).
    simpl in H.
    apply H.
    set (H:= @mod_hom_mkl _ _ _ R _ _ _ _ _ _  (condB)).
    simpl in H.
    apply H.
    set (H:= eta_kl (Monad_struct := R) ).
    simpl in H.
    rewrite H; auto.
    rewrite IHx1.
    rewrite IHx2. 
        set (H:= @mod_hom_mkl _ _ _ R _ _ _ _ _ _  (App s t)).
        simpl in H.
        rewrite <- H.
        apply f_equal. simpl. auto.
    rewrite IHx.
        set (H:= @mod_hom_mkl _ _ _ R _ _ _ _ _ _  (Abs t s)).
        simpl in H.
        rewrite <- H.
        apply f_equal.
        assert (H':= kleisli_oid (Monad_struct := R)).
        unfold Proper in H'.  red in H'. 
        simpl in H'.
        unfold shift.
        simpl.
        apply H'.
        intros; simpl.
        destruct x0; simpl; intros; auto.
        unfold lift.
        rewrite init_d_inj. auto.
     rewrite IHx.
     set (H:= @mod_hom_mkl _ _ _ R _ _ _ _ _ _  (Rec t)).
     simpl in H.
     rewrite H. auto.
Qed.

(** init_d is not only a monad morphism, but even a morphism 
    of representations *)

Obligation Tactic := simpl; intros V x; try elim x; auto.

Program Instance Init_Rep_arrow : PCF_rep_Hom_struct (P:=PCF_PCF_rep)(R:=R)
     (Build_Monad_Hom Init_Rep_mor).
Next Obligation.
Proof.
  intro y;
  elim y. auto.
Qed.
Next Obligation.
Proof.
  intro y;
  elim y. auto.
Qed.



End monad_hom.

Section initial.

(**  PCF_PCF_rep is initial in the category PCF_REP *)

Obligation Tactic := idtac.

Program Instance PCF_rep_initial : Initial PCF_REP := {
  Init := PCF_PCF_rep;
  InitMor := fun a => Build_PCF_rep_Hom (Init_Rep_arrow a)
}.
Next Obligation.
Proof.
  intros b f.
  simpl.
  intros x t x0.
  generalize dependent f.
  generalize dependent b.
  induction x0; simpl; intros.
  set (H:= Bottom_Hom (PCF_rep_Hom_struct := f)).
  simpl in H.
  apply H.
  destruct c; simpl.
    set (H:= nats_Hom (PCF_rep_Hom_struct := f)n).
    simpl in H.
    apply H.
    set (H:= ttt_Hom (PCF_rep_Hom_struct := f)).
    simpl in H.
    apply H.
    set (H:= fff_Hom (PCF_rep_Hom_struct := f)).
    simpl in H.
    apply H.
    set (H:= succ_Hom (PCF_rep_Hom_struct := f)).
    simpl in H.
    apply H.
    set (H:= zero_Hom (PCF_rep_Hom_struct := f)).
    simpl in H.
    apply H.
    set (H:= condN_Hom (PCF_rep_Hom_struct := f)).
    simpl in H.
    apply H.
    set (H:= condB_Hom (PCF_rep_Hom_struct := f)).
    simpl in H.
    apply H.
  assert (H:=monad_hom_weta (Monad_Hom_struct := f)).
  simpl in H.
  apply H.
  set (H:= App_Hom (PCF_rep_Hom_struct := f)).
  simpl in H.
  rewrite <- (IHx0_1 b f).
  rewrite <- (IHx0_2 b f).
  apply (H _ _ _ (x0_1, x0_2)).
  
  rewrite <- (IHx0 b f).
  set (H:= Abs_Hom (PCF_rep_Hom_struct := f)).
  simpl in H.
  apply H.
  
  rewrite <- (IHx0 b f).
  set (H:= Rec_Hom (PCF_rep_Hom_struct := f)).
  simpl in H.
  apply H.

Qed.

End initial. 

End initial_rep.


