Require Export  pcfpo_mod monad_h_module.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Automatic Introduction.

Section PCF_representation.

(** a lot of notation to make things readable *)

Notation "'TY'" := PCF.TY.
(*Notation "'IP'" := (IPO TY).*)
Notation "'IT'" := (ITYPE TY).
Notation "a '~>' b" := (PCF.arrow a b) (at level 69, right associativity).
(* Notation "a ~> b" := (Module_Hom a b) (at level 50).*)
(*Notation "a 'x' b" := (Prod_Mod _ a b) (at level 30).*)

Notation "a 'x' b" := (product (*C:= MOD _ _*) a b) (at level 30).

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


(** a monad is a representation if it is accompagnied by 
    - a lot of morphisms of modules 
    - beta-reduction
*)

Class PCF_rep_struct (P : Monad IT) := {
  App : forall r s, (P[r~>s]) x (P[r]) ---> P[s];
  Abs : forall r s, (d P // r)[s] ---> P[r ~> s];
  Rec : forall t, P[t ~> t] ---> P[t];
  ttt :  * ---> P[Bool];
  fff :  * ---> P[Bool];
  nats: forall m:nat, * ---> P[Nat];
  succ: * ---> P[Nat ~> Nat];
  zero : * ---> P[Nat ~> Bool];
  condN: * ---> P[Bool ~> Nat ~> Nat ~> Nat];
  condB: * ---> P[Bool ~> Bool ~> Bool ~> Bool];
  Bottom: forall t, * ---> P[t]
(*
  beta: forall r s V y z, 
        App _ _ _ (Abs r s V y, z) <<  (*IPsubstar z _ y*) y[*:= z] ;
  
  propag_App1: forall r s V y y' z,
        y << y' -> App r s V (y,z) << App _ _ _ (y',z) ;

  propag_App2: forall r s V y z z',
        z << z' -> App r s V (y,z) << App _ _ _ (y,z') ;

  propag_Abs: forall r s V y y',
        y << y' -> Abs r s V y << Abs _ _ _ y' ;
  
  propag_Rec: forall s V y y',
        y << y' -> Rec s V y << Rec _ _ y' 
*)
 
(*  
  these two are not necessary, since we are over PO
  
  beta_refl : forall r V (y : P V r), y << y ; 

  beta_trans : forall r V (a b c : P V r),
          a << b -> b << c -> a << c
*)
}.

(** the type of representations *)

Record PCF_rep := {
  pcf_rep_monad :> Monad IT;
  pcf_rep_struct :> PCF_rep_struct pcf_rep_monad
}.

Existing Instance pcf_rep_struct.

(** morphisms of representations *)

Section PCF_rep_Hom.

Variables P R : PCF_rep.

Section Rep_Hom_Class.

Variable Sig : Monad_Hom P R.

Notation "'sig'":= (PbMod_ind_Hom Sig).

Notation "'PBT_'" := (PBT Sig _ ).


(** for the constants we need a special morphism of modules 

    [* ---> (\Sigma * ) *]

    being the empty product  *)
(*
Lemma id_Term_PB_struct: 
   Module_Hom_struct (S:= Term (C:= MOD _ TYPE))  (T:=(PB_MOD Sig TYPE Term))  
                 (fun r => id (Term (C:=TYPE))).
Proof. 
  simpl.
  constructor.
  intros.
  rewrite idl.
  rewrite idr.
  simpl.
  auto.
Qed.


Definition PBT : Term ---> (PB_MOD Sig TYPE Term) :=
      Build_Module_Hom id_Term_PB_struct.

Lemma id_PT_Term_struct: 
   Module_Hom_struct (T:= Term (C:= MOD _ TYPE)) (S:=(PB_MOD Sig TYPE Term))  
                 (fun r => id (Term (C:=TYPE))).
Proof. 
  simpl.
  constructor.
  intros.
  rewrite idl.
  rewrite idr.
  simpl.
  auto.
Qed.

Definition TPB : (PB_MOD Sig TYPE Term) ---> Term := 
      Build_Module_Hom id_PT_Term_struct.
*)
(*
Notation "'FM'" := (!(FIB_MOD _ _ )).
Notation "'FPB'":= (FIB_PB _ _ _ ).
Notation "'PRPB'":= (PROD_PB _ _ _ _ ).
Notation "'PBF'":= (PB_FIB _ _ _ ).
Notation "'sig'":= (PbMod_ind_Hom Sig).
Notation "'PBM'":= (!(PB_MOD _ _ )).
Notation "'DM'":= (!(DER_MOD _ _ _ )).
Notation "'DPB'":= (DER_PB _ _ _ ).
*)


(** Sig : P -> R is a morphism of representations if it makes commute 
    all these weird diagrams
*)

Class PCF_rep_Hom_struct := {
  App_Hom: forall r s,  
        App r s ;; FM sig  == 
          (FM sig ;; FPB) X (FM sig ;; FPB);; 
                   PRPB ;; PBM (App r s) ;; PBF        ;
 
  Abs_Hom: forall r s, 
         Abs r s ;; FM sig ==
          FM (DM sig ;; DPB) ;; FPB ;; PBM (Abs r s) ;; PBF  ;

  Rec_Hom: forall t, 
         Rec t ;; FM sig ==
            FM sig ;; FPB ;; PBM (Rec t) ;; PBF ;

  ttt_Hom: ttt ;; FM sig ==
          PBT_ ;; PBM ttt ;; PBF ;
          
  fff_Hom: fff ;; FM sig ==
          PBT_ ;; PBM fff ;; PBF ;
          
  nats_Hom : forall m,
         nats m ;; FM sig ==
            PBT_ ;; PBM (nats m) ;; PBF ;

  succ_Hom: succ ;; FM sig ==
          PBT_ ;; PBM succ ;; PBF  ;

  zero_Hom: zero ;; FM sig ==
          PBT_ ;; PBM zero ;; PBF  ;

  condN_Hom: condN ;; FM sig ==
          PBT_ ;; PBM condN ;; PBF  ;

  condB_Hom: condB ;; FM sig ==
          PBT_ ;; PBM condB ;; PBF ;

  Bottom_Hom: forall t,
          Bottom t ;; FM sig ==
          PBT_ ;; PBM (Bottom t) ;; PBF

}.

End Rep_Hom_Class.

(** the type of morphismes of representations P -> R *)

Record PCF_rep_Hom := {
  rep_Hom_monad :> Monad_Hom P R ;
  rep_Hom_monad_struct :> PCF_rep_Hom_struct rep_Hom_monad
}.

End PCF_rep_Hom.
(*Existing Instance MONAD_struct.*)
Existing Instance rep_Hom_monad_struct.

(** on our way to a category of representations:
    - an equality on morphisms of reps*)

(** two morphisms are equal if their monad homs are equal,
     proof of "equivalence relation" is more or less already done in
           Monad_Hom_equiv *)
(*
Definition eq_Rep (P R: PCF_rep) : relation (PCF_rep_Hom P R) :=
       fun a c => rep_Hom_monad a == rep_Hom_monad c.
*)

Lemma eq_Rep_equiv (P R: PCF_rep) : 
   @Equivalence (PCF_rep_Hom P R) 
     (fun a c => rep_Hom_monad a == rep_Hom_monad c).
Proof.
 intros P R.
 assert (H:= Monad_Hom_equiv P R).
 destruct H as [Hr Hs Ht].
 constructor;
 simpl in *. 
 unfold Reflexive; intros; apply Hr.
 unfold Symmetric; intros r s; apply Hs.
 unfold Transitive; intros r s t; apply Ht.
Qed.

Definition eq_Rep_oid (P R : PCF_rep) := Build_Setoid (eq_Rep_equiv P R).


(** Identity Representation *)

Lemma Rep_id_struct (P : PCF_rep) : 
         PCF_rep_Hom_struct (Monad_Hom_id P).
Proof.
  intro P;
  unfold Monad_Hom_id.
  simpl.
  constructor;
  simpl;
  intros;
  try rewrite <- surjective_pairing;
  auto.
Qed.

Definition Rep_id (P: PCF_rep) := Build_PCF_rep_Hom (Rep_id_struct P).

(** Composition of Representations *)
Section Rep_comp.
Variables P Q R: PCF_rep.
Variable M: PCF_rep_Hom P Q.
Variable N: PCF_rep_Hom Q R.

Program Instance Rep_comp_struct : 
      PCF_rep_Hom_struct (Monad_Hom_comp M N).
Next Obligation.
Proof.
  set (HM:=App_Hom (Sig := M)).
  set (HN:=App_Hom (Sig := N)).
  simpl in *.
  rewrite HM.
  rewrite HN.
  auto.
Qed.
Next Obligation.
  set (HM:=Abs_Hom (Sig := M)).
  set (HN:=Abs_Hom (Sig := N)).
  simpl in *.
  
  rewrite HM.
  rewrite HN.
  auto.
Qed.
Next Obligation.
  set (HM:=Rec_Hom (Sig := M)).
  set (HN:=Rec_Hom (Sig := N)).
  simpl in *.
  
  rewrite HM.
  rewrite HN.
  auto.
Qed.
Next Obligation.
  set (HM:=ttt_Hom (Sig := M)).
  set (HN:=ttt_Hom (Sig := N)).
  simpl in *.
  
  rewrite HM.
  rewrite HN.
  auto.
Qed.
Next Obligation.
  set (HM:=fff_Hom (Sig := M)).
  set (HN:=fff_Hom (Sig := N)).
  simpl in *.
  
  rewrite HM.
  rewrite HN.
  auto.
Qed.
Next Obligation.
  set (HM:=nats_Hom (Sig := M)).
  set (HN:=nats_Hom (Sig := N)).
  simpl in *.
  
  rewrite HM.
  rewrite HN.
  auto.
Qed.
Next Obligation.
  set (HM:=succ_Hom (Sig := M)).
  set (HN:=succ_Hom (Sig := N)).
  simpl in *.
  
  rewrite HM.
  rewrite HN.
  auto.
Qed.
Next Obligation.
  set (HM:=zero_Hom (Sig := M)).
  set (HN:=zero_Hom (Sig := N)).
  simpl in *.
  
  rewrite HM.
  rewrite HN.
  auto.
Qed.
Next Obligation.
  set (HM:=condN_Hom (Sig := M)).
  set (HN:=condN_Hom (Sig := N)).
  simpl in *.
  
  rewrite HM.
  rewrite HN.
  auto.
Qed.
Next Obligation.
  set (HM:=condB_Hom (Sig := M)).
  set (HN:=condB_Hom (Sig := N)).
  simpl in *.
  
  rewrite HM.
  rewrite HN.
  auto.
Qed.
Next Obligation.
  set (HM:=Bottom_Hom (Sig := M)).
  set (HN:=Bottom_Hom (Sig := N)).
  simpl in *.
  
  rewrite HM.
  rewrite HN.
  auto.
Qed.

Definition Rep_comp := Build_PCF_rep_Hom Rep_comp_struct.

End Rep_comp.

(** category of representations *)

Program Instance PCF_REP_struct : Cat (fun a c => PCF_rep_Hom a c) := {
  mor_oid a c := eq_Rep_oid a c;
  id a := Rep_id a;
  comp P Q R f g := Rep_comp f g
}.
Next Obligation.
Proof.
  unfold Proper in *; do 2 red.
  simpl. 
  intros x' y H x0 y0 H0 x1 t g.
  rewrite H.
  rewrite H0.
  auto.
Qed.

Definition PCF_REP := Build_Category PCF_REP_struct.

End PCF_representation.

Existing Instance pcf_rep_struct.
















