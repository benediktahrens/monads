Require Export CatSem.CAT.retype_functor_po.
Require Export CatSem.CAT.rmonad_gen_type_po.
Require Export CatSem.PCF.PCF_types.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Notation "'TY'" := PCF.types.
Notation "'Bool'" := PCF.Bool.
Notation "'Nat'" := PCF.Nat.

Notation "'IP'" := (IPO TY).
Notation "a '~>' b" := (PCF.arrow a b) 
   (at level 69, right associativity).
Notation "a 'x' b" := (product a b) (at level 30).
Notation "M [ z ]" := (FIB_RMOD _ z M) (at level 35).
Notation "'d' M // s" := (DER_RMOD _ _ s M) (at level 25).
Notation "'*'" := (Term (C:=RMOD _ PO)).

Notation "f 'X' g" := (product_mor _ f g)(at level 30).

Notation "'FM'" := (#(FIB_RMOD _ _ )).
Notation "'FPB'":= (FIB_RPB _ _ _ ).
Notation "'PRPB'":= (PROD_RPB _ _ _ _ ).
(*Notation "'PBF'":= (PB_FIB _ _ _ ).*)
Notation "'PBM'":= (#(PbRMOD _ _ )).
Notation "'DM'":= (#(DER_RMOD _ _ _ )).
Notation "'DPB'":= (DER_RPB _ _ _ ).

Notation "y [* := z ]":= (Rsubstar z _ y)(at level 55).



Section PCF_rep.

Variable U : Type.
Variable P : RMonad (SM_ipo U).
Variable f : TY -> U.

(** a monad is a representation if it is accompagnied by 
    - a lot of morphisms of modules 
    - beta-reduction
*)

Class PCFPO_rep_struct := {
  app : forall r s, (P[f (r~>s)]) x (P[f r]) ---> P[f s] 
       where "A @ B" := (app _ _ _ (A,B));
  abs : forall r s, (d P //(f r))[f s] ---> P[f (r ~> s)];
  rec : forall t, P[f (t ~> t)] ---> P[f t];
  tttt :  * ---> P[f Bool];
  ffff :  * ---> P[f Bool];
  nats : forall m:nat, * ---> P[f Nat];
  Succ : * ---> P[f (Nat ~> Nat)];
  Pred : * ---> P[f (Nat ~> Nat)];
  Zero : * ---> P[f (Nat ~> Bool)];
  CondN: * ---> P[f (Bool ~> Nat ~> Nat ~> Nat)];
  CondB: * ---> P[f (Bool ~> Bool ~> Bool ~> Bool)];
  bottom: forall t, * ---> P[f t];

  beta_red : forall r s V y z, 
        app r s V (abs r s V y, z) << y[*:= z] ;
(*  
  propag_app1: forall r s V y y' z,
        y << y' -> app r s V (y,z) << app _ _ _ (y',z) ;

  propag_app2: forall r s V y z z',
        z << z' -> app r s V (y,z) << app _ _ _ (y,z') ;

  propag_abs: forall r s V y y',
        y << y' -> abs r s V y << abs _ _ _ y' ;
	
  propag_rec: forall t V y y',
        y << y' -> rec t V y << rec _ _ y' ;
*)
  CondN_t: forall V n m,
     app _ _ _ (app _ _ _ 
          (app _ _ _ (CondN V tt, tttt _ tt), 
                       n), m) << n ;
  
  CondN_f: forall V n m,
     app _ _ _ (app _ _ _ 
          (app _ _ _ (CondN V tt, ffff _ tt), 
                       n), m) << m ;
 
  CondB_t: forall V u v,
     app _ _ _ (app _ _ _ 
          (app _ _ _ (CondB V tt, tttt _ tt), 
                        u), v) << u ;
  
  CondB_f: forall V u v,
     app _ _ _ (app _ _ _ 
          (app _ _ _ (CondB V tt, ffff _ tt), 
                       u), v) << v ;
  
  Succ_red: forall V n,
     app _ _ _ (Succ V tt, nats n _ tt) << nats (S n) _ tt ;

  Zero_t: forall V,
     app _ _ _ (Zero V tt, nats 0 _ tt) << tttt _ tt ;

  Zero_f: forall V n,
     app _ _ _ (Zero V tt, nats (S n) _ tt) << ffff _ tt ;

  (*Pred_Sn: forall V n,
     app _ _ _ (Pred V tt, nats (S n) _ tt) << nats n _ tt ;*)

  Pred_Succ: forall V n,
     app _ _ _ (Pred V tt, app _ _ _ (Succ V tt, nats n _ tt)) <<
             nats n _ tt;
   
  Pred_Z: forall V,
     app _ _ _ (Pred V tt, nats 0 _ tt) << nats 0 _ tt ;
  
  Rec_A: forall V t g,
     rec _ _ g << app t t V (g, rec _ _ g) 

(*
  Rec_B: forall V t g z, 
     rec _ _ g << z -> app t t V (g , rec _ _ g) << z;

  Rec_C: forall V t g, exists z,
     rec _ _ g << z /\ app t t V (g, rec _ _ g) << z ;

  Rec_D: forall V t g M, (forall s a b, M <> app s t _ (a, b)) ->
     app t t V (g, rec _ _ g) << M -> rec _ _ g << M
*)
}.


End PCF_rep.

Record PCFPO_rep := {
  type_type : Type;
  pcf_rep_monad :> RMonad (SM_ipo type_type);
  type_mor : TY -> type_type;
  pcf_rep_struct :> PCFPO_rep_struct pcf_rep_monad type_mor
}.


Existing Instance pcf_rep_struct.







