Require Export CatSem.CAT.retype_functor_po.
Require Export CatSem.CAT.rmonad_gen_type_po.
(*Require Export CatSem.PCF.PCF_types.*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

(*Notation "'TY'" := PCF.types.*)
(*
Notation "'Bool'" := PCF.Bool.
Notation "'Nat'" := PCF.Nat.
*)
(*
Notation "'IP'" := (IPO TY).
*)
(*Notation "a '~>' b" := (PCF.arrow a b) 
   (at level 69, right associativity).
*)
Notation "a 'x' b" := (product a b) (at level 30).
Notation "M [ z ]" := (FIB_RMOD _ z M) (at level 35).
Notation "'d' M // s" := (DER_RMOD _ _ s M) (at level 25).
Notation "'*'" := (Term (C:=RMOD _ Ord)).
(*
Check FIB_RMOD.
Check FIB_RMOD_HOM.
*)
(*
Notation "f 'X' g" := (product_mor _ f g)(at level 30).
Notation "'FM'" := (#(FIB_RMOD _ _ )).
Notation "'FPB'":= (FIB_RPB _ _ _ ).
Notation "'PRPB'":= (PROD_RPB _ _ _ _ ).
(*Notation "'PBF'":= (PB_FIB _ _ _ ).*)
Notation "'PBM'":= (#(PbRMOD _ _ )).
Notation "'DM'":= (#(DER_RMOD _ _ _ )).
Notation "'DPB'":= (DER_RPB _ _ _ ).
*)
Notation "y [* := z ]":= (Rsubstar z _ y)(at level 55).



Section PCF_rep.

Variable Sorts : Type.
Variable P : RMonad (IDelta Sorts).
 (*Variable f : TY -> U.*)

Variable Arrow : Sorts -> Sorts -> Sorts.
Variable Bool : Sorts.
Variable Nat : Sorts.
Notation "a ~~> b" := (Arrow a b) (at level 60, right associativity).

(*  don't put it here, but we need it in the record,
    for the initial morphism has to have this 
    property
Hypothesis type_arrow : forall s t, f (s ~> t) = f s ~~> f t.
*)

(** a monad is a representation if it is accompagnied by 
    - a lot of morphisms of modules 
    - beta-reduction
*)


(*Reserved Notation "a $ b" (at level 50, left associativity).*)
Reserved Notation "A @ B" (at level 15, B at next level, left associativity).
Class PCFPO_rep_struct := {
  app : forall u v, (P[u ~~> v]) x (P[u]) ---> P[v]
                       where "A @ B" := (app _ _ _ (A,B));
  abs : forall u v, (d P // u)[v] ---> P[u ~~> v];
  rec : forall t, P[t ~~> t] ---> P[t];
  tttt :  * ---> P[Bool];
  ffff :  * ---> P[Bool];
  nats : forall m:nat, * ---> P[Nat];
  Succ : * ---> P[Nat ~~> Nat];
  Pred : * ---> P[Nat ~~> Nat];
  Zero : * ---> P[Nat ~~> Bool];
  CondN: * ---> P[Bool ~~> Nat ~~> Nat ~~> Nat];
  CondB: * ---> P[Bool ~~> Bool ~~> Bool ~~> Bool];
  bottom: forall t, * ---> P[t];

  beta_red : forall r s V y z, 
        abs r s V y @ z << y[*:= z] ;
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
          CondN V tt @ tttt _ tt @ n @ m << n ;

(*
  CondN_t: forall V n m,
     app _ _ _ (app _ _ _ 
          (app _ _ _ (CondN V tt, tttt _ tt), 
                       n), m) << n ;
*)

  CondN_f: forall V n m,
          CondN V tt @ ffff _ tt @ n @ m << m ;

(*
  CondN_f: forall V n m,
     app _ _ _ (app _ _ _ 
          (app _ _ _ (CondN V tt, ffff _ tt), 
                       n), m) << m ;
*)

  CondB_t: forall V n m,
          CondB V tt @ tttt _ tt @ n @ m << n ;
 
(*
  CondB_t: forall V u v,
     app _ _ _ (app _ _ _ 
          (app _ _ _ (CondB V tt, tttt _ tt), 
                        u), v) << u ;
*)

  CondB_f: forall V n m,
          CondB V tt @ ffff _ tt @ n @ m << m ;

(*
  CondB_f: forall V u v,
     app _ _ _ (app _ _ _ 
          (app _ _ _ (CondB V tt, ffff _ tt), 
                       u), v) << v ;
*)

  Succ_red: forall V n,
     Succ V tt @ nats n _ tt << nats (S n) _ tt ;
  
(*
  Succ_red: forall V n,
     app _ _ _ (Succ V tt, nats n _ tt) << nats (S n) _ tt ;
*)

  Zero_t: forall V,
     Zero V tt @ nats 0 _ tt << tttt _ tt ;

(*
  Zero_t: forall V,
     app _ _ _ (Zero V tt, nats 0 _ tt) << tttt _ tt ;
*)

  Zero_f: forall V n,
     Zero V tt @ nats (S n) _ tt << ffff _ tt ;

(*
  Zero_f: forall V n,
     app _ _ _ (Zero V tt, nats (S n) _ tt) << ffff _ tt ;
*)

  Pred_Succ: forall V n,
     Pred V tt @ (Succ V tt @ nats n _ tt) << nats n _ tt;

(*
  Pred_Succ: forall V n,
     app _ _ _ (Pred V tt, app _ _ _ (Succ V tt, nats n _ tt)) <<
             nats n _ tt;
*)

  Pred_Z: forall V,
     Pred V tt @ nats 0 _ tt << nats 0 _ tt ;

(*
  Pred_Z: forall V,
     app _ _ _ (Pred V tt, nats 0 _ tt) << nats 0 _ tt ;
*)

  Rec_A: forall V t g,
     rec t V g << g @ rec _ _ g 
 
(*
  Rec_A: forall V t g,
     rec _ _ g << app t t V (g, rec _ _ g)
*)
 }.

Notation "A @ B" := (((app (PCFPO_rep_struct := _ ) _ _ ) _ ) (A, B)).

Print PCFPO_rep_struct.



End PCF_rep.

Record PCFPO_rep := {
  Sorts : Type;
  Arrow : Sorts -> Sorts -> Sorts;
  Bool : Sorts ;
  Nat : Sorts ;
  pcf_rep_monad :> RMonad (IDelta Sorts);
(*  type_mor : TY -> type_type; *)
(*  type_arrow_dist : forall s t, type_mor (s ~> t) = 
                         type_arrow (type_mor s) (type_mor t);*)
  pcf_rep_struct :> PCFPO_rep_struct pcf_rep_monad  Arrow Bool Nat
               
}.


Existing Instance pcf_rep_struct.
Notation "a ~~> b" := (Arrow a b) 
         (at level 60, right associativity).
(*
Notation "a @ b" := (app _ _ _ (a , b))(at level 40).
Check (fun (P : PCFPO_rep) (V : ITYPE (Sorts P)) a b => a @ b).
*)



