Require Import Coq.Logic.FunctionalExtensionality.
(*Require Import Coq.Program.Equality.*)

Require Export CatSem.CAT.cat_INDEXED_TYPE.
Require Export CatSem.CAT.retype_functor.
Require Export CatSem.CAT.monad_h_morphism_gen.
Require Export CatSem.CAT.monad_h_module.
Require Export CatSem.PCF.PCF_types.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Notation "'TY'" := PCF.types.
Notation "'Bool'":= PCF.Bool.
Notation "'Nat'":= PCF.Nat.

Section rep.

Notation "'IT'" := (ITYPE TY).
Notation "a '~>' b" := (PCF.arrow a b) 
     (at level 69, right associativity).
Notation "a 'x' b" := (product (*C:= MOD _ _*) a b) (at level 30).
Notation "P [ z ]" := (ITFIB_MOD _ z P) (at level 35).
Notation "'d' P // s" := (ITDER_MOD _ _ s P) (at level 25).
Notation "'*'" := (Term (C:=MOD _ TYPE)).
Notation "f 'X' g" := (product_mor _ f g)(at level 30).

Section PCF_rep.

Variable U : Type.
Variable P : Monad (ITYPE U).
Variable f : TY -> U.

Variable Arrow : U -> U -> U.
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

Class PCF_rep_struct := {
  app : forall u v, (P[u ~~> v]) x (P[u]) ---> P[v];
  abs : forall u v, (d P //u)[v] ---> P[u ~~> v];
  rec : forall t, P[t ~~> t] ---> P[t];
  tttt :  * ---> P[f Bool];
  ffff :  * ---> P[f Bool];
  nats : forall m:nat, * ---> P[f Nat];
  Succ : * ---> P[f Nat ~~> f Nat];
  Pred : * ---> P[f Nat ~~> f Nat];
  Zero : * ---> P[f Nat ~~> f Bool];
  CondN: * ---> P[f Bool ~~> f Nat ~~> f Nat ~~> f Nat];
  CondB: * ---> P[f Bool ~~> f Bool ~~> f Bool ~~> f Bool];
  bottom: forall t, * ---> P[t]
}.

End PCF_rep.

Record PCF_rep := {
  type_type : Type;
  type_arrow : type_type -> type_type -> type_type;
  pcf_rep_monad :> Monad (ITYPE type_type);
  type_mor : TY -> type_type;
  type_arrow_dist : forall s t, type_mor (s ~> t) = 
                         type_arrow (type_mor s) (type_mor t);
  pcf_rep_struct :> PCF_rep_struct pcf_rep_monad type_mor type_arrow
               
}.

End rep.

Existing Instance pcf_rep_struct.
Notation "a ~~> b" := (type_arrow a b) 
         (at level 60, right associativity).

























