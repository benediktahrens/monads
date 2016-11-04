Require Export Coq.Classes.RelationClasses.
Require Export Coq.Classes.Morphisms.
Require Import Coq.Relations.Relation_Definitions.

Require Export CatSem.CAT.cat_INDEXED_TYPE.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Automatic Introduction.

Section Classes.

Class Rel (X : Type) := rel : relation X.

Variable T : Type.

Class IRel (X : T -> Type) := irel :> forall t, Rel (X t).

Class IPreOrder {A} (R : IRel A) :=
   ipreorder :> forall t : T, PreOrder (R t) .


Class IMor {A}{B}(Ra : IRel A) (Rb : IRel B) (f : A ---> B) : Prop :=
  imor : forall t, Proper (irel (t:=t) ++> irel (t:=t)) (f t).

Inductive optrelT (u:T) (V: T -> Type) (R : IRel V) : IRel (opt u V) :=
  | optrelTP_none :  optrelT _ (none u V) (none u V)
  | optrelTP_some : forall t (y z:V t), R _ y z -> 
          optrelT _ (some _  y) (some _ z).


End Classes.

Existing Instance  optrelT.
