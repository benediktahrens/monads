Require Export CatSem.CAT.NT.
Require Export CatSem.CAT.CatFunct.
Require Import CatSem.CAT.initial_terminal.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Automatic Introduction.

(** content : 
       - categories J, C
       - ConstFunc : constant functor (but won't be used in the following)
       - DiagFunctor : Functor C  [J, C]
       - LIMIT A := Terminal (Cone A)
       - some functions for direct access to interesting parts of a limit
*)


Section defs.

Variable obC : Type.
Variable morC : obC -> obC -> Type.
Variable C : Cat_struct morC.

Variable obJ : Type.
Variable morJ : obJ -> obJ -> Type.
Variable J : Cat_struct morJ.

(** constant functor *)

Program Definition ConstFunc (c : obC) := Build_Functor 
     (Fobj := fun j: obJ => c)(Fmor := fun a b f => id c) _ .
Next Obligation.
Proof.
  constructor;
  [unfold Proper; red | 
          idtac | idtac ];
  cat.
Qed.

(** NT between constant functors, induced by f : a --> b *)

Section on_morphisms.
Variables a b : obC.
Variable f : morC a b.

Program Instance ConstFuncNatTrans : 
    NT_struct (F:=ConstFunc a) (G:=ConstFunc b) (fun _ => f).
Next Obligation.
Proof.
  cat.
Qed.

Definition ConstFuncNT := Build_NT ConstFuncNatTrans.

End on_morphisms.

(** Diagonal functor [C ---> [J, C]] *)

Program Instance DiagFunc : Functor_struct (C:=C) (D:= FunctCat J C)
    (Fobj := ConstFunc)
                                (ConstFuncNT).
Next Obligation.
Proof.
  unfold Proper; red.
  unfold ConstFuncNT.
  simpl.
  auto.
Qed.
Next Obligation.
Proof.
  cat.
Qed.
Next Obligation.
Proof.
  unfold vcompNT1.
  cat.
Qed.

Definition DiagFunctor := Build_Functor DiagFunc.

(** category of cones *)

Section Cone.

Variable F : Functor J C.

Class ConeClass (a : obC) := {
  cone_mor : forall j, morC a (F j) ; 
  cone_prop : forall j j' (f : morJ j j'), 
             cone_mor j ;; #F f == cone_mor j'
}.

Record Cone := {
  ConeTop :> obC ;
  cone_struct :> ConeClass ConeTop
}.

Existing Instance cone_struct.

Section Cone_Homs.

Variables M N : Cone.

Class Cone_Hom_struct (f : morC M N) := {
  cone_comm : forall j:obJ, f ;; cone_mor j == cone_mor j 
}.

Record Cone_Hom := {
  cone_hom_carrier :> morC M N;
  cone_hom_struct :> Cone_Hom_struct cone_hom_carrier
}.

Lemma Cone_Hom_equiv : @Equivalence Cone_Hom 
         (fun A B => cone_hom_carrier A == cone_hom_carrier B).
Proof.
  split.
  unfold Reflexive;
  cat.
  unfold Symmetric;
  intros x y; 
  apply hom_sym.
  unfold Transitive;
  intros x y z;
  apply hom_trans.
Qed.

Definition Cone_Hom_oid := Build_Setoid Cone_Hom_equiv.

End Cone_Homs.

Existing Instance cone_hom_struct.

Section Cone_id_comp.

Variable A : Cone.

Program Definition Cone_id : Cone_Hom A A := 
   Build_Cone_Hom (cone_hom_carrier := id _ ) _ .
Next Obligation.
Proof.
  constructor.
  cat.
Qed.

Variables B D : Cone.
Variable f : Cone_Hom A B.
Variable g : Cone_Hom B D.

Program Definition Cone_comp : Cone_Hom A D := 
    Build_Cone_Hom (cone_hom_carrier := cone_hom_carrier f ;; 
                                        cone_hom_carrier g) _ .
Next Obligation.
Proof.
  constructor.
  intro j.
  rewrite assoc.
  rewrite (cone_comm j).
  rewrite (cone_comm j).
  cat.
Qed.

End Cone_id_comp.

Obligation Tactic := cat ; try apply assoc.

Program Instance CONE_struct : Cat_struct Cone_Hom := {
  mor_oid := Cone_Hom_oid;
  id := Cone_id;
  comp := Cone_comp
}.
Next Obligation.
Proof.
  unfold Proper; 
  do 2 red.
  simpl.
  intros x y H x' y' H'.
  rewrite H, H'.
  cat.
Qed.

Definition CONE := Build_Cat CONE_struct.

End Cone.

(** a limit is a terminal object in (CONE A) *)



Definition LIMIT A := Terminal (CONE A).

(** easy access to interesting parts of a limit *)

Section Limit_defs.

Variable A : Functor J C.

Hypothesis H : LIMIT A.

Definition Limit : Cone A := Term (Terminal := H).

Definition LimitVertex : obC := ConeTop Limit.

Definition LimitMor (j : obJ) := cone_mor (ConeClass := Limit) j.

End Limit_defs.

End defs.

Existing Instance cone_struct.
Existing Instance cone_hom_struct.
Existing Instance CONE_struct. 










