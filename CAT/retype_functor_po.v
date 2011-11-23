
(*Require Import Coq.Logic.FunctionalExtensionality.*)
Require Import Coq.Logic.Eqdep.

Require Import CatSem.AXIOMS.functional_extensionality.

Require Export CatSem.CAT.retype_functor. 
Require Export CatSem.CAT.ind_potype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

(** define an order on the retyped V, dependent on order on V *)

Section retype_ord.

Variables T U : Type.
Variable f : T -> U.

Inductive retype_ord (V : IPO T) : forall u, relation (retype f V (u)) :=
  | ctype_ord : forall t (x y : V t), x <<< y 
            -> retype_ord  (ctype f x) (ctype f y).

Program Instance retype_ipo_s (V : IPO T) : 
      ipo_obj_struct (retype f V) := {
  IRel := @retype_ord V
}.
Next Obligation.
Proof.
  constructor.
  unfold Reflexive.
  intro x;
  destruct x as [t x].
  constructor.
  apply IRel_refl.

  unfold Transitive.
  intros x y z H1 H2.
  generalize dependent z.
  induction H1.
  intros z H'.
  
  inversion H'.
  subst.
  assert (H44:=inj_pair2 _ _ _ _ _ H4).
  assert (H55:=inj_pair2 _ _ _ _ _ H5).
  subst.
  constructor.
  transitivity y; auto.
Qed.

Definition retype_ipo V : IPO U := Build_ipo_obj (retype_ipo_s V).

Section retype_po_hom.

Variables V W : IPO T.
Variable m : V ---> W.

Program Instance ret_po_mor_s : ipo_mor_struct 
    (a:=retype_ipo V) (b:=retype_ipo W) (retype_map m).
Next Obligation.
Proof.
  unfold Proper;
  red.
  intros x y H.
  induction H.
  simpl.
  constructor.
  apply m.
  auto.
Qed.

Definition retype_po_mor := Build_ipo_mor ret_po_mor_s.

End retype_po_hom.

Obligation Tactic := idtac.

Program Instance retype_po_func : 
    Functor_struct (Fobj := retype_ipo) retype_po_mor.
Next Obligation.
Proof.
  intros a b.
  unfold Proper;
  red.
  intros g g' H t z.
  destruct z as [t z];
  simpl.
  rewrite H;
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros a t z.
  destruct z as [t z];
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros a b c g g' t z;
  destruct z as [t z];
  auto.
Qed.

Definition RETYPE_PO := Build_Functor retype_po_func.
  
End retype_ord.

(** now natural transformations with SM_ipo *)
Section nattrans.

Variables T U : Type.
Variable f : T -> U.

(*
Definition bla2 c:
(forall t : U,
  (sm_ipo (T:=U) (retype f c)) t -> (retype_ipo f (sm_ipo (T:=T) c)) t) .
intros c t x.
simpl in *.
apply x.
*)

Program Instance id_ccs c :
ipo_mor_struct 
 (a:=sm_ipo (T:=U) (retype f c)) 
 (b:=retype_ipo f (sm_ipo (T:=T) c)) (fun t x => x).
Next Obligation.
Proof.
  unfold Proper.
  red.
  intros x y H.
  induction H.
  apply retype_ipo_s.
Qed.

Definition id_cc c := Build_ipo_mor (id_ccs c).

Program Instance RT_NTs : NT_struct
    (F:=IDelta U O RETYPE f) 
    (G:=RETYPE_PO f O IDelta T) 
    (fun c => id_cc c).

Definition RT_NT := Build_NT RT_NTs.

Program Instance id_dds c :
ipo_mor_struct 
 (b:=sm_ipo (T:=U) (retype f c)) 
 (a:=retype_ipo f (sm_ipo (T:=T) c)) (fun t x => x).
Next Obligation.
Proof.
  unfold Proper;
  red.
  intros x y H.
  induction H.
  simpl.
  induction H.
  constructor.
Qed.

Definition id_dd c := Build_ipo_mor (id_dds c).

Program Instance NNNT2s : NT_struct
    (G:=IDelta U O RETYPE f) 
    (F:=RETYPE_PO f O IDelta T) 
    (fun c => id_dd c).

Definition NNNT2 := Build_NT NNNT2s.

End nattrans.

Section Transp_po.

Variables U U': Type.
Variables f g : U -> U'.
Hypothesis H : forall t, g t = f t.

Obligation Tactic := idtac.

Program Instance transp_po_s (V : IPO U) :
  ipo_mor_struct (a:=RETYPE_PO (fun t : U => f t) V)
                 (b:=RETYPE_PO (fun t : U => g t) V) 
          (transp H (V:=V)).
Next Obligation.
Proof.
  intros V t.
  assert (Ha : f = g) by
    (apply functional_extensionality; auto).
  unfold Proper;
  red.
  unfold transp.
  subst.
  intros x y H'.
  induction H';
  simpl.
  rewrite (UIP_refl _ _ (H t)).
  simpl.
  constructor;
  auto.
Qed.

Definition transp_po : forall V : IPO U,
     (RETYPE_PO (fun t : U => f t)) V ---> 
     (RETYPE_PO (fun t : U => g t)) V :=
     fun V => Build_ipo_mor (transp_po_s V).


Program Instance transp_po_NT : 
    NT_struct (F:=RETYPE_PO (fun t => f t)) 
           (G := RETYPE_PO (fun t => g t)) transp_po.
Next Obligation.
Proof.
  simpl.
  intros V W f' t y.
  induction y.
  simpl.
  rewrite <- H.
  simpl.
  auto.
Qed.

Definition Transp_ord : NT (RETYPE_PO (fun t => f t)) 
         (RETYPE_PO (fun t => g t)) := Build_NT transp_po_NT.

End Transp_po.


Section transp_po_id.

(** retyping with the identity function is the identity *)

Variables U U' : Type.
Variable f : U -> U'.
Variable H : forall t, f t = f t.

Lemma transp_po_id : forall V, transp_po H (V) == id _.
Proof.
  simpl.
  intros V t y.
  rewrite transp_id.
  auto.
Qed.

End transp_po_id.

Section id_retype_po.

Variable T : Type.
Variable V : IPO T.

Program Instance id_retype_po_s : ipo_mor_struct (a:=V)
  (b:=retype_ipo (fun t => t) V) (id_retype(V:=V)).
Next Obligation.
Proof.
  unfold Proper;
  red.
  intros x y H.
  unfold id_retype.
  assert (H':=ctype_ord (fun t => t) H).
  auto.
Qed.

End id_retype_po.
