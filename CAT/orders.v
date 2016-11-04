
Require Export Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relations.
Require Export CatSem.CAT.cat_TYPE.
Require Export CatSem.CAT.functor.
Require Export CatSem.CAT.product.
Require Export CatSem.CAT.initial_terminal.
Require Export CatSem.CAT.cat_TYPE.



Set Implicit Arguments.
Unset Strict Implicit.

Unset Automatic Introduction.


Section clos_rt_1n.

Variable A:Type.
Variable R: relation A.
Instance Clos_RT_1n_prf : PreOrder (clos_refl_trans_1n A R).
Proof. 
  assert (H := clos_rt_is_preorder A R). 
  destruct H as [Hrefl Htrans].
  constructor.
  unfold Reflexive. intros; constructor.
  unfold Transitive.
  intros x y z H H'.
  apply trans_rt1n.
  apply Htrans with y;
  apply rt1n_trans; auto.
Qed.

Lemma clos_refl_trans_1n_contains x y : R x y -> 
           clos_refl_trans_1n _ R x y.
Proof.
  intros.
  constructor 2 with y;
  auto.
  apply Clos_RT_1n_prf.
Qed.
  
End clos_rt_1n.

Existing Instance Clos_RT_1n_prf.


(** composition of order_preserving functions is order_preserving *)
Lemma comp_order_preserve: forall A B C (RA : relation A)
                                        (RB : relation B)
                                        (RC : relation C)
          (f: A -> B) (g: B -> C)
     (Hf:Proper (RA ==> RB) f)(Hg:Proper (RB ==> RC) g),
                Proper (RA ==> RC) (fun x => g (f x)).
Proof.  
  unfold Proper; 
  red; simpl; auto. 
Qed.

Lemma id_order_preserve: forall A (R: relation A),
            Proper (R ==> R) (fun x => x).
Proof. 
  unfold Proper; 
  red; simpl; auto. 
Qed.


(** cat of preorders *)

Class PO_obj_struct (T:Type) := {
   Rel : relation T;
   POprf :> PreOrder Rel
}.

Record PO_obj : Type := {
    POCarrier:> Type;
    po_obj_struct :> PO_obj_struct POCarrier 
}.

Notation "a << b" := (Rel a b) (at level 60).

Existing Instance po_obj_struct.

Class PO_mor_struct (a b : PO_obj) (f:a -> b) := {
  PO_prop :> Proper (@Rel a _ ++> @Rel b _) f
}.

Record PO_mor (a b: PO_obj): Type := {
    PO_fun:> a -> b;
    po_mor_struct:> PO_mor_struct PO_fun
}.

Existing Instance po_mor_struct.

Lemma PO_mor_monotone (a b : PO_obj)(f : PO_mor a b):
   forall x y, x << y -> f x << f y.
Proof.
  intros a b f
     x y H.
  apply f.
  apply H.
Qed.

Section PreOrder_comp.
Variable A B C: PO_obj.
Variable f: PO_mor A B.
Variable g: PO_mor B C.

Program Definition PreOrder_comp : PO_mor A C := Build_PO_mor
      (PO_fun := fun x => g (f x)) _. 
Next Obligation.
Proof. 
  constructor;
  apply (comp_order_preserve (RB:= Rel));
  try apply f; apply g. 
Qed.

End PreOrder_comp.

Program Definition PreOrder_id(A:PO_obj) : PO_mor A A :=
               Build_PO_mor (PO_fun := fun x => x) _.
Next Obligation.
Proof. 
  constructor;
  apply id_order_preserve. 
Qed.
(*
Definition eq_PreOrder (A B: PO_obj) : relation (PO_mor A B) :=
       fun f g => forall x, f x = g x.
*)
Lemma eq_PreOrder_equiv (A B: PO_obj): @Equivalence (PO_mor A B) 
    (fun f g => forall x, f x = g x).
Proof. 
  intros A B.
  constructor; 
  unfold Reflexive, 
    Symmetric, Transitive;
  intros; try etransitivity; 
  auto. 
Qed.

Definition PreOrder_oid := fun A B => Build_Setoid (eq_PreOrder_equiv A B).

Obligation Tactic := simpl; intros; auto.

Program Instance POTYPE : Cat_struct PO_mor := {
   mor_oid := PreOrder_oid;
   comp := PreOrder_comp;
   id := PreOrder_id
}.
Next Obligation.
Proof.  
  unfold Proper. 
  repeat red. 
  simpl; intros x y H; 
  intros; rewrite H. 
  auto. 
Qed.

Canonical Structure Ord := Build_Cat POTYPE.

(** lemmata about V:PO *)
Section PO_lemmata.
Variable V: Ord.
Variable x : V.
Lemma PO_refl :  x << x.
Proof. apply POprf. Qed.

Variables y z : V.

Lemma PO_trans:  x << y -> y << z -> x << z.
Proof. apply POprf. Qed.

Lemma PO_refl_eq : x = y -> x << y.
Proof. 
 intros; subst; reflexivity.
Qed.

Lemma PO_trans_eq_r : x << y -> y = z -> x << z.
Proof.
  intros; subst; auto.
Qed.

Lemma PO_trans_eq_l : x = y -> y << z -> x << z.
Proof.
  intros; subst; auto.
Qed.

End PO_lemmata.


(** we need a product on the categories of preorders *)
Section PO_product.

Section PO_prod_data.

Variables V W: Ord.

Inductive prod_rel : relation (prod V W) :=
| rel_rel_rel: forall v v' w w',
      v << v' ->  w << w' -> prod_rel (v,w) (v',w').

Lemma prod_rel_oid : PreOrder prod_rel .
Proof.
  constructor.
  unfold Reflexive.
  intro x;
  destruct x; constructor;
  apply POprf.
  
  unfold Transitive.
  intros x y z H H';
  destruct x as [x1 x2]; 
  destruct y as [y1 y2];
  destruct z as [z1 z2].
  inversion H;
  inversion H'.
  constructor.
  apply PO_trans with y1; auto.
  apply PO_trans with y2; auto.
Qed.

Instance prod_rel_ : PO_obj_struct (prod V W) := {
  Rel := prod_rel;
  POprf := prod_rel_oid
}. 

Definition PO_product : Ord := Build_PO_obj prod_rel_.

Program Definition PO_prl : PO_product ---> V := 
    Build_PO_mor (PO_fun := fun x => fst x) _.
Next Obligation.
Proof. 
  constructor.
  unfold Proper; red.
  intros x y H;
  inversion H.
  auto.
Qed.

Program Definition PO_prr : PO_product ---> W := 
    Build_PO_mor (PO_fun := fun x => snd x) _.
Next Obligation.
Proof.
  constructor.
  unfold Proper; red.
  intros x y H;
  inversion H.
  auto.
Qed.

Variable X: Ord.
Variable f: X ---> V.
Variable g: X ---> W.


Program Definition PO_prod_mor : X ---> PO_product := 
   Build_PO_mor (PO_fun := fun x => (f x, g x)) _.
Next Obligation.
Proof.
  constructor.
  unfold Proper; red.
  intros x y H.
  constructor;
  try apply f;
  try apply g; auto.
Qed.


End PO_prod_data.


Program Instance PO_prod : Cat_Prod Ord := {
  product a b := PO_product a b;
  prl a b := PO_prl a b;
  prr a b := PO_prr a b;
  prod_mor a b c f g := PO_prod_mor f g
}.
Next Obligation.
Proof.
  unfold Proper; do 2 red.
  intros f g H f' g' H'; simpl.
  intro x; simpl.
  rewrite H.
  rewrite H'.
  auto.
Qed.
Next Obligation.
Proof.
  destruct H.
  apply injective_projections;
  simpl; auto.
Qed.

End PO_product.

Existing Instance PO_prod.

(** PO also has initial and terminal object, Empty and PO_unit *)

Section PO_unit_init.

Definition PO_term_rel : relation unit :=
      fun x y => True.
Lemma PO_term_preorder : PreOrder PO_term_rel.
Proof. 
  unfold PO_term_rel; 
  constructor;
  auto.
Qed.

Instance PO_term_rel_ : PO_obj_struct unit := {
  Rel := PO_term_rel;
  POprf := PO_term_preorder
}.

Definition PO_TERM := Build_PO_obj PO_term_rel_.

Program Definition PO_TERM_mor (A : Ord) : A ---> PO_TERM :=
     Build_PO_mor (PO_fun := fun x => tt) _ .
Next Obligation.
Proof.
  constructor.
  unfold Proper; red.
  intros.
  simpl.
  unfold PO_term_rel. 
  auto. 
Qed.

Program Instance PO_Terminal : Terminal Ord := {
  Term := PO_TERM;
  TermMor a := PO_TERM_mor a
}.

Lemma PO_init_rel : @PreOrder TEMPTY (fun x y => True).
Proof.
  constructor;
  auto.
Qed.

Instance PO_init_ : PO_obj_struct TEMPTY := { 
  Rel := _ ;
  POprf := PO_init_rel
}.

Definition PO_INIT := Build_PO_obj PO_init_.

Definition PO_Initial_morD (A : Ord) : PO_INIT -> A.
intros A t.
elim t.
Defined.

Obligation Tactic := simpl; intros;
      try unf_Proper; intros;
  repeat match goal with [x:TEMPTY |- _ ] => elim x end;
  auto.

Program Instance PO_Initial_mors (A : Ord) : 
  PO_mor_struct (a:=PO_INIT) (b:=A)
   (PO_Initial_morD A).

Definition PO_Initial_mor (A: Ord) : PO_INIT ---> A := 
  Build_PO_mor (PO_Initial_mors A).

Program Instance PO_Initial : Initial Ord := {
  Init := PO_INIT;
  InitMor a := PO_Initial_mor a
}.

End PO_unit_init.

Section forget.

Obligation Tactic := simpl; intros;
      try unf_Proper; intros;
  repeat match goal with [x:TEMPTY |- _ ] => elim x end;
  auto.

Program Instance OPO_struct : Functor_struct (C:=Ord) (D:=TYPE)
      (fun a b f => f).

Canonical Structure OPO := Build_Functor OPO_struct.

End forget.

Existing Instance Clos_RT_1n_prf.
Existing Instance PO_Initial.
Existing Instance PO_Terminal.
Existing Instance POTYPE.
Existing Instance PO_prod.








 

