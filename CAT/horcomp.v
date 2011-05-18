Require Export CatSem.CAT.CatFunct.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.	

(** horizontal composition of natural transformations *)

Section hcomp.

Variables obA obB obC: Type.
Variable morA : obA -> obA -> Type.
Variable morB : obB -> obB -> Type.
Variable morC : obC -> obC -> Type.

Variable A: Cat_struct morA.
Variable B: Cat_struct morB.
Variable C: Cat_struct morC.

Variables (F F': Functor A B) (G G': Functor B C).
Variables (alpha: F ---> F') (beta: G ---> G').


(** no choice in the definition of horizontal composition *)
Lemma no_choice (a: obA): 
       beta (F a) ;; #G' (alpha a) == 
          #G  (alpha a) ;; beta (F' a).
Proof. 
  intro a. 
  rewrite (NTcomm beta).
  cat.
Qed.

(**  definition of the composite and proof of NT axiom *)

Definition hcompNT1 (a:obA) := #G (alpha a) ;; (beta (F' a)).

Lemma hcompNT_ax: trafo_comm (F:= CompF F G) 
                             (G:= CompF F' G') hcompNT1.
Proof.  
  unfold trafo_comm. 
  intros a b f. simpl. 
  unfold hcompNT1. 
  simpl.
  repeat rewrite <- assoc.
  setoid_rewrite <- (FComp G (#F f)).
  rewrite <- (NTcomm beta).
  rewrite <- (NTcomm beta ((#F f) ;; alpha b)).
  rewrite <- (NTcomm alpha).
  rewrite  FComp.
  repeat rewrite assoc.
  apply hom_refl.
Qed.


Definition hcompNT : NT (CompF F G) (CompF F' G') := Build_NT
   (Build_NT_struct hcompNT_ax).

End hcomp.


(** horizontal composition has an identity NT *)
Section hidNT.

Variable obC: Type.
Variable morC : obC -> obC -> Type.
Variable C : Cat_struct morC.

Definition hidNT1 := fun c:obC => id (Id C c).

Lemma hidNT_ax : trafo_comm hidNT1.
Proof. 
  unfold trafo_comm. 
  intros c d f.
  unfold hidNT1. 
  simpl.
  cat.
Qed.

Definition hidNT: NT (Id C) (Id C) := Build_NT
     (trafo := hidNT1)
     (Build_NT_struct hidNT_ax).

End hidNT.



(** equality of NT, heterogeneous version eq_NTh, 
         using Equal_hom instead of == *)
Section EXT_NT_HET.

Variables obC obD: Type.
Variable morC : obC -> obC -> Type.
Variable morD : obD -> obD -> Type.
Variable C: Cat_struct morC.
Variable D: Cat_struct morD.

Variables F G F' G' : Functor C D.
Variable alpha : NT F G.
Variable beta : NT F' G'.

Definition EXT_NT_HET := forall c:obC, alpha c ===  beta c.
End EXT_NT_HET.


(** the heterogeneous equality is also a setoid *)

Section EXT_NT_HET_lemmata.
(* Variables C D: Category. *)

Notation "a =h= b" := (EXT_NT_HET a b) (at level 60).

Variables obC obD: Type.
Variable morC : obC -> obC -> Type.
Variable morD : obD -> obD -> Type.
Variable C: Cat_struct morC.
Variable D: Cat_struct morD.

Variables F G: Functor C D.
Variable alpha: NT F G.

Lemma eq_NTh_refl:  alpha =h= alpha.
Proof.
  intro c.
  apply Build_Equal_hom.
  apply hom_refl.
Qed.

Variable F' G': Functor C D.
Variable beta: F' ---> G'.

Lemma eq_NTh_sym: alpha =h= beta -> beta =h= alpha.
Proof. 
  intros H c.
  apply Equal_hom_sym. 
  auto.
Qed.

Variable F'' G'' : Functor C D.
Variable gamma: F'' ---> G''.

Lemma eq_NTh_trans: alpha =h= beta -> beta =h= gamma ->
                            alpha =h= gamma.
Proof. 
  intros H H' c.
  apply (Equal_hom_trans (H c) (H' c)).
Qed.

End EXT_NT_HET_lemmata.

(**  Properties of horizontal composition with 
       respect to heterogeneous equality *)

Section hor_comp_properties.

Notation "a 'OO' b" := (hcompNT  a b)(at level 60).


(** hor comp of NT is post-neutral *)

Section hor_comp.


Variables obC obD: Type.
Variable morC : obC -> obC -> Type.
Variable morD : obD -> obD -> Type.
Variable C: Cat_struct morC.
Variable D: Cat_struct morD.

Variables F G: Functor C D.
Variable alpha : F ---> G.

(** we have 
      - [alpha : F ---> G]
      - [alpha o (idNT D) : F ---> G o Id]

     in order to compare those we need heterogeneous equality on 
     natural transformations

*)

Lemma hid_L: EXT_NT_HET (alpha OO (hidNT D)) alpha.
Proof. 
  unfold EXT_NT_HET,hidNT,
         hcompNT,
         hcompNT1.
  simpl; unfold hidNT1.
  simpl. 
  intro c. 
  apply Build_Equal_hom. 
  cat. 
Qed.

End hor_comp.





(** we want to have a type where we can build a relation EXT_NT_HET *)
(** an element of NTlarge is a triple (F,G,alpha)  *)

Section NTlarge.

Variables obC obD: Type.
Variable morC : obC -> obC -> Type.
Variable morD : obD -> obD -> Type.
Variable C: Cat_struct morC.
Variable D: Cat_struct morD.

Record NTlarge := {
  SrcF : Functor C D;
  TgtF : Functor C D;
  NT_l : SrcF ---> TgtF
}.


Definition NT_from_NTl (alpha: NTlarge) : forall c:obC, 
                    morD (SrcF alpha c) (TgtF alpha c) := 
                 fun c => NT_l alpha c.
  

(**   equality in the type of elements (F,G,alpha) 
      - [alpha : F ---> G] 
      - [beta: F' ---> G' ]
    are  equal if they are extensionally equal 
      - this is a setoid   *)

Definition EXT_NTh : relation NTlarge :=
   fun alpha beta: NTlarge => 
     forall c:obC, NT_l alpha c === NT_l beta c.

End NTlarge.

Section EXT_NTh_lemmata.


(* Variables C D: Category. *)

Variables obC obD: Type.
Variable morC : obC -> obC -> Type.
Variable morD : obD -> obD -> Type.
Variable C: Cat_struct morC.
Variable D: Cat_struct morD.

Notation "=NT=" := (@EXT_NTh _ _ _ _ C D ).

Lemma Equal_NT_refl: @Reflexive _ =NT=. 
Proof. 
  unfold Reflexive.
  intros x c. 
  apply Equal_hom_refl.
Qed.

Lemma Equal_NT_sym: @Symmetric _ =NT=.
Proof. 
  unfold Symmetric. 
  intros x y H c.
  apply Equal_hom_sym.
  apply (H c). 
Qed.

Lemma Equal_NT_trans: @Transitive _ =NT=.
Proof. 
  unfold Transitive.
  intros x y z H H' c.
  apply (Equal_hom_trans (H c) (H' c)).
Qed.

Lemma Equal_NT_equiv: Equivalence =NT=.
Proof. 
  split.
  apply Equal_NT_refl.
  apply Equal_NT_sym.
  apply Equal_NT_trans.
Qed.

Definition Equal_NT := Build_Setoid Equal_NT_equiv.


(** the horizontal identity NT hidNT is indeed neutral *)

(* Variables C D : Category. *)

Variables F G: Functor C D.
Variable alpha: F ---> G.


(** proof only for post-composition *)

Lemma hid_l:  EXT_NTh (Build_NTlarge  (alpha OO hidNT D)) 
                     (Build_NTlarge alpha  ).
Proof.
  assert (H:=hid_L).
  unfold EXT_NT_HET in H.
  intro c.
  simpl in *.
  unfold hcompNT1 in *. 
  simpl in *.
  auto.
Qed.

End EXT_NTh_lemmata.

End hor_comp_properties.



























