
Require Export CatSem.CAT.NT.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Section CatFunct.

(** we build a category of functors and natural transformations *)

Variables obC obD: Type.
Variable morC : obC -> obC -> Type.
Variable morD : obD -> obD -> Type.
Variable C: Cat_struct morC.
Variable D: Cat_struct morD.

Obligation Tactic := cat; unfold vcompNT1;
   try (match goal with | [ |- Proper _ _ ] => 
             unfold Proper; do 2 red end) ;
   cat; unfold vcompNT1 ; try rewrite assoc;
   repeat (match goal with [ H : forall a, _ == _ |- _ ] => 
                   rewrite H end);
   cat.

Program Instance FunctCat_struct : 
           @Cat_struct (Functor C D) (NT (C:=C)(D:=D)) := {
   mor_oid F G :=  EXT_NT_oid F G;
   id F := vidNT F;
   comp a b c f g := g # f
}.

Definition FunctCat : Cat := Build_Cat FunctCat_struct.

End CatFunct.

Existing Instance FunctCat_struct.

Canonical Structure FunctCat.

Notation "[ C , D ]" := (FunctCat C D) (at level 75).


(*Definition END (C:Category) := [ C , C ].*)


Section FunctCat_lemmata.

(** we prove an extensionality principle on natural transformations *)

Variables obC obD: Type.
Variable morC : obC -> obC -> Type.
Variable morD : obD -> obD -> Type.
Variable C: Cat_struct morC.
Variable D: Cat_struct morD.

Variables F G H K: Functor C D.
Variable alpha: F ---> G.
Variable beta: H ---> K.

Hypothesis h: F = H.
Hypothesis h': G = K.

Lemma NT_Extensionality: 
  (forall x: obC, alpha x === beta x) -> alpha === beta.
Proof.
  generalize dependent alpha; clear alpha.
  rewrite h.
  generalize dependent beta; clear beta.
  rewrite h'.
  clear h h' F G.
  intros beta alpha H'.
  apply Build_Equal_hom.
  simpl.
  intro c.
  apply Equal_hom_imp_setoideq2_jmq_eq.
  apply (H' c).
Qed.

End FunctCat_lemmata.










