Require Export CatSem.CAT.prods.
Require Export CatSem.CAT.CatFunct.
Require Export CatSem.CAT.horcomp. 
Require Export CatSem.CAT.functor_leibniz_eq.
(*Require Export CatSem.CAT.setoid_lemmata.*)

Set Transparent Obligations.
Set Implicit Arguments.
Unset Strict Implicit.

Unset Automatic Introduction.

(** for a cat C and e:C, we want the functor c -> (c, e) *)

Section erightleft.

Variable obC: Type.
Variable morC : obC -> obC -> Type.
Variable C: Cat_struct morC.

Variable e:obC.

(** this functor C -> C x C  is constant on the right *)

Program Definition eright : Functor C (PROD C C) := Build_Functor
  (Fobj := fun c: obC => (c, e))
  (Fmor := fun a b f => (f, id e)) _ .
Next Obligation.
Proof. 
  apply Build_Functor_struct; 
  try red;
  try red; cat.
Qed.




(** and this one constant on the left *)

Program Definition eleft : Functor C (PROD C C) := Build_Functor
  (Fobj := fun c: obC => (e, c))
  (Fmor := fun a b f => (id e, f)) _.
Next Obligation.
Proof. 
  apply Build_Functor_struct; 
  try red;
  try red; cat.
Qed.


End erightleft.

(** there is a functor (A x B) x C ---> A x (B x C) *)

Section PROD_almost_assoc.

Variables obA obB obC:Type.
Variable morA: obA -> obA -> Type.
Variable morB: obB -> obB -> Type.
Variable morC: obC -> obC -> Type.
Variables (A: Cat_struct morA) (B: Cat_struct morB) (C:Cat_struct morC).

Program Definition iso: Functor (PROD (PROD A B) C) (PROD A (PROD B C)) := 
         Build_Functor
  (Fobj := fun a => (fst (fst a), (snd (fst a), snd a)))
  (Fmor := fun a b f => (fst (fst f), (snd (fst f), snd f))) _ .
Next Obligation.
Proof. 
  apply Build_Functor_struct;
  intros;
  try red;
  try red; 
  cat. 
  elim_conjs; cat.
Qed.

End PROD_almost_assoc.

(** strict monoidal cat *)
Section smon_cat.
 
Variable obC: Type.
Variable morC : obC -> obC -> Type.

Section smon_cat_.
Variable C: Cat_struct morC.

(** a category C is strict monoidal if there is a tensor
    which is associative and has a unit *)

Class smon_cat := {
  tensor : Functor (PROD C C) C;
  e: obC;
  tensor_assoc : CompF (Prod_functor tensor (Id C)) tensor ==
                  CompF (iso C C C) (CompF (Prod_functor (Id C) tensor) 
                                         tensor);
  eleft_unit:  CompF (eleft C e) tensor == Id C;
  eright_unit: CompF (eright C e) tensor == Id C
}.

End smon_cat_.

Record SMON := {
   cat:> Cat_struct morC;
   smon_struct:> smon_cat cat
}.

End smon_cat.


(** The category of endofunctors End(C) over a category C
    is a strict monoidal category with composition as tensor *)

Section monads.
Variable obC: Type.
Variable morC : obC -> obC -> Type.
Variable C: Cat_struct morC.

(** composition is a functor PROD (FunctCat C C) (FunctCat C C) *)


Program Definition comp_tensor : 
  Functor (PROD ([C, C]) ([C, C])) ([C, C]) := Build_Functor
    (Fobj := fun a => CompF (fst a) (snd a))
    (Fmor := fun a b f => hcompNT (fst f) (snd f)) _ .
Next Obligation.
Proof. 
  apply Build_Functor_struct. 
  
  intros a b; simpl.
  red. red.
  intros x y H. 
  unfold hcompNT.  
  simpl. 
  intro c.
  unfold hcompNT1.
(*  destruct x as [x1 x2].
  destruct y as [y1 y2].*)
  destruct H as [H1 H2].
  rewrite H1 .
  rewrite H2.
  cat.
  
  intro a; 
  simpl. 
  unfold hcompNT1.
  intro c; simpl. 
  cat.
  
  intros a b c f g; 
  simpl.
  destruct f as [alpha beta].
  destruct g as [gamma delta]. 
  simpl.
(*  unfold eq_NT1.*)
  intro c0.
  unfold vcompNT.
  unfold hcompNT.
  unfold hcompNT1.
  unfold vcompNT1.
  simpl.
  destruct a as [F1 F2].
  destruct b as [G1 G2].
  destruct c as [H1 H2].
  simpl in *|-*.
  rewrite <- assoc.
  rewrite <- assoc.
  rewrite <- (NTcomm beta).
  rewrite <- (NTcomm beta).
  rewrite (FComp G2).
  repeat rewrite assoc.
  apply hom_refl.
Qed.

End monads.

Section endo_monad.

Notation "a 'OO' b" := (hcompNT  a b)(at level 60).

Variable obC: Type.
Variable morC : obC -> obC -> Type.
Variable C: Cat_struct morC.

Local Obligation Tactic := idtac.

Program Instance monads : smon_cat (FunctCat C C) := {
  tensor := comp_tensor C;
  e := Id C
}.
Obligation 2.
Proof.
  simpl.
  intros a b f.
  assert (H:= NT_Extensionality 
        (alpha := vidNT (Id C) OO f) (beta := f)
            (IdFl _ ) (IdFl _ ) ).
  apply H.
  intro x. 
  simpl. 
  unfold hcompNT1. 
  simpl.
  apply Build_Equal_hom.
  cat.
Qed.
Next Obligation.
Proof.
  simpl.
  intros a b f.
  destruct a as [[F1 F2] F3].
  destruct b as [[G1 G2] G3]. 
  destruct f as [[alpha beta] gamma]. 
  simpl in *|-*. 
  assert (H:= NT_Extensionality 
         (alpha := (alpha OO beta) OO gamma)
         (beta := (alpha OO (beta OO gamma))) ).
  apply H.

  apply CompFassoc.
  
  apply CompFassoc.

  intro x.
  simpl. 
  unfold hcompNT.
  unfold hcompNT1.
  simpl. 
  apply Build_Equal_hom.
  rewrite (FComp F3).
  rewrite <- assoc.
  apply hom_refl.
Qed.
Next Obligation.
Proof.
  simpl.
  intros F G alpha.
  set (H:= NT_Extensionality 
        (alpha := alpha OO vidNT (Id C)) (beta := alpha)
            (IdFr _ ) (IdFr _ ) ).
  apply H.
  intro x. 
  simpl. 
  unfold hcompNT1. 
  simpl.
  apply Build_Equal_hom.
  cat.
Qed.

End endo_monad.




   





















