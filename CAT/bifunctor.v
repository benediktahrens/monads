Require Export CatSem.CAT.functor. 
Require Export CatSem.CAT.prods.
Require Import CatSem.CAT.coproduct.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Section bifunctor_def.

Variable obB obC obD : Type.
Variable morB: obB -> obB -> Type.
Variable morC: obC -> obC -> Type.
Variable morD: obD -> obD -> Type.

Variables (B: Cat_struct morB) (C: Cat_struct morC) (D: Cat_struct morD).

(** a bifunctor is a functor from a product category to somewhere *)

Definition Bifunctor := Functor (PROD B C) D.

Variable S: Bifunctor.

(** for any element [c] the "functor"
    - b => S (b, c)
    is a functor
*)

Section Left_Functor.

Variable c:obC.

Obligation Tactic := simpl; intros.

Program Instance Left_Functor_struct : Functor_struct (C:=B) (D:=D) 
             (Fobj := fun b => S (b, c)) 
             (fun (b b':obB) (f:morB b b') => 
                  #S (build_prod_mor B C f (id c))).
Next Obligation.
Proof. 
  unfold Proper; 
  red.
  intros x y H.
  apply prod_mor_equal; 
  cat.
Qed.
Next Obligation.
Proof.
  cat.
Qed.
Next Obligation.
Proof. 
  unfold build_prod_mor. 
  rewrite <- FComp. 
  simpl.
  unfold Prod_comp. 
  simpl.
  apply prod_mor_equal; 
  cat.
Qed.


Definition Left_Functor : Functor B D := Build_Functor Left_Functor_struct.

End Left_Functor.

Section Right_Functor.

Variable b: obB.

Obligation Tactic := simpl; intros.

Program Instance Right_Functor_struct : Functor_struct (C:=C) (D:=D) 
             (Fobj := fun c => S (b, c)) 
             (fun (c c':obC) (f:morC c c') => 
                  #S (build_prod_mor B C (id b) f )).  
Next Obligation.
Proof. 
  unfold Proper; 
  red.
  intros x y H.
  apply prod_mor_equal; 
  cat.
Qed.
Next Obligation.
Proof. 
  cat. 
Qed.
Next Obligation.
Proof. 
  unfold build_prod_mor. 
  rewrite <- FComp. 
  simpl.
  unfold Prod_comp. 
  simpl.
  apply prod_mor_equal; 
  cat.
Qed.

Definition Right_Functor : Functor C D := 
                Build_Functor Right_Functor_struct.

End Right_Functor.

End bifunctor_def.

(** product is a bifunctor *)

Section prod_bifunctor.


Variable obC: Type.
Variable morC: obC -> obC -> Type.
Variable C: Cat_struct morC.
Variable H: Cat_Prod C.

Definition PROD_BIF_obj : (PROD C C) -> obC := 
        fun x => product (fst x) (snd x).

Definition PROD_BIF_mor (a b:PROD C C) (f: a ---> b) : 
   morC (PROD_BIF_obj a) (PROD_BIF_obj b) :=
 prod_mor (prl (fst a) (snd a) ;; 
      (fst f)) (prr (fst a) (snd a) ;; (snd f)).


Program Definition PROD_BIF : Bifunctor C C C := Build_Functor
   (Fobj := fun x => product (fst x) (snd x))
   (Fmor:= fun a b f => prod_mor (prl (fst a) (snd a) ;; 
             (fst f)) (prr (fst a) (snd a) ;; (snd f)))  _ .
Next Obligation.
Proof. 
  constructor.

  unfold Proper;
  red.
  intros a b x y H'.
  apply prod_mor_unique.
  repeat rewrite prod_prl.
  repeat rewrite prod_prr.
  destruct x; destruct y.
  destruct H' as [h h'].
  cat.
  
  intro a. 
  apply hom_sym.
  apply prod_mor_unique.
  cat.

  intros a b c f g.
  apply hom_sym.
  apply prod_mor_unique.
  destruct a; destruct b; destruct c;
  destruct f; destruct g; simpl in *.
  repeat rewrite assoc.
  repeat rewrite prod_prl.
  repeat rewrite prod_prr.
  repeat rewrite <- assoc.
  cat.
Qed.
           
End prod_bifunctor.


Section coprod_bifunctor.

Variable obC: Type.
Variable morC: obC -> obC -> Type.
Variable C: Cat_struct morC.
Variable H: Cat_Coprod C.

Definition COPROD_BIF_obj : (PROD C C) -> obC := 
        fun x => coprod (fst x) (snd x).

Definition COPROD_BIF_mor (a b:PROD C C) (f: a ---> b) : 
  morC (COPROD_BIF_obj a) (COPROD_BIF_obj b) :=
  coprod_mor ((fst f) ;; inl (fst b) (snd b)) 
                 ((snd f) ;; inr (fst b) (snd b)).

Program Definition COPROD_BIF : Bifunctor C C C := Build_Functor
   (Fobj := COPROD_BIF_obj) (Fmor:= COPROD_BIF_mor)  _ .
Next Obligation.
Proof. 
  constructor.
  
  unfold Proper,COPROD_BIF_mor; red.
  intros a b x y H'.
  apply coprod_mor_unique.
  repeat rewrite inl_coprod.
  repeat rewrite inr_coprod.
  destruct x; destruct y.
  destruct H' as [h h'].
  simpl in *.
  rewrite h. rewrite h'.
  split; apply hom_refl.
  
  unfold COPROD_BIF_mor. simpl.
  intro a. apply hom_sym.
  apply coprod_mor_unique.
  repeat rewrite idl. repeat rewrite idr.
  split; apply hom_refl.
  
  unfold COPROD_BIF_mor, COPROD_BIF_obj.
  intros a b c f g.
  apply hom_sym.
  apply coprod_mor_unique.
  destruct a; destruct b; destruct c;
  destruct f; destruct g; simpl in *.
  repeat rewrite <- assoc.
  rewrite (inl_coprod).
  rewrite inr_coprod.
  repeat rewrite assoc.
  rewrite inl_coprod.
  rewrite inr_coprod.
  split; apply hom_refl.
Qed.
           
End coprod_bifunctor.  


(* is not possible, typing issues *)
(*
Section Bifunctor_from_Functors.

Variable obB obC obD : Type.
Variable morB: obB -> obB -> Type.
Variable morC: obC -> obC -> Type.
Variable morD: obD -> obD -> Type.

Variables (B: Cat morB) (C: Cat morC) (D: Cat morD).

Variable L: forall c:obC, Functor B D.
Variable M: forall b:obB, Functor C D.

Hypothesis H: forall b c, L c b = M b c.

Hypothesis H': forall b b' c c' (f: morB b b') (g: morC c c'),
                  L c <- f o M b' <- g == M b <- g o L c' <- f.

*)










