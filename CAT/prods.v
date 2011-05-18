Require Export CatSem.CAT.functor.
Require Export CatSem.CAT.product.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Automatic Introduction.

(** prod of two cats *)
Section prod_cat.

Variables obC obD: Type.
Variable morC : obC -> obC -> Type.
Variable morD : obD -> obD -> Type.
Variable C: Cat_struct morC.
Variable D: Cat_struct morD.
(*
Variable C D: Category.
*)
(*
Definition Prod_obj := prod obC obD.
Definition Prod_mor := fun c d: (prod obC obD) => 
                   prod (morC (fst c) (fst d))
                                              (morD (snd c) (snd d)).
*)
Definition Prod_id := fun c:(prod obC obD) => (id(fst c), id (snd c)).
Definition Prod_comp := fun (a b c: prod obC obD) 
              (f: prod (morC (fst a) (fst b))
                       (morD (snd a) (snd b)))  
              (g: prod (morC (fst b) (fst c))
                       (morD (snd b) (snd c))) => 
                          (fst f ;; fst g, snd f ;; snd g).
(*
Definition Prod_equiv1 (a b: prod obC obD) : relation (Prod_mor a b) :=
          fun f g =>  fst f == fst g /\ snd f == snd g.
*)
Lemma Prod_equiv_equiv (c d: prod obC obD) : 
       @Equivalence (prod (morC (fst c) (fst d))
                          (morD (snd c) (snd d))) 
     (fun f g =>  fst f == fst g /\ snd f == snd g).
Proof. intros a b.
        split.
  unfold Reflexive. intro x; split; apply hom_refl.
  unfold Symmetric. intros x y H. destruct H as [H1 H2].
      split; apply hom_sym; auto.
  unfold Transitive. intros x y z H h.
     destruct H as [H1 H2]; destruct h as [h1 h2].
     split. apply (hom_trans H1 h1).
            apply (hom_trans H2 h2).
Qed.

Definition Prod_equiv (a b: prod obC obD) := 
        Build_Setoid (Prod_equiv_equiv a b).

Obligation Tactic := idtac.

Program Instance PROD_struct : 
        Cat_struct (fun c d: prod obC obD => 
                      prod (morC (fst c) (fst d))
                           (morD (snd c) (snd d))) := {
(*  obj := Prod_obj;
  mor := Prod_mor; *)
  mor_oid := Prod_equiv;
  id := Prod_id;
  comp := Prod_comp
}.
Next Obligation.
Proof. 
  repeat red. 
  intros a b c x y H x0 y0 H'.
  destruct H as [H1 H2];
  destruct H' as [h1 h2]. 
  simpl. split.
  rewrite H1. rewrite h1.
  apply hom_refl.
  rewrite H2. rewrite h2.
  apply hom_refl.
Qed.
Next Obligation.
Proof.
  intros a b f.
  repeat rewrite idr.
  cat.
Qed.
Next Obligation.
Proof.
  intros a b f.
  repeat rewrite idl.
  cat.
Qed.
Next Obligation.
Proof. 
  intros a b c d f g h.
  simpl.
  split; rewrite assoc;
  apply hom_refl.
Qed.

Definition PROD := Build_Cat PROD_struct.

Section projections.

Program Instance catprod_prl_struct : Functor_struct (C:=PROD) (D:=C) 
       (fun a b f => fst f).
Next Obligation.
Proof.
  intros a b.
  unfold Proper; red.
  intros x y H.
  elim H; auto.
Qed.
Next Obligation.
Proof.
  cat.
Qed.
Next Obligation.
Proof.
  cat.
Qed.

Definition catprod_prl := Build_Functor catprod_prl_struct.

Program Instance catprod_prr_struct : Functor_struct (C:=PROD) (D:=D) 
       (fun a b f => snd f).
Next Obligation.
Proof.
  intros a b.
  unfold Proper; red.
  intros x y H.
  elim H; auto.
Qed.
Next Obligation.
Proof.
  cat.
Qed.
Next Obligation.
Proof.
  cat.
Qed.

Definition catprod_prr := Build_Functor catprod_prr_struct.


End projections.

Definition build_prod_obj (c:obC)(d:obD): PROD :=
              (c, d).

Definition build_prod_mor (c c':obC)(d d':obD)
 (f: morC c c') (g: morD d d'): 
 mor (build_prod_obj c d) (build_prod_obj c' d') := (f, g).


Lemma cat_prod_pair_eq a b c d (f f': morC a b) (g g':morD c d):
    f == f' -> g == g' -> build_prod_mor f g == 
                          build_prod_mor f' g'.
Proof.
  intros.
  simpl.
  auto.
Qed.

Lemma cat_prod_pair_Equal_hom 
      a a' b b' c c' d d' (f: morC a b) (f':morC a' b')
                          (g:morD c d) (g': morD c' d'):
    f === f' -> g === g' -> build_prod_mor f g === 
                          build_prod_mor f' g'.
Proof.
  intros.
  unfold build_prod_mor.
  generalize dependent d.
  generalize dependent c.
  generalize dependent c'.
  generalize dependent d'.
  elim H.
  intros.
  elim H1.
  intros.
  apply Build_Equal_hom.
  apply cat_prod_pair_eq; auto.
Qed.

Lemma Equal_hom_projs a a' b b' (g:morC a a') (h:morD b b') x x' y y' 
        (f : build_prod_obj x y ---> build_prod_obj x' y'):
     fst f === g -> snd f === h -> 
              f === build_prod_mor g h.
Proof.
  intros a a' b b' g h x x'
         y y' f H1 H2.
  destruct f as [f1 f2].
  simpl in *.
  set (H':=cat_prod_pair_Equal_hom H1 H2).
  apply H'.
Qed.
  


Section cat_prod_mor.

Variable obE : Type.
Variable morE : obE -> obE -> Type.
Variable E : Cat_struct morE.

Variable F: Functor E C.
Variable G: Functor E D.

Program Instance cat_prod_mor_struct : Functor_struct (C:=E)(D:=PROD)
     (fun a b f => build_prod_mor (#F f) (#G f)).
Next Obligation.
Proof.
  unfold Proper; red.
  simpl.
  intros a b x y H;
  rewrite H.
  cat.
Qed.
Next Obligation.
Proof.
  cat.
Qed.
Next Obligation.
Proof.
  cat.
Qed.

Definition cat_prod_mor := Build_Functor cat_prod_mor_struct.

End cat_prod_mor.


Section Equality_in_PROD.

Notation "f 'X' g" := (build_prod_mor  f g) (at level 0).

Lemma build_prod_mor_proper a b c d : Proper (equiv ==> equiv ==> equiv) 
                                     (@build_prod_mor a b c d).
Proof.
  intros a b c d.
  unfold Proper; do 2 red.
  intros x y H x0 y0 H0.
  simpl.
  rewrite H.
  rewrite H0.
  cat.
Qed.
  

Lemma prod_mor_equal_l (c c': obC) (d d': obD)
 (f f': morC c c') (g: morD d d') : 
    f == f' -> f X g ==  f' X  g .
Proof. intros.
       unfold equiv. simpl.
       
       simpl.
       split; try apply hom_refl; auto.
Qed.

Lemma prod_mor_equal_r (c c': obC) (d d': obD)
 (f : morC c c') (g g': morD d d') : 
    g == g' ->  f X g ==  f X g'.
Proof. intros.
       unfold equiv. simpl.
       
       simpl.
       split; try apply hom_refl; auto.
Qed.

Variable obB: Type.
Variable morB: obB -> obB -> Type.
Variable B: Cat_struct morB.

Variable S: Functor PROD_struct B.

Lemma prod_mor_equal (c c': obC) (d d': obD)
 (f f': morC c c') (g g': morD d d') : f == f' -> g == g' ->
          #S (f X g) == #S (f' X g').
Proof. 
  intros c c' d d' f f' g g' H H0.
  unfold build_prod_obj.
  simpl.
  set (H':= functor_map_morphism (Functor_struct := S)).
  simpl in H'.
  apply H'.
  simpl.
  cat.
Qed.
End Equality_in_PROD.                 
End prod_cat.

Program Instance cat_prod : Cat_Prod Cat_CAT := {
  product a b := PROD a b;
  prl a b := catprod_prl a b;
  prr a b := catprod_prr a b;
  prod_mor a b c f g := cat_prod_mor f g
}.
Next Obligation.
Proof. 
  intros a c d.
  unfold Proper; do 2 red.
  intros F G H F' G' H' r s  f.
  unfold cat_prod_mor.
  simpl.
  unfold build_prod_mor.
  set (H1:= cat_prod_pair_Equal_hom (C:=c)(D:=d)).
  unfold build_prod_mor in H1.
  set (H2 := H1 _ _ _ _ _ _ _ 
          _ _ _ _ _ (H _ _ f) (H' _ _ f)).
  auto.
Qed.
Next Obligation.
Proof.
  intros a c d f g;
  simpl;
  split; intros; 
  apply Equal_hom_refl.
Qed.
Next Obligation.
Proof.
  simpl.
  intros a c d f g h';
  simpl.
  intros.
  destruct H.
  unfold build_prod_mor.
  set (H1 := H  _ _ f0).
  set (H2 := H0 _ _ f0).
  set (r := #h' f0) in *.
  generalize dependent H1.
  generalize dependent H2.
  
  destruct r as [f1 f2].
  destruct (h' a0).
  destruct (h' b).
  simpl in *.
  intros.
  set (H4:= cat_prod_pair_Equal_hom (C:=c)(D:=d)).
  unfold build_prod_mor in H4.
  set (H5 := H4 _ _ _ _ _ _ _ 
          _ _ _ _ _ (H1) (H2)).
  apply H5.
Qed.
  

(*Reserved Notation "{ c , d }" (at level 0).*)

(*Notation "{ c , d }" := (@build_prod_obj _ _ c d)(at level 0):cat_scope.*)
(*Notation "f | g" := (build_prod_mor _ _ f g) (at level 44).*)





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
    Proof. apply Build_Functor_struct.
           
           intros a b; simpl.
           repeat red. simpl.
           unfold PROD. simpl.
           intros x y H.
           destruct H as [[H1 H2] H3]. 
           split; auto.
           
           intro a; simpl.
           repeat red. simpl.
           simpl.
           repeat split; apply hom_refl.
           
           intros a b c f g; simpl.
           repeat red.
           simpl.
           simpl. repeat split; apply hom_refl.
    Qed.
         
End PROD_almost_assoc.






(** prod of two functors *)

Section prod_func.

Variables obC obD: Type.
Variable morC : obC -> obC -> Type.
Variable morD : obD -> obD -> Type.
Variable C: Cat_struct morC.
Variable D: Cat_struct morD.

Variables obC' obD': Type.
Variable morC' : obC' -> obC' -> Type.
Variable morD' : obD' -> obD' -> Type.
Variable C': Cat_struct morC'.
Variable D': Cat_struct morD'.


(*Variables C D C' D': Category.*)
Variables (F: Functor C D) (G: Functor C' D').
(*
Definition P := PROD C C'.
Definition Q := PROD D D'.
*)
Definition prod_Fobj : obj (PROD C C') -> obj (PROD D D') := 
         fun a => (F (fst a), G (snd a)).
Definition prod_Fmor (a b: obj (PROD C C')) (f: mor a  b) : 
                prod_Fobj a ---> prod_Fobj b :=
        (#F (fst f), #G (snd f)).

Program Definition Prod_functor : Functor (PROD C C') (PROD D D') := 
          Build_Functor
  (Fobj := prod_Fobj)
  (Fmor := prod_Fmor) _ .

  Next Obligation.
    Proof. apply Build_Functor_struct.
           intros a b;
                  
       simpl. repeat red.
       intros x y H;
       destruct H as [H1 H2].
       simpl. split; [
       rewrite H1 |
       rewrite H2 ];
       apply hom_refl.
       
       intro a;
       unfold prod_Fobj,
                  Prod_id, prod_Fmor.
           simpl.
         
           split; simpl; rewrite FId;
                  apply hom_refl.
           
        unfold prod_Fobj,
                  Prod_comp, prod_Fmor.
           simpl. split; simpl; 
                  rewrite FComp;
                  apply hom_refl.
    Qed.

End prod_func.


Section some_other_product_on_functors.

Variables obC obD: Type.
Variable morC : obC -> obC -> Type.
Variable morD : obD -> obD -> Type.
Variable C: Cat_struct morC.
Variable D: Cat_struct morD.

Variables F G: Functor C D.

Program Definition par_prodF : Functor C (PROD D D):= Build_Functor
  (Fobj := fun c => (F c, G c))
  (Fmor := fun c d f => (#F f, #G f)) _.

  Next Obligation.
    Proof. apply Build_Functor_struct.
    
           intros a b;
           unfold Proper. red. simpl.
           simpl. intros x y H; 
           repeat rewrite H; split; simpl; apply hom_refl.
           
           intro a; simpl.  simpl.
           split; apply FId.
           
           intros a b c f g; simpl. simpl.
           cat.
 
  Qed.

End some_other_product_on_functors.

Existing Instance build_prod_mor_proper.















