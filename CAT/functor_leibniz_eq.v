Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.

Require Export CatSem.CAT.functor.
Require Export CatSem.CAT.category_hom_transport.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

(** a useful lemma about "Leibniz Equality" for Functors *)
(** two Functors are equal if their data are (extensionally) equal *)

Section Functor_equal.

Variables obC obD: Type.
Variable morC : obC -> obC -> Type.
Variable morD : obD -> obD -> Type.    
Variable C: Cat_struct morC.
Variable D: Cat_struct morD.

Lemma Functor_Leibniz_equal: forall F G:Functor C D,
   forall (H: forall c, G c = F c ),
   (forall a b (f: morC a b), 
          hom_transport (#F f) (H a) (H b) = (#G f)) 
     -> F = G.
Proof.
  intros F G H H'.
  assert (H0: @Fobj _ _ _ _ _  _ G = 
             @Fobj _ _ _ _ _ _ F).
  extensionality x. apply H.

  destruct F as [Fo Fm Fx].
  destruct G as [Go Gm Gx].
  simpl in H0.
 
  generalize dependent Gm.
  generalize dependent Fm.
  rewrite H0. simpl.
  intros Fm Fx Gm Gx H H1.
  
  assert (H2: Fm = Gm).
  extensionality a.
  extensionality b.
  extensionality f.
  set (h:= H1 a b f).
  rewrite <- h.
  apply eq_sym; apply hom_transport_id.
  
  generalize dependent Gx. rewrite <- H2.
  intro Gx.
  rewrite (proof_irrelevance _ Fx Gx).
  auto.
Qed.
 
(** Properties of Composition and Id wrt "Leibniz Eq" 
      - left identity
      - right identity
      - associativity 
*)

Section Functor_Leibniz_props.

Variable F: Functor C D.

Lemma IdFl: CompF (Id C) F = F.
Proof.
  assert (H: forall c, (CompF (Id C) F) c = F c);
  cat.

  assert (H': @Fobj _ _ _ _ _ _ (CompF (Id C) F) = 
            @Fobj _ _ _ _ _ _ F).
  extensionality x.
  auto.

  apply (@Functor_Leibniz_equal  
               (CompF (Id C) F) F H).
  intros a b f.
  assert (Ha := H a).
  assert (Hb := H b).
  generalize Ha; clear Ha.
  generalize Hb; clear Hb.
  unfold CompF. simpl.
  intros Hb Ha.
  rewrite hom_transport_id.
  auto.
Qed.


Lemma IdFr: CompF F (Id D) = F.
Proof.
  assert (H: forall c, (CompF F (Id D)) c = F c);
  cat.

  assert (H': @Fobj _ _ _ _ _ _  (CompF F (Id D)) = 
            @Fobj _ _ _ _ _ _      F).
  extensionality x.
  auto.

  apply (@Functor_Leibniz_equal 
              (CompF F (Id D)) F H).
  intros a b f.
  assert (Ha := H a).
  assert (Hb := H b).
  generalize Ha; clear Ha.
  generalize Hb; clear Hb.
  unfold CompF. 
  simpl.
  intros Hb Ha.
  rewrite hom_transport_id.
  auto.
Qed.

End Functor_Leibniz_props.

End Functor_equal.

Section assoc.

Variables obC obD: Type.
Variable morC : obC -> obC -> Type.
Variable morD : obD -> obD -> Type.    
Variable C: Cat_struct morC.
Variable D: Cat_struct morD.
(*Variables E E': Category.*)
Variables obE obE': Type.
Variable morE: obE -> obE -> Type.
Variable morE': obE' -> obE' -> Type.
Variable E: Cat_struct morE.
Variable E': Cat_struct morE'.
Variable F : Functor C D.
Variable G: Functor D E.
Variable H: Functor E E'.

Lemma CompFassoc: CompF (CompF F G) H = CompF F (CompF G H).
Proof. 
  assert (H': forall c, 
    (CompF F (CompF G H)) c =
    (CompF (CompF F G) H) c);
  auto.
  
  apply (@Functor_Leibniz_equal _ _ 
         _ _ _ _ _ _ H').
  intros a b f.
  unfold CompF. 
  simpl. 
  rewrite hom_transport_id.
  auto.
Qed.

End assoc.


(** what is the relation between eq_Functor and Leibniz equality ? *)

(** extensional heterogeneous equality of F and G implies 
    Leibniz equality on objects of F and G *)

Section eq_Functor_imp_eq_Fobj.

Variables obC obD: Type.
Variable morC: obC -> obC -> Type.
Variable morD: obD -> obD -> Type.
Variable C : Cat_struct morC.
Variable D : Cat_struct morD.


Variables F G: Functor C D.

Hypothesis H:forall a b (f:morC a b),  #F f === #G f.

Lemma EXT_Functor_imp_ext_Leibniz_Fobj: @Fobj _ _ _ _ _ _ F = 
                              @Fobj _ _ _ _ _ _ G.
Proof.
  assert (H': forall x, F x = G x).
  
  intros x. 
  assert (H'' := H (id x)).
  assert (H''' := Equal_hom_src H'').
  auto.
  
  extensionality x.
  auto.
Qed.

End eq_Functor_imp_eq_Fobj.


Section CompF_Morphism.

Variable obC obD obE: Type.
Variable morC : obC -> obC -> Type.
Variable morD : obD -> obD -> Type.
Variable morE : obE -> obE -> Type.
Variable C: Cat_struct morC.
Variable D: Cat_struct morD.
Variable E: Cat_struct morE.

(** Composition of functors is a morphism with respect to 
     EXTensional heterogeneous equality of functors *)

Lemma CompF_oid : 
            Proper (@EXT_Functor _ _ _ _ C D ==>
                      @EXT_Functor _ _ _ _ D E ==> 
                      @EXT_Functor _ _ _ _ C E) 
   (@CompF _ _ C _ _ _ _ D E).
Proof. 
  unfold Proper. 
  repeat red.
  unfold EXT_Functor.
  intros F F' H G G' H1 a b f.
  unfold CompF. 
  simpl. 

  
  assert (H0: @Fobj _ _ _ _ _ _ F = 
                   @Fobj _ _ _ _ _ _ F').
  apply EXT_Functor_imp_ext_Leibniz_Fobj.
       apply H.

       assert (Hf := H a b f).
       generalize dependent Hf.
       generalize (#F f).
       rewrite H0.
       intros f0 Hf0.
       assert (@Fobj _ _ _ _ _ _ G = 
               @Fobj _ _ _ _ _ _ G').
         apply EXT_Functor_imp_ext_Leibniz_Fobj.
         apply H1.
       assert (f0 == #F' f).
         apply Equal_hom_imp_setoideq2.
         auto.

       apply F_equal_helper2;
       auto. 
Qed.

      
End CompF_Morphism.



















