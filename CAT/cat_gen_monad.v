Require Export CatSem.CAT.monad_h_morphism_gen.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.



Section id.

Variable C : Cat.
Variable P : Monad C.

Obligation Tactic := cat.

Program Instance gen_Monad_Hom_id_s : gen_Monad_Hom_struct (P:=P)
  (F0 := Id C)
 (fun c => id _ ).

Definition gen_Monad_Hom_id := Build_gen_Monad_Hom gen_Monad_Hom_id_s.

End id.

Section comp.

Variable C : Cat.
Variable P : Monad C.
Variable D : Cat.
Variable Q : Monad D.
Variable E : Cat.
Variable R : Monad E.

Variable F : Functor C D.
Variable S : gen_Monad_Hom P Q F.
Variable G : Functor D E.
Variable T : gen_Monad_Hom Q R G.

Program Instance gen_Monad_Hom_comp_s : gen_Monad_Hom_struct (P:=P)
  (F0 := G O F)
 (fun c => #G(S c) ;; T (F c)).
Next Obligation.
Proof.
  repeat rewrite <-assoc.
  rewrite <- FComp.
  rewrite <- FComp.
  rewrite assoc.  
  rerew (gen_monad_hom_kl (gen_Monad_Hom_struct := T)).
  rewrite <- assoc.
  rewrite <- FComp.
  rerew (gen_monad_hom_kl (gen_Monad_Hom_struct := S)).
  apply hom_refl.
Qed.
Next Obligation.
Proof.
  rewrite <- assoc.
  rewrite <- FComp.
  rewrite (gen_monad_hom_weta (gen_Monad_Hom_struct := S)).
  rewrite (gen_monad_hom_weta (gen_Monad_Hom_struct := T)).
  apply hom_refl.
Qed.

Definition gen_Monad_Hom_comp := 
    Build_gen_Monad_Hom gen_Monad_Hom_comp_s.

End comp.

Section eq.

Variable C : Cat.
Variable P : Monad C.
Variable D : Cat.
Variable Q : Monad D.


Record gen_Monad_Hom_type  := {
 base_f : Functor C D ;
 gen_mon_hom :> gen_Monad_Hom P Q base_f
}.

(*
Section eq_rel.

Variable a b : gen_Monad_Hom_type.

Record eq_gen_Monad_Hom_type : Prop := {
  b_NT : NatIso (base_f a)(base_f b) ;
  b_comm : forall c, b_NT (P c) ;; b c == a c ;; lift (b_NT c)
}.

End eq_rel.

Lemma eq_gen_eq : Equivalence eq_gen_Monad_Hom_type.
Proof.
  constructor.
  unfold Reflexive.
  intros.
  apply (@Build_eq_gen_Monad_Hom_type _ _ (vidNT _ )).
  simpl.
  cat.
  unfold Symmetric.
  intros. destruct H.
  simpl in *.

Definition eq_gen_Monad_Hom_type : relation gen_Monad_Hom_type :=
  fun a b => 
Section eq.

Variable C : Cat.
Variable P : Monad C.
Variable D : Cat.
Variable Q : Monad D.

Lemma gen_Monad_Hom_eq : 
    Equivalence (A:=gen_Monad_Hom_type P Q)
    (fun S T => forall c, S c == T c).


Variable F : Functor C D.
Variable F' : Functor C D.

Inductive eq_gen_Monad_Hom 

Lemma gen_Monad_Hom_eq : 
    Equivalence (A:=gen_Monad_Hom P Q F)
    (fun S T => forall c, S c == T c).
Proof.
  constructor.
  unfold Reflexive.
  cat.
  unfold Symmetric.
  intros.
  rew_all; cat.
  unfold Transitive.
  intros.
  rew_all.
  rew_all.
  cat.
Qed.

Definition gen_Monad_Hom_oid := Build_Setoid gen_Monad_Hom_eq.

End eq.

Program Instance gen_Monad_s : Cat 

  rewrite <- assoc.
  cat.

  apply Foid.
  rerew  (FComp G).
  simpl.
  cat.


 (Tau : forall c, F (P c) ---> Q (F c)) := {
  gen_monad_hom_kl : forall c d (f : c ---> P d),
       #F (kleisli f) ;; Tau _  == 
          Tau _ ;; (kleisli (#F f ;; Tau _ )) ;
  gen_monad_hom_weta : forall c : C,
       #F (weta c) ;; Tau _  == weta _ 
}.


Variable D : Cat.
Variable Q : Monad D.
Variable F : Functor C D

*)

End eq.