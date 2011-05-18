
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Eqdep.

Require Export CatSem.CAT.category.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.


(** a = a' /\ b = b' gives mor a b -> mor a' b' *)

Section transport.

Variable ob: Type.
Variable hom: ob -> ob -> Type.
Variable C: Cat_struct hom.


Definition hom_transport (a b: ob)(f: hom a b) (a' b': ob)
          (H: a' = a) (H': b' = b) : hom a' b'.
intros a b f a' b' H H'. 
rewrite H; 
rewrite H'. 
exact f. 
Defined.

Lemma hom_transport_pi (a b: ob) (f: hom a b) (a' b': ob)
           (H1 H2 : a' = a) (Hb Hb2: b' = b):
      hom_transport f H1 Hb = hom_transport f H2 Hb2.
Proof. 
  intros a b f a' b' H1 H2 H3 H4.
  destruct H1.
  destruct H3.
  rewrite (UIP_refl _ _ H2).
  rewrite (UIP_refl _ _ H4).
  auto.
Qed.

Lemma hom_transport_id (a b: ob) (f: hom a b) 
              (Ha: a = a) (Hb: b = b): 
         hom_transport f Ha Hb = f.
Proof. 
  intros a b f Ha Hb. 
  rewrite (UIP_refl _ _ Ha).
  rewrite (UIP_refl _ _ Hb).
  auto.
Qed.


Lemma Equal_hom_imp_setoideq  (a b: ob)(f: hom a b) 
        (a' b': ob) (g: hom a' b')(H: f === g)(Ha: a' = a) (Hb: b' = b) :
          hom_transport f  Ha Hb == g .
Proof.
  destruct 1.
  intros Ha Hb.
  rewrite hom_transport_id.
  auto.
Qed.
 


Lemma Equal_hom_imp_setoideq2_jmq_eq (a b: ob) (f g: hom a b):
           f === g -> f == g.
Proof.
  intros a b f g H.
  dependent destruction H.
(*  dependent induction H.*)
  auto.
Qed.


Lemma Equal_hom_imp_setoideq2 (a b: ob) (f g: hom a b):
           f === g -> f == g.
Proof. 
  intros a b f g H.
  rewrite <- (@hom_transport_id a b f 
         (refl_equal) (refl_equal)).
  apply Equal_hom_imp_setoideq.
  auto.
Qed.

(** heterogeneous equality of morphisms entails 
    equality of source and target 
*)

Section Equal_hom_lemmata.

Variables a b c d: ob.
Variable f: hom a b.
Variable g: hom c d.

Hypothesis H: f === g.

Lemma Equal_hom_src: a = c.
Proof.
  elim H.
  auto.
Qed.

Lemma Equal_hom_tgt: b = d.
Proof.
  elim H. 
  auto. 
Qed.

End Equal_hom_lemmata.


End transport.
