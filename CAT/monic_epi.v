Require Export CatSem.CAT.category.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Automatic Introduction.

Section defs.

Variable obC : Type.
Variable morC : obC -> obC -> Type.
Variable C : Cat_struct morC.

(** definition of 
      - monic
      - epi
      - invertible
      - ismorphic objects
*)


Section morphisms.  

Variables a b : obC.

Class Monic (f: morC a b) := {
  monic_cond : forall d (g1 g2 : morC d a),
                 g1 ;; f == g2 ;; f -> g1 == g2
}.

Class Epi (f: morC a b) := {
  epi_cond : forall d (g1 g2 : morC b d),
                 f ;; g1 == f ;; g2 -> g1 == g2
}.

Class Invertible (f: morC a b) := {
  inverse : morC b a ;
  inv_prae : inverse ;; f == id _ ;
  inv_post : f ;; inverse == id _ 
}.

Class isomorphic := {
  inv_morphism : morC a b;
  invertible :> Invertible inv_morphism
}.

End morphisms.

Implicit Arguments inverse [a b Invertible].

Notation "-- f" := (inverse f) (at level 30).

(**   lemmata, such as "composition of monics..." etc bla bla *)

Section lemmata.

Variables a b c : obC.
Variable f : morC a b.
Variable g : morC b c.

Global Instance comp_of_monics 
   (Hf : Monic f) (Hg : Monic g) : Monic (f ;; g).
Proof.
  intros Hf Hg.
  constructor.
  intros d g1 g2.
  repeat rewrite <- assoc.
  intro H.
  assert (H': g1 ;; f == g2 ;; f).
  apply Hg; auto.
  apply Hf; auto.
Qed.

Global Instance comp_of_epis (Hf : Epi f) (Hg : Epi g) : Epi (f ;; g).
Proof.
  intros Hf Hg.
  constructor.
  intros d g1 g2.
  repeat rewrite assoc.
  intro H.
  assert (H': g ;; g1 == g ;; g2).
  apply Hf; auto.
  apply Hg; auto.
Qed.

Global Instance comp_monic_fst_monic (H : Monic (f ;; g)) : Monic f.
Proof.
  intro H.
  set (H':= monic_cond (Monic:=H)).
  constructor.
  intros d g1 g2 H2.
  apply (H' _ g1 g2).
  repeat rewrite <- assoc.
  rewrite H2.
  cat.
Qed.

Global Instance comp_epi_snd_epi (H : Epi (f ;; g)) : Epi g.
Proof.
  intro H.
  set (H':= epi_cond (Epi:=H)).
  constructor.
  intros d g1 g2 H2.
  apply (H' _ g1 g2).
  repeat rewrite assoc.
  rewrite H2.
  cat.
Qed.

(** uniqueness of the inverse *)

Lemma inverse_unique (H : Invertible f) h 
   (H1 : f ;; h == id _ ) (H2 : h ;; f == id _ ) : 
         h == -- f.
Proof.
  intros  H h H1 H2.
  transitivity (h ;; (f ;; --f)).
  rewrite inv_post; cat.
  rewrite <- assoc.
  rewrite H2.
  cat.
Qed.

Program Instance inverse_invertible (H : Invertible f) : 
                                 Invertible (--f):= {
  inverse := f;
  inv_prae := inv_post (Invertible := H);
  inv_post := inv_prae (Invertible := H)
}.

End lemmata.

Existing Instance inverse_invertible.

Section more_lemmata.

Variables a b c : obC.
Variable f : morC a b.
Variable g : morC b c.


Lemma inverse_inverse (H : Invertible f) : -- (-- f) == f.
Proof.
  intro H.
  apply hom_sym.
  apply inverse_unique.
  apply inv_prae.
  apply inv_post.
Qed.
  

Lemma put_inv_to_right (H : Invertible f) h : 
        f ;; g == h <-> g == -- f ;; h.
Proof.
  intros H h.
  split; intro H'.
  transitivity (--f ;; f ;; g).
  rewrite inv_prae; cat.
  rewrite <- H'; apply assoc.

  transitivity (f ;; --f ;; h).
  repeat rewrite assoc.
  apply praecomp; auto.
  rewrite inv_post; cat.
Qed.

End more_lemmata.


Section still_more_lemmata.

Variables a b c : obC.
Variable f : morC a b.
Variable g : morC b c.

(** inverse of a composition *)

Program Instance inv_of_comp (Hf : Invertible f) (Hg : Invertible g) :
      Invertible (f ;; g) := {
  inverse := --g ;; --f
}.
Next Obligation.
Proof.
  apply hom_sym.
  rewrite assoc.
  rewrite <- put_inv_to_right.
  rewrite <- assoc.
  rewrite inv_prae.
  cat.
Qed.

Next Obligation.
  apply hom_sym.
  
  
  rewrite <- assoc.
  set (z := f ;; g ;; -- g).
  
  assert (eqz :z == f).
  unfold z.
  rewrite  assoc .
  rewrite inv_post.
  cat.
  rewrite eqz.
  rewrite inv_post.

  cat.
Qed.


End still_more_lemmata.

End defs.

Implicit Arguments Invertible [obC morC C a b].
Implicit Arguments inverse [obC morC C a b Invertible].



