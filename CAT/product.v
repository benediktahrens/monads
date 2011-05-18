Require Export CatSem.CAT.category (*functor*).

Set Implicit Arguments.
Unset Strict Implicit.

Unset Automatic Introduction.


Section prod.

Variable obC: Type.
Variable morC: obC -> obC -> Type.

Class Cat_Prod (C:Cat_struct morC) := {
   product : obC -> obC -> obC;
   prl: forall a b, morC (product a b) a;
   prr: forall a b, morC (product a b) b;
   prod_mor: forall (a c d:obC) (f: morC a c)(g: morC a d),
       morC a (product c d);
   prod_mor_oid:> forall a c d, 
       Proper (equiv ==> equiv ==> equiv) (@prod_mor a c d);
   prod_diag: forall (a c d: obC) (f:morC a c)(g:morC a d),
              (prod_mor f g) ;; prl c d == f /\ 
              (prod_mor f g) ;; prr c d == g;
   prod_mor_unique: forall (a c d:obC) 
            (f:morC a c) (g:morC a d) (h':morC a (product c d)),
       h' ;; prl c d == f /\ h' ;; prr c d == g  -> 
                 h' == prod_mor f g
}.


Lemma prod_prl (C : Cat_struct morC)(H:Cat_Prod C): 
      forall (a c d: obC) (f:morC a c)(g:morC a d),
              (prod_mor f g) ;; prl c d == f.
Proof. 
  intros; 
  apply prod_diag. 
Qed.

Lemma prod_prr (C:Cat_struct morC)(H:Cat_Prod C): 
      forall (a c d: obC) (f:morC a c)(g:morC a d),
              (prod_mor f g) ;; prr c d == g.
Proof. 
  intros; 
  apply prod_diag. 
Qed.


End prod.

Hint Rewrite prod_prl prod_prr : cat.
Hint Resolve prod_prl prod_prr : cat.

(** some useful constructions *)

(** given
    - [f: a -> b]
    - [g: a' -> b']
   we can have f x g: a x a' -> b x b' *)
Section prod_arrow.

Notation "a 'x' b" := (product a b) (at level 40).

Variable obC: Type.
Variable morC: obC -> obC -> Type.
Variable C: Cat_struct morC.
Variable H: Cat_Prod C.

Definition product_mor a a' b b' (f: morC a b) (g : morC a' b') : 
  morC (a x a') (b x b') := 
     prod_mor (prl _ _ ;; f) (prr _ _ ;; g).

Notation "a 'X' b" := (product_mor a b) (at level 40).

Section product_mor_lemmata.

Variables a a' a'' b b' b'' c c' d e: obC.
(*
Lemma prod_mor_eq_product_mor (h:  morC (product b c) d)
                              (j: morC (product b c) e) : 
 prod_mor h j == product_mor 
*)


Lemma prod_mor_prod_mor (f: morC a b)(g: morC a c)
                        (h: morC (b x c) d)
                        (j: morC (b x c) e) : 
  prod_mor f g ;; prod_mor h j ==
          prod_mor (prod_mor f g ;; h) (prod_mor f g ;; j).
Proof.
  intros f g h j.
  apply prod_mor_unique.
  split; 
  rewrite assoc; 
  cat.
Qed.


Lemma product_mor_product_mor (f: morC a a') (f': morC a' a'') 
     (g: morC b b') (g': morC b' b''):
  (f ;; f') X (g ;; g') ==  f X g ;; f' X g'.
Proof.
  intros.
  unfold product_mor.
  apply hom_sym.
  apply prod_mor_unique.
  repeat rewrite assoc.
  repeat rewrite prod_prl.
  repeat rewrite prod_prr.
  repeat rewrite <- assoc.
  cat.
Qed.

Lemma product_mor_Proper:
     Proper (equiv ==> equiv ==> equiv) (@product_mor a a' b b').
Proof.
  unfold Proper; 
  do 2 red.
  intros y z H' x0 y0 H0.
  unfold product_mor.
  apply prod_mor_unique.
  cat.
Qed.

Lemma product_mor_id: id a X id b == id _ .
Proof.
  unfold product_mor.
  apply hom_sym.
  apply prod_mor_unique.
  cat.
Qed.


Lemma prod_mor_product_mor (f: morC a b) (g: morC a c) 
          (h: morC b b') (h': morC c c'):
  prod_mor f g ;; h X h' == prod_mor (f ;; h) (g ;; h').
Proof.
  intros f g h h'.
  unfold product_mor.
  apply prod_mor_unique.
  repeat rewrite assoc.
  rewrite prod_prl.
  rewrite prod_prr.
  repeat rewrite <- assoc.
  cat.
Qed.

End product_mor_lemmata.

End prod_arrow.

Existing Instance product_mor_Proper.

Section prod_assoc.

Variable obC: Type.
Variable morC: obC -> obC -> Type.
Variable C: Cat_struct morC.
Variable H: Cat_Prod C.

Variables a b c: obC.

Definition prod_assoc_l_r := prod_mor (prl _ _  ;; prl a b )
           (prod_mor (prl _ _ ;; prr _ _ ) (prr (product a b) c )).


Definition prod_assoc_r_l := prod_mor 
        (prod_mor (prl a (product b c)) (prr _ _ ;; prl _ _  ) )
        (prr a (product b c) ;; prr b c ).


Lemma prod_assoc_r_l_l_r: prod_assoc_r_l ;; prod_assoc_l_r == id _ .
Proof.
  unfold prod_assoc_r_l, 
         prod_assoc_l_r.
  rewrite prod_mor_prod_mor.
  rewrite <- assoc.
  rewrite prod_prl.
  rewrite prod_prl.
  apply hom_sym.
  apply prod_mor_unique.
  split; rewrite idl.
  repeat rewrite <- assoc;
  repeat rewrite prod_prl;
  cat.
  rewrite prod_mor_prod_mor.
  apply prod_mor_unique.
  split.
  rewrite <- assoc.
  rewrite prod_prl.
  rewrite prod_prr;
  cat.
  rewrite prod_prr.
  cat.
Qed.
  
Lemma prod_assoc_l_r_r_l : prod_assoc_l_r ;; prod_assoc_r_l == id _ .
Proof.
  unfold prod_assoc_r_l, 
         prod_assoc_l_r.
  rewrite prod_mor_prod_mor.
  rewrite <- assoc.
  rewrite prod_prr.
  rewrite prod_prr.
  apply hom_sym.
  apply prod_mor_unique.
  split; rewrite idl.
  rewrite prod_mor_prod_mor.
  apply prod_mor_unique.
  split.
  rewrite prod_prl; cat.
  rewrite <- assoc.
  repeat rewrite prod_prr.
  cat.
  cat.
Qed.
  
End prod_assoc.


Hint Resolve prod_prl prod_prr : cat.
Hint Rewrite prod_prl prod_prr : cat.



