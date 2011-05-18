
Require Export CatSem.CAT.category.
Require Export CatSem.CAT.functor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Section coprod.

Variable obC: Type.
Variable morC: obC -> obC -> Type.

Class Cat_Coprod (C:Cat_struct morC) := {
   coprod : obC -> obC -> obC;
   inl: forall a b, morC a (coprod a b);
   inr: forall a b, morC b (coprod a b);
   coprod_mor: forall (a b d:obC) (f: morC a d)(g: morC b d),
         morC (coprod a b) d ;
   coprod_mor_oid:> forall a c d, 
       Proper (equiv ==> equiv ==> equiv) (@coprod_mor a c d);
   coprod_diag: forall (a b d: obC) (f:morC a d)(g:morC b d),
              inl a b ;; (coprod_mor f g) == f /\ 
              inr a b ;; (coprod_mor f g) == g;
   coprod_mor_unique: forall (a b d:obC) 
            (f:morC a d) (g:morC b d) (h':morC (coprod a b) d),
       inl a b ;; h' == f /\ inr a b ;; h' == g  -> 
                 h'== coprod_mor f g
}.

Lemma inl_coprod (C:Cat_struct morC)(H:Cat_Coprod C): forall (a b d: obC) 
       (f: morC a d) (g: morC b d),
           inl a b ;; (coprod_mor f g) == f.
Proof. 
  intros; 
  apply coprod_diag. 
Qed.

Lemma inr_coprod (C:Cat_struct morC)(H:Cat_Coprod C): forall (a b d: obC) 
       (f: morC a d) (g: morC b d),
           inr a b ;; (coprod_mor f g) == g.
Proof. 
  intros; 
  apply coprod_diag. 
Qed.


End coprod.

Hint Rewrite inl_coprod inr_coprod : cat.
Hint Resolve inl_coprod inr_coprod : cat.

Section coprod_arrow.

Notation "a 'u' b" := (coprod a b) (at level 40).

Variable obC: Type.
Variable morC: obC -> obC -> Type.
Variable C: Cat_struct morC.
Variable H: Cat_Coprod C.

Definition coproduct_mor a a' b b' (f: morC a a') (g : morC b b') : 
  morC (a u b) (a' u b') := 
     coprod_mor (f ;; inl _ _ ) (g ;; inr _ _ ).

Notation "f 'U' g" := (coproduct_mor f g) (at level 40).

Variables a a' a'' b b' b'' c d e: obC.

Lemma coprod_mor_coprod_mor (f: morC a (c u d))(g:morC b (c u d))
                            (h:morC c e) (j: morC d e) : 
  coprod_mor f g ;; coprod_mor h j == 
     coprod_mor (f;; coprod_mor h j) (g;;coprod_mor h j).
Proof.
  intros;
  apply coprod_mor_unique;
  split; rewrite <- assoc; cat.
Qed.


Lemma coproduct_mor_Proper:
     Proper (equiv ==> equiv ==> equiv) (@coproduct_mor a a' b b').
Proof.
  unfold Proper; 
  do 2 red;
  intros;
  unfold coproduct_mor;
  apply coprod_mor_unique;
  rewrite inl_coprod;
  cat.
Qed.

Lemma coproduct_mor_id: id a U id b == id _ .
Proof.
  unfold coproduct_mor;
  apply hom_sym;
  apply coprod_mor_unique;
  cat.
Qed.


Lemma coprod_mor_coproduct_mor (f: morC a c) (g: morC b d) 
          (h: morC c e) (j: morC d e):
   f U g ;; coprod_mor h j == coprod_mor (f ;; h) (g ;; j).
Proof.
  intros;
  unfold coproduct_mor;
  apply coprod_mor_unique;
  repeat rewrite <- assoc;
  rewrite inl_coprod;
  rewrite inr_coprod;
  repeat rewrite  assoc;
  cat.
Qed.


Lemma coproduct_mor_coproduct_mor (f: morC a a') (f': morC a' a'') 
     (g: morC b b') (g': morC b' b''):
  (f ;; f') U (g ;; g') ==  f U g ;; f' U g'.
Proof.
  intros;
  unfold coproduct_mor;
  apply hom_sym;
  apply coprod_mor_unique;
  repeat rewrite <- assoc;
  rewrite inl_coprod;
  rewrite inr_coprod;
  repeat rewrite assoc;
  cat.
Qed.

End coprod_arrow.

Existing Instance coproduct_mor_Proper.

Section coprod_assoc.

Variable obC: Type.
Variable morC: obC -> obC -> Type.
Variable C: Cat_struct morC.
Variable H: Cat_Coprod C.

Variables a b c: obC.

Definition coprod_assoc_l_r := coprod_mor 
        (coprod_mor (inl a (coprod b c)) (inl _ _ ;; inr _ _ ))
           (inr b c ;; inr a (coprod b c)).


Definition coprod_assoc_r_l := coprod_mor 
        (inl _ _  ;; inl _ _ )
        (coprod_mor (inr a b ;; inl _ _) (inr (coprod a b) c )).

Lemma coprod_assoc_r_l_l_r: 
     coprod_assoc_r_l ;; coprod_assoc_l_r == id _ .
Proof.
  unfold coprod_assoc_r_l, 
         coprod_assoc_l_r;
  rewrite coprod_mor_coprod_mor;
  rewrite assoc;
  rewrite inl_coprod;
  rewrite inl_coprod;
  apply hom_sym;
  apply coprod_mor_unique;
  rewrite idr;
  rewrite idr;
  split;
   cat;
  rewrite coprod_mor_coprod_mor;
  apply coprod_mor_unique;
  split;
  try rewrite assoc;
  try rewrite inl_coprod;
  try rewrite inr_coprod;
  cat.
Qed.
 
Lemma coprod_assoc_l_r_r_l: 
     coprod_assoc_l_r ;; coprod_assoc_r_l == id _ .
Proof.
  unfold coprod_assoc_r_l, 
         coprod_assoc_l_r.
  rewrite coprod_mor_coprod_mor.
  rewrite assoc.
  rewrite inr_coprod.
  rewrite inr_coprod.
  apply hom_sym.
  apply coprod_mor_unique.
  rewrite idr.
  rewrite idr.
  split.
  rewrite coprod_mor_coprod_mor.
  apply coprod_mor_unique.
  split.
  rewrite inl_coprod.
  cat.
  rewrite assoc.
  rewrite inr_coprod.
  rewrite inl_coprod.
  cat.
  cat.
Qed.
  
End coprod_assoc.

(** coprod with a constant element on the right is a functor *)

Section coprod_rconst.
Notation "f 'U' g" := (coproduct_mor _ f g) (at level 40).
Variable obC: Type.
Variable morC: obC -> obC -> Type.
Variable C : Cat_struct morC.
Variable H : Cat_Coprod C.
Variable c : obC.


Program Instance CoP_R_struct : Functor_struct
 (Fobj:= fun x => coprod x c)
 (fun a b f => coproduct_mor _ f (id c)).
Next Obligation.
Proof.
  unfold Proper; red.
  intros.
  match goal with [H:_ |-_] => rewrite H end.
  cat.
Qed.
Next Obligation.
Proof.
  intros.
  rewrite coproduct_mor_id.
  cat.
Qed.
Next Obligation.
Proof.
  intros.
  rewrite <- coproduct_mor_coproduct_mor.
  cat.
Qed.

Definition CoP_R := Build_Functor CoP_R_struct.

End coprod_rconst.




