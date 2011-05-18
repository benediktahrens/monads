Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Automatic Introduction.

Definition PI := proof_irrelevance.


Lemma break_Sig_Prop : forall A : Type, forall P : A -> Prop,
           forall a a' : A, forall (pa : P a)(pa': P a'), 
            a = a' -> 
          exist P a pa = exist P a' pa'.
Proof. intros. assert (P a = P a').
rewrite H; auto.
generalize pa.
rewrite H0 in pa.
rewrite H.
intros.
rewrite (@PI (P a') pa0 pa').
reflexivity.
Qed.

Lemma break_Sig_Prop2: forall A : Type, forall P : A -> Prop,
              forall a a': sig P,
              proj1_sig a = proj1_sig a' -> a = a'.
Proof. intros A P a a' H. 
       destruct a.  destruct a'. 
       apply break_Sig_Prop.
       auto.
Qed.

Lemma reduce_to_sigma: forall (A : Type)(B : A -> Type)(C : Type),
          forall f: forall a:A, B a -> C,
           forall a a' b b', 
           existT _ a b = existT _ a' b' ->
            f a b = f a' b'.
Proof. intros. dependent rewrite H; auto. Qed.
 
Lemma simpl_eq_sig: forall (A:Type) (B: A -> Type),
          forall (a a':A)(b:B a)(b':B a'),
             existT B a b = existT B a' b' ->
                a = a'.
Proof. intros A B a a' b b' H.
    dependent rewrite H. auto.
Qed.


(*
Lemma simpl_eq_sig2: forall A:Type, forall (B:A -> Type),
          forall (a:A) b b', existT B a b = existT B a b' ->
              projT2 (existT B a b) = projT2 (existT B a b').
Proof. intros. simpl. 
inversion H.
injection H. auto.
dependent rewrite <- H. simpl. 
inversion H.
injection H.
intros.
assumption.
*)