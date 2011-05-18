Require Export CatSem.CAT.monad_haskell.
Require Export CatSem.CAT.NT.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

(** definition of a morphism of monads in haskell style *)

Section Monad_Hom.
(*
Variable obC: Type.
Variable morC: obC -> obC -> Type.
Variable C: Cat_struct morC.
*)
Variable C : Cat.

Section Monad_Hom_def.

Variables P Q: Monad C.

Class Monad_Hom_struct (Tau: forall c, P c ---> Q c) := {
  monad_hom_kl: forall X Y (f: X ---> P Y),
      kleisli f ;; Tau Y == Tau X ;; kleisli (f ;; Tau Y ) ;
  monad_hom_weta: forall c:C,
      weta c ;; Tau c == weta c
}.

Section lemmata.
Variable Tau : forall c, P c ---> Q c.
Variable H : Monad_Hom_struct Tau.

Lemma mh_weta c : weta c ;; Tau c == weta c.
Proof.
  apply H.
Qed.

Lemma mh_kleisli X Y f : 
  kleisli f ;; Tau Y == Tau X ;; kleisli (f ;; Tau Y ).
Proof.
  apply H.
Qed.

End lemmata.

Record Monad_Hom := {
  monad_hom:> forall c, P c ---> Q c;
  monad_hom_struct :> Monad_Hom_struct monad_hom
}.

Section Monad_Hom_NT.

Variable M : Monad_Hom.

Obligation Tactic := idtac.

Program Instance Monad_Hom_NatTrans : NT_struct (fun c => M c).
Next Obligation.
Proof.
  intros c d f.
  simpl.
  unfold lift.
  rewrite (monad_hom_kl (Monad_Hom_struct := M) (f;; weta d)).
  apply praecomp.
  apply kleisli_oid.
  rewrite assoc.
  rewrite (monad_hom_weta (Monad_Hom_struct := M)).
  cat.
Qed.

Canonical Structure Monad_Hom_NT := Build_NT Monad_Hom_NatTrans.

End Monad_Hom_NT.

End Monad_Hom_def.
(*
Definition eq_Monad_Hom (P Q: Monad C) : relation (Monad_Hom P Q) :=
     fun M N => forall x, M x == N x.
*)
Lemma Monad_Hom_equiv (P Q: Monad C) : 
   Equivalence (A:=Monad_Hom P Q) (fun M N => forall x, M x == N x).
Proof.
  intros P Q;
  constructor.
  unfold Reflexive.
  cat.
  unfold Symmetric;
  intros; apply hom_sym; 
  auto.
  unfold Transitive.
  intros.
  etransitivity; auto.
Qed.

Definition Monad_Hom_oid (P Q: Monad C) := 
           Build_Setoid (Monad_Hom_equiv P Q).


Hint Rewrite monad_hom_kl monad_hom_weta : monad.
Existing Instance monad_hom_struct.

Section Monad_Hom_comp.

Variables P Q R : Monad C.
Variable TT: Monad_Hom P Q.
Variable SS: Monad_Hom Q R.

Obligation Tactic := idtac.

Program Instance Monad_Hom_comp_struct : 
    Monad_Hom_struct (fun c => TT c ;; SS c).
Next Obligation.
Proof.
  intros X Y f; simpl.
  rewrite <- assoc.
  rewrite (monad_hom_kl); try apply TT.
  repeat rewrite assoc.
  apply praecomp.
  rewrite <- assoc.
  rewrite <- monad_hom_kl; 
  try apply SS.
  monad; try apply TT; try apply SS.
Qed.
Next Obligation.
Proof.
  intro c.
  rewrite <- assoc.
  rewrite monad_hom_weta;
  monad;
  try apply TT;
  try apply SS.
Qed.

Canonical Structure Monad_Hom_comp := 
        Build_Monad_Hom Monad_Hom_comp_struct.

End Monad_Hom_comp.

Section Monad_Hom_id.

Variable P: Monad C.

Obligation Tactic := monad.

Program Instance Monad_Hom_id_struct : 
         Monad_Hom_struct (fun c => id (P c)).

Canonical Structure Monad_Hom_id :=
      Build_Monad_Hom Monad_Hom_id_struct.

End Monad_Hom_id.

Existing Instance monad_hom_struct.

Obligation Tactic := simpl; intros; try apply assoc; cat.

Program Instance MONAD_struct : Cat_struct (fun P Q => Monad_Hom P Q) := {
  mor_oid P Q := Monad_Hom_oid P Q;
  id P := Monad_Hom_id P;
  comp a b c f g := Monad_Hom_comp f g
}.
Next Obligation.
Proof. 
  unfold Proper; do 2 red.
  simpl.
  intros x y H x' y' H' z;
  rewrite H;
  rewrite H';
  cat.
Qed.

Definition MONAD := Build_Cat MONAD_struct.

Section Facts.

Variables P Q:MONAD.

Variable h : P ---> Q.

Existing Instance monad_hom_struct.

Hint Rewrite monad_hom_kl monad_hom_weta : monad.

Lemma monad_hom_lift c d (f: c ---> d) : 
  lift f ;; h _ == h _ ;; lift f.
Proof.
  unfold lift.
  monad; apply h.
Qed.

Lemma monad_hom_join (c : C):
  join _ ;; h _ == h _ ;; lift (h _ )  ;; join c .
Proof.
  unfold join;
  monad; 
  try apply h.
Qed.

End Facts.

End Monad_Hom.

Existing Instance monad_hom_struct.
Existing Instance MONAD_struct.
Existing Instance Monad_Hom_oid.
Existing Instance Monad_Hom_NatTrans.

Hint Rewrite monad_hom_lift monad_hom_join monad_hom_kl 
              monad_hom_weta: monad.

Coercion Monad_Hom_NatTrans : Monad_Hom >-> NT_struct.



