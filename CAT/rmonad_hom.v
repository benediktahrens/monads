
Require Export CatSem.CAT.rmonad.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Section rmonad_hom.

Variables obC obD : Type.
Variable morC : obC -> obC -> Type.
Variable morD : obD -> obD -> Type.
Variable C : Cat_struct morC.
Variable D : Cat_struct morD.
Variable F : Functor C D.

Section rmonad_hom.

Variables P Q : RMonad F.


Class RMonad_Hom_struct (tau : forall c : obC, morD (P c) (Q c)) := {
  rmonad_hom_rweta : forall c:obC,
      rweta c ;; tau c == rweta c ;
  rmonad_hom_rkl : forall c d (f : morD (F c) (P d)),
      rkleisli f ;; tau d == tau c ;; rkleisli (f ;; tau d) 
}.

Record RMonad_Hom := {
  rmonad_hom :> forall c, morD (P c) (Q c);
  rmonad_hom_struct :> RMonad_Hom_struct rmonad_hom
}.

Section RMonad_Hom_NT.

Variable tau : forall c : obC, morD (P c) (Q c).

Variable tua : RMonad_Hom_struct tau.

(** trivial lemmata *)

Lemma rmon_hom_rweta (c : obC) : rweta c ;; tau c == rweta c.
Proof.
  apply rmonad_hom_rweta.
Qed.

Lemma rmon_hom_rkl (c d : obC) (f : morD (F c) (P d)) : 
   rkleisli f ;; tau d == tau c ;; rkleisli (f ;; tau d).
Proof.
  apply rmonad_hom_rkl.
Qed.

Hint Rewrite rmon_hom_rweta : rmonad.
Hint Resolve rmon_hom_rkl : rmonad.
Hint Rewrite rmon_hom_rkl.

Obligation Tactic := idtac.

Program Instance RMonad_Hom_NT : 
  NT_struct (F:=RMFunc P) (G:=RMFunc Q) tau.
Next Obligation.
Proof.
  simpl.
  intros c d f.
  unfold rlift.
  rewrite (rmonad_hom_rkl).
  rewrite assoc.
  rmonad.
Qed.

End RMonad_Hom_NT.

End rmonad_hom.


Section RMonad_id_comp.

Variable P : RMonad F.

Obligation Tactic := rmonad.

Program Instance RMonad_id_s : 
  RMonad_Hom_struct (P:=P) (fun _ => id _ ).

Definition RMonad_id := Build_RMonad_Hom RMonad_id_s.

Variables Q R : RMonad F.
Variable S : RMonad_Hom P Q.
Variable T : RMonad_Hom Q R.

Program Instance RMonad_comp_s : 
  RMonad_Hom_struct (fun c => S c ;; T c).
Next Obligation.
Proof.
  rewrite <- assoc.
  rewrite (rmon_hom_rweta S).
  rewrite (rmon_hom_rweta T).
  cat.
Qed.
Next Obligation.
Proof.
  rewrite <- assoc.
  rewrite (rmon_hom_rkl S).
  rewrite assoc.
  rewrite (rmon_hom_rkl T).
  rmonad.
Qed.

Definition RMonad_comp := Build_RMonad_Hom RMonad_comp_s.

End RMonad_id_comp.

Lemma RMonad_Hom_equiv (P Q: RMonad F) : 
   Equivalence (A:=RMonad_Hom P Q) (fun M N => forall x, M x == N x).
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

Definition RMonad_Hom_oid (P Q: RMonad F) := 
           Build_Setoid (RMonad_Hom_equiv P Q).

Obligation Tactic := simpl; intros; try apply assoc; cat.

Program Instance RMONAD_struct : Cat_struct RMonad_Hom := {
  mor_oid := RMonad_Hom_oid ;
  comp := RMonad_comp ;
  id := RMonad_id
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

Definition RMONAD := Build_Cat RMONAD_struct.

End rmonad_hom.

Existing Instance rmonad_hom_struct.

Hint Rewrite rmon_hom_rweta : rmonad.
Hint Resolve rmon_hom_rkl : rmonad.
Hint Rewrite rmon_hom_rkl : rmonad.