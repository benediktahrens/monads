Require Export CatSem.ORDER.pcf_order_rep.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.


Lemma eq_Rep_equiv (P R: PCFPO_rep) : 
     Equivalence (A:=PCFPO_rep_Hom P R)
         (fun a c => forall r, a r == c r).
Proof.
 intros P R.
 constructor;
 simpl in *. 
 unfold Reflexive; intros. auto.
 unfold Symmetric; simpl; intros r s.
 intros.
 auto.
 
 unfold Transitive; intros.
 transitivity (y r t z0); auto.
Qed.

Definition eq_Rep_oid (P R : PCFPO_rep) := Build_Setoid (eq_Rep_equiv P R).


(** Identity Representation *)

Lemma Rep_id_struct (P : PCFPO_rep) : 
         PCFPO_rep_Hom_struct (RMonad_Hom_id P).
Proof.
  intro P;
  unfold Monad_Hom_id.
  simpl.
  constructor;
  simpl;
  intros;
  try rewrite <- surjective_pairing;
  auto.
Qed.

Definition Rep_id (P: PCFPO_rep) := Build_PCFPO_rep_Hom (Rep_id_struct P).

(** Composition of Representations *)
Section Rep_comp.
Variables P Q R: PCFPO_rep.
Variable M: PCFPO_rep_Hom P Q.
Variable N: PCFPO_rep_Hom Q R.

Program Instance Rep_comp_struct : 
      PCFPO_rep_Hom_struct (Monad_Hom_comp M N).
Next Obligation.
Proof.
  set (HM:=App_Hom (Sig := M)).
  set (HN:=App_Hom (Sig := N)).
  simpl in *.
  rewrite HM.
  rewrite HN.
  auto.
Qed.
Next Obligation.
  set (HM:=Abs_Hom (Sig := M)).
  set (HN:=Abs_Hom (Sig := N)).
  simpl in *.
  
  rewrite HM.
  rewrite HN.
  auto.
Qed.
Next Obligation.
  set (HM:=Rec_Hom (Sig := M)).
  set (HN:=Rec_Hom (Sig := N)).
  simpl in *.
  
  rewrite HM.
  rewrite HN.
  auto.
Qed.
Next Obligation.
  set (HM:=ttt_Hom (Sig := M)).
  set (HN:=ttt_Hom (Sig := N)).
  simpl in *.
  
  rewrite HM.
  rewrite HN.
  auto.
Qed.
Next Obligation.
  set (HM:=fff_Hom (Sig := M)).
  set (HN:=fff_Hom (Sig := N)).
  simpl in *.
  
  rewrite HM.
  rewrite HN.
  auto.
Qed.
Next Obligation.
  set (HM:=nats_Hom (Sig := M)).
  set (HN:=nats_Hom (Sig := N)).
  simpl in *.
  
  rewrite HM.
  rewrite HN.
  auto.
Qed.
Next Obligation.
  set (HM:=succ_Hom (Sig := M)).
  set (HN:=succ_Hom (Sig := N)).
  simpl in *.
  
  rewrite HM.
  rewrite HN.
  auto.
Qed.
Next Obligation.
  set (HM:=zero_Hom (Sig := M)).
  set (HN:=zero_Hom (Sig := N)).
  simpl in *.
  
  rewrite HM.
  rewrite HN.
  auto.
Qed.
Next Obligation.
  set (HM:=condN_Hom (Sig := M)).
  set (HN:=condN_Hom (Sig := N)).
  simpl in *.
  
  rewrite HM.
  rewrite HN.
  auto.
Qed.
Next Obligation.
  set (HM:=condB_Hom (Sig := M)).
  set (HN:=condB_Hom (Sig := N)).
  simpl in *.
  
  rewrite HM.
  rewrite HN.
  auto.
Qed.
Next Obligation.
  set (HM:=Bottom_Hom (Sig := M)).
  set (HN:=Bottom_Hom (Sig := N)).
  simpl in *.
  
  rewrite HM.
  rewrite HN.
  auto.
Qed.

Definition Rep_comp := Build_PCFPO_rep_Hom Rep_comp_struct.

End Rep_comp.

(** category of representations *)

Program Instance PCFPO_REP_struct : Cat (fun a c => PCFPO_rep_Hom a c) := {
  mor_oid a c := eq_Rep_oid a c;
  id a := Rep_id a;
  comp P Q R f g := Rep_comp f g
}.
Next Obligation.
Proof.
  unfold Proper in *; do 2 red.
  simpl. 
  intros y z h y' z' h' e r t.
  rewrite h.
  rewrite h'.
  auto.
Qed.

Definition PCFPO_REP := Build_Category PCFPO_REP_struct.

End PCFPO_representation.

Existing Instance pcfpo_rep_struct.

