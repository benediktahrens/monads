Require Export CatSem.ORDER.tlc_order_rep.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

(** we define two morphisms of representations to be equal
    if they agree on each set of variables *)

Lemma eq_Rep_equiv (P R: TLCPO_rep) : 
     Equivalence (A:=TLCPO_rep_Hom P R)
         (fun a c => forall r, a r == c r).
Proof.
  intros;
  constructor;
  unfold Reflexive, 
         Symmetric,
         Transitive;
  simpl; intros; auto;
  etransitivity; eauto.
Qed.

Definition eq_Rep_oid (P R : TLCPO_rep) := Build_Setoid (eq_Rep_equiv P R).

(** Identity Representation *)

Program Instance Rep_id_struct (P : TLCPO_rep) : 
         TLCPO_rep_Hom_struct (RMonad_id P).
Next Obligation.
  match goal with [H:prod _ _ |- _] =>
     destruct H end;
  auto.
Qed.

Definition Rep_id (P: TLCPO_rep) := Build_TLCPO_rep_Hom (Rep_id_struct P).

(** Composition of Representations *)
Section Rep_comp.

Variables P Q R: TLCPO_rep.
Variable M: TLCPO_rep_Hom P Q.
Variable N: TLCPO_rep_Hom Q R.

Obligation Tactic := cat; 
    repeat rew (App_Hom (S:=M));
    repeat rew (App_Hom (S:=N));
    repeat rew (Abs_Hom (S:=M));
    repeat rew (Abs_Hom (S:=N));
    cat.

Program Instance Rep_comp_struct : 
      TLCPO_rep_Hom_struct (RMonad_comp M N).

Definition Rep_comp := Build_TLCPO_rep_Hom Rep_comp_struct.

End Rep_comp.

(** category of representations *)

Ltac t := match goal with [H : forall _ _ _ , _ = _ |- _ ] => 
              rewrite H end.

Obligation Tactic := cat; try unf_Proper;
      cat; repeat t; cat.

Program Instance TLCPO_REP_struct : Cat_struct (TLCPO_rep_Hom) := {
  mor_oid a c := eq_Rep_oid a c;
  id a := Rep_id a;
  comp P Q R f g := Rep_comp f g
}.

Definition TLCPO_REP := Build_Cat TLCPO_REP_struct.

Existing Instance tlcpo_rep_struct.

