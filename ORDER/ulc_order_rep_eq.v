Require Export CatSem.ORDER.ulc_order_rep.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

(** we define two morphisms of representations to be equal
    if they agree on each set of variables *)

Lemma eq_Rep_equiv (P R: ULCPO_rep) : 
     Equivalence (A:=ULCPO_rep_Hom P R)
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

Definition eq_Rep_oid (P R : ULCPO_rep) := Build_Setoid (eq_Rep_equiv P R).

(** Identity Representation *)

Program Instance Rep_id_struct (P : ULCPO_rep) : 
         ULCPO_rep_Hom_struct (RMonad_id P).
Next Obligation.
  match goal with [H:prod _ _ |- _] =>
     destruct H end;
  auto.
Qed.

Definition Rep_id (P: ULCPO_rep) := Build_ULCPO_rep_Hom (Rep_id_struct P).

(** Composition of Representations *)
Section Rep_comp.

Variables P Q R: ULCPO_rep.
Variable M: ULCPO_rep_Hom P Q.
Variable N: ULCPO_rep_Hom Q R.

Obligation Tactic := cat; 
    repeat rew (app_Hom (S:=M));
    repeat rew (app_Hom (S:=N));
    repeat rew (abs_Hom (S:=M));
    repeat rew (abs_Hom (S:=N));
    cat.

Program Instance Rep_comp_struct : 
      ULCPO_rep_Hom_struct (RMonad_comp M N).

Definition Rep_comp := Build_ULCPO_rep_Hom Rep_comp_struct.

End Rep_comp.

(** category of representations *)

Ltac t := match goal with [H : _ |- _ ] => 
              rewrite H end.

Obligation Tactic := cat; try unf_Proper;
      cat; repeat t; cat.

Program Instance ULCPO_REP_struct : Cat_struct (ULCPO_rep_Hom) := {
  mor_oid a c := eq_Rep_oid a c;
  id a := Rep_id a;
  comp P Q R f g := Rep_comp f g
}.

Definition ULCPO_REP := Build_Cat ULCPO_REP_struct.

Existing Instance ulcpo_rep_struct.

