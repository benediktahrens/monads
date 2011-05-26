Require Export CatSem.PROP_untyped.arities.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.


(** we define a category of representations of a signature Sig  *)
(** main work has been done in ./arities.v , remains to do:
	- identity representation morphism
	- composition of rep morphs
*)

Section cat_of_reps.

Notation "[ T ]" := (list T) (at level 5).


Variable S : Signature.

(** identity representation morphism *)

Section id.

Variable P : Representation S.

Hint Extern 1 (CONSTR _ _ = CONSTR _ _) => apply CONSTR_eq.

Lemma Prod_mor_c_id V i (x : prod_mod_c _ V (sig (s:= S) i)):
 Prod_mor_c1 (RMonad_id P) (l:=sig (s:=S) i) (V:=V) x = x.
Proof.
  induction x; simpl; intros; auto.
Qed.

Hint Rewrite Prod_mor_c_id : bla.

Obligation Tactic := unfold commute, commute_left, commute_right;
     simpl; intros; autorewrite with bla; auto.

Hint Extern 1 (_ = _) => apply f_equal.

Program Instance Rep_Id_struct : Representation_Hom_struct (RMonad_id P).

Definition Rep_Id := Build_Representation_Hom Rep_Id_struct.

End id.

Hint Extern 1 (CONSTR _ _ = CONSTR _ _) => apply CONSTR_eq.

(** composition of rep homs, preparation *)

Section comp_prepar.

Variables P Q R : RMonad SM_po.
Variable f : RMonad_Hom P Q.
Variable g : RMonad_Hom Q R.

Lemma prod_ind_mod_mor_comp l (V : TYPE) (t : prod_mod_c _ V l) :
    Prod_mor_c1 (RMonad_comp f g) t = Prod_mor_c1 g (Prod_mor_c1 f t).
Proof.
  induction t; simpl; auto.
Qed.

Hint Rewrite prod_ind_mod_mor_comp : bla.

Lemma comp_hophop l 
       (MR : modhom_from_arity R (l)) 
       (MP : modhom_from_arity P (l))
       (MQ : modhom_from_arity Q (l))
       (HMf : commute f MP MQ)
       (HMg : commute g MQ MR): 
       commute (RMonad_comp f g) MP MR.
Proof.
  intros;
  unfold commute, commute_left in *;
  simpl in *; intros;
  rerew_all;
  autorewrite with bla; auto.
Qed.
    
End comp_prepar.

(** composition of rep homs *)

Section comp.

Variables P Q R : Representation S.
Variable f : Representation_Hom P Q.
Variable g : Representation_Hom Q R.

Obligation Tactic := simpl; intros;
   apply comp_hophop with (repr Q _ );
   match goal with 
       [H:Representation_Hom _ _ |- _ ] => apply H end.

Program Instance Rep_comp_struct : 
   Representation_Hom_struct (RMonad_comp f g).

Definition Rep_Comp := Build_Representation_Hom Rep_comp_struct.

End comp.

(** rep homs are equal if their resp carriers (monad homs) are *)

Section Req_equiv.

Variables P R : Representation S.

Ltac equiv := match goal with 
     | [|- Reflexive _ ] => unfold Reflexive; intro;
                            apply Equivalence_Reflexive
     | [|- Symmetric _] => unfold Symmetric; do 2 intro;
                            apply Equivalence_Symmetric
     | [|- Transitive _ ] => unfold Transitive; do 3 intro;
                             apply Equivalence_Transitive end.

Existing Instance RMonad_Hom_oid.

Lemma eq_Rep_equiv : 
   @Equivalence (Representation_Hom P R) 
     (fun a c => repr_hom_c a == repr_hom_c c).
Proof.
  constructor; equiv.
Qed.

Definition eq_Rep_oid := Build_Setoid (eq_Rep_equiv).

End Req_equiv.

Existing Instance RMONAD_struct.

Obligation Tactic := simpl; intros; try unf_Proper;
        simpl; intros; 
   repeat match goal with [H:_ |-_]=>rewrite H end;
   auto.

Program Instance REPRESENTATION_struct : 
         Cat_struct (@Representation_Hom S) := {
  mor_oid a c := eq_Rep_oid a c;
  id a := Rep_Id a;
  comp P Q R f g := Rep_Comp f g }.

Definition REPRESENTATION := Build_Cat REPRESENTATION_struct.

End cat_of_reps.









