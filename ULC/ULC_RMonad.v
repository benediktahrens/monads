
Require Export CatSem.CAT.cat_TYPE_option.
Require Export CatSem.CAT.rmonad.
Require Export CatSem.CAT.rmodule_TYPE.
Require Export CatSem.ULC.ULC_semantics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Automatic Introduction.

Obligation Tactic := fin.

Program Instance ULCBETA_s : RMonad_struct (SM_po) ULCBETA := {
   rweta := VAR;
   rkleisli a b f := SUBST f
}.
Next Obligation.
Proof.
  unfold Proper;
  red;
  fin.
Qed.

Definition ULCBETA : RMonad (SM_po) := Build_RMonad ULCBETA_s.

Lemma rename_lift V (v : ULC V) W (f : V ---> W) : 
       v //- f = rlift ULCBETA f v.
Proof.
  unfold lift;
  fin.
Qed.


Section app_po.

Obligation Tactic := idtac.

Program Instance app_po_mors c : PO_mor_struct
  (a := PO_product (ULCBETA c )  (ULCBETA c))
  (b := ULCBETA c)
  (fun z => App (fst z) (snd z)).
Next Obligation.
Proof.
  intros c.
  unfold Proper;
  red.
  intros x y H.
  destruct H.
  simpl in *.
  transitivity (App v' w).
    apply cp_App1; auto.
    apply cp_App2; auto.
Qed.

Definition app_po_mor c := Build_PO_mor (app_po_mors c).

Obligation Tactic := fin.

Program Instance ulc_app_s  : RModule_Hom_struct
  (M:=product (C:=RMOD _ PO) ULCBETA ULCBETA) 
  (N:=ULCBETA) (app_po_mor).

Definition ulc_app := Build_RModule_Hom ulc_app_s.

End app_po.

Section abs_po.


Obligation Tactic := unfold Proper; red; 
        simpl; intros; apply cp_Abs; auto.

Program Instance abs_po_mors c : PO_mor_struct
  (a := (ULCBETA (option c)))
  (b := (ULCBETA c)) (@Abs _ ).

Definition abs_po_mor c := Build_PO_mor (abs_po_mors c).

Obligation Tactic := idtac.

Program Instance ulc_abs_s : RModule_Hom_struct
 (M:= DER_RMOD_not _ _  ULCBETA) 
 (N:=ULCBETA) abs_po_mor.
Next Obligation.
Proof.
  fin.
  apply f_equal.
  apply subst_eq.
  intros.
  match goal with [H:option _ |- _ ]=> destruct H end;
  simpl; fin.
Qed.

Definition ulc_abs := Build_RModule_Hom ulc_abs_s.

End abs_po.