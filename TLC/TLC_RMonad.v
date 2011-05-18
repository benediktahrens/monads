
Require Export CatSem.CAT.rmonad.
Require Export CatSem.CAT.rmodule_TYPE.
Require Export CatSem.TLC.TLC_semantics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.


Program Instance TLCBs : RMonad_struct (SM_ipo TY) (BETA) := {
  rweta c := SM_ind (var (V:=c)) ;
  rkleisli := subst
}.

Canonical Structure TLCB := Build_RMonad TLCBs.

Lemma shift_shift r V t (y : opt r V t) W 
  (f : ipo_mor (sm_ipo (T:=TY) V) (BETA W)):
     sshift_ (P:=TLCB) (W:=W) f y = y >- f.
Proof.
  intros r v t y.
  destruct y as [t y | ];
  simpl;
  intros;
  fin.
Qed.


Section app_po.

Variables r s : TLCtypes.

Obligation Tactic := idtac.

Program Instance app_po_mors c : PO_mor_struct
  (a := PO_product (ipo_proj (BETA c) (r ~> s))  (ipo_proj (BETA c) r))
  (b := ipo_proj (BETA c) s)
  (fun z => app (fst z) (snd z)).
Next Obligation.
Proof.
  intros c.
  unfold Proper;
  red.
  intros x y H.
  destruct H.
  simpl in *.
  transitivity (app v' w).
    apply cp_App1; auto.
    apply cp_App2; auto.
Qed.

Definition app_po_mor c := Build_PO_mor (app_po_mors c).

Obligation Tactic := fin.

Program Instance tlc_app_s  : RModule_Hom_struct
  (M:=product ((FIB_RMOD TLCB (r ~> s)) TLCB) 
              ((FIB_RMOD TLCB r) TLCB))
  (N:=FIB_RMOD TLCB s TLCB) (app_po_mor).

Definition tlc_app := Build_RModule_Hom tlc_app_s.

End app_po.

Section abs_po.

Variables r s : TLCtypes.

Obligation Tactic := unfold Proper; red; 
        simpl; intros; apply cp_Lam; auto.

Program Instance abs_po_mors c : PO_mor_struct
  (a := (ipo_proj (BETA (c * r)) s))
  (b := ipo_proj (BETA c) (r ~> s)) (@abs _ _ _ ).

Definition abs_po_mor c := Build_PO_mor (abs_po_mors c).

Obligation Tactic := idtac.

Program Instance tlc_abs_s : RModule_Hom_struct
 (M:=(FIB_RMOD TLCB s) ((DER_RMOD _ TLCB r) TLCB))
 (N:=(FIB_RMOD TLCB (r ~> s)) TLCB) abs_po_mor.
Next Obligation.
Proof.
  fin.
  apply f_equal.
  apply subst_eq.
  intros.
  apply (shift_shift y f ).
Qed.

Definition tlc_abs := Build_RModule_Hom tlc_abs_s.

End abs_po.



