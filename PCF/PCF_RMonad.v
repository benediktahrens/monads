Require Export CatSem.CAT.rmonad.
Require Export CatSem.CAT.rmodule_TYPE.
Require Export CatSem.PCF.PCF_semantics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Section close_notation.
Notation "'TY'" := PCF.Sorts.
Notation "'Bool'" := PCF.Bool.
Notation "'Nat'" := PCF.Nat.

Notation "'IT'" := (ITYPE TY).
Notation "a '~>' b" := (PCF.Arrow a b) 
   (at level 69, right associativity).
Notation "M [*:= N ]" := (substar N M) (at level 50).
Notation "'$' f" := (@_shift _ _ _ f) (at level 30).
Notation "y >>- f" := (_shift f y) (at level 44).
Notation "y >>= f" := (@subst _ _ f _ y) (at level 42).

Ltac opt := simpl; intros; elim_opt.

Ltac fin := simpl in *; intros; 
   autorewrite with fin; auto with fin; simpl;
	try reflexivity.
Hint Unfold lift : fin.
Hint Extern 1 (_ = _) => f_equal : fin.
Hint Resolve rename_eq : fin.
Hint Rewrite rename_eq : fin.
Hint Resolve  rename_id shift_eq : fin.
Hint Rewrite  rename_id shift_eq : fin.
Hint Resolve shift_var : fin.
Hint Rewrite shift_var : fin.
Hint Resolve var_lift_shift_eq : fin.
Hint Resolve shift_lift : fin.
Hint Rewrite shift_lift : fin.
Hint Resolve subst_eq : fin.
Hint Rewrite subst_eq : fin.
Hint Rewrite subst_rename rename_subst : fin.
Hint Unfold inj : fin.
Hint Resolve subst_shift_shift subst_var subst_var_eta : fin.
Hint Rewrite subst_shift_shift subst_var subst_var_eta : fin.
Hint Resolve subst_var subst_subst : fin.
Hint Rewrite subst_subst : fin.
Hint Rewrite lift_rename : fin.
Obligation Tactic := fin.

Program Instance PCFEM_s : RMonad_struct (IDelta TY) PCFE := {
   rweta := VAR;
   rkleisli a b f := SUBST f
}.
Next Obligation.
Proof.
  unfold Proper;
  red;
  fin.
Qed.

Definition PCFEM : RMonad (IDelta TY) := Build_RMonad PCFEM_s.


Lemma shift_shift r s V W (f : IDelta _ V ---> PCFEM W)
                (x : (opt r V) s) :
   sshift_ (P:=PCFEM) (W:=W) f x = x >>- f .
Proof.
  intros r  s V W f y.
  destruct y as [t y | ];
  simpl;
  unfold inj;
  fin.
Qed.


Program Instance PCFApp_car_s :
forall (r s : TY) (c : TY -> Type),
PO_mor_struct (a:=PO_product (ipo_proj (PCFE c) (r ~> s)) 
                             (ipo_proj (PCFE c) r))
  (b:=ipo_proj (PCFE c) s)
  (fun  y => App (fst y) (snd y)).
Next Obligation.
Proof.
  unfold Proper;
  red.
  intros y z H.
  induction H;
  simpl in *.
  transitivity (App v w').
  apply cp_App2;
  auto.
  apply cp_App1;
  auto.
Qed.


Definition PCFApp_car r s:
(forall c : ITYPE TY,
  (Prod_RMod (P:=PCFEM) PO_prod 
         (Fib_RMod (P:=PCFEM) (r ~> s) PCFEM)
         (Fib_RMod (P:=PCFEM) r PCFEM)) c ---> 
  (Fib_RMod (P:=PCFEM) s PCFEM) c)
:= fun c => Build_PO_mor (PCFApp_car_s r s c).

Program Instance PCFApp_s:
forall r s : TY,
RModule_Hom_struct
  (M:=Prod_RMod (P:=PCFEM) PO_prod 
       (Fib_RMod (P:=PCFEM) (r ~> s) PCFEM)
       (Fib_RMod (P:=PCFEM) r PCFEM)) 
  (N:=Fib_RMod (P:=PCFEM) s PCFEM)
    (PCFApp_car r s).

Notation "M [ z ]" := (FIB_RMOD _ z M) (at level 35).
Notation "'d' M // s" := (DER_RMOD _ _ s M) (at level 25).
Notation "a 'x' b" := (product a b) (at level 30).

Definition PCFApp: forall r s : TY, 
 (PCFEM [r ~> s]) x (PCFEM [r]) ---> PCFEM [s] :=
   fun r s => Build_RModule_Hom (PCFApp_s r s).

Program Instance PCFAbs_car_s :
  forall (r s : TY) (c : TY -> Type),
 PO_mor_struct 
  (a:=ipo_proj (PCFE (opt r c)) s) 
  (b:=ipo_proj (PCFE c) (r ~> s))
  (Lam (V:=c) (t:=r) (s:=s)).
Next Obligation.
Proof.
  unfold Proper;
  red.
  intros y z H.
  induction H;
  simpl.
  reflexivity.
  transitivity (Lam y); 
  auto.
  apply cp_Lam.
  apply clos_refl_trans_1n_contains.
  apply H.
Qed.

Definition PCFAbs_car :
forall (r s : TY) (c : TY -> Type),
  PO_mor (ipo_proj (PCFE (opt r c)) s) 
         (ipo_proj (PCFE c) (r ~> s)) :=
 fun r s c => Build_PO_mor (PCFAbs_car_s r s c).

Obligation Tactic := fin.

Program Instance PCFAbs_s : forall r s : TY, 
  RModule_Hom_struct
  (M:=d PCFEM // r [s]) (N:=PCFEM [r ~> s])
  (PCFAbs_car r s).
Next Obligation.
Proof.
  apply f_equal.
  apply subst_eq.
  intros.
  rewrite shift_shift.
  auto.
Qed.
  

Definition PCFAbs r s :
 (d PCFEM // r [s]) ---> (PCFEM [r ~> s]) :=
  Build_RModule_Hom (PCFAbs_s r s).

Program Instance PCFRec_cs t c :
PO_mor_struct (a:=ipo_proj (PCFE c) (t ~> t)) 
              (b:=ipo_proj (PCFE c) t)
   (Rec (t:=t)).
Next Obligation.
Proof.
  unfold Proper;
  red.
  intros y z H.
  induction H;
  simpl in *.
  reflexivity.
  transitivity (Rec y);
  auto.
  apply cp_Rec.
  apply clos_refl_trans_1n_contains.
  apply H.
Qed.

Definition PCFRec_c t c :
 (Fib_RMod (P:=PCFEM) (t ~> t) PCFEM) c ---> 
        (Fib_RMod (P:=PCFEM) t PCFEM) c :=
Build_PO_mor (PCFRec_cs t c).

Program Instance PCFRec_s t :
RModule_Hom_struct  
  (M:=Fib_RMod (P:=PCFEM) (t ~> t) PCFEM)
  (N:=Fib_RMod (P:=PCFEM) t PCFEM)
  (PCFRec_c t).

Definition PCFRec t : PCFEM [t ~> t] ---> PCFEM [t] :=
  Build_RModule_Hom (PCFRec_s t).

Section PCFconsts.

Variable t : TY.
Variable cc : Consts t.

Program Instance PCFconsts_cs c :
PO_mor_struct (a:=PO_TERM) 
     (b:=ipo_proj (PCFE c) t) (fun _ => Const _ cc).
Next Obligation.
Proof.
  unfold Proper;
  red.
  intros;
  reflexivity.
Qed.

Definition PCFconsts_c c :
 (RMOD_Term PCFEM PO_Terminal) c ---> 
    (Fib_RMod (P:=PCFEM) t PCFEM) c :=
Build_PO_mor (PCFconsts_cs c).


Program Instance PCFconsts_s:
RModule_Hom_struct 
 (M:=RMOD_Term PCFEM PO_Terminal) 
 (N:=Fib_RMod (P:=PCFEM) t PCFEM) (PCFconsts_c).

Definition PCFconsts : Term ---> PCFEM [t] := 
 Build_RModule_Hom PCFconsts_s.

End PCFconsts.

Program Instance PCFbottom_cs t c :
PO_mor_struct (a:=PO_TERM) 
       (b:=ipo_proj (PCFE c) t)
       (fun _ => Bottom _ t).
Next Obligation.
Proof.
  unfold Proper;
  red.
  reflexivity.
Qed.

Definition PCFbottom_c t c :
  (RMOD_Term PCFEM PO_Terminal) c ---> 
  (Fib_RMod (P:=PCFEM) t PCFEM) c :=
  Build_PO_mor (PCFbottom_cs t c).

Program Instance PCFbottom_s t :
RModule_Hom_struct 
  (M:=RMOD_Term PCFEM PO_Terminal) 
  (N:=Fib_RMod (P:=PCFEM) t PCFEM)
  (PCFbottom_c t).

Definition PCFbottom t : Term ---> PCFEM [t] :=
 Build_RModule_Hom (PCFbottom_s t).

End close_notation.
