Require Export CatSem.PCF.PCF_syntax.
Require Export CatSem.CAT.monad_haskell.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Obligation Tactic := fin.

Program Instance PCFm : 
     Monad_struct (C:=IT) PCF := {
  weta := Var;
  kleisli := subst
}.

Canonical Structure PCFM := Build_Monad PCFm.

Lemma rename_lift V t (v : PCF V t) W (f : V ---> W) : 
       v //- f = lift (M:=PCFM) f _ v.
Proof.
  unfold lift;
  simpl.
  intros.
  rewrite <- subst_rename.
  rewrite subst_var.
  auto.
Qed.


Lemma shift_shift a V W (f : V ---> PCF W) t (y : opt a V t) :
        y >>- f = shift f y. 
Proof.
  intros a V W f t y.
  destruct y;
  simpl;
  auto.
  unfold lift, inj.
  simpl.
  rewrite <- subst_rename.
  rewrite subst_var.
  auto.
Qed.

Hint Resolve shift_shift rename_lift : fin.
Hint Rewrite shift_shift rename_lift : fin.

Notation "'IT'" := (ITYPE TY).
Notation "a '~>' b" := (PCF.arrow a b) 
     (at level 69, right associativity).
Notation "a 'x' b" := (product a b) (at level 30).
Notation "P [ z ]" := (ITFIB_MOD _ z P) (at level 35).
Notation "'d' P // s" := (ITDER_MOD _ _ s P) (at level 25).
Notation "f 'X' g" := (product_mor _ f g)(at level 30).

Program Instance app_hom_s r s : 
Module_Hom_struct
  (S:=Prod_Mod (P:=PCFM) TYPE_prod (ITFibre_Mod (P:=PCFM) PCFM (r ~> s))
     (ITFibre_Mod (P:=PCFM) PCFM r)) 
  (T:=ITFibre_Mod (P:=PCFM) PCFM s)
  (fun V y => App (fst y) (snd y)).


Canonical Structure PCFapp r s := Build_Module_Hom
    (app_hom_s r s).

Obligation Tactic := fin.

Program Instance abs_hom_s r s : 
Module_Hom_struct
  (S:=ITFibre_Mod (P:=PCFM) (IT_Der_Mod (P:=PCFM) 
      (D:=ITYPE TY) PCFM r) s)
  (T:=ITFibre_Mod (P:=PCFM) PCFM (r ~> s))
  (fun V y => Lam y).

Canonical Structure PCFabs r s := Build_Module_Hom (abs_hom_s r s).

Program Instance rec_hom_s t : Module_Hom_struct
  (S:= PCFM [t ~> t]) (T:= PCFM [t])
  (fun V y => Rec y).

Canonical Structure PCFrec t := Build_Module_Hom (rec_hom_s t).

Program Instance ttt_hom_s : Module_Hom_struct 
  (S:=Term (C:=MOD PCFM TYPE)) (T:= PCFM [Bool])
  (fun V t => Const V ttt).

Canonical Structure PCFttt := Build_Module_Hom ttt_hom_s.

Program Instance fff_hom_s : Module_Hom_struct 
  (S:=Term (C:=MOD PCFM TYPE)) (T:= PCFM [Bool])
  (fun V t => Const V fff).

Canonical Structure PCFfff := Build_Module_Hom fff_hom_s.

Program Instance succ_hom_s : Module_Hom_struct 
  (S:=Term (C:=MOD PCFM TYPE)) (T:= PCFM [Nat ~> Nat])
  (fun V t => Const V succ).

Canonical Structure PCFsucc := Build_Module_Hom succ_hom_s.

Program Instance pred_hom_s : Module_Hom_struct 
  (S:=Term (C:=MOD PCFM TYPE)) (T:= PCFM [Nat ~> Nat])
  (fun V t => Const V preds).

Canonical Structure PCFpred := Build_Module_Hom pred_hom_s.

Program Instance zero_hom_s : Module_Hom_struct 
  (S:=Term (C:=MOD PCFM TYPE)) (T:= PCFM [Nat ~> Bool])
  (fun V t => Const V zero).

Canonical Structure PCFzero := Build_Module_Hom zero_hom_s.

Program Instance condN_hom_s : Module_Hom_struct 
  (S:=Term (C:=MOD PCFM TYPE)) (T:= PCFM [ _ ])
  (fun V t => Const V condN).

Canonical Structure PCFcondN := Build_Module_Hom condN_hom_s.

Program Instance condB_hom_s : Module_Hom_struct 
  (S:=Term (C:=MOD PCFM TYPE)) (T:= PCFM [ _ ])
  (fun V t => Const V condB).

Canonical Structure PCFcondB := Build_Module_Hom condB_hom_s.

Program Instance nats_hom_s m : Module_Hom_struct 
  (S:=Term (C:=MOD PCFM TYPE)) (T:= PCFM [ Nat ])
  (fun V t => Const V (Nats m)).

Canonical Structure PCFNats m := Build_Module_Hom (nats_hom_s m).

Program Instance bottom_hom_s t : Module_Hom_struct 
  (S:=Term (C:=MOD PCFM TYPE)) (T:= PCFM [ t ])
  (fun V _ => Bottom V t).

Canonical Structure PCFBottom t := Build_Module_Hom (bottom_hom_s t).





