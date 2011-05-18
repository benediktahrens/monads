Require Import Coq.Relations.Relations.

Require Export CatSem.CAT.ind_potype.
Require Export CatSem.TLC.TLC_syntax.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.


Section Relations_on_TLC.

Reserved Notation "x :> y" (at level 70).

Variable rel : forall (V:IT) t, relation (TLC V t).

Inductive propag (V: IT) 
       : forall t, relation (TLC V t) :=
| relorig : forall t (v v': TLC V t), rel v v' ->  v :> v'
| relApp1: forall (s t : TY)(M M' : TLC V (s ~> t)) N, 
       M :> M' -> app M N :> app M' N
| relApp2: forall (s t:TY)(M:TLC V (s ~> t)) N N',
      N :> N' -> app M N :> app M N'
| relLam: forall (s t:TY)(M M':TLC (opt s V) t),
      M :> M' -> abs M :> abs M'

where "x :> y" := (@propag _ _ x y). 

Notation "x :>> y" := 
  (clos_refl_trans_1n _ (@propag _ _ ) x y) (at level 50).

Variable V: IT.
Variables s t: TY.

(** these are some trivial lemmata  which will be used later *)

Hint Resolve clos_refl_trans_1n_contains : fin.

Lemma cp_App1 (M M': TLC V (s ~> t)) :
    M :>> M' -> forall N, app M N :>> app M' N.
Proof.
  induction 1;
  simpl; intros;
  try constructor;
  match goal with 
    [H : ?y :>> ?z|- app ?x ?N :>> app ?z ?N ] =>
      constructor 2 with (app y N) end;
  fin;
  constructor 2;
  auto.
Qed.
 
Lemma cp_App2 (M: TLC V (s ~> t)) N N':
    N :>> N' -> app M N :>> app M N'.
Proof. 
  induction 1;
  simpl; intros;
  try constructor;
  match goal with 
    [H : ?y :>> ?z|- app ?N ?x :>> app ?N ?z ] =>
      constructor 2 with (app N y) end;
  fin;
  constructor 3;
  fin.
Qed.

Lemma cp_Lam (M M': TLC (opt s V) t ):
      M :>> M' -> abs M :>> abs M'.
Proof. 
  induction 1;
  simpl; intros;
  try constructor;
  match goal with 
    [H : ?y :>> ?z|- abs ?x :>> abs ?z ] =>
      constructor 2 with (abs y) end;
  fin;
  constructor 4;
  fin.
Qed.

End Relations_on_TLC.

Hint Resolve cp_Lam cp_App1 cp_App2 : fin.

(** Beta reduction *)

Inductive beta1 (V : IT): forall t, relation (TLC V t) :=
| app_abs : forall (s t:TY) (M: TLC (opt s V) t) N, 
          beta1 (app (abs M) N) (M [*:= N]).

Definition beta_star := propag beta1.

Definition beta := 
   fun (V : IT) t => clos_refl_trans_1n _ (@beta_star V t).

Notation "a >> b" := (beta a b) (at level 60, no associativity).

Lemma beta_beta V (s t:TY) (M: TLC (opt s V) t) N : 
         app (abs M) N >> (M [*:= N]).
Proof.
  intros; 
  apply clos_refl_trans_1n_contains;
  apply relorig;
  constructor.
Qed.

Lemma beta_eq V t (y z : TLC V t) : 
      y = z -> y >> z.
Proof.
  intros; subst;
  reflexivity.
Qed.

Hint Resolve beta_eq beta_beta : fin.

Lemma beta1_rename V t (x y: TLC V t)
   (H : beta1 x y) W (f : V ---> W) :
    x //- f >> y //- f.
Proof.
  induction 1;
  simpl; intros;
  match goal with[|- _ >> ?M [*:= ?N] //- ?f] => 
     transitivity ((M//- ^f) [*:=N //- f]) end;
  try apply beta_beta;
  unfold _substar;
  fin;
  apply beta_eq;
  apply subst_eq;
  opt.
Qed.

Hint Resolve beta1_rename : fin.

Ltac sub_beta := match goal with
     [|- app ?M _ >> app ?M _ ] => apply cp_App2 
   | [|- app _ ?N >> app _ ?N ] => apply cp_App1
   | [|- abs _ >> abs _ ] => apply cp_Lam end.

Ltac spec := match goal with 
     [H:forall _ _ , _ >> _ |- _] => apply H end.

Lemma beta_star_rename V t (x y: TLC V t)
   (H : beta_star x y) W (f : V ---> W) :
   x //- f >> y //- f.
Proof.
  induction 1;
  simpl; intros;
  fin; try (sub_beta; spec).
Qed.
 
Hint Resolve beta_star_rename : fin.

Lemma beta_rename V t (y z : TLC V t) (H : beta y z)
          W (f : V ---> W) :
            y //- f >> z //- f.
Proof.
  induction 1;
  fin;
  match goal with 
      [H:forall _ _ , ?y //- _ >> ?z //- _ |- _ >> ?z//-?g] =>
        transitivity (y //- g) end;
  fin.
Qed.

Lemma beta1_subst V t (x y: TLC V t)
   (H : beta1 x y) W (f : V ---> TLC W) :
         x >>= f >> y >>= f.
Proof.
  induction 1;
  simpl; intros;
  match goal with[|- _ >> ?M [*:= ?N] >>= ?f] => 
     transitivity ((M >>= _shift f) [*:=N >>= f]) end;
  try apply beta_beta;
  unfold _substar;
  try apply beta_beta;
  try apply beta_eq;
  fin;
  try apply subst_eq;
  fin; opt;
  unfold _inj; fin.
Qed.

Hint Resolve beta1_subst : fin.

Lemma beta_star_subst V t (x y: TLC V t)
   (H : beta_star x y) W (f : V ---> TLC W) :
   x >>= f >> y >>= f.
Proof.
  induction 1;
  simpl; intros;
  fin;
  sub_beta; spec.
Qed.

Hint Resolve beta_star_subst : fin.

Lemma beta_subst V t (y z : TLC V t) (H : beta y z)
          W (f : V ---> TLC W) :
        y >>= f >> z >>= f.
Proof.
  induction 1;
  fin;
  match goal with 
      [H:forall _ _ , ?y >>= _ >> ?z >>= _ |- _ >> ?z >>= ?g] =>
        transitivity (y >>= g) end;
  fin.
Qed.

Hint Resolve beta_subst : fin.

Obligation Tactic := unfold beta; simpl; 
           intros; auto using Clos_RT_1n_prf.

Program Instance BETA_struct (V : IT) : ipo_obj_struct (TLC V) := {
 IRel t := @beta V t}.

Program Definition BETA (V: IT) : IPO TY :=
    Build_ipo_obj (BETA_struct V ).

Obligation Tactic := fin; try unf_Proper; intros;
                        apply beta_subst; auto.

Program Instance subst_s (V W : IT) (f : SM_ipo _ V ---> BETA W) :
   ipo_mor_struct (a:=BETA V)(b:=BETA W)
         (fun t y => _subst f y).

Definition subst V W f := Build_ipo_mor (subst_s V W f).

Obligation Tactic := unfold Proper; red; fin.

Program Instance subst__oid : forall a b : IT, 
 Proper (equiv ==> equiv) (subst (V:=a) (W:=b)).


