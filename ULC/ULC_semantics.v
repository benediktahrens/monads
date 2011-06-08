Require Import Coq.Relations.Relations.

Require Export CatSem.CAT.cat_TYPE_option.
Require Export CatSem.CAT.orders_bis.
Require Export CatSem.ULC.ULC_syntax.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Automatic Introduction.

Section Relations_on_ULC.

Reserved Notation "x :> y" (at level 70).

Variable rel : forall (V:TT), relation (ULC V).

Inductive ULCpropag (V: TT) 
       : relation (ULC V) :=
| relorig : forall (v v': ULC V), rel v v' ->  v :> v'
| relApp1: forall (M M' N : ULC V), 
       M :> M' -> App M N :> App M' N
| relApp2: forall M (N N' : ULC V),
      N :> N' -> App M N :> App M N'
| relAbs: forall (M M':ULC V*),
      M :> M' -> Abs M :> Abs M'

where "y :> z" := (@ULCpropag _ y z). 

Notation "y :>> z" := 
  (clos_refl_trans_1n _ (@ULCpropag _ ) y z) (at level 50).


Variable V : TT.


(** these are some trivial lemmata  which will be used later *)

Lemma cp_App1 (M M' N : ULC V) :
    M :>> M' -> App M N :>> App M' N.
Proof. 
  intros. generalize N. 
  induction H. constructor.
  intros. constructor 2 with (App y N0); auto.
  constructor 2. auto.
Qed.

Lemma cp_App2 (M N N' : ULC V) :
    N :>> N' -> App M N :>> App M N'.
Proof. 
  intros. generalize M. 
  induction H. constructor.
  intros. constructor 2 with (App M0 y); auto.
  constructor 3. auto.
Qed.

Lemma cp_Abs (M M': ULC V*):
      M :>> M' -> Abs M :>> Abs M'.
Proof. 
  intros. induction H. constructor.
  constructor 2 with (Abs y); auto.
  constructor 4. auto.
Qed.


End Relations_on_ULC.

(** Beta reduction *)
(*
Reserved Notation "a >> b" (at level 70).
*)

Inductive beta (V : TT): relation (ULC V) :=
| app_abs : forall (M: ULC V*) N, 
               beta (App (Abs M) N) (M [*:= N]).

Definition beta_star := ULCpropag beta.

Definition beta_rel := 
   fun (V : TT) => clos_refl_trans_1n _ (@beta_star V).

Notation "a >>> b" := (beta_rel a b) (at level 70).

(** lemmata *)

Lemma beta_eq : forall V (M N : ULC V),
   M = N -> M >>> N.
Proof.
  intros.
  destruct H.
  reflexivity.
Qed.

Lemma beta_trans : forall V (M N K : ULC V),
 M >>> K -> N >>> M -> N >>> K.
Proof.
  intros.
  transitivity M;
  auto.
Qed.

Lemma beta_beta : forall V M (N : ULC V), 
   App (Abs M) N >>> M [*:= N].
Proof.
  intros.
  apply clos_refl_trans_1n_contains.
  apply relorig.
  constructor.
Qed.

Lemma app_abs_red V (M : ULC _ ) (N M' : ULC V) :
   M [*:= N ] >>> M' -> App (Abs M) N >>> M'.
Proof.
  intros.
  apply (beta_trans H).
  apply beta_beta.
Qed.

Lemma App1_app_abs V  (M : ULC V*) 
       (N : ULC V) (L : ULC _ ) K:
  beta_rel (App (M [*:= N]) L) K -> 
  beta_rel (App (App (Abs M) N) L) K.
Proof.
  intros.
  transitivity (App (M[*:=N]) L).
  apply cp_App1.
  apply clos_refl_trans_1n_contains.
  apply relorig.
  constructor.
  auto.
Qed.

Lemma App2_app_abs V (M : ULC V*) 
      M' (N : ULC V) K:
  beta_rel (App M' (M [*:= N])) K -> 
  beta_rel (App M' (App (Abs M) N)) K.
Proof.
  intros.
  transitivity (App M' (M[*:=N])).
  apply cp_App2.
  apply beta_beta.
  auto.
Qed.

Lemma App1_App1_app_abs V  
     (M : ULC V*)  
     (N : ULC _) 
     (K : ULC V) 
     (L : ULC V) (R : ULC V):
  beta_rel (App (App (M[*:=N]) K) L) R ->
  beta_rel (App (App (App (Abs M) N) K) L) R.
Proof.
  simpl; intros.
  transitivity (App (App (M [*:=N]) K) L).
  apply cp_App1.
  apply cp_App1.
  apply beta_beta.
  auto.
Qed.

Lemma App1_App1_App1_app_abs V 
       (M : ULC V*) 
       (N : ULC V)
       (K : ULC V) 
       (L : ULC V)  
       (J : ULC V) (R : ULC V):
  beta_rel (App (App (App (M[*:=N]) K) L) J) R ->
  beta_rel (App (App (App (App (Abs M) N) K) L) J) R.
Proof.
  simpl; intros.
  apply (beta_trans H).
  do 3 apply cp_App1.
  apply beta_beta.
Qed.

Lemma Abs_Abs_App1_App1_Abs_app_abs V 
        (M : ULC V* * * * ) 
        (N : ULC _ ) 
        (K : ULC _ )
        (L : ULC _ ) (R : ULC V):
beta_rel (Abs (Abs 
      (App (App (Abs (M[*:=N])) K) L))) R ->
beta_rel (Abs (Abs (App (App (Abs (App (Abs M) N)) K) L))) R.
Proof.
  intros.
  apply (beta_trans H).
  repeat apply cp_Abs.
  repeat apply cp_App1.
  apply cp_Abs.
  apply beta_beta.
Qed. 

Lemma Abs_Abs_App1_App1_app_abs V
         (M : ULC V * * * ) 
         (N : ULC _)
         (K : ULC _)
         (L : ULC _) (R : ULC V):
beta_rel (Abs (Abs (App (App (M[*:=N]) K) L))) R ->
beta_rel (Abs (Abs (App (App (App (Abs M) N) K) L))) R.
Proof.
  intros.
  apply (beta_trans H).
  repeat apply cp_Abs.
  repeat apply cp_App1.
  apply beta_beta.
Qed. 

Lemma Abs_Abs_App1_app_abs V
       (M : ULC V * * * ) 
       N (K : ULC _) (R : ULC V) : 
beta_rel (Abs (Abs (App (M[*:=N]) K))) R ->
beta_rel (Abs (Abs (App (App (Abs M) N) K))) R.
Proof.
  intros.
  apply (beta_trans H).
  do 2 apply cp_Abs.
  apply cp_App1.
  apply beta_beta.
Qed.

Lemma Abs_Abs_app_abs V
       (M : ULC V * * * ) 
       N (R : ULC V) :
beta_rel (Abs (Abs (M[*:=N]))) R -> 
beta_rel (Abs (Abs (App (Abs M) N))) R.
Proof.
  intros.
  apply (beta_trans H).
  do 2 apply cp_Abs.
  apply beta_beta.
Qed.

Lemma App2_App1_app_abs V 
    (M : ULC V* ) N K 
    (L : ULC V)  (R:ULC V) :
  App K (App (M [*:=N]) L) >>> R ->
  App K (App (App (Abs M) N) L) >>> R.
Proof.
  intros.
  apply (beta_trans H).
  apply cp_App2.
  apply cp_App1.
  apply beta_beta.
Qed.

Lemma Abs_Abs_App1_Abs_App2_App1_app_abs V
     (M : ULC V * * * * )
     N (K : ULC _) (L : ULC _) (J : ULC _) 
       (R:ULC V):
   Abs (Abs (App (Abs (App K 
             (App (M[*:=N]) J))) L)) >>> R ->
   Abs (Abs (App (Abs (App K 
     (App (App (Abs M) N) J))) L)) >>> R.
Proof.
  intros.
  apply (beta_trans H).
  do 2 apply cp_Abs.
  apply cp_App1.
  apply cp_Abs.
  apply cp_App2.
  apply cp_App1.
  apply beta_beta.
Qed.

Lemma Abs_Abs_App1_Abs_App2_app_abs V 
   (M : ULC V * * * * ) 
   N (K : ULC _) (L : ULC _) 
       (R:ULC V):
   Abs (Abs (App (Abs (App K 
             (M[*:=N]) )) L)) >>> R ->
   Abs (Abs (App (Abs (App K 
      (App (Abs M) N) )) L)) >>> R.
Proof.
  intros.
  apply (beta_trans H).
  do 2 apply cp_Abs.
  apply cp_App1.
  apply cp_Abs.
  apply cp_App2.
  apply beta_beta.
Qed.

Lemma Abs_Abs_App2_app_abs V 
      (M : ULC V * * * ) 
      N K (R:ULC V ) :
  Abs (Abs (App K (M[*:=N]))) >>> R ->
  Abs (Abs (App K (App (Abs M) N))) >>> R.
Proof.
  intros.
  apply (beta_trans H).
  do 2 apply cp_Abs.
  apply cp_App2.
  apply beta_beta.
Qed.

Lemma App2_Abs_Abs_App2_App1_app_abs V 
     (M : ULC V * * * ) 
     N K L (J : ULC _) (R:ULC V) :
   App K (Abs (Abs (App L (App (M[*:=N]) J)))) >>> R ->
   App K (Abs (Abs (App L (App (App (Abs M) N) J)))) >>> R.
Proof.
  intros.
  apply (beta_trans H).
  apply cp_App2.
  do 2 apply cp_Abs.
  apply cp_App2.
  apply cp_App1.
  apply beta_beta.
Qed.

Lemma Abs_Abs_App1_App1_App1_app_abs V
   (M : ULC V * * * ) 
   N (K : ULC _ ) (L : ULC _ ) (J : ULC _ ) (R:ULC V) :
  Abs (Abs (App (App (App (M [*:=N]) K) L) J)) >>> R ->
  Abs (Abs (App (App (App (App (Abs M) N) K) L) J)) >>> R .
Proof.
  intros.
  apply (beta_trans H).
  do 2 apply cp_Abs.
  do 3 apply cp_App1.
  apply beta_beta.
Qed.

Lemma Abs_Abs_App2_App1_App1_app_abs V 
    (M : ULC V * * * )  
    (N : ULC _) (K : ULC _) 
    (L : ULC _) (J : ULC _) (R:ULC V):
   Abs (Abs (App K (App (App (M[*:=N]) L) J))) >>> R -> 
   Abs (Abs (App K (App (App (App (Abs M) N) L) J))) >>> R.
Proof.
  intros.
  apply (beta_trans H).
  do 2 apply cp_Abs.
  apply cp_App2.
  do 2 apply cp_App1.
  apply beta_beta.
Qed.

Lemma Abs_Abs_App2_App1_app_abs V
    (M : ULC V * * * ) 
    N (K : ULC _) (L : ULC _) (R:ULC V):
  Abs (Abs (App K (App (M[*:=N]) L))) >>> R ->
  Abs (Abs (App K (App (App (Abs M) N) L))) >>> R.
Proof.
  intros.
  apply (beta_trans H).
  do 2 apply cp_Abs.
  apply cp_App2.
  apply cp_App1.
  apply beta_beta.
Qed.

Lemma Abs_App2_app_abs V 
     (M : ULC V * * ) 
     N K (R : ULC V) :
   Abs (App K (M[*:=N])) >>> R -> 
   Abs (App K (App (Abs M) N)) >>> R.
Proof.
  intros.
  apply (beta_trans H).
  apply cp_Abs.
  apply cp_App2.
  apply beta_beta.
Qed.

Lemma App1_Abs_app_abs V 
   (M : ULC V * * ) 
   N (K : ULC _) (R:ULC V) :
  App (Abs (M[*:=N])) K >>> R ->
  App (Abs (App (Abs M) N)) K >>> R.
Proof.
  intros.
  apply (beta_trans H).
  apply cp_App1.
  apply cp_Abs.
  apply beta_beta.
Qed.

Lemma App1_Abs_App2_App1_app_abs V 
   (M : ULC V * * ) 
   N (K : ULC _) (L : ULC _) 
   (J : ULC _) (R:ULC V) :
  App (Abs (App K (App (M[*:=N]) L))) J >>> R -> 
  App (Abs (App K (App (App (Abs M) N) L))) J >>> R.
Proof.
  intros.
  apply (beta_trans H).
  apply cp_App1.
  apply cp_Abs.
  apply cp_App2.
  apply cp_App1.
  apply beta_beta.
Qed.


Lemma App1_Abs_Abs_App2_App1_app_abs V 
   (M : ULC V * * * ) 
    N (K : ULC _) (L:ULC _) (J : ULC _) (R:ULC V) :
  App (Abs (Abs (App K (App (M[*:=N]) L)))) J >>> R -> 
  App (Abs (Abs (App K (App (App (Abs M) N) L)))) J >>> R.
Proof.
  intros.
  apply (beta_trans H).
  apply cp_App1.
  do 2 apply cp_Abs.
  apply cp_App2.
  apply cp_App1.
  apply beta_beta.
Qed.

Lemma App1_App1_Abs_app_abs V
   (M : ULC V * * )  
    N (K : ULC _) (L : ULC _) (R:ULC V) :
  App (App (Abs (M[*:=N])) K) L >>> R -> 
  App (App (Abs (App (Abs M)N)) K) L >>> R.
Proof.
  intros.
  apply (beta_trans H).
  do 2 apply cp_App1.
  apply cp_Abs.
  apply beta_beta.
Qed.

Lemma App1_App1_Abs_Abs_app_abs V
    (M : ULC V * * * ) 
     N (K : ULC _) (L : ULC _) (R:ULC V) :
  App (App (Abs (Abs (M[*:=N]))) K) L >>> R -> 
  App (App (Abs (Abs (App (Abs M)N))) K) L >>> R.
Proof.
  intros.
  apply (beta_trans H).
  do 2 apply cp_App1.
  do 2 apply cp_Abs.
  apply beta_beta.
Qed.

Lemma App1_App1_Abs_Abs_App1_app_abs V M N K L J (R : ULC V):
    App (App (Abs (Abs (App (M[*:=N]) K))) L) J >>> R ->
    App (App (Abs (Abs (App (App (Abs M) N) K))) L) J >>> R.
Proof.
  intros.
  apply (beta_trans H).
  do 2 apply cp_App1.
  do 2 apply cp_Abs.
  apply cp_App1.
  apply beta_beta.
Qed.


Obligation Tactic := idtac.

Program Instance ULCBETA_struct (V : TT) : 
  PO_obj_struct (ULC V) := {
 Rel := @beta_rel V 
}.

Definition ULCBETA (V: TT) : PO :=
    Build_PO_obj (ULCBETA_struct V ).

Program Instance Var_s (V : TT) : 
    PO_mor_struct (a:=sm_po V) (b:=ULCBETA V) (Var (V:=V)).
Next Obligation.
Proof.
  intros V.
  unfold Proper;
  red.
  simpl.
  intros y z H.
  induction H.
  reflexivity.
Qed.

Definition VAR V := Build_PO_mor (Var_s V).

Lemma rename_beta (V W : TT)(f : V ---> W) (v w : ULC V):
     v >>> w -> v //- f >>> w //- f.
Proof.
  intros V W f v w H.
  generalize dependent W.
  induction H.
  reflexivity.
  intros W f.
  transitivity (y //- f);
  auto.
  clear dependent z.
  generalize dependent W.
  induction H.
  induction H.

  simpl.
  intros W f.
  apply app_abs_red.
  simpl.
  unfold substar.
  rewrite  rename_subst.
  simpl.
  rewrite subst_rename.
  simpl.
  apply beta_eq.
  apply (subst_eq M).
  intros y;
  destruct y as [y| ];
  simpl; 
  auto.
  
  intros W f. 
  simpl.
  apply cp_App1.
  apply IHULCpropag.
  intros W f.
  simpl.
  apply cp_App2.
  apply IHULCpropag.
  simpl.
  intros W f.
  apply cp_Abs.
  apply IHULCpropag.
Qed.
  
Program Instance subst_s (V W : TT) 
     (f : sm_po V ---> ULCBETA W) :
   PO_mor_struct 
     (a:=ULCBETA V) (b:=ULCBETA W) (_subst f).
Next Obligation.
Proof.
  intros V W f.
  unfold Proper;
  red.
  intros y z H.
  generalize dependent W.
  induction H;
  simpl;
  intros. 
  constructor.
  transitivity (_subst f y);
  try apply IHclos_refl_trans_1n.
  clear dependent z.

    generalize dependent W.
  induction H;
  simpl;
  intros.
  
  Focus 2.
  apply cp_App1.
  apply IHULCpropag.
  Focus 2.
  apply cp_App2.
  apply IHULCpropag.
  Focus 2.
  apply cp_Abs.
  simpl in *.
  apply (IHULCpropag _ (Sm_ind 
            (V:=V*) (W:=ULCBETA W*) 
      (fun y => _shift f y))).

  generalize dependent W.
    induction H;
    simpl;
    intros.
    apply clos_refl_trans_1n_contains.
    apply relorig.
    assert (H:=app_abs (_subst (_shift f) M) (_subst f N)).
    rewrite subst_substar.
    auto.
Qed.
 
Lemma subst_beta (V W : TT) (f : V ---> ULC W) 
    (v w : ULC V) :
   v >>> w -> v >>= f >>> w >>= f.
Proof.
  intros.
  assert (H':= subst_s _ _ (Sm_ind (W:= ULCBETA W) f)).
  apply H'.
  simpl.
  auto.
Qed.

Definition SUBST V W f := Build_PO_mor (subst_s V W f).

