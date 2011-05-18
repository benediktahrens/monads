Require Import Coq.Relations.Relations.
Require Import Coq.Logic.Eqdep.
Require Import Coq.Program.Equality.

Require Export CatSem.PCF_order_comp.RPCF_rep.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Automatic Introduction.

Notation "^ f" := (lift (M:= opt_monad _) f) (at level 5).

Ltac fin := simpl in *; intros; 
   autorewrite with fin; auto with fin.

Hint Unfold lift : fin.
Hint Extern 1 (_ = _) => f_equal : fin.




Notation "V *" := (opt (T:=unit) _ V) (at level 5).

Definition TT := ITYPE unit.

Lemma l_eq (V W : TT) (f g : forall t, V t -> W t) r: 
   (forall t v, f t v = g t v) ->
       (forall t (v : opt r V t), 
       lift (M:=opt_monad r) f t v = ^g t v).
Proof.
  intros.
  destruct v;
  unfold lift;
  simpl;
  auto. 
  rewrite H.
  auto.
Qed.
   

Section ULC_syntax.

Inductive ULC (V : TT) : TT :=
  | Var : forall t, V t -> ULC V t
  | Abs : forall t : unit, ULC (opt t V) t -> ULC V t
  | App : forall t, ULC V t -> ULC V t -> ULC V t.

Lemma App_eq V t (M M' N N' : ULC V t) :
  M = M' -> N = N' -> App M N = App M' N'.
Proof.
  intros.
  rewrite H.
  rewrite H0.
  auto.
Qed.

Fixpoint rename V W (f : V ---> W) t (y : ULC V t) : 
          ULC W t :=
  match y with
  | Var _ v => Var (f _ v)
  | Abs _ v => Abs (rename ^f v)
  | App _  s t => App (rename f s) (rename f t)
  end.

Definition inj u V := rename (V:=V) (W:= opt u V) 
                (@some unit u V).

Definition _shift (u : unit) (V W : TT) (f : V ---> ULC W) : 
         V*  ---> ULC (W*) :=
   fun t v => 
   match v in (opt _ _ y) return (ULC (W *) y) with
   | some t0 p => inj u (f t0 p)
   | none => Var (none u W)
   end.

Fixpoint _subst V W (f : V ---> ULC W) t (y : ULC V t) : 
         ULC W t :=
  match y with
  | Var _ v => f _ v
  | Abs _ v => Abs (_subst (_shift f) v)
  | App _ s t => App (_subst f s) (_subst f t)
  end.

Definition substar (u : unit) (V : TT) (M : ULC V u) :
           ULC (opt u V) ---> ULC V :=
 _subst (fun t (y : opt u V t) => match y with
         | none => M
         | some _ v => Var v
         end).

Notation "M [*:= N ]" := (substar N M) (at level 50).

(** Notations for functions *)
Notation "y //- f" := (rename f y)
  (at level 42, left associativity).
Notation "y >- f" := (_shift f y) (at level 40).
Notation "y >>= f" := (_subst f y) 
  (at level 42, left associativity).

Lemma rename_eq : forall (V : TT) (t : unit) (v : ULC V t) 
         (W : TT) (f g : V ---> W),
     (forall t y, f t y = g t y) -> v //- f = v //- g.
Proof.
  intros V t v.
  induction v;
  intros;
  simpl.
  rewrite H;
  auto.
  
  apply f_equal.
  apply IHv.
  simpl in *.
  intros.
  destruct t.
  destruct t0.
  assert (H':= l_eq (r:=tt) H (t:=tt) y).
  simpl in *.
  rewrite <- H'.
  auto.

  rewrite (IHv1 _ _ _ H).
  rewrite (IHv2 _ _ _ H).
  auto.
Qed.

Hint Resolve rename_eq l_eq : fin.
Hint Rewrite rename_eq l_eq : fin.


Lemma rename_comp V t (y : ULC V t) W 
         (f : V ---> W) Z (g : W ---> Z):
 y //- (fun s y => g s (f s y)) =  y //- f //- g.
Proof.
  intros V t y.
  induction y;
  simpl; 
  intros;
  fin.

  apply f_equal.
  rewrite <- IHy.
  apply rename_eq.
  intros r y0.
  destruct y0; 
  fin.
Qed.

Lemma rename_id_eq V t (y : ULC V t) (f : V ---> V)
        (H : forall t v, f t v = v) : 
    y //- f = y.
Proof.
  intros V t y.
  induction y;
  simpl; 
  intros;
  fin.
  apply f_equal.
  apply IHy.
  intros r v;
  destruct v;
  fin. unfold lift. 
  fin.
Qed.

Lemma rename_id V t (y : ULC V t) : y //- id _ = y .
Proof.
  intros V t y.
  apply rename_id_eq.
  fin.
Qed.

Lemma _shift_eq u V W (f g : V ---> ULC W) 
     (H : forall t v, f t v = g t v) t (y : opt u V t) : 
          y >- f = y >- g.
Proof.
  intros u V W f g H t v.
  destruct v;
  fin. 
Qed.

Hint Resolve  rename_id _shift_eq : fin.
Hint Rewrite  rename_id _shift_eq : fin.

Lemma shift_var u (V : TT) t (y : opt u V t) :
       y >- @Var _ = Var y.
Proof.
  intros u V t y;
  induction y;
  fin.
Qed.

Hint Resolve shift_var : fin.
Hint Rewrite shift_var : fin.

 
Lemma var_lift_shift (u : unit) V W 
    (f : V ---> W) t (y : opt u V t) :
     Var (^f _ y) = y >- (f ;; @Var _ ).
Proof.
  intros u V W f t y;
  induction y; fin.
Qed.

Hint Resolve var_lift_shift : fin.


Lemma shift_lift u V W Z (f : V ---> W) 
         (g : W ---> ULC Z) t (y : opt u V t) :
      (^f _ y) >- g = y >- (f ;; g).
Proof.
  intros u V W Z f g t y.
  induction y; fin.
Qed.

Hint Resolve shift_lift : fin.
Hint Rewrite shift_lift : fin.

Lemma subst_eq V t (y : ULC V t) 
      W (f g : V ---> ULC W) 
       (H : forall t y, f t y = g t y):  
      y >>= f = y >>= g.
Proof.
  intros V t y.
  induction y;
  fin.
Qed.

Hint Resolve subst_eq : fin.
Hint Rewrite subst_eq : fin.

Obligation Tactic := unfold Proper; red; fin.

Program Instance subst_oid V W : 
 Proper (equiv ==> equiv (Setoid:=mor_oid (ULC V) (ULC W))) 
                (@_subst V W).

Lemma subst_var (V : TT) : 
    forall t (v : ULC V t), v >>= (@Var V) = v .
Proof.
  intros V t y.
  induction y;
  fin.
  apply f_equal.
  rewrite <- IHy at 2.
  apply subst_eq.
  fin.
Qed.
  

Lemma subst_eq_rename V t (v : ULC V t) W 
            (f : V ---> W)  : 
     v //- f  = v >>= (f ;; Var (V:=W)).
Proof.
  intros V t y.
  induction y;
  fin.
  apply f_equal.
  rewrite IHy.
  apply subst_eq.
  intros tr z;
  destruct z;
  fin.
Qed.

Lemma rename_shift a V W Z (f : V ---> ULC W) 
           (g : W ---> Z) t 
       (y : opt a V t) : 
    (y >- f) //- ^g = y >- (f ;; rename g).
Proof.
  intros a V W Z f g t y.
  induction y;
  fin.  
  unfold inj.
  rewrite <- rename_comp.
  rewrite <- rename_comp.
  fin.
Qed.


Hint Rewrite rename_shift : fin.
Hint Resolve rename_shift : fin.

Hint Unfold inj : fin.

Lemma rename_subst V t (v : ULC V t) W Z (f : V ---> ULC W)
      (g : W ---> Z) : 
      (v >>= f) //- g  = v >>= (f ;; rename g).
Proof.
  intros V t y.
  induction y;
  fin.
  rewrite IHy.
  apply f_equal.
  apply subst_eq.
  intros tr z;
  destruct z;
  simpl; auto.
  unfold inj.
  rewrite <- rename_comp.
  rewrite <- rename_comp.
  apply rename_eq.
  fin.
Qed.

Lemma subst_rename V t (v : ULC V t) W Z (f : V ---> W)
      (g : W ---> ULC Z) : 
      v //- f >>= g = v >>= (f ;; g).
Proof.
  intros V t y.
  induction y;
  fin.
  apply f_equal.
  rewrite IHy.
  apply subst_eq.
  intros tr z;
  destruct z;
  fin.
Qed.


Lemma rename_substar V u t (v : ULC (opt u V) t) W 
       (f : V ---> W) N:
     v [*:= N] //- f = (v //- ^f) [*:= N //- f ].
Proof.
  intros.
  unfold substar.
  rewrite rename_subst.
  rewrite subst_rename.
  apply subst_eq.
  intros t0 z ; 
  destruct z ;  
  fin.
Qed.

Hint Rewrite subst_rename rename_subst : fin.


Hint Rewrite rename_shift : fin.
Hint Resolve rename_shift : fin.


Lemma subst_shift_shift (u:unit) V (t : unit)
      (v : opt u V t)
         W Z (f: V ---> ULC W) (g: W ---> ULC Z):
    (v >- f) >>= (_shift g)  = 
             v >- (f ;; _subst g).
Proof.
  intros u V t v.
  induction v; 
  simpl; intros; 
  try apply subst_term_inj; auto.
  unfold inj.
  rewrite subst_rename. 
  fin.
Qed.

Hint Resolve subst_shift_shift : fin.
Hint Rewrite subst_shift_shift : fin.


Lemma subst_subst V t (v : ULC V t) W Z 
             (f : V ---> ULC W) 
             (g : W ---> ULC Z) :
     v >>= f >>= g = v >>= (f;; _subst g).
Proof.
  intros V t y.
  induction y; 
  fin.
  apply f_equal.
  rewrite IHy.
  apply subst_eq.
  intros tr z;
  destruct z;
  fin.
  unfold inj. 
  fin.
Qed.


Lemma lift_rename V t (s : ULC V t) W (f : V ---> W) :
          s >>= (fun t z => Var (f t z)) = s //- f.
Proof.
  intros V t y.
  induction y;
  fin.
  apply f_equal.
  rewrite <- IHy.
  apply subst_eq.
  intros tr z;
  destruct z;
  fin.
Qed.

Lemma rename_rename V W Z (f : V ---> W) 
        (g : W ---> Z) t (v : ULC V t) :
  v //- f //- g = v //- (f ;; g).
Proof.
  intros.
  repeat rewrite <- lift_rename.
  rewrite subst_subst.
  fin.
Qed.

Lemma subst_var_eta (V:TT) t (v:ULC V t):
        v >>= (fun t z => @Var V t z) = v.
Proof. 
  induction v; intros; simpl; auto.
  rewrite <- IHv at 2.
  apply f_equal. apply subst_eq.
  intros; apply shift_var.
  rewrite IHv1. rewrite IHv2; auto.
Qed.

Lemma subst_substar (V W : TT) 
       t (M: ULC (opt t V) t) (N:ULC V t) 
      (f:forall t, V t -> ULC W t):
   M [*:=N]  >>= f = (M >>= _shift f) [*:= (N >>= f)].
Proof.
  intros V W t M N f.
  unfold substar. simpl.
  repeat rewrite subst_subst.
  apply subst_eq.
  intros t0 y.
  simpl.
  destruct y. unfold _shift.
  unfold inj. 
  simpl.
  rewrite subst_rename. simpl. 
  rewrite (subst_var_eta (f t0 v)). auto.
  simpl.
  apply subst_eq; auto.
Qed.

Hint Resolve subst_var subst_subst lift_rename : fin.
Hint Rewrite subst_subst lift_rename: fin.


Section Relations_on_ULC.

Reserved Notation "x :> y" (at level 70).

Variable rel : forall (V:TT) t, relation (ULC V t).

Inductive ULCpropag (V: TT) 
       : forall t, relation (ULC V t) :=
| relorig : forall t (v v': ULC V t), rel v v' ->  v :> v'
| relApp1: forall t (M M' : ULC V t) N, 
       M :> M' -> App M N :> App M' N
| relApp2: forall t (M:ULC V t) N N',
      N :> N' -> App M N :> App M N'
| relAbs: forall t (M M':ULC (opt t V) t),
      M :> M' -> Abs M :> Abs M'

where "y :> z" := (@ULCpropag _ _ y z). 

Notation "y :>> z" := 
  (clos_refl_trans_1n _ (@ULCpropag _ _ ) y z) (at level 50).


Variable V : TT.
Variable t : unit.

(** these are some trivial lemmata  which will be used later *)

Lemma cp_App1 (M M': ULC V t) N :
    M :>> M' -> App M N :>> App M' N.
Proof. 
  intros. generalize N. 
  induction H. constructor.
  intros. constructor 2 with (App y N0); auto.
  constructor 2. auto.
Qed.

Lemma cp_App2 (M : ULC V t) N N':
    N :>> N' -> App M N :>> App M N'.
Proof. 
  intros. generalize M. 
  induction H. constructor.
  intros. constructor 2 with (App M0 y); auto.
  constructor 3. auto.
Qed.

Lemma cp_Abs (M M': ULC (opt t V) t ):
      M :>> M' -> Abs M :>> Abs M'.
Proof. 
  intros. induction H. constructor.
  constructor 2 with (Abs y); auto.
  constructor 4. auto.
Qed.


End Relations_on_ULC.

(** Beta reduction *)



Ltac sim := unfold substar; simpl ;
            unfold inj; simpl.



Reserved Notation "a >> b" (at level 70).


Inductive beta (V : TT): forall t, relation (ULC V t) :=
| app_abs : forall t (M: ULC (opt t V) t) N, 
               beta (App (Abs M) N) (M [*:= N]).

Definition beta_star := ULCpropag beta.

Definition beta_rel := 
   fun (V : TT) t => clos_refl_trans_1n _ (@beta_star V t).

Notation "a >> b" := (beta_rel a b).

(** lemmata *)

Lemma beta_eq : forall V t (M N : ULC V t),
   M = N -> M >> N.
Proof.
  intros.
  destruct H.
  reflexivity.
Qed.

Lemma beta_trans : forall V t (M N K : ULC V t),
 M >> K -> N >> M -> N >> K.
Proof.
  intros.
  transitivity M;
  auto.
Qed.

Lemma beta_beta : forall V t M (N : ULC V t), 
   App (Abs M) N >> M [*:= N].
Proof.
  intros.
  apply clos_refl_trans_1n_contains.
  apply relorig.
  constructor.
Qed.

Lemma app_abs_red V t (M : ULC _ t) (N M' : ULC V t) :
   M [*:= N ] >> M' -> App (Abs M) N >> M'.
Proof.
  intros.
  apply (beta_trans H).
  apply beta_beta.
Qed.

Definition eta_red V t (M : ULC V t) :=
 Abs (App (inj t M) (Var (V:=V *) (none t (V) ))) >> M.

Lemma App1_app_abs V t M M' (N : ULC V t) K:
  beta_rel (App (M [*:= N]) M') K -> 
  beta_rel (App (App (Abs M) N) M') K.
Proof.
  intros.
  transitivity (App (M[*:=N]) M').
  apply cp_App1.
  apply clos_refl_trans_1n_contains.
  apply relorig.
  constructor.
  auto.
Qed.

Lemma App2_app_abs V t M M' (N : ULC V t) K:
  beta_rel (App M' (M [*:= N])) K -> 
  beta_rel (App M' (App (Abs M) N)) K.
Proof.
  intros.
  transitivity (App M' (M[*:=N])).
  apply cp_App2.
  apply beta_beta.
  auto.
Qed.

Lemma App1_App1_app_abs V t M  N K L (R : ULC V t):
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

Lemma Abs_Abs_App1_App1_Abs_app_abs V t M N K L (R : ULC V t):
beta_rel (Abs (Abs (App (App (Abs (M[*:=N])) K) L))) R ->
beta_rel (Abs (Abs (App (App (Abs (App (Abs M) N)) K) L))) R.
Proof.
  intros.
  apply (beta_trans H).
  repeat apply cp_Abs.
  repeat apply cp_App1.
  apply cp_Abs.
  apply beta_beta.
Qed. 
  
Lemma Abs_Abs_App1_App1_app_abs V t M N K L (R : ULC V t):
beta_rel (Abs (Abs (App (App ((M[*:=N])) K) L))) R ->
beta_rel (Abs (Abs (App (App ((App (Abs M) N)) K) L))) R.
Proof.
  intros.
  apply (beta_trans H).
  repeat apply cp_Abs.
  repeat apply cp_App1.
  apply beta_beta.
Qed. 

Lemma Abs_Abs_App1_app_abs V t M N K (R : ULC V t) : 
beta_rel (Abs (Abs (App (M[*:=N]) K))) R ->
beta_rel (Abs (Abs (App (App (Abs M) N) K))) R.
Proof.
  intros.
  apply (beta_trans H).
  do 2 apply cp_Abs.
  apply cp_App1.
  apply beta_beta.
Qed.

Lemma Abs_Abs_app_abs V t M N (R : ULC V t) :
beta_rel (Abs (Abs (M[*:=N]))) R -> 
beta_rel (Abs (Abs (App (Abs M) N))) R.
Proof.
  intros.
  apply (beta_trans H).
  do 2 apply cp_Abs.
  apply beta_beta.
Qed.

Lemma App2_App1_app_abs V t M N K L (R:ULC V t) :
  App K (App (M [*:=N]) L) >> R ->
  App K (App (App (Abs M) N) L) >> R.
Proof.
  intros.
  apply (beta_trans H).
  apply cp_App2.
  apply cp_App1.
  apply beta_beta.
Qed.

Lemma Abs_Abs_App1_Abs_App2_App1_app_abs V t M N K L J 
       (R:ULC V t):
   Abs (Abs (App (Abs (App K 
             (App (M[*:=N]) J))) L)) >> R ->
   Abs (Abs (App (Abs (App K 
     (App (App (Abs M) N) J))) L)) >> R.
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

Lemma Abs_Abs_App1_Abs_App2_app_abs V t M N K L 
       (R:ULC V t):
   Abs (Abs (App (Abs (App K 
             (M[*:=N]) )) L)) >> R ->
   Abs (Abs (App (Abs (App K 
      (App (Abs M) N) )) L)) >> R.
Proof.
  intros.
  apply (beta_trans H).
  do 2 apply cp_Abs.
  apply cp_App1.
  apply cp_Abs.
  apply cp_App2.
  apply beta_beta.
Qed.

Lemma Abs_Abs_App2_app_abs V t M N K (R:ULC V t) :
  Abs (Abs (App K (M[*:=N]))) >> R ->
  Abs (Abs (App K (App (Abs M) N))) >> R.
Proof.
  intros.
  apply (beta_trans H).
  do 2 apply cp_Abs.
  apply cp_App2.
  apply beta_beta.
Qed.

Lemma App2_Abs_Abs_App2_App1_app_abs V t M N K L J (R:ULC V t) :
   App K (Abs (Abs (App L (App (M[*:=N]) J)))) >> R ->
   App K (Abs (Abs (App L (App (App (Abs M) N) J)))) >> R.
Proof.
  intros.
  apply (beta_trans H).
  apply cp_App2.
  do 2 apply cp_Abs.
  apply cp_App2.
  apply cp_App1.
  apply beta_beta.
Qed.

Lemma Abs_Abs_App1_App1_App1_app_abs V t M N K L J (R:ULC V t) :
  Abs (Abs (App (App (App (M [*:=N]) K) L) J)) >> R ->
  Abs (Abs (App (App (App (App (Abs M) N) K) L) J)) >> R .
Proof.
  intros.
  apply (beta_trans H).
  do 2 apply cp_Abs.
  do 3 apply cp_App1.
  apply beta_beta.
Qed.

Lemma Abs_Abs_App2_App1_App1_app_abs V t M N K L J (R:ULC V t):
   Abs (Abs (App K (App (App (M[*:=N]) L) J))) >> R -> 
   Abs (Abs (App K (App (App (App (Abs M) N) L) J))) >> R.
Proof.
  intros.
  apply (beta_trans H).
  do 2 apply cp_Abs.
  apply cp_App2.
  do 2 apply cp_App1.
  apply beta_beta.
Qed.

Lemma Abs_Abs_App2_App1_app_abs V t M N K L (R:ULC V t):
  Abs (Abs (App K (App (M[*:=N]) L))) >> R ->
  Abs (Abs (App K (App (App(Abs M) N) L))) >> R.
Proof.
  intros.
  apply (beta_trans H).
  do 2 apply cp_Abs.
  apply cp_App2.
  apply cp_App1.
  apply beta_beta.
Qed.

Lemma Abs_App2_app_abs V t M N K (R : ULC V t) :
   Abs (App K (M[*:=N])) >> R -> 
   Abs (App K (App (Abs M) N)) >> R.
Proof.
  intros.
  apply (beta_trans H).
  apply cp_Abs.
  apply cp_App2.
  apply beta_beta.
Qed.

Lemma App1_Abs_app_abs V t M N K (R:ULC V t) :
  App (Abs (M[*:=N])) K >> R ->
  App (Abs (App (Abs M) N)) K >> R.
Proof.
  intros.
  apply (beta_trans H).
  apply cp_App1.
  apply cp_Abs.
  apply beta_beta.
Qed.

Lemma App1_Abs_App2_App1_app_abs V t M N K L J (R:ULC V t) :
  App (Abs (App K (App (M[*:=N]) L))) J >> R -> 
  App (Abs (App K (App (App (Abs M) N) L))) J >> R.
Proof.
  intros.
  apply (beta_trans H).
  apply cp_App1.
  apply cp_Abs.
  apply cp_App2.
  apply cp_App1.
  apply beta_beta.
Qed.


Lemma App1_Abs_Abs_App2_App1_app_abs V t M N K L J (R:ULC V t) :
  App (Abs (Abs (App K (App (M[*:=N]) L)))) J >> R -> 
  App (Abs (Abs (App K (App (App (Abs M) N) L)))) J >> R.
Proof.
  intros.
  apply (beta_trans H).
  apply cp_App1.
  do 2 apply cp_Abs.
  apply cp_App2.
  apply cp_App1.
  apply beta_beta.
Qed.

Obligation Tactic := idtac.

Program Instance ULCBETA_struct (V : TT) : 
   ipo_obj_struct (ULC V) := {
 IRel t := @beta_rel V t
}.
Next Obligation.
Proof.
  constructor.
  constructor.
  assert (H':= @clos_rt_is_preorder _ (@beta_star V t)).
  unfold beta_rel in *.
  unfold Transitive.
  intros.
  destruct H' as [H1 H2].
  unfold transitive in H2.
  simpl in *.
  apply trans_rt1n.
  apply H2 with y;
    apply rt1n_trans;
    auto.
Qed.



Definition ULCBETA (V: TT) : IPO unit :=
    Build_ipo_obj (ULCBETA_struct V ).

Program Instance Var_s (V : TT) : 
    ipo_mor_struct (a:=SM_ipo _ V) (b:=ULCBETA V) (Var (V:=V)).
Next Obligation.
Proof.
  intros V t.
  unfold Proper;
  red.
  simpl.
  intros y z H.
  induction H.
  reflexivity.
Qed.

Definition VAR V := Build_ipo_mor (Var_s V).

Lemma rename_beta (V W : TT)(f : V ---> W) t (v w : ULC V t):
     v >> w -> v //- f >> w //- f.
Proof.
  intros V W f t v w H.
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
  intros s y;
  destruct y as [s y| ];
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
     (f : SM_ipo _ V ---> ULCBETA W) :
   ipo_mor_struct 
     (a:=ULCBETA V) (b:=ULCBETA W) (_subst f).
Next Obligation.
Proof.
  intros V W f t.
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
  apply (IHULCpropag _ (SM_ind 
            (V:=opt _ V) (W:=ULCBETA (opt t W)) 
      (fun t y => _shift f y))).

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
 
Lemma subst_beta (V W : TT) (f : V ---> ULC W) t 
    (v w : ULC V t) :
   v >> w -> v >>= f >> w >>= f.
Proof.
  intros.
  assert (H':= subst_s _ _ (SM_ind (W:= ULCBETA W) f)).
  apply H'.
  simpl.
  auto.
Qed.

Definition SUBST V W f := Build_ipo_mor (subst_s V W f).

Obligation Tactic := fin.

Program Instance ULCBETAM_s : RMonad_struct (SM_ipo unit) ULCBETA := {
   rweta := VAR;
   rkleisli a b f := SUBST f
}.
Next Obligation.
Proof.
  unfold Proper;
  red;
  fin.
Qed.

Definition ULCBETAM : RMonad (SM_ipo unit) := Build_RMonad ULCBETAM_s.

Lemma rename_lift V t (v : ULC V t) W (f : V ---> W) : 
       v //- f = rlift ULCBETAM f _ v.
Proof.
  unfold lift;
  fin.
Qed.
(*
Hint Rewrite lift_rename : fin.
*)

Lemma shift_shift r s V W (f : SM_ipo _ V ---> ULCBETAM W)
                (y : (opt r V) s) :
   sshift_ (P:=ULCBETAM) (W:=W) f y = y >- f .
Proof.
  intros r  s V W f y.
  destruct y as [t y | ];
  simpl;
  unfold inj;
  fin.
Qed.


Hint Resolve shift_shift : fin.
Hint Rewrite shift_shift : fin.



Definition PCF_ULC_type_mor : TY -> unit := fun _ => tt.

Program Instance ULCApp_pos :
forall (r s : PCF.types) (z : unit -> Type),
PO_mor_struct
  (a:=PO_product (ipo_proj (ULCBETA z) (PCF_ULC_type_mor (r ~> s)))
     (ipo_proj (ULCBETA z) (PCF_ULC_type_mor r)))
  (b:=ipo_proj (ULCBETA z) (PCF_ULC_type_mor s))
  (fun y => App (fst y) (snd y)).
Next Obligation.
Proof.
  unfold Proper;
  red.
  intros v w H.
  destruct H.
  simpl in *.
  transitivity (App v' w).
  apply cp_App1.
  auto.
  apply cp_App2;
  auto.
Qed.


Definition ULCApp_car r s z:
((ULCBETAM [PCF_ULC_type_mor (r ~> s)]) x 
 (ULCBETAM [PCF_ULC_type_mor r]))
    z ---> (ULCBETAM [PCF_ULC_type_mor s]) z :=
Build_PO_mor (ULCApp_pos r s z).


Program Instance ulc_app_s r s :
 RModule_Hom_struct 
   (M:= ULCBETAM [PCF_ULC_type_mor (r ~> s)] x 
         (ULCBETAM [PCF_ULC_type_mor r]))
   (N:=ULCBETAM [PCF_ULC_type_mor s]) 
   (ULCApp_car r s).

Definition ulc_app r s := Build_RModule_Hom (ulc_app_s r s).


Program Instance ULCAbs_pos:
forall (r s : TY) (z : unit -> Type),
PO_mor_struct (a:=ipo_proj (ULCBETA z *) (PCF_ULC_type_mor s))
  (b:=ipo_proj (ULCBETA z) (PCF_ULC_type_mor (r ~> s)))
  (fun y => Abs y).
Next Obligation.
Proof.
  unfold Proper;
  red.
  intros v w H.
  apply cp_Abs.
  auto.
Qed.

Definition ULCAbs_car r s z:
(d ULCBETAM // PCF_ULC_type_mor r [PCF_ULC_type_mor s]) z --->
  (ULCBETAM [PCF_ULC_type_mor (r ~> s)]) z :=
  Build_PO_mor (ULCAbs_pos r s z).


Program Instance ulc_abs_s r s : RModule_Hom_struct
  (M:= d ULCBETAM // PCF_ULC_type_mor r [PCF_ULC_type_mor s] )
  (N:= ULCBETAM [PCF_ULC_type_mor (r ~> s)])
  (ULCAbs_car r s).
Next Obligation.
Proof.
  apply f_equal.
  apply subst_eq.
  intros.
  rewrite shift_shift.
  reflexivity.
Qed.


Definition ulc_abs r s := Build_RModule_Hom (ulc_abs_s r s).


(* the Turing fixpoint operator Theta.
   it has (Theta g) --> g (Theta g)
*)
Definition ULC_theta_h (V : TT) : ULC V tt :=
 Abs(
  Abs(
   App
    (Var (none tt _ ))
    (App 
      (App 
        (Var (some tt (none tt V))) 
        (Var (some tt (none tt V))))
      (Var (none tt _)))
)).

Definition ULC_theta (V : TT) : ULC V tt :=
App (ULC_theta_h V) (ULC_theta_h V).


(* Y = \f. (\x. f (x x)) (\x. f (x x))  *)

Definition ULC_fix (V : TT) : ULC V tt := 
 Abs (
   App
    (Abs 
      (App 
        (Var (some tt (none tt V)))
        (App
          (Var (none tt (opt tt V)))
          (Var (none tt (opt tt V))))
     ))
    (Abs 
      (App 
        (Var (some tt (none tt V)))
        (App
          (Var (none tt (opt tt V)))
          (Var (none tt (opt tt V))))
     ))

).


Program Instance ULCRec_pos :
forall (t : PCF.types) (V : unit -> Type),
PO_mor_struct (a:=ipo_proj (ULCBETA V) (PCF_ULC_type_mor (t ~> t)))
  (b:=ipo_proj (ULCBETA V) (PCF_ULC_type_mor t))
  (fun y => App (ULC_theta _ ) y).
Next Obligation.
Proof.
  unfold Proper;
  red.
  intros v w H.
  simpl in *.
  apply cp_App2.
  auto.
Qed.

Definition ULCRec_car t V :
(ULCBETAM [PCF_ULC_type_mor (t ~> t)]) V --->
  (ULCBETAM [PCF_ULC_type_mor t]) V :=
 Build_PO_mor (ULCRec_pos t V).


Program Instance ulc_rec_s t : RModule_Hom_struct
 (M := ULCBETAM [PCF_ULC_type_mor (t ~> t)]) 
 (N:=ULCBETAM [PCF_ULC_type_mor t])
 (ULCRec_car t).

Definition ulc_rec t := Build_RModule_Hom (ulc_rec_s t).

Program Instance ULCttt_pos : 
    forall V : unit -> Type,
 PO_mor_struct (a:=PO_TERM)  
   (b:=ipo_proj (ULCBETA V)(PCF_ULC_type_mor Bool))
   (fun _ => Abs (V:=V)
               (Abs (V:= opt tt V) 
                   (Var (some tt (none tt (V)))))).
Next Obligation.
Proof.
  unfold Proper;
  red.
  reflexivity.
Qed.

Definition ULCttt_car V:
Term (C:=RMOD ULCBETAM PO) V ---> 
       (ULCBETAM [PCF_ULC_type_mor Bool]) V :=
Build_PO_mor (ULCttt_pos V).

Program Instance ulc_ttt_s : 
RModule_Hom_struct 
  (M:=Term) (N:=ULCBETAM [PCF_ULC_type_mor Bool])
  ULCttt_car.

Definition ulc_ttt := Build_RModule_Hom ulc_ttt_s.

Program Instance ULCfff_pos : 
    forall V : unit -> Type,
 PO_mor_struct (a:=PO_TERM)  
   (b:=ipo_proj (ULCBETA V)(PCF_ULC_type_mor Bool))
   (fun _ => Abs (Abs (Var (none tt V*)))).
Next Obligation.
Proof.
  unfold Proper;
  red.
  reflexivity.
Qed.

Definition ULCfff_car V:
Term (C:=RMOD ULCBETAM PO) V ---> 
       (ULCBETAM [PCF_ULC_type_mor Bool]) V :=
Build_PO_mor (ULCfff_pos V).

Program Instance ulc_fff_s : 
RModule_Hom_struct 
  (M:=Term) (N:=ULCBETAM [PCF_ULC_type_mor Bool])
  ULCfff_car.

Definition ulc_fff := Build_RModule_Hom ulc_fff_s.

(* not: [m+1] = 
     \f.\n. ([m] f) (f n)

instead : [m+1] = \fn. f ([m] f n)
*)

(* note : [m] has 2*m redexes in it *)

Fixpoint ULC_Nat (n : nat) (V : TT) := match n with
| 0 => Abs (Abs (Var (none tt (opt tt V))))
| S n' =>
    Abs(
     Abs (
      App
       (Var (some tt (none tt _ )))
       (App
         (App 
           (ULC_Nat n' _ )
           (Var (some tt (none tt _ ))))
         (Var (none tt _ )))))
end.

Obligation Tactic := idtac.

Program Instance ULCNats_pos m V:
PO_mor_struct (a:=Term (C:=RMOD ULCBETAM _ )V)
  (b:=ULCBETAM [PCF_ULC_type_mor Nat] V)
  (fun _ => ULC_Nat m V).
Next Obligation.
Proof.
  unfold Proper;
  red;
  reflexivity.
Qed.

Definition ULCNats_car m V := Build_PO_mor (ULCNats_pos m V).

Program Instance ulc_nats_s m : RModule_Hom_struct
 (M:= Term (C:=RMOD ULCBETAM PO))
 (N:= ULCBETAM [PCF_ULC_type_mor Nat])
 (ULCNats_car m).
Next Obligation.
Proof.
  simpl.
  intro m.
  induction m.
  simpl.
  intros. auto.
  
  intros V W f r.
  simpl.
  apply f_equal.
  apply f_equal.
  unfold inj.
  simpl. 
  assert (H':=IHm _ _ (SM_ind (V:=opt tt (opt tt V)) 
                              (W:=ULCBETAM (W*) *)
                  (fun t z => _shift (_shift f) z))).
                  simpl in H'.
  rewrite H'. apply f_equal.
  auto.
  apply tt.
Qed.
 
Definition ulc_nats m := Build_RModule_Hom (ulc_nats_s m).

(* naturals are constant under renaming *)

Lemma ulc_nats_rename n :
  forall (V W : TT) (f : V ---> W),
     ULC_Nat n W = ULC_Nat n V //- f.
Proof.
  induction n.
  simpl.
  intros.
  unfold lift.
  simpl.
  auto.
  
  simpl.
  intros.
  apply f_equal.
  apply f_equal.
  apply f_equal.
  rewrite <- IHn.
  auto.
Qed.

(* nats are constant under substitution *)

Lemma ulc_nats_lemma n :
 forall (V W : TT)
       (f : V ---> ULC W),
     ULC_Nat n W = ULC_Nat n V >>= f.
Proof.
  intros n V W f.
  assert (H':= rmod_hom_rmkl (ulc_nats n)).
  simpl in H'.
  assert (H1:=H' _ _ (SM_ind (W:=ULCBETA W) f)).
  simpl in H1.
  apply (H1 tt).
Qed.

(* - pow 0 T = \x.x 
   - pow Sn T = \x. T ((pow n T) x)

   - pow 1 T = \x. T ((pow 0 T) x) = 
             = \x. T (\y.y x) -> \x. T x

   - pow 2 T = \x. T ((pow 1 T) x) =
             -> \x. T ((\x.Tx) x) ->
                \x. T (T x)
*)

Fixpoint pow n V (T : ULC V tt) : ULC V tt :=
  match n return ULC V tt with
  | 0 => Abs (Var (none tt V ))
  | S n' => Abs (t:=tt)
      (App
        (inj _ T)
        (App
          (inj tt (pow n' T))
          (Var (none tt _))))
  end.



(* lets build  fun f x => App f (f^n x) *)
(* - ULC_nat_skel 0 f y = y
   - ULC_nat_skel Sn f y = App f (...)
*)

Fixpoint ULC_nat_skel n V  
   (f : ULC (opt tt V) tt)
   (y : ULC (opt tt (opt tt V)) tt) :
      ULC (opt tt (opt tt V)) tt :=
match n with
| 0 => y
| S n' => App (inj tt f) (ULC_nat_skel n' f y)
end.

(*  take the to-be-bound-next free variables as f and y *)

Definition ULC_nat_sk n V :=
 ULC_nat_skel n (Var (none tt V)) (Var (none tt (V*))).


(*  have free variables f, y

   - ULC_Nat_noredex 0 = y
   - ULC_Nat_noredex Sn = f (...)
*)

Fixpoint ULC_Nat_noredex n V t :=
  match n with
  | 0 => Var (V:=opt t (opt t V)) (none t (opt t V))
  | S n' => App (Var (some t (none t V)))
                   (ULC_Nat_noredex n' V t)
  end.

(* ULC_nat_sk = ULC_Nat_noredex *)
(* both have two free variables f, y
*)

Lemma ULC_nat_sk_ULC_Nat_noredex n V :
   ULC_nat_sk n V = ULC_Nat_noredex n V tt.
Proof.
  induction n.
  reflexivity.
  simpl; intros.
  rewrite <- IHn.
  reflexivity.
Qed.

(* we bind the free variables f, y 
   in order to define the natural numbers
*)

Definition ULC_Nat_nox n V t : ULC V t :=
  Abs (
   Abs (ULC_Nat_noredex n V t)).

Definition ULC_N n V : ULC V tt :=
  Abs (Abs (ULC_nat_sk n V)).

Program Instance ULC_N_pos m V:
PO_mor_struct (a:=Term (C:=RMOD ULCBETAM _ )V)
  (b:=ULCBETAM [PCF_ULC_type_mor Nat] V)
  (fun _ => ULC_N m V).
Next Obligation.
Proof.
  unfold Proper;
  red;
  reflexivity.
Qed.

Definition ULC_N_car m V := Build_PO_mor (ULC_N_pos m V).

(* superseeded by the lemma after 

Lemma ULC_nat_skel_rename n V W (f : V ---> W) a b :
  ULC_nat_skel n a b //- (^^f) = 
         ULC_nat_skel n (a//-^f) (b//-^^f).
Proof.
  induction n.
  reflexivity.
  intros;
  simpl in *.
  apply App_eq;
  auto.
  unfold inj.
  repeat rewrite rename_rename.
  fin.
Qed.
*)

Lemma ULC_nat_skel_rename_lift n V W 
     (f : V* ---> W*) a b :
  ULC_nat_skel n a b //- (^f) = 
         ULC_nat_skel n (a//-f) (b//-^f).
Proof.
induction n.
  reflexivity.
  intros;
  simpl in *.
  apply App_eq;
  auto.
  unfold inj.
  repeat rewrite rename_rename.
  fin.
Qed.


Lemma ULC_nat_skel_rename_some n V  
       a b :
   ULC_nat_skel n a b //- (some tt (A:=V * *)) = 
     ULC_nat_skel n (inj _ a) (b //- some tt (A:= V * * )).
Proof.
  simpl.
  intros.
  induction n.
  reflexivity.
  simpl.
  apply App_eq.
  auto.
  simpl.
  auto.
Qed.
 
 
(* this lemma is superseeded by the next one 

Lemma ULC_N_skel_subst n V W (f : V ---> ULC W) a b :
  ULC_nat_skel n a b >>= _shift (_shift f) =
  ULC_nat_skel n (a>>= _shift f) (b>>=_shift(_shift f)).
Proof.
  induction n.
  reflexivity.
  intros;
  simpl in *.
  apply App_eq;
  auto.
  unfold inj;
  simpl.
  rewrite rename_subst.
  rewrite subst_rename.
  fin.
Qed.
*)

Lemma ULC_N_skel_subst_shift n V W 
   (f : V* ---> ULC W*) a b :
  ULC_nat_skel n a b >>= (_shift f) =
  ULC_nat_skel n (a>>= f) (b>>=(_shift f)).
Proof.
  induction n.
  reflexivity.
  intros;
  simpl in *.
  apply App_eq;
  auto.
  unfold inj;
  simpl.
  rewrite rename_subst.
  rewrite subst_rename.
  fin.
Qed.

(* is less useful than it might seem *)

Lemma ULC_N_skel_substar n V (M : ULC (V* * ) tt) 
                (a : ULC (V* * ) tt) 
                (b:ULC (opt tt (opt tt V) * ) tt) :
  inj tt (ULC_nat_skel n (a) b [*:= M]) =
  ( ULC_nat_skel n a ((inj tt (b[*:= M])))).
Proof.
  induction n.
  reflexivity.
  simpl;
  intros.
  rewrite <- IHn.
  unfold inj;
  simpl.
  apply App_eq;
  auto.
  rewrite subst_rename.
  rewrite rename_subst.
  simpl.
  rewrite rename_lift.
  simpl.
  auto.
Qed.

(* renaming with 2 times lifted map doesn't change 
   ULC_nat_sk (which has only 2 free vars)
*)
  
Lemma ULC_N_sk_rename n V W (f : V ---> W)  :
  ULC_nat_sk n V //- ^(^f) = ULC_nat_sk n _ .
Proof.
  induction n.
  reflexivity.
  intros;
  simpl in *.
  apply App_eq.
  auto.
  rewrite IHn.
  auto.
Qed.

(* similar for substitution with 2times shifted map
*)

Lemma ULC_N_sk_subst n V W (f : V ---> ULC W) :
  ULC_nat_sk n V >>= _shift (_shift f) =
    ULC_nat_sk n W .
Proof.
  induction n.
  reflexivity.
  simpl.
  intros.
  rewrite IHn.
  unfold inj.
  simpl.
  reflexivity.
Qed.

(* the naturals defined with skel are constant under 
   substitution
*)

Lemma ULC_N_subst n V W (f : V ---> ULC W) :
  ULC_N n V >>= f = ULC_N n W.
Proof.
  simpl.
  intros.
  rewrite ULC_N_sk_subst.
  auto.
Qed.

Program Instance ulc_n_s m : RModule_Hom_struct
 (M:= Term (C:=RMOD ULCBETAM PO))
 (N:= ULCBETAM [PCF_ULC_type_mor Nat])
 (ULC_N_car m).
Next Obligation.
Proof.
  simpl.
  intros.
  rewrite ULC_N_sk_subst.
  auto.
Qed.
 
Definition ulc_N m := Build_RModule_Hom (ulc_n_s m).

(* the following lemma are the same as for skel.
   no surprise, the defs are equal
*)

Lemma ULC_Nat_noredex_rename n V W (f : V ---> W) t :
  ULC_Nat_noredex n V t //- ^(^f) = ULC_Nat_noredex n _ t.
Proof.
  induction n.
  reflexivity.
  intros;
  simpl in *.
  apply App_eq.
  auto.
  rewrite IHn.
  auto.
Qed.

Lemma ULC_Nat_noredex_subst n V W (f : V ---> ULC W) t :
  ULC_Nat_noredex n V t >>= _shift (_shift f) =
    ULC_Nat_noredex n W t.
Proof.
  induction n.
  reflexivity.
  simpl.
  intros.
  apply App_eq; 
  auto.
Qed.

Lemma ULC_Nat_nox_subst n V W (f : V ---> ULC W) t:
  ULC_Nat_nox n V t >>= f = ULC_Nat_nox n W t.
Proof.
  induction n.
  reflexivity.
  simpl in *.
  intros.
  (**)
  unfold _shift in IHn.
  unfold inj in IHn.
  simpl in IHn.
  (**)
  unfold ULC_Nat_nox in *.
  simpl.
  repeat apply f_equal.
  apply ULC_Nat_noredex_subst.
Qed.

(* Nat n reduces to Nat_nox n *)
(* Nat n has 2n redexes *)

Lemma ULC_nat_red_ULC_Nat_alt n V :
  ULC_Nat n V >> ULC_Nat_nox n V tt.
Proof.
  induction n.
  reflexivity.
  intros.
  simpl.
  unfold ULC_Nat_nox in *.
  assert (H:= IHn (opt tt (opt tt V))).
transitivity (
Abs
  (Abs
     (App (Var (V:=(V *) *) (t:=tt) 
             (some tt (A:=V *) (t:=tt) (none tt V)))
        (App
           (App 

(Abs (Abs (ULC_Nat_noredex n (V *) * tt)))

              (Var (V:=(V *) *) (t:=tt)
                 (some tt (A:=V *) (t:=tt) (none tt V))))
           (Var (V:=(V *) *) (t:=tt) (none tt V *)))))
).
  apply cp_Abs.
  apply cp_Abs.
  apply cp_App2.
  apply cp_App1.
  apply cp_App1.
  apply H.
  clear H IHn.
  sim.
  apply cp_Abs.
  apply cp_Abs.
  apply cp_App2.
  apply App1_app_abs.
  sim.
  apply app_abs_red.
  sim.
  rewrite subst_subst.
  simpl.
  
  apply beta_eq.
  generalize dependent V.
  
  induction n.
  reflexivity.
  simpl.
  intro V.
  rewrite IHn.
  auto.
Qed.
 
Program Instance ULCNats_nox_pos m V:
PO_mor_struct (a:=Term (C:=RMOD ULCBETAM _ )V)
  (b:=ULCBETAM [PCF_ULC_type_mor Nat] V)
  (fun _ => ULC_Nat_nox m V tt).
Next Obligation.
Proof.
  unfold Proper;
  red;
  reflexivity.
Qed.

Definition ULCNats_nox_car m V := Build_PO_mor (ULCNats_nox_pos m V).

Program Instance ulc_nats_nox_s m : RModule_Hom_struct
 (M:= Term (C:=RMOD ULCBETAM PO))
 (N:= ULCBETAM [PCF_ULC_type_mor Nat])
 (ULCNats_nox_car m).
Next Obligation.
Proof.
  simpl.
  intro m.
  induction m.
  simpl.
  intros. auto.
  
  intros V W f r.
  simpl.
  rewrite ULC_Nat_noredex_subst.
  unfold ULC_Nat_nox.
  simpl.
  apply f_equal.
  apply f_equal.
  apply f_equal.
  auto.
Qed.
 
Definition ulc_nats_nox m := Build_RModule_Hom (ulc_nats_nox_s m).

Lemma pow_rename (n: nat) (V W : TT)(f : V ---> W) T :
   pow n T //- f = pow n (T //- f).
Proof.
  induction n.
  reflexivity.
  intros; 
  simpl.
  apply f_equal.
  apply App_eq.
  unfold inj; simpl.
  repeat rewrite rename_rename;
  fin.
  apply App_eq.
  unfold inj; simpl.
  rewrite <- IHn.
  repeat rewrite rename_rename;
  fin.
  fin.
Qed.
  

Lemma pow_subst (n: nat) (V W : TT)(f : V ---> ULC W) T :
   pow n T >>= f = pow n (T >>= f).
Proof.
  induction n.
  reflexivity.
  simpl.
  intros.
  apply f_equal.
  apply App_eq.
  unfold inj.
  rewrite rename_subst.
  rewrite subst_rename.
  fin.
  apply App_eq.
  unfold inj.
  rewrite <- IHn.
  rewrite rename_subst.
  rewrite subst_rename.
  fin.
  auto.
Qed.


Lemma n_red_pow n V T :
  App (ULC_Nat n V) T >> pow n T.
Proof.
  intro n;
  induction n.
  simpl.
  intros V T.
  apply app_abs_red.
  unfold substar;
  simpl.
  reflexivity.
  simpl in IHn.
  unfold pow in IHn.
  intros V T.
  simpl.
  apply app_abs_red.
  unfold substar;
  simpl.
  unfold pow.
  simpl.
  rewrite <- ulc_nats_lemma.
  apply cp_Abs.
  apply cp_App2.
  apply cp_App1.
  unfold inj;
  simpl.
  assert (H':= rename_beta (some tt (A:=V))
                (IHn V T)).
  apply (beta_trans H').
  apply beta_eq.
  simpl.
  rewrite <- ulc_nats_rename.
  auto.
Qed.

Definition ULC_Nat_alt n V : ULC V tt :=
  Abs (pow n (Var (none tt V))).


Program Instance ULCNats_alt_pos m V:
PO_mor_struct (a:=Term (C:=RMOD ULCBETAM _ )V)
  (b:=ULCBETAM [PCF_ULC_type_mor Nat] V)
  (fun _ => ULC_Nat_alt m V).
Next Obligation.
Proof.
  unfold Proper;
  red;
  reflexivity.
Qed.

Definition ULCNats_alt_car m V := Build_PO_mor (ULCNats_alt_pos m V).

Program Instance ulc_nats_alt_s m : RModule_Hom_struct
 (M:= Term (C:=RMOD ULCBETAM PO))
 (N:= ULCBETAM [PCF_ULC_type_mor Nat])
 (ULCNats_alt_car m).
Next Obligation.
Proof.
  simpl.
  intro m.
  induction m.
  simpl.
  intros. auto.
  
  intros V W f r.
  simpl.
  unfold ULC_Nat_alt in *.
  simpl.
  apply f_equal.
  apply f_equal.
  apply App_eq; auto.
  apply App_eq; auto.
  unfold inj;
  simpl.
  rewrite pow_rename.
  rewrite subst_rename.
  rewrite pow_subst.
  apply f_equal.
  simpl.
  auto.
Qed.
  
Definition ulc_nats_alt m := Build_RModule_Hom (ulc_nats_alt_s m).


(* [n] T --> T^n *)


(*
Fixpoint ULC_Nat (n : nat) (V : TT) := match n with
| 0 => Abs (Abs (Var (none tt (opt tt V))))
| S n' => 
      Abs (V:=V) (Abs (V:=opt tt V) 
       (
        App (App (ULC_Nat n' _) 
                 (Var (some tt (none tt V))))
            (App (Var (some tt (none tt V)))
                 (Var ((none tt _))))))
end.
*)


(** plus = \n.\m.\f.\x. n(f) (m(f)x) *)

Definition ULC_plus (V : TT) := 
  Abs (V:=V)
   (
   Abs (V:=opt tt V)
     (
    Abs (V:= opt tt (opt tt V))
         (
          Abs (V:= opt tt (opt tt (opt tt V)))
           (
             App (V:=opt tt (opt tt (opt tt (opt tt V))))
               (App (V:=opt tt (opt tt (opt tt (opt tt V))))
                    (Var (V:=opt tt (opt tt (opt tt (opt tt V))))
                         (some tt (some tt (some tt (none tt V)))))
                    (Var (V:=opt tt (opt tt (opt tt (opt tt V))))
                         (some tt (A:=(opt tt (opt tt (opt tt V))))
                              (none tt (opt tt (opt tt V)) ))) )   
               (App (V:=opt tt (opt tt (opt tt (opt tt V))))
                    (App (V:=opt tt (opt tt (opt tt (opt tt V))))
                         (Var (V:=opt tt (opt tt (opt tt (opt tt V))))
                              (some tt (some tt (none tt (opt tt V) )))) 
                         (Var (V:=opt tt (opt tt (opt tt (opt tt V))))
                              (some tt (A:= opt tt (opt tt (opt tt V)))
                                  (none tt (opt tt (opt tt V))))))
                    (Var (V:=opt tt (opt tt (opt tt (opt tt V))))
                         (none tt (opt tt (opt tt (opt tt V) )) )))
              )
             
             )
       )
 ).

(** SUCC := \nfx.f (n f x) *)
Definition ULCsucc V : ULC V tt := 
  Abs (
   Abs (
    Abs (
      App
       (Var (some tt (none tt _ )))
       (App
         (App 
           (Var (some tt (some tt (none tt _ ))))
           (Var (some tt (none tt _ )))
         )
         (Var (none tt _ ))
       )))).

(* alternative definition for succ :
    succ := \m.\f.\n. (m f)(f n)
*)
(*
Definition ULCsucc_alt V : ULC V tt :=
  Abs (
   Abs (
    Abs(
     App
      (App 
        (Var (some tt (some tt (none tt V))))
        (Var (some tt (none tt (opt tt V)))))
      (App 
        (Var (some tt (none tt _ )))
        (Var (none tt _ )))
      
))).
*)

Obligation Tactic := fin.

Program Instance ULCSucc_pos :
forall V : unit -> Type,
PO_mor_struct (a:=PO_TERM) 
  (b:=ipo_proj (ULCBETA V) (PCF_ULC_type_mor (Nat ~> Nat)))
  (fun _ => ULCsucc V).
Next Obligation.
Proof.
  unfold Proper;
  red.
  reflexivity.
Qed.

Definition ULCSucc_car V :
Term (C:=RMOD ULCBETAM _ ) V ---> 
 (ULCBETAM [PCF_ULC_type_mor (Nat ~> Nat)]) V :=
  Build_PO_mor (ULCSucc_pos V).


Program Instance ulc_succ_s : RModule_Hom_struct
  (M:= Term (C:=RMOD ULCBETAM PO))
  (N:= ULCBETAM [PCF_ULC_type_mor (Nat ~> Nat)])
  ULCSucc_car.

Definition ulc_succ := Build_RModule_Hom ulc_succ_s.

(** if then else = \a.\b.\c. a(b)(c) *)

Definition ULC_cond (V : TT) :=
     Abs (V:=V)
        ( Abs (V:=opt tt V)
            ( Abs (V:=opt tt (opt tt V))
               (
                   App (V:= opt tt (opt tt (opt tt V)))
                      (App (V:= opt tt (opt tt (opt tt V)))
                         (Var (V:= opt tt (opt tt (opt tt V)))
                            (some tt (some tt (none tt V)))) 
                         (Var (some tt (none tt (opt tt V))))
                      )
                      (Var (none tt (opt tt (opt tt V)))
                      )
               )
            )
        ).


Program Instance ULCCondN_pos :
forall V : unit -> Type,
PO_mor_struct (a:=PO_TERM) 
  (b:=ipo_proj (ULCBETA V) (PCF_ULC_type_mor 
                         (Bool ~> Nat ~> Nat ~> Nat)))
  (fun _ => ULC_cond V).
Next Obligation.
Proof.
  unfold Proper;
  red.
  reflexivity.
Qed.

Definition ULCCondN_car V :
Term (C:=RMOD ULCBETAM _ ) V ---> 
 (ULCBETAM [PCF_ULC_type_mor (Nat ~> Nat)]) V :=
  Build_PO_mor (ULCCondN_pos V).

Program Instance ulc_condn_s : RModule_Hom_struct 
  (M := Term (C:=RMOD ULCBETAM PO))
  (N:= ULCBETAM [PCF_ULC_type_mor (Bool ~> Nat ~> Nat ~> Nat)])
  (ULCCondN_car).

Definition ulc_condn := Build_RModule_Hom ulc_condn_s.


Program Instance ULCCondB_pos :
forall V : unit -> Type,
PO_mor_struct (a:=PO_TERM) 
  (b:=ipo_proj (ULCBETA V) (PCF_ULC_type_mor 
                         (Bool ~> Bool ~> Bool ~> Bool)))
  (fun _ => ULC_cond V).

Definition ULCCondB_car V :
Term (C:=RMOD ULCBETAM _ ) V ---> 
 (ULCBETAM [PCF_ULC_type_mor (Nat ~> Nat)]) V :=
  Build_PO_mor (ULCCondB_pos V).

Program Instance ulc_condb_s : RModule_Hom_struct 
  (M := Term (C:=RMOD ULCBETAM PO))
  (N:= ULCBETAM [PCF_ULC_type_mor (Bool ~> Bool ~> Bool ~> Bool)])
  (ULCCondB_car).

Definition ulc_condb := Build_RModule_Hom ulc_condb_s.


Definition ULC_omega (V : TT) :=
    Abs (V:= V)
      ( App (Var (none tt V)) (Var (none tt V))).

Program Instance ULC_bottom_pos :
forall (t : TY) (V : unit -> Type),
PO_mor_struct (a:=PO_TERM) 
 (b:=ipo_proj (ULCBETA V) (PCF_ULC_type_mor t))
 (fun _ => ULC_omega V).
Next Obligation.
Proof.
  unfold Proper;
  red.
  reflexivity.
Qed.

Definition ULCbottom_car t V :
Term (C:=RMOD ULCBETAM _ ) V ---> 
  (ULCBETAM [PCF_ULC_type_mor t]) V :=
  Build_PO_mor (ULC_bottom_pos t V).

Program Instance ulc_bottom_s t : RModule_Hom_struct 
  (M:= Term (C:= RMOD ULCBETAM PO))
  (N:= ULCBETAM [PCF_ULC_type_mor t])
  (ULCbottom_car t).

Definition ulc_bottom t := Build_RModule_Hom (ulc_bottom_s t).


(* zero? = \n.((n)(true)false)true     *)

Definition ULC_zero (V : TT) := 
  Abs (
   App 
     (App
       (Var (none tt V ))
       (Abs (ulc_fff _ tt)))
     (ulc_ttt _ tt))
.


Program Instance ULCzero_pos :
forall V : unit -> Type,
PO_mor_struct (a:=PO_TERM) 
  (b:=ipo_proj (ULCBETA V) (PCF_ULC_type_mor 
                         (Nat ~> Bool)))
  (fun _ => ULC_zero V).
Next Obligation.
Proof.
  unfold Proper;
  red.
  reflexivity.
Qed.

Definition ULCzero_car V :
Term (C:=RMOD ULCBETAM _ ) V ---> 
 (ULCBETAM [PCF_ULC_type_mor (Nat ~> Nat)]) V :=
  Build_PO_mor (ULCzero_pos V).

Program Instance ulc_zero_s : RModule_Hom_struct 
  (M:= Term (C := RMOD ULCBETAM PO))
  (N:= ULCBETAM [PCF_ULC_type_mor (Nat ~> Bool)])
  ULCzero_car.

Definition ulc_zero := Build_RModule_Hom ulc_zero_s.

(* T f := \gh. h (g f) *)
Definition ULC_T V f : ULC V tt :=
  Abs (
   Abs (
    App 
     (Var (none tt _))
     (App 
       (Var (some tt (none tt V)))
       (inj _ (inj _ f))))
).

Lemma T_rename (V W : TT) (g : V ---> W) f :
  ULC_T  f //- g = ULC_T (f//-g).
Proof.
  simpl.
  unfold ULC_T.
  intros.
  repeat apply f_equal.
  unfold inj;
  simpl.
  repeat rewrite rename_rename.
  apply rename_eq.
  simpl.
  auto.
Qed.


Check ULC_T.

(*PRED := \nfx.n (\gh.h (g f)) (\u.x) (\u.u)*)

Definition ULC_pred_alt (V : TT) : ULC V tt :=
  Abs (
   Abs (
    Abs (
     App 
       (App 
         (App
           (Var (some tt (some tt (none tt V))))         
           (ULC_T (Var (some tt (none tt _ ))))
)
         (Abs (Var (some tt (none tt _ )))))
       (Abs (Var (none _ _ )))
))).


Definition ULC_pred (V : TT) : ULC V tt :=
  Abs (
   Abs (
    Abs (
     App 
       (App 
         (App
           (Var (some tt (some tt (none tt V))))         
           (Abs (
             Abs (
              App
               (Var (none tt _ ))
               (App 
                 (Var (some tt (none tt _ )))
                 (Var (some tt (some tt (some tt (none tt _ )))))
             )))))
         (Abs (Var (some tt (none tt _ )))))
       (Abs (Var (none _ _ )))
))).

Lemma ULC_pred_alt_correct V : 
  ULC_pred_alt V = ULC_pred V.
Proof.
  reflexivity.
Qed.



Program Instance ULCpred_pos :
forall V : unit -> Type,
PO_mor_struct (a:=PO_TERM) 
  (b:=ipo_proj (ULCBETA V) (PCF_ULC_type_mor 
                         (Nat ~> Nat)))
  (fun _ => ULC_pred_alt V).
Next Obligation.
Proof.
  unfold Proper;
  red.
  reflexivity.
Qed.

Definition ULCpred_car V :
Term (C:=RMOD ULCBETAM _ ) V ---> 
 (ULCBETAM [PCF_ULC_type_mor (Nat ~> Nat)]) V :=
  Build_PO_mor (ULCpred_pos V).

Program Instance ulc_pred_s : RModule_Hom_struct 
  (M:= Term (C := RMOD ULCBETAM PO))
  (N:= ULCBETAM [PCF_ULC_type_mor (Nat ~> Nat)])
  ULCpred_car.

Definition ulc_pred := Build_RModule_Hom ulc_pred_s.

(*  pow 0 T = \x.x
    pow (S n) T = \x. T ((pow n T) x)
*)

(* this is wrong 
Lemma ULC_nat_eq_ULC_Nat_alt2 n V :
  ULC_Nat n V = ULC_Nat_alt n V.
Proof.
  induction n.
  reflexivity.
  
  simpl.
  intro V.
  rewrite IHn.
  unfold ULC_Nat_alt.
  simpl.
  apply f_equal.
  apply f_equal.
  apply App_eq.
  reflexivity.
  apply App_eq.
*)

(* T(n)(λu.x) = (λh.h(f(n-1)(x))) *)
(*
Section bla.
Variable V : TT.
Variable f : ULC V tt.
Variable y : ULC V tt.
Check inj.
(* [n+1] (T f) (\u.y) --> \h.h ([n] f y) *)
Lemma pred_helper n : beta_rel
  (App 
    (App 
       (ULC_Nat (n+1) V )
       (ULC_T (f)))
    (Abs (inj tt y))) 
  (Abs (
     App
       (Var (none tt _ ))
       (App 
         (App 
           (ULC_Nat n (opt tt V) )
           (inj _ f))
         (inj tt y)))).
Proof.
  induction n.
  simpl.
  
assert (H:= app_abs 
(Abs
        (Var (V:=(((V * ) * ) * ) * ) (t:=tt)
          (none tt (opt tt (opt tt V)) * )))
(Var (V:=(V * ) * ) (t:=tt)
       (some tt (A:=V * ) (t:=tt) (none tt V)))

).
unfold substar in H;
simpl in H.
 
 transitivity (
(App
     (App
        (Abs
           (Abs
              (App
                 (Var (V:=(V * ) * ) (t:=tt)
                    (some tt (A:=V * ) (t:=tt) (none tt V)))
                 (App
                    
(Abs (Var (V:=((V * ) * ) * ) (t:=tt) (none tt (V * ) * )))

                    (Var (V:=(V * ) * ) (t:=tt) (none tt V * )))))) 
            (ULC_T f))
     (Abs (inj tt y)))
).
apply cp_App1.
apply cp_App1.
apply cp_Abs.
apply cp_Abs.
apply cp_App2.
apply cp_App1.
apply beta_beta.
clear H.

assert (H:= app_abs 
(Var (V:=((V * ) * ) * ) (t:=tt) (none tt (opt tt (opt tt V))))
(Var (V:=(V * ) * ) (t:=tt) (none tt V * ))
).
unfold substar in H;
simpl in H.

transitivity (
(App
     (App
        (Abs
           (Abs
              (App
                 (Var (V:=(V * ) * ) (t:=tt)
                    (some tt (A:=V * ) (t:=tt) (none tt V)))
                 (Var (V:=(V * ) * ) (t:=tt) (none tt V * ))
)))
(ULC_T f))
     (Abs (inj tt y)))
).
apply cp_App1.
apply cp_App1.
apply cp_Abs.
apply cp_Abs.
apply cp_App2.
apply beta_beta.
clear H.
  
  apply App1_app_abs;
  unfold substar;
  simpl.
  unfold inj; 
  simpl.
  

  unfold lift; simpl.
  apply app_abs_red;
  unfold substar;
  simpl.
  apply app_abs_red;
  unfold substar;
  simpl.
  apply cp_Abs.
  apply cp_App2.
  unfold inj;
  simpl.
     
*)



(** some lemmata for pred (succ n) -> n*)
Check pow.
Print pow.
Fixpoint power n V t (f : ULC V t) (y : ULC V t):=
  match n with
  | 0 => y
  | S n' => App f (power n' f y)
  end.
Check ULC_T.

(* T = \gh. h (g f) *)

Definition ULC_TT V : ULC (opt tt V) tt :=
  Abs (V:=opt tt V)
   (Abs (V:= opt tt (opt tt V))
    (App (V:= opt tt (opt tt (opt tt V)))
      (Var (V:= opt tt (opt tt (opt tt V)))
           (none tt (opt tt (opt tt V))))
      (App (V:= opt tt (opt tt (opt tt V)))
        (Var (V:= opt tt (opt tt (opt tt V))) 
             (some tt (none tt _) ))
        (Var (V:= opt tt (opt tt (opt tt V)))
             (some tt (some tt 
                (none tt (_)))))))).

(* [n] T x --> power n T x *)
(*
Lemma n_T_power n V f y :
  App
   (App
    (ULC_N n V)
    f)
   y  >>
  power n f y.
Proof.
  induction n.
  intros.
  apply App1_app_abs.
  sim.
  apply beta_beta.

  simpl.
  intros.
  transitivity (
  App f (App (App (ULC_N n V) f) y)
).
Focus 2.
apply App2_App1_app_abs.
sim.
unfold ULC_nat_sk.
assert (H':=ULC_N_skel_subst_shift n).
(substar f)).
simpl in H'.
rewrite H'.
 (Var (none tt V))).
reflexivity.
apply App1_app_abs.
sim.
*)


(* [n+1] T (\u.x) --> \h.h (power n f x) *)
(*
Lemma T_n_red n V :
  App
   (App 
     (inj tt (inj tt (ULC_N (S n) V)))
     (inj tt (ULC_TT V)))
   (Abs (Var (some tt (none tt _)))) >>
     Abs 
     (App 
       (Var (none tt _ ))
       (power n 
           (Var (some tt (some tt (none tt _ ))))
           (Var (some tt (none tt _ ))))).
Proof.
  induction n.
  simpl.
  unfold inj;
  simpl.
  intro V.
  apply App1_app_abs.
  sim.
  apply app_abs_red.
  sim.
  apply app_abs_red.
  sim.
  apply Abs_App2_app_abs.
  sim.
  reflexivity.
  
  intro V.
  unfold inj in *;
  simpl in *.
  assert (H':= IHn V).
  clear IHn.
  apply App1_app_abs.
  sim.
  rew ULC_nat_skel_rename.
  rew (ULC_nat_skel_rename).
  rewrite ULC_N_skel_subst_shift.
  sim.
  assert (H2:=ULC_nat_skel_rename).
  simpl in H2.
  rewrite H2 in H'.
  rewrite H2 in H'.
  simpl in H'.
  apply App1_Abs_app_abs.
  sim.
  apply App1_Abs_Abs_App2_App1_app_abs.
  sim.
  rew ULC_nat_skel_rename_some.
  rew ULC_nat_skel_rename_some.
  unfold inj; simpl.
  
simpl.
apply cp_App1.
apply cp_App1.
apply cp_Abs.
apply cp_Abs.
apply cp_App2.
apply 

reflexivity.

*)

Obligation Tactic := idtac.

Program Instance PCF_ULC_rep_s : 
 PCFPO_rep_struct (U:=unit) ULCBETAM (PCF_ULC_type_mor) := {

  app r s := ulc_app r s ;
  abs r s := ulc_abs r s ;
  rec t := ulc_rec t ;
  tttt := ulc_ttt ;
  ffff := ulc_fff ;
  nats m := ulc_N m ;
  Succ := ulc_succ ;
  CondB := ulc_condb ;
  CondN := ulc_condn ;
  bottom t := ulc_bottom t ;
  Zero := ulc_zero ;
  Pred := ulc_pred
}.

Obligation 14.
Proof.
simpl.
intros.
unfold ULCsucc.
apply app_abs_red.
sim.
unfold ULC_nat_sk.
rew (ULC_nat_skel_rename_lift n).
rew (ULC_nat_skel_rename n).
sim.
apply Abs_Abs_App1_App1_App1_app_abs.
sim.
rew (ULC_nat_skel_rename n).
rew (ULC_nat_skel_rename n).
sim.
unfold lift;
sim.
apply Abs_Abs_App1_App1_app_abs.
sim.
rewrite ULC_N_skel_subst_shift.
sim.
apply Abs_Abs_App1_app_abs.
sim.
rewrite ULC_N_skel_subst_shift.
sim.
apply Abs_Abs_App1_app_abs.
sim.
rew (ULC_nat_skel_rename n).
sim.
apply Abs_Abs_app_abs.
sim.
rewrite ULC_N_skel_subst_shift.
sim.
apply Abs_Abs_App2_App1_App1_app_abs.
sim.
rewrite ULC_N_skel_subst_shift.
sim.
apply Abs_Abs_app_abs.
sim.
apply Abs_Abs_App1_app_abs.
sim.
assert (H:=ULC_N_skel_substar n (Abs
                (Var (V:=((V *) *) *) (t:=tt)
                   (some tt (A:=(V *) *) (t:=tt) (none tt V *))))
(Abs
              (Abs
                 (App
                    (Var (V:=(((V *) *) *) *) (t:=tt) (none tt ((V *) *) *))
                    (App
                       (Var (V:=(((V *) *) *) *) (t:=tt)
                          (some tt (A:=((V *) *) *) (t:=tt) (none tt (V *) *)))
                       (Var (V:=(((V *) *) *) *) (t:=tt)
                          (some tt (A:=((V *) *) *) (t:=tt)
                             (some tt (A:=(V *) *) (t:=tt)
                                (some tt (A:=V *) (t:=tt) (none tt V)))))))))
(Var (V:=((V *) *) *) (t:=tt) (none tt (V *) *))
).
unfold inj,substar in H.
simpl in H. Check rename_subst.
rewrite rename_subst in H.
simpl in H.
rewrite H.

simpl in H.
unfold 


Check (Abs
              (Abs
                 (App
                    (Var (V:=(((V *) *) *) *) (t:=tt) (none tt ((V *) *) *))
                    (App
                       (Var (V:=(((V *) *) *) *) (t:=tt)
                          (some tt (A:=((V *) *) *) (t:=tt) (none tt (V *) *)))
                       (Var (V:=(((V *) *) *) *) (t:=tt)
                          (some tt (A:=((V *) *) *) (t:=tt)
                             (some tt (A:=(V *) *) (t:=tt)
                                (some tt (A:=V *) (t:=tt) (none tt V))))))))).
Check 
(Var (V:=((V *) *) *) (t:=tt) (none tt (opt tt (opt tt V)))).
Check (fun (t : unit) (y : ((V *) *) * t) =>
          match y in (opt _ _ u) return (ULC (V *) * u) with
          | some t0 v => Var (V:=(V *) *) (t:=t0) v
          | none =>
              Abs
                (Var (V:=((V *) *) *) (t:=tt)
                   (some tt (A:=(V *) *) (t:=tt) (none tt (opt tt V))))
          end).
Check (Abs
                (Var (V:=((V *) *) *) (t:=tt)
                   (some tt (A:=(V *) *) (t:=tt) (none tt (opt tt V))))).
Check 
(ULC_nat_skel n
           (Abs
              (Abs
                 (App
                    (Var (V:=(((V *) *) *) *) (t:=tt) (none tt ((V *) *) *))
                    (App
                       (Var (V:=(((V *) *) *) *) (t:=tt)
                          (some tt (A:=((V *) *) *) (t:=tt) (none tt (V *) *)))
                       (Var (V:=(((V *) *) *) *) (t:=tt)
                          (some tt (A:=((V *) *) *) (t:=tt)
                             (some tt (A:=(V *) *) (t:=tt)
                                (some tt (A:=V *) (t:=tt) (none tt V)))))))))
           (Var (V:=((V *) *) *) (t:=tt) (none tt (V *) *))).

Print substar.

 Print _shift.
rew (ULC_nat_skel_rename n).
apply App2_app_abs.
sim.
unfold ULC_nat_sk.
rew (ULC_nat_skel_rename n).
rew (ULC_nat_skel_rename n).
unfold lift;
sim.
apply App2_Abs_Abs_App2_App1_app_abs.
sim.
rewrite (ULC_N_skel_subst_shift).
sim.
apply app_abs_red.
sim.
rew ULC_nat_skel_rename.
rew ULC_nat_skel_rename.
unfold lift;
sim.
apply Abs_Abs_App1_App1_app_abs.
sim.
rewrite ULC_N_skel_subst_shift.
sim.
apply Abs_Abs_App1_App1_Abs_app_abs.
sim.
rew (ULC_nat_skel_rename_lift).
sim.
apply Abs_Abs_App1_app_abs.
sim.
rewrite ULC_N_skel_subst_shift.
sim.
apply 

Obligation 13.
Proof.
simpl.
intros.
generalize dependent V.
intro V.
apply app_abs_red;
sim.
rew (ULC_nat_skel_rename n).
rew (ULC_nat_skel_rename n).
unfold lift;
sim.

apply Abs_Abs_App1_App1_app_abs.
sim.
rewrite ULC_N_skel_subst_shift.
sim.
unfold lift;
simpl.
apply Abs_Abs_App1_App1_Abs_app_abs.
sim.
rewrite ULC_nat_skel_rename_some.
sim.
unfold lift;
sim.

sim.
apply Abs_Abs_App1_app_abs.
sim.
apply Abs_Abs_app_abs.
sim.
apply Abs_Abs_app_abs.
sim.
apply Abs_Abs_app_abs.
sim.
reflexivity.

simpl in *.
intro V.
apply app_abs_red.
sim.
rewrite (ULC_nat_skel_rename _ (some tt (A:=V))).
simpl. Print ULC_nat_skel_rename.
rewrite (ULC_nat_skel_rename n (some tt (A:=V*))
 ((Var (V:=(V *) *) (t:=tt)
   (^(some tt (A:=V)) tt (none tt V))))).
simpl.
unfold lift;
simpl.
apply Abs_Abs_App1_App1_app_abs.
sim.
rewrite ULC_N_skel_subst_shift.
simpl.
unfold lift;
simpl.
apply Abs_Abs_App1_App1_Abs_app_abs.
sim.
unfold lift;
simpl. Check ULC_nat_skel.
rewrite ULC_nat_skel_rename_some.
sim.
unfold lift;
simpl.
apply Abs_Abs_App1_app_abs;
sim.
rewrite ULC_N_skel_subst_shift.
sim.
unfold lift;
sim.
apply Abs_Abs_App1_Abs_App2_App1_app_abs.
sim.
rewrite ULC_nat_skel_rename_some.
sim.
unfold lift;
sim.
apply Abs_Abs_app_abs.
sim.
rewrite ULC_N_skel_subst_shift.
sim.

clear IHn.
induction n.
simpl.
apply Abs_Abs_app_abs.
sim.
apply Abs_Abs_app_abs.
sim.

apply Abs_Abs_App2_app_abs.
sim.
reflexivity.




apply Abs_Abs_app_abs.
sim.
apply Abs_Abs_app_abs.
sim.
rewrite ULC_N_skel_subst_shift.
sim.

rewrite ULC_N_skel_subst_shift.
sim.


apply Abs_Abs_App1_Abs_App2_app_abs.
sim.
apply (Abs_Abs_App1_Abs_App2_App1_app_abs
   (Var (V:=((V *) *) *) (t:=tt) (none tt (V *) *)))  .



rewrite <- subst_shift_shift.

rewrite H'.
rewrite rename_rename.

reflexivity.






Obligation 1.
Proof.
  simpl; intros.
  apply clos_refl_trans_1n_contains.
  apply relorig.
  constructor.
Qed.
Obligation 2.
Proof.
  simpl; intros.
  apply cp_App1;
  auto.
Qed.
Obligation 3.
Proof.
  simpl; intros.
  apply cp_App2;
  auto.
Qed.
Obligation 4.
Proof.
  simpl; intros.
  apply cp_Abs;
  auto.
Qed.
Obligation 5.
Proof.
  simpl; intros.
  apply cp_App2;
  auto.
Qed.
Obligation 6.
Proof.
  simpl; intros.
  unfold ULC_cond.
  assert (H:= app_abs 
     (Abs
        (Abs
             (App
                (App
                   (Var (V:=((V *) *) *) (t:=tt)
                     (some tt (A:=(V *) *) (t:=tt)
                        (some tt (A:=V *) (t:=tt) (none tt V))))
                   (Var (V:=((V *) *) *) (t:=tt)
                       (some tt (A:=(V *) *) (t:=tt) (none tt V *))))
             (Var (V:=((V *) *) *) (t:=tt) (none tt (V *) *)))))

(Abs
              (Abs
                 (Var (V:=(V *) *) (t:=tt)
                    (some tt (A:=V *) (t:=tt) (none tt V)))))
).
simpl in H.
unfold substar in H.
simpl in H.
unfold inj in H.
simpl in H.
transitivity (App (App 
(Abs
         (Abs
            (App
               (App
                  (Abs
                     (Abs
                        (Var (V:=(((V *) *) *) *) (t:=tt)
                           (^(^(some tt (A:=V *))) tt
                              (^(^(some tt (A:=V))) tt
                         (some tt (A:=V *) (t:=tt) (none tt V)))))))
                  (Var (V:=(V *) *) (t:=tt)
                     (some tt (A:=V *) (t:=tt) (none tt V))))
               (Var (V:=(V *) *) (t:=tt) (none tt V *))))) n)m).
apply cp_App1.
apply cp_App1.
apply clos_refl_trans_1n_contains.
apply relorig.
apply app_abs.

clear H.
assert (H:=app_abs
(Abs
           (Var (V:=(((V *) *) *) *) (t:=tt)
             (^(^(some tt (A:=V *))) tt
             (^(^(some tt (A:=V))) tt
            (some tt (A:=V *) (t:=tt) (none tt V))))))

(Var (V:=(V *) *) (t:=tt)
         (some tt (A:=V *) (t:=tt) (none tt V)))).
unfold substar in H.
simpl in H.
unfold inj in H.
simpl in H.

transitivity (
(App
     (App
        (Abs
           (Abs
              (App
                 (Abs
         (Var (V:=((V *) *) *) (t:=tt)
            (some tt (A:=(V *) *) (t:=tt)
               (some tt (A:=V *) (t:=tt) (none tt V)))))
                 (Var (V:=(V *) *) (t:=tt) (none tt V *))))) n) m)).
apply cp_App1.
apply cp_App1.
apply cp_Abs.
apply cp_Abs.
apply cp_App1.
apply clos_refl_trans_1n_contains.
apply relorig.
apply app_abs.

clear H.
assert (H:=app_abs (Var (V:=((V *) *) *) (t:=tt)
                       (some tt (A:=(V *) *) (t:=tt)
                          (some tt (A:=V *) (t:=tt) (none tt V))))
(Var (V:=(V *) *) (t:=tt) (none tt V *))
).
unfold substar in H.
simpl in H.

transitivity 
(App
     (App
        (Abs
           (Abs
      (Var (V:=(V *) *) (t:=tt) (some tt (A:=V *) (t:=tt) (none tt V)))        
)) n) m).
apply cp_App1.
apply cp_App1.
apply cp_Abs.
apply cp_Abs.
apply clos_refl_trans_1n_contains.
apply relorig.
apply app_abs.
clear H.
assert (H:= app_abs
(Abs
   (Var (V:=(V *) *) (t:=tt)
          (some tt (A:=V *) (t:=tt) (none tt V)))) n).
unfold substar in H.
simpl in H.
unfold inj in H.
simpl in H.

transitivity (
  (App
     (Abs (n //- some tt (A:=V)))
m)
).
apply cp_App1.
apply clos_refl_trans_1n_contains.
apply relorig.
apply app_abs.
clear H.
assert (H:= app_abs 
   (n //- some tt (A:=V)) m).
unfold substar in H.
simpl in H.
rewrite subst_rename in H.
simpl in H.
rewrite subst_var_eta in H.
apply clos_refl_trans_1n_contains.
apply relorig.
auto.
Qed.
Next Obligation.
Proof.
  intros; simpl.
  unfold ULC_cond.
  assert (H:= app_abs 
  (Abs
     (Abs
       (App
         (App
          (Var (V:=((V *) *) *) (t:=tt)
               (some tt (A:=(V *) *) (t:=tt)
                 (some tt (A:=V *) (t:=tt) (none tt V))))
              (Var (V:=((V *) *) *) (t:=tt)
             (some tt (A:=(V *) *) (t:=tt) (none tt V *))))
          (Var (V:=((V *) *) *) (t:=tt) (none tt (V *) *)))))

(Abs (Abs (Var (V:=(V *) *) (t:=tt) (none tt V *)))))
.
unfold substar in H.
simpl in H.
unfold inj in H.
simpl in H.

transitivity(
(App
     (App
  (Abs
         (Abs
            (App
               (App
                  (Abs
                     (Abs
                        (Var (V:=(((V *) *) *) *) (t:=tt)
                           (^(^(some tt (A:=V *))) tt
                         (^(^(some tt (A:=V))) tt (none tt V *))))))
                  (Var (V:=(V *) *) (t:=tt)
                     (some tt (A:=V *) (t:=tt) (none tt V))))
               (Var (V:=(V *) *) (t:=tt) (none tt V *)))))       
n) m)
).
apply cp_App1.
apply cp_App1.
apply clos_refl_trans_1n_contains.
apply relorig.
auto.
clear H.
assert (H:= app_abs
  (Abs
      (Var (V:=(((V *) *) *) *) (t:=tt)
          (^(^(some tt (A:=V *))) tt
           (^(^(some tt (A:=V))) tt (none tt V *)))))
(Var (V:=(V *) *) (t:=tt)
                       (some tt (A:=V *) (t:=tt) (none tt V)))
).
unfold substar in H;
simpl in H.
transitivity (
(App
     (App
        (Abs
           (Abs
              (App
                 (Abs (Var (V:=((V *) *) *) (t:=tt) (none tt (V *) *)))
                 (Var (V:=(V *) *) (t:=tt) (none tt V *))))) n) m)
).
apply cp_App1.
apply cp_App1.
apply cp_Abs.
apply cp_Abs.
apply cp_App1.
apply clos_refl_trans_1n_contains.
apply relorig.
auto.
clear H.

assert (H:= app_abs 
  (Var (V:=((V *) *) *) (t:=tt) (none tt (opt tt (opt tt V ) )))
  (Var (V:=(V *) *) (t:=tt) (none tt V *))
).
unfold substar in H;
simpl in H.

transitivity (
(App
   (App
     (Abs
        (Abs

          (Var (V:=(V *) *) (t:=tt) (none tt V *))

)) n) m)
).
apply cp_App1.
apply cp_App1.
apply cp_Abs.
apply cp_Abs.
apply clos_refl_trans_1n_contains.
apply relorig.
auto.
clear H.

assert (H:= app_abs 
  (Abs (Var (V:=(V *) *) (t:=tt) (none tt V *)))
n
).
unfold substar in H;
simpl in H.

transitivity (
(App  
  (Abs (Var (V:=V *) (t:=tt) (none tt V)))
m)
).
apply cp_App1.
apply clos_refl_trans_1n_contains.
apply relorig.
auto.
clear H.
apply clos_refl_trans_1n_contains.
apply relorig.
apply app_abs.
Qed.
Next Obligation.
Proof.
  intros; simpl.
  unfold ULC_cond.
  assert (H:= app_abs 
     (Abs
          (Abs
          (App
              (App
                  (Var (V:=((V *) *) *) (t:=tt)
                     (some tt (A:=(V *) *) (t:=tt)
                       (some tt (A:=V *) (t:=tt) (none tt V))))
                 (Var (V:=((V *) *) *) (t:=tt)
                    (some tt (A:=(V *) *) (t:=tt) (none tt V *))))
                 (Var (V:=((V *) *) *) (t:=tt) (none tt (V *) *)))))

(Abs
       (Abs
         (Var (V:=(V *) *) (t:=tt)
          (some tt (A:=V *) (t:=tt) (none tt V)))))
).
simpl in H.
unfold substar in H.
simpl in H.
unfold inj in H.
simpl in H.
transitivity (App (App 
(Abs
         (Abs
            (App
               (App
                  (Abs
                     (Abs
                        (Var (V:=(((V *) *) *) *) (t:=tt)
                           (^(^(some tt (A:=V *))) tt
                              (^(^(some tt (A:=V))) tt
                                 (some tt (A:=V *) (t:=tt) 
                                         (none tt V)))))))
                  (Var (V:=(V *) *) (t:=tt)
                     (some tt (A:=V *) (t:=tt) (none tt V))))
               (Var (V:=(V *) *) (t:=tt) (none tt V *))))) u)v).
apply cp_App1.
apply cp_App1.
apply clos_refl_trans_1n_contains.
apply relorig.
apply app_abs.

clear H.
assert (H:=app_abs
(Abs
           (Var (V:=(((V *) *) *) *) (t:=tt)
             (^(^(some tt (A:=V *))) tt
             (^(^(some tt (A:=V))) tt
            (some tt (A:=V *) (t:=tt) (none tt V))))))

(Var (V:=(V *) *) (t:=tt)
         (some tt (A:=V *) (t:=tt) (none tt V)))).
unfold substar in H.
simpl in H.
unfold inj in H.
simpl in H.

transitivity (
(App
     (App
        (Abs
           (Abs
              (App
                 (Abs
         (Var (V:=((V *) *) *) (t:=tt)
            (some tt (A:=(V *) *) (t:=tt)
               (some tt (A:=V *) (t:=tt) (none tt V)))))
                 (Var (V:=(V *) *) (t:=tt) (none tt V *))))) u) v)).
apply cp_App1.
apply cp_App1.
apply cp_Abs.
apply cp_Abs.
apply cp_App1.
apply clos_refl_trans_1n_contains.
apply relorig.
apply app_abs.

clear H.
assert (H:=app_abs (Var (V:=((V *) *) *) (t:=tt)
                       (some tt (A:=(V *) *) (t:=tt)
                          (some tt (A:=V *) (t:=tt) (none tt V))))
(Var (V:=(V *) *) (t:=tt) (none tt V *))
).
unfold substar in H.
simpl in H.

transitivity 
(App
     (App
        (Abs
           (Abs
      (Var (V:=(V *) *) (t:=tt) (some tt (A:=V *) (t:=tt) 
   (none tt V)))        
)) u) v).
apply cp_App1.
apply cp_App1.
apply cp_Abs.
apply cp_Abs.
apply clos_refl_trans_1n_contains.
apply relorig.
apply app_abs.
clear H.
assert (H:= app_abs
(Abs
   (Var (V:=(V *) *) (t:=tt)
          (some tt (A:=V *) (t:=tt) (none tt V)))) u).
unfold substar in H.
simpl in H.
unfold inj in H.
simpl in H.

transitivity (
  (App
     (Abs (u //- some tt (A:=V)))
v)
).
apply cp_App1.
apply clos_refl_trans_1n_contains.
apply relorig.
apply app_abs.
clear H.
assert (H:= app_abs 
   (u //- some tt (A:=V)) v).
unfold substar in H.
simpl in H.
rewrite subst_rename in H.
simpl in H.
rewrite subst_var_eta in H.
apply clos_refl_trans_1n_contains.
apply relorig.
auto.
Qed.
Next Obligation.
Proof.
  intros; simpl.
  unfold ULC_cond.
  assert (H:= app_abs 
  (Abs
     (Abs
       (App
         (App
          (Var (V:=((V *) *) *) (t:=tt)
               (some tt (A:=(V *) *) (t:=tt)
                 (some tt (A:=V *) (t:=tt) (none tt V))))
              (Var (V:=((V *) *) *) (t:=tt)
             (some tt (A:=(V *) *) (t:=tt) (none tt V *))))
          (Var (V:=((V *) *) *) (t:=tt) (none tt (V *) *)))))

(Abs (Abs (Var (V:=(V *) *) (t:=tt) (none tt V *)))))
.
unfold substar in H.
simpl in H.
unfold inj in H.
simpl in H.

transitivity(
(App
     (App
  (Abs
         (Abs
            (App
               (App
                  (Abs
                     (Abs
                        (Var (V:=(((V *) *) *) *) (t:=tt)
                           (^(^(some tt (A:=V *))) tt
                              (^(^(some tt (A:=V))) tt (none tt V *))))))
                  (Var (V:=(V *) *) (t:=tt)
                     (some tt (A:=V *) (t:=tt) (none tt V))))
               (Var (V:=(V *) *) (t:=tt) (none tt V *)))))       
u) v)
).
apply cp_App1.
apply cp_App1.
apply clos_refl_trans_1n_contains.
apply relorig.
auto.
clear H.
assert (H:= app_abs
  (Abs
      (Var (V:=(((V *) *) *) *) (t:=tt)
          (^(^(some tt (A:=V *))) tt
           (^(^(some tt (A:=V))) tt (none tt V *)))))
(Var (V:=(V *) *) (t:=tt)
                       (some tt (A:=V *) (t:=tt) (none tt V)))
).
unfold substar in H;
simpl in H.
transitivity (
(App
     (App
        (Abs
           (Abs
              (App
                 (Abs (Var (V:=((V *) *) *) (t:=tt) (none tt (V *) *)))
                 (Var (V:=(V *) *) (t:=tt) (none tt V *))))) u) v)
).
apply cp_App1.
apply cp_App1.
apply cp_Abs.
apply cp_Abs.
apply cp_App1.
apply clos_refl_trans_1n_contains.
apply relorig.
auto.
clear H.

assert (H:= app_abs 
  (Var (V:=((V *) *) *) (t:=tt) (none tt (opt tt (opt tt V ) )))
  (Var (V:=(V *) *) (t:=tt) (none tt V *))
).
unfold substar in H;
simpl in H.

transitivity (
(App
   (App
     (Abs
        (Abs

          (Var (V:=(V *) *) (t:=tt) (none tt V *))

)) u) v)
).
apply cp_App1.
apply cp_App1.
apply cp_Abs.
apply cp_Abs.
apply clos_refl_trans_1n_contains.
apply relorig.
auto.
clear H.

assert (H:= app_abs 
  (Abs (Var (V:=(V *) *) (t:=tt) (none tt V *)))
u
).
unfold substar in H;
simpl in H.

transitivity (
(App  
  (Abs (Var (V:=V *) (t:=tt) (none tt V)))
v)
).
apply cp_App1.
apply clos_refl_trans_1n_contains.
apply relorig.
auto.
clear H.
apply clos_refl_trans_1n_contains.
apply relorig.
apply app_abs.
Qed.

Next Obligation.
Proof.
  intros; simpl.
  induction n.
  simpl.
  unfold ULCsucc.
  apply app_abs_red.
  unfold substar;
  simpl.
  unfold inj;
  simpl.
  apply cp_Abs.
  apply cp_Abs.
  unfold inj;
  simpl.
  apply cp_App2.

apply App1_app_abs.
unfold substar;
simpl.
apply app_abs_red.
sim.
reflexivity.

simpl.
unfold ULCsucc.
simpl.
apply app_abs_red.
sim.
rewrite rename_rename.
simpl.
sim.
unfold substar;
simpl.
apply cp_Abs.
apply cp_Abs.
apply App2_App1_app_abs.
sim.
apply cp_App2.
apply app_abs_red.
sim.
apply cp_App2.
apply beta_eq.
rewrite subst_rename.
simpl.
rewrite subst_subst.
simpl.
clear IHn.
generalize dependent V.

induction n.
reflexivity.
simpl; intros.
rewrite IHn.
auto.
Qed.

Next Obligation. (* zero? 0 --> true *)
Proof.
  intros; simpl.
  unfold ULC_zero.
  apply app_abs_red.
  unfold substar.
  simpl.
  unfold inj;
  simpl.
  apply App1_app_abs.
  unfold substar.
  simpl.
  apply app_abs_red.
  unfold substar.
  simpl.
  reflexivity.
Qed.
Next Obligation. (* zero? (n+1) --> false *)
Proof.
  intros; simpl.
induction n.
apply app_abs_red.
unfold substar.
simpl.
apply App1_app_abs. (* here choice *)
unfold substar.
simpl.
apply app_abs_red.
unfold substar.
simpl.
apply app_abs_red.
unfold substar;
simpl.
reflexivity.


(*

transitivity(
(App (ULC_zero V)
           (Abs
              (Abs
                 (App
                    (Var (V:=(V * ) * ) (t:=tt)
                       (some tt (A:=V * ) (t:=tt) (none tt V)))
                    (App
                       (App (ULC_Nat n (V * ) * )
                          (Var (V:=(V * ) * ) (t:=tt)
                             (some tt (A:=V * ) (t:=tt) (none tt V))))
                       (Var (V:=(V * ) * ) (t:=tt) (none tt V * )))))))
); auto.
*)
apply app_abs_red.
unfold substar;
simpl.
unfold ULC_zero;
simpl.
apply App1_app_abs.
unfold substar;
simpl.
unfold inj; 
simpl.
unfold ULC_Nat_alt in IHn.
simpl in IHn.
unfold inj;
simpl.
apply app_abs_red;
sim.
apply app_abs_red;
sim.
reflexivity.
Qed.
Obligation 14. (* pred 0 --> 0 *)
Proof.
simpl; intros.
apply app_abs_red;
unfold substar;
simpl.
unfold inj;
simpl.
apply cp_Abs.
apply cp_Abs.
apply App1_App1_app_abs.
unfold substar;
simpl.
apply App1_app_abs.
unfold substar;
simpl.
apply app_abs_red;
unfold substar;
simpl.
reflexivity.
Qed.
Obligation 15. (* rec g --> g (rec g) *) 
Proof.
simpl.
intros V t g.
apply App1_app_abs.
unfold substar;
simpl.
unfold inj; simpl.
apply app_abs_red;
unfold substar;
simpl.
reflexivity.
Qed.
Next Obligation. (* pred (n+1) --> n *)
simpl.
intros V n.

apply app_abs_red.
sim. Print ULC_Nat_noredex_rename.
rew (ULC_Nat_noredex_rename n (some tt (A:=V)) tt).
rew (ULC_Nat_noredex_rename n (some tt (A:=opt tt V)) tt).
simpl in *.
unfold lift; 
simpl.

apply Abs_Abs_App1_App1_app_abs.
sim.
unfold lift;
simpl.
apply Abs_Abs_App1_app_abs.
sim.
rewrite subst_subst.
sim.
apply Abs_Abs_App1_app_abs.
sim.
apply Abs_Abs_app_abs.
sim.
apply Abs_Abs_app_abs.
sim.
rewrite <- subst_shift_shift.

rewrite H'.
rewrite rename_rename.
induction n.

apply app_abs_red.
unfold substar;
simpl.
unfold inj;
simpl.
unfold ULC_Nat_alt.
apply cp_Abs.
apply cp_Abs.
apply App1_App1_app_abs.
unfold substar;
simpl.
unfold inj; simpl.
apply App1_app_abs.
sim.
apply App1_app_abs.
sim.
apply app_abs_red;
sim.
apply app_abs_red.
sim.
apply app_abs_red.
sim.
reflexivity.

unfold ULC_Nat_nox in *.
simpl.
apply app_abs_red.
sim.
apply Abs_Abs_App1_App1_app_abs.
sim.
rewrite rename_rename.
simpl.
apply Abs_Abs_App1_App1_Abs_app_abs.
sim.
apply Abs_Abs_App1_app_abs.
sim.
apply Abs_Abs_app_abs.
sim.
apply Abs_Abs_app_abs.
sim.
apply Abs_Abs_App1_app_abs.
sim.
apply Abs_Abs_app_abs;
sim.
apply cp_Abs.
apply cp_Abs.
apply cp_App2.
rewrite rename_subst.
rewrite subst_rename.
rewrite subst_rename.

simpl.
rewrite subst_subst.
unfold inj.

fin.
simpl.

rewrite rename_rename.
rewrite subst_shift_shift.


induction n.
simpl.
apply app_abs_red.
sim.
reflexivity.

rewrite <- IHn0.



apply Abs_app_abs;
sim.
apply App1_app_abs;
sim.
apply app_abs_red;
sim.
apply cp_App2.

apply beta_eq.


transitivity (
App (ULC_Nat_noredex n V tt) (Var (some tt (none tt V)))
).

Focus 2.
induction n.
assert (H:=app_abs_red).
simpl in H.
apply H.

apply app_abs_red.


rewrite rename_rename.
apply app_abs_red;
sim.
rewrite pow_subst.
sim.

apply cp_App2.
unfold pow.
simpl.
apply App1_app_abs.
apply cp_App1.

unfold substar;
simpl.
unfold inj;
simpl.

repeat rewrite <- lift_rename.
repeat rewrite <- ulc_nats_lemma.
unfold lift; simpl.

apply Abs_Abs_App1_App1_app_abs.
unfold substar; 
simpl.
unfold inj;
simpl.
rewrite <- ulc_nats_lemma.
simpl.

apply Abs_Abs_App1_App1_Abs_app_abs.
unfold substar; 
simpl.
unfold inj;
simpl.
rewrite <- lift_rename.
rewrite <- ulc_nats_lemma.
simpl.
apply Abs_Abs_App1_app_abs.
unfold substar; 
simpl.
unfold inj;
simpl.
rewrite <- ulc_nats_lemma.
simpl.

apply Abs_Abs_app_abs.
unfold substar; 
simpl.
unfold inj;
simpl.
rewrite <- ulc_nats_lemma.
simpl.

apply Abs_Abs_app_abs.
unfold substar; 
simpl.
unfold inj;
simpl.

generalize V.
clear V.
induction n.

Focus 1.
intro V.
apply Abs_Abs_App1_App1_app_abs.
unfold substar; simpl.

apply Abs_Abs_App1_app_abs.
unfold substar; simpl.

apply Abs_Abs_app_abs.
unfold substar; simpl.
reflexivity.

intro V.
simpl.
assert (H:= IHn (opt tt (opt tt V))).
clear IHn.


transitivity (
(Abs
     (Abs
        (App
           (Var (V:=(V *) *) (t:=tt) (some tt (A:=V *) (t:=tt) 
        (none tt V)))
           (App
              (App 

(Abs
         (Abs
            (App
               (App
                  (App (ULC_Nat n (((V *) *) *) *)
                     (Abs
                        (Abs
                           (App
                              (Var (V:=(((((V *) *) *) *) *) *) (t:=tt)
                                 (none tt ((((V *) *) *) *) *))
                              (App
                                 (Var (V:=(((((V *) *) *) *) *) *) (t:=tt)
                                    (some tt (A:=((((V *) *) *) *) *) 
 (t:=tt)
                                       (none tt (((V *) *) *) *)))
                                 (Var (V:=(((((V *) *) *) *) *) *) (t:=tt)
                                    (some tt (A:=((((V *) *) *) *) *) 
  (t:=tt)
                                       (some tt (A:=(((V *) *) *) *) 
 (t:=tt)
                                          (some tt (A:=((V *) *) *) 
 (t:=tt)
                                             (none tt (V *) *))))))))))
                  (Abs
                     (Var (V:=((((V *) *) *) *) *) (t:=tt)
                        (some tt (A:=(((V *) *) *) *) (t:=tt)
                           (none tt ((V *) *) *)))))
               (Var (V:=(((V *) *) *) *) (t:=tt)
                  (some tt (A:=((V *) *) *) (t:=tt) (none tt (V *) *))))))


               (Var (V:=(V *) *) (t:=tt)
                    (some tt (A:=V *) (t:=tt) (none tt V))))
              (Var (V:=(V *) *) (t:=tt) (none tt V *))))))
).



apply Abs_Abs_App1_App1_app_abs.
unfold substar; simpl.
unfold inj;
simpl.
rewrite <- ulc_nats_lemma.



apply Abs_Abs_App1_App1_Abs_app_abs.
unfold substar; 
simpl.
unfold inj;
simpl.
rewrite <- lift_rename.
rewrite <- ulc_nats_lemma.
simpl.

apply Abs_Abs_App1_app_abs.
unfold substar; 
simpl.
unfold inj;
simpl.

rewrite <- ulc_nats_lemma.
simpl.

apply Abs_Abs_app_abs.
unfold substar; 
simpl.
unfold inj;
simpl.

rewrite <- ulc_nats_lemma.
simpl.

reflexivity.

apply cp_Abs.
apply cp_Abs.
apply cp_App2.




rewrite <- lift_rename.
rewrite <- ulc_nats_lemma.
simpl.




r

induction n.
Focus 1.
apply app_abs_red;
unfold substar;
simpl.
unfold inj; simpl.

apply Abs_Abs_App1_App1_app_abs.
unfold substar;
simpl.
unfold inj;
simpl.

apply Abs_Abs_App1_app_abs.
unfold substar;
simpl.
unfold inj;
simpl.

apply Abs_Abs_App1_app_abs.
unfold substar;
simpl.
unfold inj;
simpl.

apply Abs_Abs_app_abs.
unfold substar;
simpl.
unfold inj;
simpl.

apply Abs_Abs_app_abs.
unfold substar;
simpl.
unfold inj;
simpl.

apply Abs_Abs_App1_App1_app_abs.
unfold substar;
simpl.
unfold inj;
simpl.

apply Abs_Abs_App1_app_abs.
unfold substar;
simpl.
unfold inj;
simpl.

apply Abs_Abs_app_abs.
unfold substar;
simpl.
unfold inj;
simpl.

reflexivity.

simpl.


apply app_abs_red.
unfold substar;
simpl.
unfold inj;
simpl.
rewrite <- lift_rename.
rewrite <- lift_rename.
rewrite <- ulc_nats_lemma.
rewrite <- ulc_nats_lemma.
simpl.

unfold lift;
simpl.
assert (H:=app_abs
(Abs
              (App
                 (Var (V:=(((V *) *) *) *) (t:=tt)
                    (some tt (A:=((V *) *) *) (t:=tt)
                         (none tt (V *) *)))
                   (App
                   (App (ULC_Nat n (((V *) *) *) *)
                         (Var (V:=(((V *) *) *) *) (t:=tt)
                           (some tt (A:=((V *) *) *) (t:=tt)
                              (none tt (V *) *))))
                     (Var (V:=(((V *) *) *) *) (t:=tt)
                          (none tt (opt tt (opt tt V)) *)))))


(Abs
                    (Abs
                       (App
                          (Var (V:=(((V *) *) *) *) (t:=tt)
                             (none tt ((V *) *) *))
                          (App
                             (Var (V:=(((V *) *) *) *) (t:=tt)
                                (some tt (A:=((V *) *) *) (t:=tt)
                                   (none tt (V *) *)))
                             (Var (V:=(((V *) *) *) *) (t:=tt)
                                (some tt (A:=((V *) *) *) (t:=tt)
                                   (some tt (A:=(V *) *) (t:=tt)
                                      (some tt (A:=V *) (t:=tt) 
                (none tt V)))))))))

).
unfold substar in H;
simpl in H.
unfold inj in H;
simpl in H.
rewrite <- ulc_nats_lemma in H.
unfold lift in H;
simpl in H.

transitivity (
(Abs
     (Abs
        (App
           (App
              

(Abs
         (App
            (Abs
               (Abs
                  (App
                     (Var (V:=((((V *) *) *) *) *) (t:=tt)
                        (none tt (((V *) *) *) *))
                     (App
                        (Var (V:=((((V *) *) *) *) *) (t:=tt)
                           (some tt (A:=(((V *) *) *) *) (t:=tt)
                              (none tt ((V *) *) *)))
                        (Var (V:=((((V *) *) *) *) *) (t:=tt)
                           (some tt (A:=(((V *) *) *) *) (t:=tt)
                              (some tt (A:=((V *) *) *) (t:=tt)
                                 (some tt (A:=(V *) *) (t:=tt)
                                    (some tt (A:=V *) (t:=tt) 
                 (none tt V))))))))))
            (App
               (App (ULC_Nat n ((V *) *) *)
                  (Abs
                     (Abs
                        (App
                           (Var (V:=((((V *) *) *) *) *) (t:=tt)
                              (none tt (((V *) *) *) *))
                           (App
                              (Var (V:=((((V *) *) *) *) *) (t:=tt)
                                 (some tt (A:=(((V *) *) *) *) (t:=tt)
                                    (none tt ((V *) *) *)))
                              (Var (V:=((((V *) *) *) *) *) (t:=tt)
                                 (some tt (A:=(((V *) *) *) *) (t:=tt)
                                    (some tt (A:=((V *) *) *) (t:=tt)
                                       (some tt (A:=(V *) *) (t:=tt)
                                          (some tt (A:=V *) (t:=tt)
                                             (none tt V)))))))))))
               (Var (V:=((V *) *) *) (t:=tt) (none tt (V *) *)))))


              (Abs
                 (Var (V:=((V *) *) *) (t:=tt)
                    (some tt (A:=(V *) *) (t:=tt) (none tt V *)))))
           (Abs (Var (V:=((V *) *) *) (t:=tt) (none tt (V *) *))))))
).

Focus 1.
apply cp_Abs.
apply cp_Abs.
apply cp_App1.
apply cp_App1.
apply clos_refl_trans_1n_contains.
apply relorig.
apply H.
clear H.

apply Abs_Abs_App1_app_abs.
unfold substar;
simpl.
unfold inj; simpl.
rewrite <- ulc_nats_lemma.
apply Abs_Abs_App1_app_abs.
unfold substar;
simpl.
unfold inj; simpl.
rewrite <- lift_rename.
rewrite <- ulc_nats_lemma.
unfold lift; simpl.

apply Abs_Abs_app_abs;
unfold substar;
simpl.
rewrite <- ulc_nats_lemma.
unfold inj; simpl.
apply Abs_Abs_app_abs;
unfold substar;
simpl.
rewrite <- ulc_nats_lemma.
unfold inj; simpl.




apply 
Abs_Abs_App1_App1_Abs_app_abs.
unfold substar;
simpl.
unfold inj;
simpl.
unfold lift;
simpl.
rewrite <- lift_rename.
rewrite <- ulc_nats_lemma.

apply Abs_Abs_App1_app_abs.
unfold substar;
simpl.
unfold inj;
simpl.
rewrite <- ulc_nats_lemma.
unfold lift; simpl.

apply Abs_Abs_app_abs.
unfold substar;
simpl.
unfold inj;
simpl.
rewrite <- ulc_nats_lemma.
apply Abs_Abs_app_abs.
unfold substar;
simpl.
unfold inj;
simpl.
rewrite <- ulc_nats_lemma.

simpl.

unfold ULC_Nat.
reflexivity.
induction n.
simpl.
un

Obligation 17.
simpl; intros.



Obligation 18.
Proof.
simpl.
intros V t g z H H1.

assert False.
Focus 2.
intuition.

dependent induction z.

Focus 2.
inversion H1.

inversion H1.

dependent induction H1.
subst.

assert (FF:= H _ g (App (ULC_fix V) g)).
intuition.
inversion H1.
assert (FF:= H _ g (App (ULC_fix V) g)).
intuition.

intuition.



Check inj_pair2.

rewrite <- (inj_pair2 _ _ _ _ _ H4).
rewrite  (inj_pair2 _ _ _ _ _ H3).

rewrite <- (inj_pair2 _ _ _ _ _ H4) in H0.
rewrite (inj_pair2 _ _ _ _ _ H3) in H0.

rewrite (inj_pair2 _ _ _ _ _ H3).

(*rewrite <- (inj_pair2 _ _ _ _ _ H).*)
assert (h := inj_pair2 _ _ _ _ _ H4).
rewrite <- (inj_pair2 _ _ _ _ _ H4) in H0.


rewrite (
rewrite <- (inj_pair2 _ _ _ _ _ H).


Check
apply App2_app_abs.
unfold substar;
simpl.
unfold inj; simpl.
apply App1_app_abs.
subst.


Obligation 15.
Proof.
simpl; intros.
apply app_abs_red.
unfold substar;
simpl.
unfold inj;
simpl.
apply app_abs_red;
unfold substar;
unfold ULC_fix.
simpl.
rewrite subst_rename.
simpl.
rewrite subst_var_eta.
apply cp_App2.

rewrite subst_rename.

reflexivity.
rewrite rename_lift.
simpl.

Next Obligation.
Proof.
  simpl; intros.
  generalize V.
  clear V.
  induction n.
  simpl.
  intro V.
assert (H:= app_abs
(Abs
    (Var (V:=(((V *) *) *) *) (t:=tt)
            (none tt (opt tt (opt tt V)) *)))
(Var (V:=(V *) *) (t:=tt)
                       (some tt (A:=V *) (t:=tt) (none tt V)))

).
  unfold substar in H;
  simpl in H.

transitivity (
(App (ULC_pred V)
     (Abs
        (Abs
           (App
              (Var (V:=(V *) *) (t:=tt)
                 (some tt (A:=V *) (t:=tt) (none tt V)))
              (App
                (Abs (Var (V:=((V *) *) *) (t:=tt) (none tt (V *) *)))
                 (Var (V:=(V *) *) (t:=tt) (none tt V *)))))))
).
apply cp_App2.
apply cp_Abs.
apply cp_Abs.
apply cp_App2.
apply cp_App1.
apply clos_refl_trans_1n_contains.
apply relorig.
apply H.
clear H.
apply app_abs_red.
unfold substar;
simpl.
unfold inj;
simpl.
apply cp_Abs.
apply cp_Abs.
unfold lift;
simpl.
apply App1_App1_app_abs.
unfold substar;
simpl.
unfold inj; simpl.
unfold lift; simpl.
apply App1_app_abs.
unfold substar;
simpl.
apply App1_app_abs.
unfold substar;
simpl.
apply app_abs_red;
unfold substar;
simpl.
apply app_abs_red;
unfold substar;
simpl.
apply App1_app_abs;
unfold substar;
simpl.
apply app_abs_red;
unfold substar;
simpl.
reflexivity. (* end of base case *)

simpl.
intro V.
assert (H':= IHn (opt tt (opt tt V))).

transitivity (
(Abs
     (Abs
        (App
    (Var (V:=(V *) *) (t:=tt) (some tt (A:=V *) (t:=tt) (none tt V)))
           (App
              (App 
(App (ULC_pred (V *) *)
          (Abs
             (Abs
                (App
                   (Var (V:=(((V *) *) *) *) (t:=tt)
            (some tt (A:=((V *) *) *) (t:=tt) (none tt (V *) *)))
                   (App
                      (App (ULC_Nat n (((V *) *) *) *)
                         (Var (V:=(((V *) *) *) *) (t:=tt)
                            (some tt (A:=((V *) *) *) (t:=tt)
                               (none tt (V *) *))))
          (Var (V:=(((V *) *) *) *) (t:=tt) (none tt ((V *) *) *)))))))
                 (Var (V:=(V *) *) (t:=tt)
                    (some tt (A:=V *) (t:=tt) (none tt V))))
              (Var (V:=(V *) *) (t:=tt) (none tt V *))))))
).

Focus 2.
apply cp_Abs.
apply cp_Abs.
apply cp_App2.
apply cp_App1.
apply cp_App1.
apply H'. (* end 2 *)

clear H'.
clear IHn.

apply app_abs_red;
unfold substar;
simpl.

apply cp_Abs.
apply cp_Abs.
unfold ULC_pred;
unfold inj; 
simpl.

apply App1_App1_app_abs;
unfold substar;
simpl.
rewrite <- lift_rename.
rewrite <- lift_rename.
rewrite <- ulc_nats_lemma.
rewrite <- ulc_nats_lemma.
rewrite <- ulc_nats_lemma.
unfold inj;
simpl.
apply App1_app_abs;
unfold substar;
simpl.
rewrite <- ulc_nats_lemma.
unfold inj;
simpl.
apply App1_app_abs;
unfold substar;
simpl.
unfold inj;
simpl.
apply app_abs_red;
unfold substar;
simpl.
unfold inj;
simpl.
rewrite <- lift_rename.
rewrite <- ulc_nats_lemma.
rewrite <- ulc_nats_lemma.
apply app_abs_red;
unfold substar;
simpl.
unfold inj;
simpl.



apply cp_App1.

apply ap


 
  unfold inj; 
  simpl.
  apply cp_Abs.
  apply cp_Abs.
  
  reflexivity.






V))) tt (none tt V *))))))

).

transitivity (
(App
     (Abs
         (App
            (App (ULC_Nat n (V *) *)
               (Var (V:=(V *) *) (t:=tt)
                  (some tt (A:=V *) (t:=tt) (none tt V))))
            (App
               (Var (V:=(V *) *) (t:=tt)
                  (some tt (A:=V *) (t:=tt) (none tt V)))
               (Var (V:=(V *) *) (t:=tt) (none tt V *))))
       [*:=Abs
             (Abs
                (Abs
                   (Var (V:=((V *) *) *) (t:=tt)
                      (^(^(some tt (A:=V))) tt (none tt V *)))))])
     (Abs
        (Abs
           (Var (V:=(V *) *) (t:=tt) (some tt (A:=V *) (t:=tt) 
(none tt V))))))
).
apply cp_App1.
apply clos_refl_trans_1n_contains.
apply relorig.
apply app_abs.
clear H.
unfold substar.
simpl.
apply app_abs_red.
simpl.
unfold substar;
simpl.

unfold substar in H;
simpl in H.
unfold inj in H;
simpl in H.

assert (H:=app_abs
(Abs
      (App
         (App (ULC_Nat n (V *) *)
           (Var (V:=(V *) *) (t:=tt)
               (some tt (A:=V *) (t:=tt) (none tt V))))
       (App
          (Var (V:=(V *) *) (t:=tt)
                (some tt (A:=V *) (t:=tt) (none tt V)))
           (Var (V:=(V *) *) (t:=tt) (none tt V *)))))


).

  unfold ULCsucc.
  unfold ULC_Nat.

Definition PCF_ULC_rep := Build_PCF_rep PCF_ULC_rep_s.

Definition PCF_ULC_compilation := InitMor PCF_ULC_rep.

End ULC_syntax.
