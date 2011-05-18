Require Import Coq.Relations.Relations.

Require Export CatSem.PCF.PCF_types.
Require Export CatSem.CAT.ind_potype.
Require Export CatSem.CAT.rmonad.
Require Export CatSem.CAT.rmodule_TYPE.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Notation "^ f" := (lift (M:= opt_monad _) f) (at level 5).

Notation "'TY'" := PCF.types.
Notation "'Bool'" := PCF.Bool.
Notation "'Nat'" := PCF.Nat.

Notation "'IT'" := (ITYPE PCF.types).
Notation "a '~>' b" := (PCF.arrow a b) 
   (at level 69, right associativity).



(** Module PCF defines the syntax of PCF according to 
    "On full abstraction for PCF" (Hyland, Ong) *)

(** Notations:
    - [^f := opt_TP_map u f]    (similar to (option_map f))
    - [v //- f := rename f v]
    - [$ f := shift f ]
    - [v >>- f := shift f v ]
    - [v >>= f := subst v f ]
    - [v // N := substar v N ]   (substitution of one variable only) *)

(** 
  
    we define at first morphisms in (TY -> Type), 
    these morphisms are named with an underscore "_" at the end
    after defining beta reduction we upgrade them to morphisms in
    the category of preorders over TY  
*)



Ltac fin := simpl in *; intros; 
   autorewrite with fin; auto with fin.

Hint Unfold lift : fin.
Hint Extern 1 (_ = _) => f_equal : fin.

(** PCF constants *)
Inductive Consts : TY -> Type :=
 | Nats : nat -> Consts Nat
 | ttt : Consts Bool
 | fff : Consts Bool
 | succ : Consts (Nat ~> Nat)
 | preds : Consts (Nat ~> Nat)
 | zero : Consts (Nat ~> Bool)
 | condN: Consts (Bool ~> Nat ~> Nat ~> Nat)
 | condB: Consts (Bool ~> Bool ~> Bool ~> Bool).

(*Notation "V '*'" := (opt _ V) (at level 5).*)
(*Notation "V '**' u":= (opt_TP u V) (at level 5).*)

(** PCF terms *)
Inductive PCF (V: TY -> Type) : TY -> Type:=
 | Bottom: forall t, PCF V t
 | Const : forall t, Consts t -> PCF V t
 | Var : forall t, V t -> PCF V t
 | App : forall t s, PCF V (s ~> t) -> PCF V s -> PCF V t
 | Lam : forall t s, PCF (opt t V) s -> PCF V (t ~> s)
 | Rec : forall t, PCF V (t ~> t) -> PCF V t.


(** a nicer name for morphisms of families of preorders *)
(*Notation "'varmap'" := ipo_mor.*)


Reserved Notation "x //- f" (at level 42, left associativity).

(** functoriality of PCF (without order) *)
Fixpoint rename (V W: TY -> Type) (f: V ---> W) 
         (t:TY)(v:PCF V t): PCF W t :=
    match v with
    | Bottom t => Bottom W t
    | Const t c => Const W c
    | Var t v => Var (f t v)
    | App t s u v => App (u //- f) (v //- f)
    | Lam t s u => Lam (u //- (^f))
    | Rec t u => Rec (u //- f)
    end
where "v //- f" := (@rename _ _ f _ v).

(** injection of terms into terms with one variable more, of type u *)
Definition inj (u:TY)(V : TY -> Type)(t:TY)(v:PCF V t): PCF (opt u V) t :=
      v //- (@some TY u V) .


(** inject term in PCF V t in PCF (V* ) t *)
Definition _shift := 
fun (u : TY) (V W : TY -> Type) (f : forall t : TY, V t -> PCF W t)
  (t : TY) (v : opt u V t) =>
match v in (opt _ _ y) return (PCF (opt u W) y) with
| some t0 p => inj u (f t0 p)
| none => Var (V:=opt u W) (t:=u) (none u W)
end.

Notation "'$' f" := (@_shift _ _ _ f) (at level 30).

Notation "y >>- f" := (_shift f y) (at level 44).

(**  substitution *)
Reserved Notation "y >>= f" (at level  42, left associativity).

Fixpoint subst (V W: TY -> Type)(f: forall t, V t -> PCF W t) 
           (t:TY)(v:PCF V t) : PCF W t :=
    match v with
    | Bottom t => Bottom W t
    | Const t c => Const W c
    | Var t v => f t v
    | App t s u v => App (u >>= f) (v >>= f)
    | Lam t s u => Lam (u >>= $ f)
    | Rec t u => Rec (u >>= f)
    end
where "y >>= f" := (@subst _ _ f _ y).


(** substitution of one variable *)
Definition substar (u:TY) (V:TY -> Type) (M:PCF V u)  
       (*PCF V t0 := subst_  *) := subst
  (fun t (x0: opt u V t) => match x0 in (opt _ _ r ) 
                              return (PCF V r )with  
            | none => M
            | some _ v0 => Var v0
            end)  .


Notation "M [*:= N ]" := (substar N M) (at level 50).

(** now a lot of lemmata about interactions between the defined functions *)


Lemma rename_eq (V: TY -> Type)(t:TY)(v: PCF V t) 
  (W: TY -> Type) (f g: V ---> W)(H: forall t y, f t y = g t y):
           v //- f  = v //- g .
Proof. 
  intros V t v; induction v; simpl; auto.
  
  intros; rewrite H; auto.
  
  intros. rewrite (IHv1 W f g); auto.
  rewrite (IHv2 W f g); auto.
  
  intros. 
  set (H':= IHv _  (lift (M:=opt_monad _ ) f) 
                   (lift (M:=opt_monad _ ) g)).
  simpl in *.
  rewrite H'. auto.
  
  set (H'':= lift_eq (opt_monad t) H). auto.
  
  intros; rewrite (IHv W f g H); auto.
Qed.

Lemma rename_id (V:TY -> Type)(t:TY)(v: PCF V t) 
  (f: V ---> V)(H: forall t y, f t y = y):
           v //- f = v.
Proof. 
  intros V t v; induction v; 
  intros f H;
  simpl; auto.
  rewrite H; auto.
  rewrite IHv1; try rewrite IHv2; auto.
  rewrite IHv; auto. 
  unfold lift.
  intros t0 y; destruct y; simpl; try rewrite H; auto.
  rewrite IHv; auto.
Qed.


Hint Resolve rename_eq : fin.
Hint Rewrite rename_eq : fin.



Lemma rename_comp (V: TY -> Type) (t: TY) (v: PCF V t)
      (W Z: TY -> Type) (f: V ---> W) (g: W ---> Z):
      v //- (f ;; g) = 
           v //- f //- g.
Proof. 
  intros V t v; induction v; 
  simpl in *; auto.
  intros W Z f g; rewrite IHv1; rewrite IHv2; auto.
  intros W Z f g. 
  apply f_equal. 
  rewrite <- (IHv _ (opt t Z)).
  apply rename_eq.
  intros r z.
  set (H':= lift_lift (opt_monad t)).
  simpl in *.
  rewrite H'. auto.
  intros W Z f g; rewrite IHv; auto.
Qed.

Lemma shift_eq (u:TY) (V:TY -> Type )(t:TY)(v:opt u V t)
          (W: TY -> Type)(f g: forall t, V t -> PCF W t)
          (H: forall t z, f t z = g t z):
          v >>- f  = v >>- g .
Proof. 
  intros u V t v; 
  induction v; 
  simpl; intros; 
  try rewrite H; auto.
Qed.

Hint Resolve  rename_id shift_eq : fin.
Hint Rewrite  rename_id shift_eq : fin.

Lemma shift_var (u:TY)(V:TY -> Type)(t:TY)(v: opt u V t):
       v >>- (fun t z => Var z)  = Var v.
Proof. 
  induction v; 
  intros; simpl; 
  auto. 
Qed.

Hint Resolve shift_var : fin.
Hint Rewrite shift_var : fin.

 
Lemma var_lift_shift_eq (u:TY) (V:TY -> Type) (t: TY) (v: opt u V t)
     (W:TY -> Type) (f: V ---> W):
    Var (^f t v) = v >>- (fun t z => Var (f t z)).
Proof. 
  induction v; 
  simpl; intros; 
  auto. 
Qed.

Hint Resolve var_lift_shift_eq : fin.

Lemma shift_lift (u:TY) (V: TY -> Type) (t:TY)(v:opt u V t)
           (W Z:TY -> Type)(f: V ---> W) 
           (g: forall t, W t -> PCF Z t): 
   ^f t v >>- g = 
    v >>- (fun t x0 => g t (f t x0)).
Proof. 
  induction v; 
  simpl; intros; 
  auto. 
Qed.

Hint Resolve shift_lift : fin.
Hint Rewrite shift_lift : fin.

Lemma subst_eq (V: TY -> Type)(t:TY)(v:PCF V t) (W:TY -> Type)
       (f g: forall t, V t -> PCF W t)
       (H: forall t z, f t z = g t z) :
       v >>= f = v >>= g.
Proof. 
  induction v; 
  intros; simpl;  auto.
  
  try rewrite (IHv1 W f g);
  try rewrite (IHv2 W f g); 
  try rewrite (IHv W f g); auto.
  
  rewrite (IHv _ (_shift f) (_shift g)); auto.
  intros; apply shift_eq; auto.
  
  rewrite (IHv W f g); auto.
Qed.

Hint Resolve subst_eq : fin.
Hint Rewrite subst_eq : fin.

Program Instance subst_oid (V W : IT) : 
 Proper (equiv (Setoid:=mor_oid V (PCF W))==> 
         equiv (Setoid:=mor_oid (PCF V) (PCF W))) 
                (@subst V W).
Next Obligation.
Proof.
  red.
  simpl;
  intros;
  apply subst_eq;
  auto.
Qed.


Lemma subst_var (V:TY -> Type)(t:TY)(v:PCF V t):
        v >>= (@Var V) = v.
Proof. 
  induction v; intros; simpl; auto.
  rewrite IHv1. rewrite IHv2; auto.
  rewrite <- IHv at 2.
  apply f_equal. apply subst_eq.
  intros; apply shift_var.
  rewrite IHv; auto.
Qed.

Lemma subst_var_eta (V:TY -> Type)(t:TY)(v:PCF V t):
        v >>= (fun t z => Var z) = v.
Proof. 
  induction v; intros; simpl; auto.
  rewrite IHv1. rewrite IHv2; auto.
  rewrite <- IHv at 2.
  apply f_equal. apply subst_eq.
  intros; apply shift_var.
  rewrite IHv; auto.
Qed.

Lemma subst_var_eta2 (V:TY -> Type)(t:TY)(v:PCF V t):
        v >>= (fun t => @Var V t) = v.
Proof. 
  induction v; intros; simpl; auto.
  rewrite IHv1. rewrite IHv2; auto.
  rewrite <- IHv at 2.
  apply f_equal. apply subst_eq.
  intros; apply shift_var.
  rewrite IHv; auto.
Qed.


Lemma subst_eq_rename (V:TY -> Type)(t:TY)(v:PCF V t)
      (W:TY -> Type) (f: V ---> W):
        v //- f  = v >>= fun t z => Var (f t z).
Proof. 
  induction v; intros; simpl; auto.
  rewrite IHv1; rewrite IHv2; auto.
  rewrite IHv. apply f_equal. apply subst_eq.
  set (H':= var_lift_shift_eq).
  simpl in H'. intros;
  apply H'.
  rewrite IHv; auto.
Qed.


Lemma rename_term_inj (u:TY)(V:TY -> Type)(t:TY)(v:PCF V t) 
    (W: TY -> Type) (g: V ---> W):
      inj u v //- ^g  =  inj u (v //- g).
Proof. 
  induction v; simpl in *; intros; auto.
  rewrite IHv1; rewrite IHv2; auto.
  unfold inj. simpl.
  apply f_equal. 
  rewrite <- rename_comp.
  rewrite <- rename_comp.
  apply rename_eq.
  induction y; simpl; auto.
  rewrite IHv. unfold inj. 
  simpl. auto.
Qed.

Lemma rename_subst (V:TY -> Type) (t:TY)(v: PCF V t) 
     (W Z: TY -> Type)(f: V ---> PCF W) 
     (g: W ---> Z):
   v >>= f //- g = 
           v >>= fun t z => f t z //- g .
Proof. 
  induction v; intros; simpl in *; auto.
  rewrite IHv1; rewrite IHv2; auto.
  
  rewrite IHv. apply f_equal. apply subst_eq.
  induction z; simpl; auto.
  set (H':= rename_term_inj).
  simpl in *. apply H'.
  
  rewrite IHv. auto.
Qed.


Hint Unfold inj : fin.

Lemma subst_rename (V:TY -> Type) (t:TY)(v: PCF V t) 
     (W Z : TY -> Type) (f: V ---> W)
     (g: W ---> PCF Z):
    v //- f >>= g = 
            v >>= fun t z =>  g t (f t z).
Proof. 
  induction v; simpl; intros; auto.
  rewrite IHv1; rewrite IHv2; auto.
  
  rewrite IHv. apply f_equal.
  apply subst_eq. intros.
  apply shift_lift.
  
  rewrite IHv. auto.
Qed.

Hint Rewrite subst_rename rename_subst : fin.

Lemma rename_substar (V: TY -> Type)(s t:TY) (v:PCF (opt s V) t)
   (W:TY -> Type) (f: V ---> W) N:
       v [*:= N]  //- f = 
         (v //- ^f) [*:= (N //- f)].
Proof. 
  intros. unfold substar.
  rewrite rename_subst.
  rewrite subst_rename. 
  apply subst_eq. 
  intros t0 z; destruct z;  
  simpl; auto.
Qed.
       
Lemma subst_term_inj (u:TY)(V:TY -> Type)(t:TY)(v:PCF V t)
      (W:TY -> Type)
      (g: V ---> PCF W):
    (inj u v) >>= $ g = inj  _ (v >>= g).
Proof. 
  induction v; simpl; intros; auto.
  rewrite IHv1; rewrite IHv2; auto.
  
  unfold inj. simpl. apply f_equal.
  rewrite rename_subst.
  rewrite subst_rename.
  apply subst_eq.
  induction z; simpl; auto.
  set (H':=rename_term_inj);
  simpl in *. rewrite H'.
  apply f_equal.
  apply rename_eq. auto.  
  rewrite IHv; auto.
Qed.


Lemma subst_shift_shift (u:TY) (V:TY -> Type) (t:TY)(v:opt u V t)
 (W Z : TY -> Type)
 (f: V ---> PCF W)
 (g: W ---> PCF Z):
   (v >>- f)  >>= $ g = 
          v >>- fun t z => f t z >>= g .
Proof. 
  induction v; 
  simpl; intros; 
  try apply subst_term_inj; auto.
Qed.

Hint Resolve subst_shift_shift : fin.
Hint Rewrite subst_shift_shift : fin.


Lemma subst_subst (V:TY -> Type)(t:TY)(v:PCF V t) 
         (W Z : TY -> Type)
         (f:V ---> PCF W)(g:W ---> PCF Z):
  v >>= f >>= g = 
      v >>= fun t z => f t z >>= g.
Proof. 
  induction v; simpl; intros; auto.
  rewrite IHv1; rewrite IHv2; auto.
  
  rewrite IHv. apply f_equal.
  apply subst_eq.
  intros; simpl.
  apply subst_shift_shift.
  
  rewrite IHv; auto.
Qed.
 
Hint Resolve subst_var subst_subst : fin.
Hint Rewrite subst_subst : fin.


Lemma subst_substar (V W : IT) 
      (s t:TY) (M: PCF (opt s V) t) (N:PCF V s) 
      (f:forall t, V t -> PCF W t):
   M [*:=N]  >>= f = (M >>= _shift f) [*:= (N >>= f)].
Proof. 
  intros V W s t M N f.
  unfold substar. simpl.
  repeat rewrite subst_subst.
  apply subst_eq.
  intros t0 x.
  destruct x. unfold _shift.
  unfold inj. 
  simpl.
  rewrite subst_rename. simpl. 
  rewrite subst_var_eta. auto.
  simpl.
  apply subst_eq; auto.
Qed.

Existing Instance subst_oid.

Obligation Tactic := fin.


Section Relations_on_PCF.

Reserved Notation "x :> y" (at level 70).

Variable rel : forall (V:IT) t, relation (PCF V t).

Inductive propag (V: IT) 
       : forall t, relation (PCF V t) :=
| relorig : forall t (v v': PCF V t), rel v v' ->  v :> v'
| relApp1: forall (s t : TY)(M M' : PCF V (s ~> t)) N, 
       M :> M' -> App M N :> App M' N
| relApp2: forall (s t:TY)(M:PCF V (s ~> t)) N N',
      N :> N' -> App M N :> App M N'
| relLam: forall (s t:TY)(M M':PCF (opt s V) t),
      M :> M' -> Lam M :> Lam M'
| relRec: forall (t : TY)(M M' : PCF V (t ~> t)), 
      M :> M' -> Rec M :> Rec M'

where "x :> y" := (@propag _ _ x y). 

Notation "x :>> y" := 
  (clos_refl_trans_1n _ (@propag _ _ ) x y) (at level 50).


Variable V: IT.
Variables s t: TY.

(** these are some trivial lemmata  which will be used later *)

Lemma cp_App1 (M M': PCF V (s ~> t)) N :
    M :>> M' -> App M N :>> App M' N.
Proof. 
  intros. generalize N. 
  induction H. constructor.
  intros. constructor 2 with (App y N0); auto.
  constructor 2. auto.
Qed.

Lemma cp_App2 (M: PCF V (s ~> t)) N N':
    N :>> N' -> App M N :>> App M N'.
Proof. 
  intros. generalize M. 
  induction H. constructor.
  intros. constructor 2 with (App M0 y); auto.
  constructor 3. auto.
Qed.

Lemma cp_Lam (M M': PCF (opt s V) t ):
      M :>> M' -> Lam M :>> Lam M'.
Proof. 
  intros. induction H. constructor.
  constructor 2 with (Lam y); auto.
  constructor 4. auto.
Qed.

Lemma cp_Rec (M M': PCF V (t ~> t)) :
      M :>> M' -> Rec M :>> Rec M'.
Proof.
  intros. 
  induction H. 
  constructor.
  constructor 2 with (Rec y); auto.
  constructor 5. auto.
Qed.

End Relations_on_PCF.

(** Beta reduction *)

Reserved Notation "a >> b" (at level 70).


Inductive eval (V : IT): forall t, relation (PCF V t) :=
| app_abs : forall (s t:TY) (M: PCF (opt s V) t) N, 
               eval (App (Lam M) N) (M [*:= N])

| condN_t: forall n m,
    eval (App (App (App (Const _ condN) (Const _ ttt)) n) m)  n 

| condN_f: forall n m,
    eval (App (App (App (Const _ condN) (Const _ fff)) n) m)  m 

| condB_t: forall u v,
    eval (App (App (App (Const _ condB) (Const _ ttt)) u) v)  u 
| condB_f: forall u v,
    eval (App (App (App (Const _ condB) (Const _ fff)) u) v)  v
| succ_red: forall n,
     eval (App (Const _ succ) (Const _ (Nats n))) (Const _ (Nats (S n)))
| zero_t: 
     eval (App (Const _ zero) (Const _ (Nats 0))) (Const _ ttt)
| zero_f: forall n,
     eval (App (Const _ zero) (Const _ (Nats (S n)))) (Const _ fff)
| pred_Succ: forall n,
     eval (App (Const _ preds) 
              (App (Const _ succ)
                   (Const _ (Nats n))))
        (Const _ (Nats n))
| pred_z: 
     eval (App (Const _ preds) (Const _ (Nats 0))) (Const _ (Nats 0))
| rec_a : forall t g,
     eval (Rec g) (App g (Rec (t:=t) g)).


Definition eval_star := propag eval.

Definition eval_rel := 
   fun (V : IT) t => clos_refl_trans_1n _ (@eval_star V t).

Obligation Tactic := idtac.

Program Instance PCFEVAL_struct (V : IT) : ipo_obj_struct (PCF V) := {
 IRel t := @eval_rel V t
}.
Next Obligation.
Proof.
  constructor.
  constructor.
  assert (H':= @clos_rt_is_preorder _ (@eval_star V t)).
  unfold eval_rel in *.
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



Definition PCFE (V: IT) : IPO TY :=
    Build_ipo_obj (PCFEVAL_struct V ).

Program Instance Var_s (V : IT) : 
    ipo_mor_struct (a:=SM_ipo _ V) (b:=PCFE V) (Var (V:=V)).
Next Obligation.
Proof.
  intros V t.
  unfold Proper;
  red.
  simpl.
  intros x y H.
  induction H.
  reflexivity.
Qed.

Definition VAR V := Build_ipo_mor (Var_s V).

Program Instance subst_s (V W : IT) (f : SM_ipo _ V ---> PCFE W) :
   ipo_mor_struct (a:=PCFE V) (b:=PCFE W) (subst f).
Next Obligation.
Proof.
  intros V W f t.
  unfold Proper;
  red.
  intros x y H.
  generalize dependent W.
  induction H;
  simpl;
  intros. 
  constructor.
  transitivity (subst f y);
  try apply IHclos_refl_trans_1n.
  clear dependent z.

    generalize dependent W.
  induction H;
  simpl;
  intros.
  
  Focus 2.
  apply cp_App1.
  apply IHpropag.
  Focus 2.
  apply cp_App2.
  apply IHpropag.
  Focus 2.
  apply cp_Lam.
  simpl in *.
  apply (IHpropag _ (SM_ind 
            (V:=opt s V) (W:=PCFE (opt s W)) (fun t y => _shift f y))).
  Focus 2.
  apply cp_Rec.
  simpl in *.
  apply IHpropag.
  generalize dependent W.
    induction H;
    simpl;
    intros.
    apply clos_refl_trans_1n_contains.
    apply relorig.
    assert (H:=app_abs (subst (_shift f) M) (subst f N)).
    rewrite subst_substar.
    auto.
    
    apply clos_refl_trans_1n_contains.
    apply relorig.
    constructor.
    apply clos_refl_trans_1n_contains.
    apply relorig.
    constructor.
    apply clos_refl_trans_1n_contains.
    apply relorig.
    constructor.
    apply clos_refl_trans_1n_contains.
    apply relorig.
    constructor.
    apply clos_refl_trans_1n_contains.
    apply relorig.
    constructor.
    apply clos_refl_trans_1n_contains.
    apply relorig.
    constructor.
    apply clos_refl_trans_1n_contains.
    apply relorig.
    constructor.
    apply clos_refl_trans_1n_contains.
    apply relorig.
    constructor.
    apply clos_refl_trans_1n_contains.
    apply relorig.
    constructor.
    apply clos_refl_trans_1n_contains.
    apply relorig.
    constructor.
Qed.

Definition SUBST V W f := Build_ipo_mor (subst_s V W f).

Obligation Tactic := fin.

Program Instance PCFEM_s : RMonad_struct (SM_ipo TY) PCFE := {
   rweta := VAR;
   rkleisli a b f := SUBST f
}.
Next Obligation.
Proof.
  unfold Proper;
  red;
  fin.
Qed.

Definition PCFEM : RMonad (SM_ipo TY) := Build_RMonad PCFEM_s.

Lemma lift_rename V t (s : PCF V t) W (f : V ---> W) :
          s //- f = s >>= (f ;; @Var _).
Proof.
  intros V t s.
  induction s;
  simpl;
  fin.
  apply f_equal.
  rewrite IHs.
  apply subst_eq.
  clear dependent s0.
  intros r z;
  destruct z as [r z | ];
  fin.
Qed.

Hint Rewrite lift_rename : fin.


Lemma shift_shift r s V W (f : SM_ipo _ V ---> PCFEM W)
                (x : (opt r V) s) :
   sshift_ (P:=PCFEM) (W:=W) f x = x >>- f .
Proof.
  intros r  s V W f y.
  destruct y as [t y | ];
  simpl;
  unfold inj;
  fin.
Qed.

Hint Rewrite shift_shift : fin.
Hint Resolve lift_rename shift_shift : fin.



