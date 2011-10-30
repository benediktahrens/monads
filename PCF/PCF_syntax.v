Require Export CatSem.PCF.PCF_types.
Require Export CatSem.CAT.cat_INDEXED_TYPE.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Notation "^ f" := (lift (M:= opt_monad _) f) (at level 5).

(*
Ltac fin := simpl in *; intros; 
   autorewrite with fin; auto with fin; simpl;
	try reflexivity.
*)

Section close_notation.

Notation "'TY'" := PCF.Sorts.
Notation "'Bool'" := PCF.Bool.
Notation "'Nat'" := PCF.Nat.

Notation "'IT'" := (ITYPE TY).
Notation "a '~>' b" := (PCF.Arrow a b) 
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
   autorewrite with fin; auto with fin; simpl;
	try reflexivity.

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
  intros V t v; 
  induction v; simpl; auto.
  intros; rewrite H; auto.
  
  intros. 
  rewrite (IHv1 W f g); auto.
  rewrite (IHv2 W f g); auto.
  
  intros.
  apply f_equal.
  apply IHv.
  intros.
  elim_opt;
  unfold lift;
  simpl;
  auto.
  apply f_equal.
  auto.  
  intros;
  simpl;
  apply f_equal;
  apply (IHv); 
  auto.
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
  intros; 
  rewrite IHv1; 
  rewrite IHv2; auto.
  intros W Z f g. 
  apply f_equal. 
  rewrite <- (IHv _ (opt t Z)).
  apply rename_eq.
  intros;
  elim_opt.
  intros; rewrite IHv; auto.
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
  red; 
  fin.
Qed.


Lemma subst_var (V:TY -> Type)(t:TY)(v:PCF V t):
        v >>= (@Var V) = v.
Proof. 
  induction v; 
  intros; simpl; auto.
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
  rewrite IHv. apply f_equal. 
  apply subst_eq.
  intros.
  assert (H:=var_lift_shift_eq).
  simpl in H.
  apply H.
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
  
  rewrite IHv. 
  apply f_equal. 
  apply subst_eq.
  intros.
  elim_opt.
  rew rename_term_inj.  
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
  simpl; intros; 
  elim_opt.
Qed.

Ltac opt := simpl; intros; elim_opt.
       
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
  opt.
  rew (rename_term_inj).
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

Hint Resolve subst_shift_shift subst_var subst_var_eta : fin.
Hint Rewrite subst_shift_shift subst_var subst_var_eta : fin.


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
  opt.
  unfold inj. 
  simpl.
  rewrite subst_rename. simpl. 
  rewrite subst_var_eta. auto.
Qed.

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

End close_notation.

Existing Instance subst_oid.


