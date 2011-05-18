
Require Export CatSem.CAT.cat_INDEXED_TYPE.
Require Export CatSem.TLC.TLC_types.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.


Notation "V * u" := (opt u V).
Notation "^ f" := (lift (M:= opt_monad _) f) (at level 5).
Notation "a '~>' b" := (TLCarrow a b) 
   (at level 69, right associativity).
Notation "'TY'" := TLCtypes.
Notation "'IT'" := (ITYPE TY).

Ltac fin := simpl in *; intros; 
   autorewrite with fin; auto with fin.
Ltac opt := simpl; intros; elim_opt; fin.

Hint Unfold lift : fin.
Hint Extern 1 (_ = _) => f_equal : fin.

Lemma l_eq (V W : TY -> Type) (f g : forall t, V t -> W t) r: 
   (forall t v, f t v = g t v) ->
       (forall t (v : opt r V t), 
       lift (M:=opt_monad r) f t v = ^g t v).
Proof.
  intros;
  elim_opt;
  unfold lift;
  simpl;
  repeat rew_hyp_2;
  auto. 
Qed.
   
Inductive TLC (V : ITYPE TY) : ITYPE TY :=
  | var : forall t, V t -> TLC V t
  | abs : forall r s, TLC (V * r) s -> TLC V (r ~> s)
  | app : forall r s, TLC V (r ~> s) -> TLC V r -> TLC V s.

Fixpoint _rename V W (f : V ---> W) t (y : TLC V t) : TLC W t :=
  match y with
  | var _ v => var (f _ v)
  | abs _ _  v => abs (_rename ^f v)
  | app _ _  s t => app (_rename f s) (_rename f t)
  end.

Definition _inj u V := _rename (V:=V) (W:=V * u) 
                (@some TY u V).

Hint Unfold _inj : fin.

Definition _shift (u : TY) (V W : IT) (f : V ---> TLC W) : 
         V * u ---> TLC (W * u) :=
   fun t v => 
   match v in (opt _ _ y) return (TLC (W * u) y) with
   | some t0 p => _inj u (f t0 p)
   | none => var (none u W)
   end.

Fixpoint _subst (V W : IT) (f : V ---> TLC W) t (y : TLC V t) : TLC W t :=
  match y with
  | var _ v => f _ v
  | abs _ _ v => abs (_subst (_shift f) v)
  | app _ _ s t => app (_subst f s) (_subst f t)
  end.


Definition _substar (u : TY) (V : IT) (M : TLC V u) :
           TLC (V * u) ---> TLC V :=
 _subst (fun t (y : opt u V t) => match y with
         | none => M
         | some _ v => var v
         end).

Notation "M [*:= N ]" := (_substar N M) (at level 40).


(** Notations for functions *)
Notation "y //- f" := (_rename f y)(at level 42, left associativity).
Notation "y >- f" := (_shift f y) (at level 40).
Notation "y >>= f" := (_subst f y) (at level 59, left associativity).

Hint Extern 1 (_ = _) => apply f_equal.

Lemma rename_eq : forall (V : IT) (t : TY) (v : TLC V t) 
         (W : IT) (f g : V ---> W),
     (forall t y, f t y = g t y) -> v //- f = v //- g.
Proof.
  induction v;
  cat;
  try apply f_equal.
  apply IHv.
  simpl; intros.
  
  intros.
  assert (H':= l_eq (r:=r) H).
  simpl in *.
  auto.

  rewrite (IHv1 _ _ _ H).
  rewrite (IHv2 _ _ _ H).
  auto.
Qed.

Hint Resolve rename_eq l_eq : fin.
Hint Rewrite rename_eq l_eq : fin.


Lemma rename_comp V t (y : TLC V t) W 
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
  opt.
Qed.

Lemma rename_id_eq V t (y : TLC V t) (f : V ---> V)
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
  intros t v;
  destruct v;
  fin. unfold lift. 
  fin.
Qed.

Lemma rename_id V t (y : TLC V t) : y //- id _ = y .
Proof.
  intros V t y.
  apply rename_id_eq.
  fin.
Qed.

Lemma _shift_eq u V W (f g : V ---> TLC W) 
     (H : forall t v, f t v = g t v) t (y : opt u V t) : 
          y >- f = y >- g.
Proof.
  opt.
Qed.

Hint Resolve  rename_id _shift_eq : fin.
Hint Rewrite  rename_id _shift_eq : fin.

Lemma shift_var u (V : IT) t (y : opt u V t) :
       y >- @var _ = var y.
Proof.
  opt.
Qed.

Hint Resolve shift_var : fin.
Hint Rewrite shift_var : fin.

 
Lemma var_lift_shift (u : TY) V W (f : V ---> W) t (y : opt u V t) :
     var (^f _ y) = y >- (f ;; @var _ ).
Proof.
  opt.
Qed.

Hint Resolve var_lift_shift : fin.


Lemma shift_lift u V W Z (f : V ---> W) 
         (g : W ---> TLC Z) t (y : opt u V t) :
      (^f _ y) >- g = y >- (f ;; g).
Proof.
  opt.
Qed.

Hint Resolve shift_lift : fin.
Hint Rewrite shift_lift : fin.

Lemma subst_eq V t (y : TLC V t) 
      W (f g : V ---> TLC W) 
       (H : forall t y, f t y = g t y):  y >>= f = y >>= g.
Proof.
  intros V t y.
  induction y;
  fin.
Qed.

Hint Resolve subst_eq : fin.
Hint Rewrite subst_eq : fin.

Obligation Tactic := unfold Proper; red; fin.

Program Instance subst_oid V W : 
 Proper (equiv ==> equiv (Setoid:=mor_oid (TLC V) (TLC W))) 
                (@_subst V W).

Lemma subst_var (V : IT) : 
    forall t (v : TLC V t), v >>= (@var V) = v .
Proof.
  intros V t y.
  induction y;
  fin.
  apply f_equal.
  rewrite <- IHy at 2.
  apply subst_eq.
  fin.
Qed.
  

Lemma subst_eq_rename V t (v : TLC V t) W (f : V ---> W)  : 
     v //- f  = v >>= f ;; var (V:=W).
Proof.
  intros V t y.
  induction y;
  fin.
  apply f_equal.
  rewrite IHy.
  apply subst_eq.
  opt.
Qed.

Lemma rename_shift a V W Z (f : V ---> TLC W) (g : W ---> Z) t 
       (y : opt a V t) : 
    (y >- f) //- ^g = y >- (f ;; _rename g).
Proof.
  intros a V W Z f g t y.
  induction y;
  fin.  
  unfold _inj.
  rewrite <- rename_comp.
  rewrite <- rename_comp.
  fin.
Qed.


Hint Rewrite rename_shift : fin.
Hint Resolve rename_shift : fin.

Hint Unfold _inj : fin.

Lemma rename_subst V t (v : TLC V t) W Z (f : V ---> TLC W)
      (g : W ---> Z) : 
      (v >>= f) //- g  = v >>= (f ;; _rename g).
Proof.
  intros V t y.
  induction y;
  fin.
  rewrite IHy.
  apply f_equal.
  apply subst_eq.
  intros t z;
  destruct z;
  simpl; auto.
  unfold _inj.
  rewrite <- rename_comp.
  rewrite <- rename_comp.
  apply rename_eq.
  fin.
Qed.

Lemma subst_rename V t (v : TLC V t) W Z (f : V ---> W)
      (g : W ---> TLC Z) : 
      v //- f >>= g = v >>= (f ;; g).
Proof.
  intros V t y.
  induction y;
  fin.
  apply f_equal.
  rewrite IHy.
  apply subst_eq.
  opt.
Qed.


Lemma rename_substar V u t (v : TLC (opt u V) t) W 
       (f : V ---> W) N:
     v [*:= N] //- f = (v //- ^f) [*:= N //- f ].
Proof.
  intros.
  unfold _substar.
  rewrite rename_subst.
  rewrite subst_rename.
  apply subst_eq.
  opt.
Qed.

Hint Rewrite subst_rename rename_subst rename_shift : fin.
Hint Resolve rename_shift : fin.

Lemma subst_shift_shift (u:TY) V (t:TY)(v : opt u V t)
         W Z (f: V ---> TLC W) (g: W ---> TLC Z):
    (v >- f) >>= (_shift g)  = 
             v >- (f ;; _subst g).
Proof.
  intros u V t v.
  induction v; 
  simpl; intros; 
  try apply subst_term_inj; auto.
  unfold _inj.
  rewrite subst_rename. 
  fin.
Qed.

Hint Resolve subst_shift_shift : fin.
Hint Rewrite subst_shift_shift : fin.


Lemma subst_subst V t (v : TLC V t) W Z (f : V ---> TLC W) 
             (g : W ---> TLC Z) :
     v >>= f >>= g = v >>= f;; _subst g.
Proof.
  intros V t y.
  induction y; 
  fin.
  apply f_equal.
  rewrite IHy.
  apply subst_eq.
  opt;
  unfold _inj;
  fin.
Qed.


Lemma subst_var_eta (V:TY -> Type)(t:TY)(v:TLC V t):
        v >>= (fun t z => var z) = v.
Proof. 
  induction v; intros; simpl; auto.

  rewrite <- IHv at 2.
  apply f_equal. apply subst_eq.
  intros; apply shift_var.
    rewrite IHv1. rewrite IHv2; auto.
Qed.

Lemma subst_substar (V W : IT) 
      (s t:TY) (M: TLC (V * s) t) (N:TLC V s) 
      (f:forall t, V t -> TLC W t):
   M [*:=N]  >>= f = (M >>= _shift f) [*:= (N >>= f)].
Proof. 
  intros V W s t M N f.
  unfold _substar. simpl.
  repeat rewrite subst_subst.
  apply subst_eq.
  opt.
  unfold _shift.
  unfold _inj. 
  simpl.
  rewrite subst_rename. simpl. 
  rewrite subst_var_eta. auto.
Qed.

Lemma lift_rename V t (s : TLC V t) W (f : V ---> W) :
          s >>= (fun t z => var (f t z)) = s //- f.
Proof.
  intros V t y.
  induction y;
  fin.
  apply f_equal.
  rewrite <- IHy.
  apply subst_eq.
  opt.
Qed.

Hint Resolve subst_var subst_var_eta subst_subst lift_rename : fin.
Hint Rewrite subst_subst lift_rename subst_var subst_var_eta : fin.

