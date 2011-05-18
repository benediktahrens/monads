
Require Export CatSem.CAT.cat_TYPE_option.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Automatic Introduction.

Notation "^ f" := (lift (M:= option_monad) f) (at level 5).

Ltac fin := simpl in *; intros; 
   autorewrite with fin; auto with fin.

Hint Unfold lift : fin.
Hint Extern 1 (_ = _) => f_equal : fin.

Notation "V *" := (option V) (at level 4).

Notation "'TT'" := TYPE.

Lemma l_eq (V W : TT) (f g : V -> W): 
   (forall v, f  v = g  v) ->
       (forall (v : option V), 
       lift (M:=option_monad) f v = ^g v).
Proof.
  intros.
  destruct v;
  unfold lift;
  simpl;
  auto. 
  rewrite H.
  auto.
Qed.

(*
Inductive ULC_ (V : Type) : Type := 
  | Var : V -> ULC_ V
  | Abs : ULC_ (option V) -> ULC_ V
  | App : ULC_ V -> ULC_ V -> ULC_ V.

Definition ULC_d (V : TT) : Type :=
      ULC_ (V tt).
Definition ULC (V : TT) : TT := 
       fun _ => ULC_d V.
*)

Inductive ULC (V : TT) : TT :=
  | Var : V -> ULC V 
  | Abs : ULC V* -> ULC V
  | App : ULC V -> ULC V -> ULC V.

Lemma App_eq V  (M M' N N': ULC V) :
  M = M' -> N = N' -> App M N = App M' N'.
Proof.
  intros.
  rewrite H.
  rewrite H0.
  auto.
Qed.

Fixpoint rename V W (f : V ---> W) (y : ULC V) : 
          ULC W :=
  match y in ULC _ return ULC W with
  | Var v => Var (f v)
  | Abs v => Abs (rename ^f v)
  | App s t => App (rename f s) (rename f t)
  end.

Definition inj V := rename (V:=V) (W:= V*) 
                (@Some V).

(*
Definition _shift_tac u (V W : TT) (f : V ---> ULC W) : 
         opt u V ---> ULC (opt u W).
simpl.
intros.
destruct X.
apply (inj u). apply f. apply v.
apply VAR. apply none.

Defined.
Print _shift_tac.
*)

Definition _shift (V W : TT) (f : V ---> ULC W) : 
         V*  ---> ULC (W*) :=
   fun v => 
   match v in (option _ ) return ULC (W *) with
   | Some p => inj (f p)
   | None => Var None
   end.

Fixpoint _subst V W (f : V ---> ULC W) (y : ULC V) : 
         ULC W :=
  match y in ULC _ return ULC W with
  | Var v => f v
  | Abs v => Abs (_subst (_shift f) v)
  | App s t => App (_subst f s) (_subst f t)
  end.

(*
Definition subst_map_tac (u : unit) (V : TT) (M : ULC V u) :
    opt u V ---> ULC V.
simpl. intros u V M t y.
destruct y.
apply (VAR v).
apply M.
Defined.
Print subst_map_tac.

Definition subst_map: forall (u : unit) (V : TT), 
    ULC V u -> V * ---> ULC V := 
fun (u : unit) (V : unit -> Type) (M : ULC V u) (t : unit) (X : V * t) =>
match X in (opt _ _ y) return (ULC V y) with
| some t0 v =>
    match t0 as u0 return (V u0 -> ULC V u0) with
    | tt => fun v0 : V tt => Var (V:=V) v0
    end v
| none => M
end.


Definition substar (u : unit) (V : TT) (M : ULC V u) :
           ULC (opt u V) ---> ULC V :=
 _subst (subst_map M).
*)

Definition substar (V : TT) (M : ULC V) :
           ULC V* ---> ULC V :=
 _subst (fun y : V* => match y with
         | None => M
         | Some v => Var v
         end).


Notation "M [*:= N ]" := (substar N M) (at level 50).

(** Notations for functions *)
Notation "y //- f" := (rename f y)
  (at level 42, left associativity).
Notation "y >- f" := (_shift f y) (at level 40).
Notation "y >>= f" := (_subst f y) 
  (at level 42, left associativity).

Lemma rename_eq : forall (V : TT) (v : ULC V) 
         (W : TT) (f g : V ---> W),
     (forall y, f y = g y) -> v //- f = v //- g.
Proof.
  intros V v.
  induction v;
  intros;
  simpl.
  rewrite H;
  auto.
  
  apply f_equal.
  apply IHv.
  simpl in *.
  intros.
  assert (H':= l_eq H y).
  simpl in *.
  rewrite <- H'.
  auto.

  rewrite (IHv1 _ _ _ H).
  rewrite (IHv2 _ _ _ H).
  auto.
Qed.

Hint Resolve rename_eq l_eq : fin.
Hint Rewrite rename_eq l_eq : fin.


Lemma rename_comp V (y : ULC V) W 
         (f : V ---> W) Z (g : W ---> Z):
 y //- (fun y => g (f y)) =  y //- f //- g.
Proof.
  intros V y.
  induction y;
  simpl; 
  intros;
  fin.

  apply f_equal.
  rewrite <- IHy.
  apply rename_eq.
  intros  y0.
  destruct y0; 
  fin.
Qed.

Lemma rename_id_eq V (y : ULC V) (f : V ---> V)
        (H : forall v, f v = v) : 
    y //- f = y.
Proof.
  intros V y.
  induction y;
  simpl; 
  intros;
  fin.
  apply f_equal.
  apply IHy.
  intros v;
  destruct v;
  fin. unfold lift. 
  fin.
Qed.

Lemma rename_id V (y : ULC V) : y //- id _ = y .
Proof.
  intros V y.
  apply rename_id_eq.
  fin.
Qed.

Lemma _shift_eq V W (f g : V ---> ULC W) 
     (H : forall v, f v = g v) (y : V*) : 
          y >- f = y >- g.
Proof.
  intros V W f g H v.
  destruct v;
  fin. 
Qed.

Hint Resolve  rename_id _shift_eq : fin.
Hint Rewrite  rename_id _shift_eq : fin.


Lemma shift_var (V : TT) (y : V*) :
       y >- @Var V = Var y.
Proof.
  intros V y.
  induction y;
  fin.
Qed.

Hint Resolve shift_var : fin.
Hint Rewrite shift_var : fin.

 
Lemma var_lift_shift V W 
    (f : V ---> W) (y : V*) :
     Var (^f y) = y >- (f ;; @Var _ ).
Proof.
  intros V W f y;
  induction y; fin.
Qed.

Hint Resolve var_lift_shift : fin.


Lemma shift_lift V W Z (f : V ---> W) 
         (g : W ---> ULC Z) (y : V*) :
      (^f y) >- g = y >- (f ;; g).
Proof.
  intros V W Z f g y.
  induction y; fin.
Qed.

Hint Resolve shift_lift : fin.
Hint Rewrite shift_lift : fin.

Lemma subst_eq V (y : ULC V) 
      W (f g : V ---> ULC W) 
       (H : forall y, f y = g y):  
      y >>= f = y >>= g.
Proof.
  intros V y.
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
    forall (v : ULC V), v >>= (@Var V) = v .
Proof.
  intros V y.
  induction y;
  fin.
  apply f_equal.
  rewrite <- IHy at 2.
  apply subst_eq.
  fin.
Qed.
  

Lemma subst_eq_rename V (v : ULC V) W 
            (f : V ---> W)  : 
     v //- f  = v >>= (f ;; Var (V:=W)).
Proof.
  intros V y.
  induction y;
  fin.
  apply f_equal.
  rewrite IHy.
  apply subst_eq.
  intros z;
  destruct z;
  fin.
Qed.

Lemma rename_shift  V W Z (f : V ---> ULC W) 
           (g : W ---> Z)  
       (y : V*) : 
    (y >- f) //- ^g = y >- (f ;; rename g).
Proof.
  intros V W Z f g y.
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

Lemma rename_subst V (v : ULC V) W Z (f : V ---> ULC W)
      (g : W ---> Z) : 
      (v >>= f) //- g  = v >>= (f ;; rename g).
Proof.
  intros V y.
  induction y;
  fin.
  rewrite IHy.
  apply f_equal.
  apply subst_eq.
  intros z;
  destruct z;
  simpl; auto.
  unfold inj.
  rewrite <- rename_comp.
  rewrite <- rename_comp.
  apply rename_eq.
  fin.
Qed.

Lemma subst_rename V (v : ULC V) W Z (f : V ---> W)
      (g : W ---> ULC Z) : 
      v //- f >>= g = v >>= (f ;; g).
Proof.
  intros V y.
  induction y;
  fin.
  apply f_equal.
  rewrite IHy.
  apply subst_eq.
  intros z;
  destruct z;
  fin.
Qed.


Lemma rename_substar V (v : ULC V*) W 
       (f : V ---> W) N:
     v [*:= N] //- f = (v //- ^f) [*:= N //- f ].
Proof.
  intros.
  unfold substar.
  rewrite rename_subst.
  rewrite subst_rename.
  apply subst_eq.
  intros z ; 
  destruct z ;  
  fin.
Qed.

Hint Rewrite subst_rename rename_subst : fin.


Hint Rewrite rename_shift : fin.
Hint Resolve rename_shift : fin.


Lemma subst_shift_shift V (v : V*)
         W Z (f: V ---> ULC W) (g: W ---> ULC Z):
    (v >- f) >>= (_shift g)  = 
             v >- (f ;; _subst g).
Proof.
  intros V v.
  induction v; 
  simpl; intros; 
  try apply subst_term_inj; auto.
  unfold inj.
  rewrite subst_rename. 
  fin.
Qed.

Hint Resolve subst_shift_shift : fin.
Hint Rewrite subst_shift_shift : fin.


Lemma subst_subst V (v : ULC V) W Z 
             (f : V ---> ULC W) 
             (g : W ---> ULC Z) :
     v >>= f >>= g = v >>= (f;; _subst g).
Proof.
  intros V y.
  induction y; 
  fin.
  apply f_equal.
  rewrite IHy.
  apply subst_eq.
  intros z;
  destruct z;
  fin.
  unfold inj. 
  fin.
Qed.


Lemma lift_rename V (s : ULC V) W (f : V ---> W) :
          s >>= (fun z => Var (f z)) = s //- f.
Proof.
  intros V y.
  induction y;
  fin.
  apply f_equal.
  rewrite <- IHy.
  apply subst_eq.
  intros z;
  destruct z;
  fin.
Qed.

Lemma rename_rename V W Z (f : V ---> W) 
        (g : W ---> Z) (v : ULC V) :
  v //- f //- g = v //- (f ;; g).
Proof.
  intros.
  repeat rewrite <- lift_rename.
  rewrite subst_subst.
  fin.
Qed.

Lemma subst_var_eta (V:TT) (v:ULC V):
        v >>= (fun z => Var z) = v.
Proof. 
  induction v; 
  intros; simpl; auto.
  rewrite <- IHv at 2.
  apply f_equal. 
  apply subst_eq.
  intros; apply shift_var.
  rewrite IHv1. 
  rewrite IHv2; auto.
Qed.

Lemma subst_substar (V W : TT) 
       (M: ULC V*) (N:ULC V) 
      (f : V ---> ULC W):
   M [*:=N]  >>= f = (M >>= _shift f) [*:= (N >>= f)].
Proof.
  intros V W M N f.
  unfold substar. 
  simpl.
  repeat rewrite subst_subst.
  apply subst_eq.
  intros y.
  simpl.
  destruct y. 
  unfold _shift.
  unfold inj. 
  simpl.
  rewrite subst_rename. 
  simpl. 
  assert (H:=subst_var_eta (f v)).
  simpl in *.
  rewrite <- H at 1.
  apply subst_eq.
  auto.
  auto.
Qed.

Hint Resolve subst_var subst_subst lift_rename : fin.
Hint Rewrite subst_subst lift_rename: fin.
