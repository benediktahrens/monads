Require Export Relations.
Require Export cat_INDEXED_TYPE.
Require Export ind_potype.
(*
Require Export order_classes.
*)
Set Implicit Arguments.
Unset Strict Implicit.

Unset Automatic Introduction.

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

Module PCF.

(** the types of PCF *)
Inductive TY : Type := 
 | Bool : TY
 | Nat : TY
 | arrow: TY -> TY -> TY.

Notation "a '~>' b" := (arrow a b) (at level 69, right associativity).

(** we are in the category of indexed preorders over type TY *)
(*Notation "'ipo'" := (ipo_obj TY).*)

Notation "'IT'" := (ITYPE TY).

(** PCF constants *)
Inductive Consts : TY -> Type :=
 | Nats : nat -> Consts Nat
 | ttt : Consts Bool
 | fff : Consts Bool
 | succ : Consts (Nat ~> Nat)
 | zero : Consts (Nat ~> Bool)
 | condN: Consts (Bool ~> Nat ~> Nat ~> Nat)
 | condB: Consts (Bool ~> Bool ~> Bool ~> Bool).

Notation "V '*'" := (opt _ V) (at level 5).
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

(** a morphism extended to a family + one element, whose type is implicit *)
Notation "^ f" := (lift (M := opt_monad _) f) (at level 10).

Reserved Notation "x //- f" (at level 42, left associativity).

(** functoriality of PCF (without order) *)
Fixpoint rename_ (V W: TY -> Type) (f: V ---> W) 
         (t:TY)(v:PCF V t): PCF W t :=
    match v with
    | Bottom t => Bottom W t
    | Const t c => Const W c
    | Var t v => Var (f t v)
    | App t s u v => App (u //- f) (v //- f)
    | Lam t s u => Lam (u //- (^f))
    | Rec t u => Rec (u //- f)
    end
where "x //- f" := (@rename_ _ _ f _ x).

(** injection of terms into terms with one variable more, of type u *)
Definition inj_(u:TY)(V : TY -> Type)(t:TY)(v:PCF V t): PCF  V* t :=
      v //- (@some TY u V) .


(** inject term in PCF V t in PCF (V* ) t *)
Definition shift_ := 
fun (u : TY) (V W : TY -> Type) (f : forall t : TY, V t -> PCF W t)
  (t : TY) (v : V* t) =>
match v in (opt _ _ y) return (PCF (opt u W) y) with
| some t0 p => inj_ u (f t0 p)
| none => Var (V:=opt u W) (t:=u) (none u W)
end.

Notation "'$' f" := (@shift_ _ _ _ f) (at level 30).

Notation "x >>- f" := (shift_ f x) (at level 44).

(**  substitution *)
Reserved Notation "x >>= f" (at level  42, left associativity).

Fixpoint subst_ (V W: TY -> Type)(f: forall t, V t -> PCF W t) 
           (t:TY)(v:PCF V t) : PCF W t :=
    match v with
    | Bottom t => Bottom W t
    | Const t c => Const W c
    | Var t v => f t v
    | App t s u v => App (u >>= f) (v >>= f)
    | Lam t s u => Lam (u >>= $ f)
    | Rec t u => Rec (u >>= f)
    end
where "x >>= f" := (@subst_ _ _ f _ x).

Definition substar_map (u:TY) (V: TY -> Type) (M: PCF V u)
       (t:TY)(v:(opt u V) t) : PCF V t.
intros.
destruct v as [t v | ].
apply (Var v).
apply M.
Defined.




(** substitution of one variable *)
Definition substar (u:TY) (V:TY -> Type) (M:PCF V u)  
       (*PCF V t0 := subst_  *) := subst_
  (fun t (x0: opt u V t) => match x0 in (opt _ _ r ) 
                              return (PCF V r )with  
            | none => M
            | some _ v0 => Var v0
            end)  .

Notation "x // N " := (@substar _ _ N _ x) (at level 40).

(** now a lot of lemmata about interactions between the defined functions *)
Section Fusion_Laws.

Lemma rename_eq (V: TY -> Type)(t:TY)(v: PCF V t) 
  (W: TY -> Type) (f g: V ---> W)(H: forall t x, f t x = g t x):
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
  (f: V ---> V)(H: forall t x, f t x = x):
           v //- f = v.
Proof. 
  intros V t v; induction v; 
  intros f H;
  simpl; auto.
  rewrite H; auto.
  rewrite IHv1; try rewrite IHv2; auto.
  rewrite IHv; auto. 
  unfold lift.
  intros t0 x; destruct x; simpl; try rewrite H; auto.
  rewrite IHv; auto.
Qed.


Lemma rename_comp (V: TY -> Type) (t: TY) (v: PCF V t)
      (W X: TY -> Type) (f: V ---> W) (g: W ---> X):
      v //- (f ;; g) = 
           v //- f //- g.
Proof. 
  intros V t v; induction v; 
  simpl in *; auto.
  intros W X f g; rewrite IHv1; rewrite IHv2; auto.
  intros W X f g. 
  apply f_equal. 
  rewrite <- (IHv _ (opt t X)).
  apply rename_eq.
  intros r x.
  set (H':= lift_lift (opt_monad t)).
  simpl in *.
  rewrite H'. auto.
  intros W X f g; rewrite IHv; auto.
Qed.

Lemma shift_eq (u:TY) (V:TY -> Type )(t:TY)(v:opt u V t)
          (W: TY -> Type)(f g: forall t, V t -> PCF W t)
          (H: forall t x, f t x = g t x):
          v >>- f  = v >>- g .
Proof. 
  intros u V t v; 
  induction v; 
  simpl; intros; 
  try rewrite H; auto.
Qed.

Lemma shift_var (u:TY)(V:TY -> Type)(t:TY)(v: opt u V t):
       v >>- (fun t x => Var x)  = Var v.
Proof. 
  induction v; 
  intros; simpl; 
  auto. 
Qed.

Lemma var_lift_shift_eq (u:TY) (V:TY -> Type) (t: TY) (v: opt u V t)
     (W:TY -> Type) (f: V ---> W):
    Var (^f t v) = v >>- (fun t x => Var (f t x)).
Proof. 
  induction v; 
  simpl; intros; 
  auto. 
Qed.

Lemma shift_lift (u:TY) (V: TY -> Type) (t:TY)(v:opt u V t)
           (W X:TY -> Type)(f: V ---> W) 
           (g: forall t, W t -> PCF X t): 
   ^f t v >>- g = 
    v >>- (fun t x0 => g t (f t x0)).
Proof. 
  induction v; 
  simpl; intros; 
  auto. 
Qed.

Lemma subst_eq (V: TY -> Type)(t:TY)(v:PCF V t) (W:TY -> Type)
       (f g: forall t, V t -> PCF W t)
       (H: forall t x, f t x = g t x) :
       v >>= f = v >>= g.
Proof. 
  induction v; 
  intros; simpl;  auto.
  
  try rewrite (IHv1 W f g);
  try rewrite (IHv2 W f g); 
  try rewrite (IHv W f g); auto.
  
  rewrite (IHv _ (shift_ f) (shift_ g)); auto.
  intros; apply shift_eq; auto.
  
  rewrite (IHv W f g); auto.
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
      inj_ u v //- ^g  =  inj_ u (v //- g).
Proof. 
  induction v; simpl in *; intros; auto.
  rewrite IHv1; rewrite IHv2; auto.
  unfold inj_. simpl.
  apply f_equal. 
  rewrite <- rename_comp.
  rewrite <- rename_comp.
  apply rename_eq.
  induction x; simpl; auto.
  rewrite IHv. unfold inj_. 
  simpl. auto.
Qed.

Lemma rename_subst (V:TY -> Type) (t:TY)(v: PCF V t) 
     (W X: TY -> Type)(f: V ---> PCF W) 
     (g: W ---> X):
   v >>= f //- g = 
           v >>= fun t x => f t x //- g .
Proof. 
  induction v; intros; simpl in *; auto.
  rewrite IHv1; rewrite IHv2; auto.
  
  rewrite IHv. apply f_equal. apply subst_eq.
  induction x; simpl; auto.
  set (H':= rename_term_inj).
  simpl in *. apply H'.
  
  rewrite IHv. auto.
Qed.


Lemma subst_rename (V:TY -> Type) (t:TY)(v: PCF V t) 
     (W X:TY -> Type) (f: V ---> W)
     (g: W ---> PCF X):
    v //- f >>= g = 
            v >>= fun t x =>  g t (f t x).
Proof. 
  induction v; simpl; intros; auto.
  rewrite IHv1; rewrite IHv2; auto.
  
  rewrite IHv. apply f_equal.
  apply subst_eq. intros.
  apply shift_lift.
  
  rewrite IHv. auto.
Qed.

Lemma rename_substar (V: TY -> Type)(s t:TY) (v:PCF (opt s V) t)
   (W:TY -> Type) (f: V ---> W) N:
       v // N  //- f = 
         (v //- ^f) // (N //- f).
Proof. 
  intros. unfold substar.
  rewrite rename_subst.
  rewrite subst_rename. 
  apply subst_eq. 
  intros t0 x; destruct x;  
  simpl; auto.
Qed.
       
Lemma subst_term_inj (u:TY)(V:TY -> Type)(t:TY)(v:PCF V t)
      (W:TY -> Type)
      (g: V ---> PCF W):
    (inj_ u v) >>= $ g = inj_  _ (v >>= g).
Proof. 
  induction v; simpl; intros; auto.
  rewrite IHv1; rewrite IHv2; auto.
  
  unfold inj_. simpl. apply f_equal.
  rewrite rename_subst.
  rewrite subst_rename.
  apply subst_eq.
  induction x; simpl; auto.
  set (H':=rename_term_inj);
  simpl in *. rewrite H'.
  apply f_equal.
  apply rename_eq. auto.  
  rewrite IHv; auto.
Qed.


Lemma subst_shift_shift (u:TY) (V:TY -> Type) (t:TY)(v:opt u V t)
 (W X : TY -> Type)
 (f: V ---> PCF W)
 (g: W ---> PCF X):
   (v >>- f)  >>= $ g = 
          v >>- fun t z => f t z >>= g .
Proof. 
  induction v; 
  simpl; intros; 
  try apply subst_term_inj; auto.
Qed.

Lemma subst_subst (V:TY -> Type)(t:TY)(v:PCF V t) 
         (W X:TY -> Type)
         (f:V ---> PCF W)(g:W ---> PCF X):
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

End Fusion_Laws.


(** we define beta reduction in three steps 
  - beta_: beta reduction at the root only, 
           + compatibility with order on variables
  - propag: for given relation "rel",
      "propag rel" relates terms whose subterms are related by rel
          abbreviated by "p"
  - clos_refl_trans_1n (from std lib) speaks for itself
          abbreviated by "rt" *)
 
Section Relations_on_PCF.

Definition PCFrel := forall V t, relation (PCF V t).

Reserved Notation "x :> y" (at level 70).

Variable rel : forall V t, relation (PCF V t).

Inductive propag V 
       : forall t, relation (PCF V t) :=
| relorig : forall t (v v':PCF V t), rel v v' ->  v :> v'
| relApp1: forall (s t:TY)(M M':PCF V (s ~> t)) N, 
       M :> M' -> App M N :> App M' N
| relApp2: forall (s t:TY)(M:PCF V (s ~> t)) N N',
      N :> N' -> App M N :> App M N'
| relLam: forall (s t:TY)(M M':PCF (opt s V) t),
      M :> M' -> Lam M :> Lam M'
| relRec : forall (s:TY) (M M':PCF V (s ~> s)),
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

Lemma cp_Rec (M M': PCF V (t ~> t)):
      M :>> M' -> Rec M :>> Rec M'.
Proof. 
  intros.
  induction H. constructor.
  constructor 2 with (Rec y); auto.
  constructor 5. auto.
Qed.


End Relations_on_PCF.

(** Beta reduction *)

Section Beta_Relation.

(*
Inductive beta_ V (RV : IRel (A:=V)) : IRel (A:=PCF V) :=
| beta_beta: forall (s t:TY) (M: PCF (opt s V) t) N, 
          beta_ _ (App (Lam M) N) (M // N)
| beta_var: forall (t:TY) (x y:V t),
         irel x y -> beta_ _ (Var x) (Var y).
*)
(*
Definition beta := propag beta_.

Definition beta V (RV : IRel V) := propag (beta_ RV).


Definition betaS := 
   fun (V:ipo) t => clos_refl_trans_1n _ (@beta V t).

Program Instance BETA_struct (V:ipo) : ipo_obj_struct (PCF V) := {
 IRel t := @betaS V t
}.
Next Obligation.
Proof.
  constructor.
  constructor.
  set (H':= @clos_rt_is_preorder _ (@beta V t)).
  unfold betaS.
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



Program Definition BETA (V: ipo) : ipo :=
    Build_ipo_obj (BETA_struct V ). 
                                    
(*  Next Obligation.
    Proof. unfold betaS; apply Clos_RT_1n. Qed. *)
*)
End Beta_Relation.

(** upgrading the morphisms of (TY -> Type) to morphisms in 
    the cat of preorders over TY 
     - [rename_ => rename]
     - [subst_ => subst] 
*)

(** we show that if (rename f) is 
    compatible with a relation "rel" on PCF,
    then it is also compatible with "propag rel" and "clos_rt rel" 
   (cf. Section rename_bs )

   same for shift_ and subst_
*)

(** for subst_ the upgrading is more difficult than for rename_
    we first prove a lemma that says that 
      [ rt (p (rt (p rel))) <= rt (p rel) ]      
   called propag_clos_propag_clos                    *)
(*

Section Compat_with_Beta.

Notation "'rt'" := (clos_refl_trans_1n _) (at level 60).
Notation "'p'" := @propag (at level 60).

Section rename.

Section rename_bs.

Variable rel: PCFrel.

Lemma rename_propag : 
    (forall (V W:ipo) (f: V ---> W) t, 
      Proper (@rel V t ==> @rel _ _) (fun v => v //- f) )
    ->
    forall (V W: ipo)(f: V ---> W) t,
    Proper (p rel V t ==> p rel W t) (fun v => v //- f).
Proof. 
  unfold Proper in *; repeat red in *.
  intros H V W f t x y H0. 
  generalize dependent W. 
  dependent induction H0. 
  red in H. 
  
  constructor 1. apply H. auto.
  
  simpl. constructor 2. auto. 
  simpl. constructor 3. auto.
  simpl in *. constructor 4.
  set (H':= IHpropag (opt_TP s W) (lift (M:=opt_TP_monad s) f)).
(*  simpl in *. *)
  apply H'.
  simpl. constructor 5. auto.
Qed.



Lemma rename_rt_clos:
  (forall (V W:ipo)(f: V ---> W) t,
   Proper (@rel V t ==> @rel W t) (fun v => v //- f)) 
   ->  
  forall (V W:ipo) (f:V ---> W) t,
  Proper (rt (@rel V t) ==> rt (@rel W t)) (fun v => v //- f).
Proof. 
  unfold Proper; repeat red. 
  intros H V W f t x y H0.
  (*       generalize dependent W. *)
  dependent induction H0; simpl.
  intros. constructor 1.
  intros. constructor 2 with (rename_  f y).
  red in H.
  apply (H V W f _ x y). auto.
  apply IHclos_refl_trans_1n; auto.
Qed.

End rename_bs.

Lemma rename_beta:
forall (V W : ipo) (f : V ---> W) (t : TY),
Proper (@beta_ V t ==> @beta_ W t) (fun v => v //- f).
Proof. 
  intros V W f t. 
  unfold Proper; repeat red.
  intros x y H.
  induction H. simpl.
  rewrite rename_substar.
  constructor.
  simpl.
  constructor 2.
  apply f; auto.
Qed.

 

Program Definition rename (V W: ipo)(f:ipo_mor V W) : 
  ipo_mor (BETA V) (BETA W) := Build_ipo_mor 
     (ipo_mor_carrier := @rename_ _ _ f) _ . 
(*a:= BETA V t)(b:= BETA W t*) 
(*              (PO_fun := fun v => v //- f) _ .*)
               (* (PO_fun := @rename_ _ _ f t) _ .*)
Next Obligation.
Proof. 
  constructor.
  unfold Proper; repeat red. 
  unfold beta.
  intros t x y H.
  apply rename_rt_clos.
  intros V0 W0 F0 t0.
  apply (@rename_propag beta_ ).
  intros V1 W1 f0 t1. 
  unfold Proper; red.
  intros.
  apply rename_beta; 
  auto.
  auto.
Qed.

End rename.

Section inj.

Program Definition  inj (u:TY)(V:ipo) : 
      ipo_mor (BETA V) (BETA (opt_TP u V)) := 
   Build_ipo_mor (ipo_mor_carrier := @inj_ u V) _. 
Next Obligation.
Proof. 
  constructor.
  unfold Proper; repeat red.
  set (H3 := ipo_mor_s ( rename (Some_TP_PO u V))).
  simpl in H3.
  destruct H3 as [h].
  unfold Proper in h.
  red in h.
  unfold inj_.
  intros.
  apply h.
  auto.
Qed.

End inj.
    
Section shift.

Variable u:TY.

Section shift_bs.

Variable rel: forall (V:ipo) t, relation (PCF V t).

Lemma shift_propag :
    (forall (u:TY)(V W:ipo) (f: V ---> (BETA W)) (t:TY), 
      Proper (IRel (A:=opt_TP u V) (t:=t) ==> @rel(opt_TP u W) t ) 
                    (@shift_ u _ _ f t)) 
    ->
    forall (V W: ipo)(f: V ---> (BETA W)) t,
    Proper (IRel (A:=opt_TP u V) (t:=t) ==> @propag rel (opt_TP u W) t )
                                     (@shift_ u _ _ f t).
Proof. 
  unfold Proper in *; repeat red in *.
  intros H V W f t x y H0. red in H. 
  generalize dependent W. 
  induction H0.
  
  constructor 1. apply H. constructor. auto.
  
  intros W f.  constructor 1. apply H.
  constructor 2. auto.
Qed.


  
Lemma shift_rt_clos : 
  (forall (u:TY)(V W:ipo) (f: V ---> (BETA W)) t, 
  Proper (IRel (A:=opt_TP u V)(t:=t) ==> @rel (opt_TP u W) t) 
                        (@shift_ u _ _ f t)) 
    ->
  forall (V W: ipo)(f: V ---> (BETA W)) t,
  Proper (IRel (A:=opt_TP u V) (t:=t)  ==> 
            @clos_refl_trans_1n _ (@rel (opt_TP u W) t) ) 
                        (@shift_ u _ _ f t).
Proof. 
  unfold Proper; repeat red in *. 
  intros H V W f t x y H0. red in H.
  induction H0.
  constructor 1.
  
  constructor 2 with (shift_ f (Some_T u z)).
  apply H. constructor. auto.
  constructor 1.
Qed.

End shift_bs.

Lemma shift_h (V W : ipo) (f : forall t, V t -> PCF W t)
      (H : ipo_mor_struct (a:=V)(b:=BETA W) f) : 
       ipo_mor_struct (a:=opt_TP u V)(b:=BETA(opt_TP u W))
                (@shift_ u V _ f).
Proof.
  intros V W f H.
  constructor.
  unfold Proper; red.
  intros t x y H'. 
  induction H'.
  constructor 1.
  
  simpl.
  set (H':= ipo_mor_s (inj u (W))).
  destruct H' as [h].
  unfold Proper in h.
  red in h. simpl in h.
  apply h.
  apply H.
  auto.
Qed.


Program Definition shift (V W: ipo)
      (f: V ---> (BETA W)) : 
       (opt_TP u V) ---> (BETA (opt_TP u W)) := 
   Build_ipo_mor (ipo_mor_carrier := @shift_ u V _ f) _ .
Next Obligation.
Proof. 
  constructor.
  unfold Proper; red.
  intros t x y H. 
  induction H.
  constructor 1.
  
  simpl.
  set (H':= ipo_mor_s (inj u (W))).
  destruct H' as [h].
  unfold Proper in h.
  red in h. simpl in h.
  apply h.
  apply f.
  auto.
Qed.

End shift.

Section subst.

Section subst_bs.

Variable rel: PCFrel.

Lemma subst_propag : 
    (forall (V W:ipo) (f: V ---> (BETA W)) t, 
      Proper (@rel V t ==> @rel _ _) (fun v => v >>= f )) 
    ->
    forall (V W: ipo)(f: V ---> (BETA W)) t,
    Proper (p rel V t ==> p rel W t) (fun v => v >>= f ).
Proof. 
  unfold Proper in *; repeat red in *.
  intros H V W f t x y H0. 
  generalize dependent W. 
  dependent induction H0.
  red in H. 
  
  constructor 1. apply H. auto.
  
  simpl. constructor 2. auto.
  
  simpl. intros; constructor 3. apply IHpropag. auto.
  
  simpl. intros. constructor 4. 
  apply (IHpropag _ (shift _ f)). auto.
  
  simpl; intros; constructor 5; auto.
Qed.
     

Lemma subst_rt_clos : 
   (forall (V W:ipo) (f: V ---> (BETA W)) t, 
      Proper (@rel V t ==> @rel _ _) (fun v => v >>= f )) 
    ->
    forall (V W: ipo)(f: V ---> (BETA W)) t,
    Proper (rt (@rel V t) ==> rt (@rel _ _)) (fun v => v >>= f ).
Proof. 
  unfold Proper in *; repeat red in *.
  intros H V W f t x y H0. 
  generalize dependent W. 
  dependent induction H0.
  red in H. 
  
  constructor 1. 
  
  intros. constructor 2 with (y >>= f). 
  apply H. auto.
  apply IHclos_refl_trans_1n.
Qed.

End subst_bs.

Lemma subst_substar (V W:ipo) 
      (s t:TY) (M: PCF V* t) (N:PCF V s) 
      (f:forall t, V t -> PCF W t):
   M // N >>= f = (M >>= $ f) // (N >>= f).
Proof. 
  intros V W s t M N f.
  unfold substar. simpl.
  repeat rewrite subst_subst.
  apply subst_eq.
  intros t0 x.
  destruct x. unfold shift_.
  unfold inj_. 
  rewrite subst_rename. simpl. 
  rewrite  subst_var_eta. auto.
  simpl.
  apply subst_eq; auto.
Qed.

Section subst_lemmata.

Variable rel:PCFrel.

Lemma propag_clos_propag_clos (V:ipo)(t:TY)(x y: PCF V t) 
(H: rt (p (fun V0 t0 => fun x0 y0 => rt (p rel V0 t0) x0 y0) V t) x y):
       rt (p rel V t) x y.
Proof.
  intros V t x y H.
  induction H.
  constructor.
  
  clear H0.
  generalize dependent z.
  induction H.
  
  transitivity v'; auto.
  
  intros. (*inversion IHclos_refl_trans_1n.*)
  transitivity (App M' N); auto.
  apply cp_App1. apply IHpropag. constructor.
  
  intros.
  transitivity (App M N'); auto.
  apply cp_App2. apply IHpropag. constructor.
  
  intros.
  transitivity (Lam M'); auto.
  apply cp_Lam. apply IHpropag. constructor.
  
  intros.
  transitivity (Rec M'); auto.
  apply cp_Rec. apply IHpropag. constructor.
Qed.
            

Lemma clos (V:ipo) (t:TY) x y:
          rel x y -> rt (@rel V t) x y.
Proof. intros. constructor 2 with y; try constructor; auto. Qed.

End subst_lemmata.

Lemma subst_h (V W : ipo) (f : forall t, V t -> PCF W t)
         (H : ipo_mor_struct (a:=V) (b:=BETA W) f) :
       ipo_mor_struct (a:=BETA V) (b:=BETA W) (subst_ f).
Proof.
  intros V W f H'.
  constructor.
  unfold Proper; repeat red.
  intros t x y H. 
  generalize dependent W.
  
  induction H. constructor.
  
  intros.
  (*constructor 2 with (subst_ y f); auto.
  apply subst_propag; auto.
  unfold Proper; repeat red; simpl; intros.
  induction H1. (* beta x y *)
  rewrite subst_substar; simpl; constructor.
  simpl. (* not solvable *)*)
  transitivity (y >>= f); auto.
  (*                 generalize dependent H0.
  generalize dependent IHclos_refl_trans_1n.*)
  apply propag_clos_propag_clos. 
  generalize dependent W.
  generalize dependent z.
  induction H. intros. simpl.
  Focus 2. intros. simpl. 
  clear H0 IHclos_refl_trans_1n z.
  apply cp_App1. 
  apply IHpropag with M'; auto. constructor.
  intros. constructor. 
  
  Focus 2. intros. simpl. 
  clear H0 IHclos_refl_trans_1n z.
  apply cp_App2. 
  apply IHpropag with N'; constructor.
  apply H'.
  
  Focus 2. intros. simpl. 
  clear H0 IHclos_refl_trans_1n z.
  apply cp_Lam.
(*  apply (IHpropag M'). *)

  apply (IHpropag M' (rt1n_refl _ _ _ ) 
  (fun W f _ => rt1n_refl _ _ _ ) _ (shift s (Build_ipo_mor H'))).
  simpl.
  apply shift_h. auto.
  (*apply (IHrelpropag M' (f:= shift s f)); 
  constructor.*)
  
  Focus 2. intros. simpl. 
  clear H0 IHclos_refl_trans_1n z.
  apply cp_Rec. 
  apply IHpropag with M'; constructor.
  apply H'.
  
  induction H.
  apply clos. constructor 1.
  simpl. 
  rewrite subst_substar. 
  apply clos. constructor 1. constructor 1.
  
  simpl.
  apply clos.
  constructor 1.
  apply H'.
  auto.
Qed.



Program Definition subst (V W: ipo)(f: V ---> (BETA W)): 
   (BETA V) ---> (BETA W) :=  
(*   Build_PO_mor (PO_fun := fun x => x >>= f) _ .*)
(*     Build_PO_mor (PO_fun := @subst_ _ _ f t) _ .*)
     Build_ipo_mor (ipo_mor_carrier := @subst_ _ _ f) _ .
Next Obligation.
Proof.
  constructor.
  unfold Proper; repeat red.
  intros t x y H. 
  generalize dependent W.
  
  induction H. constructor.
  
  intros.
  (*constructor 2 with (subst_ y f); auto.
  apply subst_propag; auto.
  unfold Proper; repeat red; simpl; intros.
  induction H1. (* beta x y *)
  rewrite subst_substar; simpl; constructor.
  simpl. (* not solvable *)*)
  transitivity (y >>= f); auto.
  (*                 generalize dependent H0.
  generalize dependent IHclos_refl_trans_1n.*)
  apply propag_clos_propag_clos. 
  generalize dependent W.
  generalize dependent z.
  induction H. intros. simpl.
  Focus 2. intros. simpl. 
  clear H0 IHclos_refl_trans_1n z.
  apply cp_App1. 
  apply IHpropag with M'; constructor.
  
  Focus 2. intros. simpl. 
  clear H0 IHclos_refl_trans_1n z.
  apply cp_App2. 
  apply IHpropag with N'; constructor.
  
  Focus 2. intros. simpl. 
  clear H0 IHclos_refl_trans_1n z.
  apply cp_Lam. 
  apply (IHpropag M' (rt1n_refl _ _ _ ) 
  (fun W f => rt1n_refl _ _ _ ) _ (shift s f)).
  (*apply (IHrelpropag M' (f:= shift s f)); 
  constructor.*)
  
  Focus 2. intros. simpl. 
  clear H0 IHclos_refl_trans_1n z.
  apply cp_Rec. 
  apply IHpropag with M'; constructor.
  
  induction H.
  apply clos. constructor 1.
  simpl. 
  rewrite subst_substar. 
  apply clos. constructor 1. constructor 1.
  
  simpl.
  apply clos.
  constructor 1.
  apply f.
  auto.
Qed.
  
End subst.

End Compat_with_Beta. 

(** preparations for defining the monad (haskell style) *)
(** return is given by VAR, the upgraded version of Var *)

Program Definition VAR (V:ipo) : ipo_mor V (BETA V) := 
   Build_ipo_mor (ipo_mor_carrier := @Var V) _.

Next Obligation.
Proof. 
  constructor.
  unfold Proper; repeat red.
  intros t x y H.
  constructor 2 with (Var y); 
  try constructor.
  constructor. auto.
Qed.
        


(** betaS in subterms *)

Section betaS_constructors.

Variable V:ipo.
Variables s t: TY.

Lemma betaS_App1 (v1 v2: BETA V (s ~> t)) w : 
          betaS v1 v2 -> betaS (App v1 w) (App v2 w).
Proof.
  intros v1 v2 w H.
  generalize dependent w.
  induction H.
  constructor 1.
  intros.
  intros;
  transitivity (App y w); auto.
  apply clos.
  apply relApp1; auto.
Qed.

Lemma betaS_App2 (v : BETA V (s ~> t)) w1 w2 : 
          betaS w1 w2 -> betaS (App v w1) (App v w2).
Proof.
  intros v v1 w2 H.
  generalize dependent v.
  induction H.
  constructor 1.
  intros.
  intros;
  transitivity (App v y); auto.
  apply clos.
  apply relApp2; auto.
Qed.

Lemma betaS_Rec (v w : BETA V (s ~> s)): 
          betaS v w -> betaS (Rec v) (Rec w).
Proof.
  intros v w H.
  induction H.
  constructor 1.
  transitivity (Rec y); auto.
  apply clos.
  apply relRec; auto.
Qed.

Lemma betaS_Lam (v w : BETA (opt_TP s V) t ): 
          betaS v w -> betaS (Lam v) (Lam w).
Proof.
  intros v w H.
  induction H.
  constructor 1.
  transitivity (Lam y); auto.
  apply clos.
  apply relLam; auto.
Qed.

End betaS_constructors.

(** upgrading the constructors to morphisms *)

Program Definition AppPO (V:ipo) r s: 
   PO_mor (product (IP_proj (r ~> s) (BETA V)) 
                   (IP_proj r (BETA V))) (IP_proj s (BETA V)) :=
 Build_PO_mor 
       (PO_fun := fun t => App  (s:= r) (fst t)  (snd t) ) _ .
Next Obligation.
Proof.
  constructor.
  unfold Proper; red.
  intros x y.
  destruct x as [x1 x2];
  destruct y as [y1 y2];
  simpl.
  intro H.
  inversion H.
  subst.
  simpl in *.
  transitivity (App x1 y2);
  auto using betaS_App2, betaS_App1.
Qed.

Program Instance LamPO_struct (V:ipo) r s : 
      PO_mor_struct (a:= IP_proj s (BETA (opt_TP r V))) 
                    (b:=IP_proj (r ~> s) (BETA V))
   (@Lam V r s).
Next Obligation.
Proof.
  unfold Proper; red.
  intros. simpl.
  auto using betaS_Lam.
Qed.

Definition LamPO (V:ipo) r s: 
      PO_mor _ _ :=
   Build_PO_mor (LamPO_struct V r s).

Program Instance RecPO_struct (V:ipo) r : 
    PO_mor_struct (a:= IP_proj (r ~> r) (BETA V)) 
                  (b:= IP_proj r (BETA V))
    (@Rec V r).
Next Obligation.
Proof.
  unfold Proper; red.
  intros; simpl;
  auto using betaS_Rec.
Qed.

Program Definition RecPO (V:ipo) r : 
        PO_mor _ _  := 
     Build_PO_mor (RecPO_struct V r).

Program Instance ConstsPO_struct (t:TY) (C:Consts t)(V:ipo) : 
     PO_mor_struct (a:= Term) (b:= IP_proj t (BETA V)) 
           (fun g => Const V C).
Next Obligation.
Proof.
  unfold Proper; red.
  constructor.
Qed.

Definition ConstsPO (t:TY)(C:Consts t) (V:ipo) := 
            Build_PO_mor (ConstsPO_struct t C V).

Program Instance BottomPO_struct (V:ipo) t : 
    PO_mor_struct (a:=Term) (b:= IP_proj t (BETA V)) (fun g => Bottom V t).
Next Obligation.
Proof.
  unfold Proper; red;
  constructor.
Qed.

Definition BottomPO (V:ipo) t := Build_PO_mor (BottomPO_struct V t).

   *)
End PCF.


(** PCF.BETA, the terms of PCF with beta reduction preorder,
    form a monad with 
    - [return := VAR]
    - [bind = subst] 
*)

Require Import monad_haskell.
(*
Program Instance PCFPO_monad_h: Monad_struct (IPO PCF.TY) 
        (*fun V => PCFBETA V*) PCF.BETA := {
      weta  := PCF.VAR ;
      kleisli  :=  PCF.subst }.

(*Next Obligation.
   apply PCF.VAR. Defined.
   
Next Obligation.
  apply (PCF.subst X). Defined. *)


(*:= {
(*  weta V t v:= PCFVAR v*)
(*  kleisli V W f := fun t x => subst x f *)
}.*)
  
Next Obligation.
Proof. 
  unfold Proper; red. 
  intros. simpl. 
  intros; apply PCF.subst_eq. 
  auto.  
Qed.
Next Obligation.
Proof. 
  apply PCF.subst_var.  
Qed.

Next Obligation.
Proof.
  apply PCF.subst_subst. 
Qed.

Definition PCFPO_monad := Build_Monad PCFPO_monad_h.
*)
Program Instance PCF_monad_struct : 
     Monad_struct (ITYPE PCF.TY) PCF.PCF := {
  weta := PCF.Var;
  kleisli := PCF.subst_
}.
Next Obligation.
Proof.
  unfold Proper; red.
  intros.
  apply PCF.subst_eq.
  auto.
Qed.
Next Obligation.
Proof.
  apply PCF.subst_var.
Qed.
Next Obligation.
Proof.
  apply PCF.subst_subst. 
Qed.

Definition PCF_monad := Build_Monad PCF_monad_struct.


(*
Program Instance PCF_monad_h : 
         Monad_struct (IT PCF.TY) (fun V => PCF.PCF V).

*)

