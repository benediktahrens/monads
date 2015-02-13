(*

Require Export cat_INDEXED_TYPE.

Set Implicit Arguments.
Unset Strict Implicit.
(* *)
Section pcf_syntax.

(*Inductive base_type := Bool | Nat.*)

Inductive TY := 
 | Bool : TY
 | Nat : TY
 | arrow: TY -> TY -> TY.

Inductive PCF_consts : TY -> Type :=
 | Nats : nat -> PCF_consts Nat
 | tt : PCF_consts Bool
 | ff : PCF_consts Bool
 | succ : PCF_consts (arrow Nat Nat)
 | zero : PCF_consts (arrow Nat Bool)
 | condN: PCF_consts (arrow Bool (arrow Nat (arrow Nat Nat)))
 | condB: PCF_consts (arrow Bool (arrow Bool (arrow Bool Bool))).

Inductive PCF (V:TY -> Type) : TY -> Type:=
 | Bottom: forall t, PCF V t
 | Const : forall t, PCF_consts t -> PCF V t
 | PCFVar : forall t, V t -> PCF V t
 | PApp : forall t s, PCF V (arrow s t) -> PCF V s -> PCF V t
 | PLam : forall t s, PCF (opt_T t V) s -> PCF V (arrow t s)
 | PRec : forall t, PCF V (arrow t t) -> PCF V t.



Definition PCF_varmap (V W: TY -> Type) := 
        forall t:TY, V t -> W t.

Fixpoint PCF_rename (V W:TY -> Type) (f:PCF_varmap V W) 
         (t:TY)(v:PCF V t): PCF W t :=
    match v with
    | Bottom t => Bottom W t
    | Const t c => Const W c
    | PCFVar t v => PCFVar (f t v)
    | PApp t s u v => PApp (PCF_rename f u) (PCF_rename f v)
    | PLam t s u => PLam (PCF_rename (lift (M:=opt_T_monad _ )(*u:=t*) f) u)
    | PRec t u => PRec (PCF_rename f u)
    end.

Lemma PCF_rename_eq (V:TY -> Type)(t:TY)(v: PCF V t) 
  (W: TY -> Type) (f g: PCF_varmap V W)(H: forall t x, f t x = g t x):
           PCF_rename f v = PCF_rename g v.
Proof. intros V t v; induction v; simpl; auto.
       
       intros; rewrite H; auto.
       
       intros. rewrite (IHv1 W f g); auto.
               rewrite (IHv2 W f g); auto.
               
       intros. 
       apply f_equal.
       set (H':=IHv (opt_T t W) (lift (M:=opt_T_monad _ ) f) 
                                (lift (M:=opt_T_monad _ ) g)).
       simpl in *. rewrite H'; auto.
       set (H'':= lift_eq (opt_T_monad t )).
       simpl in *. apply H''; auto.
        
       intros; rewrite (IHv W f g H); auto.
Qed.

Lemma PCF_rename_id (V:TY -> Type)(t:TY)(v: PCF V t) 
  (f: PCF_varmap V V)(H: forall t x, f t x = x):
           PCF_rename f v = v.
Proof. intros V t v; induction v; simpl; auto.
       intros f H; rewrite H; auto.
       intros f H; rewrite IHv1; try rewrite IHv2; auto.
       intros f H; rewrite IHv; auto.
       unfold lift. unfold kleisli. simpl.
       intros t0 x; destruct x; simpl; 
       try rewrite H; auto.
       intros f H; rewrite IHv; auto.
Qed.

Lemma PCF_rename_comp (V:TY -> Type) (t: TY) (v: PCF V t)
      (W X: TY -> Type) (f: PCF_varmap V W) (g: PCF_varmap W X):
      PCF_rename (fun t x => g t (f t x)) v = 
           PCF_rename g (PCF_rename f v).
Proof. intros V t v; induction v; simpl; auto.
       intros W X f g; rewrite IHv1; rewrite IHv2; auto.
       intros W X f g. apply f_equal. 
       rewrite <- (IHv _ (opt_T t X)).
       apply PCF_rename_eq.
       intros to x.
       set (H:= lift_lift (opt_T_monad t)).
       simpl in *. rewrite H; auto.
       intros W X f g; rewrite IHv; auto.
Qed.


(* injection of terms into terms with one variable more, of type u *)
Definition PCF_inj(u:TY)(V:TY -> Type)(t:TY)(v:PCF V t): 
           PCF (opt_T u V) t :=
    PCF_rename (@Some_T TY u V) v.




Definition PCF_shift (u:TY) (V W:TY -> Type)(f: forall t:TY, V t-> PCF W t) 
              (t:TY) (v: opt_T u V t): PCF (opt_T u W) t :=
            match v in opt_T _ _ t' return PCF (opt_T u W) t' with
            | None_T => PCFVar (None_T u W)
            | Some_T t v => PCF_inj u (f t v)
            end.

Lemma PCF_shift_eq (u:TY) (V:TY -> Type)(t:TY)(v:opt_T u V t)
          (W:TY -> Type)(f g: forall t, V t -> PCF W t)
          (H: forall t x, f t x = g t x):
          PCF_shift f v = PCF_shift g v.
Proof. intros u V t v; induction v; simpl; intros; try rewrite H; auto.
Qed.

Lemma PCF_shift_var (u:TY)(V:TY -> Type)(t:TY)(v: opt_T u V t):
       PCF_shift (fun t x => PCFVar x) v = PCFVar v.
Proof. induction v; intros; simpl; auto. Qed.

Lemma PCF_var_lift_shift_eq (u:TY) (V: TY -> Type) (t: TY) (v: opt_T u V t)
               (W:TY -> Type) (f: forall t, V t -> W t):
    PCFVar (lift (M:=opt_T_monad u) f _ v) = 
         PCF_shift (fun t x0 => PCFVar (f t x0)) v.
Proof. induction v; simpl; intros; auto. Qed.

Lemma PCF_shift_lift (u:TY) (V: TY -> Type) (t:TY)(v:opt_T u V t)
           (W:TY -> Type)(f: forall t, V t -> W t) (X: TY -> Type)
                    (g: forall t, W t -> PCF X t): 
   PCF_shift g (lift (M:=opt_T_monad u) f _ v) = 
         PCF_shift (fun t x0 => g t (f t x0)) v.
Proof. induction v; simpl; intros; auto. Qed.



Fixpoint PCF_subst (V W: TY -> Type) (t:TY) (v: PCF V t) 
       (f: forall t, V t -> PCF W t) : PCF W t :=
    match v with
    | Bottom t => Bottom W t
    | Const t c => Const W c
    | PCFVar t v => f t v
    | PApp t s u v => PApp (PCF_subst u f) (PCF_subst v f)
    | PLam t s u => PLam (PCF_subst u (PCF_shift (*u:=t*) f))
    | PRec t u => PRec (PCF_subst u f)
    end.

Definition PCF_substar (u:TY)(V: TY -> Type) (t:TY)(v:PCF (opt_T u V) t) 
      (M:PCF V u): PCF V t := PCF_subst (*V:= opt_T u V*) v 
  (fun t x => match x with  
            | None_T => M
            | Some_T _ v => PCFVar v
            end) .


Lemma PCF_subst_eq (V:TY -> Type)(t:TY)(v:PCF V t) (W:TY -> Type)
       (f g: forall t, V t -> PCF W t)
       (H: forall t x, f t x = g t x) :
       PCF_subst v f = PCF_subst v g.
Proof. induction v; intros; simpl;  auto.
  
       try rewrite (IHv1 W f g);
       try rewrite (IHv2 W f g); 
       try rewrite (IHv W f g); auto.
       
       rewrite (IHv _ (PCF_shift f) (PCF_shift g)); auto.
       intros; apply PCF_shift_eq; auto.
       
       rewrite (IHv W f g); auto.
Qed.

Lemma PCF_subst_var (V:TY -> Type)(t:TY)(v:PCF V t):
       PCF_subst v (fun t x0 => PCFVar x0) = v.
Proof. induction v; intros; simpl; auto.
       rewrite IHv1. rewrite IHv2; auto.
       rewrite <- IHv at 2.
       apply f_equal. apply PCF_subst_eq.
       intros; apply PCF_shift_var.
       rewrite IHv; auto.
Qed.

Lemma PCF_subst_eq_rename (V:TY -> Type)(t:TY)(v:PCF V t)(W:TY->Type)
           (f:forall t, V t -> W t):
        PCF_rename f v = PCF_subst v (fun t x0 => PCFVar (f t x0)).
Proof. induction v; intros; simpl; auto.
       rewrite IHv1; rewrite IHv2; auto.
       rewrite IHv. apply f_equal. apply PCF_subst_eq.
       intros; apply PCF_var_lift_shift_eq.
       rewrite IHv; auto.
Qed.


Lemma PCF_rename_term_inj (u:TY)(V:TY -> Type)(t:TY)(v:PCF V t) 
    (W:TY -> Type) (g: forall t, V t -> W t):
       PCF_rename (opt_T_map (u:=u) g) (PCF_inj u v) = 
                  PCF_inj u (PCF_rename g v).
Proof. induction v; simpl; intros; auto.
       rewrite IHv1; rewrite IHv2; auto.
       unfold PCF_inj. simpl.
       apply f_equal. 
       rewrite <- PCF_rename_comp.
       rewrite <- PCF_rename_comp.
       apply PCF_rename_eq.
       induction x; simpl; auto.
       rewrite IHv. unfold PCF_inj. simpl. auto.
Qed.

Lemma PCF_rename_subst (V:TY -> Type) (t:TY)(v: PCF V t) (W:TY -> Type)
     (f:forall t, V t -> PCF W t)(X:TY -> Type)(g:forall t, W t -> X t):
   PCF_rename g (PCF_subst v f) = 
           PCF_subst v (fun t x => PCF_rename g (f t x)).
Proof. induction v; intros; simpl; auto.
       rewrite IHv1; rewrite IHv2; auto.
       
       rewrite IHv. apply f_equal. apply PCF_subst_eq.
       induction x; simpl; auto.
       apply PCF_rename_term_inj. 
       
       rewrite IHv. auto.
Qed.


Lemma PCF_subst_rename (V:TY -> Type) (t:TY)(v: PCF V t) (W:TY -> Type)
     (f:forall t, V t -> W t)(X:TY -> Type)(g:forall t, W t -> PCF X t):
   PCF_subst (PCF_rename f v) g = 
           PCF_subst v (fun t x =>  g t (f t x)).
Proof. induction v; simpl; intros; auto.
       rewrite IHv1; rewrite IHv2; auto.
       
       rewrite IHv. apply f_equal.
       apply PCF_subst_eq. intros.
       apply PCF_shift_lift.
       
       rewrite IHv. auto.
Qed.
       
Lemma PCF_subst_term_inj (u:TY)(V:TY -> Type)(t:TY)(v:PCF V t)(W:TY -> Type)
      (g:forall t, V t -> PCF W t):
    PCF_subst (PCF_inj u v) (PCF_shift g) = PCF_inj u (PCF_subst v g).
Proof. induction v; simpl; intros; auto.
       rewrite IHv1; rewrite IHv2; auto.
       
       unfold PCF_inj. simpl. apply f_equal.
       rewrite PCF_rename_subst.
       rewrite PCF_subst_rename.
       apply PCF_subst_eq.
       induction x; simpl; auto.
       rewrite PCF_rename_term_inj. auto.
       
       rewrite IHv; auto.
Qed.


Lemma PCF_subst_shift_shift (u:TY) (V:TY -> Type) (t:TY)(v:opt_T u V t)
 (W:TY -> Type)
 (f: forall t, V t -> PCF W t) (X:TY -> Type)(g:forall t, W t -> PCF X t):
  PCF_subst (PCF_shift f v) (PCF_shift g) = 
          PCF_shift (fun t x0 => PCF_subst (f t x0) g) v.
Proof. induction v; simpl; intros; try apply PCF_subst_term_inj; auto.
Qed.

Lemma PCF_subst_subst (V:TY -> Type)(t:TY)(v:PCF V t) (W X: TY -> Type)
         (f:forall t, V t -> PCF W t)(g:forall t, W t -> PCF X t):
PCF_subst (PCF_subst v f) g = PCF_subst v (fun t x0 => PCF_subst (f t x0) g).
Proof. induction v; simpl; intros; auto.
       rewrite IHv1; rewrite IHv2; auto.

       rewrite IHv. apply f_equal.
       apply PCF_subst_eq.
       intros; simpl.
       apply PCF_subst_shift_shift.
       
       rewrite IHv; auto.
Qed.


Require Export monad_haskell.


Program Instance syntax_monad_h: Monad_struct (ITYPE TY) 
        (fun V => PCF V) := {
  weta V t v:= PCFVar v;
  kleisli V W f := fun t x => PCF_subst x f
}.
  
  Next Obligation.
    Proof. unfold Proper; red. 
           intros. apply PCF_subst_eq. auto.
    Qed.
    
  (*Next Obligation.
    Proof.  
           simpl. auto.
    Qed.
*)
  Next Obligation.
    Proof.
           intros; apply PCF_subst_var.
    Qed.
 
  Next Obligation.
    Proof.
           intros; apply PCF_subst_subst.
    Qed.


End pcf_syntax.

*)


