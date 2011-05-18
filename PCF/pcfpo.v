
(*

Require Export Relations ind_potype.

Set Implicit Arguments.
Unset Strict Implicit.

Section pcfo_syntax.

(*Inductive base_type := Bool | Nat.*)

Inductive TY := 
 | Bool : TY
 | Nat : TY
 | arrow: TY -> TY -> TY.

Definition ipo := ind_po_obj TY.

Inductive PCF_consts : TY -> Type :=
 | Nats : nat -> PCF_consts Nat
 | tt : PCF_consts Bool
 | ff : PCF_consts Bool
 | succ : PCF_consts (arrow Nat Nat)
 | zero : PCF_consts (arrow Nat Bool)
 | condN: PCF_consts (arrow Bool (arrow Nat (arrow Nat Nat)))
 | condB: PCF_consts (arrow Bool (arrow Bool (arrow Bool Bool))).


Inductive PCF (V: ind_po_obj TY) : TY -> Type:=
 | Bottom: forall t, PCF V t
 | Const : forall t, PCF_consts t -> PCF V t
 | PCFVar : forall t, V t -> PCF V t
 | PApp : forall t s, PCF V (arrow s t) -> PCF V s -> PCF V t
 | PLam : forall t s, PCF (opt_TP t V) s -> PCF V (arrow t s)
 | PRec : forall t, PCF V (arrow t t) -> PCF V t.

Definition PCF_varmap (V W: ind_po_obj TY):Type := 
        ind_po_mor V W.
	
Fixpoint PCF_rename_ (V W:ind_po_obj TY) (f:PCF_varmap V W) 
         (t:TY)(v:PCF V t): PCF W t :=
    match v with
    | Bottom t => Bottom W t
    | Const t c => Const W c
    | PCFVar t v => PCFVar (f t v)
    | PApp t s u v => PApp (PCF_rename_ f u) (PCF_rename_ f v)
    | PLam t s u => PLam (PCF_rename_ (opt_TP_map _ (*u:=t*) f) u)
    | PRec t u => PRec (PCF_rename_ f u)
    end.


Lemma PCF_rename_eq (V:ind_po_obj TY)(t:TY)(v: PCF V t) 
  (W: ind_po_obj TY) (f g: PCF_varmap V W)(H: forall t x, f t x = g t x):
           PCF_rename_ f v = PCF_rename_ g v.
Proof. intros V t v; induction v; simpl; auto.
       
       intros; rewrite H; auto.
       
       intros. rewrite (IHv1 W f g); auto.
               rewrite (IHv2 W f g); auto.
               
       intros. 
       rewrite (IHv (opt_TP t W) (opt_TP_map _ f) (opt_TP_map _ g)); auto.
       intros; apply opt_TP_map_extens; auto.
        
       intros; rewrite (IHv W f g H); auto.
Qed.

Lemma PCF_rename_id (V:ind_po_obj TY)(t:TY)(v: PCF V t) 
  (f: PCF_varmap V V)(H: forall t x, f t x = x):
           PCF_rename_ f v = v.
Proof. intros V t v; induction v; simpl; auto.
       intros f H; rewrite H; auto.
       intros f H; rewrite IHv1; try rewrite IHv2; auto.
       intros f H; rewrite IHv; intros; try apply opt_TP_map_id; auto.
       intros f H; rewrite IHv; auto.
Qed.

Lemma PCF_rename_comp (V: ind_po_obj TY) (t: TY) (v: PCF V t)
      (W X: ind_po_obj TY) (f: PCF_varmap V W) (g: PCF_varmap W X):
      PCF_rename_ (ind_po_comp f g) v = 
           PCF_rename_ g (PCF_rename_ f v).
Proof. intros V t v; induction v; simpl; auto.
       intros W X f g; rewrite IHv1; rewrite IHv2; auto.
       intros W X f g. apply f_equal. 
       rewrite <- (IHv _ (opt_TP t X)).
       apply PCF_rename_eq.
       intros to x.
       set (H3:=opt_TP_map_comp).
       simpl in *. apply H3.
       intros W X f g; rewrite IHv; auto.
Qed.


(* injection of terms into terms with one variable more, of type u *)
Definition PCF_inj_(u:TY)(V:ind_po_obj TY)(t:TY)(v:PCF V t): 
           PCF (opt_TP u V) t :=
    PCF_rename_ (@Some_TP_PO TY u V) v.



Definition PCF_shift_ := 
fun (u : TY) (V W : ind_po_obj TY) (f : forall t : TY, V t -> PCF W t)
  (t : TY) (v : opt_TP u V t) =>
match v in (opt_TPd _ _ y) return (PCF (opt_TP u W) y) with
| Some_TP t0 p => PCF_inj_ u (f t0 p)
| None_TP => PCFVar (V:=opt_TP u W) (t:=u) (None_TP u W)
end.



Lemma PCF_shift_eq (u:TY) (V:ind_po_obj TY)(t:TY)(v:opt_TP u V t)
          (W:ind_po_obj TY)(f g: forall t, V t -> PCF W t)
          (H: forall t x, f t x = g t x):
          PCF_shift_ f v = PCF_shift_ g v.
Proof. intros u V t v; induction v; simpl; intros; try rewrite H; auto.
Qed.

Lemma PCF_shift_var (u:TY)(V:ind_po_obj TY)(t:TY)(v: opt_TP u V t):
       PCF_shift_ (fun t x => PCFVar x) v = PCFVar v.
Proof. induction v; intros; simpl; auto. Qed.

Lemma PCF_var_lift_shift_eq (u:TY) (V:ind_po_obj TY) 
     (t: TY) (v: opt_TP u V t)
               (W:ind_po_obj TY) (f: ind_po_mor V W):
    PCFVar (opt_TP_map u f t v) = 
    PCF_shift_ (fun t x0 => PCFVar (f t x0)) v.
Proof. induction v; simpl; intros; auto. Qed.

Lemma PCF_shift_lift (u:TY) (V: ind_po_obj TY) (t:TY)(v:opt_TP u V t)
           (W:ind_po_obj TY)(f: ind_po_mor V W) (X: ind_po_obj TY)
                    (g: forall t, W t -> PCF X t): 
   PCF_shift_ g (opt_TP_map u f t v) = 
   PCF_shift_ (fun t x0 => g t (f t x0)) v.
Proof. induction v; simpl; intros; auto. Qed.



Fixpoint PCF_subst_ (V W: ind_po_obj TY) (t:TY) (v: PCF V t) 
       (f: forall t, V t -> PCF W t) : PCF W t :=
    match v with
    | Bottom t => Bottom W t
    | Const t c => Const W c
    | PCFVar t v => f t v
    | PApp t s u v => PApp (PCF_subst_ u f) (PCF_subst_ v f)
    | PLam t s u => PLam (PCF_subst_ u (PCF_shift_ (*u:=t*) f))
    | PRec t u => PRec (PCF_subst_ u f)
    end.


Definition PCF_substar (u:TY)(V:ind_po_obj TY) (t:TY)(v:PCF (opt_TP u V) t) 
      (M:PCF V u): PCF V t := PCF_subst_ (V:=opt_TP u V) v 
  (fun t x => match x with  
            | None_TP => M
            | Some_TP _ v => PCFVar v
            end) .

Lemma PCF_subst_eq (V: ind_po_obj TY)(t:TY)(v:PCF V t) (W:ind_po_obj TY)
       (f g: forall t, V t -> PCF W t)
       (H: forall t x, f t x = g t x) :
       PCF_subst_ v f = PCF_subst_ v g.
Proof. induction v; intros; simpl;  auto.
  
       try rewrite (IHv1 W f g);
       try rewrite (IHv2 W f g); 
       try rewrite (IHv W f g); auto.
       
       rewrite (IHv _ (PCF_shift_ f) (PCF_shift_ g)); auto.
       intros; apply PCF_shift_eq; auto.
       
       rewrite (IHv W f g); auto.
Qed.

Lemma PCF_subst_var (V:ind_po_obj TY)(t:TY)(v:PCF V t):
       PCF_subst_ v (fun t x0 => PCFVar x0) = v.
Proof. induction v; intros; simpl; auto.
       rewrite IHv1. rewrite IHv2; auto.
       rewrite <- IHv at 2.
       apply f_equal. apply PCF_subst_eq.
       intros; apply PCF_shift_var.
       rewrite IHv; auto.
Qed.

Lemma PCF_subst_eq_rename (V:ind_po_obj TY)(t:TY)(v:PCF V t)
      (W:ind_po_obj TY) (f:ind_po_mor V W):
        PCF_rename_ f v = PCF_subst_ v (fun t x0 => PCFVar (f t x0)).
Proof. induction v; intros; simpl; auto.
       rewrite IHv1; rewrite IHv2; auto.
       rewrite IHv. apply f_equal. apply PCF_subst_eq.
       intros; apply PCF_var_lift_shift_eq.
       rewrite IHv; auto.
Qed.


Lemma PCF_rename_term_inj (u:TY)(V:ind_po_obj TY)(t:TY)(v:PCF V t) 
    (W:ind_po_obj TY) (g: ind_po_mor V W):
       PCF_rename_ (opt_TP_map u g) (PCF_inj_ u v) = 
                  PCF_inj_ u (PCF_rename_ g v).
Proof. induction v; simpl; intros; auto.
       rewrite IHv1; rewrite IHv2; auto.
       unfold PCF_inj_. simpl.
       apply f_equal. 
       rewrite <- PCF_rename_comp.
       rewrite <- PCF_rename_comp.
       apply PCF_rename_eq.
       induction x; simpl; auto.
       rewrite IHv. unfold PCF_inj_. simpl. auto.
Qed.

Lemma PCF_rename_subst (V:ind_po_obj TY) (t:TY)(v: PCF V t) 
     (W:ind_po_obj TY)(f:forall t, V t -> PCF W t)(X:ind_po_obj TY) 
     (g:PCF_varmap W X):
   PCF_rename_ g (PCF_subst_ v f) = 
           PCF_subst_ v (fun t x => PCF_rename_ g (f t x)).
Proof. induction v; intros; simpl; auto.
       rewrite IHv1; rewrite IHv2; auto.
       
       rewrite IHv. apply f_equal. apply PCF_subst_eq.
       induction x; simpl; auto.
       apply PCF_rename_term_inj. 
       
       rewrite IHv. auto.
Qed.


Lemma PCF_subst_rename (V:ind_po_obj TY) (t:TY)(v: PCF V t) 
     (W:ind_po_obj TY) (f:PCF_varmap V W)(X:ind_po_obj TY)
     (g:forall t, W t -> PCF X t):
   PCF_subst_ (PCF_rename_ f v) g = 
           PCF_subst_ v (fun t x =>  g t (f t x)).
Proof. induction v; simpl; intros; auto.
       rewrite IHv1; rewrite IHv2; auto.
       
       rewrite IHv. apply f_equal.
       apply PCF_subst_eq. intros.
       apply PCF_shift_lift.
       
       rewrite IHv. auto.
Qed.

Lemma PCF_rename_substar (V:ind_po_obj TY)(s t:TY) (v:PCF (opt_TP s V) t)
   (W:ind_po_obj TY) (f:PCF_varmap V W) N:
       PCF_rename_ (W:=W) f (PCF_substar v N) = 
        PCF_substar (PCF_rename_ (opt_TP_map _ f) v) (PCF_rename_ f N).
Proof. intros. unfold PCF_substar.
       rewrite PCF_rename_subst.
       rewrite PCF_subst_rename. simpl. 
       apply PCF_subst_eq. 
       intros t0 x; destruct x;  simpl; auto.
Qed.
       
Lemma PCF_subst_term_inj (u:TY)(V:ind_po_obj TY)(t:TY)(v:PCF V t)
      (W:ind_po_obj TY)
      (g:forall t, V t -> PCF W t):
    PCF_subst_ (PCF_inj_ u v) (PCF_shift_ g) = PCF_inj_ u (PCF_subst_ v g).
Proof. induction v; simpl; intros; auto.
       rewrite IHv1; rewrite IHv2; auto.
       
       unfold PCF_inj_. simpl. apply f_equal.
       rewrite PCF_rename_subst.
       rewrite PCF_subst_rename.
       apply PCF_subst_eq.
       induction x; simpl; auto.
       rewrite PCF_rename_term_inj. auto.
       
       rewrite IHv; auto.
Qed.


Lemma PCF_subst_shift_shift (u:TY) (V:ind_po_obj TY) (t:TY)(v:opt_TP u V t)
 (W:ind_po_obj TY)
 (f: forall t, V t -> PCF W t) (X:ind_po_obj TY)
 (g:forall t, W t -> PCF X t):
  PCF_subst_ (PCF_shift_ f v) (PCF_shift_ g) = 
          PCF_shift_ (fun t x0 => PCF_subst_ (f t x0) g) v.
Proof. induction v; simpl; intros; try apply PCF_subst_term_inj; auto.
Qed.

Lemma PCF_subst_subst (V:ind_po_obj TY)(t:TY)(v:PCF V t) 
         (W X:ind_po_obj TY)
         (f:forall t, V t -> PCF W t)(g:forall t, W t -> PCF X t):
  PCF_subst_ (PCF_subst_ v f) g = 
     PCF_subst_ v (fun t x0 => PCF_subst_ (f t x0) g).
Proof. induction v; simpl; intros; auto.
       rewrite IHv1; rewrite IHv2; auto.

       rewrite IHv. apply f_equal.
       apply PCF_subst_eq.
       intros; simpl.
       apply PCF_subst_shift_shift.
       
       rewrite IHv; auto.
Qed.



Inductive PCFrelpropag (rel: forall V t, relation (PCF V t)) 
      (V:ind_po_obj TY) : forall t, relation (PCF V t) :=
| PCFrelorig : forall t v v', rel V t   v v' -> PCFrelpropag rel v v'
| PCFrelPApp1: forall (*V:ind_po_obj TY*)(s t:TY)(M M':PCF V (arrow s t)) N, 
      PCFrelpropag (V:=V) rel M M' -> 
      PCFrelpropag rel (PApp M N) (PApp M' N)
| PCFrelPApp2: forall (*V:ind_po_obj TY*)(s t:TY)(M:PCF V (arrow s t)) N N',
      PCFrelpropag rel N N' -> 
      PCFrelpropag rel (PApp M N) (PApp M N')
| PCFrelPLam: forall (s t:TY)(M M':PCF (opt_TP s V) t),
      PCFrelpropag rel (V:=opt_TP s V) M M' -> 
      PCFrelpropag rel (PLam M) (PLam M')
| PCFrelPRec : forall (s:TY) (M M':PCF V (arrow s s)),
      PCFrelpropag rel M M' ->
      PCFrelpropag rel (PRec M) (PRec M').
(* | PCFrelvv : forall t (x y:V t), PreOrderRel x y 
       -> PCFrelpropag rel (PCFVar x) (PCFVar y). *)


Inductive PCF_beta (V:ind_po_obj TY): forall t, relation (PCF V t) :=
| PCFbeta_beta: forall (s t:TY) (M:PCF (opt_TP s V) t) N, 
          PCF_beta (PApp (PLam M) N) (PCF_substar M N)
|PCFbeta_var: forall (t:TY) (x y:V t),
          x << y -> PCF_beta (PCFVar x) (PCFVar y).

Lemma PCF_rename_propag : 
    forall (rel: forall V t, relation (PCF V t)),
   (forall (V W:ind_po_obj TY) (f:PCF_varmap V W) t, 
      Proper (rel V t ==> rel _ _) (@PCF_rename_ _ _ f t)) 
    ->
    forall (V W: ind_po_obj TY)(f: PCF_varmap V W) t,
    Proper (@PCFrelpropag rel V t ==> @PCFrelpropag rel W t) 
           (@PCF_rename_ _ _ f t).
Proof. unfold Proper in *; repeat red in *.
       intros rel H V W f t x y H0. 
       generalize dependent W. 
       dependent induction H0. 
       red in H. 
       
       constructor 1. apply H. auto.
       
       simpl. constructor 2. auto. 
       simpl. constructor 3. auto.
       simpl. constructor 4. auto.
       simpl. constructor 5. auto.
       (*intros W f. simpl. constructor 6. 
       set (ft := f t). apply ft. auto.*)
Qed.

Lemma PCF_rename_rt_clos:
 forall (rel:forall V t, relation (PCF V t)),
(forall (V W:ind_po_obj TY)(f:PCF_varmap V W) t,
  Proper (rel V t ==> rel W t)
            (@PCF_rename_ _ _ f t)) ->  
 forall V W f t,
 Proper (clos_refl_trans_1n _ (rel V t) ==> clos_refl_trans_1n _ (rel W t))
                 (@PCF_rename_ _ _ f t).
Proof. unfold Proper; repeat red. 
       intros rel H V W f t x y H0.
(*       generalize dependent W. *)
       dependent induction H0; simpl.
       intros. constructor 1.
       intros. constructor 2 with (PCF_rename_  f y).
        apply H. auto.
        apply IHclos_refl_trans_1n; auto.
Qed.

Lemma PCF_rename_beta:
forall (V1 W1 : ind_po_obj TY) (f0 : PCF_varmap V1 W1) (t1 : TY),
Proper (@PCF_beta V1 t1 ==> @PCF_beta W1 t1) (@PCF_rename_ _ _  f0 t1).
Proof. intros V W f t. 
       unfold Proper; repeat red.
       intros x y H.
       induction H. simpl.
       rewrite PCF_rename_substar.
       constructor.
       simpl.
       constructor 2.
       destruct (f t) as [ft fp]. simpl.
       apply fp. auto.
Qed.


Definition PCFbeta := PCFrelpropag PCF_beta.
(*
Lemma PCFbeta_Bottom
*)
Definition PCFbetaS : forall V t, relation (PCF V t):= 
   fun V t => clos_refl_trans_1n _ (@PCFbeta V t).

Instance BETA_struct (V:ipo) t : PO_obj_struct (PCF V t) := {
 Rel := @PCFbetaS V t
}.

Program Definition PCFBETA (V: ipo) : ipo :=
        fun t => Build_PO_obj (BETA_struct V t).

(*  Next Obligation.
    Proof. unfold PCFbetaS; apply Clos_RT_1n. Qed. *)
 

Program Definition PCF_rename (V W: ind_po_obj TY)(f:ind_po_mor V W) : 
          ind_po_mor (PCFBETA V) (PCFBETA W) := fun t =>
    Build_PreOrder_mor (a:= PCFBETA V t) 
                       (b:= PCFBETA W t) 
              (PO_fun := PCF_rename_ f (t:=t)) _ .

  Next Obligation.
    Proof. unfold Proper; repeat red. unfold PCFbeta.
           intros x y H.
           apply PCF_rename_rt_clos.
           intros V0 W0 F0 t0.
           apply PCF_rename_propag.
           intros V1 W1 f0 t1. unfold Proper. repeat red.
           intros.
           apply PCF_rename_beta. auto.
           auto.
    Qed.


Program Definition  PCF_inj (u:TY)(V:ind_po_obj TY) : 
      ind_po_mor (PCFBETA V) (PCFBETA (opt_TP u V)) := fun t =>
        Build_PreOrder_mor  (PO_fun := @PCF_inj_ u V t) _. 

  Next Obligation.
    Proof. unfold Proper; repeat red.
           unfold PCF_inj_. intros.
           
           apply PCF_rename_rt_clos.
            
           intros V0 W0 F0 t0.
           apply PCF_rename_propag.
           intros V1 W1 f0 t1. unfold Proper. repeat red.
           intros.
           apply PCF_rename_beta. auto.
           auto.
    Qed.
    

Lemma PCF_shift_propag (u:TY): 
    forall (rel: forall V t, relation (PCFBETA V t)),
   (forall (u:TY)(V W:ind_po_obj TY) (f:PCF_varmap V (PCFBETA W)) t, 
      Proper (@Rel _  ==> rel _ _) (@PCF_shift_ u _ _ f t)) 
    ->
    forall (V W: ind_po_obj TY)(f: PCF_varmap V (PCFBETA W)) t,
    Proper (@Rel _  ==> @PCFrelpropag rel _ _ ) 
           (@PCF_shift_ u _ _ f t).
Proof. unfold Proper in *; repeat red in *.
       intros u rel H V W f t x y H0. red in H. 
       generalize dependent W. 
       induction H0.
          
       constructor 1. apply H. constructor. auto.
       
       intros W f.  constructor 1. apply H.
       constructor 2. auto.
Qed.

  
Lemma PCF_shift_rt_clos (u:TY): 
    forall (rel: forall V t, relation (PCFBETA V t)),
   (forall (u:TY)(V W:ind_po_obj TY) (f:PCF_varmap V (PCFBETA W)) t, 
      Proper (@Rel _  ==> rel _ _) (@PCF_shift_ u _ _ f t)) 
    ->
    forall (V W: ind_po_obj TY)(f: PCF_varmap V (PCFBETA W)) t,
    Proper (@Rel _  ==> @clos_refl_trans_1n _ (rel _ _) ) 
           (@PCF_shift_ u _ _ f t).
Proof. unfold Proper; repeat red in *. 
       intros u rel H V W f t x y H0. red in H.
(*       generalize dependent W. *)
       induction H0.
       (*constructor 2 with (PCFVar (V:=opt_TP u W) (t:=u) (None_TP u W)).
       Focus 2.
          constructor.*)
 constructor 1.
 
 constructor 2 with (PCF_shift_ f (Some_TP u y)).
 apply H. constructor.  auto.
 constructor.
(* constructor 2 with (PCF_shift_  f (Some_TP u y)).
 apply H.
 constructor. auto.
 constructor.*)
Qed.



(* this is not true *)
(*
Lemma PCF_shift_beta (u:TY):
forall (V1 W1 : ind_po_obj TY) (f0 : PCF_varmap V1 (PCFBETA W1)) (t1 : TY),
Proper (@PreOrderRel _ ==> @PCF_beta _ _ ) (@PCF_shift_ u _ _  f0 t1).
Proof. intros u V W f t. 
       unfold Proper; repeat red.
       intros x y H.
       induction H. dependent induction x.  simpl.
       unfold PCF_shift_.
       destruct x. destruct y.
       dependent induction H; simpl.
       rewrite PCF_rename_substar.
       constructor.
Qed.
*)
Program Definition PCF_shift (u:TY) (V W: ind_po_obj TY)
      (f:ind_po_mor V (PCFBETA W)) : 
          ind_po_mor (opt_TP u V) (PCFBETA (opt_TP u W)) := fun t =>
    Build_PreOrder_mor (*(a:= PCFBETA V t) 
                       (b:= PCFBETA W t) *)
              (PO_fun := @PCF_shift_ u _ _ f t) _ .

  Next Obligation.
    Proof. unfold Proper; repeat red.
           intros x y H. induction H.
           constructor 1.
           
           simpl. 
           unfold PCF_inj_. 
           apply PCF_rename_rt_clos. 
           intros V0 W0 F0 t0.
           apply PCF_rename_propag.
           intros V1 W1 f0 t1. unfold Proper. repeat red.
           intros.
           apply PCF_rename_beta. auto.
          
           unfold PCFBETA in f. simpl in f.
           unfold PCFbetaS in f.
           
           destruct (f t) as [rt fp]. simpl.
           unfold Proper in fp. simpl in fp. red in fp.
           apply fp; auto.
Qed.
           

Lemma PCF_subst_propag : 
    forall (rel: forall V t, relation (PCF V t)),
   (forall (V W:ind_po_obj TY) (f:PCF_varmap V (PCFBETA W)) t, 
      Proper (rel V t ==> rel _ _) (fun v => PCF_subst_  v f )) 
    ->
    forall (V W: ind_po_obj TY)(f: PCF_varmap V (PCFBETA W)) t,
    Proper (@PCFrelpropag rel V t ==> @PCFrelpropag rel W t) 
           (fun v => PCF_subst_ v f ).
Proof. unfold Proper in *; repeat red in *.
       intros rel H V W f t x y H0. 
       generalize dependent W. 
       dependent induction H0.
       red in H. 
       
       constructor 1. apply H. auto.
       
       simpl. constructor 2. auto.
       
       simpl. intros; constructor 3. apply IHPCFrelpropag. auto.
       
       simpl. intros. constructor 4. 
         apply (IHPCFrelpropag _ (PCF_shift _ f)). auto.
       
       simpl; intros; constructor 5; auto.
         (*red in H.
       intros. constructor 1. apply H.
       set (ft := f t). apply ft.*)
Qed.
     

Lemma PCF_subst_rt_clos : 
    forall (rel: forall V t, relation (PCF V t)),
   (forall (V W:ind_po_obj TY) (f:PCF_varmap V (PCFBETA W)) t, 
      Proper (rel V t ==> rel _ _) (fun v => PCF_subst_  v f )) 
    ->
    forall (V W: ind_po_obj TY)(f: PCF_varmap V (PCFBETA W)) t,
    Proper (clos_refl_trans_1n _ (rel V t) ==> 
                       clos_refl_trans_1n _ (rel _ _)) 
           (fun v => PCF_subst_ v f ).
Proof. unfold Proper in *; repeat red in *.
       intros rel H V W f t x y H0. 
       generalize dependent W. 
       dependent induction H0.
       red in H. 
       
       constructor 1. 
       
       intros. constructor 2 with (PCF_subst_ y f).
        apply H. auto.
        apply IHclos_refl_trans_1n.
Qed.



Lemma PCF_subst_substar (V W:ind_po_obj TY) 
      (s t:TY) (M:PCF (opt_TP s V) t) N  f:
(PCF_subst_ (V:=V) (W:=W) (PCF_substar M N) (*fun t0 => f t0*) f) = 
  PCF_substar (PCF_subst_ M (PCF_shift_ (*fun t0 => f t0*) f)) (PCF_subst_ N f).
Proof. intros V W s t M N f.
       unfold PCF_substar. simpl.
       repeat rewrite PCF_subst_subst.
       apply PCF_subst_eq.
       intros t0 x.
       destruct x. unfold PCF_shift_. (*simpl.*) unfold PCF_inj_. 
         rewrite PCF_subst_rename. simpl. 
         rewrite  PCF_subst_var. auto.
         simpl.
         apply PCF_subst_eq; auto.
Qed.


Lemma betaS_App1 (V:ind_po_obj TY) (s t: TY) (M M':PCF V (arrow s t)) 
      N (rel: forall V t, relation (PCF V t)):
   clos_refl_trans_1n _ (@PCFrelpropag rel V _) M M' ->
   clos_refl_trans_1n _ (@PCFrelpropag rel V t) (PApp M N) (PApp M' N).
Proof. intros. generalize N. 
       induction H. constructor.
         intros. constructor 2 with (PApp y N0); auto.
                 constructor 2. auto.
Qed.

Lemma betaS_App2 (V:ind_po_obj TY) (s t: TY) (M:PCF V (arrow s t)) 
      N N' (rel: forall V t, relation (PCF V t)):
   clos_refl_trans_1n _ (@PCFrelpropag rel V _) N N' ->
   clos_refl_trans_1n _ (@PCFrelpropag rel V t) (PApp M N) (PApp M N').
Proof. intros. generalize M. 
       induction H. constructor.
         intros. constructor 2 with (PApp M0 y); auto.
                 constructor 3. auto.
Qed.

Lemma betaS_Lam (V:ind_po_obj TY) (s t: TY) (M M': PCF (opt_TP s V) t )
         (rel: forall V t, relation (PCF V t)):
      clos_refl_trans_1n _ (@PCFrelpropag rel _ _ ) M M' ->
      clos_refl_trans_1n _ (@PCFrelpropag rel V _ ) (PLam M) (PLam M').
Proof. intros.
       induction H. constructor.
           constructor 2 with (PLam y); auto.
           constructor 4. auto.
Qed.

Lemma betaS_Rec (V:ind_po_obj TY) (t: TY) (M M': PCF V (arrow t t))
         (rel: forall V t, relation (PCF V t)):
      clos_refl_trans_1n _ (@PCFrelpropag rel _ _ ) M M' ->
      clos_refl_trans_1n _ (@PCFrelpropag rel V _ ) (PRec M) (PRec M').
Proof. intros.
       induction H. constructor.
           constructor 2 with (PRec y); auto.
           constructor 5. auto.
Qed.

       

Lemma propag_clos_propag_clos (rel: forall V t, relation (PCF V t))
(V:ind_po_obj TY)(t:TY)(x y: PCF V t) 
(H: clos_refl_trans_1n _ (@PCFrelpropag 
       (fun V0 t0 => 
           fun x0 y0 => clos_refl_trans_1n _ 
                (@PCFrelpropag rel V0 t0) x0 y0) V t) x y):

clos_refl_trans_1n _ (@PCFrelpropag rel V t) x y.
Proof.
        intros rel  V t x y H.
        induction H.
          constructor.
          
          clear H0.
          generalize dependent z.
          induction H.
          
            transitivity v'; auto.
          
            intros. (*inversion IHclos_refl_trans_1n.*)
            transitivity (PApp M' N); auto.
            apply betaS_App1. apply IHPCFrelpropag. constructor.
            
            intros.
            transitivity (PApp M N'); auto.
            apply betaS_App2. apply IHPCFrelpropag. constructor.
            
            intros.
            transitivity (PLam M'); auto.
            apply betaS_Lam. apply IHPCFrelpropag. constructor.
            
            intros.
            transitivity (PRec M'); auto.
            apply betaS_Rec. apply IHPCFrelpropag. constructor.
Qed.
            


Lemma PCF_clos (V:ind_po_obj TY) 
      (rel: forall V t, relation (PCF V t)) (t:TY) x y:
          rel V t x y -> clos_refl_trans_1n _ (rel V t) x y.
Proof. intros. constructor 2 with y; try constructor; auto. Qed.


Program Definition PCF_subst (V W: ind_po_obj TY) 
      (f:PCF_varmap V (PCFBETA W)): ind_po_mor (PCFBETA V) (PCFBETA W) :=
     fun t => Build_PreOrder_mor 
        (PO_fun := fun x => PCF_subst_  x f) _ .

  Next Obligation.
    Proof. unfold Proper; repeat red.
           intros x y H. 
           generalize dependent W.
           
           induction H. constructor.

           intros.
                 (*constructor 2 with (PCF_subst_ y f); auto.
                 apply PCF_subst_propag; auto.
                 unfold Proper; repeat red; simpl; intros.
                 induction H1. (* PCF_beta x y *)
                      rewrite PCF_subst_substar; simpl; constructor.
                      simpl. (* not solvable *)*)
                 transitivity (PCF_subst_ y f); auto.
(*                 generalize dependent H0.
                 generalize dependent IHclos_refl_trans_1n.*)
                 apply propag_clos_propag_clos. 
                   generalize dependent W.
                   generalize dependent z.
                 induction H. intros. simpl.
                   Focus 2. intros. simpl. 
                   clear H0 IHclos_refl_trans_1n z.
                   apply betaS_App1. 
                   apply IHPCFrelpropag with M'; constructor.

                   Focus 2. intros. simpl. 
                   clear H0 IHclos_refl_trans_1n z.
                   apply betaS_App2. 
                   apply IHPCFrelpropag with N'; constructor.
                   
                   Focus 2. intros. simpl. 
                   clear H0 IHclos_refl_trans_1n z.
                   apply betaS_Lam. 
                   apply (IHPCFrelpropag M' (rt1n_refl _ _ _ ) 
                       (fun W f => rt1n_refl _ _ _ ) _ (PCF_shift s f)).
                   (*apply (IHPCFrelpropag M' (f:= PCF_shift s f)); 
                     constructor.*)
                     
                   Focus 2. intros. simpl. 
                   clear H0 IHclos_refl_trans_1n z.
                   apply betaS_Rec. 
                   apply IHPCFrelpropag with M'; constructor.
                   
                 induction H.
                       apply PCF_clos. constructor 1.
                       simpl. 
                       rewrite PCF_subst_substar. 
                       apply PCF_clos. constructor 1. constructor 1.
                       
                       simpl.
                       set (ft := f t).
                       destruct ft as [ftt fp]. simpl.
                       unfold Proper in fp; repeat red in fp.
                       apply PCF_clos. constructor 1.
                       apply fp.  auto.
Qed. 



Program Definition PCFVAR (V:ind_po_obj TY) : ind_po_mor V (PCFBETA V) := 
       fun t => Build_PreOrder_mor (PO_fun := fun a => PCFVar a) _.

  Next Obligation.
    Proof. unfold Proper; repeat red.
           intros x y H.
           constructor 2 with (PCFVar y); try constructor.
           constructor. auto.
    Qed.
           

End pcfo_syntax.

Section bla.

Require Export monad_haskell.


(*Variable V:ind_po_obj TY.*)

Program Instance syntax_monad_h: Monad_struct (IND_PO_struct TY) 
        (*fun V => PCFBETA V*) PCFBETA. 

Next Obligation.
   apply PCFVAR. Defined.
   
Next Obligation.
  apply (PCF_subst X). Defined.


(*:= {
(*  weta V t v:= PCFVAR v*)
(*  kleisli V W f := fun t x => PCF_subst x f *)
}.*)
  
  Next Obligation.
    Proof. unfold Proper; red. unfold eq_ind_po, syntax_monad_h_obligation_2.
           intros. unfold eq_PreOrder. simpl. intros; apply PCF_subst_eq. auto.
    Qed.
    
  Next Obligation.
    Proof. unfold eq_ind_po, eq_PreOrder,ind_po_comp. 
           simpl. auto.
    Qed.

  Next Obligation.
    Proof. unfold eq_ind_po,ind_po_id,syntax_monad_h_obligation_2,
             syntax_monad_h_obligation_1,eq_PreOrder,PreOrder_id.
           intros; simpl. apply PCF_subst_var.
    Qed.
 
  Next Obligation.
    Proof. unfold eq_ind_po,ind_po_id,syntax_monad_h_obligation_2,
             syntax_monad_h_obligation_1,eq_PreOrder,PreOrder_id.
           intros; simpl. rewrite PCF_subst_subst. auto.
    Qed.



End bla.
*)
