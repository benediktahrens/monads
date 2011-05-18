
Require Export CatSem.CAT.cat_INDEXED_TYPE.
Require Export CatSem.COMP.PCF.


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
  | var : forall t, V t -> ULC V t
  | abs : forall t : unit, ULC (opt t V) t -> ULC V t
  | app : forall t, ULC V t -> ULC V t -> ULC V t.

Fixpoint rename V W (f : V ---> W) t (y : ULC V t) : ULC W t :=
  match y with
  | var _ v => var (f _ v)
  | abs _ v => abs (rename ^f v)
  | app _  s t => app (rename f s) (rename f t)
  end.

Definition inj u V := rename (V:=V) (W:= opt u V) 
                (@some unit u V).

Definition _shift (u : unit) (V W : TT) (f : V ---> ULC W) : 
         V*  ---> ULC (W*) :=
   fun t v => 
   match v in (opt _ _ y) return (ULC (W *) y) with
   | some t0 p => inj u (f t0 p)
   | none => var (none u W)
   end.

Fixpoint subst V W (f : V ---> ULC W) t (y : ULC V t) : ULC W t :=
  match y with
  | var _ v => f _ v
  | abs _ v => abs (subst (_shift f) v)
  | app _ s t => app (subst f s) (subst f t)
  end.

Definition substar (u : unit) (V : TT) (M : ULC V u) :
           ULC (V*) ---> ULC V :=
 subst (fun t (y : opt u V t) => match y with
         | none => M
         | some _ v => var v
         end).

Notation "M [*:= N ]" := (substar N M) (at level 50).

(** Notations for functions *)
Notation "y //- f" := (rename f y)(at level 42, left associativity).
Notation "y >- f" := (_shift f y) (at level 40).
Notation "y >>= f" := (subst f y) (at level 42, left associativity).

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
       y >- @var _ = var y.
Proof.
  intros u V t y;
  induction y;
  fin.
Qed.

Hint Resolve shift_var : fin.
Hint Rewrite shift_var : fin.

 
Lemma var_lift_shift (u : unit) V W (f : V ---> W) t (y : opt u V t) :
     var (^f _ y) = y >- (f ;; @var _ ).
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
 Proper (equiv ==> equiv (Setoid:=mor_oid (ULC V) (ULC W))) 
                (@subst V W).

Lemma subst_var (V : TT) : 
    forall t (v : ULC V t), v >>= (@var V) = v .
Proof.
  intros V t y.
  induction y;
  fin.
  apply f_equal.
  rewrite <- IHy at 2.
  apply subst_eq.
  fin.
Qed.
  

Lemma subst_eq_rename V t (v : ULC V t) W (f : V ---> W)  : 
     v //- f  = v >>= (f ;; var (V:=W)).
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

Lemma rename_shift a V W Z (f : V ---> ULC W) (g : W ---> Z) t 
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


Lemma subst_shift_shift (u:unit) V (t : unit)(v : opt u V t)
         W Z (f: V ---> ULC W) (g: W ---> ULC Z):
    (v >- f) >>= (_shift g)  = 
             v >- (f ;; subst g).
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


Lemma subst_subst V t (v : ULC V t) W Z (f : V ---> ULC W) 
             (g : W ---> ULC Z) :
     v >>= f >>= g = v >>= (f;; subst g).
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
          s >>= (fun t z => var (f t z)) = s //- f.
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

Hint Resolve subst_var subst_subst lift_rename : fin.
Hint Rewrite subst_subst lift_rename: fin.



Obligation Tactic := fin.

Program Instance ULCm : 
     Monad_struct TT ULC := {
  weta := var;
  kleisli := subst
}.

Canonical Structure ULCM := Build_Monad ULCm.


(** some equalities : 
    - lift = rename
    - shift = _shift
*)

Lemma rename_lift V t (v : ULC V t) W (f : V ---> W) : 
       v //- f = lift (M:=ULCM) f _ v.
Proof.
  unfold lift;
  fin.
Qed.

Lemma shift_shift a V W (f : V ---> ULC W) t (y : opt a V t) :
        y >- f = shift f y. 
Proof.
  intros a V W f t y.
  destruct y;
  simpl;
  auto.
  unfold lift, inj.
  fin.
Qed.

Hint Resolve shift_shift rename_lift : fin.
Hint Rewrite shift_shift rename_lift : fin.



Definition PCF_ULC_type_mor : TY -> unit := fun _ => tt.


Program Instance ulc_app_s r s :
 Module_Hom_struct 
   (S:= ULCM [PCF_ULC_type_mor (r ~> s)] x (ULCM [PCF_ULC_type_mor r]))
   (T:=ULCM [PCF_ULC_type_mor s]) 
   (fun z t => app (fst t) (snd t)).

Definition ulc_app r s := Build_Module_Hom (ulc_app_s r s).

Program Instance ulc_abs_s r s : Module_Hom_struct
  (S:= d ULCM // PCF_ULC_type_mor r [PCF_ULC_type_mor s] )
  (T:= ULCM [PCF_ULC_type_mor (r ~> s)])
  (fun z t => abs t).

Definition ulc_abs r s := Build_Module_Hom (ulc_abs_s r s).

Definition ULC_fix (V : TT) t : ULC V t :=
   abs (
        app (V:=opt t V) (  
               abs (V:=opt t V)(
                      app (V:=opt t (opt t V)) 
                          (var (V:= opt t (opt t V)) 
                                        (some t (A:= opt t V) 
                                                ( none t (V) ))) 
                          (app (var (none t (V*))) (var (none t V*)))
                   )
            ) 
            (
               abs (

                      app (V:=opt t (opt t V)) 
                          (var (V:= opt t (opt t V)) 
                                        (some t (A:= opt t V) 
                                                ( none t (V) ))) 
                          (app (var (none t (V*))) (var (none t V*)))

                   )
            )
     ).

Program Instance ulc_rec_s t : Module_Hom_struct
 (S := ULCM [PCF_ULC_type_mor (t ~> t)]) 
 (T:=ULCM [PCF_ULC_type_mor t])
 (fun V Z => app (ULC_fix V tt) Z).

Definition ulc_rec t := Build_Module_Hom (ulc_rec_s t).

Program Instance ulc_ttt_s : Module_Hom_struct 
 (S:= Term (C:=MOD ULCM TYPE)) 
 (T:= ULCM [PCF_ULC_type_mor Bool])
 (fun V _ => abs (V:=V)
               (abs (V:= opt tt V) 
                   (var 
                      (some tt (A:=opt tt V)
                          (none tt V))))).

Definition ulc_ttt := Build_Module_Hom ulc_ttt_s.

Program Instance ulc_fff_s : Module_Hom_struct 
 (S:= Term (C:=MOD ULCM TYPE)) 
 (T:= ULCM [PCF_ULC_type_mor Bool])
 (fun V _ => abs (V:=V)
               (abs (V:= opt tt V) 
                   (var (none tt (V*))))).

Definition ulc_fff := Build_Module_Hom ulc_fff_s.

Fixpoint ULC_Nat (n : nat) (V : TT) := match n with
| 0 => abs (abs (var (none tt (opt tt V))))
| S n' => 
      abs (V:=V) (abs (V:=opt tt V) 
       (
        app ( app (ULC_Nat n' _) (var (none tt (opt tt V))))
            (var (some tt (A:=opt tt V) (none tt V)))))
end.

Obligation Tactic := idtac.

Program Instance ulc_nats_s m : Module_Hom_struct
 (S:= Term (C:=MOD ULCM TYPE))
 (T:= ULCM [PCF_ULC_type_mor Nat])
 (fun V _ => ULC_Nat m V).
Next Obligation.
Proof.
  simpl.
  intro m.
  induction m;
  simpl.
  intros. auto.
  
  intros V W f r.
  apply f_equal.
  apply f_equal.
  fin.
Qed.
 
Definition ulc_nats m := Build_Module_Hom (ulc_nats_s m).

(** plus = \n.\m.\f.\x. n(f) (m(f)x) *)

Definition ULC_plus (V : TT) := 
  abs (V:=V)
   (
     abs (V:=opt tt V)
         (
           abs (V:= opt tt (opt tt V))
               (
                 abs (V:= opt tt (opt tt (opt tt V)))
                  (
                    app (V:=opt tt (opt tt (opt tt (opt tt V))))
                      (app (V:=opt tt (opt tt (opt tt (opt tt V))))
                           (var (V:=opt tt (opt tt (opt tt (opt tt V))))
                                (some tt (some tt (some tt (none tt V)))))
                           (var (V:=opt tt (opt tt (opt tt (opt tt V))))
                                (some tt (A:=(opt tt (opt tt (opt tt V))))
                                     (none tt (opt tt (opt tt V)) ))) )   
                      (app (V:=opt tt (opt tt (opt tt (opt tt V))))
                           (app (V:=opt tt (opt tt (opt tt (opt tt V))))
                                (var (V:=opt tt (opt tt (opt tt (opt tt V))))
                                     (some tt (some tt (none tt (opt tt V) )))) 
                                (var (V:=opt tt (opt tt (opt tt (opt tt V))))
                                     (some tt (A:= opt tt (opt tt (opt tt V)))
                                         (none tt (opt tt (opt tt V))))))
                           (var (V:=opt tt (opt tt (opt tt (opt tt V))))
                                (none tt (opt tt (opt tt (opt tt V) )) )))

                  )
               
               )
         )
   ).

Obligation Tactic := fin.

(** succ = 1 + _ *)

Program Instance ulc_succ_s : Module_Hom_struct
  (S:= Term (C:=MOD ULCM TYPE))
  (T:= ULCM [PCF_ULC_type_mor (Nat ~> Nat)])
  (fun V _ => app (ULC_plus V) (ulc_nats (S 0) _ (tt) )).

Definition ulc_succ := Build_Module_Hom ulc_succ_s.

(** if then else = \a.\b.\c. a(b)(c) *)

Definition ULC_cond (V : TT) :=
     abs (V:=V)
        ( abs (V:=opt tt V)
            ( abs (V:=opt tt (opt tt V))
               (
                   app (V:= opt tt (opt tt (opt tt V)))
                      (app (V:= opt tt (opt tt (opt tt V)))
                         (var (V:= opt tt (opt tt (opt tt V)))
                            (some tt (some tt (none tt V)))) 
                         (var (some tt (none tt (opt tt V))))
                      )
                      (var (none tt (opt tt (opt tt V)))
                      )
               )
            )
        ).

Program Instance ulc_condn_s : Module_Hom_struct 
  (S := Term (C:=MOD ULCM TYPE))
  (T:= ULCM [PCF_ULC_type_mor (Bool ~> Nat ~> Nat ~> Nat)])
  (fun V _ => ULC_cond V).

Definition ulc_condn := Build_Module_Hom ulc_condn_s.

Program Instance ulc_condb_s : Module_Hom_struct 
  (S := Term (C:=MOD ULCM TYPE))
  (T:= ULCM [PCF_ULC_type_mor (Bool ~> Bool ~> Bool ~> Bool)])
  (fun V _ => ULC_cond V).

Definition ulc_condb := Build_Module_Hom ulc_condb_s.

Definition ULC_omega (V : TT) :=
    abs (V:= V)
      ( app (var (none tt V)) (var (none tt V))).

Program Instance ulc_bottom_s t : Module_Hom_struct 
  (S:= Term (C:= MOD ULCM TYPE))
  (T:= ULCM [PCF_ULC_type_mor t])
  (fun V _ => ULC_omega V).

Definition ulc_bottom t := Build_Module_Hom (ulc_bottom_s t).

(* zero? = Ln.((n)(true)false)true     *)

Definition ULC_zero (V : TT) := 
    abs (V:=V)
       (
       app (
              (app (var (none tt V))
                   (app (ulc_ttt _ tt) (ulc_fff _ tt)))
           )
           (
               ulc_ttt _ tt
           )
       ).

Program Instance ulc_zero_s : Module_Hom_struct 
  (S:= Term (C := MOD ULCM TYPE))
  (T:= ULCM [PCF_ULC_type_mor (Nat ~> Bool)])
  (fun V _ => ULC_zero V).

Definition ulc_zero := Build_Module_Hom ulc_zero_s.

Program Instance PCF_ULC_rep_s : 
 PCF_rep_s (U:=unit) (PCF_ULC_type_mor) ULCM := {

  app r s := ulc_app r s ;
  abs r s := ulc_abs r s ;
  rec t := ulc_rec t ;
  tttt := ulc_ttt ;
  ffff := ulc_fff ;
  nats m := ulc_nats m ;
  Succ := ulc_succ ;
  CondB := ulc_condb ;
  CondN := ulc_condn ;
  bottom t := ulc_bottom t ;
  Zero := ulc_zero
}.

Definition PCF_ULC_rep := Build_PCF_rep PCF_ULC_rep_s.

Definition PCF_ULC_compilation := InitMor PCF_ULC_rep.

End ULC_syntax.









