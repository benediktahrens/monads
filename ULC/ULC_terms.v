
Require Export CatSem.ULC.ULC_syntax.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Automatic Introduction.

(* Y *)
Definition ULC_Y_h (V : TT) : ULC (V*) :=
  Abs (App (Var (Some (None)))
	   (App (Var None)
	        (Var None))). 

Definition ULC_Y (V : TT) : ULC V :=
  Abs (App (ULC_Y_h _ ) (ULC_Y_h _ )).

(* the Turing fixpoint operator Theta.
   it has (Theta g) --> g (Theta g)
*)
Definition ULC_theta_h (V : TT) : ULC V :=
 Abs(
  Abs(
   App 
    (Var None)
    (App 
      (App
        (Var (Some None))
        (Var (Some None)))
      (Var None))
)).

Definition ULC_theta (V : TT) : ULC V :=
App (ULC_theta_h V) (ULC_theta_h V).


(* Y = \f. (\x. f (x x)) (\x. f (x x))  *)

Definition ULC_fix (V : TT) : ULC V := 
 Abs (
   App 
    (Abs 
      (App 
        (Var (Some None))
        (App 
          (Var None)
          (Var None))
     ))
    (Abs 
      (App          
        (Var (Some None))
        (App 
          (Var None)
          (Var None))
     ))

).


(* not: [m+1] = 
     \f.\n. ([m] f) (f n)

instead : [m+1] = \fn. f ([m] f n)
*)

(* note : [m] has 2*m redexes in it *)

Fixpoint ULC_Nat (n : nat) (V : TT) :
        ULC V := 
 match n with
| 0 => Abs (Abs (Var None))
| S n' =>
    Abs(
     Abs (
      App 
       (Var (Some None))
       (App 
         (App
           (ULC_Nat n' _ )
           (Var (Some None)))
         (Var (None)))))
end.


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

Lemma ulc_nats_subst n :
 forall (V W : TT)
       (f : V ---> ULC W),
     ULC_Nat n W = ULC_Nat n V >>= f.
Proof.
  induction n.
  reflexivity.
  simpl.
  intros.
  rewrite <- (IHn (V * *)).
  reflexivity.
Qed.


(* - pow 0 T = \x.x 
   - pow Sn T = \x. T ((pow n T) x)

   - pow 1 T = \x. T ((pow 0 T) x) = 
             = \x. T (\y.y x) -> \x. T x

   - pow 2 T = \x. T ((pow 1 T) x) =
             -> \x. T ((\x.Tx) x) ->
                \x. T (T x)
*)

Fixpoint pow n V (T : ULC V) : ULC V:=
  match n return ULC V with
  | 0 => Abs (Var None)
  | S n' => Abs 
       (App 
        (inj T)
        (App 
          (inj (pow n' T))
          (Var (None))))
  end.


(* lets build  fun f x => App f (f^n x) *)
(* - ULC_nat_skel 0 f y = y
   - ULC_nat_skel Sn f y = App f (...)
*)

Fixpoint ULC_nat_skel n V  
   (f : ULC V* )
   (y : ULC V * * ) :
      ULC V * *  :=
match n with
| 0 => y
| S n' => App (inj f) (ULC_nat_skel n' f y)
end.

(*  take the to-be-bound-next free variables as f and y *)

Definition ULC_nat_sk n V : ULC V* * :=
 ULC_nat_skel n (Var None) (Var None).


(*  have free variables f, y

   - ULC_Nat_noredex 0 = y
   - ULC_Nat_noredex Sn = f (...)
*)
(*
Fixpoint ULC_Nat_noredex n V t :=
  match n with
  | 0 => Var (V:=opt t (opt t V)) (none t (opt t V))
  | S n' => App _ (Var (some t (none t V)))
                   (ULC_Nat_noredex n' V t)
  end.
*0
(* ULC_nat_sk = ULC_Nat_noredex *)
(* both have two free variables f, y
*)
*)
(*
Lemma ULC_nat_sk_ULC_Nat_noredex n V :
   ULC_nat_sk n V = ULC_Nat_noredex n V tt.
Proof.
  induction n.
  reflexivity.
  simpl; intros.
  rewrite <- IHn.
  reflexivity.
Qed.
*)
(* we bind the free variables f, y 
   in order to define the natural numbers
*)
(*
Definition ULC_Nat_nox n V t : ULC V t :=
  Abs (
   Abs (ULC_Nat_noredex n V t)).
*)
Definition ULC_N n V : ULC V :=
  Abs (Abs (ULC_nat_sk n V)).


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
   ULC_nat_skel n a b //- (Some (A:=V * *)) = 
     ULC_nat_skel n (inj a) (b //- Some (A:= V * * )).
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

Lemma ULC_N_skel_substar n V (M : ULC (V* * )) 
                (a : ULC (V* * )) 
                (b:ULC V * * * ) :
  inj (ULC_nat_skel n (a) b [*:= M]) =
  ( ULC_nat_skel n a ((inj (b[*:= M])))).
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
  rewrite lift_rename.
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


(* the following lemma are the same as for skel.
   no surprise, the defs are equal
*)
(*
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
*)


(* Nat n reduces to Nat_nox n *)
(* Nat n has 2n redexes *)
(*
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
     (App (Var (V:=(V * ) * ) (t:=tt) 
             (some tt (A:=V * ) (t:=tt) (none tt V)))
        (App
           (App 

(Abs (Abs (ULC_Nat_noredex n (V * ) * tt)))

              (Var (V:=(V * ) * ) (t:=tt)
                 (some tt (A:=V * ) (t:=tt) (none tt V))))
           (Var (V:=(V * ) * ) (t:=tt) (none tt V * )))))
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
 *)


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

(*
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
  rewrite <- ulc_nats_subst.
  apply cp_Abs.
  apply cp_App2.
  apply cp_App1.
  unfold inj;
  simpl.
  assert (H':= rename_beta (Some (A:=V))
                (IHn V T)).
  apply (beta_trans H').
  apply beta_eq.
  simpl.
  rewrite <- ulc_nats_rename.
  auto.
Qed.
*)

Definition ULC_Nat_alt n V : ULC V :=
  Abs (pow n (Var None)).


(** plus = \n.\m.\f.\x. n(f) (m(f)x) *)
(*
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
*)
(** SUCC := \nfx.f (n f x) *)
Definition ULCsucc V : ULC V := 
  Abs (
   Abs (
    Abs (
      App 
       (Var (Some None))
       (App 
         (App
           (Var (Some (Some None)))
           (Var (Some None))
         )
         (Var None)
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


(** if then else = \a.\b.\c. a(b)(c) *)

Definition ULC_cond (V : TT) :=
     Abs (V:=V)
        ( Abs (V:= V*)
            ( Abs (V:=V * * )
               (
                   App (V:= V * * * ) 
                      (App (V:= V * * * )
                         (Var (V:= V * * * )
                            (Some (Some None)))
                         (Var (Some None)
                      ))
                      (Var None)
                      )
               )
            )
        .


Definition ULC_omega (V : TT) :=
    Abs (V:= V)
      ( App  (Var (None)) (Var (None))).

(* TRUE = \xy.x *)
Definition ULC_True V : ULC V :=
  Abs (Abs (Var (Some (None)))).

(* FALSE = \xy.y *)
Definition ULC_False V : ULC V := 
  Abs (Abs (Var (None))).


(* zero? = \n.((n)(true)false)true     *)

Definition ULC_zero (V : TT) := 
  Abs (
   App  
     (App 
       (Var (None (A:=V) ))
       (Abs  (ULC_False _)))
     (ULC_True _ )).


(* T f := \gh. h (g f) *)
Definition ULC_T V f : ULC V :=
  Abs (
   Abs (
    App 
     (Var (None))
     (App 
       (Var (Some(None)))
       (inj (inj f))))
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

(*PRED := \nfx.n (\gh.h (g f)) (\u.x) (\u.u)*)

Definition ULC_pred_alt (V : TT) : ULC V :=
  Abs (
   Abs (
    Abs (
     App 
       (App 
         (App 
           (Var (Some(Some(None))))         
           (ULC_T (Var (Some (None))))
)
         (Abs (Var (Some (None)))))
       (Abs (Var (None)))
))).


Definition ULC_pred (V : TT) : ULC V :=
  Abs (
   Abs (
    Abs (
     App 
       (App 
         (App 
           (Var (Some(Some (None))))         
           (Abs (
             Abs (
              App 
               (Var (None))
               (App 
                 (Var (Some (None)))
                 (Var (Some (Some (Some (None)))))
             )))))
         (Abs (Var (Some(None )))))
       (Abs (Var (None)))
))).

Lemma ULC_pred_alt_correct V : 
  ULC_pred_alt V = ULC_pred V.
Proof.
  reflexivity.
Qed.

