Require Import Coq.Relations.Relations.

Require Export CatSem.PCF_o_c.RPCF_rep.
Require Export CatSem.PCF_o_c.ULC_syntax1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Automatic Introduction.

Unset Printing Implicit Defensive.
(* this will suppress printing
  of implicit arguments of Var *)

Definition PCF_ULC_type_mor : TY -> unit := fun _ => tt.


Program Instance ULCApp_pos u v c:
PO_mor_struct 
 (a:=PO_product (ipo_proj (ULCBETA c) tt) (ipo_proj (ULCBETA c) u))
  (b:=ipo_proj (ULCBETA c) v)
  (fun y => App _ (fst y) (snd y)).
Next Obligation.
Proof.
  unfold Proper;
  red.
  intros y z H.
  destruct H.
  simpl in *.
  transitivity (App v v' w).
  apply cp_App1.
  auto.
  apply cp_App2;
  auto.
Qed.


Definition ULCApp_car u v c:
  (Prod_RMod PO_prod (Fib_RMod tt ULCBETAM) 
                     (Fib_RMod u ULCBETAM)) c --->
  (Fib_RMod v ULCBETAM) c :=
       Build_PO_mor (ULCApp_pos u v c).

Program Instance ulc_app_s u v:
 RModule_Hom_struct 
  (M:=Prod_RMod PO_prod (Fib_RMod tt ULCBETAM) (Fib_RMod u ULCBETAM))
  (N:=Fib_RMod v ULCBETAM)
  (ULCApp_car u v).

Definition ulc_app u v :
 (ULCBETAM [tt]) x (ULCBETAM [u]) ---> ULCBETAM [v] :=
    Build_RModule_Hom (ulc_app_s u v).

Program Instance ULCAbs_pos u v c:
PO_mor_struct 
 (a:=ipo_proj (ULCBETA c *) v) 
 (b:=ipo_proj (ULCBETA c) tt)
 (Abs (V:=c)(r:=u)(s:=v)).
Next Obligation.
Proof.
  unfold Proper;
  red.
  intros y z H.
  apply cp_Abs.
  auto.
Qed.


Definition ULCAbs_car u v c:
  (Fib_RMod v (Der_RMod u ULCBETAM)) c ---> 
   (Fib_RMod tt ULCBETAM) c :=
  Build_PO_mor (ULCAbs_pos u v c). 

Program Instance ulc_abs_s u v :
RModule_Hom_struct 
 (M:=Fib_RMod v (Der_RMod u ULCBETAM)) 
 (N:=Fib_RMod tt ULCBETAM)
 (ULCAbs_car u v).
Next Obligation.
Proof.
  apply f_equal.
  apply subst_eq.
  intros.
  rewrite shift_shift.
  reflexivity.
Qed.

Definition ulc_abs u v : 
  d ULCBETAM // u [v] ---> ULCBETAM [tt] :=
 Build_RModule_Hom (ulc_abs_s u v).


Program Instance ULCRec_pos t V:
PO_mor_struct 
  (a:=ipo_proj (ULCBETA V) tt)
  (b:=ipo_proj (ULCBETA V) t)
  (fun y => App _ (ULC_theta _ ) y).
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
(ULCBETAM [tt]) V --->
  (ULCBETAM [t]) V :=
 Build_PO_mor (ULCRec_pos _ V).


Program Instance ulc_rec_s t : RModule_Hom_struct
 (M := ULCBETAM [tt]) 
 (N:=ULCBETAM [t])
 (ULCRec_car t).

Definition ulc_rec t := Build_RModule_Hom (ulc_rec_s t).


Program Instance ULCttt_pos : 
    forall V : unit -> Type,
 PO_mor_struct (a:=PO_TERM)  
   (b:=ipo_proj (ULCBETA V)(PCF_ULC_type_mor Bool))
   (fun _ => ULC_True V).
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
   (fun _ => ULC_False V).
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
                              (W:=ULCBETAM (W* ) * )
                  (fun t z => _shift (_shift f) z))).
                  simpl in H'.
  rewrite H'. apply f_equal.
  auto.
  apply tt.
Qed.
 
Definition ulc_nats m := Build_RModule_Hom (ulc_nats_s m).
(*
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
*)

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

Obligation Tactic := fin.

Program Instance ulc_succ_s : RModule_Hom_struct
  (M:= Term (C:=RMOD ULCBETAM PO))
  (N:= ULCBETAM [PCF_ULC_type_mor (Nat ~> Nat)])
  ULCSucc_car.

Definition ulc_succ := Build_RModule_Hom ulc_succ_s.


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


Program Instance ULC_bottom_pos :
forall t (V : unit -> Type),
PO_mor_struct (a:=PO_TERM) 
 (b:=ipo_proj (ULCBETA V) (t))
 (fun _ => match t with tt => ULC_omega V end).
Next Obligation.
Proof.
  unfold Proper;
  red.
  reflexivity.
Qed.

Definition ULCbottom_car t V :
Term (C:=RMOD ULCBETAM _ ) V ---> 
  (ULCBETAM [t]) V :=
  Build_PO_mor (ULC_bottom_pos t V).

Program Instance ulc_bottom_s t : RModule_Hom_struct 
  (M:= Term (C:= RMOD ULCBETAM PO))
  (N:= ULCBETAM [t])
  (ULCbottom_car t).
Next Obligation.
Proof.
  destruct t.
  simpl.
  auto.
Qed.

Definition ulc_bottom t := Build_RModule_Hom (ulc_bottom_s t).


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



Obligation Tactic := idtac.

Program Instance PCF_ULC_rep_s : 
 PCFPO_rep_struct (U:=unit) ULCBETAM (PCF_ULC_type_mor)
 (fun _ _ => tt) := {

  app r s := ulc_app r s;
  abs r s := ulc_abs r s;
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
Obligation 1. (* beta reduction *)
Proof.
  simpl; intros.
  apply clos_refl_trans_1n_contains.
  apply relorig.
  constructor.
Qed.
(*
Obligation 2. (* propag app 1 *)
Proof.
  simpl; intros.
  apply cp_App1;
  auto.
Qed.
Obligation 3. (* propag app 2 *)
Proof.
  simpl; intros.
  apply cp_App2;
  auto.
Qed.
Obligation 4. (* propag abs *)
Proof.
  simpl; intros.
  apply cp_Abs;
  auto.
Qed.
Obligation 5. (* propag rec *)
Proof.
  simpl; intros.
  apply cp_App2;
  auto.
Qed.
*)
Obligation 2. (* if true n m -> n *)
Proof.
  simpl; intros.
  unfold ULC_cond.
  assert (H:= app_abs 
     (Abs
        (Abs
             (App tt
                (App _
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
transitivity (App tt (App _
(Abs
         (Abs
            (App tt
               (App _
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
(App tt
     (App tt
        (Abs
           (Abs
              (App tt
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
(App tt
     (App tt
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
  (App tt
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
Next Obligation. (* if false n m -> m *)
Proof.
  intros; simpl.
  unfold ULC_cond.
  assert (H:= app_abs 
  (Abs
     (Abs
       (App tt
         (App tt
          (Var (V:=((V *) *) *) (t:=tt)
               (some tt (A:=(V *) *) (t:=tt)
                 (some tt (A:=V *) (t:=tt) (none tt V))))
              (Var (V:=((V *) *) *) (t:=tt)
             (some tt (A:=(V *) *) (t:=tt) (none tt V *))))
          (Var (V:=((V *) *) *) (t:=tt) (none tt (V *) *)))))

(Abs (Abs (Var (V:=(V *) *) (t:=tt) (none tt (opt tt V))))))
.
unfold substar in H.
simpl in H.
unfold inj in H.
simpl in H.

transitivity(
(App tt
     (App tt
  (Abs
         (Abs
            (App tt
               (App tt
                  (Abs
                     (Abs
                        (Var (V:=(((V *) *) *) *) (t:=tt)
                           (^(^(some tt (A:=V *))) tt
                         (^(^(some tt (A:=V))) tt (none tt (opt tt V)))))))
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
(App tt
     (App tt
        (Abs
           (Abs
              (App tt
                 (Abs (Var (V:=((V *) *) *) (t:=tt) (none tt (V *) *)))
                 (Var (V:=(V *) *) (t:=tt) (none tt (opt tt V)))))) n) m)
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
(App tt
   (App tt
     (Abs
        (Abs

          (Var (V:=(V *) *) (t:=tt) (none tt (opt tt V)))

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
(App tt
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
Next Obligation. (* if true b b' -> b *)
Proof.
  intros; simpl.
  unfold ULC_cond.
  assert (H:= app_abs 
     (Abs
          (Abs
          (App tt
              (App tt
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
transitivity (App tt (App tt
(Abs
         (Abs
            (App tt
               (App tt
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
(App tt
     (App tt
        (Abs
           (Abs
              (App tt
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
(App tt
     (App tt
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
  (App tt
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
Next Obligation. (* if false b b' -> b' *)
Proof.
  intros; simpl.
  unfold ULC_cond.
  assert (H:= app_abs 
  (Abs
     (Abs
       (App tt
         (App tt
          (Var (V:=((V *) *) *) (t:=tt)
               (some tt (A:=(V *) *) (t:=tt)
                 (some tt (A:=V *) (t:=tt) (none tt V))))
              (Var (V:=((V *) *) *) (t:=tt)
             (some tt (A:=(V *) *) (t:=tt) (none tt V *))))
          (Var (V:=((V *) *) *) (t:=tt) (none tt (V *) *)))))

(Abs (Abs (Var (V:=(V *) *) (t:=tt) (none tt (opt tt V))))))
.
unfold substar in H.
simpl in H.
unfold inj in H.
simpl in H.

transitivity(
(App tt
     (App tt
  (Abs
         (Abs
            (App tt
               (App tt
                  (Abs
                     (Abs
                        (Var (V:=(((V *) *) *) *) (t:=tt)
                           (^(^(some tt (A:=V *))) tt
                              (^(^(some tt (A:=V))) tt  
                             (none tt (opt tt V)))))))
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
(App tt
     (App tt
        (Abs
           (Abs
              (App tt
                 (Abs (Var (V:=((V *) *) *) (t:=tt) (none tt (V *) *)))
                 (Var (V:=(V *) *) (t:=tt) (none tt (opt tt V)))))) u) v)
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
(App tt
   (App tt
     (Abs
        (Abs

          (Var (V:=(V *) *) (t:=tt) (none tt (opt tt V)))

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
(App tt
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

Next Obligation. (* S [n] -> [n+1] *)
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
Obligation 10. (* pred 0 --> 0 *)
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
Obligation 11. (* rec g --> g (rec g) *) 
Proof.
simpl.
intros V t g.
destruct t.
apply App1_app_abs.
unfold substar;
simpl.
unfold inj; simpl.
apply app_abs_red;
unfold substar;
simpl.
reflexivity.
Qed.
Obligation 9. (* Pred (Succ n) --> n *)
simpl.         (* not : Pred (n+1) --> n *)
intros V n.
generalize dependent V.

induction n.

intros.

apply app_abs_red.
sim.

sim.

apply Abs_Abs_App1_App1_App1_app_abs.
sim.
apply Abs_Abs_App1_App1_app_abs.
sim.
apply Abs_Abs_App1_app_abs.
sim.
apply Abs_Abs_App1_app_abs.
sim.
apply Abs_Abs_app_abs;
sim.
apply Abs_Abs_app_abs.
sim.
apply Abs_Abs_App1_App1_app_abs.
sim.
apply Abs_Abs_App1_app_abs.
sim.
apply Abs_Abs_app_abs.
sim.
reflexivity.

intro V.
apply app_abs_red;
sim.
rew (ULC_nat_skel_rename_lift).
rew (ULC_nat_skel_rename_lift).
unfold lift;
sim.
unfold ULC_N.
sim.
apply cp_Abs.
apply cp_Abs.

apply App1_App1_App1_app_abs.
sim.
rew (ULC_nat_skel_rename_lift).
rew (ULC_nat_skel_rename_lift).
unfold lift;
sim.
apply App1_App1_app_abs.
sim.
rewrite (ULC_N_skel_subst_shift).
sim.
unfold lift;
sim.
apply App1_app_abs.
sim.
rewrite (ULC_N_skel_subst_shift).
sim.
apply App1_app_abs;
sim.
rew (ULC_nat_skel_rename_lift).
apply app_abs_red;
sim.
rewrite (ULC_N_skel_subst_shift).
sim.
apply app_abs_red;
sim.
apply App1_App1_app_abs.
sim.
rewrite (ULC_N_skel_subst_shift).
sim.
unfold lift;
sim.
apply App1_App1_Abs_app_abs;
sim.
rew (ULC_nat_skel_rename_some).
sim.
unfold lift;
sim.
apply App1_app_abs.
sim.
rewrite (ULC_N_skel_subst_shift).
sim.
unfold lift;
sim.
unfold ULC_nat_sk.
simpl.
sim.

clear IHn.
generalize dependent V.

induction n.
simpl.
intros.
apply app_abs_red.
sim.
apply App2_app_abs;
sim.
reflexivity.

sim.
unfold lift;
sim.

intro V.
assert (H:=IHn V).
transitivity (

App tt (Var (some tt (none tt V)))
(App tt
      (Abs
         (App tt (Var (none tt (V *) *))
            (App tt
               (ULC_nat_skel n
                  (Abs
                     (Abs
                        (App tt (Var (none tt ((V *) *) *))
                           (App tt (Var (some tt (none tt (V *) *)))
                              (Var (some tt (some tt (some tt (none tt V)))))))))
                  (Abs (Var (some tt (some tt (none tt V *))))))
               (Var (some tt (some tt (none tt V)))))))
      (Var (some tt (none tt V))))
).

Focus 2.
apply cp_App2.
apply H.
apply App1_Abs_App2_App1_app_abs.
sim.
rew (ULC_nat_skel_rename_some).
sim.
unfold lift;
sim.
apply app_abs_red.
sim.
rewrite (ULC_N_skel_subst_shift).
sim.
reflexivity.
Qed.

Definition PCF_ULC := Build_PCFPO_rep 
      (type_type:=unit) (type_arrow := fun _ _ => tt)
      (pcf_rep_monad:=ULCBETAM)
      (type_mor:=fun t => tt)
      (fun _ _ => eq_refl)
      PCF_ULC_rep_s.




