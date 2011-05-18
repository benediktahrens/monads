Require Export CatSem.ORDER.ulc.
Require Export CatSem.ORDER.ulc_order_rep_eq.
Require Export CatSem.CAT.orders_lemmas.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.



Section initiality.

Variable R : ULCPO_REP.

Fixpoint init_d V (y : ULC_Rep V) : R V :=
  match y in ULC _ return R V with
  | Var v => rweta (RMonad_struct := R ) _  v
  | Abs v => abs _ (init_d v)
  | App v1 v2 => app _ (init_d v1, init_d v2)
  end.

Lemma init_rename V (y : ULC_Rep V) W (f : V ---> W) :
    init_d (y //- f) = 
       rlift R f (init_d y).
Proof.
  intros V y.
  induction y;
  simpl; intros.
  
  assert (H:=rlift_rweta R).
  simpl in H; auto.
  
  unfold rlift. simpl.
  rerew (rmhom_rmkl (abs (ULCPO_rep_struct := R))).
  apply f_equal.
  rewrite IHy.
  unfold rlift.
  simpl.
  apply (rkl_eq R).
  simpl; intros.
  assert (H3:=shift_not_rweta R).
  simpl in *.
  destruct x as [t z | ];
  simpl; auto.
  unfold rlift; simpl;
  rew (retakl R).
  
  unfold rlift. simpl.
  rerew (rmhom_rmkl (app (ULCPO_rep_struct := R))).
  apply f_equal.
  rewrite IHy1.
  rewrite IHy2.
  auto.
Qed.

Hint Rewrite init_rename : fin.

Lemma init_subst V (y : ULC_Rep V) W (f : V ---> ULC W):
      init_d (y >>= f) = 
        rkleisli (RMonad_struct := R) 
           (Sm_ind (fun v => init_d (f v))) (init_d y).
Proof.
  induction y;
  simpl; intros.
  rew (retakl R).
  
  rerew (rmhom_rmkl (abs (ULCPO_rep_struct := R))).
  apply f_equal.
  rewrite IHy.
  simpl.
  apply (rkl_eq R).
  simpl; intros z.
  destruct z; fin.
   unfold inj. fin.
  rerew (rmhom_rmkl (app (ULCPO_rep_struct := R))).
  fin.
Qed.

Hint Rewrite init_subst : fin.
Hint Resolve init_subst : fin.

Lemma beta_init_d V (v v': ULC V)
         (H : beta v v') :
       init_d  v << init_d v'.
Proof.
  intros V v v' H.
  induction H.
  simpl.
  unfold substar.
  rewrite init_subst.
   assert (H3:=beta_red (ULCPO_rep_struct:=R) 
            (V:=V) (init_d M) (init_d N)).
   simpl in *.
   apply (Rel_eq_r H3).
   unfold Rsubstar.
   apply (rkl_eq R).
   simpl.
   intros z.
   unfold Rsubst_star_map.
   destruct z as [t0 z | ];
   simpl; auto.
Qed.

Lemma beta_star_init_d V (v v': ULC V)
         (H : beta_star v v') :
       init_d  v << init_d v'.
Proof.
  intros V v v' H.
  induction H.
  
  apply beta_init_d.
  auto.
  
  assert (H':=PO_mor_monotone (app (ULCPO_rep_struct:=R) V)).
  simpl in H'.
  apply H'.
  constructor.
  auto.
  reflexivity.
   
  assert (H':=PO_mor_monotone (app (ULCPO_rep_struct:=R) V)).
  simpl in H'.
  apply H'.
  constructor.
  reflexivity.
  auto.
  
  assert (H':=PO_mor_monotone (abs (ULCPO_rep_struct:=R) V)).
  simpl in H'.
  apply H'.
  auto.
Qed.

Obligation Tactic := idtac.

Program Instance init_s V : PO_mor_struct (init_d (V:=V)).
Next Obligation.
Proof.
  unfold Proper;
  red.
  intros V x y H.
  induction H;
  simpl.
  apply Rel_refl.
  
  transitivity (init_d y); auto.
  
  apply beta_star_init_d.
  auto.
Qed.

Definition init V := Build_PO_mor (init_s V).

Obligation Tactic := fin; try apply (rkl_eq R); fin.

Program Instance init_mon_s : 
   RMonad_Hom_struct (P:=ULCBETA) (Q:=R) init.

Definition initM := Build_RMonad_Hom init_mon_s.

Program Instance init_rep_s : ULCPO_rep_Hom_struct initM.

Definition initR := Build_ULCPO_rep_Hom init_rep_s.

Section unicity.

Variable f : ULC_Rep ---> R.

Lemma unique : f == initR.
Proof.
  intros V z;
  induction z;
  simpl;
  try rew (rmon_hom_rweta f);
  try rew (abs_Hom (ULCPO_rep_Hom_struct := f));
  try match goal with [H:ULC _ , H1:ULC _  |- _ ] => 
          rew (app_Hom (ULCPO_rep_Hom_struct := f) (H,H1)) end;
  fin.
Qed.

End unicity.

End initiality.

Program Instance ULCPO_init : Initial ULCPO_REP := {
  Init := ULC_Rep ;
  InitMor := initR ;
  InitMorUnique := unique
}.

Print Assumptions ULCPO_init.





