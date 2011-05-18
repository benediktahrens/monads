Require Export CatSem.ORDER.tlc.
Require Export CatSem.ORDER.tlc_order_rep_eq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.



Section initiality.

Variable R : TLCPO_REP.

Fixpoint init_d V t (y : TLC_Rep V t) : R V t :=
  match y in TLC _ t return R V t with
  | var _ v => rweta (RMonad_struct := R ) _ _ v
  | abs _ _ v => Abs _ _ _ (init_d v)
  | app _ _ v1 v2 => App _ _ _ (init_d v1, init_d v2)
  end.

Lemma init_rename V t (y : TLC_Rep V t) W (f : V ---> W) :
    init_d (y //- f) = 
       rlift R f _ (init_d y).
Proof.
  intros V t y.
  induction y;
  simpl; intros.
  
  assert (H:=rlift_rweta R).
  simpl in H; auto.
  
  unfold rlift. simpl.
  rerew (rmhom_rmkl (Abs (TLCPO_rep_struct := R) r s)).
  apply f_equal.
  rewrite IHy.
  unfold rlift.
  simpl.
  apply (rkl_eq R).
  simpl; intros.
  assert (H3:=sshift_rweta R).
  simpl in *.
  destruct z as [t z | ];
  simpl; auto.
  unfold rlift; simpl;
  rew (retakl R).
  
  unfold rlift. simpl.
  rerew (rmhom_rmkl (App (TLCPO_rep_struct := R) r s)).
  apply f_equal.
  rewrite IHy1.
  rewrite IHy2.
  auto.
Qed.

Hint Rewrite init_rename : fin.

Lemma init_subst V t (y : TLC_Rep V t) W (f : V ---> TLC W):
      init_d (y >>= f) = 
        rkleisli (RMonad_struct := R) 
           (SM_ind (fun t v => init_d (f t v))) _ (init_d y).
Proof.
  intros V t y.
  induction y;
  simpl; intros.
  rew (retakl R).
  
  rerew (rmhom_rmkl (Abs (TLCPO_rep_struct := R) r s)).
  apply f_equal.
  rewrite IHy.
  simpl.
  apply (rkl_eq R).
  simpl; intros t z.
  destruct z; fin.
   unfold _inj. fin.
  rerew (rmhom_rmkl (App (TLCPO_rep_struct := R) r s)).
  fin.
Qed.

Hint Rewrite init_subst : fin.
Hint Resolve init_subst : fin.

Lemma beta1_init_d V t (v v': TLC V t)
         (H : beta1 v v') :
       init_d  v <<< init_d v'.
Proof.
  intros V t v v' H.
  induction H.
  simpl.
  unfold _substar.
  rewrite init_subst.
   assert (H3:=beta_red (TLCPO_rep_struct:=R) 
          (r:=s) (s:=t) (V:=V) (init_d M) (init_d N)).
   simpl in *.
   apply (IRel_eq_r H3).
   unfold Rsubstar.
   apply (rkl_eq R).
   simpl.
   intros t0 z.
   unfold Rsubst_star_map.
   destruct z as [t0 z | ];
   simpl; auto.
Qed.

Lemma beta_star_init_d V t (v v': TLC V t)
         (H : beta_star v v') :
       init_d  v <<< init_d v'.
Proof.
  intros V t v v' H.
  induction H.
  
  apply beta1_init_d.
  auto.
  
  assert (H':=PO_mor_monotone (App (TLCPO_rep_struct:=R) s t V)).
  simpl in H'.
  apply H'.
  constructor.
  auto.
  reflexivity.
   
  assert (H':=PO_mor_monotone (App (TLCPO_rep_struct:=R) s t V)).
  simpl in H'.
  apply H'.
  constructor.
  reflexivity.
  auto.
  
  assert (H':=PO_mor_monotone (Abs (TLCPO_rep_struct:=R) s t V)).
  simpl in H'.
  apply H'.
  auto.
Qed.

Obligation Tactic := idtac.

Program Instance init_s V : ipo_mor_struct (init_d (V:=V)).
Next Obligation.
Proof.
  unfold Proper;
  red.
  intros V t x y H.
  induction H;
  simpl.
  apply IRel_refl.
  
  transitivity (init_d y); auto.
  
  apply beta_star_init_d.
  auto.
Qed.

Definition init V := Build_ipo_mor (init_s V).

Obligation Tactic := fin; try apply (rkl_eq R); fin.

Program Instance init_mon_s : 
   RMonad_Hom_struct (P:=TLCB) (Q:=R) init.

Definition initM := Build_RMonad_Hom init_mon_s.

Program Instance init_rep_s : TLCPO_rep_Hom_struct initM.

Definition initR := Build_TLCPO_rep_Hom init_rep_s.

Section unicity.

Variable f : TLC_Rep ---> R.

Lemma unique : f == initR.
Proof.
  intros V t z;
  induction z;
  simpl;
  try rew (rmon_hom_rweta f);
  try rew (Abs_Hom (TLCPO_rep_Hom_struct := f));
  try match goal with [H:TLC _ (?a ~> _), H1:TLC _ ?a |- _ ] => 
          rew (App_Hom (TLCPO_rep_Hom_struct := f) (H,H1)) end;
  fin.
Qed.

End unicity.

End initiality.

Program Instance TLCPO_init : Initial TLCPO_REP := {
  Init := TLC_Rep ;
  InitMor := initR ;
  InitMorUnique := unique
}.

Print Assumptions TLCPO_init.





