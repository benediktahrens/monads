Require Export CatSem.CAT.retype_functor_po.
Require Export CatSem.CAT.rmonad_gen_type_po.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.


Section transp_lift_id.

Variables U U' : Type.
Variable f : U -> U'.
(*Variable P : Monad (ITYPE U).*)
Variable Q : RMonad (IDelta U').

Hypothesis H : forall t, f t = f t.
Variable V : IPO U.
Variable t' : U'.


Lemma rlift_transp_id : forall y : Q (retype (fun t => f t) V) t',
   rlift Q (transp (f:= f)(g:= f) H (V:=V)) 
           _ y = y.
Proof.
  intro y.
  assert (H'' := rlift_eq_id Q).
  apply H''.
  apply transp_id.
Qed.

End transp_lift_id.

Section comp.

Variables U U' U'' : Type.
Variable f : U -> U'.
Variable f' : U' -> U''.

Variable P : RMonad (IDelta U).
Variable Q : RMonad (IDelta U').
Variable R : RMonad (IDelta U'').

Variable M : gen_RMonad_Hom P Q 
	(G1:=RETYPE (fun t => f t))
	(G2:=RETYPE_PO (fun t => f t))    
	(NNNT1 (fun t => f t)).
Variable N : gen_RMonad_Hom Q R 
	 (G1:=RETYPE (fun t => f' t))
         (G2:=RETYPE_PO (fun t => f' t)) 
	 (NNNT1 (fun t => f' t)).

Obligation Tactic := idtac.

Definition RMon_comp_data c:
(forall t,
  (retype_ipo (fun t0 => f' (f t0)) (P c)) t ->
  (R (retype (fun t0 => f' (f t0)) c)) t) :=
 fun t
    (y : retype (fun t => f' (f t)) (P c) t) =>
   match y with ctype _ z =>
    (rlift R (double_retype_1 (f:=f) 
                            (f':=f') (V:=c))) _
          (N _ _ (ctype (fun t => f' t)
               (M _ _ (ctype (fun t => f t) z ))))
   end.

Program Instance RMon_cc c :
ipo_mor_struct 
  (a:=retype_ipo (fun t => f' (f t)) (P c))
  (b:=R (retype (fun t => f' (f t)) c))
  (RMon_comp_data (c:=c)).
Next Obligation.
Proof.
  intros c t.
  unfold Proper;
  red.
  simpl.
  intros y z H.
  induction H.
  simpl.
  apply (rlift R _ ).
  apply (N (retype ( fun t0 => f t0) c)).
  constructor.
  apply (M c).
  constructor;
  auto.
Qed.


Definition RMon_car:
(forall c : ITYPE U,
  (RETYPE_PO (fun t => f' (f t))) (P c) --->
  R ((RETYPE (fun t => f' (f t))) c)) :=
   fun c => Build_ipo_mor (RMon_cc c).

Program Instance RMon_comp_s :
gen_RMonad_Hom_struct 
 (P:=P) (Q:=R) (G1:=RETYPE (fun t => f' (f t)))
   (G2:=RETYPE_PO (fun t => f' (f t)))
   (NNNT1 (fun t => f' (f t)))
   RMon_car.
Next Obligation.
Proof.
  simpl.
  intros c t z.
  destruct z as [t z];
  simpl.
  rew (gen_rmonad_hom_rweta M _ _ (ctype _ z)).
  simpl.
  assert (H:=gen_rmonad_hom_rweta N ).
  simpl in H.
  set (y := ctype (fun t0 => f t0) z).
  simpl in *.
  rew (H _ _ (ctype (*fun t => tcomp N t*) _ y)).
  rew (rlift_rweta R).
Qed.
Next Obligation.
Proof.
  simpl.
  intros V W g t z.
  destruct z as [t y].
  simpl.
  rew (gen_rh_rkl M).
  rew (gen_rh_rkl N).
  rew (rlift_rkleisli (M:=R)).
  rew (rkleisli_rlift (M:=R)).
  apply (rkl_eq R).
  
  intros t0 z.
  destruct z as [t0 z].
  simpl.
  destruct z as [t0 z].
  simpl.
  auto.
Qed.


Definition RMon_comp := Build_gen_RMonad_Hom RMon_comp_s.

End comp.
