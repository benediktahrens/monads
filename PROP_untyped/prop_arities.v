
Require Export CatSem.PROP_untyped.initial.
Require Export CatSem.CAT.SO.

Require Import Coq.Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Automatic Introduction.
Unset Transparent Obligations.


Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
Notation "[[ T ]]" := (list T) (at level 5).

(* we have a taut mod P mapsto hat{P} : RMod P wPO *)
(* sufficient : define P mapsto hat{P} as functor between module cats *)

Section wPO_taut_mod.

Variable P : RMonad SM_po.
Variable M : RModule P PO.

Check RModule.

Obligation Tactic := unfold Proper, respectful; mauto;
        try apply (rmkl_eq M);
        try rew (rmklmkl M);
        try rew (rmkleta M); mauto.

Program Instance wPO_RMod_struct : RModule_struct P wPO M := {
  rmkleisli a b f := rmkleisli (RModule_struct:= M) f
}.

Definition wPO_RMod : RModule P wPO := Build_RModule wPO_RMod_struct.

End wPO_taut_mod.

Section monadic_subst_as_mod_hom.

Variable P : RMonad SM_po.
(*
Print RModule_Hom.

Definition bla:
(forall c : TYPE,
  (product (C:= RMOD P wPO) (wPO_RMod ((DER_RMOD_not PO P) P)) (wPO_RMod P)) c --->
  (wPO_RMod P) c).
simpl.
intro c.
apply (fun y => Rsubstar_not (snd y) (fst y)).
Defined.

(*
apply substar_not.
intro c.
apply (substar 
*)
Print bla.
*)

Ltac elim_option := match goal with [H : option _ |- _ ] => 
                     destruct H end.

Ltac t := mauto ; repeat (unfold Rsubstar_not ||
         match goal with [H: prod _ _ |-_] => destruct H end ||
         rew (rklkl P) || app (rkl_eq P) || elim_option ||  
         rew (rkleta P) || rew (retakl P ) || 
         rew (rlift_rkleisli P) || rew (rkleisli_rlift P) || 
         unfold rlift || rew (rkleta_eq (FM:=P)) || mauto ).

(*
Obligation Tactic := t.
Check Der_RMod_not.
Program Instance Rsubstar_mod_hom_struct : RModule_Hom_struct
   (M := product (C:=RMOD P wPO) ((DER_RMOD_not _ _ (wPO_RMod P))) (wPO_RMod P)) 
   (N := wPO_RMod P) 
   (fun c y => Rsubstar_not (snd y) (fst y)).
Definition Rsubstar_mod_hom := Build_RModule_Hom Rsubstar_mod_hom_struct.
*)
End monadic_subst_as_mod_hom.


Section S_Mods_and_Eqs.

Variable Sig : Signature.

Class S_Module_s (s_mod_rep : forall R : REPRESENTATION Sig, RMOD R wPO) := {
   S_Mod_Hom : forall (R S : REPRESENTATION Sig) (f : R ---> S), 
      s_mod_rep R ---> PbRMod f (s_mod_rep S)  }.

Record S_Module := {
  s_mod_rep :> forall R : REPRESENTATION Sig, RMOD R wPO ;
  s_mod_hom :> S_Module_s s_mod_rep }.
(*
 forall R S (f : R ---> S), 
      s_mod_rep R ---> PbRMod f (s_mod_rep S)  }.
*)

Print S_Mod_Hom. 
Class half_equation_struct (U V : S_Module) 
    (half_eq : forall R : REPRESENTATION Sig, s_mod_rep U R ---> s_mod_rep V R) := {
  comm_eq_s : forall (R S : REPRESENTATION Sig)  (f : R ---> S), 
     S_Mod_Hom (S_Module_s := U) f ;; PbRMod_Hom _ (half_eq S) == 
                half_eq R ;; S_Mod_Hom (S_Module_s := V) f }.


Record half_equation (U V : S_Module) := {
  half_eq :> forall R : REPRESENTATION Sig, 
         s_mod_rep U R ---> s_mod_rep V R ;
  half_eq_s :> half_equation_struct half_eq }.
(*
  comm_eq : forall R S (f : R ---> S), 
     S_Mod_Hom (S_Module_struct := U) f ;; PbRMod_Hom _ (half_eq S) == half_eq R ;; S_Mod_Hom f }.
*)

Section S_Module_algebraic.

Variable l : [[nat]].

Section ob.

Variable P : RMonad SM_po.
Variable M : RModule P PO.

Obligation Tactic := mauto; repeat (t || unfold Proper, respectful || 
                             app pm_mkl_eq || rew pm_mkl_mkl || app pm_mkl_weta).

Program Instance S_Mod_alg_ob_s : RModule_struct P wPO (fun V => prod_mod_po M V l) := {
  rmkleisli a b f := pm_mkl f 
}.

Definition S_Mod_alg_ob : RMOD P wPO := Build_RModule S_Mod_alg_ob_s.

End ob.

Section mor.

Variables P Q : RMonad SM_po.
Variable f : RMonad_Hom P Q.

(*
Variable M : RModule P PO.
Variable N : RModule Q PO.
*)
(*
Definition bla:
forall c : TYPE,
  mor (c:=wPO) ((S_Mod_alg_ob M) c) ((PbRMod f (E:=wPO) (S_Mod_alg_ob N)) c).
simpl.
apply (@Prod_mor_c1 _ _ f l).
*)

Obligation Tactic := repeat (mauto || rew prod_mod_c_kl || app pm_mkl_eq).

Program Instance S_Mod_alg_mor_s : RModule_Hom_struct 
       (M := S_Mod_alg_ob P) (N := PbRMod f (S_Mod_alg_ob Q)) 
       (@Prod_mor_c1 _ _ f (l)).

Definition S_Mod_alg_mor := Build_RModule_Hom S_Mod_alg_mor_s.

End mor.
Print S_Mod_alg_ob.
Instance S_Mod_alg_s : S_Module_s (fun R => S_Mod_alg_ob R) := {
  S_Mod_Hom R S f := S_Mod_alg_mor f }.

Definition S_Mod_alg := Build_S_Module S_Mod_alg_s.

End S_Module_algebraic.
Check S_Mod_alg.

(*
Definition S_Mod_alg_s l := S_Module_s (fun R => S_Mod_alg_ob l R)
           
Check S_Mod_alg_s.
*)



Check S_Module.
(*
Definition S_Mod_alg := S_Module 

Definition S_Mod_alg l : S_Module := 
  {| s_mod_rep := fun R => S_Mod_alg_ob l R ; 
     s_mod_hom := fun R S f => S_Mod_alg_mor l f |}.
*)

(* example substar : P^* x P ---> P *)
Section substitution.

Check S_Mod_alg_ob.


Definition blubb (P : REPRESENTATION Sig) :
(forall c : TYPE, (S_Mod_alg_ob [1; 0] P) c ---> (S_Mod_alg_ob [0] P) c) .
simpl.
intros.
simpl in *.
inversion X.
simpl in *.
inversion X1.
simpl in X2.
constructor.
simpl.
apply (Rsubstar_not X2 X0).
apply TTT.
Defined.
Print blubb.

(*
Definition extract_head P l a c (x : prod_mod_c P c (a::l)) : P (c ** a).
simpl.
intros.
inversion x.
apply X.
Defined.
Print extract_head.
induction x. simpl.
induction l; 
simpl.
intros.
destruct x.

intros
*)

Program Instance sub_struct (P : Representation Sig) : RModule_Hom_struct 
  (M:=S_Mod_alg_ob [1;0] P) (N:=S_Mod_alg_ob [0] P) (blubb (P:=P)).
Next Obligation.
Proof.
  dependent destruction x.
  dependent destruction x.
  simpl in *.
  apply CONSTR_eq; auto.
  unfold Rsubstar_not.
  rew (rklkl P).
  rew (rklkl P).
  apply (rkl_eq P).
  simpl.
  mauto. 
  destruct x0; simpl.
  unfold rlift.
  simpl.
  rew (retakl P).
  rew (rklkl P).
  rew (rkleta_eq (FM:=P)).
  intros.
  rew (retakl P).
  rew (retakl P).
Qed.

Print Assumptions sub_struct.

Definition sub (P : REPRESENTATION Sig) := Build_RModule_Hom (sub_struct P).

Check half_equation_struct.
(*
Check (fun R : REPRESENTATION Sig => Rsubstar_mod_hom R).
*)


(*
Program Instance subst_half_s : half_equation_struct 
      (U:=Build_S_Module (S_Mod_alg [1 ; 0])) (V:=S_Mod_alg [0]) sub.
Next Obligation.
Proof.
  
  dependent destruction x.
  dependent destruction x.
  dependent destruction x.
  
  simpl.
  apply CONSTR_eq; auto.
  unfold Rsubstar_not.
  
  rew (rmon_hom_rkl f).
  app (rkl_eq S).
  intros. 
  match goal with [H:option _ |- _]=>destruct H end;
  simpl.
  rew (rmon_hom_rweta f).
  auto.
Qed.

Definition subst_half := Build_half_equation subst_half_s.

Check subst_half.
*)
End substitution.

Definition half_eq_alg (doml codl : [[nat]]) := 
      half_equation (S_Mod_alg doml) (S_Mod_alg codl).

Record eq_alg := {
  doml : [[nat]] ;
  codl : [[nat]] ;
  eq1 : half_eq_alg doml codl ;
  eq2 : half_eq_alg doml codl }.
(*
Record eq_alg (doml codl : [[nat]]) := {
  eq1 : half_eq_alg doml codl ;
  eq2 : half_eq_alg doml codl }.
*)


Check eq1.

(*
Definition verifies_eq l l' (e : eq_alg l l') (P : REPRESENTATION Sig) : Prop.
intros.
destruct e.
simpl in *.
destruct eq3.
destruct eq4.
Check S_Mod_alg. Print S_Module.
apply (forall c : TYPE,
         forall x : s_mod_rep (S_Mod_alg l) P c, half_eq0 P _ x << half_eq1 _ _ x).
Defined.
Print verifies_eq.
*)
Check eq1.

Definition verifies_eq (e : eq_alg) (P : REPRESENTATION Sig) :=
  forall c (x : (s_mod_rep (S_Mod_alg (doml e)) P) c), 
       half_eq (eq1 e) P _ x << half_eq (eq2 e)_ _ x.

Definition Prop_Sig_struct (A : Type) := 
        forall a : A, eq_alg.

Definition verifies_prop_sig A (T : Prop_Sig_struct A) (R : REPRESENTATION Sig) :=
      forall a, verifies_eq (T a) R. Check verifies_prop_sig.

Section subcat.

Variable A : Type.
Variable T : Prop_Sig_struct A.

Program Instance Prop_Rep : SubCat_compat (REPRESENTATION Sig)
     (fun P => verifies_prop_sig T P) (fun a b f => True).

Definition PROP_REP : Cat := SubCat Prop_Rep.

Check PROP_REP.

Check eq_alg.

Check SC_inj_ob.

Definition prop_rel_c X (x y : UTS Sig X) : Prop :=
      forall R : PROP_REP, init (SC_inj_ob R) x << init (SC_inj_ob R) y.

Program Instance prop_rel_po X : PreOrder (@prop_rel_c X).
Next Obligation.
Proof.
  unfold Reflexive.
  unfold prop_rel_c.
  reflexivity.
Qed.
Next Obligation.
Proof.
  unfold Transitive.
  unfold prop_rel_c.
  simpl; intros.
  transitivity (
   init (SC_inj_ob
     (subobP:=fun P : Representation Sig => verifies_prop_sig (A:=A) T P) R)
  y); auto.
Qed.

Definition prop_rel_po_s X := Build_PO_obj_struct (prop_rel_po X).

Definition prop_rel X := Build_PO_obj (prop_rel_po_s X).

Program Instance subst_prop_rel_s X Y (f : X ---> UTS Sig Y) : 
   PO_mor_struct (a := prop_rel X) (b := prop_rel Y) 
     (subst f).
Next Obligation.
Proof.
  unfold Proper, respectful.
  unfold prop_rel_c.
  simpl. intros.
  assert (H':= init_kleisli (SC_inj_ob R)).
  simpl in H'.
  assert (H2 := H' X x _ (Sm_ind f)).
  simpl in H2.
  rewrite H2.
  clear H2.
  assert (H3 := H' X y _ (Sm_ind f)).
  rew H3.
  clear H3.
  apply PO_mor_monotone.
  auto.
Qed.

Definition subst_prop_rel X Y f := Build_PO_mor (subst_prop_rel_s X Y f).



Program Instance UTS_prop_rel_rmonad_s : RMonad_struct SM_po prop_rel := {
  rweta c := Sm_ind (@Var Sig c);
  rkleisli := subst_prop_rel
}.
Next Obligation.
Proof.
  unfold Proper; red.
  intros.
  unfold subst_prop_rel.
  simpl in *.
  rewrite (subst_eq _ H).
  auto.
Qed.
Next Obligation.
Proof.
  rewrite subst_var.
  auto.
Qed.
Next Obligation.
Proof.
  rewrite subst_subst.
  app subst_eq.
Qed.

Definition UTSP := Build_RMonad (UTS_prop_rel_rmonad_s).
Check @Rel.

Lemma lemma36 (l : [[nat]]) (V : Type)
    (x y : prod_mod_c (fun x : Type => UTS Sig x) V l)
    (H : prod_mod_c_rel (M:=prop_rel) x y) 
    (R : subob (fun P : Representation Sig => verifies_prop_sig (A:=A) T P)):
Rel (PO_obj_struct := prod_mod_po (SC_inj_ob R) V l) 
  (Prod_mor_c1 (init_mon (Sig:=Sig) (SC_inj_ob R)) x)
  (Prod_mor_c1 (init_mon (Sig:=Sig) (SC_inj_ob R)) y).
Proof.
  simpl.
  induction l; simpl;
  intros.
  dependent destruction x.
  dependent destruction y.
  constructor.
  dependent destruction x.
  simpl.
  dependent destruction y.
  simpl.
  constructor.
  simpl.
  Focus 2.
  apply IHl.
  dependent destruction H.
  auto.
  dependent destruction H.
  unfold prop_rel in H. simpl in H.
  unfold prop_rel_c in H.
  apply (H R).
Qed.

(*
  simpl.
  assert (H00 := @H0 R).
  apply H.
  assert (H00 := H0
  apply H0).
  assert (H2 := PO_mor_monotone init_mon).
  apply PO_mor_monotone.
  apply 
  auto.
  
  destruct y.
  inversion x.

.
i

i : sig_index Sig
V : Type
x : prod_mod_c (fun x : Type => UTS Sig x) V (sig (s:=Sig) i)
y : prod_mod_c (fun x : Type => UTS Sig x) V (sig (s:=Sig) i)
H : prod_mod_c_rel (M:=prop_rel) x y
R : subob (fun P : Representation Sig => verifies_prop_sig (A:=A) T P)
______________________________________(1/1)
Prod_mor_c1
  (init_mon (Sig:=Sig)
     (SC_inj_ob
        (subobP:=fun P : Representation Sig => verifies_prop_sig (A:=A) T P)
        R)) x <<
Prod_mor_c1
  (init_mon (Sig:=Sig)
     (SC_inj_ob
        (subobP:=fun P : Representation Sig => verifies_prop_sig (A:=A) T P)
        R)) y

*)




Check bla.
Program Instance Build_prop_pos (i : sig_index Sig) V : PO_mor_struct
  (a := prod_mod UTSP (sig i) V) (b := UTSP V)
  (fun X => Build (i:=i) (STSl_f_pm (V:=V) X)).
Next Obligation.
Proof.
  unfold Proper; red.
  intros; simpl.
  Check bba.
  unfold prop_rel_c.
  simpl.
  intros.
  assert (H2:= repr_hom_s (Representation_Hom_struct := init_representic (SC_inj_ob R))).
  simpl in H2.
  unfold commute in H2.
  simpl in H2.
  Check (init
  (SC_inj_ob
     (subobP:=fun P : Representation Sig => verifies_prop_sig (A:=A) T P) R)
  (Build (i:=i) (STSl_f_pm x))).
  rewrite <- H2.
  rewrite <- H2.
  apply PO_mor_monotone.
  apply lemma36.
  auto.
Qed.

Definition Build_prop_po i V := Build_PO_mor (Build_prop_pos i V).



Lemma _lshift_lshift_eq2 (b : nat)
  (X : TYPE) (W : Type) (f : PO_mor (sm_po X) (prop_rel W))
   (x : X ** b):
 lshift_c (P:=UTSP) (l:=b) (V:=X) (W:=W) f x =
    _lshift (Sig:=Sig) (l:=b) (V:=X) (W:=W) f x .
Proof.
  induction b;
  simpl; intros.
  auto. 
  rewrite IHb.
  apply _lshift_eq.
  simpl.
  intros.
  destruct x0; simpl;
  auto.
  unfold inj.
  rewrite subst_eq_rename.
  auto.
Qed.

Lemma sts_list_subst2 l X (v : prod_mod (UTSP) l X) 
       W (f : SM_po X ---> UTSP W):
  STSl_f_pm  (pm_mkl f v ) = list_subst (STSl_f_pm v) f.
Proof.
  induction v; simpl;
  intros. auto.
  apply constr_eq.
  apply subst_eq.
  intros.
  rewrite _lshift_lshift_eq2.
  auto.
  auto.
Qed.

Hint Resolve sts_list_subst : fin.
Hint Rewrite sts_list_subst : fin.


Program Instance Build_prop_s i : RModule_Hom_struct (Build_prop_po i).
Next Obligation.
Proof.
  rewrite sts_list_subst2.
  auto.
Qed.

Definition Build_prop i := Build_RModule_Hom (Build_prop_s i).


(**  UTSP has a structure as a representation of Sig *)

Canonical Structure UTSPrepr : Repr Sig UTSP := Build_prop.


Canonical Structure UTSPRepr : REPRESENTATION Sig := 
       Build_Representation (@UTSPrepr).


Lemma lemma36_2 (l : [[nat]]) (V : Type)
    (x y : prod_mod_c (fun x : Type => UTS Sig x) V l)
    (H : forall R : subob (fun P : Representation Sig => verifies_prop_sig (A:=A) T P),
        Rel (PO_obj_struct := prod_mod_po (SC_inj_ob R) V l) 
  (Prod_mor_c1 (init_mon (Sig:=Sig) (SC_inj_ob R)) x)
  (Prod_mor_c1 (init_mon (Sig:=Sig) (SC_inj_ob R)) y) ) :
prod_mod_c_rel (M:=prop_rel) x y.
Proof.
  simpl.
  induction l; simpl;
  intros.
  constructor.
  dependent destruction x.
  dependent destruction y.
  simpl.
  constructor.
  simpl.
  Focus 2.
  apply IHl.
  intros.
  assert (h:= H R).
  clear H.
  dependent destruction h.
  apply h.
  unfold prop_rel_c.
  intros.
  assert (h:= H R).
  dependent destruction h.
  apply H0.
Qed.


(* need forall e1 : half_equation,
     e1 (STSRepr Sig) c x = e1 (UTSPRepr Sig) c x *)

Program Instance debi1s : 
   RMonad_Hom_struct (P:=UTSM_sm Sig) (Q:=UTSP) 
   (fun c => Sm_ind (id (UTS Sig c))).
Next Obligation.
Proof.
  apply subst_eq.
  auto.
Qed.

Definition debi1 := Build_RMonad_Hom debi1s.

Program Instance debi2s : 
     Representation_Hom_struct (P:=STSRepr Sig) (Q:=UTSPRepr) debi1.
Next Obligation.
Proof.
  unfold commute.
  simpl.
  intros.
  apply f_equal.
  apply f_equal.
  induction x; simpl; intros; auto.
  apply CONSTR_eq; auto.
Qed.

Definition debi2 := Build_Representation_Hom debi2s.

Existing Instance STS_initial.

Check UTSPRepr.
Lemma half_eq_const_on_carrier : forall c x, 
   init_rep UTSPRepr c x = x.
Proof.
  simpl. Print InitMorUnique.
  assert (H:=InitMorUnique (C:=REPRESENTATION Sig) debi2).
  simpl in H.
  auto.
Qed.

(*
a : A
c : Type
x : prod_mod_c (fun x : Type => UTS Sig x) c (doml (T a))
half_eq0 : forall R : Representation Sig,
           RModule_Hom (S_Mod_alg_ob (doml (T a)) R)
             (S_Mod_alg_ob (codl (T a)) R)
comm_eq_s0 : forall (R S : Representation Sig) (f : Representation_Hom R S)
               (c : Type)
               (x : prod_mod_c (fun x : Type => R x) c (doml (T a))),
             (half_eq0 S) c (Prod_mor_c1 f x) =
             Prod_mor_c1 f ((half_eq0 R) c x)
H : (half_eq0 UTSPRepr) c (Prod_mor_c1 debi2 x) =
    Prod_mor_c1 debi2 ((half_eq0 (STSRepr Sig)) c x)
______________________________________(1/1)
*)
Lemma debi25 l c (x : prod_mod_c (fun x => UTS Sig x) c l) : 
      Prod_mor_c1 debi1 x = x.
Proof.
  induction l;
  simpl; intros.
  dependent destruction x.
  simpl. auto.
  dependent destruction x.
  simpl.
  apply CONSTR_eq.
  auto.
  auto.
Qed.


Lemma debi3s a c x:
forall h : half_eq_alg (doml (T a)) (codl (T a)),
(h (STSRepr Sig)) c x = (h UTSPRepr) c x.
Proof.
  simpl.
  intros.
  destruct h.
  simpl in *.
  destruct half_eq_s0.
  simpl in *.
  assert (H:= comm_eq_s0 _ _ (debi2) c x).
  rewrite debi25 in H.
  rewrite debi25 in H.
  auto.
Qed.

Lemma UTSPRepr_sig_prop : verifies_prop_sig T UTSPRepr.
Proof.
  unfold verifies_prop_sig.
  unfold verifies_eq.
  simpl; intros.
  apply lemma36_2.
  intros. 
  assert (H2:= repr_hom_s (Representation_Hom_struct := init_representic (SC_inj_ob R))).
  unfold commute in H2;
  simpl in H2.
  Print comm_eq_s.
  assert (H4:=comm_eq_s (half_equation_struct := eq1 (T a))).
  assert (H5:=H4 _ _ (init_rep (SC_inj_ob R))).
  simpl in H5.
  clear H4.
  rerew (debi3s x (eq2 (T a)) ).
  rerew (debi3s x (eq1 (T a))).
  rewrite <- H5.
  clear H5.
  assert (H4:=comm_eq_s (half_equation_struct := eq2 (T a))).
  assert (H5:=H4 _ _ (init_rep (SC_inj_ob R))).
  simpl in H5.
  rewrite <- H5.
  clear H5 H4.
  simpl in *.
  destruct R; simpl in *.
  unfold verifies_prop_sig in v.
  unfold verifies_eq in v.
  simpl in v.
  apply v.
Qed.

Definition UTSPREPR : PROP_REP := 
 exist (fun a : Representation Sig => verifies_prop_sig (A:=A) T a) UTSPRepr
  UTSPRepr_sig_prop.


Section init.

Variable R : PROP_REP.



Program Instance init_prop_s V : PO_mor_struct
    (a:=(FINJ _ UTSPREPR) V) (b:=(FINJ _ R) V) (init (FINJ _ R) (V:=V)).
Next Obligation.
Proof.
  unfold Proper, respectful.
  intros.
  unfold prop_rel_c in H.
  simpl in H.
  apply H.
Qed.


Definition init_prop_po V := Build_PO_mor (init_prop_s V).

Program Instance init_prop_mon_s : RMonad_Hom_struct
      (P:=FINJ _ UTSPREPR)(Q:=FINJ _ R) init_prop_po.
Next Obligation.
Proof.
  rewrite init_kleisli2.
  app (rkl_eq (proj1_sig R)).
Qed.
 

Definition init_prop_mon := Build_RMonad_Hom init_prop_mon_s.
Check Representation_Hom_struct.

Lemma prod_mor_eq_init_list2 (i : sig_index Sig) V
       (x : prod_mod_c (fun V => UTS Sig V) V (sig i)) :
  Prod_mor_c1 init_prop_mon x = init_list _ (STSl_f_pm x).
Proof.
  induction x;
  simpl; auto.
  unfold FINJ in IHx. simpl in *.
  rewrite  IHx.
  simpl. auto.
Qed.


Program Instance init_prop_rep : Representation_Hom_struct 
       init_prop_mon.
Next Obligation.
Proof.
  unfold commute.
  simpl; intros.
  rewrite prod_mor_eq_init_list2.
  auto.
Qed.

Definition init_prop_re := Build_Representation_Hom init_prop_rep.

Definition init_prop : UTSPREPR ---> R := 
        exist _ init_prop_re I.

Section unique.

Variable f : UTSPREPR ---> R.

Lemma init_prop_unique : f == init_prop.
Proof.
  simpl. intros.
  destruct f.
  simpl in *.
  clear t.
  clear f.
  unfold SC_inj_ob in x1.
  simpl in x1.
  destruct R.
  simpl in *.
  clear R.
  
  apply (@STSind Sig
     (fun V v => x1 V v = init x2 v)
     (fun V l v => Prod_mor x1 l V (pm_f_STSl v) = init_list _ v));
  simpl; intros;
  auto.
  rew (rmon_hom_rweta x1).
  rewrite <- (one_way u).
  assert (H':=@repr_hom_s _ _ _ x1 x1).
  unfold commute in H'.
  simpl in H'.
  rewrite <- H'.
  
  rewrite one_way.
  rewrite H. auto.
  rewrite H0. simpl.
  rewrite H.
  auto.
Qed.

End unique.

End init.

Program Instance INITIAL_PROP : Initial PROP_REP := {
  Init := UTSPREPR ;
  InitMor := init_prop ;
  InitMorUnique := init_prop_unique
}.

End subcat.
End S_Mods_and_Eqs.
