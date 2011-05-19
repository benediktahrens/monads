
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

Record S_Module := {
  s_mod_rep : forall R : REPRESENTATION Sig, RMOD R wPO ;
  s_mod_hom : forall R S (f : R ---> S), 
      s_mod_rep R ---> PbRMod f (s_mod_rep S)  }.

Record half_equation (U V : S_Module) := {
  half_eq : forall R : REPRESENTATION Sig, 
         s_mod_rep U R ---> s_mod_rep V R ;
  comm_eq : forall R S (f : R ---> S), 
     s_mod_hom U f ;; PbRMod_Hom _ (half_eq S) == half_eq R ;; s_mod_hom V f }.


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

End S_Module_algebraic.

Definition S_Mod_alg l : S_Module := 
  {| s_mod_rep := fun R => S_Mod_alg_ob l R ; 
     s_mod_hom := fun R S f => S_Mod_alg_mor l f |}.


Section substitution.

Check S_Mod_alg_ob.

Definition bla (P : REPRESENTATION Sig) :
(forall c : TYPE, (S_Mod_alg_ob [1; 0] P) c ---> (S_Mod_alg_ob [0] P) c) .
simpl.
intros.
simpl in *.
inversion X.
simpl in *. Check Rsubstar_not.
inversion X1.
simpl in X2.
constructor.
simpl.
apply (Rsubstar_not X2 X0).
apply TTT.
Defined.
Print bla.

Definition extract_head P l a c (x : prod_mod_c P c (a::l)) : P (c ** a).
simpl.
intros.
induction x. simpl.
induction l; 
simpl.
intros.
destruct x.

intros

Program Instance sub (P : Representation Sig) : RModule_Hom_struct 
  (M:=S_Mod_alg_ob [1;0] P) (N:=S_Mod_alg_ob [0] P) (bla (P:=P)).
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

Print Assumptions sub.



  simpl.
  rew (rkleta P).
  app (rkl_eq P).
  elim_option.
  simpl.
  simpl.
  apply f_equal.
  simpl.
  dependent induction x.
  apply IHx.
  simpl.
  unfold bla.
  simpl.
  (fun V y => Rsubstar_not (snd y) (fst y)).

Check half_equation.

Check (fun R : REPRESENTATION Sig => Rsubstar_mod_hom R).

Program Definition subst_half : half_equation (S_Mod_alg [1 ; 0]) (S_Mod_alg [0]) :=
   {| half_eq := fun R => Rsubstar_mod_hom  R ;
      half_comm := _ |}.

(*
Coercion wPO_RMod : RModule >-> RModule.
Coercion wPO_RMod : obj >-> obj.
*)

Variable obC : Type.
Variable morC : obC -> obC -> Type.
Variable C : Cat_struct morC.



(* first test : monadic subsitution is a half-equation *)



