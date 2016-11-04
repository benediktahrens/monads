Require Export CatSem.CAT.monad_h_module.
Require Export CatSem.CAT.NT.
Require Export CatSem.CAT.product.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Section gen_monad_morphism.
(*
Variables obC obD : Type.
Variable morC : obC -> obC -> Type.
Variable morD : obD -> obD -> Type.
Variable C : Cat_struct morC.
Variable D : Cat_struct morD.
*)
Variables C D : Cat.
Variable P : Monad C.
Variable Q : Monad D.

Variable F : Functor C D.

(** is P;F a module C -> D over P ?*)

Program Instance F_mod_s : Module_struct P (D:=D) 
 (fun x => F (P x)) := {
  mkleisli a b f := #F (mkleisli f)
}.
Next Obligation.
Proof.
  intros; simpl.
  unfold Proper;
  red.
  intros f g H.
  apply (functor_map_morphism (kleisli_oid H)).
Qed.
Next Obligation.
Proof.
  intros; simpl.
  rewrite <- FComp.
  apply (functor_map_morphism (dist _ _ )).
Qed.
Next Obligation.
Proof.
  intros; simpl.
  monad;
  cat.
Qed.
  
Definition F_mod : MOD P D := Build_Module F_mod_s.


(** generalizing the previos one *)


Class colax_Monad_Hom_struct (Tau : forall c, F (P c) ---> Q (F c)) := {
  gen_monad_hom_kl : forall c d (f : c ---> P d),
       #F (kleisli f) ;; Tau _  == 
          Tau _ ;; (kleisli (#F f ;; Tau _ )) ;
  gen_monad_hom_weta : forall c : C,
       #F (weta c) ;; Tau _  == weta _ 
}.

Record colax_Monad_Hom := {
  gen_monad_hom:> forall c, F (P c) ---> Q (F c);
  gen_monad_hom_struct :> colax_Monad_Hom_struct gen_monad_hom
}.


Existing Instance gen_monad_hom_struct.

Section Monad_Hom_NT_PB.

Variable M : colax_Monad_Hom.

Program Instance colax_Monad_Hom_NatTrans : 
   NT_struct (F:=CompF (MFunc P) F)
            (G:=CompF F (MFunc Q)) (fun c : C => M c).
Next Obligation.
Proof.
  simpl; intros.
  unfold lift.
  simpl.
  assert (H:=gen_monad_hom_kl (colax_Monad_Hom_struct := M) (f;; weta d)).
  simpl in *.
  rewrite H.
  apply praecomp.
  apply kleisli_oid.
  rewrite FComp.
  rewrite assoc.
  rewrite (gen_monad_hom_weta (colax_Monad_Hom_struct := M)).
  cat.
Qed.

(*End Monad_Hom_NT.*)

(*Section pullback.*)
(*
Variable obE : Type.
Variable morE : obE -> obE -> Type.
Variable E : Cat morE.
*)
Variable E : Cat.
Section pullback_ob.

Variable N : MOD Q E.

Program Instance PModule_struct : Module_struct P (D:=E) 
      (fun c => N (F c)) := {
  mkleisli a b f := mkleisli (Module_struct := N)(#F f ;; M _ )
}.
Next Obligation.
Proof.
  intros; simpl.
  unfold Proper;
  red.
  intros x y H.
  apply mkleisli_oid.
  apply postcomp.
  apply (functor_map_morphism H).
Qed.
Next Obligation.
Proof.
  intros; simpl.
  rewrite mkl_mkl.
  apply mkleisli_oid.
  rewrite FComp.
  repeat rewrite assoc.
  apply praecomp.
  assert (H:=gen_monad_hom_kl (colax_Monad_Hom_struct := M)).
  simpl in *.
  mod.
Qed.
Next Obligation.
Proof.
  intros; simpl.
  rewrite gen_monad_hom_weta.
  mod.
Qed.

Definition PModule : MOD P E := Build_Module PModule_struct.

End pullback_ob.

(** pullback along a gen monad hom is functorial *)

Section pullback_mor.

Variables N N' : MOD Q E.
Variable r : N ---> N'.

Program Instance PMod_Hom_s : Module_Hom_struct 
     (S := PModule N) (T:= PModule N') (fun c => r (F c) ).
Next Obligation.
  simpl; intros.
  mod;
  try apply r.
Qed.

Definition PMod_Hom := Build_Module_Hom PMod_Hom_s.

End pullback_mor.

Variables N N' : MOD Q E.

Variable eprod : Cat_Prod E.

Obligation Tactic := cat.

Definition prod_mod : (forall x : C,
        (product (PModule N) (PModule N')) x ---> (PModule (product N N')) x) := (fun x => id (Cat_struct := E) (product (N (F x)) (N' (F x)))).


Program Instance PROD_PM_s : Module_Hom_struct 
       (S := product (PModule N) (PModule N'))
       (T := PModule (product N N')) 
       prod_mod.

Definition PROD_PM := Build_Module_Hom PROD_PM_s.

End Monad_Hom_NT_PB.



(*End gen_monad_morphism.*)


Variable M : colax_Monad_Hom.

Program Instance PMod_ind_Hom_s : Module_Hom_struct
      (S:= F_mod) (T:=PModule M Q) M.
Next Obligation.
Proof.
  simpl; intros;
  rewrite gen_monad_hom_kl.
  cat.
Qed.

Definition PMod_ind_Hom := Build_Module_Hom PMod_ind_Hom_s.  

End gen_monad_morphism.

Existing Instance gen_monad_hom_struct.







