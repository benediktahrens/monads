Require Export CatSem.CAT.mon_cats.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Section enriched_cat_def.

Notation "a 'X' b" := (build_prod_mor _ _ a b) (at level 45).

Variable obM:Type.
Variable morM: obM -> obM -> Type.
Variable M: Cat_struct morM.
Variable MonM: mon_cat (C:=M).

Class Enriched_Cat (ob: Type) (hom: ob -> ob -> obM) := {
   idM: forall a : ob, morM (*@I obM morM M MonM*) I  (hom a a);
   compM: forall a b c: ob, morM (tens (hom a b, hom b c)) (hom a c);
   tens_assoc: forall a b c d, 
          Alpha ((hom a b,hom b c),hom c d) ;; 
             #tens (compM _ _ _ X id (hom _ _ )) ;; compM _ _ _  ==
           #tens (id (hom _ _ ) X compM _ _ _ ) ;;  
             compM _ _ _  ;
   idMl: forall a b,
          #tens (idM a X id (hom a b) ) ;; compM _ _ _ ==
               Lambda _ ;
   idMr: forall a b,
           #tens  (id (hom a b) X idM b ) ;; compM _ _ _ ==
               Rho _
}.



End enriched_cat_def.  


(** a category enriched over SET is an ordinary category *)

Section enriched_over_SET_MONOIDAL.
Variable obC : Type.
Variable morC : obC -> obC -> SET.
Variable C : Enriched_Cat (SET_MONOIDAL) morC.

Lemma default_setoid_eq (A:SET) : @Equivalence A (fun a b => a = b).
Proof.
  intro A;
  constructor;
  auto.
  intros a b c H;
  rewrite H;
  auto.
Qed.

Definition default_setoid A := Build_Setoid (default_setoid_eq A).

Program Instance Enriched_cat_Cat : Cat_struct morC := {
  mor_oid A B := default_setoid (morC A B);
  id a := idM (Enriched_Cat:=C) a tt ;
  comp a b c H H0 := compM (Enriched_Cat:=C) a b c (H,H0) 
                                                      }.
(*
Next Obligation.
Proof.
  unfold Proper.
  intros x y H x' y' H'.
  rewrite H,H'.
  auto.
Qed.
*)
Next Obligation.
Proof.
  set (H:= idMr (Enriched_Cat := C)).
  simpl in *.
  set (H':= H a b (f, tt)).
  simpl in *.
  auto.
Qed.
Next Obligation.
Proof.
  set (H:= idMl (Enriched_Cat := C)).
  simpl in *.
  set (H':= H a b (tt, f)).
  simpl in *.
  auto.
Qed.
Next Obligation. 
Proof.
  set (H:= tens_assoc (Enriched_Cat := C)).
  simpl in H.
  set (H' := H a b c d (f, (g,h))).
  auto.
Qed.

End enriched_over_SET_MONOIDAL.

