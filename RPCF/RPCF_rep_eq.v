Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Eqdep.

Require Export CatSem.RPCF.RPCF_rep_hom.
Require Import CatSem.CAT.rmonad_gen_comp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.


Inductive eq_Rep (P R : PCFPO_rep) : relation (PCFPO_rep_Hom P R) :=
 | eq_rep : forall (a c : PCFPO_rep_Hom P R), 
            forall H : (forall t, Sorts_map c t = Sorts_map a t),
            (forall V, (*rep_Hom_monad*) a V ;; rlift R (Transp H V)
                                    == 
                       Transp_ord H (P V) ;; (*rep_Hom_monad*) c V ) ->
             
             eq_Rep a c.
  
(** the defined relation is an equivalence and 
    may hence serve as equality 
*)

Lemma eq_Rep_equiv (P R: PCFPO_rep) : 
   @Equivalence (PCFPO_rep_Hom P R) 
     (@eq_Rep P R).
Proof.
 intros P R.
 split.
 
 unfold Reflexive.
 intro M. 
 assert (H': forall t, Sorts_map M t = Sorts_map M t) by 
       (intros; reflexivity).

 apply (eq_rep (H:=H')).
 
 simpl.
 intros V t y.
 destruct y as [t y].
 
 simpl. 
 rewrite (UIP_refl _ _ (H' t)).
 simpl.
 assert (H:= rlift_transp_id).
 simpl in *.
 rewrite H.
 auto.

  (* now symmetric *)
 
 unfold Symmetric.
 intros M N H.
 destruct H.
  assert (H': forall t, Sorts_map a t = Sorts_map c t) by auto.
 apply (eq_rep (H:=H')). 
 simpl; intros V t y.
 destruct a.
 destruct c.
 simpl in *.
 assert (H3 : Sorts_map = Sorts_map0).
 apply (functional_extensionality).
 auto.
 
 generalize dependent y. 
 generalize dependent H'.
 generalize dependent rep_Hom_monad0.
 generalize dependent rep_Hom_monad.
 generalize dependent HNat.
 generalize dependent HNat0.
 generalize dependent HBool.
 generalize dependent HBool0.
 generalize dependent H.
 generalize dependent HArrow.
 rewrite  H3.
 intros; simpl in *.
 rewrite transp_id. 
 assert (H2:= rlift_transp_id).
 simpl in H2.
 rewrite H2.
 assert (H4 := H0 V t y).
 rewrite transp_id in H4.
 rewrite H2 in H4.
 simpl in *; auto.

  (* finally transitive *)

  unfold Transitive.
  intros a b c H H'.
  destruct H;
  destruct H'.
  assert (Ht : forall t, Sorts_map c t = Sorts_map a t).
    intro t. transitivity (Sorts_map a0 t); auto.
    
  apply (eq_rep (H:=Ht)).
  simpl; intros V t y.
  destruct a;
  destruct a0;
  destruct c.
  simpl in *.
  assert (H5 : Sorts_map0 = Sorts_map1) by
    (apply functional_extensionality; intro; auto).

  assert (H6 : Sorts_map1 = Sorts_map) by
    (apply functional_extensionality; intro; auto).
  
  generalize dependent H2. 
  generalize dependent H1. 
  generalize dependent rep_Hom_monad.
  generalize dependent rep_Hom_monad1.
  generalize dependent rep_Hom_monad0.
  generalize dependent HBool.
  generalize dependent HBool0.
  generalize dependent HBool1.
  generalize dependent HNat.
  generalize dependent HNat0.
  generalize dependent HNat1.
  
  generalize dependent H.
  generalize dependent Ht.
  generalize dependent HArrow.
  generalize dependent HArrow0.
  generalize dependent HArrow1.
  rewrite  H5.
  rewrite  H6.
  
  clear H6 H5.
  clear Sorts_map0.
  clear Sorts_map1.
  
  intros.
  assert (H7:=H0 V t y).
  assert (H9:=H2 V t y).
  rewrite transp_id in *.
  simpl in *.
  assert (H8 := rlift_transp_id).
  simpl in H8.
  rewrite H8 in *.
  transitivity (rep_Hom_monad0 V t y); 
  auto.
Qed.
  
Definition eq_Rep_oid (P R : PCFPO_rep) := Build_Setoid (eq_Rep_equiv P R).

