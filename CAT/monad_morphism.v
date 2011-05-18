Require Export CatSem.CAT.monad_def.
Require Export CatSem.CAT.prods.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

(** a morphism of monads is
 	- a morphism of functors, i.e. a NT
	- compat with eta + mu *)

Section monad_morphism_def.

Variables obC: Type.
Variable morC : obC -> obC -> Type.
Variable C: Cat_struct morC.

Variables F G: MonaD C.

Definition eta_tau_def (tau: NT F G) := forall c: obC,
              Eta c ;; tau c == Eta c.

Definition tau_tau_def (tau: NT F G):Prop := forall c:obC,
          tau (F c) ;; #G (tau c) == #F (tau c) ;; tau (G c).

Definition mu_tau_def (tau: NT F G):Prop := forall c: obC, 
         Mu c ;; tau c == tau (F c) ;; #G (tau c) ;; Mu c.

Class MonaD_Hom_struct (tau:NT F G) := {
(*    tau: NT F G;*)
    Eta_Tau: eta_tau_def tau;
    Tau_Tau: tau_tau_def tau;
    Mu_Tau: mu_tau_def tau
}.

Record MonaD_Hom := {
  Monad_NT:> NT F G;
  monad_hom_struct :> MonaD_Hom_struct Monad_NT
}.

Section Monad_Morphism_lemmata.


Variable Tau: MonaD_Hom.


Lemma eta_tau: forall c:obC,
         Eta c ;; Tau c == Eta c.
Proof. 
  apply Tau. Qed.

Lemma tau_tau: forall c:obC,
          Tau (F c) ;; #G (Tau c) == #F (Tau c) ;; Tau (G c).
Proof. apply Tau. Qed.

Lemma mu_tau: forall c: obC, 
         Mu c ;; Tau c == Tau (F c) ;; #G (Tau c) ;; Mu c.
Proof. apply Tau. Qed.

Lemma mu_tau2: forall c: obC,
         Mu c ;; Tau c == #F (Tau c) ;; Tau (G c) ;; Mu c.
Proof. intro c. rewrite <- tau_tau. apply mu_tau. Qed.

End Monad_Morphism_lemmata.


End monad_morphism_def.

Section MONAD.

Variables obC: Type.
Variable morC : obC -> obC -> Type.
Variable C: Cat_struct morC.

Definition MONAD_obj := MonaD C.


Definition MONAD_mor (a b: MonaD C) := 
      MonaD_Hom a b.
(*
Definition eq_MONAD_mor1 (a b: MONAD_obj) : relation (MONAD_mor a b) :=
         fun f g =>  Monad_NT f == Monad_NT g. 
*)
Lemma MONAD_mor_setoid (a b: MonaD C) : 
       @Equivalence (MonaD_Hom a b) 
              (fun f g =>  Monad_NT f == Monad_NT g).
Proof. 
  intros a b. 
  split. 
  unfold Reflexive. 
  cat. 
  unfold Symmetric.
  intros x y.
  apply hom_sym.
  unfold Transitive; 
  intros x y z;
  apply hom_trans.
Qed.

Definition MONAD_mor_oid (a b: MonaD C) := 
          Build_Setoid (MONAD_mor_setoid a b).

Program Definition MONAD_comp (F G H: MonaD C) 
        (alpha: MonaD_Hom F G) (beta: MonaD_Hom G H) : MonaD_Hom F H :=
    Build_MonaD_Hom (Monad_NT := beta # alpha) _  .
Next Obligation.
Proof. 
  constructor.
  unfold MONAD_mor in *|-*.
  destruct alpha as [alpha [a1 a2 a3]]; 
  destruct beta as [beta [b1 b2 b3]];
  (*destruct Fax as [F1 F2 F3];
  destruct Gax as [G1 G2 G3];*)
  unfold eta_tau_def, tau_tau_def, mu_tau_def in *|-*;
  simpl in *|-*.
  (*constructor. *)
  (*          unfold eta_tau_def in *|-*; simpl in *|-*.*)
  unfold vcompNT1; simpl. intro x.
  rewrite <- assoc.
  rewrite (a1 x).
  auto.
  
  unfold tau_tau_def in *|-*; simpl in *|-*.
  unfold vcompNT1; simpl; intro x.
  rewrite assoc.
  rewrite (NTcomm beta). 
  repeat rewrite FComp.
  repeat rewrite <- assoc.
  destruct alpha as [alpha [a1 a2 a3]]; 
  destruct beta as [beta [b1 b2 b3]];
  (*destruct Fax as [F1 F2 F3];
  destruct Gax as [G1 G2 G3];*)
  unfold eta_tau_def, tau_tau_def, mu_tau_def in *|-*;
  simpl in *|-*.
  rewrite a2.
  apply postcomp.
  repeat rewrite  assoc.
  apply praecomp.
  rewrite <- (NTcomm alpha).
  apply hom_refl.
  
  unfold mu_tau_def; simpl; intro x.
  unfold vcompNT1; simpl.
  repeat rewrite <- assoc.
  destruct alpha as [alpha [a1 a2 a3]]; 
  destruct beta as [beta [b1 b2 b3]];
  (*destruct Fax as [F1 F2 F3];
  destruct Gax as [G1 G2 G3];*)
  unfold eta_tau_def, tau_tau_def, mu_tau_def in *|-*;
  simpl in *|-*.
  rewrite a3.
  repeat rewrite assoc.
  apply praecomp.
  rewrite (b3 x).
  repeat rewrite <- assoc.
  apply postcomp.
  rewrite FComp.
  repeat rewrite <- assoc.
  apply postcomp.
  rewrite (NTcomm beta).
  apply hom_refl.
Qed.
  
Program Definition MONAD_id (F: MonaD C): MonaD_Hom F F :=
        Build_MonaD_Hom (Monad_NT := vidNT F) _ .
Next Obligation.
Proof. 
  constructor.
  unfold eta_tau_def. 
  cat. 
  unfold tau_tau_def; 
  cat. 
  unfold mu_tau_def; 
  cat. 
Qed.
   

Program Instance MONAD_struct: Cat_struct MONAD_mor := {
  mor_oid := MONAD_mor_oid;
  comp := MONAD_comp;
  id := MONAD_id
}.
Next Obligation.
Proof. 
  unfold Proper.
  red. red.
  intros a b c x y H x0 y0 H0 r.
  unfold MONAD_comp. 
  simpl in *.
  unfold vcompNT1.
  rewrite H0.
  rewrite H. 
  apply hom_refl. 
Qed.
Next Obligation.
Proof.
  simpl.
  unfold vcompNT1, 
        MONAD_comp, 
        MONAD_id; 
  simpl.
  cat.
Qed.
Next Obligation.
Proof.
  simpl;
  unfold vcompNT1; simpl.
  cat.
Qed.
Next Obligation.
Proof.
  simpl;
  unfold vcompNT1; simpl.
  unfold vcompNT1.
  intros.
  apply assoc.
Qed.

Definition MONAD := Build_Cat MONAD_struct.

End MONAD.







(** about Modules over Monads *)

(** definition of left modules, which should be called 
    after-modules or something 
    i gonna write'em on the right side... *)

Section LModule_def.

Variables obC: Type.
Variable morC : obC -> obC -> Type.
Variable C: Cat_struct morC.
Variable R: MonaD C.

Variable obD: Type.
Variable morD: obD -> obD -> Type.
Variable D: Cat_struct morD.

Class LModule_struct (M: Functor C D) := {
  sigma: NT (CompF R M) M;
  module_diag : forall c, sigma (R c) ;; sigma c == #M (Mu c) ;; sigma c
}.


Record LModule := {
  LmoduleF :>  Functor C D;
  (*sigma :> NT (CompF R LmoduleF) LmoduleF;*)
  Lmodule_struct :> LModule_struct LmoduleF
}.

(*Definition LModule_functor (M:LModule) := @LmoduleF M.
Coercion LModule_functor: LModule >-> Functor.
*)

Existing Instance Lmodule_struct.

Section LModule_lemmata.

(*Variable M: Functor C D.*)
(*Variable sigma: NT (CompF R M) M.*)
Variable M: LModule.

Lemma mod_subst (c: obC): sigma (R c) ;; sigma c == #M (Mu c) ;; sigma c.
Proof. destruct M as [F [S Dia]]; apply Dia. Qed.

End LModule_lemmata.

(*
Program Instance Tautological_Module : LModule := {
   LmoduleF := R;
   Lmodule_subst := mu
}.

  Next Obligation.
    Proof. apply Build_Module_struct. apply MonadF. Qed.
*)
End LModule_def.

Existing Instance Lmodule_struct.

(*  TODO: have another definition of product functor 
    for two parallel functors
*)    


Section Product_LModule.

Variables obC: Type.
Variable morC : obC -> obC -> Type.
Variable C: Cat_struct morC.
Variable R: MonaD C.

Variable M: LModule R C.
Variable N: LModule R C.

Program Definition Prod_NT:NT (CompF R (par_prodF M N)) (par_prodF M N) := 
     Build_NT (trafo := fun c => (sigma (LModule_struct:= M) c, 
                                  sigma (LModule_struct:= N) c)) _ .
Next Obligation.
Proof. 
  apply Build_NT_struct.
    unfold trafo_comm. 
    intros c d f. simpl.
    split. 
    rewrite (NTcomm (sigma (LModule_struct:= M)) f).
    cat.
    rewrite (NTcomm (sigma (LModule_struct:= N)) f).
    cat.
Qed.

Obligation Tactic := simpl; intros.

Program Instance PROD_MODULE: LModule_struct R (par_prodF M N) := {
      sigma := Prod_NT
}.
Next Obligation.
Proof. 
  destruct M as [MM [m1 m2]]; 
  destruct N as [NN [n1 n2]]; 
  simpl in *.
  split; try apply (m2 c); 
         try apply (n2 c).
Qed.

End Product_LModule.


Section Pull_back_Module.

Variable obC: Type.
Variable morC : obC -> obC -> Type.
Variable C: Cat_struct morC.

Variables A B: MonaD C.

Variable f: MonaD_Hom A B.

(*Variable f: NT A B.
Hypothesis monad_mor: Monad_Morphism_struct f.*)

Variable obD: Type.
Variable morD: obD -> obD -> Type.
Variable D: Cat_struct morD.

Variable M: LModule B D.

Definition cccomp:= fun c:obC => #M (f c) ;; sigma c.

Program Definition cccomp_trans: NT (CompF A M) M := 
       Build_NT (trafo := cccomp) _ .
Next Obligation.
Proof. 
  constructor.
  unfold trafo_comm, cccomp. intros c d a.
  simpl in *.
  repeat rewrite <- (assoc).
  rewrite <- (FComp M (#A a) (f d)).
  apply hom_trans with 
  (#M (f c) ;; (#M (#B a)) ;; sigma d).
  repeat rewrite assoc.
  simpl.
  apply praecomp.
  apply (NTcomm (sigma (LModule_struct := M)) a).
  
  apply postcomp.
  
  repeat rewrite <- FComp.
  assert (H': f c ;; #B a == #A a ;; f d).
  apply (NTcomm f). 
  rewrite H'. apply hom_refl.
Qed.

Obligation Tactic := simpl; intros.
           
Program Instance Pullback_Module_struct: LModule_struct A M := {
      sigma := cccomp_trans
}.
Next Obligation.
Proof. 
  unfold cccomp.
  apply hom_trans with 
  (#M (f (A c)) ;; (#M (#B (f c))) ;; sigma (B c) ;; sigma c).
  
  repeat rewrite assoc.
  apply praecomp.
  repeat rewrite <- assoc.
  apply postcomp.
  apply (NTcomm (sigma (LModule_struct := M)) (f c)).
  
  apply hom_trans with
  (#M (f (A c)) ;; #M (#B (f c)) ;; #M (Mu c) ;; sigma c).
  repeat rewrite assoc.
  repeat apply praecomp.
  destruct M as [MM [sigmaMM Max]]. simpl.
  (*destruct Max as [Max].*)
  apply (Max c).
  
  repeat rewrite <- assoc.
  apply postcomp.
  
  destruct f as [m1 [m2 m3 m4]].
  unfold mu_tau_def in m4.
  
  repeat rewrite <- FComp.
  rewrite (m4 c).
  apply hom_refl.
Qed.
  
Definition Pullback_Module : LModule A D:= 
         Build_LModule  Pullback_Module_struct.


End Pull_back_Module.

(** Morphisms of Modules *)

Section LModule_Morphism.

Variable obC: Type.
Variable morC : obC -> obC -> Type.
Variable C: Cat_struct morC.

Variable R: MonaD C.

Variable obD: Type.
Variable morD: obD -> obD -> Type.
Variable D: Cat_struct morD.

Variables M N: LModule R D.

Section LModule_Morphism_struct.

Variable F: NT M N.

Class Module_Morphism_struct := {
  Module_Mor: forall x, sigma x ;; F x == F (R x) ;; sigma x
}.

End LModule_Morphism_struct.

Record Module_Morphism := {
    lmoduleNT:> NT M N;
    lmodule_morphism_struct :> Module_Morphism_struct lmoduleNT
}.


End LModule_Morphism.


(** category of R-LModules *)
Section cat_of_R_LModules_over_D.

Variable obC: Type.
Variable morC : obC -> obC -> Type.
Variable C: Cat_struct morC.

Variables R: MonaD C.

Variable obD: Type.
Variable morD: obD -> obD -> Type.
Variable D: Cat_struct morD.


Definition LMOD_R_ob := LModule R D.


Definition MOD_R_mor (M N: LModule R D) :=
                Module_Morphism M N.

Program Definition MOD_R_id (M: LModule R D) : MOD_R_mor M M :=
           Build_Module_Morphism (lmoduleNT:= (vidNT M)) _.
Next Obligation.
Proof. 
  intros;
  apply Build_Module_Morphism_struct.
  cat.
Qed.

Program Definition MOD_R_comp (M N P: LModule R D)
          (alpha: MOD_R_mor M N)(beta: MOD_R_mor N P) : MOD_R_mor M P :=
     Build_Module_Morphism (lmoduleNT:= (vcompNT alpha beta)) _.
Next Obligation.
Proof. 
  intros;
  apply Build_Module_Morphism_struct. 
  simpl.
  intro x; unfold vcompNT1; simpl.
  destruct alpha as [alpha Pa].
  destruct Pa as [Pa].
  destruct beta as [beta Pb].
  destruct Pb as [Pb]. simpl in *|-*.
  repeat rewrite <- assoc.
  rewrite Pa.
  repeat rewrite assoc.
  apply praecomp.
  apply Pb.
Qed.

Lemma eq_MOD_R_setoid (M N: LModule R D): 
        @Equivalence (Module_Morphism M N) 
     (fun alpha beta => lmoduleNT alpha == lmoduleNT beta).
Proof. 
  intros M N. 
  split. 
  unfold Reflexive.
  cat. 
  unfold Symmetric; 
  intros r s; 
  apply hom_sym.
  unfold Transitive; 
  intros r s t;
  apply hom_trans.       
Qed.

Definition eq_MOD_R (M N: LModule R D) := 
         Build_Setoid (eq_MOD_R_setoid M N). 

Program Instance MOD_R: Cat_struct MOD_R_mor := {
  mor_oid := eq_MOD_R;
  id := MOD_R_id;
  comp := MOD_R_comp
}.
Next Obligation.
Proof. 
  unfold Proper. 
  red. red.
  unfold MOD_R_comp. 
  simpl.
  unfold vcompNT1; 
  simpl.
  intros a b c x y H x0 y0 H0 c0.
  rewrite H.
  rewrite H0. 
  apply hom_refl.
Qed.
Next Obligation.
Proof.
  simpl;
  unfold vcompNT1. 
  simpl. 
  cat.
Qed.
Next Obligation.
Proof.  
  simpl;
  unfold vcompNT1. 
  simpl.
  cat. 
Qed.
Next Obligation.
Proof. 
  simpl;
  unfold vcompNT1. 
  simpl.
  unfold vcompNT1. 
  intros;
  apply assoc.
Qed.


End cat_of_R_LModules_over_D.

Existing Instance MONAD_struct.






