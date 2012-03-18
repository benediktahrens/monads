Require Export CatSem.CAT.horcomp.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Automatic Introduction.

(** Definition of a monad, with MU and ETA *)

Section monad_def.

Variables obC obD: Type.
Variable morC : obC -> obC -> Type.
Variable C: Cat_struct morC.


(*Variable C : Cat.*)

Definition subst_ax (F:Functor C C)(mu: NT (CompF F F) F) :=
           forall c, mu (F c) ;; mu c ==
                         #F (mu c) ;; mu c.

Definition eta_mu_ax1 (F:Functor C C)(eta:NT (Id C) F)
                      (mu: NT (CompF F F) F) :=
           forall c, #F (eta c) ;; mu c == id (F c).

Definition eta_mu_ax2 (F:Functor C C)(eta:NT (Id C) F)
                      (mu: NT (CompF F F) F) :=
           forall c, eta (F c) ;; mu c == id (F c).



Class MonaD_struct (F: Functor C C) := {
    Eta: NT (Id C) F;
    Mu: NT (CompF F F) F;
    Subst_ax: subst_ax Mu;
    Eta1_ax: eta_mu_ax1 Eta Mu;
    Eta2_ax: eta_mu_ax2 Eta Mu
}.


Record MonaD := {
   T:> Functor C C;
   monaD_struct:> MonaD_struct T
}.


Existing Instance monaD_struct.

 (*
Definition Eq_Monad1: relation MonaD :=
    fun M M':MonaD => (EXT_Functor  (@T M) (@T M') /\ 
                       EXT_NT_HET (@Eta M _) (@Eta _ M') /\ 
                       EXT_NT_HET (@Mu M _ ) (@Mu M' _)).

Lemma Eq_Monad_oid: Equivalence Eq_Monad1.
Proof. 
  unfold Eq_Monad1. 
  split.
   unfold Reflexive. 
   intro x; split.
     unfold EXT_Functor.
     apply eq_Functor_equiv.
     
     split;
        apply eq_NTh_refl.

   unfold Symmetric. 
   intros x y H;
   repeat split.
     unfold EXT_Functor.
     apply eq_Functor_equiv. 
     apply H.
       apply eq_NTh_sym. apply H.
       apply eq_NTh_sym. apply H.

   unfold Transitive. 
   intros x y z H H'.
     repeat split. 
     unfold EXT_Functor.
     apply eq_Functor_equiv with (@T y).
      apply H. apply H'.
     apply (eq_NTh_trans (proj1 (proj2 H)) 
                         (proj1 (proj2 H'))).
     apply (eq_NTh_trans (proj2 (proj2 H)) 
                         (proj2 (proj2 H'))).
Qed.   

Definition Eq_Monad := Build_Setoid Eq_Monad_oid.
*)
End monad_def.

Existing Instance monaD_struct.


Section fff.

Variable C : Cat.

Section defs_and_facts.

Variable M : MonaD C.

Existing Instance cat_struct.

Definition bind a b (f : a ---> M b) : M a ---> M b := # M f ;; Mu (MonaD_struct:=M) _ .

Unset Printing Implicit Defensive.


Lemma bind_bind a b c (f : a ---> M b) (g : b ---> M c) :
      bind f ;; bind g == bind (f ;; bind g).
Proof.
  unfold bind;
  simpl; intros.
  assert (H:=(NTcomm (Mu (MonaD_struct:=M)))).
  simpl in H.
  rewrite <- assoc.
  rewrite <- assoc.
  transitivity 
    (#M f ;; (Mu (MonaD_struct:=M) b ;; # M g) ;; Mu (MonaD_struct:=M) c).
    apply postcomp.
    repeat rewrite assoc.
    apply praecomp.
    reflexivity.
(*    apply postcomp.*)
  repeat rewrite FComp.
  repeat rewrite assoc.
  apply praecomp.
  rewrite <- assoc.
  rew (H b _ g).
  (*rewrite <- FComp.*)
  assert (H':= Subst_ax (MonaD_struct := M)).
  unfold subst_ax in H'; simpl in H'.
  repeat rewrite assoc.
  apply praecomp.
  auto.
Qed.

Lemma bind_eta a : bind (Eta (MonaD_struct:=M) a) == id _ .
Proof.
  unfold bind.
  intros; simpl.
  assert (H':= Eta1_ax (MonaD_struct := M)).
  unfold eta_mu_ax1 in H'.
  simpl in *.
  apply H'.
Qed.

Lemma eta_bind a b (f : a ---> M b) : Eta (MonaD_struct:=M) _ ;; bind f == f.
Proof.
  unfold bind; simpl; intros.
  assert (H:= NTcomm (Mu (MonaD_struct := M))).
  simpl in H.
  assert (H':= Subst_ax (MonaD_struct := M)).
  unfold subst_ax in H'; simpl in H'.
  assert (H'':= NTcomm (Eta (MonaD_struct := M))).
  simpl in H''.
  rewrite <- assoc.
  rewrite H''.
  rewrite assoc.
  assert (H4:= Eta2_ax (MonaD_struct := M)).
  unfold eta_mu_ax2 in H4; simpl in H4.
  rewrite H4.
  cat.
Qed.
  
End defs_and_facts.
End fff.


(*
Section monad_comp.

Variables ob: Type.
Variable mor : ob -> ob -> Type.
Variable C: Cat_struct mor.
Variables F G: Functor C C.
Variable etaF: Id C ---> F.
Variable etaG: Id C ---> G.
Variable muF: (CompF F F) ---> F.
Variable muG: (CompF G G) ---> G.

Hypothesis MonadF: MonaD_struct F.
Hypothesis MonadG: MonaD_struct G.

Lemma eta_no_choice (c:ob) :
       etaG c ;; #G (etaF c) == etaF c ;; etaG (F c).
Proof. 
  intro c. 
  rewrite (trafo_ax (alpha := etaG)). 
  cat.
Qed.

End monad_comp.
*)






















