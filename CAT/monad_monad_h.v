Require Export CatSem.CAT.monad_def.
Require Export CatSem.CAT.monad_haskell.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Section MonaD_gives_Monad.

Variable C: Cat.

Variable M: MonaD C.

Definition Monad_h_F: C -> C := fun x => M x.

Definition Monad_h_eta: forall c:C, c ---> Monad_h_F c :=
                  fun c => Eta c.

Definition Monad_h_kl: forall a b:C, 
       a ---> (Monad_h_F b) ->  (Monad_h_F a) ---> (Monad_h_F b) :=
                   fun a b f => #M f ;; Mu b.

Program Instance Monad_h_from_Monad_struct : 
           Monad_struct  Monad_h_F := {
  weta := Monad_h_eta;
  kleisli := Monad_h_kl
}.
Next Obligation.
Proof.
  intros a b.
  unfold Proper. 
  red. 
  unfold Monad_h_F, Monad_h_kl.
  intros x y H. 
  rewrite H.
  apply hom_refl.
Qed.
Next Obligation.
Proof.
  intros a b f.
  unfold Monad_h_eta, Monad_h_kl.
  set (Struct := @monaD_struct _ _ _ M).
  destruct Struct as [eta mu Subst Eta1 Eta2].
  (*           set (Subst := @subst _ _ _  _ _ _ Struct).
  set (Eta1 := @eta1 _ _ _ _ _ _ Struct).
  set (Eta2 := @eta2 _ _ _ _ _ _ Struct). *)
  unfold subst_ax in Subst.
  unfold eta_mu_ax1 in Eta1.
  unfold eta_mu_ax2 in Eta2.
  (*           unfold Functor_Fobj in *|-*.*)
  simpl in *|-*.
  rewrite <- assoc.
  destruct eta as [eta [etax]].
  (*set (Etax := @trafo_ax _ _ _ _ _ _ _ _ (@ETA _ _ _  M)).*)
  unfold trafo_comm in etax. simpl in etax.
  rewrite etax.
  rewrite assoc.
  unfold Monad_h_F.
  rewrite Eta2.
  apply idr.
Qed.
Next Obligation.
Proof.
  intro a.
  unfold Monad_h_kl, Monad_h_eta, Monad_h_F.
  destruct M as [MM [eta mu Subst Eta1 Eta2]].
  simpl in *|-*.
  (*           set (Struct := @monad_struct _ _ _ M).           
  set (Eta1 := @eta1 _ _ _ _ _ _ Struct).*)
  unfold eta_mu_ax1 in Eta1.
  apply (Eta1 a).
Qed.
Next Obligation.
Proof.
  intros a b c f g .
  (*set (Struct := @monad_struct _ _ _ M).
  set (Subst := @subst _ _ _ _ _ _ Struct).
  set (Mux := @trafo_ax _ _ _ _ _ _ _ _ (@MU _ _ _  M)).*)
  unfold Monad_h_kl.
  (*destruct M as [MM [Eta Mu Subst Eta1 Eta2]].*)
  (*           set (MM := T M).*)
  set (Struct := monaD_struct M).
  destruct Struct as [Eta Mu Subst Eta1 Eta2].
  unfold subst_ax in Subst.
  destruct Mu as [Mu [Mux]].
  unfold trafo_comm in Mux. simpl in Mux.

  unfold Monad_h_kl, Monad_h_eta, Monad_h_F in *|-*.
  simpl in *|-*.
  repeat rewrite FComp.
  repeat rewrite assoc.
  rewrite <- (Subst c).
  apply hom_trans with 
  (#M f ;; (Mu b ;; #M g ;; Mu c)).
  repeat rewrite assoc. apply hom_refl.
  apply praecomp.
  rewrite (Mux). 
  repeat rewrite assoc; apply hom_refl.
Qed.
         

End MonaD_gives_Monad.

(** and from a haskell style monad we can define a "traditional" monad *)

Section Monad_h_gives_Monad.

Variable C: Cat.

Variable M: Monad C.
(*
Definition Mmor : forall a b (f: morC a b), morC (M a) (M b) :=
       fun a b f => kleisli  (f ;; weta b).
*)

(*
Program Definition MFunc : Functor C C := Build_Functor
  (Fobj := fun a => M a) (Fmor := Mmor) _ .

  (*Next Obligation.
    Proof. apply Build_Func.
           
           unfold Proper. red.
           unfold Mmor.
           intros a b x y H. 
           rewrite H. apply hom_refl.
           
           unfold Mmor. intro a; rewrite idl.
           apply kl_eta.
           
           unfold Mmor. intros a b c f g;
           rewrite dist.
           repeat rewrite assoc.
           rewrite eta_kl.
           apply hom_refl.
    Qed.
           *)
*)
Definition MMu: forall a, (M (M a)) ---> (M a) :=
           fun a => kleisli (id (M a)).

Program Definition MMutrafo : 
  NT (CompF (MFunc M) (MFunc M)) (MFunc M):= Build_NT
     (trafo := MMu) _ .
Next Obligation.
Proof. 
  apply Build_NT_struct.
  set (S:= @monad_h_struct  C M).
  unfold trafo_comm, MMu. simpl.
  intros.
  unfold lift.
  rewrite dist.
  rewrite dist.
  rewrite idl.
  rewrite assoc.
  rewrite eta_kl.
  cat.
Qed.

Definition MEta : forall a, a ---> (M a) := fun a => weta a.

Program Definition MEtatrafo : NT (Id C) (MFunc M) := Build_NT
       (trafo := fun a : C => MEta a) _ .

Next Obligation.
Proof. 
  constructor.
  unfold trafo_comm. 
  intros c d f.
  simpl. 
  unfold MEta, lift.
  monad.
Qed.
 
Program Instance Monad_from_Monad_h_struct : 
            MonaD_struct (MFunc M) := {
  Eta := MEtatrafo;
  Mu := MMutrafo
}.

Next Obligation. 
Proof. 
  unfold subst_ax, MMutrafo. 
  simpl.
  unfold MMu,lift. 
  intro c.
  monad.
Qed.
Next Obligation.
Proof. 
  unfold eta_mu_ax1, 
    MEtatrafo, MMutrafo.
    simpl. 
    unfold lift,MEta,MMu; simpl.
    monad.
Qed.
Next Obligation.
Proof. 
  unfold eta_mu_ax2, MEtatrafo, MMutrafo.
  simpl. 
  unfold MMu, MEta. 
  monad.
Qed.

End Monad_h_gives_Monad.

