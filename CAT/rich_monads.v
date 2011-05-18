(*Require Coq.Program.*)

Require Export CatSem.CAT.monad_h_module.
Require Export CatSem.CAT.cat_INDEXED_TYPE.
Require Export CatSem.CAT.orders.
Require Export CatSem.CAT.ind_potype.

Generalizable All Variables.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Automatic Introduction.

Section defs.

Variable T : Type.

Notation "'IT'" := (ITYPE T).
Notation "'IP'" := (IPO T).

Section order_stuff.

Class Rel (X : Type) := rel : relation X.

Class ITrel (X : IT) := itrel :> forall t, Rel (X t).

Class ITpo (X : IT)(H:ITrel X) : Prop := 
  itpo :> forall t, PreOrder (@itrel _ _ t).

Variables A B : IT.
Variable f : A ---> B.

Class ITproper (Xa : ITrel A) (Xb : ITrel B) := 
   itproper :> forall t, Proper (itrel (t:=t) ==> @itrel _ _ t) (@f t).

End order_stuff.
(*
Section rich_monad.

Variable P : Monad IT.
Variable Ind_Rel : forall X : IP,  ITrel (P X).

Class Enriched_Monad := {
  ipo_preserve : forall X : IP, (ITpo (@Ind_Rel X));
  kl_preserve : forall (X Y : IP) (f : forall t, X t -> P Y t), 
          ITproper f (@IRel _ _ X)  (@Ind_Rel Y) -> 
          ITproper (kleisli f) (@Ind_Rel _)(@Ind_Rel _ );
  we_preserve : forall X : IP, 
          ITproper (weta (Monad_struct := P)X) (@IRel T _ X) (@Ind_Rel X )
}.


Variable H : Enriched_Monad.

Program Instance ind_ipo_struct (X : IPO T) : ipo_obj_struct (P X) := {
  IRel := @Ind_Rel X 
}.
Next Obligation.
Proof.
  apply ipo_preserve.
Qed.

Definition ind_ipo X := Build_ipo_obj (ind_ipo_struct X).

Program Instance we_ipo (X : IPO T) : 
       ipo_mor_struct (a:=X)(b:= ind_ipo (X))(T:=T) 
          (weta (Monad_struct := P) X).
Next Obligation.
Proof.
  apply we_preserve.
Qed.

Program Instance kl_ipo (X Y: IPO T) (f : X ---> ind_ipo Y) : 
           ipo_mor_struct (a:=ind_ipo X) (b:=ind_ipo Y) (T:=T)
           (kleisli (Monad_struct := P) f).
Next Obligation.
Proof.
  apply kl_preserve.
  unfold ITproper.
  apply f.
Qed.

Program Instance IPO_Monad : Monad_struct IP
    (fun X => Build_ipo_obj (ind_ipo X)) := {
  weta X := Build_ipo_mor (we_ipo X) ;
  kleisli X Y f := Build_ipo_mor (kl_ipo X Y f)  
}.
Next Obligation.
Proof.
  unfold Proper; red.
  simpl.
  intros.
  assert (H':=kleisli_oid (Monad_struct:=P)).
  unfold Proper in H';
  red in H'.
  apply H'.
  simpl.
  apply H0.
Qed.
Next Obligation.
Proof.
  assert (H':=eta_kl (Monad_struct:=P)).
  simpl in H'.
  apply H'.
Qed.
Next Obligation.
Proof.
assert (H':=kl_eta (Monad_struct:=P)).
  simpl in H'.
  apply H'.
Qed.
Next Obligation.
Proof.
  assert (H':=dist (Monad_struct:=P)).
  simpl in H'.
  apply H'.
Qed.

End rich_monad.
*)

End defs.