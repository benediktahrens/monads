Require Export CatSem.CAT.functor.
Require Export CatSem.CAT.NT.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

(** definition of monad, haskell style  *)

Section monad_haskell_def.
Variable C : Cat.
(*
Variable obC : Type.
Variable morC : obC -> obC -> Type.
Variable C : Cat_struct morC.
*)
Section monad_haskell_class.

Variable F: C -> C.

(**  a monad over an object map consists of
	- return, here called weta (weak eta, since no NT a priori)
	- bind, here called kleisli (since we are point free)
	- some properties
*)

Class Monad_struct := {
  weta: forall c : C, c ---> F c;
  kleisli: forall a b : C, a ---> F b -> F a ---> F b;
  kleisli_oid:> forall a b, 
        Proper (equiv ==> equiv) (kleisli (a:=a) (b:=b));
  eta_kl : forall a b: C, forall f : a ---> F b, 
               weta a ;; kleisli f == f;
  kl_eta : forall a, kleisli (weta a) == id _;
  dist: forall a b c (f : a ---> F b) (g: b ---> F c),
           kleisli f ;; kleisli g == kleisli (f ;; kleisli g)
}.


End monad_haskell_class.

Record Monad := {
   F:> C -> C;
   monad_h_struct:> Monad_struct F 
}.
Existing Instance monad_h_struct.

Section trivial_lemmata.

Variable F : C -> C.
Variable FM : Monad_struct F.

Lemma kl_eq a b (f g : a ---> F b) : f == g -> kleisli f == kleisli g.
Proof.
  intros a b f g H;
  apply (kleisli_oid H).
Qed.

Lemma etakl a b (f : a ---> F b) : weta a ;; kleisli f == f.
Proof.
  intros;
  apply FM.
Qed.

Lemma kleta a : kleisli (weta a) == id _ .
Proof.
  intros;
  apply FM.
Qed.

Lemma kleta_id a f : f == weta a -> kleisli f == id _ .
Proof.
  intros.
  rewrite H.
  apply kleta.
Qed.

Lemma klkl a b c (f : a ---> F b) (g: b --->  F c) :
           kleisli f ;; kleisli g == kleisli (f ;; kleisli g).
Proof.
  intros;
  apply FM.
Qed.

End trivial_lemmata.

(** preparations for the fusion laws *)

Hint Rewrite eta_kl kl_eta dist: monad.

Hint Rewrite assoc idl idr : monad.

Hint Resolve idl idr hom_refl hom_sym : monad.

Ltac monad := intros; autorewrite with monad; auto with monad.

(** 
        - definition of join, lift
        - fusion laws
*)

Section Defs_and_Facts.

Variable M: Monad.

Definition lift : forall a b (f: a ---> b), M a ---> M b :=
       fun a b f => kleisli  (f ;; weta b).

Definition join (c:C): M (M c) ---> M c := kleisli (id (M c)).

Lemma lift_eq : forall a b (f g : a ---> b), 
       f == g -> lift f == lift g.
Proof.
  unfold lift;
  intros;
  match goal with [H : _ == _ |- _ ] => rewrite H end;
  cat.
Qed.

Instance lift_oid a b : Proper (equiv ==> equiv) (lift (a:=a) (b:=b)).
Proof.
  unfold lift,Proper;
  red; intros;
  apply lift_eq;
  auto.
Qed.

Lemma lift_id c :
  lift (id c) == id (M c).
Proof. 
  unfold lift; monad.  
Qed.

Lemma lift_eq_id a g : g == id a -> lift g == id (M a).
Proof.
  intros a g H.
  rewrite H.
  apply lift_id.
Qed.

Lemma lift_weta c d (f : c ---> d) : 
  weta _ ;; lift f == f ;; weta _ .
Proof. 
unfold lift; monad.
Qed.

Lemma lift_lift c d e (f : c ---> d) (g: d ---> e) :
  lift f ;; lift g == lift (f ;; g).
Proof.
unfold lift; monad.
Qed.

Lemma lift_kleisli c d e (f:c ---> d) (g: d ---> M e) :
  lift f ;; kleisli g == kleisli (f ;; g).
Proof.
unfold lift; monad.
Qed.

Lemma kleisli_lift c d e (f: c ---> M d) (g: d ---> e) :
  kleisli f ;; lift g == kleisli (f ;; lift g).
Proof.
unfold lift; monad.
Qed.

Hint Rewrite lift_id lift_weta lift_lift lift_kleisli kleisli_lift : monad.

Lemma join_join c: 
  join _ ;; join _ == lift (join _) ;; join c .
Proof.
unfold join; monad.
Qed.

Lemma join_weta c: 
  weta _ ;; join c == id _.
Proof.
unfold join; monad.
Qed.

Lemma join_lift c d (f:  c ---> M d) : 
  lift f ;; join _ == kleisli f.
Proof.
unfold join; monad.
Qed.

End Defs_and_Facts.

(*End monad_haskell_def.*)

Existing Instance monad_h_struct.

Hint Rewrite assoc idl idr eta_kl kl_eta dist 
             lift_id lift_weta lift_lift 
             lift_kleisli kleisli_lift 
             join_join join_weta join_lift: monad.

Hint Resolve idl idr hom_refl hom_sym : monad.



(** a haskell monad is a functor, in particular *)
Section monad_functor.

Section MFunc_def.

Variable M: Monad.

Existing Instance lift_oid.

Obligation Tactic := simpl; monad; unfold join; monad.

Program Instance MFunc_struct : Functor_struct (Fobj:= M) 
                   (@lift _  ).

Canonical Structure MFunc : Functor C C := Build_Functor MFunc_struct.

(*Canonical Structure MFunctor := Build_Functor MFunc.*)

Program Instance weta_NT_struct : NT_struct (F:=Id C) (G:=MFunc) (weta (Monad_struct:=M)).

Canonical Structure weta_NT := Build_NT weta_NT_struct.

Program Instance join_NT_struct : NT_struct (F:=MFunc O MFunc) (G:=MFunc) (join (M)).
Canonical Structure join_NT := Build_NT join_NT_struct.

End MFunc_def.


End monad_functor.
End monad_haskell_def.

Ltac monad := intros; autorewrite with monad; auto with monad.
Hint Rewrite assoc idl idr eta_kl kl_eta dist 
             lift_id lift_weta lift_lift 
             lift_kleisli kleisli_lift 
             join_join join_weta join_lift: monad.

Hint Resolve idl idr hom_refl hom_sym : monad.

Canonical Structure MFunc.
Existing Instance MFunc_struct.
Existing Instance lift_oid.
Existing Instance monad_h_struct.

Implicit Arguments join [C M].
Implicit Arguments lift [C M a b].

Coercion MFunc : Monad >-> Functor.







