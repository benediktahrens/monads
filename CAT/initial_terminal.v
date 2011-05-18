Require Export CatSem.CAT.category.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Section Initial_Terminal.

Variable obC: Type.
Variable morC: obC -> obC -> Type.

Class Initial (C:Cat_struct morC) := {
     Init : obC;
     InitMor: forall a:obC, morC Init a;
     InitMorUnique: forall b (f:morC Init b), f == InitMor b
}.

Class Terminal (C:Cat_struct morC) := {
      Term: obC;
      TermMor: forall a: obC, morC a Term;
      TermMorUnique: forall b f, f == TermMor b
}.


End Initial_Terminal.

Implicit Arguments Init [obC morC C Initial].
Implicit Arguments Term [obC morC C Terminal].

(*Notation "'0'" := Init.
Notation "1" := Term.*)



(*
Definition initial (C : Cat) (O : C) :=
      forall a : C, sig (fun f:mor O a => forall g:mor O a, f == g).

(** witness extraction *)

Definition zerone (C:Category) (O:C): 
          initial O -> forall a, mor O a.
intros C O X a.
unfold initial in X.
destruct (X a) as [x p].
exact x.
Defined.



Definition terminal (C:Category) (l:C):=
     forall a : C, sig (fun f:mor a l => forall g:mor a l, f == g).

Definition termone (C:Category)(l:C):
            terminal l -> forall a, mor a l.
intros C l X a. 
destruct (X a) as [x p].
exact x.
Defined.
*)