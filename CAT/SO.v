Require Export CatSem.CAT.cat_TYPE. 
Require Export CatSem.CAT.orders.
Require Export CatSem.CAT.subcategories.
Require Export CatSem.CAT.product.
Require Export CatSem.CAT.initial_terminal.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Automatic Introduction.

(** a category of preorders and maps (not necessarily monotone) 
    between them 
*)

Obligation Tactic := cat; unfold Proper; do 2 red; cat; 
       repeat rew_all; cat.

Program Instance wPO_struct : Cat_struct (fun a b : PO_obj => a -> b) := {
   mor_oid a b := TYPE_hom_oid a b;
   id a := fun x: a => x;
   comp a b c := fun (f:a -> b) (g:b -> c) => fun x => g (f x)
}.

Definition wOrd := Build_Cat wPO_struct.

Class Monotone (a b : wOrd) (f : a ---> b) := 
  monotone : Proper (Rel ==> Rel) f.

Obligation Tactic := mauto ; unfold Monotone; cat;
                 unfold Proper, respectful in *; mauto.
(*
Obligation Tactic := idtac.
*)
Program Instance wPO_monotone_SubCat : SubCat_compat wOrd
      (fun x => True) (fun a b f => Monotone f).

Definition wPO_monotone := SubCat wPO_monotone_SubCat.

Program Instance wPO_prod : Cat_Prod wOrd := {
  product a b := PO_product a b;
  prl a b := fst;
  prr a b := snd;
  prod_mor a b c f g := fun z => (f z, g z)
}.

Program Instance wPO_Terminal : Terminal wOrd := {
  Term := PO_TERM;
  TermMor a := fun x => tt
}.

Obligation Tactic := simpl; intros;
  repeat match goal with [H:TEMPTY |- _ ] => elim H end;
      cat.

Program Instance TYPE_init : Initial wOrd := {
  Init := PO_INIT 
}.






