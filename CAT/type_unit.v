Require Export CatSem.CAT.cat_INDEXED_TYPE.
Require Export CatSem.CAT.ind_potype.
Require Export CatSem.CAT.cat_TYPE_option.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.



Definition unit_passing (c : unit -> Type) t u
(y : (opt t c u)):
(option (c tt)).
intros.
destruct y.
destruct t0.
apply (Some c0).
apply (None).
Defined.


Definition unit_passing2 c t u (y : opt t c u) :
       (option (c tt)).
intros.
destruct u.
destruct y.
apply (Some c0).
apply None.
Defined.


Section bla.

Notation "'TT'":= (ITYPE unit).

Obligation Tactic := mauto.

(** a functor (unit -> Type) -> Type *)

Program Instance sunit_s : Functor_struct (C:=TT) (D:=TYPE)
    (Fobj:= fun V => V tt) (fun a b f => f tt).

Definition sunit : Functor TT TYPE := IT_proj tt.

(** a functor Type -> (unit -> Type) *)

Program Instance wunit_s : Functor_struct (C:=TYPE) (D:=TT)
     (Fobj := fun V => fun _ => V)(fun a b f => fun _ => f).

Definition wunit := Build_Functor wunit_s.

(** a functor (unit -> PO) -> PO  = (IPO unit) -> PO*)

Definition sunit_po : Functor (IPO unit) Ord := IP_proj tt.

(** a functor PO -> (IPO unit) *)

Program Instance wunit_ob_s (V : Ord): 
    ipo_obj_struct (T:=unit)(fun _ => V) := {
  IRel t := Rel ;
  IPOprf t := POprf
}.

Definition wunit_ob V := Build_ipo_obj (wunit_ob_s V).

Obligation Tactic := cat; try unf_Proper; cat;
  repeat apply PO_mor_monotone; cat.

Program Instance wunit_mor_s (V W : Ord)(f : V ---> W) : 
  ipo_mor_struct (a:=wunit_ob V) (b:=wunit_ob W)
  (fun t => f).

Definition wunit_mor V W (f:V--->W) := 
   Build_ipo_mor (wunit_mor_s _ _ f).

Obligation Tactic := mauto.

Program Instance wunit_po_s : Functor_struct (C:=Ord)(D:=IPO unit)
    (Fobj:=wunit_ob)
    (fun a b f => wunit_mor f).

Definition wunit_po : Functor Ord (IPO unit) := Build_Functor wunit_po_s.

End bla.







