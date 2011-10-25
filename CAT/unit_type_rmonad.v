Require Export CatSem.CAT.ind_potype.
Require Export CatSem.CAT.orders_bis.
Require Export CatSem.CAT.type_unit.
Require Export CatSem.CAT.rmonad.

Section bla.

(** starting from a rmonad Set -> PO,
   we define a rmonad (unit -> Set) -> (unit -> PO)
*)

Variable R : RMonad (SM_po).

Definition unit_rweta_car : 
 forall (c : ITYPE unit) (t : unit),
       (sm_ipo (T:=unit) c) t -> (wunit_ob (R (c tt))) t :=
fun (c : unit -> Type) (t : unit) (X : c t) =>
match t as u return (c u -> R (c tt)) with
| tt => fun X0 : c tt => (rweta (RMonad_struct:=R)(c tt)) X0
end X.

Obligation Tactic := cat; unf_Proper; cat;
  repeat match goal with [H:smallest_irel _ _ |- _ ] => destruct H end;
  reflexivity.

Program Instance unit_rweta_po c:
ipo_mor_struct 
 (a:=sm_ipo (T:=unit) c) (b:=wunit_ob (R (c tt)))
 (unit_rweta_car c).

Definition unit_rweta c:
(IDelta unit) c ---> wunit_po (R (sunit c)) :=
  Build_ipo_mor (unit_rweta_po c).

Obligation Tactic := cat; try unf_Proper; cat; 
     repeat apply PO_mor_monotone; cat.

Program Instance unit_rkleisli_po :
forall (a b : unit -> Type)
(f:ipo_mor (sm_ipo (T:=unit) a) (wunit_ob (R (b tt)))),
ipo_mor_struct (a:=wunit_ob (R (a tt))) (b:=wunit_ob (R (b tt)))
  (fun t => rkleisli (RMonad_struct := R) (Sm_ind (#sunit f))).

Definition unit_rkleisli :
forall (a b : ITYPE unit)
(f : (IDelta unit) a ---> wunit_po (R (sunit b))),
wunit_po (R (sunit a)) ---> wunit_po (R (sunit b)) :=
  fun a b f => Build_ipo_mor (unit_rkleisli_po a b f).

Obligation Tactic := cat; try unf_Proper;
   unfold unit_rweta_car;
   cat; repeat elim_unit;
   try apply (rkl_eq R); try rew (retakl R);
   try rerew (rkleta R); 
   repeat rew (rklkl R);
   repeat apply (rkl_eq R); cat;
   rew (rkleta R); cat.

Program Instance unit_RMonad_struct : 
    RMonad_struct (IDelta unit) (fun V => wunit_po (R (sunit V))) := {
 rweta  := unit_rweta ;
 rkleisli := unit_rkleisli
}.

Definition unit_RMonad := Build_RMonad unit_RMonad_struct.

End bla.

