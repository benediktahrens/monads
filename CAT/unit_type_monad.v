
Require Export CatSem.CAT.type_unit.
Require Export CatSem.CAT.monad_haskell.

Section bla.

Variable R : Monad TYPE. 

Definition unit_weta_car : 
 forall (c : ITYPE unit) (t : unit),
       (c) t -> (wunit (R (c tt))) t :=
fun (c : unit -> Type) (t : unit) (X : c t) =>
match t as u return (c u -> R (c tt)) with
| tt => fun X0 : c tt => (weta (Monad_struct:=R)(c tt)) X0
end X.




Definition unit_kleisli : 
forall a b : ITYPE unit,
   a ---> wunit (R (sunit b)) -> 
      wunit (R (sunit a)) ---> wunit (R (sunit b)) :=
    fun a b f =>
  fun t => kleisli (Monad_struct := R) (#sunit f).

Obligation Tactic := cat; try unf_Proper;
   unfold unit_weta_car, unit_kleisli;
   cat; repeat elim_unit;
   try apply (kl_eq R); try rew (etakl R);
   try rerew (kleta R); 
   repeat rew (klkl R);
   repeat apply (kl_eq R); cat;
   rew (kleta R); cat.

Program Instance unit_Monad_struct : 
    Monad_struct (C:=ITYPE unit) (fun V => wunit (R (sunit V))) := {
  weta := unit_weta_car ;
  kleisli := unit_kleisli
}.

Definition unit_Monad := Build_Monad unit_Monad_struct.

End bla.

