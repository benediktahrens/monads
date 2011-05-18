Require Export CatSem.CAT.cat_TYPE.
Require Export CatSem.CAT.monad_haskell.
Require Export CatSem.CAT.rmonad.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Automatic Introduction.
Unset Transparent Obligations.

Obligation Tactic := simpl; intros; 
   try unf_Proper; intros;
   repeat match goal with [H : option _ |- _ ] => destruct H end;
   auto.

Program Instance option_monad_s : 
  Monad_struct (C:=TYPE) (option) := {
  weta := @Some ;
  kleisli a b f := fun t => match t with
                   | Some y => f y
                   | None => None
                   end
}.

Definition option_monad := Build_Monad option_monad_s.

Definition option_default (V W : TYPE) (f : V ---> W) 
            (w: W): option V ---> W := fun v =>
  match v with
  | None => w
  | Some  v' => (f v')
  end.



