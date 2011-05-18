Require Export CatSem.CAT.monad_haskell.
Require Export CatSem.ULC.ULC_syntax.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Automatic Introduction.

Obligation Tactic := fin.

Program Instance ULCm : 
     Monad_struct (C:=TT) ULC := {
  weta := Var;
  kleisli := _subst
}.

Canonical Structure ULCM := Build_Monad ULCm.

Lemma rename_lift V (v : ULC V) W (f : V ---> W) : 
       v //- f = lift (M:=ULCM) f v.
Proof.
  unfold lift;
  fin.
Qed.

Lemma shift_shift V W (f : V ---> ULC W) (y : V*) :
        y >- f = _shift f y. 
Proof.
  intros V W f y.
  destruct y;
  simpl;
  auto.
Qed.