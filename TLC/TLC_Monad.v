Require Export CatSem.TLC.TLC_syntax.
Require Export CatSem.CAT.monad_haskell.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Obligation Tactic := fin.

Program Instance TLCm : 
     Monad_struct (C:=IT) TLC := {
  weta := var;
  kleisli := _subst
}.

Canonical Structure TLCM := Build_Monad TLCm.


(** some equalities : 
    - lift = rename
    - shift = _shift
*)

Lemma rename_lift V t (v : TLC V t) W (f : V ---> W) : 
       v //- f = lift (M:=TLCM) f _ v.
Proof.
  unfold lift;
  fin.
Qed.

Lemma shift_shift a V W (f : V ---> TLC W) t (y : opt a V t) :
        y >- f = shift f y. 
Proof.
  intros a V W f t y.
  destruct y;
  simpl;
  auto.
  unfold lift;
  fin.
Qed.

Hint Resolve shift_shift rename_lift : fin.
Hint Rewrite shift_shift rename_lift : fin.
