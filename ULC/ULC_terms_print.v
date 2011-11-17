Require Export CatSem.ULC.ULC_terms.

Eval compute in  ULC_theta.

Notation "a @ b" := (App a b) (at level 42, left associativity).
Notation "'1'" := (Var None) (at level 33).
Notation "'2'" := (Var (Some None)) (at level 24).
Notation "'3'" := (Var (Some (Some None))) (at level 23).
Notation "'4'" := (Var (Some (Some (Some None)))) (at level 22).
Eval compute in ULC_theta.
Eval compute in ULC_True.
Eval compute in ULC_False.
Eval compute in ULC_Nat 0.
Eval compute in ULC_Nat 2.
Eval compute in ULCsucc.
Eval compute in ULC_cond.
Eval compute in ULC_omega.
Eval compute in ULC_zero.
Eval compute in ULC_pred.
Eval compute in ULC_Y.