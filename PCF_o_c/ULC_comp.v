Require Export CatSem.PCF_o_c.RPCF_INIT.
Require Export CatSem.PCF_o_c.RPCF_ULC_nounit.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition PCF_ULC_compilation := 
    InitMor PCF_ULC.

Definition PCF_ULC_c := 
   rep_Hom_monad PCF_ULC_compilation.

(** some examples *)
(**
Eval compute in 
  (PCF_ULC_c (fun t => False) tt 
               (ctype _ (Bottom (fun _ => False) Nat))).
Eval compute in 
  (PCF_ULC_c (fun t => False) tt 
               (ctype _ (Const (fun _ => False) (succ )))).
Eval compute in 
  (PCF_ULC_c (fun t => False) tt 
               (ctype _ (Const (fun _ => False) (preds )))).

Eval compute in 
  (PCF_ULC_c (fun t => False) tt 
               (ctype _ (Const (fun _ => False) (condB )))).


Eval compute in 
  (PCF_ULC_c ( (fun t => False)) tt
               (ctype _ (
                    Lam (RPCF_syntax.Var (none Bool (fun t => False)))))).
*)
