Require Export CatSem.PCF_order_comp.RPCF_ULC_sandbox.
Require Export CatSem.PCF_order_comp.RPCF_INIT.

Unset Printing Implicit Defensive.

Definition PCF_ULC_compilation := 
    InitMor PCF_ULC.

Definition PCF_ULC_c := 
   rep_Hom_monad PCF_ULC_compilation.
(** example
Eval compute in 
  (PCF_ULC_c (fun t => False) tt 
               (ctype _ (Bottom (fun _ => False) Nat))).
*)