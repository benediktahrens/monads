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
                    Lam (PCF_syntax.Var (none Bool (fun t => False)))))).

Check ctype.
Check (Const (fun _ => False) condB).

Check (fun V t (a : PCF V t)  => PCF_ULC_c (V) tt
                   (ctype (fun t => tt) a)).

Require Import Coq.Program.Equality.

Lemma aaaa V t (a : PCF V t): 
        (exists b, (PCF_ULC_c _ _ 
                   (ctype (fun t => tt) a)) >>> b) ->
        (exists b',  a >> b').
intros.
 elim H.
 clear H.
 intros.
 simpl in *.
 inversion H.
 subst.
 exists a.
 reflexivity.
 subst.
 
 
 
 dependent induction H.



