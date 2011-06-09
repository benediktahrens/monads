Require Export CatSem.PCF_o_c.RPCF_INIT.
Require Export CatSem.PCF_o_c.RPCF_ULC_nounit.

Set Implicit Arguments.
Unset Strict Implicit.
(*Unset Printing Implicit Defensive.*)
Unset Automatic Introduction.


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

Lemma aaaa V t (a : PCF V t) b :
      (PCF_ULC_c _ _  (ctype (fun t => tt) a)) >>> b ->
        (exists b',  a >> b' /\ PCF_ULC_c _ _ (ctype _ b') = b).
  intros V t a.        
  intro b.
  dependent induction b;
  simpl; intros.
  inversion H.
  exists (PCF_syntax.Var (ct ).
  exists (Bottom V t).
  split. reflexivity.
  simpl.
  inversion H. auto.
  subst. clear H. 
  inversion H0.
  subst.
  exists (Bottom V t).
  split.
  reflexivity.
  simpl; auto.
  subst.
  exists (Bottom V t).
  split. reflexivity.
  ssiauto.
  
  destruct H.
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



