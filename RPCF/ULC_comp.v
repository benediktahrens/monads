Require Export CatSem.RPCF.RPCF_INIT.
Require Export CatSem.RPCF.RPCF_ULC_nounit.

Set Implicit Arguments.
Unset Strict Implicit.
(*Unset Printing Implicit Defensive.*)
Unset Automatic Introduction.


Definition PCF_ULC_compilation := 
    InitMor PCF_ULC.

Definition PCF_ULC_c := 
   rep_Hom_monad PCF_ULC_compilation.
Locate "@".
(** some examples *)

Notation "a @ b" := (App a b) (at level 20, left associativity).
Notation "a @@ b" := (PCF_syntax.App a b) (at level 20, left associativity).
Notation "'1'" := (Var None) (at level 33).
Notation "'2'" := (Var (Some None)) (at level 24).
Notation "'3'" := (Var (Some (Some None))) (at level 23).
Notation "'4'" := (Var (Some (Some (Some None)))) (at level 22).

Notation "'y'" := (PCF_syntax.Var None) (at level 33).

Eval compute in 
  (PCF_ULC_c (fun t => False) tt 
               (ctype _ (Bottom (fun _ => False) PCF.Nat))).
Eval compute in 
  (PCF_ULC_c (fun t => False) tt 
               (ctype _ (succ ' ))).

Eval compute in 
  (PCF_ULC_c (fun t => False) tt 
               (ctype _ (Const (fun _ => False) (succ )))).
Eval compute in 
  (PCF_ULC_c (fun t => False) tt 
               (ctype _ (preds '))).

Eval compute in 
  (PCF_ULC_c (fun t => False) tt 
               (ctype _ (condB '))).

Eval compute in 
  (PCF_ULC_c (fun t => False) tt (ctype _ 
       (condB ' @@ ttt ' @@ fff ' @@ ttt '))).

Eval compute in 
  (PCF_ULC_c (opt PCF.Bool (fun t => False)) tt (ctype _ 
       (condB ' @@ (PCF_syntax.Var (none PCF.Bool (fun t => False))) @@ fff ' @@ ttt '))).

Notation "'x_bool'" := (PCF_syntax.Var (none PCF.Bool (fun t => False))).

Eval compute in 
  (PCF_ULC_c ((fun t => False)) tt (ctype _        
   (Lam (condB ' @@ (PCF_syntax.Var (none PCF.Bool (fun t => False))) @@ fff ' @@ ttt ')))).

Eval compute in 
  (PCF_ULC_c ((fun t => False)) tt (ctype _        
   (Lam (condB ' @@ x_bool @@ fff ' @@ ttt ')))).




Check Lam.
(*
Eval compute in 
  (PCF_ULC_c (fun t => False) tt (ctype _ 
     (Lam (condB ' @@ PCF_syntax.Var None @@ fff ' @@ ttt ')))).
*)
Eval compute in 
  (PCF_ULC_c ( (fun t => False)) tt
               (ctype _ (
                    Lam (PCF_syntax.Var (none PCF.Bool (fun t => False)))))).

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



