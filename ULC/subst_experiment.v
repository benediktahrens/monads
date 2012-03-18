
Require Export CatSem.CAT.monad_haskell.
Require Export CatSem.CAT.cat_TYPE.

Notation "X *" := (option X) (at level 5).

Section freshness.

(** b fresh for z =>  z{a:=x} == z{a:=b}{b:=x} *)

Variable P : Monad TYPE.
Variable X : Type.
Variable z : P (X*).
Variable a : P (X).
Implicit Arguments kleisli [C F a b].
Implicit Arguments weta [C F c].

Definition fresh_subst := kleisli P (a:=X*) (b:=X * *)
  (fun x => match x in option _ return P (X * *) with
            | Some x => weta P (Some (Some x))
            | None => weta P None
            end).

Definition left_subst := kleisli P
  (fun x => match x in option _ return P X with
           | Some x => weta P x
           | None =>  a
           end).

Definition right_subst := kleisli P
   (fun x => match x in option _ return P X with
             | Some x' => match x' with 
                                   | Some x'' => weta P x''
                                   | None => a
                                   end
             | None => a
             end).

Lemma don: left_subst z = right_subst (fresh_subst z).
Proof.
  unfold left_subst.
  unfold right_subst.
  unfold fresh_subst.
  rew (klkl P) .
  assert (H:= kl_eq P).
  simpl in H.
  apply H.
  intros.
  destruct x; simpl; auto.
  rew (etakl P).
  rew (etakl P).
Qed.

End freshness.

Section freshness2.

(** b fresh for z =>  z{b:=x} == z *)

Variable P : Monad TYPE.

Variable X : TYPE.

Variable z : P X.

Definition z' : P(X*) := lift (M:=P) (@Some X) z.

Variable a : P X.

Implicit Arguments kleisli [C F a b].
Implicit Arguments weta [C F c].

Definition freshsubst := kleisli P (a:=X*)(b:=X)
     (fun x => match x with 
               | Some x => weta P x
               | None => a
               end).


Lemma don2 : freshsubst z' = z.
Proof.
  unfold freshsubst.
  unfold z'.
  unfold lift.
  simpl.
  rew (klkl P).
  app (kleta_id (FM:=P)).
  intros.
  rew (etakl P).
Qed.

End freshness2.

(*
  simpl.
  simpl.
  rew (etakl P).

Check inj.



  simpl.
  generalize a; clear a.
  

Require Export CatSem.ULC.ULC_syntax.

Section freshness.

Variable X : Type.

Variable z : ULC (X* ).
Variable a : ULC X.

Definition fresh_subst := _subst 
  (fun x => match x in option _ return ULC (X * * ) with
            | Some x => Var (Some (Some x))
            | None => Var None
            end).

Definition left_subst := _subst
  (fun x => match x in option _ return ULC X with
           | Some x => Var x
           | None => a
           end).

Definition right_subst := _subst
   (fun x => match x in option _ return ULC X with
             | Some x' => match x' with 
                                   | Some x'' => Var x''
                                   | None => a
                                   end
             | None => a
             end).
Check _subst.
Check left_subst.

Require Import Coq.Program.Equality.

Lemma don: left_subst z = right_subst (fresh_subst z).
unfold left_subst.
unfold right_subst.
unfold fresh_subst.
generalize a.
clear a.
generalize z.
clear z.
intro z.
dependent inversion z;
simpl; intros.
destruct o;
simpl; auto.
apply f_equal.
*)

