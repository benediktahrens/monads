
Require Import Coq.Bool.Bvector.
Require Export CatSem.CAT.cat_TYPE.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.


Ltac app_any := match goal with [H:_|-_]=>apply H end.

(** this should be in std lib -- wtf *)

Section Vmap.

Variables A B : Type.
Variable f : A -> B.

Fixpoint Vmap n (X : vector A n) : vector B n := 
  match X in vector _ n return vector B n with
  | Vnil => Vnil _
  | Vcons a _ al => Vcons _ (f a) _ (Vmap al) end.

End Vmap.

Ltac simpind x := induction x; simpl; auto; rew_all; auto.

Lemma Vmap_id A l x: Vmap (A:=A) (fun x => x) (n:=l) x = x.
Proof.
  simpind x.
Qed.

Lemma Vmap_comp A B C (f : A -> B) (g : B -> C) l (x : vector A l):
     Vmap (fun x => g (f x)) x = Vmap g (Vmap f x).
Proof.
  simpind x.
Qed.  

Hint Rewrite Vmap_id : vec.
Hint Resolve Vmap_id : vec.

Ltac vec := simpl; intros; autorewrite with vec;
               auto with vec.


Record type_sig : Type := {
  ts_ind : Type ;
  ts_dom : ts_ind -> nat }.


Section type_arity_reps.

Variable T : type_sig.

Class ts_rep_struct (X : Type) := {
  ts_rep_s : forall a : ts_ind T, vector X (ts_dom a) -> X  }.

Record ts_rep := {
  ta_c :> Type ;
  ta_rep_s :> ts_rep_struct ta_c }.

Existing Instance ta_rep_s.

Section homs.

Variable A B : ts_rep.

Class ts_rep_hom_s (f : A -> B) : Prop := {
   ts_rep_hom_com : 
       forall (a : ts_ind T) (x : vector A (ts_dom a)), 
                   f (ts_rep_s x) = ts_rep_s (Vmap f x) }.

Record ts_rep_hom : Type := {
  ts_rep_hom_c :> A -> B ;
  ts_rep_hom_struct :> ts_rep_hom_s ts_rep_hom_c }.

End homs.

Existing Instance ts_rep_hom_struct.

Obligation Tactic := vec.

Program Instance ts_rep_id_s A : ts_rep_hom_s (fun x : _ A => x).
Definition ts_rep_id A := Build_ts_rep_hom (ts_rep_id_s A).

Obligation Tactic := simpl; intros; auto;
          repeat (rewrite Vmap_comp || rewrite ts_rep_hom_com ; app_any || auto).

Program Instance ts_rep_comp_s A B C (f : ts_rep_hom A B) (g : ts_rep_hom B C) :
                 ts_rep_hom_s (fun x : _ A => g (f x)).
Definition ts_rep_comp A B C f g := Build_ts_rep_hom (ts_rep_comp_s A B C f g).

Obligation Tactic := vec ; unfold Transitive; simpl; intros; etransitivity; auto.

Program Instance ts_eq A B : Equivalence (fun f g : ts_rep_hom A B => forall x, f x = g x).
Definition ts_oid A B := Build_Setoid (ts_eq A B).



Obligation Tactic := unfold Proper, respectful; simpl; intros; 
        repeat rew_all; auto.

Program Instance TS_rep_s : Cat_struct ts_rep_hom := {
  mor_oid a b := ts_oid a b ;
  id := ts_rep_id ;
  comp := ts_rep_comp }.

Definition TS_rep := Build_Cat TS_rep_s.

Inductive ts_in : Type :=
  ts_build : forall i : ts_ind T, ts_in_list (ts_dom i) -> ts_in
with 
  ts_in_list : nat -> Type :=
   | vnil : ts_in_list 0
   | vcons : forall n, ts_in -> ts_in_list n -> ts_in_list (S n).
  
Scheme ts_induct := Induction for ts_in Sort Prop with
      ts_list_induct := Induction for ts_in_list Sort Prop.

Fixpoint vec_f_ts_list n (x : ts_in_list n) : vector ts_in n :=
    match x in ts_in_list n return vector ts_in n with 
        | vnil => Vnil 
        | vcons _ a l => Vcons a (vec_f_ts_list l) end.

Fixpoint ts_list_f_vec n (x : vector ts_in n) : ts_in_list n :=
    match x in vector _ n return ts_in_list n with 
        | Vnil => vnil 
        | Vcons a _ l => vcons a (ts_list_f_vec l) end.

Lemma one_way n (x : ts_in_list n) : 
         ts_list_f_vec (vec_f_ts_list x) = x.
Proof.
  simpind x.
Qed.

Lemma or_another n (x : vector ts_in n) : 
         vec_f_ts_list (ts_list_f_vec x) = x.
Proof.
  simpind x.
Qed.


Program Instance ts_init_rep_s : ts_rep_struct ts_in := {
   ts_rep_s := fun a x => ts_build (ts_list_f_vec x) }.
Definition ts_init : TS_rep := Build_ts_rep ts_init_rep_s.

Section init.

Variable R : TS_rep.

Fixpoint init (x : ts_in) : R :=
  match x with ts_build i l => ts_rep_s (init_list l) end
with
  init_list i (x : ts_in_list i) : vector R i :=
  match x in ts_in_list i return vector R i with 
    vnil => Vnil
    | vcons _ a al => Vcons (init a) (init_list al) end.

Lemma init_list_vmap (a : ts_ind T) (x : vector ts_in (ts_dom (t:=T) a)) : 
    init_list (ts_list_f_vec x) = Vmap init x.
Proof.
  induction x; simpl;
  repeat (reflexivity || rew_all).
Qed.

Hint Rewrite init_list_vmap : vec.

Obligation Tactic := vec.

Program Instance init_hom_s : ts_rep_hom_s (A:=ts_init) (B:=R) init.

Definition init_hom := Build_ts_rep_hom init_hom_s.

Lemma unique : forall f : ts_init ---> R, f == init_hom.
Proof.
  simpl.
  intro f.  
  apply (@ts_induct 
              (fun t => f t = init t)
              (fun n lk => Vmap f (vec_f_ts_list lk) = init_list lk));
  simpl; intros; auto.
  assert (H2:= @ts_rep_hom_com _ _ f).
  simpl in H2.
  rewrite <- H.
  rewrite <- (H2 f).
  apply f_equal.
  apply f_equal.
  rew one_way.
  repeat rew_all.
  auto.
Qed.

End init.

Program Instance ts_INIT : Initial TS_rep := {
  Init := ts_init ;
  InitMor := init_hom ;
  InitMorUnique := unique
}.

End type_arity_reps.

