Require Import Coq.Arith.Le Coq.Arith.Lt 
               Coq.Arith.Compare_dec. 
Require Import Coq.Logic.ProofIrrelevance.

Require Export CatSem.CAT.functor.

Definition PI := proof_irrelevance.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Automatic Introduction.

Section N_set.
Variable n:nat.

Definition N_set:= {m | m < n}.

Definition projTT : N_set -> nat := 
     fun x => proj1_sig x.

Coercion projTT : N_set >-> nat.
(*
Definition injTT (k: nat) (H: k <= n): {m | m < n}.
intros k H. exists k. apply H. Defined.

Definition inj : {m | m < n} := injTT (le_n n). 
*)
End N_set.
(*
Coercion injTT : nat >-> Funclass.
*)
Notation "[[ n ]]" := (N_set n).

Section monotone_maps.


Inductive N_hom: nat -> nat -> Type :=
| empty: forall n, N_hom 0 n
| shift: forall n m, N_hom n (S m) -> N_hom (S n) (S m)
| lift: forall n m, N_hom (S n) m -> N_hom (S n) (S m).


Definition HomDelta (n m: nat) := N_hom n m.
(*
Definition bla: False -> nat.
intro f. elim f.
*)

Require Import Arith.

Definition monotone (m n: nat) (f: [[m]] -> [[n]]) :=
          forall x y: [[m]], x <= y -> f x <= f y.
(*
Program Fixpoint interp (n m:nat)(f:HomDelta n m) {struct f} : 
          { f: [[n]] -> [[m]] | monotone f } :=

      match f with
      | empty _ => _ 
      | shift p q f' => fun n => match n with
                             | O => O 
                             | S n' => (interp f') (exist _ n' _ )
                             end
      | lift p q f' => fun n => S (interp f' n)
      end.

Next Obligation. unfold N_set. unfold HomDelta in f.
   elim f.
*)
Definition interp: forall n m (f:HomDelta n m), [[n]] -> [[m]].
intros n m f x.
induction f.
unfold N_set in x.
elim x.
intros b c.
assert False.
apply (lt_n_O _ c).
elim H.

destruct x as [x p].
destruct x.
exists 0. auto with arith.
assert (H0: x < n).
apply lt_S_n. 
assumption. 
apply (IHf (exist (fun x => x < n) x H0)).

set (y := IHf x).
destruct y.
assert (H0: S x0 < S m).
apply lt_n_S.
assumption.
apply (exist (fun x => x < S m) (S x0) H0).
Defined.



Definition interp2: forall n m (f: HomDelta n m), [[n]] -> nat.
intros n m f x.
induction f.
elim x. intros x0 H.
assert False. apply (lt_n_O _ H). elim H0.

destruct x as [x p].
destruct x.

exact 0.

assert (H0: x < n).
apply lt_S_n. assumption.
apply (IHf (exist (fun x => x < n) x H0)).

exact  (S (IHf x)).
Defined.

Section test.
Hypothesis H: 0 < S (S 0).

Definition test :=  shift (shift (empty 1)).

(*
Eval compute in ((interp2 test) (exist (fun x => x < 2) O H)).
Eval compute in (interp test) (exist (fun x => x < 2) O H).
*)
End test.

Lemma f_PI : forall m n (f: [[m]] -> [[n]]), 
             forall k l (H: k = l) pk pl, 
             f (exist _ k pk) = f (exist _ l pl).
Proof. intros m n f k l H. 
        rewrite H. intros pk pl. rewrite (PI _ pk pl).
        auto.
Qed.

Lemma f_PI2 : forall m n (f: [[m]] -> [[n]]), 
             forall k pk pl r,
          r = proj1_sig (f (existT _ k pk)) -> 
          r = proj1_sig (f (existT _ k pl)).
Proof. intros. simpl.  rewrite <- (PI _ pk pl). auto.
Qed.

Lemma f_PI3 : forall m n (f: [[m]] -> [[n]]),
              forall k pk pl,
            f (exist _ k pk) = f (exist _ k pl).
Proof. intros m n f k pk pl. 
       rewrite <- (PI _ pk pl). auto.
Qed.

Lemma f_PI4: forall m n (f: [[m]] -> [[n]]),
                forall k pk pl, 
          proj1_sig (f (exist _ k pk)) = 
          proj1_sig (f (exist _ k pl)).
Proof. intros. rewrite (f_PI3 f pk pl).
          auto.
Qed.

Require Import Omega.

Lemma interp_monotone: forall m n (f: N_hom m n), monotone (interp f).
Proof. induction f.
    unfold monotone. intro x. elim x.
    intros x0 p. 
    assert (H': False).  apply (lt_n_O x0 p). 
    elim H'. 
    
    unfold monotone. intros x y H. 
    destruct x as [x px].
    destruct y as [y py]. simpl in *|-*.
    destruct x. destruct y. simpl. auto.
        simpl. omega.
      destruct y. simpl. omega. 
        unfold monotone in IHf. 
        apply IHf. auto with arith.

    unfold monotone. intros x y H. simpl.
    assert (H': interp f x <= interp f y).
    apply IHf. auto.
    destruct (interp f x).
    destruct (interp f y). simpl in *|-*.
    auto with arith.
Qed.

Section translating_back.
(*
Hypothesis H: forall m n (f: [[m]] -> [[n]]), monotone f.

*)
Definition ins_0 (m:nat) : [[S m]] := exist (fun x => x < S m) 0 
                              (lt_O_Sn m).
(*
Definition shift_down (m n:nat) (f: [[S m]] -> [[S n]])
           (H: monotone f)
           (H': f (ins_0 m) > 0): [[S m]] -> [[n]].
intros m n f H H' x.
exists (pred (f x)).
assert (Hx : 1 <= f x).
apply le_trans with (f (ins_0 m)).
assumption.
apply H. auto with arith.
assert (Hxx: f x < (S n)).
elim f.
intros. simpl. assumption.
assert (pred (f x) < f x).
apply lt_pred_n_n. apply Hx.
apply le_trans with (f x). 
rewrite <- (@S_pred (f x) 0). auto with arith.
apply Hx. auto with arith.
Defined.

Lemma shift_down_monotone (m n:nat)(f: [[S m]] -> [[S n]])
           (H: monotone f)
           (H': f (ins_0 m) > 0):
         monotone (shift_down H H').
Proof. unfold monotone. intros m n f H H' x y Hxy.
       simpl.
       apply le_pred. apply H. auto.
Defined.
*)

Program Definition unlift (m n: nat) (f: [[S m]] -> [[S n]])
             (H: monotone f)
            (H': f (ins_0 m) > 0) (x:[[S m]]) : [[n]] :=
      pred (f x).
Next Obligation.
Proof. 
  simpl;
  intros m n f H H0 x.
  assert (Hx : 1 <= f x).
  apply le_trans with (f (ins_0 m)).
  assumption.
  apply H. auto with arith.
  assert (Hxx: f x < (S n)).
  elim f.
  intros. simpl. assumption.
  assert (pred (f x) < f x).
  apply lt_pred_n_n. apply Hx.
  apply le_trans with (f x). 
  rewrite <- (@S_pred (f x) 0). auto with arith.
  apply Hx. auto with arith. 
Qed.

Lemma unlift_monotone (m n:nat)(f: [[S m]] -> [[S n]])
           (H: monotone f)
           (H': f (ins_0 m) > 0):
         monotone (unlift H H').
Proof. unfold monotone. intros m n f H H' x y Hxy.
       simpl.
       apply le_pred. apply H. auto.
Qed.



Require Import Omega.

Program Definition unshift (m n: nat) (f: [[S m]] -> [[n]])
                 : [[m]] -> [[n]] :=
      fun x => f (S x).
Next Obligation. 
Proof. 
  intros m n f x.
  elim x. intros. 
  simpl.
  apply lt_n_S. 
  auto. 
Qed.

Lemma unshift_monotone (m n: nat) (f: [[S m]] -> [[n]]) : 
          monotone f -> monotone (unshift f).
Proof. unfold monotone. intros m n f H x y Hxy.
       unfold unshift. apply H. simpl. auto with arith.
Qed.

End translating_back.
End monotone_maps.
(*
Obligation Tactic := idtac.
*)
(*
Program Fixpoint abstr (m n:nat) (f: [[m]] -> [[n]]) (H: monotone f)
               {measure (plus n m)} : N_hom m n :=
     match m with
     | 0 => empty n
     | (S m') => match n with 
                | 0 => _
                | S n' =>
                    match (f (ins_0 (m'))) with
                   | 0 => shift (abstr (f:=(unshift f)) (unshift_monotone H))
                   | S p' => lift (abstr (f:=(@unlift _ _ f H (lt_O_Sn p')))
                                      (unlift_monotone H (lt_O_Sn p')))
                   end
                end
     end.

Next Obligation. 
  intros. subst. 
  unfold N_set in *|-*.
  elim f.
  intros x H'.
  assert (H0:False).
  apply (lt_n_O x). assumption.
  elim H0.
  exists m'. apply lt_n_Sn.
Defined.
Next Obligation. 
Proof.
  intros.
  simpl.
  subst.
  apply lt_O_Sn. 
Qed.
Next Obligation. 
Proof.
  simpl; intros.
  subst.
  destruct x0; auto. 
Qed.
Next Obligation. 
Proof.
  simpl; intros.
  omega.
Qed.
Next Obligation. 
Proof.
  simpl; intros.
  subst.
  destruct x0; 
  auto. 
Qed.  
Next Obligation. 
Proof.
  simpl; intros;
  subst.
  destruct x.
  auto.
Qed.
Next Obligation.
Proof.
  simpl; intros;
  subst.
  destruct x0.
  auto.
Qed.
Next Obligation.
Proof.
  simpl in *.
  intros;
  subst.
  elim f.
  simpl.
  intros.
  omega.
  exists m'.
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros.
  elim f.
  simpl.
  auto.
Qed.
Next Obligation.
Proof.
  apply f_PI2 with (abstr_func_obligation_2 (f:=f) H abstr eq_refl
                          eq_refl). 
  auto.
Qed.
Next Obligation. 
Proof.
  apply f_PI4.
Qed.
Next Obligation. 
Proof.  
  apply f_PI4. 
Qed. 
Next Obligation. 
Proof. 
  apply f_PI2 with (abstr_func_obligation_2 (f:=f) H abstr eq_refl
                          eq_refl). 
  auto. 
Qed.

Definition abstract (m n:nat) (f:{f:[[m]] -> [[n]] | monotone f}) :=
             abstr (proj2_sig f).

  
(* maybe some of these should end with Defined rather than Qed *)

Section waterloo.

Definition N_idf (n:nat): [[n]] -> [[n]] := fun x => x.

Lemma N_id_monotone (n:nat) : monotone (@N_idf n).
Proof. intro n. unfold monotone. auto. Qed.

Definition N_id (n:nat) : { f: [[n]] -> [[n]] | monotone f } :=
            exist _ (@N_idf n) (@N_id_monotone n).

Definition N_id3 := @N_id 3.
(*
Eval compute in (abstract N_id3).
*)
Lemma comp_monotone: forall k m n (f: [[k]] -> [[m]]) 
                                  (g: [[m]] -> [[n]]), 
    monotone f -> monotone g ->
              monotone (fun x => g (f x)).
Proof. unfold monotone. intros k m n f g Hf Hg x y Hxy.
       apply Hg. apply Hf. auto. Qed.

Definition N_comp (k m n: nat) (f: N_hom k m) (g: N_hom m n) :=
        abstr (comp_monotone (interp_monotone f)
                             (interp_monotone g))
           (*(fun x => (interp g) (interp f x))*).


Program Definition id3min1: { f: [[3]] -> [[2]] | monotone f} :=
       fun x => pred x.

Next Obligation.
Proof. destruct x. simpl. omega. Qed.

Next Obligation.
Proof. unfold monotone. intros x y H. simpl.
       omega. Qed.
(*
Eval compute in (N_comp (abstract N_id3) 
                 (abstract id3min1)).
*)
End waterloo.

End translating_back.

Definition eq_H_hom1 (m n: nat) : relation (N_hom m n) :=
          fun f g => forall x, proj1_sig (interp f x) = 
                               proj1_sig (interp g x).

Lemma eq_H_hom_equiv (m n: nat) : Equivalence (@eq_H_hom1 m n).
Proof. 
  intros m n. 
  unfold eq_H_hom1. split.
    unfold Reflexive. auto.
    unfold Symmetric. auto.
    unfold Transitive. 
    intros x y z H H0 x0.
      transitivity (interp (n:=m) (m:=n) y x0).
      apply (H x0).
      apply (H0 x0).
Qed.

Definition eq_H_hom (m n: nat) := Build_Setoid (eq_H_hom_equiv m n).

Definition id_H_hom (n:nat) : N_hom n n := 
           abstract (@N_id n).

Program Definition interpret (m n: nat) (f: N_hom m n) :
                  { f: [[m]] -> [[n]] | monotone f } :=
 interp f.

Next Obligation. apply interp_monotone. Qed.
*)



(*
Lemma abstract_inj : forall m n (f g: { r: [[m]] -> [[n]] | monotone r }),
              abstract f = abstract g -> f = g.
Proof. intros m n f g H.
*)


(*
Lemma interp_inj: forall m n (f g: N_hom m n), 
       interp f = interp g -> f = g.
Proof. induction f. intros. simpl.
       destruct g. inversion g. simpl.
*)
(*
Lemma interp_after_abstract: forall m n 
        (f: { f: [[m]] -> [[n]] | monotone f }),  
     interpret (abstract f) = f.
Proof. intros m n f.
unfold interpret, abstract. simpl.
destruct f as [f p].
apply break_Sig_Prop. extensionality x.
destruct x as [x px].
simpl. unfold interp. simpl.
destruct x. simpl.
*)


(*
Lemma bla2: forall m n (f: { r: [[S m]] -> [[S n]] | monotone r }),
             (proj1_sig f) (ins_0 m) > 0 -> 
             exists t, abstract f = lift t.
Proof. intros. unfold abstract. unfold abstr.
        eauto. simpl. Admitted.

Lemma abstract_after_interp: forall m n (f:N_hom m n), 
          abstract (interpret f) = f.
Proof. induction f. auto.

      Focus 2.
      assert (H: proj1_sig (interpret (lift f)) (ins_0 n) > 0).
      apply bla. generalize H. simpl. 
      unfold interpret. unfold interp.
      simpl. auto with arith. auto.
      assert (H': exists t, abstract (interpret (lift f)) = lift t).
      apply bla2. auto.
      elim H'. intros.
      unfold interpret. unfold abstract. simpl.
      unfold interp. simpl. unfold abstr. simpl.
      auto.
        
       unfold abstract, interpret in *|-*. simpl in *|-*.
       unfold interp. simpl.
       unfold abstr. simpl.  red.
       rewrite IHf. simpl.  auto. simpl.

      unfold interpret. unfold abstract.
        simpl. auto. unfold abstr. unfold interp.
        simpl. unfold abstr_func. simpl.
          auto.













Definition monotone (m n: nat) (f: [[m]] -> [[n]]) :=
          forall i j: [[m]], i <= j -> f i <= f j.

Definition N_hom (m n:nat) := {f: [[m]] -> [[n]] | monotone f}.

Definition N_comp_h (k m n:nat) (f: [[k]] -> [[m]]) (g: [[m]] -> [[n]]):
                                    [[k]] -> [[n]] :=
       fun x => g (f x).

Lemma comp_monotone : forall k m n (f:[[k]] -> [[m]])
            (g:[[m]] -> [[n]]), monotone f -> monotone g -> 
                monotone (N_comp_h f g).
Proof. intros k m n f g H H'.
 unfold N_comp_h. unfold monotone. intros i j H0.
 apply H'. apply H. apply H0.
Qed.

Definition N_comp (k m n: nat) 
        (f:N_hom k [[m]]) (g:N_hom [[m]] [[n]]): 
                  N_hom [[k]] [[n]] :=
    exist (N_comp_h f g) (comp_monotone f g).

*)















(*
Definition partial_comp (k:nat) (f: nat -> nat) (g:nat -> nat) :=
       fun x => match le_lt_dec x k with
                | left _ => f x
                | right _ => g (f x) 
                end.


Definition up_one_k (m n: nat) (k:nat) (f:[[m]] -> [[n]]) 
            (H': monotone f)
            (H: f (inj m) < n ) : [[m]] -> [[n]].
intros m n k f H' H.
intro x.
case (le_lt_dec x k).
intro Hx. apply (f x). 

intro Hx. exists (S (f x)).
apply le_trans with (S (f (inj m))).
apply le_n_S.
apply H'.
apply x.
auto with arith.
Defined.


(*
Definition const (m n: nat) (k : {x | x <= m}) : 
                    {x | x <= m} -> {x | x <= 
*)
Definition const (m n:nat) (k: [[ n ]]) : [[ m ]] -> [[ n ]].
intros m n k.
apply (fun x => k).
Defined.

Inductive monotone (m n: nat): [[ m ]] -> [[ n ]] -> Prop :=
| mon_const: forall k: [[ n ]], monotone (const k)
| mon_up_one: forall f, monotone f -> monotone (up_one_k


Variables m n: nat.

Definition hom: ob -> ob -> Prop := 
           fun k l =>  k <= l.

Definition hom_oid (a b:ob): relation (hom a b) :=
        fun p q => p = q.

Lemma all_related: forall a b: ob, forall p q: hom a b,
             hom_oid p q.
Proof.  intros a b p q.
    unfold hom_oid.
    apply PI.
Qed.

Lemma hom_setoid (a b: ob): Equivalence (@hom_oid a b).
Proof. intros a b. unfold hom_oid.
 split. unfold Reflexive.
        auto.
        unfold Symmetric. auto.
        unfold Transitive. intros x y z.
        transitivity y; auto.
Qed.


Definition category_n_oid (a b: ob) := 
        Build_Setoid (hom_setoid a b).
*) 

