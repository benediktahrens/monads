
Require Import Coq.Setoids.Setoid. 
Require Import Coq.Classes.SetoidClass.

Require Import Coq.Arith.Le 
               Coq.Arith.Lt 
               Coq.Arith.Compare_dec. 
Require Import Coq.Logic.ProofIrrelevance. 
Require Import Coq.Relations.Relations.


Require Export CatSem.CAT.functor. 
Require Export CatSem.CAT.my_lib.



Definition PI := proof_irrelevance.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Section N_set.
Variable n:nat.

Definition N_set:= {m | m < n}.

Definition projTT : N_set -> nat := 
     fun x => proj1_sig x.

Coercion projTT : N_set >-> nat.

End N_set. 

Notation "[[ n ]]" := (N_set n).
(*
Lemma N_set_inj: forall a b, [[a]] = [[b]] -> a = b.
Proof. unfold N_set.
        intros a b H.
        case (lt_eq_lt_dec a b).
        intro H'; case H'.
        intro Hl.
        set (HH:= (exist (fun x => x < b) a Hl)).
        (*
        generalize HH.
        *) rewrite <- H in HH.
        destruct HH.
        unfold N_set in H.
        H.
        induction a. destruct b.
                    auto.
             intro H. unfold N_set in *|-*. 
              H. intuition.
       intros b H.
       intro a b H. unfold N_set in H.
       injection H.
*)
Section delta_maps.

Variables m n: nat.

Definition monotone (f: [[m]] -> [[n]]) :=
          forall x y: [[m]], x <= y -> f x <= f y.

Definition HomDelta := { f : [[m]] -> [[n]] | monotone f }.

Definition forget_mon (f: HomDelta) :=
                proj1_sig f.

Coercion forget_mon: HomDelta >-> Funclass.

Definition eq_HomDelta1 : relation HomDelta :=
          fun f g => forall x, proj1_sig (f x) = 
                               proj1_sig (g x).

Lemma eq_H_hom_equiv : Equivalence (@eq_HomDelta1).
Proof. unfold eq_HomDelta1. split.
    unfold Reflexive. auto.
    unfold Symmetric. auto.
    unfold Transitive. intros x y z H H0 x0.
      transitivity (y x0).
      apply (H x0).
      apply (H0 x0).
Qed.

Definition eq_HomDelta := Build_Setoid eq_H_hom_equiv.

End delta_maps.


Notation "f =D= g" := (eq_HomDelta1 f g) (at level 70).


Section Delta_id_comp.

Variable n:nat.

Program Definition IdD: HomDelta n n := fun x => x.
Next Obligation.
  Proof. unfold monotone. auto. Qed.

Variables k m: nat.
Variable f: HomDelta k m.
Variable g: HomDelta m n.

Program Definition compDelta: HomDelta k n :=
        fun x => g (f x).
Next Obligation.
  Proof. unfold monotone. intros x y H. 
         apply (proj2_sig g).
         apply (proj2_sig f). auto.
  Qed.

End Delta_id_comp.

Section Cat_properties_Delta.

Variables m n: nat.
Variable f: HomDelta m n.

Lemma Delta_idl:  
         compDelta f (IdD n) =D= f.
Proof. unfold compDelta. simpl.
       unfold eq_HomDelta1. intro x.
       simpl. auto. Qed.

Lemma Delta_idr: 
         compDelta (IdD m) f =D= f.
Proof. unfold compDelta. simpl.
       unfold eq_HomDelta1. intro x.
       simpl. auto. Qed.

Variables k l: nat.
Variable g: HomDelta k l.
Variable h: HomDelta l m.

Lemma Delta_assoc:
        compDelta g (compDelta h f) =D= compDelta (compDelta g h) f.
Proof. unfold compDelta.
       unfold eq_HomDelta1. auto.
Qed.

End Cat_properties_Delta.


Program Instance Delta_Cat: Cat (fun m n => HomDelta m n) := {
  mor_oid a b := eq_HomDelta a b;
  id a := IdD a;
  comp k m n f g := compDelta f g;
  id_r := Delta_idr;
  id_l := Delta_idl
  (*Assoc k l m n f g h:= Delta_assoc f g h*)
}.

  Next Obligation.
    Proof. unfold Proper. red. red.
           unfold eq_HomDelta1. simpl. 
           intros x y H x0 y0 H0 x1.
           rewrite H0. 
           assert (H': x x1 = y x1). 
           apply break_Sig_Prop2. auto.
           rewrite H'. auto.
    Qed.

  Next Obligation.
    Proof. unfold eq_HomDelta1. auto. Qed.


Definition DELTA : Category := Build_Category Delta_Cat.



Require Import Omega.

Definition ins_0 (m:nat) : [[S m]] := 
     exist (fun x : nat => x < S m) 0 (lt_0_Sn m).
Require Export initial_terminal.
(*
Lemma elem_unique_1: forall x : [[S 0]], `x = 0.
Proof. intro x. elim x. intros. inversion p. simpl.
       auto. inversion H0. Qed.
*)
(*
Program Definition terminal_Delta: terminal (C:= DELTA) (S 0) := 
      fun a => fun x => (ins_0 0).

  Next Obligation.
    Proof. unfold monotone. simpl. auto. Qed.
  
  Next Obligation.
    Proof. unfold eq_HomDelta1. intro x. simpl.
           rewrite (elem_unique_1 (`(g x))). auto.
    Qed.
*)
Definition empty_map: forall m, [[0]] -> [[m]].
intros m a. elim a. intros x H.
assert (H':False).
apply (lt_n_O x H). 
elim H'.
Defined.

Lemma empty_is_empty: forall m: [[0]], False.
Proof. intro a. destruct a as [a p]. apply (lt_n_O a p).
Qed.

Lemma empty_map_monotone : forall m, monotone (empty_map m).
Proof. intro m. unfold monotone. intros x y.
           assert (H: False).
           apply (empty_is_empty x).
           inversion H.
Qed.

Definition empty_HomDelta: forall m, HomDelta 0 m :=
            fun m => exist _ (empty_map m) 
                             (empty_map_monotone m).


Program Definition init_Delta:  initial (C:=DELTA) 0 :=
            fun a => empty_HomDelta a.

  Next Obligation.
    Proof. apply empty_map_monotone. Qed. 

  Next Obligation. 
    Proof. unfold eq_HomDelta1. intro x. simpl. 
           assert (H: False).
           apply (empty_is_empty x).
           inversion H.
    Qed.



Lemma cod_wd: forall m n (f: [[m]] -> [[n]]) (x:[[m]]), 
                   f x < n.
Proof. intros m n f x. destruct (f x).
        simpl. auto. Qed.

Lemma cod_wd2: forall m n (f: [[m]] -> [[n]]) (x: [[m]]), 
               forall k:nat,  f x < n + k.
Proof. intros m n f x k.
       assert (f x < n).
       apply cod_wd.
       apply le_trans with n; auto. auto with arith.
Qed.
 
Lemma lt_minus: forall i m n, i < m + n -> n <= i -> i - n < m.
Proof. induction n. intros H0 H1. omega. 
       omega.
Qed.

Lemma lt_plus_right : forall m n, m < n -> forall i, m + i < n + i.
Proof. induction m. intros n H i. omega.
                    intros n H i. omega.
Qed.

Lemma lt_plus_left: forall m n, m < n -> forall i, i + m < i + n.
Proof. induction m. intros n H i. omega.
                    intros n H i. omega.
Qed.

Lemma le_plus_left: forall m n, m <= n -> forall i, i + m <= i + n.
Proof. induction m; intros n H i; omega. Qed.

Lemma lt_imp_le: forall m n, m < n -> m <= n.
Proof. intros. omega. Qed.

Lemma eq_plus_left: forall m n, m = n -> forall i, i + m = i + n.
Proof. auto. Qed.

Lemma f_g_equal (m n:nat) (f g: [[m]] -> [[n]]): 
       forall x, eq (A:=nat) (f x) (g x) -> eq (A:=[[n]])(f x) (g x).
Proof. intros m n f g x H. apply break_Sig_Prop2. auto. Qed.

Lemma eq_plus_minus (m n:nat) : m + n - m = n.
Proof. intros; omega. Qed.

Section plus_bifunctor.

Require Import prods.

Section plus_on_morphisms.

Variables m m' n n': nat.
Variable f: HomDelta n n'.
Variable g: HomDelta m m'.


Program Definition plus_morphism : HomDelta (n + m) (n' + m') :=
         fun i => match le_lt_dec n i return [[n' + m']] with
                  | right _ => f i 
                  | left _ => n' + g (i - n)
                  end.
(*
  Next Obligation.
    Proof. apply cod_wd2. Defined.
  *)
  Next Obligation. 
    Proof. apply lt_minus.
           rewrite plus_comm.
           apply (proj2_sig i).
           auto. 
   Qed.

  Next Obligation.
    Proof. apply lt_plus_left.
           apply cod_wd.
    Qed.

  Next Obligation.
    Proof. apply cod_wd2.
    Qed.

  Next Obligation.
    Proof. unfold monotone. intros x y H.
           case (le_lt_dec n x);
           intro l; simpl;
           case (le_lt_dec n y);
           intro l0. simpl.
           apply (le_plus_left).
           apply (proj2_sig g).
           simpl. omega.
           
           simpl; omega.

           simpl. 
           apply (le_trans) with n'.
           apply lt_imp_le. apply cod_wd.
           omega.
           
           simpl.
           apply (proj2_sig f). auto.
  Qed.
          
End plus_on_morphisms.



(*
Program Definition plusF: Functor (PROD DELTA DELTA) DELTA := Build_Functor
  (Fobj := fun a =>  plus (fst a) (snd a))
  (Fmor := fun a b f => plus_morphism (fst f) (snd f)) _ .



  Next Obligation.
    Proof. constructor.
    
           unfold Proper. red. 
           unfold Prod_equiv1, eq_HomDelta1. 
           intros a b f g H x.
           simpl.
           destruct a as [a1 a2].
           destruct b as [b1 b2].
           destruct f as [f1 f2].
           destruct g as [g1 g2].
           simpl in *|-*.
           case (le_lt_dec a1 x); intro H'; simpl.
           unfold eq_HomDelta1 in H.
           apply eq_plus_left.
           apply (proj2 H).
           apply (proj1 H).
           
           intro a.
           unfold eq_HomDelta1. intro x. simpl.
           destruct a as [a1 a2]. simpl in *|-*.
           case (le_lt_dec a1 x); intro l;
           destruct x; simpl in *|-*; omega.
           
           intros a b c f g.
           unfold eq_HomDelta1.
           destruct a as [a1 a2]. 
           destruct b as [b1 b2]. 
           destruct c as [c1 c2]. 
           destruct f as [f1 f2].
           destruct g as [g1 g2]. 
           simpl in *|-*. intro x.
           unfold plus_morphism, compDelta; simpl.
           case (le_lt_dec a1 x); 
           intro l; simpl. 
           case (le_lt_dec b1 _); 
           intro l0; simpl.
           apply eq_plus_left.
           repeat apply f_equal.
           apply break_Sig_Prop2.
           simpl. rewrite eq_plus_minus.
           simpl. auto. 
           
           omega.
           
           case (le_lt_dec b1 _);
           intro l0; simpl.
           set (H':= cod_wd f1 (exist _ (`x) l)).
           simpl in *|-*. 
           assert False. 
           apply (lt_not_le _ _ H'). auto.
           
           intuition.
           
           repeat apply f_equal.
           apply break_Sig_Prop2. simpl. auto.
    Qed.
*)

End plus_bifunctor.


(** DELTA is a subcat of SET *)

Require Import subcategories cat_SET.

Section DELTA_SET.

Definition DELTA_incl_ob (x: DELTA) : SET := N_set x.
Definition DELTA_incl_mor (x y: DELTA) (f: x ---> y): 
   mor (*Category:= SET*)(DELTA_incl_ob x)(DELTA_incl_ob y) := proj1_sig f.

Program Definition DELTA_incl_SET : Functor DELTA SET := Build_Functor
   (Fobj := DELTA_incl_ob) (Fmor := DELTA_incl_mor) _ .

  Next Obligation.
    Proof. constructor.
    
           unfold Proper. red.
           unfold eq_HomDelta1, SET_hom_equiv, 
                  DELTA_incl_mor, DELTA_incl_ob; simpl.
           intros a b f g H x.
           apply break_Sig_Prop2.
           apply H. 
           
           intro a; simpl;
           unfold SET_hom_equiv; intros; auto.
    
           intros a b c f g ;unfold SET_hom_equiv. 
           unfold DELTA_incl_mor,compDelta; intros.
           simpl. unfold SET_hom_equiv.
           auto.
    Qed.


(*
Hypothesis N_set_inj: forall m n, [[m]] = [[n]] -> m = n.   

Program Instance DELTA_SUB_SET: SubCat_struct DELTA_incl_SET.
Next Obligation. 
  Proof. unfold Finjective; simpl.
         unfold DELTA_incl_mor, DELTA_incl_ob.
         intros a b f c d g H.
         set (H':= Equal_hom_src H).
         set (H'':= Equal_hom_tgt H).
         inversion H'.
         clear H'.
         inversion H''. clear H''.
         set (Hac:= N_set_inj H1).
         set (Hbd:= N_set_inj H2).
         generalize H; clear H.
         generalize g; clear g.
         generalize f; clear f.
         rewrite Hac.
         rewrite Hbd.
         intros f g H.
         apply Build_Equal_hom.
         simpl.
         set (H':= Equal_hom_imp_setoideq2 H).
         simpl in H'.
         unfold SET_hom_equiv in H'.
         unfold eq_HomDelta1.
         intro x. simpl.
         assert (Hfgx: f x = g x). apply H'.
         rewrite Hfgx. auto.
Qed.
*)
End DELTA_SET.



(** we need to know that a strict monotone function is 
    an injective monotone one *)

Section monotone_and_strict_monotone_and_injectivity.

Definition injective (A B: Type)(f: A -> B) :=
         forall x y, f x = f y -> x = y.

Definition strict_monotone (m n: nat) (f: [[m]] -> [[n]]) :=
        forall x y:[[m]], x < y -> f x < f y.

Lemma eq_on_nat (m n: nat) (f: [[m]] -> [[n]]) 
         (i k: [[m]]) (H: proj1_sig i = proj1_sig k):
           f i = f k.
Proof. intros m n f i k H.
       assert (H': i = k).
       apply break_Sig_Prop2. auto.
       rewrite H'. auto.
Qed.


Lemma strict_monotone_imp_monotone (m n: nat) (f: [[m]] -> [[n]]):
         strict_monotone f -> monotone f.
Proof. unfold strict_monotone, monotone.  
       intros m n f H x y h.
       set (H':= le_lt_or_eq x y h).
       elim H'; intro HH. 
          assert (f x < f y). auto. 
          auto with arith.
          assert (Hh: f x = f y).
          apply eq_on_nat. auto. 
          rewrite Hh. auto.
Qed.
          
Lemma strict_monotone_imp_inj (m n: nat) (f: [[m]] -> [[n]]):
          strict_monotone f -> injective f.
Proof. unfold strict_monotone, injective. 
       intros m n f H x y Hxy.
       case (lt_eq_lt_dec x y).
       intro h. case h.
         intro hlt. 
         assert (f x < f y).
         apply H. auto.
         assert False. apply (lt_not_le (f x) (f y)).
                  auto.
               rewrite Hxy. auto.
               intuition.
            intro xy. apply break_Sig_Prop2. auto.
         intro xy.
       assert (hxy: f y < f x).
              apply H; auto.
          assert False. apply (lt_not_le (f y) (f x)).
                  auto.
               rewrite Hxy. auto.
             intuition.
Qed.

Hint Resolve break_Sig_Prop2.

Lemma monotone_and_inj_imp_strict_monotone (m n: nat) (f: [[m]] -> [[n]]):
         monotone f -> injective f -> strict_monotone f.
Proof. unfold monotone, injective, strict_monotone.
       intros m n f Hmon Hinj x y Hxy.
       assert (Hle: f x <= f y).
       apply Hmon. auto with arith.
       set (H':= le_lt_or_eq (f x) (f y) Hle).
       case H'.
             auto.
         intro HH.
         assert (Hxx: x = y). apply Hinj.
          apply break_Sig_Prop2. auto.
          rewrite Hxx in Hxy. intuition.
Qed.

Lemma strict_monotone_iff_monotone_inj (m n: nat) (f: [[m]] -> [[n]]):
         strict_monotone f <-> monotone f /\ injective f.
Proof. intros m n f.
      split; intro H.
       split. apply strict_monotone_imp_monotone. auto.
              apply strict_monotone_imp_inj. auto.
       elim H. apply monotone_and_inj_imp_strict_monotone.
Qed.
End monotone_and_strict_monotone_and_injectivity.






























