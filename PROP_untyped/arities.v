Require Export Coq.Lists.List.

Require Export CatSem.CAT.cat_TYPE_option.
Require Export CatSem.CAT.rmonad.
Require Export CatSem.CAT.rmodule_TYPE.

Require Import Coq.Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Notation "[ T ]" := (list T) (at level 5).

Record Signature : Type := {
  sig_index : Type ;
  sig : sig_index -> [nat]
}.


Notation "V *" := (option V) (at level 5).
Notation "^ f" := (lift (M:= option_monad) f) (at level 5).

Ltac opt := simpl; intros; 
   repeat (cat || autorewrite with opt || auto with opt).

Fixpoint pow (n : nat) (V : TYPE) : TYPE :=
  match n with
  | 0 => V
  | S n' => pow n' (option V)
  end.

Notation "V ** l" := (pow l V) (at level 10).

(** adding variables is functorial *)

Fixpoint pow_map (l : nat) V W (f : V ---> W) :
         V ** l ---> W ** l :=
  match l return V ** l ---> W ** l with
  | 0 => f
  | S n' => pow_map (^ f)
  end.

(*Notation "V ' u" := (opt_T u V) (at level 10).*)
Notation "f ^^ l" := (pow_map (l:=l) f) (at level 10).
(*Notation "^ f" := (lift (M:= opt_T_monad _) f) (at level 5).*)

Ltac t := simpl; intros; 
      match goal with [H : _ * |-_] => destruct H end;
      unfold lift; simpl;
      repeat rew_all; auto.

Lemma lift_opt_monad (V W : TYPE) (f g : V ---> W)
     (H : forall x, f x = g x) : 
     forall x, lift (M:=option_monad) f x = ^g x.
Proof. t.
Qed.  

(** this thing works cuz of the strange semantics of the
    Ltac match *)

Ltac app_any := match goal with [H:_|-_] => app H end.

Lemma pow_map_eq l (V W : TYPE) (f g : V ---> W) 
     (H : forall (x : V) , f x = g x) : 
   forall x, f ^^ l x = g ^^ l x.
Proof.
  induction l; 
  repeat (cat || app_any ||
    app lift_opt_monad).
Qed.

Hint Rewrite pow_map_eq : opt.
Hint Resolve pow_map_eq : opt.

Obligation Tactic := intros; do 2 red; opt.

Instance pow_map_oid V W (l : nat) : 
    Proper (equiv ==> equiv) (pow_map (V:=V) (W:=W) (l:=l)).
Proof.
(*  simpl; intros;*)
  unfold Proper; red; opt.
Qed.

Lemma pow_id (l : nat) (a : TYPE) : (id a) ^^ l == id (a ** l).
Proof.
  induction l;
  repeat (cat || rewrite (pow_map_eq (g:=fun x => x)) ||
           app_any ||
          t; auto).
Qed.

Lemma pow_eq_id l (a : TYPE) f : f == id a -> f ^^ l == id _ .
Proof.
   intros.
   repeat (rew_all || auto using pow_id).
Qed.

Lemma pow_comp (l : nat) (a b c : TYPE) (f : a ---> b) (g : b ---> c):
(f;; g) ^^ l == f ^^ l;; g ^^ l.
Proof.
  induction l;
  cat; 
  match goal with
  [l: nat |- _ = ^?g ^^  _ (^?f ^^ _   _ )] => 
          rew (pow_map_eq (l:=l)(f:= ^(f ;; g)) 
               (g:=^f ;; lift (M:=option_monad) g)) end;
  cat; rew (lift_lift option_monad).
Qed.

(** multiple adding of variables is a functor BLOWUP *)
Obligation Tactic := auto using pow_id, pow_comp.

Program Instance POW_struct (l : nat) : Functor_struct (@pow_map l).

Canonical Structure POW l := Build_Functor (POW_struct l).

(** now some functions to blow up under monads and modules *)

Section pow_and_product.

Variable P : RMonad SM_po. 

Notation "'Var' x" := (rweta (RMonad_struct := P) _ x) (at level 55).
Notation "x >>= f" := (rkleisli (RMonad_struct := P) f x) (at level 65).

(*
Hint Resolve (shift_eq (P:=P)) (shift_weta P) 
             (shift_weta_f P) f_equal : opt.
Hint Rewrite (shift_eq (P:=P)) (shift_weta P) 
             (shift_weta_f P) : opt.
*)

(** lshift is SHIFTING wrt to a list of added variables 

     it enjoys the same properties as its little brother shift

*)

Fixpoint lshift_c (l : nat) (V W : TYPE) (f : SM_po V ---> P W) : 
         V ** l ---> P (W ** l) :=
    match l return V ** l ---> P (W ** l) with
    | 0 => f
    | S n' => lshift_c (shift_not f)
    end.

Definition lshift (l : nat) V W (f : SM_po V ---> P W) : 
              SM_po (V ** l) ---> P (W ** l) := 
                     Sm_ind (lshift_c f).
(*
Program Instance lshift_c_po l V W (f : SM_po V ---> P W):
     PO_mor_struct (lshift_c (l:=l) f).
Next Obligation.
Proof.
  unfold Proper; red.
  induction l.
  simpl.
*)

Notation "x >>- f" := (lshift _ f x)(at level 60).

Lemma lshift_eq l V W (f g : SM_po V ---> P W) 
     (H : forall  x, f x = g x):
    forall (x : V ** l ),
     lshift_c f x  = lshift_c g x .
Proof.
  induction l; cat;
  app_any; intros; t.
Qed.

Hint Resolve lshift_eq : opt.
Hint Rewrite lshift_eq : opt.

Ltac tt l := induction l;
 repeat (cat || 
         match goal with [H:_|-_] => rewrite <- H end ||
         apply lshift_eq || t || rew (rlift_rweta P)).

Lemma lshift_weta (l : nat) V (x : V ** l) :
      x >>- (rweta _) = Var x.
Proof.
  tt l. 
Qed.

Hint Resolve lshift_weta : opt.
Hint Rewrite lshift_weta : opt.

Lemma lshift_weta' l V :
    lshift l (rweta (RMonad_struct := P)V) == rweta _ . 
Proof.
  simpl; auto; opt; apply lshift_weta.
Qed.

Lemma lshift_weta_f (l : nat) V W (f : V ---> W) x:
   x >>- (#SM_po f ;; rweta W) = Var (f ^^ l x).
Proof.
  tt l.
Qed.

Lemma kleisli_lshift (l : nat) V W (f : SM_po V ---> P W)
         X (g : SM_po W ---> P X) (x : (V ** l)) :
   (x >>- f) >>= (lshift _ g) = x >>- Sm_ind (fun y => f y >>= g).
Proof.
  induction l;
  simpl; intros.
  app (rkl_eq P).
  simpl in IHl.

  assert (H:=IHl (V*) (W*)(shift_not f)(X*) (shift_not g) x).
  simpl in H.
  assert (H': lshift l (shift_not g) == lshift (S l) g).
  simpl. auto.
  transitivity ((rkleisli (a:=W * ** l) (b:=X * ** l)
       (lshift l (V:=W *) (W:=X *) (shift_not (P:=P) (V:=W) (W:=X) g)))
      (lshift_c (l:=l) (V:=V *) (W:=W *) (shift_not (P:=P) (V:=V) (W:=W) f) x)).
  apply (rkl_eq P).
  auto. 
  transitivity (lshift_c (l:=l) (V:=V *) (W:=X *)
      (Sm_ind (W:=P X *)
         (fun y : V * =>
          (rkleisli (a:=W *) (b:=X *) (shift_not (P:=P) (V:=W) (W:=X) g))
            (option_default
               (fun x : V => (rlift P (a:=W) (b:=W *) Some) (f x))
               ((rweta (RMonad_struct:=P) W *) None) y))) x).
  auto.
  apply lshift_eq.
  simpl. intros.
  t.


  rew (rkleisli_rlift (M:=P)).
  rew (rlift_rkleisli (M:=P)).
  apply (rkl_eq P). simpl.
  auto.
  rew (retakl P).
Qed.


(** multiple derivation of a module M wrt a list l *)

(** we never actually USE these definitions,
    but we use parts of the properties *)

Section many_derivs.
(*
Variable obD : Type.
Variable morD : obD -> obD -> Type.
Variable D : Cat morD.
*)
Variable D : Cat.
Variable M : RMOD P D.

(** the carrier of the often derived module *)

Definition der_mod_c (l : nat) (V : TYPE) : D := M (V ** l).

(** is needed in the proofs of mkl_mkl and mkl_weta,
    so we do it before *)

(* the often derived module is a module *)

Lemma der_mod_etakl c l: 
  rmkleisli (d:=c ** l) (lshift l (V:=c) (W:=c) (rweta c)) ==
     id (der_mod_c l c).
Proof.
  intros; rewrite lshift_weta'; mod; apply rmkleta.
Qed.

Hint Rewrite der_mod_etakl : opt.

Obligation Tactic := opt;
  repeat (unf_Proper || 
          match goal with [|-rmkleisli ?a ;; rmkleisli ?b == _ ] =>
             rew (rmklmkl M a b) end || 
          apply (rmkl_eq M) || apply lshift_eq  || 
          rew kleisli_lshift || opt); mod.

Program Instance der_mod_struct (l : nat) : 
        RModule_struct P _ (der_mod_c l):= {
 rmkleisli V W f:= rmkleisli (RModule_struct := M) (lshift l f)
}.

Definition D_mod (l : nat) := Build_RModule (der_mod_struct l).

End many_derivs.

(** now for 
      - M a module
      - l an arity 
   we build the product of fibres of derived modules of M wrt to l 

  morally this product module carries the arguments of the constructors
*)


Section prod_mod_built_from_scratch_carrier.

(*
Variable M : TYPE -> TYPE.
*)
Variable M : TYPE -> PO.

(** the carrier of the module as an inductive type *)

Inductive prod_mod_c (V : TYPE) : [nat] -> Type :=
  | TTT :  prod_mod_c V nil 
  | CONSTR : forall b bs, 
         M (V ** b)-> prod_mod_c V bs -> prod_mod_c V (b::bs) .

Lemma CONSTR_eq (V : TYPE) (b : nat) 
       (bs : [nat]) 
       (elem elem' : M (V ** b)) 
       (elems elems' : prod_mod_c V bs) :
        elem = elem' -> elems = elems' -> 
    CONSTR elem elems = CONSTR elem' elems'.
Proof.
  intros; subst; auto.
Qed.

Inductive prod_mod_c_rel (V : TYPE) : forall n, relation (prod_mod_c V n) :=
  | TTT_rel : forall x y : prod_mod_c V nil, prod_mod_c_rel x y 
  | CONSTR_rel : forall n l, forall x y : M (V ** n), 
          forall a b : prod_mod_c V l,
          x << y -> prod_mod_c_rel a b -> 
          prod_mod_c_rel (CONSTR x a) (CONSTR y b).

(*

Lemma prod_mod_nil_TTT : forall V (m : prod_mod_c V nil), m = TTT _ .
Proof.
*)

Program Instance prod_mod_c_rel_po_struct V n : 
    PO_obj_struct (prod_mod_c V n) := {Rel := @prod_mod_c_rel V n }.
Next Obligation.
Proof.
  intros.
  constructor.
  unfold Reflexive.
  induction x.
  constructor.
  constructor; auto. reflexivity.
  unfold Transitive.
  intros. 
  generalize dependent z.
  dependent induction H.
  intros.
  constructor.
  intros.
  dependent destruction H1.
  constructor.
  transitivity y; auto.
  apply IHprod_mod_c_rel.
  auto.
Qed.
Print Assumptions prod_mod_c_rel_po_struct.
 
Definition prod_mod_po V n : PO := Build_PO_obj (prod_mod_c_rel_po_struct V n).

End prod_mod_built_from_scratch_carrier.

(** if M is a module, then the product of fibres of derived M also is *)

Section prod_mod_carrier_is_mod.

Variable M : RModule P PO.

(** the product module mkleisli is defined by structural recursion *)

Fixpoint pm_mkl l V W (f : SM_po V ---> P W) 
      (X : prod_mod_po M V l) : prod_mod_po M W l :=
     match X in prod_mod_c _ _ l return prod_mod_c M W l with
     | TTT => TTT M W 
     | CONSTR b bs elem elems => 
            CONSTR (M:=M) (V:=W)
     (rmkleisli (RModule_struct := M) (lshift _ f)  elem)
      (pm_mkl f elems)
     end.

Program Instance pm_mkl_struct l V W (f : SM_po V ---> P W) :
 PO_mor_struct (pm_mkl (l:=l) f).
Next Obligation.
Proof.
  unfold Proper; red.
  simpl.
  intros.
  induction H.
  constructor.
  constructor. simpl.
  apply PO_mor_monotone.
  auto.
  apply IHprod_mod_c_rel.
Qed.

Definition pm_mkl_po l V W f := Build_PO_mor (pm_mkl_struct l V W f).

(** and enjoys the mkl properties *)

Ltac t x := induction x;
  simpl; opt; 
  cat; repeat
  match goal with 
 | [|-CONSTR _ _ = CONSTR _ _ ] => apply CONSTR_eq     
 | [b : _ |-_ ]=>
   try app (rmkl_eq (M));
   try rew (rmklmkl (M));
   try rew (rmkleta (M))
   end; repeat (cat || opt || rew kleisli_lshift).

Lemma pm_mkl_eq l V W (f g : SM_po V ---> P W) 
    (H : forall  x, f x = g x) (x : prod_mod_c M V l) : 
               pm_mkl f x = pm_mkl g x.
Proof.
  t x.
Qed.

Lemma pm_mkl_mkl l V (x : prod_mod_c M V l) W (f : SM_po V ---> P W)
 X (g : SM_po W ---> P X) :
  pm_mkl g (pm_mkl f x) = 
     pm_mkl (Sm_ind (fun (x0 : V) => rkleisli g (f x0))) x .
Proof.
  t x. 
Qed.

Lemma pm_mkl_weta l V (v : prod_mod_c M V l) :
         pm_mkl (rweta V) v = v.
Proof.
  t v; app (rmkleta_id_eq M); opt; rew lshift_weta'.
Qed.

Hint Rewrite pm_mkl_mkl pm_mkl_weta pm_mkl_eq : opt.
Hint Resolve pm_mkl_mkl pm_mkl_weta pm_mkl_eq : opt.

Obligation Tactic := unfold Proper; red; opt.

Program Instance pm_mkl_oid l V W : Proper 
 (A:= (SM_po V ---> P W) -> 
        (prod_mod_c M V l ---> prod_mod_c M W l))
   (equiv ==> equiv) (@pm_mkl l V W).
Next Obligation.
Proof.
  simpl in *.
  rewrite (pm_mkl_eq H).
  auto.
Qed.

Obligation Tactic := opt || apply pm_mkl_oid.

Program Instance prod_mod_struct l : RModule_struct (F:=SM_po) P (D:=PO) PO  
   (fun V => prod_mod_po M V l) := {
  rmkleisli := pm_mkl_po l }.
Next Obligation.
Proof.
  unfold Proper; red.
  simpl. intros.
  rewrite (pm_mkl_eq H).
  auto.
Qed.
Next Obligation.
Proof.
  app (pm_mkl_eq).
Qed.

Definition prod_mod l := Build_RModule (prod_mod_struct l).

End prod_mod_carrier_is_mod.


(** we are now ready to define what the representation of an arity is *)
(*
Notation "M [( s )]" := (ITFIB_MOD _ s M) (at level 60).
*)
Section arity_rep.


(*Variable P : Monad (ITYPE T).*)

Variable M : RModule P PO.

(** to each arity we associate a type of module morphisms *)

Definition modhom_from_arity (ar : [nat]) : Type :=
  RModule_Hom (prod_mod M ar) M.

End arity_rep.

End pow_and_product.

(** the type of representations associated to a signature *)

Section signature_rep.

Variable S : Signature.

Section rep_struct.

Variable P : RMonad SM_po.

(** a represention is - for each arity - a type of module morphisms *)

Definition Repr := forall i : sig_index S, 
     modhom_from_arity P (sig i).


End rep_struct.
 

Record Representation := {
  rep_monad :> RMonad SM_po ;
  repr : Repr rep_monad
}.


(** now we come to the MORPHISMS OF REPRESENTATIONS *)
(** they are more complicated than in a "strict theory" since we
    must insert isomorphisms where on paper we have equality of objects *)

(** the commutative diagrams we must have for a morphism of 
     representations *)

Section arrows.

Variables P Q : RMonad SM_po.
Variable f : RMonad_Hom P Q.



Notation "x >>- f" := (shift_not f x)(at level 60).
Notation "x >-- f" := (lshift _ f x)(at level 60).

Lemma lshift_monad_hom l V W (g : SM_po V ---> P W) (x : V ** l) :
    f _ (x >-- g) = x >-- (g ;; f _ ).
Proof.
  induction l; 
  repeat (opt || rew_all || apply lshift_eq || 
                  rew (shift_monad_hom)).
                  destruct x0; simpl.
  unfold rlift. rew (rmon_hom_rkl f).
  apply (rkl_eq Q). simpl. 
  intros. rew (rmon_hom_rweta f).
  rew (rmon_hom_rweta f).
Qed.

Hint Rewrite lshift_monad_hom : opt.

(** the lower left corner of the commutative diagram *)



Notation "'f*' M" := (PbRMOD f _ M) (at level 5).

(** the left morphism of the commutative diagram *)
(** at first its carrier *)

Fixpoint Prod_mor_c (l : [nat]) (V : TYPE) (X : prod_mod P l V) : 
                  f* (prod_mod Q l) V :=
  match X in prod_mod_c _ _ l 
  return f* (prod_mod Q l) V with
  | TTT => TTT _ _
  | CONSTR b bs elem elems => 
    CONSTR (f  _ elem) (Prod_mor_c elems)
  end.

Program Instance prod_mor_struct l V : PO_mor_struct (@Prod_mor_c l V).
Next Obligation.
Proof.
  unfold Proper; red.
  simpl.
  intros.
  induction H.
  constructor.
  constructor.
  apply PO_mor_monotone; auto.
  apply IHprod_mod_c_rel.
Qed.

Definition prod_mor_po l V := Build_PO_mor (prod_mor_struct l V).

Lemma prod_mod_c_kl (ar : [nat]) V (x : prod_mod_c P V ar):
forall (W : TYPE) (g : SM_po V ---> P W),
 Prod_mor_c (l:=ar) (V:=W) (pm_mkl (M:=P) (W:=W) g x) =
     pm_mkl (M:=Q) (W:=W) (Sm_ind (fun (x0 : V) => f W (g x0)))
             (Prod_mor_c (l:=ar) (V:=V) x).
Proof. 
  induction x; 
  repeat (opt || apply CONSTR_eq ||
          rew (rmonad_hom_rkl (RMonad_Hom_struct := f)) ||
          app (rkl_eq Q)).
  rew (lshift_monad_hom).
  apply lshift_eq.
  auto.
Qed.

Obligation Tactic := simpl; intros; rew prod_mod_c_kl.

(** the left morphism has a module morphism structure *)
Program Instance prod_mor_s l : RModule_Hom_struct 
   (M:=prod_mod P l) (N:=f* (prod_mod Q l))
       (prod_mor_po l).
Next Obligation.
  app pm_mkl_eq.
Qed.

Definition Prod_mor ar := Build_RModule_Hom (prod_mor_s ar).

(** definition of the diagram that we kindly ask to commute *)

(** at first for ONE arity *)

Variable a : [nat].
Variable RepP : modhom_from_arity P a.
Variable RepQ : modhom_from_arity Q a.

(** the left - lower side of the diagram *)

Notation "'f*' M" := (# (PbRMOD f _ ) M).

Definition commute_left :=
        Prod_mor a ;; f* RepQ . 
        (*ITPB_FIB f _ (*snd a*) _.*)

(** the right - upper side *)
Coercion PbRMod_ind_Hom : RMonad_Hom >-> mor.

(*Notation "'f'":= (PbMod_ind_Hom f).*)
(*
Notation "y [( s )]" := (#(ITFIB_MOD _ s) y) (at level 40).
*)

Definition commute_right := RepP ;;  PbRMod_ind_Hom f .

(** they are equal *)

Definition commute := commute_left == commute_right.


End arrows.

(** definition of "morphism of representations" *)

(*Variable Sig : Signature.*)
Variables P Q : Representation.  

(** a representation morphism should make commute something *)

Class Representation_Hom_struct (f : RMonad_Hom P Q) :=
   repr_hom_s : forall i : sig_index S,
            commute f (repr P i) (repr Q i).

Record Representation_Hom : Type := {
  repr_hom_c :> RMonad_Hom P Q;
  repr_hom :> Representation_Hom_struct repr_hom_c
}.

End signature_rep.


Existing Instance repr_hom.
Existing Instance pow_map_oid.

