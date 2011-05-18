Require Export Coq.Lists.List.

Require Export CatSem.CAT.monad_h_module.
Require Export CatSem.CAT.cat_INDEXED_TYPE.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Ltac app_any := match goal with [H:_|-_] => app H end.

Section arities.

Notation "[ T ]" := (list T) (at level 5).

Ltac opt := simpl in *; intros; 
  autorewrite with opt; auto with opt.

Variable T : Type.

(** definition of a signature *)

Record Signature_t (t : T) : Type := {
  sig_index : Type ;
  sig : sig_index -> [[T] * T]
}.

Definition Signature := forall t, Signature_t t.


(** given a list of types, we add successively a variable of 
    that type to a set of indexed variables *)
Notation "V * u" := (opt u V).
Notation "^ f" := (lift (M:= opt_monad _) f) (at level 5).


Fixpoint pow (l : [T]) (V : ITYPE T) : ITYPE T :=
  match l with
  | nil => V
  | b::bs => pow bs (V * b)
  end.

Notation "V ** l" := (pow l V) (at level 10).

(** adding variables is functorial *)

Fixpoint pow_map (l : [T]) V W (f : V ---> W) :
         V ** l ---> W ** l :=
  match l return V ** l ---> W ** l with
  | nil => f
  | b::bs => pow_map (^ f)
  end.

(*Notation "V ' u" := (opt_T u V) (at level 10).*)
Notation "f ^^ l" := (pow_map (l:=l) f) (at level 10).
(*Notation "^ f" := (lift (M:= opt_T_monad _) f) (at level 5).*)

Lemma lift_opt_monad u (V W : ITYPE T) (f g : V ---> W)
     (H : forall t x, f t x = g t x) : 
     forall t x, lift (M:=opt_monad u) f t x = ^g t x.
Proof.
  intros;
  apply (lift_eq (opt_monad _));
  auto.
Qed.

(** this thing works cuz of the strange semantics of the
    Ltac match *)

Lemma pow_map_eq l (V W : ITYPE T) (f g : V ---> W) 
     (H : forall t (x : V t) , f t x = g _ x) : 
   forall t x, f ^^ l t x = g ^^ l t x.
Proof.
  induction l; 
  repeat (cat || app_any ||
    app lift_opt_monad).
Qed.

Hint Rewrite pow_map_eq : opt.
Hint Resolve pow_map_eq : opt.

Obligation Tactic := intros; do 2 red; opt.

Program Instance pow_map_oid V W (l : [T]) : 
    Proper (equiv ==> equiv) (pow_map (V:=V) (W:=W) (l:=l)).

Lemma pow_id (l : [T]) (a : ITYPE T) : (id a) ^^ l == id (a ** l).
Proof.
  induction l;
  repeat (cat || rewrite (pow_map_eq (g:=fun t x => x)) ||
           app_any ||
          elim_opt; auto).
Qed.

Lemma pow_eq_id l (a : ITYPE T) f : f == id a -> f ^^ l == id _ .
Proof.
   intros;
   repeat (rew_all || auto using pow_id).
Qed.

Lemma pow_comp (l : [T]) (a b c : ITYPE T) (f : a ---> b) (g : b ---> c):
(f;; g) ^^ l == f ^^ l;; g ^^ l.
Proof.
  induction l;
  repeat (cat || 
    match goal with 
       [l: list T,a : T |- _ = ^?g ^^  _ _ (^?f ^^ _  _ _ )] => 
          rew (pow_map_eq (l:=l)(f:= ^(f ;; g)) 
               (g:=^f ;; lift (M:=opt_monad a) g)) end ||
          rew_all || 
    match goal with [a:T |- _ ] => rew (lift_lift (opt_monad a)) end).
Qed.

(** multiple adding of variables is a functor BLOWUP *)
Obligation Tactic := auto using pow_id, pow_comp.

Program Instance POW_struct (l : [T]) : Functor_struct (@pow_map l).

Canonical Structure POW l := Build_Functor (POW_struct l).

(** now some functions to blow up under monads and modules *)

Section pow_and_product.

Variable P : Monad (ITYPE T).

Notation "'Var' x" := (weta (Monad_struct := P) _ _ x) (at level 55).
Notation "x >>= f" := (kleisli (Monad_struct := P) f _ x) (at level 65).

Hint Resolve (shift_eq (P:=P)) (shift_weta P) 
             (shift_weta_f P) f_equal : opt.
Hint Rewrite (shift_eq (P:=P)) (shift_weta P) 
             (shift_weta_f P) : opt.


(** lshift is SHIFTING wrt to a list of added variables 

     it enjoys the same properties as its little brother shift

*)

Fixpoint lshift (l : [T]) (V W: ITYPE T) (f:V ---> P W) : 
         V ** l ---> P (W ** l) :=
    match l return V ** l ---> P (W ** l) with
    | nil => f
    | b::bs => lshift (shift f)
    end.

Notation "x >>- f" := (lshift f x)(at level 60).

Lemma lshift_eq l V W (f g : V ---> P W) 
     (H : forall t x, f t x = g t x):
    forall t (x : V ** l t),
     x >>- f = x >>- g.
Proof.
  induction l; opt.
Qed.

Hint Resolve lshift_eq : opt.
Hint Rewrite lshift_eq : opt.

Ltac t l := induction l;
 repeat (cat || 
         match goal with [H:_|-_] => rewrite <- H end ||
         apply lshift_eq || opt).

Lemma lshift_weta (l : [T]) V t (x : V ** l t) :
      x >>- (weta _) = Var x.
Proof.
  t l.
Qed.

Hint Resolve lshift_weta : opt.
Hint Rewrite lshift_weta : opt.

Lemma lshift_weta' l V :
    lshift (l:=l) (weta (Monad_struct := P)V) == weta _ .
Proof.
  opt.
Qed.

Lemma lshift_weta_f (l : [T]) V W (f : V ---> W) t x:
   x >>- (f ;; weta W) = Var (f ^^ l t x).
Proof.
  t l.
Qed.

Lemma kleisli_lshift (l : [T]) V W (f : V ---> P W)
         X (g : W ---> P X) (t : T) (x : (V ** l) t) :
   (x >>- f) >>= (lshift g) = x >>- (fun s y => f s y >>= g).
Proof.
  induction l; 
  repeat (rew_all || apply lshift_eq || rew shift_kl || opt).
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
Variable M : MOD P D.

(** the carrier of the often derived module *)

Definition der_mod_c (l : [T]) (V : ITYPE T) : D := M (V ** l).

(** is needed in the proofs of mkl_mkl and mkl_weta,
    so we do it before *)

(* the often derived module is a module *)

Lemma der_mod_etakl c l: 
  mkleisli (d:=c ** l) (lshift (l:=l) (V:=c) (W:=c) (weta c)) ==
     id (der_mod_c l c).
Proof.
  intros; rewrite lshift_weta'; mod.
Qed.

Hint Rewrite der_mod_etakl : opt.

Obligation Tactic := opt;
  repeat (unf_Proper || 
          match goal with [|-mkleisli ?a ;; mkleisli ?b == _ ] =>
             rew (mklmkl M a b) end || 
          apply (mkl_eq M) || apply lshift_eq  || 
          rewrite kleisli_lshift || opt); mod.

Program Instance der_mod_struct (l : [T]) : 
        Module_struct P (der_mod_c l):= {
 mkleisli V W f:= mkleisli (Module_struct := M) (lshift (l:=l) f)
}.

Definition D_mod (l : [T]) := Build_Module (der_mod_struct l).

End many_derivs.

(** now for 
      - M a module
      - l an arity 
   we build the product of fibres of derived modules of M wrt to l 

  morally this product module carries the arguments of the constructors
*)


Section prod_mod_built_from_scratch_carrier.

Variable M : ITYPE T -> ITYPE T.

(** the carrier of the module as an inductive type *)

Inductive prod_mod_c (V : ITYPE T) : [[T] * T] -> Type :=
  | TTT :  prod_mod_c V nil 
  | CONSTR : forall b bs, 
         M (V ** (fst b)) (snd b) -> prod_mod_c V bs   ->
             prod_mod_c V (b::bs) .

Lemma CONSTR_eq (V : ITYPE T) (b : [T] * T) 
       (bs : [[T] * T]) 
       (elem elem' : M (V ** (fst b)) (snd b)) 
       (elems elems' : prod_mod_c V bs) :
        elem = elem' -> elems = elems' -> 
    CONSTR elem elems = CONSTR elem' elems'.
Proof.
  intros; subst; auto.
Qed.

End prod_mod_built_from_scratch_carrier.

(** if M is a module, then the product of fibres of derived M also is *)

Section prod_mod_carrier_is_mod.

Variable M : Module P (ITYPE T).

(** the product module mkleisli is defined by structural recursion *)

Fixpoint pm_mkl l V W (f : V ---> P W) 
      (X : prod_mod_c M V l) : prod_mod_c M W l :=
     match X in prod_mod_c _ _ l return prod_mod_c M W l with
     | TTT => TTT M W 
     | CONSTR b bs elem elems => 
            CONSTR (M:=M) (V:=W)
     (mkleisli (Module_struct := M) (lshift f) (snd b) elem)
      (pm_mkl f elems)
     end.

(** and enjoys the mkl properties *)

Ltac t x := induction x;
  simpl; intros; auto;
  cat; repeat
  match goal with 
 | [|-CONSTR _ _ = CONSTR _ _ ] => apply CONSTR_eq     
 | [b : prod _  _ |-_ ]=>
   try app (mkl_eq (der_mod_struct M (fst b)));
   try app (mklmkl (der_mod_struct M (fst b)));
   try rew (mkl_weta (Module_struct := der_mod_struct M (fst b)))
   end; cat.

Lemma pm_mkl_eq l V W (f g : V ---> P W) 
    (H : forall t x, f t x = g t x) (x : prod_mod_c M V l) : 
               pm_mkl f x = pm_mkl g x.
Proof.
  t x.
Qed.

Lemma pm_mkl_mkl l V (x : prod_mod_c M V l) W (f : V ---> P W)
 X (g : W ---> P X) :
  pm_mkl g (pm_mkl f x) = 
     pm_mkl (fun (t : T) (x0 : V t) => kleisli g t (f t x0)) x .
Proof.
  t x.
Qed.

Lemma pm_mkl_weta l V (v : prod_mod_c M V l) :
         pm_mkl (weta V) v = v.
Proof.
  t v.
Qed.

Hint Rewrite pm_mkl_mkl pm_mkl_weta pm_mkl_eq : opt.
Hint Resolve pm_mkl_mkl pm_mkl_weta pm_mkl_eq : opt.

Obligation Tactic := unfold Proper; red; opt.

Program Instance pm_mkl_oid l V W : Proper 
 (A:= (V ---> P W) -> 
        (prod_mod_c M V l ---> prod_mod_c M W l))
   (equiv ==> equiv) (@pm_mkl l V W).
 

Program Instance prod_mod_struct l : Module_struct P (D:=TYPE)
   (fun V => prod_mod_c M V l) := {
  mkleisli := pm_mkl (l:=l)
}.

Definition prod_mod l := Build_Module (prod_mod_struct l).

End prod_mod_carrier_is_mod.


(** we are now ready to define what the representation of an arity is *)

Notation "M [( s )]" := (ITFIB_MOD _ s M) (at level 60).

Section arity_rep.


(*Variable P : Monad (ITYPE T).*)

Variable M : Module P (ITYPE T).

(** to each arity we associate a type of module morphisms *)

Definition modhom_from_arity (ar : [[T] * T] * T) : Type :=
  Module_Hom (prod_mod M (fst ar)) (M [(snd ar)]).

End arity_rep.

End pow_and_product.

(** the type of representations associated to a signature *)

Section signature_rep.

Variable S : Signature.

Section rep_struct.

Variable P : Monad (ITYPE T).

(** a represention is - for each arity - a type of module morphisms *)

Definition Repr_t (t : T) :=
  forall i : sig_index (S t), 
     modhom_from_arity P ((sig i),t).

Definition Repr := forall t, Repr_t t.

End rep_struct.
 

Record Representation := {
  rep_monad :> Monad (ITYPE T);
  repr : Repr rep_monad
}.


(** now we come to the MORPHISMS OF REPRESENTATIONS *)
(** they are more complicated than in a "strict theory" since we
    must insert isomorphisms where on paper we have equality of objects *)

(** the commutative diagrams we must have for a morphism of 
     representations *)

Section arrows.

Variables P Q : Monad (ITYPE T).
Variable f : Monad_Hom P Q.

Notation "x >>- f" := (shift f x)(at level 60).
Notation "x >-- f" := (lshift f x)(at level 60).

Lemma lshift_monad_hom l V W (g : V ---> P W) t (x : V ** l t) :
    f _ t (x >-- g) = x >-- (g ;; f _ ).
Proof.
  induction l; 
  repeat (opt || rew_all || apply lshift_eq || 
                  rew (shift_monad_hom)).
Qed.

Hint Rewrite lshift_monad_hom : opt.

(** the lower left corner of the commutative diagram *)

Notation "'f*' M" := (PB_MOD f _ M) (at level 5).

(** the left morphism of the commutative diagram *)
(** at first its carrier *)

Fixpoint Prod_mor_c (l : [[T] * T]) 
  (V : ITYPE T) (X : prod_mod P l V) : 
                  f* (prod_mod Q l) V :=
  match X in prod_mod_c _ _ l 
  return f* (prod_mod Q l) V with
  | TTT => TTT _ _ 
  | CONSTR b bs elem elems => 
    CONSTR (f _ _ elem) (Prod_mor_c elems)
  end.


Lemma prod_mod_c_kl (ar : [[T] * T]) V
 (x : prod_mod_c P V ar):
forall (W : ITYPE T) (g : V ---> P W),
Prod_mor_c (l:=ar) (V:=W) (pm_mkl (M:=P) (W:=W) g x) =
pm_mkl (M:=Q) (W:=W) (fun (t : T) (x0 : V t) => f W t (g t x0))
  (Prod_mor_c (l:=ar) (V:=V) x).
Proof.
  induction x; 
  repeat (opt || apply CONSTR_eq ||
          rew (monad_hom_kl (Monad_Hom_struct := f)) ||
          app (kl_eq Q)).
Qed.

Obligation Tactic := simpl; intros; rew prod_mod_c_kl.

(** the left morphism has a module morphism structure *)
Program Instance prod_mor_s l :
       Module_Hom_struct (S:=prod_mod P l)
                         (T:=f* (prod_mod Q l))
       (Prod_mor_c (l:=l)).

Definition Prod_mor ar :=
         Build_Module_Hom (prod_mor_s ar).

(** definition of the diagram that we kindly ask to commute *)

(** at first for ONE arity *)

Variable a : [[T] * T] * T.
Variable RepP : modhom_from_arity P a.
Variable RepQ : modhom_from_arity Q a.

(** the left - lower side of the diagram *)

Notation "'f*' M" := (# (PB_MOD f _ ) M).

Definition commute_left :=
        Prod_mor (fst a) ;; 
        f* RepQ ;; 
        ITPB_FIB f _ (*snd a*) _.

(** the right - upper side *)
Coercion PbMod_ind_Hom : Monad_Hom >-> mor.

(*Notation "'f'":= (PbMod_ind_Hom f).*)
Notation "y [( s )]" := (#(ITFIB_MOD _ s) y) (at level 40).

Definition commute_right := 
      RepP ;;  f [(snd a)].

(** they are equal *)

Definition commute := commute_left == commute_right.


End arrows.

(** definition of "morphism of representations" *)

(*Variable Sig : Signature.*)
Variables P Q : Representation.  

(** a representation morphism should make commute something *)

Class Representation_Hom_struct (f : Monad_Hom P Q) :=
   repr_hom_s : forall t (i : sig_index (S t)),
            commute f (repr P i) (repr Q i).

Record Representation_Hom : Type := {
  repr_hom_c :> Monad_Hom P Q;
  repr_hom :> Representation_Hom_struct repr_hom_c
}.

End signature_rep.

End arities.

Existing Instance repr_hom.
Existing Instance pow_map_oid.





