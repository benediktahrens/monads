Require Import Coq.Program.Equality. (* for dependent induction *)

Require Export CatSem.CAT.cat_INDEXED_TYPE.
Require Export CatSem.CAT.initial_terminal.
Require Export CatSem.CAT.orders.
Require Export CatSem.CAT.monad_haskell.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

(** 
    i tried to make the following in a modular way, which means
    
    [ T -> PO_obj ] 
    [ fun A B => fun t => PO_mor (A t) (B t) ]

    like, to be easily generalizable to [T -> C] for any cat C
 
    and so on. consequence: no coercions as we'd like them
 
   modular programming rules, but not in coq

*)


Section ind_po_cat.

Variable T: Type. 


(** Category of a family of preorders indexed by T *)

Class ipo_obj_struct (A : T -> Type) := {
  IRel : forall t, relation (A t);
  IPOprf :> forall t, PreOrder (@IRel t)
}.

Notation "y <<< z" := (IRel y z) (at level 60).

Record ipo_obj := {
  ipo_obj_carrier :> T -> Type ;
  ipo_obj_s :> ipo_obj_struct ipo_obj_carrier
}.

Existing Instance ipo_obj_s.

Instance IRel_Trans (A : ipo_obj) t : Transitive (IRel (A:=A) (t:=t)).
Proof.
  intros;
  apply IPOprf.
Qed.

Lemma IRel_refl (V : ipo_obj) t (x : V t) : x <<< x.
Proof.
  reflexivity.
Qed.

Lemma IRel_eq (V : ipo_obj) t (x y : V t) : x = y -> x <<< y.
Proof.
  intros;
  subst;
  apply IRel_refl.
Qed.

Lemma IRel_eq_r (V : ipo_obj) t (x y z : V t) : 
    x <<< y -> y = z -> x <<< z.
Proof.
  intros;
  subst;
  auto.
Qed. 

Lemma IRel_eq_l (V : ipo_obj) t (x y z : V t) : 
    x <<< z -> x = y -> y <<< z.
Proof.
  intros; subst; auto.
Qed. 

Lemma IRel_trans (V : ipo_obj) t (x y z : V t) : 
       x <<< y -> y <<< z -> x <<< z.
Proof.
  intros;
  etransitivity; 
  eauto.
Qed.
 
Lemma IRel_trans_2 (V : ipo_obj) t (x y z : V t) : 
       x <<< z -> y <<< x -> y <<< z.
Proof.
  intros;
  etransitivity;
  eauto.
Qed.

Program Instance ipo_proj_struct (A:ipo_obj) (t:T) : 
    PO_obj_struct (A t) := {
  Rel := IRel (t:=t)
}.

Definition ipo_proj A t := Build_PO_obj (ipo_proj_struct A t).

Lemma proj_rel (A : ipo_obj) (t : T) (x y : A t) :
        x <<< y -> x << y.
Proof.
  auto.
Qed.

Lemma rel_proj (A : ipo_obj) (t : T) (x y : A t) :
       x << y -> x <<< y.
Proof.
  auto.
Qed.

Notation "'OB'" := ipo_obj (at level 70).

(*Definition ind_po_obj_car (X:OB) (t:T) := POCarrier (X t).

Coercion ind_po_obj_car : ind_po_obj >-> Funclass.
*)

Existing Instance ipo_obj_s.

Class ipo_mor_struct (a b: OB) (f: forall t, a t -> b t) := {
  ind_po_struct :> forall t, Proper (IRel (A:=a) (t:=t) ==> IRel (A:=b) (t:=t)) (f t)
}.

Record ipo_mor (a b: OB) := {
  ipo_mor_carrier :> forall t, a t -> b t;
  ipo_mor_s :> ipo_mor_struct ipo_mor_carrier
}.

Notation "'MOR'" := ipo_mor (at level 70).

Lemma IPO_mor_monotone (a b : ipo_obj)(f : ipo_mor a b):
   forall t x y, x <<< y -> f t x <<< f t y.
Proof.
  intros a b f t x y;
  apply f.
Qed.

Hint Resolve IPO_mor_monotone.

Program Instance ipo_comp_s (a b c: OB) (f: MOR a b)
         (g: MOR b c) : ipo_mor_struct (fun t z => g t (f t z)).
Next Obligation.
Proof.
  unfold Proper; red;
  intros; auto.
Qed.

Definition ipo_comp a b c f g := Build_ipo_mor (ipo_comp_s a b c f g).
  

Program Definition ind_po_id (a : OB) : MOR a a :=
        Build_ipo_mor (ipo_mor_carrier := 
                             fun t z => z) _ .
Next Obligation.
Proof.
  constructor; intros;
  unfold Proper; red;
  auto.
Qed.


Lemma eq_ind_setoid (a b: OB) : 
   Equivalence (fun f g: MOR a b => forall t z, f t z = g t z).
Proof. 
  intros; constructor;
  unfold Reflexive,
     Symmetric,
     Transitive; 
  intros;
  try etransitivity; auto. 
Qed.

Definition ind_po_oid (a b: OB) := 
            Build_Setoid (eq_ind_setoid a b).

Obligation Tactic := cat;
   try (match goal with | [ |- Proper _ _ ] => 
             unfold Proper; do 2 red end) ;
   cat; repeat rew_hyp_2; cat.

Program Instance IPO_struct : Cat_struct ipo_mor := {
  mor_oid := ind_po_oid;
  comp := ipo_comp;
  id := ind_po_id
}.
    
Canonical Structure IPO := Build_Cat IPO_struct.

Inductive smallest_irel (V : ITYPE T) : forall t, relation (V t) :=
  | t_eq : forall t (x : V t), smallest_irel x x.

Program Instance sm_ipo_struct (V : ITYPE T) : ipo_obj_struct V := {
  IRel := smallest_irel (V:=V)
}.
Next Obligation.
Proof.
  constructor;
  intros; simpl;
  unfold Transitive;
  intros;
  try (match goal with [ H : smallest_irel _ _ |- _ ] => 
       destruct H end);
  try constructor;
  auto.
Qed.

Canonical Structure sm_ipo (V : ITYPE T) : IPO := 
      Build_ipo_obj (sm_ipo_struct V).

Ltac elim_sm := match goal with
   | [ H : @IRel (ipo_obj_carrier (sm_ipo _)) 
                 (ipo_obj_s (sm_ipo _)) _ _ _  |- _ ] => destruct H
| [ H : _ <<< _  |- _ ] => destruct H
                end.

Lemma sm_irel_eq (V : ITYPE T) t (x y : sm_ipo V t) :
     x <<< y -> x = y.
Proof.
 intros;
   elim_sm;
  auto.
Qed.

Section sm_ipo_mor.

Variables V W : ITYPE T.
Variable f : V ---> W.

Obligation Tactic := intros;
  unfold Proper; red; intros; elim_sm; constructor.

Program Instance sm_ipo_mor_s : 
  ipo_mor_struct (a:=sm_ipo V) (b:=sm_ipo W) f.

Canonical Structure sm_ipo_mor : sm_ipo V ---> sm_ipo W := 
        Build_ipo_mor sm_ipo_mor_s.

End sm_ipo_mor.

Obligation Tactic := cat;
   try (match goal with | [ |- Proper _ _ ] => 
             unfold Proper; red end) ;
   cat; repeat rew_hyp_2; cat.

Program Instance SM_ipo_s : Functor_struct sm_ipo_mor.

Definition IDelta := Build_Functor SM_ipo_s.
(*Definition SM_ipo := Build_Functor SM_ipo_s.*)
(*Definition IDelta := SM_ipo.*)

Section SM_ind.

Variable V : ITYPE T.
Variable W : IPO.

Variable f : forall t, V t -> W t.

Obligation Tactic := idtac.

Program Instance SM_ind_s : ipo_mor_struct 
  (a:=IDelta V) (b:=W) f.
Next Obligation.
Proof.
  intros;
  try (match goal with | [ |- Proper _ _ ] => 
             unfold Proper; red end);
  intros;
  match goal with [H : IRel _  _|- _ ] => destruct H end;
  reflexivity.
Qed.

Canonical Structure SM_ind := Build_ipo_mor SM_ind_s.

End SM_ind.


Notation "'IP'":= IPO.

Section proj.

Section hom.

Variable t: T.
Variables a b : OB.
Variable f : MOR a b.
(*
Definition ipo_proj_mor_car: ipo_proj a t -> ipo_proj b t :=
             f t .
*)
Program Definition ipo_mor_proj := 
    Build_PO_mor (a:=ipo_proj a t) (b:=ipo_proj b t)
        (PO_fun := f t) _ .
Next Obligation.
Proof.
  constructor.
  unfold Proper; red.
  simpl.
  intros; apply f.
  auto.
Qed.
  
End hom.

Program Instance IP_proj_Func (t:T) : 
     Functor_struct (C:=IP) (D:=Ord)(*Fobj:= fun a => ipo_proj a t*) 
                        (ipo_mor_proj t).
  
Canonical Structure IP_proj t := Build_Functor (IP_proj_Func t).
End proj.

(** Forgetful functor [(T -> PO) -> (T -> Set)] *)
Section forget.

(** if i give Fobj as implicit argument, i will have a BAD
   eta expansion which breaks the NT in po_monads *)

Program Instance OIP_struct : Functor_struct (C:=IPO) (D:= ITYPE T) 
  (*Fobj := fun V => fun t => V t*)
  (fun V W => fun f => f). 

Definition OIP := Build_Functor OIP_struct.

End forget.

(** Category IP has initial and terminal object *)

Section IND_PO_init_term.

Program Instance IP_term_struct : ipo_obj_struct (fun t => unit) := {
  IRel t := fun _ _ => True
}.
Next Obligation.
Proof.
  constructor; 
  auto.
Qed.

Definition IP_term := Build_ipo_obj IP_term_struct.

Program Instance IP_term_mor_struct (a: OB) : 
     ipo_mor_struct (a:=a)(b:=IP_term)(fun _ _ => tt).

Definition IP_term_mor (a:OB) := Build_ipo_mor (IP_term_mor_struct a).

Hint Extern 3 (?a = ?b) => try destruct a.

Program Instance IP_Terminal : Terminal IP := {
  Term :=  IP_term;
  TermMor := IP_term_mor
}.

Program Instance IP_init_struct : ipo_obj_struct (fun t => TEMPTY) := {
  IRel t := fun _ _ => True
}.
Next Obligation.
Proof.
  constructor; 
  auto.
Qed.

Definition IP_init := Build_ipo_obj IP_init_struct.

Obligation Tactic := intros;
  unfold Proper; red; cat;
  repeat (match goal with
  [ H : TEMPTY |- _ ] => elim H end); cat.

Program Instance IP_init_mor_struct (a : OB) :
   ipo_mor_struct 
     (a:=IP_init)
     (b:=a)
     (fun t => InitMor (C:=TYPE) (a t)). 

Definition IP_init_mor (a:OB) := Build_ipo_mor (IP_init_mor_struct a).

Program Instance IP_Initial : Initial IP := {
  Init := IP_init;
  InitMor := IP_init_mor
}.

End IND_PO_init_term.


(** Adding a distinct element of type (T u) 
      to a family of preorders A *)
Global Arguments some [ _] _ [_ _] _.
Inductive optrelT (u:T) (V: IP) : 
  forall t,relation (opt u V t):=
  | optrelTP_none :  optrelT (none u V) (none u V)
  | optrelTP_some : forall t (y z:V t), IRel (A:=V) (ipo_obj_struct := ipo_obj_s V) y  z -> 
          optrelT (some u y) (some u z).


Program Instance opt_TP_preorder (u:T)(A:IP): 
     ipo_obj_struct (opt u A) := {
 IRel := @optrelT u A
}.
Next Obligation.
Proof.
  intros;
  constructor;
  unfold Reflexive, Transitive.
  intro z; induction z;
  constructor. apply IPOprf.
  
  intros r y z H. generalize dependent z.
  elim H.
  intros z Hz. 
  dependent induction Hz. 
  constructor.
  
  intros t0 x0 y0 H0 z H1.
  generalize dependent x0.
  dependent destruction H1. (* worked with dependent induction in 8.3rc1 *)
  intros.
  constructor.
  transitivity y0; auto.
Qed.

Canonical Structure opt_TP u A := Build_ipo_obj (opt_TP_preorder u A).

Notation "V *" := (opt_TP _ V) (at level 5).


(** injection Some_TP is a morphism of preorders *)
Obligation Tactic := unfold Proper; red; 
                       constructor; auto.

Program Instance Some_TP_POs (u:T) (A:IP) :  ipo_mor_struct (a:=A)(b:=opt_TP _ A)  (@some _ u _ ).

Canonical Structure Some_TP_PO (u:T) (A:IP): A ---> A* := 
  Build_ipo_mor (Some_TP_POs u A).

(** opt_TP is a monad
     - return := Some_TP
     - bind f := default f None_TP 
   this would give us a functor again *)


Program Definition opt_TP_weta (u:T)(V:IP) : V ---> V* := 
   Build_ipo_mor (ipo_mor_carrier := @some _ u V) _.

Obligation Tactic := idtac.
  
Program Definition opt_TP_kl (u:T) (V W : OB)
              (f: V ---> W*) : V* ---> W* :=
   Build_ipo_mor (ipo_mor_carrier := @opt_kl _ u V W f) _.
Next Obligation.
Proof. 
  constructor.
  unfold Proper; 
  repeat red; intros.
  induction H; simpl.
  constructor.
  apply f; auto.
Qed.

Canonical Structure opt_TP_kl.

Obligation Tactic := repeat red; cat; elim_opt.

Program Instance opt_TP_monad_struct (u:T) : 
   Monad_struct (fun V => opt_TP u V) := {
  weta V := opt_TP_weta u V;
  kleisli V W f := opt_TP_kl (u:=u)  f
}.

Canonical Structure opt_TP_monad (u:T):= 
     Build_Monad (opt_TP_monad_struct u).

Section opt_TP_opt_T.

Lemma TP_T_kl: forall u (V W:IP) (f:V ---> W*) (t:T) z,
   kleisli (Monad_struct:= (opt_TP_monad u)) f z = 
         kleisli (Monad_struct:= (opt_monad u)) f z.
Proof.
  intros; simpl; auto.
Qed.

Lemma TP_T_weta: forall u (V:IP) (t:T) (z:V t),
   weta (Monad_struct:= (opt_TP_monad u)) V t z = 
   (weta (Monad_struct:= (opt_monad u))) V t z.
Proof.
  intros; simpl; auto.
Qed.

End opt_TP_opt_T.


(** Derived Module *)

Section PostComp_w_Monad.

(** default *)

Program Definition opt_TP_default (u:T) (V W : IP)
      (f: V ---> W) (w:W u): V* ---> W := 
  Build_ipo_mor (ipo_mor_carrier := @opt_default _ u V W f w) _ .
Next Obligation.
Proof.
  constructor.
  unfold Proper;  red.
  intros t q y H; 
  induction H; simpl.
  apply IPOprf.
  apply f.
  auto.
Qed.

Canonical Structure opt_TP_default.
(** Monad P, we define 
     - var_inj V : V ---> P V*
     - def_var_inj (f: V ---> P W) -> V* ---> P W*
*) 

Variable P : Monad IPO.

Existing Instance IPO_struct.

Definition opt_TP_def_varinj (u:T) (V W: IP) (f:V ---> P W) : 
          opt_TP u V ---> P (opt_TP u W):=
 (opt_TP_default (u:=u) (V:=V) (W:=P (opt_TP u W))
 (f ;; lift (weta (Monad_struct := (opt_TP_monad u)) W))
 (weta (Monad_struct := P) (opt_TP u W) u (none u W))).

(** needed for module property of the derivative *)

Ltac t := simpl; intros; elim_opt; rew (lift_weta P).

Lemma opt_TP_def_varinj_weta (u:T)(V:IP) :
      opt_TP_def_varinj u (weta V) == weta _.
Proof. t.
Qed.
 
Lemma opt_TP_def_varinj_weta_f (u:T) (V V':IP) (f: V' ---> V) : 
     opt_TP_def_varinj u (f ;; weta V) == 
         lift (M :=opt_TP_monad u) f ;; weta _ .
Proof. t.
Qed.

End PostComp_w_Monad.

Section substitution.

Variable R: Monad IP.

Section subst_kleisli_arg.

Variable V: IP.
Variable r: T.
Variable W : R V r.

Definition IPsubst_map := opt_TP_default (weta (Monad_struct:=R) _ ) W.

End subst_kleisli_arg.

Definition IPsubstar (r:T) (V:IP) (W:R V r) := kleisli (IPsubst_map W).

End substitution.

End ind_po_cat.

Notation "x <<< y" := (IRel x y) (at level 60).

Existing Instance IP_Initial.
Existing Instance IP_Terminal.
Existing Instance IPO_struct.
Existing Instance ipo_obj_s.
Existing Instance ipo_mor_s.
Existing Instance IPOprf.
