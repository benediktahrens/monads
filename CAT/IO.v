Require Import Coq.Program.Equality. (* for dependent induction *)

Require Export CatSem.CAT.orders.
Require Export CatSem.CAT.cat_INDEXED_TYPE.
(*Require Export subcategories.*)
Require Export CatSem.CAT.SO.
Require Export CatSem.CAT.initial_terminal.
Require Export CatSem.CAT.monad_haskell.
Require Export CatSem.CAT.monad_h_module.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Automatic Introduction.

Section base_cats.

Variable T : Type.

Class io_struct (A : T -> Type) := {
  IRel : forall t, relation (A t);
  IPOprf :> forall t, PreOrder (@IRel t)
}.


Notation "y <<< z" := (IRel y z) (at level 60).

Record io_obj := {
  ipo_obj_carrier :> T -> Type ;
  ipo_obj_s :> io_struct ipo_obj_carrier
}.

Existing Instance ipo_obj_s.

Instance IRel_Trans (A : io_obj) t : Transitive (IRel (A:=A) (t:=t)).
Proof.
  intros. 
  apply IPOprf.
Qed.

Lemma IRel_refl (V : io_obj) t (x : V t) : x <<< x.
Proof.
  intros V t x.
  assert (H:=IPOprf (A:= V) t).
  destruct H.
  apply PreOrder_Reflexive.
Qed.
 
Lemma IRel_trans (V : io_obj) t (x y z : V t) : 
       x <<< y -> y <<< z -> x <<< z.
Proof.
  intros V t x y z.
  assert (H:=IPOprf (A:= V) t).
  destruct H.
  apply PreOrder_Transitive.
Qed.
 

(*Definition io_smap (a b : io_obj) := forall t, a t -> b t.*)

(*
Definition io_map (a b : io_obj) 
     (f : io_smap a b) := 
      forall t, Proper (IRel (t:=t) ==> IRel (t:=t)) (f t).
*)

Lemma smap_equiv (A B: io_obj) : 
     Equivalence (A:= forall t, A t -> B t)
          (fun p q => forall t:T, forall x: A t, p t x = q t x).
Proof. 
  intros A B; 
  constructor; 
  unfold Reflexive,Symmetric,Transitive;
  intros; simpl; try etransitivity; auto. 
Qed.

Definition smap_oid A B := 
         Build_Setoid (smap_equiv A B).

Ltac t := cat; unf_Proper ; 
     mauto; repeat rew_all; mauto.

Obligation Tactic := t.

Program Instance IO_SMAP_s : Cat_struct (fun a b : io_obj => 
     forall t, a t -> b t) := {
  mor_oid := smap_oid;
  comp A B C f g := fun t => fun x => g t (f t x);
  id A := fun t x => x
}.

Definition IO := Build_Cat IO_SMAP_s.

(*Notation "'IP'" := IO_SMAP (at level 4).*)


Class iMonotone (a b : IO) 
     (f : a ---> b) := 
  imonotone : forall t, Proper (IRel (t:=t) ==> IRel (t:=t)) (f t).

Obligation Tactic := unfold iMonotone; unfold Proper, respectful; t.

Program Instance IO_MAP_SubCat : SubCat_compat IO
      (fun x => True) (fun a b f => iMonotone f).

Definition IO_MAP := SubCat IO_MAP_SubCat.
(*
Inductive opt_T (u : T) (A : ITYPE) : (ITYPE) :=
| Some_T : forall (t : T), (A t) -> opt_T u A t
| None_T : opt_T u A u.
 *)
 
Global Arguments some [ _] _ [_ _] _.
Global Arguments none [ _]  _ _.
Inductive optrelT (u:T) (V: IO) : 
  forall t,relation (opt u V t):=
  | optrelTP_none :  optrelT (none u V) (none u V)
  | optrelTP_some : forall t (y z:V t), y <<< z -> 
          optrelT (some u y) (some u z).

Obligation Tactic := idtac.

Program Instance opt_TP_preorder (u:T)(A:IO): 
     io_struct (opt u A) := {
 IRel := @optrelT u A
}.
Next Obligation.
Proof.
  intros.
  constructor;
  unfold Reflexive, Transitive.
  intro z; induction z;
  constructor. apply IPOprf.
  
  intros r y z H. generalize dependent z.
  induction H.
  intros z Hz. 
  induction Hz.
  constructor.
  constructor. auto.
  
  intros x H'.
  generalize dependent y.
  dependent destruction H'. (* dep ind in 8.3rc1 *)
  intros y H'.
  constructor.
  transitivity z;
  auto.
Qed.

Definition opt_TP u A : IO := Build_io_obj (opt_TP_preorder u A).

Notation "V *" := (opt_TP _ V) (at level 5).

Section IND_PO_init_term.

Program Instance IO_SMAP_term_struct : io_struct (fun t => unit) := {
  IRel t := fun _ _ => True
}.
Next Obligation.
Proof.
  constructor; 
  auto.
Qed.

Definition IO_SMAP_term := Build_io_obj IO_SMAP_term_struct.

Definition IO_SMAP_term_mor (a: IO) : a ---> IO_SMAP_term :=
              (fun _ _ => tt).

Instance IO_SMAP_term_mor_monotone a : 
    iMonotone (a:=a) (b:= IO_SMAP_term) (@IO_SMAP_term_mor a).
Proof.
  unfold iMonotone.
  simpl;
  intros a.
  unfold Proper; red.
  auto.
Qed.


(*
Program Instance IP_Terminal : Terminal IP := {
  Term :=  IP_term;
  TermMor := IP_term_mor
}.
Next Obligation.
Proof.
  elim (f t z). 
  auto. 
Qed.


Program Instance IP_init_struct : ipo_obj_struct (fun t => TEMPTY) := {
  IRel t := fun _ _ => True
}.
Next Obligation.
Proof.
  constructor; 
  auto.
Qed.

Definition IP_init := Build_ipo_obj IP_init_struct.

Program Instance IP_init_mor_struct (a: OB) : 
     ipo_mor_struct (a:=IP_init)(b:=a)(fun t => InitMor (a t)).
Next Obligation.
Proof.
  unfold Proper; red.
  intro z; elim z.
Qed.

Definition IP_init_mor (a:OB) := Build_ipo_mor (IP_init_mor_struct a).

Program Instance IP_Initial : Initial IP := {
  Init := IP_init;
  InitMor := IP_init_mor
}.
Next Obligation.
Proof.
  elim z.
Qed.
*)
End IND_PO_init_term.

Definition Some_TP (u : T) (A : IO) : A ---> A* :=
           (@some _ u _).

Instance Some_TP_monotone (u:T) (A:IO): 
     iMonotone (a:=A) (b:= A*) (@Some_TP u A) .
Proof.
  unfold iMonotone.
  intros.
  unfold Proper; 
  red. 
  constructor. 
  auto. 
Qed.

Definition opt_TP_default (u:T) (V W : IO)
      (f: V ---> W) (w:W u): V* ---> W := @opt_default _ u V W f w.
 

Instance opt_TP_default_monotone (u:T) (V W : IO)
      (f: V ---> W) (H' : iMonotone f) (w:W u) :
    iMonotone (@opt_TP_default u V W f w).
Proof.
  unfold iMonotone.
  unfold Proper;  red.
  intros u V W f H' w t q y H; 
  induction H; simpl.
  apply IPOprf.
  apply H'.
  auto.
Qed.
  

Definition opt_TP_kl (u:T)(V W : IO)(f : V ---> W* ) 
      t (v: V* t) : W* t :=
 match v with
 | none _ _ => none u _
 | @some _ _ _  t' v' => f t' v'
 end.

Instance opt_TP_kl_monotone (u:T) (V W : IO)
       (f: V ---> opt_TP u W) (H : iMonotone f) : 
       iMonotone (opt_TP_kl f).
Proof. 
  intros.
  unfold iMonotone.
  unfold Proper; 
  repeat red; intros.
  induction H0; simpl.
  constructor.
  apply H; auto.
Qed.

Obligation Tactic := simpl; intros; unfold Proper; 
     unfold respectful; intros; elim_opt; 
               try app_all; mauto.

Program Instance opt_TP_monad_struct (u:T) : 
   Monad_struct (fun V => opt_TP u V) := {
  weta V := @Some_TP u V;
  kleisli V W f := opt_TP_kl (u:=u)  f
}.

Canonical Structure opt_TP_monad (u:T):= 
     Build_Monad (opt_TP_monad_struct u).

Instance opt_TP_lift_monotone (u : T) V W (f : V ---> W) (H : iMonotone f) :
      iMonotone (lift (M:= opt_TP_monad u) f).
Proof.
  intros u V W f H.
  unfold lift.
  simpl.
  apply opt_TP_kl_monotone.
  assert (H':=sub_comp (SubCat_compat:=IO_MAP_SubCat)).
  simpl in *.
  apply H';
  auto.
  apply Some_TP_monotone.
Qed.
  
Section proj.

Program Instance io_proj_struct (t : T) (A : IO) : 
    PO_obj_struct (A t) := {
  Rel := IRel (t:=t)
}.

Definition io_proj t A : wOrd := Build_PO_obj (io_proj_struct t A).

Definition io_proj_mor t A B (f : A ---> B) : 
          io_proj t A ---> io_proj t B := f t.

End proj.

End base_cats.

(*

Program Instance proj_Func (t:T) : 
     Functor_struct (C:=IO) (D:=SO) (*(Fobj:= fun a : IO => a t) *)
                        (@io_proj_mor t).
Next Obligation.
Proof.
  unfold Proper; red.
  intros f g H x.
  unfold io_proj_mor.
  auto.
Qed.
  
Canonical Structure proj (t : T) := Build_Functor (IT_proj_Func t).
End proj.


Section PostComp_w_Monad.

Variable P : Monad IO.



Definition opt_TP_def_varinj (u:T) (V W: IO) (f:V ---> P W) : 
          opt_TP u V ---> P (opt_TP u W):=
 (opt_TP_default (u:=u) (V:=V) (W:=P (opt_TP u W))
 (f ;; lift (weta (Monad_struct := (opt_TP_monad u)) W))
 (weta (Monad_struct := P) (opt_TP u W) u (none u W))).


(** needed for module property of the derivative *)

Lemma opt_TP_def_varinj_weta (u:T)(V:IO) :
      opt_TP_def_varinj (u:=u) (weta V) == weta _.
Proof.
  unfold opt_TP_def_varinj.
  simpl.
  intros u V t z;
  destruct z; 
  simpl; auto.
  set (H:= lift_weta P).
  simpl in H.
  simpl.
  rewrite H. auto.
Qed.
 

Lemma opt_TP_def_varinj_weta_f (u:T) (V V':IO) (f: V' ---> V) : 
    opt_TP_def_varinj (u:=u) (f ;; weta V) == 
              lift (M :=opt_TP_monad u) f ;; weta _ .
Proof.
  intros u V V' f t z.
  simpl.
  intros.
  destruct z; simpl.
    set (H:= lift_weta P).
    simpl in H.
    rewrite H.  auto.
    auto.
Qed.

(** for module M, we define [IPO_Der_Mod M], the derived module *)

Section Der_Module.

(*
Variable obD : Type.
Variable morD : obD -> obD -> Type.
Variable D: Cat morD.
*)
Variable D : Cat.
Section Der_Module_def.

Variable M : MOD P D.
(*
Definition der_mkl (u:T) (V W:IP) (f: V ---> P W) : 
   morD (M (opt_TP u V))  (M (opt_TP u W)) :=
        (mkleisli (opt_TP_def_varinj u f)).
*)
Program Instance IO_Der_Mod_struct (u:T) : 
        Module_struct P (D:=D) (fun V => M (opt_TP u V)) := {
  mkleisli a b f := (mkleisli (M:=M)(opt_TP_def_varinj (u:=u) f)) 
}.
Next Obligation.
Proof.
  intros u c d.
  unfold Proper; red.
  intros z y H.
  apply mkleisli_oid.
  simpl.
  intros r s; 
  destruct s;
  simpl;
  try rewrite H;
  auto.
Qed.

Obligation 3.
Proof.
  simpl in *.
  intros u c.
  assert (H:=mkleisli_oid(Module_struct:=M)).
  unfold Proper in H. red in H.
  rewrite (H _ _ _ _ (@opt_TP_def_varinj_weta u c)).
  mod.
Qed. 
  
Next Obligation.
Proof.
  intros u c d e f g.
  rewrite mkl_mkl.
  apply mkleisli_oid.
  unfold opt_TP_def_varinj. 
  
  (*intros t x; destruct x;
  simpl.*)
  assert (H:= lift_kleisli (M:=P)).
  simpl in H.  
  (*rewrite H.*)
  assert (H':= kleisli_lift (M:=P)).
  simpl in H'. 
   (*rewrite H'.*)
  assert (H'':= kleisli_oid (Monad_struct:=P)).
   unfold Proper in H''. repeat red in H''.
   simpl in H''.
(*   apply H''.*)
  intros t z. destruct z; simpl.
  rewrite H.
  rewrite H'.
  apply H''. 
  intros t0 z. simpl. auto.
  
  assert (H3:= eta_kl (Monad_struct := P)).
  simpl in H3.
  rewrite H3. simpl.
  auto. 
Qed.

Canonical Structure IO_Der_Mod (u:T) : MOD P D := 
      Build_Module (IO_Der_Mod_struct u).


End Der_Module_def.

(** deriving a module wrt u:T yields a functor *)

Section Der_Module_Functor.

Section Der_Mod_Hom.

Variables M N: MOD P D.
Variable TT : M ---> N.

Program Instance Der_Mod_Hom_struct (u:T) : 
  Module_Hom_struct (S:=IO_Der_Mod M u) (T:=IO_Der_Mod N u)
            (fun _ => TT (*opt_TP u x*) _ ) .
Next Obligation.
Proof.
  mod; try apply TT.
Qed.

Canonical Structure Der_Mod_Hom (u:T) : 
     IO_Der_Mod M u ---> IO_Der_Mod N u :=
           Build_Module_Hom 
           (Der_Mod_Hom_struct u).

End Der_Mod_Hom.

Program Instance Der_Mod_Func (u:T) : 
   Functor_struct (C:=MOD P D) (D:=MOD P D) 
        (Fobj:= fun z => IO_Der_Mod z u) 
        (fun M N TT => Der_Mod_Hom (M:=M) (N:=N) TT u).
Next Obligation.
Proof.
  unfold Proper; red.
  unfold Der_Mod_Hom; 
  simpl. auto.
Qed.
Next Obligation.
Proof.
  unfold Id_Mod.
  simpl. cat.
Qed.
Next Obligation.
Proof.
  unfold CompMod.
  simpl. cat.
Qed.

Canonical Structure DER_MOD (u:T) := Build_Functor (Der_Mod_Func u).


End Der_Module_Functor.

End Der_Module.

End PostComp_w_Monad.

(** Fibre Module:
     - P monad over IO
     - M module with codomain IO
     - M_u the u-fibre of M is a module with codomain SO *)


Section Fibre_module.

Variable P: Monad IO.

Section Fibre_Module_def.


Variable M : MOD P IO.

Program Instance Fibre_Mod_struct (u:T) : 
       Module_struct P (D:=SO) (fun c => io_proj u (M c)) := {
  mkleisli a b f := #(proj u) (@mkleisli IO P  IO M M  a b f)  
}.
Next Obligation.
Proof.
  intros u c d.
  assert (H := mkleisli_oid (P:=P) (M:=M)).
  unfold Proper in *; red; simpl in H.
  simpl in *.
  intros z y H'.
  apply H. 
  auto.
Qed.
Next Obligation.
Proof.
  intros.
  assert (H:=mkl_mkl (P:=P)(M:=M)).
  simpl in H.
  apply H.
Qed.
Next Obligation.
Proof.
  intros.
  assert (H:= mkl_weta (P:=P)(M:=M)).
  simpl in H.
  apply H.
Qed.

Canonical Structure Fibre_Mod (u:T) : MOD P SO := 
           Build_Module (Fibre_Mod_struct u).

End Fibre_Module_def.

Section Fibre_Module_Hom.
Variables M N : MOD P IO.
Variable TT : M ---> N.


Program Instance Fib_Mod_Hom_struct (u:T) : 
   Module_Hom_struct (S:= Fibre_Mod M u )(T:= Fibre_Mod N u)
    (fun z => #(proj u) (TT z) ).
Next Obligation.
Proof.
  intros u c d f x.
  destruct TT as [T1 T2].
  destruct T2 as [t1].
  assert (H:= t1 c d f).
  simpl in *.
  apply H.
Qed.

Canonical Structure Fib_Mod_Hom (u:T) : 
     Fibre_Mod M u ---> Fibre_Mod N u :=
        Build_Module_Hom (Fib_Mod_Hom_struct u).

End Fibre_Module_Hom.

Program Instance Fib_Mod_Func (u:T) : 
   Functor_struct (C:=MOD P IO) (D:=MOD P SO) 
        (Fobj:= fun x => Fibre_Mod x u) 
        (fun M N TT => Fib_Mod_Hom (M:=M) (N:=N) TT u).
Next Obligation.
Proof.
  unfold Proper; red.
  unfold Fib_Mod_Hom.
  simpl.
  auto.
Qed.

Canonical Structure FIB_MOD (u:T) := Build_Functor (Fib_Mod_Func u).

End Fibre_module.

Section DER_PB.
Notation "Sig '*' M" := (PB_MOD Sig _ M).
Variables R S: Monad IO.
Variable Sig: Monad_Hom R S.
(*
Variable obD: Type.
Variable morD: obD -> obD -> Type.
Variable D: Cat morD.
*)
Variable D : Cat.
Variable M: MOD S D.


Program Instance PB_DER_struct (u:T) : 
      Module_Hom_struct (S:= (PB_MOD Sig _ (DER_MOD _ _ u M)))
                                     (T:= DER_MOD _ _ u (PB_MOD Sig _ M))
          (fun e => id _) .
Next Obligation.
Proof.
  intros u c d f.
  rewrite idl;
  rewrite idr.
  simpl.
  apply mkleisli_oid.
  simpl.
  intros t x.
  simpl.
  destruct x; simpl.
  assert (H:= monad_hom_lift Sig (@Some_TP u d)).
  simpl in H.
  rewrite H; auto.
  assert (H':= monad_hom_weta (Monad_Hom_struct:=Sig)).
  simpl in H'.
  rewrite H'.
  auto.
Qed.

Definition PB_DER (u:T) : PB_MOD Sig _ (DER_MOD _ _ u M) ---> 
                            DER_MOD _ _ u (PB_MOD Sig _ M) :=
         Build_Module_Hom (PB_DER_struct u).

Program Instance DER_PB_struct (u:T) : 
      Module_Hom_struct (T:= (PB_MOD Sig _ (DER_MOD _ _ u M)))
                                     (S:= DER_MOD _ _ u (PB_MOD Sig _ M))
          (fun e => id _) .
Next Obligation.
Proof.
  intros u c d f.
  rewrite idl;
  rewrite idr.
  simpl.
  apply mkleisli_oid.
  simpl.
  intros t x.
  simpl.
  destruct x; simpl.
  assert (H:= monad_hom_lift Sig (@Some_TP u d)).
  simpl in H.
  rewrite H; auto.
  assert (H':= monad_hom_weta (Monad_Hom_struct:=Sig)).
  simpl in H'.
  rewrite H'.
  auto.
Qed.

Definition DER_PB (u:T) : DER_MOD _ _ u (PB_MOD Sig _ M) ---> 
                  PB_MOD Sig _ (DER_MOD _ _ u M) :=
         Build_Module_Hom (DER_PB_struct u).

Lemma DER_PB_PB_DER (u:T) : DER_PB u ;; PB_DER u == id _ .
Proof.
  intro u; simpl.
  simpl.
  cat.
Qed.

Lemma PB_DER_DER_PB (u:T) : PB_DER u ;; DER_PB u == id _.
Proof.
  intro u; simpl.
  simpl.
  cat.
Qed.



End DER_PB.

Section FIB_PB.

Notation "Sig '*' M" := (PB_MOD Sig _ M).
Variables R S: Monad IO.
Variable Sig: Monad_Hom R S.
(*
Variable obD: Type.
Variable morD: obD -> obD -> Type.
Variable D: Cat morD.
*)
(*
Variable D : Cat.
*)
Variable M: MOD S IO.

Program Instance PB_FIB_struct (u:T) : 
      Module_Hom_struct (S:= (PB_MOD Sig _ (FIB_MOD _ u M)))
                                     (T:= FIB_MOD _ u (PB_MOD Sig _ M))
          (fun e => id _) .

Definition PB_FIB (u:T) : 
      (PB_MOD Sig _ (FIB_MOD _ u M)) ---> FIB_MOD _ u (PB_MOD Sig _ M) :=
          Build_Module_Hom (PB_FIB_struct u).

Program Instance FIB_PB_struct (u:T) : 
      Module_Hom_struct (T:= (PB_MOD Sig _ (FIB_MOD _ u M)))
                                     (S:= FIB_MOD _ u (PB_MOD Sig _ M))
          (fun e => id _) .

Definition FIB_PB (u:T) : 
        FIB_MOD _ u (PB_MOD Sig _ M) ---> PB_MOD Sig _ (FIB_MOD _ u M) :=
          Build_Module_Hom (FIB_PB_struct u).

Lemma FIB_PB_PB_FIB (u:T) : 
          FIB_PB u ;; PB_FIB u == id _ .
Proof.
  intro u;
  simpl.
  simpl.
  auto.
Qed.

Lemma PB_FIB_FIB_PB (u:T) : 
          PB_FIB u ;; FIB_PB u == id _ .
Proof.
  intro u;
  simpl; auto.
Qed.
  
End FIB_PB.


(** for a monad R over IP, we define substitution of *u 
    in terms of (kleisli R) *)
Section substitution.

Variable R: Monad IO.

Section subst_kleisli_arg.

Variable V: IO.
Variable r: T.
Variable W : R V r.

Definition IPsubst_map := opt_TP_default (weta (Monad_struct:=R) _ ) W.

End subst_kleisli_arg.

Definition IOsubstar (r:T) (V:IO) (W:R V r) := kleisli (IPsubst_map W).

End substitution.

End base_cats.

(*Notation "x <<< y" := (IRel x y) (at level 60).*)

(*Existing Instance IO_Initial.*)
(*Existing Instance IO_Terminal.*)
Existing Instance Fib_Mod_Func.
Existing Instance IO_SMAP_s.
Existing Instance ipo_obj_s.
Existing Instance IRel_Trans.


*)



