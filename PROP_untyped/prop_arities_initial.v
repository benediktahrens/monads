
Require Export CatSem.PROP_untyped.initial.
Require Export CatSem.CAT.SO.

Require Import Coq.Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Automatic Introduction.
Unset Transparent Obligations.


Notation "[[ x ; .. ; y ]]" := (cons x .. (cons y nil) ..).

Notation "[ T ]" := (list T) (at level 5).

(** ** Propositional arities and their representations
	given a signature [S], we define 
	- half-equations 
	- algebraic half-equations
	- (in)equations over [S] as pairs of half-equations
	- representations of (in)equations as a predicate on representations of [S]
*)

(** ** Modules with codomain [wPO] *)

(** given a relative module [M:Set -> PO] over a relative monad [P] over Delta, 
       the data of [M] defines a [P]-module [M : Set -> wPO ] *)

Section wPO_taut_mod.

Variable P : RMonad Delta.
Variable M : RModule P Ord.

Obligation Tactic := unfold Proper, respectful; mauto;
        try apply (rmkl_eq M);
        try rew (rmklmkl M);
        try rew (rmkleta M); mauto.

Program Instance wOrd_RMod_struct : RModule_struct P wOrd M := {
  rmkleisli a b f := rmkleisli (RModule_struct:= M) f }.

Definition wOrd_RMod : RModule P wOrd := Build_RModule wOrd_RMod_struct.

End wPO_taut_mod.

(*
Section monadic_subst_as_mod_hom.

Variable P : RMonad Delta.

(*
Print RModule_Hom.

Definition bla:
(forall c : TYPE,
  (product (C:= RMOD P wPO) (wPO_RMod ((DER_RMOD_not PO P) P)) (wPO_RMod P)) c --->
  (wPO_RMod P) c).
simpl.
intro c.
apply (fun y => Rsubstar_not (snd y) (fst y)).
Defined.

(*
apply substar_not.
intro c.
apply (substar 
*)
Print bla.
*)

Ltac elim_option := match goal with [H : option _ |- _ ] => 
                     destruct H end.

Ltac t := mauto ; repeat (unfold Rsubstar_not ||
         match goal with [H: prod _ _ |-_] => destruct H end ||
         rew (rklkl P) || app (rkl_eq P) || elim_option ||  
         rew (rkleta P) || rew (retakl P ) || 
         rew (rlift_rkleisli P) || rew (rkleisli_rlift P) || 
         unfold rlift || rew (rkleta_eq (FM:=P)) || mauto ).

(*
Obligation Tactic := t.
Check Der_RMod_not.
Program Instance Rsubstar_mod_hom_struct : RModule_Hom_struct
   (M := product (C:=RMOD P wPO) ((DER_RMOD_not _ _ (wPO_RMod P))) (wPO_RMod P)) 
   (N := wPO_RMod P) 
   (fun c y => Rsubstar_not (snd y) (fst y)).
Definition Rsubstar_mod_hom := Build_RModule_Hom Rsubstar_mod_hom_struct.
*)

End monadic_subst_as_mod_hom.
*)

(** ** S-Modules and Equations
   given signature [S], we define equations and the predicate [satisfies_prop_sig]
     on representations of [S]
*)

Section S_Mods_and_Eqs.

Variable S : Signature.

(** an S_Module over [S] should be a functor from representations of [S]
      to the category whose objects are pairs of a monad P and a module over P.
   we don't need the functor properties, and use dependent types instead of the cumbersome 
   category of pairs
*)

(*
Class S_Module_s (Tau : forall R : REP S, RMOD R wOrd) := {
   S_Mod_Hom : forall (R S : REP S) (f : R ---> S), 
      Tau R ---> PbRMod f (Tau S)  }.
*)

Record S_Module := {
  s_mod :> forall R : REP S, RMOD R wOrd ;
  s_mod_hom :> forall (R T : REP S)(f : R ---> T),
         s_mod R ---> PbRMod f (s_mod T)  }.

(** a half-equation is a natural transformation of between S-Modules. 
    we need the naturality condition in the following *)

(*Notation "U @ f" := (S_Mod_Hom (S_Module_s := U) f)(at level 4).*)


Notation "U @ f" := (s_mod_hom U f)(at level 4). 

Class half_equation_struct (U V : S_Module) 
    (half_eq : forall R : REP S, (*s_mod*) U R ---> (*s_mod*) V R) := {
  comm_eq_s : forall (R T : REP S)  (f : R ---> T), 
      U @ f ;; PbRMod_Hom _ (half_eq T) ==  half_eq R ;; V @ f }.



(*
Class half_equation_struct (U V : S_Module) 
    (half_eq : forall R : REP S, s_mod U R ---> s_mod V R) := {
  comm_eq_s : forall (R S : REP S)  (f : R ---> S), 
     S_Mod_Hom (*S_Module_s := U*) f ;; PbRMod_Hom _ (half_eq S) == 
                half_eq R ;; S_Mod_Hom (S_Module_s := V) f }.
*)

(*
Class half_equation_struct (U V : S_Module) 
    (half_eq : forall R : REP S, s_mod U R ---> s_mod V R) := {
  comm_eq_s : forall (R S : REP S)  (f : R ---> S), 
     S_Mod_Hom (*S_Module_s := U*) f ;; PbRMod_Hom _ (half_eq S) == 
                half_eq R ;; S_Mod_Hom (S_Module_s := V) f }.
*)

Record half_equation (U V : S_Module) := {
  half_eq :> forall R : REP S, U R --->  V R ;
  half_eq_s :> half_equation_struct half_eq }.



Section S_Module_classic.

(** ** Classic S-Modules and Equations 

we are interested in classic S-Modules, i.e. of the form PROD_i P^{n(i)} *)

Variable l : [nat].

(** classic S-Modules on objects *)

Section ob.

Variable P : RMonad Delta.
Variable M : RModule P Ord.

Obligation Tactic := mauto; repeat (t || unfold Proper, respectful || 
                             app pm_mkl_eq || rew pm_mkl_mkl || app pm_mkl_weta).

Program Instance S_Mod_classic_ob_s : RModule_struct P wOrd (fun V => prod_mod_po M V l) := {
  rmkleisli a b f := pm_mkl f }.

Definition S_Mod_classic_ob : RMOD P wOrd := Build_RModule S_Mod_classic_ob_s.

End ob.

Section mor.

(** classic S-Modules on morphisms *)

Variables P Q : RMonad Delta.
Variable f : RMonad_Hom P Q.

Obligation Tactic := repeat (mauto || rew prod_mod_c_kl || app pm_mkl_eq).

Program Instance S_Mod_classic_mor_s : RModule_Hom_struct 
       (M := S_Mod_classic_ob P) (N := PbRMod f (S_Mod_classic_ob Q)) 
       (@Prod_mor_c _ _ f l).

Definition S_Mod_classic_mor := Build_RModule_Hom S_Mod_classic_mor_s.

End mor.

Definition S_Mod_classic := {|
      s_mod := fun R => S_Mod_classic_ob R ;
      s_mod_hom R T f := S_Mod_classic_mor f |}.
(*
Instance S_Mod_classic_s : S_Module_s (fun R => S_Mod_classic_ob R) := {
  S_Mod_Hom R S f := S_Mod_classic_mor f }.
*)
(*Definition S_Mod_classic := Build_S_Module S_Mod_classic_s.*)

End S_Module_classic.

(** ** Example : substitution *)

Section substitution.

(** substitiution is an example of half-equation *)

(** the carrier is - for the moment - defined by tactics. Buh! 
     we don't care, since it's just an example *)

Definition subst_carrier (P : REP S) :
(forall c : TYPE, (S_Mod_classic_ob [[1; 0]] P) c ---> (S_Mod_classic_ob [[0]] P) c) .
simpl.
intros.
simpl in *.
inversion X.
simpl in *.
inversion X1.
simpl in X2.
constructor.
simpl.
apply (Rsubstar_not X2 X0).
apply TTT.
Defined.

(*
Print subst_carrier.

Definition subst_carrier_exp (P : REP S) :
(forall c : TYPE, (S_Mod_classic_ob [[1; 0]] P) c ---> (S_Mod_classic_ob [[0]] P) c) :=
  fun c X => match X in (prod_mod_c _ _ l) return 
       (match l with 
        | TTT => False_rect _ _ _ 
        | CONSTR a b => match b with


Definition subst_carrier2 (P : REP S) :
(forall c : TYPE, (S_Mod_classic_ob [[1; 0]] P) c ---> (S_Mod_classic_ob [[0]] P) c) .
simpl; intros.
pose (diag x := match x with cons a b => prod_mod_c (fun x => P x) x [[0]])
  fun c X => match X in 
          prod_mod_c (fun x : Type => P x) _ l return 

*)

Program Instance sub_struct (P : REP S) : RModule_Hom_struct 
  (M:=S_Mod_classic_ob [[1;0]] P) (N:=S_Mod_classic_ob [[0]] P) (subst_carrier (P:=P)).
Next Obligation.
Proof.
  dependent destruction x.
  dependent destruction x.
  simpl in *.
  apply CONSTR_eq; auto.
  unfold Rsubstar_not.
  rew (rklkl P).
  rew (rklkl P).
  apply (rkl_eq P).
  simpl.
  mauto. 
  destruct x0; simpl.
  unfold rlift.
  simpl.
  rew (retakl P).
  rew (rklkl P).
  rew (rkleta_eq (FM:=P)).
  intros.
  rew (retakl P).
  rew (retakl P).
Qed.


Definition subst_module_mor (P : REP S) := Build_RModule_Hom (sub_struct P).


Program Instance subst_half_s : half_equation_struct 
      (U:= (S_Mod_classic [[1 ; 0]])) (V:=S_Mod_classic [[0]]) subst_module_mor.
Next Obligation.
Proof.
  
  dependent destruction x.
  dependent destruction x.
  dependent destruction x.
  
  simpl.
  apply CONSTR_eq; auto.
  unfold Rsubstar_not.
  
  rew (rmon_hom_rkl f).
  app (rkl_eq T).
  intros. 
  match goal with [H:option _ |- _]=>destruct H end;
  simpl.
  rew (rmon_hom_rweta f).
  auto.
Qed.

Definition subst_half_eq := Build_half_equation subst_half_s.

End substitution.

(** end of example *)

(** ** Algebraic stuff cont. 

an algebraic half-equation is a half-equation with algebraic codomain, and
	an arbitrary domain *)



Definition half_eq_classic (U : S_Module)(codl : [nat]) := 
      half_equation U (S_Mod_classic codl).

(** an algebraic (in)equation is given by 
       - an arbitrary domain [domS]
       - an algebraic codomain [S_Mod_alg codl]
       - two half-equations [eq1 eq2 : domS -> S_Mod_alg codl] *)

Record ineq_classic := {
  Dom : S_Module ;
  Cod : [nat] ;
  half_eq_l : half_eq_classic Dom Cod ;
  half_eq_r : half_eq_classic Dom Cod }.



(*
Definition satisfies_eq l l' (e : eq_alg l l') (P : REP S) : Prop.
intros.
destruct e.
simpl in *.
destruct eq3.
destruct eq4.
Check S_Mod_alg. Print S_Module.
apply (forall c : TYPE,
         forall x : s_mod_rep (S_Mod_alg l) P c, half_eq0 P _ x << half_eq1 _ _ x).
Defined.

*)

(** ** Representation of (a set of) (in)equations 

a representation [P] satisfies an equation [e] iff for any element in the domain [domS e P c],
 ([c] a set of variables) its two images under e1 and e2 are related
*)

(*
Definition satisfies_eq (e : eq_alg) (P : REP S) :=
  forall c (x : s_mod_rep (domS e) P c), 
       (*half_eq*) (eq1 e) P _ x << (*half_eq*) (eq2 e)_ _ x.
*)

Definition satisfies_ineq (e : ineq_classic) (P : REP S) :=
  forall c (x : Dom e P c), 
        half_eq_l _ _ _ x <<  half_eq_r _ _ _ x.

(** a set of (in)equations, indexed by a set A *)

Definition Inequations (A : Type) := A -> ineq_classic.


(** [R] satisfies [T] iff it satisfies any equation of [T] *)

Definition satisfies_ineqs A (T : Inequations A) (R : REP S) :=
      forall a, satisfies_ineq (T a) R.

(** ** Subcategory of Rep(S) of representations satisfying equations *)

Section subcat.

(** given any set of (in)equations [T], we consider the following subcategory of 
    the category of representations:
     - objects : representations that satisfy [T]
     - morphisms : morphisms that satisfy [True], hence any 
*)

Variable A : Type.
Variable T : Inequations A.

(** lemma stating that the properties are closed under composition and 
    identity *)

Program Instance Ineq_Rep : SubCat_compat (REP S)
     (fun P => satisfies_ineqs T P) (fun a b f => True).

(** hence we obtain a category, the category of representations of [(S, T)] *)

Definition INEQ_REP : Cat := SubCat Ineq_Rep.


(** * Initiality in the subcategory 
We proceed with the construction of its initial object *)

(** ** Order induced by a set of equations
first thing to do is to build the correct order on the set of terms:
     - two terms [x] and [y] are related if their images under any 
        initial morphism towards a rep of [(S, T)] is
     - this initial morphism is actually in the category of representations of 
     [S], hence we must inject [R] into the big category
*)

Definition prop_rel_c X (x y : UTS S X) : Prop :=
      forall R : INEQ_REP, init (FINJ _ R) x << init (FINJ _ R) y.

(** this ordering is a preorder *)

Program Instance prop_rel_po X : PreOrder (@prop_rel_c X).
Next Obligation.
Proof.
  unfold Reflexive.
  unfold prop_rel_c.
  reflexivity.
Qed.
Next Obligation.
Proof.
  unfold Transitive.
  unfold prop_rel_c.
  simpl; intros.
  transitivity (init (proj1_sig R) y); 
  auto.
Qed.

Definition prop_rel_po_s X := Build_PO_obj_struct (prop_rel_po X).

Definition prop_rel X := Build_PO_obj (prop_rel_po_s X).

(** ** Substitution compatible with new order
substitution as defined previously is compatible with this order *)

Program Instance subst_prop_rel_s X Y (f : X ---> UTS S Y) : 
   PO_mor_struct (a := prop_rel X) (b := prop_rel Y) (subst f).
Next Obligation.
Proof.
  unfold Proper, respectful.
  unfold prop_rel_c.
  simpl. intros.
  assert (H':= init_kleisli (proj1_sig R)).
  simpl in H'.
  assert (H2 := H' X x _ (Sm_ind f)).
  simpl in H2.
  rewrite H2.
  clear H2.
  assert (H3 := H' X y _ (Sm_ind f)).
  rew H3.
  clear H3.
  apply PO_mor_monotone.
  auto.
Qed.

Definition subst_prop_rel X Y f := Build_PO_mor (subst_prop_rel_s X Y f).

(** now this gives a new relative monad
     - the set of terms is the same as [UTS_sm]
     - the order on any set of terms is different
*)

Obligation Tactic := cat; 
      repeat (unfold Proper, respectful || 
       rewrite subst_var || app subst_eq ||
       rewrite subst_subst || cat).
      
(** ** Monad with previously defined terms but new order, induced by equations *)

Program Instance UTS_prop_rel_rmonad_s : RMonad_struct Delta prop_rel := {
  rweta c := Sm_ind (@Var S c);
  rkleisli := subst_prop_rel
}.

Definition UTSP := Build_RMonad (UTS_prop_rel_rmonad_s).

(** ** an experiment *)
Section higher_order_monotonicity.

(** see the content of this section in _variant *)

(*
Variables X Y : TYPE.
Variables f g : X -> UTSP Y.
Hypothesis H : forall x, f x << g x.
Check H.


Lemma higher_order_mon X (t : UTSP X) Y (f g : X -> UTSP Y)
           (H : forall x, f x << g x)
         : subst_prop_rel f t << subst_prop_rel g t.
Proof.
  simpl in *.
  Check (prod_mod_c_rel (M:= prop_rel)).
 Check prop_rel.
  Check prod_mod_c.
  Check (@UTSind S
           (fun X (t : UTSP  X) =>
              forall Y (f g : X ---> UTS S Y),
             (forall x : X, prop_rel_c (f x) (g x)) ->
            prop_rel_c (subst f t) (subst g t))

           (fun X l (v : UTS_list S X l) => 
              forall Y (f g : X ---> UTS S Y),
                 (forall x : X, prop_rel_c (f x) (g x)) ->

           Rel 
            prod_mod_c_rel (M:=prop_rel) (list_subst v f) (list_subst v g))).

).



       Rel (PO_obj_struct := prod_mod_po (SC_inj_ob R) V l) 
  (Prod_mor_c (init_mon (S:=S) (SC_inj_ob R)) x)
  (Prod_mor_c (init_mon (S:=S) (SC_inj_ob R)) y) ) :
prod_mod_c_rel (M:=prop_rel) x y.
          (forall x : X, forall R, init (proj1_sig R) (f x) << init _ (g x))
            -> forall t : UTSP X, subst_prop_rel f t << subst_prop_rel g t)).


 set (H:= (@UTSind S
            (fun (X : Type) (T : UTS S X) =>
             forall (Y : Type) (f g : X -> UTS S Y),
         (forall x : X, forall R, init (proj1_sig R) (f x) << init _ (g x))
            -> forall t : UTSP X, subst_prop_rel f t << subst_prop_rel g t))).


app (@UTSlistind 
      (fun V x => forall W (f g : V ---> UTS W)
              (H:f == g), x >== f = x >== g)
      (fun V l (v : UTS_list V l) => 
               forall W (f g : V ---> UTS W)(H:f == g),
           v >>== f = v >>== g) );

app (@UTSind 
       (fun (a : Type) (v : UTS a) => 
            forall (b : Type)(f g : a ---> b),
         (f == g) ->
         rename (W:=b) f v = rename (W:=b) g v)
       (fun V l (v : UTS_list V l) => 
            forall (b : TYPE)(f g : V ---> b),
         (f == g) ->
         v //-- f =  v //-- g))


  unfold po_obj_struct in H.
  unfold prop_rel in H.
*)
End higher_order_monotonicity.

(** ** Important Lemma
This lemma corresponds to one direction of Lemma 36 *)
(** it says : the relation defined by the set of equations
       behaves well when doing products and derivations.
 this is why we restrict ourselves to algebraic codomains
*)



Lemma lemma36 (l : [nat]) (V : Type)
    (x y : prod_mod_c (fun x : Type => UTS S x) V l)
    (H : prod_mod_c_rel (M:=prop_rel) x y) 
    (R : INEQ_REP):
Rel (PO_obj_struct := prod_mod_po (SC_inj_ob R) V l) 
  (Prod_mor_c (init_mon (SC_inj_ob R)) x)
  (Prod_mor_c (init_mon (SC_inj_ob R)) y).

(*
Lemma lemma36 (l : [nat]) (V : Type)
    (x y : prod_mod_c (fun x : Type => UTS Sig x) V l)
    (H : prod_mod_c_rel (M:=prop_rel) x y) 
    (R : subob (fun P : Representation Sig => satisfies_prop_sig (A:=A) T P)):
Rel (PO_obj_struct := prod_mod_po (SC_inj_ob R) V l) 
  (Prod_mor_c (init_mon (SC_inj_ob R)) x)
  (Prod_mor_c (init_mon (SC_inj_ob R)) y).
*)

Proof.
  simpl.
  induction l; simpl;
  intros.
  dependent destruction x.
  dependent destruction y.
  constructor.
  dependent destruction x.
  simpl.
  dependent destruction y.
  simpl.
  constructor.
  simpl.
  Focus 2.
  apply IHl.
  dependent destruction H.
  auto.
  dependent destruction H.
  unfold prop_rel in H. simpl in H.
  unfold prop_rel_c in H.
  apply (H R).
Qed.


(** ** Representation in the new monad 
we now pass to representations of [S] in our new shiny monad. the carrier is 
    the same as for the diagonal monad. we have to prove that it is compatible with
    the new order on terms *)

Program Instance Build_prop_pos (i : sig_index S) V : PO_mor_struct
  (a := prod_mod UTSP (sig i) V) (b := UTSP V)
  (fun X => Build (i:=i) (UTSl_f_pm (V:=V) X)).
Next Obligation.
Proof.
  unfold Proper; red.
  intros; simpl.
  unfold prop_rel_c.
  simpl.
  intros.
  assert (H2:= repr_hom_s (Representation_Hom_struct := init_representic (SC_inj_ob R))).
  simpl in H2.
  unfold commute in H2.
  simpl in H2.
  rewrite <- H2.
  rewrite <- H2.
  apply PO_mor_monotone.
  apply lemma36.
  auto.
Qed.

Definition Build_prop_po i V := Build_PO_mor (Build_prop_pos i V).

(** these lemmas are the same as for the other monad *)
(** perhaps we could reuse some code here, but that is not urgent *)

Lemma _lshift_lshift_eq2 (b : nat) (X W : TYPE) (f : PO_mor (sm_po X) (prop_rel W))
   (x : X ** b):
 lshift_c (P:=UTSP) (l:=b) (V:=X) (W:=W) f x =
    _lshift (S:=S) (l:=b) (V:=X) (W:=W) f x .
Proof.
  induction b;
  simpl; intros.
  auto. 
  rewrite IHb.
  apply _lshift_eq.
  simpl.
  intros.
  destruct x0; simpl;
  auto.
  unfold inj.
  rewrite subst_eq_rename.
  auto.
Qed.

Lemma sts_list_subst2 l X (v : prod_mod (UTSP) l X) 
       W (f : Delta X ---> UTSP W):
  UTSl_f_pm  (pm_mkl f v ) = list_subst (UTSl_f_pm v) f.
Proof.
  induction v; simpl;
  intros. auto.
  apply constr_eq.
  apply subst_eq.
  intros.
  rewrite _lshift_lshift_eq2.
  auto.
  auto.
Qed.

Hint Resolve sts_list_subst : fin.
Hint Rewrite sts_list_subst : fin.

(** we need module morphisms for the representation *)

Program Instance Build_prop_s i : RModule_Hom_struct (Build_prop_po i).
Next Obligation.
Proof.
  rewrite sts_list_subst2.
  auto.
Qed.

(** [Build_prop i] represents the arity [i] *)

Definition Build_prop i := Build_RModule_Hom (Build_prop_s i).


(**  UTSP has a structure as a representation of S *)

Canonical Structure UTSPrepr : Repr S UTSP := Build_prop.

Canonical Structure UTSProp : REP S := 
       Build_Representation (@UTSPrepr).

(** ** Important Lemma, other direction
other direction of Lemma 36
    - also here some code savings possible
    - this is actually not the variant we need: point is,
      we have V (init) = V (init_prop) (cf. later) 
    - here is the version with V (init)
*)

Lemma lemma36_2 (l : [nat]) (V : Type)
    (x y : prod_mod_c (fun x : Type => UTS S x) V l)
    (H : forall R : INEQ_REP,
        Rel (PO_obj_struct := prod_mod_po (SC_inj_ob R) V l) 
  (Prod_mor_c (init_mon (S:=S) (SC_inj_ob R)) x)
  (Prod_mor_c (init_mon (S:=S) (SC_inj_ob R)) y) ) :
prod_mod_c_rel (M:=prop_rel) x y.

(*
Lemma lemma36_2 (l : [nat]) (V : Type)
    (x y : prod_mod_c (fun x : Type => UTS Sig x) V l)
    (H : forall R : subob (fun P : Representation Sig => satisfies_prop_sig (A:=A) T P),
        Rel (PO_obj_struct := prod_mod_po (SC_inj_ob R) V l) 
  (Prod_mor_c (init_mon (Sig:=Sig) (SC_inj_ob R)) x)
  (Prod_mor_c (init_mon (Sig:=Sig) (SC_inj_ob R)) y) ) :
prod_mod_c_rel (M:=prop_rel) x y.
*)

Proof.
  simpl.
  induction l; simpl;
  intros.
  constructor.
  dependent destruction x.
  dependent destruction y.
  simpl.
  constructor.
  simpl.
  Focus 2.
  apply IHl.
  intros.
  assert (h:= H R).
  clear H.
  dependent destruction h.
  apply h.
  unfold prop_rel_c.
  intros.
  assert (h:= H R).
  dependent destruction h.
  apply H0.
Qed.

(** ** A morphism of representations 
we produce a morphism of representations from [UTSP_sm] to 
     [UTSPREPR] 
     - this is in fact the identity morphism
     - just the order becomes bigger
*)
(** we use this morphism to show that an equation is the same on 
  [UTSM_sm] (diagonal order) and [UTSP] (order induced by equations)
*)

Program Instance Id_UTSM_UTSPs : 
   RMonad_Hom_struct (P:=UTSM S) (Q:=UTSP) 
   (fun c => Sm_ind (id (UTS S c))).

Definition Id_UTSM_sm_UTSP := Build_RMonad_Hom Id_UTSM_UTSPs.

Lemma id_UTSM_sm_UTSP l c (x : prod_mod_c (fun x => UTS S x) c l) : 
      Prod_mor_c Id_UTSM_sm_UTSP x = x.
Proof.
  induction x; simpl; intros;
  auto; apply CONSTR_eq; auto.
Qed.

Obligation Tactic := unfold commute; simpl; intros;
     repeat (apply f_equal || apply id_UTSM_sm_UTSP || auto).

Program Instance debi2s : 
     Representation_Hom_struct (P:=UTSRepr S) (Q:=UTSProp) Id_UTSM_sm_UTSP.

Definition UTSM_sm_UTSP_rep_hom := Build_Representation_Hom debi2s.

Existing Instance UTS_initial.

Lemma half_eq_const_on_carrier : forall c x, 
   init_rep UTSProp c x = x.
Proof.
  simpl;
  assert (H:=InitMorUnique (C:=REP S) UTSM_sm_UTSP_rep_hom);
  simpl in H;
  auto.
Qed.


(*

(** this lemma states that half-equations are constant on 
    representations whose underlying sets of terms are the same and the 
     order gets bigger *)
(** when passing from [UTSM_sm] to [UTSP], the equations remain the same *)

Lemma debi3s a c x:
forall h : half_eq_alg (domS (T a)) (codl (T a)),
    (h (UTSRepr Sig)) c x = (h UTSPROPRepr) c x.
Proof.
  simpl.
  intros.
  destruct h.
  simpl in *.
  destruct half_eq_s0.
  simpl in *.
  assert (H:= comm_eq_s0 _ _ (debi2) c x).
  rewrite debi25 in H.
  rewrite debi25 in H.
  auto.
Qed.

*)


(** [UTSPROPRepr] satisfies (in)equations
the new nice representation [UTSPROPRepr] satisfies the equations of [T], contrary
    to the old one, [UTSRepr] *)

(** ** Weak Initiality
     we will use the weak initial morphism in the proof that
     UTSPROPRepr satisfies the equations

*)

Section weak_init.

Variable R : INEQ_REP.

(** the initial morphism is the same as before
      - we need to show that it is monotone, which is by definition
      - that it is a morphism of monads
      - morphism of representations
      - unicity
*)


Program Instance init_prop_s V : PO_mor_struct
    (a:=(UTSProp) V) (b:=(FINJ _ R) V) (init (FINJ _ R) (V:=V)).
Next Obligation.
Proof.
  unfold Proper, respectful;
  intros. 
  simpl in *. 
  unfold prop_rel_c in H. 
  simpl in H.
  apply H.
Qed.

Definition init_prop_po V := Build_PO_mor (init_prop_s V).

Obligation Tactic := cat; rewrite init_kleisli2; 
           app (rkl_eq (proj1_sig R)).

(** monadicity *)

Program Instance init_prop_mon_s : RMonad_Hom_struct
      (P:=UTSProp)(Q:=FINJ _ R) init_prop_po.

Definition init_prop_mon := Build_RMonad_Hom init_prop_mon_s.

(** representativity asks for a lemma, same as for case without equations *)

Lemma prod_mor_eq_init_list2 (i : sig_index S) V
       (x : prod_mod_c (fun V => UTS S V) V (sig i)) :
  Prod_mor_c init_prop_mon x = init_list _ (UTSl_f_pm x).
Proof.
  induction x;
  simpl; auto.
  unfold FINJ in IHx. simpl in *.
  rewrite  IHx.
  simpl. auto.
Qed.

Obligation Tactic := repeat (cat || unfold commute ||
             rewrite prod_mor_eq_init_list2).

Program Instance init_prop_rep : Representation_Hom_struct 
       init_prop_mon.

Definition init_prop_re := Build_Representation_Hom init_prop_rep.

End weak_init.


(** ** V (init) = V (init_prop)
*)

Lemma bb2b (R : INEQ_REP) a l (x : prod_mod_c (fun x : Type => UTS S x) a l):
  Prod_mor_c (init_prop_mon R) x = Prod_mor_c (init_mon (SC_inj_ob R)) x.
Proof.
  reflexivity.
Qed.

(** ** Version of lemma36_2 using init_prop
*)

Lemma lemma36_2a (l : [nat]) (V : Type)
    (x y : prod_mod_c (fun x : Type => UTS S x) V l)
    (H : forall R : INEQ_REP,
        Rel (PO_obj_struct := prod_mod_po (SC_inj_ob R) V l) 
  (Prod_mor_c (init_prop_mon  (R)) x)
  (Prod_mor_c (init_prop_mon  (R)) y) ) :
prod_mod_c_rel (M:=prop_rel) x y.
Proof.
  simpl; intros.
  apply lemma36_2.
  simpl; intros.
  rewrite <- bb2b.
  rewrite <- bb2b.
  apply H.
Qed.

(** ** [UTSPROPRepr satisfies equations
      - we use  a1(x) < a2(x) in V(Sigma)(X) iff 
                  forall R, V(init_R) (a1(x)) < V(init_R) (a2(x))
      - we rewrite V(init_R)(a1(x)) = a1 (U (init_R) x) 
      - and for a2 as well
*)

Lemma UTSPRepr_sig_prop : satisfies_ineqs T UTSProp.
Proof.
  unfold satisfies_ineqs, satisfies_ineq.
  simpl; intros.
  apply lemma36_2a.
  intros. 
  assert (H4:=comm_eq_s (half_equation_struct := half_eq_l (T a))).
  assert (H5:=H4 _ _ (init_prop_re R)).
  
  assert (H4':=comm_eq_s (half_equation_struct := half_eq_r (T a))).
  assert (H5':=H4' _ _ (init_prop_re R)).
  
  clear H4 H4'.
  simpl in *.

  rewrite <- H5.
  rewrite <- H5'.
  
  destruct R as [R v].
  unfold satisfies_ineqs in v.
  unfold satisfies_ineq in v.
  simpl in *.
  apply v.
Qed.

(*
  simpl in *.
  assert (H6:=H5 c x).
  simpl in *.
  rewrite <- bbb.
  Check Prod_mor_c.
  Check ((eq1 (T a) UTSPROPRepr) c x).
  assert (H: 
       Prod_mor_c1
                             (init_prop_mon
                                (exist
                                   (fun a : Representation Sig =>
                                    satisfies_prop_sig (A:=A) T a) x0 v))
                             (((eq1 (T a)) UTSPROPRepr) c x) = 
  Prod_mor_c1 (init_mon (Sig:=Sig) x0) (((eq1 (T a)) UTSPROPRepr) c x)).
  simpl. auto.
  rerew  H.
  clear H.
  rewrite <- H6.
  clear H5 H6.
  
  assert (H1: 
       Prod_mor_c1
      (init_prop_mon
         (exist (fun a : Representation Sig => satisfies_prop_sig (A:=A) T a)
            x0 v)) (((eq2 (T a)) UTSPROPRepr) c x) = 
        Prod_mor_c1 (init_mon (Sig:=Sig) x0) (((eq2 (T a)) UTSPROPRepr) c x)).
  simpl; auto.
  rerew H1.
  rewrite <- H5'.
       
  unfold satisfies_prop_sig in v.
  unfold satisfies_eq in v.
  simpl in v.
  apply v.
Qed.
*)

(** ** yielding an object of the subcategory 
*)

Definition UTSPROP : INEQ_REP := 
 exist (fun R : Representation S => satisfies_ineqs (*A:=A*) T R) UTSProp
  UTSPRepr_sig_prop.

(** ** Initiality in the subcategory *)

Section init.

Variable R : INEQ_REP.

(** the initial morphism is the same as before
      - we need to show that it is monotone, which is by definition
      - that it is a morphism of monads
      - morphism of representations
      - unicity
*)




(** ** Weak Initial morphism in subcategory 
    was already defined *)

Definition init_prop : UTSPROP ---> R := exist _ (init_prop_re R) I.

Section unique.

(** ** Initiality in subcategory *)

Variable f : UTSPROP ---> R.

Existing Instance REP_struct.

(** the proof uses initiality of init in the case without equations
     - unicity is only concerned with data
     - for data, the initial morphisms in the category of reps and in 
       the subcategory are the same
*)

Lemma init_prop_unique : f == init_prop.
Proof.
  simpl. intros.
  destruct f.
  simpl in *.
  clear t.
  clear f.
  unfold SC_inj_ob in x1.
  simpl in x1.
  destruct R.
  simpl in *.
  clear R.
  assert (H:= InitMorUnique (Initial := UTS_initial S) 
                         (UTSM_sm_UTSP_rep_hom ;; x1)).
  simpl in H.
  auto.
Qed.  


(*
Lemma init_prop_unique : f == init_prop.
Proof.
  simpl. intros.
  destruct f.
  simpl in *.
  clear t.
  clear f.
  unfold SC_inj_ob in x1.
  simpl in x1.
  destruct R.
  simpl in *.
  clear R.
  
  apply (@UTSind Sig
     (fun V v => x1 V v = init x2 v)
     (fun V l v => Prod_mor x1 l V (pm_f_STSl v) = init_list _ v));
  simpl; intros;
  auto.
  rew (rmon_hom_rweta x1).
  rewrite <- (one_way u).
  assert (H':=@repr_hom_s _ _ _ x1 x1).
  unfold commute in H'.
  simpl in H'.
  rewrite <- H'.
  
  rewrite one_way.
  rewrite H. auto.
  rewrite H0. simpl.
  rewrite H.
  auto.
Qed.
*)

End unique.

End init.

(** ** Initiality verified by Coq *)

Program Instance INITIAL_INEQ_REP : Initial INEQ_REP := {
  Init := UTSPROP ;
  InitMor := init_prop ;
  InitMorUnique := init_prop_unique
}.

End subcat.
End S_Mods_and_Eqs.

(* Print Assumptions INITIAL_INEQ_REP. *)