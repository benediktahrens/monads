Require Export CatSem.CAT.functor.
Require Export CatSem.CAT.NT.
Require Export CatSem.CAT.product.
Require Export CatSem.CAT.initial_terminal.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Section rmonad_def.

Variables obC obD : Type.
Variable morC : obC -> obC -> Type.
Variable morD : obD -> obD -> Type.
Variable C : Cat_struct morC.
Variable D : Cat_struct morD.
Variable F : Functor C D.

Class RMonad_struct (T : obC -> obD) := {
  rweta: forall c: obC, morD (F c) (T c);
  rkleisli: forall a b: obC, morD (F a) (T b) -> morD (T a) (T b);
  rkleisli_oid:> forall a b, 
        Proper (equiv ==> equiv) (rkleisli (a:=a) (b:=b));
  reta_kl : forall a b: obC, forall f : morD (F a) (T b), 
               rweta a ;; rkleisli f == f;
  rkl_eta : forall a, rkleisli (rweta a) == id _;
  rdist: forall a b c (f:morD (F a) (T b)) (g: morD (F b) (T c)),
           rkleisli f ;; rkleisli g == rkleisli (f ;; rkleisli g)
}.

Record RMonad := {
  FR :> obC -> obD ;
  rmonad_struct :> RMonad_struct FR
}.

Existing Instance rmonad_struct.

Section trivial_lemmata.

Variable FF : obC -> obD.
Variable FM : RMonad_struct FF.

Lemma rkl_eq a b (f g : morD (F a) (FF b)) : 
        f == g -> rkleisli f == rkleisli g.
Proof.
  intros a b f g H;
  apply (rkleisli_oid H).
Qed.



Lemma retakl a b (f:morD (F a) (FF b)) : rweta (T:=FF) a ;; rkleisli f == f.
Proof.
  intros;
  apply FM.
Qed.

Lemma rkleta a : rkleisli (rweta a) == id _ .
Proof.
  intros;
  apply FM.
Qed.

Lemma rkleta_eq a f : f == rweta a -> rkleisli f == id _ .
Proof.
  intros a f H.
  rewrite H.
  apply rkleta.
Qed.

Lemma rklkl a b c (f:morD (F a) (FF b)) (g: morD (F b) (FF c)) :
           rkleisli f ;; rkleisli g == rkleisli (f ;; rkleisli g).
Proof.
  intros;
  apply FM.
Qed.

End trivial_lemmata.


Hint Rewrite retakl rkleta rklkl : rmonad.

Hint Rewrite assoc idl idr FId FComp : rmonad.

Hint Resolve idl idr hom_refl hom_sym : rmonad.

Ltac rmonad := intros; autorewrite with rmonad; auto with rmonad.

(** 
        - definition of join, lift
        - fusion laws
*)

Section Defs_and_Facts.

Variable M : RMonad.

Definition rlift : forall a b (f: morC a b), morD (M a) (M b) :=
       fun a b f => rkleisli  (#F f ;; rweta b).

Lemma rlift_eq a b (f g : morC a b) : f == g -> rlift f == rlift g.
Proof.
  intros a b f g H.
  unfold rlift.
  rewrite H.
  cat.
Qed.

Instance rlift_oid a b : Proper (equiv ==> equiv) (rlift (a:=a) (b:=b)).
Proof.
  unfold rlift,Proper;
  red.
  apply rlift_eq.
Qed.

Lemma rlift_id c :
  rlift (id c) == id (M c).
Proof. 
  unfold rlift; rmonad.  
Qed.

Lemma rlift_eq_id a g : g == id a -> rlift g == id (M a).
Proof.
  intros a g H.
  rewrite H.
  apply rlift_id.
Qed.


Lemma rlift_rweta c d (f:morC c d) : 
  rweta _ ;; rlift f == #F f ;; rweta _ .
Proof. 
  unfold rlift; 
  rmonad.
Qed.

Lemma rlift_rlift c d e (f:morC c d) (g:morC d e) :
  rlift f ;; rlift g == rlift (f ;; g).
Proof.
  unfold rlift; 
  rmonad.
Qed.

Lemma rlift_rkleisli c d e (f:morC c d) (g: morD (F d) (M e)) :
  rlift f ;; rkleisli g == rkleisli (#F f ;; g).
Proof.
  unfold rlift; 
  rmonad.
Qed.

Lemma rkleisli_rlift c d e (f:morD (F c) (M d)) (g: morC d e) :
  rkleisli f ;; rlift g == rkleisli (f ;; rlift g).
Proof.
  unfold rlift; 
  rmonad.
Qed.

Hint Rewrite rlift_id rlift_rweta rlift_rlift 
          rlift_rkleisli rkleisli_rlift : rmonad.



Obligation Tactic := rmonad.

Program Instance RMFunc_struct : Functor_struct (Fobj:= M) 
                   (@rlift ).

Canonical Structure RMFunc := Build_Functor RMFunc_struct.


End Defs_and_Facts.


Section RModule.

Variable P : RMonad.

Section RModule_E.

Variable obE : Type.
Variable morE : obE -> obE -> Type.
Variable E : Cat_struct morE.

Class RModule_struct (M : obC -> obE) := {
  rmkleisli: forall c d (f:morD (F c) (P d)), morE (M c) (M d);
  rmkleisli_oid :> forall c d, Proper (equiv ==> equiv) 
                    (rmkleisli (c:=c)(d:=d));
  rmkl_rmkl: forall c d e (f: morD (F c) (P d)) (g:morD (F d) (P e)),
         rmkleisli f ;; rmkleisli g == rmkleisli (f ;; rkleisli g);
  rmkl_rweta: forall c:obC, rmkleisli (rweta c) == id (M c) 
}.

Record RModule := {
  rmodule :> obC -> obE ;
  rmodule_struct :> RModule_struct rmodule
}.

Existing Instance rmodule_struct.

Hint Rewrite @rmkl_rweta : rmonad.
Hint Rewrite @rmkl_rmkl : rmonad.

Section RModule_Func.

Variable M : RModule.

Lemma rmkl_eq c d (f g : morD (F c) (P d)) : f == g -> 
           rmkleisli (RModule_struct := M) f == rmkleisli g.
Proof.
  intros.
  apply (@rmkleisli_oid M).
  auto.
Qed.

Lemma rmkleta : forall c:obC, rmkleisli (rweta c) == id (M c).
Proof.
  apply rmkl_rweta.
Qed.

Lemma rmkleta_id_eq : forall c:obC, forall f, f == rweta _ ->
         rmkleisli f == id (M c).
Proof.
  intros; rew_all; apply rmkleta.
Qed.

Lemma rmklmkl : forall c d e 
    (f: morD (F c) (P d)) (g:morD (F d) (P e)),
  rmkleisli (RModule_struct := M) f ;; 
  rmkleisli g == 
  rmkleisli (f ;; rkleisli g).
Proof.
  apply rmkl_rmkl.
Qed.

Definition rmlift (c d:obC) (f:morC c d) : morE (M c) (M d) := 
        rmkleisli  (#F f ;; rweta d ).

Lemma rmlift_eq c d (f g : morC c d) : f == g -> rmlift f == rmlift g.
Proof.
  unfold rmlift.
  intros c d f g H.
  rewrite H.
  cat.
Qed.

Instance rmlift_oid c d : Proper (equiv ==> equiv) (@rmlift c d) :=
        @rmlift_eq c d.

Obligation Tactic := unfold rmlift; rmonad.

Program Instance RModFunc_struct : Functor_struct (C:=C) (D:=E) (rmlift).


Lemma rmlift_rmkleisli c d e (f: morD (F c) (P d)) (g: morC d e) :
  rmkleisli f ;; rmlift g == rmkleisli (f ;; rlift P g).
Proof.
  unfold rmlift. 
  rmonad.
Qed.

Lemma rmkleisli_rmlift c d e (f : morC c d) (g: morD (F d) (P e)) : 
  rmlift f ;; rmkleisli g == rmkleisli (#F f ;; g).
Proof.
  unfold rmlift; 
  rmonad.
Qed.

Lemma rmlift_rmlift c d e (f: morC c d) (g: morC d e) : 
  rmlift f ;; rmlift g == rmlift (f ;; g).
Proof.
  unfold rmlift; 
  rmonad.
Qed.

End RModule_Func.

Section RModule_Hom.

Variables M N : RModule.

Class RModule_Hom_struct (sig : forall c : obC, morE (M c) (N c)) := {
  rmod_hom_rmkl: forall c d (f: morD (F c) (P d)),
        rmkleisli f ;; sig d == sig c ;; rmkleisli f
}. 

Record RModule_Hom := {
  rmodule_hom:> forall x, morE (M x) (N x);
  rmodule_hom_struct :> RModule_Hom_struct rmodule_hom
}.

Existing Instance rmodule_hom_struct.

Section lemmata.

Variable S : RModule_Hom.

Lemma rmhom_rmkl : forall c d (f: morD (F c) (P d)),
        rmkleisli f ;; S d == S c ;; rmkleisli f.
Proof.
  apply rmod_hom_rmkl.
Qed.

End lemmata.

End RModule_Hom.

Existing Instance rmodule_hom_struct.

Section RMOD_id_comp.

Variable M : RModule.

Obligation Tactic := rmonad.

Program Instance RMOD_id_struct : 
    RModule_Hom_struct (M:=M) (N:=M) (fun _ => id _ ).

Canonical Structure RMOD_id := Build_RModule_Hom RMOD_id_struct.

Variables N K : RModule.

Variable S : RModule_Hom M N.
Variable T : RModule_Hom N K.

Program Instance RMOD_comp_struct : 
    RModule_Hom_struct (M:=M) (N:=K) (fun c => S c ;; T c).
Next Obligation.
Proof.
  rewrite <- assoc.
  rewrite <- assoc.
  rewrite (rmod_hom_rmkl);
    try apply S.
  repeat rewrite assoc.
  apply praecomp.
  rewrite rmod_hom_rmkl;
    try apply T.
  cat.
Qed.

Canonical Structure RMOD_comp := Build_RModule_Hom RMOD_comp_struct.

End RMOD_id_comp.

Lemma RMod_eq (A B : RModule) : Equivalence (A:=RModule_Hom A B)
      (fun M N => forall c, M c == N c).
Proof.
  intros A B.
  constructor.
  unfold Reflexive.
  cat.
  unfold Symmetric.
  intros.
  apply hom_sym. 
  auto.
  unfold Transitive.
  intros x y z H H' c.
  apply hom_trans with (y c);
  auto.
Qed.

Instance RMod_oid A B : Setoid _ := Build_Setoid (RMod_eq A B).

Instance RMod_comp_oid : 
forall a b c : RModule, Proper (equiv ==> equiv ==> equiv) 
    (RMOD_comp (M:=a)(N:=b)(K:=c)).
Proof.
  intros R S T.
  unfold Proper;
  do 2 red.
  simpl.
  intros x y H x0 y0 H0 t .
  rewrite H.
  rewrite H0.
  cat.
Qed.

Obligation Tactic := simpl; intros; try rewrite assoc; cat.

Program Instance RMOD_struct : Cat_struct RModule_Hom := {
  id := RMOD_id ;
  comp := RMOD_comp ;
  mor_oid := RMod_oid
}.

Canonical Structure RMOD := Build_Cat RMOD_struct.

(** constant module *)

Section const_rmod.

Variable e : obE.


Instance const_rmod_oid c c' : 
   Proper (equiv ==> equiv) (fun _ : morD (F c) (P c') => id e).
Proof.
  unfold Proper;
  red; cat.
Qed.


Obligation Tactic :=  try apply const_rmod_oid; cat.

Program Instance Const_RMod_struct : 
      RModule_struct (fun c => e) := {
  rmkleisli a b f := id _
}.

Canonical Structure Const_RMod : RMOD := 
       Build_RModule Const_RMod_struct.

End const_rmod.

Section terminal.

Variable T : Terminal E.

Definition RMOD_Term : RMOD := Const_RMod Term.

Hint Resolve TermMorUnique : cat.

Program Instance RMOD_TermMor_struct (A: RMOD) : 
      RModule_Hom_struct (M:=A) (N:=RMOD_Term) 
                    (fun x => TermMor (A x)) .

Canonical Structure RMOD_TermMor (A: RMOD) : A ---> RMOD_Term := 
          Build_RModule_Hom (RMOD_TermMor_struct A).


Program Instance RMOD_Terminal : Terminal (RMOD) := {
  Term := RMOD_Term;
  TermMor A := RMOD_TermMor A
}.

End terminal.

Existing Instance RMOD_Terminal.



Section product.

Variable EP : Cat_Prod E.

Section product_prep.

Variable M N: RMOD.

Notation "a 'x' b" := (product a b) (at level 30).
Notation "a 'X' b" := (product_mor _ a b) (at level 30).


Program Instance Prod_RMod_struct: 
     RModule_struct (fun a => M a x N a) := {
   rmkleisli c d f :=  (rmkleisli f) X (rmkleisli f)
}.
Next Obligation.
Proof.
  unfold Proper; red.
  intros z y HH.
  unfold product_mor.
  apply prod_mor_oid;
  rewrite HH; cat.
Qed.
Next Obligation.
Proof.
  rewrite <- product_mor_product_mor.
  rmonad.
Qed.
Next Obligation.
Proof.
  repeat rewrite rmkl_rweta.
  apply product_mor_id.
Qed.

Canonical Structure Prod_RMod : RMOD := Build_RModule Prod_RMod_struct.

Program Instance RMod_prl_struct : RModule_Hom_struct 
     (M:=Prod_RMod)(N:=M)(fun c => prl _ _ ).
Next Obligation.
Proof. 
  unfold product_mor.
  rewrite prod_prl.
  cat.
Qed.

Canonical Structure Mod_prl : Prod_RMod ---> M := 
         Build_RModule_Hom RMod_prl_struct.

Program Instance Mod_prr_struct : 
     RModule_Hom_struct (M:=Prod_RMod)(N:=N)  
        (fun c => prr _ _ ).
Next Obligation.
Proof.
  unfold product_mor.
  rewrite prod_prr.
  cat.
Qed.

Canonical Structure Mod_prr : Prod_RMod ---> N := 
        Build_RModule_Hom Mod_prr_struct.


Section Mod_prod_mor.

Variable K: RMOD.
Variables (S : K ---> M) 
          (T : K ---> N).

Program Instance Mod_prod_mor_struct : RModule_Hom_struct 
       (M:=K) (N:=Prod_RMod) (fun c => prod_mor (S c) (T c)).
Next Obligation.
Proof.
  rewrite prod_mor_product_mor.
  apply prod_mor_unique.
  repeat rewrite assoc.
  rewrite prod_prl.
  rewrite prod_prr.
  split;
  rmonad; try apply S;
      try apply T.
Qed.

Canonical Structure Mod_Prod_mor : K ---> Prod_RMod := 
          Build_RModule_Hom Mod_prod_mor_struct.

End Mod_prod_mor.

End product_prep.

Program Instance RMOD_PROD : Cat_Prod (RMOD) := {
  product M N := Prod_RMod M N;
  prl M N := Mod_prl M N;
  prr M N := Mod_prr M N;
  prod_mor a c d f g := Mod_Prod_mor f g
}.
Next Obligation.
Proof.
  unfold Proper; do 2 red.
  unfold Mod_Prod_mor;
  simpl.
  intros r s H1 r' s' H' t.
  rewrite H1.
  rewrite H'.
  cat.
Qed.
Next Obligation.
Proof.
  unfold
     Mod_Prod_mor in *;
  simpl in *.
  cat.
  apply prod_mor_unique.
  destruct H.
  cat.
Qed.

End product.

End RModule_E.

(** tautological module *)

Existing Instance rmonad_struct.
Existing Instance rkleisli_oid.

Obligation Tactic := rmonad; try apply rkleisli_oid.

Program Instance Taut_RMod_struct : RModule_struct D (P) := {
  rmkleisli := rkleisli
}.

Canonical Structure Taut_RMod := Build_RModule Taut_RMod_struct.

End RModule.
(*
Existing Instance rmonad_struct.
(*Existing Instance rmonad_hom_struct.*)
Existing Instance rmodule_struct.
Existing Instance rmodule_hom_struct.


Hint Rewrite retakl rkleta rklkl : rmonad.
Hint Rewrite assoc idl idr FId FComp : rmonad.
Hint Resolve idl idr hom_refl hom_sym : rmonad.

(*Hint Rewrite rmon_hom_rweta : rmonad.*)
(*Hint Resolve rmon_hom_rkl : rmonad.*)
(*Hint Rewrite rmon_hom_rkl : rmonad.*)

Hint Rewrite @rmkl_rweta : rmonad.
Hint Rewrite @rmkl_rmkl : rmonad.
*)

End rmonad_def.

Coercion Taut_RMod : RMonad >-> RModule.

Hint Rewrite retakl rkleta rklkl rmkleta rmklmkl rmhom_rmkl : rmonad.
Hint Rewrite assoc idl idr FId FComp : rmonad.
Hint Resolve idl idr hom_refl hom_sym : rmonad.
(*Hint Rewrite rmon_hom_rweta : rmonad.*)
(*Hint Resolve rmon_hom_rkl rmhom_rmkl : rmonad.*)
(*Hint Rewrite rmon_hom_rkl : rmonad.*)
Ltac rmonad := simpl in *; intros; 
      autorewrite with rmonad; auto with rmonad.

Existing Instance rmonad_struct.
(*Existing Instance rmonad_hom_struct.*)
Existing Instance rmodule_struct.
Existing Instance rmodule_hom_struct.
Existing Instance RMOD_Terminal.
Existing Instance RMOD_PROD.

Implicit Arguments rmod_hom_rmkl 
  [obC obD morC C morD D F P obE morE E M N c d sig].

(*

Section rmonad_hom.

Variables obC obD obC' obD': Type.
Variable morC : obC -> obC -> Type.
Variable morD : obD -> obD -> Type.
Variable morC' : obC' -> obC' -> Type.
Variable morD' : obD' -> obD' -> Type.
Variable C : Cat morC.
Variable D : Cat morD.
Variable C' : Cat morC'.
Variable D' : Cat morD'.
Variable F : Functor C D.
Variable F' : Functor C' D'.

Variable P : RMonad F.
Variable Q : RMonad F'.

(** for a monad hom we need two functors *)

Variable G1 : Functor C C'.
Variable G2 : Functor D D'.

(** and a compatibility natural transformation *)
(** this is a weak form of a commutativity property 
    for the 4 functors involved

           F
    C -----------> D
    |              |
 G1 |              | G2
    |              |
    v              v
    C' ----------> D'
           F'

*)

Variable N : NT (CompF G1 F') (CompF F G2).

Variable tau : forall (c : obC), morD' (G2 (P c)) (Q (G1 c)).

Class RMonad_Hom_struct := {
    rmonad_hom_rweta : forall c : obC,
         N _ ;; #G2 (rweta c) ;; tau c == rweta (G1 c) ;
    rmonad_hom_rkl : forall (c d : obC) (f : morD (F c) (P d)),
         #G2 (rkleisli f) ;; tau d ==
                  tau c ;; rkleisli (a:=G1 c) (N c ;; #G2 f ;; tau _ )
}.



Section Monad_Hom_NT.


Variable M : RMonad_Hom_struct.

Program Instance Monad_Hom_NatTrans : 
    NatTrans (F:=CompF (RMFunc P) G2) 
             (G:=CompF G1 (RMFunc Q))
             (fun c => tau c).
Next Obligation.
Proof.
  unfold rlift.
  assert (H':=rmonad_hom_rkl (RMonad_Hom_struct := M)).
  rewrite H'.
  apply praecomp.
  apply kleisli_oid.
  rewrite assoc.
  rewrite FComp.
  
  assert (H:= rmonad_hom_rweta (RMonad_Hom_struct := M)).
  rewrite <- FComp.
  rewrite <- assoc.
  
  
  cat.
  rewrite <- assoc.
  rewrite assoc.
  
  rewrite <- H.
  rew
  rewrite <- H.
  cat.
Qed.

Canonical Structure Monad_Hom_NT := Build_NT Monad_Hom_NatTrans.



End rmonad_hom.
*)









