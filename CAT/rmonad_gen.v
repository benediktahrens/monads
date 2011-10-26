Require Export CatSem.CAT.functor.
Require Export CatSem.CAT.NT.
Require Export CatSem.CAT.product.
Require Export CatSem.CAT.initial_terminal.
Require Export CatSem.CAT.rmonad.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Section rmonad_gen_hom.

Variables obC obD obC' obD': Type.
Variable morC : obC -> obC -> Type.
Variable morD : obD -> obD -> Type.
Variable morC' : obC' -> obC' -> Type.
Variable morD' : obD' -> obD' -> Type.
Variable C : Cat_struct morC.
Variable D : Cat_struct morD.
Variable C' : Cat_struct morC'.
Variable D' : Cat_struct morD'.

Variable F : Functor C D.
Variable F' : Functor C' D'.

Variable P : RMonad F.
Variable Q : RMonad F'.

(** for a monad hom we need two functors *)

Variable G1 : Functor C C'.
Variable G2 : Functor D D'.

Variable N : NT (CompF G1 F') (CompF F G2).

Section gen_RMonad_Hom_struct.


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


Variable tau : forall (c : obC), morD' (G2 (P c)) (Q (G1 c)).


Class colax_RMonad_Hom_struct := {
  gen_rmonad_hom_rweta : forall c : obC,
         N _ ;; #G2 (rweta c) ;; tau c == rweta (G1 c) ;
  gen_rmonad_hom_rkl : forall (c d : obC) (f : morD (F c) (P d)),
         #G2 (rkleisli f) ;; tau d ==
                  tau c ;; rkleisli (a:=G1 c) (N c ;; #G2 f ;; tau _ )
}.


Section Monad_Hom_NT.

Variable M : colax_RMonad_Hom_struct.

Program Instance colax_RMonad_Hom_NatTrans : 
    NT_struct (F:=CompF (RMFunc P) G2) 
             (G:=CompF G1 (RMFunc Q))
             (fun c => tau c).
Next Obligation.
Proof.
  simpl;
  intros c d f.
  unfold rlift.
  assert (H':=gen_rmonad_hom_rkl (colax_RMonad_Hom_struct := M)).
  rewrite H'.
  apply praecomp.
  apply rkleisli_oid.
  assert (HN:=NTcomm N).
(*
  assert (HN:=trafo_ax (NatTrans:=N)).
*)  
  simpl in *.
  rewrite assoc.
  rewrite FComp.
  assert (H:= gen_rmonad_hom_rweta (colax_RMonad_Hom_struct := M)).
  rewrite <- H.
  repeat rewrite <- assoc.
  rewrite HN.
  apply hom_refl.
Qed.

Definition colax_RMonad_Hom_NT := Build_NT colax_RMonad_Hom_NatTrans.

End Monad_Hom_NT.

End gen_RMonad_Hom_struct.

Record colax_RMonad_Hom := {
(*  Gone : Functor C C' ;
  Gtwo : Functor D D' ;*)
(*  GOGT : NT (CompF G1 F') (CompF F G2) ;*)
  gen_rmonad_hom :> forall (c : obC), morD' (G2 (P c)) (Q (G1 c)) ;
  gen_rmonad_hom_struct :> colax_RMonad_Hom_struct  gen_rmonad_hom
}.


End rmonad_gen_hom.

Existing Instance gen_rmonad_hom_struct.

Section rmonad_hom_id_comp.

Variables obC obD : Type.
Variable morC : obC -> obC -> Type.
Variable morD : obD -> obD -> Type.
Variable C : Cat_struct morC.
Variable D : Cat_struct morD.

Variable F : Functor C D.
Variable P : RMonad F.

Obligation Tactic := cat.

Program Instance NT_i : NT_struct (F:=F O Id C) (G:= Id D O F)
        (fun c => id _ ).

Program Instance colax_RMonad_Hom_id_s : colax_RMonad_Hom_struct 
     (P:=P)(Q:=P)(G1:=Id _ )(G2:=Id _ )
     (Build_NT NT_i)
     (fun c => id _ ).

Definition colax_RMonad_Hom_id :=
    Build_colax_RMonad_Hom colax_RMonad_Hom_id_s.


Variables obC' obD' obC'' obD'': Type.
Variable morC' : obC' -> obC' -> Type.
Variable morD' : obD' -> obD' -> Type.
Variable morC'' : obC'' -> obC'' -> Type.
Variable morD'' : obD'' -> obD'' -> Type.
Variable C' : Cat_struct morC'.
Variable C'' : Cat_struct morC''.
Variable D' : Cat_struct morD'.
Variable D'' : Cat_struct morD''.
Variable F' : Functor C' D'.
Variable F'': Functor C'' D''.

Variable Q : RMonad F'.
Variable R : RMonad F''.

Variable G1S : Functor C C'.
Variable G2S : Functor D D'.
Variable NS : NT (F' O G1S) (G2S O F).

Variable G1T : Functor C' C''.
Variable G2T : Functor D' D''.
Variable NTT : NT (F'' O G1T) (G2T O F').


Variable S : colax_RMonad_Hom P Q NS.
Variable T : colax_RMonad_Hom Q R NTT.

Program Instance NT_c : 
NT_struct (F:=F'' O (G1T O G1S)) (G:=(G2T O G2S) O F)
(fun c => NTT (G1S c) ;; #(G2T) (NS c)).
Next Obligation.
Proof.
  simpl.
  assert (H:=NTcomm NTT).
  assert (H':=NTcomm NS).
  rewrite assoc.
  rewrite <- FComp.
  repeat rewrite <- assoc.
  assert (H2:= H ((G1S) c)(G1S d)(#(G1S) f)). 
  rewrite <- H2.
  repeat rewrite assoc.
  apply praecomp.
  assert (H3:= H' c d f).
  rewrite H3.
  cat.
Qed.

 
Program Instance colax_RMonad_Hom_comp_s : colax_RMonad_Hom_struct
  (P:=P) (Q:=R) (G1:=CompF 
                      (G1S)
                      (G1T)) 
                (G2:=CompF 
                      (G2S) 
                      (G2T))
                (Build_NT NT_c)
                (fun c => #(G2T) (S c) ;; T (G1S c)).
Next Obligation.
Proof.
  assert (H:=gen_rmonad_hom_rweta (colax_RMonad_Hom_struct := T)).
  assert (H':=gen_rmonad_hom_rweta (colax_RMonad_Hom_struct := S)).
  rewrite <- H.
  repeat rewrite  assoc.
  apply praecomp.
  rewrite <- H'.
  repeat rewrite <- assoc.
  apply postcomp.
  rewrite FComp.
  rewrite FComp.
  apply hom_refl.
Qed.
Next Obligation.
Proof.
  assert (H:=gen_rmonad_hom_rkl (colax_RMonad_Hom_struct := T)).
  assert (H':=gen_rmonad_hom_rkl (colax_RMonad_Hom_struct := S)).
  rewrite <- assoc.
  rewrite <- assoc.
  rewrite <- FComp.
  rewrite  H'.
  rewrite FComp.
  repeat rewrite assoc.
  apply praecomp.
  rewrite H.
  apply praecomp.
  repeat rewrite <- assoc.
  rewrite FComp.
  rewrite FComp.
  repeat rewrite assoc.  
  apply hom_refl.
Qed.

Definition colax_RMonad_Hom_comp :=
    Build_colax_RMonad_Hom colax_RMonad_Hom_comp_s.

(** Pullback along S *)

Variable obE : Type.
Variable morE : obE -> obE -> Type.
Variable E : Cat_struct morE.

Variable N : RModule Q E.

Obligation Tactic := idtac.

Program Instance colax_PbRMod_s : 
  RModule_struct P E (fun c : obC => N (G1S c)) := {
   rmkleisli c d f := rmkleisli (RModule_struct := N)
         (NS c ;; #(G2S) f ;; S d)
}.
Next Obligation.
Proof.
  unfold Proper;
  red.
  intros c d f g H.
  rewrite H.
  cat.
Qed.
Next Obligation.
Proof.
  intros c d e f g.
  rewrite (rmklmkl N).
  apply (rmkl_eq N).
  repeat rewrite assoc.
  apply praecomp.
  assert (H:= gen_rmonad_hom_rkl (colax_RMonad_Hom_struct := S)).
  rewrite FComp.
  repeat rewrite assoc.
  apply praecomp.
  repeat rewrite assoc.
  rewrite H.
  repeat rewrite assoc.
  apply hom_refl.
Qed.
Next Obligation.
Proof.
  intro c.
  rewrite <- (rmkleta N).
  apply (rmkl_eq N).
  cat.
  assert (H:= gen_rmonad_hom_rweta (colax_RMonad_Hom_struct := S)).
  simpl in *.
  apply H.
Qed.

Definition colax_PbRMod := Build_RModule colax_PbRMod_s.

End rmonad_hom_id_comp.

Section pb_prod_func_and_Pb_ind_Hom.

Variables obC obD obC' obD': Type.
Variable morC : obC -> obC -> Type.
Variable morD : obD -> obD -> Type.
Variable morC' : obC' -> obC' -> Type.
Variable morD' : obD' -> obD' -> Type.
Variable C : Cat_struct morC.
Variable D : Cat_struct morD.
Variable C' : Cat_struct morC'.
Variable D' : Cat_struct morD'.

Variable F : Functor C D.
Variable F' : Functor C' D'.

Variable P : RMonad F.
Variable Q : RMonad F'.

Variable G1 : Functor C C'.
Variable G2 : Functor D D'.
Variable T : NT (F' O G1) (G2 O F).

Variable f : colax_RMonad_Hom P Q T.


Program Instance F_rmod_s : RModule_struct P _ (fun x => G2 (P x)) := {
   rmkleisli a b f := #G2 (rmkleisli f)
}.
Next Obligation.
Proof.
  intros; simpl.
  unfold Proper;
  red.
  intros x y H.
  apply (functor_map_morphism (rkleisli_oid H)).
Qed.
Next Obligation.
Proof.
  intros; simpl.
  rewrite <- FComp.
  apply (functor_map_morphism (rklkl _ _ _)).
Qed.
Next Obligation.
Proof.
  rmonad.
Qed.

Definition F_rmod := Build_RModule F_rmod_s.

Program Instance colax_PbRMod_ind_Hom_s : RModule_Hom_struct
    (M:=F_rmod) (N:=colax_PbRMod f Q) f.
Next Obligation.
Proof.
  simpl.
  intros c d g.
  rewrite gen_rmonad_hom_rkl.
  cat.
  apply f.
Qed.

Definition colax_PbRMod_ind_Hom := 
   Build_RModule_Hom colax_PbRMod_ind_Hom_s.


Variable obE : Type.
Variable morE : obE -> obE -> Type.
Variable E : Cat_struct morE.
Variable HE : Cat_Prod E.

Variable N N' : RMOD Q E.

Obligation Tactic := cat.

Program Instance colax_PROD_PM_s : RModule_Hom_struct 
        (M:=product (C:=RMOD P E) (colax_PbRMod f N) (colax_PbRMod f N'))
        (N:=colax_PbRMod f (product (C:=RMOD Q E) N N'))
        (fun c => id (product (N (G1 c)) (N' (G1 c)))).

Definition colax_PROD_PM : 
     product (C:=RMOD P E) (colax_PbRMod f N) (colax_PbRMod f N') ---> 
            colax_PbRMod f (product (C:=RMOD Q E) N N') :=
      Build_RModule_Hom colax_PROD_PM_s.

Variable h : N ---> N'.

Obligation Tactic := rmonad.

Program Instance colax_PbRMod_Hom_s : RModule_Hom_struct 
     (M:=colax_PbRMod f N) (N:=colax_PbRMod f N') (fun c => h (G1 c)).

Definition colax_PbRMod_Hom : colax_PbRMod f N ---> colax_PbRMod f N' :=
       Build_RModule_Hom colax_PbRMod_Hom_s.

End pb_prod_func_and_Pb_ind_Hom.

Coercion colax_RMonad_Hom_NatTrans : colax_RMonad_Hom_struct >-> NT_struct.
Coercion colax_RMonad_Hom_NT : colax_RMonad_Hom_struct >-> NT.

Implicit Arguments gen_rmonad_hom_rweta
[obC obD obC' obD' morC morD morC' morD' C D C' D' F
 F' P Q G1 G2 N tau].
Implicit Arguments gen_rmonad_hom_rkl
[obC obD obC' obD' morC morD morC' morD' C D C' D' F
 F' P Q G1 G2 N tau c d].


