Require Export CatSem.CAT.rmonad_gen_type_po.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Automatic Introduction.

(* contains a "smaller" version of the eq fibre transport 
    morphism of modules
*)

Section gen_pb_fib_and_eq.

Variables obC obD obC' obD': Type.
Variable morC : obC -> obC -> Type.
Variable morD : obD -> obD -> Type.
Variable morC' : obC' -> obC' -> Type.
Variable morD' : obD' -> obD' -> Type.
(*Variable C : Cat morC.
Variable D : Cat morD.*)
Variable C' : Cat_struct morC'.
Variable D' : Cat_struct morD'.

(*Variable F : Functor C D.*)
Variable F' : Functor C' D'.

(*Variable P : RMonad F.*)
Variable Q : RMonad F'.

(** for a monad hom we need two functors *)

(*Variable G1 : Functor C C'.
Variable G2 : Functor D D'.
*)
(*Variable N : NT (CompF G1 F') (CompF F G2).*)

(*Variable h : gen_RMonad_Hom P Q N.*)

Variable T : Type.

Variables u t : T.

Variable M : RMOD Q (IPO T).

Hypothesis H : u = t.

Definition bla c:
(FIB_RMOD Q u) M c -> ((FIB_RMOD Q t) M) c.
simpl.
intros c s.
rewrite <- H.
exact s.
Defined.
(*
Obligation Tactic := idtac.
*)
Program Instance eq_rect_small_po_s c:
 PO_mor_struct
 (a:=(FIB_RMOD Q u) M c) (b:=(FIB_RMOD Q t) M c)
 (fun (s:M c u) => 
eq_rect u (fun t : T => (M c) t)  s t H).
Next Obligation.
Proof.
  subst.
  simpl.
  auto.
Qed.

Definition eq_rect_small_po c:=Build_PO_mor (eq_rect_small_po_s c).

Program Instance FIB_RMOD_small_eq_s : RModule_Hom_struct 
 (M:=FIB_RMOD _ u M) (N:=FIB_RMOD _ t M)
 eq_rect_small_po.
Next Obligation.
Proof.
  subst.
  simpl.
  auto.
Qed.


Definition FIB_RMOD_small_eq :
    FIB_RMOD _ u M ---> FIB_RMOD _ t M := 
 Build_RModule_Hom FIB_RMOD_small_eq_s.

End gen_pb_fib_and_eq.
