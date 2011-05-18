Require Export CatSem.CAT.NT.
Require Export CatSem.CAT.monic_epi.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Automatic Introduction.

Section Nat_Iso_def.

Variables obC obD: Type.
Variable morC : obC -> obC -> Type.
Variable morD : obD -> obD -> Type.
Variable C: Cat_struct morC.
Variable D: Cat_struct morD.
Variables F G: Functor C D.

Section struct_def.

Variable alpha: NT F G.
(*
Class NISO_struct := {
  inv: forall c, morD (G c) (F c);
  inv_right: forall c, alpha c ;; inv c == id _;
  inv_left: forall c, inv c ;; alpha c == id _
}.
*)
Class NISO_struct := {
  NT_inv :> forall c, Invertible (alpha c)
}.


End struct_def.

Record NISO := {
  tra :> NT F G;
  niso_struct :> NISO_struct tra
}.

End Nat_Iso_def.

Existing Instance niso_struct.


Section Nat_Iso_gives_NT.

Notation "-- f" := (inverse f) (at level 30).

Variables obC obD: Type.
Variable morC : obC -> obC -> Type.
Variable morD : obD -> obD -> Type.
Variable C: Cat_struct morC.
Variable D: Cat_struct morD.
Variables F G: Functor C D.

Variable alpha: NISO F G.

Program Definition NTinv: NT G F := Build_NT
    (trafo := fun c => -- (alpha c)) _ .
Next Obligation.
Proof.
  constructor.
  intros c d f.
  destruct alpha as [al NIS]. simpl.
  destruct NIS as [INV]. 
  simpl in *|-*.
  set (H := trafo_ax (NT_struct := al)).
  assert (H': --al c ;; (al c ;; #G f) == 
                  --al c ;; (#F f ;; al d)).
  apply praecomp. auto.
  assert (H'': (--al c ;; (al c ;; #G f)) ;; --al d == 
                  (--al c ;; (#F f ;; al d)) ;; --al d).
  apply postcomp. auto.
  repeat rewrite assoc in H''.
  rewrite inv_post in H''.
  repeat rewrite <- assoc in H''.
  rewrite inv_prae in H''.
  rewrite idl in H''.
  rewrite idr in H''.
  apply hom_sym. auto.
Qed.
 

(*
Program Definition NTinv: NT G F := Build_NT
     (trafo := @inv _ _ _ _ _ _ F G alpha (niso_struct alpha) ) _ .
Next Obligation.
Proof. 
  apply Build_NatTrans.
  unfold trafo_comm, inv.
  intros c d f.        
  destruct alpha as [al da]. simpl.
  destruct da as [invv r l]. simpl in *|-*.
  destruct al as [al H]. simpl in *|-*.
  destruct H as [H].
  unfold trafo_comm in H. simpl in H.
  assert (H': invv c ;; (al c ;; !G f) == 
                  invv c ;; (!F f ;; al d)).
  apply praecomp. auto.
  assert (H'': (invv c ;; (al c ;; !G f)) ;; invv d == 
                  (invv c ;; (!F f ;; al d)) ;; invv d).
  apply postcomp. auto.
  repeat rewrite assoc in H''.
  rewrite r in H''.
  repeat rewrite <- assoc in H''.
  rewrite l in H''.
  rewrite idl in H''.
  rewrite idr in H''.
  apply hom_sym. auto.
Qed.
*)
End Nat_Iso_gives_NT.


(*
Section ISO.

Variables obC obD: Type.
Variable morC : obC -> obC -> Type.
Variable morD : obD -> obD -> Type.
Variable C: Cat morC.
Variable D: Cat morD.
Variables F G: Functor C D.

Class 

*)



























