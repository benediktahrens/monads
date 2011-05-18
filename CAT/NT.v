
Require Export CatSem.CAT.functor.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Automatic Introduction.

Section NT_def.

Variables obC obD: Type.
Variable morC : obC -> obC -> Type.
Variable morD : obD -> obD -> Type.
Variable C: Cat_struct morC.
Variable D: Cat_struct morD.

Definition trafo_comm (F G: Functor C D)
          (alpha: forall c:obC, morD (F c) (G c)):=
     forall c d f, alpha c ;; #G f == #F f ;; alpha d.

Class NT_struct {F G: Functor C D} 
         (alpha: forall c: obC, morD (F  c) (G  c)) := {
  trafo_ax: forall c d f, alpha c ;; #G f == #F f ;; alpha d
}.

Record NT (F G: Functor C D) := {
  trafo:> forall c: obC, morD (F c) (G c);
  nt_struct:> NT_struct trafo
}.


Existing Instance nt_struct.

Lemma NTcomm (F G: Functor C D)(alpha: forall c, morD (F c) (G c))
         (H:NT_struct alpha)
         (c d: obC)(f: morC c d):
       alpha c ;; #G f == #F f ;; alpha d.
Proof. 
  intros F G a c d f.
  apply trafo_ax.
Qed.



Variables F G: Functor C D.

Definition EXT_NT : relation (NT F G) :=
       fun a b => forall c: obC, a c == b c.

Lemma EXT_NT_refl: Reflexive (EXT_NT).
Proof.
  unfold Reflexive.
  intros  x c. 
  cat.
Qed.

Lemma EXT_NT_sym: Symmetric EXT_NT.
Proof. 
  unfold Symmetric.
  intros x y H c. 
  apply hom_sym.
  apply H.
Qed.

Lemma EXT_NT_trans: Transitive EXT_NT.
Proof. 
  unfold Transitive.
  intros x y z H H' c.
  apply hom_trans with (y c);
  auto.
Qed.

Lemma eq_NT_equiv : @Equivalence (NT F G) 
         (fun a b => forall c: obC, a c == b c).
Proof.
  split. 
  assert (H:=EXT_NT_refl);
  auto.
  assert (H:=EXT_NT_sym);
  auto.
  assert (H:=EXT_NT_trans);
  auto.
Qed.


Definition EXT_NT_oid := Build_Setoid eq_NT_equiv.

End NT_def.

Existing Instance nt_struct.

(*
Notation "a =NT= b" := (eq_NT1 a b) (at level 80).
*)

(** the vertical identity NT *)

Section VIDNT.

Variables obC obD: Type.
Variable morC : obC -> obC -> Type.
Variable morD : obD -> obD -> Type.
Variable C: Cat_struct morC.
Variable D: Cat_struct morD.
Variable F: Functor C D.

Program Definition vidNT : NT F F := Build_NT
  (trafo := fun c => id (F c)) _ .
Next Obligation.
Proof. 
  apply Build_NT_struct.
  cat.
Qed.

End VIDNT.

Section vcompNT.
(* Variables C D: Category. *)
Variables obC obD: Type.
Variable morC : obC -> obC -> Type.
Variable morD : obD -> obD -> Type.
Variable C: Cat_struct morC.
Variable D: Cat_struct morD.

Variables F G H: Functor C D.
Variables (a:NT F G) (b:NT G H).

Definition vcompNT1 := fun c => a c ;; b c.

Lemma vcompNT1_ax: forall c d f, 
          vcompNT1 c ;; #H f == #F f ;; vcompNT1 d.
Proof. 
  intros c d f.
  unfold vcompNT1.
  rewrite assoc.
  rewrite (NTcomm b).
  rewrite <- assoc.
  rewrite (NTcomm a).
  rewrite assoc.
  apply hom_refl.
Qed.

Definition vcompNT := Build_NT (Build_NT_struct vcompNT1_ax).

End vcompNT.


Notation "a # b" := (vcompNT b a) (at level 50, left associativity).

(** lemmata about vertical composition *)
Section vcompNT_lemmata.
Variables obC obD: Type.
Variable morC : obC -> obC -> Type.
Variable morD : obD -> obD -> Type.
Variable C: Cat_struct morC.
Variable D: Cat_struct morD.

Variable F G: Functor C D.
Variable alpha: NT F G.

Notation "a =NT= b" := (EXT_NT a b) (at level 80).

Lemma vidNTl: alpha # vidNT F =NT= alpha.
Proof. 
  unfold EXT_NT, vidNT. 
  intro c; simpl.
  unfold vcompNT1; 
  simpl. apply idl.
Qed.

Lemma vidNTr: vidNT G # alpha =NT= alpha.
Proof.
  unfold EXT_NT, vidNT. 
  intro c; simpl.
  unfold vcompNT1; simpl. 
  apply idr.
Qed.

Variables H J: Functor C D.
Variable beta: NT G H.
Variable gamma: NT H J.

Lemma vcompNT_assoc:  
     gamma # (beta # alpha) =NT= (gamma # beta) # alpha.
Proof. 
  unfold EXT_NT, vcompNT. 
  simpl.
  unfold vcompNT1; simpl.
  intro c; apply assoc.
Qed.

End vcompNT_lemmata.
