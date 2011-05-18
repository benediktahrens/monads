
Require Export Coq.Setoids.Setoid.
Require Export Coq.Classes.SetoidClass.

Require Export Misc.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
(* for coq 8.3 rc1 *)

Unset Automatic Introduction.



(** Categories *)

(** a categorical structure Cat on "obj" and "mor" consists of
   	- a setoid on each mor-set
	- an id mor
	- a composition which is compatible with setoid struct
	- id properties
	- associativity
*)
Class Cat_struct (obj:Type)(mor: obj -> obj -> Type) := {
  mor_oid:> forall a b, Setoid (mor a b);
  id: forall a, mor a a;
  comp: forall {a b c}, 
        mor a b -> mor b c -> mor a c;
  comp_oid:> forall a b c, 
        Proper (equiv ==> equiv ==> equiv) (@comp a b c);
  id_r: forall a b (f: mor a b),
        comp f (id b) == f;
  id_l: forall a b (f: mor a b),
        comp (id a) f == f;
  Assoc: forall a b c d (f: mor a b) 
            (g:mor b c) (h: mor c d),
        comp (comp f g) h == comp f (comp g h)
}.



Notation "x ';;' y" := (comp x y) (at level 50, left associativity).

(** Category *)

Record Cat := {
     obj :> Type;
     mor : obj -> obj -> Type;
     cat_struct :> Cat_struct mor}.

Notation "x ---> y" := (mor x y) (at level 50).

Existing Instance cat_struct.
 

(** Trivial lemmata for easier use in proofs *)

Section cat_lemmata.

Variable ob: Type.
Variable hom: ob -> ob -> Type.
Variable C: Cat_struct hom.
Variables a b: ob.
Variable f: hom a b.

Lemma idr: f ;; id b == f.
Proof. 
  apply (id_r).
Qed.

Lemma idl: id a ;; f == f.
Proof. 
  apply (id_l).
Qed.

Variables (c d: ob) (g: hom b c) (h: hom c d).

Lemma assoc: (f ;; g) ;; h == f ;; (g ;; h).
Proof.
  apply (Assoc).
Qed.

(** helpful lemmata, equivalence properties for the morphisms *)

Lemma hom_refl :  f == f.
Proof.
  apply (Equivalence_Reflexive).
Qed.

Variables f' f'': hom a b.

Lemma hom_sym :  f == f' -> f' == f.
Proof. 
  apply (Equivalence_Symmetric).
Qed.


Lemma hom_trans : 
           f == f' -> f' == f'' -> f == f''.
Proof.
  apply (Equivalence_Transitive).
Qed.


Lemma praecomp (g' : hom b c):
         g == g' ->  f ;; g == f ;; g'.
Proof. 
  intros; repeat rew_set; 
  apply (Equivalence_Reflexive).
Qed.

Lemma postcomp (g' : hom b c):
         g == g' ->  g ;; h == g' ;; h.
Proof. 
  intros; repeat rew_set; 
  apply (Equivalence_Reflexive).
Qed.

End cat_lemmata.


Hint Resolve hom_refl idl idr 
             praecomp postcomp : cat.

Hint Rewrite idl idr : cat.

Ltac cat := simpl in *; 
            intros; autorewrite with cat; 
	    auto with cat;
	    try reflexivity.


(** equality predicate for ALL morphisms of a category *)

Section Equal_hom.

Variable obC:Type.
Variable morC : obC -> obC -> Type.
Variable C: Cat_struct morC.

Inductive Equal_hom (a b: obC) (f : morC a b) :
  forall c d : obC, (morC c d) -> Prop :=
    Build_Equal_hom : forall g : morC a b, f == g -> Equal_hom f g.


Notation "f === g" := (Equal_hom f g) (at level 55).

(** Equal_hom has Equivalence properties *)

Hint Extern 2 (_ === _) => constructor.

Lemma Equal_hom_refl (a b: obC) (f: morC a b) :
            f === f.
Proof. 
   cat. 
Qed.

Lemma Equal_hom_sym (a b c d: obC) (f: morC a b) (g: morC c d):
             f === g -> g === f.
Proof.
  intros;
  match goal with [H : _ === _ |- _ ] => elim H end;
  cat;
  auto using hom_sym.
Qed.

Lemma Equal_hom_trans (a b c d e e': obC)
                    (f: morC a b)
                    (g: morC c d)
                    (h: morC e e'):
       f === g -> g === h -> f === h.
Proof.
  destruct 1;
  destruct 1;
  constructor;
  etransitivity; eauto.
Qed.

End Equal_hom.

Implicit Arguments Equal_hom [obC morC C a b c d].

Notation "f === g" := (Equal_hom f g) (at level 55).




