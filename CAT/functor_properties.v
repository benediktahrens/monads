Require Export CatSem.CAT.functor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Section full_faithful.

Variables obC obD : Type.
Variable morC : obC -> obC -> Type.
Variable morD : obD -> obD -> Type.
Variables (C : Cat_struct morC) (D : Cat_struct morD).

Class Faithful (F : Functor C D) := {
  faithful : forall c d (f f' : morC c d),
              #F f == #F f' -> f == f'
}.

Class Full (F : Functor C D) := {
  preimg : forall c d (f : morD (F c) (F d)), morC c d;
  preimg_cond : forall c d (f : morD (F c) (F d)), 
                   #F (preimg f) == f
}.

End full_faithful.

Section comp_of_functors.

Variables obC obD obE : Type.
Variable morC : obC -> obC -> Type.
Variable morD : obD -> obD -> Type.
Variable morE : obE -> obE -> Type.
Variables (C : Cat_struct morC) (D : Cat_struct morD) (E : Cat_struct morE).
Variables (F : Functor C D) (G : Functor D E).

Instance comp_faithful (HF : Faithful F) (HG : Faithful G) : 
           Faithful (CompF F G).
Proof.
  intros;
  constructor;
  intros;
  apply (faithful (Faithful:=HF));
  apply (faithful (Faithful:=HG));
  auto.
Qed.

Program Instance comp_full (HF : Full F) (HG : Full G) : 
          Full (CompF F G) := {
  preimg c d f := preimg (preimg (Full := HG) f)
}.
Next Obligation.
Proof.
  intros; simpl;
  repeat rewrite preimg_cond;
  cat.
Qed.


End comp_of_functors.

Existing Instance comp_full.

