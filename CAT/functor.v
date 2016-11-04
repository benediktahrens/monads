Require Export CatSem.CAT.category_hom_transport.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

(** Func - the Functorial structure on Fobj and Fmor *)
Section Functors.

Variables obC obD:Type.
Variable morC : obC -> obC -> Type.
Variable morD : obD -> obD -> Type.


Class  Functor_struct {C : Cat_struct morC} {D : Cat_struct morD}
   (Fobj: obC -> obD) 
   (Fmor: forall a b: obC, morC a b -> morD (Fobj a) (Fobj b)) := {
  
  functor_map_morphism :> forall a b,
          Proper (equiv ==> equiv)(Fmor a b) ;
  preserve_ident: forall a, 
            Fmor a a (id a) == id (Fobj a);
  preserve_comp : forall a b c (f : morC a b) (g : morC b c), 
    Fmor a c (f ;; g) == (Fmor a b f) ;; Fmor b c g 
}.

(** packaging of a functor *)

Variable C: Cat_struct morC.
Variable D: Cat_struct morD.

Record Functor := {
  Fobj :> obC -> obD;
  Fmor : forall a b: obC, morC a b -> morD (Fobj a) (Fobj b);
  Func_struct :> Functor_struct Fmor
}.

Existing Instance Func_struct.

Variable F: Functor.

Notation "#" := (Fmor) (at level 40).

Lemma Foid a b (f g: morC a b) : 
        f == g -> #F f == #F g.
Proof.
  intros.
  rewrite H.
  cat.
Qed.

Lemma FId a : #F (id a)  == id (F a).
Proof.
  apply preserve_ident. 
Qed.

Lemma FComp a b c (f: morC a b) (g: morC b c) : 
        #F (f ;; g) == #F f ;; #F g.
Proof. 
  apply preserve_comp. 
Qed.


End Functors.

Existing Instance Func_struct.


(*
Notation "F ` a" := (Fobj F a) (at level 50).
*)

Notation "#" := (Fmor) (at level 40).


(** easier access to functor properties *)

Hint Resolve FComp FId : cat.
Hint Rewrite FComp FId : cat.


Section eqFunctor.
Variables obC obD: Type.
Variable morC: obC -> obC -> Type.
Variable morD: obD -> obD -> Type.
Variable C: Cat_struct morC.
Variable D: Cat_struct morD.

(** EXTensional heterogeneous equality on functors is an 
       equivalence relation *)

(** later we'll show that F and G are equal 
 if they are extensionally equal on the morphisms
       wrt to Equal_hom, the heterogeneous equality on morphisms *)

Definition EXT_Functor: relation (Functor C D) :=
     fun F G => forall a b: obC, forall f: morC a b,
                  #F f === #G f.

Lemma eq_Functor_equiv: @Equivalence (Functor C D)
         (fun F G => forall a b: obC, forall f: morC a b,
                  #F f === #G f). 
Proof. 
  split.
  unfold Reflexive. 
  intros.
  apply Equal_hom_refl.
  unfold Symmetric. 
  intros.
  apply Equal_hom_sym; auto.
  unfold Transitive. 
  intros x y z H H' a b f.
  simpl. 
  apply (@Equal_hom_trans _ _ _ _ _ _ _ _ _ 
          (#x f)
             (#y f)
             (#z f)); auto.
Qed.

Definition EXT_Functor_oid := Build_Setoid eq_Functor_equiv.


End eqFunctor.




(** first example of a functor: the Identity Functor *)

Section Id_Comp_Functor.

Variable obC : Type.
Variable morC : obC -> obC -> Type.
Variable C: Cat_struct morC.

Obligation Tactic := cat.

Program Instance Id_Fs : Functor_struct
   (Fobj := fun x => x) (fun a b f => f).
Next Obligation.
Proof.
  unfold Proper;
  red; auto.
Qed.

Definition Id : Functor C C := Build_Functor Id_Fs.
  

(** Composition of functors *)

Variables obD obE: Type.
Variable morD: obD -> obD -> Type.
Variable morE: obE -> obE -> Type.
Variable D: Cat_struct morD.
Variable E: Cat_struct morE.

Variables (F : Functor C D) (G: Functor D E).

Instance Comp_functor_map_morphism: forall a b, 
             Proper (equiv ==> equiv)(fun x: morC a b => #G (#F x)).
Proof. 
  intros a b.
  unfold Proper.
  red.
  intros x y H;
  rewrite H.
  cat.
Qed.

Lemma Comp_preserve_ident: forall a, 
           #G (#F (id a)) == id (G (F a)).
Proof. 
  cat. 
Qed.

Lemma Comp_preserve_comp : forall a b c (f : morC a b) 
           (g : morC b c), 
    #G (#F (f ;; g)) == #G (#F f) ;; #G (#F g).
Proof. 
  cat.
Qed.

Obligation Tactic := cat.

Program Instance CompFs : Functor_struct
  (Fobj := fun x => G  (F  x))
  (fun a b => fun x: morC a b => #G (#F x)).
(* NO OBLIGATION
Next Obligation.
Proof.
  apply Comp_functor_map_morphism.
Qed.
*)

Definition CompF := Build_Functor CompFs.

End Id_Comp_Functor.

(** Equivalence on Functors *)

Existing Instance EXT_Functor_oid.


(** Properties of Composition and Id wrt "eq_Functor", our 
     equivalence on Functors *)

Section Functor_Comp_Id.

Variable obC : Type.
Variable morC : obC -> obC -> Type.
Variable C: Cat_struct morC.
Variables obD : Type.
Variable morD: obD -> obD -> Type.
Variable D: Cat_struct morD.

Lemma IdF_unit_l (F : Functor C D) : CompF (Id C) F == F. 
Proof. 
  simpl.
  intros F a b f. 
  apply Build_Equal_hom.
  cat.
Qed.

Lemma IdF_unit_r (F : Functor C D) :  CompF F (Id D) ==  F.
Proof. 
  simpl.
  intros F a b f. 
  apply Build_Equal_hom.
  cat.
Qed.

Variables obE obE' : Type.
Variable morE : obE -> obE -> Type.
Variable morE' : obE' -> obE' -> Type.
Variable E : Cat_struct morE.
Variable E' : Cat_struct morE'.
Variables (F : Functor C D)(G: Functor D E) (H: Functor E E').

Lemma CompF_assoc : CompF F  (CompF G H) == CompF (CompF F G)  H.
Proof. 
  simpl.
  intros a b f. 
  apply Build_Equal_hom.
  cat.
Qed.

(*
Lemma F_equal_helper (*F: Functor C D*) : forall a b (f g: morC a b), 
             f == g ->  #F f === #F g.
Proof. 
  intros a b f g H'.
  apply Build_Equal_hom.
  rewrite H'.
  cat.
Qed.
*)

Lemma F_equal_helper2 (F' G': Functor C D): forall a b (f g: morC a b),
           f == g -> 
      (forall x y (r: morC x y), #F' r === #G' r) -> 
                    #F' f === #G' g.
Proof. 
  intros F' G' a b f g H1 H2.
  apply (@Equal_hom_trans _ _ _ _ _ _ _ _ _ 
                       (#F' f) (#G' f) (#G' g)).
    apply H2.
    
    apply Build_Equal_hom.
    rewrite H1.
    cat.
Qed.

Lemma F_equal_helper3 (*F' : Functor C D*): 
     forall a b a' b' (f: morC a b) (g:morC a' b'),
          f === g -> #F f === #F g.
Proof. 
  intros a b a' b' f g H'.
  assert (Ha:= Equal_hom_src H'). 
  assert (Hb:= Equal_hom_tgt H').
  inversion Ha as [ha].
  inversion Hb as [hb].
  generalize dependent f. 
  subst.
  intros.
  assert (H1:= Equal_hom_imp_setoideq2 H').
  constructor.
  rewrite H1. 
  cat.
Qed.
       
End Functor_Comp_Id.

Obligation Tactic := idtac.

Program Instance Cat_CAT: Cat_struct (fun C D : Cat => Functor C D) := {
   mor_oid C D := EXT_Functor_oid C D;
   id C := Id C;
   comp a b c F G := CompF F G
}.
Next Obligation.
Proof.
  intros C D E.
  unfold Proper; repeat red; simpl.
  intros F G H K L H' x y f.
  apply (@Equal_hom_trans _ _ _ _ _ _ _ _  _ 
    (#K (#F f))
    (#K (#G f))
    (#L (#G f)) ); auto.
  intros;
  apply F_equal_helper3. 
  auto.
Qed.
Next Obligation.
Proof.
  intros C D F.
  assert (H:=IdF_unit_r).
  simpl in *.
  apply H.
Qed.
Next Obligation.
Proof.
  intros C D F.
  assert (H:=IdF_unit_l).
  simpl in *.
  apply H.
Qed.
Next Obligation.
Proof. 
  intros a b c d f g h.
  apply (CompF_assoc f g h).
Qed.

Existing Instance Cat_CAT.
Notation "G 'O' F" := (CompF F G) (at level 70).



           





















