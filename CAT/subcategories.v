Require Export CatSem.CAT.functor.
Require Export CatSem.CAT.functor_properties.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Automatic Introduction.

Section SubCat_def.

Variable ob: Type.
Variable mor: ob -> ob -> Type.
Variable C: Cat_struct mor.

Section SubCat_struct.

Variable subobP: ob -> Prop.

Definition subob:= {a:ob | subobP a}.

Definition SC_inj_ob (a: subob): ob := proj1_sig a.
Coercion SC_inj_ob : subob >-> ob.


Variable submorP: forall a b: ob, mor a b -> Prop.

Definition submor (a b: ob) := {f : mor a b | submorP f}.

(*
Definition submor_oid (a b: ob) : relation (submor a b) := 
              fun f g => proj1_sig f == proj1_sig g.

Lemma submor_equiv (a b: : Equivale
*)

Definition SC_inj_mor (a b: ob) (f: submor a b) := 
                   proj1_sig f.
Coercion SC_inj_mor: submor >-> mor.


Class SubCat_compat := { 
  (*submor_oid:> forall a b:ob, Proper (equiv ==> equiv) 
                                 (submorP (a:=a) (b:=b));*)
  sub_id: forall a: subob, submorP (id (proj1_sig a));
  sub_comp: forall (a b c:ob) (f: mor a b) (g: mor b c),
                   submorP f -> submorP g -> submorP (f ;; g)
}.

(*
Class SubCat_compat := { 
  (*submor_oid:> forall a b:ob, Proper (equiv ==> equiv) 
                                 (submorP (a:=a) (b:=b));*)
  sub_id: forall a: subob, submorP (id (SC_inj_ob a));
  sub_comp: forall (a b c:ob) (f: mor a b) (g: mor b c),
                   submorP f -> submorP g -> submorP (f ;; g)
}.
*)

Hypothesis SC: SubCat_compat.

(*

Definition SC_ob:= subob. 
Definition SC_mor (a b: subob) := submor a b.

*)

(*
Definition submor_relation (a b: ob) : relation (submor a b) := 
              fun f g => proj1_sig f == proj1_sig g.
*)


Lemma submor_equiv (a b: ob) : @Equivalence (submor a b) 
           (fun f g => proj1_sig f == proj1_sig g).
Proof. 
  intros a b.
  split. 
  unfold Reflexive. 
  intro x; simpl. 
  apply hom_refl.
  
  unfold Symmetric; 
  intros x y; simpl; 
  apply hom_sym.

  unfold Transitive; 
  intros x y z; simpl; 
  apply hom_trans.
Qed.

Definition submor_setoid (a b: ob) := Build_Setoid (submor_equiv a b).
(*
Lemma submor_rel_imp_rel: forall a b (f g : submor a b),
    submor_relation f g -> 
                  proj1_sig f == proj1_sig g.
Proof. 
  unfold submor_relation. 
  auto. 
Qed.
*)

(*
Lemma subidP: forall a: subob, submorP (id (proj1_sig a)).
Proof.  
  intro a. 
  apply sub_id. 
Qed.
*)

Program Definition subid (a: subob) : submor a a :=
  exist _ (id (proj1_sig a)) _ . 
Next Obligation.
Proof. 
  apply sub_id. 
Qed.



Program Definition subcomp (a b c: subob)(f: submor a b) (g: submor b c):
                submor a c :=
        exist _ (proj1_sig f ;; proj1_sig g) _ .
Next Obligation.
Proof. 
  destruct f; 
  destruct g; 
  apply sub_comp; 
  auto. 
Qed.
                           
Obligation Tactic := cat; try apply assoc.

Program Instance SubCat_struct: Cat_struct (obj := subob) submor := {
  mor_oid a b := submor_setoid a b;
  comp a b c f g := subcomp f g;
  id a := subid a
}.
Next Obligation.
Proof. 
  unfold Proper. 
  do 2 red.
  unfold subcomp; 
  simpl.
  intros x y H x0 y0 H0. 
  rewrite H; rewrite H0.
  apply hom_refl.
Qed.

Definition SubCat := Build_Cat SubCat_struct.

End SubCat_struct.

(*
Class SubCat : Type := {
  subobP: ob -> Prop;
  submorP: forall a b: ob, mor a b -> Prop;
  sub_compat :> SubCat_compat subobP submorP;
  subcat_struct :> Cat (SC_mor (subobP:=subobP) submorP)
}.

Definition Cat_from_SubCat (S: SubCat) := @subcat_struct S.
Coercion Cat_from_SubCat: SubCat >-> Cat.
*)

End SubCat_def.




Section Injection_Functor.

Variable ob: Type.
Variable mor: ob -> ob -> Type.
Variable C: Cat_struct mor.

Variable subobP : ob -> Prop.
Variable submorP : forall a b, mor a b -> Prop.
Variable SC: SubCat_compat C subobP submorP.

Program Definition FINJ : Functor (SubCat_struct SC) C := Build_Functor
  (Fobj := fun a => proj1_sig a)
  (Fmor := fun a b f => proj1_sig f) _ .
Next Obligation.
Proof. 
  apply Build_Functor_struct.

  intros a b; 
  unfold Proper. red.
  auto.
    
  cat.
  cat.
Qed.

Program Instance FINJ_Faithful : Faithful FINJ.

Next Obligation.
Proof.
  cat.
Qed.
End Injection_Functor.

(*
Lemma submor_rel_imp_mor_rel: forall a b: ob, forall f g: submor a b,
            f == g -> 
*)
(*Definition FINJ_ob: obj S -> C.*)

(*Program Instance FINJ : Functor S C.
  Next Obligation.
    apply X. 
  Defined.

  Next Obligation.
    apply X.
  Defined.

  Next Obligation.
    Proof. unfold Proper, FINJ_obligation_2. red.
           unfold subob, SC_mor in *. simpl.
           intros x y H. 
           apply (submor_rel_imp_rel). 
           unfold submor_relation. apply H. 
           assumption. simpl. destruct x; destruct y. simpl in *|-*. 
           repeat red in H. unfold SC_mor in H.
           unfold mor_oid in H. simpl in H.
           destruct (Cat_from_SubCat S). simpl in *|-*.
           
           unfold equiv in H. unfold SC_mor in H. simpl in H.
           unfold submor_setoid in H.
           set (CC:= @subcat_struct _ _ _ S).
           destruct CC.
           destruct (mor_oid a b).
           unfold equiv.
           intros x y H. unfold Cat_from_SubCat in  H.
           apply H. unfold  H.
           
           intros x y H; destruct x; destruct y. 
           unfold submor_relation in H.
           simpl.
           apply break_Sig_Prop.



Section injective_functor.
Variables obC obD: Type.
Variables (morC: obC -> obC -> Type) 
          (morD: obD -> obD -> Type).
Variables (C: Cat morC) 
          (D: Cat morD).

Hypothesis C_oid: Setoid obC.
Hypothesis D_oid: Setoid obD.

Variable F: Functor C D.

Definition Finjective := 
    forall a b, F a == F b -> a == b /\
    forall a b (f g: morC a  b), F <- f == F <- g -> f == g.

End injective_functor.


Section injective_functor.

Variables obC obD: Type.
Variables (morC: obC -> obC -> Type) 
          (morD: obD -> obD -> Type).
Variables (C: Cat morC) 
          (D: Cat morD).
Variable F: Functor C D.

Definition Finjective := forall a b (f: morC a b), 
                         forall c d (g: morC c d),
           F <- f === F <- g -> f === g.

Section Inj_on_objects.

Hypothesis H: Finjective.

Lemma Finj_on_objects: forall c c', F c = F c' -> c = c'.
Proof. intros c c' He.
       assert (H0: id (F c) === id (F c')).
       rewrite He. apply Equal_hom_refl.
       assert (H'': id c === id c').
       apply H.
       assert (Hc: F <- id c === id (F c)).
       apply Build_Equal_hom. apply FId.
       assert (Hc': F <- id c' === id (F c')).
       apply Build_Equal_hom. apply FId.
       assert (Hd: F <- id c === id (F c')).
       apply (Equal_hom_trans Hc H0).
       apply (Equal_hom_trans Hd (Equal_hom_sym Hc')).
       apply (Equal_hom_src H'').
Qed.

End Inj_on_objects.

End injective_functor.


Section subcat.

Variable obC: Type.
Variable morC: obC -> obC -> Type.
Variable C: Cat morC. 

Section subcat_struct.

Variable obD: Type.
Variable morD: obD -> obD -> Type.
Variable D: Cat morD.

Class SubCat_struct (F: Functor C D) := {
    Finj: Finjective F
}.

Class SubCat_F := {
     InjF:> Functor C D;
     FinjF:> SubCat_struct InjF
}.

End subcat_struct.

Class SUBCAT := {
   subobj: Type;
   submor: subobj -> subobj -> Type;
   subcat:> Cat submor;
   subF :> SubCat_F subcat
}.


End subcat.

Section IdSubcat.

Variable obC: Type.
Variable morC: obC -> obC -> Type.
Variable C: Cat morC. 

Program Instance IdSubcatF: SubCat_F C C := {
  InjF := Id C
}.
Next Obligation.
  Proof. apply Build_SubCat_struct.
         unfold Finjective. simpl. auto.
  Qed.

Program Instance IdSubcat: SUBCAT C := {
  subobj := obC;
  submor := morC;
  subcat := C;
  subF := IdSubcatF
}.

End IdSubcat.

*)   

     






  
       
     