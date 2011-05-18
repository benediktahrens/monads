Require Export CatSem.CAT.category.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Section Directed_Graph.

Variable ob arr: Type.
Variable arr_oid: Setoid arr.

Class Graph_struct := {
   dom: arr -> ob;
   cod: arr -> ob
}.

End Directed_Graph.

Class Graph := {
  O : Type;
  A : Type;
  A_oid:> Setoid A;
  graph_struct:> Graph_struct O A
}.

Definition Graph_ob (G: Graph) := @O G.
Coercion Graph_ob: Graph >-> Sortclass.

Definition Graph_arr (G: Graph) := @A G.
Coercion Graph_arr: Graph >-> Sortclass.

Section Graph_Morphisms.

Variables G1 G2: Graph.

Class Graph_Morphism := {
  D_O: G1 -> G2;
  D_A: @A G1 -> @A G2;
  D_A_oid:> Proper (equiv ==> equiv) D_A;
  dom_compat: forall f, dom (D_A f) = D_O (dom f);
  cod_compat: forall f, cod (D_A f) = D_O (cod f)
}.

Definition D_OG (G:Graph_Morphism) := @D_O G.
Coercion D_OG : Graph_Morphism >-> Funclass.

Definition D_AG (G:Graph_Morphism) := @D_A G.
Coercion D_AG : Graph_Morphism >-> Funclass.

Lemma dom_com:forall G:Graph_Morphism, forall f,
             dom (D_A f) = D_O (dom f).
Proof. intros G f. apply dom_compat. Qed.

Lemma cod_com:forall G:Graph_Morphism, forall f,
             cod (D_A f) = D_O (cod f).
Proof. intros G f. apply cod_compat. Qed.

End Graph_Morphisms.

Implicit Arguments D_A [G1 G2].
Implicit Arguments D_O [G1 G2].

Section Graph_Morphism_equiv.

Variables G1 G2 : Graph.

Definition eq_Graph_Morphism1 : relation (Graph_Morphism G1 G2) :=
      fun F G => (forall x, F x = G x) /\ 
                 (forall f, D_A F f == D_A G f).


Lemma eq_Graph_Morphism_equiv: Equivalence eq_Graph_Morphism1.
Proof. unfold eq_Graph_Morphism1.
  split.
    unfold Reflexive. 
    intro x; split; intro f; auto;
    apply A_oid.
    
    unfold Symmetric. 
    intros x y H; split; intro f.  
      apply sym_eq; apply H.
      apply A_oid; apply H.

    unfold Transitive.
    intros x y z H H'; split; intro f.
    transitivity (y f); [apply H | apply H'].
    apply Equivalence_Transitive with (D_A y f); 
         [apply H | apply H'].
Qed.

Definition eq_Graph_Morphism := Build_Setoid eq_Graph_Morphism_equiv.
        
End Graph_Morphism_equiv.


Section Morphism_Comp_Id.
Variables G1 G2 G3: Graph.
Variable F1: Graph_Morphism G1 G2.
Variable F2: Graph_Morphism G2 G3.

Program Instance CompGM : Graph_Morphism G1 G3 := {
  D_O := fun x => F2 (F1 x);
  D_A := fun f => @D_A _ _ F2 (@D_A _ _ F1 f)
}.
Next Obligation.
 Proof. unfold Proper; red.
        intros x y H.
        rewrite H.
        apply A_oid.
 Qed.
Next Obligation.
 Proof. repeat rewrite dom_com. auto. Qed.
Next Obligation.
 Proof. repeat rewrite cod_com. auto. Qed. 

End Morphism_Comp_Id.

(** forgetful functor cat -> graph *)

Section Cat_Graph.
Variable C: Cat.

Definition HOM := {a:C & {b:C & mor a b}}.

Definition src (a:HOM) := projT1 a.
Definition tgt (a:HOM) := projT1 (projT2 a).
Definition arrow (a:HOM) := projT2 (projT2 a).


Definition HOM_relation : relation HOM :=
     fun a b => arrow a === arrow b.


Lemma HOM_relation_oid : Equivalence HOM_relation.
Proof. unfold HOM_relation. split.
 unfold Reflexive.
 intro x. 
 apply Equal_hom_refl.

 unfold Symmetric.
 intros x y. apply Equal_hom_sym.
 
 unfold Transitive.
 intros x y z.
 apply Equal_hom_trans.
Qed.

Definition HOM_oid := Build_Setoid HOM_relation_oid.
                


Program Instance CatGraph: Graph := {
  O := obj C;
  A := HOM
}.
Next Obligation.
 Proof. apply HOM_oid. Qed.
Next Obligation.
 apply (*Build_Graph_struct*)
      {| dom := src; cod := tgt |}. Defined.

End Cat_Graph.

(** small graph *)

Class SmallGraph := {
  sO: Set;
  sA: Set;
  sA_oid:> Setoid sA;
  smallgraph_struct:> Graph_struct sO sA
}.

Instance Graph_from_SmallGraph (G:SmallGraph): Graph := {
  O := @sO G;
  A := @sA G;
  A_oid := sA_oid;
  graph_struct := @smallgraph_struct G
}.

Coercion Graph_from_SmallGraph: SmallGraph >-> Graph.

Program Instance SMALLGRAPH : @Cat_struct SmallGraph Graph_Morphism := {
  mor_oid a b := eq_Graph_Morphism a b;
  id a := {|D_O := (fun x => x); D_A := (fun f => f) |};
  comp a b c f g := CompGM f g
}.

Next Obligation.
 Proof. unfold Proper. red. auto. Qed.

Next Obligation.
  Proof. unfold Proper. red. red.
         unfold eq_Graph_Morphism1. simpl.
         intros x y H x0 y0 H0.
         destruct H0 as [H0 h0].
         destruct H as [H h].
         split; intro f.
          rewrite H0. rewrite H. auto.
          rewrite h0. rewrite h. apply sA_oid.
  Qed. 

Next Obligation.
  Proof. unfold eq_Graph_Morphism1. simpl.
         split; intros; [auto | apply sA_oid].
  Qed.

Next Obligation.
  Proof. unfold eq_Graph_Morphism1. simpl.
         split; intros; [auto | apply sA_oid].
  Qed.

Next Obligation.
  Proof. unfold eq_Graph_Morphism1. simpl.
         split; intros; [auto | apply sA_oid].
  Qed.














