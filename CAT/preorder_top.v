Require Export CatSem.CAT.functor.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Automatic Introduction.

Section order.

Variable T: Type.

Class order := {
  sm: T -> T -> Prop;
  Top: T;
  Top_max: forall x, sm x Top;
  Refl: forall x:T, sm x x;
  Trans: forall x y z, sm x y -> sm y z -> sm x z
}.

End order.

Section Order_Top.

Notation "x <: y" := (sm x y) (at level 45).

Record Order := {
  carrier:> Type;
  order_struct : order carrier
}.

Existing Instance order_struct.

Section order_morphism.

Variables S T: Order.

Class order_morphism (f: S -> T) := {
  preserve_Top: f (Top (T := S)) = Top (T:=T);
  preserve_order: forall x y, x <: y -> f x <: f y
}.

Record Order_morphism := {
  morcar:> S -> T;
  order_morph: order_morphism morcar
}.

End order_morphism.

Existing Instance order_morph.

Section Composition.

Variable R: Order.

Program Definition Order_id : Order_morphism R R :=
      Build_Order_morphism (morcar := fun x => x) _.
Next Obligation.
Proof. 
  apply Build_order_morphism; 
  auto. 
Qed.
    

Variables S T: Order.
Variable f: Order_morphism R S.
Variable g: Order_morphism S T.

Program Definition Order_comp : Order_morphism R T := Build_Order_morphism
       (morcar := fun x => g (f x)) _.
Next Obligation.
Proof. 
  destruct f as [a [b c]]; 
  destruct g as [A [B C]];
  apply Build_order_morphism; simpl.
  rewrite b; rewrite B; auto.
  intros x y H.
  apply C; apply c; auto.
Qed.

End Composition.

Definition order_mor_rel (A B: Order) : relation (Order_morphism A B) :=
            fun f g => forall x, f x = g x.

Lemma order_mor_equiv (A B: Order) : Equivalence (@order_mor_rel A B).
Proof. 
  intros A B;
  unfold order_mor_rel;
  split; 
  unfold Reflexive, 
         Symmetric, 
         Transitive; 
  intros; 
  try etransitivity; 
  auto.
Qed.
           
Definition order_mor_oid (A B: Order) := Build_Setoid (order_mor_equiv A B).

Obligation Tactic := simpl; 
                     unfold order_mor_rel, Order_comp;
                     auto.

Program Instance Order_Cat: Cat_struct Order_morphism := {
  mor_oid := order_mor_oid;
  id a := Order_id a;
  comp := Order_comp
}.
Next Obligation.
Proof. 
  unfold Proper; 
  repeat red.
  simpl;
  intros.
  rewrite H.
  rewrite H0.
  auto.
Qed.

Definition opt_sm (V:Order) : relation (option V) :=
      fun x y => match x, y with
                 |  _ , None => True
                 | Some v , Some w => v <: w
                 | None , _ => False
                 end.

Program Instance opt_order (V: Order) : order (option V) := {
  sm := (@opt_sm V);
  Top := None
}.
Next Obligation.
Proof. 
  unfold opt_sm. 
  destruct x; 
  simpl; auto. 
Qed.
Next Obligation.
Proof. 
  destruct x; 
  simpl; auto. 
  apply Refl.  
Qed.
Next Obligation.
Proof.
  intros V x y z H H1.
  unfold opt_sm in *|-*;
  destruct x; 
  destruct y; 
  destruct z; auto.
  apply Trans with c0; auto.
  intuition.
Qed.

Definition OptOrder (V: Order) : Order := Build_Order (opt_order V).

(** OptOrder can be extended to a functor *)

Program Definition OptOrder_map (V W: Order) (f: Order_morphism V W) : 
   Order_morphism (OptOrder V) (OptOrder W) := Build_Order_morphism
     (morcar := fun x => match x with 
                         | Some v => Some (f v)
                         | None => None
                         end) _. 
Next Obligation.
Proof. 
  intros V W f.
  apply Build_order_morphism; 
  simpl; auto.
  intros x y H.
  destruct x; destruct y; simpl; auto.
  apply preserve_order; try apply f.
  apply H.
Qed.
        
Lemma OptOrder_comp: forall (a b c : Order) 
      (f : Order_morphism a b) (g : Order_morphism b c),
    OptOrder_map (Order_comp f g) == 
          Order_comp (OptOrder_map f) (OptOrder_map g).
Proof. 
  intros a b c f g; simpl;
       unfold order_mor_rel; intro x;
       induction x; simpl; auto.
Qed.

Program Definition OptOrderFunctor : Functor Order_Cat Order_Cat :=
          Build_Functor
    (Fobj := OptOrder) (Fmor := OptOrder_map) _ .
Next Obligation.
Proof. 
  apply Build_Functor_struct.
  
  intros a b; unfold Proper; repeat red.
  intros f g H x; induction x; simpl;
  try rewrite H; auto.
  
  intro V; simpl.
  unfold order_mor_rel; intro x; 
  induction x; simpl; auto.
  
  intros a b c f g; simpl;
  unfold order_mor_rel; intro x;
  induction x; simpl; auto.
Qed.
  
Lemma OptOrder_map_extens (V W: Order) (f g: Order_morphism V W):
          f == g -> OptOrder_map f == OptOrder_map g.
Proof. 
  intros V W f g H; simpl; 
  unfold order_mor_rel, OptOrder_map; 
  intro x; induction x; simpl; try rewrite H; auto.
Qed.



(*
Definition opt_sm (V:Order) : relation (option V) :=
          fun x y => match x, y with
                     | Some v, Some w => v <: w
                     | None , None => True
                     | _ , _ => False
                     end.
*)


Inductive Fsub (V: Order) : Type :=
 | TVar : V -> Fsub V 
 | TTop : Fsub V
 | Arr : Fsub V -> Fsub V -> Fsub V
 | Uni : Fsub V -> Fsub (OptOrder V) -> Fsub V.

Fixpoint rename (V W: Order) (f: Order_morphism V W) 
            (t: Fsub V) : Fsub W :=
  match t with
  | TVar v => TVar (f v)
  | TTop => TTop W
  | Arr u v => Arr (rename f u) (rename f v)
  | Uni u v => Uni (rename f u) (rename (OptOrder_map f) v)
  end.

Lemma rename_extens (V: Order) (s t: Fsub V) (H: s = t)
                        (W: Order) (f g: Order_morphism V W): 
         f == g -> rename f s = rename g t.
Proof. 
  intros until 1. subst s.
  induction t; simpl; unfold order_mor_rel; simpl; 
  intros W f g H.
  rewrite H. auto.
  auto.
  rewrite (IHt1 W f g); try rewrite (IHt2 W f g); auto.
  rewrite (IHt1 W f g); auto.
  rewrite (IHt2 (OptOrder W) (OptOrder_map f) (OptOrder_map g) ); auto.
  apply OptOrder_map_extens; auto.
Qed.

Lemma rename_id (V: Order)(t: Fsub V)(f: Order_morphism V V)
                (H: forall x, f x = x) : rename f t = t.
Proof. 
  intros V t. induction t; simpl; auto.
  intros f H; rewrite H; auto.
  intros f H;
  rewrite IHt1; try rewrite IHt2; auto.
  intros f H;
  rewrite IHt1; auto. apply f_equal.
  apply IHt2.
  intro x; destruct x; simpl ; try rewrite H; auto.
Qed.

Lemma rename_comp (V:Order) (t: Fsub V) (W X: Order) 
                  (f:Order_morphism V W) (g: Order_morphism W X): 
        rename g (rename f t) = rename (Order_comp f g) t.
Proof. 
  intros V t; induction t; simpl; auto.
  intros W X f g; 
  rewrite IHt1; try rewrite IHt2; auto.
  intros W X f g; 
  rewrite IHt1; apply f_equal.
  rewrite IHt2.
  apply rename_extens; auto.
  apply hom_sym.
  apply OptOrder_comp.
Qed.

End Order_Top.   










