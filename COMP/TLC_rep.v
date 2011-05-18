Require Import Coq.Logic.Eqdep.
Require Import Coq.Logic.FunctionalExtensionality.

Require Export CatSem.CAT.cat_INDEXED_TYPE.
Require Export CatSem.CAT.retype_functor.
Require Export CatSem.CAT.monad_h_morphism_gen.
Require Export CatSem.CAT.monad_h_module.
Require Export CatSem.TLC.TLC_types.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Automatic Introduction.

Section rep.

(** we'll have a look at the simply typed lambda calculus with types 
      B as base types and an arrow constructor *)
Notation "'TY'" := TLCtypes.
Notation "'IT'" := (ITYPE TY).
Notation "a '~>' b" := (TLCarrow a b) 
     (at level 69, right associativity).
Notation "a 'x' b" := (product (*C:= MOD _ _*) a b) (at level 30).
Notation "P [ z ]" := (ITFIB_MOD _ z P) (at level 35).
Notation "'d' P // s" := (ITDER_MOD _ _ s P) (at level 25).
Notation "'*'" := (Term (C:=MOD _ TYPE)).
Notation "f 'X' g" := (product_mor _ f g)(at level 30).

(** a representation is given by
      - a type U
      - a morphism of types TY -> U
      - a monad over (Set/U)
      - a representation (in the sense of STS) of f_*TLC
*) 


Class TLC_rep_s U (f : TY -> U) (P : Monad (ITYPE U)) := {
  App : forall r s, (P [f (r ~> s) ] x (P [f r])) ---> P [f s];
  Abs : forall r s, (d P // (f r))[f s] ---> P [f (r ~> s)]
}.

Record TLC_rep := {
  type_type : Type;
  tlc_rep_monad :> Monad (ITYPE type_type);
  type_mor : TY -> type_type;
  tlc_rep_struct :> TLC_rep_s type_mor tlc_rep_monad
}.

Existing Instance tlc_rep_struct.

Section TLC_rep_Hom.

Variables P R : TLC_rep.

Section Rep_Hom_Class.

(** a morphism of representations 
        - (U, f, P, Rep)
        - (U', f', Q, Rep')
   is given by 
        - g : U -> U'
        - H : f ; g = f'
        - generalized monad morphism P -> Q (with F = RETYPE g)
        - properties
*)

Variable f : type_type P -> type_type R.
Variable H : forall t, f (type_mor P t) = type_mor R t.
Variable M : gen_Monad_Hom P R (RETYPE (fun t => f t)).

Definition MM := PMod_ind_Hom M.


(*Notation "'PBT_'" := (PBT _ Sig).*)

(** for the constants we need a special morphism of modules 

    [* ---> (\Sigma * ) *]

    being the empty product  *)
(*
Lemma id_Term_PB_struct: 
   Module_Hom_struct (S:= Term (C:= MOD _ TYPE))  
(T:=(PB_MOD Sig TYPE Term))  
                 (fun r => id (Term (C:=TYPE))).
Proof. 
  simpl.
  constructor.
  intros.
  rewrite idl.
  rewrite idr.
  simpl.
  auto.
Qed.


Definition PBT : Term ---> (PB_MOD Sig TYPE Term) :=
      Build_Module_Hom id_Term_PB_struct.

Lemma id_PT_Term_struct: 
   Module_Hom_struct (T:= Term (C:= MOD _ TYPE)) 
(S:=(PB_MOD Sig TYPE Term))  
                 (fun r => id (Term (C:=TYPE))).
Proof. 
  simpl.
  constructor.
  intros.
  rewrite idl.
  rewrite idr.
  simpl.
  auto.
Qed.

Definition TPB : (PB_MOD Sig TYPE Term) ---> Term := 
      Build_Module_Hom id_PT_Term_struct.
*)

(** Sig : P -> R is a morphism of representations if it makes commute 
    all these weird diagrams
*)

Class TLC_rep_Hom_struct := {
  App_Hom : forall r s,  
         App (P:=P) r s ;; 
         FFib_Mod_Hom M _ ;; 
         eq_type_fibre_mod _ (H _)
                                          ==
         product_mor (MOD_PROD _ TYPE_prod)
            (FFib_Mod_Hom M (type_mor _ (r ~> s)) ;; 
             eq_type_fibre_mod _ (H _) ;;
             PM_FIB M R _  ) 
        
            (FFib_Mod_Hom M (type_mor _ r) ;; 
             eq_type_fibre_mod _ (H _) ;;
             PM_FIB M R _ ) ;;
         PROD_PM _ _ _ _ ;; 
         PMod_Hom M (App r s);; FIB_PM M R (type_mor R s) ;


  Abs_Hom : forall r s,  
          FFib_DER_Mod_Hom_eqrect M (type_mor _ s) 
          (H r ) ;; eq_type_fibre_mod _ (H _ ) ;;
          PM_FIB _ _ _ ;;
          PMod_Hom M (Abs r s);;
          FIB_PM _ _ _ 
                                      ==
          Abs (P:=P) r s ;; 
          FFib_Mod_Hom M _ ;;
          eq_type_fibre_mod _ (H _ )
}. 


End Rep_Hom_Class.

(** the type of morphismes of representations P -> R *)

Record TLC_rep_Hom := {
  tcomp : type_type P -> type_type R ;
  ttriag : forall t, tcomp (type_mor P t) = type_mor R t;
  rep_Hom_monad :> gen_Monad_Hom P R (RETYPE (fun t => tcomp t));
  rep_gen_Hom_monad_struct :> TLC_rep_Hom_struct ttriag rep_Hom_monad
}.

End TLC_rep_Hom.

Existing Instance rep_gen_Hom_monad_struct.


(** on our way to a category of representations:
    - an equality on morphisms of reps
*)

Inductive eq_Rep (P R : TLC_rep) : relation (TLC_rep_Hom P R) :=
 | eq_rep : forall (a c : TLC_rep_Hom P R), 
            forall H : (forall t, tcomp c t = tcomp a t),
            (forall V, rep_Hom_monad a V ;; lift (M:=R) (Transp H V)
                                    == 
                       Transp H (P V) ;; rep_Hom_monad c V ) ->
             
             eq_Rep a c.

(*
Lemma eq_rep_1 P R (a c : TLC_rep_Hom P R)
    (P : eq_Rep a c) : forall t, tcomp c t = tcomp a t.
Proof.
  destruct 1.
  auto.
Qed.


Lemma eq_rep_2 P R (a c : TLC_rep_Hom P R)
    (Q : eq_Rep a c) : 
forall V, rep_Hom_monad a V ;; lift (M:=R) (Transp (eq_rep_1 Q) V)
                         == 
       Transp (eq_rep_1 Q) (P V) ;; rep_Hom_monad c V .
Proof.
  intros P R a c Q.
  destruct Q.
  assert (H': H = eq_rep_1 (eq_rep (a:=a)(c:=c)(H:=H) e)).
  apply proof_irrelevance.
  rewrite <- H'.
  auto.
Qed.
*)  

(** the defined relation is an equivalence and 
    may hence serve as equality 
*)

Lemma eq_Rep_equiv (P R: TLC_rep) : 
   @Equivalence (TLC_rep_Hom P R) 
     (@eq_Rep P R).
Proof.
 intros P R.
 split.
 
 unfold Reflexive.
 intro M. 
 assert (H': forall t, tcomp M t = tcomp M t) by 
       (intros; reflexivity).

 apply (eq_rep (H:=H')).
 
 simpl.
 intros V t y.
 destruct y as [t y].
 
 simpl. 
 rewrite (UIP_refl _ _ (H' t)).
 simpl.
 assert (H:= lift_transp_id).
 simpl in *.
 rewrite H.
 auto.

  (* now symmetric *)
 
 unfold Symmetric.
 intros M N H.
 destruct H.
  assert (H': forall t, tcomp a t = tcomp c t) by auto.
 apply (eq_rep (H:=H')). 
 simpl; intros V t y.
 destruct a.
 destruct c.
 simpl in *.
 assert (H3 : tcomp1 = tcomp0).
 apply (functional_extensionality).
 auto.
 
 generalize dependent y. 
 generalize dependent H'.
 generalize dependent rep_Hom_monad0.
 generalize dependent rep_Hom_monad1.
 generalize dependent ttriag1.
 generalize dependent ttriag0.
 generalize dependent H.
 rewrite  H3.
 intros; simpl in *.
 rewrite transp_id. 
 assert (H2:= lift_transp_id).
 simpl in H2.
 rewrite H2.
 assert (H4 := H0 V t y).
 rewrite transp_id in H4.
 rewrite H2 in H4.
 simpl in *; auto.

  (* finally transitive *)

  unfold Transitive.
  intros a b c H H'.
  destruct H;
  destruct H'.
  assert (Ht : forall t, tcomp c t = tcomp a t).
    intro t. transitivity (tcomp a0 t); auto.
    
  apply (eq_rep (H:=Ht)).
  simpl; intros V t y.
  destruct a;
  destruct a0;
  destruct c.
  simpl in *.
  assert (H5 : tcomp0 = tcomp1) by
    (apply functional_extensionality; intro; auto).

  assert (H6 : tcomp1 = tcomp2) by
    (apply functional_extensionality; intro; auto).
  
  generalize dependent H2. 
  generalize dependent H1. 
  generalize dependent rep_Hom_monad2.
  generalize dependent rep_Hom_monad1.
  generalize dependent rep_Hom_monad0.
  generalize dependent ttriag2.
  generalize dependent ttriag1.
  generalize dependent ttriag0.
  generalize dependent H.
  generalize dependent Ht.
  rewrite <- H6.
  rewrite <- H5.
  
  clear H6 H5.
  clear tcomp2.
  clear tcomp1.
  
  intros.
  assert (H7:=H0 V t y).
  assert (H9:=H2 V t y).
  rewrite transp_id in *.
  simpl in *.
  assert (H8 := lift_transp_id).
  simpl in H8.
  rewrite H8 in *.
  transitivity (rep_Hom_monad1 V t y); 
  auto.
Qed.
  
Definition eq_Rep_oid (P R : TLC_rep) := Build_Setoid (eq_Rep_equiv P R).


(** Identity Representation *)

Section id_rep.

Variable P : TLC_rep.

Definition id_rep_car:
(forall c : ITYPE (type_type P),
  (RETYPE (fun t : type_type P => t)) (P c) --->
  P ((RETYPE (fun t : type_type P => t)) c)) :=
    
 fun V t y => 
   match y with ctype _ z => 
     lift (M:=P) (@id_retype _ V) _ z end.


Obligation Tactic := idtac.

Program Instance blalala : 
       gen_Monad_Hom_struct (P:=P) (Q:=P) (F0:=RETYPE (fun t => t))
       id_rep_car.
Next Obligation.
Proof.
  simpl.
  intros V W f t y.
  destruct y.
  simpl.
  assert (H:=lift_kleisli (M:= P)).
  simpl in *.
  rewrite H. simpl.
  assert (H':=kleisli_lift (M:=P)).
  simpl in H'.
  rewrite H'.
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros V t y.
  destruct y.
  simpl.
  assert (H:=lift_weta P).
  simpl in H.
  rewrite H.
  auto.
Qed.

Definition id_Rep_monad := Build_gen_Monad_Hom blalala.

Program Instance Rep_id_struct : 
         TLC_rep_Hom_struct (f := fun t => t) 
         (fun t => eq_refl) id_Rep_monad. 
Next Obligation.
Proof.
  simpl.
  intros r s V y.
  assert (H := mod_hom_mkl 
      (Module_Hom_struct :=(App(TLC_rep_s:=P) r s))).
  simpl in H.
  unfold lift.
  rewrite H.
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros r s V y.
  assert (H := mod_hom_mkl 
     (Module_Hom_struct :=(Abs(TLC_rep_s:=P) r s))).
  unfold lift.
  simpl in *.
  rewrite <- H.
  apply f_equal.
  assert (H' := klkl P).
  simpl in H'.
  rewrite H'.
  assert (H'':= kl_eq P).
  simpl in *.
  apply H''.
  clear y.
  
  intros t y.
  assert (H4 := etakl P).
  simpl in H4.
  rewrite H4.
  simpl.
  destruct y as [t y | ].
  simpl.
  unfold lift.
  rewrite H4.
  simpl.
  auto.
  simpl.
  auto.
Qed.


Definition Rep_id := Build_TLC_rep_Hom (Rep_id_struct).

End id_rep.

End rep.

Existing Instance eq_Rep_oid.
Existing Instance tlc_rep_struct.
Existing Instance rep_gen_Hom_monad_struct.



