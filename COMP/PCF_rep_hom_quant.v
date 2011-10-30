
Require Export CatSem.COMP.PCF_rep_quant.
Require Export CatSem.CAT.unit_mod.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.


Section arrow_lemmata.

Variables U U': Type.
Variable Uar : U -> U -> U.
Variable U'ar : U' -> U' -> U'.

Notation "u >>> v" := (U'ar u v) (at level 60, right associativity).
Notation "u >> v" := (Uar u v) (at level 60, right associativity).

Variable g : U -> U'.
Hypothesis H : forall u v, g (u >> v) = g u >>> g v.

Lemma arrow_distrib3 : forall u v w, 
   g (u >> v >> w) = 
   g u >>> g v >>> g w.
Proof.
  intros u v w.
  repeat rewrite H.
  reflexivity.
Defined.

Lemma arrow_distrib4 : forall u v y z, 
   g (u >> v >> y >> z) =
   g u >>> g v >>> g y >>> g z.
Proof.
  intros u v y z.
  repeat rewrite H.
  reflexivity.
Defined.

Variable T : Type.
Variable f : T -> U.
Variable f' : T -> U'.

Hypothesis H' : forall t, g (f t) = f' t.


Lemma arrow_dist_ct2 : forall r s,
  g (f r >> f s) = 
  f' r >>> f' s.
Proof.
  intros.
  repeat rewrite H.
  repeat rewrite H'.
  reflexivity.
Defined.

Lemma arrow_dist_ct3 : forall r s t ,
  g (f r >> f s >> f t) =
  f' r >>> f' s >>> f' t.
Proof.
  intros.
  repeat rewrite H.
  repeat rewrite H'.
  reflexivity.
Defined.


Lemma arrow_dist_ct4 : forall r s t u,
  g (f r >> f s >> f t >> f u) =
  f' r >>> f' s >>> f' t >>> f' u.
Proof.
  intros.
  repeat rewrite H.
  repeat rewrite H'.
  reflexivity.
Defined.

Variable U'' : Type.
Variable f'' : T -> U''.
Variable g' : U' -> U''.
Variable U''ar : U'' -> U'' -> U''.

Notation "u >>>> v" := (U''ar u v)
       (at level 60, right associativity).

Hypothesis Hg' : forall u v,
       g' (u >>> v) = g' u >>>> g' v.
       

Lemma comp_arrow_dist:
forall u v : U,
  (fun t => g' (g t)) (u >> v) =
  (fun t => g' (g t)) u >>>>
  (fun t => g' (g t) ) v.
Proof.
  simpl.
  intros.
  rewrite H.
  rewrite Hg'.
  reflexivity.
Defined.

Hypothesis Hgf : forall t, g' (f' t) = f'' t.

Lemma comp_arrow_commute : 
   forall t, g' (g (f t)) = f'' t.
Proof.
  intros.
  rewrite H'.
  rewrite Hgf.
  reflexivity.
Defined.

End arrow_lemmata.


Section PCF_rep_Hom.

Notation "'IT'" := (ITYPE TY).
Notation "a '~>' b" := (PCF.Arrow a b) 
     (at level 69, right associativity).
Notation "a 'x' b" := (product (*C:= MOD _ _*) a b) (at level 30).
Notation "P [ z ]" := (ITFIB_MOD _ z P) (at level 35).
Notation "'d' P // s" := (ITDER_MOD _ _ s P) (at level 25).
Notation "'*'" := (Term (C:=MOD _ TYPE)).
Notation "f 'X' g" := (product_mor _ f g)(at level 30).

Variables P R : PCF_rep.

Section Rep_Hom_Class.

Variable f : type_type P -> type_type R.
Variable H : forall t, f (type_mor P t) = type_mor R t.
Hypothesis H' : forall u v, f (u ~~> v) = f u ~~> f v.
Variable M : colax_Monad_Hom P R (RETYPE (fun t => f t)).
(*
Check (fun (m : nat) =>
        nats (PCF_rep_struct :=P) m ;; 
        FFib_Mod_Hom M _ ;; 
        eq_type_fibre_mod (PModule M (E:=ITYPE (type_type R)) R) 
             (H _)
          == 
        unit_mod _ ;; 
        PMod_Hom M (nats (PCF_rep_struct:=R) m ) ;;
        FIB_PM _ _ _  ).

(*Rec_Hom*)

Check (fun t =>
        rec (PCF_rep_struct:=P) t ;;
        FFib_Mod_Hom M _  ;;
        PM_FIB _ _ _ 
          ==

(*Check (fun t =>*)  FFib_Mod_Hom M _(*type_mor _ (t ~> t)*) ;;
        eq_type_fibre_mod _ (H' _ _ ) ;;
        PM_FIB _ _ _ ;;
        PMod_Hom M (rec (PCF_rep_struct:=R) (f t)) ).

(*abs_hom2*) 
Check (fun u v =>
     abs u v ;;
        FFib_Mod_Hom M _ 
        ==
(*Check (fun u v => *)
    (FFib_DER_Mod_Hom M _ _ );;
                  PM_FIB _ _ _ ;;
                  PMod_Hom M (abs (f u) (f v));;
                  FIB_PM _ _ _ ;;
                  eq_type_fibre_mod _ (eq_sym (H' _ _ ))).

(*app*)        
Check (fun u v =>
          product_mor _
             (FFib_Mod_Hom M ((u ~~> v)) ;;
              eq_type_fibre_mod _ (H' _ _ ) ;;
              PM_FIB _ _ _ )
             (FFib_Mod_Hom M (u) ;;
              PM_FIB _ _ _ )
            ;;
           PROD_PM _ _ _ _ 
            ;;
           PMod_Hom _ (app (f u) (f v))
           ==
           app u v;;
             FFib_Mod_Hom M _ ;;
             PM_FIB _ _ _ ).
*)

Class PCF_rep_Hom_struct := {
    
  Succ_Hom : Succ (PCF_rep_struct:=P) ;;
       FFib_Mod_Hom M _ ;;
       eq_type_fibre_mod_eta _ (arrow_dist_ct2 H' H _ _ ) ;;
       PM_FIB _ _ _ 
       ==
       unit_mod _ ;;
       PMod_Hom M (Succ (PCF_rep_struct := R)) 
;

  Zero_Hom : Zero (PCF_rep_struct:=P) ;; 
        FFib_Mod_Hom M _ ;; 
        eq_type_fibre_mod_eta _ (arrow_dist_ct2 H' H _ _ ) ;;
        PM_FIB _ _ _ 
          == 
        unit_mod _ ;; 
        PMod_Hom M (Zero (PCF_rep_struct:=R)) 
;

  CondB_Hom : CondB (PCF_rep_struct:=P) ;; 
       FFib_Mod_Hom M _  ;;
       eq_type_fibre_mod_eta _ (arrow_dist_ct4 H' H _ _ _ _ ) ;;
       PM_FIB _ _ _ 
       ==
       unit_mod _ ;;
       PMod_Hom M (CondB (PCF_rep_struct := R)) 
;

  CondN_Hom : CondN (PCF_rep_struct:=P) ;; 
       FFib_Mod_Hom M _  ;;
       eq_type_fibre_mod_eta _ (arrow_dist_ct4 H' H _ _ _ _ ) ;;
       PM_FIB _ _ _ 
       ==
       unit_mod _ ;;
       PMod_Hom M (CondN (PCF_rep_struct := R)) 
;

 
  ttt_Hom : tttt (PCF_rep_struct:=P) ;; 
       FFib_Mod_Hom M _  ;;
       eq_type_fibre_mod_eta _ (H _ ) ;;
       PM_FIB _ _ _ 
       ==
       unit_mod _ ;;
       PMod_Hom M (tttt (PCF_rep_struct := R))  
;
        
  fff_Hom : ffff (PCF_rep_struct:=P) ;; 
       FFib_Mod_Hom M _  ;;
       eq_type_fibre_mod_eta _ (H _ ) ;;
       PM_FIB _ _ _ 
       ==
       unit_mod _ ;;
       PMod_Hom M (ffff (PCF_rep_struct := R))  
;

  nats_Hom : forall m, 
        nats (PCF_rep_struct :=P) m ;; 
        FFib_Mod_Hom M _ ;; 
        eq_type_fibre_mod_eta _ (H _) ;;
        PM_FIB _ _ _ 
          == 
        unit_mod _ ;; 
        PMod_Hom M (nats (PCF_rep_struct:=R) m ) 
;
 
  Bottom_Hom : forall t, 
        bottom t (P:=P) ;; 
        FFib_Mod_Hom M _ ;; 
        PM_FIB _ _ _ 
          == 
        unit_mod _ ;; 
        PMod_Hom M (bottom (f t) (P:=R))
;
  
  Rec_Hom : forall t,
        rec (PCF_rep_struct:=P) t ;;
        FFib_Mod_Hom M _  ;;
        PM_FIB _ _ _ 
          ==
        FFib_Mod_Hom M _ ;;
        eq_type_fibre_mod_eta _ (H' _ _ ) ;;
        PM_FIB _ _ _ ;;
        PMod_Hom M (rec (PCF_rep_struct:=R) (f t)) 
;
  App_Hom : forall u v,  
             app u v;;
             FFib_Mod_Hom M _ ;;
             PM_FIB _ _ _ 
             ==
  product_mor _
             (FFib_Mod_Hom M ((u ~~> v)) ;;
              eq_type_fibre_mod_eta _ (H' _ _ ) ;;
              PM_FIB _ _ _ )
             (FFib_Mod_Hom M (u) ;;
              PM_FIB _ _ _ )
            ;;
           PROD_PM _ _ _ _ 
            ;;
           PMod_Hom _ (app (f u) (f v)) 
;           

  Abs_Hom : forall u v,  
          abs u v ;;
          FFib_Mod_Hom M _ 
          ==
          FFib_DER_Mod_Hom M _ _ ;;
          PM_FIB _ _ _ ;;
          PMod_Hom M (abs (f u) (f v));;
          FIB_PM _ _ _ ;;
          eq_type_fibre_mod_eta _ (eq_sym (H' _ _ ))
;
 
  Pred_Hom : 
       Pred (PCF_rep_struct:=P) ;; 
       FFib_Mod_Hom M _  ;;
       eq_type_fibre_mod_eta _ (arrow_dist_ct2 H' H _ _ ) ;;
       PM_FIB _ _ _ 
       ==
       unit_mod _ ;;
       PMod_Hom M (Pred (PCF_rep_struct := R)) 

}. 


End Rep_Hom_Class.

(** the type of morphismes of representations P -> R *)

Record PCF_rep_Hom := {
  tcomp : type_type P -> type_type R ;
  tcomp_arrow : forall u v, tcomp (u ~~> v) = tcomp u ~~> tcomp v;
  ttriag : forall t, tcomp (type_mor P t) = type_mor R t;
  rep_Hom_monad :> colax_Monad_Hom P R (RETYPE (fun t => tcomp t));
  rep_gen_Hom_monad_struct :> 
     PCF_rep_Hom_struct ttriag tcomp_arrow rep_Hom_monad
}.

End PCF_rep_Hom.

Existing Instance rep_gen_Hom_monad_struct.
