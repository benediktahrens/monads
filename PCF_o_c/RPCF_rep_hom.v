Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Eqdep.

Require Export CatSem.PCF_o_c.RPCF_rep.
Require Export CatSem.CAT.eq_fibre.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.


(** morphisms of representations *)

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


Section rep_hom.

Variables P R : PCFPO_rep.

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
Hypothesis H : forall t, f (type_mor P t) = type_mor R t.
Hypothesis H' : forall u v, f (u ~~> v) = f u ~~> f v.

Variable M : gen_RMonad_Hom P R 
    (G1:=RETYPE (fun t => f t))
    (G2:=RETYPE_PO (fun t => f t)) (NNNT1 (fun t => f t)).

(*
Definition MM := gen_PbRMod_ind_Hom M.
Check FFib_Mod_Hom. Check FIB_RMOD_HOM.
Print FIB_RMOD_eq.
*)



(*
Check (fun r s => FIB_RMOD_eq (gen_PbRMod M R) (H (r ~> s))).
Check (fun r s => app (P:=P) r s).
Check (fun r s => app (P:=P) r s ;; 
                  FIB_RMOD_HOM M _  ).
Check (fun r s => app (P:=P) r s ;; 
                  FIB_RMOD_HOM M _  ;;
                  gen_pb_fib _ _ _ ).

Check FIB_RMOD_HOM.

Check (fun u v => 

               gen_PROD_PM _ _ _ _ ;;
               gen_PbRMod_Hom M (app (f u) (f v))).

Check (fun u v => FIB_RMOD_HOM M (u ~~> v);;
                  FIB_RMOD_eq _ (H' _ _ );;
                  gen_pb_fib M _ _ ).

Check (fun u =>  (FIB_RMOD_HOM M (u) ;;
              gen_pb_fib _ _ _ )).

Check (fun u v =>  
          product_mor _
             (FIB_RMOD_HOM M ((u ~~> v)) ;;
              FIB_RMOD_eq _ (H' _ _);;
              gen_pb_fib M _ _ )
             (FIB_RMOD_HOM M (u) ;;
              gen_pb_fib M _ _ )).
 
Check (fun (u v : type_type P) => app u v;;
             FIB_RMOD_HOM M _ ).

Check (fun u v => 

           product_mor _ 
             (FIB_RMOD_HOM M ((u ~~> v)) ;;
              FIB_RMOD_eq _ (H' _ _);;
              gen_pb_fib _ _ _ )
             (FIB_RMOD_HOM M (u) ;;
              gen_pb_fib _ _ _ )
            ;;
           gen_PROD_PM _ _ _ _ 
            ;;
           gen_PbRMod_Hom _ (app (f u) (f v))
           ==
           app u v;;
             FIB_RMOD_HOM M _ ;;
             gen_pb_fib _ _ _ ).
*)
(* this is the correct diag for app *)

(*
Check (fun u v : type_type P => abs u v ;;
             FIB_RMOD_HOM M _ ;;
             FIB_RMOD_eq _ (H' _ _ ) ;;
             gen_pb_fib _ _ _ ).

Check (der_fib_hom).
Check (fun u v => der_fib_hom_noeq _ _ _ ;; 
                gen_pb_fib _ _ _ ;;
                gen_PbRMod_Hom M (abs (f u) (f v))).

Check (fun u v =>  abs u v ;;
             FIB_RMOD_HOM M _ ;;
             FIB_RMOD_eq _ (H' _ _ ) ;;
             gen_pb_fib _ _ _ 
             ==
             der_fib_hom_noeq _ _ _ ;; 
                gen_pb_fib _ _ _ ;;
                gen_PbRMod_Hom M (abs (f u) (f v))).

Check FFib_DER_Mod_Hom_eqrect.
Check der_fib_hom.
*)

(*
Print gen_pb_fib.
Check (fun s => gen_pb_fib M s R).
Check (der_fib_hom).


Check (fun r s =>   der_fib_hom M _ (H _ ) ;;
                    FIB_RMOD_eq _ (H _ ) ;;
                    gen_pb_fib M (type_mor R s) (d R // type_mor R r) ;; 
                    gen_PbRMod_Hom M (abs r s)).
*)
(*
Check (fun r  s => der_fib_hom _ _ (H r ) ;;
                  FIB_RMOD_eq M (H s) ). ;;
                  gen_PbRMod_Hom M (abs r s)).
  *)   
(*             
Check (fun r s => abs r s ;; 
                  FIB_RMOD_HOM M _ ;;
                  FIB_RMOD_eq _ (H _ );;
                  gen_pb_fib _ _ _ ).

Check (fun t => unit_rmod M  ;; gen_PbRMod_Hom _ (bottom t )).
Check (fun t => bottom t ;; 
                FIB_RMOD_HOM M _ ;;
                FIB_RMOD_eq _ (H _ );;
                gen_pb_fib _ _ _ ).

Check (tttt (PCFPO_rep_struct := P) ;; FIB_RMOD_HOM M _ ).

Check Term.

Print gen_pb_fib.

*)
(*
Check True.
Check (CondB (PCFPO_rep_struct := P)).

Check (arrow_dist_ct4 H' H).

Check (CondB  (PCFPO_rep_struct := P) ;;
          FIB_RMOD_HOM M _  ;;
          FIB_RMOD_eq _ (arrow_dist_ct4 H' H _ _ _ _)).

Check FIB_RMOD_small_eq.
*)

Check FIB_RMOD_HOM.
Check (CondB (PCFPO_rep_struct := P)).

Class PCFPO_rep_Hom_struct := {

  CondB_hom : CondB (PCFPO_rep_struct := P) ;;
                FIB_RMOD_HOM M _ ;;
                FIB_RMOD_small_eq _ (arrow_dist_ct4 H' H _ _ _ _ );;
                gen_pb_fib _ _ _ 
           ==
           unit_rmod M  ;; 
           gen_PbRMod_Hom M (CondB (PCFPO_rep_struct := R))
;
  CondN_hom : CondN (PCFPO_rep_struct := P) ;;
                FIB_RMOD_HOM M _ ;;
                FIB_RMOD_small_eq _ (arrow_dist_ct4 H' H _ _ _ _ );; 
                gen_pb_fib _ _ _ 
           ==
           unit_rmod M  ;; 
           gen_PbRMod_Hom M (CondN (PCFPO_rep_struct := R))
;
  Pred_hom : Pred (PCFPO_rep_struct := P) ;;
                FIB_RMOD_HOM M _ ;;
                FIB_RMOD_small_eq _ (arrow_dist_ct2 H' H _ _ );; 
                gen_pb_fib _ _ _ 
           ==
           unit_rmod M  ;; 
           gen_PbRMod_Hom M (Pred (PCFPO_rep_struct := R)) 
;
  Zero_hom : Zero (PCFPO_rep_struct := P) ;;
                FIB_RMOD_HOM M _ ;;
                FIB_RMOD_small_eq _ (arrow_dist_ct2 H' H _ _);; 
                gen_pb_fib M _ _ 
           ==
           unit_rmod M  ;; 
           gen_PbRMod_Hom M (Zero (PCFPO_rep_struct := R))
;
  Succ_hom : Succ (PCFPO_rep_struct := P) ;;
                FIB_RMOD_HOM M _ ;;
                FIB_RMOD_small_eq _ (arrow_dist_ct2 H' H _ _ );; 
                gen_pb_fib M _ _ 
           ==
           unit_rmod M  ;; 
           gen_PbRMod_Hom M (Succ (PCFPO_rep_struct := R))
;
  fff_hom : ffff (PCFPO_rep_struct := P) ;;
                FIB_RMOD_HOM M _ ;;
                FIB_RMOD_small_eq _ (H _ );; 
                gen_pb_fib M _ _ 
           ==
           unit_rmod M  ;; 
           gen_PbRMod_Hom M (ffff (PCFPO_rep_struct := R))

;
  ttt_hom : tttt (PCFPO_rep_struct := P) ;;
                FIB_RMOD_HOM M _ ;;
                FIB_RMOD_small_eq _ (H _ );; 
                gen_pb_fib M _ _ 
           ==
           unit_rmod M  ;; 
           gen_PbRMod_Hom M (tttt (PCFPO_rep_struct := R))
; 
  bottom_hom : forall u,
           bottom u ;; 
                FIB_RMOD_HOM M _ ;;
(*                FIB_RMOD_eq _ (H _ );; *)
                gen_pb_fib M _ _ 
           ==
           unit_rmod M  ;; 
           gen_PbRMod_Hom _ (bottom (f u))
;
  nats_hom : forall m,
           nats m ;;
                FIB_RMOD_HOM M _ ;;
                FIB_RMOD_small_eq _ (H _ );; 
                gen_pb_fib M _ _ 
           ==
           unit_rmod M  ;; 
           gen_PbRMod_Hom _ (nats m)
;

  app_hom : forall u v, 
          product_mor _ 
             (FIB_RMOD_HOM M ((u ~~> v)) ;;
              FIB_RMOD_small_eq _ (H' _ _);;
              gen_pb_fib _ _ _ )
             (FIB_RMOD_HOM M (u) ;;
              gen_pb_fib _ _ _ )
            ;;
           gen_PROD_PM _ _ _ _ 
            ;;
           gen_PbRMod_Hom _ (app (f u) (f v))
           ==
           app u v;;
             FIB_RMOD_HOM M _ ;;
             gen_pb_fib _ _ _ 
;
 (* abs_hom : forall u v,
       abs u v ;;
             FIB_RMOD_HOM M _ ;;
             FIB_RMOD_small_eq _ (H' _ _ ) ;;
             gen_pb_fib _ _ _ 
             ==
             der_fib_hom_noeq _ _ _ ;; 
                gen_pb_fib _ _ _ ;;
                gen_PbRMod_Hom M (abs (f u) (f v))
;*)
  rec_hom : forall t,
      rec t ;; 
        FIB_RMOD_HOM M _ ;;
        gen_pb_fib M _ _ 
      ==
      FIB_RMOD_HOM M _ ;;
      FIB_RMOD_small_eq _ (H' _ _) ;;
      gen_pb_fib M _ _ ;;
      gen_PbRMod_Hom M (rec (f t))
;
  abs_hom2 : forall u v,
     abs u v ;;
        FIB_RMOD_HOM M _ 
(*        FIB_RMOD_small_eq _ (H' _ _ ) ;;
        gen_pb_fib _ _ _  *)
             ==
        der_fib_hom_noeq _ _ _ ;; 
        gen_pb_fib _ _ _ ;;
        gen_PbRMod_Hom M (abs (f u) (f v)) ;;
	gen_fib_pb _ _ _  ;;
	FIB_RMOD_small_eq _ (eq_sym (H' _ _ ))
   
}.

End Rep_Hom_Class.


(** the type of morphismes of representations P -> R *)

Record PCFPO_rep_Hom := {
  tcomp : type_type P -> type_type R ;
  tcomp_arrow : forall u v, tcomp (u ~~> v) = tcomp u ~~> tcomp v;
  ttriag : forall t, tcomp (type_mor P t) = type_mor R t;
  rep_Hom_monad :> gen_RMonad_Hom P R (NNNT1 (fun t => tcomp t));
  rep_gen_Hom_monad_struct :> PCFPO_rep_Hom_struct 
                ttriag tcomp_arrow rep_Hom_monad
}.

End rep_hom.

Existing Instance rep_gen_Hom_monad_struct.

