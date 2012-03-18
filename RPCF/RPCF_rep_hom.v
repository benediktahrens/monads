(*Require Import Coq.Logic.FunctionalExtensionality.*)
(*Require Import Coq.Logic.Eqdep.*)

Require Export CatSem.RPCF.RPCF_rep.
Require Export CatSem.CAT.eq_fibre.

Set Implicit Arguments.
Unset Strict Implicit.
Set Transparent Obligations.
Unset Automatic Introduction.

Notation "M [( s )]" := (FIB_RMOD_HOM M s) (at level 30).
Notation "f 'X' g" := (product_mor _ f g)(at level 30).
Notation "f ** rho" := (colax_PbRMod_Hom f rho)(at level 34).

Notation "'IsoPF'" := (colax_Pb_Fib _ _ _).
Notation "'IsoFP'" := (colax_Fib_Pb _ _ _).
Notation "'IsoXP'" := (colax_PROD_PM _ _ _ _ ).

(*Notation "f 'D' r [( s )] " := (DerFib_RMod_Hom f s r) (at level 33).*)

Notation "*--->*" := (unit_rmod _ ).

(** morphisms of representations *)

(*

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


Variable Ubool : U.
Variable Unat : U.
Variable U'bool : U'.
Variable U'nat : U'.

Hypothesis gnat : g Unat = U'nat.
Hypothesis gbool : g Ubool = U'bool.

Lemma n_ar_n : g (Unat >> Unat) = U'nat >>> U'nat.
Proof.
  rewrite <- gnat.
  apply H.
Defined.



(*
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
*)
(*
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
*)
End arrow_lemmata.
*)

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

Variable Sorts_map : Sorts P -> Sorts R.
(*Hypothesis H : forall t, f (type_mor P t) = type_mor R t.*)
Hypothesis HArrow : forall u v, Sorts_map (u ~~> v) = Sorts_map u ~~> Sorts_map v.
Hypothesis HBool : Sorts_map (Bool _ ) = Bool _ .
Hypothesis HNat : Sorts_map (Nat _ ) = Nat _ .


Variable f : colax_RMonad_Hom P R 
    (G1:=RETYPE (fun t => Sorts_map t))
    (G2:=RETYPE_PO (fun t => Sorts_map t)) 
  (RT_NT (fun t => Sorts_map t)).

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
(*
Check FIB_RMOD_HOM.
Check (CondB (PCFPO_rep_struct := P)).
*)

Obligation Tactic := 
        intros; simpl; repeat (rew_all || auto).

(*Print Succ.*)
Implicit Arguments Succ [Sorts P Arrow Bool Nat PCFPO_rep_struct].
(*Print Succ.*)
Implicit Arguments CondB [Sorts P Arrow Bool Nat PCFPO_rep_struct].
Implicit Arguments CondN [Sorts P Arrow Bool Nat PCFPO_rep_struct].
Implicit Arguments Pred [Sorts P Arrow Bool Nat PCFPO_rep_struct].
Implicit Arguments Zero [Sorts P Arrow Bool Nat PCFPO_rep_struct].
Implicit Arguments ffff [Sorts P Arrow Bool Nat PCFPO_rep_struct].
Implicit Arguments tttt [Sorts P Arrow Bool Nat PCFPO_rep_struct].
Implicit Arguments Nat [p].
Implicit Arguments Bool [p].
(*Print nats.*)
(*
Implicit Arguments bottom [U P Arrow Bool Nat].
Implicit Arguments nats [U P Arrow Bool Nat].
Implicit Arguments bottom [U P Arrow Bool Nat].
*)

(*Print app.*)

Program Definition Succ_hom' := 
  Succ  (*PCFPO_rep_struct := P*) ;; f [(Nat ~~> Nat)] ;;
(*                FIB_RMOD_HOM M _ ;; *)
                Fib_eq_RMod _ ( _ );; 
(*                colax_Pb_Fib f _ _ *)
                IsoPF
           ==
           *--->* ;;
(*           unit_rmod f  ;; *)
           f ** (Succ  (*PCFPO_rep_struct := R*)).



Program Definition CondB_hom' := CondB (*PCFPO_rep_struct := P*) ;;
                f [( _ )] ;;
                Fib_eq_RMod _ ( _ );;
(*                colax_Pb_Fib _ _ _ *)
                IsoPF
           ==
           *--->* ;;
(*           unit_rmod f  ;; *)
           f ** (CondB (*PCFPO_rep_struct := R*)).


Program Definition CondN_hom' := CondN (*PCFPO_rep_struct := P*) ;;
                f [( _ )] ;;
                Fib_eq_RMod _ _ ;; 
                IsoPF
           ==
           *--->* ;;
(*           unit_rmod f  ;; *)
           f ** (CondN (*PCFPO_rep_struct := R*)).


Program Definition Pred_hom' := Pred (*PCFPO_rep_struct := P*) ;;
                f [( _ )] ;;
                Fib_eq_RMod _ _ ;; 
                IsoPF
           ==
           *--->* ;;
(*           unit_rmod f  ;; *)
           f ** (Pred (*PCFPO_rep_struct := R*)) .

Program Definition Zero_hom' := Zero (*PCFPO_rep_struct := P*) ;;
                f [( _ )] ;;
                Fib_eq_RMod _ _;; 
                IsoPF
           ==
           *--->* ;;
(*           unit_rmod f  ;; *)
           f ** (Zero (*PCFPO_rep_struct := R*)).


Program Definition fff_hom' := ffff (*PCFPO_rep_struct := P*) ;;
                f [( _ )] ;;
                Fib_eq_RMod _ _ ;; 
                IsoPF
           ==
           *--->* ;;
(*           unit_rmod f  ;; *)
           f ** (ffff (*PCFPO_rep_struct := R*)).

Program Definition ttt_hom' := tttt (*PCFPO_rep_struct := P*) ;;
                f [( _ )] ;;
                Fib_eq_RMod _ _ ;; 
                IsoPF
           ==
           *--->*  ;;
(*           unit_rmod f ;; *)
           f ** (tttt (*PCFPO_rep_struct := R*)).
 
Program Definition bottom_hom' := forall u,
           bottom u ;; 
                f [( _ )] ;;
(*                FIB_RMOD_eq _ (H _ );; *)
             IsoPF
           ==
           *--->*  ;;
(*           unit_rmod f  ;; *)
           f ** (bottom (_)).

Program Definition nats_hom' := forall m,
           nats m ;;
                f [( _ )] ;;
                Fib_eq_RMod _ ( _ );; 
                IsoPF
           ==
           *--->*  ;;
(*           unit_rmod f  ;; *)
           f ** (nats m).



Program Definition app_hom' := forall u v, 
(*          product_mor _ *)
             (f [(u ~~> v)] ;;
              Fib_eq_RMod _ (HArrow _ _);;
              (*colax_Pb_Fib _ _ _ )*) IsoPF ) X 
             (f [(u)] ;;
              (*colax_Pb_Fib _ _ _ )*)
              IsoPF )
            ;;
(*           colax_PROD_PM _ _ _ _ *)
             IsoXP
            ;;
(*           colax_PbRMod_Hom _ (app (_ u) (_ v)) *)
           f ** (app _ _ )
           ==
           app u v;;
             f [( _ )] ;; IsoPF.
(*             colax_Pb_Fib _ _ _ .*)



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

Program Definition rec_hom' := forall t,
      rec t ;; 
         f [( _ )] ;; IsoPF
(*        colax_Pb_Fib f _ _ *)
      ==
      f [( _ )] ;;
      Fib_eq_RMod _  (HArrow _ _) ;;
(*      colax_Pb_Fib f _ _ ;; *)
        IsoPF ;;
      f ** (rec (_ t)) .


Program Definition  abs_hom' := forall u v,
     abs u v ;;
         f [( _ )]
(*        FIB_RMOD_small_eq _ (H' _ _ ) ;;
        gen_pb_fib _ _ _  *)
             ==
        DerFib_RMod_Hom _ _ _ ;; 
(*        D f d u [( v )]  ;; *)
(*        colax_Pb_Fib _ _ _ ;; *)
        IsoPF ;;
        f ** (abs (_ u) (_ v)) ;;
(*	colax_Fib_Pb _ _ _  ;;*)
        IsoFP ;;
	Fib_eq_RMod _ (eq_sym (HArrow _ _ )) .


Class PCFPO_rep_Hom_struct := {

  CondB_hom :  CondB_hom' 
;
  CondN_hom : CondN_hom'
;
  Pred_hom : Pred_hom'
;
  Zero_hom : Zero_hom'
;
  Succ_hom : Succ_hom'
;
  fff_hom : fff_hom'

;
  ttt_hom : ttt_hom'
; 
  bottom_hom : bottom_hom'
;
  nats_hom : nats_hom'
;

  app_hom : app_hom'
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
  rec_hom : rec_hom'
;
  abs_hom : abs_hom'
}.

End Rep_Hom_Class.


(** the type of morphismes of representations P -> R *)

Record PCFPO_rep_Hom := {
  Sorts_map : Sorts P -> Sorts R ;
  HArrow : forall u v, Sorts_map (u ~~> v) = Sorts_map u ~~> Sorts_map v;
  HNat : Sorts_map (Nat _ ) = Nat R ;
  HBool : Sorts_map (Bool _ ) = Bool R ;
  rep_Hom_monad :> colax_RMonad_Hom P R (RT_NT (fun t => Sorts_map t));
  rep_colax_Hom_monad_struct :> PCFPO_rep_Hom_struct 
                 HArrow HBool HNat rep_Hom_monad
}.

End rep_hom.

Existing Instance rep_colax_Hom_monad_struct.

