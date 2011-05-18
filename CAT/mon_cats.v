Require Export CatSem.CAT.smon_cats.
Require Export CatSem.CAT.nat_iso.

Require Export CatSem.CAT.cat_SET. (* for the example *)

Set Implicit Arguments.
Unset Strict Implicit.

Unset Automatic Introduction.

Section monoidal_cat_def.

Variable obC: Type.
Variable morC: obC -> obC -> Type.

Variable C: Cat_struct morC.

Section Diagram_def.

Notation "a 'X' b" := (build_prod_mor _ _ a b) (at level 44).

Variable tens: Functor (PROD C C) C.
Variable Alpha: 
   NISO (CompF (iso C C C) (CompF (Prod_functor (Id C) tens) tens))
                                (CompF (Prod_functor tens (Id C)) tens).

Definition penta_diag := forall z: PROD C (PROD C (PROD C C)),
          let (a, t) := z in 
          let (b, r) := t in
          let (c, d) := r in 
        Alpha ((a,b),tens(c,d)) ;; Alpha ((tens (a,b),c),d) ==
              #tens  (id a X Alpha ((b,c),d)) ;;
              Alpha ((a,(tens (b,c)),d)) ;;
              #tens (Alpha ((a,b),c) X id d).
(*
Definition penta_diag := 
 forall z: PROD C (PROD C (PROD C C)),
          let (a, t) := z in 
          let (b, r) := t in
          let (c, d) := r in 
           Alpha ((a, b), tens (c, d)) o Alpha ((tens (a, b), c), d) == 
           Fmor (Functor := tens) (a:= (a, (tens (b, (tens (c, d))))))
                                  (b:= (a, (tens (tens (b, c), d))))
                    (id a , Alpha ((b, c), d)) o
           Alpha ((a, (tens (b, c)), d)) o
           Fmor (Functor := tens) (a := (tens (a, tens (b, c)), d))
                                  (b := (tens (tens (a, b), c), d))
                                (Alpha ((a, b), c), id d).
*)

Variable I: obC.
Variable Lambda: NISO (CompF (eleft C I) tens) (Id C).
Variable Rho: NISO (CompF (eright C I) tens) (Id C).

Definition lam_rho_dia := 
        forall a c: obC,
 Alpha ((a, I), c) ;; #tens ( Rho a X id c ) ==
         #tens ( id a X Lambda c ).
(*
Definition lam_rho_dia  :=
          forall a c: C,
                Alpha ((a, I), c) o
                Fmor (Functor:= tens) (a:= (tens (a, I), c))
                                       (b:= (a, c))
                              (Rho a, id c) 
          ==

                Fmor (Functor:= tens) (a:= (a, tens (I, c)))
                                      (b:= (a, c))
                            (id a, Lambda c).
*)


       
Definition eq_lam_rho:= Lambda I == Rho I.

End Diagram_def.

End monoidal_cat_def.

Section bla.
(* Variable obC:Type.
Variable morC: obC -> obC -> Type. *)

Class mon_cat `{obC:Type, morC:obC -> obC -> Type, C: (Cat_struct obC morC)} := {
  tens : Functor (PROD C C) C;
  I: obC;
  Alpha: NISO (CompF (iso C C C) (CompF (Prod_functor (Id C) tens) tens))
                                (CompF (Prod_functor tens (Id C)) tens);
  Lambda: NISO (CompF (eleft C I) tens) (Id C);
  Rho: NISO (CompF (eright C I) tens) (Id _);
  tens_penta: penta_diag Alpha;
  lam_rho: lam_rho_dia Alpha Lambda Rho;
  eq_l_r: eq_lam_rho Lambda Rho
}.

End bla.

(** this gives a universe inconsistency *)
(** 
[
Program Instance CAT_mon_cat : mon_cat (C:=Cat_CAT).
Next Obligation.

Admitted.      (* KAWOOM *)
]
*)


(**  a smon is a mon cat *)
(*
Section smon_imp_mon.

Variable C: Category.

Hypothesis H: smon_cat C.

Let T := @tensor C H.
Let H1 := @tensor_assoc C H.
Let H2 := @eleft_unit C H.
Let H3 := @eright_unit C H.

Program Instance alpha_from_smon :  
NT
  (CompF (iso C C C)
     (CompF (Prod_functor (C:=C) (D:=C) (C':=PROD C C) (D':=C) (Id C) tensor)
        tensor))
  (CompF (Prod_functor (C:=PROD C C) (D:=C) (C':=C) (D':=C) tensor (Id C))
     tensor).

Next Obligation.
     unfold Comp_Fobj.  simpl. unfold prod_Fobj.
     destruct c as [[a b] c]. simpl in *|-*.
     unfold eq_Functor1 in H1.
     set (H':= @H1 ((a, b), c)((a, b), c)(id (Cat:= PROD (PROD C C) C) _)). 
     simpl in *|-*.
     set (H'':= Equal_hom_src H'). 
     unfold Comp_Fobj, Prod_functor in H''. simpl in H''.
     unfold prod_Fobj in H''. simpl in H''.
     rewrite H''.
     apply id.
Defined.

Next Obligation.
  Proof. unfold trafo_comm, alpha_from_smon_obligation_1.
         simpl.
         intros c d f. 
         destruct c as [[c1 c2] c3].
         destruct d as [[d1 d2] d3].
         destruct f as [[f1 f2] f3].
         simpl in *|-*.
         unfold Comp_Fmor. simpl. unfold prod_Fmor. simpl.
         rewrite <- NTcomm.
         
(id (tensor (a, tensor (b, c))))).

Program Instance mon_from_smon: mon_cat C := {
  tens := tensor;
  I := e 
}.
Next Obligation.
  unfold CompF. simpl.
  
NISO
  (CompF (iso C C C)
 (CompF (Prod_functor (C:=C) (D:=C) (C':=PROD C C) (D':=C) (Id C) tensor)
        tensor))
  (CompF (Prod_functor (C:=PROD C C) (D:=C) (C':=C) (D':=C) tensor (Id C))
     tensor)

*)

(** SET is a mon cat *)



Section SET_mon_cat.



Definition prod_set (a b:Set) : Set := prod a b.

Program Definition set_prod_functor: 
     Functor (PROD SET SET) SET := Build_Functor
  (Fobj := fun x => prod_set (fst x) (snd x))
   (Fmor := fun a b f => fun x => ((fst f) (fst x), (snd f) (snd x))) _ .
Next Obligation.
Proof.  
  constructor.
            
  unfold Proper. red. simpl.
  intros a b x y H x0. 
  destruct a as [a1 a2]. 
  destruct b as [b1 b2].
  destruct x as [x1 x2]. 
  destruct y as [y1 y2].
  destruct x0 as [w z].
  simpl in *|-*.
  rewrite (proj1 H).
  rewrite (proj2 H). 
  auto.
  
  simpl.
  intros a x;
  destruct x;
  auto.
  
  simpl. 
  auto.
Qed.

Definition I_set := unit.  

Program Definition alpha_set : 
NT (CompF (iso SET SET SET) 
  (CompF (Prod_functor (Id SET) set_prod_functor) set_prod_functor))
   (CompF (Prod_functor set_prod_functor (Id SET)) set_prod_functor):= 
Build_NT

(trafo := fun z x => ( (fst x, fst (snd x)), snd (snd x))) _ .
Next Obligation.
Proof. 
  constructor. 
  intros;
  simpl;
  auto.
Qed.
       
Program Instance alpha_invertible z : Invertible (alpha_set z) := {
  inverse := fun x => 
           (fst (fst x), (snd (fst x), (snd x)))
}.
Next Obligation.
Proof.
  destruct x as [[x1 x2] x3]. 
  simpl. auto. 
Qed.
Next Obligation.
Proof.
  destruct x as [x1 [x2 x3]]; 
  simpl. auto.
Qed.

Program Instance alpha_set_NISO : NISO_struct alpha_set.

Definition alpha_SET : NISO (CompF (iso SET SET SET) 
  (CompF (Prod_functor (Id SET) set_prod_functor) set_prod_functor))
   (CompF (Prod_functor set_prod_functor (Id SET)) set_prod_functor) := 
   Build_NISO (*niso_struct := *) alpha_set_NISO.

Program Definition lambda_set : 
     NT (CompF (eleft SET I_set) set_prod_functor) (Id SET) := 
     Build_NT (trafo := fun z x => snd x) _ .
Next Obligation.
Proof. 
  constructor. 
  intros.
  simpl. 
  auto. 
Qed.

Program Instance lambda_invertible z : Invertible (lambda_set z) := {
  inverse := fun x => (tt,x)
}.
Next Obligation.
Proof.
  destruct x as [xa xb].
  simpl in *. 
  unfold I_set in xa. 
  elim xa. 
  auto.
Qed.

Program Instance lambda_set_NISO : NISO_struct lambda_set.
  
Definition lambda_SET := Build_NISO lambda_set_NISO.
  
  
 

Program Definition rho_set : 
     NT (CompF (eright SET I_set) set_prod_functor) (Id SET) := 
     Build_NT (trafo := fun z x => fst x) _ .
Next Obligation.
Proof. 
  constructor. 
  intros.
  simpl. 
  auto. 
Qed.

Program Instance rho_invertible z : Invertible (rho_set z) := {
  inverse := fun x => (x,tt)
}.
Next Obligation.
Proof.
  destruct x as [xa xb].
  simpl in *. 
  unfold I_set in xa. 
  elim xb. 
  auto.
Qed.

Program Instance rho_set_NISO : NISO_struct rho_set.

Definition rho_SET := Build_NISO rho_set_NISO.
  
  
Program Instance SET_MONOIDAL : mon_cat (C:=SET) := {
  Alpha := alpha_SET;
  Rho := rho_SET;
  Lambda := lambda_SET
}.
Next Obligation.
Proof. 
  unfold penta_diag.
  intro z.
  destruct z as [a [b [c d]]].
  simpl.
  intro x. 
  destruct x as [xa [xb [xc xd]]]. 
  simpl in *. 
  auto. 
Qed.
Next Obligation.
Proof. 
  unfold lam_rho_dia. 
  simpl.
  auto.
Qed.
Next Obligation.
Proof. 
  unfold eq_lam_rho. 
  simpl.
  intro x; 
  destruct x as [xa xb]; 
  simpl in *.
  unfold I_set in *. 
  elim xa. 
  elim xb. 
  auto.
Qed.
           

End SET_mon_cat.
















