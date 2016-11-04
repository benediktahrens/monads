Require Export CatSem.CAT.Misc.
Require Export CatSem.CAT.monad_h_module.
Require Export CatSem.CAT.functor.
Require Export CatSem.CAT.cat_TYPE.
Require Export CatSem.CAT.monad_h_morphism_gen.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

(** category of families of types,
    T being the index type *)


Section indexed_types.

Variable T: Type.


Lemma INDEXED_TYPE_equiv (A B: T -> Type) : 
     Equivalence (A:= forall t, A t -> B t)
          (fun p q => forall t:T, forall x: A t, p t x = q t x).
Proof. 
  intros; 
  constructor; 
  unfold Reflexive,Symmetric,Transitive;
  intros; simpl; try etransitivity; auto. 
Qed.

Definition INDEXED_TYPE_oid (A B: T -> Type) := 
         Build_Setoid (INDEXED_TYPE_equiv A B).

Obligation Tactic := cat; 
   try (match goal with | [ |- Proper _ _ ] => 
             unfold Proper; do 2 red end) ;
   cat; try rewrite assoc;
   repeat (match goal with [ H : forall a b, _ = _ |- _ ] => 
                   rewrite H end);
   cat.

Program Instance ITYPE_struct : Cat_struct (obj := T -> Type) 
          (fun A B => forall t, A t -> B t) := {
  mor_oid := INDEXED_TYPE_oid;
  comp A B C f g := fun t => fun x => g t (f t x);
  id A := fun t x => x
}.

Canonical Structure ITYPE := Build_Cat ITYPE_struct.

Section proj.

Obligation Tactic := cat;
   try (match goal with | [ |- Proper _ _ ] => 
             unfold Proper; red end) ; cat.

Program Instance IT_proj_Func (t:T) : 
     Functor_struct (C:=ITYPE) (D:=TYPE)(*Fobj:= fun a => ipo_proj a t*) 
                        (fun A B f => f t).
  
Canonical Structure IT_proj t := Build_Functor (IT_proj_Func t).

End proj.

Obligation Tactic := cat; repeat (match goal with
  [ H : TEMPTY |- _ ] => elim H end); cat.

Program Instance ITYPE_init : Initial ITYPE := {
  Init := fun t => Init;
  InitMor a t := InitMor (a t)
}.

Hint Extern 3 (?a = ?b) => try elim a; try elim b.

Program Instance ITYPE_term : Terminal ITYPE := {
  Term := fun t => Term;
  TermMor a t := TermMor (a t)
}.

(** adding an element to one of the types *)
Section opt.

Inductive opt (u : T) (A : ITYPE) : (ITYPE) :=
| some : forall (t : T), (A t) -> opt u A t
| none : opt u A u.

Arguments none [_ _] .
 Global Arguments some [_ _] _ _. 

Notation "A ' u" := (opt u A) (at level 40).

Ltac elim_opt := match goal with
                 | [ H : opt _ _ _|- _ ] => 
                       destruct H; simpl; intros; auto
                 | _ => simpl; intros; auto
	         end.

Definition opt_kl (u:T) V W (f : V ---> W ' u): V ' u ---> W ' u  := 
     fun t v => 
 match v with
 | none   => @none u _
 | some     t' v' => f t' v'
 end.

Obligation Tactic := unfold Proper; try red; 
               simpl; intros; elim_opt. 

Program Instance opt_monad_struct (u:T) : 
   Monad_struct  (fun V => opt u V) := {
  weta :=  @some u    ;
  kleisli := opt_kl (u:=u) 
                                      }.


Canonical Structure opt_monad u := Build_Monad (opt_monad_struct u).

Definition opt_default (u:T) (V W : ITYPE) (f : V ---> W) 
            (w: W u): V ' u ---> W := fun t v =>
  match v with
  | none => w
  | some t' v' => (f t' v')
  end.

End opt.

Ltac elim_opt := match goal with
                 | [ H : opt _ _ _|- _ ] => 
                       destruct H; simpl; intros; auto
                 | _ => simpl; intros; auto
	         end.

Section PostComp_w_Monad.

Section Der_Module.

Variable P : Monad ITYPE.

Existing Instance ITYPE_struct.

Definition shift (u:T) (V W: ITYPE) (f:V ---> P W) : 
          opt u V ---> P (opt u W):=
 (opt_default (u:=u) (V:=V) (W:=P (opt u W))
 (f ;; lift (weta (Monad_struct := (opt_monad u)) W))
 (weta (Monad_struct := P) (opt u W) u (none u W))).


Lemma shift_eq u V W (f g : V ---> P W) 
       (H : forall t x, f t x = g t x) :
   forall t (x : opt u V t) , shift f x = shift g x.
Proof. 
  simpl; intros;
  elim_opt; repeat rew_hyp_2;
  auto.
Qed.

Lemma shift_oid (u : T) V W : 
    Proper (equiv ==> equiv) (@shift u V W).
Proof.
  unfold Proper; 
  red; simpl;
  apply shift_eq.
Qed.

Lemma shift_weta (u:T)(V:ITYPE) (t : T) (x : opt u V t) :
      shift (u:=u) (weta (Monad_struct := P) V) (t:=t) x = 
            weta (Monad_struct := P) (opt u V) t x.
Proof.
  unfold shift;
  simpl; 
  intros;
  elim_opt;
  rew (lift_weta P).
Qed.

Lemma shift_weta_f (u:T) V W (f: V ---> W) t (x : opt u V t) : 
      shift (u:=u) (fun t x => weta (Monad_struct := P) W _ (f t x)) x =  
         weta (Monad_struct := P) _ _ (lift (M :=opt_monad u) f t x) .
Proof.
  simpl;
  intros;
  elim_opt;
  rew (lift_weta P).
Qed.

Lemma shift_kl u V W X (f : V ---> P W) (g : W ---> P X) t x :
       kleisli (*Monad_struct := P*) (shift g) _ (shift f (t:=t) x) =
            shift (u:=u) (fun t x => kleisli g _ (f t x)) x.
Proof.
  simpl;
  intros;
  elim_opt;
  try (rew (lift_kleisli (M:=P)));
  try (rew (kleisli_lift (M:=P)));
  try (rew (etakl P)).
Qed.

(*
Variable obD : Type.
Variable morD : obD -> obD -> Type.
Variable D: Cat_struct morD.
*)
Variable D : Cat.
Section Der_Module_def.

Variable M : MOD P D.

Program Instance IT_Der_Mod_struct (u:T) : 
        Module_struct P (D:=D) (fun V => M (opt u V)) := {
  mkleisli a b f := (mkleisli (Module_struct := M) (shift f)) 
                    
}.
Next Obligation.
Proof.
  unfold Proper; red.
  intros x y H.
  apply mkleisli_oid.
  simpl. intros.
  apply shift_eq.
  auto.
Qed.
Next Obligation.
Proof.
  rewrite mklmkl.
  apply mkleisli_oid.
  intros t x.
  simpl.
  rewrite  shift_kl.
  auto.
Qed.
Next Obligation.
Proof.
  rewrite <- mkl_weta.
  apply mkleisli_oid.
  simpl; intros.
  apply shift_weta.
Qed.

Canonical Structure IT_Der_Mod (u:T) : MOD P D := 
      Build_Module (IT_Der_Mod_struct u).

End Der_Module_def.

(** deriving a module wrt u:T yields a functor *)

Section Der_Module_Functor.

Section Der_Mod_Hom.

Variables M N: MOD P D.
Variable TT : M ---> N.

Program Instance ITDer_Mod_Hom_struct (u:T) : 
  Module_Hom_struct (S:=IT_Der_Mod M u) (T:=IT_Der_Mod N u)
            (fun _ => TT (*optP u x*) _ ) .
Next Obligation.
Proof.
  mod; try apply TT.
Qed.

Canonical Structure ITDer_Mod_Hom (u:T) : 
     IT_Der_Mod M u ---> IT_Der_Mod N u :=
           Build_Module_Hom 
           (ITDer_Mod_Hom_struct u).

End Der_Mod_Hom.

Obligation Tactic := 
 cat; try (match goal with | [ |- Proper _ _ ] => 
             unfold Proper; red end); 
    unfold ITDer_Mod_Hom; cat.

Program Instance ITDer_Mod_Func (u:T) : 
   Functor_struct (C:=MOD P D) (D:=MOD P D) 
        (Fobj:= fun z => IT_Der_Mod z u) 
        (fun M N TT => ITDer_Mod_Hom (M:=M) (N:=N) TT u).

Canonical Structure ITDER_MOD (u:T) := Build_Functor (ITDer_Mod_Func u).

End Der_Module_Functor.

Variable M: MOD P D.

Lemma itder_mlift_lift (u:T) (V W : ITYPE) (f:V ---> W): 
  #(ModFunc (IT_Der_Mod M u)) f == #(ModFunc M) (lift (M:=opt_monad u) f).
Proof.
  intros; simpl;
  unfold mlift; simpl.
  apply mkleisli_oid.
  simpl.
  intros.
  rew (shift_weta_f).
Qed.
  
End Der_Module.

Section shift_monad_hom.   

Variables P' Q : Monad ITYPE.
Variable f : Monad_Hom P' Q.

Notation "x >>- f" := (shift f x)(at level 60).

Lemma shift_monad_hom (a : T) V W (g : V ---> P' W) t (x : opt a V t) :
     f _ _ (x >>- g) = x >>- (g ;; f _ ).
Proof.
  simpl; intros;
  elim_opt;
  try (rew (NTcomm f));
  try (rew (mh_weta f)).
Qed.

End shift_monad_hom.

End PostComp_w_Monad.

(** Fibre Module:
     - P monad over IP
     - M module with codomain IP
     - M_u the u-fibre of M is a module with codomain PO *)

Section Fibre_module.
(*
Variable obC : Type.
Variable morC : obC -> obC -> Type.
Variable C : Cat morC.
*)
Variable C : Cat.
Variable P: Monad C.

Section Fibre_Module_def.

Variable M : MOD P ITYPE.

Obligation Tactic := cat;
   try (match goal with | [ |- Proper _ _ ] => 
             unfold Proper; red end); 
   cat;
   try (apply (mkl_eq M));
   try (rew (mklmkl M));
   try (rew (mklweta M));
   cat.

Program Instance ITFibre_Mod_struct (u:T) : 
       Module_struct P (*D:=TYPE*) (fun c => M c u) := {
  mkleisli a b f := mkleisli (Module_struct := M) f u
}.

Canonical Structure ITFibre_Mod (u:T) : MOD P TYPE := 
           Build_Module (ITFibre_Mod_struct u).


(** equality of types [t = u] gives a morphism of modules 
       [M[t] ---> M[u]] *)


End Fibre_Module_def.

Section Fibre_Module_Hom.
Variables M N : MOD P ITYPE.
Variable TT : M ---> N.

Obligation Tactic :=   simpl; intros;
  rew (mod_hom_mkl (Module_Hom_struct := TT)).


Program Instance ITFib_Mod_Hom_struct (u:T) : 
   Module_Hom_struct (S:= ITFibre_Mod M u )(T:= ITFibre_Mod N u)
    (fun z => TT z u).

Canonical Structure ITFib_Mod_Hom (u:T) : 
     ITFibre_Mod M u ---> ITFibre_Mod N u :=
        Build_Module_Hom (ITFib_Mod_Hom_struct u).

End Fibre_Module_Hom.

Obligation Tactic := unfold Proper; try red; cat.

Program Instance ITFib_Mod_Func (u:T) : 
   Functor_struct (C:=MOD P ITYPE) (D:=MOD P TYPE) 
        (Fobj:= fun x => ITFibre_Mod x u) 
        (fun M N TT => ITFib_Mod_Hom (M:=M) (N:=N) TT u).

Canonical Structure ITFIB_MOD (u:T) := Build_Functor (ITFib_Mod_Func u).

Section eq_type.

Variable M : MOD P ITYPE.

Variables t u : T.
Hypothesis H : t = u.

Obligation Tactic := simpl; rewrite H; auto.

Program Instance eq_type_fibre_mod_s : Module_Hom_struct
      (S := ITFIB_MOD t M) (T := ITFIB_MOD u M) 
        (fun x p => eq_rect t _ p u H).

Canonical Structure eq_type_fibre_mod :=
     Build_Module_Hom eq_type_fibre_mod_s.

Program Instance eq_type_fibre_mod_eta_s : Module_Hom_struct
      (S := ITFIB_MOD t M) (T := ITFIB_MOD u M) 
        (fun x p => eq_rect t (fun y => M x y) p u H).

Canonical Structure eq_type_fibre_mod_eta :=
     Build_Module_Hom eq_type_fibre_mod_eta_s.

End eq_type. 

End Fibre_module.


Section DER_PB.
Notation "Sig '*' M" := (PB_MOD Sig _ M).
Variables R S: Monad ITYPE.
Variable Sig: Monad_Hom R S.
(*
Variable obD: Type.
Variable morD: obD -> obD -> Type.
Variable D: Cat morD.
*)
Variable D : Cat.
Variable M: MOD S D.

Obligation Tactic :=  simpl; intros;
  rewrite idl;
  rewrite idr;
  apply mkleisli_oid;
  simpl; intros;
  elim_opt;
  try (rew (monad_hom_lift Sig));
  try (rew (mh_weta Sig)).

Program Instance ITPB_DER_struct (u:T) : 
  Module_Hom_struct 
     (S:= (PB_MOD Sig _ (ITDER_MOD _ _ u M)))
     (T:= ITDER_MOD _ _ u (PB_MOD Sig _ M))
          (fun e => id _) .

Definition ITPB_DER (u:T) : 
   PB_MOD Sig _ (ITDER_MOD _ _ u M) --->
                   ITDER_MOD _ _ u (PB_MOD Sig _ M) :=
         Build_Module_Hom (ITPB_DER_struct u).

Program Instance ITDER_PB_struct (u:T) : 
   Module_Hom_struct 
       (T:= (PB_MOD Sig _ (ITDER_MOD _ _ u M)))
       (S:= ITDER_MOD _ _ u (PB_MOD Sig _ M))
          (fun e => id _) .

Definition ITDER_PB (u:T) : ITDER_MOD _ _ u (PB_MOD Sig _ M) ---> 
                  PB_MOD Sig _ (ITDER_MOD _ _ u M) :=
         Build_Module_Hom (ITDER_PB_struct u).

Lemma ITDER_PB_PB_DER (u:T) : ITDER_PB u ;; ITPB_DER u == id _ .
Proof.
  cat.
Qed.

Lemma PB_DER_DER_PB (u:T) : ITPB_DER u ;; ITDER_PB u == id _.
Proof.
  cat.
Qed.

End DER_PB.

Section FIB_PB.

Notation "Sig '*' M" := (PB_MOD Sig _ M).

(*
Variable obC : Type.
Variable morC : obC -> obC -> Type.
Variable C : Cat morC.
*)
Variable C : Cat.
Variables R S: Monad C. (*ITYPE.*)
Variable Sig: Monad_Hom R S.
Variable M: MOD S ITYPE.

Program Instance ITPB_FIB_struct (u:T) : 
   Module_Hom_struct 
      (S:= (PB_MOD Sig _ (ITFIB_MOD _ u M)))
      (T:= ITFIB_MOD _ u (PB_MOD Sig _ M))
          (fun e => id _) .

Definition ITPB_FIB (u:T) : 
  PB_MOD Sig _ (ITFIB_MOD _ u M) ---> 
         ITFIB_MOD _ u (PB_MOD Sig _ M) :=
       Build_Module_Hom (ITPB_FIB_struct u).

Program Instance ITFIB_PB_struct (u:T) : 
  Module_Hom_struct 
       (T:= (PB_MOD Sig _ (ITFIB_MOD _ u M)))
       (S:= ITFIB_MOD _ u (PB_MOD Sig _ M))
          (fun e => id _) .

Definition ITFIB_PB (u:T) : 
   ITFIB_MOD _ u (PB_MOD Sig _ M) ---> 
        PB_MOD Sig _ (ITFIB_MOD _ u M) :=
    Build_Module_Hom (ITFIB_PB_struct u).

Lemma ITFIB_PB_PB_FIB (u:T) :
          ITFIB_PB u ;; ITPB_FIB u == id _ .
Proof.
  cat.
Qed.

Lemma ITPB_FIB_FIB_PB (u:T) : 
          ITPB_FIB u ;; ITFIB_PB u == id _ .
Proof.
  cat.
Qed.
  

Section FIB_DER_PM.
(*
Variable obD : Type.
Variable morD : obD -> obD -> Type.
Variable D : Cat morD.
*)
Variable D : Cat.
Variable Q : Monad D. (*ITYPE.*)
Variable F : Functor C D.
Variable Si : colax_Monad_Hom R Q F.
Variable N : MOD Q ITYPE.

Program Instance FIB_PM_struct s: Module_Hom_struct 
       (S := PModule Si (ITFIB_MOD _ s N))
       (T := ITFIB_MOD _ s (PModule Si N)) (fun _ => id _) .
                       
Definition FIB_PM s := Build_Module_Hom (FIB_PM_struct s).

Program Instance PM_FIB_struct s: Module_Hom_struct 
       (T := PModule Si (ITFIB_MOD _ s N))
       (S := ITFIB_MOD _ s (PModule Si N)) (fun _ => id _) .
                       
Definition PM_FIB s :
 ITFIB_MOD _ s (PModule Si N)  --->  PModule Si (ITFIB_MOD _ s N)  := 
          Build_Module_Hom (PM_FIB_struct s).

End FIB_DER_PM.

End FIB_PB.

Section substitution.

Variable R: Monad ITYPE.

Variable V: ITYPE.
Variable r: T.
Variable W : R V r.

Definition ITsubst_map := opt_default 
          (weta (Monad_struct:=R) _ ) W.

Definition ITsubstar := kleisli (ITsubst_map).

End substitution.

End indexed_types.

Ltac elim_opt := match goal with
                 | [ H : opt _ _ _|- _ ] => 
                       destruct H; simpl; intros; auto
                 | _ => simpl; intros; auto
	         end.












