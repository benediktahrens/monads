
Require Export CatSem.CAT.ind_potype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.


(** for module M, we define [IPO_Der_Mod M], the derived module *)

Section fixatype.

Variable T : Type.

Section Der_Module.

Variable P : Monad (IPO T).
(*
Variable obD : Type.
Variable morD : obD -> obD -> Type.
Variable D: Cat morD.
*)
Variable D : Cat.
Section Der_Module_def.

Variable M : MOD P D.

Obligation Tactic := idtac.

Program Instance IPO_Der_Mod_struct (u:T) : 
        Module_struct P (fun V => M (opt_TP u V)) := {
  mkleisli a b f := (mkleisli (M:=M)(opt_TP_def_varinj u f)) 
}.
Next Obligation.
Proof.
  unfold Proper; red.
  intros u c d z y H.
  apply mkleisli_oid.
  simpl; intros.
  elim_opt.
  rewrite H;
  auto.
Qed.
Obligation 3.
Proof.
  intros; simpl.
  rewrite opt_TP_def_varinj_weta.
  mod.
Qed. 
Next Obligation.
Proof.
  simpl; intros.
  rewrite mkl_mkl.
  apply mkleisli_oid.
  unfold opt_TP_def_varinj.
  simpl; intros.
  elim_opt.
  rew (lift_kleisli (M:=P)).
  rew (kleisli_lift (M:=P)).
  apply (kl_eq P).
  simpl; auto.
  
  rew (eta_kl (Monad_struct := P)).
Qed.

Canonical Structure IPO_Der_Mod (u:T) : MOD P D := 
      Build_Module (IPO_Der_Mod_struct u).


End Der_Module_def.

(** deriving a module wrt u:T yields a functor *)

Section Der_Module_Functor.

Section Der_Mod_Hom.

Variables M N: MOD P D.
Variable TT : M ---> N.

Obligation Tactic := simpl; mod; try apply TT.

Program Instance Der_Mod_Hom_struct (u:T) : 
  Module_Hom_struct (S:=IPO_Der_Mod M u) (T:=IPO_Der_Mod N u)
            (fun _ => TT (*opt_TP u x*) _ ) .

Canonical Structure Der_Mod_Hom (u:T) : 
     IPO_Der_Mod M u ---> IPO_Der_Mod N u :=
           Build_Module_Hom 
           (Der_Mod_Hom_struct u).

End Der_Mod_Hom.

Obligation Tactic := simpl; intros; 
    try (match goal with [|-Proper _ _ ] => unfold Proper; red end);
    cat.

Program Instance Der_Mod_Func (u:T) : 
   Functor_struct (C:=MOD P D) (D:=MOD P D) 
        (Fobj:= fun z => IPO_Der_Mod z u) 
        (fun M N TT => Der_Mod_Hom (M:=M) (N:=N) TT u).

Canonical Structure DER_MOD (u:T) := Build_Functor (Der_Mod_Func u).

End Der_Module_Functor.

End Der_Module.

Section Fibre_module.

Variable P: Monad (IPO T).

Section Fibre_Module_def.

Variable M : MOD P (IPO T).

Obligation Tactic := 
    cat; 
    try (match goal with [|- Proper _ _ ] => do 2 red end);
    cat;
    try apply (mkl_eq M);
    try rew (mklmkl M); try rew (mklweta (P:=P) (M:=M)); auto.

Program Instance Fibre_Mod_struct (u:T) : 
       Module_struct P  (fun c => IP_proj u (M c)) := {
  mkleisli a b f := #(IP_proj u) (@mkleisli _ P  _ M M  a b f)  
}.

Canonical Structure Fibre_Mod (u:T) : MOD P Ord := 
           Build_Module (Fibre_Mod_struct u).

End Fibre_Module_def.

Section Fibre_Module_Hom.
Variables M N : MOD P (IPO T).
Variable TT : M ---> N.

Obligation Tactic := simpl; intros; 
   rew (mod_hom_mkl (Module_Hom_struct := TT)).

Program Instance Fib_Mod_Hom_struct (u:T) : 
   Module_Hom_struct (S:= Fibre_Mod M u )(T:= Fibre_Mod N u)
    (fun z => #(IP_proj u) (TT z) ).

Canonical Structure Fib_Mod_Hom (u:T) : 
     Fibre_Mod M u ---> Fibre_Mod N u :=
        Build_Module_Hom (Fib_Mod_Hom_struct u).

End Fibre_Module_Hom.

Obligation Tactic := repeat red; simpl; auto.

Program Instance Fib_Mod_Func (u:T) : 
   Functor_struct (C:=MOD P (IPO T)) (D:=MOD P Ord) 
        (Fobj:= fun x => Fibre_Mod x u) 
        (fun M N TT => Fib_Mod_Hom (M:=M) (N:=N) TT u).

Canonical Structure FIB_MOD (u:T) := Build_Functor (Fib_Mod_Func u).

End Fibre_module.

Section DER_PB.

Notation "Sig '*' M" := (PB_MOD Sig _ M).
Variables R S: Monad (IPO T).
Variable Sig: Monad_Hom R S.
(*
Variable obD: Type.
Variable morD: obD -> obD -> Type.
Variable D: Cat morD.
*)
Variable D : Cat.
Variable M: MOD S D.

Obligation Tactic := cat;
    apply mkleisli_oid; simpl; intros; elim_opt;
    try rew (monad_hom_lift Sig); 
    rew(monad_hom_weta (Monad_Hom_struct := Sig)).

Program Instance PB_DER_struct (u:T) : 
  Module_Hom_struct 
      (S:= (PB_MOD Sig _ (DER_MOD _ _ u M)))
      (T:= DER_MOD _ _ u (PB_MOD Sig _ M))
          (fun e => id _) .

Definition PB_DER (u:T) : PB_MOD Sig _ (DER_MOD _ _ u M) ---> 
                            DER_MOD _ _ u (PB_MOD Sig _ M) :=
         Build_Module_Hom (PB_DER_struct u).

Program Instance DER_PB_struct (u:T) : 
  Module_Hom_struct 
    (T:= (PB_MOD Sig _ (DER_MOD _ _ u M)))
    (S:= DER_MOD _ _ u (PB_MOD Sig _ M))
          (fun e => id _) .

Definition DER_PB (u:T) : DER_MOD _ _ u (PB_MOD Sig _ M) ---> 
                  PB_MOD Sig _ (DER_MOD _ _ u M) :=
         Build_Module_Hom (DER_PB_struct u).

Lemma DER_PB_PB_DER (u:T) : DER_PB u ;; PB_DER u == id _ .
Proof.
  cat.
Qed.

Lemma PB_DER_DER_PB (u:T) : PB_DER u ;; DER_PB u == id _.
Proof.
  cat.
Qed.

End DER_PB.

Section FIB_PB.

Notation "Sig '*' M" := (PB_MOD Sig _ M).
Variables R S: Monad (IPO T).
Variable Sig: Monad_Hom R S.
(*
Variable obD: Type.
Variable morD: obD -> obD -> Type.
Variable D: Cat morD.
*)
Variable M: MOD S (IPO T).

Obligation Tactic := cat.

Program Instance PB_FIB_struct (u:T) : 
   Module_Hom_struct 
   (S:= (PB_MOD Sig _ (FIB_MOD _ u M)))
   (T:= FIB_MOD _ u (PB_MOD Sig _ M))
          (fun e => id _) .

Definition PB_FIB (u:T) : 
PB_MOD Sig _ (FIB_MOD _ u M) ---> FIB_MOD _ u (PB_MOD Sig _ M) :=
          Build_Module_Hom (PB_FIB_struct u).

Program Instance FIB_PB_struct (u:T) : 
  Module_Hom_struct 
   (T:= (PB_MOD Sig _ (FIB_MOD _ u M)))
   (S:= FIB_MOD _ u (PB_MOD Sig _ M))
          (fun e => id _) .

Definition FIB_PB (u:T) : 
FIB_MOD _ u (PB_MOD Sig _ M) ---> PB_MOD Sig _ (FIB_MOD _ u M) :=
          Build_Module_Hom (FIB_PB_struct u).

Lemma FIB_PB_PB_FIB (u:T) : 
          FIB_PB u ;; PB_FIB u == id _ .
Proof.
  cat.
Qed.

Lemma PB_FIB_FIB_PB (u:T) : 
          PB_FIB u ;; FIB_PB u == id _ .
Proof.
  cat.
Qed.
  
End FIB_PB.

End fixatype.

Existing Instance Fib_Mod_Func.


