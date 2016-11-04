
Require Export CatSem.CAT.Misc.
Require Export CatSem.CAT.monad_h_morphism.
Require Export CatSem.CAT.NT.
Require Export CatSem.CAT.product.
Require Export CatSem.CAT.initial_terminal.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

(** a (post)module over a (haskell style) monad *)

Ltac mod := intros; autorewrite with monad mod; auto with mod monad.

Section Module_def.
(*
Variables obC: Type.
Variable morC : obC -> obC -> Type.
Variable C: Cat morC.
*)

Variable C : Cat.

Section fix_monad.

Variable P: Monad C.

Section mod_d.
(*
Variable obD: Type.
Variable morD: obD -> obD -> Type.
Variable D: Cat_struct morD.
*)

Variable D : Cat.

Class Module_struct (M:C -> D) := {
  mkleisli: forall c d (f:c ---> P d), M c ---> M d;
  mkleisli_oid :> forall c d, Proper (equiv ==> equiv) 
                    (mkleisli (c:=c)(d:=d));
  mkl_mkl: forall c d e (f:  c ---> P d) (g:d ---> P e),
         mkleisli f ;; mkleisli g == mkleisli (f ;; kleisli g);
  mkl_weta: forall c:C, mkleisli (weta c) == id (M c) 
}.

Record Module := {
  mod_carrier :> C -> D;
  module_struct :> Module_struct mod_carrier
}.

Existing Instance module_struct.

Section fix_mod.

Variable M : C -> D.
Variable H : Module_struct M.

Lemma mkl_eq c d (f g : c ---> P d) : 
         f == g -> mkleisli f == mkleisli g.
Proof.
  intros; apply H; auto.
Qed.

Lemma mklmkl c d e (f : c ---> P d) 
       (g : d ---> P e) :
    mkleisli f ;; mkleisli g == mkleisli (f ;; kleisli g).
Proof.
  intros;
  apply H; auto.
Qed.

Lemma mklweta c : mkleisli (weta c) == id (M c).
Proof.
  intros;
  apply H; 
  auto.
Qed.

Hint Resolve mkl_eq : cat.

Section mlift.

Definition mlift (c d:C) (f:c ---> d) : M c ---> M d := 
        mkleisli  (f ;; weta d ).

Lemma mlift_eq c d (f g : c ---> d) : f == g -> mlift f == mlift g.
Proof.
  unfold mlift. 
  cat.
Qed.

Instance mlift_oid c d : Proper (equiv ==> equiv) (@mlift c d) :=
        @mlift_eq c d.

End mlift.

Hint Rewrite @mkl_mkl @mkl_weta : mod.

Ltac mod :=  simpl in *; intros; 
             autorewrite with monad mod; 
             auto with mod monad.

Hint Resolve @mkl_mkl @mkl_weta mkl_eq : mod.

Lemma mlift_mkleisli c d e (f: c ---> P d) (g: d ---> e) :
  mkleisli f ;; mlift g == mkleisli (f ;; lift g).
Proof.
  unfold mlift;
  mod.
Qed.

Lemma mkleisli_mlift c d e (f: c ---> d) (g: d ---> P e) : 
  mlift f ;; mkleisli g == mkleisli (f ;; g).
Proof.
  unfold mlift; mod.
Qed.

Lemma mlift_mlift c d e (f: c ---> d) (g: d ---> e) : 
  mlift f ;; mlift g == mlift (f ;; g).
Proof.
  unfold mlift; mod.
Qed.

(*End ModuleDefsFacts.*)

Hint Rewrite @mlift_mlift @mkleisli_mlift @mlift_mkleisli : mod.


(** a module is a functor, isn't it ? *)
Existing Instance mlift_oid.

Obligation Tactic := unfold mlift ; mod.

Program Instance ModFunc_struct : Functor_struct (C:=C) (D:=D) (mlift).

Canonical Structure ModFunc := Build_Functor ModFunc_struct.

End fix_mod.

Existing Instance ModFunc_struct.

(** module morphisms *)
Section Module_Hom.

Variables S T: Module.

Class Module_Hom_struct (N: forall x, S x ---> T x) := {
  mod_hom_mkl: forall c d (f: c ---> P d),
        mkleisli f ;; N _ == N _ ;; mkleisli  f
}. 

Record Module_Hom := {
  module_hom:> forall x, S x ---> T x;
  module_hom_struct :> Module_Hom_struct module_hom
}.

Section Module_Hom_NT.

Variable X : Module_Hom.

Obligation Tactic := cat; unfold mlift;
  repeat rew (mod_hom_mkl (Module_Hom_struct := X)); cat.

Program Instance Module_Hom_NatTrans : 
   NT_struct (F:=ModFunc S)(G:=ModFunc T)(fun c => X c).

Canonical Structure Module_Hom_NT := Build_NT Module_Hom_NatTrans.

End Module_Hom_NT.

End Module_Hom.

Existing Instance module_hom_struct.

Hint Resolve mod_hom_mkl : mod.
Hint Rewrite mod_hom_mkl : mod.

(** MOD P D is the category of Modules over monad P with codomain D *)

Obligation Tactic := cat.

Program Instance Id_Mod_struct (M: Module): 
         Module_Hom_struct (S:=M)(T:=M) (fun x => id _) .

Canonical Structure Id_Mod (M:Module) := 
                Build_Module_Hom (Id_Mod_struct M).

Section Mod_Hom_comp.
Variables M N K : Module.
Variable S : Module_Hom M N.
Variable T : Module_Hom N K.

Obligation Tactic := intros; repeat rewrite <- assoc;
      repeat rewrite mod_hom_mkl; mod; try apply S; try apply T.

Program Instance CompMod_struct : 
     Module_Hom_struct  (fun x => S x ;; T x).

Canonical Structure CompMod := Build_Module_Hom CompMod_struct.

End Mod_Hom_comp.

Lemma Mod_Hom_oid (M N: Module) : 
        Equivalence (A:=Module_Hom M N) 
       (fun S T => forall c, S c == T c).
Proof.
  intros;
  constructor;
   unfold Reflexive,
          Symmetric,
          Transitive;
  simpl; intros;
  repeat rew_setoid;
  try reflexivity.
Qed.

Definition eq_Mod_Hom (M N : Module) := 
             Build_Setoid (Mod_Hom_oid M N).

Obligation Tactic := cat; try apply assoc;
  try unf_Proper; cat; repeat rew_setoid; cat.

Program Instance MOD_struct : 
        Cat_struct (@Module_Hom) := {
  mor_oid M N := eq_Mod_Hom M N;
  id N := Id_Mod N;
  comp a b c f g := CompMod f g
}.

Canonical Structure MOD := Build_Cat MOD_struct.

Section Prod_Mod.

Notation "a 'x' b" := (product a b) (at level 30).
Notation "a 'X' b" := (product_mor _ a b) (at level 30).


Variable H: Cat_Prod D.

Section Prod_Mod_def.

Variable M N: MOD.

Obligation Tactic := idtac.

Program Instance Prod_Mod_struct: 
     Module_struct (fun a => M a x N a) := {
   mkleisli c d f :=  (mkleisli f) X (mkleisli f)
}.
Next Obligation.
Proof.
  unfold Proper; red;
  intros;
  unfold product_mor;
  apply prod_mor_oid;
  repeat match goal with [H: _ == _ |- _ ] => rewrite H end;
  cat.
Qed.
Next Obligation.
Proof.
  intros; simpl;
  rewrite <- product_mor_product_mor;
  repeat rewrite mkl_mkl;
  cat.
Qed.
Next Obligation.
Proof.
  intros;
    cat.
    repeat rewrite mkl_weta; 
  
  apply product_mor_id;
  cat.
Qed.

Canonical Structure Prod_Mod : MOD := Build_Module Prod_Mod_struct.

Obligation Tactic := cat; unfold product_mor; 
       repeat rewrite prod_prl;
       repeat rewrite prod_prr; cat.

Program Instance Mod_prl_struct : Module_Hom_struct (S:=Prod_Mod) (T:=M)  
        (fun c => prl _ _ ).

Canonical Structure Mod_prl : Prod_Mod ---> M := 
         Build_Module_Hom Mod_prl_struct.

Program Instance Mod_prr_struct : Module_Hom_struct (S:=Prod_Mod) (T:=N)  
        (fun c => prr _ _ ).

Canonical Structure Mod_prr : Prod_Mod ---> N := 
        Build_Module_Hom Mod_prr_struct.

End Prod_Mod_def.

Section Mod_prod_mor.

Variables M N K: MOD.
Variables (S : M ---> N) 
          (T : M ---> K).

Program Instance Mod_prod_mor_struct : Module_Hom_struct 
       (S:=M) (T:=Prod_Mod N K) (fun c => prod_mor (S c) (T c)).
Next Obligation.
Proof.
  simpl; intros;
  rewrite prod_mor_product_mor;
  apply prod_mor_unique;
  repeat rewrite assoc;
  rewrite prod_prl;
  rewrite prod_prr;
  mod; try apply S;
      try apply T;
  cat.
Qed.

Canonical Structure Mod_Prod_mor : M ---> Prod_Mod N K := 
          Build_Module_Hom Mod_prod_mor_struct.

End Mod_prod_mor.

Obligation Tactic := cat; try unf_Proper; cat;
   unfold Mod_Prod_mor; cat; elim_conjs; cat;
   repeat rew_setoid; cat.

Hint Extern 3 (_ == prod_mor _ _ ) => apply prod_mor_unique.

Program Instance MOD_PROD : Cat_Prod MOD := {
  product M N := Prod_Mod M N;
  prl M N := Mod_prl M N;
  prr M N := Mod_prr M N;
  prod_mor a c d f g := Mod_Prod_mor f g
}.

End Prod_Mod.

Section Const_Mod.

Variable d : D.

Instance const_mod_oid c c' : 
   Proper (equiv ==> equiv) (fun _ :  c ---> P c' => id d).
Proof.
  unfold Proper;
  red; cat.
Qed.

Existing Instance const_mod_oid.

Obligation Tactic :=  try apply const_mod_oid; cat.

Program Instance Const_Mod_struct : 
      Module_struct (fun c => d) := {
  mkleisli a b f := id _
}.

Canonical Structure Const_Mod : MOD := Build_Module Const_Mod_struct.

End Const_Mod.


Section MOD_terminal.

Variable H: Terminal D.

Definition MOD_Term : MOD := Const_Mod Term.

Obligation Tactic := cat; apply TermMorUnique.

Program Instance MOD_TermMor_struct (A: MOD) : 
      Module_Hom_struct (S:=A) (T:=MOD_Term) (fun x => TermMor (A x)) .

Canonical Structure MOD_TermMor (A: MOD) : A ---> MOD_Term := 
          Build_Module_Hom (MOD_TermMor_struct A).

Program Instance MOD_Terminal : Terminal (MOD) := {
  Term := MOD_Term;
  TermMor A := MOD_TermMor A
}.

End MOD_terminal.


End mod_d.


Hint Resolve mklmkl mklweta mod_hom_mkl mkl_eq : mod.
Hint Rewrite mklmkl mklweta mod_hom_mkl : mod.

Existing Instance MOD_struct.

(** a monad is a module over itself, the tautological module *)

Section Taut_Mod.

Program Instance Taut_Mod_struct : 
       Module_struct  P := {
  mkleisli c d f := kleisli (Monad_struct:=P) f;
  mkleisli_oid c d := kleisli_oid (a:=c)(b:=d);
  mkl_mkl c d e f g := dist f g;
  mkl_weta c :=  kl_eta (Monad_struct := P) c
}.

Canonical Structure Taut_Mod : MOD C := Build_Module Taut_Mod_struct.
Canonical Structure Taut_Mod2 := Build_Module Taut_Mod_struct.


End Taut_Mod.

End fix_monad.


Hint Resolve mklmkl mklweta mod_hom_mkl mkl_eq : mod.
Hint Rewrite mklmkl mklweta mod_hom_mkl : mod.


(** given two monads P, Q and a module M over Q and h: P -> Q, 
     we can pull back M along h *)

Existing Instance module_struct.
Existing Instance monad_hom_struct.

Section Pullback_Mod.

Variables P Q : Monad C.
Variable h : Monad_Hom P Q.

Section fix_D.
(*
Variable obD: Type.
Variable morD: obD -> obD -> Type.
Variable D: Cat_struct morD.
*)
Variable D : Cat.

Section PB_on_objects.

Variable M: MOD Q D.

Obligation Tactic := mod; try unf_Proper; cat; 
         repeat rew_set; cat; try apply h.

Program Instance PbMod_struct : Module_struct P (D:=D) M := {
  mkleisli c d f:= mkleisli (f ;; h d) 
                                                           }.
Next Obligation.
  (* why ? *)
  mod; try unf_Proper; cat; 
    repeat rew_set; cat; try apply h.
Qed.

Canonical Structure PbMod : MOD P D := Build_Module PbMod_struct.

End PB_on_objects.

Section PbMod_Hom.

Variables M N: MOD Q D.
Variable r : M ---> N.

Obligation Tactic := simpl; mod; try apply r.

Program Instance PbMod_Hom_struct : 
        Module_Hom_struct (S:=PbMod M) (T:=PbMod N) r. 

Canonical Structure PbMod_Hom : PbMod M ---> PbMod N := 
          Build_Module_Hom PbMod_Hom_struct.

End PbMod_Hom.

Obligation Tactic := unfold Proper; red; mod; cat.

Program Instance PB_MOD_struct : Functor_struct 
       (C:=MOD _ _ ) (Fobj:= @PbMod )
              (fun a b f => PbMod_Hom f).

Definition PB_MOD := Build_Functor PB_MOD_struct.

Section Isos.

Variable HD: Cat_Prod D.
Variables M N: MOD Q D.

Existing Instance MOD_PROD.

Notation "a 'x' b" := (product a b) (at level 50).
Notation "'h*' M" := (PB_MOD M) (at level 20).

Obligation Tactic := mod.

(* Goal (forall e, (h* (M x N)) e = (h* M x h* N) e). *)
(*   intro e. *)
(*   reflexivity. *)

(* don't know why it does not work *)
Definition distrib : forall e:C, ((h* (M x N)) e) ---> ((h* M x h* N) e) := (fun e => id (Cat_struct:= D)  ((h* (M x N)) e)) .

Program Instance PB_PROD_struct : 
  Module_Hom_struct (S:= h* (M x N)) (T:= h* M x h* N) distrib.


Definition PB_PROD : h* (M x N) ---> (h* M x h* N) :=
           Build_Module_Hom PB_PROD_struct.

Definition facto : forall e:C, (h* M x h* N) e ---> ((h* (M x N)) e)  := (fun e => id (Cat_struct:= D)  ((h* (M x N)) e)) .
Program Instance PROD_PB_struct : 
       Module_Hom_struct (S:= h* M x h* N) (T:= h* (M x N)) facto.


Definition PROD_PB : (h* M x h* N) ---> h* (M x N) :=
     Build_Module_Hom PROD_PB_struct.

Lemma PROD_PB_PB_PROD : PROD_PB ;; PB_PROD == id _ .
Proof.
  cat.
Qed.

Lemma PB_PROD_PROD_PB : PB_PROD ;; PROD_PB == id _.
Proof.
  cat.
Qed.

End Isos.

End fix_D.

Section PB_ind_Mod.

Obligation Tactic := simpl; mod; try apply h.

Program Instance PbMod_ind_Hom_struct : 
      Module_Hom_struct (S:=Taut_Mod P) (T:=PB_MOD _ (Taut_Mod Q)) (h).

Canonical Structure PbMod_ind_Hom : 
   Taut_Mod P ---> PB_MOD _ (Taut_Mod Q) := 
 Build_Module_Hom PbMod_ind_Hom_struct.

End PB_ind_Mod.


(** Product of Modules 
    - monad P
    - D has products
    - modules M N : C -> D 
    - module (M x N) : c -> M c x N c 
*)




(** constant module *)


(**  given C:Cat , P : Monad C ,
    we have a terminal object in MOD *)


Existing Instance MOD_Terminal.

Section terminal_pullback.
(*
Variable obD : Type.
Variable morD : obD -> obD -> Type.
Variable D : Cat_struct morD.
*)
Variable D : Cat.
Variable H : Terminal D.

Variable M : MOD Q D.

Obligation Tactic := cat.

Program Instance id_Term_PB_struct: 
   Module_Hom_struct 
     (S:= Term (C:= MOD P D))  
     (T:=(PB_MOD D (Term (C:=MOD Q D)))) 
     (fun _ => id (Term (C:=D))). 
 
Definition PBT : Term ---> (PB_MOD _ Term) :=
      Build_Module_Hom id_Term_PB_struct.

Program Instance id_PT_Term_struct: 
   Module_Hom_struct 
      (T:= Term (C:= MOD _ D)) 
      (S:=(PB_MOD _ (Term (C:=MOD _ D))))  
      (fun r => id (Term (C:=D))).

Definition TPB : (PB_MOD _ Term) ---> Term := 
      Build_Module_Hom id_PT_Term_struct.

End terminal_pullback.
End Pullback_Mod.
End Module_def.


Hint Resolve mklmkl mklweta mod_hom_mkl mkl_eq : mod.
Hint Rewrite mklmkl mklweta mod_hom_mkl : mod.


Existing Instance module_struct.
Existing Instance MOD_Terminal.
Existing Instance MOD_PROD.
Existing Instance MOD_struct.
Existing Instance PB_MOD_struct.
Existing Instance eq_Mod_Hom.
Existing Instance Module_Hom_NatTrans.
Existing Instance monad_hom_struct.
Existing Instance module_hom_struct.
Existing Instance mlift_oid.
Coercion Taut_Mod: Monad >-> obj.
Coercion Taut_Mod2 : Monad >-> Module.
Coercion ModFunc : Module_struct >-> Functor.
Coercion Module_Hom_NT : Module_Hom >-> NT.








