Require Export CatSem.CAT.monad_h_module. 
Require Export CatSem.CAT.ind_potype.
Require Export CatSem.CAT.NT. 
Require Export CatSem.CAT.nat_iso.
Require Export CatSem.CAT.CatFunct.
(* Require Export pcfpo_mod. *)
Require Export setoid_lemmata.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Automatic Introduction.

(** we now do everything 2-dimensionally *)

(** a monad is a couple of monads *)

(** most important: names
   - PMon 
   - PMon_Hom
   - PMod
   - PMod_Hom
   - PPbMod
   - ...
*)

Section defs.

Variable T: Type.

Let IP := (IPO T).
Let IT := (ITYPE T).
Let OIP := (OIP T).

Let PMonad := Monad IP.
Let TMonad := Monad IT.

Implicit Arguments kleisli [obC morC C F a b].
Implicit Arguments weta [obC morC C F].
Implicit Arguments mkleisli [obC morC C P obD morD D M c d].

Section PMon.


(** parallel monad, which is basically two monads, connected via O_Mon *)

(* perhaps O_Mon will need to be an isomorphism ? *)

Class PMon_struct (R : PMonad) := {
   
   SMon : TMonad;
   O_Mon : (OIP O (MFunc R)) ---> ((MFunc SMon) O OIP) ;

   O_pp_we: forall c, #OIP (weta R c) ;; O_Mon _ ==
                  weta SMon (OIP c)  ;

   O_pp_kl: forall c d (f: c ---> R d), 
       #OIP (kleisli R f) ;; O_Mon _  ==
         O_Mon _ ;; kleisli SMon (#OIP f ;; O_Mon d ) 
             

}.

Record PMon := {
  PMon_carrier :> Monad IP;
  pmon_struct :> PMon_struct PMon_carrier
}.

End PMon.



Existing Instance pmon_struct.




Section PMon_Hom.

(** a morphism of parallel monads is a couple of monad_homs 
   such that something commutes *)

Variables P R : PMon.

Class PMon_Hom_struct (M:Monad_Hom P R) 
         (N: Monad_Hom (SMon (R:=P)) (SMon (R:=R))):= {
  O_hom_comm : forall c, #OIP (M c);; O_Mon _  == O_Mon _ ;; N (OIP c)
}. 

Record PMon_Hom := {
  PMon_ip :> Monad_Hom P R;
  PMon_it :> Monad_Hom (SMon (R:=P)) (SMon (R:=R)) ;
  pmon_hom_struct : PMon_Hom_struct PMon_ip PMon_it
}.

End PMon_Hom.

Existing Instance pmon_hom_struct.

Section PModules.

Variable P: PMon.

Section PModIP.

(** a parallel module over a parallel monad is 
    - a couple of modules
    - a compatibility NT (which should probably be an iso)
    - compatibility condition for mkleisli
*)

Class PModIP_struct (M: MOD P IP) := {
  SModIP : MOD (SMon (R:=P)) IT ;
  O_ModIP : (OIP O (ModFunc M)) ---> ((ModFunc SModIP) O OIP);
  O_pp_mkl : forall c d (f: c ---> P d), 
       #OIP (mkleisli M f) ;; O_ModIP _  ==
         O_ModIP _ ;; mkleisli SModIP (#OIP f ;; O_Mon d ) 
             
}.

Record PModIP := {
  PModIP_carrier :> MOD P IP;
  pmodip_struct :> PModIP_struct PModIP_carrier
}.

End PModIP.

Existing Instance pmodip_struct.

Implicit Arguments SModIP [PModIP_struct].

Section PModIP_Hom.

Implicit Arguments SModIP [M].

Variables M N : PModIP.

(** a morphism of parallel modules is a couple of morphisms of modules
    such that something commutes 
*)

Class PModIP_Hom_struct (R: M ---> N) (S: SModIP M ---> SModIP N) := {
   O_modhom_comm : forall c, 
         #OIP (R c);; O_ModIP _  == O_ModIP _ ;; S (OIP c)
}.

Record PModIP_Hom := {
  PModIP_ip : M ---> N;
  PModIP_it : SModIP M ---> SModIP N ;
  pmodip_hom_struct :> PModIP_Hom_struct PModIP_ip PModIP_it
}.

Existing Instance pmodip_hom_struct.

(** we call two morphisms of parallel modules equal if 
    both their components are equal as modules 
*)

Lemma PModIP_Hom_equiv : @Equivalence PModIP_Hom
     (fun a b => PModIP_ip a == PModIP_ip b /\ 
                 PModIP_it a == PModIP_it b).
Proof.
  constructor.
  unfold Reflexive; intros; 
  split; setoid.
  unfold Symmetric;
  split; setoid.
  unfold Transitive;
  split; setoid.
Qed.

Definition PModIP_Hom_oid := Build_Setoid PModIP_Hom_equiv.

End PModIP_Hom.
Existing Instance pmodip_hom_struct.
Section PModIP_Homs.

Variable M:PModIP.

(** Identity and composition for parallel module morphisms *)

Program Instance PModIP_id_struct : 
   PModIP_Hom_struct (id (Cat:= MOD _ _ ) M) (id (@SModIP _ M)).

Definition PModIP_id := Build_PModIP_Hom PModIP_id_struct.

Variables N K : PModIP.
Variables (R:PModIP_Hom M N) (S:PModIP_Hom N K).

Program Instance PModIP_comp_struct : 
    PModIP_Hom_struct ((PModIP_ip R) ;; (PModIP_ip S)) 
                      ((PModIP_it R) ;; (PModIP_it S)).
Next Obligation.
Proof.
  set (HR := pmodip_hom_struct R).
   destruct HR as [Hr].
   simpl in Hr.
   rewrite <- Hr.
  set (HS:= pmodip_hom_struct S).
   destruct HS as [Hs].
   simpl in Hs.
   rewrite <- Hs. auto.
Qed.

Definition PModIP_comp := Build_PModIP_Hom PModIP_comp_struct.

End PModIP_Homs.

(** category of parallel modules with cod IP *)

Program Instance PMODIP_struct : Cat PModIP_Hom := {
  mor_oid := PModIP_Hom_oid;
  comp := PModIP_comp;
  id := PModIP_id
}.
Next Obligation.
Proof.
  unfold Proper; do 2 red.
  simpl.
  intros.
  destruct H as [H1 H2].
  destruct H0 as [H3 H4].
  split; intros.
  rewrite H1,H3; auto.
  rewrite H2,H4; auto.
Qed.

Definition PMODIP := Build_Category PMODIP_struct.

(** tautological PModule : P is a PModIP*)

Program Instance PTaut_NatTrans : 
NatTrans (F:= OIP O ModFunc P) (G:= ModFunc SMon O OIP)
  (fun c => (O_Mon c)).
Next Obligation.
Proof.
  set (H:= trafo_ax (NatTrans := O_Mon (PMon_struct := P))).
  simpl in H.
  unfold mlift,lift in *. simpl in *.
  rewrite <- H.
  auto.
Qed.

Program Instance PTautMod_struct : 
  PModIP_struct (PMon_carrier P) := {
  SModIP := Taut_Mod (SMon );
  O_ModIP := Build_NT PTaut_NatTrans;
  O_pp_mkl := O_pp_kl
}.
(*
Next Obligation.
Proof.
  set (H:= O_pp_kl (PMon_struct := P)).
  simpl in H.
  apply H.
Qed.
*)

Definition PTautMod : PMODIP := Build_PModIP PTautMod_struct.


(** now some functors *)

(** derived module *)

Section Pder_mod.

Section on_objects.

Variable u: T.
Variable M : PMODIP.


Let ITdm := IT_Der_Mod (T:=T) (P:=SMon)(D:=IT) 
   (SModIP M (PModIP_struct:=M)) u.
Let IPdm := IPO_Der_Mod (T:=T) (P:=P)(D:=IP) M u.

(*
Notation "'ITdm'" := (@IT_Der_Mod T _ _ _ (ITYPE_struct T)).
Notation "'IPdm'" := (@IPO_Der_Mod T _ _ _ (IND_PO_struct T)).
*)
(*
Let IPModF := ModFunc (P:= P) IPdm.
Let ITModF := ModFunc (P:= SMon (PMon_struct := P)) ITdm.

*)
(*
Definition bla: 
(forall c : IPO T, (OIP O ModFunc IPdm) c ---> (ModFunc ITdm O OIP) c).
intros.
set (H:=O_ModIP (PModIP_struct:=M)).
simpl.
apply (H (opt_TP u c)).
Defined.
*)

(*
Lemma mlift_lift V W (f: V ---> W): mlift ITdm f == 
*)
Program Instance PDerMod_NatTrans : 
    NatTrans (F:= OIP O ModFunc IPdm) (G:=ModFunc ITdm O OIP) 
                   (fun c => O_ModIP (opt_TP u c)).
Next Obligation.
Proof.
  set (H':= trafo_ax (NatTrans := O_ModIP (PModIP_struct := M))).
(*  intros c d f.*)
  set (H2:= itder_mlift_lift (SModIP M (PModIP_struct := M)) u).
  set (H3:=mkleisli_oid (Module_struct := PModIP_carrier M)). 
  simpl in *.
  unfold ITdm.
(*  intros t x.*)
  rewrite H2.
  unfold mlift.
  simpl.
  set (h := H' (opt_TP u c) (opt_TP u d) (lift (M:= opt_TP_monad u) f)).
  simpl in *.
  unfold mlift in h.
  rewrite h.
  apply f_equal.
  unfold Proper in H3. red in H3.
  simpl in H3.
  apply (H3 _ (opt_TP u d)).
  set (H4 := opt_TP_def_varinj_weta_f).
  simpl in *.
  intros t0 z.
  destruct z; simpl; auto.
  set (Hx:= lift_weta P).
  simpl in *.
  rewrite Hx. simpl. auto.
Qed.

Definition O_ModIP_der := Build_NT PDerMod_NatTrans.
             
Program Instance PDerMod_struct : PModIP_struct IPdm := {
  SModIP := ITdm;
  O_ModIP := O_ModIP_der
}.
Next Obligation.
Proof.
  set (H:= O_pp_mkl (PModIP_struct := M)).
  simpl in H.
  rewrite H.  
  set (H':=mkleisli_oid (Module_struct := 
                SModIP M (PModIP_struct := M))).
  unfold Proper in H'. red in H'.
  simpl in H'.
  apply H'.
  intros t0 z.
  set (H'':=O_pp_kl (PMon_struct := P) ).
  simpl in H''.
  set (H3:=kleisli_oid (Monad_struct := 
                 SMon(PMon_struct := P))).
  unfold Proper in H3; red in H3.
  simpl in H3.
  set (H4:=O_pp_we (PMon_struct := P)).
  simpl in H4.
  destruct z; simpl.
  unfold lift. simpl.
  rewrite H''.
  apply H3.
  intros; simpl.
  rewrite H4.
  simpl; auto.
  rewrite H4.
  simpl; auto.
Qed.

Definition PDerModIP := Build_PModIP PDerMod_struct.

End on_objects.

Section on_morphisms.

Variable u : T.
Variable M N : PMODIP.
Variable A : M ---> N. 

Program Instance PDerMod_Hom_struct : 
  PModIP_Hom_struct (M:=PDerModIP u M) (N:=PDerModIP u N)
       (#(DER_MOD _ _ u) (PModIP_ip A)) 
                (#(ITDER_MOD _ _ u) (PModIP_it A)).
Next Obligation.
Proof.
  set (H:= O_modhom_comm (PModIP_Hom_struct := A)).
  simpl in H.
  apply H.
Qed.

Definition PDerMod_Hom := Build_PModIP_Hom (PDerMod_Hom_struct).

End on_morphisms.
(*
Program Instance PDER_MOD_struct (u:T) : 
                     Func (@PDerMod_Hom u).
Next Obligation.
Proof.
  unfold Proper; red.
  intros x y H.
  destruct H as [H1 H2].
  split; intros c t z;
  simpl;
  auto.
Qed.

Definition PDER_MOD u := Build_Functor (PDER_MOD_struct u).
*)
End Pder_mod.

Section PModPO.


Class PModPO_struct (M: MOD P PO) := {
  SModPO : MOD (SMon (R:=P)) TYPE ;
  O_ModPO : (OPO O ModFunc M) ---> (ModFunc SModPO O OIP);
  O_pp_mkl_po : forall c d (f: c ---> P d), 
       #OPO (mkleisli M f) ;; O_ModPO _  ==
         O_ModPO _ ;; mkleisli SModPO (#OIP f ;; O_Mon d ) 
             
}.

Record PModPO := {
  PModPO_carrier :> MOD P PO;
  pmodpo_struct :> PModPO_struct PModPO_carrier
}.

End PModPO.


Existing Instance pmodpo_struct.

Section PModPO_Hom.

Variables M N : PModPO.

(** a morphism of parallel modules is a couple of morphisms of modules
    such that something commutes 
*)

Class PModPO_Hom_struct (R: M ---> N)(S: SModPO ---> SModPO) := {
   O_modhom_comm_po : forall c, 
         #OPO (R c);; O_ModPO _  == O_ModPO _ ;; S (OIP c)
}.

Record PModPO_Hom := {
  PModPO_ip : M ---> N;
  PModPO_it : SModPO ---> SModPO ;
  pmodpo_hom_struct :> PModPO_Hom_struct PModPO_ip PModPO_it
}.

Existing Instance pmodpo_hom_struct.

(** we call two morphisms of parallel modules equal if 
   both their components are equal as modules 
*)

Lemma PModPO_Hom_equiv : @Equivalence PModPO_Hom
     (fun a b => PModPO_ip a == PModPO_ip b /\ 
                 PModPO_it a == PModPO_it b).
Proof.
  constructor.
  unfold Reflexive; intros; 
  split; setoid.
  unfold Symmetric;
  split; setoid.
  unfold Transitive;
  split; setoid.
Qed.

Definition PModPO_Hom_oid := Build_Setoid PModPO_Hom_equiv.

End PModPO_Hom.
Existing Instance pmodpo_hom_struct.
Section PModPO_Homs.

Variable M:PModPO.

(** Identity and composition for parallel module morphisms *)

Program Instance PModPO_id_struct : 
   PModPO_Hom_struct (id (Cat:= MOD _ _ ) M) (id (@SModPO _ M)).

Definition PModPO_id := Build_PModPO_Hom PModPO_id_struct.

Variables N K : PModPO.
Variables (R:PModPO_Hom M N) (S:PModPO_Hom N K).

Program Instance PModPO_comp_struct : 
    PModPO_Hom_struct ((PModPO_ip R) ;; (PModPO_ip S)) 
                      ((PModPO_it R) ;; (PModPO_it S)).
Next Obligation.
Proof.
  set (HR := pmodpo_hom_struct R).
   destruct HR as [Hr].
   simpl in Hr.
   rewrite <- Hr.
  set (HS:= pmodpo_hom_struct S).
   destruct HS as [Hs].
   simpl in Hs. auto.
Qed.

Definition PModPO_comp := Build_PModPO_Hom PModPO_comp_struct.

End PModPO_Homs.

(** category of parallel modules with cod PO *)

Program Instance PMODPO_struct : Cat PModPO_Hom := {
  mor_oid := PModPO_Hom_oid;
  comp := PModPO_comp;
  id := PModPO_id
}.
Next Obligation.
Proof.
  unfold Proper; do 2 red.
  simpl.
  intros.
  destruct H as [H1 H2].
  destruct H0 as [H3 H4].
  split; intros.
  rewrite H1,H3; auto.
  rewrite H2,H4; auto.
Qed.

Definition PMODPO := Build_Category PMODPO_struct.

(** constant PModPO *)
Section constant_PModPO.

Variable z : PO.

Program Instance Const_PModPO_NT:
NatTrans (F:= OPO O ModFunc (Const_Mod P PO z)) 
         (G:= ModFunc (Const_Mod (SMon(PMon_struct := P)) TYPE z) O OIP)
         (fun c => id _ ).

Program Instance Const_PModPO_struct : 
     PModPO_struct (Const_Mod P PO z) := {
  SModPO := Const_Mod (SMon) TYPE z;
  O_ModPO := Build_NT Const_PModPO_NT
}.

Definition Const_PModPO : PMODPO := Build_PModPO Const_PModPO_struct. 

End constant_PModPO.

(** Fibre modules, a functor PMODIP -> PMODPO *)
Section Pfib_mod.

Section on_objects.

Variable u:T.
Variable M:PMODIP.

Let ITfm := ITFibre_Mod (T:=T) (P:=SMon) 
   (SModIP M (PModIP_struct:=M)) u.
Let IPfm := Fibre_Mod (T:=T) (P:=P) M u.


Program Instance PFibMod_NatTrans : NatTrans 
 (F:= OPO O ModFunc IPfm) (G:= ModFunc ITfm O OIP)
 (fun c => O_ModIP c u).
Next Obligation.
Proof.
  set (H:= trafo_ax (NatTrans := O_ModIP (PModIP_struct := M))).
  unfold trafo_comm in *.
  simpl in *.
  unfold mlift in H.
  simpl in *.
  intros.
  rewrite <- H.
  auto.
Qed.


Program Instance PFibMod_struct : PModPO_struct IPfm := {
  SModPO := ITfm;
  O_ModPO := Build_NT PFibMod_NatTrans
}.
Next Obligation.
Proof. 
  set (H:= O_pp_mkl (PModIP_struct := M)).
  simpl in H.
  rewrite <- H.
  auto.
Qed.

Definition PFibMod := Build_PModPO PFibMod_struct.

End on_objects.

Section on_morphisms.
Variable u : T.
Variable M N : PMODIP.
Variable A : M ---> N. 

Program Instance PFibMod_Hom_struct : PModPO_Hom_struct (M:=PFibMod u M)
                                                 (N:=PFibMod u N)
       (#(FIB_MOD _  u) (PModIP_ip A)) (#(ITFIB_MOD _ u) (PModIP_it A)).
Next Obligation.
Proof.
  set (H:= O_modhom_comm (PModIP_Hom_struct := A)).
  simpl in H.
  apply H.
Qed.

Definition PFibMod_Hom := Build_PModPO_Hom (PFibMod_Hom_struct).
End on_morphisms.
(*
Program Instance PFIB_MOD_struct (u:T) : 
          Func (@PFibMod_Hom u).
Next Obligation.
Proof.
  unfold Proper; red.
  intros x y H.
  destruct H as [H1 H2].
  split; intros c z;
  simpl;
  auto.
Qed.

Definition PFIB_MOD u := Build_Functor (PFIB_MOD_struct u).
*)
End Pfib_mod.

Section PProdModPO.

Section on_objects.

Variables M N : PMODPO.

Let Ppr := ModFunc (Prod_Mod (P:=P) _ M N).
Let Spr := ModFunc (Prod_Mod (P:=SMon (PMon_struct := P)) _ 
                    (SModPO (PModPO_struct := M))
                    (SModPO (PModPO_struct := N))).

Program Instance PProdModPO_NatTrans : 
NatTrans (F:=OPO O ModFunc (Prod_Mod (P:=P) PO_prod M N))
  (G:=ModFunc (Prod_Mod (P:=SMon) TYPE_prod SModPO SModPO) O OIP)
  (fun V r => (O_ModPO (PModPO_struct := M) V (fst r) , 
               O_ModPO (PModPO_struct := N) V (snd r))).
Next Obligation.
Proof.
  set (HM:= trafo_ax (NatTrans := O_ModPO (PModPO_struct := M))).
  set (HN:= trafo_ax (NatTrans := O_ModPO (PModPO_struct := N))).
  simpl in *.
  unfold mlift in *.
  simpl in *.
  rewrite  HM.
  rewrite HN.
  auto.
Qed.


Program Instance PProdModPO_struct : 
   PModPO_struct (Prod_Mod _ (PModPO_carrier M) (PModPO_carrier N)) := {
  SModPO := Prod_Mod _ SModPO SModPO ;
  O_ModPO := Build_NT PProdModPO_NatTrans
}.
Next Obligation.
Proof.
  set (HM:= O_pp_mkl_po (PModPO_struct := M)).
  set (HN:= O_pp_mkl_po (PModPO_struct := N)).
  simpl in *.
  rewrite HM.
  rewrite HN.
  auto.
Qed.

Definition PProdModPO := Build_PModPO PProdModPO_struct.
(*
Let ppprl := prl (PModPO_carrier M) (PModPO_carrier N).
Let tpprl := prl (SModPO (PModPO_struct := M))
                 (SModPO (PModPO_struct := N)).
*)
Program Instance PProdModPO_prl_struct : 
   PModPO_Hom_struct (M:= PProdModPO)(N:=M)
           (prl (PModPO_carrier M) (PModPO_carrier N)) 
           (prl (SModPO (PModPO_struct := M))
                 (SModPO (PModPO_struct := N))).

Program Instance PProdModPO_prr_struct : 
   PModPO_Hom_struct (M:= PProdModPO)(N:=N)
           (prr (PModPO_carrier M) (PModPO_carrier N)) 
           (prr (SModPO (PModPO_struct := M))
                 (SModPO (PModPO_struct := N))).

Definition PProdModPO_prl := Build_PModPO_Hom PProdModPO_prl_struct.
Definition PProdModPO_prr := Build_PModPO_Hom PProdModPO_prr_struct.

End on_objects.

Section PProdPO_prod_mor.

Variables A C D : PMODPO.
Variables (f : A ---> C) (g : A ---> D).

Program Instance PProdPO_prod_mor_struct : 
   PModPO_Hom_struct (M:=A)(N:=PProdModPO C D)
   (prod_mor (PModPO_ip f) (PModPO_ip g))
   (prod_mor (PModPO_it f) (PModPO_it g)).
Next Obligation.
Proof.
  set (Hf:=O_modhom_comm_po (PModPO_Hom_struct :=f)).
  set (Hg:=O_modhom_comm_po (PModPO_Hom_struct :=g)).
  simpl in *.
  rewrite Hf.
  rewrite Hg.
  auto.
Qed.

Definition PProdPO_prod_mor := Build_PModPO_Hom PProdPO_prod_mor_struct.

End PProdPO_prod_mor.

Program Instance PModPO_prod : Cat_Prod PMODPO := {
  product := PProdModPO;
  prl := PProdModPO_prl;
  prr := PProdModPO_prr;
  prod_mor := PProdPO_prod_mor
}.
Next Obligation.
Proof.
  unfold Proper; 
  do 2 red.
  intros x y H
     x' y' H' .
  destruct H as [H1 H2].
  destruct H' as [H1' H2'].
  split;
  intros V z;
  simpl.
  rewrite H1.
  rewrite H1'. auto.
  rewrite H2;
  rewrite H2';
  auto.
Qed.
Next Obligation.
Proof.
  split;
  intros V x;
  simpl;
  apply injective_projections;
  simpl; auto.
Qed.

End PProdModPO.
  
End PModules.

Section PPbMod.

Variables P Q : PMon.
Variable A : PMon_Hom P Q.
Variable M : PModIP Q.

Implicit Arguments SModIP [P PModIP_struct].

(*
Goal (forall c : IP,
  (OIP O ModFunc (PbMod A (D:=IP) M)) c --->
  (ModFunc (PbMod (PMon_it A) (D:=IT) 
      (SModIP (PModIP_struct := M))) O OIP) c).
intros. 
set (H:= O_ModIP (PModIP_struct := M)).
apply (H c).
simpl.
apply (O_ModIP).
*)

(*
Program Instance PPbMod_NatTrans : 
NatTrans 
  (F:= OIP O ModFunc (PbMod A  M))
  (G:= ModFunc (PbMod (PMon_it A) (SModIP M (PModIP_struct := M))) O OIP)
      (fun c => O_ModIP (PModIP_struct := M) c).
Next Obligation.
Proof.
  assert (H:= trafo_ax (NatTrans := O_ModIP (PModIP_struct := M))).
(*  set (H':= trafo_ax (NatTrans := O_Mon (PMon_struct := Q))).*)
  simpl in *.
(*  unfold PbMod. *)
  unfold mlift in *.
  unfold mkleisli.
  simpl in *.
  set (H2 := O_pp_mkl (PModIP_struct := M)).
  simpl in H2.

  set (H'':= mkleisli_mlift (@SModIP Q M M)).
  simpl in *.
  rewrite <- H''.
  simpl.
  unfold mlift.
  simpl.
  set (H3:= H c (Q d) (ind_po_comp f (weta Q d))) .
  simpl in H3.
  set (H4:= mkleisli_mlift (PModIP_carrier M)).
  simpl in H4.
  rewrite <- H4.
  unfold mlift in *.
  simpl in *.
               (* this rewriting could be a good idea *)
  set (H5 := mkl_mkl (P:=PMon_carrier Q) 
             (Module_struct := PModIP_carrier M)).
  simpl in H5.
  rewrite H5.
  set (H6 := eta_kl (Monad_struct:=PMon_carrier Q)).
  set (H7:= assoc IP).
  rewrite <- H7.
  simpl in H7.
  rewrite <- assoc.
  rewrite H6.
  simpl in H6.
  rewrite <- (H _ d (ind_po_comp (f (.
  set (H6:= H5 (Module_struct := M)).
  simpl in H5.
 
  set (H1 := H c (SMon d)  (f ;; weta (Monad_struct := (@SMon P P)) d) ).
  rewrite H.
  unfold mlift in *.
  simpl in *.
  rewrite <- H.
  unfold mlift in H.
  simpl in H.
  unfold mkleisli in H.
  rewrite H.
  
  rewrite H.
  rewrite <- H. simpl.
  simpl in H.
  unfold mlift in *.
  simpl in *.
  unfold lift in *.
  unfold mkleisli in *.
  rewrite H.
  unfold PbMod.
  simpl.
  simpl in H.
  rewrite H.

.
*)
(*
Program Instance PPbModIP_struct : PModIP_struct (P:=P) 
            (PbMod (PMon_ip A) (PModIP_carrier M)) := {
  SModIP := PbMod (PMon_it A) (SModIP (PModIP_struct := M))
}.
Next Obligation.
*)

End PPbMod.

End defs.

Existing Instance pmon_struct.
Existing Instance pmodip_struct.
Existing Instance pmodip_hom_struct.
Existing Instance pmodpo_struct.
Existing Instance pmodpo_hom_struct.
Existing Instance PModPO_prod.










