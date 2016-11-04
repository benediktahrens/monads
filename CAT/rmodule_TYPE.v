Require Export CatSem.CAT.rmonad_gen.
Require Export CatSem.CAT.cat_INDEXED_TYPE.
Require Export CatSem.CAT.retype_functor_po.
Require Export CatSem.CAT.ind_potype.
Require Export CatSem.CAT.rmonad_hom.
Require Export CatSem.CAT.rmodule_pb_rmonad_hom.
Require Export CatSem.CAT.orders_bis.
Require Export CatSem.CAT.cat_TYPE_option.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.


(** some untyped modules *)

Section fixnotype.

Variable P : RMonad SM_po.
Variables V W : TYPE.

Section shift_def.

Variable f : SM_po V ---> P W.

Definition shift_ : option V -> P (option W) :=
   option_default 
      (f ;; rlift P (weta (Monad_struct := option_monad) W))
      (rweta (RMonad_struct := P) (option W) None).

Obligation Tactic := idtac.

Program Instance shift_struct : PO_mor_struct 
  (a:=SM_po (option V)) (b:=P (option W))
  (option_default 
      (f ;; rlift P (weta (Monad_struct := option_monad) W))
      (rweta (RMonad_struct := P) (option W) None)).
Next Obligation.
Proof.
  unfold Proper; red.
  simpl.
  intros.
  destruct H.
  reflexivity.
Qed.

Definition shift_not : SM_po (option V) ---> P (option W) :=
   Build_PO_mor shift_struct.

End shift_def.


Section shift_notype_eq.

Variables f g : SM_po V ---> P W.

Hypothesis H : f == g.

Lemma shift_not_eq : shift_not f == shift_not g.
Proof.
  simpl.
  intro z.
  destruct z;
  simpl;
  try rewrite H;
  auto.
Qed.

End shift_notype_eq.
End fixnotype.

Instance shift_notype_oid P V W : 
   Proper (equiv ==> equiv) (@shift_not P V W) := @shift_not_eq P V W.

Section Derivation.

Variable obE : Type.
Variable morE : obE -> obE -> Type.
Variable E : Cat_struct morE.

Variable P : RMonad SM_po.

Section der_on_obj.

Variable M : RMOD P E.

Lemma shift_not_rkl V W X (f : SM_po V ---> P W)
    (g : SM_po W ---> P X) :
shift_not (P:=P)  f;;
rkleisli (a:=option W) (b:=option X) (shift_not (P:=P) (V:=W) (W:=X) g) ==
shift_not (P:=P) (V:=V) (W:=X) (f ;; (rkleisli (a:=W) (b:=X) g)).
Proof.
  simpl.
  intros V W X f g x.
  destruct x;
  simpl. 
  assert (H:= rkleisli_rlift (M:=P)).
  assert (H':=rlift_rkleisli (M:=P)).
  simpl in *.
  rewrite H.
  rewrite H'.
  assert (H2:=rkl_eq P).
  simpl in H2.
  apply H2.
  simpl.
  auto.
  
  assert (H:=retakl P).
  simpl in H.
  rewrite H. 
  simpl;
  auto.
Qed.
  
Lemma shift_not_rweta c :
  shift_not (P:=P) (V:=c) (W:=c) (rweta c) == rweta (option c).
Proof.
  simpl.
  intros V z.
  assert (H:=rlift_rweta P).
  destruct z;
  simpl in *; 
  auto.
Qed.

Hint Rewrite shift_not_rkl shift_not_rweta : rmonad.
Hint Resolve shift_not_rkl shift_not_rweta : rmonad.

Instance rmkl_shift_not_oid :
forall c d : TYPE,
Proper (equiv ==> equiv)
  (fun f : SM_po c ---> P d =>
   rmkleisli (RModule_struct := M) 
    (c:=option c) (d:=option d) (shift_not (P:=P) (V:=c) (W:=d) f)).
Proof.
  intros c d.
  unfold Proper.
  red.
  intros f g H.
  rewrite (shift_notype_oid H).
  cat.
Qed.

Obligation Tactic := simpl; intros; autorewrite with rmonad;
                   auto with rmonad.

Program Instance Der_RMod_not_struct : 
  RModule_struct P E (fun x => M (option x)) := {
  rmkleisli a b f := rmkleisli (RModule_struct := M) (shift_not f)
                                               }.
(*
Next Obligation.
  unfold Proper;
  red.
  intros x y H.
  apply rmkl_eq.
  apply shift_not_eq.
  simpl.
  apply H.
Qed.
  *)

Definition Der_RMod_not : RMOD P E := Build_RModule Der_RMod_not_struct.

End der_on_obj.

Section der_on_mor.

Variables M N : RMOD P E.
Variable S : M ---> N.

Obligation Tactic := rmonad.

Program Instance Der_RMod_not_Hom_struct : 
  RModule_Hom_struct (M:=Der_RMod_not M) (N:=Der_RMod_not N) 
         (fun c => S (option c)).

Definition Der_RMod_not_Hom : Der_RMod_not M ---> Der_RMod_not N :=
           Build_RModule_Hom Der_RMod_not_Hom_struct.

End der_on_mor.

Obligation Tactic := unfold Proper; red; rmonad.

Program Instance DER_RMOD_not_s : Functor_struct Der_RMod_not_Hom.

Canonical Structure DER_RMOD_not := Build_Functor DER_RMOD_not_s.

End Derivation.


Section der_pb_not.

Variables P Q : RMonad (SM_po).
Variable h : RMonad_Hom P Q.
Variable obE : Type.
Variable morE : obE -> obE -> Type.
Variable E : Cat_struct morE.
Variable M : RMOD Q E.

Obligation Tactic := idtac.

Program Instance DER_RPB_not_s : RModule_Hom_struct
  (M:=DER_RMOD_not _ _  (PbRMod h M)) (N:= PbRMod h (DER_RMOD_not _ _  M))
  (fun _ => id _ ).
Next Obligation.
Proof.
  intros V W f.
  rewrite idl.
  rewrite idr.
  simpl.
  apply rmkl_eq.
  simpl.
  intros z.
  assert (H2:=rmon_hom_rweta h).
  destruct z as [t z | ];
  simpl in *;
  auto.
  unfold rlift.
  simpl.
  assert (H:=rmon_hom_rkl h).
  simpl in H.
  rewrite H.
  apply (rkl_eq Q).
  simpl.
  intros;
  auto.
Qed.  

Definition DER_RPB_not : 
  DER_RMOD_not _ _ (PbRMod h M) ---> PbRMod h (DER_RMOD_not _ _  M) :=
     Build_RModule_Hom DER_RPB_not_s.

End der_pb_not.

Section Rsubstar.

Variable P : RMonad (SM_po).

Section carrier.

Variable V : TYPE.
Variable W : P V.

Definition Rsubst_star_map_not : 
  SM_po (option V) -> P V :=
    fun z => match z in option _  return P V with
               | None => W
               | Some v => rweta (RMonad_struct := P) _ v
               end.

Obligation Tactic := idtac.

Program Instance Rsubstar_not_s : PO_mor_struct Rsubst_star_map_not.
Next Obligation.
Proof.
  intros.
  unfold Proper;
  red.
  intros x y H.
  induction H.
  reflexivity.
Qed.

Definition Rsubstar_m_not : SM_po (option V) ---> P V := 
 Build_PO_mor Rsubstar_not_s.

Definition Rsubstar_not : P (option V) ---> P V :=
      rkleisli Rsubstar_m_not.

End carrier.

Lemma rsubstar_m_not_monotone V (w w' : P V) :
  Rel (PO_obj_struct:= po_obj_struct (P V)) w  w' ->
  forall y,    
    Rel (PO_obj_struct:= po_obj_struct (P V)) (Rsubstar_m_not w y)  (Rsubstar_m_not w' y).
Proof.
  intros.
  simpl in *.
  destruct y; 
    simpl.
  reflexivity.

  auto.
Qed.

Hypothesis rkleisli_not_monotone : forall c d 
     (f g : SM_po c ---> P d) ,
   (forall  y, Rel (PO_obj_struct := po_obj_struct (P d)) (f y) ( g y)) ->
        forall  y, 
          Rel (PO_obj_struct := po_obj_struct (P d)) ((rkleisli (RMonad_struct:=P) f) y) (rkleisli g y).


Obligation Tactic := idtac.

Program Instance rsubstar_prod_not_monotone c :
PO_mor_struct 
 (a:=PO_product ((P (option c))) ((P c)))
  (b:=(P c)) 
  (fun y => Rsubstar_not (snd y) (fst y)).
Next Obligation.
Proof.


  
  intros  c.
  unfold Proper;
  red.
  intros y z H.
  destruct H.
  simpl in *.
  transitivity (
    Rsubstar_not (V:=c) w v').
  -apply (Rsubstar_not w).
   auto.
  - 
  clear dependent v.
  
  unfold Rsubstar_not.
  apply rkleisli_not_monotone.
  simpl; intros.
  assert (H':= rsubstar_m_not_monotone).
  simpl in H'.
  apply (H').
  apply H0.
Qed.

Definition rsubstar_prod_not_mon c:
  Prod_RMod (P:=P) PO_prod
     ((Der_RMod_not (P:=P) P))
     (P) c ---> P c :=
  (Build_PO_mor (rsubstar_prod_not_monotone c)).

Obligation Tactic := idtac.

Program Instance Rsubstar_not_module : 
  RModule_Hom_struct 
    (M:=Prod_RMod (PO_prod)
         ((Der_RMod_not P))
         (P))
    (N:=P)
    (rsubstar_prod_not_mon ).
Next Obligation.
Proof.
  simpl.
  intros c d f y.
  destruct y as [y z];
  simpl.
  unfold Rsubstar_not.
  rew (rklkl P).
  rew (rklkl P).
  apply (rkl_eq P).
  simpl.
  intros w.
  destruct w;
  simpl.
  rew (rlift_rkleisli (M:=P)).
  rew (retakl P).
  generalize (f c0).
  intro z'.
  assert (H':= rkleta_eq (FM:=P)).
  simpl in H'.
  apply H'.
  simpl.
  auto.
  rew (retakl P).
Qed.

End Rsubstar.


Section fixatype.

Variable T : Type.

Section shift.

Variable P : RMonad (IDelta T).

Variable u : T.

Variables V W : ITYPE T.

Section shift_def.

Variable f : IDelta T V ---> P W.


Definition sshift_  : 
        forall t, opt u V t -> P (opt u W) t :=
 (opt_default (u:=u) (V:=V) (W:=P (opt u W))
 (f ;; rlift P (weta (Monad_struct := (opt_monad u)) W))
 (rweta (RMonad_struct := P) (opt u W) u (none u W))).

Obligation Tactic := idtac.

Program Instance sshift_struct : 
      ipo_mor_struct (a:=IDelta T (opt u V)) (b:=P(opt u W)) sshift_.
Next Obligation.
Proof.
  intros.
  unfold Proper;
  red.
  intros x y H.
  induction H;
  simpl.
  apply IRel_refl.
Qed.

Definition sshift : IDelta T (opt u V) ---> P (opt u W) := 
           Build_ipo_mor sshift_struct.

End shift_def.

Section shift_eq.

Variables f g : IDelta T V ---> P W.
Hypothesis H : f == g.

Lemma sshift_eq : sshift f == sshift g.
Proof.
  simpl.
  intros t z.
  destruct z;
  simpl;
  try rewrite H;
  auto.
Qed.

End shift_eq.

Instance sshift_oid : Proper (equiv ==> equiv) (sshift):= sshift_eq.

End shift.

Existing Instance sshift_oid.


Section Derivation.


Variable obE : Type.
Variable morE : obE -> obE -> Type.
Variable E : Cat_struct morE.

(*Variable F : Functor (ITYPE T) (IPO T).*)

Variable P : RMonad (IDelta T).
Variable u : T.

Section der_on_obj.

Variable M : RMOD P E.

Lemma sshift_rkl c d e (f : IDelta T c ---> P d)
    (g : IDelta T d ---> P e) :
sshift (P:=P) u (V:=c) (W:=d) f;;
rkleisli (a:=opt u d) (b:=opt u e) (sshift (P:=P) u (V:=d) (W:=e) g) ==
sshift (P:=P) u (V:=c) (W:=e) (f ;; (rkleisli (a:=d) (b:=e) g)).
Proof.
  simpl.
  intros.
  destruct z;
  simpl. 
  assert (H:= rkleisli_rlift (M:=P)).
  assert (H':=rlift_rkleisli (M:=P)).
  simpl in *.
  rewrite H.
  rewrite H'.
  assert (H2:=rkl_eq P).
  simpl in H2.
  apply H2.
  simpl.
  auto.
  
  assert (H:=retakl P).
  simpl in H.
  rewrite H. 
  simpl;
  auto.
Qed.
  
Lemma sshift_rweta c :
  sshift (P:=P) u (V:=c) (W:=c) (rweta c) == rweta (opt u c).
Proof.
  simpl.
  intros V t z.
  assert (H:=rlift_rweta P).
  destruct z;
  simpl in *; 
  auto.
Qed.

Hint Rewrite sshift_rkl sshift_rweta : rmonad.
Hint Resolve sshift_rkl sshift_rweta : rmonad.

Instance rmkl_sshift_oid :
forall c d : ITYPE T,
Proper (equiv ==> equiv)
  (fun f : IDelta T c ---> P d =>
   rmkleisli (RModule_struct := M) 
    (c:=opt u c) (d:=opt u d) (sshift (P:=P) u (V:=c) (W:=d) f)).
Proof.
  intros c d.
  unfold Proper.
  red.
  intros f g H.
  rewrite (sshift_oid H).
  cat.
Qed.
 

Obligation Tactic := rmonad; try apply rmkl_sshift_oid.

Program Instance Der_RMod_struct : 
  RModule_struct P E (fun x => M (opt u x)) := {
  rmkleisli a b f := rmkleisli (RModule_struct := M) (sshift u f)
                                              }.

(*
Next Obligation.
  unfold Proper;
  red.
  intros x y H.
  apply rmkl_eq.
  apply sshift_eq.
  simpl.
  apply H.
Qed.
  *)

Definition Der_RMod : RMOD P E := Build_RModule Der_RMod_struct.

End der_on_obj.

Section der_on_mor.

Variables M N : RMOD P E.
Variable S : M ---> N.

Obligation Tactic := rmonad.

Program Instance Der_RMod_Hom_struct : 
  RModule_Hom_struct (M:=Der_RMod M) (N:=Der_RMod N) 
         (fun c => S (opt u c)).

Definition Der_RMod_Hom : Der_RMod M ---> Der_RMod N :=
           Build_RModule_Hom Der_RMod_Hom_struct.

End der_on_mor.

Obligation Tactic := unfold Proper; red; rmonad.

Program Instance DER_RMOD_s : Functor_struct Der_RMod_Hom.

Canonical Structure DER_RMOD := Build_Functor DER_RMOD_s.

End Derivation.

Section fibre.

Variable obC : Type.
Variable morC : obC -> obC -> Type.
Variable C : Cat_struct morC.
Variable obD : Type.
Variable morD : obD -> obD -> Type.
Variable D : Cat_struct morD.

Variable F : Functor C D.

Variable P : RMonad F.

Variable u : T.

Section fibre_on_obj.

Variable M : RMOD P (IPO T).

Obligation Tactic := idtac.

Program Instance Fib_RMod_s : 
   RModule_struct P Ord (fun c => ipo_proj (M c) u) := {
   rmkleisli a b f := ipo_mor_proj u
               (rmkleisli (RModule_struct := M) f)
}.
Next Obligation.
Proof.
  unfold Proper;
  red.
  simpl.
  intros c d f g H x0.
  apply (rmkl_eq M).
  auto.
Qed.
Next Obligation.
Proof.
  simpl; intros.
  assert (H:=rmklmkl M).
  simpl in H.
  intros.
  rewrite H.
  auto.
Qed.
Next Obligation.
Proof.
  simpl; intros.
  rewrite (rmkleta M).
  auto.
Qed.

Definition Fib_RMod : RMOD P Ord := Build_RModule Fib_RMod_s.

End fibre_on_obj.

Section fibre_on_mor.

Variables M N : RMOD P (IPO T).
Variable S : M ---> N.

Program Instance Fib_RMod_Hom_s : RModule_Hom_struct 
   (M:= Fib_RMod M) (N:=Fib_RMod N) (fun c => ipo_mor_proj u (S c)).
Next Obligation.
Proof.
  assert (H:=rmhom_rmkl S).
  simpl in H.
  auto.
Qed.

Definition Fib_RMod_Hom : Fib_RMod M ---> Fib_RMod N := 
            Build_RModule_Hom Fib_RMod_Hom_s.

End fibre_on_mor.

Instance Fib_RMod_oid : 
forall a b : RMOD P (IPO T),
Proper (equiv ==> equiv) (Fib_RMod_Hom (M:=a) (N:=b)).
Proof.
  unfold Proper;
  red.
  simpl.
  auto.
Qed.

Program Instance FIB_RMOD_s : Functor_struct Fib_RMod_Hom.

Canonical Structure FIB_RMOD := Build_Functor FIB_RMOD_s.

End fibre.

(** we should establish isomorphisms DER PB -> PB DER *)
Section der_pb.

Variables P Q : RMonad (IDelta T).
Variable h : RMonad_Hom P Q.
Variable obE : Type.
Variable morE : obE -> obE -> Type.
Variable E : Cat_struct morE.
Variable M : RMOD Q E.
Variable u : T.

Obligation Tactic := idtac.

Program Instance DER_RPB_s : RModule_Hom_struct
  (M:=DER_RMOD _ _ u (PbRMod h M)) (N:= PbRMod h (DER_RMOD _ _ u M))
  (fun _ => id _ ).
Next Obligation.
Proof.
  intros V W f.
  rewrite idl.
  rewrite idr.
  simpl.
  apply rmkl_eq.
  simpl.
  intros t z.
  assert (H2:=rmon_hom_rweta h).
  destruct z as [t z | ];
  simpl in *;
  auto.
  unfold rlift.
  simpl.
  assert (H:=rmon_hom_rkl h).
  simpl in H.
  rewrite H.
  apply (rkl_eq Q).
  simpl.
  intros;
  auto.
Qed.  

Definition DER_RPB : 
  DER_RMOD _ _ u (PbRMod h M) ---> PbRMod h (DER_RMOD _ _ u M) :=
     Build_RModule_Hom DER_RPB_s.

End der_pb.

Section fib_pb.

Variable obC : Type.
Variable morC : obC -> obC -> Type.
Variable C : Cat_struct morC.
Variable obD : Type.
Variable morD : obD -> obD -> Type.
Variable D : Cat_struct morD.

Variable F : Functor C D.

Variables P Q : RMonad F.
Variable h : RMonad_Hom P Q.

Variable u : T.

Variable M : RMOD Q (IPO T).

Program Instance FIB_RPB_s : RModule_Hom_struct 
   (M:= FIB_RMOD _ u (PbRMod h M)) (N:=PbRMod h (FIB_RMOD _ u M))
   (fun c => id _ ).

Definition FIB_RPB : 
   FIB_RMOD _ u (PbRMod h M) ---> PbRMod h (FIB_RMOD _ u M) :=
    Build_RModule_Hom FIB_RPB_s.

End fib_pb.

Section Rsubstar.

Variable P : RMonad (IDelta T).

Section carrier.

Variable V : ITYPE T.
Variable r : T.
Variable W : P V r.

Definition Rsubst_star_map : 
  forall t, IDelta T (opt r V) t -> P V t :=
    fun t z => match z in opt _ _  s return P V s with
               | none _ _  => W
               | some _ v => rweta (RMonad_struct := P) _ _ v
               end.

Obligation Tactic := idtac.

Program Instance Rsubstar_s : ipo_mor_struct Rsubst_star_map.
Next Obligation.
Proof.
  intros.
  unfold Proper;
  red.
  intros x y H.
  induction H.
  apply IRel_refl.
Qed.

Definition Rsubstar_m : IDelta T (opt r V) ---> P V := 
 Build_ipo_mor Rsubstar_s.

Definition Rsubstar : P (opt r V) ---> P V :=
      rkleisli Rsubstar_m.

End carrier.


Definition bla2 r s c :
(PO_product (ipo_proj (P (opt r c)) s) (ipo_proj (P c) r) ->
  ipo_proj (P c) s).
simpl.
intros r s c y.
apply (Rsubstar (snd y) _ (fst y)).
Defined.


Lemma rsubstar_m_monotone V t (w w' : P V t) : w <<< w' ->
        forall u y, 
        Rsubstar_m w u y <<< Rsubstar_m w' _ y.
Proof.
  intros.
  simpl in *.
  destruct y; 
  simpl.
  reflexivity.
  auto.
Qed.

Hypothesis rkleisli_monotone : forall c d 
     (f g : IDelta T c ---> P d) ,
   (forall t y, f t y <<< g t y) ->
        forall t y, 
    (rkleisli (RMonad_struct:=P) f) t y <<< rkleisli g t y.

Obligation Tactic := idtac.

Program Instance rsubstar_prod_monotone r s c :
PO_mor_struct 
 (a:=PO_product (ipo_proj (P (opt r c)) s) (ipo_proj (P c) r))
  (b:=ipo_proj (P c) s) 
  (fun y => Rsubstar (snd y) _ (fst y)).
Next Obligation.
Proof.
  intros r s c.
  unfold Proper;
  red.
  intros y z H.
  destruct H.
  simpl in *.
  transitivity (
    Rsubstar (V:=c) (r:=r) w s v').
  apply (Rsubstar w).
  auto.
  clear dependent v.
  unfold Rsubstar.
  simpl.
  apply rkleisli_monotone.
  simpl; intros.
  assert (H':= rsubstar_m_monotone).
  simpl in H'.
  apply (H').
  apply H0.
Qed.

Definition rsubstar_prod_mon r s c:
  (Prod_RMod (P:=P) PO_prod
     (Fib_RMod (P:=P) s (Der_RMod (E:=IPO T) (P:=P) r P))
     (Fib_RMod (P:=P) r P)) c ---> (Fib_RMod (P:=P) s P) c :=
  (Build_PO_mor (rsubstar_prod_monotone r s c)).

Obligation Tactic := idtac.

Program Instance Rsubstar_module r s : 
  RModule_Hom_struct 
    (M:=Prod_RMod (PO_prod)
         (Fib_RMod s (Der_RMod r P))
         (Fib_RMod r P))
    (N:=Fib_RMod s P)
    (rsubstar_prod_mon r s).
Next Obligation.
Proof.
  simpl.
  intros r s c d f y.
  destruct y as [y z];
  simpl.
  unfold Rsubstar.
  rew (rklkl P).
  rew (rklkl P).
  apply (rkl_eq P).
  simpl.
  intros t w.
  destruct w;
  simpl.
  rew (rlift_rkleisli (M:=P)).
  rew (retakl P).
  generalize (f t c0).
  intro z'.
  assert (H':= rkleta_eq (FM:=P)).
  simpl in H'.
  apply H'.
  simpl.
  auto.
  rew (retakl P).
Qed.

End Rsubstar.

End fixatype.


Section FFib_Mod_Hom.
(*
FFib_Mod_Hom
     : forall (U U' : Type) (T : U -> U') (P : Monad (ITYPE U))
         (Q : Monad (ITYPE U')) (M : gen_Monad_Hom P Q (RETYPE T)) (s : U),
       Module_Hom ((ITFIB_MOD P s) P)
         ((ITFIB_MOD P (T s)) (PModule M (E:=ITYPE U') Q))
*)
Variables T U : Type.
Variable f : T -> U.

Variable P : RMonad (IDelta T).
Variable Q : RMonad (IDelta U).

Variable h : colax_RMonad_Hom P Q (RT_NT f).
Variable s : T.

Obligation Tactic := idtac.

Program Instance fib_rmod_hom_car_po c : 
   PO_mor_struct (a:=((FIB_RMOD P s) P) c)
                  (b:=((FIB_RMOD P (f s)) (colax_PbRMod h Q)) c)
    (fun z => h c (f s) (ctype f z)).
Next Obligation.
Proof.
  simpl; intros.
  unfold Proper;
  red.
  intros x y H.
  destruct h.
  simpl in *.
  apply gen_rmonad_hom.
  simpl.
  constructor.
  auto.
Qed.

(*Definition fib_rmod_hom_c c := Build_PO_mor (fib_rmod_hom_car_po c).*)

Definition FIB_RMOD_HOM_car (c : ITYPE T):
  ((FIB_RMOD P s) P) c ---> ((FIB_RMOD P (f s)) (colax_PbRMod h Q)) c :=
   Build_PO_mor (fib_rmod_hom_car_po c).

Obligation Tactic := idtac.

Program Instance FIB_RMOD_HOM_s : RModule_Hom_struct
   (M:=FIB_RMOD _ s P) (N:=FIB_RMOD _ (f s) (colax_PbRMod h Q))
   FIB_RMOD_HOM_car.
Next Obligation.
Proof.
  simpl.
  intros c d f0 x.
  assert (H:=gen_rmonad_hom_rkl h).
  simpl in H.
  assert (H':= H _ _ f0 _ (ctype f x)).
  simpl in H'.
  auto.
Qed.
  
Definition FIB_RMOD_HOM := Build_RModule_Hom FIB_RMOD_HOM_s.


End FFib_Mod_Hom.
















