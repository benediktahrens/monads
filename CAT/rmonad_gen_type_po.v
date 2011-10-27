Require Export CatSem.CAT.rmonad_gen.
Require Export CatSem.CAT.rmodule_TYPE.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.


(** pullback of rmodule along gen. monad morphisms 
    commutes with derivation *)

(** we take two monads 
    - P : Set/T -> PO/T (F:=SM_ipo)
    - Q : Set/U -> PO/U (F:=SM_ipo)
   
   and an rmodule 
    - M : RMOD Q E
*)

Section fix_types.

Variables T U : Type.
Variable f : T -> U.

Section term_to_term.
Variable P : RMonad (IDelta T).
Variable Q : RMonad (IDelta U).
Variable M : colax_RMonad_Hom P Q
	      (G1:=RETYPE (fun t => f t))
	      (G2:=RETYPE_PO (fun t => f t)) 
              (RT_NT (fun t => f t)).


Section lemmata.
Variables (c d : ITYPE T).

Variable h : c ---> d.

Variable (g : ipo_mor (sm_ipo (T:=T) c) (P d)). 
Variable (t : T).
Variable y : P c t.

Lemma gen_rh_rkl :
(M d) (f t) (ctype (fun t => f t) (V:=P d) (t:=t) 
 ((rkleisli (RMonad_struct := P)(a:=c) (b:=d) g) t y)) =
     (rkleisli (RMonad_struct := Q)(a:=retype _ c) (b:=retype _ d)
        (ipo_comp
           (ipo_comp (id_cc _ c)
              (retype_po_mor (fun t => f t) (V:=sm_ipo (T:=T) c) (W:=P d) g)) (M d)))
       (f t) ((M c) (f t) (ctype (fun t => f t) (V:=P c) (t:=t) y)).
Proof.
  assert (H:=gen_rmonad_hom_rkl M).
  simpl in H.
  assert (H':= H _ _ g _ (ctype _ y)).
  simpl in H'.
  auto.
Qed.

Variable z : c t.

Lemma gen_rh_rweta :
(M c) (f t) (ctype (fun t => f t) (V:=P c) (t:=t) 
((rweta (RMonad_struct := P)c) t z)) =
     (rweta (RMonad_struct := Q) (retype _ c)) 
        (f t) (ctype (fun t => f t) (V:=c) (t:=t) z).
Proof.
  assert (H:=gen_rmonad_hom_rweta M).
  simpl in H.
  assert (H':= H _ _ (ctype _ z)).
  simpl in H'.
  auto.
Qed.


Lemma gen_rh_rlift : 
(rlift Q (a:=retype (fun t : T => f t) c)
        (b:=retype (fun t : T => f t) d) (retype_map (W:=d) h)) (f t)
       ((M c) (f t) (ctype (fun t : T => f t) (V:=P c) (t:=t) y)) =
     (M d) (f t)
       (ctype (fun t : T => f t) (V:=P d) (t:=t)
          ((rlift P (a:=c) (b:=d) h) t y)).
Proof.
  assert (H3 := NTcomm M).
  simpl in H3.
  assert (H4:= H3 _ _ h _ (ctype _ y)).
  simpl in H4.
  auto.
Qed.

End lemmata.

Program Instance unit_rmod_s : RModule_Hom_struct
  (M:= Term (C:=RMOD P Ord)) (N:= colax_PbRMod M (Term (C:=RMOD Q Ord)))
  (fun V => id PO_TERM).

Definition unit_rmod : 
  Term (C:=RMOD P Ord) ---> colax_PbRMod M (Term (C:=RMOD Q Ord)) :=
     Build_RModule_Hom unit_rmod_s.

End term_to_term.

Section gen_pb_der.

Variable P : RMonad (IDelta T).
Variable Q : RMonad (IDelta U).
Variable h : colax_RMonad_Hom P Q 
              (G1:=RETYPE (fun t => f t))
	      (G2:=RETYPE_PO (fun t => f t)) (RT_NT (fun t => f t)).

Variable u : T.

Variable obE : Type.
Variable morE : obE -> obE -> Type.
Variable E : Cat_struct morE.

Variable N : RMOD Q E.

Obligation Tactic := idtac.

Program Instance gen_pb_der_s : RModule_Hom_struct
   (M:= DER_RMOD _ _ u (colax_PbRMod h N))
   (N:= colax_PbRMod h (DER_RMOD _ _ (f u) N))
   (fun c => rmlift N (@der_comm _ _ _ _ c)).
Next Obligation.
Proof.
  simpl.
  intros V W g.
  rewrite (rmkleisli_rmlift).
  rewrite (rmlift_rmkleisli).
  apply (rmkl_eq).
  simpl.
  intros t z.
  destruct z as [t z];
  simpl.
  destruct z as [t z | ];
  simpl. 
  assert (H:= NTcomm (colax_RMonad_Hom_NatTrans h)).
  simpl in H.
  generalize (g t z).
  clear z.
  intro z.
  destruct g as [g gax];
  simpl.

  assert (H':= H W (opt u W) (some u (A:=W)) _ (ctype _ z)).
  simpl in H'.
  rewrite <- H'.
  assert (H2 :=rlift_rlift Q).
  simpl in H2.
  rewrite H2.
  apply (rlift_eq Q).
  simpl;
  intros t0 y;
  destruct y as [t0 y]; 
  simpl; auto.
  
  assert (H:=gen_rmonad_hom_rweta h).
  simpl in H.
  assert (H':= H (opt u W) (f u) (ctype _ (none u W))).
  simpl in H'.
  rewrite H'.
  clear H' H.
  
  assert (H:=rlift_rweta Q).
  simpl in H.
  rewrite H.
  simpl.
  auto.
Qed.
  
Definition gen_pb_der : DER_RMOD _ _ u (colax_PbRMod h N) ---> 
         colax_PbRMod h (DER_RMOD _ _ (f u) N) := 
 Build_RModule_Hom gen_pb_der_s.

End gen_pb_der.

Section gen_pb_fib_and_eq.

Variables obC obD obC' obD': Type.
Variable morC : obC -> obC -> Type.
Variable morD : obD -> obD -> Type.
Variable morC' : obC' -> obC' -> Type.
Variable morD' : obD' -> obD' -> Type.
Variable C : Cat_struct morC.
Variable D : Cat_struct morD.
Variable C' : Cat_struct morC'.
Variable D' : Cat_struct morD'.

Variable F : Functor C D.
Variable F' : Functor C' D'.

Variable P : RMonad F.
Variable Q : RMonad F'.

(** for a monad hom we need two functors *)

Variable G1 : Functor C C'.
Variable G2 : Functor D D'.

Variable N : NT (CompF G1 F') (CompF F G2).

Variable h : colax_RMonad_Hom P Q N.

Variable t : T.

Variable M : RMOD Q (IPO T).

Program Instance gen_pb_fib_s : RModule_Hom_struct
  (M:= FIB_RMOD _ t (colax_PbRMod h M))
  (N:= colax_PbRMod h (FIB_RMOD _ t M))
  (fun c => id _ ).

Definition colax_Pb_Fib : FIB_RMOD _ t (colax_PbRMod h M) ---> 
          colax_PbRMod h (FIB_RMOD _ t M) := Build_RModule_Hom gen_pb_fib_s.


Program Instance gen_fib_pb_s : RModule_Hom_struct
  (M:=colax_PbRMod h (FIB_RMOD _ t M))
  (N:= FIB_RMOD _ t (colax_PbRMod h M))
  (fun c => id _ ).

Definition colax_Fib_Pb : colax_PbRMod h (FIB_RMOD _ t M) ---> 
   FIB_RMOD _ t (colax_PbRMod h M) 
       := Build_RModule_Hom gen_fib_pb_s.

Variable u : T.
Hypothesis H : u = t.

Obligation Tactic := idtac.

Program Instance eq_rect_po_s c:
 PO_mor_struct
 (a:=(FIB_RMOD Q u) M c) (b:=(FIB_RMOD Q t) M c)
 ((eq_rect u (fun t : T => forall c : obC', (M c) u -> (M c) t)
  (fun (c : obC') (y : (M c) u) => y) t H) c).
Next Obligation.
Proof.
  intros;
  unfold Proper;
  red; subst;
  simpl; auto.
Qed.

Definition eq_rect_po c:=Build_PO_mor (eq_rect_po_s c).

Program Instance FIB_RMOD_eq_s : RModule_Hom_struct 
 (M:=FIB_RMOD _ u M) (N:=FIB_RMOD _ t M)
 eq_rect_po.
Next Obligation.
Proof.
  intros;
  simpl;
  subst;
  simpl.
  auto.
Qed.

Definition FIB_RMOD_eq :
    FIB_RMOD _ u M ---> FIB_RMOD _ t M := 
 Build_RModule_Hom FIB_RMOD_eq_s.

End gen_pb_fib_and_eq.


Section der_fibre.

Variable P : RMonad (IDelta T).
Variable Q : RMonad (IDelta U).
Variable M : colax_RMonad_Hom P Q 
                 (G1:=RETYPE (fun t => f t))
	      (G2:=RETYPE_PO (fun t => f t)) 
                  (RT_NT (fun t => f t) ).
Variables s r : T.
(*
Definition der_fib_hom_noeq_d c:
(ipo_proj (P (opt r c)) s ->
  ipo_proj (Q (opt (f r) (retype (fun t : T => f t) c))) (f s)).
simpl.
intros c y.
set (z := ctype (fun t => f t) y).
simpl in *.
set (z':= M _ _ z).
simpl in *.
apply (rlift Q (@der_comm _ _ _ _ _ ) _ (M _ _ (ctype (fun t => f t) y))).
apply (rlift Q (@der_comm _ _ _ _ _ ) _ z'). _ (gen_rmonad_hom M) _ _ (ctype _ y)).
*)

Obligation Tactic := idtac.

Program Instance der_fib_hom_noeq_car c :
PO_mor_struct (a:=ipo_proj (P (opt r c)) s)
  (b:=ipo_proj (Q (opt (f r) (retype (fun t : T => f t) c))) (f s))
  (fun y => rlift Q (@der_comm _ _ _ _ _ ) _
              (M _ _ (ctype (fun t => f t) y))).
Next Obligation.
Proof.
  intros.
  unfold Proper;
  red.
  simpl.
  intros x y H.
  apply (rlift Q (@der_comm _ _ (fun t => f t) _ _ )).
  destruct M as [Md Mx].
  apply Md.
  simpl in *.
  constructor;
  auto.
Qed.

Definition der_fib_hom_noeq_d:
(forall c : ITYPE T,
  ((FIB_RMOD P s) ((DER_RMOD (IPO T) P r) P)) c --->
  ((FIB_RMOD P (f s)) (colax_PbRMod M ((DER_RMOD (IPO U) Q (f r)) Q))) c):=
 fun c => Build_PO_mor (der_fib_hom_noeq_car c).

Obligation Tactic := idtac.

Program Instance der_fib_hom_noeq_s : RModule_Hom_struct
  (M:=FIB_RMOD _ s (DER_RMOD _ _ r P))
  (N:=FIB_RMOD _ (f s) (colax_PbRMod M (DER_RMOD _ _ (f r) Q)))
  der_fib_hom_noeq_d.
Next Obligation.
Proof.
  simpl.
  intros c d g x.
  assert (H:=gen_rmonad_hom_rkl M).
  simpl in H.
  rew (H _ _ (sshift r g) _ (ctype _ x)).
  clear H.
  rew (rkleisli_rlift (M:=Q)).
  rew (rlift_rkleisli (M:=Q)).
  apply (rkl_eq Q).
  simpl.
  intros t z.
  destruct z as [t z];
  simpl.
  destruct z as [t z | ];
  simpl.
  
  assert (H2:= NTcomm M).
  simpl in H2.
  generalize (g t z).
  clear z.
  intro z.
  rerew (H2 _ _ (some r (A:=d)) _ (ctype _ z)).
  rew (rlift_rlift Q).
  apply (rlift_eq Q).
  simpl.
  intros t0 x0;
  destruct x0;
  simpl; auto.

  rew (gen_rmonad_hom_rweta M _ _ (ctype _ (none r d))).
  rew (rlift_rweta Q).
Qed.


Definition DerFib_RMod_Hom :
  FIB_RMOD _ s (DER_RMOD _ _ r P) ---> 
     FIB_RMOD _ (f s) (colax_PbRMod M (DER_RMOD _ _ (f r) Q)) :=
     Build_RModule_Hom der_fib_hom_noeq_s.

Variable r' : U.
Hypothesis H : f r = r'.

Program Instance der_fib_hom_d c : PO_mor_struct
  (a:=((FIB_RMOD P s) ((DER_RMOD (IPO T) P r) P)) c)
  (b:=((FIB_RMOD P (f s)) (colax_PbRMod M ((DER_RMOD (IPO U) Q r') Q))) c)
  (fun x => eq_rect (f r) 
             (fun r' : U => Q (opt r' (RETYPE _ c)) (f s))
  (rlift Q (@der_comm _ _ _ _ _) _ 
       (((*gen_rmonad_hom*) M) _ _ (ctype (fun t => f t) x))) r' H).
Next Obligation.
Proof.
  unfold Proper;
  red.
  subst.
  simpl.
  intros c x y H.
  apply (rlift Q (@der_comm _ _ (fun t => f t) _ _ )).
  destruct M as [Md Mx].
  apply Md.
  simpl in *.
  constructor;
  auto.
Qed.

Definition der_fib_hom_e c : 
  ((FIB_RMOD P s) ((DER_RMOD (IPO T) P r) P)) c ---> 
  ((FIB_RMOD P (f s)) (colax_PbRMod M ((DER_RMOD (IPO U) Q r') Q))) c :=
  Build_PO_mor (der_fib_hom_d c).
 
Obligation Tactic := idtac.

Program Instance der_fib_hom_s : RModule_Hom_struct
   (M:=FIB_RMOD _ s (DER_RMOD _ _ r P))
   (N:=FIB_RMOD _ (f s) (colax_PbRMod M (DER_RMOD _ _ r' Q)))
   der_fib_hom_e.
Next Obligation.
Proof.
  simpl.
  subst.
  simpl.
  intros c d g x.
  assert (H:=gen_rmonad_hom_rkl M).
  simpl in H.
  rew (H _ _ (sshift r g) _ (ctype _ x)).
  clear H.
  rew (rkleisli_rlift (M:=Q)).
  rew (rlift_rkleisli (M:=Q)).
  apply (rkl_eq Q).
  simpl.
  intros t z.
  destruct z as [t z];
  simpl.
  destruct z as [t z | ];
  simpl.
  
  assert (H2:= NTcomm M).
  simpl in H2.
  generalize (g t z).
  clear z.
  intro z.
  rerew (H2 _ _ (some r (A:=d)) _ (ctype _ z)).
  rew (rlift_rlift Q).
  apply (rlift_eq Q).
  simpl.
  intros t0 x0;
  destruct x0;
  simpl; auto.

  rew (gen_rmonad_hom_rweta M _ _ (ctype _ (none r d))).
  rew (rlift_rweta Q).
Qed.
  
Definition der_fib_hom :
  FIB_RMOD _ s (DER_RMOD _ _ r P) ---> 
     FIB_RMOD _ (f s) (colax_PbRMod M (DER_RMOD _ _ r' Q)) :=
     Build_RModule_Hom der_fib_hom_s.

End der_fibre.

End fix_types.









