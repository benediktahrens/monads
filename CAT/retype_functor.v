Require Import Coq.Logic.Eqdep.

Require Export CatSem.CAT.cat_INDEXED_TYPE.
Require Export CatSem.CAT.monad_h_morphism_gen.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Automatic Introduction.

Section retyping.

Variables U U' : Type.

Variable T : U -> U'.

(** for T : U -> U' define a functor RETYPE : Set/U -> Set/U' *)


Inductive retype (V : ITYPE U) : ITYPE U' :=
  | ctype : forall t, V t -> retype V (T t).

Inductive backtype (V : ITYPE U') : ITYPE U :=
  | bt : forall t : U, V (T t) -> backtype V t.

Notation "' V" := (retype V) (at level 20).


Definition retype_map V W (f : V ---> W) : 'V ---> 'W :=
    fun t x => match x with
    | ctype  v => ctype (f _ v)
    end.

Instance retype_eq V W : Proper (equiv ==> equiv) (@retype_map V W).
Proof.
  unfold Proper.
  red.
  intros V W f g H t x.
  induction x.
  simpl.
  rewrite H.
  auto.
Qed.

Obligation Tactic := idtac. 

Program Instance retype_func : Functor_struct (fun V W => @retype_map V W).
Next Obligation.
Proof.
  simpl.
  intros a t x.
  induction x;
  simpl;
  auto.
Qed.
Next Obligation.
Proof.
  simpl;
  intros a b c f g u x.
  induction x;
  simpl;
  auto.
Qed.

Definition RETYPE := Build_Functor retype_func.


Definition der_comm t (V : ITYPE U) : ' (opt t V) ---> opt (T t) (' V) :=
   fun (t0 : U') (X : (' opt t V) t0) =>
   match X in ((' _) u) return (opt (T t) (' V) u) with
   | ctype  o =>
     match o in (opt _ _ y) return (opt (T t) (' V) (T y)) with
       | some t2 v => some (u:=(T t))(A:=' V)(T t2)(ctype (V:=V) (t:=t2) v)
       | none _ _ => none (T t) (' V)
    end
end.


Lemma retype_nt (V W : ITYPE U) (f : V ---> W) t (v : V t) : 
   retype_map f (ctype v) = ctype (f t v).
Proof.
  reflexivity.
Qed.


Section bla.

Variable P : Monad (ITYPE U).
Variable Q : Monad (ITYPE U').

Variable M : colax_Monad_Hom P Q (RETYPE).

Variable s : U.

(** constructors without binding can use this in each component 
    as left vertical morphism *)

Program Instance blalb : Module_Hom_struct
         (S := ITFIB_MOD _ s P)
         (T := ITFIB_MOD _ (T s) (PModule M Q)) 
         (fun x X => M _ _ (ctype X)).
Next Obligation.
Proof.
  simpl.
  intros.
  assert (H:= gen_monad_hom_kl (colax_Monad_Hom_struct := M)).
  simpl in H.
  rewrite <- H.
  apply f_equal.
  simpl.
  auto.
Qed.
  
Definition FFib_Mod_Hom := Build_Module_Hom blalb.

(** this version already commutes pullback with fibre at
    the target, but is not used at the moment 
  
    i choose to do retyping P [T s] -> P [s'] before
    commuting pullback and fibre
*)

Program Instance blalb2 : Module_Hom_struct
         (S := ITFIB_MOD _ s P)
         (T := PModule M (ITFIB_MOD _ (T s) Q))
         (fun x X => M _ _ (ctype X)).
Next Obligation.
Proof.
  simpl.
  intros.
  assert (H:= gen_monad_hom_kl (colax_Monad_Hom_struct := M)).
  simpl in H.
  rewrite <- H.
  apply f_equal.
  simpl.
  auto.
Qed.

Definition FFib_PM_Mod_Hom := Build_Module_Hom blalb.


(** now we try to produce D_r P [s] -> D_(T r) f* Q [T s] *)

Variable r : U.

(*
Lemma useful W t' t x:
lift (M:= Q) (@der_comm _ _ ) (T t')
  (M (opt t W) (T t') (retype_map (W:=P (opt t W)) 
   (lift (some t (A:=W))) x)) =
lift (M:= Q) (some (T t) (A:=' W)) (T t') (M W (T t') x) .
Proof.
  assert (H := trafo_ax (NatTrans := gen_Monad_Hom_NatTrans M)).
  simpl in H.
  intros.
  rewrite <- H.
  simpl.
  assert (H1:=lift_lift Q).
  simpl in H1.
  rewrite H1.
  assert (H2 := lift_eq Q).
  unfold Proper in H2.
  red in H2.
  apply H2.
  simpl.
  intros.
  destruct x0.
  simpl.
  auto.
Qed.
*)

Program Instance blalb3 : Module_Hom_struct
     (S := ITFIB_MOD _ s (ITDER_MOD _ _ r P))
     (T := ITFIB_MOD _ (T s) (PModule M (ITDER_MOD _ _ (T r) Q)))
    (fun t X => lift (M:=Q)(@der_comm _ _ ) _ (M _ _ (ctype X))).
Next Obligation.
Proof.
 simpl.
 intros V W f x.
 
 rewrite <- retype_nt.
(* transitivity ( lift (M:=Q) (@der_comm _ _ ) (T s)
                  (M (opt r W) (T s)
        (retype_map (kleisli (shift (P:=P)(W:=W) f))
            (ctype (V:=P (opt r V)) (t:=s)  x)))).
  auto.*)
  assert (H'':= gen_monad_hom_kl (colax_Monad_Hom_struct := M)).
  simpl in H''.
  rewrite H''.

  assert (H:= lift_kleisli (M:=Q)).
  simpl in H.
  rewrite H.
  
  assert (H':=kleisli_lift (M:=Q)).
  simpl in H'.
  rewrite H'.
  unfold lift.
  simpl.
  
  assert (H5 := kl_eq Q).
  simpl in *.
  apply H5.

  intros.
  
  destruct x0.
  simpl.
  destruct o.
  
  Focus 1.
  
  simpl.
  
  generalize (f t v).
  clear v.
  intro v.
  rewrite <- retype_nt.
  assert (H4 := NTcomm (colax_Monad_Hom_NatTrans M)).
  simpl in H4.
  rewrite <- H4.
  rewrite H.
  unfold lift.
  simpl.
  apply H5.
  intros.
  apply f_equal.
  destruct x0.
  simpl.
  auto.  (* end of 1 *)
  
  simpl.
  rewrite <- retype_nt.
  assert (H4 := NTcomm (colax_Monad_Hom_NatTrans M)).
  assert (H12 := gen_monad_hom_weta (colax_Monad_Hom_struct := M)).
  simpl in H12.
  rewrite H12.
  assert (H13 := etakl Q).
  simpl in H13.
  rewrite H13. 
  auto.
Qed.
 
Canonical Structure FFib_DER_Mod_Hom :
     ITFIB_MOD _ s (ITDER_MOD _ _ r P) --->     
            ITFIB_MOD _ (T s) (PModule M (ITDER_MOD _ _ (T r) Q)):=
      Build_Module_Hom blalb3.

Variable r' : U'.
Hypothesis Hr : T r = r'.

Program Instance blalb_eqrect : Module_Hom_struct
     (S := ITFIB_MOD _ s (ITDER_MOD _ _ r P))
     (T := ITFIB_MOD _ (T s) (PModule M (ITDER_MOD _ _ (r') Q)))
    (fun V x => eq_rect (T r) 
             (fun r' : U' => Q (opt r' (' V)) (T s))
 (lift (M:=Q)(@der_comm _ _ ) _ ((gen_monad_hom M) _ _ (ctype x))) r' Hr).
Next Obligation.
Proof.
  rewrite <- Hr.
  simpl.
  intros V W f x.
  simpl.

  rewrite <- retype_nt.
  assert (H'':= gen_monad_hom_kl (colax_Monad_Hom_struct := M)).
  simpl in H''.
  rewrite H''.

  assert (H:= lift_kleisli (M:=Q)).
  simpl in H.
  rewrite H.
  
  assert (H':=kleisli_lift (M:=Q)).
  simpl in H'.
  rewrite H'.
  unfold lift.
  simpl.

  assert (H5 := kl_eq Q).
  apply H5.
  simpl.

  intros.
  
  destruct x0.
  simpl.
  destruct o.
  
  Focus 1.
  
  simpl.
  
  generalize (f t v).
  clear v.
  intro v.
  rewrite <- retype_nt.
  assert (H4 := NTcomm (colax_Monad_Hom_NatTrans M)).
  simpl in H4.
  rewrite <- H4.
  rewrite H.
  unfold lift.
  simpl.
  apply H5.
  simpl.
  intros.
  apply f_equal.
  destruct x0.
  simpl.
  auto.  (* end of 1 *)
  
  
  simpl.
  rewrite <- retype_nt.
  assert (H4 := NTcomm (colax_Monad_Hom_NatTrans M)).
  assert (H12 := gen_monad_hom_weta (colax_Monad_Hom_struct := M)).
  simpl in H12.
  rewrite H12.
  
  
  assert (H13 := etakl Q).
  simpl in H13.
  simpl in H13.
  rewrite H13.
  apply f_equal.
  simpl.
  auto.
Qed.
 
Canonical Structure FFib_DER_Mod_Hom_eqrect :
     ITFIB_MOD _ s (ITDER_MOD _ _ r P) --->     
            ITFIB_MOD _ (T s) (PModule M (ITDER_MOD _ _ (r') Q)):=
      Build_Module_Hom blalb_eqrect.


Variable obD : Type.
Variable morD : obD -> obD -> Type.
Variable D : Cat_struct morD.

Variable N : MOD Q (ITYPE U').

Program Instance PM_DER (t : U) : Module_Hom_struct 
      (S := ITDER_MOD _ _ t (PModule M N))
      (T := PModule M (ITDER_MOD _ _ (T t) N)) 
      (fun x => mlift N (@der_comm _ _ )).
Next Obligation.
Proof.
  intros t V W f.
  assert (H6 := mlift_mkleisli N).
  assert (H7 := mkleisli_mlift N).
  simpl in *.
  
  intros t' x.
  rewrite H6.
  rewrite H7.
  
  assert (H5 := mkleisli_oid (Module_struct := N)).
  unfold Proper in H5.
  red in H5.
  apply H5.
  clear H5 H6 H7.
  clear x t'. 
  intros t' x.
  destruct x as [t' x] .
  simpl.
  destruct x as [t' x | ].
  simpl.
  
  Focus 1.
  generalize (f t' x).
  clear x.
  clear f.
  intro x.
  clear V.
  assert (H'':= gen_monad_hom_kl (colax_Monad_Hom_struct := M)).
  simpl in H''.
  
  rewrite <- retype_nt.
  
  generalize (ctype x).
  clear x.
  intro x.
  clear dependent obD.
  assert (H := NTcomm (colax_Monad_Hom_NatTrans M)).
  simpl in H.
  rewrite <- H.
  simpl.
  assert (H1:=lift_lift Q).
  simpl in H1.
  rewrite H1.
  assert (H2 := lift_eq Q).
  unfold Proper in H2.
  red in H2.
  apply H2.
  simpl.
  intros.
  destruct x0.
  simpl.
  auto.
  
  
  simpl.
  clear dependent V.
  clear dependent obD.
  
  assert (H := NTcomm (colax_Monad_Hom_NatTrans M)).
  rewrite <- retype_nt.
  auto.
  
  simpl in H.
  
  assert (H12 := gen_monad_hom_weta (colax_Monad_Hom_struct := M)).
  simpl in H12.
  rewrite H12.
  
  assert (H13 := lift_weta Q).
  simpl in H13.
  rewrite H13.
  simpl.
  auto.
Qed.
 
End bla.


Section eq_DER.

Variable P : Monad (ITYPE U).

Variable M : MOD P (ITYPE U).

Variables u u' : U.
Hypothesis H : u = u'.

Definition eq_type_der_c : 
(forall x : ITYPE U,
   (((ITDER_MOD P _ u) M) x) ---> (((ITDER_MOD P _ u') M) x)).
  intro x.
  rewrite <- H.
  apply id.
Defined.
  

Program Instance eq_type_der_mod_s : Module_Hom_struct
       (S := ITDER_MOD P _ u M)
       (T := ITDER_MOD _ _ u' M) eq_type_der_c.
Next Obligation.
Proof.
  intros c d f t.
  simpl.
  unfold eq_type_der_c.
  simpl in *.
  rewrite H.
  simpl.
  auto.
Qed.

Definition eq_type_der_mod := Build_Module_Hom eq_type_der_mod_s.

End eq_DER.


End retyping.


Section lemmata.

Variables U U' : Type.
Variable f : U -> U'.
Variable P : Monad (ITYPE U).
Variable Q : Monad (ITYPE U').

Variable M : colax_Monad_Hom P Q (RETYPE f).
Variables V W : ITYPE U.
Variable f' : V ---> P W.
Variable t : U.
Variable y : P V t.

Lemma MonadHomKl :  
M W (f t) (ctype f (V:=P W) (t:=t) (kleisli f' t y)) =
     kleisli (Monad_struct := Q) 
       (fun (t : U') (x : retype f V t) => M W t (retype_map (W:=P W) f' x))
       (f t) (M V (f t) (ctype f (V:=P V) (t:=t) y)).

Proof.
  assert (H:= gen_monad_hom_kl (colax_Monad_Hom_struct := M)).
  simpl in H.
  assert (H':= H _ _ f' _ (ctype _ y)).
  simpl in H'.
  apply H'.
Qed.

Variable z : V t.

Lemma MonadHomWe : 
    M V (f t) (ctype f (V:=P V) (t:=t) 
           (weta (Monad_struct := P) V t z)) =
     weta (Monad_struct := Q)
        (retype f V) (f t) (ctype f (V:=V) (t:=t) z).
Proof.
  assert (H:= gen_monad_hom_weta (colax_Monad_Hom_struct := M)).
  simpl in H.
  assert (H':= H _ _ (ctype _ z)).
  simpl in H'.
  auto.
Qed.

Variable g : V ---> W.

Lemma MonadHomLift : 
  lift (retype_map (W:=W) g) (f t) (M V (f t) (ctype f (V:=P V) (t:=t) y)) =
     M W (f t) (ctype f (V:=P W) (t:=t) (lift g t y)).
Proof.
  assert (H3 := NTcomm (colax_Monad_Hom_NatTrans M)).
  simpl in H3.
  assert (H4:= H3 _ _ g _ (ctype _ y)).
  simpl in H4.
  auto.
Qed.

End lemmata.


(**  this is V^{f} -> V^{g} where forall t, f t = g t   *)

Section transp.
Variables U U': Type.
Variables f g : U -> U'.
Hypothesis H : forall t, g t = f t.

Definition transp : forall V : ITYPE U,
     (RETYPE (fun t : U => f t)) V ---> 
     (RETYPE (fun t : U => g t)) V := 
  fun (V : U -> Type) (t : U') 
      (Y : retype (fun t0 : U => f t0) V t) =>
    match Y in (retype _ _ y) return 
         (retype (fun t0 : U => g t0) V y) with
    | @ctype _ _ _ _ t0 v =>
           eq_rect (g t0) 
            (fun u : U' => retype (fun t1 : U => g t1) V u)
            (ctype (fun t1 : U => g t1) (V:=V) (t:=t0) v) (f t0) (H t0)
end.
      
Obligation Tactic := idtac.

Program Instance transp_NT : 
    NT_struct (F:=RETYPE (fun t => f t)) 
           (G := RETYPE (fun t => g t)) transp.
Next Obligation.
Proof.
  simpl.
  intros V W f' t y.
  induction y.
  simpl.
  rewrite <- H.
  simpl.
  auto.
Qed.

Definition Transp : NT (RETYPE (fun t => f t)) 
         (RETYPE (fun t => g t)) := Build_NT transp_NT.

End transp.


Section transp_id.

(** retyping with the identity function is the identity *)

Variables U U' : Type.
Variable f : U -> U'.
Variable H : forall t, f t = f t.

Lemma transp_id : forall V, transp H (V:=V) == id _.
Proof.
  simpl.
  intros V t y.
  induction y.
  simpl.
  rewrite (UIP_refl _ _ (H t)).
  simpl.
  auto.
Qed.

End transp_id.

Section transp_lift_id.

Variables U U' : Type.
Variable f : U -> U'.
(*Variable P : Monad (ITYPE U).*)
Variable Q : Monad (ITYPE U').

Hypothesis H : forall t, f t = f t.
Variable V : ITYPE U.
Variable t' : U'.


Lemma lift_transp_id : forall y : Q (retype (fun t => f t) V) t',
   lift (M:=Q) (transp (f:= f)(g:= f) H (V:=V)) 
           _ y = y.
Proof.
  intro y.
  assert (H'' := lift_eq_id Q).
  apply H''.
  apply transp_id.
Qed.

End transp_lift_id.

Section id_retype.
Variable U : Type.

Definition id_retype V : V ---> retype (U':=U) (fun t => t) V :=
    fun t y => ctype (fun t0 => t0) y.

End id_retype.


Section double_retype.

Variables U U' U'' : Type.
Variable f : U -> U'.
Variable f' : U' -> U''.


Definition double_retype_1 (V : ITYPE U) :
   retype (fun t => f' t) (retype (fun t => f t) V) --->
        retype (fun t => f' (f t)) V :=
 fun  (t : U'')
  (y : retype (fun t0 : U' => f' t0) 
     (retype (fun t0 : U => f t0) V) t) =>
   match y in (retype _ _ y0) return 
       (retype (fun t0 : U => f' (f t0)) V y0)
   with | ctype _ r => 
       match r in (retype _ _ y0) return 
               (retype (fun t1 : U => f' (f t1)) V (f' y0))
       with | @ctype _ _ _ _ t1 v => 
         ctype (fun t2 : U => f' (f t2)) (V:=V) (t:=t1) v
    end
end.

Definition double_retype_2 (V : ITYPE U) :
    retype (fun t => f' (f t)) V --->
    retype (fun t => f' t) (retype (fun t => f t) V) :=
  fun (t : U'') (y : retype (fun t0 : U => f' (f t0)) V t) =>
  match y in (retype _ _ y0) return 
      (retype (fun t0 : U' => f' t0) 
         (retype (fun t0 : U => f t0) V) y0)
  with | @ctype _ _ _ _ t0 v =>
         ctype (fun t1 : U' => f' t1) 
        (V:=retype (fun t1 : U => f t1) V) (t:= f t0) 
            (ctype (fun t1 : U => f t1) (V:=V) (t:=t0) v)
end.

End double_retype.



Section comp_monad.

Variables U U' U'' : Type.
Variable f : U -> U'.
Variable f' : U' -> U''.

Variable P : Monad (ITYPE U).
Variable Q : Monad (ITYPE U').
Variable R : Monad (ITYPE U'').

Variable M : colax_Monad_Hom P Q (RETYPE (fun t => f t)).
Variable N : colax_Monad_Hom Q R (RETYPE (fun t => f' t)).

Definition comp_rep_car : (forall c : ITYPE U,
        RETYPE (fun t => f' (f t)) (P c) ---> 
     R ((RETYPE (fun t => f' (f t))) c)) :=
  
  fun (V : ITYPE U) t 
    (y : retype (fun t => f' (f t)) (P V) t) =>
   match y with ctype _ z =>
    (lift (M:=R) (double_retype_1 (f:=f) 
                            (f':=f') (V:=V))) _
          (N _ _ (ctype (fun t => f' t)
               (M _ _ (ctype (fun t => f t) z ))))end.

Obligation Tactic := idtac.

Program Instance comp_rep_mon_hom_s : 
       colax_Monad_Hom_struct (P:=P) (Q:=R) 
       (F0:=RETYPE (fun t => f' (f t)))
       comp_rep_car.
Next Obligation.
Proof.
  simpl.
  intros V W g t y.
  simpl.
  destruct y as [t y].
  simpl.

  rewrite (MonadHomKl M).
  simpl.
  rewrite (MonadHomKl N).
  assert (H':=lift_kleisli (M:=R)).
  simpl in H'.
  rewrite H'.
  assert (H3:=kleisli_lift (M:=R)).
  simpl in H3.
  rewrite H3.
  apply (kl_eq R).
  
  intros t0 z.
  destruct z.
  simpl.
  destruct r.
  simpl.
  auto.
Qed.
Next Obligation.
Proof.
  simpl.
  intros V t y.
  destruct y.
  simpl.
  
  rewrite (MonadHomWe M).
  rewrite (MonadHomWe N).
  assert (H:= lift_weta R).
  simpl in H.
  rewrite H.
  auto.
Qed.

Definition comp_Rep_monad := 
    Build_colax_Monad_Hom comp_rep_mon_hom_s.

End comp_monad.






