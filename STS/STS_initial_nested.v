Require Export CatSem.STS.STS_representations.
(*Require Setoid.*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

(** in this file we define 
    - STS, the initial monad
    - Var, a constructor of STS
    - rename, the functoriality
    - inj, renaming with (v => Some v)
    - shift, taking the substitution function and changing it in a capture
             avoiding fashion
    - subst, the substitution

    correspondences to the general monad definitions 
        (STS left, Monad right):
    - Var = weta
    - rename f = lift f
    - inj = lift weta
    - shift = opt_inj
    - subst = kleisli

    subst is defined in terms of rename. this is precisely the other way 
       round for monads. 
    after having established monadicity, we must show:
    - rename = lift
    - shift = opt_inj
*)

Section initial_type.

Ltac fin := simpl in *; intros; autorewrite with fin; auto with fin.

Variable T : Type.
Variable S : Signature T.
Notation "V * u" := (opt u V).
Notation "V ** l" := (pow l V) (at level 10).
Notation "f ^^ l" := (pow_map (l:=l) f) (at level 10).
Notation "^ f" := (lift (M:= opt_monad _) f) (at level 5).
Notation "[ T ]" := (list T) (at level 5).

(** STS will be the initial monad, STS_list represents the arguments of
     a constructor *)
(** STS_list is actually isomorphic to [prod_mod_carrier STS], but 
    we wouldn't get such a nice induction scheme with a non-mutual
    inductive type
*)

Inductive STS (V : ITYPE T) : ITYPE T :=
  | Var : forall t, V t -> STS V t
  | Build : forall t (i : sig_index (S t)),
        prod_mod_c STS V (sig i) -> STS V t.

Section STS_ind2.

Variable P : forall V t, STS V t -> Prop.

Variable Q : forall V l, prod_mod_c STS V l -> Prop.
(*
Variable Q : forall V t (i : sig_index (S t)), 
      prod_mod_c STS V (sig i) -> Prop.
*)
Hypothesis H : forall V t (i : sig_index (S t)) 
                     (x : prod_mod_c STS V (sig i)), 
          Q  x -> P (Build x).

Hypothesis HVar : forall V (t : T) (v : V t), P (Var v).

Hypothesis H0 : forall V, Q (TTT STS V).

Hypothesis H1 : forall V b l (x : STS (V ** (fst b)) (snd b)), P x ->
         forall s : prod_mod_c STS V l, Q s ->
                Q (CONSTR x s).

Fixpoint STSind V t (x : STS V t) : P x :=
   match x as r return P r with
   | Var _ v => HVar v
   | Build t i s => H  
         ((fix STSind2 V l (s' : prod_mod_c STS V l) : Q s' :=
              match s' as q return Q q with
              | TTT  => H0 _ 
              | CONSTR _ _ b bs => 
                      H1 (STSind b) (STSind2 _ _ bs)
              end) _ _ s)
   end.

End STS_ind2.
(*
Section STS_ind_i.

Variable P : forall V t, STS V t -> Prop.


Variable Q : forall V t (i : sig_index (S t)), 
      prod_mod_c STS V (sig i) -> Prop.

Hypothesis H : forall V t (i : sig_index (S t)) 
                     (x : prod_mod_c STS V (sig i)), 
          Q  x -> P (Build x).

Hypothesis HVar : forall V (t : T) (v : V t), P (Var v).
(*
Hypothesis H0 : forall V, Q (TTT STS V).
*)
Hypothesis H1 : forall V b (x : STS (V ** (fst b)) (snd b)), P x ->
         forall i (s : prod_mod_c STS V (sig i)), Q s ->
                Q (CONSTR x s).

Fixpoint STSind V t (x : STS V t) : P x :=
   match x as r return P r with
   | Var _ v => HVar v
   | Build t i s => H  
         ((fix STSind2 V l (s' : prod_mod_c STS V l) : Q s' :=
              match s' as q return Q q with
              | TTT  => H0 _ 
              | CONSTR _ _ b bs => 
                      H1 (STSind b) (STSind2 _ _ bs)
              end) _ _ s)
   end.
*)
Section Forall_def.

Variable M : ITYPE T -> ITYPE T.

Inductive Forall V (P : forall V t, M V t -> Prop) : 
      forall l, prod_mod_c M V l -> Prop :=
 | Forall_nil : Forall P (TTT _ _ )
 | Forall_cons : forall b (x : M (V**(fst b)) (snd b)),
        P _ _  x ->
        forall l (xl : prod_mod_c M V l),
          Forall P xl -> Forall P 
         (CONSTR x xl).

End Forall_def.

Section forall_ind.

Variable P : forall V t, STS V t -> Prop.

Hypothesis NVar : forall V (t:T) (v : V t), P (Var v).

Hypothesis NBuild : forall V t (i : sig_index (S t)) 
          (x : prod_mod_c STS V (sig i)), 
      Forall P x -> P (Build x).

Fixpoint STS_ind2 V t (x : STS V t) : P x :=
  match x return P x with
  | Var _ v => NVar v
  | Build t i s => NBuild
    ((fix list_STS_ind2 V l (y : prod_mod_c STS V l) : 
                Forall P y :=
         match y return Forall P y with
         | TTT => Forall_nil _ P 
         | CONSTR _ _ e el => 
              @Forall_cons STS V P _ e (STS_ind2 e) 
                     _ _ (list_STS_ind2 V _ el)
              end) _ _ s)
  end.

End forall_ind.


Section rename.



Section STS_rect2.

Variable X : forall V t, STS V t -> Type.
Variable Y : forall V l, prod_mod_c STS V l -> Type.

Hypothesis H : forall V t (i : sig_index (S t)) 
                     (x : prod_mod_c STS V (sig i)), 
          Y x -> X (Build x).

Hypothesis HVar : forall V (t : T) (v : V t), X (Var v).

Hypothesis H0 : forall V, Y (TTT STS V).

Hypothesis H1 : forall V b l (x : STS (V ** (fst b)) (snd b)), X x ->
         forall s : prod_mod_c STS V l, Y s ->
                Y (CONSTR x s).

Fixpoint STSrect V t (x : STS V t) : X x :=
   match x as r return X r with
   | Var _ v => HVar v
   | Build t i s => H  
         ((fix STSrect2 V l (s' : prod_mod_c STS V l) : Y s' :=
              match s' as q return Y q with
              | TTT  => H0 _ 
              | CONSTR _ _ b bs => 
                      H1 (STSrect b) (STSrect2 _ _ bs)
              end) _ _ s)
   end.

End STS_rect2.
(*
Inductive STS (V : ITYPE T) : ITYPE T :=
  | Var : forall t, V t -> STS V t
  | Build : forall t (i : sig_index (S t)),
             STS_list V (sig i) -> STS V t
with 
STS_list (V : ITYPE T) : 
            [[T] * T] -> Type :=
  | TT : STS_list V nil
  | constr : forall b bs, 
      STS (V ** (fst b)) (snd b) -> 
      STS_list V bs -> 
      STS_list V (b::bs).

Scheme STSind := Induction for STS Sort Prop with
       STSlistind := Induction for STS_list Sort Prop.
*)
(*
Lemma constr_eq : forall (V : ITYPE T) (b : [T] * T) 
            (bs : [[T] * T]) (x y : STS _ (snd b))
              (v w : STS_list V bs),
     x = y -> v = w -> constr x v = constr y w.
Proof.
  intros V b bs x y v w H H'.
  rewrite H;
  rewrite H';
  auto.
Qed.

Hint Rewrite constr_eq : fin.
Hint Resolve constr_eq f_equal : fin.
*)
Reserved Notation "x //- f" (at level 42, left associativity).
Reserved Notation "x //-- f" (at level 42, left associativity).
(*
Fixpoint rename (V : ITYPE T) 
             (W : ITYPE T) (f : V ---> W) t (v : STS V t) {struct v} :=
    match v in STS _ t return STS W t with
    | Var t v => Var (f t v)
    | Build  t i l => Build (i:=i) (list_rename l f)
    end
with 
  list_rename V t (l : prod_mod_c STS  V t) W (f : V ---> W) {struct l} : 
           prod_mod_c STS W t :=
     match l in prod_mod_c _ _ t return prod_mod_c STS W t with
     | TTT => TTT _ _
     | CONSTR b bs elem elems => 
             CONSTR (elem //- ( f ^^ (fst b)))
                               (elems //-- f)
     end
where "x //- f" := (rename f x) 
and "x //-- f" := (list_rename x f).
*)

Section list_iter.

(** given a function on STS, we want to use it on prod_mod_c STS *)

Variable op : forall V W t, STS V t -> STS W t.

Fixpoint list_iter V W l (s : prod_mod_c STS V l) : prod_mod_c STS W l :=
     match s in prod_mod_c _ _ l return prod_mod_c STS W l with
     | TTT => TTT _ W
     | CONSTR _ _ b bs => CONSTR (op _ b) (list_iter _ bs)
     end.

End list_iter.
(** renaming is a mutually recursive function *)

(*
Fixpoint rename (V : ITYPE T) (W : ITYPE T)
    (f : V ---> W) t (v : STS V t) : STS W t := 
    match v in STS _ t return STS W t with
    | Var t v => Var _ _ (f t v)
    | Build t i s => 
         Build W t i 
    (( fix rename_ V0 W0 (f0 : V0 ---> W0)  
          l (s' : prod_mod_c STS V0 l) : prod_mod_c STS W0 l :=
            match s' in prod_mod_c _ _ l' return prod_mod_c STS W0 l' with
            | TTT => TTT _ _ 
            | CONSTR b bs elem elems => 
                    CONSTR  (M:=STS) (V:=W0) (b:=b)(bs:=bs) 
                       (rename (*V0 ** (fst b)) (W0 ** (fst b)*) _ _
                           (f0 ^^ (fst b)) _ elem)
                           (rename_ V0 W0 f0 bs elems)
            end) V W f _ s)
    end.
*)

Fixpoint rename (V : ITYPE T) (W : ITYPE T)
    (f : V ---> W) t (v : STS V t) : STS W t := 
    match v in STS _ t return STS W t with
    | Var t v => Var (f t v)
    | Build t i s => 
         Build  
    (( fix rename_ 
          l (s' : prod_mod_c STS V l) : prod_mod_c STS W l :=
            match s' in prod_mod_c _ _ l' return prod_mod_c STS W l' with
            | TTT => TTT _ _ 
            | CONSTR b bs elem elems => 
                    CONSTR (rename (f ^^ (fst b)) elem)
                           (rename_ _ elems)
            end) _ s)
    end.

Fixpoint list_rename V W f l (x : prod_mod_c STS V l) : 
                     prod_mod_c STS W l :=
     match x in prod_mod_c _ _ l return prod_mod_c STS W l with
     | TTT => TTT _ _ 
     | CONSTR b bs elem elems => 
            CONSTR (rename (f ^^ (fst b)) elem)
                   (list_rename _ f elems)
     end.

Notation "x //- f" := (rename f x).
Notation "x //-- f" := (list_rename f x).


(*
Lemma ren V t (i : sig_index (S t)) (x : prod_mod_c STS V (sig i)) 
          W (f : V ---> W):
       rename f (Build x) = Build (list_rename f x).
Proof.
  intros V t i x.
  
  intros.
  
  elim x using 
  dependent induction x.
  rewrite <- x.
  simpl.
  apply f_equal.
  
  dependent induction x0.
  *)
    

(** functoriality of renaming for STS *)

Require Import Coq.Program.Equality.

Lemma rename_eq : forall (V : T -> Type) (t : T) (v : STS V t) 
         (W : T -> Type) (f g : V ---> W),
     (forall t x, f t x = g t x) -> v //- f = v //- g.
Proof.
  intros. Check STSind. Check STS_ind2.
  induction v using STS_ind2.
  simpl.
  intros.
  rewrite H.
  auto.
  dependent induction H0.
  assert (H':=JMeq_eq x).
  destruct x.
  dependent induction x.
  inversion H0.
  simpl.
  apply f_equal.
  destruct H0.
  auto.
  apply CONSTR_eq.
  
  
  simpl.
  auto.
  apply subst_eq.
  simpl.
   (STSind (Q:=fun V l x => Build x //- f = Build x //- g)).
  simpl.
  intros.
  rewrite H.
  
  auto.
  inversion H0.
  subst.
  
  
  case x.
  dependent induction x.
  destruct x0.

  simpl.

  dependent destruction x.
  s
  simpl.
  intros.
  generalize dependent H.
  
  
  simpl.
  elim x; 
  simpl.
  

  assert (H:= (@STSind 
       (fun (a : T -> Type) t (v : STS a t) => 
            forall (b : T -> Type)(f g : a ---> b),
         (f == g) ->
         rename (W:=b) f v = rename (W:=b) g v))
       (fun V l (v : prod_mod_c STS V l) => 
            forall (b : T -> Type)(f g : V ---> b),
         (f == g) ->
         list_rename f v = list_rename g v)).
  apply H;
  clear H; lazy iota beta delta; intros.
  
  apply f_equal.
  fold rename_.
  unfold list_rename in H.

  
  intros V t i s H' W f g H2; 
  simpl.
  apply f_equal;
  auto.
  unfold list_rename in H'.
  
  apply H'.
  simpl.
  

  intros V t v b f g H'; 
  simpl.
  rewrite H'.
  auto.
  
  intros V t i s H' W f g H2; 
  simpl.
  apply f_equal;
  auto.
  
  intros; simpl;
  auto.
  
  intros V b bs s H'
  s0 H2 W f g H3;
  simpl.
  apply constr_eq;
  auto.
  apply H'.
  rewrite H3.
  cat.
Qed.

Hint Resolve rename_eq constr_eq : fin.
Hint Rewrite rename_eq constr_eq : fin.

Obligation Tactic := unfold Proper ; red; fin.

Program Instance rename_oid V W : 
  Proper (A:=(V ---> W) -> (STS V ---> STS W)) 
       (equiv ==> equiv) (@rename V W).

Lemma rename_id V t (x : STS V t) : x //- id _ = x .
Proof.
  assert (H:= @STSind 
      (fun a t (x : STS a t) => 
           x //- id _ = x)
      (fun a t (l : STS_list a t) => 
            l //-- id _ = l)).
  apply H; 
  simpl;
  auto;
  clear H.
  
  intros V t i s H.
  rewrite H.
  auto.
  
  intros V b bs s H s0 H1.
  rewrite <- H at 2.
  assert (H':=preserve_ident (Func:=POW (fst b))). 
  fin.
Qed.


Lemma rename_comp V t (x : STS V t) W (f : V ---> W) X (g : W ---> X):
 x //- (fun s y => g s (f s y)) =  x //- f //- g.
Proof.
  assert (H:= @STSind 
   (fun a t (x : STS a t) => 
     forall b (f : a ---> b) c (g : b ---> c),
      x //- (f ;; g) = x //- f //- g)
   (fun a t (l : STS_list a t) => 
     forall b (f : a ---> b) c (g : b ---> c),
      l //-- (f ;; g) = l //-- f //-- g )).
  apply H;
  simpl;
  auto;
  clear H.
  
  intros V t i s H0 W f X g.
  rewrite H0. 
  auto.
  
  intros V b bs s H s0 H0 b0 f c g.
  rewrite <- H.
  assert (H':=preserve_comp (Func:=POW (fst b))).
  fin.
Qed.

Hint Rewrite rename_comp rename_id : fin.
Hint Resolve rename_comp rename_id : fin.

Obligation Tactic := fin.

Program Instance rename_func : Func (Fobj := @STS) rename.

(** injection of a term into the type of terms with one more variable *)

Definition inj u V := rename (V:=V) (W:=V * u) 
                (@some T u V).


Definition inj_list u V := 
    fun t (v : STS_list V t) => list_rename v (@some T u V).

(** the shifting, needed to avoid capture *)
(** we'll call it _shift in order to avoid clash with generic shift *)

Definition _shift (u : T) (V W : ITYPE T) (f : V ---> STS W) : 
         V * u ---> STS (W * u) :=
   fun t v => 
   match v in (opt _ _ y) return (STS (W * u) y) with
   | some t0 p => inj u (f t0 p)
   | none => Var (none u W)
   end.

Notation "x >- f" := (_shift f x) (at level 40).

(** same for lshift, being given a list of object language types *)

Fixpoint _lshift (l : [T]) (V W : ITYPE T) (f : V ---> STS W) : 
        V ** l ---> STS (W ** l) :=
    match l return V ** l ---> STS (W**l) with
    | nil => f
    | b::bs => @_lshift bs _ _ (_shift (u:=b) f)
    end.

(*Implicit Arguments shift_l [V W t].*)

Notation "x >>-- f" := (_lshift f x) (at level 40).

(*Notation "f $$ l" := (shift_list l f) (at level 20).*)


(** finally the substitution *)
Reserved Notation "x >== f" (at level  59, left associativity).
Reserved Notation "x >>== f" (at level 59, left associativity).

Fixpoint subst (V W : ITYPE T) (f : V ---> STS W) t (v : STS V t) : 
  STS W t :=  match v in STS _ t return STS W t with
    | Var t v => f t v
    | Build t i l => Build (l >>== f)
    end
with
  list_subst V t (l : STS_list V t) W (f : V ---> STS W) : STS_list W t :=
     match l in STS_list _ t return STS_list W t with
     | TT => TT W 
     | constr b bs elem elems => 
       constr (elem >== (_lshift f)) (elems >>== f)
     end
where "x >== f" := (subst f x) 
and "x >>== f" := (list_subst x f).

  
(** substitution of one variable only *)

Definition substar (u : T) (V : ITYPE T) (M : STS V u) :
           STS (V * u) ---> STS V :=
 subst (fun t (x : opt u V t) => match x with
         | none => M
         | some _ v => Var v
         end).

Notation "M [*:= N ]" := (substar N M) (at level 50).


(**  FUSION LAWS *)
(**  a boring section, don't read it *)

Hint Extern 1 (_ = _) => f_equal : fin.

Lemma _shift_eq u V W (f g : V ---> STS W) 
     (H : forall t x, f t x = g t x) t (x : opt u V t) : 
          x >- f = x >- g.
Proof.
  intros u V W f g H t v.
  destruct v;
  fin. 
Qed.

Hint Resolve _shift_eq : fin.
Hint Rewrite _shift_eq : fin.

Instance shift_oid u V W : 
  Proper (equiv ==> equiv) (@_shift u V W).
Proof.
  unfold Proper;
  red; fin.
Qed.
  

Lemma _lshift_eq l (V W:ITYPE T) (f g : V ---> STS W) 
    (H : forall t x, f t x = g t x) t (x : V ** l t) : 
       x >>-- f = x >>-- g.
Proof.
  induction l; fin.
Qed.

Hint Resolve _lshift_eq : fin.
Hint Rewrite _lshift_eq : fin.
  
Instance _lshift_oid l V W : 
    Proper (equiv ==> equiv) (@_lshift l V W).
Proof.
  unfold Proper;
  red; fin.
Qed.

Lemma shift_var u (V : ITYPE T) t (x : opt u V t) :
       x >- @Var _ = Var x .
Proof.
  simpl.
  intros u V t x;
  induction x;
  fin.
Qed.

Hint Resolve shift_var : fin.
Hint Rewrite shift_var : fin.

Lemma shift_l_var l V t (x : V ** l t) : 
      x >>-- @Var _ = Var x .
Proof.
  intro l;
  induction l;
  simpl;
  intros;
  auto.
  transitivity (_lshift (Var (V:= opt a V)) x);
  fin.
Qed.
  
Lemma var_lift_shift (u : T) V W (f : V ---> W) t (x : opt u V t) :
     Var (^f _ x) = x >- (f ;; @Var _ ).
Proof.
  intros u V W f t x;
  induction x; fin.
Qed.

Hint Resolve var_lift_shift : fin.

Lemma var_lift_shift_l (l : [T]) V W (f : V ---> W) t x : 
       Var ((f ^^ l) t x)  =  x >>-- (f ;; @Var _ ) .
Proof.
  intro l;
  induction l;
  simpl in *;
  intros;
  auto.
  assert (H:=var_lift_shift).
  transitivity (x >>-- (^f ;; @Var _ ));
  fin.
Qed.

Lemma shift_lift u V W X (f : V ---> W) 
         (g : W ---> STS X) t (x : opt u V t) :
      (^f _ x) >- g = x >- (f ;; g).
Proof.
  intros u V W X f g t x.
  induction x; fin.
Qed.

Hint Resolve shift_lift var_lift_shift_l : fin.
Hint Rewrite shift_lift : fin.

Lemma shift_lift_list l V W X (f : V ---> W) (g : W ---> STS X) t x:
        (f ^^ l t x) >>-- g =  x >>-- (f ;; g).
Proof.
  intro l;
  induction l;
  simpl;
  auto.
  
  intros V W X f g t x.
  simpl in IHl.
  rewrite IHl.
  simpl.
  apply _lshift_eq.
  fin.
Qed. 

Lemma subst_eq V t (x : STS V t) 
      W (f g : V ---> STS W) 
       (H : forall t x, f t x = g t x):  x >== f = x >== g.
Proof.
  assert (H:=@STSind 
      (fun V t x => forall W (f g : V ---> STS W)
              (H:f == g), x >== f = x >== g)
      (fun V l (v : STS_list V l) => 
               forall W (f g : V ---> STS W)(H:f == g),
           v >>== f = v >>== g) ).
  apply H;
  fin.
Qed.

Hint Resolve subst_eq shift_l_var 
  var_lift_shift_l _lshift_eq : fin.
Hint Rewrite subst_eq shift_l_var var_lift_shift_l : fin.

Obligation Tactic := unfold Proper; red; fin.

Program Instance subst_oid V W : 
 Proper (equiv ==> equiv (Setoid:=mor_oid (STS V) (STS W))) 
                (@subst V W).

Lemma subst_var (V : ITYPE T) : 
    forall t (v : STS V t), v >== (@Var V) = v .
Proof.
  assert (H:=@STSind
      (fun V t (v : STS V t) =>  v >== (Var (V:=V)) = v)
      (fun V l (v : STS_list V l) => v >>== (Var (V:=V)) = v)).
  simpl in *.
  apply H;
  simpl;
  clear H;
  auto.
  
  fin.

  intros V b bs s H v H1.
  rewrite <- H at 2. 
  fin.
Qed.
  

Lemma subst_eq_rename V t (v : STS V t) W (f : V ---> W)  : 
     v //- f  = v >== f ;; Var (V:=W).
Proof.
  assert (H:=@STSind 
    (fun V t (v : STS V t) => forall W (f : V ---> W),
       v //- f = v >== (f;;Var (V:=W)))
    (fun V l (v : STS_list V l) => forall W (f : V ---> W),
         v //-- f = v >>== (f ;; Var (V:=W))) ).
  simpl in *.
  apply H;
  simpl;
  auto;
  clear H.
  
  fin.

  intros V b bs v H 
     x H' W f.
  rewrite H'.
  rewrite H.
  apply constr_eq; auto.
  apply subst_eq. 
  fin.
Qed.

Lemma rename_shift a V W X (f : V ---> STS W) (g : W ---> X) t 
       (x : opt a V t) : 
    (x >- f) //- ^g = x >- (f ;; rename g).
Proof.
  intros a V W X f g t x.
  induction x;
  simpl;
  auto.
  unfold inj. 
  assert (H3 := preserve_comp (Func := rename_func)).
  simpl in H3.
  rewrite <- H3.
  rewrite <- H3.
  apply f_equal. 
  auto.
Qed.

Hint Rewrite rename_shift shift_lift_list : fin.
Hint Resolve rename_shift shift_lift_list : fin.

Lemma rename_shift_list (l : [T]) V t (x : V ** l t) 
              W X (f : V ---> STS W)
                    (g : W ---> X) :
      x >>-- f //-  g ^^ l =
      x >>-- (f ;; rename g).
Proof.
  intro l;
  induction l;
  simpl;
  auto.

  intros V t x W X f g.
  rewrite IHl.
  apply _lshift_eq.
  clear x t.   
  simpl; intros t x.
  assert (H:=rename_shift).
  fin.
Qed.

Hint Resolve rename_shift_list : fin.
Hint Rewrite rename_shift_list : fin.
  
Lemma rename_subst V t (v : STS V t) W X (f : V ---> STS W)
      (g : W ---> X) : 
      (v >== f) //- g  = v >== (f ;; rename g).
Proof.
  assert (H:=@STSind  
    (fun V t (v : STS V t) => forall W X (f : V ---> STS W)
                                         (g : W ---> X),
      (v >== f) //- g = v >== (f ;; rename g))
    (fun V l (v : STS_list V l) => forall W X 
              (f : V ---> STS W) (g : W ---> X),
      (v >>== f) //-- g = v >>== (f ;; rename g))).
  apply H;
  simpl;
  auto;
  clear H.
  
  intros V t i s H
      W X f g.
  rewrite H.
  auto.
  
  intros V b bs s H v 
     H' W X f g.
  rewrite H'.
  rewrite H.
  apply constr_eq; auto.
  apply subst_eq; fin.
Qed.

Lemma subst_rename V t (v : STS V t) W X (f : V ---> W)
      (g : W ---> STS X) : 
      v //- f >== g = v >== (f ;; g).
Proof.
  assert (H:=@STSind  
    (fun V t (v : STS V t) => forall W X (f : V ---> W)
                                         (g : W ---> STS X),
      v //- f >== g = v >== (f ;; g))
    (fun V l (v : STS_list V l) => forall W X 
              (f : V ---> W) (g : W ---> STS X),
      v //-- f >>== g = v >>== (f ;; g))).
  apply H;
  simpl;
  auto;
  clear H.
  
  fin.
 
  intros V b bs s H v 
     H' W X f g.
  rewrite H'.
  rewrite H.
  assert (H2:= shift_lift_list (l:=fst b)).
  fin.
Qed.


Lemma rename_substar V u t (v : STS (opt u V) t) W (f : V ---> W) N:
     v [*:= N] //- f = (v //- ^f) [*:= N //- f ].
Proof.
  intros.
  unfold substar.
  rewrite rename_subst.
  rewrite subst_rename.
  apply subst_eq.
  intros t0 x; 
  destruct x;  
  simpl; auto.
Qed.

Hint Rewrite rename_subst rename_subst : fin.

Lemma subst_shift_shift (u:T) V (t:T)(v : opt u V t)
         W X (f: V ---> STS W) (g: W ---> STS X):
    (v >- f) >== (_shift g)  = 
             v >- (f ;; subst g).
Proof.
  intros u V t v.
  induction v; 
  simpl; intros; 
  try apply subst_term_inj; auto.
  unfold inj.
  rewrite subst_rename. 
  fin.
Qed.

Hint Resolve subst_shift_shift : fin.
Hint Rewrite subst_shift_shift : fin.

Lemma subst_shift_shift_list (l : [T]) V t (v : V ** l t)
         W X (f: V ---> STS W) (g: W ---> STS X):
    v >>--f >== (_lshift g) = 
             v >>-- (f ;; subst g).
Proof.
  intro l;
  induction l;
  simpl;
  auto.
  
  intros V t v W X 
     f g.
  rewrite IHl.
  apply _lshift_eq. 
  fin.
Qed.


Hint Rewrite subst_shift_shift_list : fin.
Hint Resolve subst_shift_shift_list : fin.

Lemma subst_subst V t (v : STS V t) W X (f : V ---> STS W) 
             (g : W ---> STS X) :
     v >== f >== g = v >== f;; subst g.
Proof.
  assert (H:=@STSind   
    (fun (V : T -> Type) (t : T) (v : STS V t) => forall (W X : T -> Type)
          (f : V ---> STS W) (g : W ---> STS X),
        v >== f >== g = v >== (f;; subst g))
   (fun (V : T -> Type) l (v : STS_list V l) => 
       forall (W X : T -> Type)
          (f : V ---> STS W) (g : W ---> STS X),
        v >>== f >>== g = v >>== (f;; subst g) )).
  apply H;
  simpl;
  auto;
  clear H.
  
  fin.  
  
  intros V b bs s H
     s0 H' W X f g.
  rewrite H'. 
  rewrite H.
  apply constr_eq;
  auto.
  assert (H2:= subst_shift_shift_list (l:=fst b)).
  simpl in *. 
  fin.
Qed.

Hint Resolve subst_var subst_subst : fin.
Hint Rewrite subst_subst : fin.


Lemma lift_rename V t (s : STS V t) W (f : V ---> W) :
          s >== (f ;; @Var _) = s //- f.
Proof.
  assert (H:=@STSind 
    (fun V t s => forall W f,
       subst (f ;; Var (V:=W)) s =
               rename  f s)
    (fun V l s => forall W f,
        list_subst s (f ;; Var (V:=W)) =
             list_rename s f)).
  apply H;
  simpl;
  auto;
  clear H.
  
  fin.
  
  intros V b bs s
       H x H1 W f.
  rewrite H1.
  rewrite <- H.
  apply constr_eq;
  auto.
  apply subst_eq.
  fin.
Qed.

(** END OF FUSION LAWS *)

(** STS is a monad *)

Obligation Tactic := fin.

Program Instance STS_monad : 
     Monad_struct (ITYPE T) STS := {
  weta := Var;
  kleisli := subst
}.

Canonical Structure STSM := Build_Monad STS_monad.


(** as said before, STS_list is actually the same as 
    prod_mod_glue STS_monad. we give a module morphism translation *)


Fixpoint STSl_f_pm l V (x : prod_mod STSM l V)
         : STS_list V l :=
    match x in prod_mod_c _ _ l return STS_list V l with
    | TTT =>  TT V 
    | CONSTR b bs e el => constr e (STSl_f_pm el)
    end.

Fixpoint pm_f_STSl l V (v : STS_list V l) :
       prod_mod STSM l V :=
 match v in STS_list _ l return prod_mod STSM l V with
 | TT => TTT _ _ 
 | constr b bs elem elems => 
        CONSTR elem (pm_f_STSl elems)
 end.

Lemma one_way l V (v : STS_list V l) : 
    STSl_f_pm (pm_f_STSl v) = v.
Proof.
  intros l V v.
  induction v;
  fin.
Qed.

Lemma or_another l V (v : prod_mod STSM l V) : 
       pm_f_STSl (STSl_f_pm v) = v.
Proof.
  intros l V v;
  induction v;
  fin.
Qed.

(** we now establish some more properties, which will help in the future 
    
    in particular the mentioned equalities:
    - rename = lift
    - _shift = shift
*)

Lemma list_subst_eq V l (v : STS_list V l) W 
       (f g : V ---> STS W) (H : f == g) : 
          v >>== f =  v >>== g.
Proof.
  assert (H:=@STSlistind 
      (fun V t x => forall W (f g : V ---> STS W)
              (H:f == g), x >== f = x >== g)
      (fun V l (v : STS_list V l) => 
               forall W (f g : V ---> STS W)(H:f == g),
           v >>== f = v >>== g) ).
  apply H;
  fin.
Qed.



(** we establish some equalities *)

Hint Rewrite subst_eq_rename : fin.

(** shift = opt_inj STS *)

Notation "x >>- f" := (shift f x) (at level 50).
Notation "x >-- f" := (lshift f x) (at level 50).

Existing Instance STS_monad.

Lemma _shift_shift_eq a V W (f : V ---> STS W) t (x : opt a V t) :
        x >>- f = x >- f. 
Proof.
  intros a V W f t x.
  destruct x;
  simpl;
  auto.
  unfold lift, inj.
  fin.
Qed.

Hint Resolve _shift_shift_eq : fin.

Lemma _lshift_lshift_eq (l : [T]) V
     (t : T)(x : V ** l t) W (f : V ---> STS W):
       x >-- f = x >>-- f. 
Proof.
  induction l;
  simpl in *;
  intros;
  try rewrite IHl;
  fin.
Qed.

(**   rename = lift *)

Lemma lift_rename2 V t (s : STS V t) W (f : V ---> W): 
        lift f t s = s //- f.
Proof.
  fin.
Qed.



(** STSl_f_pm ;; list_subst = mkleisli ;; STSl_f_pm *)

Hint Resolve _lshift_lshift_eq : fin.

Notation "v >>>= f" := 
  (mkleisli (Module_struct := prod_mod STSM _) f v) (at level 67).
          
Lemma sts_list_subst l V (v : prod_mod STSM l V) 
       W (f : V ---> STS W):
  STSl_f_pm  (v >>>= f) = (STSl_f_pm v) >>== f.
Proof.
  intros l V v;
  induction v;
  fin.
Qed.


(** we define the Representation Structure, i.e. for every arity
    a module morphism *)

Obligation Tactic := fin; try apply f_equal;
                          try apply sts_list_subst.

Notation "y [( s )]" := ((ITFIB_MOD _ s) y) (at level 40).

Program Instance STS_arity_rep (t : T) (i : sig_index (S t)) : 
  Module_Hom_struct 
       (S := prod_mod STSM (sig i))
       (T := STSM [(t)]) 
       (fun V  X => Build (STSl_f_pm X)).

(**  STS has a structure as a representation of Sig *)

Canonical Structure STSrepr (t : T) : Repr_t S STSM t :=
       fun i => Build_Module_Hom (STS_arity_rep t i).

Canonical Structure STSRepr : REPRESENTATION S := 
       Build_Representation (fun t => @STSrepr t).


(** now INITIALITY *)

Section initiality.

Variable R : REPRESENTATION S.

(** the initial morphism STS -> R *)

Fixpoint init V t (v : STS V t) : R V t :=
        match v in STS _ t return R V t with
        | Var t v => weta (Monad_struct := R) V t v
        | Build  t i X => repr R i V (init_list X)
        end
with 
 init_list l (V : ITYPE T) (s : STS_list V l) : prod_mod R l V :=
    match s in STS_list _ l return prod_mod R l V with
    | TT => TTT _ _ 
    | constr b bs elem elems => 
         CONSTR (init elem) (init_list elems)
    end.


(** now for init to be a morphism of monads we need to establish
    commutativity with substitution

    the following lead towards this goal 
*)

(** init commutes with lift/rename *)

Lemma init_lift V t x W (f : V ---> W) : 
   init (x //- f) = lift f t (init x).
Proof.
  assert (H:=@STSind 
    (fun V t (x : STS V t) => forall W (f : V ---> W),
        init (x //- f) = lift f t (init x))
    (fun V l (s : STS_list V l) => forall 
                 W (f : V ---> W),
         (init_list (s //-- f)) =
            mlift (prod_mod R l) f (init_list s))). 
  apply H;
  simpl;
  auto;
  clear H.
  
  intros.
  assert (H:=lift_weta R).
  simpl in *.
  auto.
  
  intros.
  rewrite H.
  unfold mlift, lift.
  assert (H':=mod_hom_mkl (Module_Hom_struct:=repr R i)).
  simpl in *.
  auto.
  
  intros.
  rewrite H0.
  unfold mlift, lift.
  simpl.
  apply CONSTR_eq;
  simpl; auto.
  rewrite H.
  unfold lift.
  apply (kleisli_oid (Monad_struct :=R)).
  assert (H2:= lshift_weta_f).
  simpl in *.
  auto.
Qed.
  

(** init commutes with shift and lshift *)


Lemma init_shift a V W (f : V ---> STS W) :
   forall (t : T) (x : opt a V t),
  init (x >>- f) = x >>- (f ;; @init _).
Proof.
  intros a V W f t x.
  induction x;
  simpl;
  try rewrite <- init_lift;
  fin.
Qed.

Hint Rewrite init_shift : fin.

Lemma init_lshift (l : list T) V W 
      (f : V ---> STS W) t (x : V ** l t) :
     init (x >-- f) = x >-- (f ;; @init _).
Proof.
  intro l;
  induction l;
  simpl in *;
  auto.
  intros V W f t x.
  rewrite IHl.
  assert (H:= lshift_eq).
  simpl in H.
  apply H. 
  fin.
Qed.

Hint Rewrite init_lshift : fin.
  
(** init is a morphism of monads *)

Lemma init_kleisli V t (v : STS V t) W (f : V ---> STS W) :
  init (v >== f) =
  kleisli (f ;; @init _ ) t (init v).
Proof.
  assert (H:= @STSind 
     (fun X t (v : STS X t) => 
         forall Y (f : X ---> STS Y),
      init (v >== f) =
      kleisli (Monad_struct := R) 
            (f ;; @init _) t (init v))

     (fun X l (s : STS_list X l) => forall Y (f : X ---> STS Y),
           init_list (s >>== f) =
           mkleisli (Module_struct := prod_mod  R l)
              (f ;; @init _ ) 
                    (init_list s))).
  apply H;
  simpl;
  auto;
  clear H.

  assert (H':= eta_kl (Monad_struct := R)).
  simpl in H'.
  intros.
  rewrite H'.
  auto.
  
  intros V t i s H2 Y f .
  rewrite H2.
  assert (H:= mod_hom_mkl (Module_Hom_struct := repr R i)).
  simpl in *.
  rewrite H.
  auto.
  
  intros V b bs v H' s H
      Y f.
  apply CONSTR_eq;
  simpl;
  auto.
  rewrite H'.
  destruct b as [t l];
  simpl in *.
  apply (kleisli_oid (Monad_struct := R)) .
  intros t0 x.
  rewrite <- _lshift_lshift_eq.
  fin.
Qed.

Hint Rewrite init_kleisli CONSTR_eq: fin.
Hint Resolve init_kleisli CONSTR_eq: fin.

Obligation Tactic := fin.

Program Instance init_monadic : Monad_Hom_struct (P:=STSM) init.

Canonical Structure init_mon := Build_Monad_Hom init_monadic.

(** init is not only a monad morphism, but even a morphism of 
    representations *)

(** prod_ind_mod_mor INIT = init_list (up to STSl_f_pm) *)


Lemma prod_mor_eq_init_list t (i : sig_index (S t)) V 
       (x : prod_mod_c STS V (sig i)) :
  Prod_mor_c init_mon (*init*) x = init_list (STSl_f_pm x).
Proof.
  induction x; 
  fin.
Qed.

Hint Rewrite prod_mor_eq_init_list : fin.

Obligation Tactic :=  unfold commute; fin.

Program Instance init_representic : Representation_Hom_s
        (P:=STSRepr) init_mon (*init*).

Definition init_rep := Build_Representation_Hom init_representic.

(** INITIALITY of STSRepr with init *)

Lemma init_unique_prepa V t (v : STS V t)
  (f : Representation_Hom STSRepr R) : 
         f V t v = init v.
Proof.
  assert (H:= @STSind
     (fun V t v => forall f : Representation_Hom STSRepr R,
                  f V t v = init v)
     (fun V l v => forall f : Representation_Hom STSRepr R,
         Prod_mor f l V (pm_f_STSl v) = init_list v)).
  apply H;
  simpl;
  auto;
  clear H.
  intros V t v f.
  assert (H:=monad_hom_weta (Monad_Hom_struct := f)).
  simpl in H. 
  auto.

  intros V t i s H f.
  assert (H3:=repr_hom f (t:=t) (i:=i)).
  unfold commute in H3.
  simpl in H3.
  assert (H4:= one_way s).
  simpl in *.
  pattern s at 1.
  rewrite <- H4.
  simpl.
(*  rewrite <- H4 at 1.
  rewrite <- (one_way s) at 1.
(*  rewrite <- (one_way (l:=sig i) (V:=V) s) at 1.*) 
*)
  rewrite <- H3.
  apply f_equal.
  auto.
  
  fin.
Qed.

Hint Rewrite init_unique_prepa : fin.

Lemma init_unique :forall f : STSRepr ---> R , f == init_rep.
Proof.
  fin.
Qed.

End initiality.

Hint Rewrite init_unique : fin.

Obligation Tactic := fin.

Program Instance STS_initial : Initial (REPRESENTATION S) := {
  Init := STSRepr ;
  InitMor R := init_rep R }.


End initial_type.






