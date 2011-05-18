Require Export CatSem.CAT.Misc.
Require Export CatSem.STS.STS_representations.

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

Scheme STSrect := Induction for STS Sort Type with
       STSlistrect := Induction for STS_list Sort Type.

Lemma constr_eq : forall (V : ITYPE T) (b : [T] * T) 
            (bs : [[T] * T]) (x y : STS _ (snd b))
              (v w : STS_list V bs),
     x = y -> v = w -> constr x v = constr y w.
Proof.
  intros; subst; auto.
Qed.

Hint Rewrite constr_eq pow_map_eq : fin.
Hint Resolve constr_eq f_equal pow_map_eq : fin.

Reserved Notation "x //- f" (at level 42, left associativity).
Reserved Notation "x //-- f" (at level 42, left associativity).


(** renaming is a mutually recursive function *)

Fixpoint rename (V : ITYPE T) 
             (W : ITYPE T) (f : V ---> W) t (v : STS V t):=
    match v in STS _ t return STS W t with
    | Var t v => Var (f t v)
    | Build  t i l => Build (i:=i) (list_rename l f)
    end
with 
  list_rename V t (l : STS_list V t) W (f : V ---> W) : STS_list W t :=
     match l in STS_list _ t return STS_list W t with
     | TT => TT W 
     | constr b bs elem elems => 
             constr (elem //- ( f ^^ (fst b)))
                               (elems //-- f)
     end
where "x //- f" := (rename f x) 
and "x //-- f" := (list_rename x f).

(** functoriality of renaming for STS *)

Hint Extern 1 (_ = _) => apply f_equal.

Ltac t := repeat (cat || apply constr_eq || rew_all
                      || app_any || fin).

Lemma rename_eq : forall (V : T -> Type) (t : T) (v : STS V t) 
         (W : T -> Type) (f g : V ---> W),
     (forall t x, f t x = g t x) -> v //- f = v //- g.
Proof.
  app (@STSind 
       (fun (a : T -> Type) t (v : STS a t) => 
            forall (b : T -> Type)(f g : a ---> b),
         (f == g) ->
         rename (W:=b) f v = rename (W:=b) g v)
       (fun V l (v : STS_list V l) => 
            forall (b : T -> Type)(f g : V ---> b),
         (f == g) ->
         v //-- f =  v //-- g)); t.
Qed.

Hint Resolve rename_eq constr_eq pow_id pow_comp : fin.
Hint Rewrite rename_eq constr_eq pow_id pow_comp : fin.

Obligation Tactic := unfold Proper ; red; fin.

Program Instance rename_oid V W : 
  Proper (A:=(V ---> W) -> (STS V ---> STS W)) 
       (equiv ==> equiv) (@rename V W).

Hint Extern 1 (?f ^^ _ _ ?x = ?x) => apply pow_eq_id.

Lemma rename_eq_id V t (x : STS V t) (f : V ---> V) :
     f == id _ -> x //- f = x.
Proof.
  apply (@STSind
       (fun a t (x : STS a t) => forall f, f == id _ ->
               x //- f = x)
       (fun a t (l : STS_list a t) => forall f, f == id _ ->
            l //-- f = l)); t.
Qed.   

Lemma rename_id V t (x : STS V t) : x //- id _ = x .
Proof. 
  repeat (t || apply rename_eq_id).
Qed.

Ltac tt := repeat (t || 
      match goal with [|- ?s //- _ = ?s //- _] => 
              apply rename_eq end ||
      elim_opt ||
      rew pow_comp).

Lemma rename_comp V t (x : STS V t) W (f : V ---> W) X (g : W ---> X):
    x //- f //- g = x //- (fun s y => g s (f s y)).
Proof.
  apply (@STSind 
   (fun a t (x : STS a t) => 
     forall b (f : a ---> b) c (g : b ---> c),
      x //- f //- g = x //- (fun s y => g s (f s y)))
   (fun a t (l : STS_list a t) => 
     forall b (f : a ---> b) c (g : b ---> c),
       l //-- f //-- g  = l //-- (f ;; g))); tt. 
Qed.

Hint Rewrite rename_comp rename_id : fin.
Hint Resolve rename_comp rename_id : fin.

Obligation Tactic := fin.

Program Instance rename_func : Functor_struct (Fobj := @STS) rename.

(** injection of a term into the type of terms with one more variable *)

Definition inj u V := rename (@some T u V).

Definition inj_list u V := 
    fun t (v : STS_list V t) => list_rename v (@some T u V).

(** the shifting, needed to avoid capture *)
(** we'll call it _ shift in order to avoid clash with generic shift *)

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
  list_subst V W t (l : STS_list V t) (f : V ---> STS W) : STS_list W t :=
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
  tt.
Qed.

Hint Resolve _shift_eq : fin.
Hint Rewrite _shift_eq : fin.

Obligation Tactic := repeat red; fin.

Program Instance shift_oid u V W : 
  Proper (equiv ==> equiv) (@_shift u V W).

Lemma _lshift_eq l (V W:ITYPE T) (f g : V ---> STS W) 
    (H : forall t x, f t x = g t x) t (x : V ** l t) : 
       x >>-- f = x >>-- g.
Proof.
  induction l; fin.
Qed.

Hint Resolve _lshift_eq : fin.
Hint Rewrite _lshift_eq : fin.
  
Program Instance _lshift_oid l V W : 
    Proper (equiv ==> equiv) (@_lshift l V W).

Lemma shift_var u (V : ITYPE T) t (x : opt u V t) :
       x >- @Var _ = Var x .
Proof.
  tt.
Qed.

Hint Resolve shift_var : fin.
Hint Rewrite shift_var : fin.

Ltac ttinv := repeat (tt || rerew_all; fin).

Lemma shift_l_var l V t (x : V ** l t) : 
      x >>-- @Var _ = Var x .
Proof.
  induction l;  ttinv.
Qed.

Hint Resolve shift_l_var : fin.

Lemma shift_l_var' l V : _lshift (l:=l) (Var (V:=V)) == Var (V:=_).
Proof. 
  tt.
Qed.
  
Lemma var_lift_shift (u : T) V W (f : V ---> W) t (x : opt u V t) :
     Var (^f _ x) = x >- (f ;; @Var _ ).
Proof.
  induction x; tt.
Qed.

Hint Resolve var_lift_shift shift_l_var' : fin.
Hint Rewrite var_lift_shift shift_l_var' : fin.

Ltac elim_lshift := match goal with 
     [|-?x >>-- _ = ?x >>-- _ ] => apply _lshift_eq end.

Ltac t4 := repeat (tt || elim_lshift).

Lemma var_lift_shift_l (l : [T]) V W (f : V ---> W) t x : 
       Var ((f ^^ l) t x)  =  x >>-- (f ;; @Var _ ) .
Proof.
  induction l; t4.
Qed.

Lemma shift_lift u V W X (f : V ---> W) 
         (g : W ---> STS X) t (x : opt u V t) :
      (^f _ x) >- g = x >- (f ;; g).
Proof.
  induction x; fin.
Qed.

Hint Resolve shift_lift var_lift_shift_l : fin.
Hint Rewrite shift_lift : fin.

Lemma shift_lift_list l V W X (f : V ---> W) (g : W ---> STS X) t x:
        (f ^^ l t x) >>-- g =  x >>-- (f ;; g).
Proof.
  induction l; t4.
Qed. 

Lemma subst_eq V t (x : STS V t) 
      W (f g : V ---> STS W) 
       (H : forall t x, f t x = g t x):  x >== f = x >== g.
Proof.
  app (@STSind 
      (fun V t x => forall W (f g : V ---> STS W)
              (H:f == g), x >== f = x >== g)
      (fun V l (v : STS_list V l) => 
               forall W (f g : V ---> STS W)(H:f == g),
           v >>== f = v >>== g) );
  fin.
Qed.

Lemma lsubst_eq V l (x : STS_list V l) 
      W (f g : V ---> STS W) 
       (H : forall t x, f t x = g t x):  x >>== f = x >>== g.
Proof.
  app (@STSlistind 
      (fun V t x => forall W (f g : V ---> STS W)
              (H:f == g), x >== f = x >== g)
      (fun V l (v : STS_list V l) => 
               forall W (f g : V ---> STS W)(H:f == g),
           v >>== f = v >>== g) );
  fin.
Qed.

Hint Resolve subst_eq shift_l_var 
  var_lift_shift_l _lshift_eq lsubst_eq : fin.
Hint Rewrite subst_eq shift_l_var var_lift_shift_l : fin.

Obligation Tactic := unfold Proper; red; fin.

Program Instance subst_oid V W : 
 Proper (equiv ==> equiv (Setoid:=mor_oid (STS V) (STS W))) 
                (@subst V W).


Ltac elim_fun := match goal with 
     [|-?x >>-- _ = ?x >>-- _ ] => apply _lshift_eq 
   | [|- lshift _ ?x = lshift _ ?x ] => app lshift_eq
   | [|-?x >== _ = ?x >== _ ] => apply subst_eq 
   | [|-constr _ _ = constr _ _ ] => apply constr_eq
   | [|-?x //- _ = ?x //- _ ] => apply rename_eq 
   | [|-?x >- _ = ?x >- _ ] => apply _shift_eq 
   | [|-?x >>== _ = ?x >>== _ ] => apply lsubst_eq 
   | [|-CONSTR _ _ = CONSTR _ _ ] => apply CONSTR_eq
   | [|- _ = _ ] => apply f_equal end.

Ltac t5 := repeat (elim_fun || tt || unfold inj, substar).

Lemma subst_var (V : ITYPE T) : 
    forall t (v : STS V t), v >== (@Var V) = v .
Proof.
  apply (@STSind
      (fun V t (v : STS V t) =>  v >== (Var (V:=V)) = v)
      (fun V l (v : STS_list V l) => v >>== (Var (V:=V)) = v)); 
  repeat (t5 ||
      match goal with [|- ?s >== _lshift _ = ?s ]=>
      transitivity (s >== (Var (V:=_))) end ).
Qed.

Lemma subst_eq_rename V t (v : STS V t) W (f : V ---> W)  : 
     v //- f  = v >== f ;; Var (V:=W).
Proof.
  apply (@STSind 
    (fun V t (v : STS V t) => forall W (f : V ---> W),
       v //- f = v >== (f;;Var (V:=W)))
    (fun V l (v : STS_list V l) => forall W (f : V ---> W),
         v //-- f = v >>== (f ;; Var (V:=W))) );
  t5.
Qed.

Lemma rename_shift a V W X (f : V ---> STS W) (g : W ---> X) t 
       (x : opt a V t) : 
    x >- f //- ^g = x >- (f ;; rename g).
Proof.
  induction x; t5.
Qed.

Hint Rewrite rename_shift shift_lift_list : fin.
Hint Resolve rename_shift shift_lift_list : fin.

Lemma rename_shift_list (l : [T]) V t (x : V ** l t) 
              W X (f : V ---> STS W)
                    (g : W ---> X) :
      x >>-- f //-  g ^^ l =
      x >>-- (f ;; rename g).
Proof.
  induction l; t5.
Qed.

Hint Resolve rename_shift_list : fin.
Hint Rewrite rename_shift_list : fin.
  
Lemma rename_subst V t (v : STS V t) W X (f : V ---> STS W)
      (g : W ---> X) : 
      (v >== f) //- g  = v >== (f ;; rename g).
Proof.
  apply (@STSind  
    (fun V t (v : STS V t) => forall W X (f : V ---> STS W)
                                         (g : W ---> X),
      (v >== f) //- g = v >== (f ;; rename g))
    (fun V l (v : STS_list V l) => forall W X 
              (f : V ---> STS W) (g : W ---> X),
      (v >>== f) //-- g = v >>== (f ;; rename g)));
  t5.
Qed.

Lemma subst_rename V t (v : STS V t) W X (f : V ---> W)
      (g : W ---> STS X) : 
      v //- f >== g = v >== (f ;; g).
Proof.
  apply (@STSind  
    (fun V t (v : STS V t) => forall W X (f : V ---> W)
                                         (g : W ---> STS X),
      v //- f >== g = v >== (f ;; g))
    (fun V l (v : STS_list V l) => forall W X 
              (f : V ---> W) (g : W ---> STS X),
      v //-- f >>== g = v >>== (f ;; g)));
  t5.
Qed.

Hint Resolve subst_rename rename_subst : fin.
Hint Rewrite subst_rename rename_subst : fin.
Hint Unfold substar : fin.

Lemma rename_substar V u t (v : STS (opt u V) t) W (f : V ---> W) N:
     v [*:= N] //- f = (v //- ^f) [*:= N //- f ].
Proof.
  t5.
Qed.

Hint Rewrite rename_subst rename_subst : fin.

Lemma subst_shift_shift (u:T) V (t:T)(v : opt u V t)
         W X (f: V ---> STS W) (g: W ---> STS X):
    (v >- f) >== (_shift g)  = 
             v >- (f ;; subst g).
Proof.
  induction v; t5.
Qed.

Hint Resolve subst_shift_shift : fin.
Hint Rewrite subst_shift_shift : fin.

Lemma subst_shift_shift_list (l : [T]) V t (v : V ** l t)
         W X (f: V ---> STS W) (g: W ---> STS X):
    v >>--f >== (_lshift g) = 
             v >>-- (f ;; subst g).
Proof.
  induction l; t5.
Qed.

Hint Rewrite subst_shift_shift_list : fin.
Hint Resolve subst_shift_shift_list : fin.

Lemma subst_subst V t (v : STS V t) W X (f : V ---> STS W) 
             (g : W ---> STS X) :
     v >== f >== g = v >== f;; subst g.
Proof.
  apply (@STSind   
    (fun (V : T -> Type) (t : T) (v : STS V t) => forall (W X : T -> Type)
          (f : V ---> STS W) (g : W ---> STS X),
        v >== f >== g = v >== (f;; subst g))
   (fun (V : T -> Type) l (v : STS_list V l) => 
       forall (W X : T -> Type)
          (f : V ---> STS W) (g : W ---> STS X),
        v >>== f >>== g = v >>== (f;; subst g) ));
  t5.
Qed.

Hint Resolve subst_var subst_subst : fin.
Hint Rewrite subst_subst : fin.

Ltac tinv := t5; repeat (rerew_all || elim_fun); t5.

Lemma lift_rename V t (s : STS V t) W (f : V ---> W) :
          s >== (f ;; @Var _) = s //- f.
Proof.
  app (@STSind 
    (fun V t s => forall W f,
       subst (f ;; Var (V:=W)) s =
               rename  f s)
    (fun V l s => forall W f,
        list_subst s (f ;; Var (V:=W)) =
             list_rename s f));
  tinv.
Qed.

(** END OF FUSION LAWS *)

(** STS is a monad *)

Obligation Tactic := fin.

Program Instance STS_monad : 
     Monad_struct (C:=ITYPE T) STS := {
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
  induction v; fin.
Qed.

Lemma or_another l V (v : prod_mod STSM l V) : 
       pm_f_STSl (STSl_f_pm v) = v.
Proof.
  induction v; fin.
Qed.

(** we now establish some more properties, which will help in the future 
    
    in particular the mentioned equalities:
    - rename = lift
    - _ shift = shift
*)

Lemma list_subst_eq V l (v : STS_list V l) W 
       (f g : V ---> STS W) (H : f == g) : 
          v >>== f =  v >>== g.
Proof.
  apply (@STSlistind 
      (fun V t x => forall W (f g : V ---> STS W)
              (H:f == g), x >== f = x >== g)
      (fun V l (v : STS_list V l) => 
               forall W (f g : V ---> STS W)(H:f == g),
          v >>== f = v >>== g) );
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
  t5.
Qed.

Hint Resolve _shift_shift_eq : fin.

Lemma _lshift_lshift_eq (l : [T]) V
     (t : T)(x : V ** l t) W (f : V ---> STS W):
       x >-- f = x >>-- f. 
Proof.
  induction l; t5.
Qed.

(**   rename = lift *)

Lemma lift_rename2 V t (s : STS V t) W (f : V ---> W): 
        lift f t s = s //- f.
Proof.
  fin.
Qed.

(** STSl_f_pm ;; list_subst = mkleisli ;; STSl_f_pm *)

Hint Resolve _lshift_lshift_eq : fin.

Notation "v >>>= f" := (pm_mkl f v) (at level 67).
          
Lemma sts_list_subst l V (v : prod_mod STSM l V) 
       W (f : V ---> STS W):
  STSl_f_pm  (v >>>= f) = (STSl_f_pm v) >>== f.
Proof.
  induction v; t5.
Qed.

Hint Resolve sts_list_subst : fin.
Hint Rewrite sts_list_subst : fin.

(** we define the Representation Structure, i.e. for every arity
    a module morphism *)

Obligation Tactic := t.

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
       Build_Representation (@STSrepr).

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

Ltac tt := t5; unfold lift, mlift;
           repeat (t || rew (lift_weta R) || app (kl_eq R) 
                     || rew (kleta R) || rew (etakl R)
                     || rew lshift_weta_f ).

Lemma init_lift V t x W (f : V ---> W) : 
   init (x //- f) = lift f t (init x).
Proof.
  apply (@STSind 
    (fun V t (x : STS V t) => forall W (f : V ---> W),
        init (x //- f) = lift f t (init x))
    (fun V l (s : STS_list V l) => forall 
                 W (f : V ---> W),
         (init_list (s //-- f)) =
            mlift (prod_mod R l) f (init_list s)));
  repeat (tt ||
    match goal with [|-(module_hom ?H) _ _ = _ ] => 
        rew (mod_hom_mkl (Module_Hom_struct := H)) end).
Qed.

(** init commutes with shift and lshift *)

Lemma init_shift a V W (f : V ---> STS W) :
   forall (t : T) (x : opt a V t),
  init (x >>- f) = x >>- (f ;; @init _).
Proof.
  induction x; 
  repeat (t5 || rerew init_lift).
Qed.

Hint Rewrite init_shift : fin.

Lemma init_lshift (l : list T) V W 
      (f : V ---> STS W) t (x : V ** l t) :
     init (x >-- f) = x >-- (f ;; @init _).
Proof.
  induction l; t5.
Qed.

Hint Rewrite init_lshift : fin.
Hint Resolve init_lshift : fin.
(** init is a morphism of monads *)

Lemma init_kleisli V t (v : STS V t) W (f : V ---> STS W) :
  init (v >== f) =
  kleisli (f ;; @init _ ) t (init v).
Proof.
  apply (@STSind 
     (fun X t (v : STS X t) => 
         forall Y (f : X ---> STS Y),
      init (v >== f) =
      kleisli (Monad_struct := R) 
            (f ;; @init _) t (init v))

     (fun X l (s : STS_list X l) => forall Y (f : X ---> STS Y),
           init_list (s >>== f) =
           mkleisli (Module_struct := prod_mod  R l)
              (f ;; @init _ ) 
                    (init_list s)));
  repeat (tt ||
       match goal with [|-(module_hom ?H) _ _ = _ ] => 
        rew (mod_hom_mkl (Module_Hom_struct := H)) end ||
        rerew init_lshift).
Qed.

Hint Rewrite init_kleisli : fin.
Hint Resolve init_kleisli : fin.

Obligation Tactic := fin.

Program Instance init_monadic : Monad_Hom_struct (P:=STSM) init.

Canonical Structure init_mon := Build_Monad_Hom init_monadic.

(** init is not only a monad morphism, but even a morphism of 
    representations *)

(** prod_ind_mod_mor INIT = init_list (up to STSl_f_pm) *)


Lemma prod_mor_eq_init_list t (i : sig_index (S t)) V 
       (x : prod_mod_c STS V (sig i)) :
  Prod_mor_c init_mon  x = init_list (STSl_f_pm x).
Proof.
  induction x; fin.
Qed.

Obligation Tactic := 
        unfold commute; fin; try rew prod_mor_eq_init_list.

Program Instance init_representic : Representation_Hom_struct
        (P:=STSRepr) init_mon (*init*).

Definition init_rep := Build_Representation_Hom init_representic.

(** INITIALITY of STSRepr with init *)

Section init.

Variable f : Representation_Hom STSRepr R.

Hint Rewrite one_way : fin.

Ltac ttt := tt;
            (try match goal with [t:T, s : STS_list _ _ |-_] =>
             rewrite <- (one_way s);
             let H:=fresh in assert (H:=repr_hom f (t:=t));
             unfold commute in H; simpl in H end);
             repeat (app (mh_weta f) || tinv || tt).

(*

tt; try app (mh_weta f);
         match goal with [x : STS_list _ _ |- _ ] =>
             try rerew (one_way x) end;
         match goal with [t:T|-_] =>
         try let H:=fresh in assert (H:=repr_hom f (t:=t));
          unfold commute in H; simpl in H; rerew H end;
          try elim_fun; t.
*)

Lemma init_unique_prepa V t (v : STS V t) : 
         f V t v = init v.
Proof.
  apply (@STSind
     (fun V t v => f V t v = init v)
     (fun V l v => Prod_mor f l V (pm_f_STSl v) = init_list v));
  ttt.
Qed.

End init.

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






