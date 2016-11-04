Require Import CatSem.CAT.functor.
Require Import CatSem.CAT.cat_TYPE.
Require Import CatSem.CAT.monad_haskell.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Automatic Introduction.

Section pts.

Variable sort: Type.

Inductive term (V: Type): Type :=
  var :  V -> term V |
  srt :  sort -> term V |
  app :  term V -> term V -> term V |
  pi :  term V -> term (option V) -> term V |
  lda : term V -> term (option V) -> term V.
(*
Implicit Arguments var [n].
Implicit Arguments srt [n].
Implicit Arguments app [n].
Implicit Arguments pi [n].
Implicit Arguments lda [n].

*)

Definition lift (V W: Type) (f: V -> W) (v: option V) : option W :=
    match v with 
    | None => None
    | Some v' => Some (f v')
    end.

Lemma lift_id_ (V: Type) (x: option V) (f: V -> V) (H: forall x, f x = x):
              lift f x = x.
Proof. intros V x f H; destruct x; simpl; try rewrite H; auto. Qed.

Hint Resolve lift_id_: pts.

Lemma lift_id (V: Type) : forall x, lift (V:= V) (fun v => v) x = x.
Proof. auto with pts. Qed.

Lemma lift_comp (V W X:Type) (x: option V) (f: V -> W) (g: W -> X): 
          lift (fun x => g (f x)) x = lift g (lift f x).
Proof. intros until x; destruct x; auto. Qed.

(*
Lemma lift_comp (V W: Type) (f g: V -> W) (H: forall x, f x = g x): 
            forall x, lift (fun v => v) x
*)
Program Definition OPT : Functor TYPE TYPE := Build_Functor
   (Fobj := fun V => option V) (Fmor := fun V W f =>  lift f) _ .

Next Obligation.
Proof. 
  constructor.
  unfold Proper. red.
  intros a b f g H x.
  destruct x; simpl; try rewrite H; auto.
  
  intro a; simpl. 
  apply lift_id.
  
  intros a b c f g; simpl.
  intro x; apply lift_comp.
Qed.

Lemma lift_eq_ (V W: obj TYPE) (f g: V ---> W) (H: f == g) :
               forall x, lift f x = lift g x.
Proof. 
  intros V W f g H x; 
  destruct x; simpl; 
  try rewrite H; auto.
Qed.

Hint Resolve lift_eq_ : pts. 


Ltac pts:= intros; simpl; auto with pts.

Lemma lift_eq (V W: obj TYPE) (f g: V ---> W) (H: f == g) :
              #OPT f == #OPT g.
Proof. pts. Qed. 

Fixpoint rename (V W: Type)(f: V -> W)(x: term V): term W :=
          match x with
          | var z => var (f z)
          | srt _ s => srt W s
          | app x u => app (rename f x) (rename f u)
          | pi s t => pi (rename f s) (rename (lift f) t)
          | lda s t => lda (rename f s) (rename (lift f) t)
          end.

Lemma rename_eq (V W: obj TYPE) (f g: V ---> W) (H: f == g):
                forall x, rename f x = rename g x.

Proof. intros V W f g H x.
       generalize dependent W.
       induction x; intros; simpl; try rewrite H;
       repeat rewrite (IHx1 f g);
       repeat rewrite (IHx2 f g); auto.
       rewrite (IHx2 W f g); auto.
       rewrite (IHx1 W f g); auto.
       rewrite (IHx2 _ (lift f) (lift g)); 
       try apply lift_eq; auto.
       rewrite (IHx1 _ f g). auto.
       auto.
       simpl.
       rewrite (IHx2 _ (lift f) (lift g)); auto.
       rewrite (IHx1 _ f g); auto.
       apply lift_eq. auto.
Qed.

Hint Resolve rename_eq: pts.
       
Lemma rename_id (V: Type)(x: term V) (f: V -> V) (H: forall x, f x = x) :
              rename f x = x.
Proof. induction x; simpl; intros; 
       repeat rewrite H; 
       repeat rewrite IHx1;
       repeat rewrite IHx2; auto with pts.
Qed.


Lemma rename_comp (V:Type)(x: term V)(W X: Type)(f:V -> W) (g: W -> X):
             rename (fun x => g (f x)) x = rename g (rename f x).
Proof. induction x; intros; simpl; auto.
       rewrite IHx1; apply f_equal;
       rewrite IHx2; auto.
       
       rewrite IHx1. apply f_equal.
       rewrite <- (IHx2 _ _  (lift f) (lift g)).
       apply rename_eq. simpl.
  
       intro x; destruct x; auto.
       
       rewrite IHx1. apply f_equal.
       rewrite <- (IHx2 _ _  (lift f) (lift g)).
       apply rename_eq. simpl.
     
       intro x; destruct x; auto.
Qed.
       
    

Program Definition RENAME: Functor TYPE TYPE := Build_Functor
  (Fobj := fun V => term V) (Fmor := fun V W f => rename f) _. 

  Next Obligation.
    Proof. constructor.
    
           unfold Proper. red. 
          
           intros a b f g H x.
           apply rename_eq.
           simpl. apply H.
           
           intro a; simpl.
           intro x; apply rename_id.
           auto.
           
           intros a b c f g; simpl.

           intro x.
           apply rename_comp.
    Qed.

Definition term_inj (V:Type) (t:term V) : term (option V) :=
          rename (@Some V) t.
(*
Fixpoint term_inj (V:Type)(t:term V) : term (option V) :=
        match t with
        | var v => var (Some v)
        | srt s => srt _ s
        | app u v => app (term_inj u) (term_inj v)
        | pi u v => pi (term_inj u) (term_inj v)
        | lda u v => lda (term_inj u) (term_inj v)
        end.
*)

Definition shift (V W: Type)(f: V -> term W)(v:option V): 
                term (option W) :=
          match v with 
          | None => var None
          | Some v => term_inj (f v)
          end.

Lemma shift_eq (V: Type)(x:option V) (W: Type) (f g: V -> term W)
               (H: forall x, f x = g x): shift f x = shift g x.
Proof. induction x; simpl; intros;  try rewrite H; auto. Qed.

Lemma shift_var (V:Type)(x:option V):
         shift (fun v : V => var v) x = var x.
Proof. induction x; intros; simpl; auto. Qed.


Lemma var_lift_shift_eq (V:Type)(x: option V) (W:Type)(f:V -> W):
       var (lift f x) = shift (fun x0 : V => var (f x0)) x.
Proof. induction x; simpl; intros; auto. Qed.


Lemma shift_lift (V:Type)(x:option V)(W:Type)(f:V -> W)
                 (X:Type) (g: W -> term X):
 shift g (lift f x) = shift (fun x0 : V => g (f x0)) x.
Proof. induction x; simpl; intros; auto. Qed.



Fixpoint subst (V W: Type)(x: term V)(f:V -> term W) : term W :=
      match x with
      | var v => f v
      | srt _ s => srt W s
      | app u v => app (subst u f) (subst v f)
      | pi u v => pi (subst u f) (subst v (shift f))
      | lda u v => lda (subst u f) (subst v (shift f))
      end.

Lemma subst_eq (V: Type)(x:term V) (W: Type)(f g: V -> term W)
         (H: forall x, f x = g x): subst x f = subst x g.
Proof. induction x; simpl; intros; auto.
       
       rewrite (IHx1 W f g); auto.
       rewrite (IHx2 W f g); auto.
       
       rewrite (IHx1 W f g); auto.
       rewrite (IHx2 _ (shift f) (shift g)); auto.
       intro x; apply shift_eq; auto.
       
       rewrite (IHx1 W f g); auto.
       rewrite (IHx2 _ (shift f) (shift g)); auto.
       intro x; apply shift_eq; auto.
Qed.



(*
Definition term_kl (V W:Type) (f: V -> term W) :=
          fun x => subst x f.

Definition mu (V: Type) (x: term (term V)) :=
        subst x (fun x => x).

Definition eta (V:Type)(v:V): term V := var v.
*)
Lemma subst_var (V:Type)(x: term V): 
       subst x (fun v => var v) = x.
Proof. induction x; intros; simpl; auto.
       
       rewrite IHx1. rewrite IHx2; auto.
       
       rewrite IHx1. rewrite <- IHx2 at 2.
       apply f_equal. apply subst_eq.
       apply shift_var.
       
       rewrite IHx1. rewrite <- IHx2 at 2.
       apply f_equal. apply subst_eq.
       apply shift_var.
Qed.

Lemma subst_eq_rename (V:Type)(x:term V)(W:Type) (f:V -> W):
        rename f x = subst x (fun x => var (f x)).
Proof. induction x; simpl; intros; auto.
 
       rewrite IHx1; rewrite IHx2; auto.
       
       rewrite IHx1; apply f_equal.
       rewrite IHx2; apply subst_eq.
       intro x. apply var_lift_shift_eq.
       
       rewrite IHx1; apply f_equal.
       rewrite IHx2; apply subst_eq.
       intro x. apply var_lift_shift_eq.
Qed.

Lemma rename_term_inj (V: Type)(x: term V)(W:Type)(g: V -> W):
       rename (lift g) (term_inj x) = term_inj (rename g x).
Proof. induction x; simpl; intros; auto.
       rewrite IHx1. rewrite IHx2. auto.
       rewrite IHx1. unfold term_inj in *|-*.  simpl.
       apply f_equal. auto. repeat rewrite <- rename_comp.
       apply rename_eq. simpl. 
       intro x; simpl. 
       induction x; intros; simpl; auto. 
       rewrite IHx1. unfold term_inj in *|-*.  simpl.
       apply f_equal. auto. repeat rewrite <- rename_comp.
       apply rename_eq. simpl.
       intro x; simpl. 
       induction x; intros; simpl; auto.
Qed. 
       

Lemma rename_subst (V:Type)(x:term V)(W:Type)(f:V -> term W)(X:Type)
                   (g: W -> X):
    rename g (subst x f) = subst x (fun x => rename g (f x)).
Proof. induction x; simpl; intros; auto.
       rewrite IHx1. rewrite IHx2. auto.
       
       rewrite IHx1. rewrite IHx2. 
       apply f_equal. apply subst_eq. 
       induction x; simpl; auto.
       apply rename_term_inj.
       
       rewrite IHx1. rewrite IHx2. 
       apply f_equal. apply subst_eq. 
       induction x; simpl; auto.
       apply rename_term_inj.
Qed.




Lemma subst_rename (V:Type)(x: term V)(W:Type)(f: V -> W)
                   (X: Type) (g: W -> term X):
    subst (rename f x) g = subst x (fun x => g (f x)).
Proof. induction x; simpl; intros; auto.
       rewrite IHx1. rewrite IHx2. auto.
       
       rewrite IHx1. rewrite IHx2.
       apply f_equal; apply subst_eq.
       intro x. apply shift_lift.
       rewrite IHx1. rewrite IHx2.
       apply f_equal; apply subst_eq.
       intro x. apply shift_lift.
Qed.

Lemma subst_term_inj (V:Type)(x:term V)(W:Type)(g:V -> term W):
      subst (term_inj x) (shift g) = term_inj (subst x g).
Proof. induction x; simpl; intros; auto.

       rewrite IHx1. rewrite IHx2. auto.
       
       rewrite IHx1. unfold term_inj in *|-*; simpl.
       apply f_equal.
       rewrite rename_subst.
       rewrite subst_rename.
       apply subst_eq.
       induction x; simpl; auto.
       rewrite rename_term_inj. auto.
       
       rewrite IHx1. unfold term_inj in *|-*; simpl.
       apply f_equal.
       rewrite rename_subst.
       rewrite subst_rename.
       apply subst_eq.
       induction x; simpl; auto.
       rewrite rename_term_inj. auto.
Qed.
      
Lemma subst_shift_shift (V:Type)(x:option V)(W: Type) (f: V -> term W)
                        (X: Type) (g: W -> term X):
subst (shift f x) (shift g) = shift (fun x0 : V => subst (f x0) g) x.
Proof. induction x; simpl; intros; auto. apply subst_term_inj.
Qed.


Lemma subst_subst (V:Type)(x:term V)(W X: Type)
                  (f:V -> term W) (g: W -> term X):
subst (subst x f) g = subst x (fun x0 : V => subst (f x0) g).
Proof. induction x; simpl; intros; auto.
       
       rewrite IHx1. rewrite IHx2. auto.
       
       rewrite IHx1. apply f_equal.
       rewrite (IHx2).
       apply subst_eq. intro; simpl.
       apply subst_shift_shift.
       
       rewrite IHx1. apply f_equal.
       rewrite (IHx2).
       apply subst_eq. intro; simpl.
       apply subst_shift_shift.
Qed.


Obligation Tactic := simpl; intros;
                   try apply subst_var;
                   try apply subst_subst;
                   auto.

Program Instance syntax_monad_h: Monad_struct (fun V => term V) := {
  weta V v:= var v;
  kleisli V W f := fun x => subst x f
}.
Next Obligation.
Proof. 
  unfold Proper. 
  red.
  intros f g H x. 
  apply subst_eq.
  auto.
Qed.


Definition simp_subst (V:Type)(x:term (option V))(N:term V) :=
     subst x (fun x => match x with None => N | Some v => var v end).

(** parallel beta *)

Inductive par_red1 (V:Type) : term V -> term V -> Prop :=
| par_red1_var: forall v, par_red1 (var v) (var v)
| par_red1_srt: forall s, par_red1 (srt _ s) (srt _ s)
| par_red1_app: forall m m' n n', par_red1 m m' -> par_red1 n n' ->
                                  par_red1 (app m n) (app m' n')
| par_red1_pi: forall m m' (n n':term (option V)), par_red1 m m' -> 
                         par_red1 (V:= option V) n n' ->
                                 par_red1 (pi m n) (pi m' n')
| par_red1_lda: forall m m' n n', par_red1 m m' -> par_red1 (V:= option V) n n' ->
                                 par_red1 (lda m n) (lda m' n')
| par_red1_beta: forall m m' a n n', 
         par_red1 (V:= option V) m m' -> par_red1 n n' ->
         par_red1 (app (lda a m) n) (simp_subst m' n').

Notation "x |> y" := (par_red1 x y) (at level 80).

Lemma par_red1_refl (V:Type)(x:term V):  x |> x.
Proof.  induction x; intros; try constructor; auto. Qed.
(*
Lemma par_red1_lda_injr : forall (n : Type) (A A' : term n) 
      (M M' : term (option n)),
  lda A M |> lda A' M' -> M |> M'.
Proof. 
*)

End pts.









