Require Export CatSem.STS.STS_initial.
Require Export CatSem.TLC.TLC_types.
Require Export CatSem.PCF.PCF_types.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Section example_signatures.

(** two examples of signatures : 
    - simply typed lambda calculus 
    - a fragment of PCF (just to make it shorter)
*)
Notation "'T'" := TLCtypes.
Notation "s ~> t" := (TLCarrow s t)(at level 40).
Notation "[ S ]" := (list S) (at level 5).

Inductive TLC_index : T -> Type := 
   | TLC_abs : forall s t : T, TLC_index (s ~> t)
   | TLC_app : forall s t : T, TLC_index t.

Definition TLC_arguments : forall t, TLC_index t -> [[T] * T] :=
    fun t r => match r with 
      | TLC_abs u v => (u::nil,v)::nil
      | TLC_app u v => (nil,u ~> v)::(nil,u)::nil
      end.

Definition TLC_sig t := Build_Signature_t t 
      (@TLC_arguments t).

(*
Definition TLC_sig t := Build_Signature_t t
  (fun r : TLC_index t => match r with
      | TLC_abs s t => (s::nil,t)::nil
      | TLC_app s t => (nil,s ~> t)::(nil,s)::nil
      end).
*)

Notation "'Bool'" := PCF.Bool.
Notation "'Nat'" := PCF.Nat.
Notation "'T'" := PCF.types.
Notation "a ~> b" := (PCF.arrow a b)(at level 40).

Inductive PCF_index_t : T -> Type :=
  | PCF_abs : forall s t : T, PCF_index_t (s ~> t)
  | PCF_app : forall s t : T, PCF_index_t t
  | PCF_rec : forall t : T, PCF_index_t t
  | PCF_true : PCF_index_t Bool
  | PCF_false : PCF_index_t Bool
  | PCF_nat : forall n : nat, PCF_index_t Nat
  | PCF_succ : PCF_index_t (Nat ~> Nat)
  | PCF_zero : PCF_index_t (Nat ~> Bool)
  | PCF_condN : PCF_index_t (Bool ~> Nat ~> Nat ~> Nat)
  | PCF_condB : PCF_index_t (Bool ~> Bool ~> Bool ~> Bool)
  | PCF_bottom : forall t : T, PCF_index_t t.

Definition PCF_sig t := Build_Signature_t t
      (fun r : PCF_index_t t => match r in PCF_index_t t with
            | PCF_abs s t => (s::nil,t)::nil
            | PCF_app s t => (nil, s ~> t)::(nil,s)::nil
            | PCF_rec t => (nil, t ~> t)::nil
            | _ => nil
            end).

End example_signatures.


(** we are interested in TLC *)

(** short name for its types *)
Definition T := TLCtypes.

Notation "a ~> b" := (TLCarrow a b) (at level 60).


(** the category of reps of TLC_sig *)
Definition TLCreps : Cat := REPRESENTATION TLC_sig.

(** initiality of TLCreps *)
Definition TLCInitial : Representation TLC_sig := 
     Init (Initial := STS_initial TLC_sig).

(** we isolate the monad *)
Definition TLC : Monad (ITYPE T) := rep_monad TLCInitial.

(** we want to have a short name for its simultaneous substitution *)
Definition bind V W (f : V ---> TLC W) t x
             := kleisli f t x.

(** and the substitution of a single variable, for beta *)
Definition TLCsubstar r s V (M : TLC (opt r V) s) 
         (N : TLC V r) : TLC V s := 
      substar (S:=TLC_sig) N M.

(** and a nice notation *)
Notation "x >>= f" := (bind f x) (at level 60).
Notation "M [*:= N ]" := (TLCsubstar M N) (at level 40).

Definition app r s V (M : TLC V (r ~> s)) (N : TLC V r) : TLC V s :=
   Build (S:=TLC_sig) (i:=TLC_app r s) 
         (constr (b:=(nil,r~>s))(S:=TLC_sig) M 
                     (constr (b:=(nil,r)) N (TT (T:=T) TLC_sig V))).

Definition abs r s V (M : TLC (opt r V) s) : TLC V (r ~> s) := 
  Build (S:=TLC_sig) (t:=r ~> s) (i:=TLC_abs r s)
    (constr (b:=(r :: nil, s)) M (TT (T:=T) TLC_sig V)).

Notation "M @ N" := (app M N) (at level 30).
Notation "'\*' M" := (abs M) (at level 32).

Reserved Notation "x >> y" (at level 50).

Inductive beta : forall V t, relation (TLC V t) :=
| app_abs : forall V r s (M : TLC (opt r V) s) N, 
       (\* M) @ N >> M [*:= N]
| beta_app1 : forall V r s (M M' : TLC V (r ~> s)) N,
         M >> M' -> M @ N >> M' @ N
| beta_app2 : forall V r s (M : TLC V (r ~> s)) N N',
         N >> N' -> M @ N >> M @ N'
| beta_abs : forall V r s (M M': TLC (opt r V) s),
         M >> M' -> \* M >> \* M'

where "x >> y" := (beta x y).


(** we could now start to define reduction relations etc. *)

