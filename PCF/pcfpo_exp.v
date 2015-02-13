Require Export pcfpo_mod monad_h_module.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Automatic Introduction.

(** a PCF exponential monad is a monad together with, 
     for each u, an isomorphism of modules 
    [M -> M*u]
*)

(* TODO: replace M in PCF_abs and PCF_app1 by (M_u), the u-Module of M *)

Class PCFMonad_struct (M : Monad (IPO PCF.TY)) := {
  PCF_abs : forall (u:PCF.TY), 
         Module_Hom (IPO_Der_Mod M u) M;
  PCF_app1 : forall (u:PCF.TY), 
         Module_Hom M (IPO_Der_Mod M u);
  PCF_eta : forall u c, 
         PCF_abs u c ;; PCF_app1 u c == id _ ;
  PCF_beta: forall u c, 
         PCF_app1 u c ;; PCF_abs u c == id _ 
}.

Record PCFMonad := {
  pcfmonad :> Monad (IPO PCF.TY);
  pcfmonad_struct :> PCFMonad_struct pcfmonad
}.

Existing Instance pcfmonad_struct.

(** a morphism of PCF exp monads is a monad morphism which is compat with
   	- app1
	- abs
*)

Section PCFMonad_Hom.

Variables P Q: PCFMonad.

Class PCFMonad_Hom_struct (h: Monad_Hom P Q):= {
  expmonad_hom_abs: forall u c, 
            PCF_abs u _ ;; h _ == h _ ;; PCF_abs u c;
  expmonad_hom_app: forall u c, PCF_app1 u _ ;; h _  ==
                                h c ;; PCF_app1 u _ 
}.

Record PCFMonad_Hom := {
  pcfmonad_hom :> Monad_Hom P Q;
  pcfmonad_hom_struct :> PCFMonad_Hom_struct pcfmonad_hom
}.

End PCFMonad_Hom.

Existing Instance pcfmonad_hom_struct.



