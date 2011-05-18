Require Export CatSem.PCF_order_comp.RPCF_rep_hom.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Transparent Obligations.
Unset Automatic Introduction.

Section id_rep.

Variable P : PCFPO_rep.

Definition id_rep_car c:
(forall t : type_type P,
  (retype_ipo (fun u : type_type P => u) (P c)) t ->
  (P (retype (fun u : type_type P => u) c)) t) :=
fun  t y => 
   match y with ctype _ z => 
     rlift P (@id_retype _ c) _ z end.

Obligation Tactic := 
  intros; do 2 red;
  simpl; intros;
  try match goal with [H: retype_ord _ _ |- _ ] => induction H end;
  try apply IPO_mor_monotone; auto.

Program Instance id_rep_pos c:
ipo_mor_struct (a:=retype_ipo (fun u : type_type P => u) (P c))
  (b:=P (retype (fun u : type_type P => u) c)) (@id_rep_car c).

Definition id_rep_po c := Build_ipo_mor (id_rep_pos c).

Definition id_rep_c :
(forall c : ITYPE (type_type P),
  (RETYPE_PO (fun u : type_type P => u)) (P c) --->
  P ((RETYPE (fun u : type_type P => u)) c)) :=
      id_rep_po.

Ltac elim_retype := match goal with
    [y : retype _ _ _ |- _ ] => destruct y end.

Obligation Tactic := cat; repeat elim_retype;
  cat; 
  try rew (rlift_rweta P);
  try rew (rlift_rkleisli (M:=P));
  try rew (rkleisli_rlift (M:=P));
  try apply (rkl_eq P); cat.

Program Instance RMon_id_s :
  gen_RMonad_Hom_struct (P:=P) (Q:=P) 
   (G1:=RETYPE (fun u : type_type P => u))
   (G2:=RETYPE_PO (fun u : type_type P => u))
   (NNNT1 (fun u : type_type P => u)) id_rep_c.

Definition RMon_id := Build_gen_RMonad_Hom RMon_id_s.

Obligation Tactic := simpl; intros; unfold rlift;
  match goal with [|- _ = (_ _ _ ((rmodule_hom ?H) _ )) _ ] => 
  rerew  (rmod_hom_rmkl H) end;
  try apply f_equal; try rew (rklkl P); try apply (rkl_eq P);
  simpl; intros; try rew (retakl P); elim_opt;
  try rew (rlift_rweta P); auto.

Program Instance PCFPO_id_struct : PCFPO_rep_Hom_struct 
   (P:=P) (R:=P) 
   (f:=fun u => u) (fun u => eq_refl) RMon_id.

Definition PCFPO_id := Build_PCFPO_rep_Hom PCFPO_id_struct.

End id_rep.



