Require Export Coq.Logic.Eqdep.

Ltac rewr H := rewrite (inj_pair2 _ _ _ _ _ H).
Ltac rerewr H := rewrite <- (inj_pair2 _ _ _ _ _ H).