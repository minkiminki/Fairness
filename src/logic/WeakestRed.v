From Fairness Require Export LinkingRed.

Ltac lred2 := (prw ltac:(red_tac itree_class) 1 2 0).
Ltac rred2 := (prw ltac:(red_tac itree_class) 1 1 0).
