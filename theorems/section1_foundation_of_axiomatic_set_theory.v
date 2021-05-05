Section Section1_foundation_of_axiomatic_set_theory.
  (* P3 「変数」 *)
  Inductive variable := v : nat -> variable.

  (* P3 「式」 *)
  Inductive formula :=
  | formula_eq : variable -> variable -> formula
  | formula_in : variable -> variable -> formula
  | formula_and : formula -> formula -> formula
  | formula_not : formula -> formula
  | formula_ex : variable -> formula -> formula.

  (* P4 略記法 *)
  Definition formula_all (v: variable) (p: formula) : formula :=
    formula_not (formula_ex v (formula_not p)).

  Definition formula_or (p q: formula) : formula :=
    formula_not (formula_and (formula_not p) (formula_not q)).

  Definition formula_naraba (p q: formula) : formula :=
    formula_or (formula_not p) q.

  Definition formula_iff (p q: formula) : formula :=
    formula_and (formula_naraba p q) (formula_naraba q p).

  Definition formula_neq (v1 v2: variable) : formula :=
    formula_not (formula_eq v1 v2).

  Definition formula_notin (v1 v2: variable) : formula :=
    formula_not (formula_in v1 v2).

End Section1_foundation_of_axiomatic_set_theory.
