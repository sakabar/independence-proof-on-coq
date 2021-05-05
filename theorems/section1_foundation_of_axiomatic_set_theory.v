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

End Section1_foundation_of_axiomatic_set_theory.
