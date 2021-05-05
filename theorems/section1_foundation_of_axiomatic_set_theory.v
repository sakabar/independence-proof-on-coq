Require Import Ensembles.

Section Section1_foundation_of_axiomatic_set_theory.
  (* P3 変数 *)
  Inductive variable := var : nat -> variable.

  (* P3 式 *)
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

  (* P5 束縛と自由 *)
  Fixpoint free_variables (p: formula) : Ensemble(variable) :=
    match p with
      | formula_eq v1 v2 => Union variable (Singleton variable v1) (Singleton variable v2)
    | formula_in v1 v2 => Union variable (Singleton variable v1) (Singleton variable v2)
    | formula_and p q => Union variable (free_variables p) (free_variables q)
    | formula_not p => (free_variables p)
    | formula_ex v p => Setminus variable (free_variables p) (Singleton variable v)
    end.

  (* P6 「文」*)
  Inductive sentence : Type :=
  | sentence_intro : forall (p : formula), Same_set variable (Empty_set variable) (free_variables p) -> sentence.

  Definition p1 : formula := formula_ex (var 1) (formula_ex (var 2) (formula_eq (var 1) (var 2))).

  Theorem p1_has_no_free_vars : Same_set variable (Empty_set variable) (free_variables p1).
  Proof.
    simpl.
    unfold Same_set.
    apply conj.

    unfold Included.
    intros x H1.
    inversion H1.

    unfold Included.
    intros x H1.
    unfold In.
    unfold In in H1.
    unfold Setminus in H1.
    unfold In in H1.
    destruct H1 as [H2 H3].
    destruct H2 as [H4 H5].
    destruct H4.
    inversion H as [H6].
    unfold In in H.
    contradiction.

    unfold In in H.
    contradiction.
  Qed.

  (* sentence型の変数を定義するためには、そのformulaに自由変数が含まれていないという証明を付ける必要がある *)
  Definition s1 : sentence := sentence_intro p1 p1_has_no_free_vars.
  (* Check s1. *)
  (* s1 : sentence *)

  (* sentence同士を手軽にandしたい。モナド? *)
  (* この定義で、sentence_intro (formula_and p1 q1)*)
  (* この足りないPropを埋めて証明モードに移行したい。どうやったらいい? *)
  Program Definition sentence_and (p q : sentence) : sentence :=
    match p with
      | sentence_intro p' P => match q with
                                 | sentence_intro q' Q => sentence_intro (formula_and p' q') _
                               end
    end.
  Next Obligation.
    intros.
    clear Heq_p Heq_q.
    apply Extensionality_Ensembles in P.
    apply Extensionality_Ensembles in Q.
    unfold Same_set.
    apply conj.

    unfold Included.
    intros.
    inversion H.

    unfold Included.
    intros.
    inversion H.
    rewrite P.
    exact H0.

    rewrite Q.
    exact H0.
  Defined.

  (* Inductive proovable : Ensemble sentence -> sentence -> Prop := *)
  (*   proovable_and: forall (s : Ensemble sentence) (p q : sentence), (In sentence s p) /\ (In sentence s q) -> proovable s (formula_and p q). *)




End Section1_foundation_of_axiomatic_set_theory.
