(*
        #####################################################
        ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
        #####################################################
*)
(*
    You are only allowed to use these tactics:

    simpl, reflexivity, intros, rewrite, destruct, induction, apply, assert

    You are not allowed to use theorems outside this file *unless*
    explicitly recommended.
*)

(* ---------------------------------------------------------------------------*)




(**

Show that 5 equals 5.

 *)
Theorem ex1: 5 = 5.
Proof.
  reflexivity.
  Qed.

(**

Show that equality for natural numbers is reflexive.

 *)
Theorem ex2: forall (x:nat), x = x.
Proof.
  intros n.
  reflexivity.
  Qed.

(**

Show that [1 + n] equals the successor of [n].

 *)
Theorem ex3: forall n, 1 + n = S n.
Proof.
  intros n.
  simpl.
  reflexivity.
  Qed.

(**

Show that if [x = y], then [y = x].

 *)
Theorem ex4: forall x (y:nat), x = y -> y = x.
Proof.
  intros x y.
  intros x_y_eq.
  rewrite -> x_y_eq.
  reflexivity.
  Qed.

(**

Show that if the result of the conjunction and the disjunction equal,
then both boolean values are equal.


 *)
Theorem ex5: forall (b c : bool), (andb b c = orb b c) -> b = c.
Proof.
  intros b c. 
  destruct b.
  - simpl.
    intros c_eq.
    rewrite -> c_eq.
    reflexivity.
  - simpl.
    intros c_eq.
    rewrite -> c_eq.
    reflexivity.
  Qed.

(**

In an addition, we can move the successor of the left-hand side to
the outer most.


 *)
Theorem ex6: forall n m, n + S m = S (n + m).
Proof.
  intros n m.
  induction n.
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> IHn.
    reflexivity.
  Qed.

(**

If two additions are equal, and the numbers to the left of each addition
are equal, then the numbers to the right of each addition must be equal.
To complete this exercise you will need to use the auxiliary
theorem: eq_add_S


 *)

Print eq_add_S.
Theorem ex7: forall x y n, n + x = n + y -> x = y.
Proof.
  intros x y n.
  induction n as [ | n' IH].
  - simpl.
    intros x_y_eq.
    rewrite -> x_y_eq.
    reflexivity.
  - simpl.
    intros x_y_eq.
    apply eq_add_S.
    rewrite <- IH.
    reflexivity.
    apply eq_add_S.
    apply x_y_eq.
  Qed.

(**

Show that addition is commutative.
Hint: You might need to prove `x + 0 = x` and `S (y + x) = y + S x`
separately.


 *)

(*Theorem plus_n_0 copied from Lecture 3*)
Theorem plus_n_O : forall n:nat,
  n = n + 0.
Proof.
  intros n.
  simpl.
  induction n as [ | n' IH].
  - simpl.
    reflexivity.
  - simpl.
    rewrite <- IH.
    reflexivity.
Qed.

(* Theorem plus_n_m created by myself*)
Theorem plus_n_m : forall n m : nat, 
  S (n + m) = n + S m.
Proof.
  intros.
  induction n. 
  - simpl.
    reflexivity.
  - simpl.
    rewrite <- IHn.
    reflexivity.
  Qed.
  
Theorem ex8: forall (x y : nat), x + y = y + x.
Proof.
  intros.
  induction y.
  - simpl.
    rewrite <- plus_n_O.
    reflexivity.
  - simpl.
    rewrite <- plus_n_m.
    rewrite <- IHy.
    reflexivity.
  Qed.

(**

If two additions are equal, and the numbers to the right of each addition
are equal, then the numbers to the left of each addition must be equal.

Hint: Do not try to prove this theorem directly. You should be using
auxiliary results. You can use Admitted theorems.

 *)

Lemma plus_0: forall m n, m = n -> 0 + m = 0 + n.
Proof.
  intros m n.
  intros eq_m_n.
  apply eq_m_n.
Qed.

Theorem ex9: forall x y n, x + n = y + n -> x = y.
Proof.
  intros x y n.
  intros x_y_n_eq.
  rewrite -> (ex7 x y n).
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> ex8.
    rewrite -> x_y_n_eq.
    apply ex8.
Qed.



