(*
        #####################################################
        ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
        #####################################################
*)
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope char_scope.
Require Import Hw5Util.

(* ---------------------------------------------------------------------------*)




(**

Use `yield_def`.

 *)
Theorem yield_eq:
  forall G A w, List.In (A, w) (Hw5Util.grammar_rules G) -> Hw5Util.Yield G [A] w.
Proof.
  simpl.
  intros N.
  intros O.
  intros P.
  intros Q.
  apply yield_def with (u := []) (v := []) (w := P) (A := O).
  - simpl.
    apply Q.
  - simpl.
    reflexivity.
  - simpl.
    rewrite -> app_nil_r.
    reflexivity.
Qed.

(**

Use `yield_def` and `app_assoc` to correct the parenthesis.

 *)
Theorem yield_right:
  forall G w1 w2 r w3 w4, Hw5Util.Yield G w1 w2 -> w3 = w1 ++ r -> w4 = w2 ++ r -> Hw5Util.Yield G w3 w4.
Proof.
  simpl.
  intros N.
  intros O.
  intros P.
  intros Q.
  intros R.
  intros S.
  intros T.
  intros U.
  intros V.
  rewrite -> U.
  rewrite -> V.
  inversion T.
  rewrite -> H0.
  rewrite -> H1.
  rewrite <- app_assoc.
  rewrite <- app_assoc.
  rewrite <- app_assoc.
  rewrite <- app_assoc.
  apply yield_def with (u := u) (v := v ++ Q) (w := w) (A := A).
  - simpl.
    apply H.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.

(**

Similar proof than `yield_right`, but you should rewrite with
`app_assoc` after using `yield_def`, not before.


 *)

Theorem yield_left:
  forall G w1 w2 l w3 w4, Hw5Util.Yield G w1 w2 -> w3 = l ++ w1 -> w4 = l ++ w2 -> Hw5Util.Yield G w3 w4.
Proof.
  simpl.
  intros N.
  intros O.
  intros P.
  intros Q.
  intros R.
  intros S.
  intros T.
  intros U.
  intros V.
  rewrite -> U.
  rewrite -> V.
  inversion T.
  rewrite -> H0.
  rewrite -> H1.
  apply yield_def with (u := Q ++ u) (v := v) (w := w) (A := A).
  - simpl.
    apply H.
  - simpl.
    rewrite -> app_assoc.
    reflexivity.
  - simpl.
    rewrite -> app_assoc.
    reflexivity.
Qed.

(**

Consider using one of the lemmas you have just proved.
When your goal is `In ("C", ...) (grammar_rules g1)`, `simpl; auto`
should solve it.


 *)
Theorem g1_rule_1:
  Hw5Util.Yield g1 ["C"] ["{"; "C"; "}"].
Proof.
  simpl.
  apply yield_def with (u := []) (v := []) (w := ["{"; "C"; "}"]) (A := "C").
  - simpl.
    apply or_introl.
    apply @eq_refl.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.

(**

Consider using one of the lemmas you have just proved.
When your goal is `In ("C", ...) (grammar_rules g1)`, `simpl; auto`
should solve it.


 *)
Theorem g1_rule_2:
  Hw5Util.Yield g1 ["C"] ["C"; "C"].
Proof.
  simpl.
  apply yield_def with (u := []) (v := []) (w := ["C"; "C"]) (A := "C").
  - simpl.
    apply or_intror.
    apply or_introl.
    apply @eq_refl.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.

(**

Consider using one of the lemmas you have just proved.
When your goal is `In ("C", ...) (grammar_rules g1)`, `simpl; auto`
should solve it.


 *)
Theorem g1_rule_3:
  Hw5Util.Yield g1 ["C"] [].
Proof.
  simpl.
  apply yield_def with (u := []) (v := []) (w := []) (A := "C").
  - simpl.
    apply or_intror.
    apply or_intror.
    apply or_introl.
    apply @eq_refl.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.

(**

The proof should proceed by inversion and then case analysis on
string `u`.


 *)
Theorem yield_inv_start:
  forall G w, Hw5Util.Yield G [Hw5Util.grammar_start G] w -> In (Hw5Util.grammar_start G, w) (Hw5Util.grammar_rules G).
Proof.
  simpl.
  intros N.
  intros O.
  intros P.
  inversion P.
  induction u.
  - simpl.
    rewrite -> H1.
    simpl.
    simpl in H0.
    inversion H0.
    subst.
    rewrite -> app_nil_r.
    apply H.
  - simpl.
    induction u.
    + simpl.
      inversion H0.
    + simpl.
      inversion H0.
Qed.

(**

You will want to use `yield_inv_start`. Recall that that `List.In`
simplifies to a series of disjunctions.


 *)
Theorem g1_ex1:
  ~ Hw5Util.Yield g1 ["C"] ["{"].
Proof.
  simpl.
  unfold not.
  intros N.
  apply yield_inv_start in N.
  destruct N.
  - simpl.
    inversion H.
  - simpl.
    unfold In in H.
    inversion H.
    + simpl.
      inversion H0.
    + simpl.
      inversion H0.
      * simpl.
        inversion H1.
      * simpl.
        inversion H1.
Qed.

(**

The idea is to use either: `yield_left`, `yield_right`, or `yield_def`.


 *)
Theorem g1_step_1:
  Hw5Util.Yield g1 ["C"; "C"] ["{"; "C"; "}"; "C"].
Proof.
  simpl.
  apply yield_def with (u := []) (v := ["C"]) (w := ["{"; "C"; "}"]) (A := "C").
(*  apply yield_right with (w1 := ["C"]) (w2 := ["{"; "C"; "}"]) (r := ["C"]).
  apply yield_left with (w1 := ["C"; "C"]) (w2 := ["{"; "C"; "}"; "C"]) (l := []). *)
  - simpl.
(*    apply yield_left with (w1 := ["C"; "C"]) (w2 := ["{"; "C"; "}"; "C"]) (l := []). *)
    apply or_introl.
    apply @eq_refl.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.

Theorem g1_steap_1: Hw5Util.Yield g1 ["C"; "C"] ["{"; "C"; "}"; "C"].
Proof.
  apply yield_def with (u:=[]) (v:=["C"]) (w:=["{";"C";"}"]) (A:="C").
  - simpl; auto.
  - reflexivity.
  - simpl. reflexivity.
Qed.

(**

The idea is to use either: `yield_left`, `yield_right`, or `yield_def`.


 *)
Theorem g1_step_2:
  Hw5Util.Yield g1 ["{"; "C"; "}"; "C"] ["{"; "}"; "C"].
Proof.
  simpl.
(*  apply yield_right with (w1 := ["{"; "C"]) (w2 := ["{"]) (r := ["}"; "C"]).
  apply yield_left with (w1 := ["C"; "}"; "C"]) (w2 := ["}"; "C"]) (l := ["{"]).  *)
  apply yield_def with (u := ["{"]) (v := ["}"; "C"]) (w := []) (A := "C").
  - simpl.
    apply or_intror.
    apply or_intror.
    apply or_introl.
    apply @eq_refl.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.

(**

The idea is to use either: `yield_left`, `yield_right`, or `yield_def`.


 *)
Theorem g1_step_3:
  Hw5Util.Yield g1 ["{"; "}"; "C"] ["{"; "}"; "{"; "C"; "}"].
Proof.
  simpl.
  apply yield_def with (u := ["{"; "}"]) (v := []) (w := ["{"; "C"; "}"]) (A := "C").
  - simpl.
    apply or_introl.
    apply @eq_refl.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.

(**

The idea is to use either: `yield_left`, `yield_right`, or `yield_def`.


 *)
Theorem g1_step_4:
  Hw5Util.Yield g1 ["{"; "}"; "{"; "C"; "}"] ["{"; "}"; "{"; "}"].
Proof.
  - simpl.
(*    apply yield_def with (u := ["{"; "}"]) (v := ["}"]) (w := ["{"]) (A := "{"; "C").
    apply yield_right with (w1 := ["{"; "}"; "{"; "C"]) (w2 := ["{"; "}"; "{"]) (r := ["}"]). *)
    apply yield_left with (w1 := ["{"; "C"; "}"]) (w2 := ["{"; "}"]) (l := ["{"; "}"]).
    + simpl.
      apply yield_def with (u := ["{"]) (v := ["}"]) (w := []) (A := "C").
      * simpl.
        apply or_intror.
        apply or_intror.
        apply or_introl.
        apply @eq_refl.
      * simpl.
        reflexivity.
      * simpl.
        reflexivity.
    + simpl.
      reflexivity.
    + simpl.
      reflexivity.
Qed.

(**

Use either `derivation_nil` or `derivation_cons`.

 *)
Theorem g1_der_1:
  Hw5Util.Derivation g1 [["C"]].
Proof.
  simpl.
  apply derivation_nil.
Qed.

(**

Use either `derivation_nil` or `derivation_cons`.

 *)
Theorem g1_der_2:
  Hw5Util.Derivation g1 [["C"; "C"]; ["C"]].
Proof.
  simpl.
  apply derivation_cons.
  - simpl.
    apply derivation_nil.
  - simpl.
    apply yield_def with (u := []) (v := []) (w := ["C"; "C"]) (A := "C").
    + simpl.
      apply or_intror.
      apply or_introl.
      apply @eq_refl.
    + simpl.
      reflexivity.
    + simpl.
      reflexivity.
Qed.

(**

Use either `derivation_nil` or `derivation_cons`.

 *)
Theorem g1_der_3:
  Hw5Util.Derivation g1 [["{"; "C"; "}"; "C"]; ["C"; "C"]; ["C"]].
Proof.
  simpl.
  apply derivation_cons.
  - simpl.
    apply derivation_cons.
    + simpl.
      apply derivation_nil.
    + simpl.
      apply yield_def with (u := []) (v := []) (w := ["C"; "C"]) (A := "C").
      * simpl.
        apply or_intror.
        apply or_introl.
        apply @eq_refl.
      * simpl.
        reflexivity.
      * simpl.
        reflexivity.
  - simpl.
    apply yield_def with (u := []) (v := ["C"]) (w := ["{"; "C"; "}"]) (A := "C").
    + simpl.
      apply or_introl.
      apply @eq_refl.
    + simpl.
      reflexivity.
    + simpl.
      reflexivity.
Qed.


Theorem g1_der_4:
  Hw5Util.Derivation g1 [
    ["{"; "}"; "C"];
    ["{"; "C"; "}"; "C"];
    ["C"; "C"];
    ["C"]
].
Proof.
  simpl.
  apply derivation_cons.
  - simpl.
    apply derivation_cons.
    + simpl.
      apply derivation_cons.
      * simpl.
        apply derivation_nil.
      * simpl.
        apply yield_def with (u := []) (v := []) (w := ["C"; "C"]) (A := "C").
        -- simpl.
           apply or_intror.
           apply or_introl.
           apply @eq_refl.
        -- simpl.
           reflexivity.
        -- simpl.
           reflexivity.
    + simpl.
      apply yield_def with (u := []) (v := ["C"]) (w := ["{"; "C"; "}"]) (A := "C").
      * simpl.
        apply or_introl.
        apply @eq_refl.
      * simpl.
        reflexivity.
      * simpl.
        reflexivity.
  - simpl.
    apply yield_def with (u := ["{"]) (v := ["}"; "C"]) (w := []) (A := "C").
      + simpl.
      apply or_intror.
      apply or_intror.
      apply or_introl.
      apply @eq_refl.
      + simpl.
        reflexivity.
      + simpl.
        reflexivity.
Qed.


Theorem g1_der_5:
  Hw5Util.Derivation g1 [
    ["{"; "}"; "{"; "C"; "}"];
    ["{"; "}"; "C"];
    ["{"; "C"; "}"; "C"];
    ["C"; "C"];
    ["C"]
].
Proof.
  simpl.
  apply derivation_cons.
  - simpl.
    apply derivation_cons.
    + simpl.
      apply derivation_cons.
      * simpl.
        apply derivation_cons.
        -- simpl.
           apply derivation_nil.
        -- simpl.
           apply yield_def with (u := []) (v := []) (w := ["C"; "C"]) (A := "C").
           ++ simpl.
              apply or_intror.
              apply or_introl.
              apply @eq_refl.
           ++ simpl.
              reflexivity.
           ++ simpl.
              reflexivity.
      * simpl.
        apply yield_def with (u := []) (v := ["C"]) (w := ["{"; "C"; "}"]) (A := "C").
        -- simpl.
           apply or_introl.
           apply @eq_refl.
        -- simpl.
           reflexivity.
        -- simpl.
           reflexivity.
    + simpl.
      apply yield_def with (u := ["{"]) (v := ["}"; "C"]) (w := []) (A := "C").
      * simpl.
        apply or_intror.
        apply or_intror.
        apply or_introl.
        apply @eq_refl.
      * simpl.
        reflexivity.
      * simpl.
        reflexivity.
  - simpl.
    apply yield_def with (u := ["{"; "}"]) (v := []) (w := ["{"; "C"; "}"]) (A := "C").
    + simpl.
      apply or_introl.
      apply @eq_refl.
    + simpl.
      reflexivity.
    + simpl.
      reflexivity.
Qed.


Theorem g1_der_6:
  Hw5Util.Derivation g1 [
    ["{"; "}"; "{"; "}"];
    ["{"; "}"; "{"; "C"; "}"];
    ["{"; "}"; "C"];
    ["{"; "C"; "}"; "C"];
    ["C"; "C"];
    ["C"]
].
Proof.
  simpl.
  apply derivation_cons.
  - simpl.
    apply derivation_cons.
    + simpl.
      apply derivation_cons.
      * simpl.
        apply derivation_cons.
        -- simpl.
           apply derivation_cons.
           ++ simpl.
              apply derivation_nil.
           ++ simpl.
              apply yield_def with (u := []) (v := []) (w := ["C"; "C"]) (A := "C").
              ** simpl.
                 apply or_intror.
                 apply or_introl.
                 apply @eq_refl.
              ** simpl.
                 reflexivity.
              ** simpl.
                 reflexivity.
        -- simpl.
           apply yield_def with (u := []) (v := ["C"]) (w := ["{"; "C"; "}"]) (A := "C").
           ++ simpl.
               apply or_introl.
               apply @eq_refl.
           ++ simpl.
              reflexivity.
           ++ simpl.
              reflexivity.
      * simpl.
        apply yield_def with (u := ["{"]) (v := ["}"; "C"]) (w := []) (A := "C").
        -- simpl.
           apply or_intror.
           apply or_intror.
           apply or_introl.
           apply @eq_refl.
        -- simpl.
           reflexivity.
        -- simpl.
           reflexivity.
    + simpl.
      apply yield_def with (u := ["{"; "}"]) (v := []) (w := ["{"; "C"; "}"]) (A := "C").
      * simpl.
        apply or_introl.
        apply @eq_refl.
      * simpl.
        reflexivity.
      * simpl.
        reflexivity.
  - simpl.
     apply yield_def with (u := ["{"; "}"; "{"]) (v := ["}"]) (w := []) (A := "C").
    + simpl.
      apply or_intror.
      apply or_intror.
      apply or_introl.
      apply @eq_refl.
    + simpl.
      reflexivity.
    + simpl.
      reflexivity.
Qed.

(**

Use `g1_der_6`.

 *)
Theorem ex1:
  Accept g1 ["{"; "}"; "{"; "}"].
Proof.
  simpl.
  apply accept_def with (w := ["{"; "}"; "{"; "}"]) (ws := [["{"; "}"; "{"; "C"; "}"]; ["{"; "}"; "C"]; ["{"; "C"; "}"; "C"]; ["C"; "C"]; ["C"]]).
  - simpl.
    apply g1_der_6.
  - simpl.
    apply Forall_cons.
    + simpl.
      apply or_introl.
      apply @eq_refl.
    + simpl.
      apply Forall_cons.
      * simpl.
           apply or_intror.
           apply or_introl.
           apply @eq_refl.
      * simpl.
        apply Forall_cons.
        -- simpl.
           apply or_introl.
           apply @eq_refl.
        -- simpl.
           apply Forall_cons.
           ++ simpl.
              apply or_intror.
              apply or_introl.
              apply @eq_refl.
           ++ simpl.
              apply Forall_nil.
Qed.


