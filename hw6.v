(*
        #####################################################
        ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
        #####################################################
*)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Turing.Lang.
Require Import Turing.Regular.
Require Import Turing.Regex.
Require Import Turing.Util.
Require Import Omega.
Import ListNotations.
Import RegexNotations.
Import Lang.LangNotations.
Open Scope char_scope.
Open Scope lang_scope.
Open Scope regex_scope.

(* ---------------------- END OF PREAMBLE ------------------ *)

(**

  The objective of this homework assignment is to prove that
  language L5 is not regular, where L5 is a^n b^m where n < m.


  WARNING: DO NOT CHANGE DEFINITION L5, otherwise you will get 0 points for
  this assignment.

*)
Definition L5 : language := fun w => exists n m, w = pow1 "a" n ++ (pow1 "b" ((S m) + n)).

Lemma pow1_app_cons_inv_eq_1:
forall {T} (a b:T),
a <> b ->
forall x y v w,
pow1 a x ++ b :: y = pow1 a v ++ b :: w ->
x = v.
Proof.
intros ? a b.
induction x; intros. {
    simpl in *.
    destruct v; auto.
    simpl in *.
    inversion H0.
    subst.
    contradiction.
}
simpl in *.
destruct v; simpl in *. {
    inversion H0.
    subst.
    contradiction.
}
inversion H0; subst; clear H0.
apply IHx in H2.
subst; reflexivity.
Qed.

(* ---------------------------------------------------------------------------*)




(**

Easy. Show that the word that clogs is in L5.

 *)
Theorem l5_not_regular_1:
  forall p, In (pow1 "a" p ++ pow1 "b" (S p)) L5.
Proof.
  simpl.
  intros N.
  unfold In.
  unfold L5.
  exists N.
  exists 0.
  simpl.
  reflexivity.
Qed.

(**

Easy. Show that the clogged word has at least p-characters.

 *)
Theorem l5_not_regular_2:
  forall p, length (pow1 "a" p ++ pow1 "b" (S p)) >= p.
Proof.
  simpl.
  intros N.
  induction N.
  - simpl.
    intuition.
  - simpl.
    rewrite -> app_length.
    rewrite -> pow1_length.
    omega.
Qed.

(**

Difficult. The proof for Regular.Examples.l4_not_regular_alt is similar to what you should be doing. The only theorem you need to use is Regular.Examples.xyz_rw_ex.


 *)
Theorem l5_not_regular_4_1:
  forall p x y z n m, p >= 1 -> y <> [] -> pow1 "a" p ++ "b" :: pow1 "b" p = x ++ y ++ z -> length (x ++ y) <= p -> x ++ (y ++ y) ++ z = pow1 "a" n ++ pow1 "b" (S m + n) -> exists nx ny o,
    ny <> 0 /\
    pow1 "a" nx ++
    (pow1 "a" ny ++ pow1 "a" ny) ++
    pow1 "a" o ++
    "b" :: pow1 "b" (length (pow1 "a" nx ++ pow1 "a" ny) + o)
    =
    pow1 "a" n ++ pow1 "b" (S m + n).
Proof.
  simpl.
  intros N.
  intros M.
  intros O.
  intros P.
  intros Q.
  intros R.
  intros S.
  intros T.
  intros V.
  intros W.
  intros X.
  apply Regular.Examples.xyz_rw_ex in V.
  destruct V.
  destruct H.
  destruct H0.
  destruct H1.
  destruct H2.
  rewrite -> H1 in X.
  rewrite -> H2 in X.
  rewrite -> H3 in X.
  rewrite -> H in X.
  repeat rewrite app_assoc in *. (* l4_not_regular *)
  repeat rewrite pow1_plus in *.
  exists (length M), (length O), x.
  split.
  - simpl.
    intros Y.
    destruct O.
    + simpl.
      contradiction T.
    + simpl.
      inversion Y.
  - simpl.
    repeat rewrite app_assoc in *.
    repeat rewrite pow1_plus in *.
    rewrite -> pow1_length.
    rewrite -> app_length in X.
    rewrite -> X.
    simpl.
    reflexivity.
  - simpl.
    assumption.
Qed.


(**

Easy. Use rewriting rules (eg, app_assoc).

 *)
Theorem l5_not_regular_4_2:
  forall nx ny n m o, pow1 "a" nx ++ (pow1 "a" ny ++ pow1 "a" ny) ++ pow1 "a" o ++ "b" :: pow1 "b" (length (pow1 "a" nx ++ pow1 "a" ny) + o) = pow1 "a" n ++ pow1 "b" (S m + n) -> pow1 "a" (nx + ny + ny + o) ++ "b" :: pow1 "b" (nx + ny + o) = pow1 "a" n ++ "b" :: pow1 "b" (m + n).
Proof.
  simpl.
  intros N.
  intros M.
  intros O.
  intros P.
  intros Q.
  intros R.
  repeat rewrite app_assoc in R.
  repeat rewrite pow1_plus in R.
  repeat rewrite pow1_length in R.
  assumption.
Qed.

(**

Hard. This is the final step of the proof. You want to start by showing that the powers of "a" are equal (for which you'll need pow1_app_cons_inv_eq_1). After that you want to remove the left-hand side of the equality with app_inv_head. Your final step should be to conclude that both powers must be equal. Once you have an equality over naturals, then use `omega` to conclude.


 *)
Theorem l5_not_regular_4_3:
  forall nx ny o n m, ny <> 0 -> pow1 "a" (nx + ny + ny + o) ++ "b" :: pow1 "b" (nx + ny + o) <>
    pow1 "a" n ++ "b" :: pow1 "b" (m + n).
Proof.
  simpl.
  intros N.
  intros O.
  intros P.
  intros Q.
  intros R.
  intros S.
  intros T.
  inversion T.
  apply pow1_app_cons_inv_eq_1 in H0.
  - simpl.
    rewrite -> H0 in T.
    apply app_inv_head in T.
    inversion T.
    apply pow1_inv_eq in H1. 
    omega.
  - simpl.
    intros V.
    inversion V.
Qed.

(**

Easy. Use the lemmas that start with l5_not_regular_4_

 *)
Theorem l5_not_regular_4:
  forall p m n x y z, p >= 1 -> y <> [] -> pow1 "a" p ++ "b" :: pow1 "b" p = x ++ y ++ z -> length (x ++ y) <= p -> x ++ (y ++ y) ++ z <> pow1 "a" n ++ pow1 "b" (S m + n).
Proof.
  simpl.
  intros N.
  intros O.
  intros P.
  intros Q.
  intros R.
  intros S.
  intros T.
  intros V.
  intros W.
  intros X.
  intros Y.
  apply l5_not_regular_4_1 with (p:= N) in Y.
  - simpl.
    destruct Y.
    destruct H.
    destruct H.
    destruct H.
    apply l5_not_regular_4_2 in H0.
    apply l5_not_regular_4_3 in H0.
    + simpl.
      assumption.
    + simpl.
      assumption.
  - simpl.
    omega.
  - simpl.
    assumption.
  - simpl.
    assumption.
  - simpl.
    assumption.
Qed.

(**

Easy. Show that a^p b^(p+1) clogs L5. Conclude the proof using Lemma l5_not_regular_4 to conclude.


 *)
Theorem l5_not_regular_3:
  forall p, p >= 1 -> In (pow1 "a" p ++ pow1 "b" (S p)) (Clogs L5 p).
Proof.
  - simpl.
    unfold In, Clogs.
    intros N.
    intros O.
    intros P.
    intros Q.
    intros R.
    intros S.
    intros T.
    intros V.
    exists 2.
    intros W.
    unfold In in W.
    unfold L5 in W.
    destruct W.
    destruct H.
    simpl in H.
    rewrite app_nil_r in H.
    apply l5_not_regular_4 with (p:=N) in H.
    + simpl.
      apply H.
    + simpl.
      assumption.
    + simpl.
      assumption.
    + simpl.
      assumption.
    + simpl.
      assumption.
Qed.


(**

Easy. Show that L5 is not regular.

 *)
Theorem l5_not_regular:
  ~ Regular L5.
Proof.
  simpl.
  unfold L5.
  apply not_regular.
  intros N.
  intros O.
  apply clogged_def with (w:=(pow1 "a" N ++ pow1 "b" (1 + N)) % list).
  - simpl.
    unfold In.
    unfold L5.
    exists N.
    exists 0.
    simpl.
    reflexivity.
  - simpl.
    induction N.
    + simpl.
      intuition.
    + simpl.
      rewrite -> app_length.
      rewrite -> pow1_length.
      omega.
  - simpl.
    unfold In, Clogs.
    intros P.
    intros Q.
    intros R.
    intros S.
    intros T.
    intros V.
    exists 2.
    intros W.
    unfold In in W.
    unfold L5 in W.
    destruct W.
    destruct H.
    simpl in H.
    rewrite app_nil_r in H.
    apply l5_not_regular_4 with (p:=N) in H.
    + simpl.
      apply H.
    + simpl.
      assumption.
    + simpl.
      assumption.
    + simpl.
      assumption.
    + simpl.
      assumption.
Qed.




