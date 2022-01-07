(*
        #####################################################
        ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
        #####################################################
*)
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
From Turing Require Import Lang.
From Turing Require Import Util.
Import LangNotations.
Import ListNotations.
Import Lang.Examples.
Open Scope lang_scope.
Open Scope char_scope.

(* ---------------------------------------------------------------------------*)




(**

Show that any word that is in L4 is either empty or starts with "a".

 *)
Theorem ex1:
  forall w, L4 w -> w = [] \/ exists w', w = "a" :: w'.
Proof.
  simpl.
  intros N.
  intros O.
  induction O.  
  unfold In, App in H.
  induction x.
  destruct H.
  destruct H.
  destruct H.
  destruct H0.
  inversion H0.
  inversion H1.
  - simpl.
    left.
    rewrite -> H.
    rewrite <- H3.
    rewrite <- H4.
    reflexivity.
  - simpl.
    right.
    destruct H.
    destruct H.
    destruct H.
    destruct H0.
    inversion H0.
    inversion H1.
    exists (w2 ++ w0 ++ w4).
    rewrite -> H.
    rewrite -> H5.
    rewrite -> H4.
    rewrite -> H10.
    simpl.
    reflexivity.
Qed.

(**

Show that the following word is accepted by the given language.

 *)
Theorem ex2:
  In ["a"; "b"; "b"; "a"] ("a" >> "b" * >> "a").
Proof.
  simpl.
  unfold In, Star, App.
  exists ["a" ; "b" ; "b"], ["a"].
  split.
  - simpl.
    reflexivity.
  - simpl.
    split.
    + simpl.
      exists ["a"], ["b" ; "b"].
      simpl.
      split.
      * simpl.
        reflexivity.
      * simpl.
        split.
        -- simpl.
           reflexivity.
        -- simpl.
           exists 2.
           apply pow_cons with (w1 := ["b"]) (w2 := ["b"]).
           ++ simpl.
              apply pow_cons with (w1 := ["b"]) (w2 := []).
              ** simpl.
                 apply pow_nil.
              ** simpl.
                 reflexivity.
              ** simpl.
                 reflexivity.
           ++ simpl.
              reflexivity.
           ++ simpl.
              reflexivity.
    + simpl.
      reflexivity.
Qed.

(**

Show that the following word is rejected by the given language.

 *)
Theorem ex3:
  ~ In ["b"; "b"] ("a" >> "b" * >> "a").
Proof.
  simpl.
  unfold not, In, Star, App.
  intros N.
  destruct N.
  destruct H.
  destruct H.
  destruct H0.
  destruct H0.
  destruct H0.
  destruct H0.
  destruct H2.
  destruct H3.
  unfold Char in H2, H1.
  subst.
  inversion H.
Qed.

(**

Show that the following language is empty.

 *)
Theorem ex4:
  "0" * >> {} == {}.
Proof.
  simpl.
  apply app_r_void_rw.
Qed.

(**

Rearrange the following terms. Hint use the distribution and absorption laws.

 *)
Theorem ex5:
  ("0" U Nil) >> ( "1" * ) == ( "0" >> "1" * ) U ( "1" * ).
Proof.
  simpl.
  unfold Equiv.
  intros N.
  split.
  - simpl.
    intros O. 
    rewrite <- app_union_distr_l in O.
    rewrite app_l_nil_rw in O.
    apply O.
  - simpl.
    intros O.
    rewrite <- app_union_distr_l.
    rewrite app_l_nil_rw.
    apply O.
Qed.

(**

Show that the following langue only accepts two words.

 *)
Theorem ex6:
  ("0" >> "1" U "1" >> "0") == fun w => (w = ["0"; "1"] \/ w = ["1"; "0"]).
Proof.
  simpl.
  unfold Equiv.
  split.
  - simpl.
    unfold App, In, Union.
    intros N.
    destruct N.
    destruct H.
    destruct H.
    destruct H.
    destruct H0.
    unfold Char in H0.
    unfold Char in H1.
    + simpl.
      left.
      rewrite -> H.
      rewrite -> H0.
      rewrite -> H1.
      simpl.
      reflexivity.
    + simpl.
      destruct H.
      destruct H.
      destruct H.
      destruct H0.
      unfold Char in H0.
      unfold Char in H1.
      right.
      rewrite -> H.
      rewrite -> H0.
      rewrite -> H1.
      simpl.
      reflexivity.
  - simpl.
    unfold App, In, Union.
    intros N.
    destruct N.
    + left.
      exists ["0"].
      exists ["1"].
      split.
      ** simpl.
         rewrite -> H.
         reflexivity.
      ** simpl.
         unfold Char.
         split.
         --- simpl.
             reflexivity.
         --- simpl.
             reflexivity.
    + simpl.
      right.
      exists ["1"].
      exists ["0"].
      split.
      ** simpl.
         rewrite H.
         reflexivity.
      ** simpl.
         unfold Char.
         split.
         --- simpl.
             reflexivity.
         --- simpl.
             reflexivity.
Qed.


Theorem ex7:
  "b" >> ("a" U "b" U Nil) * >> Nil == "b" >> ("b" U "a") *.
Proof.
  simpl.
  split.
  - simpl.
    intros N.
    rewrite app_r_nil_rw in N.        (*opens last part*)
    rewrite union_sym_rw in N.        (*symmetric prop*)
    rewrite star_union_nil_rw in N.
    rewrite union_sym_rw.
    apply N.
  - simpl.
    intros N.
    rewrite app_r_nil_rw.
    rewrite union_sym_rw.
    rewrite star_union_nil_rw.
    rewrite union_sym_rw in N.
    apply N.
Qed.


Theorem ex8:
  (("b" >> ("a" U {}) ) U (Nil >> {} >> "c")* ) * == ("b" >> "a") *.
Proof.
  simpl.
  split.
  - simpl.
    intros N.
    rewrite union_r_void_rw in N.     (*open 2nd part*)
    rewrite app_r_void_rw in N.       (*open Nil part*)
    rewrite app_l_void_rw in N.       (*open last part*)
    rewrite star_void_rw in N.        (*open last part*)
    rewrite union_sym_rw in N.        (*symmetric prop*)
    rewrite star_union_nil_rw in N.
    apply N.
  - simpl.
    intros N.
    rewrite union_r_void_rw.
    rewrite app_r_void_rw.
    rewrite app_l_void_rw.
    rewrite star_void_rw.
    rewrite union_sym_rw.
    rewrite star_union_nil_rw.
    apply N.
Qed.

