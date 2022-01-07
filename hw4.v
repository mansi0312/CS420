(*
        #####################################################
        ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
        #####################################################
*)
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.

From Turing Require Import Lang.
From Turing Require Import Util.
From Turing Require Import Regex.

Import Lang.Examples.
Import LangNotations.
Import ListNotations.
Import RegexNotations.

Open Scope lang_scope.
Open Scope char_scope.

(* ---------------------------------------------------------------------------*)




(**

Show that 'aba' is accepted the the following regular expression.

 *)
Theorem ex1:
  ["a"; "b"; "a"] \in (r_star "a" ;; ("b" || "c") ;; r_star "a").
Proof.
  simpl.
  apply accept_app with (s1 := ["a" ; "b"]) (s2 := ["a"]).
  - simpl.
    apply accept_app with (s1 := ["a"]) (s2 := ["b"]).
    + simpl.
      apply accept_star_eq.
      apply accept_char.
    + simpl.
      apply accept_union_l.
      apply accept_char.
    + simpl.
      reflexivity.
  - simpl.
    apply accept_star_eq.
    apply accept_char.
  - simpl.
    reflexivity.
Qed.

(**

Show that 'bb' is rejected by the following regular expression.

 *)
Theorem ex2:
  ~ (["b"; "b"] \in (r_star "a" ;; ("b" || "c") ;; r_star "a")).
Proof.
  simpl.
  unfold not.
  intros N.
  inversion N.
  subst.
  destruct s1.
  - simpl.
    inversion H2.
    subst.
    + simpl.
      subst.
      inversion H4.
    + simpl.
      subst.
      inversion H0.
      * simpl.
        subst.
        inversion H4.
  - simpl.
    inversion H1.
    subst.
    rewrite H7 in H4.
    inversion H3.
    subst.
    inversion H5.
    subst.
    + simpl.
      inversion H8.
      subst.
      inversion H2.
      * simpl.
        inversion H6.
        subst.
        ** simpl.
           inversion H4.
      * simpl.
        inversion H0.
        subst.
        inversion H4.
    + simpl.
      inversion H8.
      subst.
      inversion H4.
    + simpl.
      inversion H0.
      subst.
      inversion H4.
Qed.


(**

Function size counts how many operators were used in a regular
expression. Show that (c ;; {})* can be written using a single
regular expression constructor.


 *)
Theorem ex3:
  exists r, size r = 1 /\ (r_star ( "c" ;; r_void ) <==> r).
Proof.
  simpl.
  exists r_nil.
  split.
  - simpl.
    reflexivity.
  - simpl.
    rewrite r_app_r_void_rw.
    apply r_star_void_rw.
Qed.

(**

Given that the following regular expression uses 530 constructors
(because size r_all = 514).
Show that you can find an equivalent regular expression that uses
at most 6 constructors.


 *)
Theorem ex4:
  exists r, size r <= 6 /\  ((r_star ( (r_all || r_star "c" ) ;; r_void) ;; r_star ("a" || "b")) ;; r_star r_nil;; "c" <==> r).
Proof.
    simpl.
    exists (r_star ("a" || "b") ;; "c").
    split.
    - simpl.
      reflexivity.
    - simpl.
      rewrite r_app_r_void_rw.  (*open 1st part*)
      rewrite r_star_nil_rw.    (*open 1st part*)
      rewrite r_star_void_rw.   (*open 1st part*)
      rewrite r_app_l_nil_rw.   (*open 1st part*)
      rewrite r_app_r_nil_rw.   (*open 1st part*)
      reflexivity.
Qed.


(**

The following code implements a function that given a string
it returns a regular expression that only accepts that string.

    Fixpoint r_word' l :=
    match l with
    | nil => r_nil
    | x :: l => (r_char x) ;; r_word' l
    end.

Prove that function `r_word'` is correct.
Note that you must copy/paste the function to outside of the comment
and in your proof state: exists r_word'.

The proof must proceed by induction.


 *)

Fixpoint r_word' l :=
    match l with
    | nil => r_nil
    | x :: l => (r_char x) ;; r_word' l
    end.

Theorem ex5:
  forall l, exists (r_word:list ascii -> regex), Accept (r_word l) == fun w => w = l.
Proof.
  simpl.
  exists r_word'.
  induction l.
  - simpl.
    unfold Equiv.
    split.
    + simpl.
      intros N.
      unfold In.
      inversion N.
      reflexivity.
    + simpl.
      intros N.
      inversion N.
      subst.
      rewrite r_nil_rw.
      apply N.
  - simpl.
    unfold Equiv.
    split.
    + simpl.
      intros N.
      inversion N.
      inversion H1.
      destruct IHl with (w:=s2).
      subst.
      intuition.
      rewrite H.
      simpl.
      reflexivity.
    + simpl.
      intros N.
      inversion N.
      unfold In.
      apply accept_app with (s1 := [a]) (s2 := l).
      ** simpl.
         apply accept_char.
      ** simpl.
         apply IHl.
         unfold In.
         simpl.
         reflexivity.
      ** simpl.
         reflexivity.
Qed.


(**

Show that there exists a regular expression with 5 constructs that
recognizes the following language. The idea is to find the smallest
regular expression that recognizes the language.


 *)
Theorem ex6:
  exists r, (Accept r == fun w => w = ["a"; "c"] \/ w = ["b"; "c"]) /\ size r = 5.
Proof.
  simpl.
  exists (("a" || "b") ;; "c").
  split.
  - simpl.
    intros N.
    split.
    + simpl.
      intros O.
      apply r_app_union_distr_l in O.
      inversion O.
      * simpl.
        subst.
        left.
        inversion H2.
        rewrite -> H5.
        inversion H1.
        inversion H3.
        simpl.
        reflexivity.
      * simpl.
        subst.
        right.
        inversion H2.
        rewrite -> H5.
        inversion H1.
        inversion H3.
        simpl.
        reflexivity.
    + simpl.
      intros O.
      apply r_app_union_distr_l.
      inversion O.
      * simpl.
        unfold In.
        apply accept_union_l.
        rewrite H.
        apply accept_app with (s1 := ["a"]) (s2 := ["c"]).
        -- simpl.
           apply accept_char.
        -- simpl.
           apply accept_char.
        -- simpl.
           reflexivity.
      * simpl.
        unfold In.
        apply accept_union_r.
        rewrite H.
        apply accept_app with (s1 := ["b"]) (s2 := ["c"]).
        -- simpl.
           apply accept_char.
        -- simpl.
           apply accept_char.
        -- simpl.
           reflexivity.
  - simpl.
    reflexivity.
Qed.


