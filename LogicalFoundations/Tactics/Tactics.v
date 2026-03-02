From LogicalFoundations Require Export Poly.

Check @curry.

(** Goal of this chapter : 
  1. "forward-" and "backward-style" proofs;
  2. reason about data constructors;
  3. strengthen an induction hypothesis;
  4. reason by case analysis. *)

(** * The apply Tactic * **)
Theorem silly1 : forall (n m : nat),
  n = m ->
  n = m.
Proof.
  intros n m eq.
  apply eq.
Qed.

(** apply works with conidtional hypotheses. *)
Theorem silly2 : forall (n m o p : nat),
  n = m ->
  (n = m -> [n;o] = [m;p]) ->
  [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2.
  apply eq1.
Qed.

(** A number is even then its successor is odd. *)
Theorem siily_ex : forall p,
  (forall n, even n = true -> even (S n) = false) ->
  (forall n, even n = false -> odd n = true) ->
  even p = true ->
  odd (S p) = true.
Proof.
  intros p eq1 eq2 eq3.
  apply eq2.
  apply eq1.
  apply eq3.
Qed.

(** apply must exactly match. *)
Theorem silly3 : forall (n m : nat),
  n = m ->
  m = n.
Proof.
  intros n m H.
  Fail apply H.
  symmetry. apply H.
Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
  l = rev l' ->
  l' = rev l.
Proof.
  intros l l' H.
  rewrite -> H.
  symmetry. apply rev_involutive.
Qed.

(** apply is rewrite + reflexivity, they are useful when the form of the goal matches the form of the theorem we want to use. *)

(** * The apply with Tactic * **)

Example trans_eq_example : forall (a b c d e f : nat),
  [a;b] = [c;d] ->
  [c;d] = [e;f] ->
  [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. apply eq2. 
Qed.

Theorem trans_eq : forall (X:Type) (x y z : X),
  x = y -> y = z -> x = z.
Proof.
  intros X x y z eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity. 
Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
  [a;b] = [c;d] ->
  [c;d] = [e;f] ->
  [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  (* couldn't directly apply, since Rocq fail to find instance for y. *)
  (* apply trans_eq with (y:=[c;d]). *)
  apply trans_eq with ([c;d]).
  apply eq1. apply eq2.
Qed.


(** Cleverly use the trans_eq theorem to build the chain of reasonging. *)
Example trans_eq_exercise : forall (n m o p : nat),
  m = (minustwo o) ->
  (n + p) = m ->
  (n + p) = (minustwo o).
Proof.
  intros n m o p eq1 eq2.
  apply trans_eq with (y := m).
  apply eq2.
  apply eq1.
Qed.

(** * The injection and discriminate Tactics * **)

