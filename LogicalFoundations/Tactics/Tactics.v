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

(**
Inductive nat : Type :=
   | o
   | S (n : nat). *)

(** Implicit facts :
   constructor S is injective;
   constructor o and S are disjoint. 

   Forall the inductively defined type : all constructors are injective, and the values built from distinct constructors are never equal. *)

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)). {reflexivity. }
  rewrite H2. rewrite H1. simpl. reflexivity.
Qed.

(** assert tactic adds a given hypothesis.

   injection tactic allows us to exploit the injectivity of any constructor. *)
Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  injection H as Hnm.
  apply Hnm.
Qed.

Theorem injection_ex1 : forall (n m o : nat),
  [n;m] = [o;o] ->
  n = m.
Proof.
  intros n m o H.
  injection H as H1 H2.
  rewrite -> H1. symmetry. apply H2.
Qed.

Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.
Proof.
  intros X x y z l j H1 H2.
  injection H1 as Hxy Hl.
  assert (Hl2 : y :: l = z :: l). { rewrite <- H2. apply Hl. }
  injection Hl2 as Hyz.
  rewrite -> Hxy. symmetry. apply Hyz.
Qed.

(** rewrite -> is replace left by right.
   
   disjointness says two terms beginning with different constructors can never be equal. *)

Theorem discriminate_ex1 : forall (n m : nat),
  false = true ->
  n = m.
Proof.
  intros n m contra.
  discriminate contra.
Qed.

Theorem discriminate_ex2 : forall (n : nat),
  S n = 0 ->
  2 + 2 = 5.
Proof.
  intros n contra.
  discriminate contra.
Qed.

(** These examples are principle of explosion, a contradictory hypothesis entails anything. 

   When the discriminate happens the theorem is somehow nonesense. *)

Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = [] ->
  x = z.
Proof.
  intros X x y z l HX contra.
  discriminate contra.
Qed.

(** Use discriminate to make connection. *)
Theorem eqb_0_l : forall n,
  0 =? n = true -> n = 0.
Proof.
  intros n.
  destruct n as [| n'].
  - (* n = 0 *)
    intros H. reflexivity.
  - (* n = S n' *)
    intros contra. discriminate contra.
Qed.

Theorem f_equal : forall (A B : Type) (f : A -> B) (x y : A),
  x = y -> f x = f y.
Proof.
  intros A B f x y eq.
  rewrite <- eq.
  reflexivity.
Qed.

Theorem eq_implies_succ_equal : forall (n m : nat),
  n = m -> S n = S m.
Proof. intros n m H. apply f_equal. apply H. Qed.

(** f_equal tactic *)

Theorem eq_implies_succ_equal' : forall (n m : nat),
  n = m -> S n = S m.
Proof.
  intros n m H.
  f_equal.
  apply H.
Qed.

(** * Using Tactics on Hypotheses * **)

Theorem S_inj : forall (n m : nat) (b : bool),
  ((S n) =? (S m)) = b ->
  (n =? m) = b.
Proof.
  intros n m b H.
  simpl in H.
  apply H.
Qed.

(** apply L in H gives us a form of "forward reasoning" *)
Theorem silly4 : forall (n m p q : nat),
  (n = m -> p = q) ->
  m = n ->
  q = p.
Proof.
  intros n m p q H1 H2.
  symmetry in H2.
  apply H1 in H2.
  symmetry in H2.
  apply H2.
Qed.

(** Forward reasoning is build a theorem exactly match the goal.
   Backward reasoning is solve the goal. *)

(** * Specializing Hypotheses * **)

(** specialize = assert and apply *)
Theorem specialize_example : forall n,
  (forall m, m * n = 0) -> n = 0.
Proof.
  intros n H.
  specialize H with (m := 1).
  Search (1 * _ = _).
  rewrite -> Nat.mul_1_l in H.
  apply H.
Qed.

Theorem specialize_example' : forall n,
  (forall m, m * n = 0) -> n = 0.
Proof.
  intros n H.
  assert (H2 : 1 * n = 0). { apply H. }
  rewrite -> Nat.mul_1_l in H2.
  apply H2.
Qed.

(** A -> B is replace A with B *)

Lemma nth_error_always_none : forall (l : list nat),
  (forall i, nth_error l i = None) ->
  l = [].
Proof.
  intros l H.
  specialize H with (i := 0).
  destruct l as [| h t].
  (* we must destruct l here, since we can't use induction, we'll use destruct. *)
  + reflexivity.
  + simpl in H. discriminate H.
    (* different constructors can't be equal. *)
Qed.

Example trans_eq_example''' : forall (a b c d e f : nat),
  [a;b] = [c;d] ->
  [c;d] = [e;f] ->
  [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  specialize trans_eq with (y := [c;d]) as H.
  apply H.
  apply eq1.
  apply eq2.
Qed.
(** as... clause can name the new hypothesis. *)

(** * Varying the Induction Hypothesis * **)
Theorem double_injective : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n. induction n.
  + intros m H. simpl in H. destruct m as [| m'].
    - reflexivity.
    - discriminate H.
  + intros m H. destruct m as [| m'].
    - specialize IHn with (m := 0). rewrite IHn in H. discriminate H. discriminate H.
    - injection H. specialize IHn with (m := m'). intros eq1. apply IHn in eq1. rewrite <- eq1. reflexivity.
Qed.

(** Problems with intros n m. **)
Theorem double_injective_FAILED : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m. induction n as [| n' IHn'].
  - (* n = O *) simpl. intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *) intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) discriminate eq.
    + (* m = S m' *) f_equal.
Abort.

(** The problems happens because we fix m, and consider forall n.

   Takeaway :
   Use induction to prove things, one doesn't want things to be so specific. *)

Theorem eqb_true : forall n m,
  n =? m = true -> 
  n = m.
Proof.
  induction n as [| n'].
  + intros m eqm. destruct m as [| m'].
    - reflexivity.
    - simpl in eqm. discriminate eqm.
  + intros m eqm. destruct m as [| m'].
    - simpl in eqm. discriminate eqm.
    - simpl in eqm. apply f_equal. specialize IHn' with (m := m'). apply IHn' in eqm.apply eqm.
Qed.

(** Informal Proof :
   we do induction on n.
   P(0) := " 0 =? m = true implies 0 = m".
   + for m = 0, it's trivial;
   + for m = S m', since two constructors can't be same, we reach a contradiction.

   Suppose P(n) := "n =? m is true implies n = m". we want to show P(S n) := "S n =? m is true implies S n = m".

   + for m = 0, since two constructors are different, we reach a contradiction.
   + for m = S m', we have S n =? S m' which can be simplified to n =? m'. Since m is bounded by universal quantifier, thus we can set m to be m' inside P(n), thus we reach the result. *)

Theorem plus_n_n_injective : forall n m,
  n + n = m + m ->
  n = m.
Proof.
  induction n as [| n'].
  + intros m eq. destruct m as [| m'].
    (* what's the difference between destruct and induction? *)
    - reflexivity.
    - simpl in eq. discriminate.
  + intros m eq. destruct m as [| m'].
    - simpl in eq. discriminate eq.
    - specialize plus_n_Sm with (n := S m') as Hm. specialize Hm with (m := m'). rewrite <- Hm in eq.
      specialize plus_n_Sm with (n := S n') as Hn. specialize Hn with (m := n'). rewrite <- Hn in eq. simpl in eq. injection eq. specialize IHn' with (m := m'). intros Hmn. apply IHn' in Hmn. apply f_equal. apply Hmn.
Qed.
