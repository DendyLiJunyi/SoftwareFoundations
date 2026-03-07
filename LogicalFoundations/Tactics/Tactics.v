From LogicalFoundations Require Export Poly.
From LogicalFoundations Require Export ProofByInduction.

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
    - simpl in eqm. apply f_equal. specialize IHn' with (m := m'). apply IHn' in eqm. apply eqm.
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

(** fewer intros before an induction to obtain a more general IH doesn't always work.

   Sometimes we need rearrangement of quantified variable. *)

Theorem double_injective_take2_FAILED : forall n m,
  double n = double m ->
  n = m.
Proof.
  induction n as [| n'].
  + intros m H. simpl in H. destruct m as [| m']. reflexivity. discriminate H.
  + intros m H. destruct m as [| m'].
    - simpl in H. discriminate H.
    - f_equal. specialize IHn' with (m := m'). apply IHn'. simpl in H. injection H as goal. apply goal.
Qed.

(** We can selectively generalize variables by using generalize dependent. *)

Theorem double_injective_take2 : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [| m' IHm'].
  - simpl. intros n eq. destruct n as [| n'] eqn : E.
    + reflexivity.
    + simpl in eq. discriminate.
  - intros n eq. destruct n as [| n'] eqn : E.
    + specialize IHm' with (n := 0). discriminate.
    + f_equal. specialize IHm' with (n := n'). apply IHm'. simpl in eq. injection eq as goal. apply goal.
Qed.

(** Actually make the induction hypothesis more general also works. *)

(** * Rewriting with conditional statements * **)

Lemma sub_add_leb : forall n m,
  n <=? m = true ->
  (m - n) + n = m.
Proof.
  induction n as [| n' IHn'].
  (* induction has an induction hypothesis where destruct doesn't *)
  - intros m H. rewrite add_0_r. destruct m as [| m'].
    + (* n = 0 *)
      reflexivity.
    + (* n = S n' *)
      reflexivity.
  - intros m H. destruct m as [| m'].
    + (* m = 0 *)
      discriminate.
    + (* m = S m' *)
      simpl in H. simpl. rewrite <- plus_n_Sm.
      rewrite IHn'.
      * reflexivity.
      * apply H.
Qed.

Theorem nth_error_after_last : forall (n : nat) (X : Type) (l : list X),
  length l = n ->
  nth_error l n = None.
Proof.
  intros n X l.
  generalize dependent n.
  induction l as [| h t IH].
  - (* l = [ ] *)
    intros n H.
    simpl. reflexivity.
  - (* l = h :: t *)
    intros n H.
    destruct n as [| n'].
    + (* n = 0 *)
      simpl. simpl in H. discriminate.
    + (* n = S n' *)
      simpl. simpl in H. specialize IH with (n := n').
      rewrite IH.
      * reflexivity.
      * injection H as goal.
        apply goal.
Qed.

(** * Unfolding Definitions * **)

Definition square n := n * n.
Lemma square_mult : forall n m,
  square (n * m) = square n * square m.
Proof.
  intros n m.
  simpl.
  unfold square.
  Search (_ * _ * _ = _ * (_ * _)).
  rewrite -> Nat.mul_shuffle1 with (n := n) (m := m) (p := n) (q := m).
  reflexivity.
Qed.

(** automatic unfolding will fail for structure involve pattern matching.

   In this case one can use both destruct and unfold to continue the proof. *)

(** * Using destruct on Compound Expressions * **)

(** Reason by cases on the result of some expression. *)
Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.

Theorem siilyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (n =? 3) eqn : E1.
  (* expression belongs to some type, thus we can use the type constructor to destruct. *)
  - (* (n =? 3) = true *)
    reflexivity.
  - (* (n =? 3) = false *)
    destruct (n =? 5) eqn : E2.
    + (* (n =? 5) = true *)
      reflexivity.
    + (* (n =? 5) = false *)
      reflexivity.
Qed.

Check @split.

Theorem combine_split_fail : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l l1 l2 H.
  destruct l1 as [| h1 t1] eqn : E1.
  - (* l1 = [ ] *)
    destruct l2 as [| h2 t2] eqn : E2.
    + (* l2 = [ ] *)
      destruct l as [| h3 t3] eqn : E3.
      ++ reflexivity.
      ++ discriminate H.
    + (* l2 = h2 :: t2 *)
      destruct l as [| h3 t3] eqn : E3.
      ++ reflexivity.
      ++ discriminate H.
  - (* l1 = h1 :: t1 *)
    destruct l2 as [| h2 t2] eqn : E2.
    + (* l2 = [ ] *)
      destruct l as [| h3 t3] eqn : e3.
      ++ discriminate.
      ++ unfold combine. discriminate.
    + (* l2 = h2 :: t2 *)
      destruct l as [| h3 t3] eqn : e3.
      ++ discriminate.
      ++ unfold combine.
Abort.
(** I'm overcomplicating by destructing l1 l2 l. *)


Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l.
  induction l as [| h t IH].
  - (* l = [ ] *)
    intros l1 l2 H.
    simpl in H.
    injection H as h1 h2.
    rewrite <- h1.
    rewrite <- h2.
    reflexivity.
  - (* l = h :: t *)
    intros l1 l2 H.
    destruct h as [x y].
    simpl in H.
    destruct (split t) as [T1 T2].
    injection H as H1 H2.
    rewrite <- H1.
    rewrite <- H2.
    simpl.
    f_equal.
    rewrite IH with (l1 := T1) (l2 := T2).
    * reflexivity.
    * reflexivity.
Qed.

(** So many tricks is being used in this problem! *)

(** When destruct compound expression, the eqn: part cannot _ be omitted. 

   If we leave it out, then destruct can erase information. *)

Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false.

Theorem sillyfun1_odd_FAILED : forall (n : nat),
  sillyfun1 n = true ->
  odd n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (n =? 3) eqn:Heqe3.
  - apply eqb_true in Heqe3.
    rewrite -> Heqe3.
    reflexivity.
  - destruct (n =? 5) eqn:Heqe5.
    + apply eqb_true in Heqe5.
      rewrite Heqe5.
      reflexivity.
    + discriminate.
Qed.

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b.
  destruct (f b) eqn:E1.
  - destruct (f true) eqn:E2.
    + destruct (f true) eqn:E3.
      ++ reflexivity.
      ++ apply E2.
    + destruct (f false) eqn:E3.
      ++ reflexivity.
      ++ rewrite <- E1.
         destruct b eqn:E4.
         +++ rewrite E2. reflexivity.
         +++ rewrite E3. reflexivity.
  - destruct (f false) eqn:E2.
    + destruct (f true) eqn:E3.
      ++ destruct b eqn:E4.
         +++ rewrite <- E3. rewrite -> E1. reflexivity.
         +++ rewrite <- E1. rewrite <- E2. reflexivity.
      ++ reflexivity.
    + apply E2.
Qed.


Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
  induction n as [| n' IH].
  - intros m. destruct (0 =? m) eqn:E.
    + Search eqb. symmetry. rewrite eqb_true with (n := 0) (m := m).
      ++ apply eqb_refl.
      ++ apply E.
    + destruct m.
      ++ discriminate.
      ++ simpl. reflexivity.
  - destruct m as [| m'].
    + reflexivity.
    + simpl. specialize IH with (m := m'). apply IH.
Qed.

Theorem eqb_trans : forall n m p,
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof.
  intros n m p H1 H2.
  apply eqb_true in H1.
  apply eqb_true in H2.
  destruct (n =? p) eqn:E.
  - reflexivity.
  - rewrite -> H1 in E.
    destruct m as [| m'].
    + destruct p as [| p'].
      ++ discriminate.
      ++ discriminate H2.
    + destruct p as [| p'].
      ++ discriminate H2.
      ++ simpl in E. injection H2 as H2. rewrite <- H2 in E.
         rewrite -> eqb_refl in E. 
         discriminate.
Qed.

Definition split_combine_statement : Prop := forall X Y (l : list (X * Y)) (l1 : list X) (l2 : list Y),
  length l1 = length l2 -> combine l1 l2 = l ->
  split l = (l1, l2).

Theorem split_combine : forall X Y (l : list (X * Y)) (l1 : list X) (l2 : list Y),
  length l1 = length l2 -> combine l1 l2 = l ->
  split l = (l1, l2).
Proof.
  intros X Y l l1.
  generalize dependent l.
  induction l1 as [| h1 t1 IH1].
  - (* l1 = [ ] *)
    intros l l2 H1 H2.
    + destruct (combine [ ] l2) eqn:E1.
      ++ (* combine [ ] [ ] = [ ] *)
         rewrite <- H2. simpl in E1. simpl in H1. simpl.
         Search length. destruct l2 eqn:E2.
         +++ reflexivity.
         +++ discriminate H1.
      ++ (* combine [ ] l2 = x :: l0 *)
         simpl in E1.
         discriminate.
  - (* l1 = h1 :: t1 *)
    intros l l2 H1 H2.
    + destruct (combine (h1 :: t1)) eqn:E1.
      ++ (* combine (h1 :: t1) l2 = [ ] *)
         rewrite <- H2.
         destruct l2 as [| h2 t2] eqn:E2.
         +++ discriminate H1.
         +++ simpl in E1. discriminate E1.
      ++ (* combine (h1 :: t1) l2 = x :: l0 *)
         rewrite <- H2.
         destruct l2 as [| h2 t2] eqn:E2.
         +++ simpl in E1. discriminate.
         +++ simpl in E1.
             specialize IH1 with (l2 := t2) (l := l0).
             simpl in H1. injection H1 as H1.
             injection E1 as E1' E1''.
             apply IH1 in H1.
             ++++ rewrite <- E1'.
                  simpl.
                  rewrite -> H1.
                  reflexivity.
             ++++ apply E1''.
Qed.
(** variable is bounded or not very important!!!! *)

Theorem filter_exercise : forall (X : Type) (test : X -> bool) (x : X) (l lf : list X),
  filter test l = x :: lf ->
  test x = true.
Proof.
  intros X test x l.
  generalize dependent x.
  induction l as [| h t IH].
  - (* l = [ ] *)
    intros x lf H.
    simpl in H. discriminate.
  - (* l = h :: t *)
    intros x lf H.
    simpl in H. destruct (test h) eqn:E.
    + (* test h = true *)
      ++ injection H as H.
         rewrite -> H in E.
         apply E.
    + (* test h = false *)
      apply IH in H. apply H.
      (* test h = false then l can reduce to a smaller list which satisfies the induction hypothesis. *)
Qed.

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [ ] => true
  | h :: t => andb (test h) (forallb test t)
  end.

Example test_forallb_1 : forallb odd [1;3;5;7;9] = true.
Proof. reflexivity. Qed.

Example test_forallb_2 : forallb negb [false;false] = true.
Proof. reflexivity. Qed.

Example test_forallb_3 : forallb even [0;2;4;5] = false.
Proof. reflexivity. Qed.

Example test_forallb_4 : forallb (eqb 5) [] = true.
Proof. reflexivity. Qed.

Fixpoint existsb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [ ] => false
  | h :: t => if test h then true
              else existsb test t
  end.

Example test_existsb_1 : existsb (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.

Example test_existsb_2 : existsb (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.

Example test_existsb_3 : existsb odd [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.

Example test_existsb_4 : existsb even [] = false.
Proof. reflexivity. Qed.

Definition existsb' {X : Type} (test : X -> bool) (l : list X) : bool := negb (forallb (fun x => negb (test x)) l).

Example test_existsb_1' : existsb' (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.

Example test_existsb_2' : existsb' (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.

Example test_existsb_3' : existsb' odd [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.

Example test_existsb_4' : existsb' even [] = false.
Proof. reflexivity. Qed.

Theorem existsb_existsb' : forall (X : Type) (test : X -> bool) (l : list X),
  existsb test l = existsb' test l.
Proof. 
  intros X test.
  induction l as [| h t IH].
  - (* l = [ ] *)
    simpl. unfold existsb'. simpl. reflexivity.
  - (* l = h :: t *)
    simpl. destruct (test h) eqn:E.
    ++ (* test h = true *)
       unfold existsb'. simpl. rewrite -> E. simpl. reflexivity.
    ++ (* test h = false *)
       rewrite -> IH. unfold existsb'. simpl. rewrite -> E. reflexivity.
Qed.

