(* * Introduction * *)
(**
Functional Style:
- Procedure or method has no side effects other than maps inputs to outputs -- that is, we can think of it as just a concrete method for computing a mathematical function.
- Empasizes the use of functions as first-class values, i.e., functions can be treated as data.
- Algebraic data types and pattern matching.
- Polymorphic type systems supportign abstraction and code reuse.
*)

(* * Data and Functions * *)
(** 
Enumerated Types:
Instead of the usual palette of atomic data types, Rocq offers a powerful mechanism for defining new data types from scratch, with all these familiar types as instances.
*)

(* * Days of the Week * *)

Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

(* New type is day, and its memebers are monday, etc. *)

Definition next_working_day (d : day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

(* Next we introduce different ways to working on examples in Rocq *)

(* Compute (next_working_day friday) *)

(* It makes an assertion (second working day after saturday is tuesday) and gives a name that can be used later *)

(*
Example test_next_working_day : 
  (next_working_day (next_working_day saturday)) = tuesday.

Proof. simpl. reflexivity. Qed.
*)

(* The assertion can be proved by observing that both sides of the equality evaluate to the same thing *)

(* Next we ask Rocq to extract from our definition, a program in a more conventiaonal programming language with a high-performance compiler. *)

(*
From Stdlib Require Export String.
*)

(* * Booleans * *)

Inductive bool : Type :=
  | true
  | false.

Definition negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1 : bool) (b2 : bool) : bool :=
 match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

(**
Unit tests:
Compute a complete truth table.
 *)

Example test_orb1 : (orb true false) = true.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5 : false || false || true = true.
Proof. simpl. reflexivity. Qed.

(**
Use square bracket to delimit fragments of Rocq code within comments.
 *)

(* * Conditional Expressions * *)

Definition negb' (b : bool) : bool :=
  if b then false
  else true.

Definition andb' (b1 : bool) (b2 : bool) : bool :=
  if b1 then b2
  else false.

Definition orb' (b1 : bool) (b2 : bool) : bool :=
  if b1 then true
  else b2.

(* Rocq supports conditional expressions over any inductively defined type with exactly two clauses in its definition. *)

Inductive bw : Type :=
  | bw_black
  | bw_white.

Definition invert (x : bw) : bw :=
  if x then bw_white
  else bw_black.

(* If equal to the first guard then true, else false. *)

Example test_invert_black : invert bw_black = bw_white.
Proof. simpl. reflexivity. Qed.

(* * Types * *)
(**
Expressions in Rocq has a type describing what sort of thing it computes.
The Check command asks Rocq to print the type of an expression. 
 *)

Check true
  : bool.

Check (negb true)
  : bool.

(** 
Function types: Functions like negb itself are also data values, just like true and flase. Their types are called function types, and they are written with arrows.
 *)

Check negb
  : bool -> bool.

(**
Function types: 
   bool -> bool pronounced "bool arrow bool"
 *)

(* * New Types from Old * *)

(**
Enumerated types: their definitions explicitly enumerate a finite set of elements, called constructors.
 *)

Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).

(**
Inductive definition does two things:
  1. introduces a set of new constructors.
  2. groups them into a new named type.
*)

(**
Constructor expressions are formed by applying a constructor to zero or more other constructors or constructor expressions, obeying the declared number and types of the constructor arguments
Notice that there are no realization of what "primary red" is.
*)

(**
We can define functions on colors using pattern matching just as we did for day and bool.
*)

Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary p => false
  end.

(**
"primary red" is a valid expression here
 *)

Check primary red
  : color.

Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.

(**
"primary _" means apply all rgb constructor to primary except red.
 *)

Example test_isred : isred white = false.
Proof. simpl. reflexivity. Qed.

(* * Modules * *)

Module Playground.
  Definition foo : rgb := blue.
End Playground.

Definition foo : bool := true.

Check foo.
Check Playground.foo.

(**
It's kind of like the namespace in Lean
 *)

(* * Tuples * *)

Module TuplePlayground.

(**
Single constructor with multiple parameters can be used to create a tuple type.
 *)

Inductive bit : Type :=
  | B1
  | B0.

Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).

Check (bits B1 B0 B0 B1).

(**
  "bits" constructor acts as a wrapper for its contents.
   Unwrapping can be done by pattern-matching.
  *)

Definition all_zero (nb : nybble) : bool :=
  match nb with
  | (bits B0 B0 B0 B0) => true
  | (bits _ _ _ _) => false
  end.

(**
  _ is a wildcard pattern, which avoids inventing variable names.
  *)

Compute (all_zero (bits B1 B1 B0 B0)).

Compute (all_zero (bits B0 B0 B0 B0)).

End TuplePlayground.

(* * Numbers * *)

Module NatPlayground.

(**
   Natural numbers are infinite set, all the types we build before are finite
   *)

(**
   Different representation of numbers can be useful in different environments.
   We want our definition of natural numbers can make the proof simpler.
   *)

Inductive nat : Type :=
  | O
  | S (n : nat).
(**
  In Rocq, 0 is not a valid constructor name, so we use O instead.

  This is an unary representation, by introducing 0 and S(Successor).

  One also need to notice that by writing the Inductive definition we aren't give the constructors a realization.
  They have no meaning at all!

  The realization process, in this case, is called interpretation.
  The interpretation process focus on how we can use them to compute.
 *)

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

End NatPlayground.

Check (S (S (S (S O)))).

(**
  Build in magic of Rocq, ordinary decimal numerals can be used as an alternative to the "unary" notation.
 *)

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Compute (minustwo (S (S 4))).

Check S.
Check minustwo.
Check pred.

(**

   We don't give computation rules for "S".
   "S" is just a function to help us write things down.

   Pattern matching is not enough for us to check properties on natural numbers.
 *)

Fixpoint even (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Definition odd (n : nat) : bool :=
  negb (even n).

Example test_odd1 : odd 1 = true.
Proof. simpl. reflexivity. Qed.

(**

   "simpl" has no effect on the goal.

 *)

Module NatPlayground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | 0 => m
  | S n' => S (plus n' m)
  end.

Compute (plus 3 2).

(**
If two or more arguments have the same type, they can be grouped together.
 *)

Fixpoint mult (n m : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => plus (mult n' m) m
  end.

Compute (mult 2 3).

(**
We can match two expressions at once by putting a comma between them:
 *)

Fixpoint minus (n m : nat) : nat :=
  match n, m with
  | 0 , _ => 0
  | _ , 0 => n
  | S n' , S m' => minus n' m'
  end.

Compute (minus 2 2).

End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
  | 0 => S 0
  | S power' => mult base (exp base power')
  end.

Compute (exp 2 3).

(**
We can make numerical expressions easier to read and write by introducing notations for addition, subtraction, and multiplication.
 *)

Notation "x + y" := (plus x y)
                    (at level 50, left associativity)
                    : nat_scope.

Notation "x - y" := (minus x y)
                    (at level 50, left associativity)
                    : nat_scope.

Notation "x * y" := (mult x y)
                    (at level 40, left associativity)
                    : nat_scope.

Compute (1 + 1 * 2).

(**

   It seems like one can not change the level to whatever number.
Check out the "More on Notation" section.

   In Rocq, even testing equality is a user - defined operation!

*)

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | 0 => match m with
         | 0 => true
         | S m' => false
         end
  | S n' => match m with
            | 0 => false
            | S m' => eqb n' m'
            end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | 0 => true
  | S n' => match m with
            | 0 => false
            | S m' => leb n' m'
            end
  end.

Compute (leb 1 2).

(**
   I guess eqb here means equal & bool
 *)

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Example test_leb : (3 <=? 4) = true.
Proof. reflexivity. Qed.

(**
   x = y is a claim -- "a proposition"
   x =? y is a boolean expression whose value we can compute
 *)

(* * Proof by Simplification * *)

(**
   Proof by simplification can also be used to establish more interesting properties.
 *)

Theorem plus_0_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.

(**
   reflexivity is very powerful, it also does more simplification than simpl does.
   We can sometimes throw simpl alway.

   If we don't want to leave the goal in a messy state - simpl.

   intros moves n from the quantifier in the goal to a context of current assumptions.

   We can use any identifier in the intros clause, but this might be confusing.

   A tactic is a command that is used between Proof and Qed to guide the process of checking some claim we are making.
  *)

Theorem plus_1_l : forall n : nat, 1 + n = S n.
Proof.
  intro n. simpl. reflexivity. Qed.

Theorem mult_0_l : forall n : nat, 0 * n = 0.
Proof.
  intro n. simpl. reflexivity. Qed.

(* * Proof by Rewriting * *)

Theorem plus_id_example : forall n m : nat,
  n = m ->
  n + n = m + m.
Proof.
  intros n m.
  intros H.
  (* rewrite the goal using hypothesis on the left side by using -> *)
  rewrite -> H.
  reflexivity. 
Qed.

(**
   Check can also be used to examine the statements of previously declared lemmas and theorems.
 *)

Check mult_n_O.
Check mult_n_Sm.

Theorem mult_n_0_m_0 : forall p q : nat, (p * 0) + (q * 0) = 0.
Proof.
  (* Use intros to intro multiple arguments at the same time *)
  intros p q.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  simpl.
  reflexivity.
Qed.

(* * Course Late Policies, Formalized * *)

Module LateDays.

Inductive letter : Type :=
  | A | B | C | D | F.

(* a Natural A is just a "plain" grade of A *)
Inductive modifier : Type :=
  | Plus | Natural | Minus.

(* a full grade is just a letter and a modifier *)
Inductive grade : Type :=
  Grade (l : letter) (m : modifier).

(* "A-" be encoded into "Grade A Minus" *)

(* Grade can be compare *)
Inductive comparison : Type :=
  | Eq
  | Lt
  | Gt.

Definition letter_comparison (l1 l2 : letter) : comparison :=
  match l1, l2 with
  | A, A => Eq
  | A, _ => Gt
  | B, A => Lt
  | B, B => Eq
  | B, _ => Gt
  | C, (A | B) => Lt
  | C, C => Eq
  | C, _ => Gt
  | D, (A | B | C) => Lt
  | D, D => Eq
  | D, _ => Gt
  | F, (A | B | C | D) => Lt
  | F, F => Eq
  end.


Compute letter_comparison A B.
Compute letter_comparison A A.

(** Exercise : letter_comparison **)

Theorem letter_comparision_Eq :
  forall l, letter_comparison l l = Eq.
Proof.
  intros l. destruct l eqn:El.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Definition modifier_comparison (m1 m2 : modifier) : comparison :=
  match m1, m2 with
  | Plus, Plus => Eq
  | Plus, _ => Gt
  | Natural, Plus => Lt
  | Natural, Natural => Eq
  | Natural, _ => Gt
  | Minus, (Plus | Natural) => Lt
  | Minus, Minus => Eq
  end.

(** Exercise : grade_comparison**)
Definition grade_comparison (g1 g2 : grade) : comparison :=
  match g1, g2 with
  | Grade l1 m1, Grade l2 m2 =>
      match letter_comparison l1 l2 with
      | Eq => modifier_comparison m1 m2
      | _ => letter_comparison l1 l2
      end
  end.

Example test_grade_comparison1 : (grade_comparison (Grade A Minus) (Grade B Plus)) = Gt.
Proof. simpl. reflexivity. Qed.

Example test_grade_comparison2 : (grade_comparison (Grade A Minus) (Grade A Plus)) = Lt.
Proof. simpl. reflexivity. Qed.

Example test_grade_comparison3 : (grade_comparison (Grade F Plus) (Grade F Plus)) = Eq.
Proof. simpl. reflexivity. Qed.

Example test_grade_comparison4 : (grade_comparison (Grade B Minus) (Grade C Plus)) = Gt.
Proof. simpl. reflexivity. Qed.

(**
   Define how to lower the letter component of a grade.
 *)

Definition lower_letter (l : letter) : letter :=
  match l with
  | A => B
  | B => C
  | C => D
  | D => F
  | F => F
  end.

Theorem lower_letter_lowers : forall (l : letter), letter_comparison (lower_letter l) l = Lt.
Proof.
  intro l.
  destruct l as [] eqn:El.
  - simpl. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
    (* Couldn't prove the problem cause the edge case produces a counter example *)
Abort.

(* * Exercise : lower_letter_lowers * *)
Theorem lower_letter_lowers :
  forall (l : letter), 
  letter_comparison F l = Lt ->
  letter_comparison (lower_letter l) l = Lt.
Proof.
  intros l H.
  destruct l as [] eqn:Hl.
  - simpl. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite <- H.
    simpl.
    reflexivity.
Qed.

(* * Exercise : lower_grade * *)

Definition lower_grade (g : grade) : grade :=
  match g with
  | Grade l Plus => Grade l Natural
  | Grade l Natural => Grade l Minus
  | Grade l Minus =>
      match l with
      | F => Grade F Minus
      | _ => Grade (lower_letter l) Plus
      end
  end.

Example lower_grade_A_Minus :
  lower_grade (Grade A Minus) = (Grade B Plus).
Proof.
  simpl.
  reflexivity.
Qed.

Example lower_grade_F_Natural :
  lower_grade (Grade F Natural) = (Grade F Minus).
Proof.
  reflexivity.
Qed.

Example lower_grade_twice :
  lower_grade (lower_grade (Grade B Minus)) = (Grade C Natural).
Proof.
  reflexivity.
Qed.

(* * Exercise : lower_grade_lowers * *)
Theorem lower_grade_lowers :
  forall (g : grade),
  grade_comparison (Grade F Minus) g = Lt ->
  grade_comparison (lower_grade g) g = Lt.
Proof.
  intros g H.
  destruct g as [] eqn:Hg.
  destruct l as [] eqn:Hl.
  - destruct m as [] eqn:Hm.
    reflexivity.
    reflexivity.
    reflexivity.
  - destruct m as [] eqn:Hm.
    reflexivity.
    reflexivity.
    reflexivity.
  - destruct m as [] eqn:Hm.
    reflexivity.
    reflexivity.
    reflexivity.
  - destruct m as [] eqn:Hm.
    reflexivity.
    reflexivity.
    reflexivity.
  - destruct m as [] eqn:Hm.
    reflexivity.
    reflexivity.
    rewrite <- H.
    simpl.
    reflexivity.
Qed.

Fixpoint ltb' (n m : nat) : bool :=
  match n with
  | 0 => match m with
         | 0 => false
         | _ => true
         end
  | S n' => match m with
            | 0 => false
            | S m' => ltb' n' m'
            end
  end.

Definition ltb (n m : nat) : bool :=
  match eqb n m with
  | true => false
  | false => leb n m
  end.

Compute (ltb 9 9).

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Definition apply_late_policy (late_days : nat) (g : grade) : grade :=
  if late_days <? 9 then g
  else if late_days <? 17 then lower_grade g
  else if late_days <? 21 then lower_grade (lower_grade g)
  else lower_grade (lower_grade (lower_grade g)).

(** External and internal are the same *)

Theorem apply_late_policy_unfold :
  forall (late_days : nat) (g : grade),
  (apply_late_policy late_days g) = 
  (if late_days <? 9 then g
  else if late_days <? 17 then lower_grade g
  else if late_days <? 21 then lower_grade (lower_grade g)
  else lower_grade (lower_grade (lower_grade g))).

Proof.
  intros.
  reflexivity.
Qed.

(* * Exercise : no_penalty_for_mostly_on_time * *)

Theorem no_penalty_for_mostly_on_time :
  forall (late_days : nat) (g : grade),
  (late_days <? 9 = true) ->
  apply_late_policy late_days g = g.
Proof.
  intros late_days g H.
  destruct late_days as [] eqn:E.
  - reflexivity.
  - rewrite -> (apply_late_policy_unfold (S n) g).
    rewrite -> H.
    reflexivity.
Qed.

(* * Exercise : graded_lowered_once * *)

Theorem grade_lowered_once :
  forall (late_days : nat) (g : grade),
  (late_days <? 9 = false) ->
  (late_days <? 17 = true) ->
  (apply_late_policy late_days g) = (lower_grade g).
Proof.
  intros late_days g H1 H2.
  destruct late_days as [] eqn:E.
  - rewrite -> (apply_late_policy_unfold 0 g).
    rewrite -> H1.
    rewrite -> H2.
    reflexivity.
  - rewrite -> (apply_late_policy_unfold (S n) g).
    rewrite -> H1.
    rewrite -> H2.
    reflexivity.
Qed.

End LateDays.

(* * Binary Numerals * *)

(** Unary representation can be replace by binary representation. *)

  Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

Fixpoint incr (m : bin) : bin :=
  match m with
  | Z => B1 Z
  | B0 n => B1 n
  | B1 n => B0 (incr n)
  end.

Check (B0 Z).

Fixpoint bin_to_nat (m : bin) : nat :=
  match m with
  | Z => 0
  | B0 n => 2 * (bin_to_nat n) 
  (* Need strict smaller argument *)
  | B1 n => S (2 * (bin_to_nat n))
  end.

Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Proof.
  reflexivity.
Qed.

Example test_bin_comprehensive : bin_to_nat (B0 Z) = 0.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof.
  simpl.
  reflexivity.
Qed.

Example test_bin_incr5 :
        bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
Proof. reflexivity. Qed.

Example test_bin_incr7 : bin_to_nat (B0 (B0 (B0 (B1 Z)))) = 8.
Proof.
  simpl.
  reflexivity.
Qed.
