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


