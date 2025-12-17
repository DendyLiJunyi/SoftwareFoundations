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

(*
Unit tests:
Compute a complete truth table.
 *)

Example test_orb1 : (orb true false) = true.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5 : false || false || true = true.
Proof. simpl. reflexivity. Qed.

(*
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

