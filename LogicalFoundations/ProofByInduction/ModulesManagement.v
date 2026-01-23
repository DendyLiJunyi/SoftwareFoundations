(* * Library files, modules and identifiers * *)

Print Libraries.

Check or_comm.

(** Coq contains files Notations.vo Ltac.vo *)

From Coq Require Bool.Bool.

(** Load all logical and computational content in the file Bool.vo *)

Print Libraries.

(** 

   Now we have two more library. 

   Once a module is being loaded, one can't unrequired it.

*)

Search andb true.

(** Search command search for theorems which has an "andb" keyword. *)

About andb_true_intro.

(** Coq has an internal name to distinguish theorems and lemmas. *)

About andb_prop.

About Bool.andb_true_l.

(** 

Coq.Bool.Bool.andb_true_l is an absolutely qualified identifier / fully qualified identifier.

An absolute qualified identifier consist of the following parts.

   - Coq : logical name of the library.
   - Path of the file containing the identifier in the given library.


Coq accept partially qualified identifier. 

Why not short name?

Silent shadow.

*)

Fail Check andb_true_l.

Locate andb_true_l.
(** 

Locate shows all the constant related to the given name. 

Import a module help us to use a shorter name.

*)

Import Bool.


Check andb_true_l.

Search andb true.
Fail Search andb_true.

(** One can use Fail to make function not working. *)

Locate Bool.

About Bool.Bool.
About Coq.Bool.Bool.

(**
  
   From _ Require Import _
   
   This is a semantic to factor name of Coq library.


From Require Import Coq.Bool.Bool.
From Coq Require Import Bool.Bool.
From Coq.Bool Require Import Bool.

   One can also use From _ Require Import _ to import multiple parts of a library or a sublibrary.

   Since only have one Bool.vo, we can from Coq Require Import Bool.

 *)

(* * Basic modules and the Import command * *)

Module Foo.
  Definition foo := 42.
  Lemma bar : 21 * 2 = foo.
  Proof. reflexivity. Qed.
  Lemma baz : 21 + 21 = foo.
  Proof. reflexivity. Qed.
End Foo.

Print Module Foo.

Print Foo.foo.
Print Foo.bar.
Print Foo.baz.

Check Foo.bar.
Check Foo.baz.

(** bar and baz are not Parameters or Axioms. *)

Print Assumptions Foo.bar.
Print Assumptions Foo.baz.

(** They are closed under the global context. *)

Fail Check bar.
Locate bar.
(* Constant ModulesManagement.Foo.bar *)

Print Module Coq.Bool.Bool.

Import Foo.

Check bar.

(**
   - We Require library files to load their content.
   - We Import modules to use short names for their content.
   - Library files are modules.

 *)

(* * Name clashes and disambiguation * *)

Module OtherFoo.
  Definition foo := true.
End OtherFoo.

Import OtherFoo.

Print foo.
About foo.

(** Newer names will cover the elder names. *)

Print Foo.foo.
About Foo.foo.

Locate foo.

(** Hierarchy:
  - OtherFoo
  - Foo
  *)

Import Foo.
Print foo.
About foo.
Locate foo.
(** foo function is being covered. *)

From Coq Require Import Arith.PeanoNat ZArith.BinInt.

Check Nat.add_0_r.
Check Z.add_0_r.

Fail Check add_0_r.
(** Fail to check because it can refer to addition on two types of integers. *)

Import Nat.
Check add_0_r.
About add_0_r.

Import Z.
Check add_0_r.
About add_0_r.

About Nat.
About Coq.Init.Nat.

Module NestedABC1.
  Module ABC.
    Definition alice := 1.
    Definition bob := 1.
  End ABC.
End NestedABC1.

Module NestedABC2.
  Module ABC.
    Definition alice := 2.
    Definition charlie := 2.
  End ABC.
End NestedABC2.

Locate alice.
Locate bob.
Locate charlie.

Import NestedABC1.
Print ABC.alice.
Print ABC.bob.
Fail Print charlie.

Import NestedABC2.
Print ABC.alice.
Print ABC.bob.
Print ABC.charlie.
(** ABC.alice is being covered. *)

Locate alice.
Print NestedABC1.ABC.alice.

Import NestedABC1.ABC.

Import ABC.
Print alice.
Print bob.
Print charlie.

Locate alice.
Print NestedABC1.ABC.alice.

(** Coq allows and not allows:
- Have tow files with the same name as long as they are in different directories.
- Possible to have two (non-file) modules with the smae name as long as they are in different modules.
- it is possible to have two constants with the same name as long as they are in different modules. 

In one sentence, the absolute path should be unique.
  *)

(* * Other content types in Moudles * *)

Module Bar.

  Parameter (secret : nat).
 
  Axiom secret_is_42 : secret = 42.

  Ltac find_secret := rewrite secret_is_42.

  Notation add_42 := (Nat.add 42).

  Tactic Notation "fs" := find_secret.

  Infix "+p" := Nat.add (only parsing, at level 30, right associativity) : nat_scope.

  Lemma secret_42 : secret = 42.
  Proof. find_secret. reflexivity. Qed.
  Lemma baz : 21 +p 21 = secret.
  Proof. fs. reflexivity. Qed.

End Bar.

(* * Guidelines about the order of Require and Import commands * *)

(**
   - All Require commands should be at the beginning of a file, it makes it easier to know on which theories the file is built. 
  *)

About Bar.secret.
About Bar.secret_is_42.
Print Assumptions Bar.secret_is_42.

Print Bar.add_42.

(** 
  - tactic notation is not available
  - tactic is available
 *)

Import Bar.
Check (21 +p 21).
Lemma forty_two' : secret = 42.
Proof.
  fs.
  reflexivity.
Qed.


