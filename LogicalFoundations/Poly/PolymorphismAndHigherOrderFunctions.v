From LogicalFoundations Require Export Lists.

(** * Polymorphism *)
(** ** Polymorphism Lists **)

Inductive boollist : Type :=
  | bool_nil
  | bool_cons (b : bool) (l : boollist).
(** In this way, one need to build a "new" functions for every datatype one might meet. *)

Inductive list (X : Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Check (list nat).

(** What is list?
    A function from Types to Inductive definitions. 
    Type -> Type. *)

Check list.

(** nil and cons in the definition of list become polymorphic constructors. One need first feed them with the Type X, then can use it! *)

Check (nil nat).
Check (cons nat).
(** cons nat : nat -> list nat -> list nat. *)

(** A list contains a single number. *)
Check (cons nat 3 (nil nat)) : list nat.

Check nil.
(** It's really clear that nil has type : forall X : Type, list X. *)
Check cons.

(** Define list in this way will meet a so called annotation burden. *)

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

Check (repeat nat).

Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity. Qed.

Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity. Qed.

Module MumbleGrumble.
Inductive mumble : Type :=
  | a
  | b (x : mumble) (y : nat)
  | c.

Inductive grumble (X : Type) : Type :=
  | d (m : mumble)
  | e (x : X).

End MumbleGrumble.

(** ** Type Annotation Inference **)

Fixpoint repeat' X x count : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat' X x count')
  end.

Check repeat'.
(** Rocq can intefere that count is of type nat. *)

(** ** Type Argument Synthesis **)
(** One can use "_" to represent a "hole". *)

(** 
    repeat' X x count : list X :=
    repeat' (X : _) (x : _) (count : _) : list X :=
 *)

Fixpoint repeat'' X x count : list X :=
  match count with
  | 0 => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.

Definition nat123 :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

Check nat123.

(** ** Implicit Arguments **)
(** Tell Rocq always to infer the type arguments of a given function. *)

Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).
Check list123''.

Definition listTTF := cons true (cons true (cons false nil)).
Check listTTF.

