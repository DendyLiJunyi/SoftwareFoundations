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

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil
  | S count' => cons x (repeat''' x count')
  end.

(** Here repeat''' is implicit argument. 

    The reason for this is that marking the parameter of an inductive type as implicit causes it to become implicit for the type itself, not just for constructors. *)

Inductive list' {X : Type} : Type :=
  | nil'
  | cons' (x : X) (l : list').

Check cons'.
(** ?X -> list' -> list' *) 
Check cons.
(** ?X -> list ?X -> list ?X *)
(** Since cons' is defined by implicit argument. So we don't encounter Types as "list' X". *)

(** Implicit declaration is like an abbreviation. *)
Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Compute (app (cons 1 nil) (cons 2 nil)).

Fixpoint rev {X : Type} (l : list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Compute (rev (cons 1 (cons 2 nil))).

(** ** Supplying Type Arguments Explicitly **)
(** We want to tell Rocq the argument explicitly just this time. *)

Fail Definition mynil := nil.

Check @nil : forall X : Type, list X.

Definition mynil' := @nil nat.

Fail Definition mynil' := nil.
(** Rocq will show that mynil' already exists.
    @ is used to disable the implicit arguments. *)

Check @nil.
Check nil.
(** ?X represents some unknown type. *)

Fail Check (nil nat).
(** Can't explicitly use type as parameter. *)

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Definition list123''' := [1; 2; 3].

Check app.
Check cons nat.
Check nil.

Theorem app_nil_r : forall (X : Type), forall l : list X, l ++ [] = l.
Proof.
  intros X l.
  induction l as [| h].
  + simpl. reflexivity.
  + simpl. rewrite -> IHl. reflexivity.
Qed.

Theorem app_assoc : forall A (l m n : list A), l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros l m n n0.
  induction m as [| h m'].
  + simpl. reflexivity.
  + simpl. rewrite IHm'. reflexivity.
Qed.
(** It's so obvious that induction on the first list is much simpler! *)

Lemma app_length : forall (X : Type) (l1 l2 : list X), length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros l1 l2 l0.
  induction l2 as [| h l2'].
  + simpl. reflexivity.
  + simpl. rewrite <- IHl2'. reflexivity.
Qed.

Theorem rev_app_distr : forall X (l1 l2 : list X), rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2.
  induction l1 as [| h t].
  + simpl. rewrite -> app_nil_r. reflexivity.
  + simpl. rewrite -> IHt. rewrite <- app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X, rev (rev l) = l.
Proof.
  intros X l.
  induction l as [| h t].
  + simpl. reflexivity.
  + simpl. rewrite -> rev_app_distr. rewrite -> IHt. simpl. reflexivity.
Qed.

(** ** Polymorphic Pairs **)
(** Polymorphic Pairs can be denoted as product. *)

Inductive prod (X Y : Type) : Type :=
  | pair (x : X) (y : Y).

Arguments pair {X} {Y}.
(** Here we make the type arguments implicit. *)

Notation "( x , y )" := (pair x y).
Fail Notation "(x, y)" := (pair x y).
(** Whitespace can be viewed as part of the grammar. *)

Notation "X * Y" := (prod X Y) : type_scope.
(** Type_scope declare that this abbreviation should only be used when parsing types, not when parsing expressions. This will differ * from multiplication. *)

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X * Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

Compute (combine [1;2] [1;2;3]).

(** combine :: list X -> list Y -> list X * Y. *)
Check combine.
Compute (combine [1;2] [false;false;true;true]).

Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | h :: t => ((fst h) :: (fst (split t)), (snd h) :: (snd (split t)))
  end.

(** The power of polymorphic function allows us to use fst and snd over type (X * Y) and (list X * list Y). *)

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof.
  simpl. reflexivity.
Qed.

