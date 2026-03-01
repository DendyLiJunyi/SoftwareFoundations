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

(** ** Polymorphic Options ** **)

Module OptionPlayground.

Inductive option (X : Type) : Type :=
  | Some (x : X)
  | None.

Arguments Some {X}.
Arguments None {X}.

Inductive option' {X : Type} : Type :=
  | Some' (x : X)
  | None'.

End OptionPlayground.

Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
  match l with
  | nil => None
  | a :: l' => match n with
               | 0 => Some a
               | S n' => nth_error l' n'
               end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = None.
Proof. reflexivity. Qed.

Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
  | nil => None
  | a :: l' => Some a
  end.

Check @hd_error.
Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
Proof. reflexivity. Qed.

(** * Functions as Data * **)
(** ** Higher-Order Functions ** **)

Definition doit3times {X : Type} (f : X -> X) (n : X) : X :=
  f (f (f n)).

Check @doit3times.
Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.
Example test_doit3times': doit3times negb true = false.
Proof. reflexivity. Qed.

(** ** Filter ** **)
(** predicate on X := X -> bool *)
Fixpoint filter {X : Type} (test : X -> bool) (l : list X) : list X :=
  match l with
  | [] => []
  | h :: t =>
      if test h then h :: (filter test t)
      else filter test t
  end.

Example test_filter1 : filter even [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  (length l) =? 1.

Example test_filter2: filter length_is_1 [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ] = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

Definition countoddmembers' (l : list nat) : nat :=
  length (filter odd l).

Example test_countoddmembers'1 : countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers'2 : countoddmembers' [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3 : countoddmembers' nil = 0.
Proof. reflexivity. Qed.

(** ** Anonymous Functions ** **)
(** Anonymous means unknown/hidden *)

Example test_anon_fun' : doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

(** fun n => n * n can be read as the function that, given a number n, yields n * n. *)

Example test_filter2' : filter (fun l => (length l) =? 1) [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ] = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

Definition filter_even_gt7 (l : list nat) : list nat := filter (fun n => andb (even n) (negb (leb n 7))) l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

Definition partition {X : Type} (test : X -> bool) (l : list X) : list X * list X :=
  (filter test l, filter (fun n => negb (test n)) l).

Example test_partition1 : partition odd [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.

Example test_partition2 : partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | h :: t => (f h) :: (map f t)
  end.
(** l = [n1, n2, ...] => f l = [f n1, f n2, ...] *)
Example test_map1 : map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Theorem map_app : forall (X Y: Type) (f : X -> Y) (l1 l2 : list X), map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
  intros X Y f l1 l2.
  induction l1 as [| h t].
  + reflexivity.
  + simpl. rewrite -> IHt.
    reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X), map f (rev l) = rev (map f l).
Proof.
  intros X Y f l.
  induction l as [| h t].
  + reflexivity.
  + simpl. rewrite <- IHt. 
    replace [f h] with (map f [h]).
    - rewrite <- map_app. reflexivity.
    - reflexivity.
Qed.

Fixpoint flat_map {X Y : Type} (f : X -> list Y) (l : list X) : list Y :=
  match l with
  | nil => []
  | h :: t => f h ++ flat_map f t
  end.

Example test_flat_map1 : flat_map (fun n => [n;n;n]) [1;5;4] = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.

(** The idea of "map" can be extend to things look like a list. *)
Definition option_map {X Y : Type} (f : X -> Y) (xo : option X) : option Y :=
  match xo with
  | None => None
  | Some x => Some (f x)
  end.

Fail Check (option_map nat nat).
(** Fail to check cause we are doing in an implicit way. *)

(** ** Fold ** **)
(** This function is inspiration for the "reduce" operation that lies at the heart of Google's map/reduce distributed programming framework. *)

Fixpoint fold {X Y : Type} (f : X -> Y -> Y) (l : list X) (b : Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

(** Intuitively, the behavior of the fold operation is to insert a given binary operator f between every pair of elements in a given list. 
  
  Since f is a binary operator, we need a starting element that serves as the initial second input to f. *)

Example foldexample5 : 
  fold (fun l n => length (filter even l) + n) [[1]] 0 = 0.
Proof. simpl. reflexivity. Qed.
(** count the even elements inside a list. *)

(** ** Functions that Construct Functions ** **)
(** We really mean the function which can return function. *)
Definition constfun {X : Type} (x : X) : nat -> X :=
  fun (k : nat) => x.

Definition ftrue := constfun true.

Check ftrue.
Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

Check plus.

Definition plus3 := plus 3.
Check plus3 : nat -> nat.

Example test_plus3 : plus3 4 = 7.
Proof. reflexivity. Qed.
Example test_plus3' : doit3times plus3 0 = 9.
Proof. reflexivity. Qed.
Example test_plus3'' : doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.

Check @fold.
(** fold is filter works on the list. *)

(** What happening here is called *partial application*.
  That's because the type constructor -> is right-associative. *)

(** * Additional Exercises * **)
Module Exercises.

Definition fold_length {X : Type} (l : list X) : nat := fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
  intros X l.
  induction l as [| h t].
  + simpl. unfold fold_length. simpl. reflexivity.
  + simpl. rewrite <- IHt. unfold fold_length. simpl. reflexivity. 
Qed.
  (* unfold tactic can inline the definition. *)

Check @fold.
Check @cons.

Definition fold_map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  fold (fun x => cons (f x)) l [].

Theorem fold_map_correct: forall X Y (l : list X) (f : X -> Y),
  map f l = fold_map f l.
Proof.
  intros X Y l f.
  induction l as [| h t].
  + simpl. unfold fold_map. simpl. reflexivity.
  + simpl. rewrite -> IHt. unfold fold_map. simpl. reflexivity.
Qed.

(** X -> Y -> Z is right associate.
  (X * Y) -> Z can't be applied partially.
  
  Converting from (X * Y) -> Z to X -> Y -> Z is called currying,
  in honor of the logician Haskell Curry.
  
  Converting from X -> Y -> Z to (X * Y) -> Z is called uncurrying. *)

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z := f (fst p) (snd p).

Example test_map1': map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type) (f : X -> Y -> Z) x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros X Y Z f x y.
  unfold prod_curry.
  unfold prod_uncurry.
  simpl.
  reflexivity.
Qed.

Theorem curry_uncurry : forall (X Y Z : Type) (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros X Y Z f p.
  unfold prod_uncurry.
  unfold prod_curry.
  destruct p.
  simpl.
  reflexivity.
Qed.
End Exercises.
