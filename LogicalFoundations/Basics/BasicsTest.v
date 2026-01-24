(* * Exercise : nandb * *)

Inductive bool : Type :=
  | true
  | false.

Definition nandb (b1 : bool) (b2 : bool) : bool :=
  if b1 then
    if b2 then false
    else true
  else true.

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

(* * Exercise : andb3 * *)

Definition andb3 (b1 : bool) (b2 : bool) (b3 : bool) :=
  if b1 then 
    if b2 then b3
    else false
  else false.

Example test_andb31: (andb3 true true true) = true.

Proof. simpl. reflexivity. Qed.

Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

(* * Exercise : factorial * *)

Fixpoint factorial (n : nat) : nat :=
  match n with
  | 0 => S 0
  | S n' => mult n (factorial n')
  end.

Compute (factorial 4).

Example test_factorial1 : (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_factorial2 : (factorial 5) = (mult 10 12).
Proof. reflexivity. Qed.

(* * Exercise : ltb * *)

Fixpoint leb (n m : nat) : bool :=
  match n with
  | 0 => true
  | S n' => match m with
            | 0 => false
            | S m' => leb n' m'
            end
  end.

Definition ltb (n m : nat) : bool :=
  match m with
  | 0 => match n with
         | 0 => false
         | S n' => leb n' 0
         end
  | S m' => leb n m'
  end.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Compute (ltb 2 2).
Compute (ltb 0 2).
Compute (ltb 4 6).

(* * Exercise : plus_id_exercise * *)

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intro n.
  intro m.
  intro o.
  intro H1.
  intro H2.
  rewrite -> H1.
  (* -> in rewrite means using left side of the equality to replace left side of the goal *)
  rewrite <- H2.
  reflexivity. 
Qed.

Theorem mult_n_1 : forall p : nat, p * 1 = p.
Proof.
  intro p.
  rewrite <- mult_n_Sm.
  (* rewrite <- is use right side of the equation to rewrite left side of the equation in the goal*)
  rewrite <- mult_n_O.
  simpl.
  reflexivity.
Qed.

