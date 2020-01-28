
(* Inductive *)

Inductive bool : Set := 
  | true
  | false.


Inductive nat : Set := 
  | O : nat
  | S : nat -> nat.


Print nat.
Print nat_rect.
Print nat_ind.
Print nat_rec.


Inductive day: Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.


Inductive natlist: Type :=
  | nil 
  | cons (n:Datatypes.nat) (l:natlist).


(* 
  Polymorhpic definition of list.
  Commented out as not used elsewhere.
*)
(*
Inductive list (A:Set) : Set :=
  | nil : list A
  | cons : A -> list A -> list A.
*)





(* Definition *)

Definition x := 4.

Check x.

Definition next_weekday (d:day): day :=
  match d with
   | monday => tuesday
   | tuesday => wednesday
   | wednesday => thursday
   | thursday => friday
   | friday => monday
   | saturday => monday
   | sunday => monday
  end.

Definition plus2 n : nat :=
  match n with
   | O => S (S O)
   | _ => S (S n)
  end.

Compute plus2 O.

Definition plus2' (n:nat) : nat :=
  match n with
   | O => S (S O)
   | _ => S (S n)
  end.

Compute plus2' O.


Definition choose1 (b:bool) (n1:Datatypes.nat) (n2:Datatypes.nat) : Datatypes.nat := 
  match b with 
    | true => n1
    | false => n2
  end.

Compute choose1 true 2 5.
Compute choose1 false 2 5.

Definition choose1' b n1 n2 : Datatypes.nat := 
  match b with 
    | true => n1
    | false => n2
  end.

Compute choose1' true 2 5.
Compute choose1' false 2 5.






(* Notation *)

Notation "[]" := nil. 

Compute []. 

Notation "x :: xs" := (cons x xs). 

Compute 3::2::1::[]. 

Compute (cons 3 (cons 2 (cons 1 nil))). 






(* Fixpoint *)




(* Compute *)

Compute 2 + 4.

Compute plus 4 2.

Compute (mult 12 4) * 3.


