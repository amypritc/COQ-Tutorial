
(* This is a comment *)
(* (* 
You must have an equal number of openings and closings
*) *)



(* Pattern matching runnable example *)
Check match true with 
| true => false
| false => true
end.



(* Lists *)
(* NOTE: using both "Load List." and defining an inductive list type will throw an error.
Uncommenting the next comment block will allow you to run those.
*)
(*
Inductive natlist : Type := 
| nil 
| cons (n : nat) (l : natlist).

Check nil.

Check cons 1 nil.

Check cons (1) (cons 2 nil).
*)
Load List.

Check 1::2::3::4::5::6::7::8::9::0::[]. 

Check [ 1; 2; 3; 4; 5; 6; 7; 8; 9; 0 ].

Check nil.

Check cons 1 nil.

Check cons (1) (cons 2 nil).



(* Tuples *)
Check (1, 2, 3).




(* Boolean Expressions *)
Require Import Arith. 
Load Bool.

Compute 1 <? 2. 

Compute 1 =? 2. 

Compute 1 <=? 2. 




(* Option Types *)
(* The option type is pre-defined - no need to define it on your own. 
If you uncomment the definition below, it will cause issues with proper recognition of option types. 

Inductive option (A : Type ) : Type := 
| None : option A
| Some : A \u2212> option A
*)


Fixpoint at_n (n : nat) (l : Datatypes.list nat) : option nat := 
match l with
 | [ ] => None
 | hd::tl => if (n =? 0)
             then Some hd 
             else at_n (n - 1) tl
end.



