
Require Import Arith.
Load List. 
Open Scope list_scope.


Fixpoint search
  (l : Datatypes.list nat) (n: nat) : bool := 
  match l with 
   | [ ] => false
   | hd :: tl => 
      if (n =? hd)
      then true
      else search tl n
  end.


Compute search [1;3;6;8] 5.

Compute length [1;2;3].


Compute head [2;4;6].

Compute tail [3;6;9].


Compute app [1;2] [3;4].

Compute [1;2] ++ [3;4].


Compute 1::[2;3;5;7].

Compute rev [9;7;5;3;1].


Compute nth 0 [2;5;7;9].

Compute nth 4 [2;5;7;9].


Compute map (Nat.mul 3) [1;2;3].


