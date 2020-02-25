
Load Arith.

Fixpoint fact (n:nat) := 
  match n with 
    | O => 1
    | S m => n * fact(m)
  end. 



