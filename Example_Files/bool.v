
Inductive bool :=
  | true
  | false.


Definition not (b:bool) : bool:=
  match b with
   | true => false
   | false => true
  end.

Definition and (b1 b2:bool) : bool:=
  match (b1, b2) with
   | (true, true) => true
   | (_, _) => false
  end.

Definition or (b1 b2:bool) : bool:=
  match (b1, b2) with
   | (false, false) => false
   | (_, _) => true
  end.


Definition xor (b1 b2:bool) : bool:=
  match (b1, b2) with
   | (true, false) => true
   | (false, true) => true
   | (_, _) => false
  end.



