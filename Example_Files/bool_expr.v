
Require Import Arith.
Load Bool.

Definition lt (n m : nat) : bool:=
  if (n <? m)
  then true
  else false.
Notation "n < m" := (lt n m).

Compute lt 2 5.
Compute lt 8 1.
Compute lt 6 6.
Compute 2 < 5.
Compute 8 < 1.
Compute 6 < 6.



Definition gt (n m : nat) : bool:=
  if (m <? n)
  then true
  else false.
Notation "n > m" := (gt n m).

Compute gt 2 5.
Compute gt 8 1.
Compute gt 6 6.
Compute 2 > 5.
Compute 8 > 1.
Compute 6 > 6.



Definition eq (n m : nat) : bool:=
  if (n =? m)
  then true
  else false.
Notation "n = m" := (eq n m).

Compute eq 3 3.
Compute eq 4 7.
Compute 3 = 3.
Compute 4 = 7.


Definition lteq (n m : nat) : bool:=
  if n <=? m
  then true
  else false.
Notation "n <= m" := (lteq n m).

Compute lteq 2 5.
Compute lteq 8 1.
Compute lteq 6 6.
Compute 2 <= 5.
Compute 8 <= 1.
Compute 6 <= 6.



Definition gteq (n m : nat) : bool:=
  if (m <=? n)
  then true
  else false.
Notation "n >= m" := (gteq n m).


Compute gteq 2 5.
Compute gteq 8 1.
Compute gteq 6 6.
Compute 2 >= 5.
Compute 8 >= 1.
Compute 6 >= 6.





