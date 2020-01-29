
Load List. Load Bool.

Inductive suit : Type :=
  | heart
  | diamond
  | spade
  | club.

Inductive val : Type :=
  | ace
  | king
  | queen
  | jack
  | num (n: nat).

Inductive card : Type :=
  | c (s: suit) (v: val).

Definition check_num (x: nat) : bool :=
  if (x <? 11)
  then if (1 <? x)
       then true
       else false
  else false.

Compute check_num 0.
Compute check_num 1.
Compute check_num 2.
Compute check_num 10.
Compute check_num 11.

Definition is_valid_card (x: card) : bool :=
 match x with
  | c s ace => true
  | c s king => true
  | c s queen => true
  | c s jack => true
  | c s (num n) => 
        if check_num n
        then true
        else false
 end.

Definition is_valid_card2 (x: card) : bool :=
 match x with
  | c s ace => true
  | c s king => true
  | c s queen => true
  | c s jack => true
  | c s (num n) => 
        if check_num n
        then true
        else false
 end.

Check (ace, king).
Check (ace, 1).


Compute is_valid_card (c heart ace).
Compute is_valid_card (c heart king).
Compute is_valid_card (c heart queen).
Compute is_valid_card (c heart jack).
Compute is_valid_card (c heart (num 10)).
Compute is_valid_card (c heart (num 9)).
Compute is_valid_card (c heart (num 11)).
Compute is_valid_card (c heart (num 1)).


Check (c heart ace).
Check (c heart (num 2)).

Check (ace::king::[]).
Check [c heart ace; c diamond king; c spade queen].



