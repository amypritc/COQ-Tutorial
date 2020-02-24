
Load Arith.

Fixpoint sumsq (n: nat) : nat := 
match n with
| O => 0
| S p => (n * n) + (sumsq p)
end.



Require FunInd.
Load FunInd.

Functional Scheme sumsq_ind := 
  Induction for sumsq Sort Prop.


Theorem Thm_sumsq :
forall n:nat,
6 * sumsq n = n * (n + 1) * (2 * n + 1).
Proof.
intros n.
functional induction (sumsq n) 
  using sumsq_ind.
- trivial.
- rewrite Nat.mul_add_distr_l 
    with (m := S p * S p) (n := 6) 
         (p := sumsq p).
(* rewrite Nat.mul_add_distr_l 
    with (m := S p * S p). *)
  rewrite -> IHn0.
  ring.
Qed.

Search Nat.mul.

