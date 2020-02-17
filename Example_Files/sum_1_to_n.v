
Load Arith.


Fixpoint sum (n: nat) : nat := 
match n with
| O => 0
| S p => (S p) + (sum p)
end.


Require FunInd.
Load FunInd.


Functional Scheme sum_ind := 
  Induction for sum Sort Prop.

Print sum_ind.

Theorem Thm_sum :
forall n:nat,
2 * sum n = (1 + n) * n.
Proof.
intros n.
functional induction (sum n)
  using sum_ind.
- trivial.
- rewrite <- Nat.add_succ_comm.
  rewrite -> Nat.mul_add_distr_r.
  rewrite -> Nat.mul_add_distr_l.
  rewrite -> IHn0.
  simpl.
  rewrite -> Nat.mul_succ_r.
  rewrite Nat.add_comm with (n:= p*p).
  reflexivity.
Qed.


Theorem Thm_sum_simple :
forall n:nat,
2 * sum n = (1 + n) * n.
Proof.
intros n.
functional induction (sum n) 
  using sum_ind.
- trivial.
- rewrite -> Nat.mul_add_distr_l.
  rewrite -> IHn0.
  ring.
Qed.





