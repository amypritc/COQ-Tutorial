
(* Note: 
   - Throwing errors when trying to prove over 
   general lists, so proving over lists of nats.
   - Some properties already defined in the List 
   library of Coq are included as commented out 
   Print statements. These can be uncommented to 
   see how they are defined. There is also a Search 
   statement commented out at the bottom - this will 
   show properties related to both the datatype 'list' 
   and the function 'rev'.
*)

Load List.


Lemma list_nil : 
forall (xs : Datatypes.list nat),
xs ++ [] = xs.
Proof.
intros xs.
induction xs.
- auto.
- simpl. 
  rewrite -> IHxs. 
  auto.
Qed.

(*
Print app_nil_l.
Print app_nil_r.
*)


Lemma list_assoc : 
forall (xs ys zs : Datatypes.list nat),
(xs ++ ys) ++ zs = xs ++ ys ++ zs.
Proof.
intros xs ys zs.
induction xs.
- auto.
- simpl.
  rewrite -> IHxs.
  auto.
Qed.

(*
Print app_assoc.
*)

Lemma rev_list : 
forall (xs ys : Datatypes.list nat),
rev (xs ++ ys) = (rev ys) ++ (rev xs).
Proof.
intros xs ys.
induction xs. 
- simpl. 
  rewrite -> list_nil.
  reflexivity.
- simpl. 
  rewrite -> IHxs.
  rewrite -> list_assoc.
  auto.
Qed.

(*
Print rev.
Print rev_app_distr.
*)


Lemma rev_rev : 
forall (xs : Datatypes.list nat),
rev (rev xs) = xs.
Proof.
intros xs.
induction xs.
- auto.
- simpl.
  rewrite -> rev_list.
  rewrite -> IHxs.
  auto.
Qed.


(* 
Search list rev. 
*)

