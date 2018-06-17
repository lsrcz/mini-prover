Theorem induction_on_dependent_term : forall (n:nat)(m:nat)(e:eq nat m n), eq nat n m.
Proof.
intros. 
induction e.
reflexivity.
Qed.
Print induction_on_dependent_term.


Definition sillyfun2 (m:nat) : bool :=
  match m as m0 in nat return bool with
  | O => false
  | S n => false
  end.


Theorem sillyfun2_false: forall (n:nat) (f:eq nat (S n) n) (g:eq (eq nat (S n) n) f f), 
eq bool (sillyfun2 (plus n (S n))) false.
Proof.  
  intros.
  unfold sillyfun2.
  destruct (plus n (S n)). 
  reflexivity. 
  reflexivity.
Qed.
Print sillyfun2_false.


Theorem false_to_all : forall (P:Type)(f:False), P.
Proof.
intros.
destruct f. 
Qed.
Print false_to_all.


Theorem two_is_even : ex nat (fun (n:nat) => eq nat (S (S O)) (plus n n)).
Proof.
exists (S O).
reflexivity.
Qed.
Print two_is_even.


Theorem plus_n_O : forall (n:nat), eq nat n (plus n O).
Proof.
intros.
induction n.
reflexivity.
simpl.
rewrite <- e.
reflexivity.
Qed.
Print plus_n_O.


Theorem show_apply : forall (n:nat) (f:nat -> nat -> nat) : nat.
Proof.
intros.
apply f.
exact O.
exact O.
Qed.
Print show_apply.


Theorem left_right_split : or (or False (and (eq nat O O) (eq nat O O))) False.
Proof.
left.
right.
split.
reflexivity.
reflexivity.
Qed.
Print left_right_split.


Definition addTwo (n:nat) : nat := S (S n).


Theorem unfoldtest : eq nat (addTwo O) (S (S O)).
Proof.
unfold addTwo.
reflexivity.
Qed.
Print unfoldtest.


Theorem error_hypothesis_leads_to_False : forall (n:nat) (x:not (eq nat (S n) (S n))), False.
Proof.
intros.
apply x.
reflexivity.
Qed.
Print error_hypothesis_leads_to_False.
