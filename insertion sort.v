Require Import Coq.Lists.List. 
Import ListNotations.
Inductive perm {A : Type} : list A -> list A -> Prop :=
| perm_nil : perm [] []
| perm_skip : forall (x : A) (l1 l2 : list A),
    perm l1 l2 -> perm (x :: l1) (x :: l2)
| perm_swap : forall (x y : A) (l : list A),
    perm (x :: y :: l) (y :: x :: l)
| perm_trans : forall (l1 l2 l3 : list A),
    perm l1 l2 -> perm l2 l3 -> perm l1 l3.
Fixpoint order (n m : nat) : bool := 
 match n,m with
  |0, _ => false
  |_,0 => true
  |S m,S n => order m n
 end.
Fixpoint insert (n : nat) (l : list nat) : list nat :=
  match l with
  | [] => [n]
  | h :: t => if (order n h) then n :: l else h :: insert n t
  end.
Fixpoint insertion_sort (l : list nat) : list nat :=
  match l with
  | [] => []
  | h :: t => insert h (insertion_sort t)
  end.
Fixpoint order_1 (n m : nat) : Prop := 
 match n,m with
  |0, _ => False
  |_,0 => True
  |S m,S n => order_1 m n
 end.
Definition head (m : list nat) : nat :=
    hd 0 m.
Fixpoint sorted (l : list nat) : Prop :=
  match l with
  | [] => True
  | [_] => True
  | x  :: t => (order_1 x (head l)) /\ sorted ( t)
  end.
Print list_ind.
Lemma insert_preserves_sortedness : forall n l,
   sorted (insert n l)-> sorted l.
Proof.
  induction l. 
  auto. 
   .




