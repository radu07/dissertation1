Require Import List.
Set Implicit Arguments.
Fixpoint foldr (A B :Type)(f:A ->B->  B) (z:B) (xs: list A) :=

      match xs with
        | nil => z
        | cons x xs' => f x (foldr f z xs')
      end.
Definition orbool  (xs: list (bool)) : bool := foldr (orb ) false xs.
Definition anyl (A:Type)(p:A->bool)(xs:list A):bool := orbool( map p xs).
Definition elem (n:nat)(x:Fin n)(xs:list (Fin n)) :bool := anyl ( eqf x) xs.

Definition In_bool (n:nat) (x:Fin n)(xs: list (Fin n)) : bool := elem x xs.