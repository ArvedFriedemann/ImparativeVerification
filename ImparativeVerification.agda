module ImparativeVerification where

open import Agda.Primitive renaming (_⊔_ to _~U~_)


data Nat : Set where
  zero : Nat
  succ : Nat -> Nat

_+_ : Nat -> Nat -> Nat
zero + b = b
succ a + b = succ (a + b)

data <U> {l : Level} : Set l where
  unit : <U>

variable
  l l1 l2 l3 l4 : Level
  A B C : Set l

record MonadMem (M : Set l1 -> Set l2) (V : Set l1 -> Set l1) : Set (lsuc (l1 ~U~ l2)) where
  field
    new : M (V A)
    read : V A -> M A
    write : V A -> A -> M <U>

record MemProperties {M : Set l1 -> Set l2} {V : Set l1 -> Set l1} {{_ : MonadMem {l1} {l2} M V}} : Set (lsuc (l1 ~U~ l2)) where
  field
    test : Set






--
