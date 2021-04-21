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
    read-after-write : write v a >>= noWritesTo v >>= read v === return a


data noWritesTo (v : A) where
  ret-prop : (return <U> : _) -> noWritesTo v
  bind-prop : (m1 : M A) (m2 : A -> M B) -> 
    noWritesTo v m1 ->
    (\(a : A) -> AnswerSet m2 s -> a in s -> noWritesTo v (m2 a)) -> noWritesTo (m1 >>= m2)

data AnswerSet M S where
  retSet : (a : A) -> AnswerSet (return a) [a]
  bind : (m1 : _) -> (m2 : _) -> AnswerSet m1 s' ->
          AnswerSet (m1 >>= m2) (Union (for s' (\s -> m2 s)))




--
