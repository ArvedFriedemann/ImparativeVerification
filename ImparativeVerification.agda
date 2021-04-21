module ImparativeVerification where

open import Agda.Primitive renaming (_⊔_ to _~U~_)

variable
  l l1 l2 l3 l4 : Level
  A B C K J L : Set l

data Bool : Set where
  true : Bool
  false : Bool

data _or_ (A B : Set l) : Set (lsuc l) where
  left : A -> A or B
  right : B -> A or B

data _===_ {l : Level} {A : Set l} (a : A) : A -> Set l where
  refl : a === a

record Eq (A : Set l) : Set (lsuc l) where
  field
    _==_ : A -> A -> Bool
open Eq {{...}} public

data <U> {l : Level} : Set l where
  unit : <U>

record Monad (M : Set l1 -> Set l2) : Set (lsuc (l1 ~U~ l2)) where
  field
    return : A -> M A
    _>>=_ : M A -> (A -> M B) -> M B
open Monad {{...}} public

data FreeMonad {l : Level} : (Set l) -> Set (lsuc l) where
  returnF : {A : Set l} -> A -> FreeMonad A
  _>>=F_ : {A : Set l} -> FreeMonad A -> (A -> FreeMonad B) -> FreeMonad B

instance
  FreeMonadMonad : Monad (FreeMonad {l})
  return {{FreeMonadMonad}} = returnF
  _>>=_ {{FreeMonadMonad}} = _>>=F_

record MonadMem (M : Set l1 -> Set l2) (V : Set l1 -> Set l1) : Set (lsuc (l1 ~U~ l2)) where
  field
    new : M (V A)
    read : V A -> M A
    write : V A -> A -> M <U>
open MonadMem {{...}} public
{-}
record MemProperties {M : Set l1 -> Set l2} {V : Set l1 -> Set l1} {{_ : MonadMem {l1} {l2} M V}} : Set (lsuc (l1 ~U~ l2)) where
  field
    read-after-write : write v a >>= noWritesTo v >>= read v === return a
-}

data noWritesTo {M : Set l1 -> Set l2} {{i : Monad M}} (v : A) (m : M B) : Set (lsuc (l1 ~U~ l2)) where
  ret-prop : {b : B} -> (m === return b) -> noWritesTo v m
  bind-prop : (m1 : M C) (m2 : C -> M B) -> (m === (m1 >>= m2)) ->
    noWritesTo v m1 ->
    ((c : C) -> noWritesTo v (m2 c)) ->
    noWritesTo v m

data writesTo {M : Set l1 -> Set l2} {{i : Monad M}} (v : A) (m : M B) : Set (lsuc (l1 ~U~ l2)) where
  todo : writesTo v m



nwt : {{_ : Eq K}} -> (v : K) -> (m : FreeMonad A) -> ((noWritesTo v m) or (writesTo v m))
nwt v (returnF x) = left (ret-prop refl)
nwt v (x >>=F y) with nwt v x
... | left x1  = left (bind-prop x y refl x1 {!!})
... | _ = right todo




module TestProof {M : Set l1 -> Set l2} {V : Set l1 -> Set l1}  where
  test : {{mon : Monad M}} {{_ : MonadMem M V}} -> {a : A} {v : V A} -> noWritesTo {{mon}} v (return a >>= \x -> return a)
  test {{_}} {{_}} {a} {v} = bind-prop (return a) (\ _ -> return a) refl (ret-prop refl) (\ _ -> ret-prop refl)
  test2 : A -> FreeMonad A
  test2 a = return a

{-}
data AnswerSet M S where
  retSet : (a : A) -> AnswerSet (return a) [a]
  bind : (m1 : _) -> (m2 : _) -> AnswerSet m1 s' ->
          AnswerSet (m1 >>= m2) (Union (for s' (\s -> m2 s)))
-}



--
