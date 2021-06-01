module ConstructorChoice where

open import Reflection
open import Data.List renaming (_∷_ to _::_)
import Data.Maybe as M
open import Level renaming (_⊔_ to _levelunion_; suc to lsuc)
open import Data.Nat renaming (ℕ to Nat; _≤_ to _<=_)
open import Agda.Builtin.Unit renaming (⊤ to T)

_!!_ : {A : Set} -> List A -> Nat -> M.Maybe A
[] !! n = M.nothing
(x :: xs) !! 0 = M.just x
(x :: xs) !! n = xs !! (pred n)

data Misc (A : Set) : Set where
    Unit : Misc A
    Single : A -> Misc A
    Double : A -> A -> Misc A

-- TODO: this has to be done as instances.
-- So something like record CountArgs, then instances for (a -> b) and for x (somehow?)
-- Then use that number to recurse on the below n times.
{-
constructTerm : Type -> Name -> Nat -> List (Arg Term) -> Term
constructTerm (a -> b) con n xs = lam visible (abs (show n) (getType b con (suc n) ((var n []) :: xs)))
constructTerm x con _ xs = def con (reverse xs)
-}

-- TODO: I think I need to do something with `args`, but I'm not sure.
withDef : Definition -> Nat -> List (Arg Term) -> Term -> TC T
withDef (data-type pars cs) n args hole =
    M.maybe (\nam -> getType nam >>=
        \type -> -- unify (getTerm type con 0 []) hole
            unify (con nam []) hole)
        (typeError [(strErr "Constructor number out of bounds.")])
        (cs !! n)
withDef _ _ _ _ = typeError [(strErr "Can't apply constructor of non-data type.")]

macro
    applyNthConstructor : Term -> Nat -> Term -> TC T
    applyNthConstructor (def f args) n hole = getDefinition f >>= \x -> withDef x n args hole
    applyNthConstructor _ _ _ = typeError [(strErr "Need to apply this to a definition.")]

test : Nat -> Misc Nat
test = applyNthConstructor (Misc Nat) 1