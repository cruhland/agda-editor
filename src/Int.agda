module Int where

open import Agda.Builtin.FromNat
open import Agda.Builtin.FromNeg
open import Data.Char hiding (fromNat)
open import Data.Integer hiding (_≤_; suc)
open import Data.Integer.Literals
open import Data.List
open import Data.Nat hiding (_≤_)
open import Data.String
open import Data.Unit hiding (_≤_)
open import Function
open import Show

postulate
  Int : Set
  primShow : Int → List Char
  primFromInteger : ℤ → Int
  primToInteger : Int → ℤ
  primMinBound : Int
  primMaxBound : Int

{-# COMPILE GHC Int = type Int #-}
{-# COMPILE GHC primShow = show #-}
{-# COMPILE GHC primFromInteger = fromInteger #-}
{-# COMPILE GHC primToInteger = toInteger #-}
{-# COMPILE GHC primMinBound = minBound #-}
{-# COMPILE GHC primMaxBound = maxBound #-}

instance ShowInt : Show Int
ShowInt = fromHaskell primShow

instance Numberℤ : Number ℤ
Numberℤ = number

-- Its values can be automatically derived as instance arguments, but
-- is otherwise identical to the standard library version
data _ℕ≤_ : ℕ → ℕ → Set where
  instance z≤n : ∀ {n}                 → zero  ℕ≤ n
  instance s≤s : ∀ {m n} {{m≤n : m ℕ≤ n}} → suc m ℕ≤ suc n

-- Its values can be automatically derived as instance arguments, but
-- is otherwise identical to the standard library version
data _≤_ : ℤ → ℤ → Set where
  instance -≤- : {m n : ℕ} → {{n≤m : n ℕ≤ m}} → -[1+ m ] ≤ -[1+ n ]
  instance -≤+ : {m n : ℕ} → (-[1+ m ]) ≤ (+ n)
  instance +≤+ : {m n : ℕ} → {{m≤n : m ℕ≤ n}} → (+ m) ≤ (+ n)

-- Use a literal for the bound so that Agda can automatically check
-- the constraints for fromNat and fromNeg. Value taken from
-- https://hackage.haskell.org/package/base-4.12.0.0/docs/Prelude.html#t:Int
maxBound : ℤ
maxBound = 536870911

-- Use the actual bound in compiled code
{-# COMPILE GHC maxBound = toInteger (maxBound :: Int) #-}

instance NumberInt : Number Int
NumberInt = record { Constraint = Constraint ; fromNat = fromNatInt }
  where
    Constraint : ℕ → Set
    Constraint n = (+ n) ≤ maxBound

    fromNatInt : ∀ n → {{_ : Constraint n}} → Int
    fromNatInt n = primFromInteger (+ n)
