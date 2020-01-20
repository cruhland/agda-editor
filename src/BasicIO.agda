module BasicIO where

open import Agda.Builtin.IO public

{-# FOREIGN GHC import Control.Exception #-}

-- This is easier than using the IO functions in the standard library,
-- but it's technically not as type-safe. And it bypasses the
-- termination checker.
postulate
  return : ∀ {A : Set} → A → IO A
  _>>_ : ∀ {A B : Set} → IO A → IO B → IO B
  _>>=_ : ∀ {A B : Set} → IO A → (A → IO B) → IO B
  bracket : {A B C : Set} → IO A → (A → IO B) → (A → IO C) → IO C

{-# COMPILE GHC return = \_ -> return #-}
{-# COMPILE GHC _>>_ = \_ _ -> (>>) #-}
{-# COMPILE GHC _>>=_ = \_ _ -> (>>=) #-}
{-# COMPILE GHC bracket = \ _ _ _ -> bracket #-}
