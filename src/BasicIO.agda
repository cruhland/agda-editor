module BasicIO where

open import Agda.Builtin.IO public
open import Data.Char
open import Data.List

{-# FOREIGN GHC import Control.Exception #-}
{-# FOREIGN GHC import System.Environment #-}

-- This is easier than using the IO functions in the standard library,
-- but it's technically not as type-safe. And it bypasses the
-- termination checker.
postulate
  return : {A : Set} → A → IO A
  _>>_ : {A B : Set} → IO A → IO B → IO B
  _>>=_ : {A B : Set} → IO A → (A → IO B) → IO B
  fail : {A : Set} → List Char → IO A
  bracket : {A B C : Set} → IO A → (A → IO B) → (A → IO C) → IO C
  getArgs : IO (List (List Char))

{-# COMPILE GHC return = \_ -> return #-}
{-# COMPILE GHC _>>_ = \_ _ -> (>>) #-}
{-# COMPILE GHC _>>=_ = \_ _ -> (>>=) #-}
{-# COMPILE GHC fail = \_ -> fail #-}
{-# COMPILE GHC bracket = \ _ _ _ -> bracket #-}
{-# COMPILE GHC getArgs = getArgs #-}
