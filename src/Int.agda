module Int where

open import Data.Char
open import Data.List
open import Data.String
open import Function
open import Show

postulate
  Int : Set
  primShow : Int → List Char

{-# COMPILE GHC Int = type Int #-}
{-# COMPILE GHC primShow = show #-}

instance IntShow : Show Int
IntShow = fromHaskell primShow
