module Pair where

postulate
  _,_ : Set → Set → Set
  fst : {A B : Set} → (A , B) → A
  snd : {A B : Set} → (A , B) → B

{-# COMPILE GHC _,_ = type (,) #-}
{-# COMPILE GHC fst = \ _ _ -> fst #-}
{-# COMPILE GHC snd = \ _ _ -> snd #-}
