module Show where

open import Data.Char hiding (show)
open import Data.List
open import Data.String hiding (show)
open import Function

record Show (A : Set) : Set where
  field
    show : A → String

open Show {{...}} public

fromHaskell : {A : Set} → (A → List Char) → Show A
fromHaskell primShow = record { show = fromList ∘ primShow }
