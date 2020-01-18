module ByteCount where

open import Agda.Builtin.Word

{-# FOREIGN GHC import Foreign.C.Types #-}

postulate
  CSize : Set
  mkCSize : Word64 → CSize

{-# COMPILE GHC CSize = type CSize #-}
{-# COMPILE GHC mkCSize = CSize #-}

ByteCount : Set
ByteCount = CSize
