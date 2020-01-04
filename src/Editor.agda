module Editor where

open import BasicIO
open import Data.Bool
open import Data.Unit

{-# FOREIGN GHC import System.Exit #-}
{-# FOREIGN GHC import System.Posix.IO #-}
{-# FOREIGN GHC import System.Posix.Terminal #-}
{-# FOREIGN GHC import System.Posix.Types #-}

postulate
  Fd : Set
  stdInput : Fd
  queryTerminal : Fd → IO Bool
  exitSuccess : IO ⊤
  exitFailure : IO ⊤

{-# COMPILE GHC Fd = type Fd #-}
{-# COMPILE GHC stdInput = stdInput #-}
{-# COMPILE GHC queryTerminal = queryTerminal #-}
{-# COMPILE GHC exitSuccess = exitSuccess #-}
{-# COMPILE GHC exitFailure = exitFailure #-}

main : IO ⊤
main = do
  isTty ← queryTerminal stdInput
  if isTty then exitSuccess else exitFailure
