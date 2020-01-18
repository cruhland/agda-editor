module Editor where

open import Agda.Builtin.FromNat
open import Agda.Builtin.Word
open import BasicIO
open import Data.Bool
open import Data.Char hiding (show)
open import Data.List hiding (_++_)
open import Data.Nat
open import Data.Nat.Literals
open import Data.String hiding (show)
open import Data.Unit
open import ByteCount
open import Function
open import Int
open import Show
open import Terminal

{-# FOREIGN GHC import Control.Exception #-}
{-# FOREIGN GHC import System.Exit #-}
{-# FOREIGN GHC import System.Posix.IO #-}

readTimeout : Int
readTimeout = 0

readMinChars : Int
readMinChars = 1

instance numberℕ : Number ℕ
numberℕ = number

readMaxChars : ByteCount
readMaxChars = mkCSize (primWord64FromNat 1024)

postulate
  bracket : {A B C : Set} → IO A → (A → IO B) → (A → IO C) → IO C
  exitFailure : IO ⊤
  exitSuccess : IO ⊤

  stdInput : Fd
  stdOutput : Fd

{-# COMPILE GHC bracket = \ _ _ _ -> bracket #-}
{-# COMPILE GHC exitFailure = exitFailure #-}
{-# COMPILE GHC exitSuccess = exitSuccess #-}

{-# COMPILE GHC stdInput = stdInput #-}
{-# COMPILE GHC stdOutput = stdOutput #-}

formatField : String → Int → List Char
formatField name value = toList (name ++ " = " ++ show value ++ "\n")

printAttrs : TerminalAttributes → IO ⊤
printAttrs attrs = do
  _ ← fdWrite stdOutput (formatField "inputTime" (inputTime attrs))
  _ ← fdWrite stdOutput (formatField "minInput" (minInput attrs))
  return tt

withUpdatedAttributes :
  {A : Set} → (TerminalAttributes → TerminalAttributes) → IO A → IO A
withUpdatedAttributes {A} updateFn actions =
  bracket (getTerminalAttributes stdOutput) setAttrs updateAndRun
    where
      setAttrs : TerminalAttributes → IO ⊤
      setAttrs attrs = setTerminalAttributes stdOutput attrs immediately

      updateAndRun : TerminalAttributes → IO A
      updateAndRun attrs = do
        _ ← setAttrs (updateFn attrs)
        actions

attrUpdates : TerminalAttributes → TerminalAttributes
attrUpdates =
  (flip withoutMode processInput)
  ∘ (flip withoutMode enableEcho)
  ∘ (flip withTime readTimeout)
  ∘ (flip withMinInput readMinChars)

handleInput : String → IO Bool
handleInput "q" = return false
handleInput cs = do
  _ ← fdWrite stdOutput (toList cs)
  return true

{-# NON_TERMINATING #-}
mainLoop : IO ⊤
mainLoop = do
  textAndLength ← fdRead stdInput readMaxChars
  continue ← handleInput (fromList (fst textAndLength))
  if continue then mainLoop else return tt

setupAndRun : IO ⊤
setupAndRun = do
  _ ← fdWrite stdOutput (toList "\^[[2J")
  mainLoop

main : IO ⊤
main = do
  isTty ← queryTerminal stdOutput
  _ ← if isTty then return tt else exitFailure
  withUpdatedAttributes attrUpdates setupAndRun
