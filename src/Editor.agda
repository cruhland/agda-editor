module Editor where

open import BasicIO
open import Data.Bool
open import Data.Char hiding (show)
open import Data.List hiding (_++_)
open import Data.String hiding (show)
open import Data.Unit
open import Function
open import Int
open import Show
open import Terminal

{-# FOREIGN GHC import Control.Exception #-}
{-# FOREIGN GHC import System.Exit #-}
{-# FOREIGN GHC import System.Posix.IO #-}
{-# FOREIGN GHC import System.Posix.Types #-}

{-# FOREIGN GHC
readTimeout :: Int
readTimeout = 0

readMinChars :: Int
readMinChars = 1

readMaxChars :: ByteCount
readMaxChars = 1024
#-}

postulate
  bracket : {A B C : Set} → IO A → (A → IO B) → (A → IO C) → IO C
  exitFailure : IO ⊤
  exitSuccess : IO ⊤

  stdInput : Fd
  stdOutput : Fd
  readTimeout : Int
  readMinChars : Int
  readMaxChars : ByteCount

{-# COMPILE GHC bracket = \ _ _ _ -> bracket #-}
{-# COMPILE GHC exitFailure = exitFailure #-}
{-# COMPILE GHC exitSuccess = exitSuccess #-}

{-# COMPILE GHC stdInput = stdInput #-}
{-# COMPILE GHC stdOutput = stdOutput #-}
{-# COMPILE GHC readTimeout = readTimeout #-}
{-# COMPILE GHC readMinChars = readMinChars #-}
{-# COMPILE GHC readMaxChars = readMaxChars #-}

setAttrs : TerminalAttributes → IO ⊤
setAttrs attrs = setTerminalAttributes stdOutput attrs immediately

attrUpdates : TerminalAttributes → TerminalAttributes
attrUpdates =
  (flip withoutMode processInput)
  ∘ (flip withoutMode enableEcho)
  ∘ (flip withTime readTimeout)
  ∘ (flip withMinInput readMinChars)

formatField : String → Int → List Char
formatField name value = toList (name ++ " = " ++ show value ++ "\n")

printAttrs : TerminalAttributes → IO ⊤
printAttrs attrs = do
  _ ← fdWrite stdOutput (formatField "inputTime" (inputTime attrs))
  _ ← fdWrite stdOutput (formatField "minInput" (minInput attrs))
  return tt

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

setupAndRun : TerminalAttributes → IO ⊤
setupAndRun attrs = do
  _ ← setAttrs (attrUpdates attrs)
  _ ← fdWrite stdOutput (toList "\^[[2J")
  mainLoop

main : IO ⊤
main = do
  isTty ← queryTerminal stdOutput
  _ ← if isTty then return tt else exitFailure
  bracket (getTerminalAttributes stdOutput) setAttrs setupAndRun
