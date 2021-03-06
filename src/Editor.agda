module Editor where

open import Agda.Builtin.FromNat
open import BasicIO
open import Data.Bool
open import Data.Char
open import Data.List hiding (_++_)
open import Data.String
open import Data.Unit
open import Function
open import Int
open import Terminal

readTimeout : Int
readTimeout = 0

readMinChars : Int
readMinChars = 1

attrUpdates : TerminalAttributes → TerminalAttributes
attrUpdates =
  (flip withoutMode processInput)
  ∘ (flip withoutMode enableEcho)
  ∘ (flip withTime readTimeout)
  ∘ (flip withMinInput readMinChars)

handleInput : String → IO Bool
handleInput "q" = return false
handleInput cs = termWrite cs >>= const (return true)

parsePath : List (List Char) → IO (List Char)
parsePath (path ∷ []) = return path
parsePath _ = fail (toList "Exactly one file path argument required")

{-# NON_TERMINATING #-}
mainLoop : IO ⊤
mainLoop = do
  input ← termRead
  continue ← handleInput input
  if continue then mainLoop else return tt

setupAndRun : IO ⊤
setupAndRun = do
  args ← getArgs
  path ← parsePath args
  bracket
    (termWrite (hideCursor ++ altScreenEnable) >> return tt)
    (const (termWrite (altScreenDisable ++ showCursor)))
    (const mainLoop)

main : IO ⊤
main = withUpdatedAttributes attrUpdates setupAndRun
