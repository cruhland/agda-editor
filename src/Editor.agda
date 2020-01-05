module Editor where

open import BasicIO
open import Data.Bool
open import Data.Char
open import Data.List
open import Data.String
open import Data.Unit

{-# FOREIGN GHC import Control.Exception #-}
{-# FOREIGN GHC import System.Exit #-}
{-# FOREIGN GHC import System.Posix.IO #-}
{-# FOREIGN GHC import System.Posix.Terminal #-}
{-# FOREIGN GHC import System.Posix.Types #-}

data TerminalState : Set where
  immediately : TerminalState
  whenDrained : TerminalState
  whenFlushed : TerminalState

{-# COMPILE GHC TerminalState =
  data TerminalState (Immediately | WhenDrained | WhenFlushed)
#-}

data TerminalMode : Set where
  interruptOnBreak : TerminalMode
  mapCRtoLF : TerminalMode
  ignoreBreak : TerminalMode
  ignoreCR : TerminalMode
  ignoreParityErrors : TerminalMode
  mapLFtoCR : TerminalMode
  checkParity : TerminalMode
  stripHighBit : TerminalMode
  startStopInput : TerminalMode
  startStopOutput : TerminalMode
  markParityErrors : TerminalMode
  processOutput : TerminalMode
  localMode : TerminalMode
  readEnable : TerminalMode
  twoStopBits : TerminalMode
  hangupOnClose : TerminalMode
  enableParity : TerminalMode
  oddParity : TerminalMode
  enableEcho : TerminalMode
  echoErase : TerminalMode
  echoKill : TerminalMode
  echoLF : TerminalMode
  processInput : TerminalMode
  extendedFunctions : TerminalMode
  keyboardInterrupts : TerminalMode
  noFlushOnInterrupt : TerminalMode
  backgroundWriteInterrupt : TerminalMode

{-# COMPILE GHC TerminalMode =
  data TerminalMode
  ( InterruptOnBreak
  | MapCRtoLF
  | IgnoreBreak
  | IgnoreCR
  | IgnoreParityErrors
  | MapLFtoCR
  | CheckParity
  | StripHighBit
  | StartStopInput
  | StartStopOutput
  | MarkParityErrors
  | ProcessOutput
  | LocalMode
  | ReadEnable
  | TwoStopBits
  | HangupOnClose
  | EnableParity
  | OddParity
  | EnableEcho
  | EchoErase
  | EchoKill
  | EchoLF
  | ProcessInput
  | ExtendedFunctions
  | KeyboardInterrupts
  | NoFlushOnInterrupt
  | BackgroundWriteInterrupt
  )
#-}

postulate
  ByteCount : Set
  Fd : Set
  TerminalAttributes : Set

  bracket : {A B C : Set} → IO A → (A → IO B) → (A → IO C) → IO C
  exitFailure : IO ⊤
  exitSuccess : IO ⊤

  stdInput : Fd
  queryTerminal : Fd → IO Bool
  getTerminalAttributes : Fd → IO TerminalAttributes
  setTerminalAttributes : Fd → TerminalAttributes → TerminalState → IO ⊤
  withoutMode : TerminalAttributes → TerminalMode → TerminalAttributes
  fdWrite : Fd → List Char → IO ByteCount

{-# COMPILE GHC ByteCount = type ByteCount #-}
{-# COMPILE GHC Fd = type Fd #-}
{-# COMPILE GHC TerminalAttributes = type TerminalAttributes #-}

{-# COMPILE GHC bracket = \ _ _ _ a r x -> bracket a r x #-}
{-# COMPILE GHC exitFailure = exitFailure #-}
{-# COMPILE GHC exitSuccess = exitSuccess #-}

{-# COMPILE GHC stdInput = stdInput #-}
{-# COMPILE GHC queryTerminal = queryTerminal #-}
{-# COMPILE GHC getTerminalAttributes = getTerminalAttributes #-}
{-# COMPILE GHC setTerminalAttributes = setTerminalAttributes #-}
{-# COMPILE GHC withoutMode = withoutMode #-}
{-# COMPILE GHC fdWrite = fdWrite #-}

clearScreen : TerminalAttributes → IO ⊤
clearScreen attrs = do
  let rawModeAttrs = withoutMode attrs processInput
  _ ← setTerminalAttributes stdInput rawModeAttrs immediately
  _ ← fdWrite stdInput (toList "\^[[2J")
  return tt

main : IO ⊤
main = do
  isTty ← queryTerminal stdInput
  _ ← if isTty then return tt else exitFailure
  bracket
    (getTerminalAttributes stdInput)
    (λ attrs → setTerminalAttributes stdInput attrs immediately)
    clearScreen
