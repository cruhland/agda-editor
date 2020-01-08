module Editor where

open import BasicIO
open import Data.Bool
open import Data.Char
open import Data.List
open import Data.String hiding (_++_)
open import Data.Unit

{-# FOREIGN GHC import Control.Exception #-}
{-# FOREIGN GHC import Data.Int #-}
{-# FOREIGN GHC import System.Exit #-}
{-# FOREIGN GHC import System.Posix.IO #-}
{-# FOREIGN GHC import System.Posix.Terminal #-}
{-# FOREIGN GHC import System.Posix.Types #-}

{-# FOREIGN GHC data ShowDict a = Show a => ShowDict #-}
postulate
  Show : Set → Set
{-# COMPILE GHC Show = type ShowDict #-}

postulate
  haskell-show : {a : Set} {{_ : Show a}} → a → List Char
{-# COMPILE GHC haskell-show = \ _ ShowDict -> show #-}

postulate
  Int : Set
  instance ShowInt : Show Int
{-# COMPILE GHC Int = type Int #-}
{-# COMPILE GHC ShowInt = ShowDict #-}

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

  stdOutput : Fd
  queryTerminal : Fd → IO Bool
  getTerminalAttributes : Fd → IO TerminalAttributes
  setTerminalAttributes : Fd → TerminalAttributes → TerminalState → IO ⊤
  withoutMode : TerminalAttributes → TerminalMode → TerminalAttributes
  inputTime : TerminalAttributes → Int
  minInput : TerminalAttributes → Int
  fdWrite : Fd → List Char → IO ByteCount

{-# COMPILE GHC ByteCount = type ByteCount #-}
{-# COMPILE GHC Fd = type Fd #-}
{-# COMPILE GHC TerminalAttributes = type TerminalAttributes #-}

{-# COMPILE GHC bracket = \ _ _ _ a r x -> bracket a r x #-}
{-# COMPILE GHC exitFailure = exitFailure #-}
{-# COMPILE GHC exitSuccess = exitSuccess #-}

{-# COMPILE GHC stdOutput = stdOutput #-}
{-# COMPILE GHC queryTerminal = queryTerminal #-}
{-# COMPILE GHC getTerminalAttributes = getTerminalAttributes #-}
{-# COMPILE GHC setTerminalAttributes = setTerminalAttributes #-}
{-# COMPILE GHC withoutMode = withoutMode #-}
{-# COMPILE GHC inputTime = inputTime #-}
{-# COMPILE GHC minInput = minInput #-}
{-# COMPILE GHC fdWrite = fdWrite #-}

setAttrs : TerminalAttributes → IO ⊤
setAttrs attrs = setTerminalAttributes stdOutput attrs immediately

clearScreen : TerminalAttributes → IO ⊤
clearScreen attrs = do
  _ ← setAttrs (withoutMode attrs processInput)
  _ ← fdWrite stdOutput (toList "\^[[2J")
  return tt

formatField : String → Int → List Char
formatField name value =
  toList name ++ toList " = " ++ haskell-show value ++ toList "\n"

printAttrs : TerminalAttributes → IO ⊤
printAttrs attrs = do
  _ ← fdWrite stdOutput (formatField "inputTime" (inputTime attrs))
  _ ← fdWrite stdOutput (formatField "minInput" (minInput attrs))
  return tt

setupAndRun : TerminalAttributes → IO ⊤
setupAndRun attrs = do
  _ ← clearScreen attrs
  printAttrs attrs

main : IO ⊤
main = do
  isTty ← queryTerminal stdOutput
  _ ← if isTty then return tt else exitFailure
  bracket (getTerminalAttributes stdOutput) setAttrs setupAndRun
