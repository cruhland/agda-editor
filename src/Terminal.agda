module Terminal where

open import BasicIO
open import Data.Bool
open import Data.Char
open import Data.List
open import Data.Unit
open import Int

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
  _,_ : Set → Set → Set
  ByteCount : Set
  Fd : Set
  TerminalAttributes : Set

  fst : {A B : Set} → (A , B) → A
  snd : {A B : Set} → (A , B) → B

  queryTerminal : Fd → IO Bool
  getTerminalAttributes : Fd → IO TerminalAttributes
  setTerminalAttributes : Fd → TerminalAttributes → TerminalState → IO ⊤
  withoutMode : TerminalAttributes → TerminalMode → TerminalAttributes
  inputTime : TerminalAttributes → Int
  withTime : TerminalAttributes → Int → TerminalAttributes
  minInput : TerminalAttributes → Int
  withMinInput : TerminalAttributes → Int → TerminalAttributes
  fdRead : Fd → ByteCount → IO (List Char , ByteCount)
  fdWrite : Fd → List Char → IO ByteCount

{-# COMPILE GHC _,_ = type (,) #-}
{-# COMPILE GHC ByteCount = type ByteCount #-}
{-# COMPILE GHC Fd = type Fd #-}
{-# COMPILE GHC TerminalAttributes = type TerminalAttributes #-}

{-# COMPILE GHC fst = \ _ _ -> fst #-}
{-# COMPILE GHC snd = \ _ _ -> snd #-}

{-# COMPILE GHC queryTerminal = queryTerminal #-}
{-# COMPILE GHC getTerminalAttributes = getTerminalAttributes #-}
{-# COMPILE GHC setTerminalAttributes = setTerminalAttributes #-}
{-# COMPILE GHC withoutMode = withoutMode #-}
{-# COMPILE GHC inputTime = inputTime #-}
{-# COMPILE GHC withTime = withTime #-}
{-# COMPILE GHC minInput = minInput #-}
{-# COMPILE GHC withMinInput = withMinInput #-}
{-# COMPILE GHC fdRead = fdRead #-}
{-# COMPILE GHC fdWrite = fdWrite #-}
