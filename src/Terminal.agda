module Terminal where

open import Agda.Builtin.Word
open import BasicIO
open import Data.Bool
open import Data.Char hiding (show)
open import Data.List hiding (_++_)
open import Data.String hiding (show)
open import Data.Unit
open import ByteCount
open import Int
open import Function
open import Show

{-# FOREIGN GHC import Control.Exception #-}
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
  Fd : Set
  TerminalAttributes : Set

  bracket : {A B C : Set} → IO A → (A → IO B) → (A → IO C) → IO C
  fst : {A B : Set} → (A , B) → A
  snd : {A B : Set} → (A , B) → B

  stdInput : Fd
  stdOutput : Fd
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
{-# COMPILE GHC Fd = type Fd #-}
{-# COMPILE GHC TerminalAttributes = type TerminalAttributes #-}

{-# COMPILE GHC bracket = \ _ _ _ -> bracket #-}
{-# COMPILE GHC fst = \ _ _ -> fst #-}
{-# COMPILE GHC snd = \ _ _ -> snd #-}

{-# COMPILE GHC stdInput = stdInput #-}
{-# COMPILE GHC stdOutput = stdOutput #-}
{-# COMPILE GHC getTerminalAttributes = getTerminalAttributes #-}
{-# COMPILE GHC setTerminalAttributes = setTerminalAttributes #-}
{-# COMPILE GHC withoutMode = withoutMode #-}
{-# COMPILE GHC inputTime = inputTime #-}
{-# COMPILE GHC withTime = withTime #-}
{-# COMPILE GHC minInput = minInput #-}
{-# COMPILE GHC withMinInput = withMinInput #-}
{-# COMPILE GHC fdRead = fdRead #-}
{-# COMPILE GHC fdWrite = fdWrite #-}

clearScreen : String
clearScreen = "\^[[2J"

showCursor : String
showCursor = "\^[[?25h"

hideCursor : String
hideCursor = "\^[[?25l"

altScreenEnable : String
altScreenEnable = "\^[[?1049h"

altScreenDisable : String
altScreenDisable = "\^[[?1049l"

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

readMaxChars : ByteCount
readMaxChars = mkCSize (primWord64FromNat 1024)

termRead : IO String
termRead = fdRead stdInput readMaxChars >>= (return ∘ fromList ∘ fst)

termWrite : String → IO ByteCount
termWrite = fdWrite stdOutput ∘ toList

printAttrs : TerminalAttributes → IO ⊤
printAttrs attrs =
  do _ ← termWrite (formatField "inputTime" (inputTime attrs))
     _ ← termWrite (formatField "minInput" (minInput attrs))
     return tt
  where
    formatField : String → Int → String
    formatField name value = name ++ " = " ++ show value ++ "\n"
