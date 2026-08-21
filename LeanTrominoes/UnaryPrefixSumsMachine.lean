/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.UnaryFieldEncoderMachine

/-! # Streaming prefix sums of unary fields -/

namespace LeanTrominoes

open Computability StateTransition Turing

namespace UnaryPrefixSumsMachine

abbrev Symbol := UnaryFieldEncoderMachine.Symbol

inductive Stack
  | input
  | sum
  | sumRestore
  | outputReverse
  | output
  deriving DecidableEq, Fintype

inductive Label
  | readField
  | copySum
  | restoreSum
  | consumeSaved
  | scanField
  | reverseOutput
  deriving Fintype

/-- The saved input symbol and whether the most recent auxiliary pop succeeded. -/
abbrev State := Option Symbol × Bool

abbrev Alphabet : Stack → Type
  | _ => Symbol

def setSaved (_ : State) (symbol : Option Symbol) : State :=
  (symbol, false)

def setPresence (state : State) (symbol : Option Symbol) : State :=
  (state.1, symbol.isSome)

def clearPresence (state : State) : State :=
  (state.1, false)

def clearState (_ : State) : State :=
  (none, false)

def savedSymbol : State → Symbol
  | (some symbol, _) => symbol
  | _ => default

def savedIsNone : State → Bool
  | (none, _) => true
  | _ => false

def savedIsUnit : State → Bool
  | (some .unit, _) => true
  | _ => false

def poppedIsNone (state : State) : Bool := !state.2

def program : Label → TM2.Stmt Alphabet Label State
  | .readField =>
      .pop .input setSaved
        (.branch savedIsNone
          (.goto fun _ => .reverseOutput)
          (.goto fun _ => .copySum))
  | .copySum =>
      .pop .sum setPresence
        (.branch poppedIsNone
          (.push .outputReverse (fun _ => .delimiter)
            (.goto fun _ => .restoreSum))
          (.push .sumRestore (fun _ => .unit)
            (.push .outputReverse (fun _ => .unit)
              (.load clearPresence (.goto fun _ => .copySum)))))
  | .restoreSum =>
      .pop .sumRestore setPresence
        (.branch poppedIsNone
          (.goto fun _ => .consumeSaved)
          (.push .sum (fun _ => .unit)
            (.load clearPresence (.goto fun _ => .restoreSum))))
  | .consumeSaved =>
      .branch savedIsUnit
        (.push .sum (fun _ => .unit)
          (.load clearState (.goto fun _ => .scanField)))
        (.load clearState (.goto fun _ => .readField))
  | .scanField =>
      .pop .input setSaved
        (.branch savedIsNone
          (.goto fun _ => .reverseOutput)
          (.branch savedIsUnit
            (.push .sum (fun _ => .unit)
              (.load clearState (.goto fun _ => .scanField)))
            (.load clearState (.goto fun _ => .readField))))
  | .reverseOutput =>
      .pop .outputReverse setSaved
        (.branch savedIsNone
          .halt
          (.push .output savedSymbol
            (.load clearState (.goto fun _ => .reverseOutput))))

abbrev machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label
  main := .readField
  σ := State
  initialState := (none, false)
  m := program

structure TapeData where
  input : List Symbol
  sum : List Symbol
  sumRestore : List Symbol
  outputReverse : List Symbol
  output : List Symbol

def tapes (data : TapeData) : ∀ stack, List (Alphabet stack)
  | .input => data.input
  | .sum => data.sum
  | .sumRestore => data.sumRestore
  | .outputReverse => data.outputReverse
  | .output => data.output

def cfg (label : Label) (state : State) (data : TapeData) :
    TM2.Cfg Alphabet Label State :=
  ⟨some label, state, tapes data⟩

def readFieldCfg (data : TapeData) := cfg .readField (none, false) data

def copySumCfg (saved : Symbol) (data : TapeData) :=
  cfg .copySum (some saved, false) data

def restoreSumCfg (saved : Symbol) (data : TapeData) :=
  cfg .restoreSum (some saved, false) data

def consumeSavedCfg (saved : Symbol) (data : TapeData) :=
  cfg .consumeSaved (some saved, false) data

def scanFieldCfg (data : TapeData) := cfg .scanField (none, false) data

def reverseOutputCfg (data : TapeData) :=
  cfg .reverseOutput (none, false) data

def haltDataCfg (data : TapeData) : TM2.Cfg Alphabet Label State :=
  ⟨none, (none, false), tapes data⟩

end UnaryPrefixSumsMachine
end LeanTrominoes
