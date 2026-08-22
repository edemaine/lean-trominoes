/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2OutputLength

/-! # Data for repeatedly running a compiler on end-delimited blocks -/

noncomputable section

namespace LeanTrominoes
namespace TM2EndDelimitedBlockMap

open Computability StateTransition Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

/-- Split after every symbol satisfying `isEnd`; a final unterminated suffix
is ignored. -/
def blocksAux {Source : Type} (isEnd : Source → Bool) :
    List Source → List Source → List (List Source)
  | _, [] => []
  | reverseBlock, symbol :: input =>
      let nextReverse := symbol :: reverseBlock
      if isEnd symbol then
        nextReverse.reverse :: blocksAux isEnd [] input
      else
        blocksAux isEnd nextReverse input

def blocks {Source : Type}
    (isEnd : Source → Bool) (input : List Source) :
    List (List Source) :=
  blocksAux isEnd [] input

/-- Concatenate the inner function's output on every complete block. -/
def mappedOutput {Source Target : Type}
    (isEnd : Source → Bool) (function : List Source → List Target)
    (input : List Source) : List Target :=
  (blocks isEnd input).flatMap function

inductive Stack (Inner : Type)
  | input
  | blockReverse
  | inner (stack : Inner)
  | outputReverse
  | output
  deriving DecidableEq, Fintype

inductive Label (InnerLabel Source : Type) (innerStackCount : Nat)
  | collect
  | pushBlock (symbol : Source)
  | prepareBlock
  | pushInner (symbol : Source)
  | inner (label : InnerLabel)
  | drainInnerOutput
  | pushOutput (symbol : Source)
  | cleanup (position : Fin (innerStackCount + 1))
  | discardPartial
  | reverseOutput
  | pushFinal (symbol : Source)
  deriving Fintype

structure State (InnerState Source Target : Type) where
  innerState : InnerState
  source : Option Source
  target : Option Target
  empty : Bool
  deriving Fintype

abbrev Alphabet (inner : FinTM2) (Source Target : Type) :
    Stack inner.K → Type
  | .input | .blockReverse => Source
  | .inner stack => inner.Γ stack
  | .outputReverse | .output => Target

abbrev CombinedLabel (inner : FinTM2) (Source Target : Type) :=
  Label inner.Λ (Source ⊕ Target) (Fintype.card inner.K)

abbrev CombinedState (inner : FinTM2) (Source Target : Type) :=
  State inner.σ Source Target

def initialState (inner : FinTM2) (Source Target : Type) :
    CombinedState inner Source Target :=
  ⟨inner.initialState, none, none, true⟩

def setInnerState (inner : FinTM2) (Source Target : Type)
    (state : CombinedState inner Source Target)
    (innerState : inner.σ) : CombinedState inner Source Target :=
  { state with innerState := innerState }

def setSource (inner : FinTM2) (Source Target : Type)
    (state : CombinedState inner Source Target)
    (source : Option Source) : CombinedState inner Source Target :=
  { state with source := source }

def setTarget (inner : FinTM2) (Source Target : Type)
    (state : CombinedState inner Source Target)
    (target : Option Target) : CombinedState inner Source Target :=
  { state with target := target }

def setEmpty (inner : FinTM2) (Source Target : Type)
    (state : CombinedState inner Source Target)
    (empty : Bool) : CombinedState inner Source Target :=
  { state with empty := empty }

def sourceIsNone (inner : FinTM2) (Source Target : Type)
    (state : CombinedState inner Source Target) : Bool :=
  state.source.isNone

def targetIsNone (inner : FinTM2) (Source Target : Type)
    (state : CombinedState inner Source Target) : Bool :=
  state.target.isNone

def sourceValue {Source : Type} [Inhabited Source]
    (inner : FinTM2) (Target : Type)
    (state : CombinedState inner Source Target) : Source :=
  state.source.getD default

def targetValue {Target : Type} [Inhabited Target]
    (inner : FinTM2) (Source : Type)
    (state : CombinedState inner Source Target) : Target :=
  state.target.getD default

def cleanupStack (inner : FinTM2)
    (position : Fin (Fintype.card inner.K + 1)) : Option inner.K :=
  if positionFits : position.val < Fintype.card inner.K then
    some ((Fintype.equivFin inner.K).symm
      ⟨position.val, positionFits⟩)
  else
    none

def nextCleanupPosition (inner : FinTM2)
    (position : Fin (Fintype.card inner.K + 1)) :
    Fin (Fintype.card inner.K + 1) :=
  ⟨min (position.val + 1) (Fintype.card inner.K), by omega⟩

/-- Embed an inner statement.  Inner halt begins output collection instead of
halting the surrounding block loop. -/
def embedInnerStatement
    (inner : FinTM2) (Source Target : Type) :
    TM2.Stmt inner.Γ inner.Λ inner.σ →
      TM2.Stmt (Alphabet inner Source Target)
        (CombinedLabel inner Source Target)
        (CombinedState inner Source Target)
  | .push stack write next =>
      .push (.inner stack)
        (fun state => write state.innerState)
        (embedInnerStatement inner Source Target next)
  | .peek stack read next =>
      .peek (.inner stack)
        (fun state symbol =>
          setInnerState inner Source Target state
            (read state.innerState symbol))
        (embedInnerStatement inner Source Target next)
  | .pop stack read next =>
      .pop (.inner stack)
        (fun state symbol =>
          setInnerState inner Source Target state
            (read state.innerState symbol))
        (embedInnerStatement inner Source Target next)
  | .load update next =>
      .load (fun state =>
        setInnerState inner Source Target state
          (update state.innerState))
        (embedInnerStatement inner Source Target next)
  | .branch test yes no =>
      .branch (fun state => test state.innerState)
        (embedInnerStatement inner Source Target yes)
        (embedInnerStatement inner Source Target no)
  | .goto target =>
      .goto fun state => .inner (target state.innerState)
  | .halt =>
      .load (fun state => setTarget inner Source Target state none)
        (.goto fun _ => .drainInnerOutput)

def program
    {Input Output Source Target : Type}
    [Fintype Source] [Fintype Target]
    [Inhabited Source] [Inhabited Target]
    {encodeInput : Input → List Source}
    {encodeOutput : Output → List Target}
    {function : Input → Output}
    (inner : TM2ComputableInPolyTime encodeInput encodeOutput function)
    (isEnd : Source → Bool) :
    CombinedLabel inner.tm Source Target →
      TM2.Stmt (Alphabet inner.tm Source Target)
        (CombinedLabel inner.tm Source Target)
        (CombinedState inner.tm Source Target)
  | .collect =>
      .pop .input (setSource inner.tm Source Target)
        (.branch (sourceIsNone inner.tm Source Target)
          (.goto fun _ => .discardPartial)
          (.goto fun state => .pushBlock
            (.inl (sourceValue inner.tm Target state))))
  | .pushBlock (.inl symbol) =>
      .push .blockReverse (fun _ => symbol)
        (.load (fun state => setSource inner.tm Source Target state none)
          (.branch (fun _ => isEnd symbol)
            (.goto fun _ => .prepareBlock)
            (.goto fun _ => .collect)))
  | .pushBlock (.inr _) => .goto fun _ => .collect
  | .prepareBlock =>
      .pop .blockReverse (setSource inner.tm Source Target)
        (.branch (sourceIsNone inner.tm Source Target)
          (.load (fun state =>
            setInnerState inner.tm Source Target state inner.tm.initialState)
            (.goto fun _ => .inner inner.tm.main))
          (.goto fun state => .pushInner
            (.inl (sourceValue inner.tm Target state))))
  | .pushInner (.inl symbol) =>
      .push (.inner inner.tm.k₀)
        (fun _ => inner.inputAlphabet.invFun symbol)
        (.load (fun state => setSource inner.tm Source Target state none)
          (.goto fun _ => .prepareBlock))
  | .pushInner (.inr _) => .goto fun _ => .prepareBlock
  | .inner label =>
      embedInnerStatement inner.tm Source Target (inner.tm.m label)
  | .drainInnerOutput =>
      .pop (.inner inner.tm.k₁)
        (fun state symbol =>
          setTarget inner.tm Source Target state
            (symbol.map inner.outputAlphabet))
        (.branch (targetIsNone inner.tm Source Target)
          (.load (fun _ => initialState inner.tm Source Target)
            (.goto fun _ => .cleanup ⟨0, by omega⟩))
          (.goto fun state => .pushOutput
            (.inr (targetValue inner.tm Source state))))
  | .pushOutput (.inr symbol) =>
      .push .outputReverse (fun _ => symbol)
        (.load (fun state => setTarget inner.tm Source Target state none)
          (.goto fun _ => .drainInnerOutput))
  | .pushOutput (.inl _) => .goto fun _ => .drainInnerOutput
  | .cleanup position =>
      match cleanupStack inner.tm position with
      | none =>
          .load (fun _ => initialState inner.tm Source Target)
            (.goto fun _ => .collect)
      | some stack =>
          .pop (.inner stack)
            (fun state symbol =>
              setEmpty inner.tm Source Target state symbol.isNone)
            (.branch (fun state => state.empty)
              (.goto fun _ => .cleanup
                (nextCleanupPosition inner.tm position))
              (.load (fun _ => initialState inner.tm Source Target)
                (.goto fun _ => .cleanup position)))
  | .discardPartial =>
      .pop .blockReverse
        (fun state symbol =>
          setEmpty inner.tm Source Target state symbol.isNone)
        (.branch (fun state => state.empty)
          (.goto fun _ => .reverseOutput)
          (.load (fun _ => initialState inner.tm Source Target)
            (.goto fun _ => .discardPartial)))
  | .reverseOutput =>
      .pop .outputReverse (setTarget inner.tm Source Target)
        (.branch (targetIsNone inner.tm Source Target)
          (.load (fun _ => initialState inner.tm Source Target) .halt)
          (.goto fun state => .pushFinal
            (.inr (targetValue inner.tm Source state))))
  | .pushFinal (.inr symbol) =>
      .push .output (fun _ => symbol)
        (.load (fun state => setTarget inner.tm Source Target state none)
          (.goto fun _ => .reverseOutput))
  | .pushFinal (.inl _) => .goto fun _ => .reverseOutput

def machine
    {Input Output Source Target : Type}
    [Fintype Source] [Fintype Target]
    [Inhabited Source] [Inhabited Target]
    {encodeInput : Input → List Source}
    {encodeOutput : Output → List Target}
    {function : Input → Output}
    (inner : TM2ComputableInPolyTime encodeInput encodeOutput function)
    (isEnd : Source → Bool) : FinTM2 where
  K := Stack inner.tm.K
  kDecidableEq := instDecidableEqStack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet inner.tm Source Target
  Γk₀Fin := inferInstance
  Λ := CombinedLabel inner.tm Source Target
  main := .collect
  σ := CombinedState inner.tm Source Target
  initialState := initialState inner.tm Source Target
  m := program inner isEnd

end TM2EndDelimitedBlockMap
end LeanTrominoes
