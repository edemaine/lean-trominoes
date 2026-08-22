/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2EndDelimitedBlockMapBoundarySteps

/-! # Output-phase steps of the end-delimited compiler map -/

noncomputable section

namespace LeanTrominoes
namespace TM2EndDelimitedBlockMap

open Computability Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

theorem step_drainOutput_cons
    {Input Output Source Target : Type}
    [Fintype Source] [Fintype Target]
    [Inhabited Source] [Inhabited Target]
    {encodeInput : Input → List Source}
    {encodeOutput : Output → List Target}
    {function : Input → Output}
    (inner : TM2ComputableInPolyTime encodeInput encodeOutput function)
    (isEnd : Source → Bool)
    (symbol : inner.tm.Γ inner.tm.k₁) (input : List Source)
    (innerState : inner.tm.σ)
    (innerContents : ∀ stack, List (inner.tm.Γ stack))
    (tail : List (inner.tm.Γ inner.tm.k₁))
    (outputReverse : List Target)
    (outputEq : innerContents inner.tm.k₁ = symbol :: tail) :
    (machine inner isEnd).step
        (drainOutputCfg inner.tm Source Target input innerState
          innerContents outputReverse) =
      some (pushOutputCfg inner.tm Source Target
        (inner.outputAlphabet symbol) input innerState
        (Function.update innerContents inner.tm.k₁ tail)
        outputReverse) := by
  simp [FinTM2.step, TM2.step, machine, program, drainOutputCfg,
    pushOutputCfg, stackContents, setTarget, targetIsNone, targetValue,
    outputEq]

theorem step_pushOutput
    {Input Output Source Target : Type}
    [Fintype Source] [Fintype Target]
    [Inhabited Source] [Inhabited Target]
    {encodeInput : Input → List Source}
    {encodeOutput : Output → List Target}
    {function : Input → Output}
    (inner : TM2ComputableInPolyTime encodeInput encodeOutput function)
    (isEnd : Source → Bool)
    (symbol : Target) (input : List Source)
    (innerState : inner.tm.σ)
    (innerContents : ∀ stack, List (inner.tm.Γ stack))
    (outputReverse : List Target) :
    (machine inner isEnd).step
        (pushOutputCfg inner.tm Source Target symbol input innerState
          innerContents outputReverse) =
      some (drainOutputCfg inner.tm Source Target input innerState
        innerContents (symbol :: outputReverse)) := by
  simp [FinTM2.step, TM2.step, machine, program, pushOutputCfg,
    drainOutputCfg, stackContents, setTarget]

theorem step_discard_cons
    {Input Output Source Target : Type}
    [Fintype Source] [Fintype Target]
    [Inhabited Source] [Inhabited Target]
    {encodeInput : Input → List Source}
    {encodeOutput : Output → List Target}
    {function : Input → Output}
    (inner : TM2ComputableInPolyTime encodeInput encodeOutput function)
    (isEnd : Source → Bool)
    (symbol : Source) (blockReverse : List Source)
    (outputReverse : List Target) :
    (machine inner isEnd).step
        (discardCfg inner.tm Source Target (symbol :: blockReverse)
          outputReverse) =
      some (discardCfg inner.tm Source Target blockReverse outputReverse) := by
  simp [FinTM2.step, TM2.step, machine, program, discardCfg,
    initialState, stackContents, setEmpty]

theorem step_discard_nil
    {Input Output Source Target : Type}
    [Fintype Source] [Fintype Target]
    [Inhabited Source] [Inhabited Target]
    {encodeInput : Input → List Source}
    {encodeOutput : Output → List Target}
    {function : Input → Output}
    (inner : TM2ComputableInPolyTime encodeInput encodeOutput function)
    (isEnd : Source → Bool) (outputReverse : List Target) :
    (machine inner isEnd).step
        (discardCfg inner.tm Source Target [] outputReverse) =
      some (reverseCfg inner.tm Source Target outputReverse []) := by
  simp [FinTM2.step, TM2.step, machine, program, discardCfg,
    reverseCfg, initialState, stackContents, setEmpty]

theorem step_reverse_cons
    {Input Output Source Target : Type}
    [Fintype Source] [Fintype Target]
    [Inhabited Source] [Inhabited Target]
    {encodeInput : Input → List Source}
    {encodeOutput : Output → List Target}
    {function : Input → Output}
    (inner : TM2ComputableInPolyTime encodeInput encodeOutput function)
    (isEnd : Source → Bool)
    (symbol : Target) (outputReverse output : List Target) :
    (machine inner isEnd).step
        (reverseCfg inner.tm Source Target (symbol :: outputReverse) output) =
      some (pushFinalCfg inner.tm Source Target symbol outputReverse output) := by
  simp [FinTM2.step, TM2.step, machine, program, reverseCfg,
    pushFinalCfg, initialState, stackContents, setTarget, targetIsNone,
    targetValue]

theorem step_pushFinal
    {Input Output Source Target : Type}
    [Fintype Source] [Fintype Target]
    [Inhabited Source] [Inhabited Target]
    {encodeInput : Input → List Source}
    {encodeOutput : Output → List Target}
    {function : Input → Output}
    (inner : TM2ComputableInPolyTime encodeInput encodeOutput function)
    (isEnd : Source → Bool)
    (symbol : Target) (outputReverse output : List Target) :
    (machine inner isEnd).step
        (pushFinalCfg inner.tm Source Target symbol outputReverse output) =
      some (reverseCfg inner.tm Source Target outputReverse
        (symbol :: output)) := by
  simp [FinTM2.step, TM2.step, machine, program, pushFinalCfg,
    reverseCfg, initialState, stackContents, setTarget]

theorem step_reverse_nil
    {Input Output Source Target : Type}
    [Fintype Source] [Fintype Target]
    [Inhabited Source] [Inhabited Target]
    {encodeInput : Input → List Source}
    {encodeOutput : Output → List Target}
    {function : Input → Output}
    (inner : TM2ComputableInPolyTime encodeInput encodeOutput function)
    (isEnd : Source → Bool) (output : List Target) :
    (machine inner isEnd).step
        (reverseCfg inner.tm Source Target [] output) =
      some (haltCfg inner.tm Source Target output) := by
  simp [FinTM2.step, TM2.step, machine, program, reverseCfg,
    haltCfg, initialState, stackContents, setTarget, targetIsNone]

end TM2EndDelimitedBlockMap
end LeanTrominoes
