/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2EndDelimitedBlockMapOutputSteps

/-! # Cleanup-phase steps of the end-delimited compiler map -/

noncomputable section

namespace LeanTrominoes
namespace TM2EndDelimitedBlockMap

open Computability Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

theorem step_drainOutput_nil
    {Input Output Source Target : Type}
    [Fintype Source] [Fintype Target]
    [Inhabited Source] [Inhabited Target]
    {encodeInput : Input → List Source}
    {encodeOutput : Output → List Target}
    {function : Input → Output}
    (inner : TM2ComputableInPolyTime encodeInput encodeOutput function)
    (isEnd : Source → Bool)
    (input : List Source) (innerState : inner.tm.σ)
    (innerContents : ∀ stack, List (inner.tm.Γ stack))
    (outputReverse : List Target)
    (outputEq : innerContents inner.tm.k₁ = []) :
    (machine inner isEnd).step
        (drainOutputCfg inner.tm Source Target input innerState
          innerContents outputReverse) =
      some (cleanupCfg inner.tm Source Target ⟨0, by omega⟩ input
        innerContents outputReverse) := by
  simp [FinTM2.step, TM2.step, machine, program, drainOutputCfg,
    cleanupCfg, initialState, stackContents, setTarget, targetIsNone,
    outputEq]
  rw [show Function.update innerContents inner.tm.k₁ [] =
    innerContents by rw [← outputEq, Function.update_eq_self]]

theorem step_cleanup_some_cons
    {Input Output Source Target : Type}
    [Fintype Source] [Fintype Target]
    [Inhabited Source] [Inhabited Target]
    {encodeInput : Input → List Source}
    {encodeOutput : Output → List Target}
    {function : Input → Output}
    (inner : TM2ComputableInPolyTime encodeInput encodeOutput function)
    (isEnd : Source → Bool)
    (position : Fin (Fintype.card inner.tm.K + 1))
    (stack : inner.tm.K)
    (input : List Source)
    (innerContents : ∀ target, List (inner.tm.Γ target))
    (symbol : inner.tm.Γ stack) (tail : List (inner.tm.Γ stack))
    (outputReverse : List Target)
    (selected : cleanupStack inner.tm position = some stack)
    (contentsEq : innerContents stack = symbol :: tail) :
    (machine inner isEnd).step
        (cleanupCfg inner.tm Source Target position input innerContents
          outputReverse) =
      some (cleanupCfg inner.tm Source Target position input
        (Function.update innerContents stack tail) outputReverse) := by
  simp [FinTM2.step, TM2.step, machine, program, cleanupCfg,
    initialState, stackContents, setEmpty, selected, contentsEq]

theorem step_cleanup_some_nil
    {Input Output Source Target : Type}
    [Fintype Source] [Fintype Target]
    [Inhabited Source] [Inhabited Target]
    {encodeInput : Input → List Source}
    {encodeOutput : Output → List Target}
    {function : Input → Output}
    (inner : TM2ComputableInPolyTime encodeInput encodeOutput function)
    (isEnd : Source → Bool)
    (position : Fin (Fintype.card inner.tm.K + 1))
    (stack : inner.tm.K)
    (input : List Source)
    (innerContents : ∀ target, List (inner.tm.Γ target))
    (outputReverse : List Target)
    (selected : cleanupStack inner.tm position = some stack)
    (contentsEq : innerContents stack = []) :
    (machine inner isEnd).step
        (cleanupCfg inner.tm Source Target position input innerContents
          outputReverse) =
      some (cleanupCfg inner.tm Source Target
        (nextCleanupPosition inner.tm position) input innerContents
        outputReverse) := by
  simp [FinTM2.step, TM2.step, machine, program, cleanupCfg,
    initialState, stackContents, setEmpty, selected, contentsEq]
  rw [show Function.update innerContents stack [] = innerContents by
    rw [← contentsEq, Function.update_eq_self]]

theorem step_cleanup_none
    {Input Output Source Target : Type}
    [Fintype Source] [Fintype Target]
    [Inhabited Source] [Inhabited Target]
    {encodeInput : Input → List Source}
    {encodeOutput : Output → List Target}
    {function : Input → Output}
    (inner : TM2ComputableInPolyTime encodeInput encodeOutput function)
    (isEnd : Source → Bool)
    (position : Fin (Fintype.card inner.tm.K + 1))
    (input : List Source)
    (innerContents : ∀ stack, List (inner.tm.Γ stack))
    (outputReverse : List Target)
    (finished : cleanupStack inner.tm position = none) :
    (machine inner isEnd).step
        (cleanupCfg inner.tm Source Target position input innerContents
          outputReverse) =
      some (collectCfg inner.tm Source Target input [] innerContents
        outputReverse) := by
  simp [FinTM2.step, TM2.step, machine, program, cleanupCfg,
    collectCfg, initialState, finished]

end TM2EndDelimitedBlockMap
end LeanTrominoes
