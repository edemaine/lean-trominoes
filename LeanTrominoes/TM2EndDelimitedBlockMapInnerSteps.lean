/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2EndDelimitedBlockMapBoundarySteps

/-! # Inner-machine steps of the end-delimited compiler map -/

noncomputable section

namespace LeanTrominoes
namespace TM2EndDelimitedBlockMap

open Computability Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

/-- Once the reversed block has been transferred, control enters the inner
machine at its main label. -/
theorem step_prepare_nil
    {Input Output Source Target : Type}
    [Fintype Source] [Fintype Target]
    [Inhabited Source] [Inhabited Target]
    {encodeInput : Input → List Source}
    {encodeOutput : Output → List Target}
    {function : Input → Output}
    (inner : TM2ComputableInPolyTime encodeInput encodeOutput function)
    (isEnd : Source → Bool)
    (input : List Source)
    (innerContents : ∀ stack, List (inner.tm.Γ stack))
    (outputReverse : List Target) :
    (machine inner isEnd).step
        (prepareCfg inner.tm Source Target input [] innerContents
          outputReverse) =
      some (liftInnerCfg inner.tm Source Target input outputReverse
        ⟨some inner.tm.main, inner.tm.initialState, innerContents⟩) := by
  simp [FinTM2.step, TM2.step, machine, program, prepareCfg,
    liftInnerCfg, initialState, stackContents, setSource, sourceIsNone,
    setInnerState]

/-- Embedded inner statements commute exactly with configuration lifting. -/
theorem embedInnerStatement_stepAux
    (inner : FinTM2) (Source Target : Type)
    (statement : TM2.Stmt inner.Γ inner.Λ inner.σ)
    (input : List Source) (outputReverse : List Target)
    (state : inner.σ)
    (innerContents : ∀ stack, List (inner.Γ stack)) :
    TM2.stepAux (embedInnerStatement inner Source Target statement)
        ⟨state, none, none, true⟩
        (stackContents inner Source Target input [] innerContents
          outputReverse []) =
      liftInnerCfg inner Source Target input outputReverse
        (TM2.stepAux statement state innerContents) := by
  induction statement generalizing state innerContents with
  | push stack write next induction =>
      simp only [embedInnerStatement, TM2.stepAux]
      rw [update_stacks_inner]
      exact induction state _
  | peek stack read next induction =>
      simp only [embedInnerStatement, TM2.stepAux, setInnerState,
        stackContents]
      exact induction _ _
  | pop stack read next induction =>
      simp only [embedInnerStatement, TM2.stepAux, setInnerState,
        stackContents]
      rw [update_stacks_inner]
      exact induction _ _
  | load update next induction =>
      simp only [embedInnerStatement, TM2.stepAux, setInnerState]
      exact induction _ _
  | branch test yes no yesInduction noInduction =>
      simp only [embedInnerStatement, TM2.stepAux]
      cases test state
      · exact noInduction _ _
      · exact yesInduction _ _
  | goto target => rfl
  | halt => rfl

/-- Every live step of the inner machine is reproduced exactly by its
embedded copy while the surrounding input and accumulated output stay fixed.
-/
theorem liftInner_step
    {Input Output Source Target : Type}
    [Fintype Source] [Fintype Target]
    [Inhabited Source] [Inhabited Target]
    {encodeInput : Input → List Source}
    {encodeOutput : Output → List Target}
    {function : Input → Output}
    (inner : TM2ComputableInPolyTime encodeInput encodeOutput function)
    (isEnd : Source → Bool)
    (input : List Source) (outputReverse : List Target)
    {before after : inner.tm.Cfg}
    (step : inner.tm.step before = some after) :
    (machine inner isEnd).step
        (liftInnerCfg inner.tm Source Target input outputReverse before) =
      some (liftInnerCfg inner.tm Source Target input outputReverse after) := by
  rcases before with ⟨label, state, innerContents⟩
  cases label with
  | none => simp [FinTM2.step, TM2.step] at step
  | some label =>
      simp only [FinTM2.step, TM2.step] at step
      cases step
      simp only [FinTM2.step, TM2.step, liftInnerCfg, machine, program]
      exact congrArg some
        (embedInnerStatement_stepAux inner.tm Source Target
          (inner.tm.m label) input outputReverse state innerContents)

end TM2EndDelimitedBlockMap
end LeanTrominoes
