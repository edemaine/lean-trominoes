/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2ForkMachineEmbeddedStatements

/-! # Live component steps inside the fork machine -/

noncomputable section

namespace LeanTrominoes
namespace TM2ForkMachine

open Turing

/-- Every live step of the first component is reproduced exactly by the fork
machine while its second input copy remains fixed. -/
theorem liftFirst_step
    {Input FirstOutput SecondOutput InputSymbol FirstSymbol SecondSymbol : Type}
    [Fintype InputSymbol] [Fintype FirstSymbol] [Fintype SecondSymbol]
    [Inhabited InputSymbol] [Inhabited FirstSymbol]
    [Inhabited SecondSymbol]
    {encodeInput : Input → List InputSymbol}
    {encodeFirst : FirstOutput → List FirstSymbol}
    {encodeSecond : SecondOutput → List SecondSymbol}
    {firstFunction : Input → FirstOutput}
    {secondFunction : Input → SecondOutput}
    (first : TM2ComputableInPolyTime encodeInput encodeFirst firstFunction)
    (second : TM2ComputableInPolyTime encodeInput encodeSecond secondFunction)
    (secondContents : ∀ stack, List (second.tm.Γ stack))
    {before after : first.tm.Cfg}
    (step : first.tm.step before = some after) :
    (machine first second).step
        (liftFirstCfg first.tm second.tm
          InputSymbol FirstSymbol SecondSymbol secondContents before) =
      some (liftFirstCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol secondContents after) := by
  rcases before with ⟨label, state, firstContents⟩
  cases label with
  | none => simp [FinTM2.step, TM2.step] at step
  | some label =>
      simp only [FinTM2.step, TM2.step] at step
      cases step
      simp only [FinTM2.step, TM2.step, liftFirstCfg, machine, program]
      exact congrArg some
        (embedFirstStatement_stepAux first.tm second.tm
          InputSymbol FirstSymbol SecondSymbol
          (first.tm.m label) state firstContents secondContents)

/-- Every live step of the second component is reproduced exactly by the
fork machine while the completed first stacks remain fixed. -/
theorem liftSecond_step
    {Input FirstOutput SecondOutput InputSymbol FirstSymbol SecondSymbol : Type}
    [Fintype InputSymbol] [Fintype FirstSymbol] [Fintype SecondSymbol]
    [Inhabited InputSymbol] [Inhabited FirstSymbol]
    [Inhabited SecondSymbol]
    {encodeInput : Input → List InputSymbol}
    {encodeFirst : FirstOutput → List FirstSymbol}
    {encodeSecond : SecondOutput → List SecondSymbol}
    {firstFunction : Input → FirstOutput}
    {secondFunction : Input → SecondOutput}
    (first : TM2ComputableInPolyTime encodeInput encodeFirst firstFunction)
    (second : TM2ComputableInPolyTime encodeInput encodeSecond secondFunction)
    (firstContents : ∀ stack, List (first.tm.Γ stack))
    {before after : second.tm.Cfg}
    (step : second.tm.step before = some after) :
    (machine first second).step
        (liftSecondCfg first.tm second.tm
          InputSymbol FirstSymbol SecondSymbol firstContents before) =
      some (liftSecondCfg first.tm second.tm
        InputSymbol FirstSymbol SecondSymbol firstContents after) := by
  rcases before with ⟨label, state, secondContents⟩
  cases label with
  | none => simp [FinTM2.step, TM2.step] at step
  | some label =>
      simp only [FinTM2.step, TM2.step] at step
      cases step
      simp only [FinTM2.step, TM2.step, liftSecondCfg, machine, program]
      exact congrArg some
        (embedSecondStatement_stepAux first.tm second.tm
          InputSymbol FirstSymbol SecondSymbol
          (second.tm.m label) state firstContents secondContents)

end TM2ForkMachine
end LeanTrominoes
