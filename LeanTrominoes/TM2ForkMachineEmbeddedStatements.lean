/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2ForkMachineConfigurations

/-! # Exact embedded component statements for the fork machine -/

noncomputable section

namespace LeanTrominoes
namespace TM2ForkMachine

open Turing

/-- Embedded first-component statements commute with configuration lifting
while leaving the prepared second-component stacks unchanged. -/
theorem embedFirstStatement_stepAux
    (first second : FinTM2)
    (InputSymbol FirstSymbol SecondSymbol : Type)
    (statement : TM2.Stmt first.Γ first.Λ first.σ)
    (state : first.σ)
    (firstContents : ∀ stack, List (first.Γ stack))
    (secondContents : ∀ stack, List (second.Γ stack)) :
    TM2.stepAux
        (embedFirstStatement first second
          InputSymbol FirstSymbol SecondSymbol statement)
        (.first state)
        (componentStacks first second InputSymbol FirstSymbol SecondSymbol
          firstContents secondContents) =
      liftFirstCfg first second InputSymbol FirstSymbol SecondSymbol
        secondContents (TM2.stepAux statement state firstContents) := by
  induction statement generalizing state firstContents with
  | push stack write next induction =>
      simp only [embedFirstStatement, TM2.stepAux, firstState]
      rw [update_componentStacks_first]
      exact induction state _
  | peek stack read next induction =>
      simp only [embedFirstStatement, TM2.stepAux, firstState,
        componentStacks]
      exact induction _ _
  | pop stack read next induction =>
      simp only [embedFirstStatement, TM2.stepAux, firstState,
        componentStacks]
      rw [update_componentStacks_first]
      exact induction _ _
  | load update next induction =>
      simp only [embedFirstStatement, TM2.stepAux, firstState]
      exact induction _ _
  | branch test yes no yesInduction noInduction =>
      simp only [embedFirstStatement, TM2.stepAux, firstState]
      cases test state
      · exact noInduction _ _
      · exact yesInduction _ _
  | goto target => rfl
  | halt => rfl

/-- Embedded second-component statements commute with configuration lifting
while leaving the completed first-component stacks unchanged. -/
theorem embedSecondStatement_stepAux
    (first second : FinTM2)
    (InputSymbol FirstSymbol SecondSymbol : Type)
    (statement : TM2.Stmt second.Γ second.Λ second.σ)
    (state : second.σ)
    (firstContents : ∀ stack, List (first.Γ stack))
    (secondContents : ∀ stack, List (second.Γ stack)) :
    TM2.stepAux
        (embedSecondStatement first second
          InputSymbol FirstSymbol SecondSymbol statement)
        (.second state)
        (componentStacks first second InputSymbol FirstSymbol SecondSymbol
          firstContents secondContents) =
      liftSecondCfg first second InputSymbol FirstSymbol SecondSymbol
        firstContents (TM2.stepAux statement state secondContents) := by
  induction statement generalizing state secondContents with
  | push stack write next induction =>
      simp only [embedSecondStatement, TM2.stepAux, secondState]
      rw [update_componentStacks_second]
      exact induction state _
  | peek stack read next induction =>
      simp only [embedSecondStatement, TM2.stepAux, secondState,
        componentStacks]
      exact induction _ _
  | pop stack read next induction =>
      simp only [embedSecondStatement, TM2.stepAux, secondState,
        componentStacks]
      rw [update_componentStacks_second]
      exact induction _ _
  | load update next induction =>
      simp only [embedSecondStatement, TM2.stepAux, secondState]
      exact induction _ _
  | branch test yes no yesInduction noInduction =>
      simp only [embedSecondStatement, TM2.stepAux, secondState]
      cases test state
      · exact noInduction _ _
      · exact yesInduction _ _
  | goto target => rfl
  | halt => rfl

end TM2ForkMachine
end LeanTrominoes
