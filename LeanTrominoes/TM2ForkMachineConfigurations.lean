/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2ForkMachine

/-! # Component configurations inside the fork machine -/

noncomputable section

namespace LeanTrominoes
namespace TM2ForkMachine

open Turing

def componentStacks (first second : FinTM2)
    (InputSymbol FirstSymbol SecondSymbol : Type)
    (firstContents : ∀ stack, List (first.Γ stack))
    (secondContents : ∀ stack, List (second.Γ stack)) :
    ∀ stack,
      List (Alphabet first second InputSymbol FirstSymbol SecondSymbol stack)
  | .input => []
  | .inputReverse => []
  | .first stack => firstContents stack
  | .second stack => secondContents stack
  | .outputReverse => []
  | .output => []

def liftFirstCfg (first second : FinTM2)
    (InputSymbol FirstSymbol SecondSymbol : Type)
    (secondContents : ∀ stack, List (second.Γ stack))
    (configuration : first.Cfg) :
    TM2.Cfg
      (Alphabet first second InputSymbol FirstSymbol SecondSymbol)
      (CombinedLabel first second)
      (CombinedState first second InputSymbol FirstSymbol SecondSymbol) where
  l := match configuration.l with
    | some label => some (.first label)
    | none => some (.second second.main)
  var := match configuration.l with
    | some _ => .first configuration.var
    | none => .second second.initialState
  stk := componentStacks first second InputSymbol FirstSymbol SecondSymbol
    configuration.stk secondContents

def liftSecondCfg (first second : FinTM2)
    (InputSymbol FirstSymbol SecondSymbol : Type)
    (firstContents : ∀ stack, List (first.Γ stack))
    (configuration : second.Cfg) :
    TM2.Cfg
      (Alphabet first second InputSymbol FirstSymbol SecondSymbol)
      (CombinedLabel first second)
      (CombinedState first second InputSymbol FirstSymbol SecondSymbol) where
  l := match configuration.l with
    | some label => some (.second label)
    | none => some .drainFirstOutput
  var := match configuration.l with
    | some _ => .second configuration.var
    | none => .firstOutput none
  stk := componentStacks first second InputSymbol FirstSymbol SecondSymbol
    firstContents configuration.stk

@[simp]
theorem update_componentStacks_first
    (first second : FinTM2)
    (InputSymbol FirstSymbol SecondSymbol : Type)
    (firstContents : ∀ stack, List (first.Γ stack))
    (secondContents : ∀ stack, List (second.Γ stack))
    (target : first.K) (value : List (first.Γ target)) :
    Function.update
        (componentStacks first second InputSymbol FirstSymbol SecondSymbol
          firstContents secondContents)
        (.first target) value =
      componentStacks first second InputSymbol FirstSymbol SecondSymbol
        (Function.update firstContents target value) secondContents := by
  funext stack
  cases stack with
  | input => simp [componentStacks]
  | inputReverse => simp [componentStacks]
  | first stack =>
      by_cases equal : stack = target
      · subst stack
        simp [componentStacks]
      · have taggedNe :
            (Stack.first stack : Stack first.K second.K) ≠
              Stack.first target := by
          intro taggedEq
          exact equal (Stack.first.inj taggedEq)
        simp [componentStacks, Function.update_of_ne equal,
          Function.update_of_ne taggedNe]
  | second stack => simp [componentStacks]
  | outputReverse => simp [componentStacks]
  | output => simp [componentStacks]

@[simp]
theorem update_componentStacks_second
    (first second : FinTM2)
    (InputSymbol FirstSymbol SecondSymbol : Type)
    (firstContents : ∀ stack, List (first.Γ stack))
    (secondContents : ∀ stack, List (second.Γ stack))
    (target : second.K) (value : List (second.Γ target)) :
    Function.update
        (componentStacks first second InputSymbol FirstSymbol SecondSymbol
          firstContents secondContents)
        (.second target) value =
      componentStacks first second InputSymbol FirstSymbol SecondSymbol
        firstContents (Function.update secondContents target value) := by
  funext stack
  cases stack with
  | input => simp [componentStacks]
  | inputReverse => simp [componentStacks]
  | first stack => simp [componentStacks]
  | second stack =>
      by_cases equal : stack = target
      · subst stack
        simp [componentStacks]
      · have taggedNe :
            (Stack.second stack : Stack first.K second.K) ≠
              Stack.second target := by
          intro taggedEq
          exact equal (Stack.second.inj taggedEq)
        simp [componentStacks, Function.update_of_ne equal,
          Function.update_of_ne taggedNe]
  | outputReverse => simp [componentStacks]
  | output => simp [componentStacks]

end TM2ForkMachine
end LeanTrominoes
