/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.TM2EndDelimitedBlockMapConfigurations

/-! # Stack transformation used while draining an inner output -/

noncomputable section

namespace LeanTrominoes
namespace TM2EndDelimitedBlockMap

open Turing

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin

def clearInnerOutput (inner : FinTM2)
    (innerContents : ∀ stack, List (inner.Γ stack)) :
    ∀ stack, List (inner.Γ stack) :=
  @Function.update _ _ inner.kDecidableEq innerContents inner.k₁ []

@[simp] theorem clearInnerOutput_update_output
    (inner : FinTM2)
    (innerContents : ∀ stack, List (inner.Γ stack))
    (value : List (inner.Γ inner.k₁)) :
    clearInnerOutput inner
        (@Function.update _ _ inner.kDecidableEq innerContents inner.k₁
          value) =
      clearInnerOutput inner innerContents := by
  simp [clearInnerOutput, Function.update_idem]

theorem clearInnerOutput_eq_self
    (inner : FinTM2)
    (innerContents : ∀ stack, List (inner.Γ stack))
    (empty : innerContents inner.k₁ = []) :
    clearInnerOutput inner innerContents = innerContents := by
  unfold clearInnerOutput
  rw [← empty, Function.update_eq_self]

theorem clearInnerOutput_haltList
    (inner : FinTM2) (output : List (inner.Γ inner.k₁)) :
    clearInnerOutput inner (haltList inner output).stk =
      emptyInnerStacks inner := by
  funext stack
  by_cases equal : stack = inner.k₁
  · subst stack
    simp [clearInnerOutput, emptyInnerStacks]
  · simp [clearInnerOutput, haltList, emptyInnerStacks, equal]

end TM2EndDelimitedBlockMap
end LeanTrominoes
