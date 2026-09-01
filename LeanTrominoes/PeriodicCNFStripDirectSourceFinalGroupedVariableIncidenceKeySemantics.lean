/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidenceKeyCompiler

/-! # Semantics of consecutive grouped variable-incidence keys -/

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The key stream is exactly the range of the grouped prefix-query count. -/
theorem directSourceFinalGroupedVariableIncidenceKeys_eq_range
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedVariableIncidenceKeys decider symbols =
      List.range
        (directSourceFinalGroupedVariableIncidencePrefixQueries
          decider symbols).length := by
  unfold directSourceFinalGroupedVariableIncidenceKeys
    UnaryFieldRange.values
    directSourceFinalGroupedVariableIncidenceKeySeeds
    FiniteUnaryFieldMap.values
  rw [List.length_map]

@[simp] theorem directSourceFinalGroupedVariableIncidenceKeys_length
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedVariableIncidenceKeys decider symbols).length =
      (directSourceFinalGroupedVariableIncidencePrefixQueries
        decider symbols).length := by
  rw [directSourceFinalGroupedVariableIncidenceKeys_eq_range,
    List.length_range]

@[simp] theorem directSourceFinalGroupedVariableIncidenceKeySeeds_length
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedVariableIncidenceKeySeeds decider symbols).length =
      (directSourceFinalGroupedVariableIncidencePrefixQueries
        decider symbols).length := by
  simp [directSourceFinalGroupedVariableIncidenceKeySeeds,
    FiniteUnaryFieldMap.values]

end LeanTrominoes.PeriodicCNFStripReduction
