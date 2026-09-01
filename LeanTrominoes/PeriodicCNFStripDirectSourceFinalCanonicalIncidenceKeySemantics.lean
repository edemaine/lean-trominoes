/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalIncidenceKeyCompiler

/-! # Semantics of complete canonical incidence keys -/

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The canonical key column is exactly the consecutive range of the full
variable-prefix/clause-suffix query count. -/
theorem directSourceFinalCanonicalIncidenceKeys_eq_range
    (symbols : List encoding.Γ) :
    directSourceFinalCanonicalIncidenceKeys decider symbols =
      List.range
        (directSourceFinalCanonicalIncidenceQueries decider symbols).length := by
  unfold directSourceFinalCanonicalIncidenceKeys
    UnaryFieldRange.values
    directSourceFinalCanonicalIncidenceKeySeeds
    FiniteUnaryFieldMap.values
  rw [List.length_map]

@[simp] theorem directSourceFinalCanonicalIncidenceQueries_length
    (symbols : List encoding.Γ) :
    (directSourceFinalCanonicalIncidenceQueries decider symbols).length =
      (directSourceFinalGroupedVariableIncidencePrefixQueries
          decider symbols).length +
        (directSourceFinalClauseIncidenceQueries decider symbols).length := by
  simp [directSourceFinalCanonicalIncidenceQueries]

@[simp] theorem directSourceFinalCanonicalIncidenceKeys_length
    (symbols : List encoding.Γ) :
    (directSourceFinalCanonicalIncidenceKeys decider symbols).length =
      (directSourceFinalCanonicalIncidenceQueries decider symbols).length := by
  rw [directSourceFinalCanonicalIncidenceKeys_eq_range,
    List.length_range]

@[simp] theorem directSourceFinalCanonicalIncidenceKeySeeds_length
    (symbols : List encoding.Γ) :
    (directSourceFinalCanonicalIncidenceKeySeeds decider symbols).length =
      (directSourceFinalCanonicalIncidenceQueries decider symbols).length := by
  simp [directSourceFinalCanonicalIncidenceKeySeeds,
    FiniteUnaryFieldMap.values]

end LeanTrominoes.PeriodicCNFStripReduction
