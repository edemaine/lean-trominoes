/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCycleInheritedAtomIdentityCompiler

/-! # Semantics of inherited cycle-occurrence source identities -/

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The marker-index stream is the generic blockwise broadcast
specification. -/
theorem directSourceFinalCycleMarkerIndexQueries_eq_expected
    (symbols : List encoding.Γ) :
    directSourceFinalCycleMarkerIndexQueries decider symbols =
      FiniteBlockIndices.expected
        directSourceFinalCycleOccurrenceBlockLength
        (directRetainedFigureNineFiniteSourceVariableMarkers
          decider symbols) := by
  unfold directSourceFinalCycleMarkerIndexQueries
  exact FiniteBlockIndices.indices_eq_expected _ _

/-- Every inherited cycle-occurrence source identity is ordinary zero-based
lookup at its broadcast retained-variable index. -/
theorem directSourceFinalCycleInheritedAtomIdentityIndices_eq_map_getD
    (symbols : List encoding.Γ) :
    directSourceFinalCycleInheritedAtomIdentityIndices decider symbols =
      (directSourceFinalCycleMarkerIndexQueries decider symbols).map
        fun query =>
          (directSourceFinalDistinctAtomIdentityIndices
            decider symbols).getD query 0 := by
  unfold directSourceFinalCycleInheritedAtomIdentityIndices
  apply UnaryIndexedValueLookup.values_eq_map_getD_of_forall_lt
  intro query member
  exact directSourceFinalCycleMarkerIndexQuery_lt
    decider symbols query member

end LeanTrominoes.PeriodicCNFStripReduction
