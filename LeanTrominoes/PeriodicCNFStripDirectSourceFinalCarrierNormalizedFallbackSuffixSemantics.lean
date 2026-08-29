/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierFallbackSuffixSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierNormalizedFallbackSuffixCompiler
import LeanTrominoes.RetainedAngularFanNormalizedFallbackSuffixDirectionBatchAllSemantics

/-! # Semantics of normalized direct carrier fallback suffixes -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierNormalizedFallbackSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCarrierNormalizedFallbackSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Canonical route-delimited normalized suffix words represented by every
direct carrier query. -/
def directSourceFinalCarrierNormalizedFallbackGeometricSuffixDirections
    (symbols : List encoding.Γ) :
    List FallbackSuffixDirectionCompiler.OutputToken :=
  NormalizedFallbackSuffixDirectionCompiler.Batch.retainedDirections
    (directSourceFinalCarrierFallbackSemanticQueries decider symbols)

/-- Every semantic carrier query has positive raw radial length. -/
theorem directSourceFinalCarrierFallbackSemanticQueries_lengthPositive
    (symbols : List encoding.Γ) :
    ∀ query ∈ directSourceFinalCarrierFallbackSemanticQueries decider symbols,
      0 < query.rawLength := by
  rw [← directSourceFinalCarrierFallbackSuffixQueries_eq]
  exact directSourceFinalCarrierFallbackSuffixQueries_lengthPositive
    decider symbols

/-- The direct normalized carrier-suffix compiler emits exactly the
canonical normalized suffix word for every semantic carrier query. -/
theorem directSourceFinalCarrierNormalizedFallbackSuffixDirections_eq_geometric
    (symbols : List encoding.Γ) :
    directSourceFinalCarrierNormalizedFallbackSuffixDirections
        decider symbols =
      directSourceFinalCarrierNormalizedFallbackGeometricSuffixDirections
        decider symbols := by
  unfold directSourceFinalCarrierNormalizedFallbackSuffixDirections
    directSourceFinalCarrierNormalizedFallbackGeometricSuffixDirections
  rw [directSourceFinalCarrierFallbackSuffixQueries_eq]
  exact
    NormalizedFallbackSuffixDirectionCompiler.Batch.directions_eq_retainedDirections
      (directSourceFinalCarrierFallbackSemanticQueries decider symbols)
      (directSourceFinalCarrierFallbackSemanticQueries_lengthPositive
        decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
