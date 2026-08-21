/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataCrossingMarkerFilteredPairSemantics
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataCrossingMarkerOccurrencePairData

/-! # Exact semantics of direct occurrence-pair crossing markers -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedCrossingOccurrencePairSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable local instance directRetainedCrossingOccurrencePairSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Fusing record construction into the pair predicate preserves the exact
filtered-pair marker word. -/
theorem directRetainedPlanarMetadataCrossingOccurrencePairMarkers_eq_filteredPairMarkers
    (symbols : List encoding.Γ) :
    directRetainedPlanarMetadataCrossingOccurrencePairMarkers decider symbols =
      directRetainedPlanarMetadataCrossingFilteredPairMarkers decider
        symbols := by
  unfold directRetainedPlanarMetadataCrossingOccurrencePairMarkers
    directRetainedPlanarMetadataCrossingFilteredPairMarkers
  rw [orientedCrossingOccurrencePairs_length_eq_pairFilter]

end LeanTrominoes.PeriodicCNFStripReduction
