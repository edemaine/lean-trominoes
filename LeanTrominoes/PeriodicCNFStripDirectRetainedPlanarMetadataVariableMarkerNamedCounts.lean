/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListDedupDecidableEq
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataVariableMarkerCounts
import LeanTrominoes.PeriodicCNFStripDirectSourceDistinctVariableCountData

/-! # Named counts for retained metadata variable markers -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedNamedMarkerCountsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable local instance directRetainedNamedMarkerCountsVariableDecidableEq :
    DecidableEq Variable :=
  Classical.decEq _

/-- The canonical retained marker suffix has a shared, decider-independent
three-count normal form. -/
theorem directRetainedPlanarMetadataVariableMarkers_eq_namedCounts
    (symbols : List encoding.Γ) :
    directRetainedPlanarMetadataVariableMarkers decider symbols =
      List.replicate
        (2 * (drawing
            (directSourceFormula decider symbols).incidenceGraph).indexedSegments.length +
          directSourceDistinctVariableCount decider symbols +
          13 * (orientedCrossings
            (directSourceFormula decider symbols).incidenceGraph).length)
        FormulaShapeDirectionOrdering.Token.variable := by
  rw [directRetainedPlanarMetadataVariableMarkers_eq_threeCounts]
  unfold directSourceDistinctVariableCount directSourceFormula
  have dedupEq := congrArg List.length
    (listDedup_eq_of_decidableEq
      (inferInstance : DecidableEq Variable)
      directSourceVariableDecidableEq
      (sourceFormula
        (PolySpaceCompiler.formulaOfSymbols decider symbols)).variableOccurrences)
  rw [dedupEq]

end PeriodicCNFStripReduction
end LeanTrominoes

end
