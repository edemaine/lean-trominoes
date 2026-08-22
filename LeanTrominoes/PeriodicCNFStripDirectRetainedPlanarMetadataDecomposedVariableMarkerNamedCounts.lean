/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataDecomposedVariableMarkerSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaShapeNamedVariableCount
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaShapeSegmentCount

/-! # Named counts for decomposed retained metadata markers -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedDecomposedNamedCountsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable local instance directRetainedDecomposedNamedCountsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The compiled marker decomposition has the shared three-count normal form. -/
theorem directRetainedPlanarMetadataDecomposedVariableMarkers_eq_namedCounts
    (symbols : List encoding.Γ) :
    directRetainedPlanarMetadataDecomposedVariableMarkers decider symbols =
      List.replicate
        (2 * (drawing
            (directSourceFormula decider symbols).incidenceGraph).indexedSegments.length +
          directSourceDistinctVariableCount decider symbols +
          13 * (orientedCrossings
            (directSourceFormula decider symbols).incidenceGraph).length)
        FormulaShapeDirectionOrdering.Token.variable := by
  rw [directRetainedPlanarMetadataDecomposedVariableMarkers_eq_replicate_counts]
  rw [directSourceFormulaShape_routedSegmentCount_eq decider symbols]
  rw [directSourceFormulaShape_variableCount_eq_distinct decider symbols]

end PeriodicCNFStripReduction
end LeanTrominoes

end
