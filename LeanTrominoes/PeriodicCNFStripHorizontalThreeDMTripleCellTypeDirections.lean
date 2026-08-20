/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalNormalizationInputSemanticBridge
import LeanTrominoes.PeriodicThreeDMNormalizationTripleColorData

/-! # Horizontal triple cell types from three incidence directions -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Gadget DegreeThreeVertexNormalization

/-- The normalized trichromatic cell type selected by three incidence
directions in canonical red, green, blue order. -/
def horizontalTripleCellTypeFromDirections
    (red green blue : AxisDirection) : OrthogonalCellType :=
  PeriodicThreeDM.NormalizationCompiler.finalVertexCellTypeFromData
    (.inr (), some
      ((VertexSide.ofDirection red, WireColor.red),
       (VertexSide.ofDirection green, WireColor.green),
       (VertexSide.ofDirection blue, WireColor.blue)))

/-- At every indexed horizontal triple, the final cell type depends only on
the first direction of its three original incidence routes. -/
theorem horizontalFinalVertexCellType_eq_incidenceDirections
    (source : PeriodicCNF Nat)
    (tripleIndex : Nat)
    (indexLt : tripleIndex <
      (horizontalNormalizationInputComputed source).problem.triples.length) :
    PeriodicThreeDM.NormalizationCompiler.finalVertexCellType
        (horizontalNormalizationInputComputed source)
        (.triple tripleIndex) =
      horizontalTripleCellTypeFromDirections
        (AxisDirection.polylineFirstDirection
          (PeriodicThreeDM.NormalizationCompiler.incidenceRoute
            (horizontalNormalizationInputComputed source)
            ⟨tripleIndex, .red⟩))
        (AxisDirection.polylineFirstDirection
          (PeriodicThreeDM.NormalizationCompiler.incidenceRoute
            (horizontalNormalizationInputComputed source)
            ⟨tripleIndex, .green⟩))
        (AxisDirection.polylineFirstDirection
          (PeriodicThreeDM.NormalizationCompiler.incidenceRoute
            (horizontalNormalizationInputComputed source)
            ⟨tripleIndex, .blue⟩)) := by
  rw [horizontalNormalizationInputComputed_eq_normalizationInput] at indexLt ⊢
  unfold normalizationInput at indexLt ⊢
  simpa [horizontalTripleCellTypeFromDirections,
    PeriodicThreeDM.NormalizationCompiler.incidenceColorTripleData,
    PeriodicThreeDM.NormalizationCompiler.incidenceSideColorAt] using
    PeriodicThreeDM.NormalizationCompiler.finalVertexCellType_eq_incidenceColorTripleData
      (presentation source)
      (presentation source).problemWellFormed
      (problem_degreeTwoOrThree source)
      tripleIndex indexLt

end PeriodicCNFStripReduction
end LeanTrominoes
