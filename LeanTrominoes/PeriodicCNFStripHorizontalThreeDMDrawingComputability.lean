/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMDrawingData
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMProblemComputability
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMEdgeRoutesComputability
import LeanTrominoes.PeriodicGridDrawingComputability

/-! # Computability of the executable horizontal 3DM drawing -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

theorem horizontalThreeDMDrawingComputed_primrec :
    Primrec horizontalThreeDMDrawingComputed := by
  unfold horizontalThreeDMDrawingComputed
  exact
    (PeriodicGridDrawing.equivData_symm_primrec.comp
      (Primrec.pair horizontalThreeDMGridSizePredComputed_primrec
        (Primrec.pair horizontalThreeDMVertexPositionsComputed_primrec
          horizontalThreeDMEdgeRoutesComputed_primrec)))

end PeriodicCNFStripReduction
end LeanTrominoes
