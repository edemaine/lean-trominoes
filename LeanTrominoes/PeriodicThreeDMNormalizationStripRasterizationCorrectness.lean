/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationStripReadback

/-!
# Lookup-level correctness interfaces for the normalized 3DM strip
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- Matching ports in the finite strip lookup imply well-formedness of the
packaged rectangular drawing. -/
theorem PlanarPresentation.stripNormalizedOrthogonalDrawing_isWellFormed_of_lookup
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (matchingPorts :
      ∀ (position : presentation.stripNormalizedOrthogonalDrawing.Position)
        (side : Side),
        (presentation.finalStripCellTypeAt
            ((position.1.val : Int), (position.2.val : Int))).portColor side =
          (presentation.finalStripCellTypeAt
            (((presentation.stripNormalizedOrthogonalDrawing.neighbor
                position side).1.val : Int),
              ((presentation.stripNormalizedOrthogonalDrawing.neighbor
                position side).2.val : Int))).portColor side.opposite) :
    presentation.stripNormalizedOrthogonalDrawing.IsWellFormed := by
  constructor
  · dsimp only [PlanarPresentation.stripNormalizedOrthogonalDrawing]
    rw [presentation.finalStripCellTypes_length]
    have oneLe : 1 ≤ presentation.finalNormalizationPeriod :=
      Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt presentation.finalNormalizationPeriod_pos)
    rw [Nat.sub_add_cancel oneLe]
    exact Nat.mul_comm _ _
  · intro position side
    rw [presentation.stripNormalizedOrthogonalDrawing_get position]
    rw [presentation.stripNormalizedOrthogonalDrawing_get
      (presentation.stripNormalizedOrthogonalDrawing.neighbor position side)]
    exact matchingPorts position side

/-- Likewise, lookup-level separation of degree-three cells proves the
packaged strip drawing's `VerticesSeparated` predicate. -/
theorem PlanarPresentation.stripNormalizedOrthogonalDrawing_verticesSeparated_of_lookup
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (separated :
      ∀ (position : presentation.stripNormalizedOrthogonalDrawing.Position)
        (side : Side),
        (presentation.finalStripCellTypeAt
            ((position.1.val : Int), (position.2.val : Int))).isVertex = true →
          (presentation.finalStripCellTypeAt
            (((presentation.stripNormalizedOrthogonalDrawing.neighbor
                position side).1.val : Int),
              ((presentation.stripNormalizedOrthogonalDrawing.neighbor
                position side).2.val : Int))).isVertex = false) :
    presentation.stripNormalizedOrthogonalDrawing.VerticesSeparated := by
  intro position side isVertex
  rw [presentation.stripNormalizedOrthogonalDrawing_get] at isVertex ⊢
  exact separated position side isVertex

end PeriodicThreeDM
end LeanTrominoes
