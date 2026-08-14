/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationStripExposedPortMatching
import LeanTrominoes.PeriodicThreeDMNormalizationStripFinalAssignmentCollisionFreedom
import LeanTrominoes.PeriodicThreeDMNormalizationStripRasterizationCorrectness

/-!
# Well-formedness of the normalized 3DM strip drawing
-/

namespace LeanTrominoes

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

namespace PeriodicThreeDM

/-- The rectangular strip compiler produces a well-formed periodic
orthogonal drawing. -/
theorem ContinuousPlanarPresentation.stripNormalizedOrthogonalDrawing_isWellFormed
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (horizontal : problem.IsOneDimensional)
    (sourceInside :
      presentation.toPlanarPresentation.drawing
        |>.RoutePointsInExpandedVerticalBand)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (sourceSimple :
      ∀ route ∈ presentation.drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route) :
    presentation.toPlanarPresentation.stripNormalizedOrthogonalDrawing.IsWellFormed := by
  let planar := presentation.toPlanarPresentation
  have collisionFree := presentation.finalStripAssignmentsCollisionFree
    wellFormed degree separated sourceSimple
  apply planar.stripNormalizedOrthogonalDrawing_isWellFormed_of_lookup
  intro position side
  cases currentPort :
      (planar.finalStripCellTypeAt
        (((position.1.val : Int), (position.2.val : Int)))).portColor side with
  | some color =>
      have neighborColor := presentation.finalStripCellTypeAt_neighbor_portColor
        wellFormed degree horizontal sourceInside collisionFree
        position side color currentPort
      simpa [planar] using neighborColor.symm
  | none =>
      cases neighborPort :
          (planar.finalStripCellTypeAt
            ((((planar.stripNormalizedOrthogonalDrawing.neighbor
                position side).1.val : Int),
              ((planar.stripNormalizedOrthogonalDrawing.neighbor
                position side).2.val : Int)))).portColor side.opposite with
      | none => rfl
      | some color =>
          have currentColor :=
            presentation.finalStripCellTypeAt_neighbor_portColor
              wellFormed degree horizontal sourceInside collisionFree
              (planar.stripNormalizedOrthogonalDrawing.neighbor position side)
              side.opposite color neighborPort
          have contradiction :
              (planar.finalStripCellTypeAt
                (((position.1.val : Int), (position.2.val : Int)))).portColor
                  side = some color := by
            simpa [planar] using currentColor
          rw [currentPort] at contradiction
          contradiction

end PeriodicThreeDM
end LeanTrominoes
