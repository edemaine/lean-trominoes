/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationExposedPortMatching

/-!
# Well-formedness of the compiled normalized drawing

Exposed-port soundness supplies matching neighbors for every nonempty port.
Applying it once more in the reverse direction rules out a colored neighbor
opposite an empty port.  Thus the complete option-valued port tables agree at
every finite torus adjacency.
-/

namespace LeanTrominoes

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

namespace PeriodicThreeDM

/-- The final raster compiler produces a well-formed periodic orthogonal
drawing: every colored half-edge meets the same color, and every unused side
meets another unused side. -/
theorem ContinuousPlanarPresentation.normalizedOrthogonalDrawing_isWellFormed
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (sourceSimple :
      ∀ route ∈ presentation.drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route) :
    presentation.toPlanarPresentation.normalizedOrthogonalDrawing.IsWellFormed := by
  let planar := presentation.toPlanarPresentation
  have collisionFree := presentation.finalAssignmentsCollisionFree
    wellFormed degree separated sourceSimple
  apply planar.normalizedOrthogonalDrawing_isWellFormed_of_lookup
  intro position side
  cases currentPort :
      (planar.finalCellTypeAt
        (((position.1.val : Int), (position.2.val : Int)))).portColor side with
  | some color =>
      have neighborColor := presentation.finalCellTypeAt_neighbor_portColor
        wellFormed degree collisionFree position side color currentPort
      simpa [planar] using neighborColor.symm
  | none =>
      cases neighborPort :
          (planar.finalCellTypeAt
            ((((planar.normalizedOrthogonalDrawing.neighbor position side).1.val :
                Int),
              ((planar.normalizedOrthogonalDrawing.neighbor position side).2.val :
                Int)))).portColor side.opposite with
      | none => rfl
      | some color =>
          have currentColor := presentation.finalCellTypeAt_neighbor_portColor
            wellFormed degree collisionFree
            (planar.normalizedOrthogonalDrawing.neighbor position side)
            side.opposite color neighborPort
          have contradiction :
              (planar.finalCellTypeAt
                (((position.1.val : Int), (position.2.val : Int)))).portColor
                  side = some color := by
            simpa [planar] using currentColor
          rw [currentPort] at contradiction
          contradiction

end PeriodicThreeDM
end LeanTrominoes
