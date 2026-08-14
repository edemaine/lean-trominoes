/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMVertexNormalizationDrawing
import LeanTrominoes.PeriodicThreeDMVertexNormalizationVerticalBandFinalRoute
import LeanTrominoes.PeriodicThreeDMVertexNormalizationVerticalBandRoundTwo

/-!
# Vertical-band preservation through final vertex normalization
-/

namespace LeanTrominoes
namespace PeriodicThreeDM

/-- The packaged final normalized drawing has the same period as one affine
scale-twelve refinement of the second intermediate drawing. -/
theorem PlanarPresentation.finalNormalizedGridDrawing_gridSize_eq_magnified_round_two
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    presentation.finalNormalizedGridDrawing.gridSize =
      (vertexNormalizationMagnifiedUnitDrawing
        presentation.normalizationGridDrawing2).gridSize := by
  rw [presentation.finalNormalizedGridDrawing_gridSize,
    vertexNormalizationMagnifiedUnitDrawing_gridSize,
    presentation.normalizationGridDrawing2_gridSize,
    presentation.normalizationGridDrawing1_gridSize]
  simp [PlanarPresentation.finalNormalizationPeriod,
    vertexNormalizationScaleNat]
  ring

/-- The complete second cyclic-normalization round preserves the open
vertical halo, yielding the final normalized route family. -/
theorem ContinuousPlanarPresentation.finalNormalizedGridDrawing_routePointsInExpandedVerticalBand
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (horizontal : problem.IsOneDimensional)
    (sourceInside :
      presentation.toPlanarPresentation.drawing
        |>.RoutePointsInExpandedVerticalBand) :
    presentation.toPlanarPresentation.finalNormalizedGridDrawing
      |>.RoutePointsInExpandedVerticalBand := by
  let planar := presentation.toPlanarPresentation
  have oldDrawingInside :=
    presentation.normalizationGridDrawing2_routePointsInExpandedVerticalBand
      wellFormed degree horizontal sourceInside
  intro route routeMember point pointMember
  rw [planar.finalNormalizedGridDrawing_edgeRoutes_eq_map] at routeMember
  rcases List.mem_map.mp routeMember with
    ⟨edge, edgeMember, rfl⟩
  have oldRoutesEq :
      planar.normalizationGridDrawing2.edgeRoutes =
        problem.contractedEdges.map planar.normalizationRoute2 := by
    rw [planar.normalizationGridDrawing2_edgeRoutes]
    unfold PlanarPresentation.normalizationEdgeRoutes2
    calc
      problem.contractedEdges.zipIdx.map
          (fun tagged => planar.normalizationRoute2 tagged.1) =
          (problem.contractedEdges.zipIdx.map Prod.fst).map
            planar.normalizationRoute2 := by
              rw [List.map_map]
              rfl
      _ = _ := by rw [List.zipIdx_map_fst]
  have oldRouteMember :
      planar.normalizationRoute2 edge ∈
        planar.normalizationGridDrawing2.edgeRoutes := by
    rw [oldRoutesEq]
    exact List.mem_map.mpr ⟨edge, edgeMember, rfl⟩
  have oldInside :
      planar.normalizationGridDrawing2.PolylineInExpandedVerticalBand
        (planar.normalizationRoute2 edge) :=
    fun oldPoint oldPointMember =>
      oldDrawingInside _ oldRouteMember _ oldPointMember
  have inside :=
    presentation.finalNormalizationRoute_inExpandedVerticalBand
      wellFormed degree horizontal edgeMember oldInside
      point pointMember
  simp only [PeriodicGridDrawing.PositionInExpandedVerticalBand] at inside ⊢
  rw [planar.finalNormalizedGridDrawing_gridSize_eq_magnified_round_two]
  exact inside

end PeriodicThreeDM
end LeanTrominoes
