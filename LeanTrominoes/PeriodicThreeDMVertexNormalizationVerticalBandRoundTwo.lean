/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMVertexNormalizationVerticalBandRoundOne
import LeanTrominoes.PeriodicThreeDMVertexNormalizationVerticalBandRoundTwoRoute

/-!
# Vertical-band preservation through the second normalization round
-/

namespace LeanTrominoes
namespace PeriodicThreeDM

/-- The complete first cyclic-normalization round preserves the enlarged
open vertical halo. -/
theorem ContinuousPlanarPresentation.normalizationGridDrawing2_routePointsInExpandedVerticalBand
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (horizontal : problem.IsOneDimensional)
    (sourceInside :
      presentation.toPlanarPresentation.drawing
        |>.RoutePointsInExpandedVerticalBand) :
    presentation.toPlanarPresentation.normalizationGridDrawing2
      |>.RoutePointsInExpandedVerticalBand := by
  let planar := presentation.toPlanarPresentation
  have oldDrawingInside :=
    planar.normalizationGridDrawing1_routePointsInExpandedVerticalBand
      horizontal sourceInside
  intro route routeMember point pointMember
  rw [planar.normalizationGridDrawing2_edgeRoutes] at routeMember
  simp only [PlanarPresentation.normalizationEdgeRoutes2,
    List.mem_map] at routeMember
  rcases routeMember with ⟨tagged, taggedMember, rfl⟩
  have edgeMember : tagged.1 ∈ problem.contractedEdges :=
    List.fst_mem_of_mem_zipIdx taggedMember
  have oldRouteMember :
      planar.normalizationRoute1 tagged.1 ∈
        planar.normalizationGridDrawing1.edgeRoutes := by
    rw [planar.normalizationGridDrawing1_edgeRoutes]
    unfold PlanarPresentation.normalizationEdgeRoutes1
    exact List.mem_map.mpr ⟨tagged, taggedMember, rfl⟩
  have oldInside :
      planar.normalizationGridDrawing1.PolylineInExpandedVerticalBand
        (planar.normalizationRoute1 tagged.1) :=
    fun oldPoint oldPointMember =>
      oldDrawingInside _ oldRouteMember _ oldPointMember
  have inside :=
    presentation.normalizationRoute2_inExpandedVerticalBand
      wellFormed degree horizontal edgeMember oldInside
      point pointMember
  simpa [PeriodicGridDrawing.PositionInExpandedVerticalBand,
    PlanarPresentation.normalizationGridDrawing2,
    PeriodicGridDrawing.gridSize] using inside

end PeriodicThreeDM
end LeanTrominoes
