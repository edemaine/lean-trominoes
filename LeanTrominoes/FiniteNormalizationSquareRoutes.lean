/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteNormalizationSquareGeometry
import LeanTrominoes.FiniteThreeDMContractionOffsets
import LeanTrominoes.PeriodicThreeDMVertexNormalizationVerticalBandFinal

/-! # Finite routes stay inside one square throughout vertex normalization -/
namespace LeanTrominoes.PeriodicGridDrawing
open PeriodicOrthocrossing

theorem PolylineInFundamentalSquare.reverse {drawing : PeriodicGridDrawing} {route : List Cell}
    (inside : drawing.PolylineInFundamentalSquare route) : drawing.PolylineInFundamentalSquare route.reverse :=
  fun point member => inside point (List.mem_reverse.mp member)

theorem PolylineInFundamentalSquare.joinPolylines {drawing : PeriodicGridDrawing} {first second : List Cell}
    (firstInside : drawing.PolylineInFundamentalSquare first)
    (secondInside : drawing.PolylineInFundamentalSquare second) :
    drawing.PolylineInFundamentalSquare (joinPolylines first second) := by
  intro point member
  rcases List.mem_append.mp member with member|member
  · exact firstInside _ member
  · exact secondInside _ (List.mem_of_mem_tail member)
end LeanTrominoes.PeriodicGridDrawing
namespace LeanTrominoes

open Gadget
open PeriodicOrthocrossing

namespace PeriodicThreeDM

/-- Every genuine incidence route inherits a pointwise vertical-band bound
from the original drawing. -/
theorem PlanarPresentation.incidenceRoute_inFundamentalSquare
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (sourceInside :
      presentation.drawing.RoutePointsInFundamentalSquare)
    (color : WireColor) (atom : Nat) {incidence : Incidence}
    (member : incidence ∈ problem.incidences color atom) :
    presentation.drawing.PolylineInFundamentalSquare
      (presentation.incidenceRoute
        ⟨incidence.tripleIndex, color⟩) := by
  have tagMember :=
    incidenceTag_mem_of_incidence_mem
      problem color atom member
  have routeMember := presentation.incidenceRoute_mem tagMember
  intro point pointMember
  exact sourceInside _ routeMember point pointMember

/-- Every contracted edge route remains in the source drawing's open vertical
halo. -/
theorem PlanarPresentation.contractedEdgeRoute_inFundamentalSquare
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (zero : problem.ZeroOffsets)
    (sourceInside :
      presentation.drawing.RoutePointsInFundamentalSquare)
    {edge : ContractedEdge}
    (member : edge ∈ problem.contractedEdges) :
    presentation.drawing.PolylineInFundamentalSquare
      (presentation.contractedEdgeRoute edge) := by
  have edgeHorizontal :=
    contractedEdge_offset_eq_zero zero member
  simp only [contractedEdges, List.mem_flatMap] at member
  rcases member with ⟨color, _colorMember, member⟩
  simp only [contractedEdgesForColor, List.mem_flatMap] at member
  rcases member with ⟨atom, _atomMember, member⟩
  have metadata :=
    contractedEdgesForElement_metadata problem color atom member
  have incidenceMembers :=
    contractedEdgesForElement_incidence_members
      problem color atom member
  cases edge with
  | retained edgeColor edgeAtom incidence =>
      simp only [ContractedEdge.color,
        ContractedEdge.atom] at metadata
      have incidenceMember :
          incidence ∈ problem.incidences edgeColor edgeAtom := by
        simpa only [metadata.1, metadata.2,
          ContractedEdge.sourceIncidence] using incidenceMembers.1
      simpa [PlanarPresentation.contractedEdgeRoute] using
        presentation.incidenceRoute_inFundamentalSquare
          sourceInside edgeColor edgeAtom incidenceMember
  | through edgeColor edgeAtom first second =>
      simp only [ContractedEdge.color,
        ContractedEdge.atom] at metadata
      have firstMember :
          first ∈ problem.incidences edgeColor edgeAtom := by
        simpa only [metadata.1, metadata.2,
          ContractedEdge.sourceIncidence] using incidenceMembers.1
      have secondMember :
          second ∈ problem.incidences edgeColor edgeAtom := by
        simpa only [metadata.1, metadata.2,
          ContractedEdge.targetIncidence] using incidenceMembers.2.1
      have firstInside :=
        presentation.incidenceRoute_inFundamentalSquare
          sourceInside edgeColor edgeAtom firstMember
      have secondInside :=
        presentation.incidenceRoute_inFundamentalSquare
          sourceInside edgeColor edgeAtom secondMember
      have shiftZero : Cell.sub first.offset second.offset=(0,0) := by
        simpa [ContractedEdge.toPeriodicEdge] using edgeHorizontal
      have translatedInside : presentation.drawing.PolylineInFundamentalSquare
          (translatePolyline (presentation.drawing.periodTranslation (Cell.sub first.offset second.offset))
            (presentation.incidenceRoute ⟨second.tripleIndex,edgeColor⟩)) := by
        intro point pointMember
        obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp pointMember
        simpa [shiftZero,PeriodicGridDrawing.periodTranslation,Cell.scale,Cell.add]
          using secondInside original originalMember
      have reversedInside := translatedInside.reverse
      exact firstInside.joinPolylines reversedInside

/-- If the original routes lie in the open vertical halo, so do all routes
stored by its one-dimensional contracted drawing. -/
theorem PlanarPresentation.contractedDrawing_routePointsInFundamentalSquare
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (zero : problem.ZeroOffsets)
    (sourceInside :
      presentation.drawing.RoutePointsInFundamentalSquare) :
    presentation.contractedDrawing.RoutePointsInFundamentalSquare := by
  intro route routeMember point pointMember
  simp only [PlanarPresentation.contractedDrawing,
    List.mem_map] at routeMember
  rcases routeMember with ⟨tagged, taggedMember, rfl⟩
  have inside :=
    presentation.contractedEdgeRoute_inFundamentalSquare
      zero sourceInside
      (List.fst_mem_of_mem_zipIdx taggedMember)
      point pointMember
  simpa [PeriodicGridDrawing.PositionInFundamentalSquare,
    PeriodicGridDrawing.gridSize,
    PlanarPresentation.contractedDrawing] using inside

end PeriodicThreeDM
end LeanTrominoes

namespace LeanTrominoes
namespace PeriodicThreeDM

/-- Every retained contracted vertex position lies in the contracted
drawing's open vertical halo. -/
theorem PlanarPresentation.normalizationPosition0_inFundamentalSquare
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {vertex : PeriodicThreeDMVertex}
    (member : vertex ∈ problem.contractedGraph.vertices) :
    presentation.contractedDrawing.PositionInFundamentalSquare
      (presentation.normalizationPosition0 vertex) := by
  apply presentation.contractedPositions_in_fundamental_square
  unfold PlanarPresentation.normalizationPosition0
  rw [presentation.contractedDrawing_vertexPosition member]
  rw [presentation.contractedVertexPositions_eq_map]
  exact List.mem_map.mpr ⟨vertex, member, rfl⟩

/-- The target occurrence of an emitted zero contracted edge has the
same vertical coordinate as its retained target prototype, and hence lies
in the old open halo. -/
theorem PlanarPresentation.normalizationTarget0_inFundamentalSquare
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (zero : problem.ZeroOffsets)
    {edge : ContractedEdge}
    (member : edge ∈ problem.contractedEdges) :
    presentation.contractedDrawing.PositionInFundamentalSquare
      (presentation.normalizationTarget0 edge) := by
  have graphEdgeMember :
      edge.toPeriodicEdge ∈ problem.contractedGraph.edges :=
    List.mem_map.mpr ⟨edge, member, rfl⟩
  have endpointMembers :=
    (contractedGraph_isWellFormed problem).2
      edge.toPeriodicEdge graphEdgeMember
  have targetInside :=
    presentation.normalizationPosition0_inFundamentalSquare
      endpointMembers.2
  have edgeZero := contractedEdge_offset_eq_zero zero member
  simpa [PlanarPresentation.normalizationTarget0,
    PeriodicGridDrawing.periodTranslation,Cell.scale,Cell.add,edgeZero] using targetInside

end PeriodicThreeDM
end LeanTrominoes

namespace LeanTrominoes
namespace PeriodicThreeDM

/-- The first Figure 2 replacement keeps one emitted contracted route inside
the scale-twelve vertical halo. -/
theorem PlanarPresentation.normalizationRoute1_inFundamentalSquare
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (zero : problem.ZeroOffsets)
    {edge : ContractedEdge}
    (member : edge ∈ problem.contractedEdges)
    (oldInside :
      presentation.contractedDrawing.PolylineInFundamentalSquare
        (presentation.contractedEdgeRoute edge)) :
    (vertexNormalizationMagnifiedUnitDrawing
      presentation.contractedDrawing)
      |>.PolylineInFundamentalSquare
        (presentation.normalizationRoute1 edge) := by
  have graphEdgeMember :
      edge.toPeriodicEdge ∈ problem.contractedGraph.edges :=
    List.mem_map.mpr ⟨edge, member, rfl⟩
  have endpointMembers :=
    (contractedGraph_isWellFormed problem).2
      edge.toPeriodicEdge graphEdgeMember
  have oldOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline
        (presentation.contractedEdgeRoute edge) := by
    have localMember := member
    simp only [contractedEdges, List.mem_flatMap] at localMember
    rcases localMember with ⟨color, _colorMember, localMember⟩
    simp only [contractedEdgesForColor,
      List.mem_flatMap] at localMember
    rcases localMember with ⟨atom, _atomMember, localMember⟩
    exact presentation.contractedEdgeRoute_orthogonal
      color atom localMember
  have sourceAnchorInside :=
    presentation.normalizationPosition0_inFundamentalSquare
      endpointMembers.1
  have targetAnchorInside :=
    presentation.normalizationTarget0_inFundamentalSquare
      zero member
  have sourceTemplateInside :=
    normalizationTemplateAt_route_inFundamentalSquare
      sourceAnchorInside
      (omittedSideAt presentation edge.toPeriodicEdge.source)
      ((ContractedEndpoint.source edge).firstNormalizedPort presentation)
  have targetTemplateInside :=
    normalizationTemplateAt_route_inFundamentalSquare
      targetAnchorInside
      (omittedSideAt presentation edge.toPeriodicEdge.target)
      ((ContractedEndpoint.target edge).firstNormalizedPort presentation)
  unfold PlanarPresentation.normalizationRoute1
  apply normalizeRouteWithTemplates_inFundamentalSquare
    oldOrthogonal oldInside
  · simpa [ContractedEndpoint.firstNormalizationTemplate,
      ContractedEndpoint.vertex] using
      sourceTemplateInside
  · simpa [ContractedEndpoint.firstNormalizationTemplate,
      ContractedEndpoint.vertex] using
      targetTemplateInside

end PeriodicThreeDM
end LeanTrominoes

namespace LeanTrominoes
namespace PeriodicThreeDM

/-- Starting from band-contained incidence routes of a one-dimensional 3DM
presentation, the complete first normalized drawing remains in its enlarged
open vertical halo. -/
theorem PlanarPresentation.normalizationGridDrawing1_routePointsInFundamentalSquare
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (zero : problem.ZeroOffsets)
    (sourceInside :
      presentation.drawing.RoutePointsInFundamentalSquare) :
    presentation.normalizationGridDrawing1
      |>.RoutePointsInFundamentalSquare := by
  have contractedInside :=
    presentation.contractedDrawing_routePointsInFundamentalSquare
      zero sourceInside
  intro route routeMember point pointMember
  rw [presentation.normalizationGridDrawing1_edgeRoutes] at routeMember
  simp only [PlanarPresentation.normalizationEdgeRoutes1,
    List.mem_map] at routeMember
  rcases routeMember with ⟨tagged, taggedMember, rfl⟩
  have edgeMember : tagged.1 ∈ problem.contractedEdges :=
    List.fst_mem_of_mem_zipIdx taggedMember
  have oldRouteMember :
      presentation.contractedEdgeRoute tagged.1 ∈
        presentation.contractedDrawing.edgeRoutes := by
    unfold PlanarPresentation.contractedDrawing
    exact List.mem_map.mpr ⟨tagged, taggedMember, rfl⟩
  have oldInside :
      presentation.contractedDrawing.PolylineInFundamentalSquare
        (presentation.contractedEdgeRoute tagged.1) :=
    fun oldPoint oldPointMember =>
      contractedInside _ oldRouteMember _ oldPointMember
  have inside :=
    presentation.normalizationRoute1_inFundamentalSquare
      zero edgeMember oldInside point pointMember
  simpa [PeriodicGridDrawing.PositionInFundamentalSquare,
    PlanarPresentation.normalizationGridDrawing1,
    PeriodicGridDrawing.gridSize] using inside

end PeriodicThreeDM
end LeanTrominoes

namespace LeanTrominoes
namespace PeriodicThreeDM

/-- Every retained vertex anchor after round 1 lies in the first normalized
drawing's open vertical halo. -/
theorem PlanarPresentation.normalizationPosition1_inFundamentalSquare
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {vertex : PeriodicThreeDMVertex}
    (member : vertex ∈ problem.contractedGraph.vertices) :
    presentation.normalizationGridDrawing1.PositionInFundamentalSquare
      (presentation.normalizationPosition1 vertex) := by
  have inside := normalizeVertexPosition_inFundamentalSquare
    (presentation.normalizationPosition0_inFundamentalSquare member)
  simpa [PlanarPresentation.normalizationPosition1,
    PeriodicGridDrawing.PositionInFundamentalSquare,
    PlanarPresentation.normalizationGridDrawing1,
    PeriodicGridDrawing.gridSize] using inside

/-- The target anchor after round 1 is the affine image of the old zero
target occurrence and lies in the first normalized drawing's halo. -/
theorem PlanarPresentation.normalizationTarget1_inFundamentalSquare
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (zero : problem.ZeroOffsets)
    {edge : ContractedEdge}
    (member : edge ∈ problem.contractedEdges) :
    presentation.normalizationGridDrawing1.PositionInFundamentalSquare
      (presentation.normalizationTarget1 edge) := by
  have inside := normalizeVertexPosition_inFundamentalSquare
    (presentation.normalizationTarget0_inFundamentalSquare
      zero member)
  simpa [PlanarPresentation.normalizationTarget1,
    PeriodicGridDrawing.PositionInFundamentalSquare,
    PlanarPresentation.normalizationGridDrawing1,
    PeriodicGridDrawing.gridSize] using inside

end PeriodicThreeDM
end LeanTrominoes

namespace LeanTrominoes
namespace PeriodicThreeDM

/-- The first cyclic replacement keeps one round-1 route inside the next
scale-twelve vertical halo. -/
theorem ContinuousPlanarPresentation.normalizationRoute2_inFundamentalSquare
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (zero : problem.ZeroOffsets)
    {edge : ContractedEdge}
    (member : edge ∈ problem.contractedEdges)
    (oldInside :
      presentation.toPlanarPresentation.normalizationGridDrawing1
        |>.PolylineInFundamentalSquare
          (presentation.toPlanarPresentation.normalizationRoute1 edge)) :
    (vertexNormalizationMagnifiedUnitDrawing
      presentation.toPlanarPresentation.normalizationGridDrawing1)
      |>.PolylineInFundamentalSquare
        (presentation.toPlanarPresentation.normalizationRoute2 edge) := by
  let planar := presentation.toPlanarPresentation
  have graphEdgeMember :
      edge.toPeriodicEdge ∈ problem.contractedGraph.edges :=
    List.mem_map.mpr ⟨edge, member, rfl⟩
  have endpointMembers :=
    (contractedGraph_isWellFormed problem).2
      edge.toPeriodicEdge graphEdgeMember
  have oldOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline
        (planar.normalizationRoute1 edge) := by
    have unitSteps := presentation.normalizationRoute1_unitSteps
      wellFormed degree member
    exact unitSteps.imp fun _ _ step => step.isAxisAligned
  have sourceAnchorInside :=
    planar.normalizationPosition1_inFundamentalSquare
      endpointMembers.1
  have targetAnchorInside :=
    planar.normalizationTarget1_inFundamentalSquare
      zero member
  have sourceTemplateInside :=
    normalizationTemplateAt_rotationRoundRoute_inFundamentalSquare
      sourceAnchorInside
      (firstRotationActive planar edge.toPeriodicEdge.source)
      ((ContractedEndpoint.source edge).firstNormalizedPort planar)
  have targetTemplateInside :=
    normalizationTemplateAt_rotationRoundRoute_inFundamentalSquare
      targetAnchorInside
      (firstRotationActive planar edge.toPeriodicEdge.target)
      ((ContractedEndpoint.target edge).firstNormalizedPort planar)
  change
    (vertexNormalizationMagnifiedUnitDrawing
      planar.normalizationGridDrawing1)
      |>.PolylineInFundamentalSquare
        (planar.normalizationRoute2 edge)
  unfold PlanarPresentation.normalizationRoute2
  apply normalizeRouteWithTemplates_inFundamentalSquare
    oldOrthogonal oldInside
  · simpa [ContractedEndpoint.secondNormalizationTemplate,
      ContractedEndpoint.vertex] using sourceTemplateInside
  · simpa [ContractedEndpoint.secondNormalizationTemplate,
      ContractedEndpoint.vertex] using targetTemplateInside

end PeriodicThreeDM
end LeanTrominoes

namespace LeanTrominoes
namespace PeriodicThreeDM

/-- The complete first cyclic-normalization round preserves the enlarged
open vertical halo. -/
theorem ContinuousPlanarPresentation.normalizationGridDrawing2_routePointsInFundamentalSquare
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (zero : problem.ZeroOffsets)
    (sourceInside :
      presentation.toPlanarPresentation.drawing
        |>.RoutePointsInFundamentalSquare) :
    presentation.toPlanarPresentation.normalizationGridDrawing2
      |>.RoutePointsInFundamentalSquare := by
  let planar := presentation.toPlanarPresentation
  have oldDrawingInside :=
    planar.normalizationGridDrawing1_routePointsInFundamentalSquare
      zero sourceInside
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
      planar.normalizationGridDrawing1.PolylineInFundamentalSquare
        (planar.normalizationRoute1 tagged.1) :=
    fun oldPoint oldPointMember =>
      oldDrawingInside _ oldRouteMember _ oldPointMember
  have inside :=
    presentation.normalizationRoute2_inFundamentalSquare
      wellFormed degree zero edgeMember oldInside
      point pointMember
  simpa [PeriodicGridDrawing.PositionInFundamentalSquare,
    PlanarPresentation.normalizationGridDrawing2,
    PeriodicGridDrawing.gridSize] using inside

end PeriodicThreeDM
end LeanTrominoes

namespace LeanTrominoes
namespace PeriodicThreeDM

/-- Every retained vertex anchor after round 2 lies in the second normalized
drawing's open vertical halo. -/
theorem PlanarPresentation.normalizationPosition2_inFundamentalSquare
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {vertex : PeriodicThreeDMVertex}
    (member : vertex ∈ problem.contractedGraph.vertices) :
    presentation.normalizationGridDrawing2.PositionInFundamentalSquare
      (presentation.normalizationPosition2 vertex) := by
  have inside := normalizeVertexPosition_inFundamentalSquare
    (presentation.normalizationPosition1_inFundamentalSquare member)
  simpa [PlanarPresentation.normalizationPosition2,
    PeriodicGridDrawing.PositionInFundamentalSquare,
    PlanarPresentation.normalizationGridDrawing2,
    PeriodicGridDrawing.gridSize] using inside

/-- The target anchor after round 2 is the affine image of the previous
zero target occurrence and lies in the second normalized halo. -/
theorem PlanarPresentation.normalizationTarget2_inFundamentalSquare
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (zero : problem.ZeroOffsets)
    {edge : ContractedEdge}
    (member : edge ∈ problem.contractedEdges) :
    presentation.normalizationGridDrawing2.PositionInFundamentalSquare
      (presentation.normalizationTarget2 edge) := by
  have inside := normalizeVertexPosition_inFundamentalSquare
    (presentation.normalizationTarget1_inFundamentalSquare
      zero member)
  simpa [PlanarPresentation.normalizationTarget2,
    PeriodicGridDrawing.PositionInFundamentalSquare,
    PlanarPresentation.normalizationGridDrawing2,
    PeriodicGridDrawing.gridSize] using inside

end PeriodicThreeDM
end LeanTrominoes

namespace LeanTrominoes
namespace PeriodicThreeDM

/-- The second cyclic replacement keeps one round-2 route inside the final
scale-twelve vertical halo. -/
theorem ContinuousPlanarPresentation.finalNormalizationRoute_inFundamentalSquare
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (zero : problem.ZeroOffsets)
    {edge : ContractedEdge}
    (member : edge ∈ problem.contractedEdges)
    (oldInside :
      presentation.toPlanarPresentation.normalizationGridDrawing2
        |>.PolylineInFundamentalSquare
          (presentation.toPlanarPresentation.normalizationRoute2 edge)) :
    (vertexNormalizationMagnifiedUnitDrawing
      presentation.toPlanarPresentation.normalizationGridDrawing2)
      |>.PolylineInFundamentalSquare
        (presentation.toPlanarPresentation.finalNormalizationRoute edge) := by
  let planar := presentation.toPlanarPresentation
  have graphEdgeMember :
      edge.toPeriodicEdge ∈ problem.contractedGraph.edges :=
    List.mem_map.mpr ⟨edge, member, rfl⟩
  have endpointMembers :=
    (contractedGraph_isWellFormed problem).2
      edge.toPeriodicEdge graphEdgeMember
  have oldOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline
        (planar.normalizationRoute2 edge) := by
    have unitSteps := presentation.normalizationRoute2_unitSteps
      wellFormed degree member
    exact unitSteps.imp fun _ _ step => step.isAxisAligned
  have sourceAnchorInside :=
    planar.normalizationPosition2_inFundamentalSquare
      endpointMembers.1
  have targetAnchorInside :=
    planar.normalizationTarget2_inFundamentalSquare
      zero member
  have sourceTemplateInside :=
    normalizationTemplateAt_rotationRoundRoute_inFundamentalSquare
      sourceAnchorInside
      (secondRotationActive planar edge.toPeriodicEdge.source)
      ((ContractedEndpoint.source edge).secondNormalizedPort planar)
  have targetTemplateInside :=
    normalizationTemplateAt_rotationRoundRoute_inFundamentalSquare
      targetAnchorInside
      (secondRotationActive planar edge.toPeriodicEdge.target)
      ((ContractedEndpoint.target edge).secondNormalizedPort planar)
  change
    (vertexNormalizationMagnifiedUnitDrawing
      planar.normalizationGridDrawing2)
      |>.PolylineInFundamentalSquare
        (planar.finalNormalizationRoute edge)
  unfold PlanarPresentation.finalNormalizationRoute
  apply normalizeRouteWithTemplates_inFundamentalSquare
    oldOrthogonal oldInside
  · simpa [ContractedEndpoint.finalNormalizationTemplate,
      ContractedEndpoint.vertex] using sourceTemplateInside
  · simpa [ContractedEndpoint.finalNormalizationTemplate,
      ContractedEndpoint.vertex] using targetTemplateInside

end PeriodicThreeDM
end LeanTrominoes

namespace LeanTrominoes
namespace PeriodicThreeDM

/-- The complete second cyclic-normalization round preserves the open
vertical halo, yielding the final normalized route family. -/
theorem ContinuousPlanarPresentation.finalNormalizedGridDrawing_routePointsInFundamentalSquare
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (zero : problem.ZeroOffsets)
    (sourceInside :
      presentation.toPlanarPresentation.drawing
        |>.RoutePointsInFundamentalSquare) :
    presentation.toPlanarPresentation.finalNormalizedGridDrawing
      |>.RoutePointsInFundamentalSquare := by
  let planar := presentation.toPlanarPresentation
  have oldDrawingInside :=
    presentation.normalizationGridDrawing2_routePointsInFundamentalSquare
      wellFormed degree zero sourceInside
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
      planar.normalizationGridDrawing2.PolylineInFundamentalSquare
        (planar.normalizationRoute2 edge) :=
    fun oldPoint oldPointMember =>
      oldDrawingInside _ oldRouteMember _ oldPointMember
  have inside :=
    presentation.finalNormalizationRoute_inFundamentalSquare
      wellFormed degree zero edgeMember oldInside
      point pointMember
  simp only [PeriodicGridDrawing.PositionInFundamentalSquare] at inside ⊢
  rw [planar.finalNormalizedGridDrawing_gridSize_eq_magnified_round_two]
  exact inside

end PeriodicThreeDM
end LeanTrominoes
