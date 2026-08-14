/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationStripReverseTagValues

/-!
# Monochromatic element vertices in reverse strip orientations
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

set_option maxRecDepth 2048
set_option linter.constructorNameAsVariable false

/-- Reading the selected endpoint at one canonical strip vertex port returns
the orientation value on that port of the translated vertex occurrence. -/
theorem ContinuousPlanarPresentation.stripDrawingEndpointInward_endpointAtVertexPort
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (orientation :
      presentation.toPlanarPresentation.stripNormalizedOrthogonalDrawing
        |>.Orientation)
    {vertex : PeriodicThreeDMVertex}
    (vertexMember : vertex ∈ problem.contractedGraph.vertices)
    (translate : Cell) (port : CanonicalVertexPort) :
    let planar := presentation.toPlanarPresentation
    planar.stripDrawingEndpointInward orientation
        (planar.endpointAtVertexPort vertex port.side) translate =
      orientation
        (Cell.add
          (stripReflectedLocation planar.finalNormalizationPeriod
            (planar.finalNormalizationPosition vertex))
          (planar.stripPeriodTranslation translate)) port.side := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  obtain ⟨color, exposed⟩ :=
    planar.finalVertexCellType_portColor_isSome vertex port
  have endpointData :=
    PlanarPresentation.endpointAtVertexPort_data_of_exposed
      presentation wellFormed degree vertexMember exposed
  let endpoint := planar.endpointAtVertexPort vertex port.side
  change endpoint ∈ problem.contractedEndpoints ∧
      endpoint.vertex = vertex ∧
      (endpoint.finalNormalizedPort planar).side = port.side ∧ _ at endpointData
  change orientation
      (Cell.add
        (stripReflectedLocation planar.finalNormalizationPeriod
          (planar.finalNormalizationPosition endpoint.vertex))
        (planar.stripPeriodTranslation translate))
      (endpoint.finalNormalizedPort planar).side = _
  rw [endpointData.2.1, endpointData.2.2.1]

/-- Target-endpoint strip values of the three retained edges at one colored
element. -/
def PlanarPresentation.retainedStripElementDrawingInwardValues
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (orientation : presentation.stripNormalizedOrthogonalDrawing.Orientation)
    (color : WireColor) (atom : Nat) (translate : Cell) : List Bool :=
  (problem.contractedEdgesForElement color atom).map fun edge =>
    presentation.stripDrawingEndpointInward orientation (.target edge) translate

/-- Retained endpoint values at a degree-three element satisfy exact-one in
every translated strip occurrence. -/
theorem ContinuousPlanarPresentation.retainedStripElementDrawingInwardValues_exactlyOne
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (horizontal : problem.IsOneDimensional)
    (sourceInside :
      presentation.toPlanarPresentation.drawing
        |>.RoutePointsInExpandedVerticalBand)
    (collisionFree :
      presentation.toPlanarPresentation.FinalStripAssignmentsCollisionFree)
    (orientation :
      presentation.toPlanarPresentation.stripNormalizedOrthogonalDrawing
        |>.Orientation)
    (valid :
      presentation.toPlanarPresentation.stripNormalizedOrthogonalDrawing
        |>.IsOrientation orientation)
    (color : WireColor) (atom : Nat)
    (atomLt : atom < problem.elementCount color)
    (degreeThree : problem.degree color atom = 3)
    (translate : Cell) :
    PeriodicOneInThree.ExactlyOne
      (presentation.toPlanarPresentation
        |>.retainedStripElementDrawingInwardValues orientation color atom
          translate) := by
  let planar := presentation.toPlanarPresentation
  let vertex := PeriodicThreeDMVertex.element color atom
  have vertexMember : vertex ∈ problem.contractedGraph.vertices := by
    cases color <;> simp_all [vertex, contractedGraph, tripleVertices,
      contractedElementVertices, contractedElementVerticesForColor,
      incidenceColors]
  have portPerm :=
    PlanarPresentation.normalizedVertexPortEndpoints_perm
      presentation wellFormed degree vertexMember
  have targetPerm := contractedEdgesForElement_targets_perm_endpointsAt
    problem degree color atom atomLt degreeThree
  have endpointPerm :
      List.Perm (planar.normalizedVertexPortEndpoints vertex)
        ((problem.contractedEdgesForElement color atom).map
          ContractedEndpoint.target) :=
    portPerm.trans targetPerm.symm
  have valuePerm := endpointPerm.map fun endpoint =>
    planar.stripDrawingEndpointInward orientation endpoint translate
  have westValue :=
    presentation.stripDrawingEndpointInward_endpointAtVertexPort
      wellFormed degree orientation vertexMember translate .west
  have northValue :=
    presentation.stripDrawingEndpointInward_endpointAtVertexPort
      wellFormed degree orientation vertexMember translate .north
  have eastValue :=
    presentation.stripDrawingEndpointInward_endpointAtVertexPort
      wellFormed degree orientation vertexMember translate .east
  dsimp only at westValue northValue eastValue
  simp only [CanonicalVertexPort.side] at westValue northValue eastValue
  let occurrence := Cell.add
    (stripReflectedLocation planar.finalNormalizationPeriod
      (planar.finalNormalizationPosition vertex))
    (planar.stripPeriodTranslation translate)
  have valuesPerm :
      List.Perm
        [orientation occurrence .west,
          orientation occurrence .north,
          orientation occurrence .east]
        (planar.retainedStripElementDrawingInwardValues orientation color atom
          translate) := by
    change List.Perm
      [planar.stripDrawingEndpointInward orientation
          (planar.endpointAtVertexPort vertex .west) translate,
        planar.stripDrawingEndpointInward orientation
          (planar.endpointAtVertexPort vertex .north) translate,
        planar.stripDrawingEndpointInward orientation
          (planar.endpointAtVertexPort vertex .east) translate]
      _ at valuePerm
    dsimp only [planar] at valuePerm ⊢
    rw [westValue, northValue, eastValue] at valuePerm
    simpa [occurrence,
      PlanarPresentation.retainedStripElementDrawingInwardValues,
      List.map_map, Function.comp_def] using valuePerm
  have localConstraint :=
    presentation.finalStripVertexCellType_satisfied_of_orientation
      wellFormed degree horizontal sourceInside collisionFree orientation valid
        vertexMember translate
  change
    [orientation occurrence .west,
      orientation occurrence .north,
      orientation occurrence .east].count true = 1 at localConstraint
  change (planar.retainedStripElementDrawingInwardValues orientation color atom
    translate).count true = 1
  rw [← valuesPerm.count_eq]
  exact localConstraint

end PeriodicThreeDM

end LeanTrominoes
