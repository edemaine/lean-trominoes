/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationReverseOrientation
import LeanTrominoes.PeriodicThreeDMNormalizationStripOrientationSiteMembership
import LeanTrominoes.OrthogonalDrawingOrientationInterface

/-!
# Reading endpoint values from a normalized strip orientation
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

set_option maxRecDepth 2048
set_option linter.constructorNameAsVariable false

/-- The infinite-lift strip location of one contracted endpoint, based at the
rectangular block translate of its endpoint vertex. -/
def PlanarPresentation.stripEndpointDrawingLocation
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (endpoint : ContractedEndpoint) (translate : Cell) : Cell :=
  Cell.add
    (stripReflectedLocation presentation.finalNormalizationPeriod
      (presentation.finalNormalizationPosition endpoint.vertex))
    (presentation.stripPeriodTranslation translate)

/-- Read the inward half-edge value at a contracted endpoint's normalized
strip vertex port. -/
def PlanarPresentation.stripDrawingEndpointInward
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (orientation : presentation.stripNormalizedOrthogonalDrawing.Orientation)
    (endpoint : ContractedEndpoint) (translate : Cell) : Bool :=
  orientation (presentation.stripEndpointDrawingLocation endpoint translate)
    (endpoint.finalNormalizedPort presentation).side

/-- Extract the original triple-to-element Boolean from an arbitrary strip
orientation. -/
noncomputable def PlanarPresentation.reverseStripGraphOrientation
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (orientation : presentation.stripNormalizedOrthogonalDrawing.Orientation) :
    problem.GraphOrientation :=
  fun tag translate =>
    !(presentation.stripDrawingEndpointInward orientation
      (problem.contractedTripleEndpointForTag tag) translate)

/-- At an explicit occurrence of a listed strip vertex, global validity
supplies its local vertex constraint. -/
theorem ContinuousPlanarPresentation.finalStripVertexCellType_satisfied_of_orientation
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
    {vertex : PeriodicThreeDMVertex}
    (vertexMember : vertex ∈ problem.contractedGraph.vertices)
    (translate : Cell) :
    let planar := presentation.toPlanarPresentation
    PeriodicOrthogonalDrawing.satisfiesOrientation
      (planar.finalVertexCellType vertex)
      (fun side => orientation
        (Cell.add
          (stripReflectedLocation planar.finalNormalizationPeriod
            (planar.finalNormalizationPosition vertex))
          (planar.stripPeriodTranslation translate)) side) := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  have siteMember := planar.finalStripOrientationSite_vertex_mem vertexMember
  have lookup := presentation.finalStripOrientationSiteAt_periodOccurrence
    wellFormed degree horizontal sourceInside collisionFree siteMember
      (translate := translate)
  have cellType :=
    planar.stripNormalizedOrthogonalDrawing_getAt_eq_of_site_lookup
      collisionFree lookup
  have cellType' :
      planar.stripNormalizedOrthogonalDrawing.getAt
          (Cell.add
            (stripReflectedLocation planar.finalNormalizationPeriod
              (planar.finalNormalizationPosition vertex))
            (planar.stripPeriodTranslation translate)) =
        planar.finalVertexCellType vertex := by
    simpa [FinalOrientationSite.cellType, FinalOrientationSite.point] using
      cellType
  let occurrence := Cell.add
    (stripReflectedLocation planar.finalNormalizationPeriod
      (planar.finalNormalizationPosition vertex))
    (planar.stripPeriodTranslation translate)
  rcases PeriodicOrthogonalDrawing.IsOrientation.localConstraint
      (drawing := planar.stripNormalizedOrthogonalDrawing)
      (orientation := orientation) valid occurrence with
    ⟨localConstraint⟩
  rw [show occurrence = Cell.add
      (stripReflectedLocation planar.finalNormalizationPeriod
        (planar.finalNormalizationPosition vertex))
      (planar.stripPeriodTranslation translate) by rfl] at localConstraint
  rw [cellType'] at localConstraint
  simpa [planar] using localConstraint

/-- Any two contracted endpoints at the same translated triple vertex have
equal inward strip-orientation values. -/
theorem ContinuousPlanarPresentation.stripDrawingEndpointInward_eq_at_triple
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
    {first second : ContractedEndpoint}
    (firstMember : first ∈ problem.contractedEndpoints)
    (tripleIndex : Nat)
    (firstVertex : first.vertex = .triple tripleIndex)
    (secondVertex : second.vertex = .triple tripleIndex)
    (translate : Cell) :
    presentation.toPlanarPresentation.stripDrawingEndpointInward orientation
        first translate =
      presentation.toPlanarPresentation.stripDrawingEndpointInward orientation
        second translate := by
  let planar := presentation.toPlanarPresentation
  have vertexMember := first.vertex_mem_of_mem firstMember
  rw [firstVertex] at vertexMember
  have localConstraint :=
    presentation.finalStripVertexCellType_satisfied_of_orientation
      wellFormed degree horizontal sourceInside collisionFree orientation valid
        vertexMember translate
  change PeriodicOrthogonalDrawing.satisfiesOrientation
      (planar.finalVertexCellType (.triple tripleIndex)) _ at localConstraint
  change orientation (planar.stripEndpointDrawingLocation first translate)
      (first.finalNormalizedPort planar).side =
    orientation (planar.stripEndpointDrawingLocation second translate)
      (second.finalNormalizedPort planar).side
  rw [show planar.stripEndpointDrawingLocation first translate =
      Cell.add
        (stripReflectedLocation planar.finalNormalizationPeriod
          (planar.finalNormalizationPosition (.triple tripleIndex)))
        (planar.stripPeriodTranslation translate) by
      simp [PlanarPresentation.stripEndpointDrawingLocation, firstVertex]]
  rw [show planar.stripEndpointDrawingLocation second translate =
      Cell.add
        (stripReflectedLocation planar.finalNormalizationPeriod
          (planar.finalNormalizationPosition (.triple tripleIndex)))
        (planar.stripPeriodTranslation translate) by
      simp [PlanarPresentation.stripEndpointDrawingLocation, secondVertex]]
  dsimp only [planar]
  simp only [PlanarPresentation.finalVertexCellType,
    PeriodicOrthogonalDrawing.satisfiesOrientation] at localConstraint
  generalize firstPortEq : first.finalNormalizedPort planar = firstPort
  generalize secondPortEq : second.finalNormalizedPort planar = secondPort
  cases firstPort <;> cases secondPort <;>
    simp_all [CanonicalVertexPort.side]

end PeriodicThreeDM

end LeanTrominoes
