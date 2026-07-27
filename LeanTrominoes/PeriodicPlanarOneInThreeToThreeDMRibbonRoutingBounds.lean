import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonCorridorBounds
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonRouting

/-!
# Pointwise bounds for complete ribbon routes

Every listed point of a corrected three-strand route belongs either to the
source-variable endpoint block, to a block along the unitized corridor, or
to the lifted source-clause endpoint block.  This decomposition is the
coordinate-bound and far-separation interface for the complete joined route.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget

/-- The variable endpoint is one of the selected unit source route's listed
points. -/
theorem occurrenceUnitSourceRoute_variableEndpoint_mem
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    placement.position entry.1.1 ∈
      occurrenceUnitSourceRoute presentation entry := by
  let data := occurrenceSpliceData presentation entry
  have atomEq :
      data.tagged.1.atom = entry.1.1 :=
    (PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom
      source.erase entry.1.1 entry.1.2 data.tagged
      data.occurrenceLookup).2
  have endpoint :=
    (occurrenceUnitSourceRoute_endpoints
      presentation entry).1
  have headEq :
      (occurrenceUnitSourceRoute presentation entry).head? =
        some (placement.position entry.1.1) := by
    simpa [data, atomEq] using endpoint
  cases routeEquation :
      occurrenceUnitSourceRoute presentation entry with
  | nil =>
      simp [routeEquation] at headEq
  | cons first rest =>
      have firstEq :
          first = placement.position entry.1.1 := by
        rw [routeEquation] at headEq
        exact Option.some.inj headEq
      subst first
      simp

/-- The lifted clause endpoint is one of the selected unit source route's
listed points. -/
theorem occurrenceUnitSourceRoute_clauseEndpoint_mem
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    let data := occurrenceSpliceData presentation entry
    PositionedPeriodicCNF.variableToClauseTarget
        placement data.positionedClause data.tagged.1 ∈
      occurrenceUnitSourceRoute presentation entry := by
  let data := occurrenceSpliceData presentation entry
  exact
    mem_of_getLast?_eq_some
      (occurrenceUnitSourceRoute_endpoints
        presentation entry).2

/-- Pointwise ownership decomposition for one complete corrected colored
route. -/
theorem occurrenceRibbonThreeStrandRoute_points_bounded
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) {point : Cell}
    (member :
      point ∈ occurrenceRibbonThreeStrandRoute
        presentation entry color) :
    InRibbonMacrocell (placement.position entry.1.1) point ∨
      (∃ center ∈ occurrenceUnitSourceRoute presentation entry,
        InRibbonMacrocell center point) ∨
      let data := occurrenceSpliceData presentation entry
      InRibbonMacrocell
        (PositionedPeriodicCNF.variableToClauseTarget
          placement data.positionedClause data.tagged.1)
        point := by
  unfold occurrenceRibbonThreeStrandRoute at member
  rcases mem_joinAtEndpoint member with
      prefixMember | clauseMember
  · rcases mem_joinAtEndpoint prefixMember with
        variableMember | coreMember
    · exact
        Or.inl
          (occurrenceRibbonVariableStub_points_bounded
            presentation entry color variableMember)
    · exact
        Or.inr
          (Or.inl
            (occurrenceRibbonCorridorCore_points_bounded
              presentation entry color coreMember))
  · exact
      Or.inr
        (Or.inr
          (occurrenceRibbonClauseStub_points_bounded
            presentation entry color clauseMember))

/-- Every point of a complete corrected route lies in the refined block of
some listed point on its selected unit source route. -/
theorem occurrenceRibbonThreeStrandRoute_point_in_source_macrocell
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) {point : Cell}
    (member :
      point ∈ occurrenceRibbonThreeStrandRoute
        presentation entry color) :
    ∃ center ∈ occurrenceUnitSourceRoute presentation entry,
      InRibbonMacrocell center point := by
  rcases
      occurrenceRibbonThreeStrandRoute_points_bounded
        presentation entry color member with
      variableBounded | coreBounded | clauseBounded
  · exact
      ⟨placement.position entry.1.1,
        occurrenceUnitSourceRoute_variableEndpoint_mem
          presentation entry,
        variableBounded⟩
  · exact coreBounded
  · let data := occurrenceSpliceData presentation entry
    exact
      ⟨PositionedPeriodicCNF.variableToClauseTarget
          placement data.positionedClause data.tagged.1,
        occurrenceUnitSourceRoute_clauseEndpoint_mem
          presentation entry,
        clauseBounded⟩

/-- Unit subdivision preserves the ordinary pointwise source halo bound. -/
theorem occurrenceUnitSourceRoute_pointsInsideExpandedSquare
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (sourceBounds :
      presentation.RebasedRoutePointsInExpandedSquare)
    (entry : ActiveOccurrenceEntry source.erase)
    {point : Cell}
    (pointMember :
      point ∈ occurrenceUnitSourceRoute presentation entry) :
    (PositionedPeriodicCNF.incidenceDrawing
      source placement presentation.routes)
      |>.PositionInExpandedSquare point := by
  let data := occurrenceSpliceData presentation entry
  have originalPointInside :
      ∀ originalPoint ∈ occurrenceSourceRoute presentation entry,
        (PositionedPeriodicCNF.incidenceDrawing
          source placement presentation.routes)
          |>.PositionInExpandedSquare originalPoint := by
    intro originalPoint originalPointMember
    exact
      sourceBounds data.indexed data.indexedMember
        originalPoint originalPointMember
  rcases
      AxisDirection.unitSubdividePolyline_mem_original_or_segmentInterior
        (occurrenceSourceRoute_orthogonal presentation entry)
        pointMember with
    originalMember | ⟨segment, segmentMember, interior⟩
  · exact originalPointInside point originalMember
  · have endpoints :=
      gridPolylineSegments_endpoints_mem segmentMember
    exact
      PeriodicGridDrawing.expanded_of_contains
        (originalPointInside segment.start endpoints.1)
        (originalPointInside segment.finish endpoints.2)
        (GridSegment.contains_of_interiorContains interior)

/-- Unit subdivision also preserves a one-unit upper halo margin. -/
theorem occurrenceUnitSourceRoute_pointsInsideExpandedSquareWithUpperMargin
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (sourceBounds :
      presentation.RebasedRoutePointsInExpandedSquareWithUpperMargin)
    (entry : ActiveOccurrenceEntry source.erase)
    {point : Cell}
    (pointMember :
      point ∈ occurrenceUnitSourceRoute presentation entry) :
    (PositionedPeriodicCNF.incidenceDrawing
      source placement presentation.routes)
      |>.PositionInExpandedSquareWithUpperMargin point := by
  let data := occurrenceSpliceData presentation entry
  have originalPointInside :
      ∀ originalPoint ∈ occurrenceSourceRoute presentation entry,
        (PositionedPeriodicCNF.incidenceDrawing
          source placement presentation.routes)
          |>.PositionInExpandedSquareWithUpperMargin originalPoint := by
    intro originalPoint originalPointMember
    exact
      sourceBounds data.indexed data.indexedMember
        originalPoint originalPointMember
  rcases
      AxisDirection.unitSubdividePolyline_mem_original_or_segmentInterior
        (occurrenceSourceRoute_orthogonal presentation entry)
        pointMember with
    originalMember | ⟨segment, segmentMember, interior⟩
  · exact originalPointInside point originalMember
  · have endpoints :=
      gridPolylineSegments_endpoints_mem segmentMember
    exact
      PeriodicGridDrawing.expandedWithUpperMargin_of_contains
        (originalPointInside segment.start endpoints.1)
        (originalPointInside segment.finish endpoints.2)
        (GridSegment.contains_of_interiorContains interior)

/-- A point in the closed refined block above a source point with one unit
of upper halo margin lies in the corrected assembled open halo. -/
theorem inRibbonMacrocell_insideExpandedSquare
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.ContinuousPlanarIncidencePresentation placement)
    {center point : Cell}
    (centerInside :
      (PositionedPeriodicCNF.incidenceDrawing
        source placement presentation.routes)
        |>.PositionInExpandedSquareWithUpperMargin center)
    (bounded : InRibbonMacrocell center point) :
    (assembledDrawing
      (ribbonThreeStrandRouting presentation))
      |>.PositionInExpandedSquare point := by
  simp only
      [PeriodicGridDrawing.PositionInExpandedSquareWithUpperMargin]
    at centerInside
  simp only [PeriodicGridDrawing.PositionInExpandedSquare]
  rw [PositionedPeriodicCNF.incidenceDrawing_gridSize
    source placement presentation.routes presentation.periodPositive]
    at centerInside
  rw [assembledDrawing_gridSize]
  rcases center with ⟨centerX, centerY⟩
  rcases point with ⟨pointX, pointY⟩
  simp only [InRibbonMacrocell, ribbonMacrocellOrigin,
    ribbonThreeStrandRouting, standardThreeStrandLayout,
    Cell.scale] at bounded ⊢
  omega

/-- Every point of a complete corrected occurrence route is halo-bounded
once the source rebased routes carry one unit of upper margin. -/
theorem occurrenceRibbonThreeStrandRoute_pointsInsideExpandedSquare
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.ContinuousPlanarIncidencePresentation placement)
    (sourceBounds :
      presentation.toPlanarIncidencePresentation
        |>.RebasedRoutePointsInExpandedSquareWithUpperMargin)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor)
    {point : Cell}
    (pointMember :
      point ∈ occurrenceRibbonThreeStrandRoute
        presentation.toPlanarIncidencePresentation entry color) :
    (assembledDrawing
      (ribbonThreeStrandRouting presentation))
      |>.PositionInExpandedSquare point := by
  rcases
      occurrenceRibbonThreeStrandRoute_point_in_source_macrocell
        presentation.toPlanarIncidencePresentation
        entry color pointMember with
    ⟨center, centerMember, bounded⟩
  exact
    inRibbonMacrocell_insideExpandedSquare presentation
      (occurrenceUnitSourceRoute_pointsInsideExpandedSquareWithUpperMargin
        presentation.toPlanarIncidencePresentation
        sourceBounds entry centerMember)
      bounded

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
