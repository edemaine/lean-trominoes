import LeanTrominoes.OrthogonalPolylineUnitSubdivisionScaling
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonUnitRoutes
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMNormalized
import LeanTrominoes.PositionedPeriodicCNFRibbonScaling

/-!
# Interior points in padded normalized ribbon routes

The corrected ribbon construction doubles its source presentation before
anchor normalization.  Doubling inserts a genuine lattice point into the
first segment of every active unit-subdivided route, while anchor
normalization leaves the physical variable-to-clause route unchanged.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open PeriodicOrthocrossing

/-- Every active route in the padded, anchor-normalized source contains at
least one point strictly between its two advertised endpoints. -/
theorem paddedNormalizedOccurrenceUnitSourceRoute_length_ge_three
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (entry :
      ActiveOccurrenceEntry
        (normalizedPositionedSource
          (source.scale 2) (placement.scale 2)).erase) :
    3 ≤
      (occurrenceUnitSourceRoute
        (normalizedRibbonReadyIncidencePresentation presentation.scaleTwo
          |>.toPlanarIncidencePresentation)
        entry).length := by
  let padded := presentation.scaleTwo
  let normalized :=
    normalizedRibbonReadyIncidencePresentation padded
  let planar := normalized.toPlanarIncidencePresentation
  let data := occurrenceSpliceData planar entry
  have normalizedMember :
      data.indexed ∈
        (PeriodicCNF.incidencesWithMetadata
          ((source.scale 2).erase.anchorNormalize)).zipIdx := by
    simpa only [normalizedPositionedSource,
      PositionedPeriodicCNF.erase_anchorNormalize] using
        data.indexedMember
  rw [
    PeriodicCNF.incidencesWithMetadata_anchorNormalize,
    List.zipIdx_map] at normalizedMember
  rcases List.mem_map.mp normalizedMember with
    ⟨originalIndexed, originalMember, indexedEqual⟩
  have indexedEqual' :
      data.indexed =
        (originalIndexed.1.anchorNormalize, originalIndexed.2) :=
    indexedEqual.symm
  have originalMember' :
      originalIndexed ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx := by
    simpa using originalMember
  have originalLength :
      2 ≤
        (presentation.toPlanarIncidencePresentation
          |>.variableToClauseRoute originalIndexed.1).length := by
    have segmentsNonempty :=
      presentation.toPlanarIncidencePresentation
        |>.route_segments_ne_nil_of_tagged originalMember'
    have segmentsPositive :
        0 <
          (gridPolylineSegments
            (presentation.routes
              originalIndexed.1.clauseIndex
              originalIndexed.1.literalIndex)).length :=
      List.length_pos_iff.mpr segmentsNonempty
    rw [gridPolylineSegments_length] at segmentsPositive
    simpa [
      PositionedPeriodicCNF.PlanarIncidencePresentation.variableToClauseRoute,
      translatePolyline] using (show
        2 ≤
          (presentation.routes
            originalIndexed.1.clauseIndex
            originalIndexed.1.literalIndex).length by
        omega)
  have originalOrthogonal :
      OrthogonalPolyline
        (presentation.toPlanarIncidencePresentation
          |>.variableToClauseRoute originalIndexed.1) :=
    presentation.toPlanarIncidencePresentation
      |>.variableToClauseRoute_orthogonal originalMember'
  have paddedRoute :
      padded.toPlanarIncidencePresentation.variableToClauseRoute
          originalIndexed.1 =
        scalePolyline 2
          (presentation.toPlanarIncidencePresentation
            |>.variableToClauseRoute originalIndexed.1) := by
    exact
      presentation.toContinuousPlanarIncidencePresentation
        |>.variableToClauseRoute_scale (by decide) originalIndexed.1
  change
    3 ≤
      (AxisDirection.unitSubdividePolyline
        (planar.variableToClauseRoute data.indexed.1)).length
  rw [indexedEqual']
  change
    3 ≤
      (AxisDirection.unitSubdividePolyline
        (padded.toPlanarIncidencePresentation.anchorNormalize
          |>.variableToClauseRoute originalIndexed.1.anchorNormalize)).length
  rw [PositionedPeriodicCNF.PlanarIncidencePresentation.variableToClauseRoute_anchorNormalize,
    paddedRoute]
  exact
    AxisDirection.unitSubdividePolyline_scale_two_length_ge_three
      originalLength originalOrthogonal

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
