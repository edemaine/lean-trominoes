import LeanTrominoes.OrthogonalPolylineRibbon
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVertexGeometry

/-!
# Ribbon corridors for the planar exact-one to 3DM reduction

This file replaces the central part of the earlier three-strand candidate.
Rather than diagonally translating a refined source route, each color uses
the certified normal-offset ribbon construction.  The three positive lane
distances fit strictly inside the `128`-cell refinement clearance.

Endpoint fans into the finite variable and clause gadgets are deliberately
left to the next layer.  Here we prove the exact central endpoints,
nondegeneracy inherited from every genuine incidence, and orthogonality.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PeriodicOrthocrossing

/-- Three nested lanes on the right side of each directed source route. -/
def standardRibbonLaneDistance : WireColor → Int
  | .red => 40
  | .green => 44
  | .blue => 48

theorem standardRibbonLaneDistance_positive (color : WireColor) :
    0 < standardRibbonLaneDistance color := by
  cases color <;> decide

theorem standardRibbonLaneDistance_lt_factor (color : WireColor) :
    standardRibbonLaneDistance color <
      standardThreeStrandLayout.factor := by
  cases color <;> decide

/-- The rebased variable-to-clause source route selected for one active
occurrence. -/
noncomputable def occurrenceSourceRoute
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) : List Cell :=
  let data := occurrenceSpliceData presentation entry
  presentation.variableToClauseRoute data.indexed.1

/-- Every genuine incidence route has at least two points.  Reversal and
rebasing preserve the length of the original certified route. -/
theorem occurrenceSourceRoute_length
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase) :
    2 ≤ (occurrenceSourceRoute presentation entry).length := by
  let data := occurrenceSpliceData presentation entry
  have segmentsNonempty :=
    presentation.route_segments_ne_nil_of_tagged
      data.indexedMember
  have segmentsPositive :
      0 <
        (gridPolylineSegments
          (presentation.routes
            data.indexed.1.clauseIndex
            data.indexed.1.literalIndex)).length :=
    List.length_pos_iff.mpr segmentsNonempty
  rw [gridPolylineSegments_length] at segmentsPositive
  change
    2 ≤
      (presentation.variableToClauseRoute data.indexed.1).length
  simpa [PositionedPeriodicCNF.PlanarIncidencePresentation.variableToClauseRoute,
    translatePolyline] using (show
      2 ≤
        (presentation.routes
          data.indexed.1.clauseIndex
          data.indexed.1.literalIndex).length by
      omega)

/-- One normal-offset colored lane through the refined source corridor. -/
noncomputable def occurrenceRibbonLane
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) : List Cell :=
  ribbonPolyline
    standardThreeStrandLayout.factor
    (standardRibbonLaneDistance color)
    (occurrenceSourceRoute presentation entry)

/-- The computed refined endpoint of a colored lane at the variable side. -/
noncomputable def occurrenceRibbonStart
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) : Cell :=
  ribbonPolylineStart
    standardThreeStrandLayout.factor
    (standardRibbonLaneDistance color)
    (occurrenceSourceRoute presentation entry)

/-- The computed refined endpoint of a colored lane at the clause side. -/
noncomputable def occurrenceRibbonEnd
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) : Cell :=
  ribbonPolylineEnd
    standardThreeStrandLayout.factor
    (standardRibbonLaneDistance color)
    (occurrenceSourceRoute presentation entry)

/-- Exact outer endpoints of one central ribbon lane. -/
theorem occurrenceRibbonLane_endpoints
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    (occurrenceRibbonLane presentation entry color).head? =
        some (occurrenceRibbonStart presentation entry color) ∧
      (occurrenceRibbonLane presentation entry color).getLast? =
        some (occurrenceRibbonEnd presentation entry color) := by
  have length := occurrenceSourceRoute_length presentation entry
  have nonempty :
      occurrenceSourceRoute presentation entry ≠ [] := by
    intro empty
    rw [empty] at length
    simp at length
  exact
    ⟨ribbonPolyline_head?_eq_some_start
        standardThreeStrandLayout.factor
        (standardRibbonLaneDistance color) nonempty,
      ribbonPolyline_getLast?_eq_some_end
        standardThreeStrandLayout.factor
        (standardRibbonLaneDistance color) nonempty⟩

/-- The corrected central colored lane is rectilinear. -/
theorem occurrenceRibbonLane_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    OrthogonalPolyline
      (occurrenceRibbonLane presentation entry color) := by
  apply ribbonPolyline_orthogonal
    standardThreeStrandLayout.factorPositive
    (standardRibbonLaneDistance_positive color)
  exact
    presentation.variableToClauseRoute_orthogonal
      (occurrenceSpliceData presentation entry).indexedMember

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
