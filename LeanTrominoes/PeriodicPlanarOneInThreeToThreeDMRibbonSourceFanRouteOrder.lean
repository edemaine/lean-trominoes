import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceClauseRouteOrder
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceCoordinatedStubs
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableFanOrder

/-!
# Source route orders supply coordinated ribbon fans

The finite coordinated endpoint routers need one common compatibility
condition for all source variable and clause fans.  The clause half is
already forced by the unit-elimination templates.  This file isolates the
remaining variable-side rotation invariant at its natural source boundary:
the three actual outgoing directions must follow occurrence slots
`first`, `second`, and `third` clockwise.

Variables with fewer than three occurrences need no order premise.  When
the invariant does hold, it combines with the unit-elimination clause-route
order to discharge the complete `SourceRibbonFansClockwiseCompatible`
condition used by the coordinated source stub system.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open PlanarThreeDM PeriodicOrthocrossing

/-- At every degree-three source variable, the actual outgoing directions
follow the source occurrence-slot order clockwise. -/
def SourceVariableDirectionsInOccurrenceOrder
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement) : Prop :=
  ∀ (first second third : ActiveOccurrenceEntry source.erase),
    first.1.2 = .first →
    second.1.2 = .second →
    third.1.2 = .third →
    first.1.1 = second.1.1 →
    first.1.1 = third.1.1 →
    AxisDirection.InClockwiseOrder
      (occurrenceSourceVariableDirection presentation first)
      (occurrenceSourceVariableDirection presentation second)
      (occurrenceSourceVariableDirection presentation third)

/-- The source variable rotation invariant discharges every finite
variable-fan table lookup. -/
theorem sourceVariableRibbonFanData_isClockwiseCompatible_of_occurrenceOrder
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (ordered :
      SourceVariableDirectionsInOccurrenceOrder
        presentation.toPlanarIncidencePresentation)
    (entry : ActiveOccurrenceEntry source.erase) :
    (sourceVariableRibbonFanData
        presentation.toPlanarIncidencePresentation entry)
      |>.IsClockwiseCompatible := by
  let planar := presentation.toPlanarIncidencePresentation
  let data := sourceVariableRibbonFanData planar entry
  apply
    (VariableRibbonFanData.sourceVariableRibbonFanData_isClockwiseCompatible_iff
      presentation entry).2
  intro count
  have dataCount : data.count = 3 := by
    simpa [data] using count
  have firstActiveData : data.SlotActive .first := by
    change VariableSiteSlot.first.index < data.count
    rw [dataCount]
    decide
  have secondActiveData : data.SlotActive .second := by
    change VariableSiteSlot.second.index < data.count
    rw [dataCount]
    decide
  have thirdActiveData : data.SlotActive .third := by
    change VariableSiteSlot.third.index < data.count
    rw [dataCount]
    decide
  have firstActive : data.outerData.SlotActive .first := by
    exact
      (VariableRibbonFanData.outerData_slotActive
        data .first).2 firstActiveData
  have secondActive : data.outerData.SlotActive .second := by
    exact
      (VariableRibbonFanData.outerData_slotActive
        data .second).2 secondActiveData
  have thirdActive : data.outerData.SlotActive .third := by
    exact
      (VariableRibbonFanData.outerData_slotActive
        data .third).2 thirdActiveData
  let first :=
    VariableRibbonFanData.sourceVariableRibbonFanEntryAtActiveSlot
      presentation entry .first firstActive
  let second :=
    VariableRibbonFanData.sourceVariableRibbonFanEntryAtActiveSlot
      presentation entry .second secondActive
  let third :=
    VariableRibbonFanData.sourceVariableRibbonFanEntryAtActiveSlot
      presentation entry .third thirdActive
  have clockwise := ordered first second third
    (by rfl)
    (by rfl)
    (by rfl)
    (by simp [first, second])
    (by simp [first, third])
  have firstDirection :
      data.direction .first =
        occurrenceSourceVariableDirection planar first := by
    simpa [data, first] using
      VariableRibbonFanData.sourceVariableRibbonFanData_direction_of_same_atom
        planar entry first (by simp [first])
  have secondDirection :
      data.direction .second =
        occurrenceSourceVariableDirection planar second := by
    simpa [data, second] using
      VariableRibbonFanData.sourceVariableRibbonFanData_direction_of_same_atom
        planar entry second (by simp [second])
  have thirdDirection :
      data.direction .third =
        occurrenceSourceVariableDirection planar third := by
    simpa [data, third] using
      VariableRibbonFanData.sourceVariableRibbonFanData_direction_of_same_atom
        planar entry third (by simp [third])
  rw [firstDirection, secondDirection, thirdDirection]
  exact clockwise

/-- Variable occurrence order and unit-elimination clause order together
supply the single compatibility premise required by all coordinated source
fans. -/
theorem sourceRibbonFansClockwiseCompatible_of_routeOrders
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity :
      PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (variableOrdered :
      SourceVariableDirectionsInOccurrenceOrder
        presentation.toPlanarIncidencePresentation)
    (clauseOrdered :
      source.TernaryClauseRoutesInUnitEliminationOrder
        presentation.toPlanarIncidencePresentation.routes) :
    SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation := by
  constructor
  · intro entry
    exact
      sourceVariableRibbonFanData_isClockwiseCompatible_of_occurrenceOrder
        presentation variableOrdered entry
  · intro entry
    exact
      sourceClauseRibbonFanData_isClockwiseCompatible_of_unitEliminationOrder
        presentation width occurrences arity clauseOrdered entry

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
