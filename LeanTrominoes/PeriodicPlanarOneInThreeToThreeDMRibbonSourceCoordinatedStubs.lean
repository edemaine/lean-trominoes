import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceFanPorts
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonEndpointFanSystem

/-!
# Translated coordinated source ribbon stubs

This file instantiates the finite coordinated variable and clause fans at
the actual source macrocells.  A source-level compatibility predicate records
the remaining cyclic-order obligation.  Under that obligation and source
width three, the translated routes have exactly the occurrence-level
endpoints required by the central ribbon corridor and the assembled 3DM
drawing.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM
open PeriodicOrthocrossing

/-- Every actual variable and lifted-clause fan has one of the clockwise
direction orders supported by the finite coordinated routing tables. -/
def SourceRibbonFansClockwiseCompatible
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement) : Prop :=
  (∀ entry : ActiveOccurrenceEntry source.erase,
      (sourceVariableRibbonFanData presentation entry).IsClockwiseCompatible) ∧
    ∀ entry : ActiveOccurrenceEntry source.erase,
      (sourceClauseRibbonFanData presentation
        (occurrenceSourceClauseTarget presentation entry))
        |>.IsClockwiseCompatible

/-- The coordinated variable fan for one occurrence, translated into its
actual source-variable macrocell. -/
noncomputable def occurrenceCoordinatedRibbonVariableStub
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) : List Cell :=
  let data := sourceVariableRibbonFanData presentation entry
  translatePolyline
    (ribbonMacrocellOrigin (placement.position entry.1.1))
    (data.coordinatedRoute
      (occurrenceVariableSiteSlot entry.1.2) color)

/-- The coordinated clause fan for one occurrence, translated into its
actual lifted source-clause macrocell. -/
noncomputable def occurrenceCoordinatedRibbonClauseStub
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) : List Cell :=
  let target := occurrenceSourceClauseTarget presentation entry
  let data := sourceClauseRibbonFanData presentation target
  translatePolyline
    (ribbonMacrocellOrigin target)
    (data.coordinatedRoute
      (occurrenceClauseTerminalGroup source.erase entry)
      (routedRibbonLane source.erase entry color))

/-- The translated coordinated variable fan begins at the assembled
variable port and ends at the first central-corridor boundary point. -/
theorem occurrenceCoordinatedRibbonVariableStub_endpoints
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible presentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    (occurrenceCoordinatedRibbonVariableStub
        presentation entry color).head? =
        some (Cell.add
          (constructedVariableOrigin placement
            standardThreeStrandLayout entry.1.1)
          (routedVariablePortPosition source.erase entry color)) ∧
      (occurrenceCoordinatedRibbonVariableStub
        presentation entry color).getLast? =
        some (ribbonCorridorRouteStart
          (routedRibbonLane source.erase entry color)
          (occurrenceUnitSourceRoute presentation entry)) := by
  let data := sourceVariableRibbonFanData presentation entry
  let slot := occurrenceVariableSiteSlot entry.1.2
  have active : data.SlotActive slot :=
    VariableRibbonFanData.sourceVariableRibbonFanData_slotActive
      presentation entry
  have dataCompatible : data.IsClockwiseCompatible :=
    compatible.1 entry
  have portEq :
      data.port slot active color =
        occurrenceVariableRibbonFanPort
          source.erase entry color := by
    simpa [data, slot] using
      VariableRibbonFanData.sourceVariableRibbonFanData_port
        presentation entry color
  constructor
  · rw [show
      occurrenceCoordinatedRibbonVariableStub
          presentation entry color =
        translatePolyline
          (ribbonMacrocellOrigin (placement.position entry.1.1))
          (data.coordinatedRoute slot color) by
            rfl]
    simp [VariableRibbonFanData.coordinatedRoute_head?
        data slot active color,
      portEq,
      occurrenceVariableRibbonFanPort,
      PeriodicOrthocrossing.translatePolyline,
      constructedVariableOrigin, ribbonMacrocellOrigin,
      Cell.add]
    all_goals omega
  · rw [occurrenceRibbonCorridorRouteStart_eq
      presentation entry color]
    rw [show
      occurrenceCoordinatedRibbonVariableStub
          presentation entry color =
        translatePolyline
          (ribbonMacrocellOrigin (placement.position entry.1.1))
          (data.coordinatedRoute slot color) by
            rfl]
    simp only [PeriodicOrthocrossing.translatePolyline]
    rw [List.getLast?_map,
      VariableRibbonFanData.coordinatedRoute_getLast?
        data dataCompatible slot active color]
    simp only [Option.map_some]
    rw [VariableRibbonFanData.sourceVariableRibbonFanData_direction
      presentation entry]
    rw [VariableRibbonFanData.sourceVariableRibbonFanData_ribbonLaneForColor_of_same_atom
        presentation entry entry rfl color]
    rfl

/-- The translated coordinated clause fan begins at the final
central-corridor boundary point and ends at the assembled translated clause
port. -/
theorem occurrenceCoordinatedRibbonClauseStub_endpoints
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible presentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    (occurrenceCoordinatedRibbonClauseStub
        presentation entry color).head? =
        some (ribbonCorridorRouteEnd
          (routedRibbonLane source.erase entry color)
          (occurrenceUnitSourceRoute presentation entry)) ∧
      (occurrenceCoordinatedRibbonClauseStub
        presentation entry color).getLast? =
        some (routedClauseTargetPosition source.erase
          (standardThreeStrandLayout.factor * placement.period)
          (constructedClauseOrigin source standardThreeStrandLayout)
          entry color) := by
  let target := occurrenceSourceClauseTarget presentation entry
  let data := sourceClauseRibbonFanData presentation target
  let group := occurrenceClauseTerminalGroup source.erase entry
  let lane := routedRibbonLane source.erase entry color
  have member :
      entry ∈
        activeClauseTargetOccurrenceEntries presentation target :=
    entry.mem_activeClauseTargetOccurrenceEntries presentation
  have active : data.GroupActive group :=
    ClauseRibbonFanData.sourceClauseRibbonFanData_groupActive
      presentation target entry member
  have dataCompatible : data.IsClockwiseCompatible :=
    compatible.2 entry
  constructor
  · rw [occurrenceRibbonCorridorRouteEnd_eq
      presentation entry color]
    rw [show
      occurrenceCoordinatedRibbonClauseStub
          presentation entry color =
        translatePolyline (ribbonMacrocellOrigin target)
          (data.coordinatedRoute group lane) by
            rfl]
    simp only [PeriodicOrthocrossing.translatePolyline]
    rw [List.head?_map,
      ClauseRibbonFanData.coordinatedRoute_head?
        data dataCompatible group active lane]
    simp only [Option.map_some]
    rw [ClauseRibbonFanData.sourceClauseRibbonFanData_direction_at_occurrence_of_widthAtMostThree
        presentation width entry]
    rfl
  · rw [standardRoutedClauseTarget_eq_refinedSourceTarget
      presentation entry color]
    rw [show
      occurrenceCoordinatedRibbonClauseStub
          presentation entry color =
        translatePolyline (ribbonMacrocellOrigin target)
          (data.coordinatedRoute group lane) by
            rfl]
    simp only [PeriodicOrthocrossing.translatePolyline]
    rw [List.getLast?_map,
      ClauseRibbonFanData.coordinatedRoute_getLast?
        data dataCompatible group active lane]
    simp only [Option.map_some]
    rw [ClauseRibbonFanData.lanePort_routedRibbonLane
      source.erase entry color]
    simp [target, occurrenceSourceClauseTarget,
      occurrenceClauseRibbonFanPort, ribbonMacrocellOrigin,
      Cell.add]
    all_goals omega

/-- Translating a coordinated source variable fan preserves
rectilinearity. -/
theorem occurrenceCoordinatedRibbonVariableStub_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible presentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    OrthogonalPolyline
      (occurrenceCoordinatedRibbonVariableStub
        presentation entry color) := by
  let data := sourceVariableRibbonFanData presentation entry
  let slot := occurrenceVariableSiteSlot entry.1.2
  have active : data.SlotActive slot :=
    VariableRibbonFanData.sourceVariableRibbonFanData_slotActive
      presentation entry
  exact
    (VariableRibbonFanData.coordinatedRoute_orthogonal
      data (compatible.1 entry) slot active color).translate
        (ribbonMacrocellOrigin (placement.position entry.1.1))

/-- Translating a coordinated source clause fan preserves
rectilinearity. -/
theorem occurrenceCoordinatedRibbonClauseStub_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible presentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor) :
    OrthogonalPolyline
      (occurrenceCoordinatedRibbonClauseStub
        presentation entry color) := by
  let target := occurrenceSourceClauseTarget presentation entry
  let data := sourceClauseRibbonFanData presentation target
  let group := occurrenceClauseTerminalGroup source.erase entry
  let lane := routedRibbonLane source.erase entry color
  have member :
      entry ∈
        activeClauseTargetOccurrenceEntries presentation target :=
    entry.mem_activeClauseTargetOccurrenceEntries presentation
  have active : data.GroupActive group :=
    ClauseRibbonFanData.sourceClauseRibbonFanData_groupActive
      presentation target entry member
  exact
    (ClauseRibbonFanData.coordinatedRoute_orthogonal
      data (compatible.2 entry) group active lane).translate
        (ribbonMacrocellOrigin target)

/-- Every translated coordinated variable-fan point stays in its source
variable macrocell. -/
theorem occurrenceCoordinatedRibbonVariableStub_points_bounded
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible presentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor)
    {point : Cell}
    (member :
      point ∈ occurrenceCoordinatedRibbonVariableStub
        presentation entry color) :
    InRibbonMacrocell (placement.position entry.1.1) point := by
  let data := sourceVariableRibbonFanData presentation entry
  let slot := occurrenceVariableSiteSlot entry.1.2
  have active : data.SlotActive slot :=
    VariableRibbonFanData.sourceVariableRibbonFanData_slotActive
      presentation entry
  unfold occurrenceCoordinatedRibbonVariableStub
    PeriodicOrthocrossing.translatePolyline at member
  rcases List.mem_map.mp member with
    ⟨localPoint, localMember, rfl⟩
  apply inRibbonMacrocell_add_origin
  exact
    VariableRibbonFanData.coordinatedRoute_points_bounded
      data (compatible.1 entry) slot active color localMember

/-- Every translated coordinated clause-fan point stays in its lifted
source-clause macrocell. -/
theorem occurrenceCoordinatedRibbonClauseStub_points_bounded
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible presentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor)
    {point : Cell}
    (member :
      point ∈ occurrenceCoordinatedRibbonClauseStub
        presentation entry color) :
    let data := occurrenceSpliceData presentation entry
    InRibbonMacrocell
      (PositionedPeriodicCNF.variableToClauseTarget
        placement data.positionedClause data.tagged.1)
      point := by
  let target := occurrenceSourceClauseTarget presentation entry
  let data := sourceClauseRibbonFanData presentation target
  let group := occurrenceClauseTerminalGroup source.erase entry
  let lane := routedRibbonLane source.erase entry color
  have targetMember :
      entry ∈
        activeClauseTargetOccurrenceEntries presentation target :=
    entry.mem_activeClauseTargetOccurrenceEntries presentation
  have active : data.GroupActive group :=
    ClauseRibbonFanData.sourceClauseRibbonFanData_groupActive
      presentation target entry targetMember
  unfold occurrenceCoordinatedRibbonClauseStub
    PeriodicOrthocrossing.translatePolyline at member
  rcases List.mem_map.mp member with
    ⟨localPoint, localMember, rfl⟩
  apply inRibbonMacrocell_add_origin
  exact
    ClauseRibbonFanData.coordinatedRoute_points_bounded
      data (compatible.2 entry) group active lane localMember

/-- The source-instantiated coordinated fans, packaged in the generic
endpoint-fan interface used to join them to the central corridor. -/
noncomputable def coordinatedSourceRibbonEndpointFanSystem
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible presentation) :
    RibbonEndpointFanSystem presentation where
  variableStub :=
    occurrenceCoordinatedRibbonVariableStub presentation
  clauseStub :=
    occurrenceCoordinatedRibbonClauseStub presentation
  variableStubEndpoints :=
    occurrenceCoordinatedRibbonVariableStub_endpoints
      presentation compatible
  clauseStubEndpoints :=
    occurrenceCoordinatedRibbonClauseStub_endpoints
      presentation width compatible
  variableStubOrthogonal :=
    occurrenceCoordinatedRibbonVariableStub_orthogonal
      presentation compatible
  clauseStubOrthogonal :=
    occurrenceCoordinatedRibbonClauseStub_orthogonal
      presentation compatible
  variableStubPointsBounded :=
    occurrenceCoordinatedRibbonVariableStub_points_bounded
      presentation compatible
  clauseStubPointsBounded :=
    occurrenceCoordinatedRibbonClauseStub_points_bounded
      presentation compatible

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
