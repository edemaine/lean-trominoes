import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMGlobalRouteSeparation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceRouting

/-!
# Source clause cores versus coordinated clause stubs

The finite clause-fan tables already certify that every coordinated fan
avoids the complete checked clause core in its own macrocell.  A strict
one-cell inset around every clause-core route separates it from a fan in
any other source macrocell.  This file lifts those two local facts to the
translated source construction.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- The finite clause-side fan can contact the checked core only at the
fan's final advertised core port. -/
theorem coordinatedClauseRoute_meets_clauseCore_onlyAtFirstTail :
    ∀ (data : ClauseRibbonFanData),
      data.IsClockwiseCompatible →
      ∀ group, data.GroupActive group →
        ∀ lane set color,
          RoutesMeetOnlyAtFirstTail
            (data.coordinatedRoute group lane)
            (translatePolyline standardThreeStrandLayout.clauseOffset
              (X3CClauseOrthogonal.route set color)) := by
  native_decide +revert

/-- A route in the strict inset of one standard macrocell is contact-free
from a route in the closed bounds of any distinct macrocell. -/
theorem insetRoute_strictlyAvoids_route_in_distinctRibbonMacrocell
    {first second : List Cell}
    {firstCenter secondCenter : Cell}
    (firstBounded :
      ∀ point ∈ first,
        InClosedGridRectangle (1, 1) (127, 127) point)
    (secondBounded :
      ∀ point ∈ second, InRibbonMacrocell secondCenter point)
    (centersNe : firstCenter ≠ secondCenter) :
    RoutesStrictlyAvoidEachOther
      (translatePolyline (ribbonMacrocellOrigin firstCenter) first)
      second := by
  apply routesStrictlyAvoidEachOther_of_inSeparatedClosedGridRectangles
      (firstLower :=
        Cell.add (ribbonMacrocellOrigin firstCenter) (1, 1))
      (firstUpper :=
        Cell.add (ribbonMacrocellOrigin firstCenter) (127, 127))
      (secondLower := ribbonMacrocellOrigin secondCenter)
      (secondUpper :=
        Cell.add (ribbonMacrocellOrigin secondCenter) (128, 128))
  · intro point pointMember
    unfold translatePolyline at pointMember
    rcases List.mem_map.mp pointMember with
      ⟨localPoint, localMember, rfl⟩
    have bounded := firstBounded localPoint localMember
    rcases firstCenter with ⟨centerX, centerY⟩
    rcases localPoint with ⟨pointX, pointY⟩
    simp only [InClosedGridRectangle, ribbonMacrocellOrigin,
      standardThreeStrandLayout, Cell.add, Cell.scale] at bounded ⊢
    omega
  · intro point pointMember
    have bounded := secondBounded point pointMember
    rcases secondCenter with ⟨centerX, centerY⟩
    rcases point with ⟨pointX, pointY⟩
    simpa [InClosedGridRectangle, InRibbonMacrocell,
      ribbonMacrocellOrigin, standardThreeStrandLayout,
      Cell.add, Cell.scale] using bounded
  · rcases firstCenter with ⟨firstX, firstY⟩
    rcases secondCenter with ⟨secondX, secondY⟩
    have coordinateNe : firstX ≠ secondX ∨ firstY ≠ secondY := by
      by_cases xEq : firstX = secondX
      · right
        intro yEq
        exact centersNe (Prod.ext xEq yEq)
      · exact Or.inl xEq
    simp only [ClosedGridRectanglesSeparated, ribbonMacrocellOrigin,
      standardThreeStrandLayout, Cell.add, Cell.scale]
    rcases coordinateNe with xNe | yNe <;> omega

/-- Every translated checked clause-core route avoids every coordinated
source clause stub.  At a common lifted clause center this is the finite
clause-fan certificate; at distinct centers the avoidance is strict. -/
theorem constructedClauseRoute_avoids_occurrenceCoordinatedRibbonClauseStub
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible presentation)
    (clauseIndex : Nat)
    (set : X3CClauseSet)
    (coreColor : WireColor)
    (entry : ActiveOccurrenceEntry source.erase)
    (fanColor : WireColor) :
    RoutesAvoidEachOther
      (translatePolyline
        (constructedClauseOrigin source standardThreeStrandLayout
          clauseIndex)
        (X3CClauseOrthogonal.route set coreColor))
      (occurrenceCoordinatedRibbonClauseStub
        presentation entry fanColor) := by
  let firstCenter := positionedClausePositionAt source clauseIndex
  let secondCenter := occurrenceSourceClauseTarget presentation entry
  by_cases centersEq : firstCenter = secondCenter
  · let entryClauseIndex :=
      occurrenceClauseIndex source.erase entry.1.1 entry.1.2
    let data := sourceClauseRibbonFanData presentation entryClauseIndex
    let group := occurrenceClauseTerminalGroup source.erase entry
    let lane := routedRibbonLane source.erase entry fanColor
    have active : data.GroupActive group :=
      ClauseRibbonFanData.sourceClauseRibbonFanData_groupActive
        presentation entryClauseIndex entry
        entry.mem_activeClauseOccurrenceEntries
    have localAvoid := routesAvoidEachOther_comm
      (data.coordinatedRoute_avoids_clauseCore
        (compatible.2 entry) group active lane set coreColor)
    have translatedAvoid := routesAvoidEachOther_translate localAvoid
      (ribbonMacrocellOrigin secondCenter)
    have coreTranslation :
        translatePolyline (ribbonMacrocellOrigin secondCenter)
            (translatePolyline standardThreeStrandLayout.clauseOffset
              (X3CClauseOrthogonal.route set coreColor)) =
          translatePolyline
            (constructedClauseOrigin source standardThreeStrandLayout
              clauseIndex)
            (X3CClauseOrthogonal.route set coreColor) := by
      rw [translatePolyline_add]
      congr 1
      simp [constructedClauseOrigin, firstCenter, centersEq,
        ribbonMacrocellOrigin, Cell.add, add_comm]
    change RoutesAvoidEachOther
      (translatePolyline (ribbonMacrocellOrigin secondCenter)
        (translatePolyline standardThreeStrandLayout.clauseOffset
          (X3CClauseOrthogonal.route set coreColor)))
      (translatePolyline (ribbonMacrocellOrigin secondCenter)
        (data.coordinatedRoute group lane)) at translatedAvoid
    rw [coreTranslation] at translatedAvoid
    simpa [occurrenceCoordinatedRibbonClauseStub, secondCenter,
      entryClauseIndex, data, group, lane] using translatedAvoid
  · have separated :=
      insetRoute_strictlyAvoids_route_in_distinctRibbonMacrocell
        (firstCenter := firstCenter) (secondCenter := secondCenter)
        (first :=
          translatePolyline standardThreeStrandLayout.clauseOffset
            (X3CClauseOrthogonal.route set coreColor))
        (second :=
          occurrenceCoordinatedRibbonClauseStub
            presentation entry fanColor)
        (all_clauseRoute_points_in_inset_rectangle set coreColor)
        (fun point pointMember => by
          simpa [secondCenter, occurrenceSourceClauseTarget] using
            occurrenceCoordinatedRibbonClauseStub_points_bounded
              presentation compatible entry fanColor pointMember)
        centersEq
    rw [translatePolyline_add] at separated
    simpa [constructedClauseOrigin, firstCenter, ribbonMacrocellOrigin,
      Cell.add, add_comm] using separated.toRoutesAvoidEachOther

/-- Every listed contact of a coordinated clause stub with a checked clause
core occurs at the stub's final core port. -/
theorem occurrenceCoordinatedRibbonClauseStub_meets_constructedClauseRoute_onlyAtFirstTail
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible presentation)
    (clauseIndex : Nat)
    (set : X3CClauseSet)
    (coreColor : WireColor)
    (entry : ActiveOccurrenceEntry source.erase)
    (fanColor : WireColor) :
    RoutesMeetOnlyAtFirstTail
      (occurrenceCoordinatedRibbonClauseStub
        presentation entry fanColor)
      (translatePolyline
        (constructedClauseOrigin source standardThreeStrandLayout
          clauseIndex)
        (X3CClauseOrthogonal.route set coreColor)) := by
  let firstCenter := positionedClausePositionAt source clauseIndex
  let secondCenter := occurrenceSourceClauseTarget presentation entry
  by_cases centersEq : firstCenter = secondCenter
  · let entryClauseIndex :=
      occurrenceClauseIndex source.erase entry.1.1 entry.1.2
    let data := sourceClauseRibbonFanData presentation entryClauseIndex
    let group := occurrenceClauseTerminalGroup source.erase entry
    let lane := routedRibbonLane source.erase entry fanColor
    have active : data.GroupActive group :=
      ClauseRibbonFanData.sourceClauseRibbonFanData_groupActive
        presentation entryClauseIndex entry
        entry.mem_activeClauseOccurrenceEntries
    have localContacts :=
      coordinatedClauseRoute_meets_clauseCore_onlyAtFirstTail
        data (compatible.2 entry) group active lane set coreColor
    have translatedContacts := localContacts.translate
      (ribbonMacrocellOrigin secondCenter)
    have coreTranslation :
        translatePolyline (ribbonMacrocellOrigin secondCenter)
            (translatePolyline standardThreeStrandLayout.clauseOffset
              (X3CClauseOrthogonal.route set coreColor)) =
          translatePolyline
            (constructedClauseOrigin source standardThreeStrandLayout
              clauseIndex)
            (X3CClauseOrthogonal.route set coreColor) := by
      rw [translatePolyline_add]
      congr 1
      simp [constructedClauseOrigin, firstCenter, centersEq,
        ribbonMacrocellOrigin, Cell.add, add_comm]
    change RoutesMeetOnlyAtFirstTail
      (translatePolyline (ribbonMacrocellOrigin secondCenter)
        (data.coordinatedRoute group lane))
      (translatePolyline (ribbonMacrocellOrigin secondCenter)
        (translatePolyline standardThreeStrandLayout.clauseOffset
          (X3CClauseOrthogonal.route set coreColor))) at translatedContacts
    rw [coreTranslation] at translatedContacts
    simpa [occurrenceCoordinatedRibbonClauseStub, secondCenter,
      entryClauseIndex, data, group, lane] using translatedContacts
  · have separated :=
      insetRoute_strictlyAvoids_route_in_distinctRibbonMacrocell
        (firstCenter := firstCenter) (secondCenter := secondCenter)
        (first :=
          translatePolyline standardThreeStrandLayout.clauseOffset
            (X3CClauseOrthogonal.route set coreColor))
        (second :=
          occurrenceCoordinatedRibbonClauseStub
            presentation entry fanColor)
        (all_clauseRoute_points_in_inset_rectangle set coreColor)
        (fun point pointMember => by
          simpa [secondCenter, occurrenceSourceClauseTarget] using
            occurrenceCoordinatedRibbonClauseStub_points_bounded
              presentation compatible entry fanColor pointMember)
        centersEq
    rw [translatePolyline_add] at separated
    have constructedSeparated :
        RoutesStrictlyAvoidEachOther
          (translatePolyline
            (constructedClauseOrigin source standardThreeStrandLayout
              clauseIndex)
            (X3CClauseOrthogonal.route set coreColor))
          (occurrenceCoordinatedRibbonClauseStub
            presentation entry fanColor) := by
      simpa [constructedClauseOrigin, firstCenter, ribbonMacrocellOrigin,
        Cell.add, add_comm] using separated
    intro stubPoint stubMember corePoint coreMember equal
    exact (constructedSeparated.2.2.2
      corePoint coreMember stubPoint stubMember equal.symm).elim

/-- The same clause-core/fan separation in the assembled coordinated
three-strand routing used by the hardness construction. -/
theorem assembledClauseRoute_avoids_occurrenceCoordinatedRibbonClauseStub
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (clauseIndex : Nat)
    (set : X3CClauseSet)
    (coreColor : WireColor)
    (entry : ActiveOccurrenceEntry source.erase)
    (fanColor : WireColor) :
    let routing := coordinatedSourceRibbonThreeStrandRouting
      presentation width compatible
    RoutesAvoidEachOther
      (assembledClauseRoute routing clauseIndex set coreColor)
      (occurrenceCoordinatedRibbonClauseStub
        presentation.toPlanarIncidencePresentation entry fanColor) := by
  dsimp only
  simpa [assembledClauseRoute, orientedIncidenceLocalRoute,
    coordinatedSourceRibbonThreeStrandRouting,
    RibbonEndpointFanSystem.threeStrandRouting] using
    constructedClauseRoute_avoids_occurrenceCoordinatedRibbonClauseStub
      presentation.toPlanarIncidencePresentation compatible clauseIndex
      set coreColor entry fanColor

/-- A checked clause-core route is strictly separated from every
coordinated variable stub.  The two pieces belong to distinct declared
source-vertex macrocells. -/
theorem constructedClauseRoute_strictlyAvoids_occurrenceCoordinatedRibbonVariableStub
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (compatible : SourceRibbonFansClockwiseCompatible presentation)
    (clauseIndex : Nat)
    (indexLt : clauseIndex < source.clauses.length)
    (set : X3CClauseSet)
    (coreColor : WireColor)
    (entry : ActiveOccurrenceEntry source.erase)
    (fanColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      (translatePolyline
        (constructedClauseOrigin source standardThreeStrandLayout
          clauseIndex)
        (X3CClauseOrthogonal.route set coreColor))
      (occurrenceCoordinatedRibbonVariableStub
        presentation entry fanColor) := by
  let firstCenter := positionedClausePositionAt source clauseIndex
  let secondCenter := placement.position entry.1.1
  have centersNe : firstCenter ≠ secondCenter := by
    exact assemblyMacrocellOwnerPosition_ne_of_ne
      presentation anchorsZero (.clause clauseIndex) (.atom entry.1.1)
      (by simpa [AssemblyMacrocellOwner.IsDeclared,
        PositionedPeriodicCNF.erase] using indexLt)
      entry.atom_mem
      (by intro equal; cases equal)
  have separated :=
    insetRoute_strictlyAvoids_route_in_distinctRibbonMacrocell
      (firstCenter := firstCenter) (secondCenter := secondCenter)
      (first :=
        translatePolyline standardThreeStrandLayout.clauseOffset
          (X3CClauseOrthogonal.route set coreColor))
      (second :=
        occurrenceCoordinatedRibbonVariableStub
          presentation entry fanColor)
      (all_clauseRoute_points_in_inset_rectangle set coreColor)
      (fun point pointMember => by
        simpa [secondCenter] using
          occurrenceCoordinatedRibbonVariableStub_points_bounded
            presentation compatible entry fanColor pointMember)
      centersNe
  rw [translatePolyline_add] at separated
  simpa [constructedClauseOrigin, firstCenter, ribbonMacrocellOrigin,
    Cell.add, add_comm] using separated

/-- The assembled coordinated routing inherits strict clause-core versus
variable-stub separation. -/
theorem assembledClauseRoute_strictlyAvoids_occurrenceCoordinatedRibbonVariableStub
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (clauseIndex : Nat)
    (indexLt : clauseIndex < source.clauses.length)
    (set : X3CClauseSet)
    (coreColor : WireColor)
    (entry : ActiveOccurrenceEntry source.erase)
    (fanColor : WireColor) :
    let routing := coordinatedSourceRibbonThreeStrandRouting
      presentation width compatible
    RoutesStrictlyAvoidEachOther
      (assembledClauseRoute routing clauseIndex set coreColor)
      (occurrenceCoordinatedRibbonVariableStub
        presentation.toPlanarIncidencePresentation entry fanColor) := by
  dsimp only
  simpa [assembledClauseRoute, orientedIncidenceLocalRoute,
    coordinatedSourceRibbonThreeStrandRouting,
    RibbonEndpointFanSystem.threeStrandRouting] using
    constructedClauseRoute_strictlyAvoids_occurrenceCoordinatedRibbonVariableStub
      presentation.toPlanarIncidencePresentation anchorsZero compatible
      clauseIndex indexLt set coreColor entry fanColor

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
