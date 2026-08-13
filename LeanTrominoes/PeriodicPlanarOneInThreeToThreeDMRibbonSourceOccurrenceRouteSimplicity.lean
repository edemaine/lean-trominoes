/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableCorridorSimplicity
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableClauseSeparation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceRouting

/-!
# Simplicity of complete coordinated occurrence routes

The clause-side proof peels corridor tiles from the variable end.  Every
nonfinal tile is contact-free from the clause fan, while the final tile has
only its advertised tail contact.  This composes with the already-simple
variable-fan/corridor prefix to prove simplicity of the full occurrence
route used by the padded coordinated routing.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Prepending a contact-free route piece preserves ordinary avoidance and
the fact that all listed contact occurs at the resulting route's tail. -/
private theorem join_left_preserves_only_first_tail
    {first extra second : List Cell}
    {boundary : Cell}
    (firstAvoid : RoutesStrictlyAvoidEachOther first second)
    (extraAvoid : RoutesAvoidEachOther extra second)
    (extraContacts : RoutesMeetOnlyAtFirstTail extra second)
    (firstLast : first.getLast? = some boundary)
    (extraHead : extra.head? = some boundary) :
    RoutesAvoidEachOther (joinAtEndpoint first extra) second ∧
      RoutesMeetOnlyAtFirstTail (joinAtEndpoint first extra) second := by
  refine ⟨RoutesAvoidEachOther.join_left_of_tail_contact
    firstAvoid extraAvoid extraContacts firstLast extraHead, ?_⟩
  intro joinedPoint joinedMember secondPoint secondMember equal
  rcases mem_joinAtEndpoint joinedMember with firstMember | extraMember
  · exact (firstAvoid.2.2.2
      joinedPoint firstMember secondPoint secondMember equal).elim
  · have contacts :=
      extraContacts joinedPoint extraMember secondPoint secondMember equal
    exact
      ⟨joinAtEndpoint_getLast?
          firstLast extraHead contacts.1,
        contacts.2⟩

/-- Along a duplicate-free source route ending at the advertised clause
edge, the complete corridor is ordinarily separated from its same-colored
clause fan and all listed contact occurs at the corridor tail. -/
theorem occurrenceRibbonCorridorCore_avoids_clauseStub_and_meets_only_at_tail_append_pair
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor)
    (sourceLeading : List Cell)
    (before target : Cell)
    (sourceRouteEquation :
      occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation entry =
        sourceLeading ++ [before, target])
    (finalUnit : AxisDirection.IsUnitAxisStep before target)
    (first : Cell)
    (rest : List Cell)
    (unitSteps :
      ((first :: rest) ++ [before, target]).IsChain
        AxisDirection.IsUnitAxisStep)
    (noReversal :
      SourceRouteHasNoImmediateReversal
        ((first :: rest) ++ [before, target]))
    (nodup : ((first :: rest) ++ [before, target]).Nodup) :
    RoutesAvoidEachOther
        (ribbonCorridorCore
          (routedRibbonLane source.erase entry color)
          ((first :: rest) ++ [before, target]))
        (occurrenceCoordinatedRibbonClauseStub
          presentation.toPlanarIncidencePresentation entry color) ∧
      RoutesMeetOnlyAtFirstTail
        (ribbonCorridorCore
          (routedRibbonLane source.erase entry color)
          ((first :: rest) ++ [before, target]))
        (occurrenceCoordinatedRibbonClauseStub
          presentation.toPlanarIncidencePresentation entry color) := by
  let planar := presentation.toPlanarIncidencePresentation
  let lane := routedRibbonLane source.erase entry color
  induction rest generalizing first with
  | nil =>
      have displayedUnitSteps :
          (first :: before :: target :: []).IsChain
            AxisDirection.IsUnitAxisStep := by
        simpa using unitSteps
      have parts := unitSteps_cons_cons_cons displayedUnitSteps
      have displayedNoReversal :
          SourceRouteHasNoImmediateReversal
            (first :: before :: target :: []) := by
        simpa using noReversal
      have avoid :=
        finalRibbonMacrocellRoute_avoids_occurrenceCoordinatedRibbonClauseStub
          presentation width compatible entry color
          sourceLeading first before target sourceRouteEquation
          finalUnit parts.1 displayedNoReversal.1
      have onlyCommon :=
        finalRibbonMacrocellRoute_occurrenceCoordinatedRibbonClauseStub_only_common
          presentation width compatible entry color
          sourceLeading first before target sourceRouteEquation
          finalUnit parts.1 displayedNoReversal.1
      rw [show ([first] ++ [before, target]) =
          first :: before :: target :: [] by rfl,
        ribbonCorridorCore]
      refine ⟨avoid, ?_⟩
      intro tilePoint tileMember fanPoint fanMember equal
      have sharedEq := onlyCommon tilePoint tileMember
        (equal ▸ fanMember)
      have tileLast :
          (ribbonMacrocellRoute before
            (AxisDirection.between first before)
            (AxisDirection.between before target) lane).getLast? =
          some tilePoint := by
        rw [sharedEq]
        exact ribbonMacrocellRoute_getLast? before
          (AxisDirection.between first before)
          (AxisDirection.between before target) lane
      rcases List.mem_iff_get.mp tileMember with
        ⟨tileIndex, tileIndexed⟩
      rcases List.mem_iff_get.mp fanMember with
        ⟨fanIndex, fanIndexed⟩
      have endpoints := avoid.2.2.2 tileIndex fanIndex
        (tileIndexed.trans (equal.trans fanIndexed.symm))
      rw [tileIndexed, fanIndexed] at endpoints
      exact ⟨tileLast, endpoints.2⟩
  | cons second remaining tailInduction =>
      cases remaining with
      | nil =>
          have displayedUnitSteps :
              (first :: second :: before :: target :: []).IsChain
                AxisDirection.IsUnitAxisStep := by
            simpa using unitSteps
          have parts := unitSteps_cons_cons_cons displayedUnitSteps
          have displayedNoReversal :
              SourceRouteHasNoImmediateReversal
                (first :: second :: before :: target :: []) := by
            simpa using noReversal
          have displayedNodup :
              (first :: second :: before :: target :: []).Nodup := by
            simpa using nodup
          have secondFresh : second ∉ [before, target] :=
            (List.nodup_cons.mp
              (List.nodup_cons.mp displayedNodup).2).1
          have secondNeBefore : second ≠ before := by
            simpa using (show second ≠ before ∧ second ≠ target by
              simpa using secondFresh).1
          have secondNeTarget : second ≠ target := by
            simpa using (show second ≠ before ∧ second ≠ target by
              simpa using secondFresh).2
          have headAvoid :=
            (occurrenceCoordinatedRibbonClauseStub_strictlyAvoids_ribbonMacrocellRoute_of_center_ne
              presentation width compatible entry color
              sourceLeading before target sourceRouteEquation finalUnit
              second secondNeTarget secondNeBefore
              (AxisDirection.between first second)
              (AxisDirection.between second before)
              (AxisDirection.between_isGenuine_of_unitAxisStep parts.1)
              (AxisDirection.between_isGenuine_of_unitAxisStep parts.2.1)
              displayedNoReversal.1 lane).symm
          have tailPair :=
            tailInduction second parts.2.2 displayedNoReversal.2
              (List.nodup_cons.mp displayedNodup).2
          have shared :=
            ribbonMacrocellExit_eq_entry_of_unitAxisStep parts.2.1 lane
          rw [show ((first :: second :: []) ++ [before, target]) =
              first :: second :: before :: target :: [] by rfl,
            ribbonCorridorCore]
          exact join_left_preserves_only_first_tail
            headAvoid tailPair.1 tailPair.2
            (ribbonMacrocellRoute_getLast? second
              (AxisDirection.between first second)
              (AxisDirection.between second before) lane)
            (by
              rw [shared]
              exact ribbonCorridorCore_head? lane second before target [])
      | cons third remaining =>
          have displayedUnitSteps :
              (first :: second :: third ::
                (remaining ++ [before, target])).IsChain
                  AxisDirection.IsUnitAxisStep := by
            simpa using unitSteps
          have parts := unitSteps_cons_cons_cons displayedUnitSteps
          have displayedNoReversal :
              SourceRouteHasNoImmediateReversal
                (first :: second :: third ::
                  (remaining ++ [before, target])) := by
            simpa using noReversal
          have displayedNodup :
              (first :: second :: third ::
                (remaining ++ [before, target])).Nodup := by
            simpa using nodup
          have secondFresh :
              second ∉ third :: (remaining ++ [before, target]) :=
            (List.nodup_cons.mp
              (List.nodup_cons.mp displayedNodup).2).1
          have secondNeBefore : second ≠ before := by
            intro equal
            apply secondFresh
            simp [equal]
          have secondNeTarget : second ≠ target := by
            intro equal
            apply secondFresh
            simp [equal]
          have headAvoid :=
            (occurrenceCoordinatedRibbonClauseStub_strictlyAvoids_ribbonMacrocellRoute_of_center_ne
              presentation width compatible entry color
              sourceLeading before target sourceRouteEquation finalUnit
              second secondNeTarget secondNeBefore
              (AxisDirection.between first second)
              (AxisDirection.between second third)
              (AxisDirection.between_isGenuine_of_unitAxisStep parts.1)
              (AxisDirection.between_isGenuine_of_unitAxisStep parts.2.1)
              displayedNoReversal.1 lane).symm
          have tailPair :=
            tailInduction second parts.2.2 displayedNoReversal.2
              (List.nodup_cons.mp displayedNodup).2
          have shared :=
            ribbonMacrocellExit_eq_entry_of_unitAxisStep parts.2.1 lane
          have assembled :=
            join_left_preserves_only_first_tail
              headAvoid tailPair.1 tailPair.2
              (ribbonMacrocellRoute_getLast? second
                (AxisDirection.between first second)
                (AxisDirection.between second third) lane)
              (by
                rw [shared]
                cases remaining with
                | nil =>
                    simpa using ribbonCorridorCore_head?
                      lane second third before [target]
                | cons fourth remaining =>
                    simpa using ribbonCorridorCore_head?
                      lane second third fourth (remaining ++ [before, target]))
          cases remaining with
          | nil => simpa [ribbonCorridorCore] using assembled
          | cons fourth remaining =>
              simpa [ribbonCorridorCore] using assembled

/-- The complete occurrence corridor is ordinarily separated from its
same-colored coordinated clause fan, with contact only at the corridor tail. -/
theorem occurrenceRibbonCorridorCore_avoids_clauseStub_and_meets_only_at_tail_of_length_ge_three
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor)
    (lengthGeThree :
      3 ≤ (occurrenceUnitSourceRoute
        presentation.toPlanarIncidencePresentation entry).length) :
    RoutesAvoidEachOther
        (occurrenceRibbonCorridorCore
          presentation.toPlanarIncidencePresentation entry color)
        (occurrenceCoordinatedRibbonClauseStub
          presentation.toPlanarIncidencePresentation entry color) ∧
      RoutesMeetOnlyAtFirstTail
        (occurrenceRibbonCorridorCore
          presentation.toPlanarIncidencePresentation entry color)
        (occurrenceCoordinatedRibbonClauseStub
          presentation.toPlanarIncidencePresentation entry color) := by
  let planar := presentation.toPlanarIncidencePresentation
  let route := occurrenceUnitSourceRoute planar entry
  have routeLength : 3 ≤ route.length := by
    simpa [route, planar] using lengthGeThree
  have routeUnitSteps : route.IsChain AxisDirection.IsUnitAxisStep := by
    simpa [route] using occurrenceUnitSourceRoute_unitSteps planar entry
  rcases AxisDirection.exists_eq_append_pair_of_length_ge_two
      (show 2 ≤ route.length by omega) with
    ⟨leading, before, target, routeEquation⟩
  have actualRouteEquation :
      occurrenceUnitSourceRoute planar entry = leading ++ [before, target] := by
    simpa [route] using routeEquation
  have finalUnit : AxisDirection.IsUnitAxisStep before target := by
    rw [routeEquation] at routeUnitSteps
    exact (List.isChain_append_cons_cons.mp routeUnitSteps).2.1
  cases leading with
  | nil => simp [routeEquation] at routeLength
  | cons first rest =>
      have unitSteps :
          ((first :: rest) ++ [before, target]).IsChain
            AxisDirection.IsUnitAxisStep := by
        rw [← actualRouteEquation]
        exact occurrenceUnitSourceRoute_unitSteps planar entry
      have noReversal :
          SourceRouteHasNoImmediateReversal
            ((first :: rest) ++ [before, target]) := by
        rw [← actualRouteEquation]
        exact occurrenceUnitSourceRoute_hasNoImmediateReversal
          presentation.toContinuousPlanarIncidencePresentation entry
      have nodup : ((first :: rest) ++ [before, target]).Nodup := by
        rw [← actualRouteEquation]
        exact occurrenceUnitSourceRoute_nodup presentation entry
      change RoutesAvoidEachOther
          (ribbonCorridorCore
            (routedRibbonLane source.erase entry color)
            (occurrenceUnitSourceRoute planar entry)) _ ∧
        RoutesMeetOnlyAtFirstTail
          (ribbonCorridorCore
            (routedRibbonLane source.erase entry color)
            (occurrenceUnitSourceRoute planar entry)) _
      rw [actualRouteEquation]
      exact
        occurrenceRibbonCorridorCore_avoids_clauseStub_and_meets_only_at_tail_append_pair
          presentation width compatible entry color
          (first :: rest) before target actualRouteEquation finalUnit
          first rest unitSteps noReversal nodup

/-- The advertised final boundary is the only listed point shared by the
complete occurrence corridor and its same-colored clause fan. -/
theorem occurrenceRibbonCorridorCore_clauseStub_only_common_of_length_ge_three
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor)
    (lengthGeThree :
      3 ≤ (occurrenceUnitSourceRoute
        presentation.toPlanarIncidencePresentation entry).length) :
    ∀ point,
      point ∈ occurrenceRibbonCorridorCore
        presentation.toPlanarIncidencePresentation entry color →
      point ∈ occurrenceCoordinatedRibbonClauseStub
        presentation.toPlanarIncidencePresentation entry color →
      point = ribbonCorridorRouteEnd
        (routedRibbonLane source.erase entry color)
        (occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation entry) := by
  let planar := presentation.toPlanarIncidencePresentation
  have contacts :=
    (occurrenceRibbonCorridorCore_avoids_clauseStub_and_meets_only_at_tail_of_length_ge_three
      presentation width compatible entry color lengthGeThree).2
  intro point coreMember clauseMember
  have tail := contacts point coreMember point clauseMember rfl
  exact Option.some.inj
    (tail.1.symm.trans
      (occurrenceRibbonCorridorCore_endpoints planar entry color).2)

/-- The already-joined variable-fan/corridor prefix is ordinarily separated
from the same-colored clause fan. -/
theorem occurrenceVariableStubJoinCorridorCore_avoids_clauseStub_of_length_ge_three
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor)
    (lengthGeThree :
      3 ≤ (occurrenceUnitSourceRoute
        presentation.toPlanarIncidencePresentation entry).length) :
    RoutesAvoidEachOther
      (joinAtEndpoint
        (occurrenceCoordinatedRibbonVariableStub
          presentation.toPlanarIncidencePresentation entry color)
        (occurrenceRibbonCorridorCore
          presentation.toPlanarIncidencePresentation entry color))
      (occurrenceCoordinatedRibbonClauseStub
        presentation.toPlanarIncidencePresentation entry color) := by
  let planar := presentation.toPlanarIncidencePresentation
  have variableAvoid :=
    occurrenceCoordinatedRibbonVariableStub_strictlyAvoids_occurrenceCoordinatedRibbonClauseStub_of_length_ge_three
      presentation compatible entry entry color color lengthGeThree
  have corePair :=
    occurrenceRibbonCorridorCore_avoids_clauseStub_and_meets_only_at_tail_of_length_ge_three
      presentation width compatible entry color lengthGeThree
  exact RoutesAvoidEachOther.join_left_of_tail_contact
    variableAvoid corePair.1 corePair.2
    (occurrenceCoordinatedRibbonVariableStub_endpoints
      planar compatible entry color).2
    (occurrenceRibbonCorridorCore_endpoints planar entry color).1

/-- The advertised final boundary is the only point shared by the complete
variable-fan/corridor prefix and its clause fan. -/
theorem occurrenceVariableStubJoinCorridorCore_clauseStub_only_common_of_length_ge_three
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor)
    (lengthGeThree :
      3 ≤ (occurrenceUnitSourceRoute
        presentation.toPlanarIncidencePresentation entry).length) :
    ∀ point,
      point ∈ joinAtEndpoint
        (occurrenceCoordinatedRibbonVariableStub
          presentation.toPlanarIncidencePresentation entry color)
        (occurrenceRibbonCorridorCore
          presentation.toPlanarIncidencePresentation entry color) →
      point ∈ occurrenceCoordinatedRibbonClauseStub
        presentation.toPlanarIncidencePresentation entry color →
      point = ribbonCorridorRouteEnd
        (routedRibbonLane source.erase entry color)
        (occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation entry) := by
  have variableAvoid :=
    occurrenceCoordinatedRibbonVariableStub_strictlyAvoids_occurrenceCoordinatedRibbonClauseStub_of_length_ge_three
      presentation compatible entry entry color color lengthGeThree
  have coreOnly :=
    occurrenceRibbonCorridorCore_clauseStub_only_common_of_length_ge_three
      presentation width compatible entry color lengthGeThree
  intro point prefixMember clauseMember
  rcases mem_joinAtEndpoint prefixMember with variableMember | coreMember
  · exact (variableAvoid.2.2.2
      point variableMember point clauseMember rfl).elim
  · exact coreOnly point coreMember clauseMember

/-- Every complete coordinated occurrence route with an interior source
lattice point is geometrically simple. -/
theorem coordinatedOccurrenceThreeStrandRoute_simple_of_length_ge_three
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor)
    (lengthGeThree :
      3 ≤ (occurrenceUnitSourceRoute
        presentation.toPlanarIncidencePresentation entry).length) :
    LocalIncidenceDrawing.RouteIsSimple
      (joinAtEndpoint
        (joinAtEndpoint
          (occurrenceCoordinatedRibbonVariableStub
            presentation.toPlanarIncidencePresentation entry color)
          (occurrenceRibbonCorridorCore
            presentation.toPlanarIncidencePresentation entry color))
        (occurrenceCoordinatedRibbonClauseStub
          presentation.toPlanarIncidencePresentation entry color)) := by
  let planar := presentation.toPlanarIncidencePresentation
  apply
    (occurrenceCoordinatedRibbonVariableStub_join_corridorCore_simple_of_length_ge_three
      presentation compatible entry color lengthGeThree).joinAtEndpoint_of_only_common
  · exact occurrenceCoordinatedRibbonClauseStub_simple
      planar compatible entry color
  · exact
      occurrenceVariableStubJoinCorridorCore_avoids_clauseStub_of_length_ge_three
        presentation width compatible entry color lengthGeThree
  · apply joinAtEndpoint_getLast?
    · exact
        (occurrenceCoordinatedRibbonVariableStub_endpoints
          planar compatible entry color).2
    · exact (occurrenceRibbonCorridorCore_endpoints planar entry color).1
    · exact (occurrenceRibbonCorridorCore_endpoints planar entry color).2
  · exact
      (occurrenceCoordinatedRibbonClauseStub_endpoints
        planar width compatible entry color).1
  · exact
      occurrenceVariableStubJoinCorridorCore_clauseStub_only_common_of_length_ge_three
        presentation width compatible entry color lengthGeThree

/-- The route field of the coordinated source routing is simple whenever
its selected unit source route contains an interior lattice point. -/
theorem coordinatedSourceRibbonThreeStrandRouting_route_simple_of_length_ge_three
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (entry : ActiveOccurrenceEntry source.erase)
    (color : WireColor)
    (lengthGeThree :
      3 ≤ (occurrenceUnitSourceRoute
        presentation.toPlanarIncidencePresentation entry).length) :
    LocalIncidenceDrawing.RouteIsSimple
      ((coordinatedSourceRibbonThreeStrandRouting
        presentation width compatible).route entry color) := by
  rw [coordinatedSourceRibbonThreeStrandRouting_route]
  simpa [RibbonEndpointFanSystem.occurrenceThreeStrandRoute,
    coordinatedSourceRibbonEndpointFanSystem] using
      coordinatedOccurrenceThreeStrandRoute_simple_of_length_ge_three
        presentation width compatible entry color lengthGeThree

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
