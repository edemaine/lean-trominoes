/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceClauseCoreStubSeparation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableCoreCorridorSeparation

/-!
# Source clause cores versus ribbon corridors

Clause-core routes lie in the strict inset of their source macrocell.  This
file separates such a route from every ribbon tile whose source-route center
is different, then assembles the tilewise result across a corridor core.
The source-level theorem exposes the exact remaining freshness obligation:
the canonical clause center may not occur as an interior center of the
selected lifted source route.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- A translated strict-inset route avoids a legal ribbon tile centered at
any other source point. -/
theorem translatedInsetRoute_strictlyAvoids_ribbonMacrocellRoute_of_center_ne
    {first : List Cell}
    {firstCenter : Cell}
    (firstBounded :
      ∀ point ∈ first,
        InClosedGridRectangle (1, 1) (127, 127) point)
    (center : Cell)
    (centerNe : center ≠ firstCenter)
    (incoming outgoing : AxisDirection)
    (tileColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      (translatePolyline (ribbonMacrocellOrigin firstCenter) first)
      (ribbonMacrocellRoute center incoming outgoing tileColor) := by
  exact insetRoute_strictlyAvoids_route_in_distinctRibbonMacrocell
    firstBounded
    (ribbonMacrocellRoute_points_bounded
      center incoming outgoing tileColor)
    centerNe.symm

/-- Tilewise strict separation assembles across every interior center of a
unit-step, nonreversing ribbon corridor. -/
theorem translatedInsetRoute_strictlyAvoids_ribbonCorridorCore_of_interior_fresh
    {first : List Cell}
    {firstCenter : Cell}
    (firstBounded :
      ∀ point ∈ first,
        InClosedGridRectangle (1, 1) (127, 127) point)
    (previous center next : Cell)
    (rest : List Cell)
    (unitSteps :
      (previous :: center :: next :: rest).IsChain
        AxisDirection.IsUnitAxisStep)
    (noReversal :
      SourceRouteHasNoImmediateReversal
        (previous :: center :: next :: rest))
    (interiorFresh :
      firstCenter ∉ (center :: next :: rest).dropLast)
    (tileColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      (translatePolyline (ribbonMacrocellOrigin firstCenter) first)
      (ribbonCorridorCore tileColor
        (previous :: center :: next :: rest)) := by
  induction rest generalizing previous center next with
  | nil =>
      rw [ribbonCorridorCore]
      have centerNe : center ≠ firstCenter := by
        intro equal
        exact interiorFresh (by simpa using equal.symm)
      exact
        translatedInsetRoute_strictlyAvoids_ribbonMacrocellRoute_of_center_ne
          firstBounded center centerNe
          (AxisDirection.between previous center)
          (AxisDirection.between center next) tileColor
  | cons fourth rest induction =>
      rw [ribbonCorridorCore]
      have parts := unitSteps_cons_cons_cons unitSteps
      have freshParts :
          center ≠ firstCenter ∧
            firstCenter ∉ (next :: fourth :: rest).dropLast := by
        have parts :
            firstCenter ≠ center ∧
              firstCenter ∉ (next :: fourth :: rest).dropLast := by
          simpa [List.dropLast_cons_of_ne_nil] using interiorFresh
        exact ⟨parts.1.symm, parts.2⟩
      have headAvoid :=
        translatedInsetRoute_strictlyAvoids_ribbonMacrocellRoute_of_center_ne
          firstBounded center freshParts.1
          (AxisDirection.between previous center)
          (AxisDirection.between center next) tileColor
      have tailAvoid :=
        induction center next fourth parts.2.2 noReversal.2
          freshParts.2
      have shared :=
        ribbonMacrocellExit_eq_entry_of_unitAxisStep
          parts.2.1 tileColor
      apply headAvoid.join_right tailAvoid
        (ribbonMacrocellRoute_getLast? center
          (AxisDirection.between previous center)
          (AxisDirection.between center next) tileColor)
      rw [shared]
      exact ribbonCorridorCore_head? tileColor center next fourth rest

/-- A translated checked clause-core route strictly avoids an occurrence
corridor whenever its canonical center is absent from the corridor's
interior source-route centers. -/
theorem constructedClauseRoute_strictlyAvoids_occurrenceRibbonCorridorCore_of_interior_fresh
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (anchorsZero : HasZeroClauseAnchors source)
    (clauseIndex : Nat)
    (indexLt : clauseIndex < source.clauses.length)
    (set : X3CClauseSet)
    (coreColor : WireColor)
    (entry : ActiveOccurrenceEntry source.erase)
    (corridorColor : WireColor)
    (interiorFresh :
      positionedClausePositionAt source clauseIndex ∉
        (occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation entry).tail.dropLast) :
    RoutesStrictlyAvoidEachOther
      (translatePolyline
        (constructedClauseOrigin source standardThreeStrandLayout
          clauseIndex)
        (X3CClauseOrthogonal.route set coreColor))
      (occurrenceRibbonCorridorCore
        presentation.toPlanarIncidencePresentation entry corridorColor) := by
  let planar := presentation.toPlanarIncidencePresentation
  let route := occurrenceUnitSourceRoute planar entry
  let firstCenter := positionedClausePositionAt source clauseIndex
  have routeLength : 2 ≤ route.length := by
    simpa [route] using occurrenceUnitSourceRoute_length planar entry
  cases routeEquation : route with
  | nil => simp [routeEquation] at routeLength
  | cons start tail =>
      cases tail with
      | nil => simp [routeEquation] at routeLength
      | cons second rest =>
          have startEq : start = placement.position entry.1.1 := by
            have headEq :=
              occurrenceUnitSourceRoute_variableEndpoint_head?
                planar entry
            rw [show occurrenceUnitSourceRoute planar entry =
                start :: second :: rest by
              simpa [route] using routeEquation] at headEq
            exact Option.some.inj headEq
          have startNe : start ≠ firstCenter := by
            rw [startEq]
            exact (assemblyMacrocellOwnerPosition_ne_of_ne
              planar anchorsZero (.clause clauseIndex) (.atom entry.1.1)
              (by simpa [AssemblyMacrocellOwner.IsDeclared,
                PositionedPeriodicCNF.erase] using indexLt)
              entry.atom_mem
              (by intro equal; cases equal)).symm
          cases rest with
          | nil =>
              have actualRouteEquation :
                  occurrenceUnitSourceRoute planar entry =
                    [start, second] := by
                simpa [route] using routeEquation
              have separated :=
                insetRoute_strictlyAvoids_route_in_distinctRibbonMacrocell
                  (firstCenter := firstCenter) (secondCenter := start)
                  (first :=
                    translatePolyline standardThreeStrandLayout.clauseOffset
                      (X3CClauseOrthogonal.route set coreColor))
                  (second :=
                    occurrenceRibbonCorridorCore
                      planar entry corridorColor)
                  (all_clauseRoute_points_in_inset_rectangle
                    set coreColor)
                  (fun point pointMember => by
                    rw [occurrenceRibbonCorridorCore,
                      actualRouteEquation] at pointMember
                    simp only [ribbonCorridorCore_pair,
                      List.mem_singleton] at pointMember
                    subst point
                    exact ribbonMacrocellExit_bounded start
                      (AxisDirection.between start second)
                      (routedRibbonLane source.erase entry corridorColor))
                  startNe.symm
              rw [translatePolyline_add] at separated
              simpa [constructedClauseOrigin, firstCenter,
                ribbonMacrocellOrigin, Cell.add, add_comm] using separated
          | cons third rest =>
              have actualRouteEquation :
                  occurrenceUnitSourceRoute planar entry =
                    start :: second :: third :: rest := by
                simpa [route] using routeEquation
              have unitSteps :
                  (start :: second :: third :: rest).IsChain
                    AxisDirection.IsUnitAxisStep := by
                rw [← actualRouteEquation]
                exact occurrenceUnitSourceRoute_unitSteps planar entry
              have noReversal :
                  SourceRouteHasNoImmediateReversal
                    (start :: second :: third :: rest) := by
                rw [← actualRouteEquation]
                exact occurrenceUnitSourceRoute_hasNoImmediateReversal
                  presentation.toContinuousPlanarIncidencePresentation entry
              have fresh :
                  firstCenter ∉ (second :: third :: rest).dropLast := by
                rw [actualRouteEquation] at interiorFresh
                simpa [firstCenter] using interiorFresh
              have separated :=
                translatedInsetRoute_strictlyAvoids_ribbonCorridorCore_of_interior_fresh
                  (firstCenter := firstCenter)
                  (first :=
                    translatePolyline standardThreeStrandLayout.clauseOffset
                      (X3CClauseOrthogonal.route set coreColor))
                  (all_clauseRoute_points_in_inset_rectangle
                    set coreColor)
                  start second third rest unitSteps noReversal fresh
                  (routedRibbonLane source.erase entry corridorColor)
              rw [translatePolyline_add] at separated
              rw [occurrenceRibbonCorridorCore, actualRouteEquation]
              simpa [constructedClauseOrigin, firstCenter,
                ribbonMacrocellOrigin, Cell.add, add_comm] using separated

/-- The assembled coordinated routing inherits clause-core versus corridor
separation under the same source-route freshness condition. -/
theorem assembledClauseRoute_strictlyAvoids_occurrenceRibbonCorridorCore_of_interior_fresh
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
    (corridorColor : WireColor)
    (interiorFresh :
      positionedClausePositionAt source clauseIndex ∉
        (occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation entry).tail.dropLast) :
    let routing := coordinatedSourceRibbonThreeStrandRouting
      presentation width compatible
    RoutesStrictlyAvoidEachOther
      (assembledClauseRoute routing clauseIndex set coreColor)
      (occurrenceRibbonCorridorCore
        presentation.toPlanarIncidencePresentation entry corridorColor) := by
  dsimp only
  simpa [assembledClauseRoute, orientedIncidenceLocalRoute,
    coordinatedSourceRibbonThreeStrandRouting,
    RibbonEndpointFanSystem.threeStrandRouting] using
    constructedClauseRoute_strictlyAvoids_occurrenceRibbonCorridorCore_of_interior_fresh
      presentation anchorsZero clauseIndex indexLt set coreColor entry
      corridorColor interiorFresh

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
