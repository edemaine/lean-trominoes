/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMTranslatedCorridorSeparation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableCoreSeparation
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceCoreClauseSeparation

/-!
# Separation of endpoint fans from translated ribbon corridors

The endpoint fans remain in their source-endpoint macrocells, while a
translated corridor inherits the full lifted source route.  Endpoint-only
contact of those lifted routes therefore supplies exactly the freshness
premise used by the existing fan-versus-corridor induction.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Translation preserves duplicate-freeness of an occurrence's unit source
route. -/
theorem translatedOccurrenceUnitSourceRoute_nodup
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (translate : Cell) :
    (translatePolyline (placement.translation translate)
      (occurrenceUnitSourceRoute
        presentation.toPlanarIncidencePresentation entry)).Nodup := by
  exact
    (occurrenceUnitSourceRoute_nodup presentation entry).map
      (Cell.add_left_injective (placement.translation translate))

/-- Translation preserves the unit-step chain of an occurrence source
route. -/
theorem translatedOccurrenceUnitSourceRoute_unitSteps
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (translate : Cell) :
    (translatePolyline (placement.translation translate)
      (occurrenceUnitSourceRoute presentation entry)).IsChain
        AxisDirection.IsUnitAxisStep := by
  unfold translatePolyline
  apply List.isChain_map_of_isChain (Cell.add (placement.translation translate))
  · intro first second
      (unit : AxisDirection.IsUnitAxisStep first second)
    exact unit.translate (placement.translation translate)
  · exact occurrenceUnitSourceRoute_unitSteps presentation entry

/-- Translation preserves the absence of immediate reversals on an
occurrence source route. -/
theorem translatedOccurrenceUnitSourceRoute_hasNoImmediateReversal
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (translate : Cell) :
    SourceRouteHasNoImmediateReversal
      (translatePolyline (placement.translation translate)
        (occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation entry)) := by
  exact
    (occurrenceUnitSourceRoute_hasNoImmediateReversal
      presentation.toContinuousPlanarIncidencePresentation entry).translate
        (placement.translation translate)

/-- An unshifted coordinated variable fan strictly avoids every translated
length-three corridor belonging to a distinct lifted source-route key. -/
theorem occurrenceCoordinatedRibbonVariableStub_strictlyAvoids_translatedOccurrenceRibbonCorridorCore
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (first second : ActiveOccurrenceEntry source.erase)
    (translate : Cell)
    (different :
      occurrenceSourceRouteKeyAt
          presentation.toPlanarIncidencePresentation first (0, 0) ≠
        occurrenceSourceRouteKeyAt
          presentation.toPlanarIncidencePresentation second translate)
    (firstLength :
      3 ≤
        (occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation first).length)
    (secondLength :
      3 ≤
        (occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation second).length)
    (firstColor secondColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      (occurrenceCoordinatedRibbonVariableStub
        presentation.toPlanarIncidencePresentation first firstColor)
      (translatePolyline
        (ribbonMacrocellOrigin (placement.translation translate))
        (occurrenceRibbonCorridorCore
          presentation.toPlanarIncidencePresentation second secondColor)) := by
  let planar := presentation.toPlanarIncidencePresentation
  let firstRoute := occurrenceUnitSourceRoute planar first
  let secondRoute := occurrenceUnitSourceRoute planar second
  let translatedSecondRoute :=
    translatePolyline (placement.translation translate) secondRoute
  have firstRouteLength : 3 ≤ firstRoute.length := by
    simpa [firstRoute, planar] using firstLength
  cases firstEquation : firstRoute with
  | nil => simp [firstEquation] at firstRouteLength
  | cons firstStart firstTail =>
      cases firstTail with
      | nil => simp [firstEquation] at firstRouteLength
      | cons firstNext firstRest =>
          have firstStartEq :
              firstStart = placement.position first.1.1 := by
            have headEq :=
              occurrenceUnitSourceRoute_variableEndpoint_head? planar first
            rw [show occurrenceUnitSourceRoute planar first =
                firstStart :: firstNext :: firstRest by
              simpa [firstRoute] using firstEquation] at headEq
            exact Option.some.inj headEq
          subst firstStart
          have firstRouteEquation :
              occurrenceUnitSourceRoute planar first =
                placement.position first.1.1 :: firstNext :: firstRest := by
            simpa [firstRoute] using firstEquation
          have firstUnit :
              AxisDirection.IsUnitAxisStep
                (placement.position first.1.1) firstNext :=
            (List.isChain_cons_cons.mp (by
              rw [← firstRouteEquation]
              exact occurrenceUnitSourceRoute_unitSteps planar first)).1
          have translatedSecondLength :
              3 ≤ translatedSecondRoute.length := by
            simpa [translatedSecondRoute, translatePolyline] using secondLength
          cases secondEquation : translatedSecondRoute with
          | nil =>
              simp [secondEquation] at translatedSecondLength
          | cons secondStart secondTail =>
              cases secondTail with
              | nil =>
                  simp [secondEquation] at translatedSecondLength
              | cons secondNext secondRest =>
                  cases secondRest with
                  | nil =>
                      simp [secondEquation] at translatedSecondLength
                  | cons secondThird secondRest =>
                      have secondNodup : translatedSecondRoute.Nodup := by
                        simpa [translatedSecondRoute, secondRoute, planar] using
                          translatedOccurrenceUnitSourceRoute_nodup
                            presentation second translate
                      have meetOnly :
                          RoutesMeetOnlyAtEndpoints
                            firstRoute translatedSecondRoute := by
                        simpa [firstRoute, secondRoute, translatedSecondRoute,
                          planar, PeriodicVariablePlacement.translation,
                          Cell.scale] using
                          translatedOccurrenceUnitSourceRoutes_meetOnlyAtEndpoints
                            presentation first second (0, 0) translate different
                      have firstCenterMember :
                          placement.position first.1.1 ∈ firstRoute := by
                        rw [firstEquation]
                        simp
                      have firstNextMember : firstNext ∈ firstRoute := by
                        rw [firstEquation]
                        simp
                      have interiorCentersNe :
                          ∀ (leading : List Cell)
                            (previous center next : Cell)
                            (remaining : List Cell),
                            translatedSecondRoute = leading ++
                                previous :: center :: next :: remaining →
                              center ≠ placement.position first.1.1 ∧
                                center ≠ firstNext := by
                        intro leading previous center next remaining equation
                        have centerMember : center ∈ translatedSecondRoute := by
                          rw [equation]
                          simp
                        have centerInternal :
                            ¬RoutePointIsEndpoint translatedSecondRoute center :=
                          routeCenter_not_endpoint_of_nodup_of_eq_append_triple
                            equation secondNodup
                        constructor
                        · exact
                            (routePoints_ne_of_routesMeetOnlyAtEndpoints
                              meetOnly firstCenterMember centerMember
                              (Or.inr centerInternal)).symm
                        · exact
                            (routePoints_ne_of_routesMeetOnlyAtEndpoints
                              meetOnly firstNextMember centerMember
                              (Or.inr centerInternal)).symm
                      have secondUnitSteps :
                          (secondStart :: secondNext :: secondThird ::
                            secondRest).IsChain
                              AxisDirection.IsUnitAxisStep := by
                        rw [← secondEquation]
                        simpa [translatedSecondRoute, secondRoute, planar] using
                          translatedOccurrenceUnitSourceRoute_unitSteps
                            planar second translate
                      have secondNoReversal :
                          SourceRouteHasNoImmediateReversal
                            (secondStart :: secondNext :: secondThird ::
                              secondRest) := by
                        rw [← secondEquation]
                        simpa [translatedSecondRoute, secondRoute, planar] using
                          translatedOccurrenceUnitSourceRoute_hasNoImmediateReversal
                            presentation second translate
                      change RoutesStrictlyAvoidEachOther _
                        (translatePolyline
                          (ribbonMacrocellOrigin
                            (placement.translation translate))
                          (ribbonCorridorCore
                            (routedRibbonLane source.erase second secondColor)
                            (occurrenceUnitSourceRoute planar second)))
                      rw [← ribbonCorridorCore_translatePolyline]
                      rw [show translatePolyline
                          (placement.translation translate)
                          (occurrenceUnitSourceRoute planar second) =
                            secondStart :: secondNext :: secondThird ::
                              secondRest by
                        simpa [translatedSecondRoute, secondRoute] using
                          secondEquation]
                      exact
                        occurrenceCoordinatedRibbonVariableStub_strictlyAvoids_ribbonCorridorCore_of_interiorCenters_ne
                          presentation compatible first firstColor
                          firstNext firstRest firstRouteEquation firstUnit
                          translatedSecondRoute interiorCentersNe []
                          secondStart secondNext secondThird secondRest
                          (by simpa using secondEquation)
                          secondUnitSteps secondNoReversal
                          (routedRibbonLane source.erase second secondColor)

/-- An unshifted coordinated clause fan strictly avoids every translated
length-three corridor belonging to a distinct lifted source-route key. -/
theorem occurrenceCoordinatedRibbonClauseStub_strictlyAvoids_translatedOccurrenceRibbonCorridorCore
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (first second : ActiveOccurrenceEntry source.erase)
    (translate : Cell)
    (different :
      occurrenceSourceRouteKeyAt
          presentation.toPlanarIncidencePresentation first (0, 0) ≠
        occurrenceSourceRouteKeyAt
          presentation.toPlanarIncidencePresentation second translate)
    (firstLength :
      3 ≤
        (occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation first).length)
    (secondLength :
      3 ≤
        (occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation second).length)
    (firstColor secondColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      (occurrenceCoordinatedRibbonClauseStub
        presentation.toPlanarIncidencePresentation first firstColor)
      (translatePolyline
        (ribbonMacrocellOrigin (placement.translation translate))
        (occurrenceRibbonCorridorCore
          presentation.toPlanarIncidencePresentation second secondColor)) := by
  let planar := presentation.toPlanarIncidencePresentation
  let firstRoute := occurrenceUnitSourceRoute planar first
  let secondRoute := occurrenceUnitSourceRoute planar second
  let translatedSecondRoute :=
    translatePolyline (placement.translation translate) secondRoute
  have firstRouteLength : 2 ≤ firstRoute.length := by
    have lengthThree : 3 ≤ firstRoute.length := by
      simpa [firstRoute, planar] using firstLength
    omega
  have firstUnitSteps :
      firstRoute.IsChain AxisDirection.IsUnitAxisStep := by
    simpa [firstRoute] using occurrenceUnitSourceRoute_unitSteps planar first
  rcases AxisDirection.exists_eq_append_pair_of_length_ge_two firstRouteLength with
    ⟨firstLeading, firstBefore, firstTarget, firstEquation⟩
  have firstRouteEquation :
      occurrenceUnitSourceRoute planar first =
        firstLeading ++ [firstBefore, firstTarget] := by
    simpa [firstRoute] using firstEquation
  have firstFinalUnit :
      AxisDirection.IsUnitAxisStep firstBefore firstTarget := by
    rw [firstEquation] at firstUnitSteps
    exact (List.isChain_append_cons_cons.mp firstUnitSteps).2.1
  have translatedSecondLength :
      3 ≤ translatedSecondRoute.length := by
    simpa [translatedSecondRoute, translatePolyline] using secondLength
  cases secondEquation : translatedSecondRoute with
  | nil => simp [secondEquation] at translatedSecondLength
  | cons secondStart secondTail =>
      cases secondTail with
      | nil => simp [secondEquation] at translatedSecondLength
      | cons secondNext secondRest =>
          cases secondRest with
          | nil => simp [secondEquation] at translatedSecondLength
          | cons secondThird secondRest =>
              have secondNodup : translatedSecondRoute.Nodup := by
                simpa [translatedSecondRoute, secondRoute, planar] using
                  translatedOccurrenceUnitSourceRoute_nodup
                    presentation second translate
              have meetOnly :
                  RoutesMeetOnlyAtEndpoints firstRoute translatedSecondRoute := by
                simpa [firstRoute, secondRoute, translatedSecondRoute, planar,
                  PeriodicVariablePlacement.translation, Cell.scale] using
                  translatedOccurrenceUnitSourceRoutes_meetOnlyAtEndpoints
                    presentation first second (0, 0) translate different
              have firstBeforeMember : firstBefore ∈ firstRoute := by
                rw [firstEquation]
                simp
              have firstTargetMember : firstTarget ∈ firstRoute := by
                rw [firstEquation]
                simp
              have interiorCentersNe :
                  ∀ (leading : List Cell) (previous center next : Cell)
                    (remaining : List Cell),
                    translatedSecondRoute = leading ++
                        previous :: center :: next :: remaining →
                      center ≠ firstTarget ∧ center ≠ firstBefore := by
                intro leading previous center next remaining equation
                have centerMember : center ∈ translatedSecondRoute := by
                  rw [equation]
                  simp
                have centerInternal :
                    ¬RoutePointIsEndpoint translatedSecondRoute center :=
                  routeCenter_not_endpoint_of_nodup_of_eq_append_triple
                    equation secondNodup
                constructor
                · exact
                    (routePoints_ne_of_routesMeetOnlyAtEndpoints
                      meetOnly firstTargetMember centerMember
                      (Or.inr centerInternal)).symm
                · exact
                    (routePoints_ne_of_routesMeetOnlyAtEndpoints
                      meetOnly firstBeforeMember centerMember
                      (Or.inr centerInternal)).symm
              have secondUnitSteps :
                  (secondStart :: secondNext :: secondThird :: secondRest).IsChain
                    AxisDirection.IsUnitAxisStep := by
                rw [← secondEquation]
                simpa [translatedSecondRoute, secondRoute, planar] using
                  translatedOccurrenceUnitSourceRoute_unitSteps
                    planar second translate
              have secondNoReversal :
                  SourceRouteHasNoImmediateReversal
                    (secondStart :: secondNext :: secondThird :: secondRest) := by
                rw [← secondEquation]
                simpa [translatedSecondRoute, secondRoute, planar] using
                  translatedOccurrenceUnitSourceRoute_hasNoImmediateReversal
                    presentation second translate
              change RoutesStrictlyAvoidEachOther _
                (translatePolyline
                  (ribbonMacrocellOrigin (placement.translation translate))
                  (ribbonCorridorCore
                    (routedRibbonLane source.erase second secondColor)
                    (occurrenceUnitSourceRoute planar second)))
              rw [← ribbonCorridorCore_translatePolyline]
              rw [show translatePolyline (placement.translation translate)
                  (occurrenceUnitSourceRoute planar second) =
                    secondStart :: secondNext :: secondThird :: secondRest by
                simpa [translatedSecondRoute, secondRoute] using secondEquation]
              exact
                occurrenceCoordinatedRibbonClauseStub_strictlyAvoids_ribbonCorridorCore_of_interiorCenters_ne
                  presentation width compatible first firstColor
                  firstLeading firstBefore firstTarget firstRouteEquation
                  firstFinalUnit translatedSecondRoute interiorCentersNe []
                  secondStart secondNext secondThird secondRest
                  (by simpa using secondEquation)
                  secondUnitSteps secondNoReversal
                  (routedRibbonLane source.erase second secondColor)

/-- Reversing the relative frame turns the preceding clause/fan theorem
into corridor separation from a forward translated clause fan. -/
theorem occurrenceRibbonCorridorCore_strictlyAvoids_translatedOccurrenceCoordinatedRibbonClauseStub_of_nonzero
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      presentation.toPlanarIncidencePresentation)
    (first second : ActiveOccurrenceEntry source.erase)
    (translate : Cell) (translateNonzero : translate ≠ (0, 0))
    (firstLength :
      3 ≤
        (occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation first).length)
    (secondLength :
      3 ≤
        (occurrenceUnitSourceRoute
          presentation.toPlanarIncidencePresentation second).length)
    (firstColor secondColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      (occurrenceRibbonCorridorCore
        presentation.toPlanarIncidencePresentation first firstColor)
      (translatePolyline
        (ribbonMacrocellOrigin (placement.translation translate))
        (occurrenceCoordinatedRibbonClauseStub
          presentation.toPlanarIncidencePresentation second secondColor)) := by
  let reverseTranslate := Cell.sub (0, 0) translate
  let backwardsPhysical :=
    ribbonMacrocellOrigin (placement.translation reverseTranslate)
  let forwardsPhysical :=
    ribbonMacrocellOrigin (placement.translation translate)
  have reverseNonzero : reverseTranslate ≠ (0, 0) := by
    intro reverseZero
    apply translateNonzero
    rcases translate with ⟨translateX, translateY⟩
    simp [reverseTranslate, Cell.sub] at reverseZero ⊢
    exact reverseZero
  have backwards :=
    occurrenceCoordinatedRibbonClauseStub_strictlyAvoids_translatedOccurrenceRibbonCorridorCore
      presentation width compatible second first reverseTranslate
      (occurrenceSourceRouteKeyAt_zero_ne_of_translate_ne_zero
        presentation.toPlanarIncidencePresentation second first reverseNonzero)
      secondLength firstLength secondColor firstColor
  have shifted := backwards.translatePolyline forwardsPhysical
  have shiftsCancel :
      Cell.add backwardsPhysical forwardsPhysical = (0, 0) := by
    rcases translate with ⟨translateX, translateY⟩
    simp [backwardsPhysical, forwardsPhysical, reverseTranslate,
      ribbonMacrocellOrigin, PeriodicVariablePlacement.translation,
      standardThreeStrandLayout, Cell.sub, Cell.add, Cell.scale]
  rw [translatePolyline_add, shiftsCancel, translatePolyline_zero] at shifted
  simpa [backwardsPhysical, forwardsPhysical] using shifted.symm

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
