import LeanTrominoes.RetainedAngularFanSourceScaling
import LeanTrominoes.RetainedAngularFanSourceSpliceSeparation

/-!
# Separation interface after refining the retained source

Source-first refinement preserves every old prefix/prefix separation fact and
scales the classified terminal lengths exactly.  Applying the retained splice
theorem therefore still leaves only the two directed source-prefix/fan-suffix
cross cases; no additional bookkeeping obligations are introduced by the
clearance scale.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Refining both source routes before inserting their fixed-size angular
fans transports all inherited hypotheses automatically.  The only new
hypotheses are the two directed cross cases and the already-certified
fan/fan separation. -/
theorem
    retainedAngularFanSourceScaledSplicedBoundaryPolylines_strictlyAvoid
    {factor : Nat} (factorPositive : 0 < factor)
    (firstRoute secondRoute : List Cell)
    (firstTerminal secondTerminal : RetainedTerminalData)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (firstLength : 2 ≤ firstRoute.length)
    (secondLength : 2 ≤ secondRoute.length)
    (firstClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector firstRoute) =
        some firstTerminal)
    (secondClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector secondRoute) =
        some secondTerminal)
    (sourcePrefixesAvoid :
      RoutesStrictlyAvoidEachOther
        firstRoute.dropLast secondRoute.dropLast)
    (firstPrefixAvoidSecondFan :
      RoutesStrictlyAvoidEachOther
        (scalePolyline retainedTerminalFanTotalRefinement
          (scalePolyline factor firstRoute)).dropLast
        (retainedTerminalFanOuterCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline factor secondRoute).getLastD (0, 0)))
          (scaleRetainedTerminalData factor secondTerminal)
          secondSlot))
    (firstFanAvoidSecondPrefix :
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline factor firstRoute).getLastD (0, 0)))
          (scaleRetainedTerminalData factor firstTerminal)
          firstSlot)
        (scalePolyline retainedTerminalFanTotalRefinement
          (scalePolyline factor secondRoute)).dropLast)
    (fansAvoid :
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline factor firstRoute).getLastD (0, 0)))
          (scaleRetainedTerminalData factor firstTerminal)
          firstSlot)
        (retainedTerminalFanOuterCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline factor secondRoute).getLastD (0, 0)))
          (scaleRetainedTerminalData factor secondTerminal)
          secondSlot)) :
    RoutesStrictlyAvoidEachOther
      (retainedAngularFanSplicedBoundaryPolyline
        (scalePolyline factor firstRoute)
        (scaleRetainedTerminalData factor firstTerminal)
        firstSlot)
      (retainedAngularFanSplicedBoundaryPolyline
        (scalePolyline factor secondRoute)
        (scaleRetainedTerminalData factor secondTerminal)
        secondSlot) := by
  apply
    retainedAngularFanSplicedBoundaryPolylines_strictlyAvoid
      (scalePolyline factor firstRoute)
      (scalePolyline factor secondRoute)
      (scaleRetainedTerminalData factor firstTerminal)
      (scaleRetainedTerminalData factor secondTerminal)
      firstSlot secondSlot
  · simpa [scalePolyline] using firstLength
  · simpa [scalePolyline] using secondLength
  · exact
      routeTerminalVector_scale_classified
        factorPositive firstClassified
  · exact
      routeTerminalVector_scale_classified
        factorPositive secondClassified
  · have factorPositiveInt : (0 : Int) < factor := by
      exact_mod_cast factorPositive
    have scaled :=
      sourcePrefixesAvoid.scalePolyline factorPositiveInt
    simpa [scalePolyline] using scaled
  · exact firstPrefixAvoidSecondFan
  · exact firstFanAvoidSecondPrefix
  · exact fansAvoid

/-- A singleton source prefix remains a singleton after source-first and
fan refinement, and its unique point is exactly its own outer-fan gate. -/
theorem retainedAngularFanSourceScaledPrefix_eq_singleton_gate
    {factor : Nat} (factorPositive : 0 < factor)
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector route) =
        some terminal)
    (singletonPrefix : route.dropLast.length = 1) :
    (scalePolyline retainedTerminalFanTotalRefinement
      (scalePolyline factor route)).dropLast =
        [(retainedAngularFanOuterDemand
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline factor route).getLastD (0, 0)))
          (scaleRetainedTerminalData factor terminal)
          slot).gate] := by
  let scaledRoute := scalePolyline factor route
  let refinedRoute :=
    scalePolyline retainedTerminalFanTotalRefinement
      scaledRoute
  have scaledLength : 2 ≤ scaledRoute.length := by
    simpa [scaledRoute, scalePolyline] using routeLength
  have refinedLength : 2 ≤ refinedRoute.length := by
    simpa [refinedRoute, scalePolyline] using scaledLength
  have refinedSingleton :
      refinedRoute.dropLast.length = 1 := by
    simpa [refinedRoute, scaledRoute, scalePolyline] using
      singletonPrefix
  rcases List.length_eq_one_iff.mp refinedSingleton with
    ⟨entrance, prefixEq⟩
  have reverseTailExists :=
    exists_reverse_tail_head?_of_two_le_length
      refinedRoute refinedLength
  have entranceLast :
      refinedRoute.dropLast.getLast? =
        some (polylineLastEntrance refinedRoute) :=
    dropLast_getLast?_of_reverse_tail_head?
      (polylineLastEntrance_spec reverseTailExists)
  have entranceEq :
      entrance = polylineLastEntrance refinedRoute := by
    rw [prefixEq] at entranceLast
    simpa using Option.some.inj entranceLast
  have classifiedScaled :=
    routeTerminalVector_scale_classified
      factorPositive classified
  have gateEq :=
    polylineLastEntrance_scalePolyline_eq_outerDemand_gate
      scaledLength classifiedScaled slot
  rw [prefixEq, entranceEq]
  simpa [refinedRoute, scaledRoute] using gateEq

/-- When a refined source prefix is a singleton, separation of its own
complete fan from another complete fan already implies the directed
source-prefix-versus-fan cross case. -/
theorem
    retainedAngularFanSourceScaledPrefix_strictlyAvoids_otherOuterCompleteRoute_of_singletonPrefix
    {factor : Nat} (factorPositive : 0 < factor)
    (sourceRoute : List Cell)
    (sourceTerminal otherTerminal : RetainedTerminalData)
    (sourceSlot otherSlot : RetainedTerminalSlot)
    (otherCenter : Cell)
    (sourceLength : 2 ≤ sourceRoute.length)
    (sourceClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector sourceRoute) =
        some sourceTerminal)
    (singletonPrefix : sourceRoute.dropLast.length = 1)
    (fansAvoid :
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline factor sourceRoute).getLastD (0, 0)))
          (scaleRetainedTerminalData factor sourceTerminal)
          sourceSlot)
        (retainedTerminalFanOuterCompleteRoute
          otherCenter otherTerminal otherSlot)) :
    RoutesStrictlyAvoidEachOther
      (scalePolyline retainedTerminalFanTotalRefinement
        (scalePolyline factor sourceRoute)).dropLast
      (retainedTerminalFanOuterCompleteRoute
        otherCenter otherTerminal otherSlot) := by
  let sourceCenter :=
    Cell.scale retainedTerminalFanTotalRefinement
      ((scalePolyline factor sourceRoute).getLastD (0, 0))
  let sourceScaledTerminal :=
    scaleRetainedTerminalData factor sourceTerminal
  let sourceGate :=
    (retainedAngularFanOuterDemand
      sourceCenter sourceScaledTerminal sourceSlot).gate
  have prefixEq :
      (scalePolyline retainedTerminalFanTotalRefinement
        (scalePolyline factor sourceRoute)).dropLast =
          [sourceGate] := by
    simpa [sourceCenter, sourceScaledTerminal, sourceGate] using
      retainedAngularFanSourceScaledPrefix_eq_singleton_gate
        factorPositive sourceRoute sourceTerminal sourceSlot
        sourceLength sourceClassified singletonPrefix
  have sourceGateMember :
      sourceGate ∈
        retainedTerminalFanOuterCompleteRoute
          sourceCenter sourceScaledTerminal sourceSlot := by
    have headEq :=
      retainedTerminalFanOuterCompleteRoute_head?
        sourceCenter sourceScaledTerminal sourceSlot
    cases routeEq :
        retainedTerminalFanOuterCompleteRoute
          sourceCenter sourceScaledTerminal sourceSlot with
    | nil =>
        rw [routeEq] at headEq
        simp at headEq
    | cons head tail =>
        rw [routeEq] at headEq
        simp only [List.head?_cons, Option.some.injEq] at headEq
        simpa [sourceGate, headEq]
  rw [prefixEq]
  apply fansAvoid.singleton_left
  simpa [sourceCenter, sourceScaledTerminal] using
    sourceGateMember

end PeriodicEightOccurrenceSplit
end LeanTrominoes
