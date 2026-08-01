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

/-- Source-first refinement also transports the common-clause splice
certificate, preserving both ordinary avoidance and the fact that the shared
source head is the only possible listed contact. -/
theorem
    retainedAngularFanSourceScaledSplicedBoundaryPolylines_separated
    {factor : Nat} (factorPositive : 0 < factor)
    (firstRoute secondRoute : List Cell)
    (firstTerminal secondTerminal : RetainedTerminalData)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (firstLength : 2 ≤ firstRoute.length)
    (secondLength : 2 ≤ secondRoute.length)
    (firstNodup : firstRoute.Nodup)
    (secondNodup : secondRoute.Nodup)
    (firstClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector firstRoute) =
        some firstTerminal)
    (secondClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector secondRoute) =
        some secondTerminal)
    (sourceRoutesAvoid :
      RoutesAvoidEachOther firstRoute secondRoute)
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
    RoutesAvoidEachOther
        (retainedAngularFanSplicedBoundaryPolyline
          (scalePolyline factor firstRoute)
          (scaleRetainedTerminalData factor firstTerminal)
          firstSlot)
        (retainedAngularFanSplicedBoundaryPolyline
          (scalePolyline factor secondRoute)
          (scaleRetainedTerminalData factor secondTerminal)
          secondSlot) ∧
      RoutesMeetOnlyAtHeads
        (retainedAngularFanSplicedBoundaryPolyline
          (scalePolyline factor firstRoute)
          (scaleRetainedTerminalData factor firstTerminal)
          firstSlot)
        (retainedAngularFanSplicedBoundaryPolyline
          (scalePolyline factor secondRoute)
          (scaleRetainedTerminalData factor secondTerminal)
          secondSlot) := by
  apply
    retainedAngularFanSplicedBoundaryPolylines_separated
      (scalePolyline factor firstRoute)
      (scalePolyline factor secondRoute)
      (scaleRetainedTerminalData factor firstTerminal)
      (scaleRetainedTerminalData factor secondTerminal)
      firstSlot secondSlot
  · simpa [scalePolyline] using firstLength
  · simpa [scalePolyline] using secondLength
  · exact firstNodup.map
      (Cell.scale_injective
        (show (factor : Int) ≠ 0 by
          exact_mod_cast factorPositive.ne'))
  · exact secondNodup.map
      (Cell.scale_injective
        (show (factor : Int) ≠ 0 by
          exact_mod_cast factorPositive.ne'))
  · exact
      routeTerminalVector_scale_classified
        factorPositive firstClassified
  · exact
      routeTerminalVector_scale_classified
        factorPositive secondClassified
  · have factorPositiveInt : (0 : Int) < factor := by
      exact_mod_cast factorPositive
    simpa [scalePolyline] using
      sourceRoutesAvoid.scalePolyline factorPositiveInt
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

/-- For two singleton-prefix incidences, one endpoint-aware fan/fan
certificate supplies every piece-pair obligation for ordinary avoidance of
the completed source-to-boundary splices.  This is the shared-clause form:
all contacts inherited from the fan pair are permitted only at the common
outer head. -/
theorem
    retainedAngularFanSourceScaledSplicedBoundaryPolylines_avoid_of_singletonPrefixes
    {factor : Nat} (factorPositive : 0 < factor)
    (firstRoute secondRoute : List Cell)
    (firstTerminal secondTerminal : RetainedTerminalData)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (firstLength : 2 ≤ firstRoute.length)
    (secondLength : 2 ≤ secondRoute.length)
    (firstNodup : firstRoute.Nodup)
    (secondNodup : secondRoute.Nodup)
    (firstClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector firstRoute) =
        some firstTerminal)
    (secondClassified :
      retainedTerminalDirectionClassify
          (PeriodicThreeSATThree.routeTerminalVector secondRoute) =
        some secondTerminal)
    (sourceRoutesAvoid :
      RoutesAvoidEachOther firstRoute secondRoute)
    (firstSingleton : firstRoute.dropLast.length = 1)
    (secondSingleton : secondRoute.dropLast.length = 1)
    (fansAvoid :
      RoutesAvoidEachOther
        (retainedTerminalFanOuterCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline factor firstRoute).getLastD (0, 0)))
          (scaleRetainedTerminalData factor firstTerminal)
          firstSlot)
        (retainedTerminalFanOuterCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline factor secondRoute).getLastD (0, 0)))
          (scaleRetainedTerminalData factor secondTerminal)
          secondSlot))
    (fanContactsAtHeads :
      RoutesMeetOnlyAtHeads
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
    RoutesAvoidEachOther
      (retainedAngularFanSplicedBoundaryPolyline
        (scalePolyline factor firstRoute)
        (scaleRetainedTerminalData factor firstTerminal)
        firstSlot)
      (retainedAngularFanSplicedBoundaryPolyline
        (scalePolyline factor secondRoute)
        (scaleRetainedTerminalData factor secondTerminal)
        secondSlot) := by
  let firstScaled := scalePolyline factor firstRoute
  let secondScaled := scalePolyline factor secondRoute
  let firstRefined :=
    scalePolyline retainedTerminalFanTotalRefinement firstScaled
  let secondRefined :=
    scalePolyline retainedTerminalFanTotalRefinement secondScaled
  let firstCenter :=
    Cell.scale retainedTerminalFanTotalRefinement
      (firstScaled.getLastD (0, 0))
  let secondCenter :=
    Cell.scale retainedTerminalFanTotalRefinement
      (secondScaled.getLastD (0, 0))
  let firstScaledTerminal :=
    scaleRetainedTerminalData factor firstTerminal
  let secondScaledTerminal :=
    scaleRetainedTerminalData factor secondTerminal
  let firstGate :=
    (retainedAngularFanOuterDemand
      firstCenter firstScaledTerminal firstSlot).gate
  let secondGate :=
    (retainedAngularFanOuterDemand
      secondCenter secondScaledTerminal secondSlot).gate
  let firstFan :=
    retainedTerminalFanOuterCompleteRoute
      firstCenter firstScaledTerminal firstSlot
  let secondFan :=
    retainedTerminalFanOuterCompleteRoute
      secondCenter secondScaledTerminal secondSlot
  have firstPrefixEq :
      firstRefined.dropLast = [firstGate] := by
    simpa [firstRefined, firstScaled, firstCenter,
      firstScaledTerminal, firstGate] using
      retainedAngularFanSourceScaledPrefix_eq_singleton_gate
        factorPositive firstRoute firstTerminal firstSlot
        firstLength firstClassified firstSingleton
  have secondPrefixEq :
      secondRefined.dropLast = [secondGate] := by
    simpa [secondRefined, secondScaled, secondCenter,
      secondScaledTerminal, secondGate] using
      retainedAngularFanSourceScaledPrefix_eq_singleton_gate
        factorPositive secondRoute secondTerminal secondSlot
        secondLength secondClassified secondSingleton
  have firstFanHead :
      firstFan.head? = some firstGate := by
    exact retainedTerminalFanOuterCompleteRoute_head?
      firstCenter firstScaledTerminal firstSlot
  have secondFanHead :
      secondFan.head? = some secondGate := by
    exact retainedTerminalFanOuterCompleteRoute_head?
      secondCenter secondScaledTerminal secondSlot
  have firstGateMember : firstGate ∈ firstFan :=
    List.mem_of_mem_head? firstFanHead
  have secondGateMember : secondGate ∈ secondFan :=
    List.mem_of_mem_head? secondFanHead
  have concreteFansAvoid :
      RoutesAvoidEachOther firstFan secondFan := by
    simpa [firstFan, secondFan, firstCenter, secondCenter,
      firstScaled, secondScaled, firstScaledTerminal,
      secondScaledTerminal] using fansAvoid
  have concreteFanContacts :
      RoutesMeetOnlyAtHeads firstFan secondFan := by
    simpa [firstFan, secondFan, firstCenter, secondCenter,
      firstScaled, secondScaled, firstScaledTerminal,
      secondScaledTerminal] using fanContactsAtHeads
  have firstPrefixAvoidSecondFan :
      RoutesAvoidEachOther firstRefined.dropLast secondFan := by
    rw [firstPrefixEq]
    exact concreteFansAvoid.singleton_left firstGateMember
  have firstPrefixSecondFanContacts :
      RoutesMeetOnlyAtHeads firstRefined.dropLast secondFan := by
    rw [firstPrefixEq]
    exact concreteFanContacts.singleton_left
      firstGateMember
  have firstFanAvoidSecondPrefix :
      RoutesAvoidEachOther firstFan secondRefined.dropLast := by
    rw [secondPrefixEq]
    exact concreteFansAvoid.singleton_right secondGateMember
  have firstFanSecondPrefixContacts :
      RoutesMeetOnlyAtHeads firstFan secondRefined.dropLast := by
    rw [secondPrefixEq]
    exact concreteFanContacts.singleton_right
      secondGateMember
  have factorPositiveInt : (0 : Int) < factor := by
    exact_mod_cast factorPositive
  have refinementPositive :
      (0 : Int) < retainedTerminalFanTotalRefinement := by
    native_decide
  have refinedRoutesAvoid :
      RoutesAvoidEachOther firstRefined secondRefined := by
    have scaledAvoid :=
      sourceRoutesAvoid.scalePolyline factorPositiveInt
    have refinedAvoid :=
      scaledAvoid.scalePolyline refinementPositive
    simpa [firstRefined, secondRefined,
      firstScaled, secondScaled, scalePolyline] using refinedAvoid
  have firstRefinedNodup : firstRefined.Nodup := by
    exact
      List.Nodup.map
        (Cell.scale_injective refinementPositive.ne')
        (List.Nodup.map
          (Cell.scale_injective factorPositiveInt.ne')
          firstNodup)
  have secondRefinedNodup : secondRefined.Nodup := by
    exact
      List.Nodup.map
        (Cell.scale_injective refinementPositive.ne')
        (List.Nodup.map
          (Cell.scale_injective factorPositiveInt.ne')
          secondNodup)
  have firstOuterHead :
      firstRefined.dropLast.head? = firstFan.head? := by
    rw [firstPrefixEq, firstFanHead]
    simp
  have secondOuterHead :
      secondRefined.dropLast.head? = secondFan.head? := by
    rw [secondPrefixEq, secondFanHead]
    simp
  have firstEntrance :
      firstRefined.dropLast.getLast? = some firstGate := by
    rw [firstPrefixEq]
    simp
  have secondEntrance :
      secondRefined.dropLast.getLast? = some secondGate := by
    rw [secondPrefixEq]
    simp
  have assembled :=
    RoutesAvoidEachOther.replace_tails_of_all_head_avoiding_pieces
      refinedRoutesAvoid firstRefinedNodup secondRefinedNodup
      firstPrefixAvoidSecondFan firstPrefixSecondFanContacts
      firstFanAvoidSecondPrefix firstFanSecondPrefixContacts
      concreteFansAvoid concreteFanContacts
      firstOuterHead secondOuterHead
      firstEntrance firstFanHead secondEntrance secondFanHead
  simpa [retainedAngularFanSplicedBoundaryPolyline,
    firstRefined, secondRefined, firstScaled, secondScaled,
    firstFan, secondFan, firstCenter, secondCenter,
    firstScaledTerminal, secondScaledTerminal] using assembled

end PeriodicEightOccurrenceSplit
end LeanTrominoes
