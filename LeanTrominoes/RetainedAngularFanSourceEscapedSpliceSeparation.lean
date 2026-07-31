import LeanTrominoes.OrthogonalPolylineTailReplacementSeparation
import LeanTrominoes.RetainedAngularFanSourceEscapedSplice
import LeanTrominoes.RetainedAngularFanSourceScaledSeparation

/-!
# Separation of one escaped and one ordinary retained source splice

A failed final direct-source choice with a singleton source prefix now uses
the delayed-lane escaped fan.  At another literal of the same clause, the
fallback prefix is necessarily non-singleton.  The escaped fan may therefore
meet that retained source prefix at their common clause head, while every
other newly introduced piece pair must be strictly separated.

This file packages that asymmetric tail-replacement pattern.  Its remaining
hypotheses are precisely the local geometric facts needed from the final
carrier/bend analysis.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- A singleton refined source prefix is the escaped fan's own head, so
escaped/ordinary fan separation supplies the directed prefix/ordinary-fan
cross case by restriction. -/
theorem
    retainedAngularFanSourceScaledPrefix_strictlyAvoids_otherOuterCompleteRoute_of_singletonPrefix_of_escapedFansAvoid
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
        (retainedTerminalFanOuterEscapedCompleteRoute
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
        retainedTerminalFanOuterEscapedCompleteRoute
          sourceCenter sourceScaledTerminal sourceSlot := by
    exact List.mem_of_mem_head?
      (retainedTerminalFanOuterEscapedCompleteRoute_head?
        sourceCenter sourceScaledTerminal sourceSlot)
  rw [prefixEq]
  apply fansAvoid.singleton_left
  simpa [sourceCenter, sourceScaledTerminal] using
    sourceGateMember

/-- Replacing a singleton-prefix route by its escaped fan and another route
by its ordinary fan preserves common-head-only avoidance.  The escaped fan
may meet the second retained prefix only at their inherited common head; all
other replacement-piece pairs remain strictly separated. -/
theorem
    retainedAngularFanEscapedOrdinarySplicedBoundaryPolylines_avoid_of_first_singletonPrefix
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
    (firstSingletonPrefix :
      firstRoute.dropLast.length = 1)
    (firstPrefixAvoidSecondFan :
      RoutesStrictlyAvoidEachOther
        (scalePolyline retainedTerminalFanTotalRefinement
          firstRoute).dropLast
        (retainedTerminalFanOuterCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            (secondRoute.getLastD (0, 0)))
          secondTerminal secondSlot))
    (firstEscapedFanAvoidSecondPrefix :
      RoutesAvoidEachOther
        (retainedTerminalFanOuterEscapedCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            (firstRoute.getLastD (0, 0)))
          firstTerminal firstSlot)
        (scalePolyline retainedTerminalFanTotalRefinement
          secondRoute).dropLast)
    (firstEscapedFanSecondPrefixContactsAtHeads :
      RoutesMeetOnlyAtHeads
        (retainedTerminalFanOuterEscapedCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            (firstRoute.getLastD (0, 0)))
          firstTerminal firstSlot)
        (scalePolyline retainedTerminalFanTotalRefinement
          secondRoute).dropLast)
    (fansAvoid :
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterEscapedCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            (firstRoute.getLastD (0, 0)))
          firstTerminal firstSlot)
        (retainedTerminalFanOuterCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            (secondRoute.getLastD (0, 0)))
          secondTerminal secondSlot)) :
    RoutesAvoidEachOther
        (retainedAngularFanEscapedSplicedBoundaryPolyline
          firstRoute firstTerminal firstSlot)
        (retainedAngularFanSplicedBoundaryPolyline
          secondRoute secondTerminal secondSlot) ∧
      RoutesMeetOnlyAtHeads
        (retainedAngularFanEscapedSplicedBoundaryPolyline
          firstRoute firstTerminal firstSlot)
        (retainedAngularFanSplicedBoundaryPolyline
          secondRoute secondTerminal secondSlot) := by
  let firstScaled :=
    scalePolyline retainedTerminalFanTotalRefinement firstRoute
  let secondScaled :=
    scalePolyline retainedTerminalFanTotalRefinement secondRoute
  let firstCenter :=
    Cell.scale retainedTerminalFanTotalRefinement
      (firstRoute.getLastD (0, 0))
  let secondCenter :=
    Cell.scale retainedTerminalFanTotalRefinement
      (secondRoute.getLastD (0, 0))
  let firstFan :=
    retainedTerminalFanOuterEscapedCompleteRoute
      firstCenter firstTerminal firstSlot
  let secondFan :=
    retainedTerminalFanOuterCompleteRoute
      secondCenter secondTerminal secondSlot
  have firstReverseTailExists :
      ∃ entrance, firstScaled.reverse.tail.head? =
        some entrance := by
    apply exists_reverse_tail_head?_of_two_le_length
    simpa [firstScaled, scalePolyline] using firstLength
  have secondReverseTailExists :
      ∃ entrance, secondScaled.reverse.tail.head? =
        some entrance := by
    apply exists_reverse_tail_head?_of_two_le_length
    simpa [secondScaled, scalePolyline] using secondLength
  have firstLastEntrance :
      polylineLastEntrance firstScaled =
        (retainedAngularFanOuterDemand
          firstCenter firstTerminal firstSlot).gate := by
    exact polylineLastEntrance_scalePolyline_eq_outerDemand_gate
      firstLength firstClassified firstSlot
  have secondLastEntrance :
      polylineLastEntrance secondScaled =
        (retainedAngularFanOuterDemand
          secondCenter secondTerminal secondSlot).gate := by
    exact polylineLastEntrance_scalePolyline_eq_outerDemand_gate
      secondLength secondClassified secondSlot
  have firstReverseTailHead :
      firstScaled.reverse.tail.head? =
        some
          (retainedAngularFanOuterDemand
            firstCenter firstTerminal firstSlot).gate := by
    rw [polylineLastEntrance_spec firstReverseTailExists,
      firstLastEntrance]
  have secondReverseTailHead :
      secondScaled.reverse.tail.head? =
        some
          (retainedAngularFanOuterDemand
            secondCenter secondTerminal secondSlot).gate := by
    rw [polylineLastEntrance_spec secondReverseTailExists,
      secondLastEntrance]
  have firstEntrance :
      firstScaled.dropLast.getLast? =
        some
          (retainedAngularFanOuterDemand
            firstCenter firstTerminal firstSlot).gate :=
    dropLast_getLast?_of_reverse_tail_head?
      firstReverseTailHead
  have secondEntrance :
      secondScaled.dropLast.getLast? =
        some
          (retainedAngularFanOuterDemand
            secondCenter secondTerminal secondSlot).gate :=
    dropLast_getLast?_of_reverse_tail_head?
      secondReverseTailHead
  have firstFanHead :
      firstFan.head? =
        some
          (retainedAngularFanOuterDemand
            firstCenter firstTerminal firstSlot).gate := by
    exact retainedTerminalFanOuterEscapedCompleteRoute_head?
      firstCenter firstTerminal firstSlot
  have secondFanHead :
      secondFan.head? =
        some
          (retainedAngularFanOuterDemand
            secondCenter secondTerminal secondSlot).gate := by
    exact retainedTerminalFanOuterCompleteRoute_head?
      secondCenter secondTerminal secondSlot
  have refinementPositive :
      (0 : Int) <
        retainedTerminalFanTotalRefinement := by
    norm_num [retainedTerminalFanTotalRefinement,
      PeriodicEightOccurrenceSplitPositioned.refinementScale,
      retainedTerminalFanRoutingRefinement]
  have scaledRoutesAvoid :
      RoutesAvoidEachOther firstScaled secondScaled := by
    simpa [firstScaled, secondScaled] using
      sourceRoutesAvoid.scalePolyline refinementPositive
  have firstScaledNodup : firstScaled.Nodup := by
    exact
      List.Nodup.map
        (Cell.scale_injective refinementPositive.ne')
        firstNodup
  have secondScaledNodup : secondScaled.Nodup := by
    exact
      List.Nodup.map
        (Cell.scale_injective refinementPositive.ne')
        secondNodup
  have firstScaledSingleton :
      firstScaled.dropLast.length = 1 := by
    simpa [firstScaled, scalePolyline] using
      firstSingletonPrefix
  rcases List.length_eq_one_iff.mp firstScaledSingleton with
    ⟨firstHead, firstPrefixEq⟩
  have firstHeadEq :
      firstHead =
        (retainedAngularFanOuterDemand
          firstCenter firstTerminal firstSlot).gate := by
    rw [firstPrefixEq] at firstEntrance
    simpa using Option.some.inj firstEntrance
  have firstOuterHead :
      firstScaled.dropLast.head? = firstFan.head? := by
    rw [firstPrefixEq, firstFanHead]
    simp [firstHeadEq]
  have assembled :=
    RoutesAvoidEachOther.replace_tails_of_first_replacement_head_contact
      scaledRoutesAvoid firstScaledNodup secondScaledNodup
      (by
        simpa [firstScaled, secondFan, secondCenter] using
          firstPrefixAvoidSecondFan)
      (by
        simpa [firstFan, firstCenter, secondScaled] using
          firstEscapedFanAvoidSecondPrefix)
      (by
        simpa [firstFan, firstCenter, secondScaled] using
          firstEscapedFanSecondPrefixContactsAtHeads)
      (by
        simpa [firstFan, firstCenter, secondFan, secondCenter] using
          fansAvoid)
      firstOuterHead
      firstEntrance firstFanHead
      secondEntrance secondFanHead
  simpa [retainedAngularFanEscapedSplicedBoundaryPolyline,
    retainedAngularFanSplicedBoundaryPolyline,
    firstScaled, secondScaled, firstCenter, secondCenter,
    firstFan, secondFan] using assembled

end PeriodicEightOccurrenceSplit
end LeanTrominoes
