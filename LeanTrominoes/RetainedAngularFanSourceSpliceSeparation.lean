import LeanTrominoes.OrthogonalPolylineTailReplacementSeparation
import LeanTrominoes.RetainedAngularFanSourceSplice

/-!
# Separation of retained source/fan splices

The pre-rasterized retained splice is a simultaneous tail replacement.
This module applies the generic replacement theorem and packages the exact
classified entrance equations.  Consequently, after the original source
routes and the two outer-fan suffixes are separated, only the two directed
source-prefix-versus-fan-suffix cross cases remain.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Two classified retained source/fan splices are strictly separated once
the two genuinely new directed prefix/suffix cross cases and suffix/suffix
separation are known. -/
theorem retainedAngularFanSplicedBoundaryPolylines_strictlyAvoid
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
          firstRoute).dropLast
        (retainedTerminalFanOuterCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            (secondRoute.getLastD (0, 0)))
          secondTerminal secondSlot))
    (firstFanAvoidSecondPrefix :
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            (firstRoute.getLastD (0, 0)))
          firstTerminal firstSlot)
        (scalePolyline retainedTerminalFanTotalRefinement
          secondRoute).dropLast)
    (fansAvoid :
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            (firstRoute.getLastD (0, 0)))
          firstTerminal firstSlot)
        (retainedTerminalFanOuterCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            (secondRoute.getLastD (0, 0)))
          secondTerminal secondSlot)) :
    RoutesStrictlyAvoidEachOther
      (retainedAngularFanSplicedBoundaryPolyline
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
    retainedTerminalFanOuterCompleteRoute
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
    exact retainedTerminalFanOuterCompleteRoute_head?
      firstCenter firstTerminal firstSlot
  have secondFanHead :
      secondFan.head? =
        some
          (retainedAngularFanOuterDemand
            secondCenter secondTerminal secondSlot).gate := by
    exact retainedTerminalFanOuterCompleteRoute_head?
      secondCenter secondTerminal secondSlot
  have scaledPrefixesAvoid :
      RoutesStrictlyAvoidEachOther
        firstScaled.dropLast secondScaled.dropLast := by
    have scaled :=
      sourcePrefixesAvoid.scalePolyline
        (factor :=
          (retainedTerminalFanTotalRefinement : Int))
        (by
          norm_num [retainedTerminalFanTotalRefinement,
            PeriodicEightOccurrenceSplitPositioned.refinementScale,
            retainedTerminalFanRoutingRefinement])
    simpa [firstScaled, secondScaled, scalePolyline] using scaled
  apply RoutesStrictlyAvoidEachOther.replace_tails_of_prefixes
    scaledPrefixesAvoid
    (by simpa [firstScaled, secondFan, secondCenter] using
      firstPrefixAvoidSecondFan)
    (by simpa [firstFan, firstCenter, secondScaled] using
      firstFanAvoidSecondPrefix)
    (by simpa [firstFan, firstCenter, secondFan, secondCenter] using
      fansAvoid)
    firstEntrance firstFanHead secondEntrance secondFanHead

/-- Two classified retained source/fan splices preserve ordinary
endpoint-only avoidance when the original source routes may share a clause
head.  Duplicate-freedom ensures that this head is the only contact retained
by the source prefixes; all geometry involving either fan suffix remains
strictly separated. -/
theorem retainedAngularFanSplicedBoundaryPolylines_avoid
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
          firstRoute).dropLast
        (retainedTerminalFanOuterCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            (secondRoute.getLastD (0, 0)))
          secondTerminal secondSlot))
    (firstFanAvoidSecondPrefix :
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            (firstRoute.getLastD (0, 0)))
          firstTerminal firstSlot)
        (scalePolyline retainedTerminalFanTotalRefinement
          secondRoute).dropLast)
    (fansAvoid :
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            (firstRoute.getLastD (0, 0)))
          firstTerminal firstSlot)
        (retainedTerminalFanOuterCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            (secondRoute.getLastD (0, 0)))
          secondTerminal secondSlot)) :
    RoutesAvoidEachOther
      (retainedAngularFanSplicedBoundaryPolyline
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
    retainedTerminalFanOuterCompleteRoute
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
    exact retainedTerminalFanOuterCompleteRoute_head?
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
  apply RoutesAvoidEachOther.replace_tails
    scaledRoutesAvoid firstScaledNodup secondScaledNodup
    (by simpa [firstScaled, secondFan, secondCenter] using
      firstPrefixAvoidSecondFan)
    (by simpa [firstFan, firstCenter, secondScaled] using
      firstFanAvoidSecondPrefix)
    (by simpa [firstFan, firstCenter, secondFan, secondCenter] using
      fansAvoid)
    firstEntrance firstFanHead secondEntrance secondFanHead

end PeriodicEightOccurrenceSplit
end LeanTrominoes
