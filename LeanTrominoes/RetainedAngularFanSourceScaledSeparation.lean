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

end PeriodicEightOccurrenceSplit
end LeanTrominoes
