import LeanTrominoes.RetainedAngularFanOccurrenceOuterSeparation
import LeanTrominoes.RetainedFinalFlatNormalizedCorridorSeparation
import LeanTrominoes.RetainedFinalTerminalGateDistinctness

/-!
# Final fan separation at a shared variable center

Two different retained incidences of one source variable end at the same
variable center.  Their angular occurrence slots nevertheless select
strictly separated outer fans.  Combining that finite fan fact with the
final retained source-prefix separation closes strict separation of the two
complete source-to-boundary splices, including oblique terminal directions.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 2000000

/-- The angular terminal slot of one genuine occurrence in the final retained
drawing, with the final drawing's named occurrence order as its public
interface. -/
def retainedFinalAngularTerminalSlot
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (fits :
      FitsEightSlots
        (PeriodicOrthocrossing.retainedDrawingAngularOccurrenceOrder
          formula))
    (atom :
      PeriodicOrthocrossing.WrappedPeriodicPlanarSATVariable Variable)
    (copy :
      ThreeOccurrenceVariable
        (PeriodicOrthocrossing.WrappedPeriodicPlanarSATVariable Variable))
    (copyMember :
      copy ∈
        occurrenceVariables
          (PeriodicOrthocrossing.retainedPlanarSATFormula formula)
          atom) :
    RetainedTerminalSlot :=
  retainedAngularTerminalSlot
    (PeriodicOrthocrossing.retainedPlanarSATFormula formula)
    (PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
      formula)
    (by
      simpa [PeriodicOrthocrossing.retainedDrawingAngularOccurrenceOrder]
        using fits)
    atom copy copyMember

/-- Distinct genuine occurrences of one variable whose final retained routes
share their variable endpoint produce strictly separated source-scaled
source-to-boundary splices.  No axis-alignment hypothesis is needed. -/
theorem
    retainedFinalSourceScaledSplicedBoundaryPolylines_strictlyAvoid_of_sameCenterOccurrences
    {Variable : Type*}
    [variableDecidableEq : DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (clausesNonempty :
      ∀ clause ∈
          PeriodicOrthocrossing.retainedDrawingPlanarSATFormula formula,
        clause.literals ≠ [])
    (fits :
      FitsEightSlots
        (PeriodicOrthocrossing.retainedDrawingAngularOccurrenceOrder
          formula))
    {factor : Nat} (factorGreaterThanOne : 1 < factor)
    (clearance :
      845 <
        retainedTerminalFanTotalRefinement * factor)
    (atom :
      PeriodicOrthocrossing.WrappedPeriodicPlanarSATVariable Variable)
    (firstCopy secondCopy :
      ThreeOccurrenceVariable
        (PeriodicOrthocrossing.WrappedPeriodicPlanarSATVariable Variable))
    (firstCopyMember :
      firstCopy ∈
        occurrenceVariables
          (PeriodicOrthocrossing.retainedPlanarSATFormula formula)
          atom)
    (secondCopyMember :
      secondCopy ∈
        occurrenceVariables
          (PeriodicOrthocrossing.retainedPlanarSATFormula formula)
          atom)
    (copiesDifferent : firstCopy ≠ secondCopy)
    {firstRoute secondRoute : List Cell}
    {firstIndex secondIndex : Nat}
    {firstSource secondSource center : Cell}
    (firstRouteEq :
      firstRoute =
        PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
          formula firstCopy.2.1 firstCopy.2.2)
    (secondRouteEq :
      secondRoute =
        PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
          formula secondCopy.2.1 secondCopy.2.2)
    (firstMember :
      (firstRoute, firstIndex) ∈
        (PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).edgeRoutes.zipIdx)
    (secondMember :
      (secondRoute, secondIndex) ∈
        (PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).edgeRoutes.zipIdx)
    (firstLength : 2 ≤ firstRoute.length)
    (secondLength : 2 ≤ secondRoute.length)
    (indicesDifferent : firstIndex ≠ secondIndex)
    (headsDifferent : firstRoute.head? ≠ secondRoute.head?)
    (firstHead : firstRoute.head? = some firstSource)
    (secondHead : secondRoute.head? = some secondSource)
    (firstLast : firstRoute.getLast? = some center)
    (secondLast : secondRoute.getLast? = some center)
    (firstSourceNeCenter : firstSource ≠ center)
    (secondSourceNeCenter : secondSource ≠ center) :
    RoutesStrictlyAvoidEachOther
      (retainedAngularFanSplicedBoundaryPolyline
        (scalePolyline factor firstRoute)
        (scaleRetainedTerminalData factor
          (classifiedRetainedTerminalData
            (occurrenceTerminalVector
              (PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
                formula)
              firstCopy)))
        (retainedFinalAngularTerminalSlot
          formula fits atom firstCopy firstCopyMember))
      (retainedAngularFanSplicedBoundaryPolyline
        (scalePolyline factor secondRoute)
        (scaleRetainedTerminalData factor
          (classifiedRetainedTerminalData
            (occurrenceTerminalVector
              (PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
                formula)
              secondCopy)))
        (retainedFinalAngularTerminalSlot
          formula fits atom secondCopy secondCopyMember)) := by
  let source :=
    PeriodicOrthocrossing.retainedPlanarSATFormula formula
  let routes :=
    PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
      formula
  have concreteFits :
      FitsEightSlots
        (angularOccurrenceOrder source routes) := by
    simpa [source, routes,
      PeriodicOrthocrossing.retainedDrawingAngularOccurrenceOrder]
      using fits
  let firstTerminal :=
    classifiedRetainedTerminalData
      (occurrenceTerminalVector routes firstCopy)
  let secondTerminal :=
    classifiedRetainedTerminalData
      (occurrenceTerminalVector routes secondCopy)
  let firstSlot :=
    retainedAngularTerminalSlot
      source routes concreteFits atom firstCopy firstCopyMember
  let secondSlot :=
    retainedAngularTerminalSlot
      source routes concreteFits atom secondCopy secondCopyMember
  have retained :
      RetainedOccurrenceTerminalCertificate source routes := by
    exact
      PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATOccurrence_terminalCertificate
        formula wellFormed degree isLocal clausesNonempty
  have vectorsInjective :
      RetainedOccurrenceTerminalVectorsInjective source routes := by
    exact
      PeriodicOrthocrossing.retainedDeduplicatedGaugedWrappedDrawing_terminalVectorsInjective
        formula wellFormed degree isLocal clausesNonempty
  have firstClassifiedOccurrence :
      retainedTerminalDirectionClassify
          (occurrenceTerminalVector routes firstCopy) =
        some firstTerminal := by
    exact
      retainedTerminalDirectionClassify_classifiedRetainedTerminalData
        (retained atom firstCopy firstCopyMember)
  have secondClassifiedOccurrence :
      retainedTerminalDirectionClassify
          (occurrenceTerminalVector routes secondCopy) =
        some secondTerminal := by
    exact
      retainedTerminalDirectionClassify_classifiedRetainedTerminalData
        (retained atom secondCopy secondCopyMember)
  have firstClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector firstRoute) =
        some firstTerminal := by
    rw [firstRouteEq]
    exact firstClassifiedOccurrence
  have secondClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector secondRoute) =
        some secondTerminal := by
    rw [secondRouteEq]
    exact secondClassifiedOccurrence
  let commonFanCenter :=
    Cell.scale retainedTerminalFanTotalRefinement
      (Cell.scale factor center)
  have fansAvoidCommon :
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterCompleteRoute
          commonFanCenter
          (scaleRetainedTerminalData factor firstTerminal)
          firstSlot)
        (retainedTerminalFanOuterCompleteRoute
          commonFanCenter
          (scaleRetainedTerminalData factor secondTerminal)
          secondSlot) := by
    exact
      retainedOccurrenceScaledOuterCompleteRoutes_strictlyAvoid_of_ne
        source routes retained vectorsInjective concreteFits
        factorGreaterThanOne.le atom firstCopy secondCopy
        firstCopyMember secondCopyMember copiesDifferent commonFanCenter
  have firstLastD :
      firstRoute.getLastD (0, 0) = center := by
    simp [List.getLastD_eq_getLast?, firstLast]
  have secondLastD :
      secondRoute.getLastD (0, 0) = center := by
    simp [List.getLastD_eq_getLast?, secondLast]
  have fansAvoid :
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
          secondSlot) := by
    rw [scalePolyline_getLastD, firstLastD,
      scalePolyline_getLastD, secondLastD]
    exact fansAvoidCommon
  simpa only [firstTerminal, secondTerminal, firstSlot, secondSlot,
    retainedFinalAngularTerminalSlot, source, routes] using
    retainedFinalSourceScaledSplicedBoundaryPolylines_strictlyAvoid
      formula wellFormed degree isLocal clausesNonempty
      factorGreaterThanOne clearance
      firstMember secondMember firstLength secondLength
      indicesDifferent headsDifferent
      firstHead secondHead firstLast secondLast
      firstSourceNeCenter secondSourceNeCenter
      firstTerminal secondTerminal firstSlot secondSlot
      firstClassified secondClassified fansAvoid

end PeriodicEightOccurrenceSplit
end LeanTrominoes
