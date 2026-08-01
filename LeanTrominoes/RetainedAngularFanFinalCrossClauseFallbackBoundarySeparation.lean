import LeanTrominoes.RetainedAngularFanFinalCrossClauseOccurrenceSuffixSeparation
import LeanTrominoes.RetainedAngularFanFinalDirectSourceSameTargetClassification
import LeanTrominoes.RetainedFinalPositionedOccurrenceSpliceSeparation
import LeanTrominoes.RetainedFinalSourceRouteOtherVertexFinalSegmentSeparation

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 4000000

/-- The legacy occurrence-membership slot and the final coordinated slot
have the same value.  The explicit atom equality also covers uses where a
shared-center theorem transports the second occurrence into the first
atom's occurrence list. -/
theorem retainedFinalAngularTerminalSlot_eq_coordinatedOccurrenceSlot
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (fits :
      FitsEightSlots
        (retainedDrawingAngularOccurrenceOrder formula))
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (atom : WrappedPeriodicPlanarSATVariable Variable)
    (atomEqual : atom = literal.atom)
    (copyMember :
      (literal.atom, clauseIndex, literalIndex) ∈
        occurrenceVariables
          (retainedPlanarSATFormula formula) atom) :
    retainedFinalAngularTerminalSlot
        formula fits atom
        (literal.atom, clauseIndex, literalIndex) copyMember =
      retainedFinalCoordinatedOccurrenceSlot
        formula literal clauseIndex literalIndex := by
  apply Fin.ext
  unfold retainedFinalAngularTerminalSlot
  rw [retainedAngularTerminalSlot_val]
  rw [retainedFinalCoordinatedOccurrenceSlot_val
    formula sourceLocal sourceWidth sourceOccurrences
    sourceClausesNonempty clauseMember literalMember]
  unfold angularOccurrenceIndex
  rw [PositionedPeriodicCNF.erase_scale,
    angularOccurrenceOrder_scaleIncidenceRoutes
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        formula).erase
      retainedAngularFanSourceClearanceFactor_pos
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        formula)]
  simpa [indexedOccurrence, atomEqual,
    retainedPlanarSATFormula, finalCoordinatedSource]

/-- Ordinary boundary splices of two failed choices in different final
source clauses are contact-free. -/
theorem retainedFinalCrossClauseFallbackOrdinaryBoundarySplices_strictlyAvoid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {firstClause secondClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    (firstChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula firstClauseIndex firstLiteralIndex = none)
    (secondChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula secondClauseIndex secondLiteralIndex = none)
    (clauseIndicesDifferent :
      firstClauseIndex ≠ secondClauseIndex) :
    RoutesStrictlyAvoidEachOther
      (retainedAngularFanSplicedBoundaryPolyline
        (scalePolyline retainedAngularFanSourceClearanceFactor
          (finalCoordinatedSourceRoutes
            formula firstClauseIndex firstLiteralIndex))
        (scaleRetainedTerminalData
          retainedAngularFanSourceClearanceFactor
          (classifiedRetainedTerminalData
            (routeTerminalVector
              (finalCoordinatedSourceRoutes
                formula firstClauseIndex firstLiteralIndex))))
        (retainedFinalCoordinatedOccurrenceSlot
          formula firstLiteral
          firstClauseIndex firstLiteralIndex))
      (retainedAngularFanSplicedBoundaryPolyline
        (scalePolyline retainedAngularFanSourceClearanceFactor
          (finalCoordinatedSourceRoutes
            formula secondClauseIndex secondLiteralIndex))
        (scaleRetainedTerminalData
          retainedAngularFanSourceClearanceFactor
          (classifiedRetainedTerminalData
            (routeTerminalVector
              (finalCoordinatedSourceRoutes
                formula secondClauseIndex secondLiteralIndex))))
        (retainedFinalCoordinatedOccurrenceSlot
          formula secondLiteral
          secondClauseIndex secondLiteralIndex)) := by
  let certificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let retainedClausesNonempty :=
    retainedDrawingPlanarSATFormula_clausesNonempty_of_source
      formula sourceClausesNonempty
  have fits :=
    retainedDrawingAngularOccurrenceOrder_fitsEightSlots
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  have sourcesDifferent :=
    retainedFinalCanonicalClausePositions_ne
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
      firstClauseMember secondClauseMember clauseIndicesDifferent
  have copiesDifferent :
      (firstLiteral.atom, firstClauseIndex, firstLiteralIndex) ≠
        (secondLiteral.atom, secondClauseIndex, secondLiteralIndex) := by
    intro copiesEqual
    apply clauseIndicesDifferent
    exact congrArg (fun copy => copy.2.1) copiesEqual
  let firstCopy :
      ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable) :=
    (firstLiteral.atom, firstClauseIndex, firstLiteralIndex)
  let secondCopy :
      ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable) :=
    (secondLiteral.atom, secondClauseIndex, secondLiteralIndex)
  have firstCopyMember :
      firstCopy ∈
        occurrenceVariables
          (retainedPlanarSATFormula formula) firstLiteral.atom := by
    exact occurrenceVariables_mem _
      (taggedLiteral_mem_of_positioned_members
        (finalCoordinatedSource formula)
        firstClauseMember firstLiteralMember)
  have secondCopyMember :
      secondCopy ∈
        occurrenceVariables
          (retainedPlanarSATFormula formula) secondLiteral.atom := by
    exact occurrenceVariables_mem _
      (taggedLiteral_mem_of_positioned_members
        (finalCoordinatedSource formula)
        secondClauseMember secondLiteralMember)
  have firstSlotEq :
      retainedFinalAngularTerminalSlot
          formula fits firstLiteral.atom firstCopy firstCopyMember =
        retainedFinalCoordinatedOccurrenceSlot
          formula firstLiteral
          firstClauseIndex firstLiteralIndex := by
    exact
      retainedFinalAngularTerminalSlot_eq_coordinatedOccurrenceSlot
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty fits
        firstClauseMember firstLiteralMember
        firstLiteral.atom rfl firstCopyMember
  have secondSlotEq :
      retainedFinalAngularTerminalSlot
          formula fits secondLiteral.atom secondCopy secondCopyMember =
        retainedFinalCoordinatedOccurrenceSlot
          formula secondLiteral
          secondClauseIndex secondLiteralIndex := by
    exact
      retainedFinalAngularTerminalSlot_eq_coordinatedOccurrenceSlot
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty fits
        secondClauseMember secondLiteralMember
        secondLiteral.atom rfl secondCopyMember
  by_cases centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          firstClause firstLiteral =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          secondClause secondLiteral
  · have atomsEqual :=
      retainedFinalCanonicalLiteralPositions_eq_imp_atoms_eq
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember centersEqual
    have secondCopyMemberAtFirst :
        secondCopy ∈
          occurrenceVariables
            (retainedPlanarSATFormula formula) firstLiteral.atom := by
      simpa [atomsEqual] using secondCopyMember
    have secondSharedSlotEq :
        retainedFinalAngularTerminalSlot
            formula fits firstLiteral.atom secondCopy
              secondCopyMemberAtFirst =
          retainedFinalCoordinatedOccurrenceSlot
            formula secondLiteral
            secondClauseIndex secondLiteralIndex := by
      exact
        retainedFinalAngularTerminalSlot_eq_coordinatedOccurrenceSlot
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty fits
          secondClauseMember secondLiteralMember
          firstLiteral.atom atomsEqual secondCopyMemberAtFirst
    have separated :=
      PeriodicEightOccurrenceSplit.retainedFinalPositionedOccurrenceSplices_strictlyAvoid_of_sameCenter
        formula certificate.graphWellFormed
        certificate.graphDegreeAtMostThree
        certificate.graphIsLocal retainedClausesNonempty fits
        retainedAngularFanSourceClearanceFactor_gt_one
        (by native_decide)
        firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember
        atomsEqual copiesDifferent sourcesDifferent centersEqual
    dsimp only at separated
    rw [firstSlotEq, secondSharedSlotEq] at separated
    simpa only [firstCopy, secondCopy,
      finalCoordinatedSourceRoutes,
      occurrenceTerminalVector] using separated
  · have firstAligned :=
      finalCoordinatedFallbackSourceRoute_finalSegment_isAxisAligned
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        firstClauseMember firstLiteralMember firstChoiceNone
    have secondAligned :=
      finalCoordinatedFallbackSourceRoute_finalSegment_isAxisAligned
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        secondClauseMember secondLiteralMember secondChoiceNone
    have separated :=
      PeriodicEightOccurrenceSplit.retainedFinalPositionedOccurrenceSplices_strictlyAvoid_of_distinctCenters_of_axisAligned
        formula certificate.graphWellFormed
        certificate.graphDegreeAtMostThree
        certificate.graphIsLocal retainedClausesNonempty fits
        retainedAngularFanSourceClearanceFactor_gt_one
        (by native_decide)
        firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember
        copiesDifferent sourcesDifferent centersEqual
        firstAligned secondAligned
    simpa [firstCopy, secondCopy, firstSlotEq, secondSlotEq,
      finalCoordinatedSource, finalCoordinatedSourceRoutes,
      occurrenceTerminalVector] using separated

end PeriodicOrthocrossing
end LeanTrominoes
