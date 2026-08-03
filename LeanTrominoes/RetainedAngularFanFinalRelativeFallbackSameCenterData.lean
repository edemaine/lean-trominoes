import LeanTrominoes.RetainedAngularFanFinalRelativeCopiedSourceReduction
import LeanTrominoes.RetainedAngularFanFinalCrossClauseFallbackOrder

/-!
# Same-center data for translated fallback pairs

Two failed-choice source routes may end at the same physical variable after
one is translated by a nonzero period.  The occurrences are nevertheless
different entries of the finite angular order, hence receive different
slots.  Because both failed-choice source routes are orthogonal, relative
source planarity also forces their terminal directions to differ.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Different stored incidences whose canonical targets coincide only after
a nonzero period translation receive different coordinated fan slots. -/
theorem
    retainedFinalCoordinatedOccurrenceSlots_ne_of_center_eq_translated_of_nonzero
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
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0))
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          firstClause firstLiteral =
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            secondClause secondLiteral)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate)) :
    retainedFinalCoordinatedOccurrenceSlot
        formula firstLiteral firstClauseIndex firstLiteralIndex ≠
      retainedFinalCoordinatedOccurrenceSlot
        formula secondLiteral secondClauseIndex secondLiteralIndex := by
  let source :=
    (finalCoordinatedSource formula).scale
      retainedAngularFanSourceClearanceFactor
  let routes :=
    PositionedPeriodicCNF.scaleIncidenceRoutes
      retainedAngularFanSourceClearanceFactor
      (finalCoordinatedSourceRoutes formula)
  let order := angularOccurrenceOrder source.erase routes
  have atomsEqual : firstLiteral.atom = secondLiteral.atom :=
    retainedFinalCanonicalLiteralPosition_eq_translated_imp_atoms_eq
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstClauseMember secondClauseMember
      firstLiteralMember secondLiteralMember relativeTranslate centersEqual
  let firstOccurrence :
      ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable) :=
    (firstLiteral.atom, firstClauseIndex, firstLiteralIndex)
  let secondOccurrence :
      ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable) :=
    (secondLiteral.atom, secondClauseIndex, secondLiteralIndex)
  let ordered := order.copies firstLiteral.atom
  have firstScaledClauseMember :
      (firstClause.scale retainedAngularFanSourceClearanceFactor,
          firstClauseIndex) ∈ source.clauses.zipIdx := by
    dsimp only [source]
    rw [PositionedPeriodicCNF.scale_clauses, List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(firstClause, firstClauseIndex), firstClauseMember, rfl⟩
  have secondScaledClauseMember :
      (secondClause.scale retainedAngularFanSourceClearanceFactor,
          secondClauseIndex) ∈ source.clauses.zipIdx := by
    dsimp only [source]
    rw [PositionedPeriodicCNF.scale_clauses, List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(secondClause, secondClauseIndex), secondClauseMember, rfl⟩
  have firstOccurrenceMember :
      firstOccurrence ∈
        occurrenceVariables source.erase firstLiteral.atom := by
    exact occurrenceVariables_mem _
      (taggedLiteral_mem_of_positioned_members
        source firstScaledClauseMember firstLiteralMember)
  have secondOccurrenceMember :
      secondOccurrence ∈
        occurrenceVariables source.erase firstLiteral.atom := by
    simpa [secondOccurrence, atomsEqual] using
      (occurrenceVariables_mem _
        (taggedLiteral_mem_of_positioned_members
          source secondScaledClauseMember secondLiteralMember))
  have firstOrderedMember : firstOccurrence ∈ ordered :=
    (order.mem_iff firstLiteral.atom firstOccurrence).mpr
      firstOccurrenceMember
  have secondOrderedMember : secondOccurrence ∈ ordered :=
    (order.mem_iff firstLiteral.atom secondOccurrence).mpr
      secondOccurrenceMember
  have occurrencesDifferent : firstOccurrence ≠ secondOccurrence := by
    simpa [firstOccurrence, secondOccurrence, atomsEqual] using
      retainedFinalOccurrenceIndices_ne_of_center_eq_translated_of_nonzero
        formula firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember
        relativeTranslate relativeTranslateNonzero centersEqual
  intro slotsEqual
  apply occurrencesDifferent
  apply idxOf_injective_on ordered
    firstOrderedMember secondOrderedMember
  have slotValuesEqual := congrArg Fin.val slotsEqual
  have firstSlotVal :=
    retainedFinalCoordinatedOccurrenceSlot_val
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstClauseMember firstLiteralMember
  have secondSlotVal :=
    retainedFinalCoordinatedOccurrenceSlot_val
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty secondClauseMember secondLiteralMember
  simpa [source, routes, order, ordered,
    firstOccurrence, secondOccurrence,
    angularOccurrenceIndex, indexedOccurrence, atomsEqual,
    finalCoordinatedSource, finalCoordinatedSourceRoutes,
    firstSlotVal, secondSlotVal] using slotValuesEqual

/-- Failed-choice source routes ending at one physical target after a
nonzero period translation have different terminal directions. -/
theorem
    retainedFinalFallbackTerminalDirections_ne_of_center_eq_translated_of_nonzero
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
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0))
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          firstClause firstLiteral =
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            secondClause secondLiteral)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate)) :
    (classifiedRetainedTerminalData
        (routeTerminalVector
          (finalCoordinatedSourceRoutes
            formula firstClauseIndex firstLiteralIndex))).1 ≠
      (classifiedRetainedTerminalData
        (routeTerminalVector
          (finalCoordinatedSourceRoutes
            formula secondClauseIndex secondLiteralIndex))).1 := by
  let placement := finalCoordinatedPlacement formula
  let firstRoute :=
    finalCoordinatedSourceRoutes
      formula firstClauseIndex firstLiteralIndex
  let secondRoute :=
    finalCoordinatedSourceRoutes
      formula secondClauseIndex secondLiteralIndex
  let translatedSecondRoute :=
    translatePolyline
      (placement.translation relativeTranslate) secondRoute
  let firstTerminal : RetainedTerminalData :=
    classifiedRetainedTerminalData (routeTerminalVector firstRoute)
  let secondTerminal : RetainedTerminalData :=
    classifiedRetainedTerminalData (routeTerminalVector secondRoute)
  have firstLength : 2 ≤ firstRoute.length := by
    simpa [firstRoute] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember firstLiteralMember
  have secondLength : 2 ≤ secondRoute.length := by
    simpa [secondRoute] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty secondClauseMember secondLiteralMember
  have translatedSecondLength :
      2 ≤ translatedSecondRoute.length := by
    simpa [translatedSecondRoute, translatePolyline] using secondLength
  have firstOrthogonal : OrthogonalPolyline firstRoute := by
    simpa [firstRoute] using
      finalCoordinatedFallbackSourceRoute_orthogonal
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember firstLiteralMember
        firstChoiceNone
  have secondOrthogonal : OrthogonalPolyline secondRoute := by
    simpa [secondRoute] using
      finalCoordinatedFallbackSourceRoute_orthogonal
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty secondClauseMember secondLiteralMember
        secondChoiceNone
  have translatedSecondOrthogonal :
      OrthogonalPolyline translatedSecondRoute :=
    secondOrthogonal.translate (placement.translation relativeTranslate)
  have firstEndpoints :=
    finalCoordinatedSourceRoutes_endpoints
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstClauseMember firstLiteralMember
  have secondEndpoints :=
    finalCoordinatedSourceRoutes_endpoints
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty secondClauseMember secondLiteralMember
  have translatedSecondLast :
      translatedSecondRoute.getLast? =
        some
          (Cell.add (placement.translation relativeTranslate)
            (PositionedPeriodicCNF.canonicalLiteralPosition
              placement secondClause secondLiteral)) := by
    simp [translatedSecondRoute, translatePolyline,
      secondRoute, placement, secondEndpoints.2]
  have sameFinish :
      firstRoute.getLast? = translatedSecondRoute.getLast? := by
    rw [show firstRoute.getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            placement firstClause firstLiteral) by
          simpa [firstRoute, placement] using firstEndpoints.2,
      translatedSecondLast]
    apply congrArg some
    simpa [placement, Cell.add, add_comm] using centersEqual
  have rawAvoid :
      RoutesAvoidEachOther firstRoute translatedSecondRoute := by
    simpa [firstRoute, secondRoute, translatedSecondRoute,
      placement] using
      finalCoordinatedSourceRoutes_avoid_translated_of_nonzero
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember
        relativeTranslate relativeTranslateNonzero
  have firstClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector firstRoute) = some firstTerminal := by
    simpa [firstRoute, firstTerminal] using
      finalCoordinatedSourceRoute_classified
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseMember firstLiteralMember
  have secondClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector secondRoute) = some secondTerminal := by
    simpa [secondRoute, secondTerminal] using
      finalCoordinatedSourceRoute_classified
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty secondClauseMember secondLiteralMember
  have translatedSecondClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector translatedSecondRoute) =
        some secondTerminal := by
    simpa [translatedSecondRoute,
      routeTerminalVector_translatePolyline] using secondClassified
  change firstTerminal.1 ≠ secondTerminal.1
  exact
    retainedTerminalDataDirections_ne_of_routesAvoidEachOther
      firstTerminal secondTerminal
      firstLength translatedSecondLength
      firstOrthogonal translatedSecondOrthogonal
      sameFinish rawAvoid firstClassified translatedSecondClassified

/-- At a shared physical target, two translated failed-choice occurrences
have slots and terminal-direction ranks increasing in the same strict
orientation. -/
theorem
    retainedFinalFallbackTerminalStrictAngularOrder_of_center_eq_translated_of_nonzero
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
    (relativeTranslate : Cell)
    (relativeTranslateNonzero : relativeTranslate ≠ (0, 0))
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          firstClause firstLiteral =
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            secondClause secondLiteral)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate)) :
    let firstTerminal :=
      classifiedRetainedTerminalData
        (routeTerminalVector
          (finalCoordinatedSourceRoutes
            formula firstClauseIndex firstLiteralIndex))
    let secondTerminal :=
      classifiedRetainedTerminalData
        (routeTerminalVector
          (finalCoordinatedSourceRoutes
            formula secondClauseIndex secondLiteralIndex))
    let firstSlot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula firstLiteral firstClauseIndex firstLiteralIndex
    let secondSlot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula secondLiteral secondClauseIndex secondLiteralIndex
    DirectFallbackStrictAngularOrderCompatible
      firstTerminal.1 secondTerminal.1 firstSlot secondSlot := by
  dsimp only
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
  have atomsEqual : firstLiteral.atom = secondLiteral.atom :=
    retainedFinalCanonicalLiteralPosition_eq_translated_imp_atoms_eq
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstClauseMember secondClauseMember
      firstLiteralMember secondLiteralMember relativeTranslate centersEqual
  let source := retainedPlanarSATFormula formula
  let routes := finalCoordinatedSourceRoutes formula
  let firstCopy :
      ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable) :=
    (firstLiteral.atom, firstClauseIndex, firstLiteralIndex)
  let secondCopy :
      ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable) :=
    (secondLiteral.atom, secondClauseIndex, secondLiteralIndex)
  have firstCopyMember :
      firstCopy ∈ occurrenceVariables source firstLiteral.atom := by
    exact occurrenceVariables_mem _
      (taggedLiteral_mem_of_positioned_members
        (finalCoordinatedSource formula)
        firstClauseMember firstLiteralMember)
  have secondCopyMember :
      secondCopy ∈ occurrenceVariables source secondLiteral.atom := by
    exact occurrenceVariables_mem _
      (taggedLiteral_mem_of_positioned_members
        (finalCoordinatedSource formula)
        secondClauseMember secondLiteralMember)
  have secondCopyMemberAtFirst :
      secondCopy ∈ occurrenceVariables source firstLiteral.atom := by
    simpa [atomsEqual] using secondCopyMember
  have terminalCertificate :
      RetainedOccurrenceTerminalCertificate source routes := by
    simpa [source, routes, finalCoordinatedSourceRoutes,
      retainedPlanarSATFormula] using
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATOccurrence_terminalCertificate
        formula certificate.graphWellFormed
        certificate.graphDegreeAtMostThree certificate.graphIsLocal
        retainedClausesNonempty
  have baseFits :
      FitsEightSlots (angularOccurrenceOrder source routes) := by
    simpa [source, routes, finalCoordinatedSourceRoutes,
      retainedDrawingAngularOccurrenceOrder] using fits
  let profile :=
    retainedAngularTerminalProfile
      source routes terminalCertificate baseFits firstLiteral.atom
  let firstProfileSlot :=
    retainedAngularTerminalSlot
      source routes baseFits firstLiteral.atom
      firstCopy firstCopyMember
  let secondProfileSlot :=
    retainedAngularTerminalSlot
      source routes baseFits firstLiteral.atom
      secondCopy secondCopyMemberAtFirst
  let firstTerminal :=
    classifiedRetainedTerminalData
      (occurrenceTerminalVector routes firstCopy)
  let secondTerminal :=
    classifiedRetainedTerminalData
      (occurrenceTerminalVector routes secondCopy)
  have firstLookup :
      profile.terminals[firstProfileSlot.val]? =
        some firstTerminal := by
    exact
      retainedAngularTerminalProfile_getElem_slot
        source routes terminalCertificate baseFits
        firstLiteral.atom firstCopy firstCopyMember
  have secondLookup :
      profile.terminals[secondProfileSlot.val]? =
        some secondTerminal := by
    exact
      retainedAngularTerminalProfile_getElem_slot
        source routes terminalCertificate baseFits
        firstLiteral.atom secondCopy secondCopyMemberAtFirst
  have firstSlotEq :
      firstProfileSlot =
        retainedFinalCoordinatedOccurrenceSlot
          formula firstLiteral
          firstClauseIndex firstLiteralIndex := by
    simpa [firstProfileSlot, source, routes, baseFits,
      retainedFinalAngularTerminalSlot,
      finalCoordinatedSourceRoutes,
      retainedDrawingAngularOccurrenceOrder] using
      retainedFinalAngularTerminalSlot_eq_coordinatedOccurrenceSlot
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty fits
        firstClauseMember firstLiteralMember
        firstLiteral.atom rfl firstCopyMember
  have secondSlotEq :
      secondProfileSlot =
        retainedFinalCoordinatedOccurrenceSlot
          formula secondLiteral
          secondClauseIndex secondLiteralIndex := by
    simpa [secondProfileSlot, source, routes, baseFits,
      retainedFinalAngularTerminalSlot,
      finalCoordinatedSourceRoutes,
      retainedDrawingAngularOccurrenceOrder] using
      retainedFinalAngularTerminalSlot_eq_coordinatedOccurrenceSlot
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty fits
        secondClauseMember secondLiteralMember
        firstLiteral.atom atomsEqual secondCopyMemberAtFirst
  have slotsDifferent :
      firstProfileSlot.val ≠ secondProfileSlot.val := by
    intro valuesEqual
    have profileSlotsEqual :
        firstProfileSlot = secondProfileSlot := Fin.ext valuesEqual
    apply
      retainedFinalCoordinatedOccurrenceSlots_ne_of_center_eq_translated_of_nonzero
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember
        relativeTranslate relativeTranslateNonzero centersEqual
    rw [← firstSlotEq, ← secondSlotEq]
    exact profileSlotsEqual
  have directionsDifferent : firstTerminal.1 ≠ secondTerminal.1 := by
    simpa [firstTerminal, secondTerminal, routes,
      firstCopy, secondCopy, occurrenceTerminalVector,
      finalCoordinatedSourceRoutes] using
      retainedFinalFallbackTerminalDirections_ne_of_center_eq_translated_of_nonzero
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember
        firstChoiceNone secondChoiceNone
        relativeTranslate relativeTranslateNonzero centersEqual
  have ranksDifferent :
      firstTerminal.1.angularRank ≠
        secondTerminal.1.angularRank := by
    intro ranksEqual
    exact directionsDifferent
      (RetainedTerminalDirection.angularRank_injective ranksEqual)
  unfold DirectFallbackStrictAngularOrderCompatible
  rcases lt_or_gt_of_ne slotsDifferent with slotsLt | slotsGt
  · have ranksLe :=
      profile.directionRank_le_of_lookups
        firstProfileSlot secondProfileSlot
        firstTerminal secondTerminal
        firstLookup secondLookup slotsLt
    left
    rw [firstSlotEq, secondSlotEq] at slotsLt
    simpa [firstTerminal, secondTerminal, routes,
      firstCopy, secondCopy, occurrenceTerminalVector,
      finalCoordinatedSourceRoutes] using
      And.intro slotsLt (Nat.lt_of_le_of_ne ranksLe ranksDifferent)
  · have ranksLe :=
      profile.directionRank_le_of_lookups
        secondProfileSlot firstProfileSlot
        secondTerminal firstTerminal
        secondLookup firstLookup slotsGt
    right
    rw [firstSlotEq, secondSlotEq] at slotsGt
    have ranksLt :
        secondTerminal.1.angularRank <
          firstTerminal.1.angularRank :=
      Nat.lt_of_le_of_ne ranksLe ranksDifferent.symm
    simpa [firstTerminal, secondTerminal, routes,
      firstCopy, secondCopy, occurrenceTerminalVector,
      finalCoordinatedSourceRoutes] using
      And.intro slotsGt ranksLt

end PeriodicOrthocrossing
end LeanTrominoes
