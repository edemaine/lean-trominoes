/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCrossClauseFallbackDirectionSeparation
import LeanTrominoes.RetainedAngularFanOuterCrossSeparation

/-!
# Angular order of shared-center fallback routes

At one final variable center, the retained terminal profile orders genuine
occurrences by nondecreasing terminal-direction rank.  Distinct fallback
routes at that center have different directions, so their coordinated slots
and direction ranks in fact increase strictly in the same orientation.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 4000000

/-- Failed choices in different final source clauses at one variable center
have coordinated slots and terminal-direction ranks in the same strict
order. -/
theorem
    retainedFinalCrossClauseFallbackTerminalAngularOrder_of_sameCenter
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
      firstClauseIndex ≠ secondClauseIndex)
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          firstClause firstLiteral =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          secondClause secondLiteral) :
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
    (firstSlot.val < secondSlot.val ∧
        firstTerminal.1.angularRank <
          secondTerminal.1.angularRank) ∨
      (secondSlot.val < firstSlot.val ∧
        secondTerminal.1.angularRank <
          firstTerminal.1.angularRank) := by
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
  have atomsEqual :
      firstLiteral.atom = secondLiteral.atom :=
    retainedFinalCanonicalLiteralPositions_eq_imp_atoms_eq
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
      firstClauseMember secondClauseMember
      firstLiteralMember secondLiteralMember centersEqual
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
        firstProfileSlot = secondProfileSlot :=
      Fin.ext valuesEqual
    apply
      retainedFinalCrossClauseCoordinatedOccurrenceSlots_ne_of_sameCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember
        clauseIndicesDifferent centersEqual
    rw [← firstSlotEq, ← secondSlotEq]
    exact profileSlotsEqual
  have ranksDifferent :
      firstTerminal.1.angularRank ≠
        secondTerminal.1.angularRank := by
    simpa [firstTerminal, secondTerminal, routes,
      firstCopy, secondCopy, occurrenceTerminalVector,
      finalCoordinatedSourceRoutes] using
      retainedFinalCrossClauseFallbackTerminalAngularRanks_ne_of_sameCenter
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember
        firstChoiceNone secondChoiceNone
        clauseIndicesDifferent centersEqual
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
