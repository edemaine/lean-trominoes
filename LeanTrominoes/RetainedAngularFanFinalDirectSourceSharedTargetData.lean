/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalDirectSourceCrossClauseOrder
import LeanTrominoes.RetainedAngularFanFinalDirectSourceOtherCycleSeparation

/-!
# Shared-target data for final direct-source routes

Equality of two canonical final variable positions determines the same
wrapped atom even when the occurrences belong to different clauses.  For
successful direct-source selections it also determines a common physical
source endpoint, a common component origin, and the angular-order relation
required by the finite same-target atlas.
-/

namespace LeanTrominoes

namespace PositionedPeriodicCNF

/-- Equality of canonical lifted literal positions, possibly from different
clauses, identifies their fundamental-square representatives. -/
theorem canonicalLiteralPosition_eq_imp_position_eq
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (periodPositive : 0 < placement.period)
    (firstClause secondClause : PositionedPeriodicClause Variable)
    (firstLiteral secondLiteral : PeriodicLiteral Variable)
    (firstInSquare :
      0 ≤ (placement.position firstLiteral.atom).1 ∧
        (placement.position firstLiteral.atom).1 < placement.period ∧
        0 ≤ (placement.position firstLiteral.atom).2 ∧
        (placement.position firstLiteral.atom).2 < placement.period)
    (secondInSquare :
      0 ≤ (placement.position secondLiteral.atom).1 ∧
        (placement.position secondLiteral.atom).1 < placement.period ∧
        0 ≤ (placement.position secondLiteral.atom).2 ∧
        (placement.position secondLiteral.atom).2 < placement.period)
    (positionsEqual :
      canonicalLiteralPosition placement firstClause firstLiteral =
        canonicalLiteralPosition placement secondClause secondLiteral) :
    placement.position firstLiteral.atom =
      placement.position secondLiteral.atom := by
  rcases firstPositionEq :
      placement.position firstLiteral.atom with
    ⟨firstPositionX, firstPositionY⟩
  rcases secondPositionEq :
      placement.position secondLiteral.atom with
    ⟨secondPositionX, secondPositionY⟩
  rcases firstOffsetEq : firstLiteral.offset with
    ⟨firstOffsetX, firstOffsetY⟩
  rcases secondOffsetEq : secondLiteral.offset with
    ⟨secondOffsetX, secondOffsetY⟩
  simp only [canonicalLiteralPosition,
    PeriodicVariablePlacement.translation,
    Cell.add, Cell.sub, Cell.scale,
    firstPositionEq, secondPositionEq,
    firstOffsetEq, secondOffsetEq,
    Prod.mk.injEq] at positionsEqual
  simp only [firstPositionEq, secondPositionEq]
    at firstInSquare secondInSquare ⊢
  have horizontal :=
    periodicRepresentativeAndOffset_eq
      placement.period periodPositive
      firstPositionX secondPositionX
      (firstOffsetX -
        (PeriodicCNF.clauseAnchor firstClause.literals).1)
      (secondOffsetX -
        (PeriodicCNF.clauseAnchor secondClause.literals).1)
      firstInSquare.1 firstInSquare.2.1
      secondInSquare.1 secondInSquare.2.1
      positionsEqual.1
  have vertical :=
    periodicRepresentativeAndOffset_eq
      placement.period periodPositive
      firstPositionY secondPositionY
      (firstOffsetY -
        (PeriodicCNF.clauseAnchor firstClause.literals).2)
      (secondOffsetY -
        (PeriodicCNF.clauseAnchor secondClause.literals).2)
      firstInSquare.2.2.1 firstInSquare.2.2.2
      secondInSquare.2.2.1 secondInSquare.2.2.2
      positionsEqual.2
  exact Prod.ext horizontal.1 vertical.1

end PositionedPeriodicCNF

namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Equal canonical positions of two genuine final incidences determine the
same wrapped source atom. -/
theorem retainedFinalCanonicalLiteralPositions_eq_imp_atoms_eq
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
    (positionsEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          firstClause firstLiteral =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          secondClause secondLiteral) :
    firstLiteral.atom = secondLiteral.atom := by
  let source := finalCoordinatedSource formula
  let placement := finalCoordinatedPlacement formula
  let sourceCertificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  have firstAtomMember :
      firstLiteral.atom ∈ source.erase.variableOccurrences :=
    atom_mem_variableOccurrences_of_positioned_members
      source firstClauseMember firstLiteralMember
  have secondAtomMember :
      secondLiteral.atom ∈ source.erase.variableOccurrences :=
    atom_mem_variableOccurrences_of_positioned_members
      source secondClauseMember secondLiteralMember
  have firstValid :
      RetainedDrawingPeriodicPlanarSATVariableValid
        formula firstLiteral.atom.original :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSAT_variableOccurrences_valid
      formula
      sourceCertificate.graphWellFormed
      sourceCertificate.graphDegreeAtMostThree
      sourceCertificate.graphIsLocal
      (by simpa [source, finalCoordinatedSource] using firstAtomMember)
  have secondValid :
      RetainedDrawingPeriodicPlanarSATVariableValid
        formula secondLiteral.atom.original :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSAT_variableOccurrences_valid
      formula
      sourceCertificate.graphWellFormed
      sourceCertificate.graphDegreeAtMostThree
      sourceCertificate.graphIsLocal
      (by simpa [source, finalCoordinatedSource] using secondAtomMember)
  have firstStrictBounds :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_position_inSquare
      formula firstLiteral.atom
  have secondStrictBounds :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_position_inSquare
      formula secondLiteral.atom
  have positionEq :=
    PositionedPeriodicCNF.canonicalLiteralPosition_eq_imp_position_eq
      placement
      (by
        simpa [placement, finalCoordinatedPlacement,
          retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_period,
          wrappedDrawingPeriodicPlanarSATPlacement]
          using drawingPeriodicPlanarSATPlacement_period_pos formula)
      firstClause secondClause firstLiteral secondLiteral
      ⟨firstStrictBounds.1.le, firstStrictBounds.2.1,
        firstStrictBounds.2.2.1.le, firstStrictBounds.2.2.2⟩
      ⟨secondStrictBounds.1.le, secondStrictBounds.2.1,
        secondStrictBounds.2.2.1.le, secondStrictBounds.2.2.2⟩
      (by simpa [placement] using positionsEqual)
  exact
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_position_injective_of_valid
      formula
      sourceCertificate.graphWellFormed
      sourceCertificate.graphDegreeAtMostThree
      sourceCertificate.graphIsLocal
      firstValid secondValid
      (by simpa [placement, finalCoordinatedPlacement] using positionEq)

/-- Equal represented variable endpoints place two successful final direct
choices at the same physical component origin. -/
theorem retainedFinalDirectSourceRouteChoices_origins_eq_of_finishes_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (firstChoice secondChoice : RetainedDirectSourceRouteChoice)
    (firstClauseIndex firstLiteralIndex
      secondClauseIndex secondLiteralIndex : Nat)
    (firstLookup :
      retainedFinalDirectSourceRouteChoice?
          formula firstClauseIndex firstLiteralIndex =
        some firstChoice)
    (secondLookup :
      retainedFinalDirectSourceRouteChoice?
          formula secondClauseIndex secondLiteralIndex =
        some secondChoice)
    (finishesEqual :
      firstChoice.sourceSegment.finish =
        secondChoice.sourceSegment.finish) :
    firstChoice.origin = secondChoice.origin := by
  rcases retainedFinalDirectSourceRouteChoice_originData
      formula firstClauseIndex firstLiteralIndex
      firstChoice firstLookup with
    ⟨firstData⟩
  rcases retainedFinalDirectSourceRouteChoice_originData
      formula secondClauseIndex secondLiteralIndex
      secondChoice secondLookup with
    ⟨secondData⟩
  have firstBounds :=
    (retainedDirectSourceLocalRouteAt_endpoints_in_macrocell
      firstChoice.kind firstChoice.index).2
  have secondBounds :=
    (retainedDirectSourceLocalRouteAt_endpoints_in_macrocell
      secondChoice.kind secondChoice.index).2
  rcases firstData.center with ⟨firstCenterX, firstCenterY⟩
  rcases secondData.center with ⟨secondCenterX, secondCenterY⟩
  rcases
      (retainedDirectSourceLocalRouteAt
        firstChoice.kind firstChoice.index).getLastD (0, 0) with
    ⟨firstLocalX, firstLocalY⟩
  rcases
      (retainedDirectSourceLocalRouteAt
        secondChoice.kind secondChoice.index).getLastD (0, 0) with
    ⟨secondLocalX, secondLocalY⟩
  simp only [RetainedDirectSourceRouteChoice.sourceSegment,
    Cell.add, Cell.scale,
    firstData.originEq, secondData.originEq,
    Prod.mk.injEq] at finishesEqual ⊢
  norm_num [planarMacroScale] at firstBounds secondBounds finishesEqual ⊢
  omega

/-- A shared canonical target packages all global facts required by the
finite same-target direct-source atlas. -/
theorem retainedFinalDirectSourceRouteChoices_sharedTargetData
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (firstChoice secondChoice : RetainedDirectSourceRouteChoice)
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
    (firstChoiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula firstClauseIndex firstLiteralIndex =
        some firstChoice)
    (secondChoiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula secondClauseIndex secondLiteralIndex =
        some secondChoice)
    (occurrencesDifferent :
      (firstClauseIndex, firstLiteralIndex) ≠
        (secondClauseIndex, secondLiteralIndex))
    (targetsEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          firstClause firstLiteral =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          secondClause secondLiteral) :
    let firstSlot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula firstLiteral firstClauseIndex firstLiteralIndex
    let secondSlot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula secondLiteral secondClauseIndex secondLiteralIndex
    firstLiteral.atom = secondLiteral.atom ∧
      firstChoice.sourceSegment.finish =
        secondChoice.sourceSegment.finish ∧
      firstChoice.origin = secondChoice.origin ∧
      firstChoice.AngularOrderCompatible
        secondChoice firstSlot secondSlot := by
  let firstSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula firstLiteral firstClauseIndex firstLiteralIndex
  let secondSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula secondLiteral secondClauseIndex secondLiteralIndex
  have atomsEqual :=
    retainedFinalCanonicalLiteralPositions_eq_imp_atoms_eq
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
      firstClauseMember secondClauseMember
      firstLiteralMember secondLiteralMember targetsEqual
  have firstFinish :=
    retainedFinalDirectSourceRouteChoice_sourceSegment_finish
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstChoice
      firstClauseMember firstLiteralMember firstChoiceLookup
  have secondFinish :=
    retainedFinalDirectSourceRouteChoice_sourceSegment_finish
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty secondChoice
      secondClauseMember secondLiteralMember secondChoiceLookup
  have finishesEqual :
      firstChoice.sourceSegment.finish =
        secondChoice.sourceSegment.finish := by
    rw [firstFinish, secondFinish]
    exact targetsEqual
  have originsEqual :=
    retainedFinalDirectSourceRouteChoices_origins_eq_of_finishes_eq
      formula firstChoice secondChoice
      firstClauseIndex firstLiteralIndex
      secondClauseIndex secondLiteralIndex
      firstChoiceLookup secondChoiceLookup finishesEqual
  have angularOrder :=
    retainedFinalDirectSourceRouteChoices_angularOrderCompatible
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstChoice secondChoice
      firstClauseMember secondClauseMember
      firstLiteralMember secondLiteralMember
      firstChoiceLookup secondChoiceLookup
      atomsEqual occurrencesDifferent
  exact
    ⟨atomsEqual, finishesEqual, originsEqual,
      by simpa [firstSlot, secondSlot] using angularOrder⟩

end PeriodicEightOccurrenceSplit
end LeanTrominoes
