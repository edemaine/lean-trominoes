/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalDirectSourceSameTargetClassification

/-!
# Final direct-source separation at one shared target

For two direct incidences from different final source clauses, equality of
their canonical variable target activates the angular-order bridge and the
same-component atlas classification.  Each classified local certificate
then transports through the common physical component origin.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

private theorem localFinish_eq_of_sameOriginFinish_eq
    (origin : Cell)
    (firstKind secondKind : RetainedDirectClauseKind)
    (firstIndex :
      Fin (retainedDirectSourcePrefixChoices firstKind).length)
    (secondIndex :
      Fin (retainedDirectSourcePrefixChoices secondKind).length)
    (finishEqual :
      (⟨origin, firstKind, firstIndex⟩ :
          RetainedDirectSourceRouteChoice).sourceSegment.finish =
        (⟨origin, secondKind, secondIndex⟩ :
          RetainedDirectSourceRouteChoice).sourceSegment.finish) :
    (retainedDirectSourceLocalChoice
        firstKind firstIndex).sourceSegment.finish =
      (retainedDirectSourceLocalChoice
        secondKind secondIndex).sourceSegment.finish := by
  rcases origin with ⟨originX, originY⟩
  rcases
      (retainedDirectSourceLocalRouteAt
        firstKind firstIndex).getLastD (0, 0) with
    ⟨firstX, firstY⟩
  rcases
      (retainedDirectSourceLocalRouteAt
        secondKind secondIndex).getLastD (0, 0) with
    ⟨secondX, secondY⟩
  simp [RetainedDirectSourceRouteChoice.sourceSegment,
    retainedDirectSourceLocalChoice, Cell.add] at finishEqual ⊢
  exact Prod.ext finishEqual.1 finishEqual.2

/-- Complete Figure 7 routes chosen by different final source clauses and
converging on one canonical target are strictly separated. -/
theorem
    retainedFinalDirectSourceCrossClauseSameTarget_completeFigure7Routes_strictlyAvoid
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
    (clauseIndicesDifferent :
      firstClauseIndex ≠ secondClauseIndex)
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
    RoutesStrictlyAvoidEachOther
      (firstChoice.completeFigure7Route firstSlot)
      (secondChoice.completeFigure7Route secondSlot) := by
  let firstSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula firstLiteral firstClauseIndex firstLiteralIndex
  let secondSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula secondLiteral secondClauseIndex secondLiteralIndex
  have occurrencesDifferent :
      (firstClauseIndex, firstLiteralIndex) ≠
        (secondClauseIndex, secondLiteralIndex) := by
    intro equal
    exact clauseIndicesDifferent (congrArg Prod.fst equal)
  rcases
      retainedFinalDirectSourceRouteChoices_sharedTargetData
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstChoice secondChoice
        firstClauseMember secondClauseMember
        firstLiteralMember secondLiteralMember
        firstChoiceLookup secondChoiceLookup
        occurrencesDifferent targetsEqual with
    ⟨atomsEqual, finishesEqual, originsEqual, angularOrder⟩
  have atlasCase :=
    retainedFinalDirectSourceRouteChoices_sameTargetAtlasCase
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstChoice secondChoice
      firstClauseMember secondClauseMember
      firstLiteralMember secondLiteralMember
      firstChoiceLookup secondChoiceLookup
      clauseIndicesDifferent originsEqual
  cases atlasCase with
  | crossover
      origin firstClause secondClause firstIndex secondIndex
      clausesDifferent =>
      have localFinish :=
        localFinish_eq_of_sameOriginFinish_eq
          origin (.crossover firstClause) (.crossover secondClause)
          firstIndex secondIndex finishesEqual
      have localAngular :
          (retainedDirectSourceLocalChoice
              (.crossover firstClause) firstIndex)
            |>.AngularOrderCompatible
              (retainedDirectSourceLocalChoice
                (.crossover secondClause) secondIndex)
              firstSlot secondSlot := by
        simpa [RetainedDirectSourceRouteChoice.AngularOrderCompatible,
          retainedDirectSourceLocalChoice] using angularOrder
      exact
        retainedDirectSourceSameOriginCompleteFigure7Routes_strictlyAvoid_of_local
          origin (.crossover firstClause) (.crossover secondClause)
          firstIndex secondIndex firstSlot secondSlot
          (retainedDirectSourceCrossoverCrossClauseSameTarget_strictlyAvoid
            firstClause secondClause firstIndex secondIndex
            firstSlot secondSlot clausesDifferent
            localFinish localAngular)
  | duplicator
      origin firstArm secondArm firstClause secondClause
      firstIndex secondIndex branchesDifferent =>
      have localFinish :=
        localFinish_eq_of_sameOriginFinish_eq
          origin
          (.duplicator firstArm firstClause)
          (.duplicator secondArm secondClause)
          firstIndex secondIndex finishesEqual
      have localAngular :
          (retainedDirectSourceLocalChoice
              (.duplicator firstArm firstClause) firstIndex)
            |>.AngularOrderCompatible
              (retainedDirectSourceLocalChoice
                (.duplicator secondArm secondClause) secondIndex)
              firstSlot secondSlot := by
        simpa [RetainedDirectSourceRouteChoice.AngularOrderCompatible,
          retainedDirectSourceLocalChoice] using angularOrder
      exact
        retainedDirectSourceSameOriginCompleteFigure7Routes_strictlyAvoid_of_local
          origin
          (.duplicator firstArm firstClause)
          (.duplicator secondArm secondClause)
          firstIndex secondIndex firstSlot secondSlot
          (retainedDirectSourceDuplicatorCrossClauseSameTarget_strictlyAvoid
            firstArm secondArm firstClause secondClause
            firstIndex secondIndex firstSlot secondSlot
            branchesDifferent localFinish localAngular)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
