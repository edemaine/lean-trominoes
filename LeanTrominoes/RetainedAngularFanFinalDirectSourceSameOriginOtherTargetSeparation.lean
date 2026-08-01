import LeanTrominoes.RetainedAngularFanFinalDirectSourceSameTargetSeparation

/-!
# Final direct-source separation from one component to different targets

For two direct incidences from different final source clauses, a shared
physical component origin activates the atlas classification.  Distinct
canonical targets give distinct local finishes, and the crossover and
duplicator certificates then separate the complete Figure 7 routes.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

private theorem localFinish_ne_of_sameOriginFinish_ne
    (origin : Cell)
    (firstKind secondKind : RetainedDirectClauseKind)
    (firstIndex :
      Fin (retainedDirectSourcePrefixChoices firstKind).length)
    (secondIndex :
      Fin (retainedDirectSourcePrefixChoices secondKind).length)
    (finishDifferent :
      (⟨origin, firstKind, firstIndex⟩ :
          RetainedDirectSourceRouteChoice).sourceSegment.finish ≠
        (⟨origin, secondKind, secondIndex⟩ :
          RetainedDirectSourceRouteChoice).sourceSegment.finish) :
    (retainedDirectSourceLocalChoice
        firstKind firstIndex).sourceSegment.finish ≠
      (retainedDirectSourceLocalChoice
        secondKind secondIndex).sourceSegment.finish := by
  intro localEqual
  apply finishDifferent
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
    retainedDirectSourceLocalChoice, Cell.add] at localEqual ⊢
  exact
    ⟨congrArg Prod.fst localEqual,
      congrArg Prod.snd localEqual⟩

/-- Complete local crossover routes from different clause terminals to
different targets are strictly separated. -/
theorem
    retainedDirectSourceCrossoverCrossClauseOtherTarget_strictlyAvoid
    (firstClauseIndex secondClauseIndex : Fin 26)
    (firstIndex :
      Fin
        (retainedDirectSourcePrefixChoices
          (.crossover firstClauseIndex)).length)
    (secondIndex :
      Fin
        (retainedDirectSourcePrefixChoices
          (.crossover secondClauseIndex)).length)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (clausesDifferent : firstClauseIndex ≠ secondClauseIndex)
    (finishDifferent :
      (retainedDirectSourceLocalChoice
        (.crossover firstClauseIndex) firstIndex).sourceSegment.finish ≠
      (retainedDirectSourceLocalChoice
        (.crossover secondClauseIndex) secondIndex).sourceSegment.finish) :
    RoutesStrictlyAvoidEachOther
      ((retainedDirectSourceLocalChoice
        (.crossover firstClauseIndex) firstIndex)
          |>.completeFigure7Route firstSlot)
      ((retainedDirectSourceLocalChoice
        (.crossover secondClauseIndex) secondIndex)
          |>.completeFigure7Route secondSlot) := by
  let first :=
    retainedDirectSourceLocalChoice
      (.crossover firstClauseIndex) firstIndex
  let second :=
    retainedDirectSourceLocalChoice
      (.crossover secondClauseIndex) secondIndex
  by_cases rectanglesSeparated :
      first.SourceRectanglesSeparated second
  · exact
      first.completeFigure7Routes_strictlyAvoid_of_sourceRectanglesSeparated
        second firstSlot secondSlot rectanglesSeparated
  · exact
      retainedDirectSourceLocalCompleteFigure7Routes_strictlyAvoid_of_crossClausePieces
        (.crossover firstClauseIndex) (.crossover secondClauseIndex)
        firstIndex secondIndex firstSlot secondSlot
        (retainedDirectSourceCrossoverCrossClauseOtherTarget_piecesLinearlySeparated
          firstClauseIndex secondClauseIndex firstIndex secondIndex
          firstSlot secondSlot clausesDifferent finishDifferent
          rectanglesSeparated)

/-- Complete local duplicator routes from different clause branches to
different targets are strictly separated. -/
theorem
    retainedDirectSourceDuplicatorCrossClauseOtherTarget_strictlyAvoid
    (firstArm secondArm : PlanarThreeSAT.DuplicatorArm)
    (firstClauseIndex secondClauseIndex : Fin 2)
    (firstIndex :
      Fin
        (retainedDirectSourcePrefixChoices
          (.duplicator firstArm firstClauseIndex)).length)
    (secondIndex :
      Fin
        (retainedDirectSourcePrefixChoices
          (.duplicator secondArm secondClauseIndex)).length)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (branchesDifferent :
      (firstArm, firstClauseIndex) ≠
        (secondArm, secondClauseIndex))
    (finishDifferent :
      (retainedDirectSourceLocalChoice
        (.duplicator firstArm firstClauseIndex)
          firstIndex).sourceSegment.finish ≠
      (retainedDirectSourceLocalChoice
        (.duplicator secondArm secondClauseIndex)
          secondIndex).sourceSegment.finish) :
    RoutesStrictlyAvoidEachOther
      ((retainedDirectSourceLocalChoice
        (.duplicator firstArm firstClauseIndex) firstIndex)
          |>.completeFigure7Route firstSlot)
      ((retainedDirectSourceLocalChoice
        (.duplicator secondArm secondClauseIndex) secondIndex)
          |>.completeFigure7Route secondSlot) := by
  let first :=
    retainedDirectSourceLocalChoice
      (.duplicator firstArm firstClauseIndex) firstIndex
  let second :=
    retainedDirectSourceLocalChoice
      (.duplicator secondArm secondClauseIndex) secondIndex
  by_cases rectanglesSeparated :
      first.SourceRectanglesSeparated second
  · exact
      first.completeFigure7Routes_strictlyAvoid_of_sourceRectanglesSeparated
        second firstSlot secondSlot rectanglesSeparated
  · exact
      retainedDirectSourceLocalCompleteFigure7Routes_strictlyAvoid_of_crossClausePieces
        (.duplicator firstArm firstClauseIndex)
        (.duplicator secondArm secondClauseIndex)
        firstIndex secondIndex firstSlot secondSlot
        (retainedDirectSourceDuplicatorCrossClauseOtherTarget_piecesLinearlySeparated
          firstArm secondArm firstClauseIndex secondClauseIndex
          firstIndex secondIndex firstSlot secondSlot
          branchesDifferent finishDifferent rectanglesSeparated)

/-- Complete Figure 7 routes chosen by different final source clauses from
one physical component to different canonical targets are strictly
separated. -/
theorem
    retainedFinalDirectSourceCrossClauseSameOriginOtherTarget_completeFigure7Routes_strictlyAvoid
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
    (targetsDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          firstClause firstLiteral ≠
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          secondClause secondLiteral)
    (originsEqual :
      firstChoice.origin = secondChoice.origin) :
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
  have finishesDifferent :
      firstChoice.sourceSegment.finish ≠
        secondChoice.sourceSegment.finish := by
    rw [firstFinish, secondFinish]
    exact targetsDifferent
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
        localFinish_ne_of_sameOriginFinish_ne
          origin (.crossover firstClause) (.crossover secondClause)
          firstIndex secondIndex finishesDifferent
      exact
        retainedDirectSourceSameOriginCompleteFigure7Routes_strictlyAvoid_of_local
          origin (.crossover firstClause) (.crossover secondClause)
          firstIndex secondIndex firstSlot secondSlot
          (retainedDirectSourceCrossoverCrossClauseOtherTarget_strictlyAvoid
            firstClause secondClause firstIndex secondIndex
            firstSlot secondSlot clausesDifferent localFinish)
  | duplicator
      origin firstArm secondArm firstClause secondClause
      firstIndex secondIndex branchesDifferent =>
      have localFinish :=
        localFinish_ne_of_sameOriginFinish_ne
          origin
          (.duplicator firstArm firstClause)
          (.duplicator secondArm secondClause)
          firstIndex secondIndex finishesDifferent
      exact
        retainedDirectSourceSameOriginCompleteFigure7Routes_strictlyAvoid_of_local
          origin
          (.duplicator firstArm firstClause)
          (.duplicator secondArm secondClause)
          firstIndex secondIndex firstSlot secondSlot
          (retainedDirectSourceDuplicatorCrossClauseOtherTarget_strictlyAvoid
            firstArm secondArm firstClause secondClause
            firstIndex secondIndex firstSlot secondSlot
            branchesDifferent localFinish)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
