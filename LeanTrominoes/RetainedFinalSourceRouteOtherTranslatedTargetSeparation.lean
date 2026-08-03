import LeanTrominoes.RetainedFinalSourceRouteOtherTranslatedVertexSeparation

/-!
# Final source routes avoid translated incidence targets

The periodic vertex lemmas are phrased around an atom's fundamental-square
position.  Occurrence fans are centered instead at canonical literal
positions, which include the literal's clause-relative period offset.  This
file absorbs that offset and exposes the two source-prefix/final-segment
interfaces needed by relative occurrence-route separation.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- A canonical literal center translated by an external period shift is
the atom position translated by the sum of its incidence offset and that
external shift. -/
theorem canonicalLiteralPosition_add_translation_eq_atomPosition_translation
    {Variable : Type*}
    (placement : PeriodicVariablePlacement Variable)
    (clause : PositionedPeriodicClause Variable)
    (literal : PeriodicLiteral Variable)
    (relativeTranslate : Cell) :
    Cell.add
        (PositionedPeriodicCNF.canonicalLiteralPosition
          placement clause literal)
        (placement.translation relativeTranslate) =
      Cell.add (placement.position literal.atom)
        (placement.translation
          (Cell.add
            (incidenceRelativeOffset clause literal)
            relativeTranslate)) := by
  rcases positionEq : placement.position literal.atom with
    ⟨positionX, positionY⟩
  rcases literalOffsetEq : literal.offset with
    ⟨literalX, literalY⟩
  rcases anchorEq : PeriodicCNF.clauseAnchor clause.literals with
    ⟨anchorX, anchorY⟩
  rcases relativeTranslate with ⟨relativeX, relativeY⟩
  simp [PositionedPeriodicCNF.canonicalLiteralPosition,
    incidenceRelativeOffset, PeriodicVariablePlacement.translation,
    positionEq, literalOffsetEq, anchorEq,
    Cell.add, Cell.sub, Cell.scale]
  constructor <;> ring

/-- A final source prefix avoids the periodically translated canonical
target center of every other incidence. -/
theorem
    finalCoordinatedSourceRoutePrefix_avoids_translatedCanonicalLiteralPosition
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {sourceClause targetClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {sourceClauseIndex targetClauseIndex : Nat}
    (sourceClauseMember :
      (sourceClause, sourceClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (targetClauseMember :
      (targetClause, targetClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {sourceLiteral targetLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {sourceLiteralIndex targetLiteralIndex : Nat}
    (sourceLiteralMember :
      (sourceLiteral, sourceLiteralIndex) ∈
        sourceClause.literals.zipIdx)
    (targetLiteralMember :
      (targetLiteral, targetLiteralIndex) ∈
        targetClause.literals.zipIdx)
    (relativeTranslate : Cell)
    (centersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          sourceClause sourceLiteral ≠
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            targetClause targetLiteral)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate)) :
    let target :=
      Cell.add
        (PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          targetClause targetLiteral)
        ((finalCoordinatedPlacement formula).translation
          relativeTranslate)
    (∀ point ∈
        (finalCoordinatedSourceRoutes
          formula sourceClauseIndex sourceLiteralIndex).dropLast,
        point ≠ target) ∧
      ∀ segment ∈
        gridPolylineSegments
          (finalCoordinatedSourceRoutes
            formula sourceClauseIndex sourceLiteralIndex).dropLast,
        segment.IsAxisAligned → ¬segment.Contains target := by
  dsimp only
  have targetTagged :
      (targetLiteral, targetClauseIndex, targetLiteralIndex) ∈
        taggedLiterals (finalCoordinatedSource formula).erase :=
    taggedLiteral_mem_of_positioned_members
      (finalCoordinatedSource formula)
      targetClauseMember targetLiteralMember
  have targetAtomMember :
      targetLiteral.atom ∈
        sourceVariables (finalCoordinatedSource formula).erase :=
    sourceVariables_mem
      (finalCoordinatedSource formula).erase targetTagged
  let combinedTranslate :=
    Cell.add
      (incidenceRelativeOffset targetClause targetLiteral)
      relativeTranslate
  have targetEq :
      Cell.add
          ((finalCoordinatedPlacement formula).position
            targetLiteral.atom)
          ((finalCoordinatedPlacement formula).translation
            combinedTranslate) =
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            targetClause targetLiteral)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate) := by
    exact
      (canonicalLiteralPosition_add_translation_eq_atomPosition_translation
        (finalCoordinatedPlacement formula)
        targetClause targetLiteral relativeTranslate).symm
  have separated :=
    finalCoordinatedSourceRoutePrefix_avoids_translatedSourceVariablePosition
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty sourceClauseMember sourceLiteralMember
      targetLiteral.atom targetAtomMember combinedTranslate
      (by simpa [targetEq] using centersDifferent)
  simpa [combinedTranslate, targetEq] using separated

/-- An axis-aligned discarded final segment avoids the periodically
translated canonical target center of every other incidence. -/
theorem
    finalCoordinatedSourceRoute_finalSegment_avoids_translatedCanonicalLiteralPosition_of_axisAligned
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {sourceClause targetClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {sourceClauseIndex targetClauseIndex : Nat}
    (sourceClauseMember :
      (sourceClause, sourceClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (targetClauseMember :
      (targetClause, targetClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {sourceLiteral targetLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {sourceLiteralIndex targetLiteralIndex : Nat}
    (sourceLiteralMember :
      (sourceLiteral, sourceLiteralIndex) ∈
        sourceClause.literals.zipIdx)
    (targetLiteralMember :
      (targetLiteral, targetLiteralIndex) ∈
        targetClause.literals.zipIdx)
    (sourceFinalAligned :
      let route :=
        finalCoordinatedSourceRoutes
          formula sourceClauseIndex sourceLiteralIndex
      (⟨polylineLastEntrance route,
          route.getLastD (0, 0)⟩ : GridSegment).IsAxisAligned)
    (relativeTranslate : Cell)
    (centersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          sourceClause sourceLiteral ≠
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            targetClause targetLiteral)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate)) :
    let route :=
      finalCoordinatedSourceRoutes
        formula sourceClauseIndex sourceLiteralIndex
    let finalSegment : GridSegment :=
      ⟨polylineLastEntrance route, route.getLastD (0, 0)⟩
    let target :=
      Cell.add
        (PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          targetClause targetLiteral)
        ((finalCoordinatedPlacement formula).translation
          relativeTranslate)
    finalSegment.IsAxisAligned ∧ ¬finalSegment.Contains target := by
  dsimp only
  have targetTagged :
      (targetLiteral, targetClauseIndex, targetLiteralIndex) ∈
        taggedLiterals (finalCoordinatedSource formula).erase :=
    taggedLiteral_mem_of_positioned_members
      (finalCoordinatedSource formula)
      targetClauseMember targetLiteralMember
  have targetAtomMember :
      targetLiteral.atom ∈
        sourceVariables (finalCoordinatedSource formula).erase :=
    sourceVariables_mem
      (finalCoordinatedSource formula).erase targetTagged
  let combinedTranslate :=
    Cell.add
      (incidenceRelativeOffset targetClause targetLiteral)
      relativeTranslate
  have targetEq :
      Cell.add
          ((finalCoordinatedPlacement formula).position
            targetLiteral.atom)
          ((finalCoordinatedPlacement formula).translation
            combinedTranslate) =
        Cell.add
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            targetClause targetLiteral)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate) := by
    exact
      (canonicalLiteralPosition_add_translation_eq_atomPosition_translation
        (finalCoordinatedPlacement formula)
        targetClause targetLiteral relativeTranslate).symm
  have separated :=
    finalCoordinatedSourceRoute_finalSegment_avoids_translatedSourceVariablePosition_of_axisAligned
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty sourceClauseMember sourceLiteralMember
      sourceFinalAligned targetLiteral.atom targetAtomMember
      combinedTranslate
      (by simpa [targetEq] using centersDifferent)
  simpa [combinedTranslate, targetEq] using separated

end PeriodicOrthocrossing
end LeanTrominoes
