/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineLocalRouteSeparation
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineSuffixCases

/-!
# Relative separation of retained Figure 9 auxiliary routes

Either generation of auxiliary has a singleton completed suffix, so its
complete spliced route is exactly the normalized local route.  Consequently
the retained local/local separation theorem already settles every relative
pair in which both literals are auxiliary.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

local instance orderedAuxiliaryRouteVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

/-- Two distinct relatively positioned non-inherited incidences have
separated complete retained routes. -/
theorem
    retainedOrderedFixedEightComposedRawIncidenceRoutes_relative_avoidEachOther_of_both_not_inherited
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {firstClause secondClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    (relativeTranslate : Cell)
    (generatedOccurrencesDifferent :
      ((firstClauseIndex, firstLiteralIndex), (0, 0)) ≠
        ((secondClauseIndex, secondLiteralIndex), relativeTranslate))
    (firstNotInherited :
      ∀ sourceAtom :
        ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable),
        firstLiteral.atom ≠ .inl (.inl sourceAtom))
    (secondNotInherited :
      ∀ sourceAtom :
        ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable),
        secondLiteral.atom ≠ .inl (.inl sourceAtom)) :
    RoutesAvoidEachOther
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty firstClauseIndex firstLiteralIndex)
      ((retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty secondClauseIndex secondLiteralIndex).map
        (Cell.add
          ((retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
            source).translation relativeTranslate))) := by
  rw [
    retainedOrderedFixedEightComposedRawIncidenceRoutes_eq_normalizedLocalRoutes_of_not_inherited
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstClauseMember firstLiteralMember
      firstNotInherited,
    retainedOrderedFixedEightComposedRawIncidenceRoutes_eq_normalizedLocalRoutes_of_not_inherited
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty secondClauseMember secondLiteralMember
      secondNotInherited]
  exact
    retainedOrderedFixedEightFigureNineNormalizedLocalRoutes_relative_avoidEachOther
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
      firstClauseMember secondClauseMember
      firstLiteralMember secondLiteralMember
      relativeTranslate generatedOccurrencesDifferent

end PeriodicOrthocrossing
end LeanTrominoes
