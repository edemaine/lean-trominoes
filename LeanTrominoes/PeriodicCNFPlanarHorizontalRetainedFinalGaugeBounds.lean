/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedVertexBounds

/-!
# Vertical bounds for the final retained canonical gauge

These small endpoint lemmas turn the existing strict fundamental-square
bounds into a zero vertical component of the canonical position gauge.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- A local final literal with zero vertical offset places its underlying
variable in the vertical fundamental interval, hence has zero vertical
canonical gauge. -/
theorem
    retainedOrderedFixedEightFinalGauge_vertical_eq_zero_of_local_literal
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {rawClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {rawClauseIndex : Nat}
    (rawClauseMember :
      (rawClause, rawClauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).clauses.zipIdx)
    {rawLiteral :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {rawLiteralIndex : Nat}
    (rawLiteralMember :
      (rawLiteral, rawLiteralIndex) ∈ rawClause.literals.zipIdx)
    (rawLiteralVertical : rawLiteral.offset.2 = 0)
    (notInherited :
      ∀ sourceAtom :
          ThreeOccurrenceVariable
            (WrappedPeriodicPlanarSATVariable Variable),
        rawLiteral.atom ≠ .inl (.inl sourceAtom)) :
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge
      source rawLiteral.atom).2 = 0 := by
  let rawPlacement :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
      source
  have literalInside :=
    retainedOrderedFixedEightComposedRawLocalLiteralPosition_inSquare
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty rawClauseMember rawLiteralMember notInherited
  have rawPositionVerticalEq :
      (rawPlacement.position rawLiteral.atom).2 =
        (rawPlacement.literalPosition rawLiteral).2 := by
    simp [PeriodicVariablePlacement.literalPosition,
      PeriodicVariablePlacement.translation, Cell.add, Cell.scale,
      rawLiteralVertical]
  have gaugeVertical :
      (rawPlacement.canonicalPositionGauge rawLiteral.atom).2 = 0 := by
    apply Int.ediv_eq_zero_of_lt
    · rw [rawPositionVerticalEq]
      exact le_of_lt literalInside.2.2.1
    · rw [rawPositionVerticalEq]
      exact literalInside.2.2.2
  simpa only [rawPlacement,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge] using
    gaugeVertical

/-- A fully inherited final variable is a uniform `72 × 72` refinement
of a clearance-source representative already strictly inside its period. -/
theorem
    retainedOrderedFixedEightFinalGauge_vertical_eq_zero_of_inherited
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceAtom :
      ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable))
    (sourceAtomMember :
      sourceAtom ∈
        (retainedFigureNineClearancePositionedFormula
          source).erase.variableOccurrences) :
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge
      source (.inl (.inl sourceAtom))).2 = 0 := by
  let rawPlacement :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
      source
  have sourceInside :=
    retainedFigureNineClearancePlacement_position_inSquare_of_mem
      source sourceAtom sourceAtomMember
  have rawPositionVertical :
      (rawPlacement.position (.inl (.inl sourceAtom))).2 =
        72 *
          ((retainedFigureNineClearancePlacement source).position
            sourceAtom).2 := by
    simp [rawPlacement,
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement,
      PlanarOneInThreeNoUnitsFigureNine.composedPlacement,
      PeriodicOneInThreeNoUnitsPositioned.placement,
      PeriodicOneInThreePositioned.placement,
      PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
      PlanarOneInThree.gadgetScale, Cell.scale]
    ring
  have rawPeriod :
      rawPlacement.period =
        72 * (retainedFigureNineClearancePlacement source).period := by
    simp [rawPlacement,
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement,
      PlanarOneInThreeNoUnitsFigureNine.composedPlacement,
      PeriodicOneInThreeNoUnitsPositioned.placement,
      PeriodicOneInThreePositioned.placement,
      PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
      PlanarOneInThree.gadgetScale]
    omega
  have gaugeVertical :
      (rawPlacement.canonicalPositionGauge
        (.inl (.inl sourceAtom))).2 = 0 := by
    apply Int.ediv_eq_zero_of_lt
    · rw [rawPositionVertical]
      nlinarith [sourceInside.2.2.1]
    · rw [rawPositionVertical, rawPeriod]
      norm_num
      exact sourceInside.2.2.2
  simpa only [rawPlacement,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge] using
    gaugeVertical

end PeriodicOrthocrossing
end LeanTrominoes
