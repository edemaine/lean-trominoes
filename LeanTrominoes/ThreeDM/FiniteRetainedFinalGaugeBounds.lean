/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedVertexBounds

/-! # Fundamental-square bounds give zero finite canonical gauges -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- A local final literal with zero offset places its underlying
variable in the fundamental square, hence has zero
canonical gauge. -/
theorem
    retainedOrderedFixedEightFinalGauge_eq_zero_of_local_literal
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
    (rawLiteralZero : rawLiteral.offset = (0,0))
    (notInherited :
      ∀ sourceAtom :
          ThreeOccurrenceVariable
            (WrappedPeriodicPlanarSATVariable Variable),
        rawLiteral.atom ≠ .inl (.inl sourceAtom)) :
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge
      source rawLiteral.atom = (0,0) := by
  let rawPlacement :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
      source
  have literalInside :=
    retainedOrderedFixedEightComposedRawLocalLiteralPosition_inSquare
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty rawClauseMember rawLiteralMember notInherited
  have rawPositionEq : rawPlacement.position rawLiteral.atom = rawPlacement.literalPosition rawLiteral := by
    simp [PeriodicVariablePlacement.literalPosition,
      PeriodicVariablePlacement.translation, Cell.add, Cell.scale,rawLiteralZero]
  have gaugeZero : rawPlacement.canonicalPositionGauge rawLiteral.atom=(0,0) := by
    apply Prod.ext
    · apply Int.ediv_eq_zero_of_lt
      · rw [rawPositionEq]; exact le_of_lt literalInside.1
      · rw [rawPositionEq]; exact literalInside.2.1
    · apply Int.ediv_eq_zero_of_lt
      · rw [rawPositionEq]; exact le_of_lt literalInside.2.2.1
      · rw [rawPositionEq]; exact literalInside.2.2.2
  simpa only [rawPlacement,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge] using gaugeZero

/-- A fully inherited final variable is a uniform `72 × 72` refinement
of a clearance-source representative already strictly inside its period. -/
theorem
    retainedOrderedFixedEightFinalGauge_eq_zero_of_inherited
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceAtom :
      ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable))
    (sourceAtomMember :
      sourceAtom ∈
        (retainedFigureNineClearancePositionedFormula
          source).erase.variableOccurrences) :
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge
      source (.inl (.inl sourceAtom)) = (0,0) := by
  let rawPlacement :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
      source
  have sourceInside :=
    retainedFigureNineClearancePlacement_position_inSquare_of_mem
      source sourceAtom sourceAtomMember
  have rawPositionEq : rawPlacement.position (.inl (.inl sourceAtom)) =
      Cell.scale 72 ((retainedFigureNineClearancePlacement source).position sourceAtom) := by
    simp [rawPlacement,
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement,
      PlanarOneInThreeNoUnitsFigureNine.composedPlacement,
      PeriodicOneInThreeNoUnitsPositioned.placement,
      PeriodicOneInThreePositioned.placement,
      PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
      PlanarOneInThree.gadgetScale, Cell.scale]
    constructor <;> ring
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
  have gaugeZero : rawPlacement.canonicalPositionGauge (.inl (.inl sourceAtom))=(0,0) := by
    apply Prod.ext
    · apply Int.ediv_eq_zero_of_lt
      · rw [rawPositionEq]; change 0≤72*_; nlinarith [sourceInside.1]
      · rw [rawPositionEq,rawPeriod]; norm_num only [Cell.scale,Nat.cast_mul,Nat.cast_ofNat]; nlinarith [sourceInside.2.1]
    · apply Int.ediv_eq_zero_of_lt
      · rw [rawPositionEq]; change 0≤72*_; nlinarith [sourceInside.2.2.1]
      · rw [rawPositionEq,rawPeriod]; norm_num only [Cell.scale,Nat.cast_mul,Nat.cast_ofNat]; nlinarith [sourceInside.2.2.2]
  simpa only [rawPlacement,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge] using gaugeZero

end PeriodicOrthocrossing
end LeanTrominoes
