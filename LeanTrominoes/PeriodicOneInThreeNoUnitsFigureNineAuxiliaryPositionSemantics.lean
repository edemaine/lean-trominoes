/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineAuxiliaryEndpoints
import Mathlib.Tactic.LinearCombination

/-! # Physical positions of composed auxiliary occurrences -/

namespace LeanTrominoes.PlanarOneInThreeNoUnitsFigureNine

/-- Both generations of auxiliary variables end at the selected local
endpoint; only fully inherited source variables require an external tail. -/
theorem normalizedLocalEndpoint_auxiliary
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (width : source.erase.WidthAtMost 3) (distinct : source.AllAtomsNodup)
    {clause : PositionedPeriodicClause (OneInThreeNoUnitVariable (OneInThreeVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember : (clause, clauseIndex) ∈
      (PeriodicOneInThreeNoUnitsPositioned.formula
        (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    {literal : PeriodicLiteral (OneInThreeNoUnitVariable (OneInThreeVariable Variable))}
    {literalIndex : Nat} (literalMember : (literal, literalIndex) ∈ clause.literals.zipIdx)
    (auxiliary : ∀ atom, literal.atom ≠ .inl (.inl atom)) :
    normalizedLocalEndpoint source placement clauseIndex literalIndex =
      PositionedPeriodicCNF.canonicalLiteralPosition (composedPlacement source placement) clause literal := by
  cases atomEq : literal.atom with
  | inr atom =>
      exact normalizedLocalEndpoint_unitAuxiliary
        source placement width distinct clauseMember literalMember atom atomEq
  | inl atom =>
      cases atom with
      | inl atom => exact (auxiliary atom atomEq).elim
      | inr atom =>
          exact normalizedLocalEndpoint_figureNineAuxiliary
            source placement width distinct clauseMember literalMember atom atomEq

/-- Undoing the common clause-anchor translation identifies an auxiliary's
physical occurrence with its instantiated template position. -/
theorem auxiliaryLiteralPosition_eq_instantiatedPosition
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (width : source.erase.WidthAtMost 3) (distinct : source.AllAtomsNodup)
    {metadata : ClauseMetadata Variable} {clauseIndex : Nat}
    (metadataLookup : (formulaClauseMetadata source)[clauseIndex]? = some metadata)
    (clauseMember : (metadata.clause, clauseIndex) ∈
      (PeriodicOneInThreeNoUnitsPositioned.formula
        (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    {literal : PeriodicLiteral (OneInThreeNoUnitVariable (OneInThreeVariable Variable))}
    {literalIndex : Nat} (literalMember : (literal, literalIndex) ∈ metadata.clause.literals.zipIdx)
    (auxiliary : ∀ atom, literal.atom ≠ .inl (.inl atom)) :
    (composedPlacement source placement).literalPosition literal =
      (instantiatedDrawing metadata.sourceClauseIndex metadata.figureNineClauseStart
        metadata.sourceClause).variablePosition literal.atom := by
  have endpoint := normalizedLocalEndpoint_auxiliary
    source placement width distinct clauseMember literalMember auxiliary
  simp only [normalizedLocalEndpoint, metadataLookup,
    List.mk_mem_zipIdx_iff_getElem?.mp literalMember] at endpoint
  apply Prod.ext
  · have equal := congrArg Prod.fst endpoint
    simp only [PositionedPeriodicCNF.canonicalLiteralPosition, PeriodicVariablePlacement.literalPosition,
      PeriodicVariablePlacement.translation, Cell.add, Cell.sub, Cell.scale] at equal ⊢
    linear_combination -equal
  · have equal := congrArg Prod.snd endpoint
    simp only [PositionedPeriodicCNF.canonicalLiteralPosition, PeriodicVariablePlacement.literalPosition,
      PeriodicVariablePlacement.translation, Cell.add, Cell.sub, Cell.scale] at equal ⊢
    linear_combination -equal

end LeanTrominoes.PlanarOneInThreeNoUnitsFigureNine
