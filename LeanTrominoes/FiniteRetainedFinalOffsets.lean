/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteRetainedExactOneOffsets
import LeanTrominoes.FiniteRetainedFinalGaugeBounds
import LeanTrominoes.PeriodicCNFPlanarHorizontalRetainedFinalGaugeRawMembership

/-! # The final retained exact-one gauge preserves finite offsets -/
namespace LeanTrominoes.PositionedPeriodicCNF

theorem exists_indexedZeroOccurrence_of_mem_variableOccurrences
    {V : Type*} (source : PositionedPeriodicCNF V) (zero : FiniteCNF.ZeroOffsets source.erase)
    {atom : V} (member : atom∈source.erase.variableOccurrences) :
    ∃ clause clauseIndex literal literalIndex,
      (clause,clauseIndex)∈source.clauses.zipIdx ∧
      (literal,literalIndex)∈clause.literals.zipIdx ∧ literal.atom=atom ∧ literal.offset=(0,0) := by
  obtain ⟨clause,clauseIndex,literal,literalIndex,clauseMember,literalMember,atomEq⟩ :=
    exists_indexedOccurrence_of_mem_variableOccurrences source member
  refine ⟨clause,clauseIndex,literal,literalIndex,clauseMember,literalMember,atomEq,?_⟩
  exact zero clause.literals
    (List.mem_map.mpr ⟨clause,List.fst_mem_of_mem_zipIdx clauseMember,rfl⟩)
    literal (List.fst_mem_of_mem_zipIdx literalMember)
end LeanTrominoes.PositionedPeriodicCNF
namespace LeanTrominoes
namespace PeriodicOrthocrossing
/-- Every atom occurring after the final clause sort has an indexed raw
occurrence whose offset is zero. -/
theorem
    exists_zero_composedRaw_occurrence_of_finalClockwise_mem
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (graphLocal : source.incidenceGraph.IsLocal)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (zero : FiniteCNF.ZeroOffsets source)
    {atom :
      OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)}
    (atomMember :
      atom ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).erase.variableOccurrences) :
    ∃ rawClause rawClauseIndex rawLiteral rawLiteralIndex,
      (rawClause, rawClauseIndex) ∈
          (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
            source).clauses.zipIdx ∧
        (rawLiteral, rawLiteralIndex) ∈ rawClause.literals.zipIdx ∧
        rawLiteral.atom = atom ∧
        rawLiteral.offset = (0,0) := by
  let rawFormula :=
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
      source
  have rawMember : atom ∈ rawFormula.erase.variableOccurrences := by
    simpa only [rawFormula] using
      (finalClockwise_variableOccurrence_mem_composedRaw
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty atomMember)
  have rawZero : FiniteCNF.ZeroOffsets rawFormula.erase := by
    simpa only [rawFormula] using
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_erase_zeroOffsets
        wellFormed degree graphLocal zero)
  exact
    PositionedPeriodicCNF.exists_indexedZeroOccurrence_of_mem_variableOccurrences
      rawFormula rawZero rawMember

end PeriodicOrthocrossing
end LeanTrominoes

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- An occurring final atom is inherited with source membership, or has a
zero indexed raw occurrence and is not fully inherited. -/
theorem
    finalClockwise_mem_inherited_or_exists_zero_local_occurrence
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (graphLocal : source.incidenceGraph.IsLocal)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (zero : FiniteCNF.ZeroOffsets source)
    {atom :
      OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)}
    (atomMember :
      atom ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).erase.variableOccurrences) :
    (∃ sourceAtom :
        ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable),
      atom = .inl (.inl sourceAtom) ∧
        sourceAtom ∈
          (retainedFigureNineClearancePositionedFormula
            source).erase.variableOccurrences) ∨
      ∃ rawClause rawClauseIndex rawLiteral rawLiteralIndex,
        rawLiteral.atom = atom ∧
          (rawClause, rawClauseIndex) ∈
            (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
              source).clauses.zipIdx ∧
          (rawLiteral, rawLiteralIndex) ∈ rawClause.literals.zipIdx ∧
          rawLiteral.offset = (0,0) ∧
          ∀ sourceAtom :
              ThreeOccurrenceVariable
                (WrappedPeriodicPlanarSATVariable Variable),
            rawLiteral.atom ≠ .inl (.inl sourceAtom) := by
  rcases
      exists_zero_composedRaw_occurrence_of_finalClockwise_mem
        wellFormed degree graphLocal sourceLocal sourceWidth
        sourceOccurrences sourceClausesNonempty zero atomMember with
    ⟨rawClause, rawClauseIndex, rawLiteral, rawLiteralIndex,
      rawClauseMember, rawLiteralMember, rawLiteralAtomEq,
      rawLiteralZero⟩
  rcases composedLiteralVariable_inMacrocellOrbit
      (retainedFigureNineClearancePositionedFormula source)
      (retainedFigureNineClearancePlacement source)
      (by
        simpa only [
          retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula]
          using rawClauseMember)
      rawLiteralMember with
    ⟨_base, _address, sourceData, _orbit, _localPosition⟩
  generalize classifiedAtomEq : rawLiteral.atom = classifiedAtom at sourceData
  cases sourceData with
  | inherited sourceAtom sourceAtomMember =>
      exact Or.inl
        ⟨sourceAtom,
          rawLiteralAtomEq.symm.trans classifiedAtomEq,
          sourceAtomMember⟩
  | figureNineAuxiliary =>
      exact Or.inr ⟨rawClause, rawClauseIndex, rawLiteral,
        rawLiteralIndex, rawLiteralAtomEq, rawClauseMember,
        rawLiteralMember, rawLiteralZero, by
          intro sourceAtom inheritedEq
          rw [inheritedEq] at classifiedAtomEq
          simp at classifiedAtomEq⟩
  | unitEliminationAuxiliary =>
      exact Or.inr ⟨rawClause, rawClauseIndex, rawLiteral,
        rawLiteralIndex, rawLiteralAtomEq, rawClauseMember,
        rawLiteralMember, rawLiteralZero, by
          intro sourceAtom inheritedEq
          rw [inheritedEq] at classifiedAtomEq
          simp at classifiedAtomEq⟩

end PeriodicOrthocrossing
end LeanTrominoes

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- The final canonical position gauge is zero on every variable
occurring before the gauge is applied. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge_eq_zero_of_mem
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (graphLocal : source.incidenceGraph.IsLocal)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (zero : FiniteCNF.ZeroOffsets source)
    {atom :
      OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)}
    (atomMember :
      atom ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).erase.variableOccurrences) :
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge
      source atom = (0,0) := by
  rcases
      finalClockwise_mem_inherited_or_exists_zero_local_occurrence
        wellFormed degree graphLocal sourceLocal sourceWidth
        sourceOccurrences sourceClausesNonempty zero atomMember with
    ⟨sourceAtom, rfl, sourceAtomMember⟩ |
      ⟨rawClause, rawClauseIndex, rawLiteral, rawLiteralIndex,
        rfl, rawClauseMember, rawLiteralMember, rawLiteralZero,
        notInherited⟩
  · exact
      retainedOrderedFixedEightFinalGauge_eq_zero_of_inherited
        source sourceAtom sourceAtomMember
  · exact
      retainedOrderedFixedEightFinalGauge_eq_zero_of_local_literal
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty rawClauseMember rawLiteralMember
        rawLiteralZero notInherited

end PeriodicOrthocrossing
end LeanTrominoes

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Applying the final canonical variable gauge preserves the concrete
retained exact-one endpoint's zero offsets. -/
theorem
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_erase_zeroOffsets
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (graphLocal : source.incidenceGraph.IsLocal)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (zero : FiniteCNF.ZeroOffsets source) :
    FiniteCNF.ZeroOffsets (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).erase := by
  rw [
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula,
    PositionedPeriodicCNF.erase_variableGauge]
  apply FiniteCNF.zeroOffsets_variableGauge
  · exact
      retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula_erase_zeroOffsets
        wellFormed degree graphLocal sourceLocal sourceWidth
        sourceOccurrences sourceClausesNonempty zero
  · intro atom atomMember
    exact
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge_eq_zero_of_mem
        wellFormed degree graphLocal sourceLocal sourceWidth
        sourceOccurrences sourceClausesNonempty zero atomMember

end PeriodicOrthocrossing
end LeanTrominoes
