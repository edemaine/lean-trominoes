/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarHorizontalRetainedFinalGaugeBounds
import LeanTrominoes.PeriodicCNFPlanarHorizontalRetainedFinalGaugeRawMembership

/-!
# Provenance of a selected horizontal final occurrence

The composed Figure 9 occurrence theorem classifies the selected raw literal
as either fully inherited from the clearance source or local to one of the
two exact-one replacement layers.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- An occurring final atom is inherited with source membership, or has a
horizontal indexed raw occurrence and is not fully inherited. -/
theorem
    finalClockwise_mem_inherited_or_exists_horizontal_local_occurrence
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
    (horizontal : source.incidenceGraph.HasZeroVerticalOffsets)
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
          rawLiteral.offset.2 = 0 ∧
          ∀ sourceAtom :
              ThreeOccurrenceVariable
                (WrappedPeriodicPlanarSATVariable Variable),
            rawLiteral.atom ≠ .inl (.inl sourceAtom) := by
  rcases
      exists_horizontal_composedRaw_occurrence_of_finalClockwise_mem
        wellFormed degree graphLocal sourceLocal sourceWidth
        sourceOccurrences sourceClausesNonempty horizontal atomMember with
    ⟨rawClause, rawClauseIndex, rawLiteral, rawLiteralIndex,
      rawClauseMember, rawLiteralMember, rawLiteralAtomEq,
      rawLiteralVertical⟩
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
        rawLiteralMember, rawLiteralVertical, by
          intro sourceAtom inheritedEq
          rw [inheritedEq] at classifiedAtomEq
          simp at classifiedAtomEq⟩
  | unitEliminationAuxiliary =>
      exact Or.inr ⟨rawClause, rawClauseIndex, rawLiteral,
        rawLiteralIndex, rawLiteralAtomEq, rawClauseMember,
        rawLiteralMember, rawLiteralVertical, by
          intro sourceAtom inheritedEq
          rw [inheritedEq] at classifiedAtomEq
          simp at classifiedAtomEq⟩

end PeriodicOrthocrossing
end LeanTrominoes
