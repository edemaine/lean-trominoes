/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalAtomValueRowCodes
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalAuxiliaryAtomHorizontalSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceInheritedSourceLiterals
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineRingAtomMembership

/-! # Actual inherited atoms at every global occurrence index -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open PeriodicCNF.FormulaShapeFigureNineRoutePrefix
open PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail
open PeriodicCNF.FormulaShapeRetainedFigureNineDirection
open PeriodicCNF.ClauseProfilePolarityRouteOperation
open HorizontalRoutedRouteHeader PeriodicOrthocrossing PlanarOneInThreeNoUnitsFigureNine

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance inheritedHorizontalStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

local instance inheritedHorizontalVariableDecidableEq : DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- An inherited record's numeric code and source witness select the
same actual ring atom. The lookup retains its original global output index. -/
theorem directSourceFinalInheritedAtom_witness
    (symbols : List encoding.Γ) (index : Nat) (occurrence : SourceOccurrence)
    (witness : OccurrenceWitness (directSourceFormula decider symbols) occurrence)
    (occurrenceLookup : (directSourceFinalOccurrences decider symbols)[index]? = some occurrence)
    (original : ¬ sourceOccurrenceIsFresh occurrence) (slot : SourceLiteralSlot)
    (selected : sourceSlot? (prefixAtom occurrence.header.figurePrefix) = some slot) :
    ∃ atom : ThreeOccurrenceVariable (WrappedPeriodicPlanarSATVariable Variable),
      instantiatedVariableMap witness.metadata.sourceClauseIndex witness.metadata.figureNineClauseStart
        witness.metadata.sourceClause (prefixAtom occurrence.header.figurePrefix) = .inl (.inl atom) ∧
      (directSourceFinalInheritedRingAtomCodes decider symbols).getD index 0 =
        directSourceFinalRingVariableCode decider symbols atom ∧
      atom ∈ (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        (directSourceFormula decider symbols)).erase.variableOccurrences := by
  have querySelected := selected
  rw [prefixAtom_eq_localQuery] at querySelected
  obtain ⟨literal, literalLookup, atomEq⟩ := witness.inheritedSourceLiteral slot querySelected
  have scope := sourceOccurrenceScope_of_inherited occurrence original slot selected
  have valueEq := sourceOccurrenceCopiedValue_eq_literal
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
      (directSourceFormula decider symbols)).clauses
    (directSourceFinalRingVariableCode decider symbols) occurrence witness.refinedClause literal slot
    witness.sourceLookup scope literalLookup
  have codeLookup : (directSourceFinalInheritedRingAtomCodes decider symbols)[index]? =
      some (directSourceFinalRingVariableCode decider symbols literal.atom) := by
    rw [directSourceFinalInheritedRingAtomCodes_eq_occurrence_rows, List.getElem?_map,
      occurrenceLookup, Option.map_some,
      sourceOccurrenceAtomValue_eq_copiedValue_of_inherited _ occurrence slot scope,
      List.map_map]
    simp only [Function.comp_def]
    rw [directSourceFinalAtomValueBlocks_literals, valueEq]
  refine ⟨literal.atom, ?_, ?_, ?_⟩
  · simpa only [prefixAtom_eq_localQuery] using atomEq
  · simp only [List.getD_eq_getElem?_getD, codeLookup, Option.getD_some]
  · simp only [PeriodicCNF.variableOccurrences, PositionedPeriodicCNF.erase, List.flatMap_map]
    exact List.mem_flatMap.mpr ⟨witness.refinedClause,
      List.mem_iff_getElem?.mpr ⟨occurrence.parentClauseIndex, witness.sourceLookup⟩,
      List.mem_map.mpr ⟨literal, List.mem_iff_getElem?.mpr ⟨_, literalLookup⟩, rfl⟩⟩

/-- The complete numeric identity and the actual horizontal atom at an
inherited index are obtained from that same represented ring atom. -/
theorem directSourceFinalInheritedAtom_eq_horizontal
    (symbols : List encoding.Γ) (index : Nat) (occurrence : SourceOccurrence)
    (occurrenceLookup : (directSourceFinalOccurrences decider symbols)[index]? = some occurrence)
    (original : ¬ sourceOccurrenceIsFresh occurrence) (slot : SourceLiteralSlot)
    (selected : sourceSlot? (prefixAtom occurrence.header.figurePrefix) = some slot)
    (horizontalAtom : RoutedVariable)
    (atomLookup : (horizontalRoutedFormulaComputed
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences[index]? = some horizontalAtom) :
    ∃ atom : ThreeOccurrenceVariable (WrappedPeriodicPlanarSATVariable Variable),
      horizontalAtom = .inl (.inl (.inl atom)) ∧
      (directSourceFinalAtomIdentityCodes decider symbols).getD index 0 =
        directSourceFinalRingVariableCode decider symbols atom * 2 ∧
      atom ∈ (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        (directSourceFormula decider symbols)).erase.variableOccurrences := by
  obtain ⟨indexLt, rfl⟩ := List.getElem?_eq_some_iff.mp occurrenceLookup
  let witness := directSourceFinalOccurrenceWitness decider symbols index indexLt
  obtain ⟨atom, atomEq, codeEq, member⟩ :=
    directSourceFinalInheritedAtom_witness decider symbols index _ witness (List.getElem?_eq_getElem indexLt) original slot selected
  have originalEq : directSourceFinalOriginalAtom decider symbols index indexLt = .inl (.inl atom) := by
    simpa only [directSourceFinalOriginalAtom, witness] using atomEq
  refine ⟨atom, ?_, ?_, member⟩
  · rw [directSourceFinalOriginalAtom_eq_horizontal decider symbols index indexLt original horizontalAtom atomLookup, originalEq]
  · rw [directSourceFinalAtomIdentityCodes_getD_of_inherited decider symbols index indexLt slot
      (sourceOccurrenceScope_of_inherited _ original slot selected), directSourceFinalEvenInheritedAtomCodes_eq_map]
    have codeLt : index < (directSourceFinalInheritedRingAtomCodes decider symbols).length := by
      rw [directSourceFinalInheritedRingAtomCodes_length, ← directSourceFinalOccurrences_length_eq_compiled]
      exact indexLt
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using codeLt), List.getElem_map]
    simpa only [List.getD_eq_getElem _ _ codeLt] using congrArg (fun code => code * 2) codeEq

/-- Two inherited incidences have equal complete numeric identities
exactly when their actual horizontal atoms are equal. -/
theorem directSourceFinalAtomIdentityCodes_inherited_eq_iff_horizontalAtoms
    (symbols : List encoding.Γ) (firstIndex secondIndex : Nat)
    (first second : SourceOccurrence)
    (firstOccurrenceLookup : (directSourceFinalOccurrences decider symbols)[firstIndex]? = some first)
    (secondOccurrenceLookup : (directSourceFinalOccurrences decider symbols)[secondIndex]? = some second)
    (firstOriginal : ¬ sourceOccurrenceIsFresh first) (secondOriginal : ¬ sourceOccurrenceIsFresh second)
    (firstSlot secondSlot : SourceLiteralSlot)
    (firstSelected : sourceSlot? (prefixAtom first.header.figurePrefix) = some firstSlot)
    (secondSelected : sourceSlot? (prefixAtom second.header.figurePrefix) = some secondSlot)
    (firstAtom secondAtom : RoutedVariable)
    (firstAtomLookup : (horizontalRoutedFormulaComputed
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences[firstIndex]? = some firstAtom)
    (secondAtomLookup : (horizontalRoutedFormulaComputed
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences[secondIndex]? = some secondAtom) :
    (directSourceFinalAtomIdentityCodes decider symbols).getD firstIndex 0 =
        (directSourceFinalAtomIdentityCodes decider symbols).getD secondIndex 0 ↔
      firstAtom = secondAtom := by
  obtain ⟨firstRing, firstAtomEq, firstCodeEq, firstMember⟩ :=
    directSourceFinalInheritedAtom_eq_horizontal decider symbols firstIndex first firstOccurrenceLookup
      firstOriginal firstSlot firstSelected firstAtom firstAtomLookup
  obtain ⟨secondRing, secondAtomEq, secondCodeEq, secondMember⟩ :=
    directSourceFinalInheritedAtom_eq_horizontal decider symbols secondIndex second secondOccurrenceLookup
      secondOriginal secondSlot secondSelected secondAtom secondAtomLookup
  rw [firstCodeEq, secondCodeEq, firstAtomEq, secondAtomEq]
  simp only [Sum.inl.injEq]
  have numeric : directSourceFinalRingVariableCode decider symbols firstRing * 2 =
        directSourceFinalRingVariableCode decider symbols secondRing * 2 ↔
      directSourceFinalRingVariableCode decider symbols firstRing =
        directSourceFinalRingVariableCode decider symbols secondRing := by omega
  rw [numeric]
  obtain ⟨firstSource, firstVertex, firstSourceMember, rfl⟩ :=
    finalPositionedFormula_atom_is_ringCopy (directSourceFormula decider symbols) firstRing firstMember
  obtain ⟨secondSource, secondVertex, secondSourceMember, rfl⟩ :=
    finalPositionedFormula_atom_is_ringCopy (directSourceFormula decider symbols) secondRing secondMember
  exact directSourceFinalRingVariableCode_eq_iff_ringCopy decider symbols firstSource secondSource
    firstSourceMember secondSourceMember firstVertex secondVertex

end LeanTrominoes.PeriodicCNFStripReduction

end
