/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceBlocks
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalAuxiliaryAtomHorizontalSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceInheritedSourceLiterals
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedFigureNineRingAtomMembership

/-! # Actual inherited atoms at global copied-occurrence indices -/

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

noncomputable local instance copiedInheritedHorizontalStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

local instance copiedInheritedHorizontalVariableDecidableEq : DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- An inherited copied record's numeric code and source witness select the
same actual ring atom. The lookup retains its original global output index. -/
theorem directSourceFinalCopiedInheritedAtom_witness
    (symbols : List encoding.Γ) (index : Nat) (occurrence : SourceOccurrence)
    (witness : OccurrenceWitness (directSourceFormula decider symbols) occurrence)
    (copiedLookup : (directSourceFinalCopiedOccurrences decider symbols)[index]? = some occurrence)
    (original : ¬ sourceOccurrenceIsFresh occurrence) (slot : SourceLiteralSlot)
    (selected : sourceSlot? (prefixAtom occurrence.header.figurePrefix) = some slot) :
    ∃ atom : ThreeOccurrenceVariable (WrappedPeriodicPlanarSATVariable Variable),
      instantiatedVariableMap witness.metadata.sourceClauseIndex witness.metadata.figureNineClauseStart
        witness.metadata.sourceClause (prefixAtom occurrence.header.figurePrefix) = .inl (.inl atom) ∧
      (directSourceFinalInheritedRingAtomCodes decider symbols).getD index 0 =
        directSourceFinalRingVariableCode decider symbols atom ∧
      atom ∈ (copiedOccurrenceClauses (directSourceFormula decider symbols)).flatMap
        (fun clause => clause.literals.map PeriodicLiteral.atom) := by
  have copiedMember := List.mem_iff_getElem?.mpr ⟨index, copiedLookup⟩
  have parentLt := directSourceFinalCopiedOccurrences_parent_lt decider symbols occurrence copiedMember
  have parentLookup := witness.sourceLookup
  rw [finalPositionedFormula_clauses_eq_descriptorBlocks, List.getElem?_append_left parentLt] at parentLookup
  have querySelected := selected
  rw [prefixAtom_eq_localQuery] at querySelected
  obtain ⟨literal, literalLookup, atomEq⟩ := witness.inheritedSourceLiteral slot querySelected
  have scope := sourceOccurrenceScope_of_inherited occurrence original slot selected
  have valueEq := sourceOccurrenceCopiedValue_eq_literal
    (copiedOccurrenceClauses (directSourceFormula decider symbols))
    (directSourceFinalRingVariableCode decider symbols) occurrence witness.refinedClause literal slot
    parentLookup scope literalLookup
  have codeLookup := directSourceFinalInheritedRingAtomCodes_copied_lookup decider symbols index occurrence copiedLookup
  rw [valueEq] at codeLookup
  refine ⟨literal.atom, ?_, ?_, ?_⟩
  · simpa only [prefixAtom_eq_localQuery] using atomEq
  · simp only [List.getD_eq_getElem?_getD, codeLookup, Option.getD_some]
  · exact List.mem_flatMap.mpr ⟨witness.refinedClause,
      List.mem_iff_getElem?.mpr ⟨occurrence.parentClauseIndex, parentLookup⟩,
      List.mem_map.mpr ⟨literal, List.mem_iff_getElem?.mpr ⟨_, literalLookup⟩, rfl⟩⟩

/-- The complete numeric identity and the actual horizontal atom at an
inherited copied index are obtained from that same represented ring atom. -/
theorem directSourceFinalCopiedInheritedAtom_eq_horizontal
    (symbols : List encoding.Γ) (index : Nat) (occurrence : SourceOccurrence)
    (occurrenceLookup : (directSourceFinalOccurrences decider symbols)[index]? = some occurrence)
    (copiedLt : index < (directSourceFinalCopiedOccurrences decider symbols).length)
    (original : ¬ sourceOccurrenceIsFresh occurrence) (slot : SourceLiteralSlot)
    (selected : sourceSlot? (prefixAtom occurrence.header.figurePrefix) = some slot)
    (horizontalAtom : RoutedVariable)
    (atomLookup : (horizontalRoutedFormulaComputed
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences[index]? = some horizontalAtom) :
    ∃ atom : ThreeOccurrenceVariable (WrappedPeriodicPlanarSATVariable Variable),
      horizontalAtom = .inl (.inl (.inl atom)) ∧
      (directSourceFinalAtomIdentityCodes decider symbols).getD index 0 =
        directSourceFinalRingVariableCode decider symbols atom * 2 ∧
      atom ∈ (copiedOccurrenceClauses (directSourceFormula decider symbols)).flatMap
        (fun clause => clause.literals.map PeriodicLiteral.atom) := by
  have copiedLookup := directSourceFinalOccurrences_copied_lookup decider symbols index occurrence copiedLt occurrenceLookup
  obtain ⟨indexLt, rfl⟩ := List.getElem?_eq_some_iff.mp occurrenceLookup
  let witness := directSourceFinalOccurrenceWitness decider symbols index indexLt
  obtain ⟨atom, atomEq, codeEq, member⟩ :=
    directSourceFinalCopiedInheritedAtom_witness decider symbols index _ witness copiedLookup original slot selected
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

/-- Two inherited copied incidences have equal complete numeric identities
exactly when their actual horizontal atoms are equal. -/
theorem directSourceFinalAtomIdentityCodes_copiedInherited_eq_iff_horizontalAtoms
    (symbols : List encoding.Γ) (firstIndex secondIndex : Nat)
    (first second : SourceOccurrence)
    (firstOccurrenceLookup : (directSourceFinalOccurrences decider symbols)[firstIndex]? = some first)
    (secondOccurrenceLookup : (directSourceFinalOccurrences decider symbols)[secondIndex]? = some second)
    (firstCopied : firstIndex < (directSourceFinalCopiedOccurrences decider symbols).length)
    (secondCopied : secondIndex < (directSourceFinalCopiedOccurrences decider symbols).length)
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
    directSourceFinalCopiedInheritedAtom_eq_horizontal decider symbols firstIndex first firstOccurrenceLookup
      firstCopied firstOriginal firstSlot firstSelected firstAtom firstAtomLookup
  obtain ⟨secondRing, secondAtomEq, secondCodeEq, secondMember⟩ :=
    directSourceFinalCopiedInheritedAtom_eq_horizontal decider symbols secondIndex second secondOccurrenceLookup
      secondCopied secondOriginal secondSlot secondSelected secondAtom secondAtomLookup
  rw [firstCodeEq, secondCodeEq, firstAtomEq, secondAtomEq]
  simp only [Sum.inl.injEq]
  have numeric : directSourceFinalRingVariableCode decider symbols firstRing * 2 =
        directSourceFinalRingVariableCode decider symbols secondRing * 2 ↔
      directSourceFinalRingVariableCode decider symbols firstRing =
        directSourceFinalRingVariableCode decider symbols secondRing := by omega
  rw [numeric]
  obtain ⟨firstSource, firstVertex, firstSourceMember, rfl⟩ :=
    copiedOccurrenceClauses_atom_is_ringCopy (directSourceFormula decider symbols) firstRing firstMember
  obtain ⟨secondSource, secondVertex, secondSourceMember, rfl⟩ :=
    copiedOccurrenceClauses_atom_is_ringCopy (directSourceFormula decider symbols) secondRing secondMember
  exact directSourceFinalRingVariableCode_eq_iff_ringCopy decider symbols firstSource secondSource
    firstSourceMember secondSourceMember firstVertex secondVertex

end LeanTrominoes.PeriodicCNFStripReduction

end
