/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRingVariableSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalScaledTerminalCertificate
import LeanTrominoes.RetainedAngularOccurrenceCopiedAtomSemantics
import LeanTrominoes.PeriodicCNFStripHorizontalSourceOccurrenceCopiedValues

/-! # Copied inherited codes select actual pre-Figure 9 ring literals -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit PeriodicOrthocrossing PeriodicThreeSATThree
open PeriodicCNF.FormulaShapeRetainedFigureNineDirection

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance copiedRingVariableStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

local instance copiedRingVariableVariableDecidableEq : DecidableEq Variable :=
  directSourceVariableDecidableEq

private theorem copiedOccurrenceClauses_atoms
    {Atom : Type} [DecidableEq Atom] (source : PeriodicCNF Atom) :
    (copiedOccurrenceClauses source).flatMap (fun clause => clause.literals.map PeriodicLiteral.atom) =
      selectedCopies (retainedFinalCoordinatedScaledSource source).erase
        (occurrencePortsForFigureSeven source) := by
  rw [← PeriodicEightOccurrenceSplit.occurrenceClauses_variableOccurrences]
  unfold retainedFinalCoordinatedScaledSource
  rw [PositionedPeriodicCNF.erase_scale]
  unfold copiedOccurrenceClauses copiedOccurrenceClause
  simp only [
    PeriodicCNF.variableOccurrences, PeriodicEightOccurrenceSplit.occurrenceClauses,
    PositionedPeriodicCNF.erase, List.zipIdx_map, List.map_map, List.flatMap_map,
    Function.comp_def, Prod.map, id_eq]

/-- The candidate identity stream is exactly the semantic code of every
literal atom in the actual copied-clause prefix, in presentation order. -/
theorem directSourceFinalPreFigureNineInheritedRingAtomCodes_eq_copied_atoms
    (symbols : List encoding.Γ) :
    directSourceFinalPreFigureNineInheritedRingAtomCodes decider symbols =
      ((copiedOccurrenceClauses (directSourceFormula decider symbols)).flatMap
        (fun clause => clause.literals.map PeriodicLiteral.atom)).map
          (directSourceFinalRingVariableCode decider symbols) := by
  rw [directSourceFinalPreFigureNineInheritedRingAtomCodes_eq_semantic_pairs,
    copiedOccurrenceClauses_atoms]
  change _ = (selectedCopies
    (retainedFinalCoordinatedScaledSource (directSourceFormula decider symbols)).erase
    (occurrencePortsOfAngularOrder
      (retainedFinalCoordinatedScaledSource (directSourceFormula decider symbols)).erase
      (angularOccurrenceOrder
        (retainedFinalCoordinatedScaledSource (directSourceFormula decider symbols)).erase
        (retainedFinalCoordinatedScaledSourceRoutes (directSourceFormula decider symbols))))).map _
  rw [selectedCopies_eq_boundedGlobalStableAtomRankPairs _ _
    (directSourceFinalScaledOccurrenceTerminalCertificate decider symbols)
    (directSourceFinalScaledSource_occurrencesAtMostEight decider symbols), List.map_map]
  apply List.map_congr_left
  intro pair member
  obtain ⟨occurrence, _occurrenceMember, rfl⟩ := List.mem_map.mp member
  exact (directSourceFinalRingVariableCode_angularCopy decider symbols occurrence.1 _
    (boundedRetainedTerminalSlot _).isLt).symm

/-- Every compiled copied query selects the semantic code of the actual
copied literal at that source position. -/
theorem directSourceFinalCopiedInheritedRingAtomCodes_eq_selected_copied_atoms
    (symbols : List encoding.Γ) :
    directSourceFinalCopiedInheritedRingAtomCodes decider symbols =
      HorizontalRoutedRouteHeaderCopiedSourcePosition.selectedValues
        (directRetainedFigureNineCopiedClauseDescriptors decider symbols)
        (((copiedOccurrenceClauses (directSourceFormula decider symbols)).flatMap
          (fun clause => clause.literals.map PeriodicLiteral.atom)).map
            (directSourceFinalRingVariableCode decider symbols)) := by
  rw [directSourceFinalCopiedInheritedRingAtomCodes_eq_selectedValues,
    directSourceFinalPreFigureNineInheritedRingAtomCodes_eq_copied_atoms]

/-- Copied inherited queries read the actual literal row of their own
parent clause, after the same finite presentation-slot remapping used by the
header compiler. This preserves all parent and header boundaries. -/
theorem directSourceFinalCopiedInheritedRingAtomCodes_eq_clause_blocks
    (symbols : List encoding.Γ) :
    directSourceFinalCopiedInheritedRingAtomCodes decider symbols =
      (finalCoordinatedSource (directSourceFormula decider symbols)).clauses.zipIdx.flatMap
        (fun tagged =>
          (HorizontalRoutedRouteHeaderPresentationAtomScope.clauseBlock
            (copiedClauseProfile (directSourceFormula decider symbols) tagged.2 tagged.1)).map
            (fun control =>
              ((copiedOccurrenceClause (directSourceFormula decider symbols) tagged.2 tagged.1).literals.map
                (fun literal => directSourceFinalRingVariableCode decider symbols literal.atom)).getD
                  (HorizontalRoutedRouteHeaderCopiedSourcePosition.scopeOffset control) 0)) := by
  let source := directSourceFormula decider symbols
  let blocks := (finalCoordinatedSource source).clauses.zipIdx.map fun tagged =>
    (copiedClauseProfile source tagged.2 tagged.1,
      (copiedOccurrenceClause source tagged.2 tagged.1).literals.map
        (fun literal => directSourceFinalRingVariableCode decider symbols literal.atom))
  have tokensEq : blocks.map (fun block => PeriodicCNF.FormulaShapeDirectionOrdering.Token.clause block.1) =
      directRetainedFigureNineCopiedClauseDescriptors decider symbols := by
    change _ = copiedClauseDescriptors source
    simp only [blocks, copiedClauseDescriptors, List.map_map, Function.comp_def]
  have valuesEq : blocks.flatMap Prod.snd =
      ((copiedOccurrenceClauses source).flatMap
        (fun clause => clause.literals.map PeriodicLiteral.atom)).map
          (directSourceFinalRingVariableCode decider symbols) := by
    simp only [blocks, copiedOccurrenceClauses, List.flatMap_map, List.map_flatMap,
      List.map_map, Function.comp_def]
  have lengths : ∀ block ∈ blocks, block.2.length =
      HorizontalRoutedRouteHeaderCopiedSourcePosition.sourceWordCount block.1 := by
    intro block member
    obtain ⟨tagged, taggedMember, rfl⟩ := List.mem_map.mp member
    have clauseMember := List.fst_mem_of_mem_zipIdx taggedMember
    have literalMember : tagged.1.literals ∈
        PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection.deduplicatedClauses source := by
      rw [← finalCoordinatedSource_clauseLiterals_eq]
      exact List.mem_map.mpr ⟨tagged.1, clauseMember, rfl⟩
    have nonempty := directSource_deduplicatedClauses_nonempty decider symbols _ literalMember
    have width := directSource_deduplicatedClauses_widthAtMostThree decider symbols _ literalMember
    simp only [List.length_map, copiedOccurrenceClause, PeriodicEightOccurrenceSplit.occurrenceClause,
      List.length_zipIdx, HorizontalRoutedRouteHeaderCopiedSourcePosition.sourceWordCount,
      HorizontalRoutedRouteHeaderCopiedScopedAtomWords.sourceWordCount, copiedClauseProfile]
    rw [PeriodicCNF.FormulaShapeDirectionOrdering.DirectedClauseProfile.taggedLiterals_ofList _
      (by simpa using nonempty) (by simpa using width)]
    simp only [List.length_map, List.length_zipIdx]
  rw [directSourceFinalCopiedInheritedRingAtomCodes_eq_selected_copied_atoms,
    ← tokensEq, ← valuesEq,
    HorizontalRoutedRouteHeaderCopiedSourcePosition.selectedValues_clauseBlocks blocks lengths]
  simp only [blocks, List.flatMap_map, source]

/-- The copied code column is read from the same coherent parent/header
records used by the final source witnesses, for any attached tail tables. -/
theorem directSourceFinalCopiedInheritedRingAtomCodes_eq_occurrence_values
    (symbols : List encoding.Γ) (tails : List (List (List AxisDirection))) :
    directSourceFinalCopiedInheritedRingAtomCodes decider symbols =
      (PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail.sourceOccurrences
        (directRetainedFigureNineCopiedClauseDescriptors decider symbols) tails).map
        (sourceOccurrenceCopiedValue
          ((copiedOccurrenceClauses (directSourceFormula decider symbols)).map
            (fun clause => clause.literals.map
              (fun literal => directSourceFinalRingVariableCode decider symbols literal.atom)))) := by
  rw [directSourceFinalCopiedInheritedRingAtomCodes_eq_clause_blocks]
  let source := directSourceFormula decider symbols
  let blocks := (finalCoordinatedSource source).clauses.zipIdx.map fun tagged =>
    (copiedClauseProfile source tagged.2 tagged.1,
      (copiedOccurrenceClause source tagged.2 tagged.1).literals.map
        (fun literal => directSourceFinalRingVariableCode decider symbols literal.atom))
  change _ = (PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail.sourceOccurrences
    (copiedClauseDescriptors source) tails).map _
  have mapped := sourceOccurrences_map_copiedValue_blocks blocks tails
  simpa only [blocks, copiedClauseDescriptors, copiedOccurrenceClauses, List.map_map,
    List.flatMap_map, Function.comp_def, source] using mapped.symm

end LeanTrominoes.PeriodicCNFStripReduction

end
