/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceAuxiliaryAtoms
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceAtomClassification
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOriginalAtomHorizontalSemantics

/-! # Compiled auxiliary identities agree with actual horizontal atoms -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open PeriodicCNF.FormulaShapeFigureNineRoutePrefix
open PeriodicCNF.FormulaShapeRetainedFigureNineSourceTail
open HorizontalRoutedRouteHeader

/-- An original Figure 9 or unit-elimination auxiliary occurrence. -/
def sourceOccurrenceIsAuxiliary (occurrence : SourceOccurrence) : Prop :=
  ¬ sourceOccurrenceIsFresh occurrence ∧ sourceSlot? (prefixAtom occurrence.header.figurePrefix) = none

/-- Original auxiliaries select the parent-local namespace with their own
finite original-atom control. -/
theorem sourceOccurrenceScope_of_auxiliary (occurrence : SourceOccurrence)
    (auxiliary : sourceOccurrenceIsAuxiliary occurrence) :
    outputAtomScopeControl occurrence.header = .parentLocal (.original occurrence.header.figurePrefix) := by
  rcases auxiliary with ⟨original, selected⟩
  cases operation : occurrence.header.polarity.operation <;>
    simp_all [sourceOccurrenceIsFresh, outputAtomScopeControl, outputAtomControl,
      AtomControl.scopeControl, AtomControl.inheritedSourceSlot?, AtomControl.representedAtom,
      ParentRelativeAtom.inheritedSourceSlot?]

private theorem sourceOccurrenceLocalAtomCode_of_auxiliary (occurrence : SourceOccurrence)
    (auxiliary : sourceOccurrenceIsAuxiliary occurrence) :
    sourceOccurrenceLocalAtomCode occurrence =
      HorizontalRoutedRouteHeaderGlobalLocalAtoms.numericCode
        (occurrence.parentClauseIndex, parentLocalAtomCode (.original occurrence.header.figurePrefix)) := by
  rw [sourceOccurrenceLocalAtomCode, sourceOccurrenceScope_of_auxiliary occurrence auxiliary]
  rfl

/-- The finite quotient compares actual template roles, while the numeric
pairing keeps their original parents distinct. -/
theorem sourceOccurrenceLocalAtomCode_auxiliary_eq_iff
    (first second : SourceOccurrence)
    (firstAuxiliary : sourceOccurrenceIsAuxiliary first)
    (secondAuxiliary : sourceOccurrenceIsAuxiliary second) :
    sourceOccurrenceLocalAtomCode first = sourceOccurrenceLocalAtomCode second ↔
      (first.parentClauseIndex, prefixAtom first.header.figurePrefix) =
        (second.parentClauseIndex, prefixAtom second.header.figurePrefix) := by
  rw [sourceOccurrenceLocalAtomCode_of_auxiliary first firstAuxiliary,
    sourceOccurrenceLocalAtomCode_of_auxiliary second secondAuxiliary,
    HorizontalRoutedRouteHeaderGlobalLocalAtoms.numericCode_injective.eq_iff]
  simp only [Prod.mk.injEq, parentLocalAtomCode_eq_iff, AtomControl.representedAtom, Sum.inl.injEq]

/-- An original source-port occurrence selects the inherited namespace. -/
theorem sourceOccurrenceScope_of_inherited (occurrence : SourceOccurrence)
    (original : ¬ sourceOccurrenceIsFresh occurrence)
    (slot : PeriodicCNF.ClauseProfilePolarityRouteOperation.SourceLiteralSlot)
    (selected : sourceSlot? (prefixAtom occurrence.header.figurePrefix) = some slot) :
    outputAtomScopeControl occurrence.header = .inherited slot := by
  cases operation : occurrence.header.polarity.operation <;>
    simp_all [sourceOccurrenceIsFresh, outputAtomScopeControl, outputAtomControl,
      AtomControl.scopeControl, AtomControl.inheritedSourceSlot?, AtomControl.representedAtom,
      ParentRelativeAtom.inheritedSourceSlot?]

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance auxiliaryHorizontalStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance auxiliaryHorizontalVariableDecidableEq : DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Genuine original auxiliaries retain exactly the parent and finite role
used by the numeric local identity compiler. -/
theorem directSourceFinalOriginalAtom_auxiliary_eq_iff
    (symbols : List encoding.Γ) (firstIndex secondIndex : Nat)
    (firstLt : firstIndex < (directSourceFinalOccurrences decider symbols).length)
    (secondLt : secondIndex < (directSourceFinalOccurrences decider symbols).length)
    (firstAuxiliary : sourceOccurrenceIsAuxiliary (directSourceFinalOccurrences decider symbols)[firstIndex])
    (secondAuxiliary : sourceOccurrenceIsAuxiliary (directSourceFinalOccurrences decider symbols)[secondIndex]) :
    directSourceFinalOriginalAtom decider symbols firstIndex firstLt =
        directSourceFinalOriginalAtom decider symbols secondIndex secondLt ↔
      ((directSourceFinalOccurrences decider symbols)[firstIndex].parentClauseIndex,
          prefixAtom (directSourceFinalOccurrences decider symbols)[firstIndex].header.figurePrefix) =
        ((directSourceFinalOccurrences decider symbols)[secondIndex].parentClauseIndex,
          prefixAtom (directSourceFinalOccurrences decider symbols)[secondIndex].header.figurePrefix) := by
  have firstSelected := firstAuxiliary.2
  have secondSelected := secondAuxiliary.2
  rw [prefixAtom_eq_localQuery] at firstSelected secondSelected
  have identity := (directSourceFinalOccurrenceWitness decider symbols firstIndex firstLt).auxiliaryAtom_eq_iff
    (directSourceFinalOccurrenceWitness decider symbols secondIndex secondLt) firstSelected secondSelected
  simpa only [directSourceFinalOriginalAtom, prefixAtom_eq_localQuery] using identity

/-- Complete numeric identities of genuine auxiliary incidences agree
exactly when their actual horizontal atoms agree. -/
theorem directSourceFinalAtomIdentityCodes_auxiliary_eq_iff_horizontalAtoms
    (symbols : List encoding.Γ) (firstIndex secondIndex : Nat)
    (firstLt : firstIndex < (directSourceFinalOccurrences decider symbols).length)
    (secondLt : secondIndex < (directSourceFinalOccurrences decider symbols).length)
    (firstAuxiliary : sourceOccurrenceIsAuxiliary (directSourceFinalOccurrences decider symbols)[firstIndex])
    (secondAuxiliary : sourceOccurrenceIsAuxiliary (directSourceFinalOccurrences decider symbols)[secondIndex])
    (firstAtom secondAtom : RoutedVariable)
    (firstLookup : (horizontalRoutedFormulaComputed
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences[firstIndex]? = some firstAtom)
    (secondLookup : (horizontalRoutedFormulaComputed
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences[secondIndex]? = some secondAtom) :
    (directSourceFinalAtomIdentityCodes decider symbols).getD firstIndex 0 =
        (directSourceFinalAtomIdentityCodes decider symbols).getD secondIndex 0 ↔
      firstAtom = secondAtom := by
  rw [directSourceFinalAtomIdentityCodes_getD_of_parentLocal decider symbols firstIndex firstLt _
      (sourceOccurrenceScope_of_auxiliary _ firstAuxiliary),
    directSourceFinalAtomIdentityCodes_getD_of_parentLocal decider symbols secondIndex secondLt _
      (sourceOccurrenceScope_of_auxiliary _ secondAuxiliary)]
  have numeric :
      sourceOccurrenceLocalAtomCode (directSourceFinalOccurrences decider symbols)[firstIndex] * 2 + 1 =
          sourceOccurrenceLocalAtomCode (directSourceFinalOccurrences decider symbols)[secondIndex] * 2 + 1 ↔
        sourceOccurrenceLocalAtomCode (directSourceFinalOccurrences decider symbols)[firstIndex] =
          sourceOccurrenceLocalAtomCode (directSourceFinalOccurrences decider symbols)[secondIndex] := by omega
  rw [numeric, sourceOccurrenceLocalAtomCode_auxiliary_eq_iff _ _ firstAuxiliary secondAuxiliary,
    directSourceFinalOriginalAtom_eq_horizontal decider symbols firstIndex firstLt firstAuxiliary.1 firstAtom firstLookup,
    directSourceFinalOriginalAtom_eq_horizontal decider symbols secondIndex secondLt secondAuxiliary.1 secondAtom secondLookup,
    Sum.inl.injEq]
  exact (directSourceFinalOriginalAtom_auxiliary_eq_iff
    decider symbols firstIndex secondIndex firstLt secondLt firstAuxiliary secondAuxiliary).symm

/-- Actual original auxiliaries and inherited source variables occupy
different constructors, even when they come from different parents. -/
theorem directSourceFinalOriginalAtom_ne_of_auxiliary_inherited
    (symbols : List encoding.Γ) (firstIndex secondIndex : Nat)
    (firstLt : firstIndex < (directSourceFinalOccurrences decider symbols).length)
    (secondLt : secondIndex < (directSourceFinalOccurrences decider symbols).length)
    (firstAuxiliary : sourceOccurrenceIsAuxiliary (directSourceFinalOccurrences decider symbols)[firstIndex])
    (slot : PeriodicCNF.ClauseProfilePolarityRouteOperation.SourceLiteralSlot)
    (secondSelected : sourceSlot?
      (prefixAtom (directSourceFinalOccurrences decider symbols)[secondIndex].header.figurePrefix) = some slot) :
    directSourceFinalOriginalAtom decider symbols firstIndex firstLt ≠
      directSourceFinalOriginalAtom decider symbols secondIndex secondLt := by
  let firstWitness := directSourceFinalOccurrenceWitness decider symbols firstIndex firstLt
  let secondWitness := directSourceFinalOccurrenceWitness decider symbols secondIndex secondLt
  have firstSelected := firstAuxiliary.2
  rw [prefixAtom_eq_localQuery] at firstSelected secondSelected
  obtain ⟨atom, inherited⟩ := secondWitness.instantiatedAtom_inherited_iff.mpr ⟨slot, secondSelected⟩
  have unequal := instantiatedVariableMap_not_inherited_of_sourceSlot_none
    firstWitness.metadata.sourceClauseIndex firstWitness.metadata.figureNineClauseStart
    firstWitness.metadata.sourceClause _ firstSelected atom
  have concreteNe :
      PlanarOneInThreeNoUnitsFigureNine.instantiatedVariableMap firstWitness.metadata.sourceClauseIndex
        firstWitness.metadata.figureNineClauseStart firstWitness.metadata.sourceClause
        ((PlanarOneInThreeNoUnitsFigureNine.templateDrawingOfClauseProfile
          (directSourceFinalOccurrences decider symbols)[firstIndex].header.figurePrefix.localQuery.1).incidenceAt
          (directSourceFinalOccurrences decider symbols)[firstIndex].header.figurePrefix.localQuery.2).literal.1 ≠
      PlanarOneInThreeNoUnitsFigureNine.instantiatedVariableMap secondWitness.metadata.sourceClauseIndex
        secondWitness.metadata.figureNineClauseStart secondWitness.metadata.sourceClause
        ((PlanarOneInThreeNoUnitsFigureNine.templateDrawingOfClauseProfile
          (directSourceFinalOccurrences decider symbols)[secondIndex].header.figurePrefix.localQuery.1).incidenceAt
          (directSourceFinalOccurrences decider symbols)[secondIndex].header.figurePrefix.localQuery.2).literal.1 := by
    intro equal
    exact unequal (equal.trans inherited)
  simpa only [directSourceFinalOriginalAtom, prefixAtom_eq_localQuery, firstWitness, secondWitness] using concreteNe

/-- Every comparison involving an original auxiliary incidence is correct,
including comparisons with inherited and polarity-fresh incidences. -/
theorem directSourceFinalAtomIdentityCodes_eq_iff_horizontalAtoms_of_auxiliary
    (symbols : List encoding.Γ) (firstIndex secondIndex : Nat)
    (firstLt : firstIndex < (directSourceFinalOccurrences decider symbols).length)
    (secondLt : secondIndex < (directSourceFinalOccurrences decider symbols).length)
    (firstAuxiliary : sourceOccurrenceIsAuxiliary (directSourceFinalOccurrences decider symbols)[firstIndex])
    (firstAtom secondAtom : RoutedVariable)
    (firstLookup : (horizontalRoutedFormulaComputed
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences[firstIndex]? = some firstAtom)
    (secondLookup : (horizontalRoutedFormulaComputed
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences[secondIndex]? = some secondAtom) :
    (directSourceFinalAtomIdentityCodes decider symbols).getD firstIndex 0 =
        (directSourceFinalAtomIdentityCodes decider symbols).getD secondIndex 0 ↔
      firstAtom = secondAtom := by
  by_cases secondFresh : sourceOccurrenceIsFresh (directSourceFinalOccurrences decider symbols)[secondIndex]
  · have fresh := directSourceFinalAtomIdentityCodes_eq_iff_horizontalAtoms_of_fresh
      decider symbols secondIndex firstIndex secondLt firstLt secondFresh
      secondAtom firstAtom secondLookup firstLookup
    exact eq_comm.trans (fresh.trans eq_comm)
  · cases selected : sourceSlot?
        (prefixAtom (directSourceFinalOccurrences decider symbols)[secondIndex].header.figurePrefix) with
    | none =>
        exact directSourceFinalAtomIdentityCodes_auxiliary_eq_iff_horizontalAtoms
          decider symbols firstIndex secondIndex firstLt secondLt firstAuxiliary
          ⟨secondFresh, selected⟩ firstAtom secondAtom firstLookup secondLookup
    | some slot =>
        have numericNe : (directSourceFinalAtomIdentityCodes decider symbols).getD firstIndex 0 ≠
            (directSourceFinalAtomIdentityCodes decider symbols).getD secondIndex 0 := by
          rw [directSourceFinalAtomIdentityCodes_getD_of_parentLocal decider symbols firstIndex firstLt _
              (sourceOccurrenceScope_of_auxiliary _ firstAuxiliary),
            directSourceFinalAtomIdentityCodes_getD_of_inherited decider symbols secondIndex secondLt slot
              (sourceOccurrenceScope_of_inherited _ secondFresh slot selected)]
          have even : (directSourceFinalEvenInheritedAtomCodes decider symbols).getD secondIndex 0 % 2 = 0 := by
            rw [directSourceFinalEvenInheritedAtomCodes_eq_map,
              List.getD_eq_getElem?_getD, List.getElem?_map]
            cases (directSourceFinalInheritedRingAtomCodes decider symbols)[secondIndex]? <;> simp
          omega
        have semanticNe : firstAtom ≠ secondAtom := by
          rw [directSourceFinalOriginalAtom_eq_horizontal decider symbols firstIndex firstLt
              firstAuxiliary.1 firstAtom firstLookup,
            directSourceFinalOriginalAtom_eq_horizontal decider symbols secondIndex secondLt
              secondFresh secondAtom secondLookup]
          intro equal
          exact directSourceFinalOriginalAtom_ne_of_auxiliary_inherited
            decider symbols firstIndex secondIndex firstLt secondLt firstAuxiliary slot selected
            (Sum.inl.inj equal)
        exact ⟨fun equal => (numericNe equal).elim, fun equal => (semanticNe equal).elim⟩

end LeanTrominoes.PeriodicCNFStripReduction

end
