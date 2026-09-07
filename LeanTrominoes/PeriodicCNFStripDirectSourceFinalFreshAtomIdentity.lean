/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceLocalAtomCodes
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalAtomIdentitySemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutePairOccurrenceDataSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineSourceOccurrenceIdentity

/-! # Compiled fresh-atom identities equal exact source-occurrence identities -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail
open HorizontalRoutedRouteHeader

/-- The main and complement-clause uses of a polarity fresh variable. -/
def sourceOccurrenceIsFresh (occurrence : SourceOccurrence) : Prop :=
  occurrence.header.polarity.operation = .incompatible ∨
    occurrence.header.polarity.operation = .complementFresh

private theorem sourceOccurrenceScope_of_fresh (occurrence : SourceOccurrence)
    (fresh : sourceOccurrenceIsFresh occurrence) :
    outputAtomScopeControl occurrence.header =
      .parentLocal (.fresh occurrence.header.figurePrefix) := by
  rcases fresh with fresh | fresh <;>
    simp [outputAtomScopeControl, outputAtomControl, fresh,
      AtomControl.scopeControl, AtomControl.inheritedSourceSlot?,
      AtomControl.representedAtom, ParentRelativeAtom.inheritedSourceSlot?]

private theorem sourceOccurrenceLocalAtomCode_of_fresh (occurrence : SourceOccurrence)
    (fresh : sourceOccurrenceIsFresh occurrence) :
    sourceOccurrenceLocalAtomCode occurrence =
      HorizontalRoutedRouteHeaderGlobalLocalAtoms.numericCode
        (occurrence.parentClauseIndex, parentLocalAtomCode (.fresh occurrence.header.figurePrefix)) := by
  rw [sourceOccurrenceLocalAtomCode, sourceOccurrenceScope_of_fresh occurrence fresh]
  rfl

private theorem sourceOccurrenceLocalAtomCode_of_parentLocal (occurrence : SourceOccurrence)
    (control : AtomControl)
    (scope : outputAtomScopeControl occurrence.header = .parentLocal control) :
    sourceOccurrenceLocalAtomCode occurrence =
      HorizontalRoutedRouteHeaderGlobalLocalAtoms.numericCode
        (occurrence.parentClauseIndex, parentLocalAtomCode control) := by
  rw [sourceOccurrenceLocalAtomCode, scope]
  rfl

private theorem scopeControl_parentLocal_control (atom control : AtomControl)
    (scope : atom.scopeControl = .parentLocal control) : atom = control := by
  cases selected : atom.inheritedSourceSlot? with
  | none => simpa only [AtomControl.scopeControl, selected, AtomScopeControl.parentLocal.injEq] using scope
  | some slot =>
      simp only [AtomControl.scopeControl, selected] at scope
      cases scope

/-- A local code equal to a fresh code cannot represent an original Figure 9
atom: the finite quotient retains the original/fresh constructor. -/
theorem sourceOccurrenceIsFresh_of_localAtomCode_eq
    (first second : SourceOccurrence) (firstFresh : sourceOccurrenceIsFresh first)
    (control : AtomControl)
    (secondScope : outputAtomScopeControl second.header = .parentLocal control)
    (codesEq : sourceOccurrenceLocalAtomCode first = sourceOccurrenceLocalAtomCode second) :
    sourceOccurrenceIsFresh second := by
  rw [sourceOccurrenceLocalAtomCode_of_fresh first firstFresh,
    sourceOccurrenceLocalAtomCode_of_parentLocal second control secondScope] at codesEq
  have paired := HorizontalRoutedRouteHeaderGlobalLocalAtoms.numericCode_injective codesEq
  have represented := (parentLocalAtomCode_eq_iff _ _).mp (congrArg Prod.snd paired)
  have controlEq := scopeControl_parentLocal_control (outputAtomControl second.header) control secondScope
  rw [← controlEq] at represented
  cases operation : second.header.polarity.operation with
  | incompatible => exact Or.inl operation
  | complementFresh => exact Or.inr operation
  | compatible => simp [outputAtomControl, operation, AtomControl.representedAtom] at represented
  | complementOriginal => simp [outputAtomControl, operation, AtomControl.representedAtom] at represented

/-- The finite quotient and parent arithmetic preserve exactly the local
fresh-variable key, including agreement between the two polarity operations. -/
theorem sourceOccurrenceLocalAtomCode_fresh_eq_iff
    (first second : SourceOccurrence)
    (firstFresh : sourceOccurrenceIsFresh first) (secondFresh : sourceOccurrenceIsFresh second) :
    sourceOccurrenceLocalAtomCode first = sourceOccurrenceLocalAtomCode second ↔
      (first.parentClauseIndex, first.header.figurePrefix) =
        (second.parentClauseIndex, second.header.figurePrefix) := by
  rw [sourceOccurrenceLocalAtomCode_of_fresh first firstFresh,
    sourceOccurrenceLocalAtomCode_of_fresh second secondFresh,
    HorizontalRoutedRouteHeaderGlobalLocalAtoms.numericCode_injective.eq_iff]
  simp only [Prod.mk.injEq, parentLocalAtomCode_eq_iff,
    AtomControl.representedAtom, Sum.inr.injEq]

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance freshAtomIdentityStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance freshAtomIdentityVariableDecidableEq : DecidableEq Variable :=
  directSourceVariableDecidableEq

theorem directSourceFinalOccurrences_length_eq_compiled
    (symbols : List encoding.Γ) :
    (directSourceFinalOccurrences decider symbols).length =
      (directSourceFinalCompiledOccurrenceData decider symbols).length := by
  rw [directSourceFinalCompiledOccurrenceData_eq_routePairs,
    ← directSourceFinalOccurrences_map_pair]
  simp only [List.length_map]

/-- The scope selector is another projection of the same coherent records
that supply the parent-code column. -/
theorem directSourceFinalAtomScopeBits_eq_occurrences
    (symbols : List encoding.Γ) :
    directSourceFinalAtomScopeBits decider symbols =
      (directSourceFinalOccurrences decider symbols).map
        (fun occurrence => finalAtomScopeBit (outputAtomScopeControl occurrence.header)) := by
  rw [directSourceFinalAtomScopeBits_eq_map, directSourceFinalAtomScopeControls_eq_map,
    directSourceFinalCompiledOccurrenceData_eq_routePairs,
    ← directSourceFinalOccurrences_map_pair]
  simp only [List.map_map, Function.comp_def, SourceOccurrence.pair,
    occurrenceData_atomScopeControl]

/-- A parent-local occurrence selects its own odd-encoded local code. -/
theorem directSourceFinalAtomIdentityCodes_getD_of_parentLocal
    (symbols : List encoding.Γ) (index : Nat)
    (indexLt : index < (directSourceFinalOccurrences decider symbols).length)
    (control : AtomControl)
    (scope : outputAtomScopeControl (directSourceFinalOccurrences decider symbols)[index].header =
      .parentLocal control) :
    (directSourceFinalAtomIdentityCodes decider symbols).getD index 0 =
      sourceOccurrenceLocalAtomCode (directSourceFinalOccurrences decider symbols)[index] * 2 + 1 := by
  have compiledLt : index < (directSourceFinalCompiledOccurrenceData decider symbols).length := by
    rw [← directSourceFinalOccurrences_length_eq_compiled]
    exact indexLt
  have scopeAt : (directSourceFinalAtomScopeBits decider symbols).getD index false = true := by
    rw [directSourceFinalAtomScopeBits_eq_occurrences]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem indexLt, Option.map_some, Option.getD_some,
      scope, finalAtomScopeBit]
  rw [directSourceFinalAtomIdentityCodes_getD decider symbols index compiledLt, scopeAt]
  rw [directSourceFinalOddLocalAtomCodes_eq_map,
    ← directSourceFinalOccurrences_map_localAtomCode]
  simp only [ite_true, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem indexLt, Option.map_some, Option.getD_some]

/-- An inherited occurrence selects the even namespace. -/
theorem directSourceFinalAtomIdentityCodes_getD_of_inherited
    (symbols : List encoding.Γ) (index : Nat)
    (indexLt : index < (directSourceFinalOccurrences decider symbols).length)
    (slot : PeriodicCNF.ClauseProfilePolarityRouteOperation.SourceLiteralSlot)
    (scope : outputAtomScopeControl (directSourceFinalOccurrences decider symbols)[index].header =
      .inherited slot) :
    (directSourceFinalAtomIdentityCodes decider symbols).getD index 0 =
      (directSourceFinalEvenInheritedAtomCodes decider symbols).getD index 0 := by
  have compiledLt : index < (directSourceFinalCompiledOccurrenceData decider symbols).length := by
    rw [← directSourceFinalOccurrences_length_eq_compiled]
    exact indexLt
  have scopeAt : (directSourceFinalAtomScopeBits decider symbols).getD index false = false := by
    rw [directSourceFinalAtomScopeBits_eq_occurrences]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem indexLt, Option.map_some, Option.getD_some,
      scope, finalAtomScopeBit]
  rw [directSourceFinalAtomIdentityCodes_getD decider symbols index compiledLt, scopeAt]
  rfl

/-- At a genuine fresh occurrence, the complete numeric identity selects
the odd encoding of that record's own parent-local code. -/
theorem directSourceFinalAtomIdentityCodes_getD_of_fresh
    (symbols : List encoding.Γ) (index : Nat)
    (indexLt : index < (directSourceFinalOccurrences decider symbols).length)
    (fresh : sourceOccurrenceIsFresh (directSourceFinalOccurrences decider symbols)[index]) :
    (directSourceFinalAtomIdentityCodes decider symbols).getD index 0 =
      sourceOccurrenceLocalAtomCode (directSourceFinalOccurrences decider symbols)[index] * 2 + 1 := by
  exact directSourceFinalAtomIdentityCodes_getD_of_parentLocal decider symbols index indexLt _
    (sourceOccurrenceScope_of_fresh _ fresh)

/-- No inherited or original auxiliary code can collide with a fresh code. -/
theorem directSourceFinalOccurrence_isFresh_of_identity_eq
    (symbols : List encoding.Γ) (firstIndex secondIndex : Nat)
    (firstLt : firstIndex < (directSourceFinalOccurrences decider symbols).length)
    (secondLt : secondIndex < (directSourceFinalOccurrences decider symbols).length)
    (firstFresh : sourceOccurrenceIsFresh (directSourceFinalOccurrences decider symbols)[firstIndex])
    (codesEq : (directSourceFinalAtomIdentityCodes decider symbols).getD firstIndex 0 =
      (directSourceFinalAtomIdentityCodes decider symbols).getD secondIndex 0) :
    sourceOccurrenceIsFresh (directSourceFinalOccurrences decider symbols)[secondIndex] := by
  rw [directSourceFinalAtomIdentityCodes_getD_of_fresh decider symbols firstIndex firstLt firstFresh] at codesEq
  cases scope : outputAtomScopeControl (directSourceFinalOccurrences decider symbols)[secondIndex].header with
  | inherited slot =>
      rw [directSourceFinalAtomIdentityCodes_getD_of_inherited
        decider symbols secondIndex secondLt slot scope] at codesEq
      have even : (directSourceFinalEvenInheritedAtomCodes decider symbols).getD secondIndex 0 % 2 = 0 := by
        rw [directSourceFinalEvenInheritedAtomCodes_eq_map,
          List.getD_eq_getElem?_getD, List.getElem?_map]
        cases selected : (directSourceFinalInheritedRingAtomCodes decider symbols)[secondIndex]? <;> simp
      omega
  | parentLocal control =>
      rw [directSourceFinalAtomIdentityCodes_getD_of_parentLocal
        decider symbols secondIndex secondLt control scope] at codesEq
      exact sourceOccurrenceIsFresh_of_localAtomCode_eq _ _ firstFresh control scope (by omega)

/-- Complete compiled fresh-atom codes agree exactly at equal global source
occurrences, rather than merely at equal finite profiles. -/
theorem directSourceFinalAtomIdentityCodes_fresh_eq_iff_sourceIndex
    (symbols : List encoding.Γ) (firstIndex secondIndex : Nat)
    (firstLt : firstIndex < (directSourceFinalOccurrences decider symbols).length)
    (secondLt : secondIndex < (directSourceFinalOccurrences decider symbols).length)
    (firstFresh : sourceOccurrenceIsFresh (directSourceFinalOccurrences decider symbols)[firstIndex])
    (secondFresh : sourceOccurrenceIsFresh (directSourceFinalOccurrences decider symbols)[secondIndex]) :
    (directSourceFinalAtomIdentityCodes decider symbols).getD firstIndex 0 =
        (directSourceFinalAtomIdentityCodes decider symbols).getD secondIndex 0 ↔
      (directSourceFinalOccurrences decider symbols)[firstIndex].sourceIndex =
        (directSourceFinalOccurrences decider symbols)[secondIndex].sourceIndex := by
  rw [directSourceFinalAtomIdentityCodes_getD_of_fresh decider symbols firstIndex firstLt firstFresh,
    directSourceFinalAtomIdentityCodes_getD_of_fresh decider symbols secondIndex secondLt secondFresh]
  have arithmetic :
      sourceOccurrenceLocalAtomCode (directSourceFinalOccurrences decider symbols)[firstIndex] * 2 + 1 =
          sourceOccurrenceLocalAtomCode (directSourceFinalOccurrences decider symbols)[secondIndex] * 2 + 1 ↔
        sourceOccurrenceLocalAtomCode (directSourceFinalOccurrences decider symbols)[firstIndex] =
          sourceOccurrenceLocalAtomCode (directSourceFinalOccurrences decider symbols)[secondIndex] := by
    omega
  rw [arithmetic, sourceOccurrenceLocalAtomCode_fresh_eq_iff _ _ firstFresh secondFresh]
  exact sourceOccurrencesFrom_freshKey_eq_iff_sourceIndex 0 0 _ _ _ _
    (List.getElem_mem firstLt) (List.getElem_mem secondLt)

/-- A fresh code's entire equality class consists precisely of the fresh
uses of that global source occurrence. -/
theorem directSourceFinalAtomIdentityCodes_eq_iff_of_fresh
    (symbols : List encoding.Γ) (firstIndex secondIndex : Nat)
    (firstLt : firstIndex < (directSourceFinalOccurrences decider symbols).length)
    (secondLt : secondIndex < (directSourceFinalOccurrences decider symbols).length)
    (firstFresh : sourceOccurrenceIsFresh (directSourceFinalOccurrences decider symbols)[firstIndex]) :
    (directSourceFinalAtomIdentityCodes decider symbols).getD firstIndex 0 =
        (directSourceFinalAtomIdentityCodes decider symbols).getD secondIndex 0 ↔
      sourceOccurrenceIsFresh (directSourceFinalOccurrences decider symbols)[secondIndex] ∧
        (directSourceFinalOccurrences decider symbols)[firstIndex].sourceIndex =
          (directSourceFinalOccurrences decider symbols)[secondIndex].sourceIndex := by
  constructor
  · intro equal
    have secondFresh := directSourceFinalOccurrence_isFresh_of_identity_eq
      decider symbols firstIndex secondIndex firstLt secondLt firstFresh equal
    exact ⟨secondFresh, (directSourceFinalAtomIdentityCodes_fresh_eq_iff_sourceIndex
      decider symbols firstIndex secondIndex firstLt secondLt firstFresh secondFresh).mp equal⟩
  · rintro ⟨secondFresh, indexEq⟩
    exact (directSourceFinalAtomIdentityCodes_fresh_eq_iff_sourceIndex
      decider symbols firstIndex secondIndex firstLt secondLt firstFresh secondFresh).mpr indexEq

end LeanTrominoes.PeriodicCNFStripReduction

end
