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

/-- At a genuine fresh occurrence, the complete numeric identity selects
the odd encoding of that record's own parent-local code. -/
theorem directSourceFinalAtomIdentityCodes_getD_of_fresh
    (symbols : List encoding.Γ) (index : Nat)
    (indexLt : index < (directSourceFinalOccurrences decider symbols).length)
    (fresh : sourceOccurrenceIsFresh (directSourceFinalOccurrences decider symbols)[index]) :
    (directSourceFinalAtomIdentityCodes decider symbols).getD index 0 =
      sourceOccurrenceLocalAtomCode (directSourceFinalOccurrences decider symbols)[index] * 2 + 1 := by
  have compiledLt : index < (directSourceFinalCompiledOccurrenceData decider symbols).length := by
    rw [← directSourceFinalOccurrences_length_eq_compiled]
    exact indexLt
  have scopeAt : (directSourceFinalAtomScopeBits decider symbols).getD index false = true := by
    rw [directSourceFinalAtomScopeBits_eq_occurrences]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem indexLt, Option.map_some, Option.getD_some,
      sourceOccurrenceScope_of_fresh _ fresh, finalAtomScopeBit]
  rw [directSourceFinalAtomIdentityCodes_getD decider symbols index compiledLt, scopeAt]
  rw [directSourceFinalOddLocalAtomCodes_eq_map,
    ← directSourceFinalOccurrences_map_localAtomCode]
  simp only [ite_true, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem indexLt, Option.map_some, Option.getD_some]

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

end LeanTrominoes.PeriodicCNFStripReduction

end
