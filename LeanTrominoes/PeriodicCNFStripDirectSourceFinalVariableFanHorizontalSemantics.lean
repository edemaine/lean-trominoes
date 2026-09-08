/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFanOccurrenceFieldSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableFanCountHorizontalSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableFanStableSemantics
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanSemanticBridge
import LeanTrominoes.FinalFanDataSourceSemantics

/-! # Complete direct variable fans agree with the actual horizontal source -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance variableFanHorizontalStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

/-- At every genuine presentation index, the complete compiled fan is the
actual source fan of that same atom, including every inactive field. -/
theorem directSourceFinalVariableFanData_getD_eq_source
    (symbols : List encoding.Γ) (index : Nat)
    (entry : ActiveOccurrenceEntry (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase)
    (atomLookup : (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences[index]? = some entry.1.1) :
    (directSourceFinalVariableFanData decider symbols).getD index default =
      sourceVariableRibbonFanData (horizontalSemanticNormalizedPlanarPresentation
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)) entry := by
  let positioned := horizontalSemanticNormalizedRibbonSource
    (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)
  let presentation := horizontalSemanticNormalizedPlanarPresentation
    (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)
  have codeLt : index < (directSourceFinalAtomIdentityCodes decider symbols).length := by
    rw [directSourceFinalAtomIdentityCodes_length_eq_horizontalAtoms,
      ← horizontalSemanticNormalizedRibbonSource_variableOccurrences]
    exact (List.getElem?_eq_some_iff.mp atomLookup).1
  rw [directSourceFinalVariableFanData_eq_map_stableFan,
    List.getD_eq_getElem _ _ (by simpa only [List.length_map] using codeLt), List.getElem_map]
  have codeEq : (directSourceFinalAtomIdentityCodes decider symbols)[index] =
      (directSourceFinalAtomIdentityCodes decider symbols).getD index 0 :=
    (List.getD_eq_getElem _ _ codeLt).symm
  rw [codeEq, directSourceFinalVariableFan_countPred_eq_source decider symbols index entry.1.1 atomLookup]
  refine FinalFanDataTripleAssembler.stableFan_eq_source_of_fields presentation entry
    (directSourceFinalOccurrenceCandidateKeys decider symbols)
    (directSourceFinalVariableOccurrenceData decider symbols)
    ((directSourceFinalAtomIdentityCodes decider symbols).getD index 0) ?_
  intro slot slotMember
  let candidate : ActiveOccurrenceEntry positioned.erase :=
    ⟨(entry.1.1, slot), (mem_occurrenceEntries_iff positioned.erase entry.1.1 slot).mpr
      ⟨entry.atom_mem, slotMember⟩⟩
  have fields := directSourceFinalFanOccurrence_fields_eq_semantic
    decider symbols index candidate atomLookup
  have kind := VariableRibbonFanData.sourceVariableRibbonFanData_kind_of_same_atom
    presentation entry candidate rfl
  have polarity := VariableRibbonFanData.sourceVariableRibbonFanData_polarity_of_same_atom
    presentation entry candidate rfl
  have direction := VariableRibbonFanData.sourceVariableRibbonFanData_direction_of_same_atom
    presentation entry candidate rfl
  exact fields.trans (congrArg₂ Prod.mk (congrArg₂ Prod.mk kind polarity) direction).symm

/-- The compiled fan at a genuine index is the complete executable horizontal
fan of that incidence's actual normalized atom. -/
theorem directSourceFinalVariableFanData_getD_eq_horizontal
    (symbols : List encoding.Γ) (index : Nat) (atom : RoutedVariable)
    (atomLookup : (horizontalSemanticNormalizedRibbonSource
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences[index]? = some atom) :
    (directSourceFinalVariableFanData decider symbols).getD index default =
      horizontalOccurrenceVariableRibbonFanDataComputed
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols, atom) := by
  let positioned := horizontalSemanticNormalizedRibbonSource
    (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)
  have atomMember : atom ∈ occurringVariables positioned.erase := by
    simpa only [occurringVariables, PeriodicOneInThreeToThreeDM.occurringVariables, List.mem_dedup] using
      (List.mem_iff_getElem?.mpr ⟨index, atomLookup⟩)
  have firstMember : (.first : OccurrenceSlot) ∈ usedSlots positioned.erase atom := by
    rcases usedSlots_cases_of_atom_mem positioned.erase atom atomMember with one | two | three
    · simp [one]
    · simp [two]
    · simp [three]
  let entry : ActiveOccurrenceEntry positioned.erase :=
    ⟨(atom, .first), (mem_occurrenceEntries_iff positioned.erase atom .first).mpr ⟨atomMember, firstMember⟩⟩
  exact (directSourceFinalVariableFanData_getD_eq_source decider symbols index entry atomLookup).trans
    (horizontalOccurrenceVariableRibbonFanDataComputed_eq_semantic
      (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols) entry).symm

/-- The whole fan stream agrees in its original clause/literal order with
one actual normalized horizontal variable fan per incidence. -/
theorem directSourceFinalVariableFanData_eq_horizontal
    (symbols : List encoding.Γ) :
    directSourceFinalVariableFanData decider symbols =
      (horizontalSemanticNormalizedRibbonSource
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences.map
        (fun atom => horizontalOccurrenceVariableRibbonFanDataComputed
          (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols, atom)) := by
  have lengths : (directSourceFinalVariableFanData decider symbols).length =
      (horizontalSemanticNormalizedRibbonSource
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences.length := by
    rw [directSourceFinalVariableFanData_length, ← directSourceFinalAtomIdentityCodes_length,
      directSourceFinalAtomIdentityCodes_length_eq_horizontalAtoms,
      horizontalSemanticNormalizedRibbonSource_variableOccurrences]
  apply List.ext_getElem
  · simpa only [List.length_map] using lengths
  · intro index fanLt atomLt
    have sourceLt : index < (horizontalSemanticNormalizedRibbonSource
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase.variableOccurrences.length := by
      simpa only [List.length_map] using atomLt
    have identified := directSourceFinalVariableFanData_getD_eq_horizontal decider symbols index _
      (List.getElem?_eq_getElem sourceLt)
    simpa only [List.getElem_map, List.getD_eq_getElem _ _ fanLt] using identified

end LeanTrominoes.PeriodicCNFStripReduction

end
