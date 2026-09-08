/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripCountedContractedIncidenceValueCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalIncidenceEndpointSummaryHorizontalSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalSelectedIncidenceBodyHorizontalSemantics

/-! # Finite endpoint summaries in canonical colored-element order -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing Gadget PeriodicThreeDM PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- Actual finite summaries at one colored element in its stable incidence order. -/
def horizontalIncidenceEndpointSummariesForElement
    (source : PeriodicCNF Nat) (element : WireColor × Nat) :
    List IncidenceEndpointSummary.Summary :=
  ((horizontalThreeDMProblemComputed source).incidences element.1 element.2).map
    (fun incidence => horizontalIncidenceEndpointSummary source ⟨incidence.tripleIndex, element.1⟩)

def horizontalIncidenceEndpointSummariesByElement (source : PeriodicCNF Nat) :
    List IncidenceEndpointSummary.Summary :=
  (CountedContractedIncidence.horizontalElementPairs (horizontalThreeDMProblemComputed source)).flatMap
    (horizontalIncidenceEndpointSummariesForElement source)

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Identity and finite endpoint columns name the same canonical incidence list. -/
theorem directSourceFinalIncidenceEndpointSummaryColumns_length (symbols : List encoding.Γ) :
    (directSourceFinalCanonicalIncidenceElementCodes decider symbols).length =
      (directSourceFinalIncidenceEndpointSummaries decider symbols).length := by
  rw [directSourceFinalCanonicalIncidenceElementCodes_eq_horizontal,
    directSourceFinalIncidenceEndpointSummaries_eq_horizontal, List.length_map, List.length_map]

/-- Reuse the existing counted occurrence keys to select endpoint records. -/
def directSourceFinalSelectedIncidenceEndpointSummaries (symbols : List encoding.Γ) :
    List IncidenceEndpointSummary.Summary :=
  CountedContractedIncidence.selectedValues
    (directSourceFinalCanonicalElementCodes decider symbols)
    (directSourceFinalCanonicalElementDegrees decider symbols)
    (directSourceFinalCanonicalIncidenceElementCodes decider symbols)
    (directSourceFinalIncidenceEndpointSummaries decider symbols)

noncomputable def directSourceFinalSelectedIncidenceEndpointSummariesComputableInPolyTime :
    TM2ComputableInPolyTime id id (directSourceFinalSelectedIncidenceEndpointSummaries decider) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalSelectedIncidenceEndpointSummaries
    exact CountedContractedIncidence.selectedValuesComputableInPolyTimeOf id
      (directSourceFinalCanonicalElementCodes decider)
      (directSourceFinalCanonicalElementDegrees decider)
      (directSourceFinalCanonicalIncidenceElementCodes decider)
      (directSourceFinalIncidenceEndpointSummaries decider)
      (directSourceFinalIncidenceEndpointSummaryColumns_length decider)
      (directSourceFinalCanonicalElementCodesComputableInPolyTime decider)
      (directSourceFinalCanonicalElementDegreesComputableInPolyTime decider)
      (directSourceFinalCanonicalIncidenceElementCodesComputableInPolyTime decider)
      (directSourceFinalIncidenceEndpointSummariesComputableInPolyTime decider)
  else by
    letI : IsEmpty encoding.Γ := ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime id _

/-- The selected records are the actual incidence summaries in element-major
order, with no permutation left to reconcile. -/
theorem directSourceFinalSelectedIncidenceEndpointSummaries_eq_horizontal
    (symbols : List encoding.Γ) :
    directSourceFinalSelectedIncidenceEndpointSummaries decider symbols =
      horizontalIncidenceEndpointSummariesByElement
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols) := by
  unfold directSourceFinalSelectedIncidenceEndpointSummaries
  rw [CountedContractedIncidence.selectedValues_eq_grouped _ _ _ _
    (directSourceFinalCountedContraction_elementColumns_length decider symbols)
    (directSourceFinalIncidenceEndpointSummaryColumns_length decider symbols)
    (directSourceFinalCountedContraction_degrees_valid decider symbols)
    (directSourceFinalCanonicalElementCodes_nodup decider symbols)
    (directSourceFinalCanonicalIncidenceElementCodes_perm_expanded decider symbols)]
  rw [directSourceFinalCanonicalElementCodes_eq_horizontal,
    directSourceFinalCanonicalIncidenceElementCodes_eq_horizontal,
    directSourceFinalIncidenceEndpointSummaries_eq_horizontal]
  unfold horizontalIncidenceEndpointSummariesByElement horizontalIncidenceEndpointSummariesForElement
  apply incidenceFields_grouped_code_eq
  intro element member tag tagMember
  apply directSourceFinalHorizontalIncidenceCode_eq_iff decider symbols element _ tag tagMember
  simp only [CountedContractedIncidence.horizontalElementPairs, List.mem_flatMap, List.mem_map] at member
  obtain ⟨color, _, atom, atomMember, rfl⟩ := member
  exact List.mem_range.mp atomMember

/-- The finite record stream has one entry for every compiled incidence role. -/
theorem directSourceFinalSelectedIncidenceEndpointSummaries_length_roles
    (symbols : List encoding.Γ) :
    (directSourceFinalSelectedIncidenceEndpointSummaries decider symbols).length =
      (CountedContractedIncidence.roles
        (directSourceFinalCanonicalElementDegrees decider symbols)).length := by
  have contract := directSourceFinalCountedContraction_occurrenceKeyContract decider symbols
  unfold directSourceFinalSelectedIncidenceEndpointSummaries
  rw [CountedContractedIncidence.selectedValues_eq_map_alignedDatum _ _ _ _
    (directSourceFinalIncidenceEndpointSummaryColumns_length decider symbols)
    contract.1 contract.2, List.length_map]
  exact (CountedContractedIncidence.roles_length_eq_queryKeys _ _
    (directSourceFinalCountedContraction_elementColumns_length decider symbols)
    (directSourceFinalCountedContraction_degrees_valid decider symbols)).symm

end LeanTrominoes.PeriodicCNFStripReduction

end
