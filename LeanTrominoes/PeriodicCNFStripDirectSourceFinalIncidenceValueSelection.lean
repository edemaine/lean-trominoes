/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalElementCodeNumberingSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCountedContractionPlanSemantics
import LeanTrominoes.UnaryKeyedValueLookupUniqueSemantics
import LeanTrominoes.TM2EmptyAlphabetListInputCompiler

/-! # Canonical element-order selection of arbitrary compiled incidence values -/

noncomputable section
namespace LeanTrominoes.PeriodicCNFStripReduction
open Computability Turing Gadget PeriodicThreeDM

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance selectedIncidenceValueStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) := decider.stackAlphabetFinite stack

/-- Use the same element/rank keys as the verified direction-word contraction. -/
def directSourceFinalSelectedIncidenceValues (symbols : List encoding.Γ) (values : List Nat) : List Nat :=
  UnaryKeyedValueLookup.values
    (CountedContractedIncidence.queryKeys
      (directSourceFinalCanonicalElementCodes decider symbols)
      (directSourceFinalCanonicalElementDegrees decider symbols))
    (CountedContractedIncidence.incidenceBlockKeys
      (directSourceFinalCanonicalIncidenceElementCodes decider symbols)) values

private theorem candidateKeys_length (symbols : List encoding.Γ) :
    (CountedContractedIncidence.incidenceBlockKeys
      (directSourceFinalCanonicalIncidenceElementCodes decider symbols)).length =
        (horizontalThreeDMProblemComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).incidenceTags.length := by
  rw [CountedContractedIncidence.incidenceBlockKeys, UnaryFieldStableOccurrenceKeys.keys_length,
    directSourceFinalCanonicalIncidenceElementCodes_eq_horizontal, List.length_map]

/-- Any compiled scalar field aligned with canonical incidence tags can use
this selection without constructing another machine. -/
noncomputable def directSourceFinalSelectedIncidenceValuesComputableInPolyTime
    (values : List encoding.Γ → List Nat)
    (aligned : ∀ symbols, (values symbols).length =
      (horizontalThreeDMProblemComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).incidenceTags.length)
    (compiler : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields values) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun symbols => directSourceFinalSelectedIncidenceValues decider symbols (values symbols)) := by
  classical
  exact if nonemptyAlphabet : Nonempty encoding.Γ then by
    letI : Inhabited encoding.Γ := ⟨Classical.choice nonemptyAlphabet⟩
    unfold directSourceFinalSelectedIncidenceValues
    exact UnaryKeyedValueLookup.valuesComputableInPolyTime id _ _ values
      (fun symbols => (aligned symbols).trans (candidateKeys_length decider symbols).symm)
      (CountedContractedIncidence.queryKeysComputableInPolyTimeOf id _ _
        (directSourceFinalCanonicalElementCodesComputableInPolyTime decider)
        (directSourceFinalCanonicalElementDegreesComputableInPolyTime decider))
      (TM2CompositionMachine.computableInPolyTime
        (directSourceFinalCanonicalIncidenceElementCodesComputableInPolyTime decider)
        UnaryFieldStableOccurrenceKeys.computableInPolyTime)
      compiler
  else by
    letI : IsEmpty encoding.Γ := ⟨fun symbol => nonemptyAlphabet ⟨symbol⟩⟩
    exact TM2EmptyAlphabetListInputCompiler.computableInPolyTime
      UnaryFieldEncoderMachine.unaryFields _

/-- Scalar values follow exactly the shared canonical incidence index ordering. -/
theorem directSourceFinalSelectedIncidenceValues_eq_grouped
    (symbols : List encoding.Γ) (values : List Nat)
    (aligned : values.length =
      (horizontalThreeDMProblemComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).incidenceTags.length) :
    directSourceFinalSelectedIncidenceValues decider symbols values =
      (directSourceFinalCanonicalElementCodes decider symbols).flatMap fun elementCode =>
        ((directSourceFinalCanonicalIncidenceElementCodes decider symbols).idxsOf elementCode).map
          (fun index => values.getD index 0) := by
  unfold directSourceFinalSelectedIncidenceValues
  rw [UnaryKeyedValueLookup.values_eq_map_alignedDatum _ _ _
    ((candidateKeys_length decider symbols).trans aligned.symm)
    (directSourceFinalCountedContraction_occurrenceKeyContract decider symbols).1
    (directSourceFinalCountedContraction_occurrenceKeyContract decider symbols).2,
    CountedContractedIncidence.incidenceBlockKeys_eq_candidateKeys]
  unfold UnaryKeyedValueLookup.alignedDatum
  simpa only [List.map_map, List.map_flatMap, Function.comp_def] using
    congrArg (List.map (fun index => values.getD index 0))
      (CountedContractedIncidence.queryKeys_map_candidateIndex_eq_flatMap_idxsOf_of_perm_expanded
        _ _ _ (directSourceFinalCountedContraction_elementColumns_length decider symbols)
        (directSourceFinalCountedContraction_degrees_valid decider symbols)
        (directSourceFinalCanonicalElementCodes_nodup decider symbols)
        (directSourceFinalCanonicalIncidenceElementCodes_perm_expanded decider symbols))

/-- The selected values are the actual incidence fields at each colored
element, in the exact order used by executable contraction. -/
theorem directSourceFinalSelectedIncidenceValues_map_eq_horizontal
    (symbols : List encoding.Γ) (field : IncidenceTag → Nat) :
    directSourceFinalSelectedIncidenceValues decider symbols
        ((horizontalThreeDMProblemComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).incidenceTags.map field) =
      (CountedContractedIncidence.horizontalElementPairs
        (horizontalThreeDMProblemComputed (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols))).flatMap
        (fun element => ((horizontalThreeDMProblemComputed
          (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).incidences element.1 element.2).map
            (fun incidence => field ⟨incidence.tripleIndex, element.1⟩)) := by
  rw [directSourceFinalSelectedIncidenceValues_eq_grouped decider symbols _ (List.length_map ..),
    directSourceFinalCanonicalElementCodes_eq_horizontal,
    directSourceFinalCanonicalIncidenceElementCodes_eq_horizontal]
  apply incidenceFields_grouped_code_eq
  intro element member tag tagMember
  apply directSourceFinalHorizontalIncidenceCode_eq_iff decider symbols element _ tag tagMember
  simp only [CountedContractedIncidence.horizontalElementPairs, List.mem_flatMap, List.mem_map] at member
  obtain ⟨color, _, atom, atomMember, rfl⟩ := member
  exact List.mem_range.mp atomMember

end LeanTrominoes.PeriodicCNFStripReduction
end
