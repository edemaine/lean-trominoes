/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFanOccurrenceDataCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFanQueryKeySemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceCandidateKeyNodup
import LeanTrominoes.UnaryKeyedValueLookupUniqueSemantics

/-! # Semantics of selected direct final fan occurrence data -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Declarative occurrence records at the unique candidate-key positions of
the three fan queries emitted for every final occurrence. -/
def directSourceFinalFanSelectedOccurrenceDataExpected
    (symbols : List encoding.Γ) : List FinalFanOccurrenceData :=
  (directSourceFinalFanQueryKeys decider symbols).map fun query =>
    (directSourceFinalVariableOccurrenceData decider symbols).getD
      ((directSourceFinalOccurrenceCandidateKeys decider symbols).idxOf query)
      default

/-- Keyed lookup is pointwise unique-candidate index recovery. -/
theorem directSourceFinalFanSelectedOccurrenceCodes_eq_map_alignedDatum
    (symbols : List encoding.Γ) :
    directSourceFinalFanSelectedOccurrenceCodes decider symbols =
      (directSourceFinalFanQueryKeys decider symbols).map
        (UnaryKeyedValueLookup.alignedDatum
          (directSourceFinalOccurrenceCandidateKeys decider symbols)
          (directSourceFinalFanOccurrenceCandidateCodes decider symbols)) := by
  unfold directSourceFinalFanSelectedOccurrenceCodes
  apply UnaryKeyedValueLookup.values_eq_map_alignedDatum
  · exact (directSourceFinalOccurrenceCandidateKeys_length
      decider symbols).trans
        (directSourceFinalFanOccurrenceCandidateCodes_length
          decider symbols).symm
  · exact directSourceFinalOccurrenceCandidateKeys_nodup decider symbols
  · intro query queryMember
    exact directSourceFinalFanQueryKey_mem_candidateKeys
      decider symbols query queryMember

private theorem directSourceFinalFanAlignedDatum_eq_code
    (symbols : List encoding.Γ) (query : Nat)
    (queryMember : query ∈ directSourceFinalFanQueryKeys decider symbols) :
    UnaryKeyedValueLookup.alignedDatum
        (directSourceFinalOccurrenceCandidateKeys decider symbols)
        (directSourceFinalFanOccurrenceCandidateCodes decider symbols)
        query =
      finalFanOccurrenceDataCode
        ((directSourceFinalVariableOccurrenceData decider symbols).getD
          ((directSourceFinalOccurrenceCandidateKeys
            decider symbols).idxOf query) default) := by
  have candidateMember := directSourceFinalFanQueryKey_mem_candidateKeys
    decider symbols query queryMember
  let index :=
    (directSourceFinalOccurrenceCandidateKeys decider symbols).idxOf query
  have indexLt : index <
      (directSourceFinalOccurrenceCandidateKeys decider symbols).length :=
    List.idxOf_lt_length_iff.mpr candidateMember
  have occurrenceIndexLt : index <
      (directSourceFinalVariableOccurrenceData decider symbols).length := by
    rw [directSourceFinalVariableOccurrenceData_length,
      ← directSourceFinalOccurrenceCandidateKeys_length]
    exact indexLt
  have mappedIndexLt : index <
      ((directSourceFinalVariableOccurrenceData decider symbols).map
        finalFanOccurrenceDataCode).length := by
    simpa using occurrenceIndexLt
  unfold UnaryKeyedValueLookup.alignedDatum
    directSourceFinalFanOccurrenceCandidateCodes
  change ((directSourceFinalVariableOccurrenceData decider symbols).map
      finalFanOccurrenceDataCode).getD index 0 =
    finalFanOccurrenceDataCode
      ((directSourceFinalVariableOccurrenceData decider symbols).getD
        index default)
  rw [List.getD_eq_getElem _ _ mappedIndexLt, List.getElem_map,
    List.getD_eq_getElem _ _ occurrenceIndexLt]

/-- Selected unary codes are exactly encodings of the uniquely keyed final
occurrence records. -/
theorem directSourceFinalFanSelectedOccurrenceCodes_eq_expected_map
    (symbols : List encoding.Γ) :
    directSourceFinalFanSelectedOccurrenceCodes decider symbols =
      (directSourceFinalFanSelectedOccurrenceDataExpected
        decider symbols).map finalFanOccurrenceDataCode := by
  rw [directSourceFinalFanSelectedOccurrenceCodes_eq_map_alignedDatum]
  unfold directSourceFinalFanSelectedOccurrenceDataExpected
  rw [List.map_map]
  apply List.map_congr_left
  intro query queryMember
  exact directSourceFinalFanAlignedDatum_eq_code
    decider symbols query queryMember

/-- Decoding removes the finite role encoding and exposes exactly the three
uniquely keyed occurrence records per final occurrence. -/
theorem directSourceFinalFanSelectedOccurrenceData_eq_expected
    (symbols : List encoding.Γ) :
    directSourceFinalFanSelectedOccurrenceData decider symbols =
      directSourceFinalFanSelectedOccurrenceDataExpected decider symbols := by
  unfold directSourceFinalFanSelectedOccurrenceData
  rw [directSourceFinalFanSelectedOccurrenceCodes_eq_expected_map,
    decodedFinalFanOccurrenceData_map_code]

end LeanTrominoes.PeriodicCNFStripReduction

end
