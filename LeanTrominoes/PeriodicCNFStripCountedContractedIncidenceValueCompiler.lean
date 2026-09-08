/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.FiniteAlphabetKeyedValueLookupCompiler
import LeanTrominoes.FiniteAlphabetKeyedValueLookupUniqueSemantics
import LeanTrominoes.PeriodicCNFStripCountedContractedIncidenceRankedBodySemantics

/-! # Counted incidence lookup for arbitrary finite endpoint records -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction.CountedContractedIncidence

open Computability Turing

variable {Value : Type} [Fintype Value] [Inhabited Value]

/-- Select finite records with the same stable occurrence keys as incidence
word contraction. -/
def selectedValues (elementCodes sizes incidenceElementCodes : List Nat)
    (values : List Value) : List Value :=
  FiniteAlphabetKeyedValueLookup.values
    (queryKeys elementCodes sizes) (incidenceBlockKeys incidenceElementCodes) values

/-- Unique covering occurrence keys select exactly one aligned record for
 each query. -/
theorem selectedValues_eq_map_alignedDatum
    (elementCodes sizes incidenceCodes : List Nat) (values : List Value)
    (aligned : incidenceCodes.length = values.length)
    (unique : (incidenceBlockKeys incidenceCodes).Nodup)
    (present : ∀ query ∈ queryKeys elementCodes sizes,
      query ∈ incidenceBlockKeys incidenceCodes) :
    selectedValues elementCodes sizes incidenceCodes values =
      (queryKeys elementCodes sizes).map
        (FiniteAlphabetKeyedValueLookup.alignedDatum (incidenceBlockKeys incidenceCodes) values) := by
  unfold selectedValues
  exact FiniteAlphabetKeyedValueLookup.values_eq_map_alignedDatum _ _ _
    (by simpa only [incidenceBlockKeys, UnaryFieldStableOccurrenceKeys.keys_length] using aligned)
    unique present

omit [Fintype Value] in
private theorem queryBlock_map_alignedDatum
    (incidenceCodes : List Nat) (values : List Value)
    (countLeThree : ∀ code ∈ incidenceCodes, incidenceCodes.count code ≤ 3)
    (code size : Nat) (valid : size = 2 ∨ size = 3)
    (sizeEq : size = incidenceCodes.count code) :
    (queryBlock code size).map
        (FiniteAlphabetKeyedValueLookup.alignedDatum
          (StableOccurrenceRanks.candidateKeys incidenceCodes) values) =
      (incidenceCodes.idxsOf code).map (fun index => values.getD index default) := by
  rw [queryBlock_eq_map_range code size valid, List.map_map]
  have rangeLength : size = (incidenceCodes.idxsOf code).length := by
    simpa using sizeEq
  rw [rangeLength]
  rw [show (incidenceCodes.idxsOf code).map (fun index => values.getD index default) =
      ((List.range (incidenceCodes.idxsOf code).length).map
        (fun rank => (incidenceCodes.idxsOf code).getD rank 0)).map
        (fun index => values.getD index default) by rw [List.map_range_getD]]
  rw [List.map_map]
  apply List.map_congr_left
  intro rank member
  dsimp only [Function.comp_apply]
  unfold FiniteAlphabetKeyedValueLookup.alignedDatum
  have rankLt : rank < incidenceCodes.count code := by
    rw [← sizeEq, rangeLength]
    exact List.mem_range.mp member
  rw [StableOccurrenceRanks.candidateKeys_idxOf_rank incidenceCodes countLeThree code rank rankLt]

/-- Stable finite-value lookup groups records by raw element code and keeps
presentation order inside each degree-two or degree-three group. -/
theorem selectedValues_eq_grouped
    (elementCodes sizes incidenceCodes : List Nat) (values : List Value)
    (columnsAligned : elementCodes.length = sizes.length)
    (valuesAligned : incidenceCodes.length = values.length)
    (degreesValid : ∀ size ∈ sizes, size = 2 ∨ size = 3)
    (codesNodup : elementCodes.Nodup)
    (incidencePermutation : incidenceCodes.Perm
      (expandedElementCodes (elementCodes.zip sizes))) :
    selectedValues elementCodes sizes incidenceCodes values =
      elementCodes.flatMap (fun code =>
        (incidenceCodes.idxsOf code).map (fun index => values.getD index default)) := by
  have contract := occurrenceKeyContract_of_perm_expanded
    elementCodes sizes incidenceCodes columnsAligned degreesValid codesNodup incidencePermutation
  unfold selectedValues
  rw [FiniteAlphabetKeyedValueLookup.values_eq_map_alignedDatum _ _ _
    (by simpa only [incidenceBlockKeys, UnaryFieldStableOccurrenceKeys.keys_length] using valuesAligned)
    contract.1 contract.2, incidenceBlockKeys_eq_candidateKeys]
  let pairs := elementCodes.zip sizes
  have pairCodes : pairs.map Prod.fst = elementCodes := List.map_fst_zip (by omega)
  have pairSizes : pairs.map Prod.snd = sizes := List.map_snd_zip (by omega)
  have pairCodesNodup : (pairs.map Prod.fst).Nodup := by
    rw [pairCodes]
    exact codesNodup
  have pairDegrees : ∀ pair ∈ pairs, pair.2 = 2 ∨ pair.2 = 3 := by
    intro pair member
    apply degreesValid pair.2
    rw [← pairSizes]
    exact List.mem_map.mpr ⟨pair, member, rfl⟩
  have countLeThree := incidenceElementCodes_count_le_three_of_perm_expanded
    pairs incidenceCodes pairCodesNodup pairDegrees incidencePermutation
  rw [queryKeys_eq_pairQueryKeys _ _ columnsAligned degreesValid]
  change (pairQueryKeys pairs).map _ = _
  unfold pairQueryKeys
  rw [List.map_flatMap]
  calc
    _ = pairs.flatMap (fun pair =>
        (incidenceCodes.idxsOf pair.1).map (fun index => values.getD index default)) := by
      apply List.flatMap_congr
      intro pair member
      exact queryBlock_map_alignedDatum incidenceCodes values countLeThree pair.1 pair.2
        (pairDegrees pair member)
        (incidenceElementCodes_count_eq_degree_of_perm_expanded
          pairs incidenceCodes pairCodesNodup incidencePermutation pair member).symm
    _ = _ := by
      simpa only [List.flatMap_map, Function.comp_def] using
        congrArg (fun codes : List Nat => codes.flatMap (fun code =>
        (incidenceCodes.idxsOf code).map (fun index => values.getD index default))) pairCodes

/-- Independently compiled identity, degree, and finite-record columns
instantiate counted record grouping in polynomial time. -/
noncomputable def selectedValuesComputableInPolyTimeOf
    {Source InputSymbol : Type} [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeSource : Source → List InputSymbol)
    (elementCodes sizes incidenceCodes : Source → List Nat)
    (values : Source → List Value)
    (aligned : ∀ source, (incidenceCodes source).length = (values source).length)
    (elementCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields elementCodes)
    (sizeCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields sizes)
    (incidenceCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields incidenceCodes)
    (valueCompiler : TM2ComputableInPolyTime encodeSource id values) :
    TM2ComputableInPolyTime encodeSource id (fun source =>
      selectedValues (elementCodes source) (sizes source) (incidenceCodes source) (values source)) := by
  unfold selectedValues
  exact FiniteAlphabetKeyedValueLookup.valuesComputableInPolyTime encodeSource
    (fun source => queryKeys (elementCodes source) (sizes source))
    (fun source => incidenceBlockKeys (incidenceCodes source)) values
    (fun source => by
      simpa only [incidenceBlockKeys, UnaryFieldStableOccurrenceKeys.keys_length] using aligned source)
    (queryKeysComputableInPolyTimeOf encodeSource elementCodes sizes elementCompiler sizeCompiler)
    (incidenceBlockKeysComputableInPolyTimeOf encodeSource incidenceCodes incidenceCompiler)
    valueCompiler

end LeanTrominoes.PeriodicCNFStripReduction.CountedContractedIncidence

end
