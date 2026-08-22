/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupTime
import LeanTrominoes.LastTrueUnaryValueLookupValidity
import LeanTrominoes.PeriodicCNFSourceOccurrenceAtomContributionStartCompiler
import LeanTrominoes.PeriodicCNFSourceOccurrenceAtomEqualityRowSemantics
import LeanTrominoes.PeriodicCNFSourceOccurrenceAtomRankSemantics
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2ForkMachineTime
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Source atom-block starts in occurrence order -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceOccurrenceAtomPerOccurrenceBlockStarts

open Turing

local instance : Inhabited
    SourceSplitRouteDescriptorTokens.finEncoding.Γ :=
  ⟨PartrecToTM2.Γ'.bit0⟩

private theorem selectedValues_length {ranks sizes : List Nat}
    (valid : UnarySuccessorEqualityFilterMachine.Valid ranks sizes) :
    (UnarySuccessorEqualityFilterMachine.selectedValues ranks sizes).length =
      ranks.length := by
  induction valid with
  | nil => rfl
  | cons _ _ induction =>
      simp [UnarySuccessorEqualityFilterMachine.selectedValues, induction]

theorem contributionStarts_length
    (source : SourceSplitRouteDescriptorTokens.Source) :
    (SourceOccurrenceAtomContributionStarts.starts source).length =
      SourceOccurrenceAtomEqualityRows.occurrenceCount source := by
  rw [SourceOccurrenceAtomContributionStarts.starts,
    PrefixSums.starts_length]
  have contributionLength := selectedValues_length
    (SourceOccurrenceAtomLastContributions.filterInput source).valid
  have contributionLength' :
      (SourceOccurrenceAtomLastContributions.contributions source).length =
        (SourceOccurrenceAtomRanks.ranks source).length := by
    exact contributionLength
  rw [contributionLength', SourceOccurrenceAtomRanks.ranks_eq_map_zipIdx]
  simp [SourceOccurrenceAtomEqualityRows.occurrenceCount,
    SourceOccurrenceAtomRanks.occurrenceAtoms]

theorem equalityRows_forall_length
    (source : SourceSplitRouteDescriptorTokens.Source) :
    (SourceOccurrenceAtomEqualityRows.rows source).words.Forall fun row =>
      row.length = SourceOccurrenceAtomEqualityRows.occurrenceCount source := by
  rw [SourceOccurrenceAtomEqualityRows.rows_words,
    List.forall_iff_forall_mem]
  intro row rowMem
  unfold SourceOccurrenceAtomEqualityRows.semanticRows at rowMem
  rcases List.mem_map.mp rowMem with ⟨first, firstMem, rfl⟩
  simp [SourceOccurrenceAtomEqualityRows.occurrenceCount]

/-- Equality rows and contribution starts have one column/value per source
literal occurrence. -/
theorem equalityRows_forall_starts_length
    (source : SourceSplitRouteDescriptorTokens.Source) :
    (SourceOccurrenceAtomEqualityRows.rows source).words.Forall fun row =>
      row.length =
        (SourceOccurrenceAtomContributionStarts.starts source).length := by
  rw [contributionStarts_length]
  exact equalityRows_forall_length source

def lookupInput (source : SourceSplitRouteDescriptorTokens.Source) :
    LastTrueUnaryValueLookupMachine.Input where
  rows := (SourceOccurrenceAtomEqualityRows.rows source).words
  values := SourceOccurrenceAtomContributionStarts.starts source
  valid := LastTrueUnaryValueLookupMachine.RowsValid.of_forall_length
    (equalityRows_forall_starts_length source)

/-- The start of the atom block containing each source occurrence, listed in
source occurrence order. -/
def starts (source : SourceSplitRouteDescriptorTokens.Source) : List Nat :=
  LastTrueUnaryValueLookupMachine.lookups
    (lookupInput source).rows (lookupInput source).values

/-- Per-occurrence source atom-block starts are emitted as unary fields in
polynomial time. -/
noncomputable def unaryFieldsComputableInPolyTime :
    TM2ComputableInPolyTime
      SourceSplitRouteDescriptorTokens.finEncoding.encode
      UnaryFieldEncoderMachine.unaryFields starts := by
  let paired := TM2ForkMachine.computableInPolyTime
    SourceOccurrenceAtomEqualityRows.rowsComputableInPolyTime
    SourceOccurrenceAtomContributionStarts.unaryFieldsComputableInPolyTime
  let prepared : TM2ComputableInPolyTime
      SourceSplitRouteDescriptorTokens.finEncoding.encode
      LastTrueUnaryValueLookupMachine.encode lookupInput :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq paired
      (fun _ => by rfl)
  let lookedUp := TM2CompositionMachine.computableInPolyTime prepared
    LastTrueUnaryValueLookupMachine.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq lookedUp
    (fun _ => by rfl)

end SourceOccurrenceAtomPerOccurrenceBlockStarts
end PeriodicCNF
end LeanTrominoes

end
