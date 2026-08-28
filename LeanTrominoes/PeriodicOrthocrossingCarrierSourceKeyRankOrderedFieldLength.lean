/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalSuccessorData
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRankOrderedFieldData

/-! # Length alignment for globally ranked carrier source-key fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSourceKeyRankOrderedFields

private theorem fixedFieldRows_length (width : Nat)
    (input : DelimitedBinaryWords.Input) :
    (DelimitedBinaryWordFixedFieldRowExpansion.rows width input).words.length =
      input.words.length * width := by
  rcases input with ⟨words⟩
  unfold DelimitedBinaryWordFixedFieldRowExpansion.rows
  induction words with
  | nil => simp
  | cons row rows induction =>
      simp [induction, Nat.succ_mul, Nat.add_comm]

theorem selectedFields_length (descriptors : List RouteDescriptor) :
    (CarrierSourceKeyRepresentativeFieldLookup.selectedFields
        descriptors).length =
      (CarrierRankGlobal.ranks descriptors).length * fieldCount := by
  unfold CarrierSourceKeyRepresentativeFieldLookup.selectedFields
    LastTrueUnaryValueLookupMachine.lookups
  rw [List.length_map]
  unfold CarrierSourceKeyRepresentativeFieldLookup.expandedRows
  rw [fixedFieldRows_length]
  rw [CarrierRankGlobalSuccessor.ranks_length]
  rfl

end CarrierSourceKeyRankOrderedFields
end LeanTrominoes.PeriodicOrthocrossing
