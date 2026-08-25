/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordRepresentativeSquareSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderCandidateStreamLength
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderRepresentativeRowCompiler

/-! # Lengths of carrier order-coordinate representative rows -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierOrderRepresentativeRows

/-- Every sentinel-free representative row spans the complete
sentinel-extended candidate value stream. -/
theorem rows_forall_values_length (keepPositive : Bool)
    (descriptors : List RouteDescriptor) :
    (rows descriptors).words.Forall fun row =>
      row.length =
        (CarrierOrderCandidateFieldStream.valuesWithSentinel
          keepPositive descriptors).length := by
  unfold rows DelimitedBinaryWordsDropLastMachine.dropLast
  rw [DelimitedBinaryWordRepresentativeSquare.rows_eq,
    LastRepresentativeEqualityRows.rows_equalityRows,
    List.forall_iff_forall_mem]
  intro row rowMember
  have rowMember' := List.dropLast_subset _ rowMember
  rcases List.mem_map.mp rowMember' with ⟨word, _, rfl⟩
  rw [CarrierOrderCandidateFieldStream.valuesWithSentinel_length]
  simp [LastRepresentativeEqualityRows.equalityRow]

end CarrierOrderRepresentativeRows
end LeanTrominoes.PeriodicOrthocrossing
