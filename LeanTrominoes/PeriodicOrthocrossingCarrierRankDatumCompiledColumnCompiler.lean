/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCompiledFirstCrossingCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCompiledPrefixCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCompiledSecondCrossingCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCompiledSuffixCompiler

/-! # Column-major compiler for all fifty carrier rank-datum fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankDatumCompiledFields

open Computability Turing

/-- The exact column-major unary stream of all fifty selected carrier fields
is computable in polynomial time from the numeric route descriptors. -/
noncomputable def encodedColumnsComputableInPolyTime :
    TM2ComputableInPolyTime descriptorInputEncoding id encodedColumns := by
  let prefixAndFirst := TM2ListAppend.computableInPolyTime
    encodedPrefixComputableInPolyTime
    encodedFirstCrossingComputableInPolyTime
  let secondAndSuffix := TM2ListAppend.computableInPolyTime
    encodedSecondCrossingComputableInPolyTime
    encodedSuffixComputableInPolyTime
  let groups := TM2ListAppend.computableInPolyTime
    prefixAndFirst secondAndSuffix
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (encodeOutput₂ := id) (function₂ := encodedColumns) groups
    (fun descriptors => by
      rw [encodedColumns_eq_groups]
      simp only [List.append_assoc])

end CarrierRankDatumCompiledFields
end LeanTrominoes.PeriodicOrthocrossing

end
