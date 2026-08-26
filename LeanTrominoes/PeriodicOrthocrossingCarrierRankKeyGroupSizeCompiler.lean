/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordTrueCountCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyEqualityRowCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Multiplicities of compiled carrier keys -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeyGroupSizes

open Turing

abbrev InputEncoding := CarrierRankKeyEquality.InputEncoding

/-- Full multiplicity of the aggregate key at each compact row. -/
def sizes (descriptors : List RouteDescriptor) : List Nat :=
  DelimitedBinaryWordTrueCounts.counts
    (CarrierRankKeyEqualityRows.rows descriptors)

noncomputable def unaryFieldsComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding
      UnaryFieldEncoderMachine.unaryFields sizes := by
  let composed := TM2CompositionMachine.computableInPolyTime
    CarrierRankKeyEqualityRows.rowsComputableInPolyTime
    DelimitedBinaryWordTrueCounts.computableInPolyTime
  exact composed

end CarrierRankKeyGroupSizes
end LeanTrominoes.PeriodicOrthocrossing

end
