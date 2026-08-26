/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPrefixTrueCountTime
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyEqualityRowCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Stable occurrence ranks of compiled carrier keys -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeyOccurrenceRanks

open Turing

abbrev InputEncoding := CarrierRankKeyEquality.InputEncoding

/-- Presentation rank of each aggregate key among its equal predecessors. -/
def ranks (descriptors : List RouteDescriptor) : List Nat :=
  DelimitedBinaryWordPrefixTrueCounts.counts
    (CarrierRankKeyEqualityRows.rows descriptors)

noncomputable def unaryFieldsComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding
      UnaryFieldEncoderMachine.unaryFields ranks := by
  let composed := TM2CompositionMachine.computableInPolyTime
    CarrierRankKeyEqualityRows.rowsComputableInPolyTime
    DelimitedBinaryWordPrefixTrueCountMachine.computableInPolyTime
  exact composed

end CarrierRankKeyOccurrenceRanks
end LeanTrominoes.PeriodicOrthocrossing

end
