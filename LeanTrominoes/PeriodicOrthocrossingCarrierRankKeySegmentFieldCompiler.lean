/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyFieldProjectorNatStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyFieldCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeySegmentFieldData

/-! # Compiler for the selected carrier-key segment field -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeySegmentField

open Computability Turing

/-- The segment-index field of every deduplicated carrier-node
representative is emitted in unary in polynomial time. -/
noncomputable def valuesComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      UnaryFieldEncoderMachine.unaryFields values := by
  exact CarrierRankKeyField.valuesComputableInPolyTime
    .segment CarrierKeyFieldProjector.wordCorrect_segment

end CarrierRankKeySegmentField
end LeanTrominoes.PeriodicOrthocrossing

end
