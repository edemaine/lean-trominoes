/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierPackedSpanRouteTailRecordDecoderSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedRouteTailRecordStreamData

/-! # Semantics of the global retained carrier Figure 9 record stream -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

theorem retainedRouteTailRecordStream_eq_flatMap
    (descriptors : List RouteDescriptor) :
    retainedRouteTailRecordStream descriptors =
      (packedSpanCodes descriptors).flatMap fun code =>
        CarrierPackedSpanRouteTailRecords.blockOutput
          (UnaryFieldEncoderMachine.unaryField code) := by
  unfold retainedRouteTailRecordStream packedSpanStream
  exact CarrierPackedSpanRouteTailRecords.stream_unaryFields _

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing
