/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierPackedSpanRouteTailRecordDecoderData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPackedSpanData

/-! # Global retained carrier Figure 9 tail-record stream -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

/-- Decode every packed carrier-pair matrix field in row-major order. -/
def retainedRouteTailRecordStream (descriptors : List RouteDescriptor) :
    List PeriodicCNFStripReduction.HorizontalRoutedRouteTailRecord.Token :=
  CarrierPackedSpanRouteTailRecords.stream (packedSpanStream descriptors)

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing
