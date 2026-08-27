/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierPackedSpanRouteTailRecordDecoder
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPackedSpanStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedRouteTailRecordStreamData

/-! # Compiler for the global retained carrier Figure 9 record stream -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

open Computability Turing

noncomputable def retainedRouteTailRecordStreamComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding id
      retainedRouteTailRecordStream := by
  change TM2ComputableInPolyTime InputEncoding id
    (fun descriptors =>
      CarrierPackedSpanRouteTailRecords.stream
        (packedSpanStream descriptors))
  exact TM2CompositionMachine.computableInPolyTime
    packedSpanStreamComputableInPolyTime
    CarrierPackedSpanRouteTailRecords.streamComputableInPolyTime

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing

end
