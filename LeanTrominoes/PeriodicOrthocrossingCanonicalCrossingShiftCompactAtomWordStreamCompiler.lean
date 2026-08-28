/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordOccurrenceSlotPairProductCompiler
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftLeftSourceKeyStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingCrossoverCompactAtomWordCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairFieldTagCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Compiler for compact crossover words from common-shift candidates -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CanonicalCrossingShiftCompactAtomWordStream

open Computability Turing

/-- Compile descriptor words through slot expansion, ordered pairing,
field tagging, and the common-shift source-key emitter. -/
def sourceTokens (input : DelimitedBinaryWords.Input) :
    List DelimitedBinaryWords.Token :=
  CanonicalCrossingShiftLeftSourceKeyStream.emittedDescriptorStream input

noncomputable def sourceTokensComputableInPolyTime :
    TM2ComputableInPolyTime
      DelimitedBinaryWords.finEncoding.encode id sourceTokens := by
  change TM2ComputableInPolyTime
    DelimitedBinaryWords.finEncoding.encode id
    CanonicalCrossingShiftLeftSourceKeyStream.emittedDescriptorStream
  exact CanonicalCrossingShiftLeftSourceKeyStream.emittedDescriptorStreamComputableInPolyTime

/-- Apply the fixed 58-role crossover expander to every emitted guarded
source-key candidate. -/
def emittedTokens (input : DelimitedBinaryWords.Input) :
    List DelimitedBinaryWords.Token :=
  CrossoverCompactAtomWords.tokens (sourceTokens input)

noncomputable def emittedTokensComputableInPolyTime :
    TM2ComputableInPolyTime
      DelimitedBinaryWords.finEncoding.encode id emittedTokens := by
  change TM2ComputableInPolyTime
    DelimitedBinaryWords.finEncoding.encode id
    (fun input => CrossoverCompactAtomWords.tokens (sourceTokens input))
  exact TM2CompositionMachine.computableInPolyTime
    sourceTokensComputableInPolyTime
    CrossoverCompactAtomWords.tokensComputableInPolyTime

end CanonicalCrossingShiftCompactAtomWordStream
end LeanTrominoes.PeriodicOrthocrossing

end
