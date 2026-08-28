/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftLeftSourceKeyRepresentativeWordStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingCrossoverCompactAtomWordCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Compiler for representative canonical crossover compact atom words -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CanonicalCrossingRepresentativeCompactAtomWordStream

open Computability Turing

abbrev descriptorInputEncoding :
    List RouteDescriptor → List DelimitedBinaryWords.Token :=
  CanonicalCrossingShiftLeftSourceKeyRepresentativeWordStream.descriptorInputEncoding

/-- Expand every unique reconstructed crossing source pair through the fixed
Figure 8(b) crossover-role table. -/
def emittedTokens (descriptors : List RouteDescriptor) :
    List DelimitedBinaryWords.Token :=
  CrossoverCompactAtomWords.tokens
    (CanonicalCrossingShiftLeftSourceKeyRepresentativeWordStream.emittedTokens
      descriptors)

noncomputable def emittedTokensComputableInPolyTime :
    TM2ComputableInPolyTime descriptorInputEncoding id emittedTokens := by
  change TM2ComputableInPolyTime descriptorInputEncoding id
    (fun descriptors => CrossoverCompactAtomWords.tokens
      (CanonicalCrossingShiftLeftSourceKeyRepresentativeWordStream.emittedTokens
        descriptors))
  exact TM2CompositionMachine.computableInPolyTime
    CanonicalCrossingShiftLeftSourceKeyRepresentativeWordStream.emittedTokensComputableInPolyTime
    CrossoverCompactAtomWords.tokensComputableInPolyTime

end CanonicalCrossingRepresentativeCompactAtomWordStream
end LeanTrominoes.PeriodicOrthocrossing

end
