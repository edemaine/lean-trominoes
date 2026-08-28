/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordGuardedPairMergeCompiler
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingLeftSourceKeyRecipeEmitterCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Compiler for merged canonical-left crossing source keys -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CanonicalCrossingLeftSourceKeyEmitter

open Computability Turing

def emittedTokens
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List DelimitedBinaryWords.Token :=
  DelimitedBinaryWordGuardedPairMerge.tokens
    (CanonicalCrossingLeftSourceKeyRecipeEmitter.emittedTokens tokens)

noncomputable def emittedTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id emittedTokens := by
  change TM2ComputableInPolyTime id id
    (fun tokens => DelimitedBinaryWordGuardedPairMerge.tokens
      (CanonicalCrossingLeftSourceKeyRecipeEmitter.emittedTokens tokens))
  exact TM2CompositionMachine.computableInPolyTime
    CanonicalCrossingLeftSourceKeyRecipeEmitter.emittedTokensComputableInPolyTime
    DelimitedBinaryWordGuardedPairMerge.tokensComputableInPolyTime

end CanonicalCrossingLeftSourceKeyEmitter
end LeanTrominoes.PeriodicOrthocrossing

end
