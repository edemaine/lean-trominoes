/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairProductTime
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairFieldTagCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Terminal-pair tags for the carrier-key axis compiler -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyAxisTerminalTags

open Computability Turing

def tags (input : DelimitedBinaryWords.Input) :
    List RouteDescriptorPairFieldTags.Token :=
  RouteDescriptorPairFieldTags.inputTokens
    (DelimitedBinaryWordPairProductMachine.pairs input)

noncomputable def tagsComputableInPolyTime :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      tags := by
  change TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
    (fun input => RouteDescriptorPairFieldTags.inputTokens
      (DelimitedBinaryWordPairProductMachine.pairs input))
  exact TM2CompositionMachine.computableInPolyTime
    DelimitedBinaryWordPairProductMachine.computableInPolyTime
    RouteDescriptorPairFieldTags.inputTokensComputableInPolyTime

end CarrierKeyAxisTerminalTags
end LeanTrominoes.PeriodicOrthocrossing

end
