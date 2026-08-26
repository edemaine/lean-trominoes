/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyLastContributionCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.UnaryPrefixSumsTime

/-! # Prefix starts of carrier-key last-occurrence contributions -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeyContributionStarts

open Turing

/-- Prefix sum immediately before each possible final-key contribution. -/
def starts (descriptors : List RouteDescriptor) : List Nat :=
  PrefixSums.starts
    (CarrierRankKeyLastContributions.contributions descriptors)

noncomputable def unaryFieldsComputableInPolyTime :
    TM2ComputableInPolyTime CarrierRankKeyEquality.InputEncoding
      UnaryFieldEncoderMachine.unaryFields starts := by
  let composed := TM2CompositionMachine.computableInPolyTime
    CarrierRankKeyLastContributions.unaryFieldsComputableInPolyTime
    UnaryPrefixSumsMachine.computableInPolyTime
  exact composed

end CarrierRankKeyContributionStarts
end LeanTrominoes.PeriodicOrthocrossing

end
