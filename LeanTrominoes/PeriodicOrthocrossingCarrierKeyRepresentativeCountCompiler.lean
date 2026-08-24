/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordTrueCountCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRepresentativeRowRecipeCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Unary occurrence counts of retained carrier keys -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing

open Computability Turing

/-- Number of active terminal or crossing-boundary candidates on every
retained carrier key, in last-occurrence representative order. -/
def paddedCarrierKeyRepresentativeCounts
    (descriptors : List RouteDescriptor) : List Nat :=
  DelimitedBinaryWordTrueCounts.counts
    (paddedCarrierKeyRepresentativeRows descriptors)

/-- The verified representative-row recipe followed by unary true counting
computes all retained carrier-key occurrence counts in polynomial time. -/
noncomputable def
    paddedCarrierKeyRepresentativeCountUnaryFieldsComputableInPolyTime :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      UnaryFieldEncoderMachine.unaryFields
      paddedCarrierKeyRepresentativeCounts := by
  unfold paddedCarrierKeyRepresentativeCounts
  exact TM2CompositionMachine.computableInPolyTime
    paddedCarrierKeyRepresentativeRowsRecipeComputableInPolyTime
    DelimitedBinaryWordTrueCounts.computableInPolyTime

end LeanTrominoes.PeriodicOrthocrossing

end
