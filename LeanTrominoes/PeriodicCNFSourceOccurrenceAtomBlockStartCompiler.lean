/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.PeriodicCNFSourceOccurrenceAtomGroupSizeCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.UnaryPrefixSumsTime

/-! # Polynomial-time source atom-block starts -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceOccurrenceAtomBlockStarts

open Computability Turing

/-- Starting vertex index of every source atom's stable occurrence block. -/
def starts (source : SourceSplitRouteDescriptorTokens.Source) : List Nat :=
  PrefixSums.starts (SourceOccurrenceAtomGroupSizes.sizes source)

/-- Stable source atom-block starts are emitted as unary natural fields in
polynomial time. -/
noncomputable def unaryFieldsComputableInPolyTime :
    TM2ComputableInPolyTime
      SourceSplitRouteDescriptorTokens.finEncoding.encode
      UnaryFieldEncoderMachine.unaryFields starts := by
  let composed := TM2CompositionMachine.computableInPolyTime
    SourceOccurrenceAtomGroupSizes.unaryFieldsComputableInPolyTime
    UnaryPrefixSumsMachine.computableInPolyTime
  exact composed

end SourceOccurrenceAtomBlockStarts
end PeriodicCNF
end LeanTrominoes

end
