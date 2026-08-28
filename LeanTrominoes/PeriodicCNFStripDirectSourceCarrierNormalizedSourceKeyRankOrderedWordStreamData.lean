/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierNormalizedSourceKeyRankOrderedFieldData
import LeanTrominoes.PeriodicOrthocrossingCarrierSourcePairFieldFormatterData

/-! # Direct-source normalized carrier source-pair words in rank order -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Format every globally rank-ordered normalized carrier source-pair field
block as one guarded delimited word. -/
def directSourceCarrierNormalizedSourceKeyRankOrderedWordTokens
    (symbols : List encoding.Γ) : List DelimitedBinaryWords.Token :=
  CarrierSourcePairFieldFormatter.output
    (UnaryFieldEncoderMachine.unaryFields
      (directSourceCarrierNormalizedSourceKeyRankOrderedFields
        decider symbols))

end PeriodicCNFStripReduction
end LeanTrominoes

end
