/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierCompactAtomWordFinalBlockCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceCrossoverCompactAtomWordBlockCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFiveFamilyCompactAtomWordCompilerData

/-! # Compiler for the crossover/carrier compact prefix -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directCompactCrossoverCarrierStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The first two final compact atom-word families are polynomial-time
computable. -/
noncomputable def
    directSourceFinalCompactCrossoverCarrierAtomWordsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) DelimitedBinaryWords.Input
      encoding.Γ DelimitedBinaryWords.Token
      id DelimitedBinaryWords.finEncoding.encode
      (directSourceFinalCompactCrossoverCarrierAtomWords decider) := by
  change @TM2ComputableInPolyTime
    (List encoding.Γ) DelimitedBinaryWords.Input
    encoding.Γ DelimitedBinaryWords.Token
    id DelimitedBinaryWords.finEncoding.encode
    (fun symbols => DelimitedBinaryWords.append
      (directSourceFinalCompactCrossoverAtomWords decider symbols)
      (directSourceFinalCompactCarrierAtomWords decider symbols))
  exact DelimitedBinaryWords.appendComputableInPolyTime
    (directSourceFinalCompactCrossoverAtomWordsComputableInPolyTime decider)
    (directSourceFinalCompactCarrierAtomWordsComputableInPolyTime decider)

end PeriodicCNFStripReduction
end LeanTrominoes

end
