/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Compact.PeriodicCNFStripDirectSourceFinalCompactBendRoutedClauseAtomWordCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Routed.PeriodicCNFStripDirectSourceRoutedVariableCompactAtomWordCompiler

/-! # Compiler for the final three compact atom-word families -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- The final three compact atom-word families are polynomial-time
computable. -/
noncomputable def
    directSourceFinalCompactBendRoutedSuffixAtomWordsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) DelimitedBinaryWords.Input
      encoding.Γ DelimitedBinaryWords.Token
      id DelimitedBinaryWords.finEncoding.encode
      (directSourceFinalCompactBendRoutedSuffixAtomWords decider) := by
  change @TM2ComputableInPolyTime
    (List encoding.Γ) DelimitedBinaryWords.Input
    encoding.Γ DelimitedBinaryWords.Token
    id DelimitedBinaryWords.finEncoding.encode
    (fun symbols => DelimitedBinaryWords.append
      (directSourceFinalCompactBendRoutedClauseAtomWords decider symbols)
      (directSourceFinalRoutedVariableCompactAtomWords decider symbols))
  exact DelimitedBinaryWords.appendComputableInPolyTime
    (directSourceFinalCompactBendRoutedClauseAtomWordsComputableInPolyTime
      decider)
    (directSourceFinalRoutedVariableCompactAtomWordsComputableInPolyTime
      decider)

end PeriodicCNFStripReduction
end LeanTrominoes

end
