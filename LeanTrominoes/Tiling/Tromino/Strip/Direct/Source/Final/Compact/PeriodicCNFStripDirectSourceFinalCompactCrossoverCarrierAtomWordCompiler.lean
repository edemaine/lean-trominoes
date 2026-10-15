/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Carrier.PeriodicCNFStripDirectSourceCarrierCompactAtomWordFinalBlockCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Crossover.PeriodicCNFStripDirectSourceCrossoverCompactAtomWordBlockCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Five.PeriodicCNFStripDirectSourceFinalFiveFamilyCompactAtomWordCompilerData

/-! # Compiler for the crossover/carrier compact prefix -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


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
