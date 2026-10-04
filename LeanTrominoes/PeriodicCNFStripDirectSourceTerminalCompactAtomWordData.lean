/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.DelimitedBinaryWordsDecode
import LeanTrominoes.PeriodicCNFStripDirectSourceTerminalCompactAtomWordTokenData

/-! # Semantic source-terminal compact atom words for direct sources -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Decode the physical source-terminal compact-word stream. -/
def directSourceTerminalCompactAtomWords
    (symbols : List encoding.Γ) : DelimitedBinaryWords.Input :=
  DelimitedBinaryWords.decodeOrEmpty
    (directSourceTerminalCompactAtomWordTokens decider symbols)

end PeriodicCNFStripReduction
end LeanTrominoes

end
