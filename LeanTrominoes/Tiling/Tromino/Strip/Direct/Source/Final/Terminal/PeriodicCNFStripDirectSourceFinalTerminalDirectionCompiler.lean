/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Carrier.PeriodicCNFStripDirectSourceFinalCarrierTerminalDirectionSuffixCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Direct.PeriodicCNFStripDirectSourceFinalDirectTerminalColumnCompiler

/-! # Compiling the complete final terminal-direction column -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


noncomputable def directSourceFinalTerminalDirectionRanksComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalTerminalDirectionRanks decider) := by
  change TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
    (fun symbols : List encoding.Γ =>
      directSourceFinalCrossoverTerminalDirectionRanks decider symbols ++
        directSourceFinalCarrierTerminalDirectionRankSuffix decider symbols)
  exact UnaryFieldEncoderMachine.appendComputableInPolyTime
    (directSourceFinalCrossoverTerminalDirectionRanksComputableInPolyTime
      decider)
    (directSourceFinalCarrierTerminalDirectionRankSuffixComputableInPolyTime
      decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
