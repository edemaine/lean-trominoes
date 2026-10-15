/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Carrier.PeriodicCNFStripDirectSourceFinalCarrierTerminalRadialSuffixCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Direct.PeriodicCNFStripDirectSourceFinalDirectTerminalColumnCompiler

/-! # Compiling the complete final terminal-radial column -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


noncomputable def directSourceFinalTerminalRadialLengthsComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalTerminalRadialLengths decider) := by
  change TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
    (fun symbols : List encoding.Γ =>
      directSourceFinalCrossoverTerminalRadialLengths decider symbols ++
        directSourceFinalCarrierTerminalRadialSuffix decider symbols)
  exact UnaryFieldEncoderMachine.appendComputableInPolyTime
    (directSourceFinalCrossoverTerminalRadialLengthsComputableInPolyTime
      decider)
    (directSourceFinalCarrierTerminalRadialSuffixComputableInPolyTime
      decider)

end LeanTrominoes.PeriodicCNFStripReduction

end

