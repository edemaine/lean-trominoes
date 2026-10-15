/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Base.PeriodicCNFStripDirectSourceBaseBendTerminalRadialCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Direct.PeriodicCNFStripDirectSourceFinalDirectTerminalColumnCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Terminal.PeriodicCNFStripDirectSourceFinalTerminalColumnData
import LeanTrominoes.Computation.Encoding.Unary.UnaryFieldEncoderAppendClosure

/-! # Compiling the final bend/routed terminal-radial suffix -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


noncomputable def
    directSourceFinalBendRoutedTerminalRadialLengthsComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceFinalBendRoutedTerminalRadialLengths decider) := by
  change TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
    (fun symbols : List encoding.Γ =>
      directSourceBaseBendTerminalRadialLengths decider symbols ++
        directSourceFinalRoutedTerminalRadialLengths decider symbols)
  exact UnaryFieldEncoderMachine.appendComputableInPolyTime
    (directSourceBaseBendTerminalRadialLengthsComputableInPolyTime decider)
    (directSourceFinalRoutedTerminalRadialLengthsComputableInPolyTime decider)

end LeanTrominoes.PeriodicCNFStripReduction

end

