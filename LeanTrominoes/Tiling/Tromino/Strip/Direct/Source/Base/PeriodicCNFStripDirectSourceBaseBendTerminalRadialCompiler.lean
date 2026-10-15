/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Base.PeriodicCNFStripDirectSourceBaseBendTerminalRadialOutputTransport
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Base.PeriodicCNFStripDirectSourceBaseBendTerminalRadialSemantics

/-! # Direct compilation of retained-bend terminal radial lengths -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Compile direct source symbols to all retained-bend terminal radial
lengths in polynomial time. -/
opaque
    directSourceBaseBendTerminalRadialLengthsComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceBaseBendTerminalRadialLengths decider) :=
  directSourceBaseBendTerminalRadialOutputTransport decider
    (directSourceBaseBendTerminalRadialStream_eq decider)

end LeanTrominoes.PeriodicCNFStripReduction

end

