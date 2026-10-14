/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierTerminalRadialData
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierTerminalRadialOutputTransport

/-! # Direct compilation of retained-carrier terminal radial lengths -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing
open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directSourceCarrierTerminalRadialVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Direct source symbols compile to the exact retained-carrier terminal
radial-length column in polynomial time. -/
opaque
    directSourceCarrierTerminalRadialLengthsComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceCarrierTerminalRadialLengths decider) :=
  directSourceCarrierTerminalRadialOutputTransport decider
    (directSourceCarrierTerminalRadialStream_eq decider)

end PeriodicCNFStripReduction
end LeanTrominoes

end
