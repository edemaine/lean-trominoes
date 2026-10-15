/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Carrier.PeriodicCNFStripDirectSourceCarrierTerminalDirectionData
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Carrier.PeriodicCNFStripDirectSourceCarrierTerminalDirectionOutputTransport

/-! # Direct compilation of retained-carrier terminal directions -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing
open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directSourceCarrierTerminalDirectionVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Direct source symbols compile to the exact retained-carrier terminal
direction-rank column in polynomial time. -/
opaque
    directSourceCarrierTerminalDirectionRanksComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceCarrierTerminalDirectionRanks decider) :=
  directSourceCarrierTerminalDirectionOutputTransport decider
    (directSourceCarrierTerminalDirectionStream_eq decider)

end PeriodicCNFStripReduction
end LeanTrominoes

end
