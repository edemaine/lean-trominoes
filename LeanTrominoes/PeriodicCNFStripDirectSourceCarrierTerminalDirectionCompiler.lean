/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierTerminalDirectionData
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierTerminalDirectionOutputTransport

/-! # Direct compilation of retained-carrier terminal directions -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing
open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceCarrierTerminalDirectionStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

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
