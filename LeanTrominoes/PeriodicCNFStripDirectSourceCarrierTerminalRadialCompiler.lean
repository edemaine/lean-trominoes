/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierTerminalRadialData
import LeanTrominoes.PeriodicCNFStripDirectSourceCarrierTerminalRadialOutputTransport

/-! # Direct compilation of retained-carrier terminal radial lengths -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing
open PeriodicCNF PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceCarrierTerminalRadialStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

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
