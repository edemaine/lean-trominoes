/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceBaseBendTerminalDirectionOutputTransport
import LeanTrominoes.PeriodicCNFStripDirectSourceBaseBendTerminalDirectionSemantics

/-! # Direct compilation of retained-bend terminal directions -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directBaseBendDirectionCompilerStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- Compile direct source symbols to all retained-bend terminal direction
ranks in polynomial time. -/
opaque
    directSourceBaseBendTerminalDirectionRanksComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (directSourceBaseBendTerminalDirectionRanks decider) :=
  directSourceBaseBendTerminalDirectionOutputTransport decider
    (directSourceBaseBendTerminalDirectionStream_eq decider)

end LeanTrominoes.PeriodicCNFStripReduction

end

