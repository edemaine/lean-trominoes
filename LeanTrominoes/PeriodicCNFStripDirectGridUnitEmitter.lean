/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectGridUnitData
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.TM2CompositionMachine

/-! # Polynomial-time direct unary grid-unit emitter -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directGridUnitEmitterStackFintype
    (stack : decider.tm.K) :
    Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The fixed token-to-grid-unit block transducer. -/
def gridUnitsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      PeriodicCNF.StripGridUnitTokens.gridUnits :=
  FiniteBlockTransducer.computableInPolyTime
    PeriodicCNF.StripGridUnitTokens.block

/-- Compose the existing direct request printer with the fixed grid-weight
transducer. -/
def directGridUnitsOfSymbolsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directGridUnitsOfSymbols decider) := by
  let composed := TM2CompositionMachine.computableInPolyTime
    (PeriodicCNF.PolySpaceRequestEmitter.sourceTokensComputableInPolyTime
      decider)
    gridUnitsComputableInPolyTime
  exact composed

end PeriodicCNFStripReduction
end LeanTrominoes
