/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Gadgets.GadgetPreparedHeaderEmitter
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectGridUnitEmitter
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectPreparedHeaderData

/-! # Polynomial-time direct prepared strip-header emitter -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Compose the direct unary grid-unit stream with the fixed prepared-header
machine. -/
def directPreparedHeaderOfSymbolsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directPreparedHeaderOfSymbols decider) := by
  let composed := TM2CompositionMachine.computableInPolyTime
    (directGridUnitsOfSymbolsComputableInPolyTime decider)
    (GadgetPreparedHeaderEmitter.computableInPolyTime
      normalizationPeriodFactor)
  exact composed

end PeriodicCNFStripReduction
end LeanTrominoes
