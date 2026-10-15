/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectGridUnitData
import LeanTrominoes.Computation.Encoding.Finite.FiniteBlockTransducer
import LeanTrominoes.Computation.TM2.TM2CompositionMachine

/-! # Polynomial-time direct unary grid-unit emitter -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


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
    (PeriodicCNF.ProgramSource.sourceTokensComputableInPolyTime
      decider)
    gridUnitsComputableInPolyTime
  exact composed

end PeriodicCNFStripReduction
end LeanTrominoes
