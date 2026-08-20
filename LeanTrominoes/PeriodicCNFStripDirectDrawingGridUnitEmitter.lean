/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectDrawingGridUnitsData
import LeanTrominoes.PeriodicCNFStripDirectGridUnitEmitter

/-! # Polynomial-time direct 3DM drawing-grid unit emission -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directDrawingGridUnitEmitterStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The fixed source-grid-unit to assembled-grid-unit expansion. -/
def drawingGridUnitsComputableInPolyTime :
    TM2ComputableInPolyTime id id drawingGridUnits :=
  FiniteBlockTransducer.computableInPolyTime fun _ : Unit =>
    List.replicate directDrawingGridFactor ()

/-- Raw source symbols produce the exact unary assembled-drawing grid scale
in polynomial time. -/
def directDrawingGridUnitsOfSymbolsComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directDrawingGridUnitsOfSymbols decider) := by
  let composed := TM2CompositionMachine.computableInPolyTime
    (directGridUnitsOfSymbolsComputableInPolyTime decider)
    drawingGridUnitsComputableInPolyTime
  change TM2ComputableInPolyTime id id
    (fun symbols => drawingGridUnits
      (directGridUnitsOfSymbols decider symbols))
  exact composed

end PeriodicCNFStripReduction
end LeanTrominoes
