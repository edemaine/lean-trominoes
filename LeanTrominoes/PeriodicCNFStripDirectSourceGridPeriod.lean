/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectGridUnitData
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaData

/-! # Exact unary period for the direct source drawing -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceGridPeriodStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

noncomputable local instance directSourceGridPeriodVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The existing direct grid-unit stream has exactly the period consumed by
the graph-free crossing predicate. -/
theorem directGridUnitsOfSymbols_length_eq_directSourceDrawingGridSize
    (symbols : List encoding.Γ) :
    (directGridUnitsOfSymbols decider symbols).length =
      PeriodicOrthocrossing.drawingGridSize
        (directSourceFormula decider symbols).incidenceGraph := by
  rw [directGridUnitsOfSymbols_length]
  rfl

end LeanTrominoes.PeriodicCNFStripReduction
