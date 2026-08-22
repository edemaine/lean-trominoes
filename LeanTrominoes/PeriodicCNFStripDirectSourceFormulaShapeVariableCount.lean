/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaShapeCorrect

/-! # Direct formula-shape variable counts -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSourceShapeVariableCountStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The direct finite shape counts exactly the named source formula's distinct
variables. -/
theorem directSourceFormulaShape_variableCount_eq
    (symbols : List encoding.Γ) :
    FormulaShape.variableCount (directSourceFormulaShape decider symbols) =
      (directSourceFormula decider symbols).variableOccurrences.dedup.length :=
  (directSourceFormulaShape_correct_named decider symbols).2

end PeriodicCNFStripReduction
end LeanTrominoes

end
