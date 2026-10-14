/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaShapeCorrect

/-! # Direct formula-shape variable counts -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


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
