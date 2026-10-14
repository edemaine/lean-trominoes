/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.ListDedupDecidableEq
import LeanTrominoes.PeriodicCNFStripDirectSourceDistinctVariableCountData
import LeanTrominoes.PeriodicCNFStripDirectSourceFormulaShapeVariableCount

/-! # Named direct formula-shape variable counts -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- The direct finite shape counts the shared named distinct-variable total. -/
theorem directSourceFormulaShape_variableCount_eq_distinct
    (symbols : List encoding.Γ) :
    FormulaShape.variableCount (directSourceFormulaShape decider symbols) =
      directSourceDistinctVariableCount decider symbols := by
  calc
    FormulaShape.variableCount (directSourceFormulaShape decider symbols) =
        (directSourceFormula decider symbols).variableOccurrences.dedup.length :=
      directSourceFormulaShape_variableCount_eq decider symbols
    _ = directSourceDistinctVariableCount decider symbols := by
      unfold directSourceDistinctVariableCount
      exact congrArg List.length
        (listDedup_eq_of_decidableEq
          (inferInstance : DecidableEq Variable)
          directSourceVariableDecidableEq _)

end PeriodicCNFStripReduction
end LeanTrominoes

end
