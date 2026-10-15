/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.SAT.CNF.PeriodicCNFClauseProfileOccurrenceShapeData
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Formula.PeriodicCNFStripDirectSourceFormulaClauseProfiles

/-! # Finite formula shapes of guarded direct strip sources -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.UnaryProgramClauseProfile

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Ordered guarded clauses plus one unary marker for every distinct guarded
occurrence variable. -/
def directSourceFormulaShape (symbols : List encoding.Γ) :
    List FormulaShape.Token :=
  ClauseProfileOccurrenceShape.shape
    (StripDirectClauseProfileScan.sourceClauseProfiles decider symbols)

@[simp] theorem directSourceFormulaShape_clauseProfiles
    (symbols : List encoding.Γ) :
    FormulaShape.clauseProfiles
        (directSourceFormulaShape decider symbols) =
      directSourceFormulaClauseProfiles decider symbols := by
  simp [directSourceFormulaShape,
    directSourceFormulaClauseProfiles]

end PeriodicCNFStripReduction
end LeanTrominoes
