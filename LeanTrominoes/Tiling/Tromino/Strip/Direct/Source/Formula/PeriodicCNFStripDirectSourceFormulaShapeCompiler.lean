/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFClauseProfileOccurrenceShapeCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Formula.PeriodicCNFStripDirectSourceFormulaShapeData
import LeanTrominoes.Computation.TM2.TM2CompositionMachine

/-! # Polynomial-time guarded direct source shapes -/

noncomputable section

namespace LeanTrominoes

open Computability Turing

namespace PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


noncomputable def directSourceFormulaShapeComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ) (List FormulaShape.Token)
      encoding.Γ FormulaShape.Token id id
      (directSourceFormulaShape decider) := by
  let sourceProfiles :=
    (StripDirectClauseProfileScan.sourceClauseProfilesComputableInPolyTime
      decider)
  let occurrenceShape :=
    ClauseProfileOccurrenceShape.shapeComputableInPolyTime
  let complete := TM2CompositionMachine.computableInPolyTime
    sourceProfiles occurrenceShape
  unfold directSourceFormulaShape
  exact complete

end PeriodicCNFStripReduction
end LeanTrominoes
