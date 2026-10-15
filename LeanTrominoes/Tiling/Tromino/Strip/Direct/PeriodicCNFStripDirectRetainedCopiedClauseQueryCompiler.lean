/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedCopiedClauseQuerySemantics
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Final.Copied.RetainedAngularFanFinalCopiedClauseQueryCompiler
import LeanTrominoes.SAT.Planar.OccurrenceSplit.RetainedInputAppendPipeline
import LeanTrominoes.Computation.TM2.TM2CompositionMachine

/-! # Direct copied-clause query compilation boundary -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing PeriodicCNF
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Compiling the exact finite clause queries suffices to compile the public
copied descriptor prefix. -/
noncomputable def
    directRetainedFigureNineCopiedClauseDescriptorsComputableInPolyTimeOfQueries
    (queries : DirectRetainedFigureNineCopiedClauseQueryCompiler decider) :
    @TM2ComputableInPolyTime
      (List encoding.Γ)
      (List FormulaShapeDirectionOrdering.Token)
      encoding.Γ FormulaShapeDirectionOrdering.Token id id
      (directRetainedFigureNineCopiedClauseDescriptors decider) := by
  let evaluated := TM2CompositionMachine.computableInPolyTime queries
    retainedFinalCopiedClauseDescriptorsComputableInPolyTime
  exact RetainedInputAppendPipeline.computableInPolyTimeOfEq
    (directRetainedFigureNineCopiedClauseQueryDescriptors decider)
    (directRetainedFigureNineCopiedClauseDescriptors decider)
    (directRetainedFigureNineCopiedClauseQueryDescriptors_eq decider)
    evaluated

/-- Preserve the source symbols beside the exact compiled copied descriptor
prefix. -/
noncomputable def
    directRetainedFigureNineCopiedClauseDescriptorAppenderOfQueries
    (queries : DirectRetainedFigureNineCopiedClauseQueryCompiler decider) :=
  RetainedInputAppendPipeline.appendedComputableInPolyTimeOfCompiler
    (directRetainedFigureNineCopiedClauseDescriptors decider)
    (directRetainedFigureNineCopiedClauseDescriptorsComputableInPolyTimeOfQueries
      decider queries)

end PeriodicCNFStripReduction
end LeanTrominoes

end
