/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedFinalClauseDescriptorAssemblyCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedFinalClauseDescriptorAssemblyCorrectness
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedFiniteSourceDirectionDescriptorData
import LeanTrominoes.SAT.Planar.OccurrenceSplit.AngularFan.Final.Copied.RetainedAngularFanFinalCopiedClauseQueryIndexedPresentation
import LeanTrominoes.SAT.Planar.OccurrenceSplit.RetainedInputAppendPipeline

/-! # Direct compilation of exact final copied-clause descriptors -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directFinalCopiedDescriptorCompilerVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The verified final family assembly is exactly the public copied-clause
descriptor prefix consumed by the fixed-eight expansion. -/
theorem directRetainedFinalClauseDescriptorAssembly_eq_copiedClauseDescriptors
    (symbols : List encoding.Γ) :
    directRetainedFinalClauseDescriptorAssembly decider symbols =
      directRetainedFigureNineCopiedClauseDescriptors decider symbols := by
  rw [directRetainedFinalClauseDescriptorAssembly_eq_finalCopied]
  unfold directRetainedFigureNineCopiedClauseDescriptors directSourceFormula
  rw [← retainedFinalCopiedClauseQueries_eq_indexed]
  exact retainedFinalCopiedClauseDescriptors_queries_eq _

/-- The five-family final query assembly therefore compiles the exact public
copied-clause descriptor prefix in polynomial time. -/
noncomputable def
    directRetainedFigureNineCopiedClauseDescriptorsComputableInPolyTime :
    @TM2ComputableInPolyTime
      (List encoding.Γ)
      (List FormulaShapeDirectionOrdering.Token)
      encoding.Γ FormulaShapeDirectionOrdering.Token id id
      (directRetainedFigureNineCopiedClauseDescriptors decider) :=
  RetainedInputAppendPipeline.computableInPolyTimeOfEq
    (directRetainedFinalClauseDescriptorAssembly decider)
    (directRetainedFigureNineCopiedClauseDescriptors decider)
    (directRetainedFinalClauseDescriptorAssembly_eq_copiedClauseDescriptors
      decider)
    (directRetainedFinalClauseDescriptorAssemblyComputableInPolyTime decider)

/-- Preserve source symbols beside the now concrete exact copied-clause
descriptor compiler. -/
noncomputable def directRetainedFigureNineCopiedClauseDescriptorAppender :=
  RetainedInputAppendPipeline.appendedComputableInPolyTimeOfCompiler
    (directRetainedFigureNineCopiedClauseDescriptors decider)
    (directRetainedFigureNineCopiedClauseDescriptorsComputableInPolyTime
      decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
