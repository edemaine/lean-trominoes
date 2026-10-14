/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFStripDirectRetainedCopiedClauseQueryData

/-! # Semantics of direct copied-clause queries -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directRetainedCopiedClauseQuerySemanticsVariableDecidableEq :
    DecidableEq Variable :=
  Classical.decEq _

/-- Evaluating the direct source's exact clause queries gives its public
finite copied descriptor prefix. -/
theorem directRetainedFigureNineCopiedClauseQueryDescriptors_eq
    (symbols : List encoding.Γ) :
    directRetainedFigureNineCopiedClauseQueryDescriptors decider symbols =
      directRetainedFigureNineCopiedClauseDescriptors decider symbols := by
  unfold directRetainedFigureNineCopiedClauseQueryDescriptors
    directRetainedFigureNineCopiedClauseQueries
    directRetainedFigureNineCopiedClauseDescriptors
  exact retainedFinalCopiedClauseDescriptors_queries_eq
    (sourceFormula (ProgramSource.formulaOfSymbols decider symbols))

end PeriodicCNFStripReduction
end LeanTrominoes
