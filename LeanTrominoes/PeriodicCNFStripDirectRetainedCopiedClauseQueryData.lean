/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedFiniteSourceDirectionDescriptorData
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQuery

/-! # Direct copied-clause query streams -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open Computability Turing PeriodicCNF
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directRetainedCopiedClauseQueryDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directRetainedCopiedClauseQueryDataVariableDecidableEq :
    DecidableEq Variable :=
  Classical.decEq _

/-- Direct source-symbol specialization of the exact final copied-clause
query stream. -/
def directRetainedFigureNineCopiedClauseQueries
    (symbols : List encoding.Γ) :
    List RetainedFinalCopiedClauseQuery :=
  retainedFinalCopiedClauseQueries
    (sourceFormula (PolySpaceCompiler.formulaOfSymbols decider symbols))

/-- Evaluate the direct specialized query stream before retargeting it to the
public copied descriptor name. -/
def directRetainedFigureNineCopiedClauseQueryDescriptors
    (symbols : List encoding.Γ) :
    List FormulaShapeDirectionOrdering.Token :=
  retainedFinalCopiedClauseDescriptors
    (directRetainedFigureNineCopiedClauseQueries decider symbols)

/-- The sole remaining source compiler needed for final copied-clause
descriptors. -/
abbrev DirectRetainedFigureNineCopiedClauseQueryCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ)
    (List RetainedFinalCopiedClauseQuery)
    encoding.Γ RetainedFinalCopiedClauseQuery id id
    (directRetainedFigureNineCopiedClauseQueries decider)

end PeriodicCNFStripReduction
end LeanTrominoes
