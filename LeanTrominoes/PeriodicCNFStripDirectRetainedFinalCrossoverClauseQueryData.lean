/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalCopiedClauseQueryTemplates
import LeanTrominoes.PeriodicCNFStripDirectRetainedPlanarMetadataCrossingMarkerData

/-! # Direct final crossover clause-query blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing PeriodicCNF PeriodicOrthocrossing
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCrossoverQueryDataStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCrossoverQueryDataVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Finite-state expansion of the established thirteen-marker crossing
stream into stable direct crossover queries. -/
def directRetainedFinalCompiledCrossoverClauseQueries
    (symbols : List encoding.Γ) :
    List RetainedFinalCopiedClauseQuery :=
  ThirteenMarkerPairBlocks.output
    retainedFinalDirectCrossoverClauseQueryPair
    (directRetainedPlanarMetadataCrossingMarkers decider symbols)

/-- One fixed twenty-six-query block per canonical oriented crossing. -/
def directRetainedFinalCrossoverClauseQueries
    (symbols : List encoding.Γ) :
    List RetainedFinalCopiedClauseQuery :=
  (List.replicate
    (orientedCrossings
      (directSourceFormula decider symbols).incidenceGraph).length
    retainedFinalDirectCrossoverClauseQueries).flatten

abbrev DirectRetainedFinalCompiledCrossoverClauseQueryCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ) (List RetainedFinalCopiedClauseQuery)
    encoding.Γ RetainedFinalCopiedClauseQuery id id
    (directRetainedFinalCompiledCrossoverClauseQueries decider)

abbrev DirectRetainedFinalCrossoverClauseQueryCompiler :=
  @TM2ComputableInPolyTime
    (List encoding.Γ) (List RetainedFinalCopiedClauseQuery)
    encoding.Γ RetainedFinalCopiedClauseQuery id id
    (directRetainedFinalCrossoverClauseQueries decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
