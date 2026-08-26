/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedFinalCrossoverClauseQueryData
import LeanTrominoes.ThirteenMarkerPairBlockSemantics

/-! # Semantics of direct final crossover query blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCrossoverQuerySemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCrossoverQuerySemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The thirteen consecutive query pairs are exactly the fixed crossover
query block. -/
theorem retainedFinalDirectCrossoverClauseQueryPairs_eq :
    ThirteenMarkerPairBlocks.block
        retainedFinalDirectCrossoverClauseQueryPair =
      retainedFinalDirectCrossoverClauseQueries := by
  native_decide

/-- Expanding the crossing markers produces exactly one stable direct query
block per canonical oriented crossing. -/
theorem directRetainedFinalCompiledCrossoverClauseQueries_eq
    (symbols : List encoding.Γ) :
    directRetainedFinalCompiledCrossoverClauseQueries decider symbols =
      directRetainedFinalCrossoverClauseQueries decider symbols := by
  unfold directRetainedFinalCompiledCrossoverClauseQueries
    directRetainedPlanarMetadataCrossingMarkers
    directRetainedFinalCrossoverClauseQueries
  rw [ThirteenMarkerPairBlocks.output_replicate_mul_thirteen,
    retainedFinalDirectCrossoverClauseQueryPairs_eq]

end LeanTrominoes.PeriodicCNFStripReduction

end
