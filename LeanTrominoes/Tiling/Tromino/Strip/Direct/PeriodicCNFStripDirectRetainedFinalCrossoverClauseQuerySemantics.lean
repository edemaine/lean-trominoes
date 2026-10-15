/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedFinalCrossoverClauseQueryData
import LeanTrominoes.Computation.Encoding.Thirteen.ThirteenMarkerPairBlockSemantics

/-! # Semantics of direct final crossover query blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directFinalCrossoverQuerySemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The thirteen consecutive query pairs are exactly the fixed crossover
query block. -/
theorem retainedFinalDirectCrossoverClauseQueryPairs_eq :
    ThirteenMarkerPairBlocks.block
        retainedFinalDirectCrossoverClauseQueryPair =
      retainedFinalDirectCrossoverClauseQueries := by
  decide +kernel

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
