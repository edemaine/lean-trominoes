/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedFinalCrossoverClauseQuerySemantics
import LeanTrominoes.Tiling.Tromino.Strip.Direct.PeriodicCNFStripDirectRetainedPlanarMetadataCrossingMarkerAffineCompiler
import LeanTrominoes.SAT.Planar.OccurrenceSplit.RetainedInputAppendPipeline
import LeanTrominoes.Computation.Encoding.Thirteen.ThirteenMarkerPairBlockCompiler
import LeanTrominoes.Computation.TM2.TM2CompositionMachine

/-! # Compiling direct final crossover clause queries -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- Compile the finite-state marker expansion before retargeting it to the
fixed block presentation. -/
noncomputable def
    directRetainedFinalCompiledCrossoverClauseQueriesComputableInPolyTime :
    DirectRetainedFinalCompiledCrossoverClauseQueryCompiler decider := by
  let markers :=
    directRetainedPlanarMetadataCrossingMarkersComputableInPolyTime decider
  let queries :=
    ThirteenMarkerPairBlocks.computableInPolyTime
      (Marker := PeriodicCNF.FormulaShapeDirectionOrdering.Token)
      retainedFinalDirectCrossoverClauseQueryPair
  change @TM2ComputableInPolyTime
    (List encoding.Γ) (List RetainedFinalCopiedClauseQuery)
    encoding.Γ RetainedFinalCopiedClauseQuery id id
    (fun symbols =>
      ThirteenMarkerPairBlocks.output
        retainedFinalDirectCrossoverClauseQueryPair
        (directRetainedPlanarMetadataCrossingMarkers decider symbols))
  exact TM2CompositionMachine.computableInPolyTime markers queries

/-- The exact fixed direct crossover query stream is polynomial-time
computable. -/
noncomputable def
    directRetainedFinalCrossoverClauseQueriesComputableInPolyTime :
    DirectRetainedFinalCrossoverClauseQueryCompiler decider :=
  RetainedInputAppendPipeline.computableInPolyTimeOfEq
    (directRetainedFinalCompiledCrossoverClauseQueries decider)
    (directRetainedFinalCrossoverClauseQueries decider)
    (directRetainedFinalCompiledCrossoverClauseQueries_eq decider)
    (directRetainedFinalCompiledCrossoverClauseQueriesComputableInPolyTime
      decider)

end LeanTrominoes.PeriodicCNFStripReduction

end
