/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Computation.Encoding.Finite.FiniteBlockTransducer
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Clause.PeriodicCNFStripDirectSourceFinalClauseFanCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Grouped.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidenceDirectionCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Horizontal.PeriodicCNFStripHorizontalFiniteIncidenceDirectionQueryCompiler
import LeanTrominoes.ThreeDM.Reduction.FromSAT.PeriodicPlanarOneInThreeToThreeDMTyped
import LeanTrominoes.Computation.TM2.TM2CompositionMachine

/-! # Finite direction blocks for all final clause incidences -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Computability Turing
open Gadget PeriodicCNF
open PeriodicPlanarOneInThreeToThreeDM

/-- The nine clause-core triples, each expanded in stable RGB order.  The
fan payload is irrelevant because every final clause uses the same finite
X3C core. -/
def finalClauseIncidenceQueryBlock
    (_ : ClauseRibbonFanData) :
    List HorizontalFiniteIncidenceDirectionQuery :=
  allClauseSets.flatMap fun set =>
    [.clause set .red, .clause set .green, .clause set .blue]

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


/-- One finite direction query for every final clause-core triple and color,
in clause-major, triple-major, RGB-minor order. -/
def directSourceFinalClauseIncidenceQueries
    (symbols : List encoding.Γ) :
    List HorizontalFiniteIncidenceDirectionQuery :=
  (directSourceFinalClauseFans decider symbols).flatMap
    finalClauseIncidenceQueryBlock

/-- Independently delimited finite clause-core directions in the normalized
query compiler alphabet. -/
def directSourceFinalClauseIncidenceNormalizedDirectionTokens
    (symbols : List encoding.Γ) :
    List VariableIncidencePrefixNormalizedToken :=
  HorizontalFiniteIncidenceDirectionQuery.delimitedOutput
    (directSourceFinalClauseIncidenceQueries decider symbols)

/-- The same clause-core blocks in the common generic direction alphabet. -/
def directSourceFinalClauseIncidenceDirectionTokens
    (symbols : List encoding.Γ) : List VariableIncidenceDirectionToken :=
  (directSourceFinalClauseIncidenceNormalizedDirectionTokens
    decider symbols).flatMap variableIncidencePrefixDirectionTokenBlock

noncomputable def
    directSourceFinalClauseIncidenceQueriesComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalClauseIncidenceQueries decider) := by
  unfold directSourceFinalClauseIncidenceQueries
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalClauseFansComputableInPolyTime decider)
    (FiniteBlockTransducer.computableInPolyTime
      finalClauseIncidenceQueryBlock)

noncomputable def
    directSourceFinalClauseIncidenceNormalizedDirectionTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalClauseIncidenceNormalizedDirectionTokens
        decider) := by
  unfold directSourceFinalClauseIncidenceNormalizedDirectionTokens
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalClauseIncidenceQueriesComputableInPolyTime decider)
    HorizontalFiniteIncidenceDirectionQuery.delimitedOutputComputableInPolyTime

/-- All final clause-core direction blocks compile in polynomial time. -/
noncomputable def
    directSourceFinalClauseIncidenceDirectionTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (directSourceFinalClauseIncidenceDirectionTokens decider) := by
  unfold directSourceFinalClauseIncidenceDirectionTokens
  exact TM2CompositionMachine.computableInPolyTime
    (directSourceFinalClauseIncidenceNormalizedDirectionTokensComputableInPolyTime
      decider)
    (FiniteBlockTransducer.computableInPolyTime
      variableIncidencePrefixDirectionTokenBlock)

end LeanTrominoes.PeriodicCNFStripReduction

end
