/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidenceDirectionCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidencePrefixSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidenceSuffixSemantics

/-! # Semantics of complete grouped variable-incidence direction blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

/-- Converting one normalized finite-query block recovers the same exact
direction body in the generic delimited alphabet. -/
@[simp] theorem variableIncidencePrefixDirectionTokenBlock_query
    (query : HorizontalFiniteIncidenceDirectionQuery) :
    (HorizontalFiniteIncidenceDirectionQuery.block query).flatMap
        variableIncidencePrefixDirectionTokenBlock =
      FiniteAlphabetDelimitedBlockJoin.block
        (HorizontalFiniteIncidenceDirectionQuery.directions query) := by
  unfold HorizontalFiniteIncidenceDirectionQuery.block
    FiniteAlphabetDelimitedBlockJoin.block
  rw [List.flatMap_append, List.flatMap_map]
  simp [variableIncidencePrefixDirectionTokenBlock]
  rw [← List.map_eq_flatMap]

private theorem convertedQueryBlocks
    (queries : List HorizontalFiniteIncidenceDirectionQuery) :
    (queries.flatMap HorizontalFiniteIncidenceDirectionQuery.block).flatMap
        variableIncidencePrefixDirectionTokenBlock =
      FiniteAlphabetDelimitedBlockJoin.blocks
        (queries.map HorizontalFiniteIncidenceDirectionQuery.directions) := by
  induction queries with
  | nil => rfl
  | cons query queries induction =>
      rw [List.flatMap_cons, List.flatMap_append,
        variableIncidencePrefixDirectionTokenBlock_query, induction]
      rfl

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The converted prefix stream contains exactly one delimited finite table
direction word for every grouped incidence query. -/
theorem directSourceFinalGroupedVariableIncidencePrefixDelimitedTokens_eq_blocks
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedVariableIncidencePrefixDelimitedTokens
        decider symbols =
      FiniteAlphabetDelimitedBlockJoin.blocks
        ((directSourceFinalGroupedVariableIncidencePrefixQueries
          decider symbols).map
            HorizontalFiniteIncidenceDirectionQuery.directions) := by
  unfold directSourceFinalGroupedVariableIncidencePrefixDelimitedTokens
  rw [directSourceFinalGroupedVariableIncidencePrefixDirectionTokens_eq]
  exact convertedQueryBlocks _

/-- The complete stream is definitionally the verified pointwise join of
those exact finite prefixes and the exact sparse suffix selection. -/
theorem directSourceFinalGroupedVariableIncidenceDirectionTokens_eq_joined
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedVariableIncidenceDirectionTokens decider symbols =
      FiniteAlphabetDelimitedBlockJoin.joined
        (directSourceFinalGroupedVariableIncidencePrefixDelimitedTokens
          decider symbols)
        (VariableIncidenceSparseSuffixToken.output
          (directSourceFinalGroupedVariableIncidenceSparseSuffixTokensExpected
            decider symbols)) := by
  unfold directSourceFinalGroupedVariableIncidenceDirectionTokens
  rw [directSourceFinalGroupedVariableIncidenceSuffixDirectionTokens_eq_expected]

end LeanTrominoes.PeriodicCNFStripReduction

end
