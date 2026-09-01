/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetDelimitedBlockJoinSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidenceDirectionSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidenceSuffixBlockSemantics

/-! # Complete grouped variable-incidence direction body list -/

noncomputable section

set_option maxHeartbeats 800000

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Exact finite table prefix body for every grouped variable incidence. -/
def directSourceFinalGroupedVariableIncidencePrefixBodies
    (symbols : List encoding.Γ) : List (List AxisDirection) :=
  (directSourceFinalGroupedVariableIncidencePrefixQueries
    decider symbols).map HorizontalFiniteIncidenceDirectionQuery.directions

@[simp] theorem directSourceFinalGroupedVariableIncidencePrefixBodies_length
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedVariableIncidencePrefixBodies
      decider symbols).length =
      (directSourceFinalGroupedVariableIncidencePrefixQueries
        decider symbols).length := by
  simp [directSourceFinalGroupedVariableIncidencePrefixBodies]

@[simp] theorem directSourceFinalGroupedVariableIncidenceSuffixBodies_length
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedVariableIncidenceSuffixBodies
      decider symbols).length =
      (directSourceFinalGroupedVariableIncidencePrefixQueries
        decider symbols).length := by
  unfold directSourceFinalGroupedVariableIncidenceSuffixBodies
    VariableIncidenceSparseSuffixToken.sparseBodies
  rw [List.length_map,
    directSourceFinalGroupedVariableIncidenceKeys_length]

/-- Exact complete direction body for every grouped variable incidence,
obtained by appending its empty or routed sparse suffix to its finite table
prefix. -/
def directSourceFinalGroupedVariableIncidenceBodies
    (symbols : List encoding.Γ) : List (List AxisDirection) :=
  List.zipWith (fun prefixBody suffixBody => prefixBody ++ suffixBody)
    (directSourceFinalGroupedVariableIncidencePrefixBodies decider symbols)
    (directSourceFinalGroupedVariableIncidenceSuffixBodies decider symbols)

/-- The compiled grouped variable-incidence stream serializes exactly the
pointwise prefix-plus-suffix body list. -/
theorem directSourceFinalGroupedVariableIncidenceDirectionTokens_eq_blocks
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedVariableIncidenceDirectionTokens
        decider symbols =
      FiniteAlphabetDelimitedBlockJoin.blocks
        (directSourceFinalGroupedVariableIncidenceBodies
          decider symbols) := by
  unfold directSourceFinalGroupedVariableIncidenceDirectionTokens
  rw [directSourceFinalGroupedVariableIncidencePrefixDelimitedTokens_eq_blocks,
    directSourceFinalGroupedVariableIncidenceSuffixDirectionTokens_eq_blocks]
  exact FiniteAlphabetDelimitedBlockJoin.joined_blocks_zipWith _ _ (by simp)

end LeanTrominoes.PeriodicCNFStripReduction

end
