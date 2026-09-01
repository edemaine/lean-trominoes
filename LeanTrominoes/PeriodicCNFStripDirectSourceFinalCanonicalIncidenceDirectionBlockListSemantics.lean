/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalIncidenceDirectionSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCanonicalIncidenceKeySemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidenceDirectionBlockListSemantics

/-! # Complete direct final canonical incidence direction body list -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Exact finite-table body for every final clause-core incidence. -/
def directSourceFinalClauseIncidenceBodies
    (symbols : List encoding.Γ) : List (List AxisDirection) :=
  (directSourceFinalClauseIncidenceQueries decider symbols).map
    HorizontalFiniteIncidenceDirectionQuery.directions

@[simp] theorem directSourceFinalClauseIncidenceBodies_length
    (symbols : List encoding.Γ) :
    (directSourceFinalClauseIncidenceBodies decider symbols).length =
      (directSourceFinalClauseIncidenceQueries decider symbols).length := by
  simp [directSourceFinalClauseIncidenceBodies]

/-- Complete canonical incidence bodies in stable variable-first,
clause-second order. -/
def directSourceFinalCanonicalIncidenceBodies
    (symbols : List encoding.Γ) : List (List AxisDirection) :=
  directSourceFinalGroupedVariableIncidenceBodies decider symbols ++
    directSourceFinalClauseIncidenceBodies decider symbols

@[simp] theorem directSourceFinalCanonicalIncidenceBodies_length
    (symbols : List encoding.Γ) :
    (directSourceFinalCanonicalIncidenceBodies decider symbols).length =
      (directSourceFinalCanonicalIncidenceQueries decider symbols).length := by
  rw [directSourceFinalCanonicalIncidenceQueries_length]
  simp [directSourceFinalCanonicalIncidenceBodies]

/-- The canonical key column is aligned one-for-one with the explicit
canonical incidence body list. -/
theorem directSourceFinalCanonicalIncidenceBodies_length_eq_keys
    (symbols : List encoding.Γ) :
    (directSourceFinalCanonicalIncidenceBodies decider symbols).length =
      (directSourceFinalCanonicalIncidenceKeys decider symbols).length := by
  rw [directSourceFinalCanonicalIncidenceBodies_length,
    directSourceFinalCanonicalIncidenceKeys_length]

/-- The complete canonical incidence-direction stream is serialization of
the exact variable-body list followed by the exact clause-body list. -/
theorem directSourceFinalCanonicalIncidenceDirectionTokens_eq_blocks
    (symbols : List encoding.Γ) :
    directSourceFinalCanonicalIncidenceDirectionTokens decider symbols =
      FiniteAlphabetDelimitedBlockJoin.blocks
        (directSourceFinalCanonicalIncidenceBodies decider symbols) := by
  unfold directSourceFinalCanonicalIncidenceDirectionTokens
    directSourceFinalCanonicalIncidenceBodies
    directSourceFinalClauseIncidenceBodies
  rw [directSourceFinalGroupedVariableIncidenceDirectionTokens_eq_blocks,
    directSourceFinalClauseIncidenceDirectionTokens_eq_blocks,
    ← FiniteAlphabetDelimitedBlockJoin.blocks_append]

end LeanTrominoes.PeriodicCNFStripReduction

end
