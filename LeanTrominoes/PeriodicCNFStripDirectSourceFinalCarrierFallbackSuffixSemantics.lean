/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierFallbackTerminalDataSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierFallbackSuffixQueryLength
import LeanTrominoes.RetainedAngularFanFallbackSuffixQueryColumnSemantics

/-! # Semantic fallback-suffix queries of direct-source carriers -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierFallbackSuffixSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCarrierFallbackSuffixSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The direct query columns reconstruct the exact carrier policy, terminal
data, and selected occurrence slots in one semantic zipper. -/
def directSourceFinalCarrierFallbackSemanticQueries
    (symbols : List encoding.Γ) :
    List FallbackSuffixDirectionCompiler.Batch.Query :=
  let terminals :=
    directSourceFinalCarrierFallbackTerminalData decider symbols
  FallbackSuffixQueryColumns.alignedQueries
    (FallbackSuffixHeaderRoles.carrierRoles (terminals.map Prod.fst))
    (terminals.map Prod.snd)
    (directSourceFinalCarrierOccurrenceSlots decider symbols)

theorem directSourceFinalCarrierFallbackSuffixQueries_eq
    (symbols : List encoding.Γ) :
    directSourceFinalCarrierFallbackSuffixQueries decider symbols =
      directSourceFinalCarrierFallbackSemanticQueries decider symbols := by
  unfold directSourceFinalCarrierFallbackSuffixQueries
    directSourceFinalCarrierFallbackHeaderRoles
    directSourceFinalCarrierFallbackSemanticQueries
  rw [directSourceFinalCarrierFallbackTerminalDirections_eq,
    directSourceFinalCarrierFallbackTerminalRadialLengths_eq]

/-- Every direct carrier fallback query has a positive raw terminal length. -/
theorem directSourceFinalCarrierFallbackSuffixQueries_lengthPositive
    (symbols : List encoding.Γ) :
    ∀ query ∈ directSourceFinalCarrierFallbackSuffixQueries
        decider symbols,
      0 < query.rawLength := by
  rw [directSourceFinalCarrierFallbackSuffixQueries_eq]
  unfold directSourceFinalCarrierFallbackSemanticQueries
  apply FallbackSuffixQueryColumns.alignedQueries_lengthPositive
  intro radial radialMember
  rcases List.mem_map.mp radialMember with
    ⟨terminal, terminalMember, rfl⟩
  exact directSourceFinalCarrierFallbackTerminalData_lengthPositive
    decider symbols terminal terminalMember

end LeanTrominoes.PeriodicCNFStripReduction

end
