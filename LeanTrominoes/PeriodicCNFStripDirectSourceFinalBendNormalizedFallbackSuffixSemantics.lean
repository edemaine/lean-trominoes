/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendFallbackSuffixSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendNormalizedFallbackSuffixCompiler
import LeanTrominoes.RetainedAngularFanNormalizedFallbackSuffixDirectionBatchSemantics

/-! # Semantics of normalized direct bend fallback suffixes -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF PeriodicOrthocrossing
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalBendNormalizedFallbackSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalBendNormalizedFallbackSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

private theorem alignedOrdinaryQueries_kind
    (terminals : List RetainedTerminalData)
    (slots : List RetainedTerminalSlot) :
    ∀ query ∈
        FallbackSuffixQueries.alignedQueries
          (List.replicate terminals.length .ordinary)
          terminals slots,
      query.kind = .ordinary := by
  induction terminals generalizing slots with
  | nil => simp [FallbackSuffixQueries.alignedQueries]
  | cons terminal terminals induction =>
      cases slots with
      | nil => simp [FallbackSuffixQueries.alignedQueries]
      | cons slot slots =>
          intro query queryMember
          simp only [List.length_cons, List.replicate_succ,
            FallbackSuffixQueries.alignedQueries,
            List.mem_cons] at queryMember
          rcases queryMember with queryEq | queryMember
          · subst query
            rfl
          · exact induction slots query queryMember

/-- Canonical route-delimited normalized suffix words represented by every
direct bend query. -/
def directSourceFinalBendNormalizedFallbackGeometricSuffixDirections
    (symbols : List encoding.Γ) :
    List FallbackSuffixDirectionCompiler.OutputToken :=
  NormalizedFallbackSuffixDirectionCompiler.Batch.retainedOrdinaryDirections
    (directSourceFinalBendFallbackSemanticQueries decider symbols)

/-- The direct normalized bend-suffix compiler emits exactly the canonical
normalized suffix word for every semantic bend query. -/
theorem directSourceFinalBendNormalizedFallbackSuffixDirections_eq_geometric
    (symbols : List encoding.Γ) :
    directSourceFinalBendNormalizedFallbackSuffixDirections decider symbols =
      directSourceFinalBendNormalizedFallbackGeometricSuffixDirections
        decider symbols := by
  have ordinary :
      ∀ query ∈
          directSourceFinalBendFallbackSemanticQueries decider symbols,
        query.kind = .ordinary := by
    unfold directSourceFinalBendFallbackSemanticQueries
    exact alignedOrdinaryQueries_kind
      (directSourceFinalBendFallbackTerminalData decider symbols)
      (directSourceFinalBendOccurrenceSlots decider symbols)
  have positive :
      ∀ query ∈
          directSourceFinalBendFallbackSemanticQueries decider symbols,
        0 < query.rawLength := by
    rw [← directSourceFinalBendFallbackSuffixQueries_eq]
    exact directSourceFinalBendFallbackSuffixQueries_lengthPositive
      decider symbols
  unfold directSourceFinalBendNormalizedFallbackSuffixDirections
    directSourceFinalBendNormalizedFallbackGeometricSuffixDirections
  rw [directSourceFinalBendFallbackSuffixQueries_eq]
  exact
    NormalizedFallbackSuffixDirectionCompiler.Batch.directions_eq_retainedOrdinaryDirections
      (directSourceFinalBendFallbackSemanticQueries decider symbols)
      ordinary positive

end LeanTrominoes.PeriodicCNFStripReduction

end
