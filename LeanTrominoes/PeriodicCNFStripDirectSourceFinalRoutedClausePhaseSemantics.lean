/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedFinalRoutedClauseQueryData
import LeanTrominoes.RetainedAngularFanDirectClauseRouteTailRecordPhaseFilter

/-! # Routed-clause route-tail phase classification -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalRoutedClausePhaseStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

theorem directRetainedFinalRoutedClauseQueries_isDirectRouted
    (symbols : List encoding.Γ) :
    ∀ query ∈ directRetainedFinalRoutedClauseQueries decider symbols,
      query.isDirectRouted = true := by
  intro query queryMember
  unfold directRetainedFinalRoutedClauseQueries at queryMember
  rcases List.mem_flatMap.mp queryMember with
    ⟨profile, _profileMember, queryMember⟩
  simp only [directRetainedFinalRoutedClauseQueryBlock,
    List.mem_singleton] at queryMember
  subst query
  cases profile <;>
    rfl

theorem directRetainedFinalRoutedClauseQueries_notDirectCrossover
    (symbols : List encoding.Γ) :
    ∀ query ∈ directRetainedFinalRoutedClauseQueries decider symbols,
      query.isDirectCrossover = false := by
  intro query queryMember
  unfold directRetainedFinalRoutedClauseQueries at queryMember
  rcases List.mem_flatMap.mp queryMember with
    ⟨profile, _profileMember, queryMember⟩
  simp only [directRetainedFinalRoutedClauseQueryBlock,
    List.mem_singleton] at queryMember
  subst query
  cases profile <;>
    rfl

end LeanTrominoes.PeriodicCNFStripReduction

end
