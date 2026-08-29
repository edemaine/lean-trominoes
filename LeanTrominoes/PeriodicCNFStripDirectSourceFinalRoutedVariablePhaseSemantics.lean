/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedFinalRoutedVariableClauseQueryData
import LeanTrominoes.RetainedAngularFanDirectClauseRouteTailRecordRoutedVariablePhaseSemantics

/-! # Routed-variable route-tail phase classification -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalRoutedVariablePhaseStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

theorem directRetainedFinalRoutedVariableClauseQueries_isDirectRouted
    (symbols : List encoding.Γ) :
    ∀ query ∈
        directRetainedFinalRoutedVariableClauseQueries decider symbols,
      query.isDirectRouted = true := by
  have fixed : ∀ query ∈ retainedFinalDirectRoutedVariableFullSiteQueries,
      query.isDirectRouted = true :=
    retainedFinalDirectRoutedVariableFullSiteQueries_phase.1
  intro query queryMember
  unfold directRetainedFinalRoutedVariableClauseQueries at queryMember
  rcases List.mem_flatMap.mp queryMember with
    ⟨_targetIndex, _targetMember, queryMember⟩
  exact fixed query queryMember

theorem directRetainedFinalRoutedVariableClauseQueries_notDirectCrossover
    (symbols : List encoding.Γ) :
    ∀ query ∈
        directRetainedFinalRoutedVariableClauseQueries decider symbols,
      query.isDirectCrossover = false := by
  have fixed : ∀ query ∈ retainedFinalDirectRoutedVariableFullSiteQueries,
      query.isDirectCrossover = false :=
    retainedFinalDirectRoutedVariableFullSiteQueries_phase.2
  intro query queryMember
  unfold directRetainedFinalRoutedVariableClauseQueries at queryMember
  rcases List.mem_flatMap.mp queryMember with
    ⟨_targetIndex, _targetMember, queryMember⟩
  exact fixed query queryMember

end LeanTrominoes.PeriodicCNFStripReduction

end
