/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedFinalCrossoverClauseQueryData
import LeanTrominoes.RetainedAngularFanDirectClauseRouteTailRecordCrossoverPhaseSemantics

/-! # Direct-source crossover route-tail phase classification -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCrossoverPhaseStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

theorem directRetainedFinalCrossoverClauseQueries_isDirectCrossover
    (symbols : List encoding.Γ) :
    ∀ query ∈ directRetainedFinalCrossoverClauseQueries decider symbols,
      query.isDirectCrossover = true := by
  intro query queryMember
  unfold directRetainedFinalCrossoverClauseQueries at queryMember
  rcases List.mem_flatten.mp queryMember with
    ⟨block, blockMember, queryMember⟩
  have blockEq : block = retainedFinalDirectCrossoverClauseQueries :=
    (List.mem_replicate.mp blockMember).2
  subst block
  exact retainedFinalDirectCrossoverClauseQueries_phase.1
    query queryMember

theorem directRetainedFinalCrossoverClauseQueries_notDirectRouted
    (symbols : List encoding.Γ) :
    ∀ query ∈ directRetainedFinalCrossoverClauseQueries decider symbols,
      query.isDirectRouted = false := by
  intro query queryMember
  unfold directRetainedFinalCrossoverClauseQueries at queryMember
  rcases List.mem_flatten.mp queryMember with
    ⟨block, blockMember, queryMember⟩
  have blockEq : block = retainedFinalDirectCrossoverClauseQueries :=
    (List.mem_replicate.mp blockMember).2
  subst block
  exact retainedFinalDirectCrossoverClauseQueries_phase.2
    query queryMember

end LeanTrominoes.PeriodicCNFStripReduction

end
