/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedFinalFallbackClauseQueryData
import LeanTrominoes.RetainedAngularFanDirectClauseRouteTailRecordPhaseFilter

/-! # Direct-source fallback route-tail phase classification -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalFallbackPhaseStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

private theorem precomputedQueries_not_crossover
    (tokens : List PeriodicCNF.FormulaShapeDirectionOrdering.Token) :
    ∀ query ∈ retainedFinalPrecomputedClauseQueries tokens,
      query.isDirectCrossover = false := by
  intro query queryMember
  unfold retainedFinalPrecomputedClauseQueries at queryMember
  rcases List.mem_flatMap.mp queryMember with
    ⟨token, _tokenMember, queryMember⟩
  simp only [retainedFinalPrecomputedClauseQueryBlock,
    List.mem_singleton] at queryMember
  subst query
  rfl

private theorem precomputedQueries_not_routed
    (tokens : List PeriodicCNF.FormulaShapeDirectionOrdering.Token) :
    ∀ query ∈ retainedFinalPrecomputedClauseQueries tokens,
      query.isDirectRouted = false := by
  intro query queryMember
  unfold retainedFinalPrecomputedClauseQueries at queryMember
  rcases List.mem_flatMap.mp queryMember with
    ⟨token, _tokenMember, queryMember⟩
  simp only [retainedFinalPrecomputedClauseQueryBlock,
    List.mem_singleton] at queryMember
  subst query
  rfl

theorem directRetainedFinalCarrierClauseQueries_notDirectCrossover
    (symbols : List encoding.Γ) :
    ∀ query ∈ directRetainedFinalCarrierClauseQueries decider symbols,
      query.isDirectCrossover = false :=
  precomputedQueries_not_crossover _

theorem directRetainedFinalCarrierClauseQueries_notDirectRouted
    (symbols : List encoding.Γ) :
    ∀ query ∈ directRetainedFinalCarrierClauseQueries decider symbols,
      query.isDirectRouted = false :=
  precomputedQueries_not_routed _

theorem directRetainedFinalBendClauseQueries_notDirectCrossover
    (symbols : List encoding.Γ) :
    ∀ query ∈ directRetainedFinalBendClauseQueries decider symbols,
      query.isDirectCrossover = false :=
  precomputedQueries_not_crossover _

theorem directRetainedFinalBendClauseQueries_notDirectRouted
    (symbols : List encoding.Γ) :
    ∀ query ∈ directRetainedFinalBendClauseQueries decider symbols,
      query.isDirectRouted = false :=
  precomputedQueries_not_routed _

end LeanTrominoes.PeriodicCNFStripReduction

end
