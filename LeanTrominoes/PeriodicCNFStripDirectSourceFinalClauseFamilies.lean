/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceAtomCodeFamilies

/-! # Named final direct-source clause families -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalClauseFamiliesStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalClauseFamiliesVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Crossover prefix of the final duplicate-free clause presentation. -/
def directSourceFinalCrossoverClauses
    (symbols : List encoding.Γ) :=
  crossoverMetadataNormalizedClausesDedup
    (PeriodicThreeSATThree.formula
      (directThreeCNFSourceFormula decider symbols))

/-- Retained-carrier family in final clause order. -/
def directSourceFinalCarrierClauses
    (symbols : List encoding.Γ) :=
  PeriodicThreeSATThree.formulaCarrierMetadataNormalizedClauses
    (directThreeCNFSourceFormula decider symbols)

/-- Canonical base-bend family in final clause order. -/
def directSourceFinalBendClauses
    (symbols : List encoding.Γ) :=
  PeriodicThreeSATThree.formulaBaseBendNormalizedClauses
    (directThreeCNFSourceFormula decider symbols)

/-- Routed source-clause family in final clause order. -/
def directSourceFinalRoutedClauseClauses
    (symbols : List encoding.Γ) :=
  PeriodicThreeSATThree.formulaBaseRoutedClauseNormalizedClauses
    (directThreeCNFSourceFormula decider symbols)

/-- Canonical routed-variable suffix in final clause order. -/
def directSourceFinalRoutedVariableClauses
    (symbols : List encoding.Γ) :=
  PeriodicThreeSATThree.formulaCanonicalWrappedNormalizedRoutedVariableClauses
    (directThreeCNFSourceFormula decider symbols)

/-- The named families recover the exact append tree of the final quotient. -/
theorem directSourceFinalFiveFamilyClauses_eq_named
    (symbols : List encoding.Γ) :
    directSourceFinalFiveFamilyClauses decider symbols =
      (directSourceFinalCrossoverClauses decider symbols ++
        directSourceFinalCarrierClauses decider symbols) ++
      ((directSourceFinalBendClauses decider symbols ++
        directSourceFinalRoutedClauseClauses decider symbols) ++
        directSourceFinalRoutedVariableClauses decider symbols) := by
  rfl

private theorem namedFamily_subset_deduplicated
    (symbols : List encoding.Γ)
    (family : List
      (PeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)))
    (subset : ∀ clause ∈ family,
      clause ∈ directSourceFinalFiveFamilyClauses decider symbols) :
    ∀ clause ∈ family,
      clause ∈ deduplicatedClauses
        (directSourceFormula decider symbols) := by
  intro clause clauseMember
  rw [directSource_deduplicatedClauses_eq_fiveFamilies]
  exact subset clause clauseMember

theorem directSourceFinalCrossoverClauses_subset_deduplicated
    (symbols : List encoding.Γ) :
    ∀ clause ∈ directSourceFinalCrossoverClauses decider symbols,
      clause ∈ deduplicatedClauses
        (directSourceFormula decider symbols) := by
  apply namedFamily_subset_deduplicated
  intro clause clauseMember
  rw [directSourceFinalFiveFamilyClauses_eq_named]
  simp only [List.mem_append]
  exact Or.inl (Or.inl clauseMember)

theorem directSourceFinalCarrierClauses_subset_deduplicated
    (symbols : List encoding.Γ) :
    ∀ clause ∈ directSourceFinalCarrierClauses decider symbols,
      clause ∈ deduplicatedClauses
        (directSourceFormula decider symbols) := by
  apply namedFamily_subset_deduplicated
  intro clause clauseMember
  rw [directSourceFinalFiveFamilyClauses_eq_named]
  simp only [List.mem_append]
  exact Or.inl (Or.inr clauseMember)

theorem directSourceFinalBendClauses_subset_deduplicated
    (symbols : List encoding.Γ) :
    ∀ clause ∈ directSourceFinalBendClauses decider symbols,
      clause ∈ deduplicatedClauses
        (directSourceFormula decider symbols) := by
  apply namedFamily_subset_deduplicated
  intro clause clauseMember
  rw [directSourceFinalFiveFamilyClauses_eq_named]
  simp only [List.mem_append]
  exact Or.inr (Or.inl (Or.inl clauseMember))

theorem directSourceFinalRoutedClauseClauses_subset_deduplicated
    (symbols : List encoding.Γ) :
    ∀ clause ∈ directSourceFinalRoutedClauseClauses decider symbols,
      clause ∈ deduplicatedClauses
        (directSourceFormula decider symbols) := by
  apply namedFamily_subset_deduplicated
  intro clause clauseMember
  rw [directSourceFinalFiveFamilyClauses_eq_named]
  simp only [List.mem_append]
  exact Or.inr (Or.inl (Or.inr clauseMember))

theorem directSourceFinalRoutedVariableClauses_subset_deduplicated
    (symbols : List encoding.Γ) :
    ∀ clause ∈ directSourceFinalRoutedVariableClauses decider symbols,
      clause ∈ deduplicatedClauses
        (directSourceFormula decider symbols) := by
  apply namedFamily_subset_deduplicated
  intro clause clauseMember
  rw [directSourceFinalFiveFamilyClauses_eq_named]
  simp only [List.mem_append]
  exact Or.inr (Or.inr clauseMember)

end LeanTrominoes.PeriodicCNFStripReduction

end
