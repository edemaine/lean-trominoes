/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFamilies
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalDeduplicatedClauseShape

/-! # Shape of named final direct-source clause families -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF
open PeriodicOrthocrossing

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalClauseFamilyShapeStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalClauseFamilyShapeVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

private theorem family_nonempty
    (symbols : List encoding.Γ)
    (family : List
      (PeriodicClause (WrappedPeriodicPlanarSATVariable Variable)))
    (subset : ∀ clause ∈ family,
      clause ∈ PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection.deduplicatedClauses
        (directSourceFormula decider symbols)) :
    ∀ clause ∈ family, clause ≠ [] := by
  intro clause clauseMember
  exact directSource_deduplicatedClauses_nonempty
    decider symbols clause (subset clause clauseMember)

private theorem family_widthAtMostThree
    (symbols : List encoding.Γ)
    (family : List
      (PeriodicClause (WrappedPeriodicPlanarSATVariable Variable)))
    (subset : ∀ clause ∈ family,
      clause ∈ PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection.deduplicatedClauses
        (directSourceFormula decider symbols)) :
    ∀ clause ∈ family, clause.length ≤ 3 := by
  intro clause clauseMember
  exact directSource_deduplicatedClauses_widthAtMostThree
    decider symbols clause (subset clause clauseMember)

theorem directSourceFinalCrossoverClauses_nonempty
    (symbols : List encoding.Γ) :
    ∀ clause ∈ directSourceFinalCrossoverClauses decider symbols,
      clause ≠ [] :=
  family_nonempty decider symbols _
    (directSourceFinalCrossoverClauses_subset_deduplicated
      decider symbols)

theorem directSourceFinalCrossoverClauses_widthAtMostThree
    (symbols : List encoding.Γ) :
    ∀ clause ∈ directSourceFinalCrossoverClauses decider symbols,
      clause.length ≤ 3 :=
  family_widthAtMostThree decider symbols _
    (directSourceFinalCrossoverClauses_subset_deduplicated
      decider symbols)

theorem directSourceFinalCarrierClauses_nonempty
    (symbols : List encoding.Γ) :
    ∀ clause ∈ directSourceFinalCarrierClauses decider symbols,
      clause ≠ [] :=
  family_nonempty decider symbols _
    (directSourceFinalCarrierClauses_subset_deduplicated
      decider symbols)

theorem directSourceFinalCarrierClauses_widthAtMostThree
    (symbols : List encoding.Γ) :
    ∀ clause ∈ directSourceFinalCarrierClauses decider symbols,
      clause.length ≤ 3 :=
  family_widthAtMostThree decider symbols _
    (directSourceFinalCarrierClauses_subset_deduplicated
      decider symbols)

theorem directSourceFinalBendClauses_nonempty
    (symbols : List encoding.Γ) :
    ∀ clause ∈ directSourceFinalBendClauses decider symbols,
      clause ≠ [] :=
  family_nonempty decider symbols _
    (directSourceFinalBendClauses_subset_deduplicated
      decider symbols)

theorem directSourceFinalBendClauses_widthAtMostThree
    (symbols : List encoding.Γ) :
    ∀ clause ∈ directSourceFinalBendClauses decider symbols,
      clause.length ≤ 3 :=
  family_widthAtMostThree decider symbols _
    (directSourceFinalBendClauses_subset_deduplicated
      decider symbols)

theorem directSourceFinalRoutedClauseClauses_nonempty
    (symbols : List encoding.Γ) :
    ∀ clause ∈ directSourceFinalRoutedClauseClauses decider symbols,
      clause ≠ [] :=
  family_nonempty decider symbols _
    (directSourceFinalRoutedClauseClauses_subset_deduplicated
      decider symbols)

theorem directSourceFinalRoutedClauseClauses_widthAtMostThree
    (symbols : List encoding.Γ) :
    ∀ clause ∈ directSourceFinalRoutedClauseClauses decider symbols,
      clause.length ≤ 3 :=
  family_widthAtMostThree decider symbols _
    (directSourceFinalRoutedClauseClauses_subset_deduplicated
      decider symbols)

theorem directSourceFinalRoutedVariableClauses_nonempty
    (symbols : List encoding.Γ) :
    ∀ clause ∈ directSourceFinalRoutedVariableClauses decider symbols,
      clause ≠ [] :=
  family_nonempty decider symbols _
    (directSourceFinalRoutedVariableClauses_subset_deduplicated
      decider symbols)

theorem directSourceFinalRoutedVariableClauses_widthAtMostThree
    (symbols : List encoding.Γ) :
    ∀ clause ∈ directSourceFinalRoutedVariableClauses decider symbols,
      clause.length ≤ 3 :=
  family_widthAtMostThree decider symbols _
    (directSourceFinalRoutedVariableClauses_subset_deduplicated
      decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
