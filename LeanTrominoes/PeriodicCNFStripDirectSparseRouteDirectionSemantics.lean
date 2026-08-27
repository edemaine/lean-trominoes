/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseRouteDirectionData
import LeanTrominoes.PeriodicThreeDMNormalizationRouteDirectionConditions

/-! # Certified direct route-direction semantics -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directSparseRouteDirectionSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

/-- The proof-free direct normalization input inherits every route-direction
condition from its certified continuously planar presentation. -/
theorem directSparseComputedRouteDirectionConditions
    (symbols : List encoding.Γ) :
    let input := directSparseComputedNormalizationInputOfSymbols
      decider symbols
    ∀ edge, edge ∈ input.problem.contractedEdges →
      PeriodicThreeDM.NormalizationCompiler.RouteDirectionConditions
        input edge := by
  dsimp only
  rw [directSparseComputedNormalizationInputOfSymbols_eq]
  intro edge member
  let source := PeriodicCNF.PolySpaceCompiler.formulaOfSymbols
    decider symbols
  exact (presentation source).routeDirectionConditions
    (presentation source).problemWellFormed
    (problem_degreeTwoOrThree source) member

/-- Consequently the finite-direction cursor emits the exact canonical
edge-major route-record suffix, with no remaining geometric hypothesis. -/
theorem directSparseComputedRouteDirectionRecordsOfSymbols_eq_canonical
    (symbols : List encoding.Γ) :
    directSparseComputedRouteDirectionRecordsOfSymbols decider symbols =
      directSparseComputedRouteTripleRecordsOfSymbols decider symbols :=
  directSparseComputedRouteDirectionRecordsOfSymbols_eq decider symbols
    (directSparseComputedRouteDirectionConditions decider symbols)

end PeriodicCNFStripReduction
end LeanTrominoes

end
