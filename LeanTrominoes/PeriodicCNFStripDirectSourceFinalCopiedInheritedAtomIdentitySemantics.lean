/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCopiedInheritedAtomIdentityCompiler
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderCopiedSourcePositionSemantics

/-! # Semantics of direct copied inherited-atom identities -/

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- There is one selected inherited identity per direct copied final
occurrence, including harmless values in the parent-local positions. -/
theorem directSourceFinalCopiedInheritedAtomIdentityIndices_length
    (symbols : List encoding.Γ) :
    (directSourceFinalCopiedInheritedAtomIdentityIndices
      decider symbols).length =
      (directSourceFinalCopiedOccurrenceData decider symbols).length := by
  unfold directSourceFinalCopiedInheritedAtomIdentityIndices
    directSourceFinalCopiedOccurrenceData
  exact HorizontalRoutedRouteHeaderCopiedSourcePosition.selectedValues_length
    _ _

/-- Every direct inherited-identity value is ordinary zero-based lookup in
the compact source-identity column at the compiled presentation position. -/
theorem directSourceFinalCopiedInheritedAtomIdentityIndices_eq_map_getD
    (symbols : List encoding.Γ) :
    directSourceFinalCopiedInheritedAtomIdentityIndices decider symbols =
      (directSourceFinalCopiedSourcePositions decider symbols).map
        fun position =>
          (directSourceFinalCompactOccurrenceAtomIdentityIndices
            decider symbols).getD position 0 := by
  unfold directSourceFinalCopiedInheritedAtomIdentityIndices
    directSourceFinalCopiedSourcePositions
  apply HorizontalRoutedRouteHeaderCopiedSourcePosition.selectedValues_eq_map_getD
  exact
    directSourceFinalCompactOccurrenceAtomIdentityIndices_length_eq_total
      decider symbols

end LeanTrominoes.PeriodicCNFStripReduction
