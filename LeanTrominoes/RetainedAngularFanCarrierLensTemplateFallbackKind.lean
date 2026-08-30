/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PlanarThreeSATEqualityLens

/-! # Fallback policies of canonical carrier-lens templates -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT

/-- The canonical east-facing carrier template realizes the finite carrier
fallback-policy table.  Every other placement preserves these route lengths. -/
theorem horizontalEqualityLensRoute_singletonPrefix_iff
    (span : Int)
    (localClauseIndex literalIndex : Nat) :
    (horizontalEqualityLensRoutes span
        localClauseIndex literalIndex).dropLast.length = 1 ↔
      (localClauseIndex = 0 ∧ literalIndex = 0) ∨
      (localClauseIndex = 1 ∧ literalIndex = 1) := by
  rcases localClauseIndex with (_ | _ | localClauseIndex) <;>
    rcases literalIndex with (_ | _ | literalIndex) <;>
    simp [horizontalEqualityLensRoutes,
      horizontalEqualityLensUpperLeftRoute,
      horizontalEqualityLensUpperRightRoute,
      horizontalEqualityLensLowerLeftRoute,
      horizontalEqualityLensLowerRightRoute]

end PeriodicEightOccurrenceSplit
end LeanTrominoes
