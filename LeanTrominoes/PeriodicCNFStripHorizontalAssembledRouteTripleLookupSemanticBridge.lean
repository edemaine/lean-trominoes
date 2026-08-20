/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMTypedTriplesSemanticBridge

/-! # Semantic bridge for tag-indexed typed-triple lookup -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

theorem horizontalAssembledRouteTriple?Computed_eq_semantic
    (source : PeriodicCNF Nat)
    (tag : PeriodicThreeDM.IncidenceTag) :
    horizontalAssembledRouteTriple?Computed (source, tag) =
      (horizontalSemanticThreeDMTypedTriples source)[tag.tripleIndex]? := by
  unfold horizontalAssembledRouteTriple?Computed
  rw [horizontalThreeDMTypedTriplesComputed_eq_semantic]

end PeriodicCNFStripReduction
end LeanTrominoes
