/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicEqualityOneDimensional
import LeanTrominoes.PeriodicCNFPlanarHorizontalRetainedCarriers
import LeanTrominoes.PeriodicCNFPlanarRetainedNormalizationComponents

/-!
# One-dimensional retained-carrier clause families

This small wrapper lifts the geometric equal-vertical-shift certificate for
retained carrier links first through normalized equality clauses and then
through the carrier-to-planar-SAT atom embedding.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- The normalized retained straight-carrier equality family is one
dimensional for a horizontal local graph. -/
theorem normalizedRetainedCompleteCarrierClauses_isOneDimensional
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (isLocal : graph.IsLocal)
    (horizontal : graph.HasZeroVerticalOffsets) :
    PeriodicCNF.IsOneDimensional
      ⟨PeriodicEquality.normalizedFormulaClauses
        (normalizeCarrierNode graph)
        (retainedDrawingCompleteCarrierLinks graph)⟩ := by
  exact
    @PeriodicEquality.normalizedFormulaClauses_isOneDimensional
      CarrierNode PeriodicCarrierNode
      (normalizeCarrierNode graph)
      (retainedDrawingCompleteCarrierLinks graph)
      (fun _link linkMember =>
        retainedDrawingCompleteCarrierLinks_verticalEqual
          isLocal horizontal linkMember)

end PeriodicOrthocrossing
end LeanTrominoes
