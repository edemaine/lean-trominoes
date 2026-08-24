/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierLinks

/-! # Ordered finite bits of retained carrier links -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Presentation-order carrier-link data for any supplied ownership bit:
physical axis followed by that bit.  Keeping ownership abstract makes this
finite data boundary independent of formula normalization. -/
def retainedCarrierLinkBits
    {Vertex : Type} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (nextSlice : EqualityLink CarrierNode → Bool) : List (Bool × Bool) :=
  (retainedDrawingCompleteCarrierLinks graph).map fun link =>
    (link.first.isHorizontal, nextSlice link)

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
