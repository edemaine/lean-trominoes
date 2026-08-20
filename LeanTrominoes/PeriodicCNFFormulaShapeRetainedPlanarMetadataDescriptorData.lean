/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRawRouteData

/-! # Retained direction descriptors from finite clause metadata -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- A position-free presentation of the deduplicated normalized metadata
clauses.  Formula-shape descriptors inspect only literals and route
directions, so the common zero position is sufficient at this boundary. -/
def positionedSource {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    PositionedPeriodicCNF
      (WrappedPeriodicPlanarSATVariable Variable) :=
  ⟨(deduplicatedClauses source).map fun clause =>
    ⟨(0, 0), clause⟩⟩

/-- Finite retained clause-profile/first-direction descriptors read entirely
from normalized clause metadata and its selected raw component routes. -/
def descriptors {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    List FormulaShapeDirectionOrdering.Token :=
  FormulaShapeDirectionOrdering.ofFormula
    (positionedSource source) (rawRepresentativeRoute source)

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
