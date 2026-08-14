/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFOneDimensionalMapping
import LeanTrominoes.PeriodicCNFPlanarThreeSATThree

/-!
# One-dimensional opaque variable wrapping

The routed planar-SAT wrapper changes only literal atoms and preserves every
literal offset.
-/

namespace LeanTrominoes
namespace PeriodicCNF

/-- The opaque planar-SAT variable wrapper preserves literal offsets. -/
theorem wrapPeriodicPlanarSATFormula_isOneDimensional
    {Original : Type*} {source : PeriodicCNF Original}
    (horizontal : source.IsOneDimensional) :
    (PeriodicOrthocrossing.wrapPeriodicPlanarSATFormula
      source).IsOneDimensional := by
  let mapLiteral :
      PeriodicLiteral Original →
        PeriodicLiteral
          (PeriodicOrthocrossing.WrappedPeriodicVariable Original) :=
    PeriodicOrthocrossing.wrapPeriodicPlanarSATLiteral
  change IsOneDimensional
    ⟨source.clauses.map fun clause => clause.map mapLiteral⟩
  exact IsOneDimensional.mapLiterals source.clauses mapLiteral
    (fun _literal => rfl) horizontal

end PeriodicCNF
end LeanTrominoes
