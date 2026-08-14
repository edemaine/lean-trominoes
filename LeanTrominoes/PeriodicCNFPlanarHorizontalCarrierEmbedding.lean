/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFOneDimensionalMapping
import LeanTrominoes.PeriodicCNFPlanarNormalizationComponents

/-!
# One-dimensional embedded carrier clauses

The carrier-to-planar-SAT embedding changes only literal atoms.  This generic
lemma transports one-dimensionality for any carrier clause list, leaving
retained carrier enumeration opaque until the final component assembly.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Embedding carrier literals in the combined planar-SAT variable type
preserves every literal's vertical offset. -/
theorem embedPeriodicCarrierClauses_isOneDimensional
    {Variable : Type*}
    (clauses : List (PeriodicClause PeriodicCarrierNode))
    (horizontal : PeriodicCNF.IsOneDimensional ⟨clauses⟩) :
    @PeriodicCNF.IsOneDimensional
      (PeriodicPlanarSATVariable Variable)
      ⟨clauses.map (@embedPeriodicCarrierClause Variable)⟩ := by
  let mapLiteral :
      PeriodicLiteral PeriodicCarrierNode →
        PeriodicLiteral (PeriodicPlanarSATVariable Variable) :=
    fun literal =>
      ⟨periodicCarrierNodeToPlanarSATVariable literal.atom,
        literal.offset, literal.value⟩
  change @PeriodicCNF.IsOneDimensional
    (PeriodicPlanarSATVariable Variable)
    ⟨clauses.map fun clause => clause.map mapLiteral⟩
  exact PeriodicCNF.IsOneDimensional.mapLiterals
    clauses mapLiteral (fun _literal => rfl) horizontal

end PeriodicOrthocrossing
end LeanTrominoes
