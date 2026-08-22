/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverInternalRename

/-! # Double-renamed carrier clauses contain no crossover internals -/

namespace LeanTrominoes
namespace PeriodicCNF

open PeriodicOrthocrossing PlanarThreeSAT

namespace FormulaShapeRetainedPlanarMetadataDirection

/-- The two-stage carrier embedding used by the metadata clause projections
is the external-only core carrier embedding. -/
theorem embeddedClauseHasCrossoverInternal_doubleRename_coreCarrier_eq_false
    {Variable : Type}
    (clause : EmbeddedClause CarrierNode) :
    embeddedClauseHasCrossoverInternal
        ((clause.rename fun node =>
            (Sum.inl node :
              Sum CarrierNode
                (CrossingRecord × CrossoverInternal))).rename
          (@planarSATCoreVariableMap Variable)) = false := by
  unfold embeddedClauseHasCrossoverInternal
    EmbeddedClause.rename EmbeddedClause.map
  induction clause.literals with
  | nil => rfl
  | cons literal literals induction =>
    simp only [List.map_cons, List.any_cons]
    rw [show planarSATAtomIsCrossoverInternal
          (@planarSATCoreVariableMap Variable
            (Sum.inl literal.1)) = false by rfl,
      Bool.false_or, induction]

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
