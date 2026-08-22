/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverInternalClassifierData

/-! # Internal-atom classification of the fixed crossover clauses -/

namespace LeanTrominoes
namespace PeriodicCNF

open PeriodicOrthocrossing PlanarThreeSAT

namespace FormulaShapeRetainedPlanarMetadataDirection

/-- Every one of the 26 fixed Figure 8(b) clauses contains an internal
crossover role. -/
theorem crossoverFormula_all_hasInternalRole :
    crossoverFormula.all (fun clause =>
      clause.literals.any fun literal =>
        crossoverRoleIsInternal literal.1) = true := by
  native_decide

/-- Consequently, every canonical wrapped normalized crossover clause
contains a crossover-internal periodic atom. -/
theorem wrappedNormalizedClause_hasCrossoverInternal
    {Variable : Type}
    (crossing : CrossingRecord)
    (clause : EmbeddedClause CrossoverVariable)
    (clauseMember : clause ∈ crossoverFormula) :
    normalizedClauseHasCrossoverInternal
        (FormulaShapeCrossoverDirection.wrappedNormalizedClause
          (Variable := Variable) crossing clause) = true := by
  have fixed :=
    (List.all_eq_true.mp crossoverFormula_all_hasInternalRole)
      clause clauseMember
  unfold normalizedClauseHasCrossoverInternal
    FormulaShapeCrossoverDirection.wrappedNormalizedClause
  rw [List.any_map]
  change clause.literals.any (fun literal =>
      wrappedAtomIsCrossoverInternal
        (⟨normalizedCrossoverAtom crossing literal.1⟩ :
          WrappedPeriodicPlanarSATVariable Variable)) = true
  simpa only [wrappedAtomIsCrossoverInternal_normalizedCrossoverAtom]
    using fixed

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
