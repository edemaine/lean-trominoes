/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalDirectClauseQueryTemplateDirectness

/-! # Directness of the fixed final crossover query block -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PlanarThreeSAT
open PeriodicCNF

private theorem crossoverFormula_length : crossoverFormula.length = 26 := by
  native_decide

/-- The fixed crossover block contains only direct query fields. -/
theorem retainedFinalDirectCrossoverClauseQueries_allDirect :
    ∀ query ∈ retainedFinalDirectCrossoverClauseQueries,
      query.AllDirect := by
  intro query queryMember
  rw [retainedFinalDirectCrossoverClauseQueries,
    List.mem_map] at queryMember
  rcases queryMember with ⟨index, _indexMember, rfl⟩
  unfold retainedFinalDirectCrossoverClauseQueryAt
  have indexLt : index.val <
      PeriodicCNF.FormulaShapeCrossoverDirection.descriptors.length := by
    simp [PeriodicCNF.FormulaShapeCrossoverDirection.descriptors,
      crossoverFormula_length]
  rw [List.getD_eq_getElem _ _ indexLt]
  simp only [PeriodicCNF.FormulaShapeCrossoverDirection.descriptors,
    List.getElem_map]
  unfold RetainedFinalCopiedClauseQuery.directOfToken
  exact RetainedFinalCopiedClauseQuery.allDirect_directOfProfile _ _

end PeriodicEightOccurrenceSplit
end LeanTrominoes
