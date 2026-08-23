/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListUnionFilter
import LeanTrominoes.PeriodicThreeSATThreeVariableRouteSiteSplit

/-! # Union form of occurrence-split routed-variable sites -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

open PeriodicOrthocrossing

/-- Last-occurrence deduplication of the split formula retains the copied
source-site stream union the rotated full cycle-site blocks. -/
theorem drawingVariableRouteSites_formula_eq_occurrence_union_rotated
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    drawingVariableRouteSites (formula source) =
      decidableListUnion (occurrenceVariableRouteSites source)
        (rotatedVariableRouteSiteBlocks source) := by
  rw [drawingVariableRouteSites_formula_eq_dedup_occurrence_append_cycle]
  rw [List.dedup_append]
  rw [cycleLinkVariableRouteSites_dedup_eq_rotatedBlocks]
  rfl

end PeriodicThreeSATThree
end LeanTrominoes
