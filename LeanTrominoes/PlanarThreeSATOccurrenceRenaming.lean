/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PlanarThreeSATOcurrences

/-! # Variable occurrences under embedded-formula renaming -/

namespace LeanTrominoes.PlanarThreeSAT

/-- Renaming every embedded clause maps the flattened variable-occurrence
list by the same variable map. -/
@[simp] theorem embeddedVariableOccurrences_rename
    {Source Target : Type*}
    (variableMap : Source → Target)
    (formula : List (EmbeddedClause Source)) :
    embeddedVariableOccurrences
        (formula.map fun clause => clause.rename variableMap) =
      (embeddedVariableOccurrences formula).map variableMap := by
  simpa only [EmbeddedClause.rename] using
    embeddedVariableOccurrences_map variableMap id formula

end LeanTrominoes.PlanarThreeSAT
