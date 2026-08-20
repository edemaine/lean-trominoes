/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarThreeSATThreePositioned

/-! # Nonempty clauses after erasing positioned presentations -/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

theorem erase_clausesNonempty_of_clausesNonempty
    {Variable : Type*} (source : PositionedPeriodicCNF Variable)
    (nonempty :
      ∀ clause ∈ source.clauses, clause.literals ≠ []) :
    ∀ clause ∈ source.erase.clauses, clause ≠ [] := by
  intro clause clauseMember
  unfold erase at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨positionedClause, positionedClauseMember, rfl⟩
  exact nonempty positionedClause positionedClauseMember

end PositionedPeriodicCNF
end LeanTrominoes
