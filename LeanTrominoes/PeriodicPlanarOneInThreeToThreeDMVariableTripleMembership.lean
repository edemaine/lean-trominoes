/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMTyped

/-! # Constructor membership in the variable-triple prefix -/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

/-- The variable-module prefix contains only ordinary and fixed-red
constructors, never a clause-core constructor. -/
@[simp] theorem clause_not_mem_variableTriples
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) (clauseIndex : Nat)
    (set : PlanarThreeDM.X3CClauseSet) :
    Triple.clause clauseIndex set ∉ variableTriples source := by
  unfold variableTriples
  simp only [List.mem_flatMap, not_exists]
  rintro atom ⟨atomMember, slot, slotMember, clauseMember⟩
  unfold occurrenceTriples at clauseMember
  split at clauseMember <;> simp at clauseMember

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
