/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceBoundaryVariableRouteSiteData

/-! # Next-offset copied variable-route site filtering -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

open PeriodicOrthocrossing

theorem filter_nextVariableRouteSiteBlock_against_cycle
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : ThreeOccurrenceVariable Variable)
    (atomMember : atom ∈ allOccurrenceVariables source) :
    (variableRouteSiteBlock atom (1, 0)).filter
        (cycleVariableRouteSiteAbsent source) =
      nextBoundaryVariableRouteSiteBlock atom := by
  unfold cycleVariableRouteSiteAbsent
  apply List.filter_congr
  intro site siteMember
  rw [variableRouteSiteBlock, List.mem_map] at siteMember
  obtain ⟨translate, translateMember, rfl⟩ := siteMember
  exact Bool.decide_congr (by
    rw [not_iff_not, mem_cycleLinkVariableRouteSites_iff]
    simp [atomMember])

end PeriodicThreeSATThree
end LeanTrominoes
