/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceBoundaryVariableRouteSiteData

/-! # Current-offset copied variable-route site filtering -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

open PeriodicOrthocrossing

theorem filter_currentVariableRouteSiteBlock_against_cycle
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom : ThreeOccurrenceVariable Variable)
    (atomMember : atom ∈ allOccurrenceVariables source) :
    (variableRouteSiteBlock atom (0, 0)).filter
        (cycleVariableRouteSiteAbsent source) = [] := by
  unfold cycleVariableRouteSiteAbsent
  rw [List.filter_eq_nil_iff]
  intro site siteMember
  rw [variableRouteSiteBlock, List.mem_map] at siteMember
  obtain ⟨translate, translateMember, rfl⟩ := siteMember
  have cycleMember := (mem_cycleLinkVariableRouteSites_iff
    source atom translate).mpr ⟨atomMember, translateMember⟩
  have adjustedCycleMember :
      (atom, Cell.add translate (0, 0)) ∈
        cycleLinkVariableRouteSites source := by
    simpa [Cell.add] using cycleMember
  simpa only [decide_eq_true_eq, not_not] using adjustedCycleMember

end PeriodicThreeSATThree
end LeanTrominoes
