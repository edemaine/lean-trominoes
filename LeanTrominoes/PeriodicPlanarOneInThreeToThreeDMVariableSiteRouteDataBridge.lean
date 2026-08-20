/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVariableSiteRouteComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceVariableCoreSplice

/-! # Semantic bridge for totalized finite variable-site routes -/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM

/-- On an active occurrence block, the proof-free finite table returns the
same route as the dependent typed variable-site drawing. -/
theorem variableSiteRouteData_sourceVariableRibbonFanData_eq
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : source.PlanarIncidencePresentation placement)
    (entry : ActiveOccurrenceEntry source.erase)
    (triple : Triple Variable)
    (tripleMember :
      triple ∈ occurrenceTriples source.erase entry.1.1 entry.1.2)
    (color : WireColor) :
    variableSiteRouteData
        (sourceVariableRibbonFanData presentation entry)
        (variableSiteTripleOfTyped triple) color =
      typedVariableSiteRoute source.erase entry.1.1 entry.atom_mem
        entry.1.2 entry.slot_mem triple tripleMember color := by
  let data := sourceVariableRibbonFanData presentation entry
  have countEq :
      data.count = sourceVariableSiteCount source.erase entry.1.1 :=
    VariableRibbonFanData.sourceVariableRibbonFanData_count
      presentation entry
  have matching :
      (variableSiteTripleOfTyped triple).MatchesKind
        data.count data.kind := by
    rw [countEq]
    exact variableSiteTripleOfTyped_matches source.erase entry.1.1
      entry.atom_mem entry.1.2 entry.slot_mem triple tripleMember
  rw [variableSiteRouteData_eq data _ color matching]
  unfold typedVariableSiteRoute sourceVariableSiteDrawing
  apply variableSiteDrawing_route_eq_of_indices_eq
  · exact countEq
  · rfl
  · rfl
  · rfl

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
