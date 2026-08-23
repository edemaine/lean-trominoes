/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRoutedVariablePortRankArmOrder
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorSemantics

/-! # Routed-variable duplicator arms from numeric route descriptors -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- The target-port rank of a routed occurrence is the corresponding field
of its compact numeric incidence descriptor. -/
theorem CNFRouteOccurrence.targetPortRank_eq_numericRouteDescriptor
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrence : CNFRouteOccurrence Variable)
    (occurrenceMember :
      occurrence ∈ drawingCNFRouteOccurrences formula) :
    portRank formula.incidenceGraph
        (targetPort occurrence.edge occurrence.edgeIndex) =
      (occurrence.incidence.numericRouteDescriptor
        formula occurrence.edgeIndex).targetPortRank := by
  rcases List.mem_flatMap.mp occurrenceMember with
    ⟨tagged, taggedMember, occurrenceMember⟩
  rcases List.mem_map.mp occurrenceMember with
    ⟨translate, _translateMember, occurrenceEq⟩
  subst occurrence
  exact congrArg RouteDescriptor.targetPortRank
    (CNFIncidence.routeDescriptor_eq_numericRouteDescriptor
      formula tagged taggedMember)

/-- Active link arms are obtained directly from the compact numeric
descriptors of the selected incidences, in global edge order. -/
theorem routedVariableLinksAt_arms_eq_numericTargetPortRankArms
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable) :
    ((routedVariableLinksAt formula site).map fun link =>
        link.first.duplicatorArm) =
      ((variableRouteOccurrencesAt formula site).take 3).map
        fun occurrence =>
          targetDuplicatorArm
            (occurrence.incidence.numericRouteDescriptor
              formula occurrence.edgeIndex).targetPortRank := by
  rw [routedVariableLinksAt_arms_eq_targetPortRankArms]
  apply List.map_congr_left
  intro occurrence occurrenceMember
  rw [occurrence.targetPortRank_eq_numericRouteDescriptor formula]
  exact
    (variableRouteOccurrencesAt_mem_drawing_and_variableOccurrence
      formula site (List.mem_of_mem_take occurrenceMember)).1

end PeriodicOrthocrossing
end LeanTrominoes
