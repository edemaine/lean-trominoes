/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationRoutePortCompleteness
import LeanTrominoes.PeriodicThreeDMNormalizationStripAssignmentBounds
import LeanTrominoes.PeriodicThreeDMNormalizationStripTargetOccurrence

/-!
# Completeness of final normalized strip route ports
-/

namespace LeanTrominoes

namespace PeriodicThreeDM

/-- Every assignment in the flattened strip route suffix comes from a
displayed consecutive triple of one listed contracted edge. -/
theorem PlanarPresentation.exists_final_strip_route_triple_of_assignment_mem
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {assignment : NormalizedCellAssignment}
    (member : assignment ∈ presentation.finalStripRouteAssignments) :
    ∃ edge ∈ problem.contractedEdges,
      ∃ leading before current after rest,
        presentation.finalNormalizationRoute edge =
            leading ++ before :: current :: after :: rest ∧
          assignment =
            (stripRasterLocation presentation.finalNormalizationPeriod current,
              routingCellTypeAt before current after edge.color) := by
  simp only [PlanarPresentation.finalStripRouteAssignments,
    List.mem_flatMap] at member
  rcases member with ⟨edge, edgeMember, assignmentMember⟩
  rcases exists_route_triple_of_mem_stripRouteInteriorAssignments
      presentation.finalNormalizationPeriod edge.color assignmentMember with
    ⟨leading, before, current, after, rest,
      routeEquation, assignmentEquation⟩
  exact ⟨edge, edgeMember, leading, before, current, after, rest,
    routeEquation, assignmentEquation⟩

end PeriodicThreeDM
end LeanTrominoes
