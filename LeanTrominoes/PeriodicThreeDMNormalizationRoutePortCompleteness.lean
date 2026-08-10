import LeanTrominoes.PeriodicThreeDMNormalizationVertexPortCompleteness
import LeanTrominoes.PeriodicThreeDMNormalizationRouteRasterization

/-!
# Completeness of final normalized route ports

This module inverts the recursive route rasterizer.  Every emitted interior
assignment is shown to arise from a displayed consecutive triple of one
listed final route, and its only exposed sides point to the predecessor and
successor of that triple.
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- Membership in the recursive route-interior compiler exposes the complete
route context of the emitted three-point window. -/
theorem exists_route_triple_of_mem_routeInteriorAssignments
    (period : Nat) (color : WireColor) :
    ∀ {route : List Cell} {assignment : NormalizedCellAssignment},
      assignment ∈ routeInteriorAssignments period color route →
        ∃ leading before current after rest,
          route = leading ++ before :: current :: after :: rest ∧
            assignment =
              (rasterLocation period current,
                routingCellTypeAt before current after color)
  | [], _, member => by simp [routeInteriorAssignments] at member
  | [_], _, member => by simp [routeInteriorAssignments] at member
  | [_, _], _, member => by simp [routeInteriorAssignments] at member
  | before :: current :: after :: rest, assignment, member => by
      simp only [routeInteriorAssignments, List.mem_cons] at member
      rcases member with equal | tailMember
      · exact ⟨[], before, current, after, rest, by simp, equal⟩
      · rcases exists_route_triple_of_mem_routeInteriorAssignments
          period color tailMember with
        ⟨leading, previous, middle, next, trailing,
          routeEquation, assignmentEquation⟩
        exact ⟨before :: leading, previous, middle, next, trailing,
          by simp [routeEquation], assignmentEquation⟩

/-- An exposed port of a valid routing triple has the route color and points
to exactly the predecessor or successor. -/
theorem routingCellTypeAt_portColor_eq_some_classify
    {before current after : Cell}
    (incoming : AxisDirection.IsUnitAxisStep before current)
    (outgoing : AxisDirection.IsUnitAxisStep current after)
    (noReverse :
      AxisDirection.between current after ≠
        (AxisDirection.between before current).opposite)
    (color exposedColor : WireColor) (side : Side)
    (exposed :
      (routingCellTypeAt before current after color).portColor side =
        some exposedColor) :
    exposedColor = color ∧
      (side = Side.ofAxisDirection
          (AxisDirection.between current before) ∨
        side = Side.ofAxisDirection
          (AxisDirection.between current after)) := by
  rw [routingCellTypeAt_portColor incoming outgoing noReverse] at exposed
  split at exposed
  next selected =>
    exact ⟨(Option.some.inj exposed).symm, selected⟩
  next notSelected => contradiction

/-- Every assignment in the flattened final route suffix comes from a
displayed consecutive triple of one listed contracted edge. -/
theorem PlanarPresentation.exists_final_route_triple_of_assignment_mem
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {assignment : NormalizedCellAssignment}
    (member : assignment ∈ presentation.finalRouteAssignments) :
    ∃ edge ∈ problem.contractedEdges,
      ∃ leading before current after rest,
        presentation.finalNormalizationRoute edge =
            leading ++ before :: current :: after :: rest ∧
          assignment =
            (rasterLocation presentation.finalNormalizationPeriod current,
              routingCellTypeAt before current after edge.color) := by
  simp only [PlanarPresentation.finalRouteAssignments,
    List.mem_flatMap] at member
  rcases member with ⟨edge, edgeMember, assignmentMember⟩
  rcases exists_route_triple_of_mem_routeInteriorAssignments
      presentation.finalNormalizationPeriod edge.color assignmentMember with
    ⟨leading, before, current, after, rest,
      routeEquation, assignmentEquation⟩
  exact ⟨edge, edgeMember, leading, before, current, after, rest,
    routeEquation, assignmentEquation⟩

end PeriodicThreeDM
end LeanTrominoes
