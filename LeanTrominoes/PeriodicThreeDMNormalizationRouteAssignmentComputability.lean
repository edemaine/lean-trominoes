import LeanTrominoes.PeriodicThreeDMNormalizationVertexAssignmentComputability

/-! # Computability of normalized edge-route assignments -/

noncomputable section
namespace LeanTrominoes
open Gadget LeanTrominoes.Computability
namespace PeriodicThreeDM.NormalizationCompiler
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

def finalRouteAssignmentInput
    (input : Input × ContractedEdge) :
    RouteInteriorAssignmentsInput :=
  ((finalNormalizationPeriod input.1, input.2.color),
    finalNormalizationRoute input.1 input.2)

theorem finalRouteAssignmentInput_primrec :
    Primrec finalRouteAssignmentInput :=
  (Primrec.pair
    (Primrec.pair
      (finalNormalizationPeriod_primrec.comp Primrec.fst)
      (contractedEdge_color_primrec.comp Primrec.snd))
    finalNormalizationRoute_primrec).of_eq fun _ => rfl

def finalRouteAssignmentsForEdge
    (input : Input × ContractedEdge) :
    List NormalizedCellAssignment :=
  routeInteriorAssignments
    (finalRouteAssignmentInput input).1.1
    (finalRouteAssignmentInput input).1.2
    (finalRouteAssignmentInput input).2

theorem finalRouteAssignmentsForEdge_primrec :
    Primrec finalRouteAssignmentsForEdge :=
  (routeInteriorAssignments_primrec.comp
    finalRouteAssignmentInput_primrec).of_eq fun _ => rfl

theorem finalRouteAssignments_primrec :
    Primrec finalRouteAssignments := by
  have edges : Primrec fun input : Input =>
      input.problem.contractedEdges :=
    contractedEdges_primrec.comp Input.problem_primrec
  exact (Primrec.list_flatMap edges
    finalRouteAssignmentsForEdge_primrec.to₂).of_eq fun _ => rfl

end PeriodicThreeDM.NormalizationCompiler
end LeanTrominoes
