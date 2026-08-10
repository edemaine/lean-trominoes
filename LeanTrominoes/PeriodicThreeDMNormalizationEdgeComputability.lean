import LeanTrominoes.PeriodicThreeDMNormalizationTargetComputability

/-!
# Primitive-recursive contracted-edge endpoint data
-/

noncomputable section

namespace LeanTrominoes

open Gadget
open LeanTrominoes.Computability

namespace PeriodicThreeDM
namespace NormalizationCompiler

set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem contractedEdge_sourceVertex_primrec :
    Primrec fun edge : ContractedEdge => edge.toPeriodicEdge.source :=
  periodicEdge_source_primrec.comp contractedEdge_toPeriodicEdge_primrec

theorem contractedEdge_targetVertex_primrec :
    Primrec fun edge : ContractedEdge => edge.toPeriodicEdge.target :=
  periodicEdge_target_primrec.comp contractedEdge_toPeriodicEdge_primrec

theorem contractedEdge_sourceEndpoint_primrec :
    Primrec fun edge : ContractedEdge => ContractedEndpoint.source edge :=
  contractedEndpoint_source_primrec

theorem contractedEdge_targetEndpoint_primrec :
    Primrec fun edge : ContractedEdge => ContractedEndpoint.target edge :=
  contractedEndpoint_target_primrec

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
