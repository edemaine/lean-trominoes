import LeanTrominoes.PeriodicThreeDMNormalizationSpliceComputability

/-!
# Computability of initial contracted vertex positions
-/

noncomputable section

namespace LeanTrominoes

open Gadget
open DegreeThreeVertexNormalization
open LeanTrominoes.Computability

namespace PeriodicThreeDM
namespace NormalizationCompiler

set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem normalizationPosition0_primrec :
    Primrec fun input : Input × PeriodicThreeDMVertex =>
      normalizationPosition0 input.1 input.2 := by
  have vertices : Primrec (fun input : Input × PeriodicThreeDMVertex =>
      input.1.problem.contractedGraph.vertices) :=
    contractedGraphVertices_primrec.comp
      (Input.problem_primrec.comp Primrec.fst)
  have drawing : Primrec (fun input : Input × PeriodicThreeDMVertex =>
      contractedDrawing input.1) :=
    contractedDrawing_primrec.comp Primrec.fst
  exact (vertexPosition_primrec.comp
    (Primrec.pair (Primrec.pair vertices drawing) Primrec.snd)).of_eq
      fun _ => rfl

end NormalizationCompiler
end PeriodicThreeDM
end LeanTrominoes
