/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.CNF.FiniteRouteRasterPaddingCompiler

/-! # Reuse the original route field machines for the finite padded input -/
noncomputable section
namespace LeanTrominoes.FiniteNormalizationRoutePaddingCompiler
open _root_.Computability Turing PeriodicCNFStripReduction.RouteRasterRequest
open PeriodicThreeDM.NormalizationCompiler
open UnaryFieldEncoderMachine (unaryFields)

variable {Symbol : Type} [Fintype Symbol] [Inhabited Symbol]
variable (inputs : List Symbol → Input) (units : List Symbol → List Unit)
variable (unitLength : ∀ source,(units source).length=(inputs source).drawing.gridSize)
variable (zero : ∀ source,(inputs source).problem.ZeroOffsets)
variable (vertexLength : ∀ source,(inputs source).drawing.vertexPositions.length=
    (inputs source).problem.incidenceGraph.vertices.length)
variable (bounds : ∀ source vertex,vertex∈(inputs source).problem.contractedGraph.vertices →
    let point := (inputs source).drawing.vertexPosition (inputs source).problem.incidenceGraph vertex
    0≤point.1 ∧ point.1<((inputs source).drawing.gridSize:Int) ∧
    0≤point.2 ∧ point.2<((inputs source).drawing.gridSize:Int))

def requests (source : List Symbol) : List Request :=
  (inputs source).problem.contractedEdges.map (ofEdge (inputs source))

include unitLength zero vertexLength bounds in
private theorem requests_eq (source : List Symbol) :
    finitePadRequests (requests inputs) units source=
      (inputs source).finitePad.problem.contractedEdges.map (ofEdge (inputs source).finitePad) := by
  simp only [finitePadRequests,requests,List.map_map,Function.comp_def,Input.finitePad_problem]
  rw [unitLength]
  apply List.map_congr_left
  intro edge member
  exact (ofEdge_finitePad (inputs source) (zero source) (vertexLength source) (bounds source) member).symm

/-- Every finite padded request is serialized using the original field
compilers followed by the checked unary padding adapters. -/
def computableInPolyTime
    (gridCompiler : TM2ComputableInPolyTime id unaryFields
      (fun source => (requests inputs source).map (fun request => request.metadata.gridSize)))
    (xCompiler : TM2ComputableInPolyTime id unaryFields
      (fun source => (requests inputs source).map (fun request => request.metadata.horizontal)))
    (yCompiler : TM2ComputableInPolyTime id unaryFields
      (fun source => (requests inputs source).map (fun request => request.metadata.verticalComplement)))
    (colorCompiler : TM2ComputableInPolyTime id id
      (fun source => (requests inputs source).map (fun request => request.metadata.color)))
    (normalizationCompiler : TM2ComputableInPolyTime id id
      (fun source => PeriodicThreeDM.NormalizationDirectionRequest.Batch.tokens ((requests inputs source).map (fun request => request.normalization))))
    (unitCompiler : TM2ComputableInPolyTime id id units) :
    TM2ComputableInPolyTime id id
      (fun source => GadgetSparseRouteRasterRequestTokens.tokens
        ((inputs source).finitePad.problem.contractedEdges.map (ofEdge (inputs source).finitePad))) := by
  let compiler := finitePadRequestsComputableInPolyTime (requests inputs) units
    gridCompiler xCompiler yCompiler colorCompiler normalizationCompiler unitCompiler
  exact compiler.of_eq (fun source => congrArg GadgetSparseRouteRasterRequestTokens.tokens
    (requests_eq inputs units unitLength zero vertexLength bounds source))
end LeanTrominoes.FiniteNormalizationRoutePaddingCompiler
