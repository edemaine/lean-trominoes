/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteNormalizationRecordSemantics
import LeanTrominoes.FiniteSparseAssignmentSeamCompiler
import LeanTrominoes.GadgetSparseRouteRequestRenderingCompiler
import LeanTrominoes.FiniteGadgetRegionCompiler
import LeanTrominoes.TM2ListAppendClosure

/-! # Actual finite-region emission from compact padded normalization records -/
noncomputable section
namespace LeanTrominoes.FiniteNormalizationRegionCompiler
open _root_.Computability Turing Gadget PeriodicCNFStripReduction
open PeriodicThreeDM.NormalizationCompiler
open GadgetSparseAssignmentTokens (assignmentsTokens)

variable {Source Symbol : Type} [Fintype Symbol] [Inhabited Symbol]
variable (encodeSource : Source → List Symbol) (inputs : Source → Input)
variable (bounds : ∀ source vertex,vertex∈(inputs source).problem.contractedGraph.vertices →
    let position := (inputs source).drawing.vertexPosition (inputs source).problem.incidenceGraph vertex
    0≤position.1 ∧ position.1<((inputs source).drawing.gridSize:Int) ∧
    0≤position.2 ∧ position.2<((inputs source).drawing.gridSize:Int))
variable (conditions : ∀ source edge,edge∈(inputs source).problem.contractedEdges →
    RouteDirectionConditions (inputs source) edge)
variable (vertices : TM2ComputableInPolyTime encodeSource id
    (fun source => (inputs source).problem.contractedGraph.vertices.flatMap
      (sparseBoundedInputVertexRequestRecord (inputs source))))
variable (routes : TM2ComputableInPolyTime encodeSource id
    (fun source => GadgetSparseRouteRasterRequestTokens.tokens
      ((inputs source).problem.contractedEdges.map (RouteRasterRequest.ofEdge (inputs source)))))

include bounds in
private theorem vertexExpand_eq (source : Source) :
    GadgetSparseAffineVertexTokens.expand
      ((inputs source).problem.contractedGraph.vertices.flatMap
        (sparseBoundedInputVertexRequestRecord (inputs source)))=
      assignmentsTokens (finalStripVertexAssignments (inputs source)) := by
  rw [affineExpand_flatMap,vertexRecords_eq_flatMap]
  apply List.flatMap_congr
  intro vertex member
  have inside := bounds source vertex member
  rw [expand_sparseBoundedInputVertexRequestRecord _ vertex inside.1 inside.2.1 inside.2.2.1 inside.2.2.2,
    sparseVertexRecordBlock_eq_input _ member,
    sparseInputVertexRecordAssignment_eq_bounded _ vertex inside.1 inside.2.1]

include bounds in
private theorem routeCursorValid (source : Source) (edge : PeriodicThreeDM.ContractedEdge)
    (member : edge∈(inputs source).problem.contractedEdges) :
    (RouteRasterRequest.ofEdge (inputs source) edge).metadata.CursorValid := by
  have inside := bounds source edge.toPeriodicEdge.source
    (RouteRasterRequest.contractedEdge_source_mem (inputs source).problem member)
  have natBound : ((inputs source).drawing.vertexPosition
      (inputs source).problem.incidenceGraph edge.toPeriodicEdge.source).1.toNat <
      (inputs source).drawing.gridSize := by omega
  unfold RouteRasterRequest.ofEdge RouteRasterRequest.Metadata.CursorValid
    RouteRasterRequest.Metadata.cursorHorizontal RouteRasterRequest.Metadata.period
  change 1728*((inputs source).drawing.vertexPosition
    (inputs source).problem.incidenceGraph edge.toPeriodicEdge.source).1.toNat+471 <
    1728*(inputs source).drawing.gridSize
  omega

/-- The two compact source emitters produce the canonical assignment stream
of the padded normalization input. -/
def assignmentsComputableInPolyTime : TM2ComputableInPolyTime encodeSource id
    (fun source => assignmentsTokens (finalStripCellAssignments (inputs source))) := by
  let expanded := TM2CompositionMachine.computableInPolyTime vertices GadgetSparseAffineVertexTokens.computableInPolyTime
  let vertexRecords : TM2ComputableInPolyTime encodeSource id
      (fun source => assignmentsTokens (finalStripVertexAssignments (inputs source))) :=
    expanded.of_eq (vertexExpand_eq inputs bounds)
  let rendered := GadgetSparseRouteRequestRenderingCompiler.computableInPolyTime encodeSource
    (fun source => (inputs source).problem.contractedEdges.map (RouteRasterRequest.ofEdge (inputs source))) routes
    (fun source request member => by
      obtain ⟨edge,edgeMember,rfl⟩ := List.mem_map.mp member
      exact routeCursorValid inputs bounds source edge edgeMember)
  let routeRecords : TM2ComputableInPolyTime encodeSource id
      (fun source => assignmentsTokens (finalStripRouteAssignments (inputs source))) := by
    apply TM2ComputableInPolyTime.of_eq rendered
    intro source
    rw [List.flatMap_map,routeRecords_eq_flatMap]
    apply List.flatMap_congr
    intro edge member
    exact RouteRasterRequest.normalizedRecordBlock_ofEdge _ member
      (bounds source _ (RouteRasterRequest.contractedEdge_source_mem _ member)) (conditions source edge member)
  let appended := TM2ListAppend.computableInPolyTime vertexRecords routeRecords
  exact appended.of_eq (fun source => by
    rw [←GadgetSparseAssignmentTokens.assignmentsTokens_append]
    rfl)

/-- Seam subtraction and fixed gadget expansion emit the original finite
region encoding directly from the original source word. -/
def regionComputableInPolyTime (t : Tromino)
    (positive : ∀ source assignment,assignment∈finalStripCellAssignments (inputs source) →
      0<assignment.1.1 ∧ 0<assignment.1.2) :
    TM2ComputableInPolyTime encodeSource Tromino.FiniteCoordinateColumns.regionEncoding.encode
      (fun source => sparseExpandedMotif t
        ((finalStripCellAssignments (inputs source)).map FiniteSparseAssignmentSeamCompiler.shift)) := by
  let seam := FiniteSparseAssignmentSeamCompiler.ofEmitter encodeSource
    (fun source => finalStripCellAssignments (inputs source))
    (assignmentsComputableInPolyTime encodeSource inputs bounds conditions vertices routes) positive
  exact Gadget.FiniteRegionCompiler.computableInPolyTime t seam (fun source assignment member => by
    obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
    have inside := positive source original originalMember
    simp only [FiniteSparseAssignmentSeamCompiler.shift]
    omega)
end LeanTrominoes.FiniteNormalizationRegionCompiler
