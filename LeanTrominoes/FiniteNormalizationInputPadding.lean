/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteGridDrawingPadding
import LeanTrominoes.FiniteThreeDMContractionOffsets
import LeanTrominoes.PeriodicThreeDMNormalizationDirectionRequests
import LeanTrominoes.OrthogonalPolylineEndpointDirections
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirectionTranslation

/-! # Padding preserves the compiler's contracted route directions -/
namespace LeanTrominoes.PeriodicThreeDM.NormalizationCompiler
open PeriodicOrthocrossing Gadget

def Input.finitePad (input : Input) : Input :=
  ⟨input.problem,input.drawing.finitePad⟩

@[simp] theorem Input.finitePad_problem (input : Input) : input.finitePad.problem=input.problem := rfl
@[simp] theorem Input.finitePad_drawing (input : Input) : input.finitePad.drawing=input.drawing.finitePad := rfl

theorem incidenceRoute_finitePad (input : Input) (tag : IncidenceTag) :
    incidenceRoute input.finitePad tag=translatePolyline input.drawing.finitePaddingOffset
      (incidenceRoute input tag) :=
  PeriodicGridDrawing.finitePad_edgeRoute _ _

theorem contractedEdgeRoute_finitePad (input : Input) (zero : input.problem.ZeroOffsets)
    {edge : ContractedEdge} (member : edge∈input.problem.contractedEdges) :
    contractedEdgeRoute input.finitePad edge=translatePolyline input.drawing.finitePaddingOffset
      (contractedEdgeRoute input edge) := by
  simp only [contractedEdges,List.mem_flatMap] at member
  obtain ⟨color,_,member⟩ := member
  simp only [contractedEdgesForColor,List.mem_flatMap] at member
  obtain ⟨atom,_,member⟩ := member
  have metadata := contractedEdgesForElement_metadata input.problem color atom member
  have incidences := contractedEdgesForElement_incidence_members input.problem color atom member
  cases edge with
  | retained edgeColor edgeAtom incidence =>
      exact incidenceRoute_finitePad input _
  | through edgeColor edgeAtom first second =>
      simp only [ContractedEdge.color,ContractedEdge.atom] at metadata
      obtain ⟨rfl,rfl⟩ := metadata
      have firstZero := incidence_offset_eq_zero zero edgeColor edgeAtom
        (by simpa only [ContractedEdge.sourceIncidence] using incidences.1)
      have secondZero := incidence_offset_eq_zero zero edgeColor edgeAtom
        (by simpa only [ContractedEdge.targetIncidence] using incidences.2.1)
      simp only [contractedEdgeRoute,reversedIncidenceRouteAt,incidenceRoute_finitePad,
        firstZero,secondZero,Cell.sub,sub_self]
      simp [Input.finitePad,PeriodicGridDrawing.periodTranslation,Cell.scale,Cell.add,
        translatePolyline,joinPolylines,List.map_append,Function.comp_def]

theorem outwardDirection_finitePad (input : Input) (zero : input.problem.ZeroOffsets)
    {endpoint : ContractedEndpoint} (member : endpoint.edge∈input.problem.contractedEdges) :
    outwardDirection input.finitePad endpoint=outwardDirection input endpoint := by
  cases endpoint with
  | source edge =>
      change edge∈input.problem.contractedEdges at member
      change AxisDirection.polylineFirstDirection (contractedEdgeRoute input.finitePad edge)=
        AxisDirection.polylineFirstDirection (contractedEdgeRoute input edge)
      rw [contractedEdgeRoute_finitePad input zero member,
        AxisDirection.polylineFirstDirection_translatePolyline]
  | target edge =>
      change edge∈input.problem.contractedEdges at member
      change (AxisDirection.polylineLastDirection (contractedEdgeRoute input.finitePad edge)).opposite=
        (AxisDirection.polylineLastDirection (contractedEdgeRoute input edge)).opposite
      rw [contractedEdgeRoute_finitePad input zero member,
        AxisDirection.polylineLastDirection_translatePolyline]

theorem outwardSide_finitePad (input : Input) (zero : input.problem.ZeroOffsets)
    {endpoint : ContractedEndpoint} (member : endpoint.edge∈input.problem.contractedEdges) :
    outwardSide input.finitePad endpoint=outwardSide input endpoint := by
  unfold outwardSide
  rw [outwardDirection_finitePad input zero member]

private theorem tripleEdges_mem (problem : PeriodicThreeDM) (vertex : PeriodicThreeDMVertex)
    {first second third : ContractedEndpoint}
    (atTriple : problem.endpointTripleAt vertex=some (first,second,third)) :
    first.edge∈problem.contractedEdges ∧ second.edge∈problem.contractedEdges ∧ third.edge∈problem.contractedEdges := by
  unfold PeriodicThreeDM.endpointTripleAt at atTriple
  split at atTriple
  next a b c listEq =>
    simp only [Option.some.injEq,Prod.mk.injEq] at atTriple
    obtain ⟨rfl,rfl,rfl⟩ := atTriple
    have member (endpoint : ContractedEndpoint) (inTriple : endpoint∈[a,b,c]) :
        endpoint∈problem.contractedEndpoints :=
      ((contractedEndpointsAt_mem_iff problem vertex endpoint).mp (by rw [listEq];exact inTriple)).1
    exact ⟨ContractedEndpoint.edge_mem_of_mem (member a (by simp)),
      ContractedEndpoint.edge_mem_of_mem (member b (by simp)),
      ContractedEndpoint.edge_mem_of_mem (member c (by simp))⟩
  next => simp at atTriple

theorem omittedSideAt_finitePad (input : Input) (zero : input.problem.ZeroOffsets)
    (vertex : PeriodicThreeDMVertex) : omittedSideAt input.finitePad vertex=omittedSideAt input vertex := by
  cases fan : input.problem.endpointTripleAt vertex with
  | none => simp [omittedSideAt,Input.finitePad_problem,fan]
  | some triple =>
      obtain ⟨first,second,third⟩ := triple
      have members := tripleEdges_mem input.problem vertex fan
      simp only [omittedSideAt,Input.finitePad_problem,fan]
      rw [outwardSide_finitePad input zero members.1,outwardSide_finitePad input zero members.2.1,
        outwardSide_finitePad input zero members.2.2]

theorem endpointColorAtSide_finitePad (input : Input) (zero : input.problem.ZeroOffsets)
    (vertex : PeriodicThreeDMVertex) (side : VertexSide) :
    endpointColorAtSide input.finitePad vertex side=endpointColorAtSide input vertex side := by
  cases fan : input.problem.endpointTripleAt vertex with
  | none => simp [endpointColorAtSide,Input.finitePad_problem,fan]
  | some triple =>
      obtain ⟨first,second,third⟩ := triple
      have members := tripleEdges_mem input.problem vertex fan
      simp only [endpointColorAtSide,Input.finitePad_problem,fan]
      rw [outwardSide_finitePad input zero members.1,outwardSide_finitePad input zero members.2.1]

theorem canonicalColoringAt_finitePad (input : Input) (zero : input.problem.ZeroOffsets)
    (vertex : PeriodicThreeDMVertex) : canonicalColoringAt input.finitePad vertex=canonicalColoringAt input vertex := by
  funext port
  unfold canonicalColoringAt
  rw [omittedSideAt_finitePad input zero,endpointColorAtSide_finitePad input zero]

theorem finalVertexCellType_finitePad (input : Input) (zero : input.problem.ZeroOffsets)
    (vertex : PeriodicThreeDMVertex) : finalVertexCellType input.finitePad vertex=finalVertexCellType input vertex := by
  cases vertex with
  | triple index => simp only [finalVertexCellType,canonicalColoringAt_finitePad input zero]
  | element color atom => rfl

theorem rotationCountAt_finitePad (input : Input) (zero : input.problem.ZeroOffsets)
    (vertex : PeriodicThreeDMVertex) : rotationCountAt input.finitePad vertex=rotationCountAt input vertex := by
  cases vertex with
  | triple index => simp only [rotationCountAt,canonicalColoringAt_finitePad input zero]
  | element color atom => rfl

theorem firstNormalizedPort_finitePad (input : Input) (zero : input.problem.ZeroOffsets)
    {endpoint : ContractedEndpoint} (member : endpoint.edge∈input.problem.contractedEdges) :
    firstNormalizedPort input.finitePad endpoint=firstNormalizedPort input endpoint := by
  unfold firstNormalizedPort
  rw [omittedSideAt_finitePad input zero,outwardSide_finitePad input zero member]

theorem firstRotationActive_finitePad (input : Input) (zero : input.problem.ZeroOffsets)
    (vertex : PeriodicThreeDMVertex) : firstRotationActive input.finitePad vertex=firstRotationActive input vertex := by
  unfold firstRotationActive
  rw [rotationCountAt_finitePad input zero]

theorem secondRotationActive_finitePad (input : Input) (zero : input.problem.ZeroOffsets)
    (vertex : PeriodicThreeDMVertex) : secondRotationActive input.finitePad vertex=secondRotationActive input vertex := by
  unfold secondRotationActive
  rw [rotationCountAt_finitePad input zero]

theorem secondNormalizedPort_finitePad (input : Input) (zero : input.problem.ZeroOffsets)
    {endpoint : ContractedEndpoint} (member : endpoint.edge∈input.problem.contractedEdges) :
    secondNormalizedPort input.finitePad endpoint=secondNormalizedPort input endpoint := by
  unfold secondNormalizedPort
  rw [firstRotationActive_finitePad input zero,firstNormalizedPort_finitePad input zero member]

/-- Compact normalization requests can reuse the original contracted direction
word after padding the coordinate metadata. -/
theorem contractedDirections_finitePad (input : Input) (zero : input.problem.ZeroOffsets)
    {edge : ContractedEdge} (member : edge∈input.problem.contractedEdges) :
    Gadget.unitSubdivisionDirections (contractedEdgeRoute input.finitePad edge)=
      Gadget.unitSubdivisionDirections (contractedEdgeRoute input edge) := by
  rw [contractedEdgeRoute_finitePad input zero member,
    Gadget.unitSubdivisionDirections_translatePolyline]
/-- The entire finite request, including all six template choices, is unchanged. -/
theorem normalizationRequest_finitePad (input : Input) (zero : input.problem.ZeroOffsets)
    {edge : ContractedEdge} (member : edge∈input.problem.contractedEdges) :
    NormalizationDirectionRequest.ofEdge input.finitePad edge=NormalizationDirectionRequest.ofEdge input edge := by
  have sourceMember : (ContractedEndpoint.source edge).edge∈input.problem.contractedEdges := member
  have targetMember : (ContractedEndpoint.target edge).edge∈input.problem.contractedEdges := member
  simp only [NormalizationDirectionRequest.ofEdge,omittedSideAt_finitePad input zero,
    firstNormalizedPort_finitePad input zero sourceMember,firstNormalizedPort_finitePad input zero targetMember,
    firstRotationActive_finitePad input zero,secondRotationActive_finitePad input zero,
    secondNormalizedPort_finitePad input zero sourceMember,secondNormalizedPort_finitePad input zero targetMember,
    contractedDirections_finitePad input zero member]
end LeanTrominoes.PeriodicThreeDM.NormalizationCompiler
