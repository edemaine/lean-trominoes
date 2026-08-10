import LeanTrominoes.PeriodicThreeDMNormalizationVertexOrientation
import LeanTrominoes.PeriodicThreeDMContractedTagEndpoints
import LeanTrominoes.PeriodicThreeDMNormalizationOrientationOccurrence

/-!
# Reading a 3DM orientation from a normalized drawing

An original incidence tag has a unique endpoint at a contracted triple
vertex.  This module reads the drawing orientation at that endpoint and
negates the inward value, recovering the original triple-to-element Boolean.
It proves the first half of validity of the extracted assignment: the three
colors at every translated triple are coherent.
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

set_option maxRecDepth 2048

/-- Every color at an in-range triple index is one of the problem's original
incidence tags. -/
theorem tripleIncidenceTag_mem_incidenceTags
    (problem : PeriodicThreeDM) (tripleIndex : Nat)
    (indexLt : tripleIndex < problem.triples.length)
    (color : WireColor) :
    (⟨tripleIndex, color⟩ : IncidenceTag) ∈ problem.incidenceTags := by
  rw [problem.incidenceTags_eq_range_flatMap]
  apply List.mem_flatMap.mpr
  refine ⟨tripleIndex, List.mem_range.mpr indexLt, ?_⟩
  cases color <;> simp [tripleIncidenceTags, incidenceColors]

/-- A triple endpoint is also an endpoint in the complete contracted-edge
enumeration. -/
theorem contractedTripleEndpoint_mem_contractedEndpoints
    (problem : PeriodicThreeDM) {endpoint : ContractedEndpoint}
    (member : endpoint ∈ problem.contractedTripleEndpoints) :
    endpoint ∈ problem.contractedEndpoints := by
  unfold contractedTripleEndpoints at member
  rcases List.mem_flatMap.mp member with
    ⟨edge, edgeMember, endpointMember⟩
  unfold contractedEndpoints
  apply List.mem_flatMap.mpr
  refine ⟨edge, edgeMember, ?_⟩
  cases edge <;> simp_all [ContractedEdge.tripleEndpoints]

/-- The vertex of a listed triple endpoint is the triple named by its
incidence tag. -/
theorem ContractedEndpoint.vertex_eq_triple_incidenceTag
    {problem : PeriodicThreeDM} {endpoint : ContractedEndpoint}
    (member : endpoint ∈ problem.contractedTripleEndpoints) :
    endpoint.vertex = .triple endpoint.incidenceTag.tripleIndex := by
  unfold contractedTripleEndpoints at member
  rcases List.mem_flatMap.mp member with
    ⟨edge, edgeMember, endpointMember⟩
  cases edge with
  | retained color atom incidence =>
      simp only [ContractedEdge.tripleEndpoints, List.mem_singleton]
        at endpointMember
      subst endpoint
      rfl
  | through color atom first second =>
      simp [ContractedEdge.tripleEndpoints] at endpointMember
      rcases endpointMember with rfl | rfl <;> rfl

/-- The infinite-lift drawing location of one contracted endpoint, based at
the lattice translate of its endpoint vertex. -/
def PlanarPresentation.endpointDrawingLocation
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (endpoint : ContractedEndpoint) (translate : Cell) : Cell :=
  reflectedLocation
    (Cell.add (presentation.finalNormalizationPosition endpoint.vertex)
      (Cell.scale (presentation.finalNormalizationPeriod : Int) translate))

/-- Read the inward half-edge value at a contracted endpoint's normalized
vertex port. -/
def PlanarPresentation.drawingEndpointInward
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (orientation : presentation.normalizedOrthogonalDrawing.Orientation)
    (endpoint : ContractedEndpoint) (translate : Cell) : Bool :=
  orientation (presentation.endpointDrawingLocation endpoint translate)
    (endpoint.finalNormalizedPort presentation).side

/-- Extract the original triple-to-element Boolean carried by every incidence
tag.  Values outside the finite presentation use the selector's harmless
fallback and are irrelevant to the orientation predicates. -/
noncomputable def PlanarPresentation.reverseGraphOrientation
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (orientation : presentation.normalizedOrthogonalDrawing.Orientation) :
    problem.GraphOrientation :=
  fun tag translate =>
    !(presentation.drawingEndpointInward orientation
      (problem.contractedTripleEndpointForTag tag) translate)

/-- At an explicit occurrence of a listed vertex, validity of the global
drawing orientation supplies the corresponding local vertex constraint. -/
theorem ContinuousPlanarPresentation.finalVertexCellType_satisfied_of_orientation
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (collisionFree :
      presentation.toPlanarPresentation.FinalAssignmentsCollisionFree)
    (orientation :
      presentation.toPlanarPresentation.normalizedOrthogonalDrawing.Orientation)
    (valid :
      presentation.toPlanarPresentation.normalizedOrthogonalDrawing.IsOrientation
        orientation)
    {vertex : PeriodicThreeDMVertex}
    (vertexMember : vertex ∈ problem.contractedGraph.vertices)
    (translate : Cell) :
    let planar := presentation.toPlanarPresentation
    PeriodicOrthogonalDrawing.satisfiesOrientation
      (planar.finalVertexCellType vertex)
      (fun side => orientation
        (reflectedLocation
          (Cell.add (planar.finalNormalizationPosition vertex)
            (Cell.scale (planar.finalNormalizationPeriod : Int) translate)))
        side) := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  have siteMember := planar.finalOrientationSite_vertex_mem vertexMember
  have lookup := planar.finalOrientationSiteAt_reflected_periodOccurrence
    collisionFree siteMember (translate := translate)
  have cellType :=
    planar.normalizedOrthogonalDrawing_getAt_eq_of_site_lookup
      collisionFree lookup
  have cellType' :
      planar.normalizedOrthogonalDrawing.getAt
          (reflectedLocation
            (Cell.add (planar.finalNormalizationPosition vertex)
              (Cell.scale (planar.finalNormalizationPeriod : Int)
                translate))) =
        planar.finalVertexCellType vertex := by
    simpa [FinalOrientationSite.cellType, FinalOrientationSite.point] using
      cellType
  have localConstraint := valid.1
    (reflectedLocation
      (Cell.add (planar.finalNormalizationPosition vertex)
        (Cell.scale (planar.finalNormalizationPeriod : Int) translate)))
  rw [cellType'] at localConstraint
  simpa [planar] using localConstraint

/-- Any two contracted endpoints at the same translated triple vertex have
equal inward drawing values. -/
theorem ContinuousPlanarPresentation.drawingEndpointInward_eq_at_triple
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (collisionFree :
      presentation.toPlanarPresentation.FinalAssignmentsCollisionFree)
    (orientation :
      presentation.toPlanarPresentation.normalizedOrthogonalDrawing.Orientation)
    (valid :
      presentation.toPlanarPresentation.normalizedOrthogonalDrawing.IsOrientation
        orientation)
    {first second : ContractedEndpoint}
    (firstMember : first ∈ problem.contractedEndpoints)
    (tripleIndex : Nat)
    (firstVertex : first.vertex = .triple tripleIndex)
    (secondVertex : second.vertex = .triple tripleIndex)
    (translate : Cell) :
    presentation.toPlanarPresentation.drawingEndpointInward orientation
        first translate =
      presentation.toPlanarPresentation.drawingEndpointInward orientation
        second translate := by
  let planar := presentation.toPlanarPresentation
  have vertexMember := first.vertex_mem_of_mem firstMember
  rw [firstVertex] at vertexMember
  have localConstraint :=
    presentation.finalVertexCellType_satisfied_of_orientation
    collisionFree orientation valid vertexMember translate
  change PeriodicOrthogonalDrawing.satisfiesOrientation
      (planar.finalVertexCellType (.triple tripleIndex)) _ at localConstraint
  change orientation (planar.endpointDrawingLocation first translate)
      (first.finalNormalizedPort planar).side =
    orientation (planar.endpointDrawingLocation second translate)
      (second.finalNormalizedPort planar).side
  rw [show planar.endpointDrawingLocation first translate =
      reflectedLocation
        (Cell.add (planar.finalNormalizationPosition (.triple tripleIndex))
          (Cell.scale (planar.finalNormalizationPeriod : Int) translate)) by
        simp [PlanarPresentation.endpointDrawingLocation, firstVertex]]
  rw [show planar.endpointDrawingLocation second translate =
      reflectedLocation
        (Cell.add (planar.finalNormalizationPosition (.triple tripleIndex))
          (Cell.scale (planar.finalNormalizationPeriod : Int) translate)) by
        simp [PlanarPresentation.endpointDrawingLocation, secondVertex]]
  dsimp only [planar]
  simp only [PlanarPresentation.finalVertexCellType,
    PeriodicOrthogonalDrawing.satisfiesOrientation] at localConstraint
  generalize firstPortEq : first.finalNormalizedPort planar = firstPort
  generalize secondPortEq : second.finalNormalizedPort planar = secondPort
  cases firstPort <;> cases secondPort <;>
    simp_all [CanonicalVertexPort.side]

/-- The selected endpoint for every valid tag is based at that tag's triple
vertex. -/
theorem contractedTripleEndpointForTag_vertex
    (problem : PeriodicThreeDM)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    {tag : IncidenceTag} (tagMember : tag ∈ problem.incidenceTags) :
    (problem.contractedTripleEndpointForTag tag).vertex =
      .triple tag.tripleIndex := by
  let endpoint := problem.contractedTripleEndpointForTag tag
  have endpointMember := problem.contractedTripleEndpointForTag_mem
    wellFormed degree tagMember
  have endpointTag := problem.contractedTripleEndpointForTag_incidenceTag
    wellFormed degree tagMember
  have vertexEq := endpoint.vertex_eq_triple_incidenceTag endpointMember
  rw [endpointTag] at vertexEq
  exact vertexEq

/-- The drawing-derived graph assignment is coherent at every translated
triple vertex. -/
theorem ContinuousPlanarPresentation.reverseGraphOrientation_tripleCoherent
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (collisionFree :
      presentation.toPlanarPresentation.FinalAssignmentsCollisionFree)
    (orientation :
      presentation.toPlanarPresentation.normalizedOrthogonalDrawing.Orientation)
    (valid :
      presentation.toPlanarPresentation.normalizedOrthogonalDrawing.IsOrientation
        orientation) :
    problem.GraphTripleCoherent
      (presentation.toPlanarPresentation.reverseGraphOrientation orientation) := by
  intro tripleIndex indexLt translate
  let planar := presentation.toPlanarPresentation
  let redTag : IncidenceTag := ⟨tripleIndex, .red⟩
  let greenTag : IncidenceTag := ⟨tripleIndex, .green⟩
  let blueTag : IncidenceTag := ⟨tripleIndex, .blue⟩
  let redEndpoint := problem.contractedTripleEndpointForTag redTag
  let greenEndpoint := problem.contractedTripleEndpointForTag greenTag
  let blueEndpoint := problem.contractedTripleEndpointForTag blueTag
  have redTagMember := problem.tripleIncidenceTag_mem_incidenceTags
    tripleIndex indexLt .red
  have greenTagMember := problem.tripleIncidenceTag_mem_incidenceTags
    tripleIndex indexLt .green
  have blueTagMember := problem.tripleIncidenceTag_mem_incidenceTags
    tripleIndex indexLt .blue
  have redTripleMember := problem.contractedTripleEndpointForTag_mem
    wellFormed degree redTagMember
  have greenTripleMember := problem.contractedTripleEndpointForTag_mem
    wellFormed degree greenTagMember
  have redMember := problem.contractedTripleEndpoint_mem_contractedEndpoints
    redTripleMember
  have greenMember := problem.contractedTripleEndpoint_mem_contractedEndpoints
    greenTripleMember
  have redVertex := problem.contractedTripleEndpointForTag_vertex
    wellFormed degree redTagMember
  have greenVertex := problem.contractedTripleEndpointForTag_vertex
    wellFormed degree greenTagMember
  have blueVertex := problem.contractedTripleEndpointForTag_vertex
    wellFormed degree blueTagMember
  have redGreen := presentation.drawingEndpointInward_eq_at_triple
    collisionFree orientation valid redMember tripleIndex
      redVertex greenVertex translate
  have greenBlue := presentation.drawingEndpointInward_eq_at_triple
    collisionFree orientation valid greenMember tripleIndex
      greenVertex blueVertex translate
  change
    (!(planar.drawingEndpointInward orientation redEndpoint translate)) =
        (!(planar.drawingEndpointInward orientation greenEndpoint translate)) ∧
      (!(planar.drawingEndpointInward orientation greenEndpoint translate)) =
        (!(planar.drawingEndpointInward orientation blueEndpoint translate))
  exact ⟨congrArg (fun value : Bool => !value) redGreen,
    congrArg (fun value : Bool => !value) greenBlue⟩

end PeriodicThreeDM

end LeanTrominoes
