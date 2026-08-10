import LeanTrominoes.PeriodicThreeDMNormalizationEndpointOrientation

/-!
# Local orientation semantics of normalized contracted vertices

The final west, north, and east ports are a permutation of the three
contracted endpoints at each retained vertex.  Consequently suppressed 3DM
triple coherence becomes the trichromatic vertex constraint, while exact
coverage at a retained degree-three element becomes the monochromatic
exact-one constraint.
-/

namespace LeanTrominoes

open Gadget
open DegreeThreeVertexNormalization

namespace PeriodicThreeDM

/-- Every canonical port of a compiled degree-three vertex is exposed with
some color. -/
theorem PlanarPresentation.finalVertexCellType_portColor_isSome
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (vertex : PeriodicThreeDMVertex)
    (port : CanonicalVertexPort) :
    ∃ color,
      (presentation.finalVertexCellType vertex).portColor port.side =
        some color := by
  cases vertex with
  | triple tripleIndex =>
      generalize orderEq :
        trichromaticOrder
          (canonicalColoringAt presentation (.triple tripleIndex)) = order
      cases order <;> cases port <;>
        simp [PlanarPresentation.finalVertexCellType,
          OrthogonalCellType.portColor, CanonicalVertexPort.side, orderEq]
  | element color atom =>
      cases port <;>
        simp [PlanarPresentation.finalVertexCellType,
          OrthogonalCellType.portColor, CanonicalVertexPort.side]

/-- The endpoints selected at the three canonical ports, in west/north/east
order. -/
def PlanarPresentation.normalizedVertexPortEndpoints
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (vertex : PeriodicThreeDMVertex) : List ContractedEndpoint :=
  [presentation.endpointAtVertexPort vertex .west,
    presentation.endpointAtVertexPort vertex .north,
    presentation.endpointAtVertexPort vertex .east]

/-- The three canonical port selectors enumerate exactly the endpoints at a
retained contracted vertex, up to their normalized geometric order. -/
theorem PlanarPresentation.normalizedVertexPortEndpoints_perm
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    {vertex : PeriodicThreeDMVertex}
    (vertexMember : vertex ∈ problem.contractedGraph.vertices) :
    List.Perm
      (presentation.toPlanarPresentation.normalizedVertexPortEndpoints vertex)
      (problem.contractedEndpointsAt vertex) := by
  let planar := presentation.toPlanarPresentation
  let westEndpoint := planar.endpointAtVertexPort vertex .west
  let northEndpoint := planar.endpointAtVertexPort vertex .north
  let eastEndpoint := planar.endpointAtVertexPort vertex .east
  obtain ⟨westColor, westExposed⟩ :=
    planar.finalVertexCellType_portColor_isSome vertex .west
  obtain ⟨northColor, northExposed⟩ :=
    planar.finalVertexCellType_portColor_isSome vertex .north
  obtain ⟨eastColor, eastExposed⟩ :=
    planar.finalVertexCellType_portColor_isSome vertex .east
  have westData :=
    PlanarPresentation.endpointAtVertexPort_data_of_exposed
      presentation wellFormed degree vertexMember westExposed
  have northData :=
    PlanarPresentation.endpointAtVertexPort_data_of_exposed
      presentation wellFormed degree vertexMember northExposed
  have eastData :=
    PlanarPresentation.endpointAtVertexPort_data_of_exposed
      presentation wellFormed degree vertexMember eastExposed
  change westEndpoint ∈ problem.contractedEndpoints ∧
      westEndpoint.vertex = vertex ∧
      (westEndpoint.finalNormalizedPort planar).side = .west ∧
      westEndpoint.color = westColor at westData
  change northEndpoint ∈ problem.contractedEndpoints ∧
      northEndpoint.vertex = vertex ∧
      (northEndpoint.finalNormalizedPort planar).side = .north ∧
      northEndpoint.color = northColor at northData
  change eastEndpoint ∈ problem.contractedEndpoints ∧
      eastEndpoint.vertex = vertex ∧
      (eastEndpoint.finalNormalizedPort planar).side = .east ∧
      eastEndpoint.color = eastColor at eastData
  have westNeNorth : westEndpoint ≠ northEndpoint := by
    intro equal
    subst northEndpoint
    simp_all
  have westNeEast : westEndpoint ≠ eastEndpoint := by
    intro equal
    subst eastEndpoint
    simp_all
  have northNeEast : northEndpoint ≠ eastEndpoint := by
    intro equal
    subst eastEndpoint
    simp_all
  have selectedNodup : [westEndpoint, northEndpoint, eastEndpoint].Nodup := by
    simp [westNeNorth, westNeEast, northNeEast]
  have endpointNodup := contractedEndpointsAt_nodup problem degree vertex
  apply (List.perm_ext_iff_of_nodup selectedNodup endpointNodup).mpr
  intro endpoint
  constructor
  · intro selectedMember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at selectedMember
    rcases selectedMember with rfl | rfl | rfl
    · exact (contractedEndpointsAt_mem_iff problem vertex westEndpoint).2
        ⟨westData.1, westData.2.1⟩
    · exact (contractedEndpointsAt_mem_iff problem vertex northEndpoint).2
        ⟨northData.1, northData.2.1⟩
    · exact (contractedEndpointsAt_mem_iff problem vertex eastEndpoint).2
        ⟨eastData.1, eastData.2.1⟩
  · intro endpointAt
    have endpointData :=
      (contractedEndpointsAt_mem_iff problem vertex endpoint).1 endpointAt
    have selected := PlanarPresentation.endpointAtVertexPort_eq
      presentation wellFormed degree endpointData.1
    rw [endpointData.2] at selected
    change planar.endpointAtVertexPort vertex
      (endpoint.finalNormalizedPort planar).side = endpoint at selected
    generalize portEq : endpoint.finalNormalizedPort planar = port at selected
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    cases port with
    | west => exact Or.inl selected.symm
    | north => exact Or.inr (Or.inl selected.symm)
    | east => exact Or.inr (Or.inr selected.symm)

/-- Any two canonical ports at a trichromatic vertex receive the same inward
value from a valid suppressed orientation. -/
theorem PlanarPresentation.vertexPortInward_eq_at_triple
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (values : problem.GraphOrientation)
    (valid : problem.IsSuppressedOrientation values)
    (tripleIndex : Nat)
    (indexLt : tripleIndex < problem.triples.length)
    (translate : Cell)
    (first second : CanonicalVertexPort) :
    presentation.toPlanarPresentation.vertexPortInward values
        (.triple tripleIndex) translate first.side =
      presentation.toPlanarPresentation.vertexPortInward values
        (.triple tripleIndex) translate second.side := by
  let planar := presentation.toPlanarPresentation
  have vertexMember :
      .triple tripleIndex ∈ problem.contractedGraph.vertices := by
    simp [contractedGraph, tripleVertices, indexLt]
  obtain ⟨firstColor, firstExposed⟩ :=
    planar.finalVertexCellType_portColor_isSome
      (.triple tripleIndex) first
  obtain ⟨secondColor, secondExposed⟩ :=
    planar.finalVertexCellType_portColor_isSome
      (.triple tripleIndex) second
  have firstData :=
    PlanarPresentation.endpointAtVertexPort_data_of_exposed
      presentation wellFormed degree vertexMember firstExposed
  have secondData :=
    PlanarPresentation.endpointAtVertexPort_data_of_exposed
      presentation wellFormed degree vertexMember secondExposed
  let firstEndpoint :=
    planar.endpointAtVertexPort (.triple tripleIndex) first.side
  let secondEndpoint :=
    planar.endpointAtVertexPort (.triple tripleIndex) second.side
  change firstEndpoint ∈ problem.contractedEndpoints ∧
      firstEndpoint.vertex = .triple tripleIndex ∧ _ at firstData
  change secondEndpoint ∈ problem.contractedEndpoints ∧
      secondEndpoint.vertex = .triple tripleIndex ∧ _ at secondData
  change firstEndpoint.inwardAtVertexTranslate values translate =
    secondEndpoint.inwardAtVertexTranslate values translate
  rw [firstEndpoint.inwardAtVertexTranslate_eq_not_value_of_triple
      values tripleIndex firstData.2.1 translate,
    secondEndpoint.inwardAtVertexTranslate_eq_not_value_of_triple
      values tripleIndex secondData.2.1 translate]
  have coherent := problem.tripleInward_coherent
    values valid tripleIndex indexLt translate
  cases firstEndpoint.color <;> cases secondEndpoint.color <;> simp_all

/-- A valid suppressed orientation satisfies every normalized
trichromatic vertex cell. -/
theorem PlanarPresentation.finalVertexCellType_satisfiesOrientation_triple
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (values : problem.GraphOrientation)
    (valid : problem.IsSuppressedOrientation values)
    (tripleIndex : Nat)
    (indexLt : tripleIndex < problem.triples.length)
    (translate : Cell) :
    PeriodicOrthogonalDrawing.satisfiesOrientation
      (presentation.toPlanarPresentation.finalVertexCellType
        (.triple tripleIndex))
      (presentation.toPlanarPresentation.vertexPortInward values
        (.triple tripleIndex) translate) := by
  change
    presentation.toPlanarPresentation.vertexPortInward values
          (.triple tripleIndex) translate .west =
        presentation.toPlanarPresentation.vertexPortInward values
          (.triple tripleIndex) translate .north ∧
      presentation.toPlanarPresentation.vertexPortInward values
          (.triple tripleIndex) translate .north =
        presentation.toPlanarPresentation.vertexPortInward values
          (.triple tripleIndex) translate .east
  exact
    ⟨PlanarPresentation.vertexPortInward_eq_at_triple
        presentation wellFormed degree values valid tripleIndex indexLt translate
        .west .north,
      PlanarPresentation.vertexPortInward_eq_at_triple
        presentation wellFormed degree values valid tripleIndex indexLt translate
        .north .east⟩

/-- An edge emitted for an in-range colored element belongs to the complete
contracted edge enumeration. -/
theorem contractedEdgesForElement_mem_contractedEdges
    (problem : PeriodicThreeDM)
    (color : WireColor) (atom : Nat)
    (atomLt : atom < problem.elementCount color)
    {edge : ContractedEdge}
    (member : edge ∈ problem.contractedEdgesForElement color atom) :
    edge ∈ problem.contractedEdges := by
  unfold contractedEdges
  apply List.mem_flatMap.mpr
  refine ⟨color, ?_, ?_⟩
  · cases color <;> simp [incidenceColors]
  · unfold contractedEdgesForColor
    exact List.mem_flatMap.mpr
      ⟨atom, List.mem_range.mpr atomLt, member⟩

/-- At a retained degree-three colored element, the three targets of its
edge block are exactly the contracted endpoints at that element vertex. -/
theorem contractedEdgesForElement_targets_perm_endpointsAt
    (problem : PeriodicThreeDM)
    (degree : problem.DegreeTwoOrThree)
    (color : WireColor) (atom : Nat)
    (atomLt : atom < problem.elementCount color)
    (degreeThree : problem.degree color atom = 3) :
    List.Perm
      ((problem.contractedEdgesForElement color atom).map
        ContractedEndpoint.target)
      (problem.contractedEndpointsAt (.element color atom)) := by
  let targets :=
    (problem.contractedEdgesForElement color atom).map
      ContractedEndpoint.target
  have endpointsNodup :=
    contractedEndpointsAt_nodup problem degree (.element color atom)
  have endpointsSubset :
      problem.contractedEndpointsAt (.element color atom) ⊆ targets := by
    intro endpoint endpointAt
    have endpointData :=
      (contractedEndpointsAt_mem_iff problem (.element color atom) endpoint).1
        endpointAt
    have edgeMember := endpoint.edge_mem_of_mem endpointData.1
    cases endpoint with
    | source edge =>
        cases edge <;>
          simp [ContractedEndpoint.vertex, ContractedEdge.toPeriodicEdge]
            at endpointData
    | target edge =>
        cases edge with
        | retained edgeColor edgeAtom incidence =>
            simp only [ContractedEndpoint.vertex,
              ContractedEdge.toPeriodicEdge] at endpointData
            injection endpointData.2 with colorEq atomEq
            subst edgeColor
            subst edgeAtom
            have ownMember := contractedEdge_mem_own_element
              problem edgeMember
            exact List.mem_map.mpr
              ⟨.retained color atom incidence, ownMember, rfl⟩
        | through edgeColor edgeAtom first second =>
            simp [ContractedEndpoint.vertex, ContractedEdge.toPeriodicEdge]
              at endpointData
  have subperm :
      List.Subperm
        (problem.contractedEndpointsAt (.element color atom)) targets :=
    endpointsNodup.subperm endpointsSubset
  have targetLength : targets.length = 3 := by
    simp [targets,
      contractedEdgesForElement_length_of_degree_three
        problem color atom degreeThree]
  have endpointLength :
      (problem.contractedEndpointsAt (.element color atom)).length = 3 :=
    contractedEndpointsAt_element_length problem color atom atomLt degreeThree
  apply (subperm.perm_of_length_le ?_).symm
  rw [targetLength, endpointLength]

/-- The west/north/east inward values at a retained monochromatic vertex
are a permutation of the edge-block values already known to satisfy
exact-one. -/
theorem PlanarPresentation.vertexPortInwardValues_perm_retainedElementInwardValues
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (values : problem.GraphOrientation)
    (color : WireColor) (atom : Nat)
    (atomLt : atom < problem.elementCount color)
    (degreeThree : problem.degree color atom = 3)
    (translate : Cell) :
    List.Perm
      [presentation.toPlanarPresentation.vertexPortInward values
        (.element color atom) translate .west,
      presentation.toPlanarPresentation.vertexPortInward values
        (.element color atom) translate .north,
      presentation.toPlanarPresentation.vertexPortInward values
        (.element color atom) translate .east]
      (problem.retainedElementInwardValues values color atom translate) := by
  let planar := presentation.toPlanarPresentation
  have vertexMember :
      .element color atom ∈ problem.contractedGraph.vertices := by
    cases color <;> simp_all [contractedGraph, contractedElementVertices,
      contractedElementVerticesForColor, incidenceColors]
  have portPerm :=
    PlanarPresentation.normalizedVertexPortEndpoints_perm
      presentation wellFormed degree vertexMember
  have targetPerm := contractedEdgesForElement_targets_perm_endpointsAt
    problem degree color atom atomLt degreeThree
  have endpointPerm :
      List.Perm
        (planar.normalizedVertexPortEndpoints (.element color atom))
        ((problem.contractedEdgesForElement color atom).map
          ContractedEndpoint.target) :=
    portPerm.trans targetPerm.symm
  have valuePerm := endpointPerm.map fun endpoint =>
    endpoint.inwardAtVertexTranslate values translate
  simpa [PlanarPresentation.normalizedVertexPortEndpoints,
    PlanarPresentation.vertexPortInward,
    retainedElementInwardValues, List.map_map,
    Function.comp_def] using valuePerm

/-- A valid suppressed orientation satisfies every retained normalized
monochromatic element vertex cell. -/
theorem PlanarPresentation.finalVertexCellType_satisfiesOrientation_element
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (values : problem.GraphOrientation)
    (valid : problem.IsSuppressedOrientation values)
    (color : WireColor) (atom : Nat)
    (atomLt : atom < problem.elementCount color)
    (degreeThree : problem.degree color atom = 3)
    (translate : Cell) :
    PeriodicOrthogonalDrawing.satisfiesOrientation
      (presentation.toPlanarPresentation.finalVertexCellType
        (.element color atom))
      (presentation.toPlanarPresentation.vertexPortInward values
        (.element color atom) translate) := by
  have valuesPerm :=
    PlanarPresentation.vertexPortInwardValues_perm_retainedElementInwardValues
      presentation wellFormed degree values color atom atomLt degreeThree
        translate
  have incidenceShape :
      ∃ first second third,
        problem.incidences color atom = [first, second, third] := by
    unfold PeriodicThreeDM.degree at degreeThree
    generalize incidencesEq :
        problem.incidences color atom = incidences at degreeThree ⊢
    change incidences.length = 3 at degreeThree
    rcases incidences with _ | ⟨first, incidences⟩
    · simp at degreeThree
    rcases incidences with _ | ⟨second, incidences⟩
    · simp at degreeThree
    rcases incidences with _ | ⟨third, incidences⟩
    · simp at degreeThree
    rcases incidences with _ | ⟨fourth, incidences⟩
    · exact ⟨first, second, third, rfl⟩
    · simp at degreeThree
  rcases incidenceShape with ⟨first, second, third, incidences⟩
  have retainedExactlyOne :
      PeriodicOneInThree.ExactlyOne
        (problem.retainedElementInwardValues values color atom translate) := by
    exact problem.retainedElementInwardValues_exactlyOne
      values valid color atom atomLt first second third incidences translate
  change
    [presentation.toPlanarPresentation.vertexPortInward values
        (.element color atom) translate .west,
      presentation.toPlanarPresentation.vertexPortInward values
        (.element color atom) translate .north,
      presentation.toPlanarPresentation.vertexPortInward values
        (.element color atom) translate .east].count true = 1
  rw [valuesPerm.count_eq]
  exact retainedExactlyOne

/-- A valid suppressed orientation satisfies the compiled local constraint
at every retained contracted vertex. -/
theorem PlanarPresentation.finalVertexCellType_satisfiesOrientation
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (values : problem.GraphOrientation)
    (valid : problem.IsSuppressedOrientation values)
    {vertex : PeriodicThreeDMVertex}
    (vertexMember : vertex ∈ problem.contractedGraph.vertices)
    (translate : Cell) :
    PeriodicOrthogonalDrawing.satisfiesOrientation
      (presentation.toPlanarPresentation.finalVertexCellType vertex)
      (presentation.toPlanarPresentation.vertexPortInward values
        vertex translate) := by
  cases vertex with
  | triple tripleIndex =>
      have indexLt : tripleIndex < problem.triples.length := by
        simpa [contractedGraph, tripleVertices,
          contractedElementVertices,
          contractedElementVerticesForColor] using vertexMember
      exact PlanarPresentation.finalVertexCellType_satisfiesOrientation_triple
        presentation wellFormed degree values valid tripleIndex indexLt
          translate
  | element color atom =>
      have atomData : atom < problem.elementCount color ∧
          problem.degree color atom = 3 := by
        simp [contractedGraph, tripleVertices,
          contractedElementVertices,
          contractedElementVerticesForColor,
          incidenceColors] at vertexMember
        cases color <;> simp_all
      exact PlanarPresentation.finalVertexCellType_satisfiesOrientation_element
        presentation wellFormed degree values valid color atom atomData.1
          atomData.2 translate

end PeriodicThreeDM

end LeanTrominoes
