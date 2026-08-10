import LeanTrominoes.PeriodicThreeDMNormalizationReverseRouteCompatibility
import LeanTrominoes.PeriodicThreeDMNormalizationForwardVertexCompatibility

/-!
# Colored-element constraints in the reverse normalized orientation

Complete-route compatibility identifies extracted incidence values with the
inward values at retained monochromatic endpoints, and preserves inequality
across suppressed degree-two elements.  The local monochromatic vertex rule
therefore recovers every post-contraction colored-element constraint.
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

set_option maxRecDepth 2048

/-- The source endpoint of every emitted edge occurs in the triple-endpoint
enumeration. -/
theorem ContractedEdge.source_mem_contractedTripleEndpoints
    {problem : PeriodicThreeDM} {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges) :
    ContractedEndpoint.source edge ∈ problem.contractedTripleEndpoints := by
  unfold contractedTripleEndpoints
  apply List.mem_flatMap.mpr
  refine ⟨edge, edgeMember, ?_⟩
  cases edge <;> simp [ContractedEdge.tripleEndpoints]

/-- The target of a through edge occurs in the triple-endpoint enumeration. -/
theorem ContractedEdge.through_target_mem_contractedTripleEndpoints
    (problem : PeriodicThreeDM)
    (color : WireColor) (atom : Nat) (first second : Incidence)
    (edgeMember :
      ContractedEdge.through color atom first second ∈
        problem.contractedEdges) :
    ContractedEndpoint.target (.through color atom first second) ∈
      problem.contractedTripleEndpoints := by
  unfold contractedTripleEndpoints
  apply List.mem_flatMap.mpr
  exact ⟨.through color atom first second, edgeMember, by
    simp [ContractedEdge.tripleEndpoints]⟩

/-- The tag selector chooses the actual source endpoint of any emitted
contracted edge. -/
theorem contractedTripleEndpointForTag_sourceTag
    (problem : PeriodicThreeDM)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges) :
    problem.contractedTripleEndpointForTag edge.sourceTag =
      .source edge := by
  have tagMember : edge.sourceTag ∈ problem.incidenceTags :=
    incidenceTag_mem_of_contractedEdge problem edgeMember (by
      cases edge <;> simp [ContractedEdge.incidenceTags,
        ContractedEdge.sourceTag])
  apply problem.contractedTripleEndpointForTag_eq wellFormed degree tagMember
    (ContractedEdge.source_mem_contractedTripleEndpoints edgeMember)
  rfl

/-- For a through edge, the tag selector chooses its actual target triple
endpoint. -/
theorem contractedTripleEndpointForTag_through_targetTag
    (problem : PeriodicThreeDM)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (color : WireColor) (atom : Nat) (first second : Incidence)
    (edgeMember :
      ContractedEdge.through color atom first second ∈
        problem.contractedEdges) :
    problem.contractedTripleEndpointForTag
        (ContractedEdge.through color atom first second).targetTag =
      .target (.through color atom first second) := by
  let edge := ContractedEdge.through color atom first second
  have tagMember : edge.targetTag ∈ problem.incidenceTags :=
    incidenceTag_mem_of_contractedEdge problem edgeMember (by
      simp [edge, ContractedEdge.incidenceTags, ContractedEdge.targetTag])
  apply problem.contractedTripleEndpointForTag_eq wellFormed degree tagMember
    (ContractedEdge.through_target_mem_contractedTripleEndpoints
      problem color atom first second edgeMember)
  rfl

/-- At the source tag of an emitted edge, extraction is exactly negation of
the inward drawing value at that edge's source endpoint. -/
theorem PlanarPresentation.reverseGraphOrientation_sourceTag
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (orientation : presentation.normalizedOrthogonalDrawing.Orientation)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges)
    (translate : Cell) :
    presentation.reverseGraphOrientation orientation edge.sourceTag translate =
      !(presentation.drawingEndpointInward orientation (.source edge)
        translate) := by
  unfold PlanarPresentation.reverseGraphOrientation
  rw [problem.contractedTripleEndpointForTag_sourceTag
    wellFormed degree edgeMember]

/-- At the second tag of a through edge, extraction is negation of its target
triple endpoint's inward drawing value. -/
theorem PlanarPresentation.reverseGraphOrientation_through_targetTag
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (orientation : presentation.normalizedOrthogonalDrawing.Orientation)
    (color : WireColor) (atom : Nat) (first second : Incidence)
    (edgeMember :
      ContractedEdge.through color atom first second ∈
        problem.contractedEdges)
    (translate : Cell) :
    presentation.reverseGraphOrientation orientation
        (ContractedEdge.through color atom first second).targetTag translate =
      !(presentation.drawingEndpointInward orientation
        (.target (ContractedEdge.through color atom first second)) translate) := by
  unfold PlanarPresentation.reverseGraphOrientation
  rw [problem.contractedTripleEndpointForTag_through_targetTag
    wellFormed degree color atom first second edgeMember]

/-- An extracted incidence carried by a retained edge equals the inward
drawing value at its translated monochromatic target endpoint. -/
theorem ContinuousPlanarPresentation.reverseGraphOrientation_retained_eq_target
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
        orientation)
    (color : WireColor) (atom : Nat) (incidence : Incidence)
    (edgeMember :
      ContractedEdge.retained color atom incidence ∈ problem.contractedEdges)
    (sourceTranslate : Cell) :
    let planar := presentation.toPlanarPresentation
    let edge := ContractedEdge.retained color atom incidence
    let targetTranslate := Cell.add sourceTranslate incidence.offset
    planar.reverseGraphOrientation orientation edge.sourceTag sourceTranslate =
      planar.drawingEndpointInward orientation (.target edge)
        targetTranslate := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  let edge := ContractedEdge.retained color atom incidence
  let targetTranslate := Cell.add sourceTranslate incidence.offset
  have endpointDifferent := presentation.drawingEndpointInward_ne
    wellFormed degree collisionFree orientation valid edgeMember sourceTranslate
  have sourceValue := planar.reverseGraphOrientation_sourceTag
    wellFormed degree orientation edgeMember sourceTranslate
  have endpointDifferent' :
      planar.drawingEndpointInward orientation (.source edge)
          sourceTranslate ≠
        planar.drawingEndpointInward orientation (.target edge)
          targetTranslate := by
    simpa [planar, edge, targetTranslate, ContractedEdge.toPeriodicEdge] using
      endpointDifferent
  change planar.reverseGraphOrientation orientation edge.sourceTag
      sourceTranslate =
    planar.drawingEndpointInward orientation (.target edge) targetTranslate
  calc
    _ = !(planar.drawingEndpointInward orientation (.source edge)
          sourceTranslate) := sourceValue
    _ = planar.drawingEndpointInward orientation (.target edge)
          targetTranslate :=
      (bool_eq_not_of_ne _ _ (Ne.symm endpointDifferent')).symm

/-- The two extracted incidences represented by a through edge are unequal. -/
theorem ContinuousPlanarPresentation.reverseGraphOrientation_through_ne
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
        orientation)
    (color : WireColor) (atom : Nat) (first second : Incidence)
    (edgeMember :
      ContractedEdge.through color atom first second ∈ problem.contractedEdges)
    (sourceTranslate : Cell) :
    let planar := presentation.toPlanarPresentation
    let edge := ContractedEdge.through color atom first second
    let targetTranslate := Cell.add sourceTranslate
      (Cell.sub first.offset second.offset)
    planar.reverseGraphOrientation orientation edge.sourceTag sourceTranslate ≠
      planar.reverseGraphOrientation orientation edge.targetTag
        targetTranslate := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  let edge := ContractedEdge.through color atom first second
  let targetTranslate := Cell.add sourceTranslate
    (Cell.sub first.offset second.offset)
  have endpointDifferent := presentation.drawingEndpointInward_ne
    wellFormed degree collisionFree orientation valid edgeMember sourceTranslate
  have sourceValue := planar.reverseGraphOrientation_sourceTag
    wellFormed degree orientation edgeMember sourceTranslate
  have targetValue := planar.reverseGraphOrientation_through_targetTag
    wellFormed degree orientation color atom first second edgeMember
      targetTranslate
  have endpointDifferent' :
      planar.drawingEndpointInward orientation (.source edge)
          sourceTranslate ≠
        planar.drawingEndpointInward orientation (.target edge)
          targetTranslate := by
    simpa [planar, edge, targetTranslate, ContractedEdge.toPeriodicEdge] using
      endpointDifferent
  change planar.reverseGraphOrientation orientation edge.sourceTag
      sourceTranslate ≠
    planar.reverseGraphOrientation orientation edge.targetTag targetTranslate
  intro extractedEqual
  have complementsEqual :
      (!(planar.drawingEndpointInward orientation (.source edge)
          sourceTranslate)) =
        (!(planar.drawingEndpointInward orientation (.target edge)
          targetTranslate)) :=
    sourceValue.symm.trans (extractedEqual.trans targetValue)
  apply endpointDifferent'
  cases sourceInward :
      planar.drawingEndpointInward orientation (.source edge) sourceTranslate <;>
    cases targetInward :
      planar.drawingEndpointInward orientation (.target edge)
        targetTranslate <;>
    simp_all

/-- Reading the selected endpoint at one canonical vertex port returns the
orientation value on that port of the translated vertex occurrence. -/
theorem ContinuousPlanarPresentation.drawingEndpointInward_endpointAtVertexPort
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (orientation :
      presentation.toPlanarPresentation.normalizedOrthogonalDrawing.Orientation)
    {vertex : PeriodicThreeDMVertex}
    (vertexMember : vertex ∈ problem.contractedGraph.vertices)
    (translate : Cell) (port : CanonicalVertexPort) :
    let planar := presentation.toPlanarPresentation
    planar.drawingEndpointInward orientation
        (planar.endpointAtVertexPort vertex port.side) translate =
      orientation
        (reflectedLocation
          (Cell.add (planar.finalNormalizationPosition vertex)
            (Cell.scale (planar.finalNormalizationPeriod : Int) translate)))
        port.side := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  obtain ⟨color, exposed⟩ :=
    planar.finalVertexCellType_portColor_isSome vertex port
  have endpointData :=
    PlanarPresentation.endpointAtVertexPort_data_of_exposed
      presentation wellFormed degree vertexMember exposed
  let endpoint := planar.endpointAtVertexPort vertex port.side
  change endpoint ∈ problem.contractedEndpoints ∧
      endpoint.vertex = vertex ∧
      (endpoint.finalNormalizedPort planar).side = port.side ∧ _ at endpointData
  change orientation
      (reflectedLocation
        (Cell.add (planar.finalNormalizationPosition endpoint.vertex)
          (Cell.scale (planar.finalNormalizationPeriod : Int) translate)))
      (endpoint.finalNormalizedPort planar).side = _
  rw [endpointData.2.1, endpointData.2.2.1]

/-- Target-endpoint values of the three retained edges at one colored
element. -/
def PlanarPresentation.retainedElementDrawingInwardValues
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (orientation : presentation.normalizedOrthogonalDrawing.Orientation)
    (color : WireColor) (atom : Nat) (translate : Cell) : List Bool :=
  (problem.contractedEdgesForElement color atom).map fun edge =>
    presentation.drawingEndpointInward orientation (.target edge) translate

/-- The retained endpoint values at a degree-three element satisfy exact-one
in every translated occurrence. -/
theorem ContinuousPlanarPresentation.retainedElementDrawingInwardValues_exactlyOne
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
        orientation)
    (color : WireColor) (atom : Nat)
    (atomLt : atom < problem.elementCount color)
    (degreeThree : problem.degree color atom = 3)
    (translate : Cell) :
    PeriodicOneInThree.ExactlyOne
      (presentation.toPlanarPresentation.retainedElementDrawingInwardValues
        orientation color atom translate) := by
  let planar := presentation.toPlanarPresentation
  let vertex := PeriodicThreeDMVertex.element color atom
  have vertexMember : vertex ∈ problem.contractedGraph.vertices := by
    cases color <;> simp_all [vertex, contractedGraph, tripleVertices,
      contractedElementVertices, contractedElementVerticesForColor,
      incidenceColors]
  have portPerm :=
    PlanarPresentation.normalizedVertexPortEndpoints_perm
      presentation wellFormed degree vertexMember
  have targetPerm := contractedEdgesForElement_targets_perm_endpointsAt
    problem degree color atom atomLt degreeThree
  have endpointPerm :
      List.Perm (planar.normalizedVertexPortEndpoints vertex)
        ((problem.contractedEdgesForElement color atom).map
          ContractedEndpoint.target) :=
    portPerm.trans targetPerm.symm
  have valuePerm := endpointPerm.map fun endpoint =>
    planar.drawingEndpointInward orientation endpoint translate
  have westValue :=
    presentation.drawingEndpointInward_endpointAtVertexPort
      wellFormed degree orientation vertexMember translate .west
  have northValue :=
    presentation.drawingEndpointInward_endpointAtVertexPort
      wellFormed degree orientation vertexMember translate .north
  have eastValue :=
    presentation.drawingEndpointInward_endpointAtVertexPort
      wellFormed degree orientation vertexMember translate .east
  dsimp only at westValue northValue eastValue
  simp only [CanonicalVertexPort.side] at westValue northValue eastValue
  have valuesPerm :
      List.Perm
        [orientation
          (reflectedLocation
            (Cell.add (planar.finalNormalizationPosition vertex)
              (Cell.scale (planar.finalNormalizationPeriod : Int) translate)))
          .west,
        orientation
          (reflectedLocation
            (Cell.add (planar.finalNormalizationPosition vertex)
              (Cell.scale (planar.finalNormalizationPeriod : Int) translate)))
          .north,
        orientation
          (reflectedLocation
            (Cell.add (planar.finalNormalizationPosition vertex)
              (Cell.scale (planar.finalNormalizationPeriod : Int) translate)))
          .east]
        (planar.retainedElementDrawingInwardValues orientation color atom
          translate) := by
    change List.Perm
      [planar.drawingEndpointInward orientation
          (planar.endpointAtVertexPort vertex .west) translate,
        planar.drawingEndpointInward orientation
          (planar.endpointAtVertexPort vertex .north) translate,
        planar.drawingEndpointInward orientation
          (planar.endpointAtVertexPort vertex .east) translate]
      _ at valuePerm
    dsimp only [planar] at valuePerm ⊢
    rw [westValue, northValue, eastValue] at valuePerm
    simpa [PlanarPresentation.retainedElementDrawingInwardValues,
      List.map_map, Function.comp_def] using valuePerm
  have localConstraint :=
    presentation.finalVertexCellType_satisfied_of_orientation
      collisionFree orientation valid vertexMember translate
  change
    [orientation
        (reflectedLocation
          (Cell.add (planar.finalNormalizationPosition vertex)
            (Cell.scale (planar.finalNormalizationPeriod : Int) translate)))
        .west,
      orientation
        (reflectedLocation
          (Cell.add (planar.finalNormalizationPosition vertex)
            (Cell.scale (planar.finalNormalizationPeriod : Int) translate)))
        .north,
      orientation
        (reflectedLocation
          (Cell.add (planar.finalNormalizationPosition vertex)
            (Cell.scale (planar.finalNormalizationPeriod : Int) translate)))
        .east].count true = 1 at localConstraint
  change (planar.retainedElementDrawingInwardValues orientation color atom
    translate).count true = 1
  rw [← valuesPerm.count_eq]
  exact localConstraint

/-- A degree-two colored element satisfies the extracted suppressed wire
constraint. -/
theorem ContinuousPlanarPresentation.reverseGraphOrientation_element_degreeTwo
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
        orientation)
    (color : WireColor) (atom : Nat)
    (atomLt : atom < problem.elementCount color)
    (degreeTwo : problem.degree color atom = 2)
    (translate : Cell) :
    SuppressedElementConstraint
      (problem.graphIncidentValues
        (presentation.toPlanarPresentation.reverseGraphOrientation orientation)
        color atom translate) := by
  obtain ⟨first, second, incidences⟩ :
      ∃ first second, problem.incidences color atom = [first, second] := by
    unfold PeriodicThreeDM.degree at degreeTwo
    generalize incidenceListEq :
      problem.incidences color atom = incidenceList at degreeTwo ⊢
    change incidenceList.length = 2 at degreeTwo
    rcases incidenceList with _ | ⟨first, incidenceList⟩
    · simp at degreeTwo
    rcases incidenceList with _ | ⟨second, incidenceList⟩
    · simp at degreeTwo
    rcases incidenceList with _ | ⟨third, incidenceList⟩
    · exact ⟨first, second, rfl⟩
    · simp at degreeTwo
  let edge := ContractedEdge.through color atom first second
  have localEdgeMember : edge ∈
      problem.contractedEdgesForElement color atom := by
    rw [contractedEdgesForElement_of_incidences_pair
      problem color atom first second incidences]
    simp [edge]
  have edgeMember := contractedEdgesForElement_mem_contractedEdges
    problem color atom atomLt localEdgeMember
  let sourceTranslate := Cell.sub translate first.offset
  have targetTranslate :
      Cell.add sourceTranslate (Cell.sub first.offset second.offset) =
        Cell.sub translate second.offset := by
    rcases translate with ⟨translateX, translateY⟩
    rcases first with ⟨firstIndex, firstX, firstY⟩
    rcases second with ⟨secondIndex, secondX, secondY⟩
    simp [sourceTranslate, Cell.add, Cell.sub]
  have different := presentation.reverseGraphOrientation_through_ne
    wellFormed degree collisionFree orientation valid color atom first second
      edgeMember sourceTranslate
  rw [graphIncidentValues, incidences]
  simp only [List.map_cons, List.map_nil,
    suppressedElementConstraint_pair_iff]
  simpa [edge, ContractedEdge.sourceTag, ContractedEdge.targetTag,
    sourceTranslate, targetTranslate] using different

/-- A retained degree-three colored element satisfies its extracted exact-one
constraint. -/
theorem ContinuousPlanarPresentation.reverseGraphOrientation_element_degreeThree
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
        orientation)
    (color : WireColor) (atom : Nat)
    (atomLt : atom < problem.elementCount color)
    (degreeThree : problem.degree color atom = 3)
    (translate : Cell) :
    SuppressedElementConstraint
      (problem.graphIncidentValues
        (presentation.toPlanarPresentation.reverseGraphOrientation orientation)
        color atom translate) := by
  obtain ⟨first, second, third, incidences⟩ :
      ∃ first second third,
        problem.incidences color atom = [first, second, third] := by
    unfold PeriodicThreeDM.degree at degreeThree
    generalize incidenceListEq :
      problem.incidences color atom = incidenceList at degreeThree ⊢
    change incidenceList.length = 3 at degreeThree
    rcases incidenceList with _ | ⟨first, incidenceList⟩
    · simp at degreeThree
    rcases incidenceList with _ | ⟨second, incidenceList⟩
    · simp at degreeThree
    rcases incidenceList with _ | ⟨third, incidenceList⟩
    · simp at degreeThree
    rcases incidenceList with _ | ⟨fourth, incidenceList⟩
    · exact ⟨first, second, third, rfl⟩
    · simp at degreeThree
  let firstEdge := ContractedEdge.retained color atom first
  let secondEdge := ContractedEdge.retained color atom second
  let thirdEdge := ContractedEdge.retained color atom third
  have firstLocal : firstEdge ∈
      problem.contractedEdgesForElement color atom := by
    rw [contractedEdgesForElement_of_incidences_triple
      problem color atom first second third incidences]
    simp [firstEdge]
  have secondLocal : secondEdge ∈
      problem.contractedEdgesForElement color atom := by
    rw [contractedEdgesForElement_of_incidences_triple
      problem color atom first second third incidences]
    simp [secondEdge]
  have thirdLocal : thirdEdge ∈
      problem.contractedEdgesForElement color atom := by
    rw [contractedEdgesForElement_of_incidences_triple
      problem color atom first second third incidences]
    simp [thirdEdge]
  have firstMember := contractedEdgesForElement_mem_contractedEdges
    problem color atom atomLt firstLocal
  have secondMember := contractedEdgesForElement_mem_contractedEdges
    problem color atom atomLt secondLocal
  have thirdMember := contractedEdgesForElement_mem_contractedEdges
    problem color atom atomLt thirdLocal
  have firstValue := presentation.reverseGraphOrientation_retained_eq_target
    wellFormed degree collisionFree orientation valid color atom first
      firstMember (Cell.sub translate first.offset)
  have secondValue := presentation.reverseGraphOrientation_retained_eq_target
    wellFormed degree collisionFree orientation valid color atom second
      secondMember (Cell.sub translate second.offset)
  have thirdValue := presentation.reverseGraphOrientation_retained_eq_target
    wellFormed degree collisionFree orientation valid color atom third
      thirdMember (Cell.sub translate third.offset)
  have endpointExactlyOne :=
    presentation.retainedElementDrawingInwardValues_exactlyOne
      wellFormed degree collisionFree orientation valid color atom atomLt
        degreeThree translate
  rw [graphIncidentValues, incidences]
  simp only [List.map_cons, List.map_nil,
    suppressedElementConstraint_triple_iff]
  unfold PlanarPresentation.retainedElementDrawingInwardValues at endpointExactlyOne
  rw [contractedEdgesForElement_of_incidences_triple
    problem color atom first second third incidences] at endpointExactlyOne
  simp only [List.map_cons, List.map_nil] at endpointExactlyOne
  rw [Cell.add_sub_right_cancel] at firstValue secondValue thirdValue
  dsimp only at firstValue secondValue thirdValue
  have firstValue' :
      presentation.toPlanarPresentation.reverseGraphOrientation orientation
          ⟨first.tripleIndex, color⟩ (Cell.sub translate first.offset) =
        presentation.toPlanarPresentation.drawingEndpointInward orientation
          (.target firstEdge) translate := by
    simpa [firstEdge, ContractedEdge.sourceTag] using firstValue
  have secondValue' :
      presentation.toPlanarPresentation.reverseGraphOrientation orientation
          ⟨second.tripleIndex, color⟩ (Cell.sub translate second.offset) =
        presentation.toPlanarPresentation.drawingEndpointInward orientation
          (.target secondEdge) translate := by
    simpa [secondEdge, ContractedEdge.sourceTag] using secondValue
  have thirdValue' :
      presentation.toPlanarPresentation.reverseGraphOrientation orientation
          ⟨third.tripleIndex, color⟩ (Cell.sub translate third.offset) =
        presentation.toPlanarPresentation.drawingEndpointInward orientation
          (.target thirdEdge) translate := by
    simpa [thirdEdge, ContractedEdge.sourceTag] using thirdValue
  rw [firstValue', secondValue', thirdValue']
  simpa [firstEdge, secondEdge, thirdEdge] using endpointExactlyOne

/-- Every colored element satisfies its extracted post-contraction
constraint. -/
theorem ContinuousPlanarPresentation.reverseGraphOrientation_suppressedCoversElements
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
    problem.SuppressedCoversElements
      (presentation.toPlanarPresentation.reverseGraphOrientation orientation) := by
  intro color atom atomLt translate
  by_cases degreeTwo : problem.degree color atom = 2
  · exact presentation.reverseGraphOrientation_element_degreeTwo
      wellFormed degree collisionFree orientation valid color atom atomLt
        degreeTwo translate
  · have degreeCases :
        problem.degree color atom = 2 ∨ problem.degree color atom = 3 := by
      simpa using degree color atom atomLt
    have degreeThree : problem.degree color atom = 3 :=
      degreeCases.resolve_left degreeTwo
    exact presentation.reverseGraphOrientation_element_degreeThree
      wellFormed degree collisionFree orientation valid color atom atomLt
        degreeThree translate

/-- An arbitrary valid orientation of the compiled drawing extracts a valid
suppressed 3DM orientation. -/
theorem ContinuousPlanarPresentation.reverseGraphOrientation_isSuppressedOrientation
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
    problem.IsSuppressedOrientation
      (presentation.toPlanarPresentation.reverseGraphOrientation orientation) :=
  ⟨presentation.reverseGraphOrientation_tripleCoherent
      wellFormed degree collisionFree orientation valid,
    presentation.reverseGraphOrientation_suppressedCoversElements
      wellFormed degree collisionFree orientation valid⟩

end PeriodicThreeDM

end LeanTrominoes
