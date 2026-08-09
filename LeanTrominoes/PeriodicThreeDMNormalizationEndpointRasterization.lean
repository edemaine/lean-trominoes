import LeanTrominoes.PeriodicThreeDMVertexNormalizationEndpointColors
import LeanTrominoes.PeriodicThreeDMNormalizationAssignmentLookup
import LeanTrominoes.PeriodicGridDrawingUnitSubdivision

/-!
# Rasterized normalized-route endpoints

This module joins the endpoint geometry, endpoint colors, and collision-free
assignment lookup.  It proves that the first routing cell of every listed
normalized edge is emitted by the rasterizer and that its port toward the
source vertex has exactly the owning edge's color.  Consequently the source
vertex and its adjacent routing cell have matching ports.
-/

namespace LeanTrominoes

open Gadget
open DegreeThreeVertexNormalization

namespace PeriodicThreeDM

/-- A list of length at least three can expose its first three entries. -/
theorem List.exists_eq_cons_cons_cons_of_length_ge_three
    {α : Type*} {items : List α}
    (length : 3 ≤ items.length) :
    ∃ first second third rest,
      items = first :: second :: third :: rest := by
  cases items with
  | nil => simp at length
  | cons first items =>
      cases items with
      | nil => simp at length
      | cons second items =>
          cases items with
          | nil => simp at length
          | cons third rest => exact ⟨first, second, third, rest, rfl⟩

/-- A list of length at least two can expose its first two entries. -/
theorem List.exists_eq_cons_cons_of_length_ge_two
    {α : Type*} {items : List α}
    (length : 2 ≤ items.length) :
    ∃ first second rest, items = first :: second :: rest := by
  cases items with
  | nil => simp at length
  | cons first items =>
      cases items with
      | nil => simp at length
      | cons second rest => exact ⟨first, second, rest, rfl⟩

/-- A list of length at least four can expose its first four entries. -/
theorem List.exists_eq_cons_cons_cons_cons_of_length_ge_four
    {α : Type*} {items : List α}
    (length : 4 ≤ items.length) :
    ∃ first second third fourth rest,
      items = first :: second :: third :: fourth :: rest := by
  obtain ⟨first, second, third, rest, equation⟩ :=
    List.exists_eq_cons_cons_cons_of_length_ge_three
      (le_trans (by omega) length)
  cases rest with
  | nil => simp [equation] at length
  | cons fourth rest => exact ⟨first, second, third, fourth, rest, equation⟩

/-- Both choices of final rotation template avoid immediate reversal. -/
theorem rotationRoundPortAndRoute_noImmediateReversal
    (active : Bool) (oldPort : CanonicalVertexPort) :
    AxisDirection.HasNoImmediateReversal
      (rotationRoundPortAndRoute active oldPort).2 := by
  cases active <;> cases oldPort <;>
    simp [rotationRoundPortAndRoute,
      DegreeThreeVertexNormalization.identityRotationRoute,
      DegreeThreeVertexNormalization.clockwiseRotationRoute,
      newPortAfterClockwise,
      AxisDirection.HasNoImmediateReversal,
      AxisDirection.between, AxisDirection.opposite]

/-- Every endpoint's selected final template avoids immediate reversal. -/
theorem ContractedEndpoint.finalNormalizationTemplate_noImmediateReversal
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (endpoint : ContractedEndpoint) :
    AxisDirection.HasNoImmediateReversal
      (endpoint.finalNormalizationTemplate presentation) := by
  simpa [ContractedEndpoint.finalNormalizationTemplate] using
    rotationRoundPortAndRoute_noImmediateReversal
      (secondRotationActive presentation endpoint.vertex)
      (endpoint.secondNormalizedPort presentation)

/-- Translation preserves a unit-step chain. -/
theorem normalizationTemplateAt_unitSteps
    (position : Cell) {template : List Cell}
    (unitSteps : template.IsChain AxisDirection.IsUnitAxisStep) :
    (normalizationTemplateAt position template).IsChain
      AxisDirection.IsUnitAxisStep := by
  unfold normalizationTemplateAt
  unfold PeriodicOrthocrossing.translatePolyline
  apply List.isChain_map_of_isChain
      (Cell.add (Cell.scale vertexNormalizationScale position))
  · intro first second (step : AxisDirection.IsUnitAxisStep first second)
    exact AxisDirection.IsUnitAxisStep.translate step _
  · exact unitSteps

/-- The translated final template is literally a prefix of the fully spliced
normalized route. -/
theorem PlanarPresentation.finalNormalizationSourceTemplate_prefix
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) :
    normalizationTemplateAt
        (presentation.normalizationPosition2 edge.toPeriodicEdge.source)
        ((ContractedEndpoint.source edge).finalNormalizationTemplate
          presentation) <+:
      presentation.finalNormalizationRoute edge := by
  unfold PlanarPresentation.finalNormalizationRoute
  unfold normalizeRouteWithTemplates
  exact ⟨_, rfl⟩

/-- The first three points of every final route consist of its normalized
source vertex, the computed adjacent port point, and one further point.  The
two local edges are unit steps and do not immediately reverse. -/
theorem PlanarPresentation.exists_finalNormalizationRoute_sourceTriple
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) :
    ∃ third rest,
      presentation.finalNormalizationRoute edge =
        presentation.finalNormalizationPosition
            edge.toPeriodicEdge.source ::
          Cell.add
              (presentation.finalNormalizationPosition
                edge.toPeriodicEdge.source)
              ((ContractedEndpoint.source edge).finalNormalizedPort
                presentation).direction.step ::
          third :: rest ∧
      AxisDirection.IsUnitAxisStep
        (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
        (Cell.add
          (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
          ((ContractedEndpoint.source edge).finalNormalizedPort
            presentation).direction.step) ∧
      AxisDirection.IsUnitAxisStep
        (Cell.add
          (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
          ((ContractedEndpoint.source edge).finalNormalizedPort
            presentation).direction.step)
        third ∧
      AxisDirection.between
          (Cell.add
            (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
            ((ContractedEndpoint.source edge).finalNormalizedPort
              presentation).direction.step)
          third ≠
        (AxisDirection.between
          (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
          (Cell.add
            (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
            ((ContractedEndpoint.source edge).finalNormalizedPort
              presentation).direction.step)).opposite := by
  let endpoint := ContractedEndpoint.source edge
  let localRoute := normalizationTemplateAt
    (presentation.normalizationPosition2 edge.toPeriodicEdge.source)
    (endpoint.finalNormalizationTemplate presentation)
  have geometry := endpoint.finalNormalizationTemplate_geometry presentation
  have localLength : 3 ≤ localRoute.length := by
    simp only [localRoute, normalizationTemplateAt_length]
    exact le_trans (by omega)
      (endpoint.finalNormalizationTemplate_length_ge_four presentation)
  obtain ⟨first, second, third, localRest, localEquation⟩ :=
    List.exists_eq_cons_cons_cons_of_length_ge_three localLength
  have localHead : localRoute.head? =
      some (presentation.finalNormalizationPosition
        edge.toPeriodicEdge.source) := by
    change (normalizationTemplateAt
      (presentation.normalizationPosition2 edge.toPeriodicEdge.source)
      (endpoint.finalNormalizationTemplate presentation)).head? = _
    exact normalizationTemplateAt_head?
      (presentation.normalizationPosition2 edge.toPeriodicEdge.source)
      geometry.1
  have localSecond : localRoute.tail.head? =
      some (Cell.add
        (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
        (endpoint.finalNormalizedPort presentation).direction.step) := by
    change (normalizationTemplateAt
      (presentation.normalizationPosition2 edge.toPeriodicEdge.source)
      (endpoint.finalNormalizationTemplate presentation)).tail.head? = _
    rw [normalizationTemplateAt_tail_head?
      (secondPoint := endpoint.finalNormalizationTemplate_secondPoint
        presentation)]
    simp [PlanarPresentation.finalNormalizationPosition,
      normalizeVertexPosition, Cell.add_assoc]
  rw [localEquation] at localHead localSecond
  have firstEqual : first = presentation.finalNormalizationPosition
      edge.toPeriodicEdge.source := Option.some.inj localHead
  have secondEqual : second = Cell.add
      (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
      (endpoint.finalNormalizedPort presentation).direction.step := by
    simpa using Option.some.inj localSecond
  subst first
  subst second
  have localUnitSteps : localRoute.IsChain
      AxisDirection.IsUnitAxisStep :=
    normalizationTemplateAt_unitSteps _ geometry.2.2.1
  have localNoReversal :
      AxisDirection.HasNoImmediateReversal localRoute := by
    change AxisDirection.HasNoImmediateReversal
      ((endpoint.finalNormalizationTemplate presentation).map
        (Cell.add (Cell.scale vertexNormalizationScale
          (presentation.normalizationPosition2
            edge.toPeriodicEdge.source))))
    exact (endpoint.finalNormalizationTemplate_noImmediateReversal
      presentation).translate _
  rw [localEquation] at localUnitSteps localNoReversal
  have firstStep := (List.isChain_cons_cons.mp localUnitSteps).1
  have secondStep :=
    (List.isChain_cons_cons.mp
      (List.isChain_cons_cons.mp localUnitSteps).2).1
  have noReverse := localNoReversal.1
  rcases presentation.finalNormalizationSourceTemplate_prefix edge with
    ⟨suffix, prefixEquation⟩
  change localRoute ++ suffix = _ at prefixEquation
  rw [localEquation] at prefixEquation
  refine ⟨third, localRest ++ suffix, ?_, firstStep, secondStep, noReverse⟩
  simpa using prefixEquation.symm

/-- The first route-interior cell of a listed edge is one of the rasterizer's
emitted assignments. -/
theorem PlanarPresentation.sourceAdjacentAssignment_mem
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) :
    ∃ third rest,
      presentation.finalNormalizationRoute edge =
        presentation.finalNormalizationPosition
            edge.toPeriodicEdge.source ::
          Cell.add
              (presentation.finalNormalizationPosition
                edge.toPeriodicEdge.source)
              ((ContractedEndpoint.source edge).finalNormalizedPort
                presentation).direction.step ::
          third :: rest ∧
      (rasterLocation presentation.finalNormalizationPeriod
          (Cell.add
            (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
            ((ContractedEndpoint.source edge).finalNormalizedPort
              presentation).direction.step),
        routingCellTypeAt
          (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
          (Cell.add
            (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
            ((ContractedEndpoint.source edge).finalNormalizedPort
              presentation).direction.step)
          third edge.color) ∈
        routeInteriorAssignments presentation.finalNormalizationPeriod
          edge.color (presentation.finalNormalizationRoute edge) := by
  obtain ⟨third, rest, routeEquation, firstStep, secondStep, noReverse⟩ :=
    presentation.exists_finalNormalizationRoute_sourceTriple edge
  refine ⟨third, rest, routeEquation, ?_⟩
  rw [routeEquation]
  simp [routeInteriorAssignments]

/-- With collision-free assignments, the source-adjacent routing cell has
the owning edge's color on the side facing its source vertex. -/
theorem PlanarPresentation.finalCellTypeAt_sourceAdjacent_portColor
    {problem : PeriodicThreeDM}
    {presentation : problem.PlanarPresentation}
    (collisionFree : presentation.FinalAssignmentsCollisionFree)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges) :
    (presentation.finalCellTypeAt
      (rasterLocation presentation.finalNormalizationPeriod
        (Cell.add
          (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
          ((ContractedEndpoint.source edge).finalNormalizedPort
            presentation).direction.step))).portColor
      ((ContractedEndpoint.source edge).finalNormalizedPort
        presentation).side.opposite = some edge.color := by
  obtain ⟨third, rest, routeEquation, firstStep, secondStep, noReverse⟩ :=
    presentation.exists_finalNormalizationRoute_sourceTriple edge
  have assignmentMember :
      (rasterLocation presentation.finalNormalizationPeriod
          (Cell.add
            (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
            ((ContractedEndpoint.source edge).finalNormalizedPort
              presentation).direction.step),
        routingCellTypeAt
          (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
          (Cell.add
            (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
            ((ContractedEndpoint.source edge).finalNormalizedPort
              presentation).direction.step)
          third edge.color) ∈
        routeInteriorAssignments presentation.finalNormalizationPeriod
          edge.color (presentation.finalNormalizationRoute edge) := by
    rw [routeEquation]
    simp [routeInteriorAssignments]
  rw [presentation.finalCellTypeAt_routeInterior collisionFree edgeMember
    assignmentMember]
  rw [routingCellTypeAt_portColor firstStep secondStep noReverse]
  let port := (ContractedEndpoint.source edge).finalNormalizedPort presentation
  have forward : AxisDirection.between
      (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
      (Cell.add
        (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
        port.direction.step) = port.direction :=
    AxisDirection.between_add_step _
      (CanonicalVertexPort.direction_isGenuine port)
  have backward : AxisDirection.between
      (Cell.add
        (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
        port.direction.step)
      (presentation.finalNormalizationPosition edge.toPeriodicEdge.source) =
      port.direction.opposite := by
    rw [AxisDirection.between_reverse_eq_opposite
      (AxisDirection.between_isGenuine_of_unitAxisStep firstStep)]
    rw [forward]
  have backwardSide : Side.ofAxisDirection
      (AxisDirection.between
        (Cell.add
          (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)
          port.direction.step)
        (presentation.finalNormalizationPosition edge.toPeriodicEdge.source)) =
      port.side.opposite := by
    rw [backward]
    rw [Side.ofAxisDirection_opposite
      (CanonicalVertexPort.direction_isGenuine port)]
    simp
  simp [port, backwardSide]

/-- Every listed edge's source vertex and source-adjacent routing cell expose
the same color on their common side. -/
theorem PlanarPresentation.finalCellTypeAt_source_port_matches
    {problem : PeriodicThreeDM}
    {presentation : problem.ContinuousPlanarPresentation}
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (collisionFree :
      presentation.toPlanarPresentation.FinalAssignmentsCollisionFree)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges) :
    let endpoint := ContractedEndpoint.source edge
    let port := endpoint.finalNormalizedPort
      presentation.toPlanarPresentation
    (presentation.toPlanarPresentation.finalCellTypeAt
      (rasterLocation
        presentation.toPlanarPresentation.finalNormalizationPeriod
        (presentation.toPlanarPresentation.finalNormalizationPosition
          edge.toPeriodicEdge.source))).portColor port.side =
    (presentation.toPlanarPresentation.finalCellTypeAt
      (rasterLocation
        presentation.toPlanarPresentation.finalNormalizationPeriod
        (Cell.add
          (presentation.toPlanarPresentation.finalNormalizationPosition
            edge.toPeriodicEdge.source)
          port.direction.step))).portColor port.side.opposite := by
  dsimp only
  let endpoint := ContractedEndpoint.source edge
  have endpointMember : endpoint ∈ problem.contractedEndpoints := by
    simp only [endpoint, contractedEndpoints, List.mem_flatMap]
    exact ⟨edge, edgeMember, by simp⟩
  have vertexMember := endpoint.vertex_mem_of_mem endpointMember
  have sourceVertex : endpoint.vertex = edge.toPeriodicEdge.source := rfl
  rw [← sourceVertex]
  rw [presentation.toPlanarPresentation.finalCellTypeAt_vertex
    collisionFree vertexMember]
  rw [PlanarPresentation.finalVertexCellType_portColor_endpoint
    (presentation := presentation) wellFormed degree endpointMember]
  simpa [endpoint, sourceVertex, ContractedEndpoint.color,
    ContractedEndpoint.edge] using
    (PlanarPresentation.finalCellTypeAt_sourceAdjacent_portColor
      (presentation := presentation.toPlanarPresentation)
      collisionFree edgeMember).symm

/-! ## Target endpoints -/

/-- Dropping the last point of the target template leaves a prefix of the
reversed, fully spliced route.  The middle needs two points only so that the
outer join cannot consume any part of this target-side prefix. -/
theorem normalizeRouteWithTemplates_targetDropLast_reverse_prefix
    (sourcePosition targetPosition : Cell)
    (sourceTemplate targetTemplate oldRoute : List Cell)
    (middleLength : 2 ≤ (trimmedMagnifiedRoute oldRoute).length) :
    (normalizationTemplateAt targetPosition targetTemplate).dropLast <+:
      (normalizeRouteWithTemplates sourcePosition targetPosition
        sourceTemplate targetTemplate oldRoute).reverse := by
  obtain ⟨first, second, rest, middleEquation⟩ :=
    List.exists_eq_cons_cons_of_length_ge_two middleLength
  unfold normalizeRouteWithTemplates
  rw [middleEquation]
  unfold LeanTrominoes.joinAtEndpoint
  simp only [List.tail_cons, List.cons_append, List.reverse_append,
    List.reverse_cons,
    List.tail_reverse, List.reverse_reverse]
  refine ⟨rest.reverse ++ [second] ++
    (normalizationTemplateAt sourcePosition sourceTemplate).reverse, ?_⟩
  simp only [List.append_assoc]

/-- Assignments generated from a suffix of at least three points also occur
in the assignments generated from any longer leading route. -/
theorem routeInteriorAssignments_subset_append
    (period : Nat) (color : WireColor)
    (leading suffix : List Cell)
    (suffixLength : 3 ≤ suffix.length) :
    ∀ assignment,
      assignment ∈ routeInteriorAssignments period color suffix →
      assignment ∈ routeInteriorAssignments period color (leading ++ suffix) := by
  induction leading with
  | nil =>
      intro assignment member
      simpa using member
  | cons first leading induction =>
      intro assignment member
      cases leading with
      | nil =>
          obtain ⟨suffixFirst, suffixSecond, suffixThird, suffixRest,
              suffixEquation⟩ :=
            List.exists_eq_cons_cons_cons_of_length_ge_three suffixLength
          rw [suffixEquation] at member ⊢
          simp only [List.cons_append, List.nil_append]
          rw [routeInteriorAssignments]
          exact List.mem_cons_of_mem _ member
      | cons second leading =>
          have recursive := induction assignment member
          obtain ⟨after, remainder, tailEquation⟩ :
              ∃ after remainder,
                leading ++ suffix = after :: remainder := by
            cases leading with
            | nil =>
                obtain ⟨suffixFirst, suffixSecond, suffixThird, suffixRest,
                    suffixEquation⟩ :=
                  List.exists_eq_cons_cons_cons_of_length_ge_three suffixLength
                rw [suffixEquation]
                exact ⟨suffixFirst, suffixSecond :: suffixThird :: suffixRest,
                  rfl⟩
            | cons after remainder => exact ⟨after, remainder ++ suffix, rfl⟩
          change assignment ∈ routeInteriorAssignments period color
            (second :: (leading ++ suffix)) at recursive
          rw [tailEquation] at recursive
          change assignment ∈ routeInteriorAssignments period color
            (first :: second :: (leading ++ suffix))
          rw [tailEquation]
          rw [routeInteriorAssignments]
          exact List.mem_cons_of_mem _ recursive

/-- Reading a list backward, every final normalized route begins at its
periodic target occurrence, takes the endpoint's outward unit step, and then
takes one further nonreversing unit step. -/
theorem PlanarPresentation.exists_finalNormalizationRoute_targetTriple
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) :
    ∃ third rest,
      (presentation.finalNormalizationRoute edge).reverse =
        normalizeVertexPosition (presentation.normalizationTarget2 edge) ::
          Cell.add
              (normalizeVertexPosition (presentation.normalizationTarget2 edge))
              ((ContractedEndpoint.target edge).finalNormalizedPort
                presentation).direction.step ::
          third :: rest ∧
      AxisDirection.IsUnitAxisStep
        (normalizeVertexPosition (presentation.normalizationTarget2 edge))
        (Cell.add
          (normalizeVertexPosition (presentation.normalizationTarget2 edge))
          ((ContractedEndpoint.target edge).finalNormalizedPort
            presentation).direction.step) ∧
      AxisDirection.IsUnitAxisStep
        (Cell.add
          (normalizeVertexPosition (presentation.normalizationTarget2 edge))
          ((ContractedEndpoint.target edge).finalNormalizedPort
            presentation).direction.step)
        third ∧
      AxisDirection.between
          (Cell.add
            (normalizeVertexPosition (presentation.normalizationTarget2 edge))
            ((ContractedEndpoint.target edge).finalNormalizedPort
              presentation).direction.step)
          third ≠
        (AxisDirection.between
          (normalizeVertexPosition (presentation.normalizationTarget2 edge))
          (Cell.add
            (normalizeVertexPosition (presentation.normalizationTarget2 edge))
            ((ContractedEndpoint.target edge).finalNormalizedPort
              presentation).direction.step)).opposite := by
  let endpoint := ContractedEndpoint.target edge
  let localRoute := normalizationTemplateAt
    (presentation.normalizationTarget2 edge)
    (endpoint.finalNormalizationTemplate presentation)
  have geometry := endpoint.finalNormalizationTemplate_geometry presentation
  have localLength : 4 ≤ localRoute.length := by
    simpa only [localRoute, normalizationTemplateAt_length] using
      endpoint.finalNormalizationTemplate_length_ge_four presentation
  obtain ⟨first, second, third, fourth, localRest, localEquation⟩ :=
    List.exists_eq_cons_cons_cons_cons_of_length_ge_four localLength
  have localHead : localRoute.head? =
      some (normalizeVertexPosition (presentation.normalizationTarget2 edge)) := by
    change (normalizationTemplateAt
      (presentation.normalizationTarget2 edge)
      (endpoint.finalNormalizationTemplate presentation)).head? = _
    exact normalizationTemplateAt_head?
      (presentation.normalizationTarget2 edge) geometry.1
  have localSecond : localRoute.tail.head? =
      some (Cell.add
        (normalizeVertexPosition (presentation.normalizationTarget2 edge))
        (endpoint.finalNormalizedPort presentation).direction.step) := by
    change (normalizationTemplateAt
      (presentation.normalizationTarget2 edge)
      (endpoint.finalNormalizationTemplate presentation)).tail.head? = _
    rw [normalizationTemplateAt_tail_head?
      (secondPoint := endpoint.finalNormalizationTemplate_secondPoint
        presentation)]
    simp [normalizeVertexPosition, Cell.add_assoc]
  rw [localEquation] at localHead localSecond
  have firstEqual : first =
      normalizeVertexPosition (presentation.normalizationTarget2 edge) :=
    Option.some.inj localHead
  have secondEqual : second = Cell.add
      (normalizeVertexPosition (presentation.normalizationTarget2 edge))
      (endpoint.finalNormalizedPort presentation).direction.step := by
    simpa using Option.some.inj localSecond
  subst first
  subst second
  have localUnitSteps : localRoute.IsChain
      AxisDirection.IsUnitAxisStep :=
    normalizationTemplateAt_unitSteps _ geometry.2.2.1
  have localNoReversal :
      AxisDirection.HasNoImmediateReversal localRoute := by
    change AxisDirection.HasNoImmediateReversal
      ((endpoint.finalNormalizationTemplate presentation).map
        (Cell.add (Cell.scale vertexNormalizationScale
          (presentation.normalizationTarget2 edge))))
    exact (endpoint.finalNormalizationTemplate_noImmediateReversal
      presentation).translate _
  rw [localEquation] at localUnitSteps localNoReversal
  have firstStep := (List.isChain_cons_cons.mp localUnitSteps).1
  have secondStep :=
    (List.isChain_cons_cons.mp
      (List.isChain_cons_cons.mp localUnitSteps).2).1
  have noReverse := localNoReversal.1
  have targetPrefix := normalizeRouteWithTemplates_targetDropLast_reverse_prefix
    (presentation.normalizationPosition2 edge.toPeriodicEdge.source)
    (presentation.normalizationTarget2 edge)
    ((ContractedEndpoint.source edge).finalNormalizationTemplate presentation)
    (endpoint.finalNormalizationTemplate presentation)
    (presentation.normalizationRoute2 edge)
    (le_trans (by omega)
      (presentation.finalTrimmedMiddle_length_ge_seven edge))
  change localRoute.dropLast <+:
    (presentation.finalNormalizationRoute edge).reverse at targetPrefix
  rw [localEquation] at targetPrefix
  simp only [List.dropLast_cons_cons] at targetPrefix
  rcases targetPrefix with ⟨suffix, prefixEquation⟩
  refine ⟨third, (fourth :: localRest).dropLast ++ suffix,
    ?_, firstStep, secondStep, noReverse⟩
  simpa using prefixEquation.symm

/-- A displayed target triple in the reversed route emits its adjacent
cell during the original forward traversal. -/
theorem PlanarPresentation.targetAdjacentAssignment_mem_of_reverse_eq
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) {third : Cell} {reverseRest : List Cell}
    (reverseEquation :
      (presentation.finalNormalizationRoute edge).reverse =
        normalizeVertexPosition (presentation.normalizationTarget2 edge) ::
          Cell.add
              (normalizeVertexPosition (presentation.normalizationTarget2 edge))
              ((ContractedEndpoint.target edge).finalNormalizedPort
                presentation).direction.step ::
          third :: reverseRest) :
    (rasterLocation presentation.finalNormalizationPeriod
        (Cell.add
          (normalizeVertexPosition (presentation.normalizationTarget2 edge))
          ((ContractedEndpoint.target edge).finalNormalizedPort
            presentation).direction.step),
      routingCellTypeAt third
        (Cell.add
          (normalizeVertexPosition (presentation.normalizationTarget2 edge))
          ((ContractedEndpoint.target edge).finalNormalizedPort
            presentation).direction.step)
        (normalizeVertexPosition (presentation.normalizationTarget2 edge))
        edge.color) ∈
      routeInteriorAssignments presentation.finalNormalizationPeriod
        edge.color (presentation.finalNormalizationRoute edge) := by
  have forwardEquation := congrArg List.reverse reverseEquation
  simp only [List.reverse_reverse, List.reverse_cons] at forwardEquation
  let suffix := [third,
    Cell.add
      (normalizeVertexPosition (presentation.normalizationTarget2 edge))
      ((ContractedEndpoint.target edge).finalNormalizedPort
        presentation).direction.step,
    normalizeVertexPosition (presentation.normalizationTarget2 edge)]
  have suffixLength : 3 ≤ suffix.length := by simp [suffix]
  have suffixAssignment :
      (rasterLocation presentation.finalNormalizationPeriod
          (Cell.add
            (normalizeVertexPosition (presentation.normalizationTarget2 edge))
            ((ContractedEndpoint.target edge).finalNormalizedPort
              presentation).direction.step),
        routingCellTypeAt third
          (Cell.add
            (normalizeVertexPosition (presentation.normalizationTarget2 edge))
            ((ContractedEndpoint.target edge).finalNormalizedPort
              presentation).direction.step)
          (normalizeVertexPosition (presentation.normalizationTarget2 edge))
          edge.color) ∈
        routeInteriorAssignments presentation.finalNormalizationPeriod
          edge.color suffix := by
    simp [suffix, routeInteriorAssignments]
  rw [show presentation.finalNormalizationRoute edge =
    reverseRest.reverse ++ suffix by simpa [suffix] using forwardEquation]
  exact routeInteriorAssignments_subset_append _ _ _ _
    suffixLength _ suffixAssignment

/-- The target-adjacent cell of a listed edge is emitted by the forward
route traversal, with its predecessor supplied by the third point of the
reversed target triple. -/
theorem PlanarPresentation.targetAdjacentAssignment_mem
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (edge : ContractedEdge) :
    ∃ third leading,
      presentation.finalNormalizationRoute edge =
        leading ++ [third,
          Cell.add
            (normalizeVertexPosition (presentation.normalizationTarget2 edge))
            ((ContractedEndpoint.target edge).finalNormalizedPort
              presentation).direction.step,
          normalizeVertexPosition (presentation.normalizationTarget2 edge)] ∧
      (rasterLocation presentation.finalNormalizationPeriod
          (Cell.add
            (normalizeVertexPosition (presentation.normalizationTarget2 edge))
            ((ContractedEndpoint.target edge).finalNormalizedPort
              presentation).direction.step),
        routingCellTypeAt third
          (Cell.add
            (normalizeVertexPosition (presentation.normalizationTarget2 edge))
            ((ContractedEndpoint.target edge).finalNormalizedPort
              presentation).direction.step)
          (normalizeVertexPosition (presentation.normalizationTarget2 edge))
          edge.color) ∈
        routeInteriorAssignments presentation.finalNormalizationPeriod
          edge.color (presentation.finalNormalizationRoute edge) := by
  obtain ⟨third, reverseRest, reverseEquation, firstStep, secondStep,
      noReverse⟩ :=
    presentation.exists_finalNormalizationRoute_targetTriple edge
  have forwardEquation := congrArg List.reverse reverseEquation
  simp only [List.reverse_reverse, List.reverse_cons] at forwardEquation
  refine ⟨third, reverseRest.reverse, by simpa using forwardEquation, ?_⟩
  exact presentation.targetAdjacentAssignment_mem_of_reverse_eq edge
    reverseEquation

/-- Under collision freedom, the target-adjacent routing cell has the owning
edge's color on the side facing the periodic target occurrence. -/
theorem PlanarPresentation.finalCellTypeAt_targetAdjacent_portColor
    {problem : PeriodicThreeDM}
    {presentation : problem.PlanarPresentation}
    (collisionFree : presentation.FinalAssignmentsCollisionFree)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges) :
    (presentation.finalCellTypeAt
      (rasterLocation presentation.finalNormalizationPeriod
        (Cell.add
          (normalizeVertexPosition (presentation.normalizationTarget2 edge))
          ((ContractedEndpoint.target edge).finalNormalizedPort
            presentation).direction.step))).portColor
      ((ContractedEndpoint.target edge).finalNormalizedPort
        presentation).side.opposite = some edge.color := by
  obtain ⟨third, reverseRest, reverseEquation, firstStep, secondStep,
      reverseNoReverse⟩ :=
    presentation.exists_finalNormalizationRoute_targetTriple edge
  have assignmentMember :=
    presentation.targetAdjacentAssignment_mem_of_reverse_eq edge
      reverseEquation
  rw [presentation.finalCellTypeAt_routeInterior collisionFree edgeMember
    assignmentMember]
  have incoming := secondStep.symm
  have outgoing := firstStep.symm
  have noReverse : AxisDirection.between
      (Cell.add
        (normalizeVertexPosition (presentation.normalizationTarget2 edge))
        ((ContractedEndpoint.target edge).finalNormalizedPort
          presentation).direction.step)
      (normalizeVertexPosition (presentation.normalizationTarget2 edge)) ≠
    (AxisDirection.between third
      (Cell.add
        (normalizeVertexPosition (presentation.normalizationTarget2 edge))
        ((ContractedEndpoint.target edge).finalNormalizedPort
          presentation).direction.step)).opposite := by
    have firstGenuine :=
      AxisDirection.between_isGenuine_of_unitAxisStep firstStep
    have secondGenuine :=
      AxisDirection.between_isGenuine_of_unitAxisStep secondStep
    rw [AxisDirection.between_reverse_eq_opposite firstGenuine]
    rw [AxisDirection.between_reverse_eq_opposite secondGenuine]
    simp only [AxisDirection.opposite_opposite]
    exact Ne.symm reverseNoReverse
  rw [routingCellTypeAt_portColor incoming outgoing noReverse]
  let port := (ContractedEndpoint.target edge).finalNormalizedPort presentation
  have forward : AxisDirection.between
      (normalizeVertexPosition (presentation.normalizationTarget2 edge))
      (Cell.add
        (normalizeVertexPosition (presentation.normalizationTarget2 edge))
        port.direction.step) = port.direction :=
    AxisDirection.between_add_step _
      (CanonicalVertexPort.direction_isGenuine port)
  have backward : AxisDirection.between
      (Cell.add
        (normalizeVertexPosition (presentation.normalizationTarget2 edge))
        port.direction.step)
      (normalizeVertexPosition (presentation.normalizationTarget2 edge)) =
      port.direction.opposite := by
    rw [AxisDirection.between_reverse_eq_opposite
      (AxisDirection.between_isGenuine_of_unitAxisStep firstStep)]
    rw [forward]
  have backwardSide : Side.ofAxisDirection
      (AxisDirection.between
        (Cell.add
          (normalizeVertexPosition (presentation.normalizationTarget2 edge))
          port.direction.step)
        (normalizeVertexPosition (presentation.normalizationTarget2 edge))) =
      port.side.opposite := by
    rw [backward]
    rw [Side.ofAxisDirection_opposite
      (CanonicalVertexPort.direction_isGenuine port)]
    simp
  simp [port, backwardSide]

/-- Every listed edge's target vertex and target-adjacent routing cell expose
the same color on their common finite-torus side. -/
theorem PlanarPresentation.finalCellTypeAt_target_port_matches
    {problem : PeriodicThreeDM}
    {presentation : problem.ContinuousPlanarPresentation}
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (collisionFree :
      presentation.toPlanarPresentation.FinalAssignmentsCollisionFree)
    {edge : ContractedEdge}
    (edgeMember : edge ∈ problem.contractedEdges) :
    let endpoint := ContractedEndpoint.target edge
    let port := endpoint.finalNormalizedPort
      presentation.toPlanarPresentation
    (presentation.toPlanarPresentation.finalCellTypeAt
      (rasterLocation
        presentation.toPlanarPresentation.finalNormalizationPeriod
        (presentation.toPlanarPresentation.finalNormalizationPosition
          edge.toPeriodicEdge.target))).portColor port.side =
    (presentation.toPlanarPresentation.finalCellTypeAt
      (rasterLocation
        presentation.toPlanarPresentation.finalNormalizationPeriod
        (Cell.add
          (normalizeVertexPosition
            (presentation.toPlanarPresentation.normalizationTarget2 edge))
          port.direction.step))).portColor port.side.opposite := by
  dsimp only
  let endpoint := ContractedEndpoint.target edge
  have endpointMember : endpoint ∈ problem.contractedEndpoints := by
    simp only [endpoint, contractedEndpoints, List.mem_flatMap]
    exact ⟨edge, edgeMember, by simp⟩
  have vertexMember := endpoint.vertex_mem_of_mem endpointMember
  have targetVertex : endpoint.vertex = edge.toPeriodicEdge.target := rfl
  rw [← targetVertex]
  rw [presentation.toPlanarPresentation.finalCellTypeAt_vertex
    collisionFree vertexMember]
  rw [PlanarPresentation.finalVertexCellType_portColor_endpoint
    (presentation := presentation) wellFormed degree endpointMember]
  simpa [endpoint, targetVertex, ContractedEndpoint.color,
    ContractedEndpoint.edge] using
    (PlanarPresentation.finalCellTypeAt_targetAdjacent_portColor
      (presentation := presentation.toPlanarPresentation)
      collisionFree edgeMember).symm

end PeriodicThreeDM
end LeanTrominoes
