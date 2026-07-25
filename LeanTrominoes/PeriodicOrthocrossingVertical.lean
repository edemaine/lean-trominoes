import LeanTrominoes.PeriodicOrthocrossingHorizontal

/-!
# Vertical private lanes in the periodic track construction

Vertical fanout and boundary pieces have unit length, so no integer grid point
lies in their relative interior.  Every vertical occurrence relevant to the
orthocrossing condition is therefore either a real port column or a private
gate column.  This file normalizes those columns to the fundamental square and
proves that their representatives identify the semantic segment role.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 800000

/-- The three kinds of vertical pieces long enough to contain an integer grid
point in their relative interior. -/
def SegmentRole.IsActiveVertical {Vertex : Type*} :
    SegmentRole Vertex → Prop
  | .sourcePortVertical _
  | .gateVertical _
  | .targetPortVertical _ => True
  | _ => False

/-- Port named by an active vertical role, when the role uses a real port
column rather than a private gate column. -/
def SegmentRole.activeVerticalPort {Vertex : Type*} :
    SegmentRole Vertex → Option (GraphPort Vertex)
  | .sourcePortVertical port
  | .targetPortVertical port => some port
  | _ => none

/-- The owner of an active vertical lane: either a real graph port or a
private gate belonging to an indexed protoedge. -/
def SegmentRole.activeVerticalLaneOwner {Vertex : Type*} :
    SegmentRole Vertex → Option (GraphPort Vertex ⊕ Nat)
  | .sourcePortVertical port
  | .targetPortVertical port => some (.inl port)
  | .gateVertical edgeIndex => some (.inr edgeIndex)
  | _ => none

/-- Source and target port-column roles name a port of the corresponding
endpoint kind. -/
def SegmentRole.ActiveVerticalEndCorrect {Vertex : Type*} :
    SegmentRole Vertex → Prop
  | .sourcePortVertical port => port.endKind = .source
  | .targetPortVertical port => port.endKind = .target
  | _ => True

instance {Vertex : Type*} (role : SegmentRole Vertex) :
    Decidable role.IsActiveVertical := by
  cases role <;> unfold SegmentRole.IsActiveVertical <;> infer_instance

/-- A unit vertical segment has no integer grid point in its relative
interior. -/
theorem not_interiorContains_of_unit_vertical
    {segment : GridSegment} {point : Cell}
    (vertical : segment.IsVertical)
    (unit :
      segment.finish.2 = segment.start.2 + 1 ∨
        segment.start.2 = segment.finish.2 + 1) :
    ¬segment.InteriorContains point := by
  intro contains
  rcases contains with
    ⟨horizontal, _, _⟩ | ⟨_, _, between⟩
  · exact vertical.2 horizontal.1
  · unfold GridSegment.StrictlyBetween at between
    rcases unit with unit | unit <;>
      rcases between with between | between <;>
      omega

/-- The only nonactive vertical piece in an edge core is the unit boundary
step used by a horizontal cell-crossing detour. -/
theorem classifiedEdgeCore_vertical_active_or_boundary
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {edge : PeriodicEdge Vertex} {edgeIndex : Nat}
    {classified : ClassifiedSegment Vertex}
    (classifiedMem :
      classified ∈ classifiedEdgeCore graph edge edgeIndex)
    (vertical : classified.segment.IsVertical) :
    classified.role.IsActiveVertical ∨
      classified.role = .boundaryVertical edgeIndex := by
  have all :
      ∀ item ∈ classifiedEdgeCore graph edge edgeIndex,
        item.segment.IsVertical →
        item.role.IsActiveVertical ∨
          item.role = .boundaryVertical edgeIndex := by
    simp [classifiedEdgeCore, SegmentRole.IsActiveVertical,
      GridSegment.IsVertical, Cell.add, Cell.scale]
    split <;> simp_all
    all_goals split <;> simp_all
    all_goals omega
  exact all classified classifiedMem vertical

/-- A classified boundary step has unit vertical length, also after an
occurrence translation. -/
theorem classifiedEdgeCore_boundary_unit
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {edge : PeriodicEdge Vertex} {edgeIndex : Nat}
    {classified : ClassifiedSegment Vertex}
    (classifiedMem :
      classified ∈ classifiedEdgeCore graph edge edgeIndex)
    (boundary :
      classified.role = .boundaryVertical edgeIndex)
    (translate : Cell) :
    (classified.segment.translate
        ((drawing graph).periodTranslation translate)).finish.2 =
      (classified.segment.translate
        ((drawing graph).periodTranslation translate)).start.2 + 1 := by
  have all :
      ∀ item ∈ classifiedEdgeCore graph edge edgeIndex,
        item.role = .boundaryVertical edgeIndex →
        (item.segment.translate
            ((drawing graph).periodTranslation translate)).finish.2 =
          (item.segment.translate
            ((drawing graph).periodTranslation translate)).start.2 + 1 := by
    simp [classifiedEdgeCore]
    split <;> simp_all
    all_goals split <;> simp_all
    all_goals simp [GridSegment.translate,
      PeriodicGridDrawing.periodTranslation, drawing_gridSize,
      Cell.add, Cell.scale]
    all_goals omega
  exact all classified classifiedMem boundary

/-- Any classified vertical occurrence whose interior contains an integer
grid point has one of the three active vertical roles. -/
theorem classifiedSegment_activeVertical_of_interiorContains
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {edge : PeriodicEdge Vertex} {edgeIndex : Nat}
    {classified : ClassifiedSegment Vertex}
    (classifiedMem :
      classified ∈ classifiedRouteSegments graph edge edgeIndex)
    (translate point : Cell)
    (contains :
      (classified.segment.translate
        ((drawing graph).periodTranslation translate)).InteriorContains
          point)
    (vertical :
      (classified.segment.translate
        ((drawing graph).periodTranslation translate)).IsVertical) :
    classified.role.IsActiveVertical := by
  have storedVertical :
      classified.segment.IsVertical :=
    (GridSegment.isVertical_translate _ _).mp vertical
  have sourceAll :
      ∀ item ∈ classifiedSourceFanout graph edge edgeIndex,
        (item.segment.translate
          ((drawing graph).periodTranslation translate)).InteriorContains
            point →
        (item.segment.translate
          ((drawing graph).periodTranslation translate)).IsVertical →
        item.role.IsActiveVertical := by
    intro item itemMem itemContains itemVertical
    by_cases same :
        vertexX (graph.vertices.idxOf edge.source) =
          portX graph (sourcePort edge edgeIndex)
    · simp [classifiedSourceFanout, same] at itemMem
      subst item
      exact (not_interiorContains_of_unit_vertical
        (point := point) itemVertical (by
          left
          simp [GridSegment.translate,
            PeriodicGridDrawing.periodTranslation, drawing_gridSize,
            Cell.add, Cell.scale]
          omega)) itemContains
    · simp [classifiedSourceFanout, same] at itemMem
      rcases itemMem with rfl | rfl
      · simp [GridSegment.IsVertical, GridSegment.translate,
          PeriodicGridDrawing.periodTranslation, drawing_gridSize,
          Cell.add, Cell.scale] at itemVertical
      · exact (not_interiorContains_of_unit_vertical
          (point := point) itemVertical (by
            left
            simp [GridSegment.translate,
              PeriodicGridDrawing.periodTranslation, drawing_gridSize,
              Cell.add, Cell.scale]
            omega)) itemContains
  have coreAll :
      ∀ item ∈ classifiedEdgeCore graph edge edgeIndex,
        (item.segment.translate
          ((drawing graph).periodTranslation translate)).InteriorContains
            point →
        (item.segment.translate
          ((drawing graph).periodTranslation translate)).IsVertical →
        item.role.IsActiveVertical := by
    intro item itemMem itemContains itemVertical
    have itemStoredVertical :
        item.segment.IsVertical :=
      (GridSegment.isVertical_translate _ _).mp itemVertical
    rcases classifiedEdgeCore_vertical_active_or_boundary
        itemMem itemStoredVertical with active | boundary
    · exact active
    · exact (not_interiorContains_of_unit_vertical
        (point := point) itemVertical (Or.inl
          (classifiedEdgeCore_boundary_unit
            itemMem boundary translate)) itemContains).elim
  have targetAll :
      ∀ item ∈ classifiedTargetFanout graph edge edgeIndex,
        (item.segment.translate
          ((drawing graph).periodTranslation translate)).InteriorContains
            point →
        (item.segment.translate
          ((drawing graph).periodTranslation translate)).IsVertical →
        item.role.IsActiveVertical := by
    intro item itemMem itemContains itemVertical
    by_cases same :
        vertexX (graph.vertices.idxOf edge.target) =
          portX graph (targetPort edge edgeIndex)
    · simp [classifiedTargetFanout, same] at itemMem
      subst item
      exact (not_interiorContains_of_unit_vertical
        (point := point) itemVertical (by
          right
          simp [GridSegment.translate,
            PeriodicGridDrawing.periodTranslation, drawing_gridSize,
            Cell.add, Cell.scale]
          omega)) itemContains
    · simp [classifiedTargetFanout, same] at itemMem
      rcases itemMem with rfl | rfl
      · exact (not_interiorContains_of_unit_vertical
          (point := point) itemVertical (by
            right
            simp [GridSegment.translate,
              PeriodicGridDrawing.periodTranslation, drawing_gridSize,
              Cell.add, Cell.scale]
            omega)) itemContains
      · simp [GridSegment.IsVertical, GridSegment.translate,
          PeriodicGridDrawing.periodTranslation, drawing_gridSize,
          Cell.add, Cell.scale] at itemVertical
  simp only [classifiedRouteSegments, List.mem_append] at classifiedMem
  exact classifiedMem.elim
    (fun sourceOrCore => sourceOrCore.elim
      (fun sourceMem =>
        sourceAll classified sourceMem contains vertical)
      (fun coreMem =>
        coreAll classified coreMem contains vertical))
    (fun targetMem =>
      targetAll classified targetMem contains vertical)

/-- Fundamental-square representative of an active vertical lane. -/
def verticalLaneBase {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) : SegmentRole Vertex → Int
  | .sourcePortVertical port
  | .targetPortVertical port => portX graph port
  | .gateVertical edgeIndex => edgeGateX graph edgeIndex
  | _ => 0

/-- Whole-cell correction already stored in an active vertical lane. -/
def verticalLaneCellShift {Vertex : Type*}
    (edge : PeriodicEdge Vertex) : SegmentRole Vertex → Int
  | .targetPortVertical _ => edge.offset.1
  | _ => 0

/-- Column assigned to an active vertical lane owner. -/
def verticalLaneOwnerX {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) : GraphPort Vertex ⊕ Nat → Int
  | .inl port => portX graph port
  | .inr edgeIndex => edgeGateX graph edgeIndex

/-- An active role's lane representative is the column of its owner. -/
theorem verticalLaneBase_eq_ownerX
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {role : SegmentRole Vertex}
    {owner : GraphPort Vertex ⊕ Nat}
    (ownerEq : role.activeVerticalLaneOwner = some owner) :
    verticalLaneBase graph role = verticalLaneOwnerX graph owner := by
  cases role <;>
    simp [SegmentRole.activeVerticalLaneOwner] at ownerEq
  all_goals subst owner <;>
    rfl

/-- Every active vertical role exposes a lane owner. -/
theorem exists_activeVerticalLaneOwner
    {Vertex : Type*} {role : SegmentRole Vertex}
    (active : role.IsActiveVertical) :
    ∃ owner, role.activeVerticalLaneOwner = some owner := by
  cases role <;>
    simp_all [SegmentRole.IsActiveVertical,
      SegmentRole.activeVerticalLaneOwner]

/-- Real port columns and private gate columns are mutually disjoint, and
each family is internally injective. -/
theorem verticalLaneOwnerX_injective
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    {first second : GraphPort Vertex ⊕ Nat}
    (firstPortMem :
      ∀ port, first = .inl port → port ∈ allPorts graph)
    (secondPortMem :
      ∀ port, second = .inl port → port ∈ allPorts graph)
    (sameX :
      verticalLaneOwnerX graph first =
        verticalLaneOwnerX graph second) :
    first = second := by
  cases first with
  | inl firstPort =>
      cases second with
      | inl secondPort =>
          have firstMem := firstPortMem firstPort rfl
          have secondMem := secondPortMem secondPort rfl
          have portsEqual :=
            portX_injective_on_allPorts
              wellFormed degree firstMem secondMem
                (by simpa [verticalLaneOwnerX] using sameX)
          simp [portsEqual]
      | inr secondEdgeIndex =>
          have firstMem := firstPortMem firstPort rfl
          have separated :=
            portX_lt_edgeGateX
              wellFormed degree firstMem secondEdgeIndex
          simp [verticalLaneOwnerX] at sameX
          omega
  | inr firstEdgeIndex =>
      cases second with
      | inl secondPort =>
          have secondMem := secondPortMem secondPort rfl
          have separated :=
            portX_lt_edgeGateX
              wellFormed degree secondMem firstEdgeIndex
          simp [verticalLaneOwnerX] at sameX
          omega
      | inr secondEdgeIndex =>
          simp [verticalLaneOwnerX, edgeGateX] at sameX
          simp_all

/-- Equal owners identify equal active roles once source and target endpoint
kinds are known to be correct. -/
theorem activeVertical_roles_eq_of_owner_eq
    {Vertex : Type*}
    {first second : SegmentRole Vertex}
    (firstActive : first.IsActiveVertical)
    (secondActive : second.IsActiveVertical)
    (firstEnd : first.ActiveVerticalEndCorrect)
    (secondEnd : second.ActiveVerticalEndCorrect)
    (ownersEqual :
      first.activeVerticalLaneOwner =
        second.activeVerticalLaneOwner) :
    first = second := by
  cases first <;> cases second <;>
    simp_all [SegmentRole.IsActiveVertical,
      SegmentRole.ActiveVerticalEndCorrect,
      SegmentRole.activeVerticalLaneOwner]

/-- A classified active vertical segment's stored column is its fundamental
lane plus the whole-cell correction carried by a target port. -/
theorem classifiedSegment_vertical_lane
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {edge : PeriodicEdge Vertex} {edgeIndex : Nat}
    {classified : ClassifiedSegment Vertex}
    (classifiedMem :
      classified ∈ classifiedRouteSegments graph edge edgeIndex)
    (active : classified.role.IsActiveVertical) :
    classified.segment.start.1 =
      verticalLaneBase graph classified.role +
        drawingGridSize graph *
          verticalLaneCellShift edge classified.role := by
  have all :
      ∀ item ∈ classifiedRouteSegments graph edge edgeIndex,
        item.role.IsActiveVertical →
        item.segment.start.1 =
          verticalLaneBase graph item.role +
            drawingGridSize graph *
              verticalLaneCellShift edge item.role := by
    let sourceCenter := vertexX (graph.vertices.idxOf edge.source)
    let targetCenter := vertexX (graph.vertices.idxOf edge.target)
    let sourceColumn := portX graph (sourcePort edge edgeIndex)
    let targetColumn := portX graph (targetPort edge edgeIndex)
    by_cases sourceSame : sourceCenter = sourceColumn <;>
      by_cases targetSame : targetCenter = targetColumn <;>
      simp [classifiedRouteSegments, classifiedSourceFanout,
        classifiedEdgeCore, classifiedTargetFanout,
        SegmentRole.IsActiveVertical, verticalLaneBase,
        verticalLaneCellShift, sourceCenter, targetCenter,
        sourceColumn, targetColumn, sourceSame, targetSame,
        Cell.add, Cell.scale]
    all_goals split <;> simp_all
    all_goals try aesop
    all_goals simp_all [add_comm]
  exact all classified classifiedMem active

/-- Active vertical port roles produced by the constructor name real graph
ports. -/
theorem classifiedSegment_activeVerticalPort_mem
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {edge : PeriodicEdge Vertex} {edgeIndex : Nat}
    (edgeMem : (edge, edgeIndex) ∈ graph.edges.zipIdx)
    {classified : ClassifiedSegment Vertex}
    (classifiedMem :
      classified ∈ classifiedRouteSegments graph edge edgeIndex)
    {port : GraphPort Vertex}
    (portEq : classified.role.activeVerticalPort = some port) :
    port ∈ allPorts graph := by
  have sourceMem := sourcePort_mem_allPorts graph edgeMem
  have targetMem := targetPort_mem_allPorts graph edgeMem
  have sourceAll :
      ∀ item ∈ classifiedSourceFanout graph edge edgeIndex,
        item.role.activeVerticalPort = some port →
          port ∈ allPorts graph := by
    simp [classifiedSourceFanout,
      SegmentRole.activeVerticalPort]
    split <;> simp_all
  have coreAll :
      ∀ item ∈ classifiedEdgeCore graph edge edgeIndex,
        item.role.activeVerticalPort = some port →
          port ∈ allPorts graph := by
    simp [classifiedEdgeCore,
      SegmentRole.activeVerticalPort]
    split <;> simp_all
    all_goals aesop
  have targetAll :
      ∀ item ∈ classifiedTargetFanout graph edge edgeIndex,
        item.role.activeVerticalPort = some port →
          port ∈ allPorts graph := by
    simp [classifiedTargetFanout,
      SegmentRole.activeVerticalPort]
    split <;> simp_all
  simp only [classifiedRouteSegments, List.mem_append] at classifiedMem
  exact classifiedMem.elim
    (fun sourceOrCore => sourceOrCore.elim
      (fun sourceClassified =>
        sourceAll classified sourceClassified portEq)
      (fun coreClassified =>
        coreAll classified coreClassified portEq))
    (fun targetClassified =>
      targetAll classified targetClassified portEq)

/-- Every active vertical lane representative lies in the half-open
fundamental drawing period. -/
theorem verticalLaneBase_bounds
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    {edge : PeriodicEdge Vertex} {edgeIndex : Nat}
    (edgeMem : (edge, edgeIndex) ∈ graph.edges.zipIdx)
    {classified : ClassifiedSegment Vertex}
    (classifiedMem :
      classified ∈ classifiedRouteSegments graph edge edgeIndex)
    (active : classified.role.IsActiveVertical) :
    0 ≤ verticalLaneBase graph classified.role ∧
      verticalLaneBase graph classified.role < drawingGridSize graph := by
  have roleIndex := classifiedSegment_role_edgeIndex classifiedMem
  cases roleEq : classified.role with
  | sourcePortVertical port =>
      have portMem :=
        classifiedSegment_activeVerticalPort_mem
          edgeMem classifiedMem (port := port) (by
            simp [roleEq, SegmentRole.activeVerticalPort])
      have bounds := portX_bounds wellFormed degree portMem
      simpa [roleEq, verticalLaneBase] using
        And.intro (le_of_lt bounds.1) bounds.2
  | gateVertical roleEdgeIndex =>
      have gateBounds := edgeGateX_bounds graph edgeMem
      have indexEq : roleEdgeIndex = edgeIndex := by
        simpa [roleEq, SegmentRole.edgeIndex] using roleIndex
      subst roleEdgeIndex
      simpa [roleEq, verticalLaneBase] using
        And.intro (le_of_lt gateBounds.1) gateBounds.2
  | targetPortVertical port =>
      have portMem :=
        classifiedSegment_activeVerticalPort_mem
          edgeMem classifiedMem (port := port) (by
            simp [roleEq, SegmentRole.activeVerticalPort])
      have bounds := portX_bounds wellFormed degree portMem
      simpa [roleEq, verticalLaneBase] using
        And.intro (le_of_lt bounds.1) bounds.2
  | sourceFanoutHorizontal port =>
      simp [roleEq, SegmentRole.IsActiveVertical] at active
  | sourceFanoutVertical port =>
      simp [roleEq, SegmentRole.IsActiveVertical] at active
  | lowHorizontal roleEdgeIndex =>
      simp [roleEq, SegmentRole.IsActiveVertical] at active
  | highHorizontal roleEdgeIndex =>
      simp [roleEq, SegmentRole.IsActiveVertical] at active
  | boundaryVertical roleEdgeIndex =>
      simp [roleEq, SegmentRole.IsActiveVertical] at active
  | targetFanoutVertical port =>
      simp [roleEq, SegmentRole.IsActiveVertical] at active
  | targetFanoutHorizontal port =>
      simp [roleEq, SegmentRole.IsActiveVertical] at active

/-- Active vertical roles produced by the route constructor carry the
endpoint kind appropriate to their source or target side. -/
theorem classifiedSegment_activeVerticalEndCorrect
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {edge : PeriodicEdge Vertex} {edgeIndex : Nat}
    {classified : ClassifiedSegment Vertex}
    (classifiedMem :
      classified ∈ classifiedRouteSegments graph edge edgeIndex) :
    classified.role.ActiveVerticalEndCorrect := by
  have sourceAll :
      ∀ item ∈ classifiedSourceFanout graph edge edgeIndex,
        item.role.ActiveVerticalEndCorrect := by
    simp [classifiedSourceFanout,
      SegmentRole.ActiveVerticalEndCorrect, sourcePort]
    split <;> simp_all
  have coreAll :
      ∀ item ∈ classifiedEdgeCore graph edge edgeIndex,
        item.role.ActiveVerticalEndCorrect := by
    simp [classifiedEdgeCore,
      SegmentRole.ActiveVerticalEndCorrect, sourcePort, targetPort]
    split <;> simp_all
    all_goals split <;> simp_all
  have targetAll :
      ∀ item ∈ classifiedTargetFanout graph edge edgeIndex,
        item.role.ActiveVerticalEndCorrect := by
    simp [classifiedTargetFanout,
      SegmentRole.ActiveVerticalEndCorrect, targetPort]
    split <;> simp_all
  simp only [classifiedRouteSegments, List.mem_append] at classifiedMem
  exact classifiedMem.elim
    (fun sourceOrCore => sourceOrCore.elim
      (fun sourceMem => sourceAll classified sourceMem)
      (fun coreMem => coreAll classified coreMem))
    (fun targetMem => targetAll classified targetMem)

/-- Equal normalized columns identify equal active vertical semantic roles
across two constructed routes. -/
theorem activeVertical_roles_eq_of_lanes_eq
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    {firstEdge secondEdge : PeriodicEdge Vertex}
    {firstEdgeIndex secondEdgeIndex : Nat}
    (firstEdgeMem :
      (firstEdge, firstEdgeIndex) ∈ graph.edges.zipIdx)
    (secondEdgeMem :
      (secondEdge, secondEdgeIndex) ∈ graph.edges.zipIdx)
    {firstClassified secondClassified : ClassifiedSegment Vertex}
    (firstClassifiedMem :
      firstClassified ∈
        classifiedRouteSegments graph firstEdge firstEdgeIndex)
    (secondClassifiedMem :
      secondClassified ∈
        classifiedRouteSegments graph secondEdge secondEdgeIndex)
    (firstActive : firstClassified.role.IsActiveVertical)
    (secondActive : secondClassified.role.IsActiveVertical)
    (lanesEqual :
      verticalLaneBase graph firstClassified.role =
        verticalLaneBase graph secondClassified.role) :
    firstClassified.role = secondClassified.role := by
  rcases exists_activeVerticalLaneOwner firstActive with
    ⟨firstOwner, firstOwnerEq⟩
  rcases exists_activeVerticalLaneOwner secondActive with
    ⟨secondOwner, secondOwnerEq⟩
  have ownerColumnsEqual :
      verticalLaneOwnerX graph firstOwner =
        verticalLaneOwnerX graph secondOwner := by
    rw [← verticalLaneBase_eq_ownerX graph firstOwnerEq,
      ← verticalLaneBase_eq_ownerX graph secondOwnerEq]
    exact lanesEqual
  have firstOwnerPortMem :
      ∀ port, firstOwner = .inl port → port ∈ allPorts graph := by
    intro port ownerEq
    have portEq :
        firstClassified.role.activeVerticalPort = some port := by
      cases roleEq : firstClassified.role <;>
        simp_all [SegmentRole.IsActiveVertical,
          SegmentRole.activeVerticalLaneOwner,
          SegmentRole.activeVerticalPort]
    exact classifiedSegment_activeVerticalPort_mem
      firstEdgeMem firstClassifiedMem portEq
  have secondOwnerPortMem :
      ∀ port, secondOwner = .inl port → port ∈ allPorts graph := by
    intro port ownerEq
    have portEq :
        secondClassified.role.activeVerticalPort = some port := by
      cases roleEq : secondClassified.role <;>
        simp_all [SegmentRole.IsActiveVertical,
          SegmentRole.activeVerticalLaneOwner,
          SegmentRole.activeVerticalPort]
    exact classifiedSegment_activeVerticalPort_mem
      secondEdgeMem secondClassifiedMem portEq
  have ownersEqual :=
    verticalLaneOwnerX_injective
      wellFormed degree firstOwnerPortMem secondOwnerPortMem
        ownerColumnsEqual
  have optionOwnersEqual :
      firstClassified.role.activeVerticalLaneOwner =
        secondClassified.role.activeVerticalLaneOwner := by
    rw [firstOwnerEq, secondOwnerEq, ownersEqual]
  exact activeVertical_roles_eq_of_owner_eq
    firstActive secondActive
      (classifiedSegment_activeVerticalEndCorrect firstClassifiedMem)
      (classifiedSegment_activeVerticalEndCorrect secondClassifiedMem)
      optionOwnersEqual

end PeriodicOrthocrossing
end LeanTrominoes
