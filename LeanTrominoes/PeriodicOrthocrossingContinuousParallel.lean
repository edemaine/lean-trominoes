import LeanTrominoes.PeriodicOrthocrossingCertified
import LeanTrominoes.PeriodicOrthocrossingCrossoverCenterDisjointness
import LeanTrominoes.PeriodicGridDrawingContinuousPlanarity

/-!
# Continuous separation of parallel source segments

The integer-point orthocrossing certificate deliberately ignores open
overlap shorter than one grid cell.  Physical gadget corridors need the
continuous statement.  The constructed drawing has even horizontal
coordinates, so any continuous overlap of horizontal segment interiors
contains an integer grid point and is already covered by the established
private-lane theorem.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 800000

/-- There is still an integer strictly between two distinct even integers. -/
theorem add_one_lt_of_even_of_even_of_lt
    {first second : Int}
    (firstEven : Even first)
    (secondEven : Even second)
    (less : first < second) :
    first + 1 < second := by
  rcases firstEven with ⟨firstHalf, firstEq⟩
  rcases secondEven with ⟨secondHalf, secondEq⟩
  omega

/-- The minimum of two even integers is even. -/
theorem even_min {first second : Int}
    (firstEven : Even first) (secondEven : Even second) :
    Even (min first second) := by
  rcases le_total first second with ordered | ordered
  · simpa [min_eq_left ordered] using firstEven
  · simpa [min_eq_right ordered] using secondEven

/-- The maximum of two even integers is even. -/
theorem even_max {first second : Int}
    (firstEven : Even first) (secondEven : Even second) :
    Even (max first second) := by
  rcases le_total first second with ordered | ordered
  · simpa [max_eq_right ordered] using secondEven
  · simpa [max_eq_left ordered] using firstEven

/-- Two nondegenerate open intervals with even endpoints have a common
integer interior point whenever their continuous interiors overlap. -/
theorem
    exists_common_strictlyBetween_of_openIntervalsOverlap_of_even_endpoints
    {firstStart firstFinish secondStart secondFinish : Int}
    (firstDifferent : firstStart ≠ firstFinish)
    (secondDifferent : secondStart ≠ secondFinish)
    (firstStartEven : Even firstStart)
    (firstFinishEven : Even firstFinish)
    (secondStartEven : Even secondStart)
    (secondFinishEven : Even secondFinish)
    (overlap :
      GridSegment.OpenIntervalsOverlap
        firstStart firstFinish secondStart secondFinish) :
    ∃ point,
      GridSegment.StrictlyBetween firstStart firstFinish point ∧
        GridSegment.StrictlyBetween secondStart secondFinish point := by
  let firstLower := min firstStart firstFinish
  let firstUpper := max firstStart firstFinish
  let secondLower := min secondStart secondFinish
  let secondUpper := max secondStart secondFinish
  let lower := max firstLower secondLower
  have firstLowerEven : Even firstLower :=
    even_min firstStartEven firstFinishEven
  have firstUpperEven : Even firstUpper :=
    even_max firstStartEven firstFinishEven
  have secondLowerEven : Even secondLower :=
    even_min secondStartEven secondFinishEven
  have secondUpperEven : Even secondUpper :=
    even_max secondStartEven secondFinishEven
  have lowerEven : Even lower :=
    even_max firstLowerEven secondLowerEven
  have firstNonempty : firstLower < firstUpper := by
    simp only [firstLower, firstUpper]
    rcases lt_or_gt_of_ne firstDifferent with forward | backward
    · rw [min_eq_left (le_of_lt forward),
        max_eq_right (le_of_lt forward)]
      exact forward
    · rw [min_eq_right (le_of_lt backward),
        max_eq_left (le_of_lt backward)]
      exact backward
  have secondNonempty : secondLower < secondUpper := by
    simp only [secondLower, secondUpper]
    rcases lt_or_gt_of_ne secondDifferent with forward | backward
    · rw [min_eq_left (le_of_lt forward),
        max_eq_right (le_of_lt forward)]
      exact forward
    · rw [min_eq_right (le_of_lt backward),
        max_eq_left (le_of_lt backward)]
      exact backward
  have overlap' :
      firstLower < secondUpper ∧ secondLower < firstUpper := by
    simpa [GridSegment.OpenIntervalsOverlap,
      firstLower, firstUpper, secondLower, secondUpper] using overlap
  have lowerLtFirstUpper : lower < firstUpper := by
    simp only [lower, max_lt_iff]
    exact ⟨firstNonempty, overlap'.2⟩
  have lowerLtSecondUpper : lower < secondUpper := by
    simp only [lower, max_lt_iff]
    exact ⟨overlap'.1, secondNonempty⟩
  have pointLtFirstUpper : lower + 1 < firstUpper :=
    add_one_lt_of_even_of_even_of_lt
      lowerEven firstUpperEven lowerLtFirstUpper
  have pointLtSecondUpper : lower + 1 < secondUpper :=
    add_one_lt_of_even_of_even_of_lt
      lowerEven secondUpperEven lowerLtSecondUpper
  have firstLowerLtPoint : firstLower < lower + 1 := by
    have : firstLower ≤ lower := by
      simp [lower]
    omega
  have secondLowerLtPoint : secondLower < lower + 1 := by
    have : secondLower ≤ lower := by
      simp [lower]
    omega
  refine ⟨lower + 1, ?_, ?_⟩
  · unfold GridSegment.StrictlyBetween
    rcases lt_or_gt_of_ne firstDifferent with forward | backward
    · left
      simpa [firstLower, firstUpper,
        min_eq_left (le_of_lt forward),
        max_eq_right (le_of_lt forward)] using
          And.intro firstLowerLtPoint pointLtFirstUpper
    · right
      simpa [firstLower, firstUpper,
        min_eq_right (le_of_lt backward),
        max_eq_left (le_of_lt backward)] using
          And.intro firstLowerLtPoint pointLtFirstUpper
  · unfold GridSegment.StrictlyBetween
    rcases lt_or_gt_of_ne secondDifferent with forward | backward
    · left
      simpa [secondLower, secondUpper,
        min_eq_left (le_of_lt forward),
        max_eq_right (le_of_lt forward)] using
          And.intro secondLowerLtPoint pointLtSecondUpper
    · right
      simpa [secondLower, secondUpper,
        min_eq_right (le_of_lt backward),
        max_eq_left (le_of_lt backward)] using
          And.intro secondLowerLtPoint pointLtSecondUpper

/-- Open translates of the same interval of length at most one period can
overlap only when their period shifts agree. -/
theorem openIntervalsOverlap_periodic_shifts_unique
    {period first last firstShift secondShift : Int}
    (periodPositive : 0 < period)
    (spanForward : last - first ≤ period)
    (spanBackward : first - last ≤ period)
    (overlap :
      GridSegment.OpenIntervalsOverlap
        (first + period * firstShift)
        (last + period * firstShift)
        (first + period * secondShift)
        (last + period * secondShift)) :
    firstShift = secondShift := by
  unfold GridSegment.OpenIntervalsOverlap at overlap
  simp only [min_add_add_right, max_add_add_right] at overlap
  rcases le_total first last with forward | backward
  · rw [min_eq_left forward, max_eq_right forward] at overlap
    nlinarith
  · rw [min_eq_right backward, max_eq_left backward] at overlap
    nlinarith

/-- The six semantic roles whose generated segments are vertical, including
the unit fanout and boundary roles omitted by `IsActiveVertical`. -/
def SegmentRole.IsContinuousVertical {Vertex : Type*} :
    SegmentRole Vertex → Prop
  | .sourceFanoutVertical _
  | .sourcePortVertical _
  | .gateVertical _
  | .boundaryVertical _
  | .targetPortVertical _
  | .targetFanoutVertical _ => True
  | _ => False

instance {Vertex : Type*} (role : SegmentRole Vertex) :
    Decidable role.IsContinuousVertical := by
  cases role <;>
    unfold SegmentRole.IsContinuousVertical <;>
    infer_instance

/-- Real port named by any continuous vertical port-lane role. -/
def SegmentRole.continuousVerticalPort {Vertex : Type*} :
    SegmentRole Vertex → Option (GraphPort Vertex)
  | .sourceFanoutVertical port
  | .sourcePortVertical port
  | .targetPortVertical port
  | .targetFanoutVertical port => some port
  | _ => none

/-- Endpoint kind expected of the four port-lane roles. -/
def SegmentRole.ContinuousVerticalEndCorrect {Vertex : Type*} :
    SegmentRole Vertex → Prop
  | .sourceFanoutVertical port
  | .sourcePortVertical port => port.endKind = .source
  | .targetPortVertical port
  | .targetFanoutVertical port => port.endKind = .target
  | _ => True

/-- Lane owner for all vertical roles.  `none` is the periodic boundary
column; `some (.inl port)` and `some (.inr edgeIndex)` reuse the established
real-port and private-gate owners. -/
def SegmentRole.continuousVerticalLaneOwner {Vertex : Type*} :
    SegmentRole Vertex → Option (Option (GraphPort Vertex ⊕ Nat))
  | .sourceFanoutVertical port
  | .sourcePortVertical port
  | .targetPortVertical port
  | .targetFanoutVertical port => some (some (.inl port))
  | .gateVertical edgeIndex => some (some (.inr edgeIndex))
  | .boundaryVertical _ => some none
  | _ => none

/-- Fundamental representative of a continuous vertical lane. -/
def continuousVerticalLaneBase
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) : SegmentRole Vertex → Int
  | .sourceFanoutVertical port
  | .sourcePortVertical port
  | .targetPortVertical port
  | .targetFanoutVertical port => portX graph port
  | .gateVertical edgeIndex => edgeGateX graph edgeIndex
  | .boundaryVertical _ => 0
  | _ => 0

/-- Whole-cell correction stored in each continuous vertical lane. -/
def continuousVerticalLaneCellShift
    {Vertex : Type*} (edge : PeriodicEdge Vertex) :
    SegmentRole Vertex → Int
  | .targetPortVertical _
  | .targetFanoutVertical _ => edge.offset.1
  | .boundaryVertical _ =>
      if edge.offset = (1, 0) then 1 else 0
  | _ => 0

/-- Any geometrically vertical classified segment has one of the six
continuous vertical roles. -/
theorem classifiedSegment_continuousVerticalRole_of_isVertical
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {edge : PeriodicEdge Vertex} {edgeIndex : Nat}
    {classified : ClassifiedSegment Vertex}
    (classifiedMem :
      classified ∈ classifiedRouteSegments graph edge edgeIndex)
    (vertical : classified.segment.IsVertical) :
    classified.role.IsContinuousVertical := by
  have sourceAll :
      ∀ item ∈ classifiedSourceFanout graph edge edgeIndex,
        item.segment.IsVertical →
          item.role.IsContinuousVertical := by
    simp [classifiedSourceFanout,
      SegmentRole.IsContinuousVertical,
      GridSegment.IsVertical]
    split <;> simp_all
  have coreAll :
      ∀ item ∈ classifiedEdgeCore graph edge edgeIndex,
        item.segment.IsVertical →
          item.role.IsContinuousVertical := by
    simp [classifiedEdgeCore,
      SegmentRole.IsContinuousVertical,
      GridSegment.IsVertical, Cell.add, Cell.scale]
    split <;> simp_all
    all_goals split <;> simp_all
  have targetAll :
      ∀ item ∈ classifiedTargetFanout graph edge edgeIndex,
        item.segment.IsVertical →
          item.role.IsContinuousVertical := by
    simp [classifiedTargetFanout,
      SegmentRole.IsContinuousVertical,
      GridSegment.IsVertical, Cell.add, Cell.scale]
    split <;> simp_all
  simp only [classifiedRouteSegments, List.mem_append] at classifiedMem
  exact classifiedMem.elim
    (fun sourceOrCore => sourceOrCore.elim
      (fun sourceMem =>
        sourceAll classified sourceMem vertical)
      (fun coreMem =>
        coreAll classified coreMem vertical))
    (fun targetMem =>
      targetAll classified targetMem vertical)

/-- Every continuous vertical port role produced by the constructor names a
real graph port. -/
theorem classifiedSegment_continuousVerticalPort_mem
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {edge : PeriodicEdge Vertex} {edgeIndex : Nat}
    (edgeMem : (edge, edgeIndex) ∈ graph.edges.zipIdx)
    {classified : ClassifiedSegment Vertex}
    (classifiedMem :
      classified ∈ classifiedRouteSegments graph edge edgeIndex)
    {port : GraphPort Vertex}
    (portEq :
      classified.role.continuousVerticalPort = some port) :
    port ∈ allPorts graph := by
  have sourceMem := sourcePort_mem_allPorts graph edgeMem
  have targetMem := targetPort_mem_allPorts graph edgeMem
  have sourceAll :
      ∀ item ∈ classifiedSourceFanout graph edge edgeIndex,
        item.role.continuousVerticalPort = some port →
          port ∈ allPorts graph := by
    simp [classifiedSourceFanout,
      SegmentRole.continuousVerticalPort]
    split <;> simp_all
    all_goals intro equal
    all_goals subst port
    all_goals exact sourceMem
  have coreAll :
      ∀ item ∈ classifiedEdgeCore graph edge edgeIndex,
        item.role.continuousVerticalPort = some port →
          port ∈ allPorts graph := by
    simp [classifiedEdgeCore,
      SegmentRole.continuousVerticalPort]
    split <;> simp_all
    all_goals aesop
  have targetAll :
      ∀ item ∈ classifiedTargetFanout graph edge edgeIndex,
        item.role.continuousVerticalPort = some port →
          port ∈ allPorts graph := by
    simp [classifiedTargetFanout,
      SegmentRole.continuousVerticalPort]
    split <;> simp_all
    all_goals intro equal
    all_goals subst port
    all_goals exact targetMem
  simp only [classifiedRouteSegments, List.mem_append] at classifiedMem
  exact classifiedMem.elim
    (fun sourceOrCore => sourceOrCore.elim
      (fun sourceMem' =>
        sourceAll classified sourceMem' portEq)
      (fun coreMem' =>
        coreAll classified coreMem' portEq))
    (fun targetMem' =>
      targetAll classified targetMem' portEq)

/-- Continuous vertical port roles carry the source/target endpoint kind
appropriate to the part of the route in which they occur. -/
theorem classifiedSegment_continuousVerticalEndCorrect
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {edge : PeriodicEdge Vertex} {edgeIndex : Nat}
    {classified : ClassifiedSegment Vertex}
    (classifiedMem :
      classified ∈ classifiedRouteSegments graph edge edgeIndex) :
    classified.role.ContinuousVerticalEndCorrect := by
  have sourceAll :
      ∀ item ∈ classifiedSourceFanout graph edge edgeIndex,
        item.role.ContinuousVerticalEndCorrect := by
    simp [classifiedSourceFanout,
      SegmentRole.ContinuousVerticalEndCorrect, sourcePort]
    split <;> simp_all
  have coreAll :
      ∀ item ∈ classifiedEdgeCore graph edge edgeIndex,
        item.role.ContinuousVerticalEndCorrect := by
    simp [classifiedEdgeCore,
      SegmentRole.ContinuousVerticalEndCorrect,
      sourcePort, targetPort]
    split <;> simp_all
    all_goals split <;> simp_all
  have targetAll :
      ∀ item ∈ classifiedTargetFanout graph edge edgeIndex,
        item.role.ContinuousVerticalEndCorrect := by
    simp [classifiedTargetFanout,
      SegmentRole.ContinuousVerticalEndCorrect, targetPort]
    split <;> simp_all
  simp only [classifiedRouteSegments, List.mem_append] at classifiedMem
  exact classifiedMem.elim
    (fun sourceOrCore => sourceOrCore.elim
      (fun sourceMem =>
        sourceAll classified sourceMem)
      (fun coreMem =>
        coreAll classified coreMem))
    (fun targetMem =>
      targetAll classified targetMem)

/-- The extended continuous lane data agrees with the established active
lane data on active roles. -/
theorem continuousVerticalLane_data_eq_of_active
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex)
    {role : SegmentRole Vertex}
    (active : role.IsActiveVertical) :
    continuousVerticalLaneBase graph role = verticalLaneBase graph role ∧
      continuousVerticalLaneCellShift edge role =
        verticalLaneCellShift edge role := by
  cases role <;>
    simp_all [SegmentRole.IsActiveVertical,
      continuousVerticalLaneBase,
      continuousVerticalLaneCellShift,
      verticalLaneBase, verticalLaneCellShift]

/-- A classified boundary step uses column one in the positive neighboring
cell and column zero in the negative neighboring cell. -/
theorem classifiedEdgeCore_boundary_vertical_lane
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {edge : PeriodicEdge Vertex} {edgeIndex roleEdgeIndex : Nat}
    {classified : ClassifiedSegment Vertex}
    (classifiedMem :
      classified ∈ classifiedEdgeCore graph edge edgeIndex)
    (boundary :
      classified.role = .boundaryVertical roleEdgeIndex) :
    classified.segment.start.1 =
      drawingGridSize graph *
        (if edge.offset = (1, 0) then 1 else 0) := by
  simp [classifiedEdgeCore] at classifiedMem
  all_goals try split at classifiedMem
  all_goals try split at classifiedMem
  all_goals try simp only [List.mem_cons] at classifiedMem
  all_goals try rcases classifiedMem with rfl | classifiedMem
  all_goals try rcases classifiedMem with rfl | classifiedMem
  all_goals try rcases classifiedMem with rfl | classifiedMem
  all_goals try rcases classifiedMem with rfl | classifiedMem
  all_goals try rcases classifiedMem with rfl | classifiedMem
  all_goals try simp at classifiedMem
  all_goals simp_all

/-- A classified continuous vertical segment's stored column is its
fundamental lane plus the whole-cell correction carried by its role. -/
theorem classifiedSegment_continuousVertical_lane
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {edge : PeriodicEdge Vertex} {edgeIndex : Nat}
    {classified : ClassifiedSegment Vertex}
    (classifiedMem :
      classified ∈ classifiedRouteSegments graph edge edgeIndex)
    (vertical : classified.role.IsContinuousVertical) :
    classified.segment.start.1 =
      continuousVerticalLaneBase graph classified.role +
        drawingGridSize graph *
          continuousVerticalLaneCellShift edge classified.role := by
  have sourceAll :
      ∀ item ∈ classifiedSourceFanout graph edge edgeIndex,
        item.role.IsContinuousVertical →
        item.segment.start.1 =
          continuousVerticalLaneBase graph item.role +
            drawingGridSize graph *
              continuousVerticalLaneCellShift edge item.role := by
    simp [classifiedSourceFanout,
      SegmentRole.IsContinuousVertical,
      continuousVerticalLaneBase,
      continuousVerticalLaneCellShift]
    split <;> simp_all
  have coreAll :
      ∀ item ∈ classifiedEdgeCore graph edge edgeIndex,
        item.role.IsContinuousVertical →
        item.segment.start.1 =
          continuousVerticalLaneBase graph item.role +
            drawingGridSize graph *
              continuousVerticalLaneCellShift edge item.role := by
    intro item itemMem itemVertical
    have itemRoleMem :
        item.role ∈
          (classifiedEdgeCore graph edge edgeIndex).map
            ClassifiedSegment.role :=
      List.mem_map_of_mem itemMem
    have itemFullMem :
        item ∈ classifiedRouteSegments graph edge edgeIndex := by
      simp [classifiedRouteSegments, itemMem]
    by_cases active : item.role.IsActiveVertical
    · have lane :=
        classifiedSegment_vertical_lane itemFullMem active
      have data :=
        continuousVerticalLane_data_eq_of_active graph edge active
      simpa [data.1, data.2] using lane
    · have boundary :
          ∃ roleEdgeIndex,
            item.role = .boundaryVertical roleEdgeIndex := by
        cases roleEq : item.role <;>
          simp_all [SegmentRole.IsActiveVertical,
            SegmentRole.IsContinuousVertical]
        all_goals
          simp [classifiedEdgeCore] at itemRoleMem
          all_goals try split at itemRoleMem
          all_goals try split at itemRoleMem
          all_goals simp_all
      rcases boundary with ⟨roleEdgeIndex, roleEq⟩
      have lane :=
        classifiedEdgeCore_boundary_vertical_lane
          itemMem roleEq
      simpa [roleEq, continuousVerticalLaneBase,
        continuousVerticalLaneCellShift] using lane
  have targetAll :
      ∀ item ∈ classifiedTargetFanout graph edge edgeIndex,
        item.role.IsContinuousVertical →
        item.segment.start.1 =
          continuousVerticalLaneBase graph item.role +
            drawingGridSize graph *
              continuousVerticalLaneCellShift edge item.role := by
    simp [classifiedTargetFanout,
      SegmentRole.IsContinuousVertical,
      continuousVerticalLaneBase,
      continuousVerticalLaneCellShift, Cell.add, Cell.scale]
    split <;> simp_all <;> ring
  simp only [classifiedRouteSegments, List.mem_append] at classifiedMem
  exact classifiedMem.elim
    (fun sourceOrCore => sourceOrCore.elim
      (fun sourceMem =>
        sourceAll classified sourceMem vertical)
      (fun coreMem =>
        coreAll classified coreMem vertical))
    (fun targetMem =>
      targetAll classified targetMem vertical)

/-- Every continuous vertical lane representative lies in the half-open
fundamental drawing period. -/
theorem continuousVerticalLaneBase_bounds
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    {edge : PeriodicEdge Vertex} {edgeIndex : Nat}
    (edgeMem : (edge, edgeIndex) ∈ graph.edges.zipIdx)
    {classified : ClassifiedSegment Vertex}
    (classifiedMem :
      classified ∈ classifiedRouteSegments graph edge edgeIndex)
    (vertical : classified.role.IsContinuousVertical) :
    0 ≤ continuousVerticalLaneBase graph classified.role ∧
      continuousVerticalLaneBase graph classified.role <
        drawingGridSize graph := by
  have roleIndex :=
    classifiedSegment_role_edgeIndex classifiedMem
  cases roleEq : classified.role with
  | sourceFanoutVertical port
  | sourcePortVertical port
  | targetPortVertical port
  | targetFanoutVertical port =>
      have portMem :=
        classifiedSegment_continuousVerticalPort_mem
          edgeMem classifiedMem (port := port) (by
            simp [roleEq, SegmentRole.continuousVerticalPort])
      have bounds := portX_bounds wellFormed degree portMem
      simpa [roleEq, continuousVerticalLaneBase] using
        And.intro (le_of_lt bounds.1) bounds.2
  | gateVertical roleEdgeIndex =>
      have gateBounds := edgeGateX_bounds graph edgeMem
      have indexEq : roleEdgeIndex = edgeIndex := by
        simpa [roleEq, SegmentRole.edgeIndex] using roleIndex
      subst roleEdgeIndex
      simpa [roleEq, continuousVerticalLaneBase] using
        And.intro (le_of_lt gateBounds.1) gateBounds.2
  | boundaryVertical roleEdgeIndex =>
      have periodPositive : 0 < drawingGridSize graph :=
        drawingGridSize_pos graph
      simpa [roleEq, continuousVerticalLaneBase] using
        periodPositive
  | sourceFanoutHorizontal port =>
      simp [roleEq, SegmentRole.IsContinuousVertical] at vertical
  | lowHorizontal roleEdgeIndex =>
      simp [roleEq, SegmentRole.IsContinuousVertical] at vertical
  | highHorizontal roleEdgeIndex =>
      simp [roleEq, SegmentRole.IsContinuousVertical] at vertical
  | targetFanoutHorizontal port =>
      simp [roleEq, SegmentRole.IsContinuousVertical] at vertical

/-- Coordinate represented by one continuous vertical lane owner. -/
def continuousVerticalLaneOwnerX
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    Option (GraphPort Vertex ⊕ Nat) → Int
  | none => 0
  | some owner => verticalLaneOwnerX graph owner

/-- The lane base stored by a vertical role is the coordinate of its owner. -/
theorem continuousVerticalLaneBase_eq_ownerX
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {role : SegmentRole Vertex}
    {owner : Option (GraphPort Vertex ⊕ Nat)}
    (ownerEq : role.continuousVerticalLaneOwner = some owner) :
    continuousVerticalLaneBase graph role =
      continuousVerticalLaneOwnerX graph owner := by
  cases role <;>
    simp [SegmentRole.continuousVerticalLaneOwner] at ownerEq
  all_goals subst owner <;>
    rfl

/-- A real-port continuous lane owner exposes the same port through the
role's port projection. -/
theorem continuousVerticalPort_eq_of_laneOwner_eq_inl
    {Vertex : Type*}
    {role : SegmentRole Vertex}
    {ownerPort port : GraphPort Vertex}
    (ownerEq :
      role.continuousVerticalLaneOwner =
        some (some (.inl ownerPort)))
    (portEq : ownerPort = port) :
    role.continuousVerticalPort = some port := by
  subst port
  cases role <;>
    simp_all [SegmentRole.continuousVerticalLaneOwner,
      SegmentRole.continuousVerticalPort]

/-- Every continuous vertical role exposes a lane owner. -/
theorem exists_continuousVerticalLaneOwner
    {Vertex : Type*} {role : SegmentRole Vertex}
    (vertical : role.IsContinuousVertical) :
    ∃ owner, role.continuousVerticalLaneOwner = some owner := by
  cases role <;>
    simp_all [SegmentRole.IsContinuousVertical,
      SegmentRole.continuousVerticalLaneOwner]

/-- Boundary, real-port, and private-gate continuous vertical lanes have
distinct fundamental representatives. -/
theorem continuousVerticalLaneOwnerX_injective
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    {first second : Option (GraphPort Vertex ⊕ Nat)}
    (firstPortMem :
      ∀ port, first = some (.inl port) → port ∈ allPorts graph)
    (secondPortMem :
      ∀ port, second = some (.inl port) → port ∈ allPorts graph)
    (sameX :
      continuousVerticalLaneOwnerX graph first =
        continuousVerticalLaneOwnerX graph second) :
    first = second := by
  cases first with
  | none =>
      cases second with
      | none => rfl
      | some secondOwner =>
          cases secondOwner with
          | inl secondPort =>
              have secondMem :=
                secondPortMem secondPort rfl
              have positive :=
                (portX_bounds wellFormed degree secondMem).1
              simp [continuousVerticalLaneOwnerX,
                verticalLaneOwnerX] at sameX
              omega
          | inr secondEdgeIndex =>
              simp [continuousVerticalLaneOwnerX,
                verticalLaneOwnerX, edgeGateX] at sameX
              omega
  | some firstOwner =>
      cases second with
      | none =>
          cases firstOwner with
          | inl firstPort =>
              have firstMem :=
                firstPortMem firstPort rfl
              have positive :=
                (portX_bounds wellFormed degree firstMem).1
              simp [continuousVerticalLaneOwnerX,
                verticalLaneOwnerX] at sameX
              omega
          | inr firstEdgeIndex =>
              simp [continuousVerticalLaneOwnerX,
                verticalLaneOwnerX, edgeGateX] at sameX
              omega
      | some secondOwner =>
          have ownersEqual :=
            verticalLaneOwnerX_injective
              wellFormed degree
              (fun port equality =>
                firstPortMem port (congrArg some equality))
              (fun port equality =>
                secondPortMem port (congrArg some equality))
              (by simpa [continuousVerticalLaneOwnerX] using sameX)
          simpa [ownersEqual]

/-- The four ways two distinct vertical port roles can be consecutive parts
of one source or target fanout. -/
def SegmentRole.ContinuousVerticalAdjacent {Vertex : Type*} :
    SegmentRole Vertex → SegmentRole Vertex → Prop
  | .sourceFanoutVertical first, .sourcePortVertical second
  | .sourcePortVertical first, .sourceFanoutVertical second
  | .targetPortVertical first, .targetFanoutVertical second
  | .targetFanoutVertical first, .targetPortVertical second =>
      first = second
  | _, _ => False

/-- Consecutive continuous vertical roles carry the same route-edge
index. -/
theorem SegmentRole.edgeIndex_eq_of_continuousVerticalAdjacent
    {Vertex : Type*}
    {first second : SegmentRole Vertex}
    (adjacent : first.ContinuousVerticalAdjacent second) :
    first.edgeIndex = second.edgeIndex := by
  cases first <;> cases second <;>
    simp_all [SegmentRole.ContinuousVerticalAdjacent,
      SegmentRole.edgeIndex]

/-- Exhaustive semantic forms of two consecutive continuous vertical
roles. -/
theorem continuousVerticalAdjacent_cases
    {Vertex : Type*}
    {first second : SegmentRole Vertex}
    (adjacent : first.ContinuousVerticalAdjacent second) :
    (∃ port,
      first = .sourceFanoutVertical port ∧
        second = .sourcePortVertical port) ∨
    (∃ port,
      first = .sourcePortVertical port ∧
        second = .sourceFanoutVertical port) ∨
    (∃ port,
      first = .targetPortVertical port ∧
        second = .targetFanoutVertical port) ∨
    (∃ port,
      first = .targetFanoutVertical port ∧
        second = .targetPortVertical port) := by
  cases first <;> cases second <;>
    simp_all [SegmentRole.ContinuousVerticalAdjacent]

/-- Equal lane owners identify equal continuous vertical roles, except for
the two adjacent roles at one real port and the family of boundary roles
whose edge index is encoded axially rather than by the column. -/
theorem continuousVertical_roles_eq_or_adjacent_or_boundaries
    {Vertex : Type*}
    {first second : SegmentRole Vertex}
    (firstVertical : first.IsContinuousVertical)
    (secondVertical : second.IsContinuousVertical)
    (firstEnd : first.ContinuousVerticalEndCorrect)
    (secondEnd : second.ContinuousVerticalEndCorrect)
    (ownersEqual :
      first.continuousVerticalLaneOwner =
        second.continuousVerticalLaneOwner) :
    first = second ∨
      first.ContinuousVerticalAdjacent second ∨
      (∃ firstEdgeIndex secondEdgeIndex,
        first = .boundaryVertical firstEdgeIndex ∧
          second = .boundaryVertical secondEdgeIndex) := by
  cases first <;> cases second <;>
    simp_all [SegmentRole.IsContinuousVertical,
      SegmentRole.ContinuousVerticalEndCorrect,
      SegmentRole.continuousVerticalLaneOwner,
      SegmentRole.ContinuousVerticalAdjacent]

/-- A source fanout's vertical step runs exactly from row two to row
three. -/
theorem classifiedSegment_sourceFanoutVertical_y
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {edge : PeriodicEdge Vertex} {edgeIndex : Nat}
    {classified : ClassifiedSegment Vertex}
    (classifiedMem :
      classified ∈ classifiedRouteSegments graph edge edgeIndex)
    {port : GraphPort Vertex}
    (roleEq : classified.role = .sourceFanoutVertical port) :
    classified.segment.start.2 = 2 ∧
      classified.segment.finish.2 = 3 := by
  have sourceAll :
      ∀ item ∈ classifiedSourceFanout graph edge edgeIndex,
        item.role = .sourceFanoutVertical port →
          item.segment.start.2 = 2 ∧
            item.segment.finish.2 = 3 := by
    simp [classifiedSourceFanout]
    split <;> simp_all
  have coreAll :
      ∀ item ∈ classifiedEdgeCore graph edge edgeIndex,
        item.role = .sourceFanoutVertical port →
          item.segment.start.2 = 2 ∧
            item.segment.finish.2 = 3 := by
    simp [classifiedEdgeCore]
    split <;> simp_all
    all_goals split <;> simp_all
  have targetAll :
      ∀ item ∈ classifiedTargetFanout graph edge edgeIndex,
        item.role = .sourceFanoutVertical port →
          item.segment.start.2 = 2 ∧
            item.segment.finish.2 = 3 := by
    simp [classifiedTargetFanout]
    split <;> simp_all
  simp only [classifiedRouteSegments, List.mem_append] at classifiedMem
  exact classifiedMem.elim
    (fun sourceOrCore => sourceOrCore.elim
      (fun sourceMem =>
        sourceAll classified sourceMem roleEq)
      (fun coreMem =>
        coreAll classified coreMem roleEq))
    (fun targetMem =>
      targetAll classified targetMem roleEq)

/-- A target fanout's vertical step runs from its target-cell port row
three back to row two. -/
theorem classifiedSegment_targetFanoutVertical_y
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {edge : PeriodicEdge Vertex} {edgeIndex : Nat}
    {classified : ClassifiedSegment Vertex}
    (classifiedMem :
      classified ∈ classifiedRouteSegments graph edge edgeIndex)
    {port : GraphPort Vertex}
    (roleEq : classified.role = .targetFanoutVertical port) :
    classified.segment.start.2 =
        3 + drawingGridSize graph * edge.offset.2 ∧
      classified.segment.finish.2 =
        2 + drawingGridSize graph * edge.offset.2 := by
  have sourceAll :
      ∀ item ∈ classifiedSourceFanout graph edge edgeIndex,
        item.role = .targetFanoutVertical port →
          item.segment.start.2 =
              3 + drawingGridSize graph * edge.offset.2 ∧
            item.segment.finish.2 =
              2 + drawingGridSize graph * edge.offset.2 := by
    simp [classifiedSourceFanout]
    split <;> simp_all
  have coreAll :
      ∀ item ∈ classifiedEdgeCore graph edge edgeIndex,
        item.role = .targetFanoutVertical port →
          item.segment.start.2 =
              3 + drawingGridSize graph * edge.offset.2 ∧
            item.segment.finish.2 =
              2 + drawingGridSize graph * edge.offset.2 := by
    simp [classifiedEdgeCore]
    split <;> simp_all
    all_goals split <;> simp_all
  have targetAll :
      ∀ item ∈ classifiedTargetFanout graph edge edgeIndex,
        item.role = .targetFanoutVertical port →
          item.segment.start.2 =
              3 + drawingGridSize graph * edge.offset.2 ∧
            item.segment.finish.2 =
              2 + drawingGridSize graph * edge.offset.2 := by
    simp [classifiedTargetFanout, Cell.add, Cell.scale]
    split <;> simp_all <;> ring_nf <;> simp_all
  simp only [classifiedRouteSegments, List.mem_append] at classifiedMem
  exact classifiedMem.elim
    (fun sourceOrCore => sourceOrCore.elim
      (fun sourceMem =>
        sourceAll classified sourceMem roleEq)
      (fun coreMem =>
        coreAll classified coreMem roleEq))
    (fun targetMem =>
      targetAll classified targetMem roleEq)

/-- A source port column begins at row three and ends strictly inside the
top of the fundamental cell. -/
theorem classifiedSegment_sourcePortVertical_y_bounds
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {edge : PeriodicEdge Vertex} {edgeIndex : Nat}
    (edgeMem : (edge, edgeIndex) ∈ graph.edges.zipIdx)
    {classified : ClassifiedSegment Vertex}
    (classifiedMem :
      classified ∈ classifiedRouteSegments graph edge edgeIndex)
    {port : GraphPort Vertex}
    (roleEq : classified.role = .sourcePortVertical port) :
    classified.segment.start.2 = 3 ∧
      3 < classified.segment.finish.2 ∧
        classified.segment.finish.2 < drawingGridSize graph := by
  have tracks := edgeTrack_bounds graph edgeMem
  simp at tracks
  have sourceAll :
      ∀ item ∈ classifiedSourceFanout graph edge edgeIndex,
        item.role = .sourcePortVertical port →
          item.segment.start.2 = 3 ∧
            3 < item.segment.finish.2 ∧
              item.segment.finish.2 < drawingGridSize graph := by
    simp [classifiedSourceFanout]
    split <;> simp_all
  have coreAll :
      ∀ item ∈ classifiedEdgeCore graph edge edgeIndex,
        item.role = .sourcePortVertical port →
          item.segment.start.2 = 3 ∧
            3 < item.segment.finish.2 ∧
              item.segment.finish.2 < drawingGridSize graph := by
    simp [classifiedEdgeCore]
    split <;> simp_all
    all_goals try split <;> simp_all
    all_goals omega
  have targetAll :
      ∀ item ∈ classifiedTargetFanout graph edge edgeIndex,
        item.role = .sourcePortVertical port →
          item.segment.start.2 = 3 ∧
            3 < item.segment.finish.2 ∧
              item.segment.finish.2 < drawingGridSize graph := by
    simp [classifiedTargetFanout]
    split <;> simp_all
  simp only [classifiedRouteSegments, List.mem_append] at classifiedMem
  exact classifiedMem.elim
    (fun sourceOrCore => sourceOrCore.elim
      (fun sourceMem =>
        sourceAll classified sourceMem roleEq)
      (fun coreMem =>
        coreAll classified coreMem roleEq))
    (fun targetMem =>
      targetAll classified targetMem roleEq)

/-- A target port column finishes at row three of the target cell and
approaches that row from above, within one drawing period. -/
theorem classifiedSegment_targetPortVertical_y_bounds
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {edge : PeriodicEdge Vertex} {edgeIndex : Nat}
    (edgeMem : (edge, edgeIndex) ∈ graph.edges.zipIdx)
    (edgeLocal : edge.span ≤ 1)
    {classified : ClassifiedSegment Vertex}
    (classifiedMem :
      classified ∈ classifiedRouteSegments graph edge edgeIndex)
    {port : GraphPort Vertex}
    (roleEq : classified.role = .targetPortVertical port) :
    classified.segment.finish.2 =
        3 + drawingGridSize graph * edge.offset.2 ∧
      3 + drawingGridSize graph * edge.offset.2 <
        classified.segment.start.2 ∧
      classified.segment.start.2 <
        3 + drawingGridSize graph * edge.offset.2 +
          drawingGridSize graph := by
  have tracks := edgeTrack_bounds graph edgeMem
  simp at tracks
  have sourceAll :
      ∀ item ∈ classifiedSourceFanout graph edge edgeIndex,
        item.role = .targetPortVertical port →
          item.segment.finish.2 =
              3 + drawingGridSize graph * edge.offset.2 ∧
            3 + drawingGridSize graph * edge.offset.2 <
              item.segment.start.2 ∧
            item.segment.start.2 <
              3 + drawingGridSize graph * edge.offset.2 +
                drawingGridSize graph := by
    simp [classifiedSourceFanout]
    split <;> simp_all
  have coreAll :
      ∀ item ∈ classifiedEdgeCore graph edge edgeIndex,
        item.role = .targetPortVertical port →
          item.segment.finish.2 =
              3 + drawingGridSize graph * edge.offset.2 ∧
            3 + drawingGridSize graph * edge.offset.2 <
              item.segment.start.2 ∧
            item.segment.start.2 <
              3 + drawingGridSize graph * edge.offset.2 +
                drawingGridSize graph := by
    rcases offset_eq_of_span_le_one edge edgeLocal with
      offsetZero | offsetRight | offsetLeft | offsetUp | offsetDown
    · simp [classifiedEdgeCore, offsetZero, Cell.add, Cell.scale]
      omega
    · simp [classifiedEdgeCore, offsetRight, Cell.add, Cell.scale]
      split <;> simp_all <;> omega
    · simp [classifiedEdgeCore, offsetLeft, Cell.add, Cell.scale]
      split <;> simp_all <;> omega
    · simp [classifiedEdgeCore, offsetUp, Cell.add, Cell.scale]
      omega
    · simp [classifiedEdgeCore, offsetDown, Cell.add, Cell.scale]
      omega
  have targetAll :
      ∀ item ∈ classifiedTargetFanout graph edge edgeIndex,
        item.role = .targetPortVertical port →
          item.segment.finish.2 =
              3 + drawingGridSize graph * edge.offset.2 ∧
            3 + drawingGridSize graph * edge.offset.2 <
              item.segment.start.2 ∧
            item.segment.start.2 <
              3 + drawingGridSize graph * edge.offset.2 +
                drawingGridSize graph := by
    simp [classifiedTargetFanout]
    split <;> simp_all
  simp only [classifiedRouteSegments, List.mem_append] at classifiedMem
  exact classifiedMem.elim
    (fun sourceOrCore => sourceOrCore.elim
      (fun sourceMem =>
        sourceAll classified sourceMem roleEq)
      (fun coreMem =>
        coreAll classified coreMem roleEq))
    (fun targetMem =>
      targetAll classified targetMem roleEq)

/-- A boundary role is the unit vertical step between an edge's private
low and high tracks. -/
theorem classifiedSegment_boundaryVertical_y
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {edge : PeriodicEdge Vertex} {edgeIndex roleEdgeIndex : Nat}
    {classified : ClassifiedSegment Vertex}
    (classifiedMem :
      classified ∈ classifiedRouteSegments graph edge edgeIndex)
    (roleEq :
      classified.role = .boundaryVertical roleEdgeIndex) :
    classified.segment.start.2 = edgeTrack roleEdgeIndex ∧
      classified.segment.finish.2 = edgeTrack roleEdgeIndex + 1 := by
  have sourceAll :
      ∀ item ∈ classifiedSourceFanout graph edge edgeIndex,
        item.role = .boundaryVertical roleEdgeIndex →
          item.segment.start.2 = edgeTrack roleEdgeIndex ∧
            item.segment.finish.2 = edgeTrack roleEdgeIndex + 1 := by
    simp [classifiedSourceFanout]
    split <;> simp_all
  have coreAll :
      ∀ item ∈ classifiedEdgeCore graph edge edgeIndex,
        item.role = .boundaryVertical roleEdgeIndex →
          item.segment.start.2 = edgeTrack roleEdgeIndex ∧
            item.segment.finish.2 = edgeTrack roleEdgeIndex + 1 := by
    simp [classifiedEdgeCore]
    split <;> simp_all
    all_goals split <;> simp_all
  have targetAll :
      ∀ item ∈ classifiedTargetFanout graph edge edgeIndex,
        item.role = .boundaryVertical roleEdgeIndex →
          item.segment.start.2 = edgeTrack roleEdgeIndex ∧
            item.segment.finish.2 = edgeTrack roleEdgeIndex + 1 := by
    simp [classifiedTargetFanout]
    split <;> simp_all
  simp only [classifiedRouteSegments, List.mem_append] at classifiedMem
  exact classifiedMem.elim
    (fun sourceOrCore => sourceOrCore.elim
      (fun sourceMem =>
        sourceAll classified sourceMem roleEq)
      (fun coreMem =>
        coreAll classified coreMem roleEq))
    (fun targetMem =>
      targetAll classified targetMem roleEq)

/-- Consecutive fanout and port columns share only their advertised
endpoint, even across different periodic copies. -/
theorem continuousVerticalAdjacent_no_openOverlap
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (isLocal : graph.IsLocal)
    {firstRoute secondRoute :
      (PeriodicEdge Vertex × Nat) × Nat}
    (firstRouteMem : firstRoute ∈ graph.edges.zipIdx.zipIdx)
    (secondRouteMem : secondRoute ∈ graph.edges.zipIdx.zipIdx)
    {firstClassified secondClassified :
      ClassifiedSegment Vertex × Nat}
    (firstClassifiedMem :
      firstClassified ∈
        (classifiedRouteSegments graph
          firstRoute.1.1 firstRoute.1.2).zipIdx)
    (secondClassifiedMem :
      secondClassified ∈
        (classifiedRouteSegments graph
          secondRoute.1.1 secondRoute.1.2).zipIdx)
    {firstShift secondShift : Int}
    (adjacent :
      firstClassified.1.role.ContinuousVerticalAdjacent
        secondClassified.1.role) :
    ¬GridSegment.OpenIntervalsOverlap
      (firstClassified.1.segment.start.2 +
        drawingGridSize graph * firstShift)
      (firstClassified.1.segment.finish.2 +
        drawingGridSize graph * firstShift)
      (secondClassified.1.segment.start.2 +
        drawingGridSize graph * secondShift)
      (secondClassified.1.segment.finish.2 +
        drawingGridSize graph * secondShift) := by
  have firstClassifiedMem' :=
    List.fst_mem_of_mem_zipIdx firstClassifiedMem
  have secondClassifiedMem' :=
    List.fst_mem_of_mem_zipIdx secondClassifiedMem
  have firstRoleIndex :=
    classifiedSegment_role_edgeIndex firstClassifiedMem'
  have secondRoleIndex :=
    classifiedSegment_role_edgeIndex secondClassifiedMem'
  have firstNested := nested_zipIdx_indices_eq firstRouteMem
  have secondNested := nested_zipIdx_indices_eq secondRouteMem
  have roleIndicesEqual :=
    SegmentRole.edgeIndex_eq_of_continuousVerticalAdjacent adjacent
  have routeIndicesEqual : firstRoute.2 = secondRoute.2 := by
    rw [← firstNested, ← secondNested]
    rw [← firstRoleIndex, ← secondRoleIndex]
    exact roleIndicesEqual
  have routesEqual :=
    tagged_eq_of_mem_zipIdx_of_snd_eq
      firstRouteMem secondRouteMem routeIndicesEqual
  subst secondRoute
  have edgeMem :
      (firstRoute.1.1, firstRoute.1.2) ∈ graph.edges.zipIdx :=
    List.fst_mem_of_mem_zipIdx firstRouteMem
  have edgeLocal :
      firstRoute.1.1.span ≤ 1 :=
    isLocal firstRoute.1.1
      (List.fst_mem_of_mem_zipIdx edgeMem)
  have periodPositive : (0 : Int) < drawingGridSize graph := by
    exact_mod_cast drawingGridSize_pos graph
  intro overlap
  rcases continuousVerticalAdjacent_cases adjacent with
    sourceForward | sourceBackward | targetForward | targetBackward
  · rcases sourceForward with ⟨port, firstRole, secondRole⟩
    have firstY :=
      classifiedSegment_sourceFanoutVertical_y
        firstClassifiedMem' firstRole
    have secondY :=
      classifiedSegment_sourcePortVertical_y_bounds
        edgeMem secondClassifiedMem' secondRole
    unfold GridSegment.OpenIntervalsOverlap at overlap
    simp [firstY.1, firstY.2, secondY.1,
      min_add_add_right, max_add_add_right,
      min_eq_left (show (2 : Int) ≤ 3 by omega),
      max_eq_right (show (2 : Int) ≤ 3 by omega),
      min_eq_left (le_of_lt secondY.2.1),
      max_eq_right (le_of_lt secondY.2.1)] at overlap
    have shifts : secondShift < firstShift :=
      (Int.mul_lt_mul_left periodPositive).mp overlap.2
    have step : secondShift + 1 ≤ firstShift := by omega
    have periodStep :
        drawingGridSize graph * (secondShift + 1) ≤
          drawingGridSize graph * firstShift :=
      Int.mul_le_mul_of_nonneg_left step (le_of_lt periodPositive)
    nlinarith [secondY.2.2, periodStep]
  · rcases sourceBackward with ⟨port, firstRole, secondRole⟩
    have firstY :=
      classifiedSegment_sourcePortVertical_y_bounds
        edgeMem firstClassifiedMem' firstRole
    have secondY :=
      classifiedSegment_sourceFanoutVertical_y
        secondClassifiedMem' secondRole
    unfold GridSegment.OpenIntervalsOverlap at overlap
    simp [firstY.1, secondY.1, secondY.2,
      min_add_add_right, max_add_add_right,
      min_eq_left (le_of_lt firstY.2.1),
      max_eq_right (le_of_lt firstY.2.1),
      min_eq_left (show (2 : Int) ≤ 3 by omega),
      max_eq_right (show (2 : Int) ≤ 3 by omega)] at overlap
    have shifts : firstShift < secondShift :=
      (Int.mul_lt_mul_left periodPositive).mp overlap.1
    have step : firstShift + 1 ≤ secondShift := by omega
    have periodStep :
        drawingGridSize graph * (firstShift + 1) ≤
          drawingGridSize graph * secondShift :=
      Int.mul_le_mul_of_nonneg_left step (le_of_lt periodPositive)
    nlinarith [firstY.2.2, periodStep]
  · rcases targetForward with ⟨port, firstRole, secondRole⟩
    have firstY :=
      classifiedSegment_targetPortVertical_y_bounds
        edgeMem edgeLocal firstClassifiedMem' firstRole
    have secondY :=
      classifiedSegment_targetFanoutVertical_y
        secondClassifiedMem' secondRole
    unfold GridSegment.OpenIntervalsOverlap at overlap
    simp [firstY.1, secondY.1, secondY.2,
      min_add_add_right, max_add_add_right,
      min_eq_right (le_of_lt firstY.2.1),
      max_eq_left (le_of_lt firstY.2.1)] at overlap
    have shifts : firstShift < secondShift :=
      (Int.mul_lt_mul_left periodPositive).mp overlap.1
    have step : firstShift + 1 ≤ secondShift := by omega
    have periodStep :
        drawingGridSize graph * (firstShift + 1) ≤
          drawingGridSize graph * secondShift :=
      Int.mul_le_mul_of_nonneg_left step (le_of_lt periodPositive)
    nlinarith [firstY.2.2, periodStep]
  · rcases targetBackward with ⟨port, firstRole, secondRole⟩
    have firstY :=
      classifiedSegment_targetFanoutVertical_y
        firstClassifiedMem' firstRole
    have secondY :=
      classifiedSegment_targetPortVertical_y_bounds
        edgeMem edgeLocal secondClassifiedMem' secondRole
    unfold GridSegment.OpenIntervalsOverlap at overlap
    simp [firstY.1, firstY.2, secondY.1,
      min_add_add_right, max_add_add_right,
      min_eq_right (le_of_lt secondY.2.1),
      max_eq_left (le_of_lt secondY.2.1)] at overlap
    have shifts : secondShift < firstShift :=
      (Int.mul_lt_mul_left periodPositive).mp overlap.2
    have step : secondShift + 1 ≤ firstShift := by omega
    have periodStep :
        drawingGridSize graph * (secondShift + 1) ≤
          drawingGridSize graph * firstShift :=
      Int.mul_le_mul_of_nonneg_left step (le_of_lt periodPositive)
    nlinarith [secondY.2.2, periodStep]

/-- Overlapping periodic copies of boundary steps have the same private
track, hence the same boundary role. -/
theorem boundaryVertical_roles_eq_of_openOverlap
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {firstRoute secondRoute :
      (PeriodicEdge Vertex × Nat) × Nat}
    (firstRouteMem : firstRoute ∈ graph.edges.zipIdx.zipIdx)
    (secondRouteMem : secondRoute ∈ graph.edges.zipIdx.zipIdx)
    {firstClassified secondClassified :
      ClassifiedSegment Vertex × Nat}
    (firstClassifiedMem :
      firstClassified ∈
        (classifiedRouteSegments graph
          firstRoute.1.1 firstRoute.1.2).zipIdx)
    (secondClassifiedMem :
      secondClassified ∈
        (classifiedRouteSegments graph
          secondRoute.1.1 secondRoute.1.2).zipIdx)
    {firstEdgeIndex secondEdgeIndex : Nat}
    (firstRole :
      firstClassified.1.role =
        .boundaryVertical firstEdgeIndex)
    (secondRole :
      secondClassified.1.role =
        .boundaryVertical secondEdgeIndex)
    {firstShift secondShift : Int}
    (overlap :
      GridSegment.OpenIntervalsOverlap
        (firstClassified.1.segment.start.2 +
          drawingGridSize graph * firstShift)
        (firstClassified.1.segment.finish.2 +
          drawingGridSize graph * firstShift)
        (secondClassified.1.segment.start.2 +
          drawingGridSize graph * secondShift)
        (secondClassified.1.segment.finish.2 +
          drawingGridSize graph * secondShift)) :
    firstClassified.1.role = secondClassified.1.role := by
  have firstClassifiedMem' :=
    List.fst_mem_of_mem_zipIdx firstClassifiedMem
  have secondClassifiedMem' :=
    List.fst_mem_of_mem_zipIdx secondClassifiedMem
  have firstRoleIndex :=
    classifiedSegment_role_edgeIndex firstClassifiedMem'
  have secondRoleIndex :=
    classifiedSegment_role_edgeIndex secondClassifiedMem'
  have firstIndexEq : firstEdgeIndex = firstRoute.1.2 := by
    simpa [firstRole, SegmentRole.edgeIndex] using firstRoleIndex
  have secondIndexEq : secondEdgeIndex = secondRoute.1.2 := by
    simpa [secondRole, SegmentRole.edgeIndex] using secondRoleIndex
  have firstY :=
    classifiedSegment_boundaryVertical_y
      firstClassifiedMem' firstRole
  have secondY :=
    classifiedSegment_boundaryVertical_y
      secondClassifiedMem' secondRole
  have translatedTracksEqual :
      edgeTrack firstEdgeIndex +
          drawingGridSize graph * firstShift =
        edgeTrack secondEdgeIndex +
          drawingGridSize graph * secondShift := by
    unfold GridSegment.OpenIntervalsOverlap at overlap
    simp [firstY.1, firstY.2, secondY.1, secondY.2,
      min_add_add_right, max_add_add_right,
      min_eq_left (show edgeTrack firstEdgeIndex ≤
        edgeTrack firstEdgeIndex + 1 by omega),
      max_eq_right (show edgeTrack firstEdgeIndex ≤
        edgeTrack firstEdgeIndex + 1 by omega),
      min_eq_left (show edgeTrack secondEdgeIndex ≤
        edgeTrack secondEdgeIndex + 1 by omega),
      max_eq_right (show edgeTrack secondEdgeIndex ≤
        edgeTrack secondEdgeIndex + 1 by omega)] at overlap
    omega
  have firstEdgeMem :
      (firstRoute.1.1, firstRoute.1.2) ∈ graph.edges.zipIdx :=
    List.fst_mem_of_mem_zipIdx firstRouteMem
  have secondEdgeMem :
      (secondRoute.1.1, secondRoute.1.2) ∈ graph.edges.zipIdx :=
    List.fst_mem_of_mem_zipIdx secondRouteMem
  have firstTrackBoundsRaw := edgeTrack_bounds graph firstEdgeMem
  have secondTrackBoundsRaw := edgeTrack_bounds graph secondEdgeMem
  simp at firstTrackBoundsRaw secondTrackBoundsRaw
  have firstTrackBounds :
      0 ≤ edgeTrack firstEdgeIndex ∧
        edgeTrack firstEdgeIndex < drawingGridSize graph := by
    rw [firstIndexEq]
    omega
  have secondTrackBounds :
      0 ≤ edgeTrack secondEdgeIndex ∧
        edgeTrack secondEdgeIndex < drawingGridSize graph := by
    rw [secondIndexEq]
    omega
  have periodPositive : (0 : Int) < drawingGridSize graph := by
    exact_mod_cast drawingGridSize_pos graph
  have normalized :=
    periodic_coordinate_unique periodPositive
      firstTrackBounds secondTrackBounds translatedTracksEqual
  have indicesEqual : firstEdgeIndex = secondEdgeIndex := by
    simp [edgeTrack] at normalized
    omega
  simpa [firstRole, secondRole, indicesEqual]

/-- Once normalized continuous lanes identify the same semantic role,
continuous vertical overlap determines the route, segment, and cell
translation. -/
theorem continuousVertical_classified_occurrences_unique_of_roles_eq
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (isLocal : graph.IsLocal)
    {firstRoute secondRoute :
      (PeriodicEdge Vertex × Nat) × Nat}
    (firstRouteMem : firstRoute ∈ graph.edges.zipIdx.zipIdx)
    (secondRouteMem : secondRoute ∈ graph.edges.zipIdx.zipIdx)
    {firstClassified secondClassified :
      ClassifiedSegment Vertex × Nat}
    (firstClassifiedMem :
      firstClassified ∈
        (classifiedRouteSegments graph
          firstRoute.1.1 firstRoute.1.2).zipIdx)
    (secondClassifiedMem :
      secondClassified ∈
        (classifiedRouteSegments graph
          secondRoute.1.1 secondRoute.1.2).zipIdx)
    {firstTranslate secondTranslate : Cell}
    (firstVertical :
      (firstClassified.1.segment.translate
        ((drawing graph).periodTranslation firstTranslate)).IsVertical)
    (secondVertical :
      (secondClassified.1.segment.translate
        ((drawing graph).periodTranslation secondTranslate)).IsVertical)
    (meet :
      GridSegment.InteriorsMeet
        (firstClassified.1.segment.translate
          ((drawing graph).periodTranslation firstTranslate))
        (secondClassified.1.segment.translate
          ((drawing graph).periodTranslation secondTranslate)))
    (rolesEqual :
      firstClassified.1.role = secondClassified.1.role) :
    PeriodicGridDrawing.SegmentOccurrenceKey
        ⟨firstRoute.2, firstClassified.2,
          firstClassified.1.segment⟩ firstTranslate =
      PeriodicGridDrawing.SegmentOccurrenceKey
        ⟨secondRoute.2, secondClassified.2,
          secondClassified.1.segment⟩ secondTranslate := by
  have firstClassifiedMem' :=
    List.fst_mem_of_mem_zipIdx firstClassifiedMem
  have secondClassifiedMem' :=
    List.fst_mem_of_mem_zipIdx secondClassifiedMem
  have firstRoleIndex :=
    classifiedSegment_role_edgeIndex firstClassifiedMem'
  have secondRoleIndex :=
    classifiedSegment_role_edgeIndex secondClassifiedMem'
  have firstNested := nested_zipIdx_indices_eq firstRouteMem
  have secondNested := nested_zipIdx_indices_eq secondRouteMem
  have routeIndicesEqual : firstRoute.2 = secondRoute.2 := by
    rw [← firstNested, ← secondNested]
    rw [← firstRoleIndex, ← secondRoleIndex]
    exact congrArg SegmentRole.edgeIndex rolesEqual
  have routesEqual :=
    tagged_eq_of_mem_zipIdx_of_snd_eq
      firstRouteMem secondRouteMem routeIndicesEqual
  subst secondRoute
  have classifiedEqual :=
    taggedClassified_eq_of_role_eq
      firstClassifiedMem secondClassifiedMem rolesEqual
  subst secondClassified
  have verticalMeet :
      (firstClassified.1.segment.translate
          ((drawing graph).periodTranslation firstTranslate)).IsVertical ∧
        (firstClassified.1.segment.translate
          ((drawing graph).periodTranslation secondTranslate)).IsVertical ∧
        (firstClassified.1.segment.translate
          ((drawing graph).periodTranslation firstTranslate)).start.1 =
          (firstClassified.1.segment.translate
            ((drawing graph).periodTranslation secondTranslate)).start.1 ∧
        GridSegment.OpenIntervalsOverlap
          (firstClassified.1.segment.translate
            ((drawing graph).periodTranslation firstTranslate)).start.2
          (firstClassified.1.segment.translate
            ((drawing graph).periodTranslation firstTranslate)).finish.2
          (firstClassified.1.segment.translate
            ((drawing graph).periodTranslation secondTranslate)).start.2
          (firstClassified.1.segment.translate
            ((drawing graph).periodTranslation secondTranslate)).finish.2 := by
    rcases meet with
      horizontal | vertical | horizontalVertical | verticalHorizontal
    · exact False.elim (firstVertical.2 horizontal.1.1)
    · exact vertical
    · exact False.elim
        (firstVertical.2 horizontalVertical.1.1)
    · exact False.elim
        (secondVertical.2 verticalHorizontal.2.1.1)
  have periodPositive : (0 : Int) < drawingGridSize graph := by
    exact_mod_cast drawingGridSize_pos graph
  have translatedColumnsEqual :
      firstClassified.1.segment.start.1 +
          drawingGridSize graph * firstTranslate.1 =
        firstClassified.1.segment.start.1 +
          drawingGridSize graph * secondTranslate.1 := by
    simpa [GridSegment.translate,
      PeriodicGridDrawing.periodTranslation, drawing_gridSize,
      Cell.add, Cell.scale, add_comm] using verticalMeet.2.2.1
  have translateXEqual :
      firstTranslate.1 = secondTranslate.1 := by
    have multiplied :
        (drawingGridSize graph : Int) * firstTranslate.1 =
          drawingGridSize graph * secondTranslate.1 :=
      Int.add_left_cancel translatedColumnsEqual
    exact mul_left_cancel₀
      (ne_of_gt periodPositive) multiplied
  have storedVertical :
      firstClassified.1.segment.IsVertical :=
    (GridSegment.isVertical_translate _ _).mp firstVertical
  have edgeMem :
      (firstRoute.1.1, firstRoute.1.2) ∈ graph.edges.zipIdx :=
    List.fst_mem_of_mem_zipIdx firstRouteMem
  have edgeLocal :
      firstRoute.1.1.span ≤ 1 :=
    isLocal firstRoute.1.1
      (List.fst_mem_of_mem_zipIdx edgeMem)
  have span :=
    classifiedSegment_vertical_span_le_period
      edgeMem edgeLocal firstClassifiedMem' storedVertical
  have overlap :
      GridSegment.OpenIntervalsOverlap
        (firstClassified.1.segment.start.2 +
          drawingGridSize graph * firstTranslate.2)
        (firstClassified.1.segment.finish.2 +
          drawingGridSize graph * firstTranslate.2)
        (firstClassified.1.segment.start.2 +
          drawingGridSize graph * secondTranslate.2)
        (firstClassified.1.segment.finish.2 +
          drawingGridSize graph * secondTranslate.2) := by
    simpa [GridSegment.translate,
      PeriodicGridDrawing.periodTranslation, drawing_gridSize,
      Cell.add, Cell.scale, add_comm] using verticalMeet.2.2.2
  have translateYEqual :=
    openIntervalsOverlap_periodic_shifts_unique
      periodPositive span.1 span.2 overlap
  have translatesEqual : firstTranslate = secondTranslate := by
    apply Prod.ext
    · exact translateXEqual
    · exact translateYEqual
  subst secondTranslate
  rfl

/-- Continuous overlap of two vertical constructed occurrences determines
the same indexed occurrence key. -/
theorem drawing_hasUniqueVerticalContinuousInteriors
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal) :
    ∀ first ∈ (drawing graph).indexedSegments,
      ∀ second ∈ (drawing graph).indexedSegments,
        ∀ firstTranslate secondTranslate,
          (first.segment.translate
            ((drawing graph).periodTranslation firstTranslate)).IsVertical →
          (second.segment.translate
            ((drawing graph).periodTranslation secondTranslate)).IsVertical →
          GridSegment.InteriorsMeet
              (first.segment.translate
                ((drawing graph).periodTranslation firstTranslate))
              (second.segment.translate
                ((drawing graph).periodTranslation secondTranslate)) →
          PeriodicGridDrawing.SegmentOccurrenceKey first firstTranslate =
            PeriodicGridDrawing.SegmentOccurrenceKey
              second secondTranslate := by
  intro first firstMem second secondMem
    firstTranslate secondTranslate firstVertical secondVertical meet
  rcases exists_classifiedSegment_of_drawing_mem firstMem with
    ⟨firstRoute, firstRouteMem,
      firstClassified, firstClassifiedMem, firstEq⟩
  rcases exists_classifiedSegment_of_drawing_mem secondMem with
    ⟨secondRoute, secondRouteMem,
      secondClassified, secondClassifiedMem, secondEq⟩
  subst first
  subst second
  have firstEdgeMem :
      (firstRoute.1.1, firstRoute.1.2) ∈ graph.edges.zipIdx :=
    List.fst_mem_of_mem_zipIdx firstRouteMem
  have secondEdgeMem :
      (secondRoute.1.1, secondRoute.1.2) ∈ graph.edges.zipIdx :=
    List.fst_mem_of_mem_zipIdx secondRouteMem
  have firstClassifiedMem' :=
    List.fst_mem_of_mem_zipIdx firstClassifiedMem
  have secondClassifiedMem' :=
    List.fst_mem_of_mem_zipIdx secondClassifiedMem
  have firstStoredVertical :
      firstClassified.1.segment.IsVertical :=
    (GridSegment.isVertical_translate _ _).mp firstVertical
  have secondStoredVertical :
      secondClassified.1.segment.IsVertical :=
    (GridSegment.isVertical_translate _ _).mp secondVertical
  have firstRoleVertical :=
    classifiedSegment_continuousVerticalRole_of_isVertical
      firstClassifiedMem' firstStoredVertical
  have secondRoleVertical :=
    classifiedSegment_continuousVerticalRole_of_isVertical
      secondClassifiedMem' secondStoredVertical
  have firstEnd :=
    classifiedSegment_continuousVerticalEndCorrect
      firstClassifiedMem'
  have secondEnd :=
    classifiedSegment_continuousVerticalEndCorrect
      secondClassifiedMem'
  have verticalMeet :
      (firstClassified.1.segment.translate
          ((drawing graph).periodTranslation firstTranslate)).IsVertical ∧
        (secondClassified.1.segment.translate
          ((drawing graph).periodTranslation secondTranslate)).IsVertical ∧
        (firstClassified.1.segment.translate
          ((drawing graph).periodTranslation firstTranslate)).start.1 =
          (secondClassified.1.segment.translate
            ((drawing graph).periodTranslation secondTranslate)).start.1 ∧
        GridSegment.OpenIntervalsOverlap
          (firstClassified.1.segment.translate
            ((drawing graph).periodTranslation firstTranslate)).start.2
          (firstClassified.1.segment.translate
            ((drawing graph).periodTranslation firstTranslate)).finish.2
          (secondClassified.1.segment.translate
            ((drawing graph).periodTranslation secondTranslate)).start.2
          (secondClassified.1.segment.translate
            ((drawing graph).periodTranslation secondTranslate)).finish.2 := by
    rcases meet with
      horizontal | vertical | horizontalVertical | verticalHorizontal
    · exact False.elim (firstVertical.2 horizontal.1.1)
    · exact vertical
    · exact False.elim
        (firstVertical.2 horizontalVertical.1.1)
    · exact False.elim
        (secondVertical.2 verticalHorizontal.2.1.1)
  have firstLane :=
    classifiedSegment_continuousVertical_lane
      firstClassifiedMem' firstRoleVertical
  have secondLane :=
    classifiedSegment_continuousVertical_lane
      secondClassifiedMem' secondRoleVertical
  have translatedColumnsEqual :
      firstClassified.1.segment.start.1 +
          drawingGridSize graph * firstTranslate.1 =
        secondClassified.1.segment.start.1 +
          drawingGridSize graph * secondTranslate.1 := by
    simpa [GridSegment.translate,
      PeriodicGridDrawing.periodTranslation, drawing_gridSize,
      Cell.add, Cell.scale, add_comm] using verticalMeet.2.2.1
  have normalizedLanesEqual :
      continuousVerticalLaneBase graph firstClassified.1.role +
          drawingGridSize graph *
            (continuousVerticalLaneCellShift
              firstRoute.1.1 firstClassified.1.role +
              firstTranslate.1) =
        continuousVerticalLaneBase graph secondClassified.1.role +
          drawingGridSize graph *
            (continuousVerticalLaneCellShift
              secondRoute.1.1 secondClassified.1.role +
              secondTranslate.1) := by
    calc
      _ = firstClassified.1.segment.start.1 +
          drawingGridSize graph * firstTranslate.1 := by
            rw [firstLane]
            ring
      _ = secondClassified.1.segment.start.1 +
          drawingGridSize graph * secondTranslate.1 :=
            translatedColumnsEqual
      _ = _ := by
        rw [secondLane]
        ring
  have periodPositive : (0 : Int) < drawingGridSize graph := by
    exact_mod_cast drawingGridSize_pos graph
  have firstLaneBounds :=
    continuousVerticalLaneBase_bounds
      wellFormed degree firstEdgeMem
      firstClassifiedMem' firstRoleVertical
  have secondLaneBounds :=
    continuousVerticalLaneBase_bounds
      wellFormed degree secondEdgeMem
      secondClassifiedMem' secondRoleVertical
  have normalizedLaneData :=
    periodic_coordinate_unique
      periodPositive firstLaneBounds secondLaneBounds
      normalizedLanesEqual
  rcases exists_continuousVerticalLaneOwner firstRoleVertical with
    ⟨firstOwner, firstOwnerEq⟩
  rcases exists_continuousVerticalLaneOwner secondRoleVertical with
    ⟨secondOwner, secondOwnerEq⟩
  have firstBaseEq :=
    continuousVerticalLaneBase_eq_ownerX
      graph firstOwnerEq
  have secondBaseEq :=
    continuousVerticalLaneBase_eq_ownerX
      graph secondOwnerEq
  have ownerCoordinatesEqual :
      continuousVerticalLaneOwnerX graph firstOwner =
        continuousVerticalLaneOwnerX graph secondOwner := by
    rw [← firstBaseEq, ← secondBaseEq]
    exact normalizedLaneData.1
  have ownersEqual : firstOwner = secondOwner :=
    continuousVerticalLaneOwnerX_injective
      wellFormed degree
      (fun port equality =>
        classifiedSegment_continuousVerticalPort_mem
          firstEdgeMem firstClassifiedMem'
          (continuousVerticalPort_eq_of_laneOwner_eq_inl
            (by simpa [equality] using firstOwnerEq) rfl))
      (fun port equality =>
        classifiedSegment_continuousVerticalPort_mem
          secondEdgeMem secondClassifiedMem'
          (continuousVerticalPort_eq_of_laneOwner_eq_inl
            (by simpa [equality] using secondOwnerEq) rfl))
      ownerCoordinatesEqual
  have roleOwnersEqual :
      firstClassified.1.role.continuousVerticalLaneOwner =
        secondClassified.1.role.continuousVerticalLaneOwner := by
    calc
      _ = some firstOwner := firstOwnerEq
      _ = some secondOwner := congrArg some ownersEqual
      _ = _ := secondOwnerEq.symm
  have roleCases :=
    continuousVertical_roles_eq_or_adjacent_or_boundaries
      firstRoleVertical secondRoleVertical
      firstEnd secondEnd roleOwnersEqual
  have openOverlap :
      GridSegment.OpenIntervalsOverlap
        (firstClassified.1.segment.start.2 +
          drawingGridSize graph * firstTranslate.2)
        (firstClassified.1.segment.finish.2 +
          drawingGridSize graph * firstTranslate.2)
        (secondClassified.1.segment.start.2 +
          drawingGridSize graph * secondTranslate.2)
        (secondClassified.1.segment.finish.2 +
          drawingGridSize graph * secondTranslate.2) := by
    simpa [GridSegment.translate,
      PeriodicGridDrawing.periodTranslation, drawing_gridSize,
      Cell.add, Cell.scale, add_comm] using verticalMeet.2.2.2
  rcases roleCases with rolesEqual | adjacent | boundaries
  · exact continuousVertical_classified_occurrences_unique_of_roles_eq
      isLocal firstRouteMem secondRouteMem
      firstClassifiedMem secondClassifiedMem
      firstVertical secondVertical meet rolesEqual
  · exact False.elim
      (continuousVerticalAdjacent_no_openOverlap
        isLocal firstRouteMem secondRouteMem
        firstClassifiedMem secondClassifiedMem adjacent
        openOverlap)
  · rcases boundaries with
      ⟨firstEdgeIndex, secondEdgeIndex, firstRole, secondRole⟩
    have rolesEqual :=
      boundaryVertical_roles_eq_of_openOverlap
        firstRouteMem secondRouteMem
        firstClassifiedMem secondClassifiedMem
        firstRole secondRole openOverlap
    exact continuousVertical_classified_occurrences_unique_of_roles_eq
      isLocal firstRouteMem secondRouteMem
      firstClassifiedMem secondClassifiedMem
      firstVertical secondVertical meet rolesEqual

/-- Distinct vertical segment occurrences in the constructed drawing have
disjoint continuous relative interiors. -/
theorem drawing_verticalContinuousInteriors_disjoint
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {first second : IndexedGridSegment}
    (firstMem : first ∈ (drawing graph).indexedSegments)
    (secondMem : second ∈ (drawing graph).indexedSegments)
    {firstTranslate secondTranslate : Cell}
    (firstVertical :
      (first.segment.translate
        ((drawing graph).periodTranslation firstTranslate)).IsVertical)
    (secondVertical :
      (second.segment.translate
        ((drawing graph).periodTranslation secondTranslate)).IsVertical)
    (different :
      PeriodicGridDrawing.SegmentOccurrenceKey first firstTranslate ≠
        PeriodicGridDrawing.SegmentOccurrenceKey second secondTranslate) :
    ¬GridSegment.InteriorsMeet
      (first.segment.translate
        ((drawing graph).periodTranslation firstTranslate))
      (second.segment.translate
        ((drawing graph).periodTranslation secondTranslate)) := by
  intro meet
  exact different
    (drawing_hasUniqueVerticalContinuousInteriors
      wellFormed degree isLocal
      first firstMem second secondMem
      firstTranslate secondTranslate
      firstVertical secondVertical meet)

/-- Both horizontal coordinates of every translated constructed horizontal
segment are even. -/
theorem classifiedSegment_horizontal_translated_endpoints_even
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {edge : PeriodicEdge Vertex} {edgeIndex : Nat}
    {classified : ClassifiedSegment Vertex}
    (classifiedMem :
      classified ∈ classifiedRouteSegments graph edge edgeIndex)
    (horizontal : classified.segment.IsHorizontal)
    (translate : Cell) :
    Even
        ((classified.segment.translate
          ((drawing graph).periodTranslation translate)).start.1) ∧
      Even
        ((classified.segment.translate
          ((drawing graph).periodTranslation translate)).finish.1) := by
  have sourceAll :
      ∀ item ∈ classifiedSourceFanout graph edge edgeIndex,
        item.segment.IsHorizontal →
          Even
              ((item.segment.translate
                ((drawing graph).periodTranslation translate)).start.1) ∧
            Even
              ((item.segment.translate
                ((drawing graph).periodTranslation translate)).finish.1) := by
    intro item itemMem itemHorizontal
    by_cases same :
        vertexX (graph.vertices.idxOf edge.source) =
          portX graph (sourcePort edge edgeIndex)
    · simp [classifiedSourceFanout, same] at itemMem
      subst item
      simp [GridSegment.IsHorizontal] at itemHorizontal
    · simp [classifiedSourceFanout, same] at itemMem
      rcases itemMem with rfl | rfl
      · norm_num [GridSegment.translate,
          PeriodicGridDrawing.periodTranslation, drawing_gridSize,
          Cell.add, Cell.scale, drawingGridSize, vertexX, portX,
          parity_simps]
      · simp [GridSegment.IsHorizontal] at itemHorizontal
  have coreAll :
      ∀ item ∈ classifiedEdgeCore graph edge edgeIndex,
        item.segment.IsHorizontal →
          Even
              ((item.segment.translate
                ((drawing graph).periodTranslation translate)).start.1) ∧
            Even
              ((item.segment.translate
                ((drawing graph).periodTranslation translate)).finish.1) := by
    intro item itemMem itemHorizontal
    simp [classifiedEdgeCore] at itemMem
    all_goals try split at itemMem
    all_goals try split at itemMem
    all_goals try simp only [List.mem_cons] at itemMem
    all_goals try rcases itemMem with rfl | itemMem
    all_goals try rcases itemMem with rfl | itemMem
    all_goals try rcases itemMem with rfl | itemMem
    all_goals try rcases itemMem with rfl | itemMem
    all_goals try rcases itemMem with rfl | itemMem
    all_goals try simp at itemMem
    all_goals norm_num [GridSegment.translate,
      PeriodicGridDrawing.periodTranslation, drawing_gridSize,
      Cell.add, Cell.scale, drawingGridSize, vertexX, portX,
      edgeGateX, parity_simps]
  have targetAll :
      ∀ item ∈ classifiedTargetFanout graph edge edgeIndex,
        item.segment.IsHorizontal →
          Even
              ((item.segment.translate
                ((drawing graph).periodTranslation translate)).start.1) ∧
            Even
              ((item.segment.translate
                ((drawing graph).periodTranslation translate)).finish.1) := by
    intro item itemMem itemHorizontal
    have itemFullMem :
        item ∈ classifiedRouteSegments graph edge edgeIndex := by
      simp [classifiedRouteSegments, itemMem]
    by_cases same :
        vertexX (graph.vertices.idxOf edge.target) =
          portX graph (targetPort edge edgeIndex)
    · simp [classifiedTargetFanout, same] at itemMem
      subst item
      simp [GridSegment.IsHorizontal, Cell.add, Cell.scale]
        at itemHorizontal
    · simp [classifiedTargetFanout, same] at itemMem
      rcases itemMem with rfl | rfl
      · simp [GridSegment.IsHorizontal, Cell.add, Cell.scale]
          at itemHorizontal
      · exact horizontalFanout_translated_endpoints_even
          itemFullMem (by
            simp [SegmentRole.IsHorizontalFanout]) translate
  simp only [classifiedRouteSegments, List.mem_append] at classifiedMem
  exact classifiedMem.elim
    (fun sourceOrCore => sourceOrCore.elim
      (fun sourceMem =>
        sourceAll classified sourceMem horizontal)
      (fun coreMem =>
        coreAll classified coreMem horizontal))
    (fun targetMem =>
      targetAll classified targetMem horizontal)

/-- Both horizontal coordinates of a translated drawing-segment occurrence
are even. -/
theorem drawing_horizontal_translated_endpoints_even
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {indexed : IndexedGridSegment}
    (indexedMem : indexed ∈ (drawing graph).indexedSegments)
    (translate : Cell)
    (horizontal :
      (indexed.segment.translate
        ((drawing graph).periodTranslation translate)).IsHorizontal)
    :
    Even
        ((indexed.segment.translate
          ((drawing graph).periodTranslation translate)).start.1) ∧
      Even
        ((indexed.segment.translate
          ((drawing graph).periodTranslation translate)).finish.1) := by
  rcases exists_classifiedSegment_of_drawing_mem indexedMem with
    ⟨route, routeMem, classified, classifiedMem, indexedEq⟩
  subst indexed
  have storedHorizontal :
      classified.1.segment.IsHorizontal :=
    (GridSegment.isHorizontal_translate _ _).mp horizontal
  exact classifiedSegment_horizontal_translated_endpoints_even
    (List.fst_mem_of_mem_zipIdx classifiedMem)
    storedHorizontal translate

/-- Continuous overlap of two horizontal constructed occurrences contains
an integer grid point, so the existing private-lane certificate identifies
their occurrence keys. -/
theorem drawing_hasUniqueHorizontalContinuousInteriors
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal) :
    ∀ first ∈ (drawing graph).indexedSegments,
      ∀ second ∈ (drawing graph).indexedSegments,
        ∀ firstTranslate secondTranslate,
          (first.segment.translate
            ((drawing graph).periodTranslation firstTranslate)).IsHorizontal →
          (second.segment.translate
            ((drawing graph).periodTranslation secondTranslate)).IsHorizontal →
          GridSegment.InteriorsMeet
              (first.segment.translate
                ((drawing graph).periodTranslation firstTranslate))
              (second.segment.translate
                ((drawing graph).periodTranslation secondTranslate)) →
          PeriodicGridDrawing.SegmentOccurrenceKey first firstTranslate =
            PeriodicGridDrawing.SegmentOccurrenceKey
              second secondTranslate := by
  intro first firstMem second secondMem
    firstTranslate secondTranslate firstHorizontal secondHorizontal meet
  let firstSegment :=
    first.segment.translate
      ((drawing graph).periodTranslation firstTranslate)
  let secondSegment :=
    second.segment.translate
      ((drawing graph).periodTranslation secondTranslate)
  have firstEven :=
    drawing_horizontal_translated_endpoints_even
      firstMem firstTranslate firstHorizontal
  have secondEven :=
    drawing_horizontal_translated_endpoints_even
      secondMem secondTranslate secondHorizontal
  have horizontalMeet :
      firstSegment.IsHorizontal ∧ secondSegment.IsHorizontal ∧
        firstSegment.start.2 = secondSegment.start.2 ∧
        GridSegment.OpenIntervalsOverlap
          firstSegment.start.1 firstSegment.finish.1
          secondSegment.start.1 secondSegment.finish.1 := by
    rcases meet with
      horizontal | vertical | horizontalVertical | verticalHorizontal
    · exact horizontal
    · exact False.elim (firstHorizontal.2 vertical.1.1)
    · exact False.elim (secondHorizontal.2 horizontalVertical.2.1.1)
    · exact False.elim (firstHorizontal.2 verticalHorizontal.1.1)
  rcases
      exists_common_strictlyBetween_of_openIntervalsOverlap_of_even_endpoints
        firstHorizontal.2 secondHorizontal.2
        firstEven.1 firstEven.2 secondEven.1 secondEven.2
        horizontalMeet.2.2.2 with
    ⟨pointX, firstBetween, secondBetween⟩
  let point : Cell := (pointX, firstSegment.start.2)
  have firstContains : firstSegment.InteriorContains point := by
    exact Or.inl
      ⟨firstHorizontal, rfl, firstBetween⟩
  have secondContains : secondSegment.InteriorContains point := by
    apply Or.inl
    refine ⟨secondHorizontal, ?_, secondBetween⟩
    simpa [point] using horizontalMeet.2.2.1
  exact drawing_hasUniqueHorizontalInteriors
    wellFormed degree isLocal
    first firstMem second secondMem
    firstTranslate secondTranslate point
    firstContains secondContains firstHorizontal secondHorizontal

/-- Distinct horizontal segment occurrences in the constructed drawing have
disjoint continuous relative interiors. -/
theorem drawing_horizontalContinuousInteriors_disjoint
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {first second : IndexedGridSegment}
    (firstMem : first ∈ (drawing graph).indexedSegments)
    (secondMem : second ∈ (drawing graph).indexedSegments)
    {firstTranslate secondTranslate : Cell}
    (firstHorizontal :
      (first.segment.translate
        ((drawing graph).periodTranslation firstTranslate)).IsHorizontal)
    (secondHorizontal :
      (second.segment.translate
        ((drawing graph).periodTranslation secondTranslate)).IsHorizontal)
    (different :
      PeriodicGridDrawing.SegmentOccurrenceKey first firstTranslate ≠
        PeriodicGridDrawing.SegmentOccurrenceKey second secondTranslate) :
    ¬GridSegment.InteriorsMeet
      (first.segment.translate
        ((drawing graph).periodTranslation firstTranslate))
      (second.segment.translate
        ((drawing graph).periodTranslation secondTranslate)) := by
  intro meet
  exact different
    (drawing_hasUniqueHorizontalContinuousInteriors
      wellFormed degree isLocal
      first firstMem second secondMem
      firstTranslate secondTranslate
      firstHorizontal secondHorizontal meet)

end PeriodicOrthocrossing
end LeanTrominoes
