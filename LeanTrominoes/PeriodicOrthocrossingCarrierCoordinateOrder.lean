import LeanTrominoes.PeriodicOrthocrossingCarrierLensGeometry
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizationDegree

/-!
# Strict coordinate order on complete carriers

The complete carrier chains are sorted by their physical axis coordinate.
This module proves that two listed nodes on one occurrence cannot tie in
that coordinate, and upgrades the sorted chains to strict pairwise order.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Two listed carrier nodes on one segment occurrence with the same axis
coordinate are the same node. -/
theorem carrierNode_eq_of_commonCarrier_orderCoordinate_eq
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {first second : CarrierNode}
    (firstMem : first ∈ drawingCarrierNodes graph)
    (secondMem : second ∈ drawingCarrierNodes graph)
    (keyEqual : first.carrierKey = second.carrierKey)
    (coordinateEqual :
      first.orderCoordinate graph =
        second.orderCoordinate graph) :
    first = second := by
  cases first with
  | terminal firstTerminal =>
      have firstTerminalMem :
          firstTerminal ∈ drawingSegmentTerminals graph := by
        unfold drawingCarrierNodes at firstMem
        simpa using firstMem
      have firstAligned :
          firstTerminal.indexed.segment.IsAxisAligned :=
        drawing_isOrthogonal wellFormed isLocal degree
          firstTerminal.indexed
          (drawingSegmentTerminal_indexed_mem
            graph firstTerminalMem).1
      cases second with
      | terminal secondTerminal =>
          have secondTerminalMem :
              secondTerminal ∈ drawingSegmentTerminals graph := by
            unfold drawingCarrierNodes at secondMem
            simpa using secondMem
          by_contra different
          have extreme :=
            terminal_terminal_orderCoordinate_extreme
              graph firstTerminalMem secondTerminalMem
              keyEqual.symm (Ne.symm different) firstAligned
          by_cases lower : firstTerminal.IsLower
          · rw [if_pos lower] at extreme
            omega
          · rw [if_neg lower] at extreme
            omega
      | boundary secondBoundary =>
          have secondBoundaryMem :
              secondBoundary ∈ drawingCrossingBoundaries graph := by
            unfold drawingCarrierNodes at secondMem
            simpa using secondMem
          have extreme :=
            terminal_boundary_orderCoordinate_extreme
              graph firstTerminalMem secondBoundaryMem
              keyEqual.symm firstAligned
          by_cases lower : firstTerminal.IsLower
          · rw [if_pos lower] at extreme
            omega
          · rw [if_neg lower] at extreme
            omega
  | boundary firstBoundary =>
      have firstBoundaryMem :
          firstBoundary ∈ drawingCrossingBoundaries graph := by
        unfold drawingCarrierNodes at firstMem
        simpa using firstMem
      cases second with
      | terminal secondTerminal =>
          have secondTerminalMem :
              secondTerminal ∈ drawingSegmentTerminals graph := by
            unfold drawingCarrierNodes at secondMem
            simpa using secondMem
          have secondAligned :
              secondTerminal.indexed.segment.IsAxisAligned :=
            drawing_isOrthogonal wellFormed isLocal degree
              secondTerminal.indexed
              (drawingSegmentTerminal_indexed_mem
                graph secondTerminalMem).1
          have extreme :=
            terminal_boundary_orderCoordinate_extreme
              graph secondTerminalMem firstBoundaryMem
              keyEqual secondAligned
          by_cases lower : secondTerminal.IsLower
          · rw [if_pos lower] at extreme
            omega
          · rw [if_neg lower] at extreme
            omega
      | boundary secondBoundary =>
          have secondBoundaryMem :
              secondBoundary ∈ drawingCrossingBoundaries graph := by
            unfold drawingCarrierNodes at secondMem
            simpa using secondMem
          by_cases crossingEqual :
              firstBoundary.crossing = secondBoundary.crossing
          · rcases firstBoundary with
              ⟨crossing, firstSide⟩
            rcases secondBoundary with
              ⟨secondCrossing, secondSide⟩
            simp only at crossingEqual
            subst secondCrossing
            have crossingMem :=
              drawingCrossingBoundary_crossing_mem
                graph firstBoundaryMem
            have different :=
              (orientedCrossings_sound
                graph crossingMem).2.2.2.2.1.2.1
            cases firstSide <;> cases secondSide
            · rfl
            · simp [CarrierNode.orderCoordinate,
                CarrierNode.isHorizontal, CarrierNode.position,
                CrossingBoundary.position, crossingMacroOrigin,
                CrossingSide.localPosition,
                CrossoverVariable.position, Cell.add, Cell.scale,
                planarMacroScale] at coordinateEqual
            · exact (different keyEqual).elim
            · exact (different keyEqual).elim
            · simp [CarrierNode.orderCoordinate,
                CarrierNode.isHorizontal, CarrierNode.position,
                CrossingBoundary.position, crossingMacroOrigin,
                CrossingSide.localPosition,
                CrossoverVariable.position, Cell.add, Cell.scale,
                planarMacroScale] at coordinateEqual
            · rfl
            · exact (different keyEqual).elim
            · exact (different keyEqual).elim
            · exact (different keyEqual.symm).elim
            · exact (different keyEqual.symm).elim
            · rfl
            · simp [CarrierNode.orderCoordinate,
                CarrierNode.isHorizontal, CarrierNode.position,
                CrossingBoundary.position, crossingMacroOrigin,
                CrossingSide.localPosition,
                CrossoverVariable.position, Cell.add, Cell.scale,
                planarMacroScale] at coordinateEqual
            · exact (different keyEqual.symm).elim
            · exact (different keyEqual.symm).elim
            · simp [CarrierNode.orderCoordinate,
                CarrierNode.isHorizontal, CarrierNode.position,
                CrossingBoundary.position, crossingMacroOrigin,
                CrossingSide.localPosition,
                CrossoverVariable.position, Cell.add, Cell.scale,
                planarMacroScale] at coordinateEqual
            · rfl
          · exact False.elim
              ((crossingBoundary_orderCoordinate_ne_of_common_carrier
                wellFormed degree isLocal
                firstBoundaryMem secondBoundaryMem
                keyEqual crossingEqual) coordinateEqual)

/-- A noduplicated weakly sorted list whose sort key is injective on its
members is strictly sorted. -/
theorem List.pairwise_lt_of_pairwise_le_of_nodup_of_injective
    {Value : Type*} [DecidableEq Value]
    (coordinate : Value → Int)
    {values : List Value}
    (ordered :
      values.Pairwise fun first second =>
        coordinate first ≤ coordinate second)
    (nodup : values.Nodup)
    (injective :
      ∀ first ∈ values, ∀ second ∈ values,
        coordinate first = coordinate second →
          first = second) :
    values.Pairwise fun first second =>
      coordinate first < coordinate second := by
  induction values with
  | nil =>
      simp
  | cons head tail induction =>
      rw [List.pairwise_cons] at ordered
      rw [List.nodup_cons] at nodup
      rw [List.pairwise_cons]
      constructor
      · intro item itemMem
        have coordinateNe :
            coordinate head ≠ coordinate item := by
          intro coordinateEqual
          have itemEqual :
              head = item :=
            injective head (by simp) item
              (by simp [itemMem]) coordinateEqual
          exact nodup.1 (itemEqual ▸ itemMem)
        exact lt_of_le_of_ne
          (ordered.1 item itemMem) coordinateNe
      · apply induction ordered.2 nodup.2
        intro first firstMem second secondMem coordinateEqual
        exact injective first
          (by simp [firstMem]) second
          (by simp [secondMem]) coordinateEqual

/-- Every complete carrier chain is strictly sorted by its physical axis
coordinate. -/
theorem completeCarrierNodes_pairwise_orderCoordinate_lt
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    (key : Nat × Nat × Cell) :
    (completeCarrierNodes graph key).Pairwise
      fun first second =>
        first.orderCoordinate graph <
          second.orderCoordinate graph := by
  apply List.pairwise_lt_of_pairwise_le_of_nodup_of_injective
    (CarrierNode.orderCoordinate graph)
  · unfold completeCarrierNodes
    exact List.pairwise_insertionSort _ _
  · exact completeCarrierNodes_nodup graph key
  · intro first firstMem second secondMem coordinateEqual
    have firstData :=
      (mem_completeCarrierNodes_iff
        graph key first).mp firstMem
    have secondData :=
      (mem_completeCarrierNodes_iff
        graph key second).mp secondMem
    exact carrierNode_eq_of_commonCarrier_orderCoordinate_eq
      wellFormed degree isLocal
      firstData.1 secondData.1
      (firstData.2.trans secondData.2.symm)
      coordinateEqual

/-- In a strictly sorted list, an element whose coordinate lies after the
first and no later than the second member of a consecutive pair is that
second member. -/
theorem eq_second_of_mem_consecutivePairs_of_coordinate_between
    {Value : Type*}
    (coordinate : Value → Int)
    {values : List Value}
    (ordered :
      values.Pairwise fun first second =>
        coordinate first < coordinate second)
    {pair : Value × Value}
    (pairMem : pair ∈ consecutivePairs values)
    {middle : Value}
    (middleMem : middle ∈ values)
    (firstLt :
      coordinate pair.1 < coordinate middle)
    (middleLe :
      coordinate middle ≤ coordinate pair.2) :
    middle = pair.2 := by
  induction values with
  | nil =>
      simp [consecutivePairs] at pairMem
  | cons head tail induction =>
      cases tail with
      | nil =>
          simp [consecutivePairs] at pairMem
      | cons next rest =>
          rw [List.pairwise_cons] at ordered
          simp only [consecutivePairs, List.mem_cons] at pairMem
          rcases pairMem with pairEqual | pairMem
          · subst pair
            change coordinate head < coordinate middle at firstLt
            change coordinate middle ≤ coordinate next at middleLe
            change middle = next
            simp only [List.mem_cons] at middleMem
            rcases middleMem with middleEqual | middleMem
            · subst middle
              omega
            · rcases middleMem with middleEqual | middleMem
              · subst middle
                rfl
              · have nextLtMiddle :=
                  (List.pairwise_cons.mp ordered.2).1
                    middle middleMem
                omega
          · have pairMembers :=
              mem_of_mem_consecutivePairs pairMem
            simp only [List.mem_cons] at middleMem
            rcases middleMem with middleEqual | middleMem
            · subst middle
              have headLtFirst :=
                ordered.1 pair.1
                  (by simp [pairMembers.1])
              omega
            · exact induction ordered.2 pairMem
                (by simpa only [List.mem_cons] using middleMem)

/-- Dual form: in a strictly sorted list, an element no earlier than the
first and before the second member of a consecutive pair is that first
member. -/
theorem eq_first_of_mem_consecutivePairs_of_coordinate_between
    {Value : Type*}
    (coordinate : Value → Int)
    {values : List Value}
    (ordered :
      values.Pairwise fun first second =>
        coordinate first < coordinate second)
    {pair : Value × Value}
    (pairMem : pair ∈ consecutivePairs values)
    {middle : Value}
    (middleMem : middle ∈ values)
    (firstLe :
      coordinate pair.1 ≤ coordinate middle)
    (middleLt :
      coordinate middle < coordinate pair.2) :
    middle = pair.1 := by
  induction values with
  | nil =>
      simp [consecutivePairs] at pairMem
  | cons head tail induction =>
      cases tail with
      | nil =>
          simp [consecutivePairs] at pairMem
      | cons next rest =>
          rw [List.pairwise_cons] at ordered
          simp only [consecutivePairs, List.mem_cons] at pairMem
          rcases pairMem with pairEqual | pairMem
          · subst pair
            change coordinate head ≤ coordinate middle at firstLe
            change coordinate middle < coordinate next at middleLt
            change middle = head
            simp only [List.mem_cons] at middleMem
            rcases middleMem with middleEqual | middleMem
            · exact middleEqual
            · rcases middleMem with middleEqual | middleMem
              · subst middle
                omega
              · have nextLtMiddle :=
                  (List.pairwise_cons.mp ordered.2).1
                    middle middleMem
                omega
          · have pairMembers :=
              mem_of_mem_consecutivePairs pairMem
            simp only [List.mem_cons] at middleMem
            rcases middleMem with middleEqual | middleMem
            · subst middle
              have headLtFirst :=
                ordered.1 pair.1
                  (by simp [pairMembers.1])
              omega
            · exact induction ordered.2 pairMem
                (by simpa only [List.mem_cons] using middleMem)

/-- Retained adjacent carrier nodes advance by at least one full ten-cell
port-coordinate step. -/
theorem completeCarrierPair_orderCoordinate_add_ten_le
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    (key : Nat × Nat × Cell)
    {pair : CarrierNode × CarrierNode}
    (pairMem :
      pair ∈ consecutivePairs
        (completeCarrierNodes graph key))
    (retained :
      !pair.1.sameCrossoverSite pair.2) :
    pair.1.orderCoordinate graph + 10 ≤
      pair.2.orderCoordinate graph := by
  have members := mem_of_mem_consecutivePairs pairMem
  have firstData :=
    (mem_completeCarrierNodes_iff
      graph key pair.1).mp members.1
  have secondData :=
    (mem_completeCarrierNodes_iff
      graph key pair.2).mp members.2
  have keyEqual :
      pair.1.carrierKey = pair.2.carrierKey :=
    firstData.2.trans secondData.2.symm
  have occurrenceEqual :=
    carrierNode_indexed_translate_eq_of_carrierKey_eq
      graph firstData.1 secondData.1 keyEqual
  have firstAligned :
      pair.1.indexed.segment.IsAxisAligned :=
    drawing_isOrthogonal wellFormed isLocal degree
      pair.1.indexed
      (carrierNode_indexed_mem graph firstData.1)
  have secondAligned :
      pair.2.indexed.segment.IsAxisAligned := by
    rw [← occurrenceEqual.1]
    exact firstAligned
  have axisData :=
    carrierNode_commonCarrier_axis_data
      wellFormed degree isLocal
      firstData.1 secondData.1 keyEqual
  have strict :=
    completeCarrierPair_orderCoordinate_lt
      wellFormed degree isLocal key pairMem retained
  by_cases horizontal : pair.1.isHorizontal = true
  · have firstHorizontal :
        pair.1.indexed.segment.IsHorizontal :=
      (carrierNode_isHorizontal_iff
        graph firstData.1 firstAligned).mp horizontal
    have secondHorizontal :
        pair.2.indexed.segment.IsHorizontal := by
      rw [← occurrenceEqual.1]
      exact firstHorizontal
    have secondHorizontalTag :
        pair.2.isHorizontal = true :=
      (carrierNode_isHorizontal_iff
        graph secondData.1 secondAligned).mpr secondHorizontal
    have axisData' :
        (pair.1.position graph).1 % 10 = 1 ∧
          (pair.2.position graph).1 % 10 = 1 := by
      rw [if_pos horizontal] at axisData
      exact axisData.2
    simp [CarrierNode.orderCoordinate,
      horizontal, secondHorizontalTag] at strict ⊢
    omega
  · have secondNotHorizontalTag :
        ¬pair.2.isHorizontal = true := by
      intro secondHorizontalTag
      have secondHorizontal :=
        (carrierNode_isHorizontal_iff
          graph secondData.1 secondAligned).mp
          secondHorizontalTag
      have firstHorizontal :
          pair.1.indexed.segment.IsHorizontal := by
        rw [occurrenceEqual.1]
        exact secondHorizontal
      exact horizontal
        ((carrierNode_isHorizontal_iff
          graph firstData.1 firstAligned).mpr firstHorizontal)
    have axisData' :
        (pair.1.position graph).2 % 10 = 1 ∧
          (pair.2.position graph).2 % 10 = 1 := by
      rw [if_neg horizontal] at axisData
      exact axisData.2
    simp [CarrierNode.orderCoordinate,
      horizontal, secondNotHorizontalTag] at strict ⊢
    omega

/-- Both endpoints of a retained carrier link have the same horizontal-axis
tag. -/
theorem drawingCompleteCarrierLink_first_isHorizontal_iff_second
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ drawingCompleteCarrierLinks graph) :
    link.first.isHorizontal = true ↔
      link.second.isHorizontal = true := by
  have endpoints :=
    drawingCompleteCarrierLink_endpoints_mem graph linkMem
  have keyEqual :=
    drawingCompleteCarrierLinks_common_key graph linkMem
  have occurrenceEqual :=
    carrierNode_indexed_translate_eq_of_carrierKey_eq
      graph endpoints.1 endpoints.2 keyEqual
  have firstAligned :
      link.first.indexed.segment.IsAxisAligned :=
    drawing_isOrthogonal wellFormed isLocal degree
      link.first.indexed
      (carrierNode_indexed_mem graph endpoints.1)
  have secondAligned :
      link.second.indexed.segment.IsAxisAligned := by
    rw [← occurrenceEqual.1]
    exact firstAligned
  constructor
  · intro firstHorizontalTag
    have firstHorizontal :=
      (carrierNode_isHorizontal_iff
        graph endpoints.1 firstAligned).mp
        firstHorizontalTag
    have secondHorizontal :
        link.second.indexed.segment.IsHorizontal := by
      rw [← occurrenceEqual.1]
      exact firstHorizontal
    exact
      (carrierNode_isHorizontal_iff
        graph endpoints.2 secondAligned).mpr
        secondHorizontal
  · intro secondHorizontalTag
    have secondHorizontal :=
      (carrierNode_isHorizontal_iff
        graph endpoints.2 secondAligned).mp
        secondHorizontalTag
    have firstHorizontal :
        link.first.indexed.segment.IsHorizontal := by
      rw [occurrenceEqual.1]
      exact secondHorizontal
    exact
      (carrierNode_isHorizontal_iff
        graph endpoints.1 firstAligned).mpr
        firstHorizontal

end PeriodicOrthocrossing
end LeanTrominoes
