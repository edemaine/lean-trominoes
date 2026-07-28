import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedCarrierClauseSignatures

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

@[simp]
theorem CarrierNode.periodTranslate_neg
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (node : CarrierNode) (shift : Cell) :
    (node.periodTranslate graph shift).periodTranslate graph
        (Cell.neg shift) =
      node := by
  cases node with
  | boundary boundary =>
      rcases boundary with ⟨crossing, side⟩
      simp [CarrierNode.periodTranslate,
        CrossingBoundary.periodTranslate,
        CrossingRecord.periodTranslate_neg]
  | terminal terminal =>
      rcases terminal with ⟨indexed, translate, endpoint⟩
      rcases shift with ⟨shiftX, shiftY⟩
      simp [CarrierNode.periodTranslate,
        SegmentTerminal.periodTranslate,
        Cell.neg, Cell.sub, Cell.add]

@[simp]
theorem CarrierNode.periodTranslate_neg_left
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (node : CarrierNode) (shift : Cell) :
    (node.periodTranslate graph (Cell.neg shift)).periodTranslate graph
        shift =
      node := by
  cases node with
  | boundary boundary =>
      rcases boundary with ⟨crossing, side⟩
      rcases crossing with
        ⟨first, firstTranslate, second, secondTranslate, point⟩
      rcases shift with ⟨shiftX, shiftY⟩
      simp [CarrierNode.periodTranslate,
        CrossingBoundary.periodTranslate,
        CrossingRecord.periodTranslate,
        PeriodicGridDrawing.periodTranslation,
        Cell.neg, Cell.sub, Cell.add, Cell.scale]
  | terminal terminal =>
      rcases terminal with ⟨indexed, translate, endpoint⟩
      rcases shift with ⟨shiftX, shiftY⟩
      simp [CarrierNode.periodTranslate,
        SegmentTerminal.periodTranslate,
        Cell.neg, Cell.sub, Cell.add]

theorem retainedCrossingBoundary_periodTranslate_mem_of_translate_neighbor
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {boundary : CrossingBoundary}
    (boundaryMem :
      boundary ∈ retainedCrossingBoundaries graph)
    (shift : Cell)
    (translateNeighbor :
      IsNeighborTranslation
        (boundary.periodTranslate graph shift).translate) :
    boundary.periodTranslate graph shift ∈
      retainedCrossingBoundaries graph := by
  let translated := boundary.periodTranslate graph shift
  have translatedData :=
    retainedCrossingBoundary_periodTranslate_indexed_mem_and_contains
      graph boundaryMem shift
  have pointBounds :
      InCarrierCrossingRetentionSquare graph
        translated.crossing.point :=
    drawing_neighbor_occurrence_point_in_retention_square
      wellFormed degree isLocal translatedData.1
        translateNeighbor translatedData.2
  have shiftMem :
      crossingPeriodShift graph translated.crossing ∈
        carrierCrossingRetentionShifts :=
    crossingPeriodShift_mem_retentionShifts
      graph translated.crossing pointBounds
  have normalizedBoundaryMem :
      translated.periodNormalize graph ∈
        drawingCrossingBoundaries graph := by
    simpa [translated] using
      retainedCrossingBoundary_periodNormalize_mem
        graph boundaryMem
  have normalizedCrossingMem :
      translated.crossing.periodNormalize graph ∈
        orientedCrossings graph :=
    drawingCrossingBoundary_crossing_mem_orientedCrossings
      graph normalizedBoundaryMem
  have crossingMem :
      translated.crossing ∈ retainedCrossings graph :=
    mem_retainedCrossings_of_periodNormalize_mem_of_shift_mem
      graph translated.crossing normalizedCrossingMem shiftMem
  change translated ∈ retainedCrossingBoundaries graph
  rcases translated with ⟨crossing, side⟩
  apply List.mem_flatMap.mpr
  refine ⟨crossing, crossingMem, ?_⟩
  cases side <;> simp

theorem retainedCarrierNode_periodTranslate_mem_of_translate_neighbor
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {node : CarrierNode}
    (nodeMem : node ∈ retainedDrawingCarrierNodes graph)
    (shift : Cell)
    (translateNeighbor :
      IsNeighborTranslation
        (node.periodTranslate graph shift).translate) :
    node.periodTranslate graph shift ∈
      retainedDrawingCarrierNodes graph := by
  cases node with
  | boundary boundary =>
      have boundaryMem :
          boundary ∈ retainedCrossingBoundaries graph := by
        unfold retainedDrawingCarrierNodes at nodeMem
        simpa using nodeMem
      unfold retainedDrawingCarrierNodes
      apply List.mem_append_right
      apply List.mem_map.mpr
      refine ⟨boundary.periodTranslate graph shift, ?_, rfl⟩
      exact
        retainedCrossingBoundary_periodTranslate_mem_of_translate_neighbor
          wellFormed degree isLocal boundaryMem shift translateNeighbor
  | terminal terminal =>
      have terminalMem :
          terminal ∈ drawingSegmentTerminals graph := by
        unfold retainedDrawingCarrierNodes at nodeMem
        simpa using nodeMem
      unfold retainedDrawingCarrierNodes
      apply List.mem_append_left
      apply List.mem_map.mpr
      refine ⟨terminal.periodTranslate shift, ?_, rfl⟩
      apply mem_drawingSegmentTerminals_of_indexed_mem_of_translate_neighbor
      · simpa [SegmentTerminal.periodTranslate] using
          (drawingSegmentTerminal_indexed_mem graph terminalMem).1
      · change
          IsNeighborTranslation
            (terminal.periodTranslate shift).translate
          at translateNeighbor
        exact translateNeighbor

theorem retainedCarrierNode_isHorizontal_eq_of_carrierKey_eq
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {first second : CarrierNode}
    (firstMem : first ∈ retainedDrawingCarrierNodes graph)
    (secondMem : second ∈ retainedDrawingCarrierNodes graph)
    (keyEq : first.carrierKey = second.carrierKey) :
    first.isHorizontal = second.isHorizontal := by
  have fields :=
    carrierNode_indexed_translate_eq_of_carrierKey_eq_of_indexed_mem
      graph
      (retainedCarrierNode_indexed_mem graph firstMem)
      (retainedCarrierNode_indexed_mem graph secondMem)
      keyEq
  have firstAligned :
      first.indexed.segment.IsAxisAligned :=
    drawing_isOrthogonal wellFormed isLocal degree first.indexed
      (retainedCarrierNode_indexed_mem graph firstMem)
  have secondAligned :
      second.indexed.segment.IsAxisAligned := by
    rw [← fields.1]
    exact firstAligned
  apply Bool.eq_iff_iff.mpr
  rw [retainedCarrierNode_isHorizontal_iff
      graph firstMem firstAligned,
    retainedCarrierNode_isHorizontal_iff
      graph secondMem secondAligned,
    fields.1]

theorem CarrierNode.orderCoordinate_periodTranslate_lt_iff
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (first second : CarrierNode) (shift : Cell)
    (sameAxis : first.isHorizontal = second.isHorizontal) :
    (first.periodTranslate graph shift).orderCoordinate graph <
        (second.periodTranslate graph shift).orderCoordinate graph ↔
      first.orderCoordinate graph < second.orderCoordinate graph := by
  rw [CarrierNode.orderCoordinate_periodTranslate,
    CarrierNode.orderCoordinate_periodTranslate]
  rw [sameAxis]
  split <;> omega

theorem mem_consecutivePairs_of_pairwise_lt_of_gap
    {Value : Type*}
    (coordinate : Value → Int)
    {values : List Value}
    (ordered :
      values.Pairwise fun first second =>
        coordinate first < coordinate second)
    {first second : Value}
    (firstMem : first ∈ values)
    (secondMem : second ∈ values)
    (firstLt : coordinate first < coordinate second)
    (gap :
      ∀ middle ∈ values,
        coordinate first < coordinate middle →
        coordinate middle ≤ coordinate second →
        middle = second) :
    (first, second) ∈ consecutivePairs values := by
  induction values with
  | nil =>
      simp at firstMem
  | cons head tail induction =>
      cases tail with
      | nil =>
          simp at firstMem secondMem
          subst first
          subst second
          omega
      | cons next rest =>
          rw [List.pairwise_cons] at ordered
          simp only [List.mem_cons] at firstMem secondMem
          rcases firstMem with firstEq | firstMem
          · subst first
            have tailOrdered := ordered.2
            rw [List.pairwise_cons] at tailOrdered
            have nextLe : coordinate next ≤ coordinate second := by
              rcases secondMem with secondEq | secondTailMem
              · subst second
                omega
              · rcases secondTailMem with secondEq | secondRestMem
                · subst second
                  exact Int.le_refl _
                · exact le_of_lt
                    (tailOrdered.1 second secondRestMem)
            have nextEq :
                next = second :=
              gap next (by simp) (ordered.1 next (by simp)) nextLe
            subst second
            simp [consecutivePairs]
          · have secondTailMem : second ∈ next :: rest := by
              rcases secondMem with secondEq | secondMem
              · subst second
                have headLtFirst :=
                  ordered.1 first (by simp [firstMem])
                omega
              · simpa only [List.mem_cons] using secondMem
            rw [consecutivePairs]
            simp only [List.mem_cons]
            right
            apply induction ordered.2
              (by simp [firstMem]) secondTailMem
            intro middle middleMem middleLt middleLe
            exact gap middle (by simp [middleMem]) middleLt middleLe

theorem retainedCompleteCarrierLink_periodTranslate_mem
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {key : Nat × Nat × Cell}
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedCompleteCarrierLinks graph key)
    (shift : Cell)
    (sourceNeighbor :
      IsNeighborTranslation link.first.translate)
    (targetNeighbor :
      IsNeighborTranslation
        (link.first.periodTranslate graph shift).translate) :
    carrierLinkPeriodTranslate graph link shift ∈
      retainedCompleteCarrierLinks graph
        (periodTranslateCarrierKey key shift) := by
  rcases List.mem_map.mp linkMem with
    ⟨pair, pairMem, linkEq⟩
  subst link
  have pairConsecutive :=
    (List.mem_filter.mp pairMem).1
  have pairAllowed :=
    (List.mem_filter.mp pairMem).2
  have pairMembers :=
    mem_of_mem_consecutivePairs pairConsecutive
  have firstData :=
    (mem_retainedCompleteCarrierNodes_iff
      graph key pair.1).mp pairMembers.1
  have secondData :=
    (mem_retainedCompleteCarrierNodes_iff
      graph key pair.2).mp pairMembers.2
  have sourceAxisEq :
      pair.1.isHorizontal = pair.2.isHorizontal :=
    retainedCarrierNode_isHorizontal_eq_of_carrierKey_eq
      wellFormed degree isLocal firstData.1 secondData.1
      (firstData.2.trans secondData.2.symm)
  have sourceFields :=
    carrierNode_indexed_translate_eq_of_carrierKey_eq_of_indexed_mem
      graph
      (retainedCarrierNode_indexed_mem graph firstData.1)
      (retainedCarrierNode_indexed_mem graph secondData.1)
      (firstData.2.trans secondData.2.symm)
  change IsNeighborTranslation pair.1.translate at sourceNeighbor
  change
    IsNeighborTranslation
      (pair.1.periodTranslate graph shift).translate
    at targetNeighbor
  have targetSecondNeighbor :
      IsNeighborTranslation
        (pair.2.periodTranslate graph shift).translate := by
    rw [CarrierNode.translate_periodTranslate,
      sourceFields.2.symm]
    simpa only [CarrierNode.translate_periodTranslate] using targetNeighbor
  have targetFirstRetained :
      pair.1.periodTranslate graph shift ∈
        retainedDrawingCarrierNodes graph :=
    retainedCarrierNode_periodTranslate_mem_of_translate_neighbor
      wellFormed degree isLocal firstData.1 shift targetNeighbor
  have targetSecondRetained :
      pair.2.periodTranslate graph shift ∈
        retainedDrawingCarrierNodes graph :=
    retainedCarrierNode_periodTranslate_mem_of_translate_neighbor
      wellFormed degree isLocal secondData.1 shift
        targetSecondNeighbor
  let targetKey := periodTranslateCarrierKey key shift
  let targetPair : CarrierNode × CarrierNode :=
    (pair.1.periodTranslate graph shift,
      pair.2.periodTranslate graph shift)
  have targetFirstKey :
      targetPair.1.carrierKey = targetKey := by
    simp only [targetPair, targetKey,
      CarrierNode.carrierKey_periodTranslate]
    rw [firstData.2]
  have targetSecondKey :
      targetPair.2.carrierKey = targetKey := by
    simp only [targetPair, targetKey,
      CarrierNode.carrierKey_periodTranslate]
    rw [secondData.2]
  have targetFirstMem :
      targetPair.1 ∈ retainedCompleteCarrierNodes graph targetKey :=
    (mem_retainedCompleteCarrierNodes_iff
      graph targetKey targetPair.1).mpr
        ⟨by simpa [targetPair] using targetFirstRetained,
          targetFirstKey⟩
  have targetSecondMem :
      targetPair.2 ∈ retainedCompleteCarrierNodes graph targetKey :=
    (mem_retainedCompleteCarrierNodes_iff
      graph targetKey targetPair.2).mpr
        ⟨by simpa [targetPair] using targetSecondRetained,
          targetSecondKey⟩
  have sourceOrdered :=
    consecutivePairs_rel_of_pairwise
      (retainedCompleteCarrierNodes_pairwise_orderCoordinate_lt
        wellFormed degree isLocal key)
      pairConsecutive
  have targetFirstLt :
      targetPair.1.orderCoordinate graph <
        targetPair.2.orderCoordinate graph := by
    change
      (pair.1.periodTranslate graph shift).orderCoordinate graph <
        (pair.2.periodTranslate graph shift).orderCoordinate graph
    exact
      (CarrierNode.orderCoordinate_periodTranslate_lt_iff
        graph pair.1 pair.2 shift sourceAxisEq).mpr sourceOrdered
  have targetConsecutive :
      targetPair ∈ consecutivePairs
        (retainedCompleteCarrierNodes graph targetKey) := by
    apply mem_consecutivePairs_of_pairwise_lt_of_gap
      (CarrierNode.orderCoordinate graph)
      (retainedCompleteCarrierNodes_pairwise_orderCoordinate_lt
        wellFormed degree isLocal targetKey)
      targetFirstMem targetSecondMem targetFirstLt
    intro middle middleMem firstLtMiddle middleLeSecond
    have middleData :=
      (mem_retainedCompleteCarrierNodes_iff
        graph targetKey middle).mp middleMem
    have targetFirstAxisEq :
        targetPair.1.isHorizontal = middle.isHorizontal :=
      retainedCarrierNode_isHorizontal_eq_of_carrierKey_eq
        wellFormed degree isLocal
        (by simpa [targetPair] using targetFirstRetained)
        middleData.1
        (targetFirstKey.trans middleData.2.symm)
    have middleTargetSecondAxisEq :
        middle.isHorizontal = targetPair.2.isHorizontal :=
      retainedCarrierNode_isHorizontal_eq_of_carrierKey_eq
        wellFormed degree isLocal middleData.1
        (by simpa [targetPair] using targetSecondRetained)
        (middleData.2.trans targetSecondKey.symm)
    let back := middle.periodTranslate graph (Cell.neg shift)
    have targetFields :=
      carrierNode_indexed_translate_eq_of_carrierKey_eq_of_indexed_mem
        graph
        (retainedCarrierNode_indexed_mem graph middleData.1)
        (retainedCarrierNode_indexed_mem graph
          (by simpa [targetPair] using targetFirstRetained))
        (middleData.2.trans targetFirstKey.symm)
    have backTranslateEq :
        back.translate = pair.1.translate := by
      rcases shift with ⟨shiftX, shiftY⟩
      dsimp [back]
      rw [CarrierNode.translate_periodTranslate]
      rw [targetFields.2]
      simp [targetPair, CarrierNode.translate_periodTranslate,
        Cell.neg, Cell.sub, Cell.add]
    have backRetained :
        back ∈ retainedDrawingCarrierNodes graph := by
      apply
        retainedCarrierNode_periodTranslate_mem_of_translate_neighbor
          wellFormed degree isLocal middleData.1 (Cell.neg shift)
      rw [backTranslateEq]
      exact sourceNeighbor
    have backKey : back.carrierKey = key := by
      dsimp [back]
      rw [CarrierNode.carrierKey_periodTranslate]
      rw [middleData.2]
      rcases key with ⟨route, segment, keyTranslate⟩
      rcases shift with ⟨shiftX, shiftY⟩
      simp [targetKey, periodTranslateCarrierKey,
        Cell.neg, Cell.sub, Cell.add]
    have backMem :
        back ∈ retainedCompleteCarrierNodes graph key :=
      (mem_retainedCompleteCarrierNodes_iff
        graph key back).mpr ⟨backRetained, backKey⟩
    have sourceFirstLtBack :
        pair.1.orderCoordinate graph <
          back.orderCoordinate graph := by
      have translated :=
        (CarrierNode.orderCoordinate_periodTranslate_lt_iff
          graph targetPair.1 middle (Cell.neg shift)
            targetFirstAxisEq).mpr firstLtMiddle
      simpa [targetPair, back] using translated
    have backLeSourceSecond :
        back.orderCoordinate graph ≤
          pair.2.orderCoordinate graph := by
      have translated :=
        (CarrierNode.orderCoordinate_periodTranslate_le_iff
          graph middle targetPair.2 (Cell.neg shift)
            middleTargetSecondAxisEq).mpr middleLeSecond
      simpa [targetPair, back] using translated
    have backEq :
        back = pair.2 :=
      eq_second_of_mem_consecutivePairs_of_coordinate_between
        (CarrierNode.orderCoordinate graph)
        (retainedCompleteCarrierNodes_pairwise_orderCoordinate_lt
          wellFormed degree isLocal key)
        pairConsecutive backMem
        sourceFirstLtBack backLeSourceSecond
    have forwardEq :=
      congrArg
        (fun node : CarrierNode =>
          node.periodTranslate graph shift)
        backEq
    simpa [back, targetPair] using forwardEq
  apply List.mem_map.mpr
  refine ⟨targetPair, List.mem_filter.mpr
    ⟨targetConsecutive, ?_⟩, ?_⟩
  · simpa [targetPair] using pairAllowed
  · simp [targetPair]

theorem retainedDrawingCompleteCarrierLinkRaw_periodTranslate_mem
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ retainedDrawingCompleteCarrierLinksRaw graph)
    (shift : Cell)
    (sourceNeighbor :
      IsNeighborTranslation link.first.translate)
    (targetNeighbor :
      IsNeighborTranslation
        (link.first.periodTranslate graph shift).translate) :
    carrierLinkPeriodTranslate graph link shift ∈
      retainedDrawingCompleteCarrierLinksRaw graph := by
  rcases List.mem_flatMap.mp linkMem with
    ⟨key, _keyMem, chainMem⟩
  have endpoints :=
    retainedDrawingCompleteCarrierLinkRaw_endpoints_mem graph linkMem
  have targetFirstRetained :=
    retainedCarrierNode_periodTranslate_mem_of_translate_neighbor
      wellFormed degree isLocal endpoints.1 shift targetNeighbor
  let targetKey := periodTranslateCarrierKey key shift
  have targetKeyMem :
      targetKey ∈ retainedDrawingCompleteCarrierKeys graph := by
    unfold retainedDrawingCompleteCarrierKeys
    rw [List.mem_dedup]
    apply List.mem_map.mpr
    refine ⟨link.first.periodTranslate graph shift,
      targetFirstRetained, ?_⟩
    simp only [targetKey, CarrierNode.carrierKey_periodTranslate]
    have common :=
      retainedCompleteCarrierLinks_common_key graph key chainMem
    rw [common.1]
  apply List.mem_flatMap.mpr
  refine ⟨targetKey, targetKeyMem, ?_⟩
  exact retainedCompleteCarrierLink_periodTranslate_mem
    wellFormed degree isLocal chainMem shift
      sourceNeighbor targetNeighbor

theorem retainedDrawingCompleteCarrierLinksRaw_eq_of_first_eq
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {first second : EqualityLink CarrierNode}
    (firstMem :
      first ∈ retainedDrawingCompleteCarrierLinksRaw graph)
    (secondMem :
      second ∈ retainedDrawingCompleteCarrierLinksRaw graph)
    (firstEq : first.first = second.first) :
    first = second := by
  rcases List.mem_flatMap.mp firstMem with
    ⟨firstKey, _firstKeyMem, firstChainMem⟩
  rcases List.mem_flatMap.mp secondMem with
    ⟨secondKey, _secondKeyMem, secondChainMem⟩
  have firstCommon :=
    retainedCompleteCarrierLinks_common_key
      graph firstKey firstChainMem
  have secondCommon :=
    retainedCompleteCarrierLinks_common_key
      graph secondKey secondChainMem
  have keyEq : firstKey = secondKey := by
    rw [← firstCommon.1, ← secondCommon.1, firstEq]
  subst secondKey
  rcases List.mem_map.mp firstChainMem with
    ⟨firstPair, firstPairMem, firstLinkEq⟩
  rcases List.mem_map.mp secondChainMem with
    ⟨secondPair, secondPairMem, secondLinkEq⟩
  have pairEq :
      firstPair = secondPair := by
    apply consecutivePairs_eq_of_fst_eq_of_nodup
      (retainedCompleteCarrierNodes_nodup graph firstKey)
      (List.mem_filter.mp firstPairMem).1
      (List.mem_filter.mp secondPairMem).1
    calc
      firstPair.1 =
          first.first :=
        congrArg EqualityLink.first firstLinkEq
      _ = second.first := firstEq
      _ = secondPair.1 :=
        (congrArg EqualityLink.first secondLinkEq).symm
  subst secondPair
  exact firstLinkEq.symm.trans secondLinkEq

theorem
    retainedDrawingCompleteCarrierLink_terminalZeroTranslate_mem_raw
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem : link ∈ retainedDrawingCompleteCarrierLinks graph)
    {terminal : SegmentTerminal}
    (firstEq : link.first = .terminal terminal) :
    carrierLinkPeriodTranslate graph link
        (Cell.neg terminal.translate) ∈
      retainedDrawingCompleteCarrierLinksRaw graph := by
  apply retainedDrawingCompleteCarrierLinkRaw_periodTranslate_mem
    wellFormed degree isLocal
    ((mem_retainedDrawingCompleteCarrierLinks_iff
      graph link).mp linkMem).1
  · exact
      retainedDrawingCompleteCarrierLink_first_translate_neighbor
        graph linkMem
  · rw [firstEq]
    rcases terminal with ⟨indexed, translate, endpoint⟩
    rcases translate with ⟨translateX, translateY⟩
    simp [CarrierNode.periodTranslate,
      SegmentTerminal.periodTranslate,
      CarrierNode.translate,
      Cell.neg, Cell.sub, Cell.add, IsNeighborTranslation]

theorem retainedDrawingCompleteCarrierLinks_normalizeLink_eq_of_first_eq
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {first second : EqualityLink CarrierNode}
    (firstMem :
      first ∈ retainedDrawingCompleteCarrierLinks graph)
    (secondMem :
      second ∈ retainedDrawingCompleteCarrierLinks graph)
    (normalizedFirstEq :
      (normalizeCarrierNode graph first.first).1 =
        (normalizeCarrierNode graph second.first).1) :
    PeriodicEquality.normalizeLink (normalizeCarrierNode graph) first =
      PeriodicEquality.normalizeLink (normalizeCarrierNode graph)
        second := by
  cases firstNode : first.first with
  | boundary firstBoundary =>
      cases secondNode : second.first with
      | terminal secondTerminal =>
          simp [firstNode, secondNode, normalizeCarrierNode]
            at normalizedFirstEq
      | boundary secondBoundary =>
          have firstRepresentative :=
            ((mem_retainedDrawingCompleteCarrierLinks_iff
              graph first).mp firstMem).2
          have secondRepresentative :=
            ((mem_retainedDrawingCompleteCarrierLinks_iff
              graph second).mp secondMem).2
          have firstNormalize :=
            carrierLinkRepresentative_first_boundary_normalizes_self
              graph firstNode firstRepresentative
          have secondNormalize :=
            carrierLinkRepresentative_first_boundary_normalizes_self
              graph secondNode secondRepresentative
          have boundaryEq : firstBoundary = secondBoundary := by
            simpa [firstNode, secondNode, normalizeCarrierNode,
              firstNormalize, secondNormalize] using normalizedFirstEq
          have linkEq : first = second := by
            apply retainedDrawingCompleteCarrierLinks_eq_of_first_eq
              firstMem secondMem
            rw [firstNode, secondNode, boundaryEq]
          rw [linkEq]
  | terminal firstTerminal =>
      cases secondNode : second.first with
      | boundary secondBoundary =>
          simp [firstNode, secondNode, normalizeCarrierNode]
            at normalizedFirstEq
      | terminal secondTerminal =>
          have terminalData :
              firstTerminal.indexed = secondTerminal.indexed ∧
                firstTerminal.endpoint = secondTerminal.endpoint := by
            simpa [firstNode, secondNode, normalizeCarrierNode] using
              normalizedFirstEq
          let firstZero :=
            carrierLinkPeriodTranslate graph first
              (Cell.neg firstTerminal.translate)
          let secondZero :=
            carrierLinkPeriodTranslate graph second
              (Cell.neg secondTerminal.translate)
          have firstZeroMem :
              firstZero ∈
                retainedDrawingCompleteCarrierLinksRaw graph := by
            exact
              retainedDrawingCompleteCarrierLink_terminalZeroTranslate_mem_raw
                wellFormed degree isLocal firstMem firstNode
          have secondZeroMem :
              secondZero ∈
                retainedDrawingCompleteCarrierLinksRaw graph := by
            exact
              retainedDrawingCompleteCarrierLink_terminalZeroTranslate_mem_raw
                wellFormed degree isLocal secondMem secondNode
          have zeroFirstEq :
              firstZero.first = secondZero.first := by
            rcases firstTerminal with
              ⟨firstIndexed, firstTranslate, firstEndpoint⟩
            rcases secondTerminal with
              ⟨secondIndexed, secondTranslate, secondEndpoint⟩
            rcases firstTranslate with ⟨firstX, firstY⟩
            rcases secondTranslate with ⟨secondX, secondY⟩
            simp only at terminalData
            simp [firstZero, secondZero, firstNode, secondNode,
              carrierLinkPeriodTranslate, CarrierNode.periodTranslate,
              SegmentTerminal.periodTranslate,
              Cell.neg, Cell.sub, Cell.add,
              terminalData.1, terminalData.2]
          have zeroEq : firstZero = secondZero :=
            retainedDrawingCompleteCarrierLinksRaw_eq_of_first_eq
              firstZeroMem secondZeroMem zeroFirstEq
          calc
            PeriodicEquality.normalizeLink
                (normalizeCarrierNode graph) first =
              PeriodicEquality.normalizeLink
                (normalizeCarrierNode graph) firstZero := by
                  symm
                  exact normalizeLink_carrierLinkPeriodTranslate
                    graph first (Cell.neg firstTerminal.translate)
            _ =
              PeriodicEquality.normalizeLink
                (normalizeCarrierNode graph) secondZero := by
                  rw [zeroEq]
            _ =
              PeriodicEquality.normalizeLink
                (normalizeCarrierNode graph) second :=
                  normalizeLink_carrierLinkPeriodTranslate
                    graph second (Cell.neg secondTerminal.translate)

theorem cell_emod_period_eq_of_planarSATPeriodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {first second : Cell} (shift : Cell)
    (equal :
      first =
        Cell.add second
          (Cell.scale
            (drawingPeriodicPlanarSATPlacement formula).period
            shift)) :
    first.1 %
          (drawingPeriodicPlanarSATPlacement formula).period =
        second.1 %
          (drawingPeriodicPlanarSATPlacement formula).period ∧
      first.2 %
          (drawingPeriodicPlanarSATPlacement formula).period =
        second.2 %
          (drawingPeriodicPlanarSATPlacement formula).period := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  rcases shift with ⟨shiftX, shiftY⟩
  constructor
  · have coordinateEq := congrArg Prod.fst equal
    simp [Cell.add, Cell.scale] at coordinateEq
    rw [coordinateEq]
    exact Int.add_mul_emod_self_left _ _ _
  · have coordinateEq := congrArg Prod.snd equal
    simp [Cell.add, Cell.scale] at coordinateEq
    rw [coordinateEq]
    exact Int.add_mul_emod_self_left _ _ _

theorem gaugedPeriodicCarrierNode_position_eq_emod
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (node : CarrierNode) :
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula).position
        ⟨periodicCarrierNodeToPlanarSATVariable
          (normalizeCarrierNode
            (PeriodicCNF.incidenceGraph formula) node).1⟩ =
      ((node.position (PeriodicCNF.incidenceGraph formula)).1 %
          (drawingPeriodicPlanarSATPlacement formula).period,
        (node.position (PeriodicCNF.incidenceGraph formula)).2 %
          (drawingPeriodicPlanarSATPlacement formula).period) := by
  rw [
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_position_mk,
    PeriodicVariablePlacement.variableGauge_canonicalPositionGauge_position]
  have physicalPosition :=
    normalizePlanarSATVariable_position formula
      (.inl (.carrier node))
  have normalizedEq :
      normalizePlanarSATVariable formula (.inl (.carrier node)) =
        (periodicCarrierNodeToPlanarSATVariable
            (normalizeCarrierNode
              (PeriodicCNF.incidenceGraph formula) node).1,
          (normalizeCarrierNode
            (PeriodicCNF.incidenceGraph formula) node).2) := by
    cases node <;> rfl
  rw [normalizedEq] at physicalPosition
  have residueData :=
    cell_emod_period_eq_of_planarSATPeriodTranslate formula
      (normalizeCarrierNode
        (PeriodicCNF.incidenceGraph formula) node).2
      (by
        simpa [normalizePlanarSATVariable,
          periodicCarrierNodeToPlanarSATVariable,
          drawingPlanarSATVariablePosition,
          drawingPeriodicPlanarSATPlacement,
          PeriodicVariablePlacement.translation] using
            physicalPosition.symm)
  apply Prod.ext
  · exact residueData.1.symm
  · exact residueData.2.symm

theorem carrierFirst_normalizedPrototype_eq_of_residue_eq
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {firstLink secondLink : EqualityLink CarrierNode}
    (firstLinkMem :
      firstLink ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    (secondLinkMem :
      secondLink ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    {firstClause secondClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {firstIndex secondIndex : Nat}
    (firstMember :
      (firstClause, firstIndex) ∈
        (drawingPlanarSATCarrierFormulaAt
          (Variable := Variable) firstLink).zipIdx)
    (secondMember :
      (secondClause, secondIndex) ∈
        (drawingPlanarSATCarrierFormulaAt
          (Variable := Variable) secondLink).zipIdx)
    (residueEq :
      clauseResidue formula firstClause =
        clauseResidue formula secondClause) :
    (normalizeCarrierNode
        (PeriodicCNF.incidenceGraph formula) firstLink.first).1 =
      (normalizeCarrierNode
        (PeriodicCNF.incidenceGraph formula) secondLink.first).1 := by
  rcases carrierFirstPosition_eq_translate_of_residue_eq
      wellFormed degree isLocal
      firstLinkMem secondLinkMem firstMember secondMember residueEq with
    ⟨shift, positionEq⟩
  have physicalResidueEq :=
    cell_emod_period_eq_of_planarSATPeriodTranslate
      formula shift positionEq
  let firstAtom : PeriodicPlanarSATVariable Variable :=
    periodicCarrierNodeToPlanarSATVariable
      (normalizeCarrierNode
        (PeriodicCNF.incidenceGraph formula) firstLink.first).1
  let secondAtom : PeriodicPlanarSATVariable Variable :=
    periodicCarrierNodeToPlanarSATVariable
      (normalizeCarrierNode
        (PeriodicCNF.incidenceGraph formula) secondLink.first).1
  have firstPositionEq :
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula).position
          ⟨firstAtom⟩ =
        ((firstLink.first.position
            (PeriodicCNF.incidenceGraph formula)).1 %
              (drawingPeriodicPlanarSATPlacement formula).period,
          (firstLink.first.position
            (PeriodicCNF.incidenceGraph formula)).2 %
              (drawingPeriodicPlanarSATPlacement formula).period) := by
    exact gaugedPeriodicCarrierNode_position_eq_emod
      formula firstLink.first
  have secondPositionEq :
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula).position
          ⟨secondAtom⟩ =
        ((secondLink.first.position
            (PeriodicCNF.incidenceGraph formula)).1 %
              (drawingPeriodicPlanarSATPlacement formula).period,
          (secondLink.first.position
            (PeriodicCNF.incidenceGraph formula)).2 %
              (drawingPeriodicPlanarSATPlacement formula).period) := by
    exact gaugedPeriodicCarrierNode_position_eq_emod
      formula secondLink.first
  have gaugedPositionEq :
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula).position
          ⟨firstAtom⟩ =
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement formula).position
          ⟨secondAtom⟩ := by
    rw [firstPositionEq, secondPositionEq]
    exact Prod.ext physicalResidueEq.1 physicalResidueEq.2
  have firstEndpoints :=
    retainedDrawingCompleteCarrierLink_endpoints_mem
      (PeriodicCNF.incidenceGraph formula) firstLinkMem
  have secondEndpoints :=
    retainedDrawingCompleteCarrierLink_endpoints_mem
      (PeriodicCNF.incidenceGraph formula) secondLinkMem
  have firstValid :
      RetainedDrawingPeriodicPlanarSATVariableValid formula firstAtom := by
    have normalizedEq :
        (normalizePlanarSATVariable formula
          (.inl (.carrier firstLink.first))).1 = firstAtom := by
      cases firstNode : firstLink.first <;>
        simp [firstAtom, firstNode, normalizePlanarSATVariable,
          normalizeCarrierNode, periodicCarrierNodeToPlanarSATVariable]
    rw [← normalizedEq]
    exact retainedDrawingPlanarSATVariableValid_normalize
      formula wellFormed degree isLocal
      (.inl (.carrier firstLink.first)) firstEndpoints.1
  have secondValid :
      RetainedDrawingPeriodicPlanarSATVariableValid formula secondAtom := by
    have normalizedEq :
        (normalizePlanarSATVariable formula
          (.inl (.carrier secondLink.first))).1 = secondAtom := by
      cases secondNode : secondLink.first <;>
        simp [secondAtom, secondNode, normalizePlanarSATVariable,
          normalizeCarrierNode, periodicCarrierNodeToPlanarSATVariable]
    rw [← normalizedEq]
    exact retainedDrawingPlanarSATVariableValid_normalize
      formula wellFormed degree isLocal
      (.inl (.carrier secondLink.first)) secondEndpoints.1
  have wrappedEq :
      (⟨firstAtom⟩ :
          WrappedPeriodicPlanarSATVariable Variable) =
        ⟨secondAtom⟩ :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_position_injective_of_valid
      formula wellFormed degree isLocal
      firstValid secondValid gaugedPositionEq
  have atomEq : firstAtom = secondAtom := by
    exact congrArg WrappedPeriodicVariable.original wrappedEq
  exact periodicCarrierNodeToPlanarSATVariable_injective
    (by simpa [firstAtom, secondAtom] using atomEq)

theorem carrier_anchorNormalized_periodicizedClause_eq_of_residue_eq
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    {firstLink secondLink : EqualityLink CarrierNode}
    (firstLinkMem :
      firstLink ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    (secondLinkMem :
      secondLink ∈ retainedDrawingCompleteCarrierLinks
        (PeriodicCNF.incidenceGraph formula))
    {firstClause secondClause :
      EmbeddedClause (PlanarSATVariable Variable)}
    {firstIndex secondIndex : Nat}
    (firstMember :
      (firstClause, firstIndex) ∈
        (drawingPlanarSATCarrierFormulaAt
          (Variable := Variable) firstLink).zipIdx)
    (secondMember :
      (secondClause, secondIndex) ∈
        (drawingPlanarSATCarrierFormulaAt
          (Variable := Variable) secondLink).zipIdx)
    (residueEq :
      clauseResidue formula firstClause =
        clauseResidue formula secondClause) :
    (periodicizePlanarSATClause
        formula firstClause).anchorNormalize =
      (periodicizePlanarSATClause
        formula secondClause).anchorNormalize := by
  have signatureEq :=
    carrierClause_axis_and_index_eq_of_residue_eq
      wellFormed degree isLocal
      firstLinkMem secondLinkMem firstMember secondMember residueEq
  have normalizedFirstEq :=
    carrierFirst_normalizedPrototype_eq_of_residue_eq
      wellFormed degree isLocal
      firstLinkMem secondLinkMem firstMember secondMember residueEq
  have normalizedLinkEq :=
    retainedDrawingCompleteCarrierLinks_normalizeLink_eq_of_first_eq
      wellFormed degree isLocal
      firstLinkMem secondLinkMem normalizedFirstEq
  exact anchorNormalized_periodicizedCarrierClause_eq
    formula firstMember secondMember normalizedLinkEq signatureEq.2

theorem carrier_metadata_anchorNormalized_eq_of_residue_eq
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (first second : DrawingPlanarSATClauseMetadata Variable)
    (firstValid : first.RetainedValid formula)
    (secondValid : second.RetainedValid formula)
    {firstLink secondLink : EqualityLink CarrierNode}
    {firstIndex secondIndex : Nat}
    (firstSource :
      first.source = .carrier firstLink firstIndex)
    (secondSource :
      second.source = .carrier secondLink secondIndex)
    (residueEq :
      clauseResidue formula first.clause =
        clauseResidue formula second.clause) :
    (periodicizePlanarSATClause
        formula first.clause).anchorNormalize =
      (periodicizePlanarSATClause
        formula second.clause).anchorNormalize := by
  unfold DrawingPlanarSATClauseMetadata.RetainedValid
    at firstValid secondValid
  rw [firstSource] at firstValid
  rw [secondSource] at secondValid
  exact carrier_anchorNormalized_periodicizedClause_eq_of_residue_eq
    wellFormed degree isLocal
    firstValid.1 secondValid.1
    firstValid.2 secondValid.2 residueEq

theorem carrier_metadataGaugedNormalizedClause_eq_of_residue_eq
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (first second : DrawingPlanarSATClauseMetadata Variable)
    (firstValid : first.RetainedValid formula)
    (secondValid : second.RetainedValid formula)
    {firstLink secondLink : EqualityLink CarrierNode}
    {firstIndex secondIndex : Nat}
    (firstSource :
      first.source = .carrier firstLink firstIndex)
    (secondSource :
      second.source = .carrier secondLink secondIndex)
    (residueEq :
      clauseResidue formula first.clause =
        clauseResidue formula second.clause) :
    metadataGaugedNormalizedClause formula first =
      metadataGaugedNormalizedClause formula second := by
  unfold metadataGaugedNormalizedClause
  apply variableGauge_anchorNormalize_eq_of_anchorNormalize_eq
  rw [← wrapPeriodicPlanarSATClause_anchorNormalize,
    ← wrapPeriodicPlanarSATClause_anchorNormalize]
  exact congrArg wrapPeriodicPlanarSATClause
    (carrier_metadata_anchorNormalized_eq_of_residue_eq
      wellFormed degree isLocal first second
      firstValid secondValid firstSource secondSource residueEq)

end LeanTrominoes.PeriodicOrthocrossing
