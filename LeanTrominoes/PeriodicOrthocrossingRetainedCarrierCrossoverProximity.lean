import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierMacrocellSeparation
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierInterfaces
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossoverSeparation

/-!
# Retained carrier proximity to a matched crossover

Once a selected carrier is known to be one of a retained crossover's two
source occurrences, overlap with that crossover's standard macrocell forces
endpoint incidence.  The proof uses the two retained boundary nodes and
strict consecutivity of the selected carrier pair.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- A selected horizontal link on a retained crossover's horizontal source
occurrence is incident to that crossover whenever their rectangles are not
separated. -/
theorem
    retainedDrawingCompleteCarrierLink_incidentToCrossover_of_horizontal_key_eq
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ retainedDrawingCompleteCarrierLinks graph)
    (horizontal : link.first.isHorizontal = true)
    {crossing : CrossingRecord}
    (crossingMem : crossing ∈ retainedCrossings graph)
    (keyEqual :
      link.first.carrierKey =
        (CarrierNode.boundary
          ⟨crossing, .left⟩).carrierKey)
    (notSeparated :
      ¬ClosedGridRectanglesSeparated
        (drawingCompleteCarrierLinkRectangleLower graph link)
        (drawingCompleteCarrierLinkRectangleUpper graph link)
        (planarSATMacrocellRouteLower crossing.point)
        (planarSATMacrocellRouteUpper crossing.point)) :
    CarrierLinkIncidentToCrossover link crossing := by
  let leftBoundary : CrossingBoundary := ⟨crossing, .left⟩
  let rightBoundary : CrossingBoundary := ⟨crossing, .right⟩
  let leftNode : CarrierNode := .boundary leftBoundary
  let rightNode : CarrierNode := .boundary rightBoundary
  have leftBoundaryMem :
      leftBoundary ∈ retainedCrossingBoundaries graph := by
    apply List.mem_flatMap.mpr
    refine ⟨crossing, crossingMem, ?_⟩
    simp [leftBoundary]
  have rightBoundaryMem :
      rightBoundary ∈ retainedCrossingBoundaries graph := by
    apply List.mem_flatMap.mpr
    refine ⟨crossing, crossingMem, ?_⟩
    simp [rightBoundary]
  have leftNodeMem :
      leftNode ∈ retainedDrawingCarrierNodes graph := by
    unfold retainedDrawingCarrierNodes
    exact List.mem_append_right _
      (List.mem_map.mpr
        ⟨leftBoundary, leftBoundaryMem, rfl⟩)
  have rightNodeMem :
      rightNode ∈ retainedDrawingCarrierNodes graph := by
    unfold retainedDrawingCarrierNodes
    exact List.mem_append_right _
      (List.mem_map.mpr
        ⟨rightBoundary, rightBoundaryMem, rfl⟩)
  have overlapData :=
    retainedDrawingCompleteCarrierLink_horizontal_macrocell_overlap_data
      wellFormed degree isLocal linkMem horizontal
      crossing.point notSeparated
  have linkRaw :=
    ((mem_retainedDrawingCompleteCarrierLinks_iff
      graph link).mp linkMem).1
  rcases List.mem_flatMap.mp linkRaw with
    ⟨key, _keyMem, linkInChain⟩
  have common :=
    retainedCompleteCarrierLinks_common_key
      graph key linkInChain
  have keyEq : key = link.first.carrierKey :=
    common.1.symm
  subst key
  rcases List.mem_map.mp linkInChain with
    ⟨pair, pairMem, linkEqual⟩
  subst link
  have pairData := List.mem_filter.mp pairMem
  have pairMembers := mem_of_mem_consecutivePairs pairData.1
  have firstData :=
    (mem_retainedCompleteCarrierNodes_iff
      graph (carrierNodePairLink graph pair).first.carrierKey
      pair.1).mp pairMembers.1
  have secondData :=
    (mem_retainedCompleteCarrierNodes_iff
      graph (carrierNodePairLink graph pair).first.carrierKey
      pair.2).mp pairMembers.2
  have leftKey :
      leftNode.carrierKey =
        (carrierNodePairLink graph pair).first.carrierKey := by
    simpa [leftNode, leftBoundary, carrierNodePairLink] using
      keyEqual.symm
  have rightKey :
      rightNode.carrierKey =
        (carrierNodePairLink graph pair).first.carrierKey := by
    calc
      rightNode.carrierKey = leftNode.carrierKey := by
        change
          PeriodicGridDrawing.SegmentOccurrenceKey
              crossing.first crossing.firstTranslate =
            PeriodicGridDrawing.SegmentOccurrenceKey
              crossing.first crossing.firstTranslate
        rfl
      _ = _ := leftKey
  have leftChainMem :
      leftNode ∈ retainedCompleteCarrierNodes graph
        (carrierNodePairLink graph pair).first.carrierKey :=
    (mem_retainedCompleteCarrierNodes_iff
      graph _ leftNode).mpr ⟨leftNodeMem, leftKey⟩
  have firstHorizontal :
      pair.1.isHorizontal = true := by
    simpa [carrierNodePairLink] using horizontal
  have secondHorizontal :=
    (retainedCarrierNode_isHorizontal_iff_of_commonCarrier
      wellFormed degree isLocal firstData.1 secondData.1
      (firstData.2.trans secondData.2.symm)).mp firstHorizontal
  have firstLeftAxis :=
    retainedCarrierNode_commonCarrier_axis_data
      wellFormed degree isLocal firstData.1 leftNodeMem
      (firstData.2.trans leftKey.symm)
  have firstRightAxis :=
    retainedCarrierNode_commonCarrier_axis_data
      wellFormed degree isLocal firstData.1 rightNodeMem
      (firstData.2.trans rightKey.symm)
  have secondLeftAxis :=
    retainedCarrierNode_commonCarrier_axis_data
      wellFormed degree isLocal secondData.1 leftNodeMem
      (secondData.2.trans leftKey.symm)
  rw [if_pos firstHorizontal] at firstLeftAxis firstRightAxis
  rw [if_pos secondHorizontal] at secondLeftAxis
  have leftCoordinate :
      leftNode.orderCoordinate graph =
        planarMacroScale * crossing.point.1 + 1 := by
    simp [leftNode, leftBoundary,
      CarrierNode.orderCoordinate, CarrierNode.isHorizontal,
      CarrierNode.position, CrossingBoundary.position,
      crossingMacroOrigin, CrossingSide.localPosition,
      CrossoverVariable.position, Cell.add, Cell.scale]
  have rightCoordinate :
      rightNode.orderCoordinate graph =
        planarMacroScale * crossing.point.1 + 11 := by
    simp [rightNode, rightBoundary,
      CarrierNode.orderCoordinate, CarrierNode.isHorizontal,
      CarrierNode.position, CrossingBoundary.position,
      crossingMacroOrigin, CrossingSide.localPosition,
      CrossoverVariable.position, Cell.add, Cell.scale]
  have firstUpper :
      pair.1.orderCoordinate graph ≤
        planarMacroScale * crossing.point.1 + 13 := by
    simpa [carrierNodePairLink, CarrierNode.orderCoordinate,
      firstHorizontal] using overlapData.2.1
  have secondLower :
      planarMacroScale * crossing.point.1 ≤
        pair.2.orderCoordinate graph := by
    simpa [carrierNodePairLink, CarrierNode.orderCoordinate,
      secondHorizontal] using overlapData.2.2
  have firstMod :
      pair.1.orderCoordinate graph % 10 = 1 := by
    simpa [CarrierNode.orderCoordinate, firstHorizontal] using
      firstLeftAxis.2.1
  have leftMod :
      leftNode.orderCoordinate graph % 10 = 1 := by
    simpa [leftNode, leftBoundary, CarrierNode.orderCoordinate,
      CarrierNode.isHorizontal] using firstLeftAxis.2.2
  have rightMod :
      rightNode.orderCoordinate graph % 10 = 1 := by
    simpa [rightNode, rightBoundary, CarrierNode.orderCoordinate,
      CarrierNode.isHorizontal] using firstRightAxis.2.2
  have secondMod :
      pair.2.orderCoordinate graph % 10 = 1 := by
    simpa [CarrierNode.orderCoordinate, secondHorizontal] using
      secondLeftAxis.2.1
  have firstLeRight :
      pair.1.orderCoordinate graph ≤
        rightNode.orderCoordinate graph := by
    simp only [planarMacroScale] at firstUpper leftCoordinate rightCoordinate
    omega
  by_cases firstCoordinateEqual :
      pair.1.orderCoordinate graph =
        rightNode.orderCoordinate graph
  · have firstEqual :
        pair.1 = rightNode :=
      retainedCarrierNode_eq_of_commonCarrier_orderCoordinate_eq
        wellFormed degree isLocal firstData.1 rightNodeMem
        (firstData.2.trans rightKey.symm)
        firstCoordinateEqual
    refine ⟨.right, Or.inl ?_⟩
    simpa [rightNode, rightBoundary, carrierNodePairLink] using
      firstEqual
  · have firstLtRight :
        pair.1.orderCoordinate graph <
          rightNode.orderCoordinate graph := by
      omega
    have firstLeLeft :
        pair.1.orderCoordinate graph ≤
          leftNode.orderCoordinate graph := by
      simp only [planarMacroScale] at leftCoordinate rightCoordinate
      omega
    have leftLeSecond :
        leftNode.orderCoordinate graph ≤
          pair.2.orderCoordinate graph := by
      simp only [planarMacroScale] at secondLower leftCoordinate rightCoordinate
      omega
    by_cases secondCoordinateEqual :
        leftNode.orderCoordinate graph =
          pair.2.orderCoordinate graph
    · have secondEqual :
          leftNode = pair.2 :=
        retainedCarrierNode_eq_of_commonCarrier_orderCoordinate_eq
          wellFormed degree isLocal leftNodeMem secondData.1
          (leftKey.trans secondData.2.symm)
          secondCoordinateEqual
      refine ⟨.left, Or.inr ?_⟩
      simpa [leftNode, leftBoundary, carrierNodePairLink] using
        secondEqual.symm
    · have leftLtSecond :
          leftNode.orderCoordinate graph <
            pair.2.orderCoordinate graph := by
        omega
      have leftEqual :=
        eq_first_of_mem_consecutivePairs_of_coordinate_between
          (CarrierNode.orderCoordinate graph)
          (retainedCompleteCarrierNodes_pairwise_orderCoordinate_lt
            wellFormed degree isLocal
            (carrierNodePairLink graph pair).first.carrierKey)
          pairData.1 leftChainMem firstLeLeft leftLtSecond
      refine ⟨.left, Or.inl ?_⟩
      simpa [leftNode, leftBoundary, carrierNodePairLink] using
        leftEqual.symm

/-- A selected vertical link on a retained crossover's vertical source
occurrence is incident to that crossover whenever their rectangles are not
separated. -/
theorem
    retainedDrawingCompleteCarrierLink_incidentToCrossover_of_vertical_key_eq
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    (isLocal : graph.IsLocal)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ retainedDrawingCompleteCarrierLinks graph)
    (vertical : ¬link.first.isHorizontal = true)
    {crossing : CrossingRecord}
    (crossingMem : crossing ∈ retainedCrossings graph)
    (keyEqual :
      link.first.carrierKey =
        (CarrierNode.boundary
          ⟨crossing, .top⟩).carrierKey)
    (notSeparated :
      ¬ClosedGridRectanglesSeparated
        (drawingCompleteCarrierLinkRectangleLower graph link)
        (drawingCompleteCarrierLinkRectangleUpper graph link)
        (planarSATMacrocellRouteLower crossing.point)
        (planarSATMacrocellRouteUpper crossing.point)) :
    CarrierLinkIncidentToCrossover link crossing := by
  let topBoundary : CrossingBoundary := ⟨crossing, .top⟩
  let bottomBoundary : CrossingBoundary := ⟨crossing, .bottom⟩
  let topNode : CarrierNode := .boundary topBoundary
  let bottomNode : CarrierNode := .boundary bottomBoundary
  have topBoundaryMem :
      topBoundary ∈ retainedCrossingBoundaries graph := by
    apply List.mem_flatMap.mpr
    refine ⟨crossing, crossingMem, ?_⟩
    simp [topBoundary]
  have bottomBoundaryMem :
      bottomBoundary ∈ retainedCrossingBoundaries graph := by
    apply List.mem_flatMap.mpr
    refine ⟨crossing, crossingMem, ?_⟩
    simp [bottomBoundary]
  have topNodeMem :
      topNode ∈ retainedDrawingCarrierNodes graph := by
    unfold retainedDrawingCarrierNodes
    exact List.mem_append_right _
      (List.mem_map.mpr
        ⟨topBoundary, topBoundaryMem, rfl⟩)
  have bottomNodeMem :
      bottomNode ∈ retainedDrawingCarrierNodes graph := by
    unfold retainedDrawingCarrierNodes
    exact List.mem_append_right _
      (List.mem_map.mpr
        ⟨bottomBoundary, bottomBoundaryMem, rfl⟩)
  have overlapData :=
    retainedDrawingCompleteCarrierLink_vertical_macrocell_overlap_data
      wellFormed degree isLocal linkMem vertical
      crossing.point notSeparated
  have linkRaw :=
    ((mem_retainedDrawingCompleteCarrierLinks_iff
      graph link).mp linkMem).1
  rcases List.mem_flatMap.mp linkRaw with
    ⟨key, _keyMem, linkInChain⟩
  have common :=
    retainedCompleteCarrierLinks_common_key
      graph key linkInChain
  have keyEq : key = link.first.carrierKey :=
    common.1.symm
  subst key
  rcases List.mem_map.mp linkInChain with
    ⟨pair, pairMem, linkEqual⟩
  subst link
  have pairData := List.mem_filter.mp pairMem
  have pairMembers := mem_of_mem_consecutivePairs pairData.1
  have firstData :=
    (mem_retainedCompleteCarrierNodes_iff
      graph (carrierNodePairLink graph pair).first.carrierKey
      pair.1).mp pairMembers.1
  have secondData :=
    (mem_retainedCompleteCarrierNodes_iff
      graph (carrierNodePairLink graph pair).first.carrierKey
      pair.2).mp pairMembers.2
  have topKey :
      topNode.carrierKey =
        (carrierNodePairLink graph pair).first.carrierKey := by
    simpa [topNode, topBoundary, carrierNodePairLink] using
      keyEqual.symm
  have bottomKey :
      bottomNode.carrierKey =
        (carrierNodePairLink graph pair).first.carrierKey := by
    calc
      bottomNode.carrierKey = topNode.carrierKey := by
        change
          PeriodicGridDrawing.SegmentOccurrenceKey
              crossing.second crossing.secondTranslate =
            PeriodicGridDrawing.SegmentOccurrenceKey
              crossing.second crossing.secondTranslate
        rfl
      _ = _ := topKey
  have topChainMem :
      topNode ∈ retainedCompleteCarrierNodes graph
        (carrierNodePairLink graph pair).first.carrierKey :=
    (mem_retainedCompleteCarrierNodes_iff
      graph _ topNode).mpr ⟨topNodeMem, topKey⟩
  have firstVertical :
      ¬pair.1.isHorizontal = true := by
    simpa [carrierNodePairLink] using vertical
  have secondVertical :
      ¬pair.2.isHorizontal = true := by
    intro secondHorizontal
    exact firstVertical
      ((retainedCarrierNode_isHorizontal_iff_of_commonCarrier
        wellFormed degree isLocal firstData.1 secondData.1
        (firstData.2.trans secondData.2.symm)).mpr
          secondHorizontal)
  have firstTopAxis :=
    retainedCarrierNode_commonCarrier_axis_data
      wellFormed degree isLocal firstData.1 topNodeMem
      (firstData.2.trans topKey.symm)
  have firstBottomAxis :=
    retainedCarrierNode_commonCarrier_axis_data
      wellFormed degree isLocal firstData.1 bottomNodeMem
      (firstData.2.trans bottomKey.symm)
  have secondTopAxis :=
    retainedCarrierNode_commonCarrier_axis_data
      wellFormed degree isLocal secondData.1 topNodeMem
      (secondData.2.trans topKey.symm)
  rw [if_neg firstVertical] at firstTopAxis firstBottomAxis
  rw [if_neg secondVertical] at secondTopAxis
  have topCoordinate :
      topNode.orderCoordinate graph =
        planarMacroScale * crossing.point.2 + 1 := by
    simp [topNode, topBoundary,
      CarrierNode.orderCoordinate, CarrierNode.isHorizontal,
      CarrierNode.position, CrossingBoundary.position,
      crossingMacroOrigin, CrossingSide.localPosition,
      CrossoverVariable.position, Cell.add, Cell.scale]
  have bottomCoordinate :
      bottomNode.orderCoordinate graph =
        planarMacroScale * crossing.point.2 + 11 := by
    simp [bottomNode, bottomBoundary,
      CarrierNode.orderCoordinate, CarrierNode.isHorizontal,
      CarrierNode.position, CrossingBoundary.position,
      crossingMacroOrigin, CrossingSide.localPosition,
      CrossoverVariable.position, Cell.add, Cell.scale]
  have firstUpper :
      pair.1.orderCoordinate graph ≤
        planarMacroScale * crossing.point.2 + 13 := by
    simpa [carrierNodePairLink, CarrierNode.orderCoordinate,
      firstVertical] using overlapData.2.1
  have secondLower :
      planarMacroScale * crossing.point.2 ≤
        pair.2.orderCoordinate graph := by
    simpa [carrierNodePairLink, CarrierNode.orderCoordinate,
      secondVertical] using overlapData.2.2
  have firstMod :
      pair.1.orderCoordinate graph % 10 = 1 := by
    simpa [CarrierNode.orderCoordinate, firstVertical] using
      firstTopAxis.2.1
  have topMod :
      topNode.orderCoordinate graph % 10 = 1 := by
    simpa [topNode, topBoundary, CarrierNode.orderCoordinate,
      CarrierNode.isHorizontal] using firstTopAxis.2.2
  have bottomMod :
      bottomNode.orderCoordinate graph % 10 = 1 := by
    simpa [bottomNode, bottomBoundary, CarrierNode.orderCoordinate,
      CarrierNode.isHorizontal] using firstBottomAxis.2.2
  have secondMod :
      pair.2.orderCoordinate graph % 10 = 1 := by
    simpa [CarrierNode.orderCoordinate, secondVertical] using
      secondTopAxis.2.1
  have firstLeBottom :
      pair.1.orderCoordinate graph ≤
        bottomNode.orderCoordinate graph := by
    simp only [planarMacroScale] at firstUpper topCoordinate bottomCoordinate
    omega
  by_cases firstCoordinateEqual :
      pair.1.orderCoordinate graph =
        bottomNode.orderCoordinate graph
  · have firstEqual :
        pair.1 = bottomNode :=
      retainedCarrierNode_eq_of_commonCarrier_orderCoordinate_eq
        wellFormed degree isLocal firstData.1 bottomNodeMem
        (firstData.2.trans bottomKey.symm)
        firstCoordinateEqual
    refine ⟨.bottom, Or.inl ?_⟩
    simpa [bottomNode, bottomBoundary, carrierNodePairLink] using
      firstEqual
  · have firstLtBottom :
        pair.1.orderCoordinate graph <
          bottomNode.orderCoordinate graph := by
      omega
    have firstLeTop :
        pair.1.orderCoordinate graph ≤
          topNode.orderCoordinate graph := by
      simp only [planarMacroScale] at topCoordinate bottomCoordinate
      omega
    have topLeSecond :
        topNode.orderCoordinate graph ≤
          pair.2.orderCoordinate graph := by
      simp only [planarMacroScale] at secondLower topCoordinate bottomCoordinate
      omega
    by_cases secondCoordinateEqual :
        topNode.orderCoordinate graph =
          pair.2.orderCoordinate graph
    · have secondEqual :
          topNode = pair.2 :=
        retainedCarrierNode_eq_of_commonCarrier_orderCoordinate_eq
          wellFormed degree isLocal topNodeMem secondData.1
          (topKey.trans secondData.2.symm)
          secondCoordinateEqual
      refine ⟨.top, Or.inr ?_⟩
      simpa [topNode, topBoundary, carrierNodePairLink] using
        secondEqual.symm
    · have topLtSecond :
          topNode.orderCoordinate graph <
            pair.2.orderCoordinate graph := by
        omega
      have topEqual :=
        eq_first_of_mem_consecutivePairs_of_coordinate_between
          (CarrierNode.orderCoordinate graph)
          (retainedCompleteCarrierNodes_pairwise_orderCoordinate_lt
            wellFormed degree isLocal
            (carrierNodePairLink graph pair).first.carrierKey)
          pairData.1 topChainMem firstLeTop topLtSecond
      refine ⟨.top, Or.inl ?_⟩
      simpa [topNode, topBoundary, carrierNodePairLink] using
        topEqual.symm

end PeriodicOrthocrossing
end LeanTrominoes
