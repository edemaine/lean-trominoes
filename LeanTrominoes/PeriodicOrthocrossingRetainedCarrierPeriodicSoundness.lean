/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierRepresentativeMembership
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATPeriodicization
import LeanTrominoes.PeriodicCNFPlanarPeriodicCompleteness

/-!
# Periodic soundness of retained carrier links

The retained finite formula contains only one owned representative of each
periodic straight-carrier equality.  This file transfers that finite equality
back to every raw neighboring physical link.  The key bookkeeping fact is
that translating a physical carrier node is equivalent to translating the
finite assignment at which its normalized periodic variable is evaluated.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Carrier-node normalization inside the combined planar-SAT variable type
is exactly carrier-only normalization followed by the canonical embedding. -/
theorem normalizePlanarSATVariable_carrier
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable) (node : CarrierNode) :
    normalizePlanarSATVariable formula (.inl (.carrier node)) =
      (@periodicCarrierNodeToPlanarSATVariable Variable
          (normalizeCarrierNode
            (PeriodicCNF.incidenceGraph formula) node).1,
        (normalizeCarrierNode
          (PeriodicCNF.incidenceGraph formula) node).2) := by
  cases node <;> rfl

/-- Evaluating a translated physical carrier node at one finite-block
translate is the same as evaluating the original node at the sum of the two
translations. -/
theorem planarSATFiniteAssignmentAt_carrier_periodTranslate
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment :
      PeriodicPlanarSATVariable Variable → Cell → Bool)
    (translate shift : Cell) (node : CarrierNode) :
    planarSATFiniteAssignmentAt formula assignment translate
        (.inl (.carrier
          (node.periodTranslate
            (PeriodicCNF.incidenceGraph formula) shift))) =
      planarSATFiniteAssignmentAt formula assignment
        (Cell.add translate shift) (.inl (.carrier node)) := by
  let graph := PeriodicCNF.incidenceGraph formula
  unfold planarSATFiniteAssignmentAt
  rw [normalizePlanarSATVariable_carrier,
    normalizePlanarSATVariable_carrier,
    normalizeCarrierNode_periodTranslate]
  apply congrArg
    (assignment
      (@periodicCarrierNodeToPlanarSATVariable Variable
        (normalizeCarrierNode graph node).1))
  rcases translate with ⟨translateX, translateY⟩
  rcases shift with ⟨shiftX, shiftY⟩
  rcases (normalizeCarrierNode graph node).2 with
    ⟨offsetX, offsetY⟩
  apply Prod.ext <;> simp [Cell.add] <;> omega

/-- A satisfying retained periodic formula enforces the equality belonging
to every raw retained link whose first endpoint lies in the neighboring
source window, even when that physical link is not itself the selected
finite representative. -/
theorem retainedDrawingCompleteCarrierLink_assignment_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (assignment :
      PeriodicPlanarSATVariable Variable → Cell → Bool)
    (satisfies :
      (retainedDrawingPeriodicPlanarSATFormula formula).Satisfies
        assignment)
    (translate : Cell)
    {link : EqualityLink CarrierNode}
    (linkMem :
      link ∈ retainedDrawingCompleteCarrierLinksRaw
        (PeriodicCNF.incidenceGraph formula))
    (sourceNeighbor :
      IsNeighborTranslation link.first.translate) :
    planarSATFiniteAssignmentAt formula assignment translate
        (.inl (.carrier link.first)) =
      planarSATFiniteAssignmentAt formula assignment translate
        (.inl (.carrier link.second)) := by
  let graph := PeriodicCNF.incidenceGraph formula
  let correction :=
    carrierLinkRepresentativeCorrection graph link
  let representative :=
    carrierLinkPeriodTranslate graph link correction
  have representativeMem :
      representative ∈ retainedDrawingCompleteCarrierLinks graph := by
    exact
      retainedDrawingCompleteCarrierLink_representativeCorrection_mem
        wellFormed degree isLocal linkMem sourceNeighbor
  let representativeTranslate := Cell.sub translate correction
  let finiteAssignment :=
    planarSATFiniteAssignmentAt formula assignment
      representativeTranslate
  have finiteHolds :
      FormulaHolds finiteAssignment
        (retainedDrawingPlanarSATFormula formula) := by
    exact
      (retainedDrawingPeriodicPlanarSATFormula_satisfies_iff
        formula assignment).mp satisfies representativeTranslate
  have coreHolds :
      FormulaHolds
          (finiteAssignment ∘ planarSATCoreVariableMap)
          (retainedDrawingRoutePlanarCoreFormula graph) :=
    (retainedDrawingPlanarSATFormula_holds_iff
      formula finiteAssignment).mp finiteHolds |>.1
  have wireHolds :
      FormulaHolds
          ((finiteAssignment ∘ planarSATCoreVariableMap) ∘ Sum.inl)
          (retainedDrawingRouteWireFormula graph) :=
    (retainedDrawingRoutePlanarCoreFormula_holds_iff
      graph (finiteAssignment ∘ planarSATCoreVariableMap)).mp
        coreHolds |>.2
  have carrierHolds :
      FormulaHolds
          ((finiteAssignment ∘ planarSATCoreVariableMap) ∘ Sum.inl)
          (retainedDrawingCompleteCarrierFormula graph) := by
    exact
      (formulaHolds_route_append_iff
        ((finiteAssignment ∘ planarSATCoreVariableMap) ∘ Sum.inl)
        (retainedDrawingCompleteCarrierFormula graph)
        (drawingRouteBendFormula graph)).mp
          (by simpa [retainedDrawingRouteWireFormula] using wireHolds) |>.1
  have representativeEq :
      finiteAssignment (.inl (.carrier representative.first)) =
        finiteAssignment (.inl (.carrier representative.second)) := by
    have laws :=
      (equalityFamily_holds_iff
        (((finiteAssignment ∘ planarSATCoreVariableMap) ∘ Sum.inl))
        (retainedDrawingCompleteCarrierLinks graph)).mp
          (by
            simpa [retainedDrawingCompleteCarrierFormula] using
              carrierHolds)
    simpa [Function.comp_def, planarSATCoreVariableMap] using
      laws representative representativeMem
  have translateBack :
      Cell.add representativeTranslate correction = translate := by
    rcases translate with ⟨translateX, translateY⟩
    rcases correction with ⟨correctionX, correctionY⟩
    simp [representativeTranslate, Cell.add, Cell.sub]
  have firstBack :
      finiteAssignment (.inl (.carrier representative.first)) =
        planarSATFiniteAssignmentAt formula assignment translate
          (.inl (.carrier link.first)) := by
    change
      planarSATFiniteAssignmentAt formula assignment
          representativeTranslate
          (.inl (.carrier
            (link.first.periodTranslate graph correction))) =
        _
    rw [planarSATFiniteAssignmentAt_carrier_periodTranslate,
      translateBack]
  have secondBack :
      finiteAssignment (.inl (.carrier representative.second)) =
        planarSATFiniteAssignmentAt formula assignment translate
          (.inl (.carrier link.second)) := by
    change
      planarSATFiniteAssignmentAt formula assignment
          representativeTranslate
          (.inl (.carrier
            (link.second.periodTranslate graph correction))) =
        _
    rw [planarSATFiniteAssignmentAt_carrier_periodTranslate,
      translateBack]
  exact firstBack.symm.trans (representativeEq.trans secondBack)

/-- A satisfying retained periodic formula propagates both signals through
every retained physical crossover, including noncanonical period translates
that do not themselves occur in the finite crossover family. -/
theorem retainedCrossing_assignment_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment :
      PeriodicPlanarSATVariable Variable → Cell → Bool)
    (satisfies :
      (retainedDrawingPeriodicPlanarSATFormula formula).Satisfies
        assignment)
    (translate : Cell)
    {crossing : CrossingRecord}
    (crossingMem :
      crossing ∈ retainedCrossings
        (PeriodicCNF.incidenceGraph formula)) :
    let finiteAssignment :=
      planarSATFiniteAssignmentAt formula assignment translate
    finiteAssignment
          (.inl (.carrier (.boundary ⟨crossing, .left⟩))) =
        finiteAssignment
          (.inl (.carrier (.boundary ⟨crossing, .right⟩))) ∧
      finiteAssignment
          (.inl (.carrier (.boundary ⟨crossing, .top⟩))) =
        finiteAssignment
          (.inl (.carrier (.boundary ⟨crossing, .bottom⟩))) := by
  let graph := PeriodicCNF.incidenceGraph formula
  let shift := crossingPeriodShift graph crossing
  let canonical := crossing.periodNormalize graph
  let canonicalTranslate := Cell.add translate shift
  let canonicalAssignment :=
    planarSATFiniteAssignmentAt formula assignment
      canonicalTranslate
  have canonicalMem :
      canonical ∈ orientedCrossingHalo graph :=
    orientedCrossings_subset_orientedCrossingHalo graph
      (retainedCrossing_periodNormalize_mem_orientedCrossings
        graph crossingMem)
  have canonicalHolds :
      FormulaHolds canonicalAssignment
        (retainedDrawingPlanarSATFormula formula) :=
    (retainedDrawingPeriodicPlanarSATFormula_satisfies_iff
      formula assignment).mp satisfies canonicalTranslate
  have coreHolds :
      FormulaHolds
          (canonicalAssignment ∘ planarSATCoreVariableMap)
          (retainedDrawingRoutePlanarCoreFormula graph) :=
    (retainedDrawingPlanarSATFormula_holds_iff
      formula canonicalAssignment).mp canonicalHolds |>.1
  have crossoverHolds :
      FormulaHolds
          (canonicalAssignment ∘ planarSATCoreVariableMap)
          (drawingCarrierNodeCrossoverFormula graph) :=
    (retainedDrawingRoutePlanarCoreFormula_holds_iff
      graph
      (canonicalAssignment ∘ planarSATCoreVariableMap)).mp
        coreHolds |>.1
  have canonicalLaws :
      canonicalAssignment
            (.inl (.carrier (.boundary ⟨canonical, .left⟩))) =
          canonicalAssignment
            (.inl (.carrier (.boundary ⟨canonical, .right⟩))) ∧
        canonicalAssignment
            (.inl (.carrier (.boundary ⟨canonical, .top⟩))) =
          canonicalAssignment
            (.inl (.carrier (.boundary ⟨canonical, .bottom⟩))) := by
    have laws :=
      crossoverFamily_boundary_eq
        (canonicalAssignment ∘ planarSATCoreVariableMap)
        (orientedCrossingHalo graph)
        carrierNodeCrossingPorts crossingMacroOrigin 1
        crossoverHolds canonical canonicalMem
    simpa [Function.comp_def, planarSATCoreVariableMap,
      carrierNodeCrossingPorts] using laws
  have boundaryBack (side : CrossingSide) :
      planarSATFiniteAssignmentAt formula assignment translate
          (.inl (.carrier (.boundary ⟨crossing, side⟩))) =
        canonicalAssignment
          (.inl (.carrier (.boundary ⟨canonical, side⟩))) := by
    have translated :=
      planarSATFiniteAssignmentAt_carrier_periodTranslate
        formula assignment translate shift
        (.boundary (⟨canonical, side⟩ : CrossingBoundary))
    simpa [graph, shift, canonical, canonicalTranslate,
      canonicalAssignment, CarrierNode.periodTranslate,
      CrossingBoundary.periodTranslate,
      CrossingRecord.periodNormalize_periodTranslate_shift] using
        translated
  constructor
  · exact
      (boundaryBack .left).trans
        (canonicalLaws.1.trans (boundaryBack .right).symm)
  · exact
      (boundaryBack .top).trans
        (canonicalLaws.2.trans (boundaryBack .bottom).symm)

/-- Two ports of one retained physical crossover have equal values whenever
they lie on the same straight carrier. -/
theorem
    retainedCrossingBoundary_assignment_eq_of_common_carrier
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment :
      PeriodicPlanarSATVariable Variable → Cell → Bool)
    (satisfies :
      (retainedDrawingPeriodicPlanarSATFormula formula).Satisfies
        assignment)
    (translate : Cell)
    (crossing : CrossingRecord)
    (crossingMem :
      crossing ∈ retainedCrossings
        (PeriodicCNF.incidenceGraph formula))
    (firstSide secondSide : CrossingSide)
    (commonCarrier :
      (CrossingBoundary.mk crossing firstSide).carrierKey =
        (CrossingBoundary.mk crossing secondSide).carrierKey) :
    planarSATFiniteAssignmentAt formula assignment translate
          (.inl (.carrier
            (.boundary ⟨crossing, firstSide⟩))) =
      planarSATFiniteAssignmentAt formula assignment translate
          (.inl (.carrier
            (.boundary ⟨crossing, secondSide⟩))) := by
  let graph := PeriodicCNF.incidenceGraph formula
  have laws :=
    retainedCrossing_assignment_eq
      formula assignment satisfies translate crossingMem
  have canonicalMem :
      crossing.periodNormalize graph ∈
        orientedCrossingHalo graph :=
    orientedCrossings_subset_orientedCrossingHalo graph
      (retainedCrossing_periodNormalize_mem_orientedCrossings
        graph crossingMem)
  have differentCanonical :
      PeriodicGridDrawing.SegmentOccurrenceKey
          (crossing.periodNormalize graph).first
          (crossing.periodNormalize graph).firstTranslate ≠
        PeriodicGridDrawing.SegmentOccurrenceKey
          (crossing.periodNormalize graph).second
          (crossing.periodNormalize graph).secondTranslate :=
    (orientedCrossingHalo_sound graph canonicalMem).2.2.2.2.1
  have different :
      PeriodicGridDrawing.SegmentOccurrenceKey
          crossing.first crossing.firstTranslate ≠
        PeriodicGridDrawing.SegmentOccurrenceKey
          crossing.second crossing.secondTranslate := by
    intro equal
    apply differentCanonical
    have shiftedEqual :=
      congrArg
        (fun key : Nat × Nat × Cell =>
          (key.1, key.2.1,
            Cell.sub key.2.2
              (crossingPeriodShift graph crossing)))
        equal
    simpa [PeriodicGridDrawing.SegmentOccurrenceKey,
      CrossingRecord.periodNormalize] using shiftedEqual
  cases firstSide <;> cases secondSide <;>
    simp only [CrossingBoundary.carrierKey] at commonCarrier
  · rfl
  · exact laws.1
  · exact (different commonCarrier).elim
  · exact (different commonCarrier).elim
  · exact laws.1.symm
  · rfl
  · exact (different commonCarrier).elim
  · exact (different commonCarrier).elim
  · exact (different commonCarrier.symm).elim
  · exact (different commonCarrier.symm).elim
  · rfl
  · exact laws.2
  · exact (different commonCarrier.symm).elim
  · exact (different commonCarrier.symm).elim
  · exact laws.2.symm
  · rfl

/-- Every consecutive pair in one retained physical carrier chain has equal
values.  An explicit raw link is handled through its selected representative;
the omitted same-site pair is handled by the retained crossover gadget law. -/
theorem retainedCompleteCarrierConsecutivePair_assignment_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (assignment :
      PeriodicPlanarSATVariable Variable → Cell → Bool)
    (satisfies :
      (retainedDrawingPeriodicPlanarSATFormula formula).Satisfies
        assignment)
    (translate : Cell)
    (key : Nat × Nat × Cell)
    (keyNeighbor : IsNeighborTranslation key.2.2)
    (pair : CarrierNode × CarrierNode)
    (pairMem :
      pair ∈ consecutivePairs
        (retainedCompleteCarrierNodes
          (PeriodicCNF.incidenceGraph formula) key)) :
    planarSATFiniteAssignmentAt formula assignment translate
          (.inl (.carrier pair.1)) =
      planarSATFiniteAssignmentAt formula assignment translate
          (.inl (.carrier pair.2)) := by
  let graph := PeriodicCNF.incidenceGraph formula
  have members := mem_of_mem_consecutivePairs pairMem
  have firstData :=
    (mem_retainedCompleteCarrierNodes_iff
      graph key pair.1).mp members.1
  have secondData :=
    (mem_retainedCompleteCarrierNodes_iff
      graph key pair.2).mp members.2
  have firstTranslateEq : pair.1.translate = key.2.2 := by
    have keyEq := firstData.2
    rw [CarrierNode.carrierKey_eq_indexed_translate] at keyEq
    exact congrArg (fun value : Nat × Nat × Cell => value.2.2)
      keyEq
  have firstNeighbor :
      IsNeighborTranslation pair.1.translate := by
    rw [firstTranslateEq]
    exact keyNeighbor
  by_cases sameSite : pair.1.sameCrossoverSite pair.2
  · rcases pair with ⟨first, second⟩
    cases first with
    | terminal firstTerminal =>
        simp [CarrierNode.sameCrossoverSite] at sameSite
    | boundary firstBoundary =>
        cases second with
        | terminal secondTerminal =>
            simp [CarrierNode.sameCrossoverSite] at sameSite
        | boundary secondBoundary =>
            rcases firstBoundary with
              ⟨firstCrossing, firstSide⟩
            rcases secondBoundary with
              ⟨secondCrossing, secondSide⟩
            have crossingEq :
                firstCrossing = secondCrossing := by
              simpa [CarrierNode.sameCrossoverSite] using sameSite
            subst secondCrossing
            have boundaryMem :
                (CrossingBoundary.mk firstCrossing firstSide) ∈
                  retainedCrossingBoundaries graph := by
              unfold retainedDrawingCarrierNodes at firstData
              simpa using firstData.1
            exact
              retainedCrossingBoundary_assignment_eq_of_common_carrier
                formula assignment satisfies translate firstCrossing
                (retainedCrossingBoundary_crossing_mem
                  graph boundaryMem)
                firstSide secondSide
                (firstData.2.trans secondData.2.symm)
  · have keyMem :
        key ∈ retainedDrawingCompleteCarrierKeys graph := by
      simp only [retainedDrawingCompleteCarrierKeys,
        List.mem_dedup, List.mem_map]
      exact ⟨pair.1, firstData.1, firstData.2⟩
    have localLinkMem :
        carrierNodePairLink graph pair ∈
          retainedCompleteCarrierLinks graph key := by
      apply List.mem_map.mpr
      refine ⟨pair, ?_, rfl⟩
      exact List.mem_filter.mpr
        ⟨pairMem, by simp [sameSite]⟩
    apply
      retainedDrawingCompleteCarrierLink_assignment_eq
        formula wellFormed degree isLocal assignment satisfies
        translate
        (link := carrierNodePairLink graph pair)
    · exact List.mem_flatMap.mpr
        ⟨key, keyMem, localLinkMem⟩
    · simpa [carrierNodePairLink] using firstNeighbor

/-- Every two nodes on one neighboring retained physical carrier receive the
same value under a satisfying periodic assignment. -/
theorem retainedCompleteCarrierNodes_assignment_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (assignment :
      PeriodicPlanarSATVariable Variable → Cell → Bool)
    (satisfies :
      (retainedDrawingPeriodicPlanarSATFormula formula).Satisfies
        assignment)
    (translate : Cell)
    (key : Nat × Nat × Cell)
    (keyNeighbor : IsNeighborTranslation key.2.2)
    {first second : CarrierNode}
    (firstMem :
      first ∈ retainedCompleteCarrierNodes
        (PeriodicCNF.incidenceGraph formula) key)
    (secondMem :
      second ∈ retainedCompleteCarrierNodes
        (PeriodicCNF.incidenceGraph formula) key) :
    planarSATFiniteAssignmentAt formula assignment translate
          (.inl (.carrier first)) =
      planarSATFiniteAssignmentAt formula assignment translate
          (.inl (.carrier second)) := by
  exact
    assignment_eq_of_consecutivePairs
      (fun node =>
        planarSATFiniteAssignmentAt formula assignment translate
          (.inl (.carrier node)))
      (retainedCompleteCarrierNodes
        (PeriodicCNF.incidenceGraph formula) key)
      (retainedCompleteCarrierConsecutivePair_assignment_eq
        formula wellFormed degree isLocal assignment satisfies
        translate key keyNeighbor)
      first firstMem second secondMem

/-- The start and finish terminals of every listed neighboring segment
occurrence carry the same value under a satisfying retained periodic
formula. -/
theorem retainedSegmentOccurrenceTerminals_assignment_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed :
      (PeriodicCNF.incidenceGraph formula).IsWellFormed)
    (degree :
      (PeriodicCNF.incidenceGraph formula).DegreeAtMost 3)
    (isLocal :
      (PeriodicCNF.incidenceGraph formula).IsLocal)
    (assignment :
      PeriodicPlanarSATVariable Variable → Cell → Bool)
    (satisfies :
      (retainedDrawingPeriodicPlanarSATFormula formula).Satisfies
        assignment)
    (blockTranslate : Cell)
    (indexed : IndexedGridSegment)
    (indexedMem :
      indexed ∈
        (drawing
          (PeriodicCNF.incidenceGraph formula)).indexedSegments)
    (translate : Cell)
    (translateNeighbor : IsNeighborTranslation translate) :
    planarSATFiniteAssignmentAt formula assignment blockTranslate
          (.inl (.carrier
            (.terminal ⟨indexed, translate, .start⟩))) =
      planarSATFiniteAssignmentAt formula assignment blockTranslate
          (.inl (.carrier
            (.terminal ⟨indexed, translate, .finish⟩))) := by
  let graph := PeriodicCNF.incidenceGraph formula
  let startTerminal : SegmentTerminal :=
    ⟨indexed, translate, .start⟩
  let finishTerminal : SegmentTerminal :=
    ⟨indexed, translate, .finish⟩
  have occurrenceMem :
      (indexed, translate) ∈ neighborOccurrences graph :=
    (mem_neighborOccurrences_iff graph _).mpr
      ⟨indexedMem, translateNeighbor⟩
  have startTerminalMem :
      startTerminal ∈ drawingSegmentTerminals graph := by
    apply List.mem_flatMap.mpr
    refine ⟨(indexed, translate), occurrenceMem, ?_⟩
    simp [occurrenceTerminals, startTerminal]
  have finishTerminalMem :
      finishTerminal ∈ drawingSegmentTerminals graph := by
    apply List.mem_flatMap.mpr
    refine ⟨(indexed, translate), occurrenceMem, ?_⟩
    simp [occurrenceTerminals, finishTerminal]
  have startNodeMem :
      CarrierNode.terminal startTerminal ∈
        retainedCompleteCarrierNodes graph
          startTerminal.carrierKey := by
    apply
      (mem_retainedCompleteCarrierNodes_iff
        graph startTerminal.carrierKey _).mpr
    constructor
    · apply List.mem_append_left
      exact List.mem_map.mpr
        ⟨startTerminal, startTerminalMem, rfl⟩
    · rfl
  have finishNodeMem :
      CarrierNode.terminal finishTerminal ∈
        retainedCompleteCarrierNodes graph
          startTerminal.carrierKey := by
    apply
      (mem_retainedCompleteCarrierNodes_iff
        graph startTerminal.carrierKey _).mpr
    constructor
    · apply List.mem_append_left
      exact List.mem_map.mpr
        ⟨finishTerminal, finishTerminalMem, rfl⟩
    · rfl
  have keyNeighbor :
      IsNeighborTranslation startTerminal.carrierKey.2.2 := by
    simpa [startTerminal, SegmentTerminal.carrierKey,
      PeriodicGridDrawing.SegmentOccurrenceKey] using translateNeighbor
  exact
    retainedCompleteCarrierNodes_assignment_eq
      formula wellFormed degree isLocal assignment satisfies
      blockTranslate startTerminal.carrierKey keyNeighbor
      startNodeMem finishNodeMem

end PeriodicOrthocrossing
end LeanTrominoes
