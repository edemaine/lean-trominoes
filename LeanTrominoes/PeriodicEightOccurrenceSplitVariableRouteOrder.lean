/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicEightOccurrenceSplitCycleBlockIndex
import LeanTrominoes.PeriodicEightOccurrenceSplitCanonicalAngularRoutes
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceFanRouteOrder

/-!
# Fixed-eight variable route order

The copied source incidence of every degree-three split variable is followed
in presentation order by its two implication-ring incidences.  This file
joins the global occurrence indexing to the local Figure 7 direction
certificate, proving that the actual angular-spliced routes occur clockwise
in exactly that order.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplitPositioned

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

/-- Presentation-order occurrence lookup is independent of the chosen
correct equality decision procedure. -/
theorem occurrenceAt_eq_of_decidableEq
    {Variable : Type*}
    (firstEq secondEq : DecidableEq Variable)
    (source : PeriodicCNF Variable)
    (atom : Variable)
    (slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot) :
    @PeriodicOneInThreeToThreeDM.occurrenceAt
        Variable firstEq source atom slot =
      @PeriodicOneInThreeToThreeDM.occurrenceAt
        Variable secondEq source atom slot := by
  unfold PeriodicOneInThreeToThreeDM.occurrenceAt
    PeriodicOneInThreeToThreeDM.occurrencesOf
  apply congrArg (fun occurrences => occurrences[slot.index]?)
  generalize taggedLiterals source = occurrences
  induction occurrences with
  | nil =>
      rfl
  | cons head rest induction =>
      have decisionEqual :
          @decide (head.1.atom = atom) (firstEq _ _) =
            @decide (head.1.atom = atom) (secondEq _ _) := by
        apply Bool.eq_iff_iff.mpr
        simp
      simp only [List.filter_cons]
      rw [decisionEqual, induction]

/-- A filtered copied-source occurrence retains the positioned source clause
and literal at the same presentation indices. -/
theorem copiedSourceOccurrence_metadata
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (occurrencePorts : OccurrencePorts)
    (output : ThreeOccurrenceVariable Variable)
    (tagged :
      PeriodicOneInThreeToThreeDM.TaggedOccurrence
        (ThreeOccurrenceVariable Variable))
    (taggedMember :
      tagged ∈ copiedSourceOccurrencesOf
        source.erase occurrencePorts output) :
    ∃ sourceClause sourceLiteral,
      (sourceClause, tagged.2.1) ∈ source.clauses.zipIdx ∧
      (sourceLiteral, tagged.2.2) ∈
        sourceClause.literals.zipIdx ∧
      tagged.1 =
        PeriodicEightOccurrenceSplit.occurrenceLiteral
          occurrencePorts tagged.2.1 tagged.2.2 sourceLiteral ∧
      tagged.1.atom = output := by
  have filteredMember :
      tagged ∈
        PeriodicThreeSATThree.taggedLiterals
          (PeriodicCNF.mk
            (PeriodicEightOccurrenceSplit.occurrenceClauses
              source.erase occurrencePorts)) :=
    (List.mem_filter.mp taggedMember).1
  have taggedAtom : tagged.1.atom = output := by
    simpa using (List.mem_filter.mp taggedMember).2
  unfold PeriodicThreeSATThree.taggedLiterals at filteredMember
  rcases List.mem_flatMap.mp filteredMember with
    ⟨taggedClause, taggedClauseMember, literalMappedMember⟩
  rcases List.mem_map.mp literalMappedMember with
    ⟨taggedLiteral, taggedLiteralMember, taggedEqual⟩
  have positionedClauseMember :
      (taggedClause.1, taggedClause.2) ∈
        ((occurrenceClauses source occurrencePorts).map
          PositionedPeriodicClause.literals).zipIdx := by
    simpa using taggedClauseMember
  rw [List.zipIdx_map] at positionedClauseMember
  rcases List.mem_map.mp positionedClauseMember with
    ⟨positionedTaggedClause, positionedTaggedClauseMember,
      positionedTaggedClauseEqual⟩
  have clauseIndexEqual :
      positionedTaggedClause.2 = taggedClause.2 :=
    congrArg Prod.snd positionedTaggedClauseEqual
  have clauseLiteralsEqual :
      positionedTaggedClause.1.literals = taggedClause.1 :=
    congrArg Prod.fst positionedTaggedClauseEqual
  have positionedLiteralMember :
      (taggedLiteral.1, taggedLiteral.2) ∈
        positionedTaggedClause.1.literals.zipIdx := by
    simpa [clauseLiteralsEqual] using taggedLiteralMember
  rcases occurrenceMetadata_of_members source occurrencePorts
      (by simpa [clauseIndexEqual] using positionedTaggedClauseMember)
      positionedLiteralMember with
    ⟨metadata, sourceLiteral, _metadataClauseEqual,
      _metadataIndex, sourceClauseMember, sourceLiteralMember,
      copiedLiteralEqual⟩
  have taggedLiteralEqual : taggedLiteral.1 = tagged.1 :=
    congrArg (fun occurrence => occurrence.1) taggedEqual
  have taggedClauseIndexEqual : taggedClause.2 = tagged.2.1 :=
    congrArg (fun occurrence => occurrence.2.1) taggedEqual
  have taggedLiteralIndexEqual : taggedLiteral.2 = tagged.2.2 :=
    congrArg (fun occurrence => occurrence.2.2) taggedEqual
  refine ⟨metadata.sourceClause, sourceLiteral, ?_, ?_, ?_, taggedAtom⟩
  · simpa [clauseIndexEqual, taggedClauseIndexEqual] using
      sourceClauseMember
  · simpa [taggedLiteralIndexEqual] using sourceLiteralMember
  · simpa [taggedLiteralEqual, clauseIndexEqual,
      taggedClauseIndexEqual, taggedLiteralIndexEqual] using
      copiedLiteralEqual

/-- Angular-spliced fixed-eight routes end around every degree-three output
variable in source-spoke, incoming-ring, outgoing-ring clockwise order. -/
theorem angularSplicedIncidenceRoutes_variableRoutesInOccurrenceOrder
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order : OccurrenceOrder source.erase)
    (fits : FitsEightSlots order)
    (boundary :
      AngularBoundaryRoutes source sourcePlacement order) :
    PositionedPeriodicCNF.VariableRoutesInOccurrenceOrder
      (formula source sourcePlacement
        (occurrencePortsOfAngularOrder source.erase order))
      (angularSplicedIncidenceRoutes
        source sourcePlacement order boundary) := by
  intro output first second third
    firstLookup secondLookup thirdLookup
  let occurrencePorts :=
    occurrencePortsOfAngularOrder source.erase order
  have collisionFree :
      occurrencePorts.CollisionFree source.erase :=
    occurrencePortsOfAngularOrder_collisionFree
      source.erase order fits
  have firstLookupCurrent :
      PeriodicOneInThreeToThreeDM.occurrenceAt
          (PeriodicEightOccurrenceSplit.formula
            source.erase occurrencePorts)
          output .first = some first := by
    unfold PeriodicPlanarOneInThreeToThreeDM.occurrenceAt at firstLookup
    simpa [occurrencePorts] using firstLookup
  have secondLookupCurrent :
      PeriodicOneInThreeToThreeDM.occurrenceAt
          (PeriodicEightOccurrenceSplit.formula
            source.erase occurrencePorts)
          output .second = some second := by
    unfold PeriodicPlanarOneInThreeToThreeDM.occurrenceAt at secondLookup
    simpa [occurrencePorts] using secondLookup
  have thirdLookupCurrent :
      PeriodicOneInThreeToThreeDM.occurrenceAt
          (PeriodicEightOccurrenceSplit.formula
            source.erase occurrencePorts)
          output .third = some third := by
    unfold PeriodicPlanarOneInThreeToThreeDM.occurrenceAt at thirdLookup
    simpa [occurrencePorts] using thirdLookup
  have firstLookupSemantic :
      @PeriodicOneInThreeToThreeDM.occurrenceAt
          (ThreeOccurrenceVariable Variable)
          (fun left right => instDecidableEqProd left right)
          (PeriodicEightOccurrenceSplit.formula
            source.erase occurrencePorts)
          output .first = some first := by
    rw [← occurrenceAt_eq_of_decidableEq
      (inferInstance :
        DecidableEq (ThreeOccurrenceVariable Variable))
      (fun left right => instDecidableEqProd left right)
      (PeriodicEightOccurrenceSplit.formula
        source.erase occurrencePorts)
      output .first]
    exact firstLookupCurrent
  have secondLookupSemantic :
      @PeriodicOneInThreeToThreeDM.occurrenceAt
          (ThreeOccurrenceVariable Variable)
          (fun left right => instDecidableEqProd left right)
          (PeriodicEightOccurrenceSplit.formula
            source.erase occurrencePorts)
          output .second = some second := by
    rw [← occurrenceAt_eq_of_decidableEq
      (inferInstance :
        DecidableEq (ThreeOccurrenceVariable Variable))
      (fun left right => instDecidableEqProd left right)
      (PeriodicEightOccurrenceSplit.formula
        source.erase occurrencePorts)
      output .second]
    exact secondLookupCurrent
  have thirdLookupSemantic :
      @PeriodicOneInThreeToThreeDM.occurrenceAt
          (ThreeOccurrenceVariable Variable)
          (fun left right => instDecidableEqProd left right)
          (PeriodicEightOccurrenceSplit.formula
            source.erase occurrencePorts)
          output .third = some third := by
    rw [← occurrenceAt_eq_of_decidableEq
      (inferInstance :
        DecidableEq (ThreeOccurrenceVariable Variable))
      (fun left right => instDecidableEqProd left right)
      (PeriodicEightOccurrenceSplit.formula
        source.erase occurrencePorts)
      output .third]
    exact thirdLookupCurrent
  have decomposition :=
    occurrenceAt_three_decomposition
      source.erase occurrencePorts collisionFree
      output first second third
      firstLookupSemantic secondLookupSemantic
      thirdLookupSemantic
  have firstMember :
      first ∈ copiedSourceOccurrencesOf
        source.erase occurrencePorts output := by
    rw [decomposition.1]
    simp
  rcases copiedSourceOccurrence_metadata
      source occurrencePorts output first firstMember with
    ⟨sourceClause, sourceLiteral,
      sourceClauseMember, sourceLiteralMember,
      firstLiteralEqual, firstAtomEqual⟩
  let port : Port :=
    occurrencePorts.port first.2.1 first.2.2
  have outputEqual :
      output = copy sourceLiteral.atom port := by
    rw [← firstAtomEqual, firstLiteralEqual]
    rfl
  have sourceTaggedMember :
      (sourceLiteral, first.2.1, first.2.2) ∈
        taggedLiterals source.erase :=
    taggedLiteral_mem_of_positioned_members
      source sourceClauseMember sourceLiteralMember
  have atomMember :
      sourceLiteral.atom ∈ sourceVariables source.erase :=
    sourceVariables_mem source.erase sourceTaggedMember
  have occurrenceClausesLength :
      (PeriodicEightOccurrenceSplit.occurrenceClauses
          source.erase occurrencePorts).length =
        (occurrenceClauses source occurrencePorts).length := by
    calc
      _ =
          ((occurrenceClauses source occurrencePorts).map
            PositionedPeriodicClause.literals).length :=
        congrArg List.length
          (occurrenceClauses_literals
            source occurrencePorts).symm
      _ = (occurrenceClauses source occurrencePorts).length :=
        List.length_map PositionedPeriodicClause.literals
  have cyclePairIndices :
      [(second.2.1, second.2.2),
        (third.2.1, third.2.2)] =
        (cycleOccurrenceIndicesFor sourceLiteral.atom
          (copy sourceLiteral.atom port)).map
          (fun index =>
            ((occurrenceClauses source occurrencePorts).length +
                cycleBlockStart
                  (sourceVariables source.erase)
                  sourceLiteral.atom +
                index.1,
              index.2)) := by
    calc
      [(second.2.1, second.2.2),
          (third.2.1, third.2.2)] =
          (cycleOccurrencesOf source.erase
            occurrencePorts output).map
              (fun tagged =>
                (tagged.2.1, tagged.2.2)) := by
            rw [decomposition.2]
            rfl
      _ =
          (cycleOccurrenceIndicesFor sourceLiteral.atom
            (copy sourceLiteral.atom port)).map
            (fun index =>
              ((PeriodicEightOccurrenceSplit.occurrenceClauses
                  source.erase occurrencePorts).length +
                  cycleBlockStart
                    (sourceVariables source.erase)
                    sourceLiteral.atom +
                  index.1,
                index.2)) := by
            rw [outputEqual]
            exact cycleOccurrencesOf_ringCopy_indices
              source.erase occurrencePorts sourceLiteral.atom
              (.port port) atomMember
      _ =
          (cycleOccurrenceIndicesFor sourceLiteral.atom
            (copy sourceLiteral.atom port)).map
            (fun index =>
              ((occurrenceClauses source occurrencePorts).length +
                  cycleBlockStart
                    (sourceVariables source.erase)
                    sourceLiteral.atom +
                  index.1,
                index.2)) := by
            rw [occurrenceClausesLength]
  have localLength :
      (cycleOccurrenceIndicesFor sourceLiteral.atom
        (copy sourceLiteral.atom port)).length = 2 :=
    cycleOccurrenceIndicesFor_copy_length sourceLiteral.atom port
  rcases List.length_eq_two.mp localLength with
    ⟨firstCycleIndex, secondCycleIndex, localIndicesEqual⟩
  have firstCycleIndexMember :
      firstCycleIndex ∈
        cycleOccurrenceIndicesFor sourceLiteral.atom
          (copy sourceLiteral.atom port) := by
    rw [localIndicesEqual]
    simp
  have secondCycleIndexMember :
      secondCycleIndex ∈
        cycleOccurrenceIndicesFor sourceLiteral.atom
          (copy sourceLiteral.atom port) := by
    rw [localIndicesEqual]
    simp
  have firstCycleIndexLt :
      firstCycleIndex.1 <
        (PeriodicEightOccurrenceSplit.cycleClausesFor
          sourceLiteral.atom).length :=
    cycleOccurrenceIndicesFor_clauseIndex_lt
      sourceLiteral.atom
      (copy sourceLiteral.atom port)
      firstCycleIndexMember
  have secondCycleIndexLt :
      secondCycleIndex.1 <
        (PeriodicEightOccurrenceSplit.cycleClausesFor
          sourceLiteral.atom).length :=
    cycleOccurrenceIndicesFor_clauseIndex_lt
      sourceLiteral.atom
      (copy sourceLiteral.atom port)
      secondCycleIndexMember
  rw [localIndicesEqual] at cyclePairIndices
  simp only [List.map_cons, List.map_nil] at cyclePairIndices
  have secondIndicesEqual :
      (second.2.1, second.2.2) =
        ((occurrenceClauses source occurrencePorts).length +
            cycleBlockStart
              (sourceVariables source.erase)
              sourceLiteral.atom +
            firstCycleIndex.1,
          firstCycleIndex.2) :=
    congrArg List.head? cyclePairIndices
      |> Option.some.inj
  have thirdIndicesEqual :
      (third.2.1, third.2.2) =
        ((occurrenceClauses source occurrencePorts).length +
            cycleBlockStart
              (sourceVariables source.erase)
              sourceLiteral.atom +
            secondCycleIndex.1,
          secondCycleIndex.2) := by
    have tailsEqual := congrArg List.tail cyclePairIndices
    exact congrArg List.head? tailsEqual
      |> Option.some.inj
  have firstPrefixIndex :
      first.2.1 <
        (occurrenceClauses source occurrencePorts).length := by
    simpa [occurrenceClauses] using
      (List.mem_zipIdx' sourceClauseMember).1
  have portEqual :
      port =
        angularPortOfIndex
          (angularOccurrenceIndex order sourceLiteral
            first.2.1 first.2.2) := by
    unfold port occurrencePorts
    exact occurrencePortsOfAngularOrder_eq_angularPort
      source order sourceClauseMember sourceLiteralMember
  have firstRouteDirection :
      AxisDirection.polylineLastDirection
          (angularSplicedIncidenceRoutes
            source sourcePlacement order boundary
            first.2.1 first.2.2) =
        AxisDirection.polylineLastDirection
          (spokeRoute port) := by
    rw [angularSplicedIncidenceRoutes_occurrence
      source sourcePlacement order boundary
      first.2.1 first.2.2 firstPrefixIndex]
    rw [angularSplicedOccurrenceRoutes_of_members
      boundary sourceClauseMember sourceLiteralMember]
    rw [angularSplicedOccurrenceRoute_lastDirection
      boundary sourceClauseMember sourceLiteralMember]
    rw [← portEqual]
  have secondClauseIndexEqual :
      second.2.1 =
        (occurrenceClauses source occurrencePorts).length +
          (cycleBlockStart
              (sourceVariables source.erase)
              sourceLiteral.atom +
            firstCycleIndex.1) := by
    have := congrArg Prod.fst secondIndicesEqual
    omega
  have secondLiteralIndexEqual :
      second.2.2 = firstCycleIndex.2 := by
    have projected :=
      congrArg (fun index : Nat × Nat => index.2)
        secondIndicesEqual
    exact projected
  have thirdClauseIndexEqual :
      third.2.1 =
        (occurrenceClauses source occurrencePorts).length +
          (cycleBlockStart
              (sourceVariables source.erase)
              sourceLiteral.atom +
            secondCycleIndex.1) := by
    have := congrArg Prod.fst thirdIndicesEqual
    omega
  have thirdLiteralIndexEqual :
      third.2.2 = secondCycleIndex.2 := by
    have projected :=
      congrArg (fun index : Nat × Nat => index.2)
        thirdIndicesEqual
    exact projected
  have secondRouteDirection :
      AxisDirection.polylineLastDirection
          (angularSplicedIncidenceRoutes
            source sourcePlacement order boundary
            second.2.1 second.2.2) =
        AxisDirection.polylineLastDirection
          (cycleRoutes
            firstCycleIndex.1 firstCycleIndex.2) := by
    rw [secondClauseIndexEqual, secondLiteralIndexEqual]
    rw [angularSplicedIncidenceRoutes_cycle
      source sourcePlacement order boundary]
    exact allCycleRoutes_cycleBlockStart_lastDirection
      source sourcePlacement sourceLiteral.atom atomMember
      firstCycleIndex.1 firstCycleIndex.2
      firstCycleIndexLt
  have thirdRouteDirection :
      AxisDirection.polylineLastDirection
          (angularSplicedIncidenceRoutes
            source sourcePlacement order boundary
            third.2.1 third.2.2) =
        AxisDirection.polylineLastDirection
          (cycleRoutes
            secondCycleIndex.1 secondCycleIndex.2) := by
    rw [thirdClauseIndexEqual, thirdLiteralIndexEqual]
    rw [angularSplicedIncidenceRoutes_cycle
      source sourcePlacement order boundary]
    exact allCycleRoutes_cycleBlockStart_lastDirection
      source sourcePlacement sourceLiteral.atom atomMember
      secondCycleIndex.1 secondCycleIndex.2
      secondCycleIndexLt
  have localIndicesAtEqual :
      cycleOccurrenceIndicesAt (.port port) =
        [firstCycleIndex, secondCycleIndex] := by
    calc
      cycleOccurrenceIndicesAt (.port port) =
          cycleOccurrenceIndicesFor sourceLiteral.atom
            (copy sourceLiteral.atom port) := by
        exact
          (cycleOccurrenceIndicesFor_ringCopy
            sourceLiteral.atom (.port port)).symm
      _ = [firstCycleIndex, secondCycleIndex] :=
        localIndicesEqual
  have localClockwise :=
    port_occurrenceDirections_inClockwiseOrder port
  simpa [spokeOccurrenceDirection,
    cycleOccurrenceDirectionsAt, localIndicesAtEqual,
    cycleOccurrenceDirection,
    firstRouteDirection, secondRouteDirection,
    thirdRouteDirection] using localClockwise

/-- The concrete canonical angular-spliced route family inherits the same
clockwise fixed-eight variable order. -/
theorem canonicalAngularSplicedIncidenceRoutes_variableRoutesInOccurrenceOrder
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order : OccurrenceOrder source.erase)
    (fits : FitsEightSlots order) :
    PositionedPeriodicCNF.VariableRoutesInOccurrenceOrder
      (formula source sourcePlacement
        (occurrencePortsOfAngularOrder source.erase order))
      (canonicalAngularSplicedIncidenceRoutes
        source sourcePlacement order) := by
  exact
    angularSplicedIncidenceRoutes_variableRoutesInOccurrenceOrder
      source sourcePlacement order fits
      (canonicalAngularBoundaryRoutes
        source sourcePlacement order)

end PeriodicEightOccurrenceSplitPositioned
end LeanTrominoes
