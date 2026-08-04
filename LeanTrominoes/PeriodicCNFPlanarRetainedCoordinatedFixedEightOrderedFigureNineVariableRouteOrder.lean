import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFigureNineClearanceVariableRouteOrder
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineTerminalDirections
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineOccurrenceSlots
import LeanTrominoes.PositionedPeriodicCNFDeduplicationTerminalPorts

/-!
# Variable route order through the ordered Figure 9 composition

A degree-three atom in the twice-transformed formula is inherited through
both exact-one reductions.  The composed provenance recovers its clearance
occurrence in the same first, second, or third slot, while the raw route keeps
that occurrence's variable-side terminal direction.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

set_option maxHeartbeats 3000000

private theorem value_eq_of_mem_zipIdx_same_index
    {Value : Type*} {values : List Value}
    {first second : Value} {index : Nat}
    (firstMember : (first, index) ∈ values.zipIdx)
    (secondMember : (second, index) ∈ values.zipIdx) :
    first = second := by
  exact
    (List.mem_zipIdx' firstMember).2.trans
      (List.mem_zipIdx' secondMember).2.symm

/-- One final occurrence recovers a clearance occurrence in the same slot,
and its raw route has the recovered route's terminal direction. -/
private theorem
    retainedOrderedFixedEightComposedRawIncidenceRoutes_slot
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (finalEq :
      DecidableEq
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable)))
    (sourceAtom :
      ThreeOccurrenceVariable
        (WrappedPeriodicPlanarSATVariable Variable))
    (slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot)
    (tagged :
      PeriodicOneInThreeToThreeDM.TaggedOccurrence
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable)))
    (lookup :
      @PeriodicOneInThreeToThreeDM.occurrenceAt
          (OneInThreeNoUnitVariable
            (PeriodicPlanarOneInThreeThreeRawVariable Variable))
          finalEq
          (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
            source).erase
          (.inl (.inl sourceAtom)) slot = some tagged) :
    ∃ data :
        PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData
          (retainedFigureNineClearancePositionedFormula source)
          (retainedFigureNineClearancePlacement source)
          tagged.2.1 tagged.2.2,
      @PeriodicOneInThreeToThreeDM.occurrenceAt
          (ThreeOccurrenceVariable
            (WrappedPeriodicPlanarSATVariable Variable))
          inferInstance
          (retainedFigureNineClearancePositionedFormula source).erase
          sourceAtom slot =
        some
          (data.sourceLiteral, data.sourceClauseIndex,
            data.sourceLiteralIndex) ∧
      AxisDirection.polylineLastDirection
          (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty tagged.2.1 tagged.2.2) =
        AxisDirection.polylineLastDirection
          (retainedFigureNineClearanceIncidenceRoutes
            source data.sourceClauseIndex data.sourceLiteralIndex) := by
  have info :=
    @PeriodicOneInThreeToThreeDM.occurrenceAt_mem_and_atom
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable))
      finalEq
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source).erase
      (.inl (.inl sourceAtom)) slot tagged lookup
  rcases PositionedPeriodicCNF.exists_positionedOccurrence_of_tagged
      _ info.1 with
    ⟨clause, clauseMember, literalMember⟩
  rcases
      retainedOrderedFixedEightComposedRawIncidenceRoutes_lastDirection_of_inherited
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
        sourceAtom info.2 with
    ⟨data, _dataLookup, direction⟩
  have generatedClauseEq : data.generatedClause = clause :=
    value_eq_of_mem_zipIdx_same_index
      data.generatedClauseMember clauseMember
  have generatedLiteralEq : data.generatedLiteral = tagged.1 := by
    apply value_eq_of_mem_zipIdx_same_index
      data.generatedLiteralMember
    simpa [generatedClauseEq] using literalMember
  have dataSourceAtom : data.sourceLiteral.atom = sourceAtom := by
    have generatedAtom :
        data.generatedLiteral.atom = .inl (.inl sourceAtom) := by
      simpa [generatedLiteralEq] using info.2
    have nested :
        (.inl (.inl data.sourceLiteral.atom) :
          OneInThreeNoUnitVariable
            (PeriodicPlanarOneInThreeThreeRawVariable Variable)) =
          .inl (.inl sourceAtom) :=
      data.literalAtom.symm.trans generatedAtom
    exact Sum.inl.inj (Sum.inl.inj nested)
  have semanticLookup :
      @PeriodicOneInThreeToThreeDM.occurrenceAt
          (OneInThreeNoUnitVariable
            (PeriodicPlanarOneInThreeThreeRawVariable Variable))
          finalEq
          (PeriodicOneInThreeNoUnits.formula
            (PeriodicOneInThree.formula
              (retainedFigureNineClearancePositionedFormula source).erase))
          (.inl (.inl sourceAtom)) slot = some tagged := by
    simpa only [
      retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula,
      PeriodicOneInThreeNoUnitsPositioned.erase_formula,
      PeriodicOneInThreePositioned.erase_formula] using lookup
  have dataFinalLookup :
      @PeriodicOneInThreeToThreeDM.occurrenceAt
          (OneInThreeNoUnitVariable
            (PeriodicPlanarOneInThreeThreeRawVariable Variable))
          finalEq
          (PeriodicOneInThreeNoUnits.formula
            (PeriodicOneInThree.formula
              (retainedFigureNineClearancePositionedFormula source).erase))
          data.generatedLiteral.atom slot =
        some (data.generatedLiteral, tagged.2.1, tagged.2.2) := by
    have generatedOccurrenceEq :
        (data.generatedLiteral, tagged.2.1, tagged.2.2) = tagged := by
      apply Prod.ext
      · exact generatedLiteralEq
      · rfl
    calc
      @PeriodicOneInThreeToThreeDM.occurrenceAt
          (OneInThreeNoUnitVariable
            (PeriodicPlanarOneInThreeThreeRawVariable Variable))
          finalEq
          (PeriodicOneInThreeNoUnits.formula
            (PeriodicOneInThree.formula
              (retainedFigureNineClearancePositionedFormula source).erase))
          data.generatedLiteral.atom slot =
        @PeriodicOneInThreeToThreeDM.occurrenceAt
          (OneInThreeNoUnitVariable
            (PeriodicPlanarOneInThreeThreeRawVariable Variable))
          finalEq
          (PeriodicOneInThreeNoUnits.formula
            (PeriodicOneInThree.formula
              (retainedFigureNineClearancePositionedFormula source).erase))
          (.inl (.inl sourceAtom)) slot := by
            rw [generatedLiteralEq, info.2]
      _ = some tagged := semanticLookup
      _ = some
          (data.generatedLiteral, tagged.2.1, tagged.2.2) :=
        congrArg some generatedOccurrenceEq.symm
  have sourceLookup :=
    PlanarOneInThreeNoUnitsFigureNine.InheritedEndpointProvenance.sourceOccurrenceAt
      (retainedFigureNineClearancePositionedFormula source)
      (retainedFigureNineClearancePlacement source)
      (retainedFigureNineClearancePositionedFormula_widthAtMostThree
        source sourceWidth)
      data finalEq slot dataFinalLookup
  refine ⟨data, ?_, direction⟩
  rw [← dataSourceAtom]
  exact sourceLookup

/-- The complete raw ordered Figure 9 construction retains clockwise
variable route order from the clearance source. -/
theorem
    retainedOrderedFixedEightComposedRawIncidenceRoutes_variableRoutesInOccurrenceOrder
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.VariableRoutesInOccurrenceOrder
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty) := by
  apply
    @PositionedPeriodicCNF.variableRoutesInOccurrenceOrder_of_decidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable))
      PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq
      (inferInstance)
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
  intro outputAtom first second third
    firstLookup secondLookup thirdLookup
  change
    @PeriodicOneInThreeToThreeDM.occurrenceAt
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))
        PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).erase outputAtom .first = some first
    at firstLookup
  change
    @PeriodicOneInThreeToThreeDM.occurrenceAt
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))
        PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).erase outputAtom .second = some second
    at secondLookup
  change
    @PeriodicOneInThreeToThreeDM.occurrenceAt
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))
        PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).erase outputAtom .third = some third
    at thirdLookup
  have thirdSemantic :
      @PeriodicOneInThreeToThreeDM.occurrenceAt
          (OneInThreeNoUnitVariable
            (PeriodicPlanarOneInThreeThreeRawVariable Variable))
          PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq
          (PeriodicOneInThreeNoUnits.formula
            (PeriodicOneInThree.formula
              (retainedFigureNineClearancePositionedFormula source).erase))
          outputAtom .third = some third := by
    simpa only [
      retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula,
      PeriodicOneInThreeNoUnitsPositioned.erase_formula,
      PeriodicOneInThreePositioned.erase_formula] using thirdLookup
  rcases
      PlanarOneInThreeNoUnitsFigureNine.exists_sourceAtom_of_occurrenceAt_third
        (retainedFigureNineClearancePositionedFormula source).erase
        PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq
        outputAtom third thirdSemantic with
    ⟨sourceAtom, outputAtomEq⟩
  subst outputAtom
  rcases retainedOrderedFixedEightComposedRawIncidenceRoutes_slot
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
      PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq
      sourceAtom .first first firstLookup with
    ⟨firstData, sourceFirstLookup, firstDirection⟩
  rcases retainedOrderedFixedEightComposedRawIncidenceRoutes_slot
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
      PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq
      sourceAtom .second second secondLookup with
    ⟨secondData, sourceSecondLookup, secondDirection⟩
  rcases retainedOrderedFixedEightComposedRawIncidenceRoutes_slot
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
      PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq
      sourceAtom .third third thirdLookup with
    ⟨thirdData, sourceThirdLookup, thirdDirection⟩
  have sourceClockwise :=
    retainedFigureNineClearanceIncidenceRoutes_variableRoutesInOccurrenceOrder
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty sourceAtom
      (firstData.sourceLiteral, firstData.sourceClauseIndex,
        firstData.sourceLiteralIndex)
      (secondData.sourceLiteral, secondData.sourceClauseIndex,
        secondData.sourceLiteralIndex)
      (thirdData.sourceLiteral, thirdData.sourceClauseIndex,
        thirdData.sourceLiteralIndex)
      sourceFirstLookup sourceSecondLookup sourceThirdLookup
  rw [firstDirection, secondDirection, thirdDirection]
  exact sourceClockwise

end PeriodicOrthocrossing
end LeanTrominoes
