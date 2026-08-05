import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalClauseOrbits
import LeanTrominoes.PeriodicOneInThreeNoUnitsAuxiliaryIncidences

/-!
# Source macrocells of final Figure Nine variables

The two exact-one replacement layers create three kinds of variables.  This
file places inherited source variables, first-stage Figure Nine auxiliaries,
and second-stage unit-elimination auxiliaries in the finite `72 × 72` local
address table.  For a genuine second-stage source clause, its first-stage
metadata also recovers the original source clause macrocell.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- A source variable inherited through both replacement layers remains at
the origin of its source-variable macrocell. -/
theorem composedInheritedVariable_inMacrocellOrbit
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (atom : Variable) :
    Cell.InMacrocellOrbit finalFigureNineMacrocellScale
      sourcePlacement.period (sourcePlacement.position atom)
      FinalFigureNineLocalAddress.inheritedVariable.position
      ((PlanarOneInThreeNoUnitsFigureNine.composedPlacement
        source sourcePlacement).position (.inl (.inl atom))) := by
  have firstOrbit :=
    PeriodicOneInThreePositioned.placement_inherited_inMacrocellOrbit
      source sourcePlacement atom
  have secondOrbit :=
    PeriodicOneInThreeNoUnitsPositioned.placement_inherited_inMacrocellOrbit
      (PeriodicOneInThreePositioned.formula source)
      (PeriodicOneInThreePositioned.placement source sourcePlacement)
      (.inl atom)
  have composedOrbit := firstOrbit.compose secondOrbit
  simpa [PlanarOneInThreeNoUnitsFigureNine.composedPlacement,
    finalFigureNineMacrocellScale,
    FinalFigureNineLocalAddress.position,
    PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
    Cell.add, Cell.scale] using composedOrbit

/-- A Figure Nine auxiliary inherited through unit elimination retains its
first-stage local address over the source clause macrocell. -/
theorem composedFigureNineAuxiliary_inMacrocellOrbit
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClauseIndex : Nat)
    (sourceClause : PeriodicClause Variable)
    (kind : OneInThreeAux) :
    Cell.InMacrocellOrbit finalFigureNineMacrocellScale
      sourcePlacement.period
      (source.clausePosition sourceClauseIndex)
      (FinalFigureNineLocalAddress.figureNineAuxiliary kind).position
      ((PlanarOneInThreeNoUnitsFigureNine.composedPlacement
        source sourcePlacement).position
          (.inl (.inr ((sourceClauseIndex, sourceClause), kind)))) := by
  have firstOrbit :=
    PeriodicOneInThreePositioned.placement_auxiliary_inMacrocellOrbit
      source sourcePlacement sourceClauseIndex sourceClause kind
  have secondOrbit :=
    PeriodicOneInThreeNoUnitsPositioned.placement_inherited_inMacrocellOrbit
      (PeriodicOneInThreePositioned.formula source)
      (PeriodicOneInThreePositioned.placement source sourcePlacement)
      (.inr ((sourceClauseIndex, sourceClause), kind))
  have composedOrbit := firstOrbit.compose secondOrbit
  simpa [PlanarOneInThreeNoUnitsFigureNine.composedPlacement,
    finalFigureNineMacrocellScale,
    FinalFigureNineLocalAddress.position,
    PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
    Cell.add, Cell.scale] using composedOrbit

/-- A unit-elimination auxiliary whose source is a genuine Figure Nine
clause lies in the original source clause's macrocell.  Its finite address
records the Figure Nine clause index and its unit-elimination kind. -/
theorem composedUnitAuxiliary_inMacrocellOrbit
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    {figureNineClause :
      PositionedPeriodicClause (OneInThreeVariable Variable)}
    {figureNineClauseIndex : Nat}
    (figureNineClauseMember :
      (figureNineClause, figureNineClauseIndex) ∈
        (PeriodicOneInThreePositioned.formula source).clauses.zipIdx)
    (kind : OneInThreeNoUnitAux) :
    ∃ sourceClause sourceClauseIndex,
      ∃ localFigureNineClauseIndex : Fin 6,
      (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx ∧
      Cell.InMacrocellOrbit finalFigureNineMacrocellScale
        sourcePlacement.period sourceClause.position
        (FinalFigureNineLocalAddress.unitEliminationAuxiliary
          localFigureNineClauseIndex kind).position
        ((PlanarOneInThreeNoUnitsFigureNine.composedPlacement
          source sourcePlacement).position
            (.inr ((figureNineClauseIndex,
              figureNineClause.literals), kind))) := by
  rcases PeriodicOneInThreePositioned.formulaClauseMetadata_lookup_valid
      source figureNineClauseMember with
    ⟨metadata, _metadataLookup, metadataClauseEqual,
      sourceClauseMember, localClauseMember⟩
  have localFigureNineClauseIndexLt : metadata.localClauseIndex < 6 :=
    lt_of_lt_of_le
      (List.mem_zipIdx' localClauseMember).1
      (PeriodicOneInThreePositioned.clauseGadget_length_le_six
        metadata.sourceClauseIndex metadata.sourceClause)
  let localFigureNineClauseIndex : Fin 6 :=
    ⟨metadata.localClauseIndex, localFigureNineClauseIndexLt⟩
  have figureNineClausePosition :
      (PeriodicOneInThreePositioned.formula source).clausePosition
          figureNineClauseIndex = figureNineClause.position := by
    simp [PositionedPeriodicCNF.clausePosition,
      (List.mem_zipIdx_iff_getElem?).mp figureNineClauseMember]
  have generatedPosition :
      metadata.clause.position =
        PlanarOneInThree.generatedClausePosition
          metadata.sourceClause.position metadata.localClauseIndex :=
    PeriodicOneInThreePositioned.clauseGadget_position_eq_generatedClausePosition
      metadata.sourceClauseIndex metadata.sourceClause localClauseMember
  have firstOrbit :
      Cell.InMacrocellOrbit 12 sourcePlacement.period
        metadata.sourceClause.position
        (PeriodicOneInThreePositioned.generatedClauseLocalPosition
          metadata.localClauseIndex)
        metadata.clause.position := by
    rw [generatedPosition]
    exact
      PeriodicOneInThreePositioned.generatedClausePosition_inMacrocellOrbit
        sourcePlacement.period metadata.sourceClause.position
        metadata.localClauseIndex
  have secondOrbit :
      Cell.InMacrocellOrbit 6 (12 * sourcePlacement.period)
        metadata.clause.position
        (PeriodicOneInThreeNoUnitsPositioned.auxiliaryLocalPosition kind)
        ((PlanarOneInThreeNoUnitsFigureNine.composedPlacement
          source sourcePlacement).position
            (.inr ((figureNineClauseIndex,
              figureNineClause.literals), kind))) := by
    rw [metadataClauseEqual, ← figureNineClausePosition]
    exact
      PeriodicOneInThreeNoUnitsPositioned.placement_auxiliary_inMacrocellOrbit
        (PeriodicOneInThreePositioned.formula source)
        (PeriodicOneInThreePositioned.placement source sourcePlacement)
        figureNineClauseIndex figureNineClause.literals kind
  have composedOrbit := firstOrbit.compose secondOrbit
  refine ⟨metadata.sourceClause, metadata.sourceClauseIndex,
    localFigureNineClauseIndex, sourceClauseMember, ?_⟩
  simpa [finalFigureNineMacrocellScale,
    FinalFigureNineLocalAddress.position,
    finalFigureNineClauseLocalPosition,
    localFigureNineClauseIndex,
    PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
    PeriodicOneInThreePositioned.generatedClauseLocalPosition] using
      composedOrbit

end PeriodicOrthocrossing
end LeanTrominoes
