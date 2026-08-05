import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalClauseOrbits
import LeanTrominoes.PeriodicOneInThreeNoUnitsAuxiliaryIncidences
import LeanTrominoes.PeriodicOneInThreeAuxiliaryIncidences
import LeanTrominoes.PeriodicOneInThreeNoUnitsInheritedIncidences
import LeanTrominoes.PeriodicOneInThreeInheritedIncidences

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
      (figureNineClause, localFigureNineClauseIndex.val) ∈
        (PeriodicOneInThreePositioned.clauseGadget
          sourceClauseIndex sourceClause).zipIdx ∧
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
    localFigureNineClauseIndex, sourceClauseMember, ?_, ?_⟩
  · simpa [metadataClauseEqual, localFigureNineClauseIndex] using
      localClauseMember
  simpa [finalFigureNineMacrocellScale,
    FinalFigureNineLocalAddress.position,
    finalFigureNineClauseLocalPosition,
    localFigureNineClauseIndex,
    PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
    PeriodicOneInThreePositioned.generatedClauseLocalPosition] using
      composedOrbit

/-- Provenance retained by the macrocell decomposition of a final variable.
The relation is indexed by the exact final atom, base position, and finite
local address, so it can later be inverted in collision arguments. -/
inductive FinalFigureNineVariableSource
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable) :
    OneInThreeNoUnitVariable (OneInThreeVariable Variable) →
      Cell → FinalFigureNineLocalAddress → Prop
  | inherited
      (sourceAtom : Variable)
      (sourceAtomMember : sourceAtom ∈ source.erase.variableOccurrences) :
      FinalFigureNineVariableSource source sourcePlacement
        (.inl (.inl sourceAtom))
        (sourcePlacement.position sourceAtom) .inheritedVariable
  | figureNineAuxiliary
      (sourceClause : PositionedPeriodicClause Variable)
      (sourceClauseIndex : Nat)
      (sourceClauseMember :
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx)
      (kind : OneInThreeAux) :
      FinalFigureNineVariableSource source sourcePlacement
        (.inl (.inr
          ((sourceClauseIndex, sourceClause.literals), kind)))
        sourceClause.position (.figureNineAuxiliary kind)
  | unitEliminationAuxiliary
      (sourceClause : PositionedPeriodicClause Variable)
      (sourceClauseIndex : Nat)
      (sourceClauseMember :
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx)
      (figureNineClause :
        PositionedPeriodicClause (OneInThreeVariable Variable))
      (figureNineClauseIndex : Nat)
      (localFigureNineClauseIndex : Fin 6)
      (localFigureNineClauseMember :
        (figureNineClause, localFigureNineClauseIndex.val) ∈
          (PeriodicOneInThreePositioned.clauseGadget
            sourceClauseIndex sourceClause).zipIdx)
      (figureNineClauseMember :
        (figureNineClause, figureNineClauseIndex) ∈
          (PeriodicOneInThreePositioned.formula source).clauses.zipIdx)
      (figureNineMetadataLookup :
        (PeriodicOneInThreePositioned.formulaClauseMetadata source)[
            figureNineClauseIndex]? =
          some
            ({ sourceClause := sourceClause
               sourceClauseIndex := sourceClauseIndex
               clause := figureNineClause
               localClauseIndex := localFigureNineClauseIndex.val } :
              PeriodicOneInThreePositioned.ClauseMetadata Variable))
      (kind : OneInThreeNoUnitAux) :
      FinalFigureNineVariableSource source sourcePlacement
        (.inr ((figureNineClauseIndex, figureNineClause.literals), kind))
        sourceClause.position
        (.unitEliminationAuxiliary localFigureNineClauseIndex kind)

/-- Every literal occurrence in the twice-replaced formula supplies a
genuine source certificate and the corresponding macrocell orbit. -/
theorem composedLiteralVariable_inMacrocellOrbit
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable (OneInThreeVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable (OneInThreeVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    ∃ base address,
      FinalFigureNineVariableSource source sourcePlacement
        literal.atom base address ∧
      Cell.InMacrocellOrbit finalFigureNineMacrocellScale
        sourcePlacement.period base address.position
        ((PlanarOneInThreeNoUnitsFigureNine.composedPlacement
          source sourcePlacement).position literal.atom) := by
  rcases PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata_lookup_valid
      source clauseMember with
    ⟨metadata, metadataLookup, metadataClauseEqual,
      sourceClauseMember, localClauseMember⟩
  have metadataIndexLt :
      clauseIndex <
        (PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata
          source).length :=
    (List.getElem?_eq_some_iff.mp metadataLookup).1
  have metadataAt :
      (PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata
        source)[clauseIndex] = metadata :=
    (List.getElem?_eq_some_iff.mp metadataLookup).2
  have metadataMember :
      metadata ∈
        PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata source := by
    rw [← metadataAt]
    exact List.getElem_mem metadataIndexLt
  have metadataLiteralMember :
      (literal, literalIndex) ∈ metadata.clause.literals.zipIdx := by
    simpa [metadataClauseEqual] using literalMember
  have finalLiteralMember : literal ∈ metadata.clause.literals :=
    List.fst_mem_of_mem_zipIdx metadataLiteralMember
  have finalClauseMember :
      metadata.clause ∈
        PlanarOneInThreeNoUnitsFigureNine.unitEliminationClausesFrom
          metadata.figureNineClauseStart
          (PeriodicOneInThreePositioned.clauseGadget
            metadata.sourceClauseIndex metadata.sourceClause) :=
    List.fst_mem_of_mem_zipIdx localClauseMember
  rw [PlanarOneInThreeNoUnitsFigureNine.unitEliminationClausesFrom_eq_localZipIdx]
    at finalClauseMember
  rcases List.mem_flatMap.mp finalClauseMember with
    ⟨taggedFigureNineClause, taggedFigureNineClauseMember,
      finalClauseInGadget⟩
  have finalClauseLiteralsMember :
      metadata.clause.literals ∈
        PeriodicOneInThreeNoUnits.clauseClauses
          (metadata.figureNineClauseStart + taggedFigureNineClause.2)
          taggedFigureNineClause.1.literals := by
    rw [← PeriodicOneInThreeNoUnitsPositioned.clauseGadget_literals]
    exact List.mem_map.mpr
      ⟨metadata.clause, finalClauseInGadget, rfl⟩
  have figureNineClauseMember :
      taggedFigureNineClause.1.literals ∈
        PeriodicOneInThree.clauseClauses
          metadata.sourceClauseIndex metadata.sourceClause.literals := by
    rw [← PeriodicOneInThreePositioned.clauseGadget_literals]
    exact List.mem_map.mpr
      ⟨taggedFigureNineClause.1,
        List.fst_mem_of_mem_zipIdx taggedFigureNineClauseMember, rfl⟩
  have figureNineGlobalMember :
      (taggedFigureNineClause.1,
          metadata.figureNineClauseStart + taggedFigureNineClause.2) ∈
        (PeriodicOneInThreePositioned.formula source).clauses.zipIdx :=
    PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata_figureNineClause_member
      source metadataMember taggedFigureNineClauseMember
  cases literalAtom : literal.atom with
  | inl figureNineAtom =>
      rcases PeriodicOneInThreeNoUnits.inherited_of_mem_clauseClauses
          (metadata.figureNineClauseStart + taggedFigureNineClause.2)
          taggedFigureNineClause.1.literals
          finalClauseLiteralsMember finalLiteralMember
          figureNineAtom literalAtom with
        ⟨figureNineLiteral, figureNineLiteralIndex,
          figureNineLiteralMember, figureNineLiteralAtom, _literalOffset⟩
      have figureNineLiteralMem :
          figureNineLiteral ∈ taggedFigureNineClause.1.literals :=
        List.fst_mem_of_mem_zipIdx figureNineLiteralMember
      cases figureNineAtom with
      | inl sourceAtom =>
          rcases PeriodicOneInThree.inherited_of_mem_clauseClauses
              metadata.sourceClauseIndex metadata.sourceClause.literals
              figureNineClauseMember figureNineLiteralMem
              sourceAtom figureNineLiteralAtom with
            ⟨sourceLiteral, sourceLiteralIndex, sourceLiteralMember,
              sourceLiteralAtom, _figureNineLiteralOffset⟩
          have sourceAtomMember :
              sourceAtom ∈ source.erase.variableOccurrences := by
            unfold PeriodicCNF.variableOccurrences
            apply List.mem_flatMap.mpr
            refine ⟨metadata.sourceClause.literals, ?_, ?_⟩
            · exact List.mem_map.mpr
                ⟨metadata.sourceClause,
                  List.fst_mem_of_mem_zipIdx sourceClauseMember, rfl⟩
            · exact List.mem_map.mpr
                ⟨sourceLiteral,
                  List.fst_mem_of_mem_zipIdx sourceLiteralMember,
                  sourceLiteralAtom⟩
          refine ⟨sourcePlacement.position sourceAtom,
            .inheritedVariable, ?_, ?_⟩
          · simpa [literalAtom] using
              FinalFigureNineVariableSource.inherited
                (source := source) (sourcePlacement := sourcePlacement)
                sourceAtom sourceAtomMember
          · simpa [literalAtom] using
              composedInheritedVariable_inMacrocellOrbit
                source sourcePlacement sourceAtom
      | inr auxiliary =>
          have auxiliaryData :=
            PeriodicOneInThree.auxiliary_scope_offset_of_mem_clauseClauses
              metadata.sourceClauseIndex metadata.sourceClause.literals
              figureNineClauseMember figureNineLiteralMem
              auxiliary figureNineLiteralAtom
          rcases auxiliary with ⟨auxiliaryScope, kind⟩
          have auxiliaryScopeEqual :
              auxiliaryScope =
                (metadata.sourceClauseIndex,
                  metadata.sourceClause.literals) :=
            auxiliaryData.1
          have sourceClausePosition :
              source.clausePosition metadata.sourceClauseIndex =
                metadata.sourceClause.position := by
            simp [PositionedPeriodicCNF.clausePosition,
              (List.mem_zipIdx_iff_getElem?).mp sourceClauseMember]
          refine ⟨metadata.sourceClause.position,
            .figureNineAuxiliary kind, ?_, ?_⟩
          · simpa [literalAtom, auxiliaryScopeEqual] using
              FinalFigureNineVariableSource.figureNineAuxiliary
                (source := source) (sourcePlacement := sourcePlacement)
                metadata.sourceClause
                metadata.sourceClauseIndex sourceClauseMember kind
          · simpa [literalAtom, auxiliaryScopeEqual, sourceClausePosition] using
              composedFigureNineAuxiliary_inMacrocellOrbit
                source sourcePlacement metadata.sourceClauseIndex
                metadata.sourceClause.literals kind
  | inr auxiliary =>
      have auxiliaryData :=
        PeriodicOneInThreeNoUnits.auxiliary_scope_offset_of_mem_clauseClauses
          (metadata.figureNineClauseStart + taggedFigureNineClause.2)
          taggedFigureNineClause.1.literals
          finalClauseLiteralsMember finalLiteralMember
          auxiliary literalAtom
      rcases auxiliary with ⟨auxiliaryScope, kind⟩
      have auxiliaryScopeEqual :
          auxiliaryScope =
            (metadata.figureNineClauseStart + taggedFigureNineClause.2,
              taggedFigureNineClause.1.literals) :=
        auxiliaryData.1
      have localFigureNineClauseIndexLt : taggedFigureNineClause.2 < 6 :=
        lt_of_lt_of_le
          (List.mem_zipIdx' taggedFigureNineClauseMember).1
          (PeriodicOneInThreePositioned.clauseGadget_length_le_six
            metadata.sourceClauseIndex metadata.sourceClause)
      let localFigureNineClauseIndex : Fin 6 :=
        ⟨taggedFigureNineClause.2, localFigureNineClauseIndexLt⟩
      have generatedPosition :
          taggedFigureNineClause.1.position =
            PlanarOneInThree.generatedClausePosition
              metadata.sourceClause.position taggedFigureNineClause.2 :=
        PeriodicOneInThreePositioned.clauseGadget_position_eq_generatedClausePosition
          metadata.sourceClauseIndex metadata.sourceClause
          taggedFigureNineClauseMember
      have firstOrbit :
          Cell.InMacrocellOrbit 12 sourcePlacement.period
            metadata.sourceClause.position
            (PeriodicOneInThreePositioned.generatedClauseLocalPosition
              taggedFigureNineClause.2)
            taggedFigureNineClause.1.position := by
        rw [generatedPosition]
        exact
          PeriodicOneInThreePositioned.generatedClausePosition_inMacrocellOrbit
            sourcePlacement.period metadata.sourceClause.position
            taggedFigureNineClause.2
      have figureNineClausePosition :
          (PeriodicOneInThreePositioned.formula source).clausePosition
              (metadata.figureNineClauseStart + taggedFigureNineClause.2) =
            taggedFigureNineClause.1.position := by
        simp [PositionedPeriodicCNF.clausePosition,
          (List.mem_zipIdx_iff_getElem?).mp figureNineGlobalMember]
      have secondOrbit :
          Cell.InMacrocellOrbit 6 (12 * sourcePlacement.period)
            taggedFigureNineClause.1.position
            (PeriodicOneInThreeNoUnitsPositioned.auxiliaryLocalPosition kind)
            ((PlanarOneInThreeNoUnitsFigureNine.composedPlacement
              source sourcePlacement).position
                (.inr
                  ((metadata.figureNineClauseStart +
                    taggedFigureNineClause.2,
                    taggedFigureNineClause.1.literals), kind))) := by
        rw [← figureNineClausePosition]
        exact
          PeriodicOneInThreeNoUnitsPositioned.placement_auxiliary_inMacrocellOrbit
            (PeriodicOneInThreePositioned.formula source)
            (PeriodicOneInThreePositioned.placement source sourcePlacement)
            (metadata.figureNineClauseStart + taggedFigureNineClause.2)
            taggedFigureNineClause.1.literals kind
      have orbit := firstOrbit.compose secondOrbit
      refine ⟨metadata.sourceClause.position,
        .unitEliminationAuxiliary localFigureNineClauseIndex kind, ?_, ?_⟩
      · simpa [literalAtom, auxiliaryScopeEqual,
          localFigureNineClauseIndex] using
          FinalFigureNineVariableSource.unitEliminationAuxiliary
            (source := source) (sourcePlacement := sourcePlacement)
            metadata.sourceClause
            metadata.sourceClauseIndex sourceClauseMember
            taggedFigureNineClause.1
            (metadata.figureNineClauseStart + taggedFigureNineClause.2)
            localFigureNineClauseIndex
            (by simpa [localFigureNineClauseIndex] using
              taggedFigureNineClauseMember)
            figureNineGlobalMember
            (by
              simpa [localFigureNineClauseIndex] using
                PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata_figureNineMetadata_lookup
                  source metadataMember taggedFigureNineClauseMember)
            kind
      · simpa [literalAtom, auxiliaryScopeEqual,
          finalFigureNineMacrocellScale,
          FinalFigureNineLocalAddress.position,
          finalFigureNineClauseLocalPosition,
          localFigureNineClauseIndex,
          PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
          PeriodicOneInThreePositioned.generatedClauseLocalPosition] using
            orbit

/-- The literal-level classification lifts to every variable occurrence in
the erased twice-replaced formula. -/
theorem composedVariableOccurrence_inMacrocellOrbit
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    {atom : OneInThreeNoUnitVariable (OneInThreeVariable Variable)}
    (atomMember :
      atom ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).erase.variableOccurrences) :
    ∃ base address,
      FinalFigureNineVariableSource source sourcePlacement atom base address ∧
      Cell.InMacrocellOrbit finalFigureNineMacrocellScale
        sourcePlacement.period base address.position
        ((PlanarOneInThreeNoUnitsFigureNine.composedPlacement
          source sourcePlacement).position atom) := by
  unfold PeriodicCNF.variableOccurrences at atomMember
  rcases List.mem_flatMap.mp atomMember with
    ⟨clauseLiterals, clauseLiteralsMember, atomInClause⟩
  rcases List.mem_map.mp clauseLiteralsMember with
    ⟨clause, clauseMember, clauseLiteralsEqual⟩
  subst clauseLiterals
  rcases List.mem_map.mp atomInClause with
    ⟨literal, literalMember, literalAtomEqual⟩
  rcases List.mem_iff_getElem.mp clauseMember with
    ⟨clauseIndex, clauseIndexLt, clauseAt⟩
  have taggedClauseMember :
      (clause, clauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff]
    exact ⟨clauseIndexLt, clauseAt⟩
  rcases List.mem_iff_getElem.mp literalMember with
    ⟨literalIndex, literalIndexLt, literalAt⟩
  have taggedLiteralMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff]
    exact ⟨literalIndexLt, literalAt⟩
  simpa [literalAtomEqual] using
    composedLiteralVariable_inMacrocellOrbit
      source sourcePlacement taggedClauseMember taggedLiteralMember

/-- Specialization to the retained fixed-eight source and composed raw
placement used in the hardness construction. -/
theorem retainedOrderedFixedEightComposedRawVariableOccurrence_inMacrocellOrbit
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    {atom :
      OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)}
    (atomMember :
      atom ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).erase.variableOccurrences) :
    ∃ base address,
      FinalFigureNineVariableSource
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        atom base address ∧
      Cell.InMacrocellOrbit finalFigureNineMacrocellScale
        (retainedFigureNineClearancePlacement source).period
        base address.position
        ((retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
          source).position atom) := by
  simpa only [
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement]
    using
      composedVariableOccurrence_inMacrocellOrbit
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source) atomMember

end PeriodicOrthocrossing
end LeanTrominoes
