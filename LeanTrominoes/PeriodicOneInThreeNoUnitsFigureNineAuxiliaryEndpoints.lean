import LeanTrominoes.PeriodicOneInThreeNoUnitsAuxiliaryIncidences
import LeanTrominoes.PeriodicOneInThreeAuxiliaryIncidences
import LeanTrominoes.PeriodicOneInThreeNoUnitsInheritedIncidences
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineNormalizedLocalRoutes
import LeanTrominoes.PositionedPeriodicCNFOrthogonalIncidenceRoutes

/-!
# Finality of composed auxiliary endpoints

The composed Figure 9-plus-unit-elimination drawings contain two generations
of fresh variables.  This file identifies their displayed endpoints with the
canonical positions supplied by the two-stage periodic placement.
-/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

open PlanarThreeSAT

/-- Every second-stage unit-elimination auxiliary in a composed block is
already at its final canonical endpoint after anchor normalization. -/
theorem normalizedLocalEndpoint_unitAuxiliary
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (auxiliary :
      (Nat × PeriodicClause (OneInThreeVariable Variable)) ×
        OneInThreeNoUnitAux)
    (literalAuxiliary : literal.atom = .inr auxiliary) :
    normalizedLocalEndpoint source sourcePlacement
        clauseIndex literalIndex =
      PositionedPeriodicCNF.canonicalLiteralPosition
        (composedPlacement source sourcePlacement) clause literal := by
  letI := nestedVariableDecidableEq (Variable := Variable)
  rcases formulaClauseMetadata_lookup_valid
      source clauseMember with
    ⟨metadata, metadataLookup, clauseEqual,
      sourceClauseMember, localClauseMember⟩
  have metadataLiteralMember :
      (literal, literalIndex) ∈
        metadata.clause.literals.zipIdx := by
    simpa [clauseEqual] using literalMember
  have metadataSourceMember :
      metadata.sourceClause ∈ source.clauses :=
    List.fst_mem_of_mem_zipIdx sourceClauseMember
  have metadataWidth :
      metadata.sourceClause.literals.length ≤ 3 := by
    apply sourceWidth metadata.sourceClause.literals
    exact List.mem_map.mpr
      ⟨metadata.sourceClause, metadataSourceMember, rfl⟩
  have metadataDistinct :
      metadata.sourceClause.AtomsNodup :=
    sourceDistinct metadata.sourceClause metadataSourceMember
  have metadataIndexLt :
      clauseIndex < (formulaClauseMetadata source).length :=
    (List.getElem?_eq_some_iff.mp metadataLookup).1
  have metadataAt :
      (formulaClauseMetadata source)[clauseIndex] = metadata :=
    (List.getElem?_eq_some_iff.mp metadataLookup).2
  have metadataMember :
      metadata ∈ formulaClauseMetadata source := by
    rw [← metadataAt]
    exact List.getElem_mem metadataIndexLt
  have embeddedClauseMember :=
    localClauseMember_embedded
      metadata.sourceClauseIndex
      metadata.figureNineClauseStart
      metadata.sourceClause localClauseMember
  have embeddedLiteralMember :
      (literal.atom, literal.value) ∈
        (PlanarOneInThreeNoUnits.embedPositionedClause
          metadata.clause).literals := by
    unfold PlanarOneInThreeNoUnits.embedPositionedClause
    exact List.mem_map.mpr
      ⟨literal,
        List.fst_mem_of_mem_zipIdx metadataLiteralMember,
        rfl⟩
  have atomMember :
      literal.atom ∈
        (instantiatedDrawing
          metadata.sourceClauseIndex
          metadata.figureNineClauseStart
          metadata.sourceClause).variableVertices := by
    unfold EmbeddedCNFIncidenceDrawing.variableVertices
    rw [instantiatedDrawing_formula
      metadata.sourceClauseIndex
      metadata.figureNineClauseStart
      metadata.sourceClause metadataWidth]
    simp only [List.mem_dedup]
    exact List.mem_flatMap.mpr
      ⟨PlanarOneInThreeNoUnits.embedPositionedClause metadata.clause,
        List.fst_mem_of_mem_zipIdx embeddedClauseMember,
        List.mem_map.mpr
          ⟨(literal.atom, literal.value),
            embeddedLiteralMember, rfl⟩⟩
  have finalClauseMember :
      metadata.clause ∈
        unitEliminationClausesFrom
          metadata.figureNineClauseStart
          (PeriodicOneInThreePositioned.clauseGadget
            metadata.sourceClauseIndex
            metadata.sourceClause) :=
    List.fst_mem_of_mem_zipIdx localClauseMember
  rw [unitEliminationClausesFrom_eq_localZipIdx]
    at finalClauseMember
  rcases List.mem_flatMap.mp finalClauseMember with
    ⟨taggedFigureNineClause, taggedFigureNineClauseMember,
      finalClauseInGadget⟩
  have finalClauseLiteralsMember :
      metadata.clause.literals ∈
        PeriodicOneInThreeNoUnits.clauseClauses
          (metadata.figureNineClauseStart +
            taggedFigureNineClause.2)
          taggedFigureNineClause.1.literals := by
    rw [←
      PeriodicOneInThreeNoUnitsPositioned.clauseGadget_literals]
    exact List.mem_map.mpr
      ⟨metadata.clause, finalClauseInGadget, rfl⟩
  have finalLiteralMember :
      literal ∈ metadata.clause.literals :=
    List.fst_mem_of_mem_zipIdx metadataLiteralMember
  have auxiliaryData :=
    PeriodicOneInThreeNoUnits.auxiliary_scope_offset_of_mem_clauseClauses
      (metadata.figureNineClauseStart +
        taggedFigureNineClause.2)
      taggedFigureNineClause.1.literals
      finalClauseLiteralsMember finalLiteralMember
      auxiliary literalAuxiliary
  rcases auxiliary with ⟨auxiliaryScope, kind⟩
  have auxiliaryScopeEqual :
      auxiliaryScope =
        (metadata.figureNineClauseStart +
          taggedFigureNineClause.2,
          taggedFigureNineClause.1.literals) :=
    auxiliaryData.1
  have literalOffset :
      literal.offset =
        PeriodicOneInThree.anchor
          taggedFigureNineClause.1.literals :=
    auxiliaryData.2
  have figureNineClauseGlobalMember :
      (taggedFigureNineClause.1,
          metadata.figureNineClauseStart +
            taggedFigureNineClause.2) ∈
        (PeriodicOneInThreePositioned.formula
          source).clauses.zipIdx :=
    formulaClauseMetadata_figureNineClause_member
      source metadataMember taggedFigureNineClauseMember
  have figureNineClausePosition :
      (PeriodicOneInThreePositioned.formula source).clausePosition
          (metadata.figureNineClauseStart +
            taggedFigureNineClause.2) =
        taggedFigureNineClause.1.position := by
    simp [PositionedPeriodicCNF.clausePosition,
      (List.mem_zipIdx_iff_getElem?).mp
        figureNineClauseGlobalMember]
  have localFigureNineClauseLookup :
      (PeriodicOneInThreePositioned.clauseGadget
        metadata.sourceClauseIndex
        metadata.sourceClause)[taggedFigureNineClause.2]? =
          some taggedFigureNineClause.1 :=
    (List.mem_zipIdx_iff_getElem?).mp
      taggedFigureNineClauseMember
  have figureNineClauseLiteralsEqual :
      figureNineClauseLiterals
          metadata.sourceClauseIndex
          metadata.sourceClause
          taggedFigureNineClause.2 =
        taggedFigureNineClause.1.literals := by
    simp [figureNineClauseLiterals,
      localFigureNineClauseLookup]
  have figureNineClausePositionEqual :
      taggedFigureNineClause.1.position =
        PlanarOneInThree.generatedClausePosition
          metadata.sourceClause.position
          taggedFigureNineClause.2 := by
    have lookup := localFigureNineClauseLookup
    simp [PeriodicOneInThreePositioned.clauseGadget]
      at lookup
    rcases lookup with ⟨sourceLiterals, sourceLiteralsLookup,
      clauseEqual⟩
    exact (congrArg PositionedPeriodicClause.position
      clauseEqual).symm
  have expectedAtomMember :
      (.inr
        ((metadata.figureNineClauseStart +
            taggedFigureNineClause.2,
          figureNineClauseLiterals
            metadata.sourceClauseIndex
            metadata.sourceClause
            taggedFigureNineClause.2),
          kind) :
        OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)) ∈
        (instantiatedDrawing
          metadata.sourceClauseIndex
          metadata.figureNineClauseStart
          metadata.sourceClause).variableVertices := by
    rw [figureNineClauseLiteralsEqual,
      ← auxiliaryScopeEqual, ← literalAuxiliary]
    exact atomMember
  have physicalPosition :=
    instantiatedDrawing_unitAuxiliaryPosition
      metadata.sourceClauseIndex
      metadata.figureNineClauseStart
      metadata.sourceClause metadataWidth metadataDistinct
      taggedFigureNineClause.2 kind expectedAtomMember
  have literalPhysicalPosition :
      (instantiatedDrawing
        metadata.sourceClauseIndex
        metadata.figureNineClauseStart
        metadata.sourceClause).variablePosition literal.atom =
      Cell.add
        (Cell.scale composedGadgetScale
          metadata.sourceClause.position)
        (Cell.add
          (Cell.scale 6
            (PlanarOneInThree.generatedClausePosition
              (0, 0) taggedFigureNineClause.2))
          (PeriodicOneInThreeNoUnitsPositioned.auxiliaryLocalPosition
            kind)) := by
    rw [literalAuxiliary, auxiliaryScopeEqual,
      ← figureNineClauseLiteralsEqual]
    exact physicalPosition
  subst clause
  simp only [normalizedLocalEndpoint, metadataLookup]
  rw [(List.mem_zipIdx_iff_getElem?).mp metadataLiteralMember]
  simp only
  rw [literalPhysicalPosition]
  apply Prod.ext <;>
  simp [PositionedPeriodicCNF.canonicalLiteralPosition,
    composedPlacement,
    PeriodicOneInThreeNoUnitsPositioned.placement,
    PeriodicOneInThreeNoUnitsPositioned.auxiliaryOccurrencePosition,
    PeriodicVariablePlacement.translation,
    literalAuxiliary, auxiliaryScopeEqual, literalOffset,
    figureNineClausePosition,
    figureNineClausePositionEqual,
    PlanarOneInThree.generatedClausePosition,
    composedGadgetScale, PlanarOneInThree.gadgetScale,
    PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
    Cell.add, Cell.sub, Cell.scale]
  <;> ring

/-- Every first-stage Figure 9 auxiliary inherited through unit elimination
is likewise already at its final canonical composed endpoint. -/
theorem normalizedLocalEndpoint_figureNineAuxiliary
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (OneInThreeVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (auxiliary :
      (Nat × PeriodicClause Variable) × OneInThreeAux)
    (literalAuxiliary :
      literal.atom = .inl (.inr auxiliary)) :
    normalizedLocalEndpoint source sourcePlacement
        clauseIndex literalIndex =
      PositionedPeriodicCNF.canonicalLiteralPosition
        (composedPlacement source sourcePlacement) clause literal := by
  letI := nestedVariableDecidableEq (Variable := Variable)
  rcases formulaClauseMetadata_lookup_valid
      source clauseMember with
    ⟨metadata, metadataLookup, clauseEqual,
      sourceClauseMember, localClauseMember⟩
  have metadataLiteralMember :
      (literal, literalIndex) ∈
        metadata.clause.literals.zipIdx := by
    simpa [clauseEqual] using literalMember
  have metadataSourceMember :
      metadata.sourceClause ∈ source.clauses :=
    List.fst_mem_of_mem_zipIdx sourceClauseMember
  have metadataWidth :
      metadata.sourceClause.literals.length ≤ 3 := by
    apply sourceWidth metadata.sourceClause.literals
    exact List.mem_map.mpr
      ⟨metadata.sourceClause, metadataSourceMember, rfl⟩
  have metadataDistinct :
      metadata.sourceClause.AtomsNodup :=
    sourceDistinct metadata.sourceClause metadataSourceMember
  have embeddedClauseMember :=
    localClauseMember_embedded
      metadata.sourceClauseIndex
      metadata.figureNineClauseStart
      metadata.sourceClause localClauseMember
  have embeddedLiteralMember :
      (literal.atom, literal.value) ∈
        (PlanarOneInThreeNoUnits.embedPositionedClause
          metadata.clause).literals := by
    unfold PlanarOneInThreeNoUnits.embedPositionedClause
    exact List.mem_map.mpr
      ⟨literal,
        List.fst_mem_of_mem_zipIdx metadataLiteralMember,
        rfl⟩
  have atomMember :
      literal.atom ∈
        (instantiatedDrawing
          metadata.sourceClauseIndex
          metadata.figureNineClauseStart
          metadata.sourceClause).variableVertices := by
    unfold EmbeddedCNFIncidenceDrawing.variableVertices
    rw [instantiatedDrawing_formula
      metadata.sourceClauseIndex
      metadata.figureNineClauseStart
      metadata.sourceClause metadataWidth]
    simp only [List.mem_dedup]
    exact List.mem_flatMap.mpr
      ⟨PlanarOneInThreeNoUnits.embedPositionedClause metadata.clause,
        List.fst_mem_of_mem_zipIdx embeddedClauseMember,
        List.mem_map.mpr
          ⟨(literal.atom, literal.value),
            embeddedLiteralMember, rfl⟩⟩
  have finalClauseMember :
      metadata.clause ∈
        unitEliminationClausesFrom
          metadata.figureNineClauseStart
          (PeriodicOneInThreePositioned.clauseGadget
            metadata.sourceClauseIndex
            metadata.sourceClause) :=
    List.fst_mem_of_mem_zipIdx localClauseMember
  rw [unitEliminationClausesFrom_eq_localZipIdx]
    at finalClauseMember
  rcases List.mem_flatMap.mp finalClauseMember with
    ⟨taggedFigureNineClause, taggedFigureNineClauseMember,
      finalClauseInGadget⟩
  have finalClauseLiteralsMember :
      metadata.clause.literals ∈
        PeriodicOneInThreeNoUnits.clauseClauses
          (metadata.figureNineClauseStart +
            taggedFigureNineClause.2)
          taggedFigureNineClause.1.literals := by
    rw [←
      PeriodicOneInThreeNoUnitsPositioned.clauseGadget_literals]
    exact List.mem_map.mpr
      ⟨metadata.clause, finalClauseInGadget, rfl⟩
  have finalLiteralMember :
      literal ∈ metadata.clause.literals :=
    List.fst_mem_of_mem_zipIdx metadataLiteralMember
  rcases
      PeriodicOneInThreeNoUnits.inherited_of_mem_clauseClauses
        (metadata.figureNineClauseStart +
          taggedFigureNineClause.2)
        taggedFigureNineClause.1.literals
        finalClauseLiteralsMember finalLiteralMember
        (.inr auxiliary) literalAuxiliary with
    ⟨figureNineLiteral, figureNineLiteralIndex,
      figureNineLiteralMember, figureNineLiteralAtom,
      finalLiteralOffset⟩
  have figureNineClauseMember :
      taggedFigureNineClause.1.literals ∈
        PeriodicOneInThree.clauseClauses
          metadata.sourceClauseIndex
          metadata.sourceClause.literals := by
    rw [← PeriodicOneInThreePositioned.clauseGadget_literals]
    exact List.mem_map.mpr
      ⟨taggedFigureNineClause.1,
        List.fst_mem_of_mem_zipIdx
          taggedFigureNineClauseMember,
        rfl⟩
  have figureNineLiteralMem :
      figureNineLiteral ∈
        taggedFigureNineClause.1.literals :=
    List.fst_mem_of_mem_zipIdx figureNineLiteralMember
  have auxiliaryData :=
    PeriodicOneInThree.auxiliary_scope_offset_of_mem_clauseClauses
      metadata.sourceClauseIndex
      metadata.sourceClause.literals
      figureNineClauseMember figureNineLiteralMem
      auxiliary figureNineLiteralAtom
  rcases auxiliary with ⟨auxiliaryScope, kind⟩
  have auxiliaryScopeEqual :
      auxiliaryScope =
        (metadata.sourceClauseIndex,
          metadata.sourceClause.literals) :=
    auxiliaryData.1
  have literalOffset :
      literal.offset =
        PeriodicOneInThree.anchor
          metadata.sourceClause.literals :=
    finalLiteralOffset.trans auxiliaryData.2
  have sourceClauseLookup :
      source.clauses[metadata.sourceClauseIndex]? =
        some metadata.sourceClause :=
    (List.mem_zipIdx_iff_getElem?).mp sourceClauseMember
  have sourceClausePosition :
      source.clausePosition metadata.sourceClauseIndex =
        metadata.sourceClause.position := by
    simp [PositionedPeriodicCNF.clausePosition,
      sourceClauseLookup]
  have expectedAtomMember :
      (.inl
        (.inr
          ((metadata.sourceClauseIndex,
            metadata.sourceClause.literals), kind)) :
        OneInThreeNoUnitVariable
          (OneInThreeVariable Variable)) ∈
        (instantiatedDrawing
          metadata.sourceClauseIndex
          metadata.figureNineClauseStart
          metadata.sourceClause).variableVertices := by
    rw [← auxiliaryScopeEqual, ← literalAuxiliary]
    exact atomMember
  have physicalPosition :=
    instantiatedDrawing_figureNineAuxiliaryPosition
      metadata.sourceClauseIndex
      metadata.figureNineClauseStart
      metadata.sourceClause metadataWidth metadataDistinct
      kind expectedAtomMember
  have literalPhysicalPosition :
      (instantiatedDrawing
        metadata.sourceClauseIndex
        metadata.figureNineClauseStart
        metadata.sourceClause).variablePosition literal.atom =
      Cell.add
        (Cell.scale composedGadgetScale
          metadata.sourceClause.position)
        (Cell.scale 6
          (PeriodicOneInThreePositioned.auxiliaryLocalPosition
            kind)) := by
    rw [literalAuxiliary, auxiliaryScopeEqual]
    exact physicalPosition
  subst clause
  simp only [normalizedLocalEndpoint, metadataLookup]
  rw [(List.mem_zipIdx_iff_getElem?).mp metadataLiteralMember]
  simp only
  rw [literalPhysicalPosition]
  apply Prod.ext <;>
  simp [PositionedPeriodicCNF.canonicalLiteralPosition,
    composedPlacement,
    PeriodicOneInThreeNoUnitsPositioned.placement,
    PeriodicOneInThreePositioned.placement,
    PeriodicOneInThreePositioned.auxiliaryOccurrencePosition,
    PeriodicVariablePlacement.translation,
    literalAuxiliary, auxiliaryScopeEqual, literalOffset,
    sourceClausePosition,
    composedGadgetScale, PlanarOneInThree.gadgetScale,
    PeriodicOneInThreeNoUnitsPositioned.gadgetScale,
    Cell.add, Cell.sub, Cell.scale]
  <;> ring

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
