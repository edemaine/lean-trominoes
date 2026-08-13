/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineInheritedConnectorSeparation

/-!
# Mixed auxiliary/inherited endpoint separation

An auxiliary incidence and a twice-inherited incidence can share a retained
source gauge, but their local endpoints cannot coincide.  After transporting
both endpoints into that common gauge, they are positions of differently
typed variable vertices in one valid finite Figure 9-plus-unit-elimination
drawing.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

local instance mixedEndpointVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (OneInThreeVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

private theorem metadata_mem_of_lookup
    {Variable : Type*}
    (source : PositionedPeriodicCNF Variable)
    {metadata :
      PlanarOneInThreeNoUnitsFigureNine.ClauseMetadata Variable}
    {clauseIndex : Nat}
    (lookup :
      (PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata source)[
        clauseIndex]? = some metadata) :
    metadata ∈
      PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata source := by
  have indexLt := (List.getElem?_eq_some_iff.mp lookup).1
  have metadataAt := (List.getElem?_eq_some_iff.mp lookup).2
  rw [← metadataAt]
  exact List.getElem_mem indexLt

/-- Within one composed source block, a non-inherited local endpoint cannot
be one of the original source ports. -/
private theorem normalizedLocalEndpoint_ne_normalizedSourcePort_of_not_inherited
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
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
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (literalNotInherited :
      ∀ sourceAtom : Variable,
        literal.atom ≠ .inl (.inl sourceAtom))
    (metadata :
      PlanarOneInThreeNoUnitsFigureNine.ClauseMetadata Variable)
    (metadataLookup :
      (PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata source)[
        clauseIndex]? = some metadata)
    {sourceLiteral : PeriodicLiteral Variable}
    {sourceLiteralIndex : Nat}
    (sourceLiteralMember :
      (sourceLiteral, sourceLiteralIndex) ∈
        metadata.sourceClause.literals.zipIdx) :
    PlanarOneInThreeNoUnitsFigureNine.normalizedLocalEndpoint
        source sourcePlacement clauseIndex literalIndex ≠
      PlanarOneInThreeNoUnitsFigureNine.normalizedSourcePort
        (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
          source sourcePlacement)
        metadata.sourceClause clause sourceLiteralIndex := by
  let outputPlacement :=
    PlanarOneInThreeNoUnitsFigureNine.composedPlacement
      source sourcePlacement
  rcases
      PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata_lookup_valid_embedded
        source clauseMember with
    ⟨actualMetadata, actualLookup, actualClause,
      sourceClauseMember, embeddedClauseMember⟩
  have actualMetadataEqual : actualMetadata = metadata := by
    apply Option.some.inj
    exact actualLookup.symm.trans metadataLookup
  subst actualMetadata
  have metadataClause : metadata.clause = clause := actualClause
  have sourceClauseMem : metadata.sourceClause ∈ source.clauses :=
    List.fst_mem_of_mem_zipIdx sourceClauseMember
  have metadataWidth : metadata.sourceClause.literals.length ≤ 3 :=
    sourceWidth metadata.sourceClause.literals
      (List.mem_map.mpr
        ⟨metadata.sourceClause, sourceClauseMem, rfl⟩)
  have metadataDistinct : metadata.sourceClause.AtomsNodup :=
    sourceDistinct metadata.sourceClause sourceClauseMem
  let drawing :=
    PlanarOneInThreeNoUnitsFigureNine.instantiatedDrawing
      metadata.sourceClauseIndex metadata.figureNineClauseStart
      metadata.sourceClause
  have drawingValid : drawing.IsValid :=
    PlanarOneInThreeNoUnitsFigureNine.instantiatedDrawing_isValid
      metadata.sourceClauseIndex metadata.figureNineClauseStart
      metadata.sourceClause metadataWidth metadataDistinct
  have metadataLiteralMember :
      (literal, literalIndex) ∈ metadata.clause.literals.zipIdx := by
    simpa [metadataClause] using literalMember
  have embeddedLiteralMember :
      (literal.atom, literal.value) ∈
        (PlanarOneInThreeNoUnits.embedPositionedClause
          metadata.clause).literals := by
    unfold PlanarOneInThreeNoUnits.embedPositionedClause
    exact List.mem_map.mpr
      ⟨literal,
        List.fst_mem_of_mem_zipIdx metadataLiteralMember, rfl⟩
  have localAtomMember : literal.atom ∈ drawing.variableVertices := by
    unfold PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.variableVertices
    rw [List.mem_dedup]
    exact List.mem_flatMap.mpr
      ⟨PlanarOneInThreeNoUnits.embedPositionedClause metadata.clause,
        by
          change
            PlanarOneInThreeNoUnits.embedPositionedClause metadata.clause ∈
              (PlanarOneInThreeNoUnitsFigureNine.instantiatedDrawing
                metadata.sourceClauseIndex
                metadata.figureNineClauseStart
                metadata.sourceClause).formula
          rw [PlanarOneInThreeNoUnitsFigureNine.instantiatedDrawing_formula
            metadata.sourceClauseIndex metadata.figureNineClauseStart
            metadata.sourceClause metadataWidth]
          exact List.fst_mem_of_mem_zipIdx embeddedClauseMember,
        List.mem_map.mpr
          ⟨(literal.atom, literal.value),
            embeddedLiteralMember, rfl⟩⟩
  have sourceAtomMember :
      (.inl (.inl sourceLiteral.atom) :
          OneInThreeNoUnitVariable (OneInThreeVariable Variable)) ∈
        drawing.variableVertices :=
    PlanarOneInThreeNoUnitsFigureNine.instantiatedDrawing_sourceAtom_mem_variableVertices
      metadata.sourceClauseIndex metadata.figureNineClauseStart
      metadata.sourceClause metadataWidth metadataDistinct
      sourceLiteralMember
  have variablePositionsNodup :
      (drawing.variableVertices.map drawing.variablePosition).Nodup := by
    have vertexPositionsNodup := drawingValid.2.2.2.2.2
    rw [PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.vertexPositions,
      List.nodup_append] at vertexPositionsNodup
    exact vertexPositionsNodup.1
  have variablePositionInjective :=
    (List.nodup_map_iff_inj_on
      (List.nodup_dedup
        (drawing.formula.flatMap fun localClause =>
          localClause.literals.map Prod.fst))).mp
      variablePositionsNodup
  have finitePositionsDifferent :
      drawing.variablePosition literal.atom ≠
        drawing.variablePosition (.inl (.inl sourceLiteral.atom)) := by
    intro positionsEqual
    exact literalNotInherited sourceLiteral.atom
      (variablePositionInjective
        literal.atom localAtomMember
        (.inl (.inl sourceLiteral.atom)) sourceAtomMember
        positionsEqual)
  have localEndpoint :
      PlanarOneInThreeNoUnitsFigureNine.normalizedLocalEndpoint
          source sourcePlacement clauseIndex literalIndex =
        Cell.sub
          (drawing.variablePosition literal.atom)
          (outputPlacement.translation
            (PeriodicCNF.clauseAnchor clause.literals)) := by
    simp only [PlanarOneInThreeNoUnitsFigureNine.normalizedLocalEndpoint,
      metadataLookup]
    rw [(List.mem_zipIdx_iff_getElem?).mp metadataLiteralMember]
    simp only
    rw [metadataClause]
  have sourcePosition :=
    PlanarOneInThreeNoUnitsFigureNine.instantiatedDrawing_sourcePosition
      metadata.sourceClauseIndex metadata.figureNineClauseStart
      metadata.sourceClause metadataWidth metadataDistinct
      sourceLiteralMember
  have sourcePort :
      PlanarOneInThreeNoUnitsFigureNine.normalizedSourcePort
          outputPlacement metadata.sourceClause clause
          sourceLiteralIndex =
        Cell.sub
          (drawing.variablePosition (.inl (.inl sourceLiteral.atom)))
          (outputPlacement.translation
            (PeriodicCNF.clauseAnchor clause.literals)) := by
    rw [sourcePosition]
    apply Prod.ext <;>
      simp [PlanarOneInThreeNoUnitsFigureNine.normalizedSourcePort,
        PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition,
        Cell.add, Cell.sub] <;>
      ring
  intro pointsEqual
  apply finitePositionsDifferent
  apply Cell.sub_right_injective
    (offset := outputPlacement.translation
      (PeriodicCNF.clauseAnchor clause.literals))
  exact localEndpoint.symm.trans
    (pointsEqual.trans sourcePort)

/-- Equal normalized source gauges identify the local metadata entry and an
inherited incidence as belonging to the same finite composed source block. -/
private theorem localMetadata_sourceBlock_eq_inherited_of_gaugesEqual
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {localClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {localClauseIndex : Nat}
    (localClauseMember :
      (localClause, localClauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).clauses.zipIdx)
    (localMetadata :
      PlanarOneInThreeNoUnitsFigureNine.ClauseMetadata
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable)))
    (localMetadataLookup :
      (PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata
        (retainedFigureNineClearancePositionedFormula source))[
          localClauseIndex]? = some localMetadata)
    (localMetadataClause : localMetadata.clause = localClause)
    {secondClauseIndex secondLiteralIndex : Nat}
    (second :
      PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        secondClauseIndex secondLiteralIndex)
    (relativeTranslate : Cell)
    (sourceGaugesEqual :
      PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
          (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source))
          localMetadata.sourceClause localClause =
        Cell.add
          ((PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source)).translation
              relativeTranslate)
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
            (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
              (retainedFigureNineClearancePositionedFormula source)
              (retainedFigureNineClearancePlacement source))
            second.sourceClause second.generatedClause)) :
    localMetadata.sourceClauseIndex =
        second.metadata.sourceClauseIndex ∧
      localMetadata.sourceClause = second.sourceClause ∧
      localMetadata.figureNineClauseStart =
        second.metadata.figureNineClauseStart := by
  let clearanceSource :=
    retainedFigureNineClearancePositionedFormula source
  have sourceIndexEqual :
      localMetadata.sourceClauseIndex = second.sourceClauseIndex :=
    retainedOrderedFixedEightFigureNine_sourceClauseIndex_eq_of_normalizedSourceGaugesEqual
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty localClauseMember
      localMetadata localMetadataLookup localMetadataClause
      second relativeTranslate sourceGaugesEqual
  have metadataSourceIndexEqual :
      localMetadata.sourceClauseIndex =
        second.metadata.sourceClauseIndex :=
    sourceIndexEqual.trans second.metadataSourceClauseIndex.symm
  have sourceBlockEqual :=
    PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata_sourceBlock_eq
      clearanceSource
      (metadata_mem_of_lookup clearanceSource localMetadataLookup)
      (metadata_mem_of_lookup clearanceSource second.metadataLookup)
      metadataSourceIndexEqual
  exact
    ⟨metadataSourceIndexEqual,
      sourceBlockEqual.1.trans second.metadataSourceClause,
      sourceBlockEqual.2⟩

/-- In a common retained source gauge, the endpoint of an auxiliary local
route differs from the translated inherited source port. -/
theorem
    retainedOrderedFixedEightFigureNine_normalizedLocalEndpoint_ne_translatedInheritedSourcePort_of_sourceGaugesEqual_of_not_inherited
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {localClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {localClauseIndex : Nat}
    (localClauseMember :
      (localClause, localClauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).clauses.zipIdx)
    {localLiteral :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {localLiteralIndex : Nat}
    (localLiteralMember :
      (localLiteral, localLiteralIndex) ∈ localClause.literals.zipIdx)
    (localNotInherited :
      ∀ sourceAtom :
        ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable),
        localLiteral.atom ≠ .inl (.inl sourceAtom))
    (localMetadata :
      PlanarOneInThreeNoUnitsFigureNine.ClauseMetadata
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable)))
    (localMetadataLookup :
      (PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata
        (retainedFigureNineClearancePositionedFormula source))[
          localClauseIndex]? = some localMetadata)
    {secondClauseIndex secondLiteralIndex : Nat}
    (second :
      PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        secondClauseIndex secondLiteralIndex)
    (relativeTranslate : Cell)
    (sourceGaugesEqual :
      PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
          (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source))
          localMetadata.sourceClause localClause =
        Cell.add
          ((PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source)).translation
              relativeTranslate)
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
            (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
              (retainedFigureNineClearancePositionedFormula source)
              (retainedFigureNineClearancePlacement source))
            second.sourceClause second.generatedClause)) :
    PlanarOneInThreeNoUnitsFigureNine.normalizedLocalEndpoint
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        localClauseIndex localLiteralIndex ≠
      Cell.add
        ((PlanarOneInThreeNoUnitsFigureNine.composedPlacement
          (retainedFigureNineClearancePositionedFormula source)
          (retainedFigureNineClearancePlacement source)).translation
            relativeTranslate)
        (PlanarOneInThreeNoUnitsFigureNine.normalizedSourcePort
          (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source))
          second.sourceClause second.generatedClause
          second.sourceLiteralIndex) := by
  let clearanceSource :=
    retainedFigureNineClearancePositionedFormula source
  let clearancePlacement :=
    retainedFigureNineClearancePlacement source
  let outputPlacement :=
    PlanarOneInThreeNoUnitsFigureNine.composedPlacement
      clearanceSource clearancePlacement
  let offset := outputPlacement.translation relativeTranslate
  rcases
      PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata_lookup_valid_embedded
        clearanceSource localClauseMember with
    ⟨actualMetadata, actualLookup, actualClause,
      _localSourceClauseMember, _localEmbeddedClauseMember⟩
  have actualMetadataEqual : actualMetadata = localMetadata := by
    apply Option.some.inj
    exact actualLookup.symm.trans localMetadataLookup
  subst actualMetadata
  have localMetadataClause : localMetadata.clause = localClause :=
    actualClause
  have sourceBlockEqual :=
    localMetadata_sourceBlock_eq_inherited_of_gaugesEqual
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty localClauseMember
      localMetadata localMetadataLookup localMetadataClause
      second relativeTranslate sourceGaugesEqual
  have secondSourceLiteralMemberLocal :
      (second.sourceLiteral, second.sourceLiteralIndex) ∈
        localMetadata.sourceClause.literals.zipIdx := by
    simpa [sourceBlockEqual.2.1] using second.sourceLiteralMember
  let clearanceWidth :=
    retainedFigureNineClearancePositionedFormula_widthAtMostThree
      source sourceWidth
  have localPortDifferent :=
    normalizedLocalEndpoint_ne_normalizedSourcePort_of_not_inherited
      clearanceSource clearancePlacement clearanceWidth
      (retainedFigureNineClearancePositionedFormula_allAtomsNodup
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      localClauseMember localLiteralMember localNotInherited
      localMetadata localMetadataLookup secondSourceLiteralMemberLocal
  have sourceGaugesEqual' :
      PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
          outputPlacement localMetadata.sourceClause localClause =
        Cell.add offset
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
            outputPlacement second.sourceClause second.generatedClause) := by
    simpa [outputPlacement, offset, clearanceSource,
      clearancePlacement] using sourceGaugesEqual
  have portsEqual :
      PlanarOneInThreeNoUnitsFigureNine.normalizedSourcePort
          outputPlacement localMetadata.sourceClause localClause
          second.sourceLiteralIndex =
        Cell.add offset
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourcePort
            outputPlacement second.sourceClause second.generatedClause
            second.sourceLiteralIndex) := by
    rw [PlanarOneInThreeNoUnitsFigureNine.normalizedSourcePort,
      PlanarOneInThreeNoUnitsFigureNine.normalizedSourcePort,
      sourceGaugesEqual']
    apply Prod.ext <;>
      simp [Cell.add] <;>
      ring
  intro pointsEqual
  apply localPortDifferent
  exact pointsEqual.trans
    (by simpa [outputPlacement, offset, clearanceSource,
      clearancePlacement] using portsEqual.symm)

/-- At equal retained source gauges, an arbitrary auxiliary normalized
local route strictly avoids the translated inherited suffix. -/
theorem
    retainedOrderedFixedEightFigureNine_normalizedLocal_strictlyAvoids_translatedInheritedSuffix_of_sourceGaugesEqual_of_not_inherited
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {localClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {localClauseIndex : Nat}
    (localClauseMember :
      (localClause, localClauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).clauses.zipIdx)
    {localLiteral :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {localLiteralIndex : Nat}
    (localLiteralMember :
      (localLiteral, localLiteralIndex) ∈ localClause.literals.zipIdx)
    (localNotInherited :
      ∀ sourceAtom :
        ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable),
        localLiteral.atom ≠ .inl (.inl sourceAtom))
    (localMetadata :
      PlanarOneInThreeNoUnitsFigureNine.ClauseMetadata
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable)))
    (localMetadataLookup :
      (PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata
        (retainedFigureNineClearancePositionedFormula source))[
          localClauseIndex]? = some localMetadata)
    {secondClauseIndex secondLiteralIndex : Nat}
    (second :
      PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        secondClauseIndex secondLiteralIndex)
    (relativeTranslate : Cell)
    (sourceGaugesEqual :
      PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
          (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source))
          localMetadata.sourceClause localClause =
        Cell.add
          ((PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source)).translation
              relativeTranslate)
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
            (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
              (retainedFigureNineClearancePositionedFormula source)
              (retainedFigureNineClearancePlacement source))
            second.sourceClause second.generatedClause)) :
    let clearanceWidth :=
      retainedFigureNineClearancePositionedFormula_widthAtMostThree
        source sourceWidth
    let outputPlacement :=
      PlanarOneInThreeNoUnitsFigureNine.composedPlacement
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
    RoutesStrictlyAvoidEachOther
      (PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        localClauseIndex localLiteralIndex)
      (translatePolyline (outputPlacement.translation relativeTranslate)
        (PlanarOneInThreeNoUnitsFigureNine.fanInheritedRouteSuffix
          outputPlacement
          (retainedFigureNineClearancePlacement source)
          second.sourceClause second.generatedClause
          (PositionedPeriodicCNF.clauseExitFanData
            second.sourceClause second.sourceClauseIndex
            (retainedFigureNineClearanceIncidenceRoutes source))
          (second.sourceSlot clearanceWidth)
          (retainedFigureNineClearanceIncidenceRoutes
            source second.sourceClauseIndex
            second.sourceLiteralIndex))) := by
  let clearanceSource :=
    retainedFigureNineClearancePositionedFormula source
  let clearancePlacement :=
    retainedFigureNineClearancePlacement source
  let clearanceWidth :=
    retainedFigureNineClearancePositionedFormula_widthAtMostThree
      source sourceWidth
  let outputPlacement :=
    PlanarOneInThreeNoUnitsFigureNine.composedPlacement
      clearanceSource clearancePlacement
  let localRoute :=
    PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
      clearanceSource clearancePlacement
      localClauseIndex localLiteralIndex
  let connector :=
    (PositionedPeriodicCNF.clauseExitFanData
      second.sourceClause second.sourceClauseIndex
      (retainedFigureNineClearanceIncidenceRoutes source)
    ).translatedExtendedRoute
      (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
        outputPlacement second.sourceClause second.generatedClause)
      (second.sourceSlot clearanceWidth)
  let offset := outputPlacement.translation relativeTranslate
  rcases
      PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata_lookup_valid_embedded
        clearanceSource localClauseMember with
    ⟨actualMetadata, actualLookup, actualClause,
      _localSourceMember, _localEmbeddedMember⟩
  have actualMetadataEqual : actualMetadata = localMetadata := by
    apply Option.some.inj
    exact actualLookup.symm.trans localMetadataLookup
  subst actualMetadata
  have localEndpoints :=
    PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes_endpoints_of_members
      clearanceSource clearancePlacement clearanceWidth
      (retainedFigureNineClearancePositionedFormula_allAtomsNodup
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      localClauseMember localLiteralMember
  have connectorHead :=
    retainedOrderedFixedEightFigureNine_inheritedExtendedConnector_head?
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty second
  have endpointPointsDifferent :=
    retainedOrderedFixedEightFigureNine_normalizedLocalEndpoint_ne_translatedInheritedSourcePort_of_sourceGaugesEqual_of_not_inherited
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty localClauseMember localLiteralMember
      localNotInherited localMetadata localMetadataLookup
      second relativeTranslate sourceGaugesEqual
  have endpointsDifferent :
      localRoute.getLast? ≠
        (translatePolyline offset connector).head? := by
    have translatedConnectorHead :
        (translatePolyline offset connector).head? =
          some
            (Cell.add offset
              (PlanarOneInThreeNoUnitsFigureNine.normalizedSourcePort
                outputPlacement second.sourceClause
                second.generatedClause second.sourceLiteralIndex)) := by
      simpa [connector, translatePolyline] using
        congrArg (Option.map (Cell.add offset)) connectorHead
    rw [localEndpoints.2, translatedConnectorHead]
    exact fun equal => endpointPointsDifferent (Option.some.inj equal)
  exact
    retainedOrderedFixedEightFigureNineNormalizedLocalRoute_strictlyAvoids_translatedInheritedSuffix_of_sourceGauge
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty localClauseMember localLiteralMember
      localMetadata localMetadataLookup actualClause
      second relativeTranslate sourceGaugesEqual
      (by simpa [localRoute, connector, offset,
        clearanceSource, clearancePlacement, outputPlacement,
        clearanceWidth] using endpointsDifferent)

/-- Every auxiliary normalized local route strictly avoids every translated
inherited suffix, whether or not their retained source gauges agree. -/
theorem
    retainedOrderedFixedEightFigureNine_normalizedLocal_strictlyAvoids_translatedInheritedSuffix_of_not_inherited
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {localClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {localClauseIndex : Nat}
    (localClauseMember :
      (localClause, localClauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
          source).clauses.zipIdx)
    {localLiteral :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {localLiteralIndex : Nat}
    (localLiteralMember :
      (localLiteral, localLiteralIndex) ∈ localClause.literals.zipIdx)
    (localNotInherited :
      ∀ sourceAtom :
        ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable),
        localLiteral.atom ≠ .inl (.inl sourceAtom))
    (localMetadata :
      PlanarOneInThreeNoUnitsFigureNine.ClauseMetadata
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable)))
    (localMetadataLookup :
      (PlanarOneInThreeNoUnitsFigureNine.formulaClauseMetadata
        (retainedFigureNineClearancePositionedFormula source))[
          localClauseIndex]? = some localMetadata)
    {secondClauseIndex secondLiteralIndex : Nat}
    (second :
      PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        secondClauseIndex secondLiteralIndex)
    (relativeTranslate : Cell) :
    let clearanceWidth :=
      retainedFigureNineClearancePositionedFormula_widthAtMostThree
        source sourceWidth
    let outputPlacement :=
      PlanarOneInThreeNoUnitsFigureNine.composedPlacement
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
    RoutesStrictlyAvoidEachOther
      (PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        localClauseIndex localLiteralIndex)
      (translatePolyline (outputPlacement.translation relativeTranslate)
        (PlanarOneInThreeNoUnitsFigureNine.fanInheritedRouteSuffix
          outputPlacement
          (retainedFigureNineClearancePlacement source)
          second.sourceClause second.generatedClause
          (PositionedPeriodicCNF.clauseExitFanData
            second.sourceClause second.sourceClauseIndex
            (retainedFigureNineClearanceIncidenceRoutes source))
          (second.sourceSlot clearanceWidth)
          (retainedFigureNineClearanceIncidenceRoutes
            source second.sourceClauseIndex
            second.sourceLiteralIndex))) := by
  by_cases sourceGaugesEqual :
      PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
          (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source))
          localMetadata.sourceClause localClause =
        Cell.add
          ((PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source)).translation
              relativeTranslate)
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
            (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
              (retainedFigureNineClearancePositionedFormula source)
              (retainedFigureNineClearancePlacement source))
            second.sourceClause second.generatedClause)
  · exact
      retainedOrderedFixedEightFigureNine_normalizedLocal_strictlyAvoids_translatedInheritedSuffix_of_sourceGaugesEqual_of_not_inherited
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty localClauseMember localLiteralMember
        localNotInherited localMetadata localMetadataLookup
        second relativeTranslate sourceGaugesEqual
  · exact
      retainedOrderedFixedEightFigureNine_normalizedLocal_strictlyAvoids_translatedInheritedSuffix_of_sourceGaugesNe
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty localClauseMember localLiteralMember
        localMetadata localMetadataLookup
        second relativeTranslate sourceGaugesEqual

end PeriodicOrthocrossing
end LeanTrominoes
