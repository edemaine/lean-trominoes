import LeanTrominoes.RetainedAngularFanFinalRelativeCycleSeparation
import LeanTrominoes.RetainedAngularFanFinalDirectSourceOtherCycleSeparation

/-!
# Relative direct-source/cycle separation

This file lifts the successful direct-source branch of the final fixed-eight
router against implication cycles in arbitrary period cells.  The key
periodic identification says that if a source occurrence center equals a
translated cycle center, then the atoms agree and the occurrence's relative
offset is exactly that translation.  Consequently the translated flattened
cycle route is the already-certified matching Figure 7 lift.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Equality between a genuine source occurrence center and a periodically
translated occurring source center identifies both the atom and the exact
relative occurrence offset. -/
theorem
    retainedFinalCanonicalLiteralPosition_eq_translatedSourcePosition_imp
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (targetAtom : WrappedPeriodicPlanarSATVariable Variable)
    (targetAtomMember :
      targetAtom ∈
        sourceVariables
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor).erase)
    (relativeTranslate : Cell)
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          clause literal =
        Cell.add
          ((finalCoordinatedPlacement formula).position targetAtom)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate)) :
    literal.atom = targetAtom ∧
      incidenceRelativeOffset
          (clause.scale retainedAngularFanSourceClearanceFactor)
          literal =
        relativeTranslate := by
  let placement := finalCoordinatedPlacement formula
  let targetLiteral :
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable) :=
    { atom := targetAtom
      offset := Cell.add
        (PeriodicCNF.clauseAnchor clause.literals)
        relativeTranslate
      value := true }
  have targetCanonical :
      PositionedPeriodicCNF.canonicalLiteralPosition
          placement clause targetLiteral =
        Cell.add (placement.position targetAtom)
          (placement.translation relativeTranslate) := by
    unfold PositionedPeriodicCNF.canonicalLiteralPosition
    congr 1
    congr 1
    rcases anchorEq : PeriodicCNF.clauseAnchor clause.literals with
      ⟨anchorX, anchorY⟩
    rcases relativeTranslate with ⟨translateX, translateY⟩
    simp [targetLiteral, anchorEq, Cell.add, Cell.sub]
  have literalStrictBounds :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_position_inSquare
      formula literal.atom
  have targetStrictBounds :=
    retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_position_inSquare
      formula targetAtom
  have literalBounds :
      0 ≤ (placement.position literal.atom).1 ∧
        (placement.position literal.atom).1 < placement.period ∧
        0 ≤ (placement.position literal.atom).2 ∧
        (placement.position literal.atom).2 < placement.period := by
    simpa [placement, finalCoordinatedPlacement] using
      And.intro literalStrictBounds.1.le
        (And.intro literalStrictBounds.2.1
          (And.intro literalStrictBounds.2.2.1.le
            literalStrictBounds.2.2.2))
  have targetBounds :
      0 ≤ (placement.position targetLiteral.atom).1 ∧
        (placement.position targetLiteral.atom).1 < placement.period ∧
        0 ≤ (placement.position targetLiteral.atom).2 ∧
        (placement.position targetLiteral.atom).2 < placement.period := by
    simpa [placement, targetLiteral, finalCoordinatedPlacement] using
      And.intro targetStrictBounds.1.le
        (And.intro targetStrictBounds.2.1
          (And.intro targetStrictBounds.2.2.1.le
            targetStrictBounds.2.2.2))
  have positionAndOffsetEqual :=
    PositionedPeriodicCNF.canonicalLiteralPosition_eq_sameClause_imp
      placement
      (by
        simpa [placement, finalCoordinatedPlacement,
          retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_period,
          wrappedDrawingPeriodicPlanarSATPlacement]
          using drawingPeriodicPlanarSATPlacement_period_pos formula)
      clause literal targetLiteral
      literalBounds targetBounds
      (by simpa [placement, targetCanonical] using centersEqual)
  have literalTagged :
      (literal, clauseIndex, literalIndex) ∈
        taggedLiterals (finalCoordinatedSource formula).erase :=
    taggedLiteral_mem_of_positioned_members
      (finalCoordinatedSource formula)
      clauseMember literalMember
  have literalAtomMember :
      literal.atom ∈
        sourceVariables
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor).erase := by
    simpa only [PositionedPeriodicCNF.erase_scale] using
      sourceVariables_mem
        (finalCoordinatedSource formula).erase literalTagged
  have atomsEqual : literal.atom = targetAtom := by
    apply
      retainedFinalCoordinatedScaledPlacement_position_injective_on_sourceVariables
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        literalAtomMember targetAtomMember
    simpa [PeriodicVariablePlacement.scale] using
      congrArg
        (Cell.scale retainedAngularFanSourceClearanceFactor)
        positionAndOffsetEqual.1
  constructor
  · exact atomsEqual
  · rcases anchorEq : PeriodicCNF.clauseAnchor clause.literals with
      ⟨anchorX, anchorY⟩
    rcases relativeTranslate with ⟨translateX, translateY⟩
    simp [incidenceRelativeOffset,
      PositionedPeriodicClause.scale_literals,
      positionAndOffsetEqual.2, targetLiteral,
      anchorEq, Cell.add, Cell.sub]

/-- A flattened cycle route translated to the same center as a genuine
source occurrence is exactly that occurrence's matching cycle lift. -/
theorem
    retainedFinalScaledTranslatedAllCycleRoute_eq_matchingCycleLift_of_center_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    {metadata :
      CycleClauseMetadata
        (WrappedPeriodicPlanarSATVariable Variable)}
    {cycleIndex : Nat}
    (metadataLookup :
      (allCycleClauseMetadata
        ((finalCoordinatedSource formula).scale
          retainedAngularFanSourceClearanceFactor)
        ((finalCoordinatedPlacement formula).scale
          retainedAngularFanSourceClearanceFactor))[cycleIndex]? =
        some metadata)
    (cycleLiteralIndex : Nat)
    (relativeTranslate : Cell)
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          clause literal =
        Cell.add
          ((finalCoordinatedPlacement formula).position metadata.atom)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate)) :
    translatePolyline
        ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          formula).translation relativeTranslate)
        (scalePolyline retainedTerminalFanRoutingRefinement
          (allCycleRoutes
            ((finalCoordinatedSource formula).scale
              retainedAngularFanSourceClearanceFactor)
            ((finalCoordinatedPlacement formula).scale
              retainedAngularFanSourceClearanceFactor)
            cycleIndex cycleLiteralIndex)) =
      retainedFinalMatchingCycleLift
        formula clause literal
        metadata.localClauseIndex cycleLiteralIndex := by
  have metadataAtomMember :
      metadata.atom ∈
        sourceVariables
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor).erase :=
    allCycleClauseMetadata_lookup_atom_mem
      ((finalCoordinatedSource formula).scale
        retainedAngularFanSourceClearanceFactor)
      ((finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor)
      metadataLookup
  have identified :=
    retainedFinalCanonicalLiteralPosition_eq_translatedSourcePosition_imp
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
      metadata.atom metadataAtomMember relativeTranslate centersEqual
  unfold retainedFinalMatchingCycleLift
  unfold allCycleRoutes
  rw [metadataLookup, identified.1, identified.2]
  rw [show
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
        formula).translation relativeTranslate =
      Cell.scale retainedTerminalFanRoutingRefinement
        ((PeriodicEightOccurrenceSplitPositioned.placement
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)).translation
          relativeTranslate) by
    simp [retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement,
      retainedAngularFanSourceScaledRefinedPlacement,
      retainedAngularFanRefinedPlacement, finalCoordinatedPlacement]]
  rw [← scalePolyline_translatePolyline]

/-- At an equal translated center, a successful direct occurrence reuses
the certified local matching-cycle separation theorem. -/
theorem
    retainedFinalCoordinatedDirectOccurrenceRoute_avoids_translatedAllCycleRoute_of_center_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = some choice)
    {cycleClause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {cycleIndex : Nat}
    (cycleClauseMember :
      (cycleClause, cycleIndex) ∈
        (allCycleClauses
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)).zipIdx)
    {cycleLiteral :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {cycleLiteralIndex : Nat}
    (cycleLiteralMember :
      (cycleLiteral, cycleLiteralIndex) ∈
        cycleClause.literals.zipIdx)
    (relativeTranslate : Cell)
    (centersEqual :
      ∀ metadata,
        (allCycleClauseMetadata
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor))[cycleIndex]? =
            some metadata →
        PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            clause literal =
          Cell.add
            ((finalCoordinatedPlacement formula).position metadata.atom)
            ((finalCoordinatedPlacement formula).translation
              relativeTranslate)) :
    RoutesAvoidEachOther
      (retainedFinalCoordinatedDirectOccurrenceRoute
        formula choice
        (clause.scale retainedAngularFanSourceClearanceFactor)
        literal clauseIndex literalIndex)
      (translatePolyline
        ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          formula).translation relativeTranslate)
        (scalePolyline retainedTerminalFanRoutingRefinement
          (allCycleRoutes
            ((finalCoordinatedSource formula).scale
              retainedAngularFanSourceClearanceFactor)
            ((finalCoordinatedPlacement formula).scale
              retainedAngularFanSourceClearanceFactor)
            cycleIndex cycleLiteralIndex))) := by
  rcases allCycleClauseMetadata_lookup_valid
      ((finalCoordinatedSource formula).scale
        retainedAngularFanSourceClearanceFactor)
      ((finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor)
      cycleClauseMember with
    ⟨metadata, metadataLookup, metadataClauseEqual,
      localClauseMember⟩
  have routeEqual :=
    retainedFinalScaledTranslatedAllCycleRoute_eq_matchingCycleLift_of_center_eq
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
      metadataLookup cycleLiteralIndex relativeTranslate
      (centersEqual metadata metadataLookup)
  have localClauseIndexLt :
      metadata.localClauseIndex < presentedCycleVertices.length :=
    positionedCycleClause_localIndex_lt
      ((finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor)
      metadata.atom localClauseMember
  have localLiteralMember :
      (cycleLiteral, cycleLiteralIndex) ∈
        metadata.clause.literals.zipIdx := by
    simpa [metadataClauseEqual] using cycleLiteralMember
  have cycleLiteralIndexLt : cycleLiteralIndex < 2 :=
    positionedCycleClause_literalIndex_lt_two
      ((finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor)
      metadata.atom localClauseMember localLiteralMember
  have avoids :=
    retainedFinalCoordinatedDirectOccurrenceRoute_avoids_matchingCycleLift
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice
      clauseMember literalMember choiceLookup
      metadata.localClauseIndex cycleLiteralIndex
      localClauseIndexLt cycleLiteralIndexLt
  dsimp only at avoids
  rw [routeEqual]
  exact avoids

/-- A periodic copy of a valid final source variable can lie in a successful
direct choice's source-segment rectangle only at the represented endpoint. -/
theorem
    retainedFinalDirectSourceRouteChoice_sourceSegment_contains_only_translatedVariablePosition_of_valid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (choice : RetainedDirectSourceRouteChoice)
    (clauseIndex literalIndex : Nat)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex =
        some choice)
    (targetAtom :
      WrappedPeriodicPlanarSATVariable Variable)
    (targetValid :
      RetainedDrawingPeriodicPlanarSATVariableValid
        formula targetAtom.original)
    (relativeTranslate : Cell)
    (bounded :
      InClosedGridRectangle
        choice.sourceSegment.coordinateLower
        choice.sourceSegment.coordinateUpper
        (Cell.add
          ((finalCoordinatedPlacement formula).position targetAtom)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate))) :
    Cell.add
        ((finalCoordinatedPlacement formula).position targetAtom)
        ((finalCoordinatedPlacement formula).translation
          relativeTranslate) =
      choice.sourceSegment.finish := by
  rcases retainedFinalDirectSourceRouteChoice_originData
      formula clauseIndex literalIndex choice choiceLookup with
    ⟨sourceData⟩
  rcases retainedFinalVariablePositionData_of_valid
      formula wellFormed degree isLocal targetAtom targetValid with
    ⟨targetData⟩
  apply
    choice.sourceSegment_contains_only_retainedMacrocellPosition
      sourceData.center
      (Cell.add targetData.center
        ((drawing formula.incidenceGraph).periodTranslation
          relativeTranslate))
      targetData.localPosition
      (Cell.add
        ((finalCoordinatedPlacement formula).position targetAtom)
        ((finalCoordinatedPlacement formula).translation
          relativeTranslate))
      sourceData.originEq
  · rw [targetData.positionEq,
      show
        (finalCoordinatedPlacement formula).translation
            relativeTranslate =
          carrierMacroPeriodTranslation
            formula.incidenceGraph relativeTranslate by
        simpa only [finalCoordinatedPlacement] using
          retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_translation_eq_carrierMacro
            formula relativeTranslate]
    rcases targetData.center with ⟨targetX, targetY⟩
    rcases relativeTranslate with ⟨translateX, translateY⟩
    simp [carrierMacroPeriodTranslation,
      PeriodicGridDrawing.periodTranslation,
      Cell.scale, Cell.add]
    constructor <;> ring
  · exact targetData.localBounds
  · intro centersEqual
    exact
      compatibleVariableLocalPosition_of_centerKinds_periodTranslate
        formula wellFormed degree isLocal
        sourceData.centerKind targetData.centerKind centersEqual
  · exact bounded

/-- The atom recovered from any genuine final implication-cycle metadata
entry is geometrically valid in the retained planar-SAT construction. -/
theorem retainedFinalCycleMetadata_atom_valid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {metadata :
      CycleClauseMetadata
        (WrappedPeriodicPlanarSATVariable Variable)}
    {cycleIndex : Nat}
    (metadataLookup :
      (allCycleClauseMetadata
        ((finalCoordinatedSource formula).scale
          retainedAngularFanSourceClearanceFactor)
        ((finalCoordinatedPlacement formula).scale
          retainedAngularFanSourceClearanceFactor))[cycleIndex]? =
        some metadata) :
    RetainedDrawingPeriodicPlanarSATVariableValid
      formula metadata.atom.original := by
  let sourceCertificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let source :=
    (finalCoordinatedSource formula).scale
      retainedAngularFanSourceClearanceFactor
  let placement :=
    (finalCoordinatedPlacement formula).scale
      retainedAngularFanSourceClearanceFactor
  have targetAtomMemberScaled :
      metadata.atom ∈ sourceVariables source.erase :=
    allCycleClauseMetadata_lookup_atom_mem
      source placement metadataLookup
  have targetAtomMember :
      metadata.atom ∈
        sourceVariables
          (finalCoordinatedSource formula).erase := by
    simpa only [source,
      PositionedPeriodicCNF.erase_scale] using
      targetAtomMemberScaled
  rcases
      exists_positioned_members_of_mem_sourceVariables
        (finalCoordinatedSource formula) targetAtomMember with
    ⟨targetClause, targetClauseIndex,
      targetLiteral, targetLiteralIndex,
      targetClauseMember, targetLiteralMember,
      targetAtomEqual⟩
  have targetOccurrence :
      metadata.atom ∈
        (finalCoordinatedSource formula).erase.variableOccurrences := by
    have occurrence :=
      positionedLiteral_atom_mem_variableOccurrences_of_members
        (finalCoordinatedSource formula)
        targetClauseMember targetLiteralMember
    rw [targetAtomEqual] at occurrence
    exact occurrence
  apply
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSAT_variableOccurrences_valid
      formula
      sourceCertificate.graphWellFormed
      sourceCertificate.graphDegreeAtMostThree
      sourceCertificate.graphIsLocal
  simpa only [finalCoordinatedSource] using targetOccurrence

/-- A translated genuine cycle center different from the represented direct
occurrence cannot lie in the direct source segment's endpoint rectangle. -/
theorem
    retainedFinalDirectSourceRouteChoice_translatedCycleCenter_outside_of_ne
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = some choice)
    {metadata :
      CycleClauseMetadata
        (WrappedPeriodicPlanarSATVariable Variable)}
    {cycleIndex : Nat}
    (metadataLookup :
      (allCycleClauseMetadata
        ((finalCoordinatedSource formula).scale
          retainedAngularFanSourceClearanceFactor)
        ((finalCoordinatedPlacement formula).scale
          retainedAngularFanSourceClearanceFactor))[cycleIndex]? =
        some metadata)
    (relativeTranslate : Cell)
    (centersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          clause literal ≠
        Cell.add
          ((finalCoordinatedPlacement formula).position metadata.atom)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate)) :
    ¬InClosedGridRectangle
      choice.sourceSegment.coordinateLower
      choice.sourceSegment.coordinateUpper
      (Cell.add
        ((finalCoordinatedPlacement formula).position metadata.atom)
        ((finalCoordinatedPlacement formula).translation
          relativeTranslate)) := by
  let sourceCertificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  have targetValid :=
    retainedFinalCycleMetadata_atom_valid
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty metadataLookup
  intro centerInside
  have targetEqualsFinish :=
    retainedFinalDirectSourceRouteChoice_sourceSegment_contains_only_translatedVariablePosition_of_valid
      formula
      sourceCertificate.graphWellFormed
      sourceCertificate.graphDegreeAtMostThree
      sourceCertificate.graphIsLocal
      choice clauseIndex literalIndex choiceLookup
      metadata.atom targetValid relativeTranslate centerInside
  have finishEqualsCanonical :=
    retainedFinalDirectSourceRouteChoice_sourceSegment_finish
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice
      clauseMember literalMember choiceLookup
  apply centersDifferent
  exact (targetEqualsFinish.trans finishEqualsCanonical).symm

/-- Translating a genuine flattened cycle route moves its fixed radius-48
center rectangle by the corresponding fully refined period translation. -/
theorem
    retainedFinalTranslatedSourceScaledAllCycleRoute_point_in_metadataCenterRectangle
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {metadata :
      CycleClauseMetadata
        (WrappedPeriodicPlanarSATVariable Variable)}
    {cycleIndex : Nat}
    (metadataLookup :
      (allCycleClauseMetadata
        ((finalCoordinatedSource formula).scale
          retainedAngularFanSourceClearanceFactor)
        ((finalCoordinatedPlacement formula).scale
          retainedAngularFanSourceClearanceFactor))[cycleIndex]? =
        some metadata)
    (literalIndex : Nat)
    (relativeTranslate : Cell)
    {point : Cell}
    (pointMember :
      point ∈
        translatePolyline
          ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
            formula).translation relativeTranslate)
          (scalePolyline retainedTerminalFanRoutingRefinement
            (allCycleRoutes
              ((finalCoordinatedSource formula).scale
                retainedAngularFanSourceClearanceFactor)
              ((finalCoordinatedPlacement formula).scale
                retainedAngularFanSourceClearanceFactor)
              cycleIndex literalIndex))) :
    InClosedGridRectangle
      (coordinateRadiusLower 48
        (Cell.scale
          (retainedTerminalFanTotalRefinement *
            retainedAngularFanSourceClearanceFactor)
          (Cell.add
            ((finalCoordinatedPlacement formula).position metadata.atom)
            ((finalCoordinatedPlacement formula).translation
              relativeTranslate))))
      (coordinateRadiusUpper 48
        (Cell.scale
          (retainedTerminalFanTotalRefinement *
            retainedAngularFanSourceClearanceFactor)
          (Cell.add
            ((finalCoordinatedPlacement formula).position metadata.atom)
            ((finalCoordinatedPlacement formula).translation
              relativeTranslate))))
      point := by
  unfold translatePolyline at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨sourcePoint, sourcePointMember, rfl⟩
  have sourceBound :=
    retainedFinalSourceScaledAllCycleRoute_point_in_metadataCenterRectangle
      formula metadataLookup literalIndex sourcePointMember
  have translationEq :
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          formula).translation relativeTranslate =
        Cell.scale
          (retainedTerminalFanTotalRefinement *
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate) := by
    simp [retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement,
      retainedAngularFanSourceScaledRefinedPlacement,
      retainedAngularFanRefinedPlacement,
      PeriodicEightOccurrenceSplitPositioned.placement,
      PeriodicVariablePlacement.translation,
      finalCoordinatedPlacement,
      retainedTerminalFanTotalRefinement_eq,
      retainedTerminalFanRoutingRefinement,
      retainedAngularFanSourceClearanceFactor,
      refinementScale, Cell.scale]
    constructor <;> ring
  rw [translationEq]
  rcases positionEq :
      (finalCoordinatedPlacement formula).position metadata.atom with
    ⟨centerX, centerY⟩
  rcases translationBaseEq :
      (finalCoordinatedPlacement formula).translation
        relativeTranslate with
    ⟨translateX, translateY⟩
  rcases sourcePoint with ⟨pointX, pointY⟩
  simp only [positionEq,
    coordinateRadiusLower, coordinateRadiusUpper,
    InClosedGridRectangle, Cell.add, Cell.scale]
    at sourceBound ⊢
  ring_nf at sourceBound ⊢
  omega

/-- If a translated cycle center lies outside the represented source
segment's endpoint rectangle, the successful direct occurrence and that
translated flattened cycle route are strictly contact-free. -/
theorem
    retainedFinalCoordinatedDirectOccurrenceRoute_strictlyAvoids_translatedAllCycleRoute_of_center_outside
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = some choice)
    {metadata :
      CycleClauseMetadata
        (WrappedPeriodicPlanarSATVariable Variable)}
    {cycleIndex : Nat}
    (metadataLookup :
      (allCycleClauseMetadata
        ((finalCoordinatedSource formula).scale
          retainedAngularFanSourceClearanceFactor)
        ((finalCoordinatedPlacement formula).scale
          retainedAngularFanSourceClearanceFactor))[cycleIndex]? =
        some metadata)
    (cycleLiteralIndex : Nat)
    (relativeTranslate : Cell)
    (centerOutside :
      ¬InClosedGridRectangle
        choice.sourceSegment.coordinateLower
        choice.sourceSegment.coordinateUpper
        (Cell.add
          ((finalCoordinatedPlacement formula).position metadata.atom)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate))) :
    RoutesStrictlyAvoidEachOther
      (retainedFinalCoordinatedDirectOccurrenceRoute
        formula choice
        (clause.scale retainedAngularFanSourceClearanceFactor)
        literal clauseIndex literalIndex)
      (translatePolyline
        ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          formula).translation relativeTranslate)
        (scalePolyline retainedTerminalFanRoutingRefinement
          (allCycleRoutes
            ((finalCoordinatedSource formula).scale
              retainedAngularFanSourceClearanceFactor)
            ((finalCoordinatedPlacement formula).scale
              retainedAngularFanSourceClearanceFactor)
            cycleIndex cycleLiteralIndex))) := by
  have routeEqual :=
    retainedFinalCoordinatedDirectOccurrenceRoute_eq_completeFigure7Route
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice
      clauseMember literalMember choiceLookup
  rw [routeEqual]
  apply
    routesStrictlyAvoidEachOther_of_inSeparatedClosedGridRectangles
      (firstLower :=
        coordinateRadiusLower 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement * 4)
            choice.sourceSegment.coordinateLower))
      (firstUpper :=
        coordinateRadiusUpper 288
          (Cell.scale
            (retainedTerminalFanTotalRefinement * 4)
            choice.sourceSegment.coordinateUpper))
      (secondLower :=
        coordinateRadiusLower 48
          (Cell.scale
            (retainedTerminalFanTotalRefinement *
              retainedAngularFanSourceClearanceFactor)
            (Cell.add
              ((finalCoordinatedPlacement formula).position metadata.atom)
              ((finalCoordinatedPlacement formula).translation
                relativeTranslate))))
      (secondUpper :=
        coordinateRadiusUpper 48
          (Cell.scale
            (retainedTerminalFanTotalRefinement *
              retainedAngularFanSourceClearanceFactor)
            (Cell.add
              ((finalCoordinatedPlacement formula).position metadata.atom)
              ((finalCoordinatedPlacement formula).translation
                relativeTranslate))))
  · intro point pointMember
    exact
      choice.completeFigure7Route_point_in_sourceSegmentRectangle
        (retainedFinalCoordinatedOccurrenceSlot
          formula literal clauseIndex literalIndex)
        pointMember
  · intro point pointMember
    exact
      retainedFinalTranslatedSourceScaledAllCycleRoute_point_in_metadataCenterRectangle
        formula metadataLookup cycleLiteralIndex
        relativeTranslate pointMember
  · simpa [retainedAngularFanSourceClearanceFactor_eq] using
      choice.scaledSourceRectangle_separated_pointCycleRectangle
        centerOutside

/-- A successful direct occurrence is strictly separated from a translated
flattened cycle whenever their translated source centers differ. -/
theorem
    retainedFinalCoordinatedDirectOccurrenceRoute_strictlyAvoids_translatedAllCycleRoute_of_center_ne
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = some choice)
    {metadata :
      CycleClauseMetadata
        (WrappedPeriodicPlanarSATVariable Variable)}
    {cycleIndex : Nat}
    (metadataLookup :
      (allCycleClauseMetadata
        ((finalCoordinatedSource formula).scale
          retainedAngularFanSourceClearanceFactor)
        ((finalCoordinatedPlacement formula).scale
          retainedAngularFanSourceClearanceFactor))[cycleIndex]? =
        some metadata)
    (cycleLiteralIndex : Nat)
    (relativeTranslate : Cell)
    (centersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          clause literal ≠
        Cell.add
          ((finalCoordinatedPlacement formula).position metadata.atom)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate)) :
    RoutesStrictlyAvoidEachOther
      (retainedFinalCoordinatedDirectOccurrenceRoute
        formula choice
        (clause.scale retainedAngularFanSourceClearanceFactor)
        literal clauseIndex literalIndex)
      (translatePolyline
        ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          formula).translation relativeTranslate)
        (scalePolyline retainedTerminalFanRoutingRefinement
          (allCycleRoutes
            ((finalCoordinatedSource formula).scale
              retainedAngularFanSourceClearanceFactor)
            ((finalCoordinatedPlacement formula).scale
              retainedAngularFanSourceClearanceFactor)
            cycleIndex cycleLiteralIndex))) := by
  exact
    retainedFinalCoordinatedDirectOccurrenceRoute_strictlyAvoids_translatedAllCycleRoute_of_center_outside
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice
      clauseMember literalMember choiceLookup
      metadataLookup cycleLiteralIndex relativeTranslate
      (retainedFinalDirectSourceRouteChoice_translatedCycleCenter_outside_of_ne
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice
        clauseMember literalMember choiceLookup
        metadataLookup relativeTranslate centersDifferent)

/-- Every successful direct occurrence avoids every periodically translated
genuine flattened implication-cycle route. -/
theorem
    retainedFinalCoordinatedDirectOccurrenceRoute_avoids_translatedAllCycleRoute
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = some choice)
    {cycleClause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {cycleIndex : Nat}
    (cycleClauseMember :
      (cycleClause, cycleIndex) ∈
        (allCycleClauses
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)).zipIdx)
    {cycleLiteral :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {cycleLiteralIndex : Nat}
    (cycleLiteralMember :
      (cycleLiteral, cycleLiteralIndex) ∈
        cycleClause.literals.zipIdx)
    (relativeTranslate : Cell) :
    RoutesAvoidEachOther
      (retainedFinalCoordinatedDirectOccurrenceRoute
        formula choice
        (clause.scale retainedAngularFanSourceClearanceFactor)
        literal clauseIndex literalIndex)
      (translatePolyline
        ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          formula).translation relativeTranslate)
        (scalePolyline retainedTerminalFanRoutingRefinement
          (allCycleRoutes
            ((finalCoordinatedSource formula).scale
              retainedAngularFanSourceClearanceFactor)
            ((finalCoordinatedPlacement formula).scale
              retainedAngularFanSourceClearanceFactor)
            cycleIndex cycleLiteralIndex))) := by
  rcases allCycleClauseMetadata_lookup_valid
      ((finalCoordinatedSource formula).scale
        retainedAngularFanSourceClearanceFactor)
      ((finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor)
      cycleClauseMember with
    ⟨metadata, metadataLookup, _metadataClauseEqual,
      _localClauseMember⟩
  by_cases centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          clause literal =
        Cell.add
          ((finalCoordinatedPlacement formula).position metadata.atom)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate)
  · exact
      retainedFinalCoordinatedDirectOccurrenceRoute_avoids_translatedAllCycleRoute_of_center_eq
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice
        clauseMember literalMember choiceLookup
        cycleClauseMember cycleLiteralMember relativeTranslate
        (fun otherMetadata otherLookup => by
          have metadataEqual : otherMetadata = metadata :=
            Option.some.inj (otherLookup.symm.trans metadataLookup)
          rw [metadataEqual]
          exact centersEqual)
  · exact
      (retainedFinalCoordinatedDirectOccurrenceRoute_strictlyAvoids_translatedAllCycleRoute_of_center_ne
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice
        clauseMember literalMember choiceLookup
        metadataLookup cycleLiteralIndex
        relativeTranslate centersEqual).toRoutesAvoidEachOther

/-- The public coordinated source route selected by a successful direct
choice avoids every periodically translated genuine cycle route. -/
theorem
    retainedFinalCoordinatedDirectSourceRoute_avoids_translatedAllCycleRoute
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = some choice)
    {cycleClause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {cycleIndex : Nat}
    (cycleClauseMember :
      (cycleClause, cycleIndex) ∈
        (allCycleClauses
          ((finalCoordinatedSource formula).scale
            retainedAngularFanSourceClearanceFactor)
          ((finalCoordinatedPlacement formula).scale
            retainedAngularFanSourceClearanceFactor)).zipIdx)
    {cycleLiteral :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {cycleLiteralIndex : Nat}
    (cycleLiteralMember :
      (cycleLiteral, cycleLiteralIndex) ∈
        cycleClause.literals.zipIdx)
    (relativeTranslate : Cell) :
    RoutesAvoidEachOther
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula clauseIndex literalIndex)
      (translatePolyline
        ((retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement
          formula).translation relativeTranslate)
        (scalePolyline retainedTerminalFanRoutingRefinement
          (allCycleRoutes
            ((finalCoordinatedSource formula).scale
              retainedAngularFanSourceClearanceFactor)
            ((finalCoordinatedPlacement formula).scale
              retainedAngularFanSourceClearanceFactor)
            cycleIndex cycleLiteralIndex))) := by
  have scaledClauseMember :
      (clause.scale retainedAngularFanSourceClearanceFactor,
          clauseIndex) ∈
        ((finalCoordinatedSource formula).scale
          retainedAngularFanSourceClearanceFactor).clauses.zipIdx := by
    rw [PositionedPeriodicCNF.scale_clauses, List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(clause, clauseIndex), clauseMember, rfl⟩
  have clauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp scaledClauseMember
  have literalLookup :
      (clause.scale
        retainedAngularFanSourceClearanceFactor).literals[
          literalIndex]? = some literal := by
    simpa using
      (List.mem_zipIdx_iff_getElem?).mp literalMember
  rw [
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_some
      formula clauseIndex literalIndex choice
      (clause.scale retainedAngularFanSourceClearanceFactor)
      literal choiceLookup clauseLookup literalLookup]
  exact
    retainedFinalCoordinatedDirectOccurrenceRoute_avoids_translatedAllCycleRoute
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice
      clauseMember literalMember choiceLookup
      cycleClauseMember cycleLiteralMember relativeTranslate

end PeriodicOrthocrossing
end LeanTrominoes
