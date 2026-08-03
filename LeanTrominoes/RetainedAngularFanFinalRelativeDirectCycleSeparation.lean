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

end PeriodicOrthocrossing
end LeanTrominoes
