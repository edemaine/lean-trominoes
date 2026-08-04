import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineNormalizedRoutes
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineInheritedConnectorSeparation
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFigureNineClearance
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineSplicedRouteSeparation

/-!
# Relative separation interface for ordered retained Figure 9 routes

This module specializes the generic relative splice assembly to the retained
clockwise-ordered fixed-eight source.  It identifies the complete global
separation obligation with six explicit component predicates for each pair of
incidences and relative lattice translation, and connects that obligation all
the way to ribbon readiness of the normalized drawing.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 2000000

local instance orderedComposedVariableDecidableEqForSeparation
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

/-- A distinct final relative occurrence remains distinct after recovering
its original source coordinates and changing to the inherited source-route
gauges. -/
private theorem inheritedSourceOccurrencesDifferent
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    {firstClauseIndex firstLiteralIndex
      secondClauseIndex secondLiteralIndex : Nat}
    (first :
      PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData
        source sourcePlacement firstClauseIndex firstLiteralIndex)
    (second :
      PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData
        source sourcePlacement secondClauseIndex secondLiteralIndex)
    (relativeTranslate : Cell)
    (generatedOccurrencesDifferent :
      ((firstClauseIndex, firstLiteralIndex), (0, 0)) ≠
        ((secondClauseIndex, secondLiteralIndex), relativeTranslate)) :
    ((first.sourceClauseIndex, first.sourceLiteralIndex), (0, 0)) ≠
      ((second.sourceClauseIndex, second.sourceLiteralIndex),
        PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRelativeTranslate
          first.sourceClause second.sourceClause
          first.generatedClause second.generatedClause
          relativeTranslate) := by
  intro sourceOccurrencesEqual
  have sourceClauseIndexEqual :
      first.sourceClauseIndex = second.sourceClauseIndex :=
    congrArg (fun occurrence : (Nat × Nat) × Cell => occurrence.1.1)
      sourceOccurrencesEqual
  have sourceLiteralIndexEqual :
      first.sourceLiteralIndex = second.sourceLiteralIndex :=
    congrArg (fun occurrence : (Nat × Nat) × Cell => occurrence.1.2)
      sourceOccurrencesEqual
  have sourceCoordinatesNotDistinct :
      ¬ (first.sourceClauseIndex ≠ second.sourceClauseIndex ∨
        first.sourceLiteralIndex ≠ second.sourceLiteralIndex) := by
    simp [sourceClauseIndexEqual, sourceLiteralIndexEqual]
  have generatedCoordinatesNotDistinct :
      ¬ (firstClauseIndex ≠ secondClauseIndex ∨
        firstLiteralIndex ≠ secondLiteralIndex) := by
    intro generatedCoordinatesDistinct
    exact sourceCoordinatesNotDistinct
      (first.sourceCoordinatesDistinct_of_generatedDistinct
        source sourcePlacement sourceWidth second
        generatedCoordinatesDistinct)
  simp only [not_or, not_ne_iff] at generatedCoordinatesNotDistinct
  have sourceClauseEqual : first.sourceClause = second.sourceClause := by
    have secondMember :
        (second.sourceClause, first.sourceClauseIndex) ∈
          source.clauses.zipIdx := by
      simpa [sourceClauseIndexEqual] using second.sourceClauseMember
    exact
      (List.mem_zipIdx' first.sourceClauseMember).2.trans
        (List.mem_zipIdx' secondMember).2.symm
  have generatedClauseEqual :
      first.generatedClause = second.generatedClause := by
    have secondMember :
        (second.generatedClause, firstClauseIndex) ∈
          (PeriodicOneInThreeNoUnitsPositioned.formula
            (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx := by
      simpa [generatedCoordinatesNotDistinct.1] using
        second.generatedClauseMember
    exact
      (List.mem_zipIdx' first.generatedClauseMember).2.trans
        (List.mem_zipIdx' secondMember).2.symm
  have adjustedTranslateZero :
      (0, 0) =
        PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRelativeTranslate
          first.sourceClause second.sourceClause
          first.generatedClause second.generatedClause
          relativeTranslate :=
    congrArg (fun occurrence : (Nat × Nat) × Cell => occurrence.2)
      sourceOccurrencesEqual
  have relativeTranslateZero : relativeTranslate = (0, 0) := by
    simpa [
      PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRelativeTranslate,
      PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRouteGauge,
      sourceClauseEqual, generatedClauseEqual,
      Cell.add, Cell.sub] using adjustedTranslateZero.symm
  apply generatedOccurrencesDifferent
  apply Prod.ext
  · exact Prod.ext generatedCoordinatesNotDistinct.1
      generatedCoordinatesNotDistinct.2
  · exact relativeTranslateZero.symm

/-- Two inherited source-route cores of the retained ordered construction
remain relatively separated after factor-`72` refinement.  Removing their
obsolete clause-side heads leaves routes whose only possible listed contact
is at their variable-side tails. -/
theorem
    retainedOrderedFixedEightInheritedSourceRouteTails_relativeSeparated
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {firstClauseIndex firstLiteralIndex
      secondClauseIndex secondLiteralIndex : Nat}
    (first :
      PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        firstClauseIndex firstLiteralIndex)
    (second :
      PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        secondClauseIndex secondLiteralIndex)
    (relativeTranslate : Cell)
    (generatedOccurrencesDifferent :
      ((firstClauseIndex, firstLiteralIndex), (0, 0)) ≠
        ((secondClauseIndex, secondLiteralIndex), relativeTranslate)) :
    let sourceFormula :=
      retainedFigureNineClearancePositionedFormula source
    let sourcePlacement :=
      retainedFigureNineClearancePlacement source
    let sourceRoutes :=
      retainedFigureNineClearanceIncidenceRoutes source
    let outputPlacement :=
      PlanarOneInThreeNoUnitsFigureNine.composedPlacement
        sourceFormula sourcePlacement
    let firstTransformed :=
      PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRoute
        outputPlacement sourcePlacement first.sourceClause
        first.generatedClause
        (sourceRoutes first.sourceClauseIndex first.sourceLiteralIndex)
    let secondTransformed :=
      (PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRoute
        outputPlacement sourcePlacement second.sourceClause
        second.generatedClause
        (sourceRoutes second.sourceClauseIndex second.sourceLiteralIndex)).map
          (Cell.add (outputPlacement.translation relativeTranslate))
    PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
        firstTransformed.tail secondTransformed.tail ∧
      PlanarThreeSAT.EmbeddedCNFIncidenceDrawing.RoutesMeetOnlyAtTails
        firstTransformed.tail secondTransformed.tail := by
  let sourceFormula :=
    retainedFigureNineClearancePositionedFormula source
  let sourcePlacement :=
    retainedFigureNineClearancePlacement source
  let sourceRoutes :=
    retainedFigureNineClearanceIncidenceRoutes source
  have sourceOccurrencesDifferent :=
    inheritedSourceOccurrencesDifferent
      sourceFormula sourcePlacement
      (retainedFigureNineClearancePositionedFormula_widthAtMostThree
        source sourceWidth)
      first second relativeTranslate generatedOccurrencesDifferent
  have sourceAvoids :=
    (retainedFigureNineClearanceIncidenceRoutes_relativeAvoidEachOther
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).coordinate
      first.sourceClause first.sourceClauseIndex first.sourceClauseMember
      first.sourceLiteral first.sourceLiteralIndex first.sourceLiteralMember
      second.sourceClause second.sourceClauseIndex second.sourceClauseMember
      second.sourceLiteral second.sourceLiteralIndex second.sourceLiteralMember
      (PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRelativeTranslate
        first.sourceClause second.sourceClause
        first.generatedClause second.generatedClause relativeTranslate)
      sourceOccurrencesDifferent
  exact
    PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRoute_tails_relative_separated
      sourceFormula sourcePlacement
      first.sourceClause second.sourceClause
      first.generatedClause second.generatedClause
      (sourceRoutes first.sourceClauseIndex first.sourceLiteralIndex)
      (sourceRoutes second.sourceClauseIndex second.sourceLiteralIndex)
      relativeTranslate sourceAvoids
      (retainedFigureNineClearanceIncidenceRoutes_isSimple
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty first.sourceClauseMember
        first.sourceLiteralMember).1
      (retainedFigureNineClearanceIncidenceRoutes_isSimple
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty second.sourceClauseMember
        second.sourceLiteralMember).1

/-- Unequal retained source gauges let the two inherited Figure 9 suffixes
be assembled from strictly separated finite connectors, strictly separated
connector–tail cross pairs, and source tails that can meet only at their
variable-side endpoints. -/
theorem
    retainedOrderedFixedEightFigureNine_inheritedSuffixes_relativeAvoidEachOther_of_sourceGaugesNe
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {firstClauseIndex firstLiteralIndex
      secondClauseIndex secondLiteralIndex : Nat}
    (first :
      PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        firstClauseIndex firstLiteralIndex)
    (second :
      PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        secondClauseIndex secondLiteralIndex)
    (relativeTranslate : Cell)
    (sourceGaugesNe :
      PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
          (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source))
          first.sourceClause first.generatedClause ≠
        Cell.add
          ((PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source)).translation
              relativeTranslate)
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
            (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
              (retainedFigureNineClearancePositionedFormula source)
              (retainedFigureNineClearancePlacement source))
            second.sourceClause second.generatedClause))
    (generatedOccurrencesDifferent :
      ((firstClauseIndex, firstLiteralIndex), (0, 0)) ≠
        ((secondClauseIndex, secondLiteralIndex), relativeTranslate)) :
    let clearanceWidth :=
      retainedFigureNineClearancePositionedFormula_widthAtMostThree
        source sourceWidth
    let outputPlacement :=
      PlanarOneInThreeNoUnitsFigureNine.composedPlacement
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
    RoutesAvoidEachOther
      (PlanarOneInThreeNoUnitsFigureNine.fanInheritedRouteSuffix
        outputPlacement
        (retainedFigureNineClearancePlacement source)
        first.sourceClause first.generatedClause
        (PositionedPeriodicCNF.clauseExitFanData
          first.sourceClause first.sourceClauseIndex
          (retainedFigureNineClearanceIncidenceRoutes source))
        (first.sourceSlot clearanceWidth)
        (retainedFigureNineClearanceIncidenceRoutes
          source first.sourceClauseIndex first.sourceLiteralIndex))
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
  let clearancePlacement :=
    retainedFigureNineClearancePlacement source
  let clearanceWidth :=
    retainedFigureNineClearancePositionedFormula_widthAtMostThree
      source sourceWidth
  let outputPlacement :=
    PlanarOneInThreeNoUnitsFigureNine.composedPlacement
      (retainedFigureNineClearancePositionedFormula source)
      clearancePlacement
  let offset := outputPlacement.translation relativeTranslate
  let firstConnector :=
    (PositionedPeriodicCNF.clauseExitFanData
      first.sourceClause first.sourceClauseIndex
      (retainedFigureNineClearanceIncidenceRoutes source)
    ).translatedRoute
      (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
        outputPlacement first.sourceClause first.generatedClause)
      (first.sourceSlot clearanceWidth)
  let secondConnectorBase :=
    (PositionedPeriodicCNF.clauseExitFanData
      second.sourceClause second.sourceClauseIndex
      (retainedFigureNineClearanceIncidenceRoutes source)
    ).translatedRoute
      (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
        outputPlacement second.sourceClause second.generatedClause)
      (second.sourceSlot clearanceWidth)
  let secondConnector := translatePolyline offset secondConnectorBase
  let firstTail :=
    (PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRoute
      outputPlacement clearancePlacement
      first.sourceClause first.generatedClause
      (retainedFigureNineClearanceIncidenceRoutes
        source first.sourceClauseIndex first.sourceLiteralIndex)).tail
  let secondTailBase :=
    (PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRoute
      outputPlacement clearancePlacement
      second.sourceClause second.generatedClause
      (retainedFigureNineClearanceIncidenceRoutes
        source second.sourceClauseIndex second.sourceLiteralIndex)).tail
  let secondTail := translatePolyline offset secondTailBase
  have connectorsStrict :
      RoutesStrictlyAvoidEachOther firstConnector secondConnector := by
    simpa [firstConnector, secondConnector, secondConnectorBase,
      outputPlacement, clearancePlacement, clearanceWidth, offset] using
      retainedOrderedFixedEightFigureNine_inheritedConnectors_strictlyAvoidEachOther_of_sourceGaugesNe
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty first second relativeTranslate sourceGaugesNe
  have connectorContactsAtHeads :
      RoutesMeetOnlyAtHeads firstConnector secondConnector := by
    intro firstPoint firstMember secondPoint secondMember pointsEqual
    exact (connectorsStrict.2.2.2
      firstPoint firstMember secondPoint secondMember pointsEqual).elim
  have firstConnectorAvoidsSecondTail :
      RoutesStrictlyAvoidEachOther firstConnector secondTail := by
    simpa [firstConnector, secondTail, secondTailBase,
      outputPlacement, clearancePlacement, clearanceWidth, offset] using
      retainedOrderedFixedEightFigureNine_inheritedConnector_strictlyAvoids_translatedInheritedSourceTail_of_sourceGaugesNe
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty first second relativeTranslate sourceGaugesNe
  have firstTailAvoidsSecondConnector :
      RoutesStrictlyAvoidEachOther firstTail secondConnector := by
    simpa [firstTail, secondConnector, secondConnectorBase,
      outputPlacement, clearancePlacement, clearanceWidth, offset] using
      retainedOrderedFixedEightFigureNine_inheritedSourceTail_strictlyAvoids_translatedInheritedConnector_of_sourceGaugesNe
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty first second relativeTranslate sourceGaugesNe
  have tailsSeparated :=
    retainedOrderedFixedEightInheritedSourceRouteTails_relativeSeparated
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty first second relativeTranslate
      generatedOccurrencesDifferent
  have tailsAvoid : RoutesAvoidEachOther firstTail secondTail := by
    simpa [firstTail, secondTail, secondTailBase,
      outputPlacement, clearancePlacement, offset,
      translatePolyline] using tailsSeparated.1
  have tailContactsAtTails :
      RoutesMeetOnlyAtTails firstTail secondTail := by
    simpa [firstTail, secondTail, secondTailBase,
      outputPlacement, clearancePlacement, offset,
      translatePolyline] using tailsSeparated.2
  rcases
      retainedOrderedFixedEightFigureNine_inheritedConnector_spliceEndpoint
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty first with
    ⟨firstSplicePoint, firstConnectorLast, firstTailHead⟩
  rcases
      retainedOrderedFixedEightFigureNine_inheritedConnector_spliceEndpoint
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty second with
    ⟨secondSplicePoint, secondConnectorBaseLast, secondTailBaseHead⟩
  have firstConnectorLast' :
      firstConnector.getLast? = some firstSplicePoint := by
    simpa [firstConnector, outputPlacement,
      clearancePlacement, clearanceWidth] using firstConnectorLast
  have firstTailHead' :
      firstTail.head? = some firstSplicePoint := by
    simpa [firstTail, outputPlacement,
      clearancePlacement] using firstTailHead
  have secondConnectorLast :
      secondConnector.getLast? =
        some (Cell.add offset secondSplicePoint) := by
    simpa [secondConnector, secondConnectorBase,
      translatePolyline] using
        congrArg (Option.map (Cell.add offset)) secondConnectorBaseLast
  have secondTailHead :
      secondTail.head? =
        some (Cell.add offset secondSplicePoint) := by
    simpa [secondTail, secondTailBase,
      translatePolyline] using
        congrArg (Option.map (Cell.add offset)) secondTailBaseHead
  have assembled :=
    connectorsStrict.toRoutesAvoidEachOther
      |>.join_tails_of_prefix_heads_and_suffix_tails
        connectorContactsAtHeads
        firstConnectorAvoidsSecondTail
        firstTailAvoidsSecondConnector
        tailsAvoid tailContactsAtTails
        firstConnectorLast' firstTailHead'
        secondConnectorLast secondTailHead
  simpa [PlanarOneInThreeNoUnitsFigureNine.fanInheritedRouteSuffix,
    replacePolylineHead,
    firstConnector, secondConnector, secondConnectorBase,
    firstTail, secondTail, secondTailBase,
    outputPlacement, clearancePlacement, clearanceWidth, offset,
    translatePolyline_joinAtEndpoint] using assembled

/-- Equal retained source gauges let the two inherited Figure 9 suffixes be
assembled from strictly separated finite connectors, strictly separated
connector–tail cross pairs, and source tails that can meet only at their
variable-side endpoints. -/
theorem
    retainedOrderedFixedEightFigureNine_inheritedSuffixes_relativeAvoidEachOther_of_sourceGaugesEqual
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {firstClauseIndex firstLiteralIndex
      secondClauseIndex secondLiteralIndex : Nat}
    (first :
      PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        firstClauseIndex firstLiteralIndex)
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
          first.sourceClause first.generatedClause =
        Cell.add
          ((PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source)).translation
              relativeTranslate)
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
            (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
              (retainedFigureNineClearancePositionedFormula source)
              (retainedFigureNineClearancePlacement source))
            second.sourceClause second.generatedClause))
    (generatedOccurrencesDifferent :
      ((firstClauseIndex, firstLiteralIndex), (0, 0)) ≠
        ((secondClauseIndex, secondLiteralIndex), relativeTranslate)) :
    let clearanceWidth :=
      retainedFigureNineClearancePositionedFormula_widthAtMostThree
        source sourceWidth
    let outputPlacement :=
      PlanarOneInThreeNoUnitsFigureNine.composedPlacement
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
    RoutesAvoidEachOther
      (PlanarOneInThreeNoUnitsFigureNine.fanInheritedRouteSuffix
        outputPlacement
        (retainedFigureNineClearancePlacement source)
        first.sourceClause first.generatedClause
        (PositionedPeriodicCNF.clauseExitFanData
          first.sourceClause first.sourceClauseIndex
          (retainedFigureNineClearanceIncidenceRoutes source))
        (first.sourceSlot clearanceWidth)
        (retainedFigureNineClearanceIncidenceRoutes
          source first.sourceClauseIndex first.sourceLiteralIndex))
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
  let clearancePlacement :=
    retainedFigureNineClearancePlacement source
  let clearanceWidth :=
    retainedFigureNineClearancePositionedFormula_widthAtMostThree
      source sourceWidth
  let outputPlacement :=
    PlanarOneInThreeNoUnitsFigureNine.composedPlacement
      (retainedFigureNineClearancePositionedFormula source)
      clearancePlacement
  let offset := outputPlacement.translation relativeTranslate
  let firstConnector :=
    (PositionedPeriodicCNF.clauseExitFanData
      first.sourceClause first.sourceClauseIndex
      (retainedFigureNineClearanceIncidenceRoutes source)
    ).translatedRoute
      (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
        outputPlacement first.sourceClause first.generatedClause)
      (first.sourceSlot clearanceWidth)
  let secondConnectorBase :=
    (PositionedPeriodicCNF.clauseExitFanData
      second.sourceClause second.sourceClauseIndex
      (retainedFigureNineClearanceIncidenceRoutes source)
    ).translatedRoute
      (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
        outputPlacement second.sourceClause second.generatedClause)
      (second.sourceSlot clearanceWidth)
  let secondConnector := translatePolyline offset secondConnectorBase
  let firstTail :=
    (PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRoute
      outputPlacement clearancePlacement
      first.sourceClause first.generatedClause
      (retainedFigureNineClearanceIncidenceRoutes
        source first.sourceClauseIndex first.sourceLiteralIndex)).tail
  let secondTailBase :=
    (PlanarOneInThreeNoUnitsFigureNine.inheritedSourceRoute
      outputPlacement clearancePlacement
      second.sourceClause second.generatedClause
      (retainedFigureNineClearanceIncidenceRoutes
        source second.sourceClauseIndex second.sourceLiteralIndex)).tail
  let secondTail := translatePolyline offset secondTailBase
  have connectorsStrict :
      RoutesStrictlyAvoidEachOther firstConnector secondConnector := by
    simpa [firstConnector, secondConnector, secondConnectorBase,
      outputPlacement, clearancePlacement, clearanceWidth, offset] using
      retainedOrderedFixedEightFigureNine_inheritedConnectors_strictlyAvoidEachOther_of_sourceGaugesEqual
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty first second relativeTranslate
        sourceGaugesEqual generatedOccurrencesDifferent
  have connectorContactsAtHeads :
      RoutesMeetOnlyAtHeads firstConnector secondConnector := by
    intro firstPoint firstMember secondPoint secondMember pointsEqual
    exact (connectorsStrict.2.2.2
      firstPoint firstMember secondPoint secondMember pointsEqual).elim
  have firstConnectorAvoidsSecondTail :
      RoutesStrictlyAvoidEachOther firstConnector secondTail := by
    simpa [firstConnector, secondTail, secondTailBase,
      outputPlacement, clearancePlacement, clearanceWidth, offset] using
      retainedOrderedFixedEightFigureNine_inheritedConnector_strictlyAvoids_translatedInheritedSourceTail_of_sourceGaugesEqual
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty first second relativeTranslate
        sourceGaugesEqual generatedOccurrencesDifferent
  have firstTailAvoidsSecondConnector :
      RoutesStrictlyAvoidEachOther firstTail secondConnector := by
    simpa [firstTail, secondConnector, secondConnectorBase,
      outputPlacement, clearancePlacement, clearanceWidth, offset] using
      retainedOrderedFixedEightFigureNine_inheritedSourceTail_strictlyAvoids_translatedInheritedConnector_of_sourceGaugesEqual
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty first second relativeTranslate
        sourceGaugesEqual generatedOccurrencesDifferent
  have tailsSeparated :=
    retainedOrderedFixedEightInheritedSourceRouteTails_relativeSeparated
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty first second relativeTranslate
      generatedOccurrencesDifferent
  have tailsAvoid : RoutesAvoidEachOther firstTail secondTail := by
    simpa [firstTail, secondTail, secondTailBase,
      outputPlacement, clearancePlacement, offset,
      translatePolyline] using tailsSeparated.1
  have tailContactsAtTails :
      RoutesMeetOnlyAtTails firstTail secondTail := by
    simpa [firstTail, secondTail, secondTailBase,
      outputPlacement, clearancePlacement, offset,
      translatePolyline] using tailsSeparated.2
  rcases
      retainedOrderedFixedEightFigureNine_inheritedConnector_spliceEndpoint
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty first with
    ⟨firstSplicePoint, firstConnectorLast, firstTailHead⟩
  rcases
      retainedOrderedFixedEightFigureNine_inheritedConnector_spliceEndpoint
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty second with
    ⟨secondSplicePoint, secondConnectorBaseLast, secondTailBaseHead⟩
  have firstConnectorLast' :
      firstConnector.getLast? = some firstSplicePoint := by
    simpa [firstConnector, outputPlacement,
      clearancePlacement, clearanceWidth] using firstConnectorLast
  have firstTailHead' :
      firstTail.head? = some firstSplicePoint := by
    simpa [firstTail, outputPlacement,
      clearancePlacement] using firstTailHead
  have secondConnectorLast :
      secondConnector.getLast? =
        some (Cell.add offset secondSplicePoint) := by
    simpa [secondConnector, secondConnectorBase,
      translatePolyline] using
        congrArg (Option.map (Cell.add offset)) secondConnectorBaseLast
  have secondTailHead :
      secondTail.head? =
        some (Cell.add offset secondSplicePoint) := by
    simpa [secondTail, secondTailBase,
      translatePolyline] using
        congrArg (Option.map (Cell.add offset)) secondTailBaseHead
  have assembled :=
    connectorsStrict.toRoutesAvoidEachOther
      |>.join_tails_of_prefix_heads_and_suffix_tails
        connectorContactsAtHeads
        firstConnectorAvoidsSecondTail
        firstTailAvoidsSecondConnector
        tailsAvoid tailContactsAtTails
        firstConnectorLast' firstTailHead'
        secondConnectorLast secondTailHead
  simpa [PlanarOneInThreeNoUnitsFigureNine.fanInheritedRouteSuffix,
    replacePolylineHead,
    firstConnector, secondConnector, secondConnectorBase,
    firstTail, secondTail, secondTailBase,
    outputPlacement, clearancePlacement, clearanceWidth, offset,
    translatePolyline_joinAtEndpoint] using assembled

/-- The unequal-source-gauge inherited branch supplies all four
geometric avoidances required by the generic relative splice assembler. -/
theorem
    retainedOrderedFixedEightFigureNine_relativeSplicedRoutePairAvoidances_of_inherited_sourceGaugesNe
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {firstClauseIndex firstLiteralIndex
      secondClauseIndex secondLiteralIndex : Nat}
    (first :
      PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        firstClauseIndex firstLiteralIndex)
    (second :
      PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        secondClauseIndex secondLiteralIndex)
    (firstLookup :
      PlanarOneInThreeNoUnitsFigureNine.inheritedIncidenceData?
          (retainedFigureNineClearancePositionedFormula source)
          (retainedFigureNineClearancePlacement source)
          firstClauseIndex firstLiteralIndex = some first)
    (secondLookup :
      PlanarOneInThreeNoUnitsFigureNine.inheritedIncidenceData?
          (retainedFigureNineClearancePositionedFormula source)
          (retainedFigureNineClearancePlacement source)
          secondClauseIndex secondLiteralIndex = some second)
    (relativeTranslate : Cell)
    (sourceGaugesNe :
      PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
          (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source))
          first.sourceClause first.generatedClause ≠
        Cell.add
          ((PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source)).translation
              relativeTranslate)
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
            (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
              (retainedFigureNineClearancePositionedFormula source)
              (retainedFigureNineClearancePlacement source))
            second.sourceClause second.generatedClause))
    (generatedOccurrencesDifferent :
      ((firstClauseIndex, firstLiteralIndex), (0, 0)) ≠
        ((secondClauseIndex, secondLiteralIndex), relativeTranslate)) :
    PlanarOneInThreeNoUnitsFigureNine.RelativeSplicedRoutePairAvoidances
      (retainedFigureNineClearancePositionedFormula source)
      (retainedFigureNineClearancePlacement source)
      (retainedFigureNineClearancePositionedFormula_widthAtMostThree
        source sourceWidth)
      (retainedFigureNineClearancePositionedFormula_allAtomsNodup
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsOriginalInheritedRouteSuffixes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      firstClauseIndex firstLiteralIndex
      secondClauseIndex secondLiteralIndex relativeTranslate := by
  let clearanceSource :=
    retainedFigureNineClearancePositionedFormula source
  let clearancePlacement :=
    retainedFigureNineClearancePlacement source
  let clearanceWidth :=
    retainedFigureNineClearancePositionedFormula_widthAtMostThree
      source sourceWidth
  let clearanceDistinct :=
    retainedFigureNineClearancePositionedFormula_allAtomsNodup
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let original :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsOriginalInheritedRouteSuffixes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let suffixes :=
    PlanarOneInThreeNoUnitsFigureNine.completeRouteSuffixes
      clearanceSource clearancePlacement clearanceWidth
      clearanceDistinct original
  let outputPlacement :=
    PlanarOneInThreeNoUnitsFigureNine.composedPlacement
      clearanceSource clearancePlacement
  let offset := outputPlacement.translation relativeTranslate
  have firstSuffixEq :
      suffixes.routes firstClauseIndex firstLiteralIndex =
        PlanarOneInThreeNoUnitsFigureNine.fanInheritedRouteSuffix
          outputPlacement clearancePlacement
          first.sourceClause first.generatedClause
          (PositionedPeriodicCNF.clauseExitFanData
            first.sourceClause first.sourceClauseIndex
            (retainedFigureNineClearanceIncidenceRoutes source))
          (first.sourceSlot clearanceWidth)
          (retainedFigureNineClearanceIncidenceRoutes
            source first.sourceClauseIndex first.sourceLiteralIndex) := by
    have completedShape :=
      PlanarOneInThreeNoUnitsFigureNine.completeRouteSuffixes_routes_of_members
        clearanceSource clearancePlacement clearanceWidth
        clearanceDistinct original first.generatedClauseMember
        first.generatedLiteralMember
    rw [first.literalAtom] at completedShape
    rw [completedShape]
    change
      PlanarOneInThreeNoUnitsFigureNine.orderedInheritedRouteSuffixesRoutes
          clearanceSource clearancePlacement clearanceWidth
          (retainedFigureNineClearanceIncidenceRoutes source)
          firstClauseIndex firstLiteralIndex = _
    exact
      PlanarOneInThreeNoUnitsFigureNine.orderedInheritedRouteSuffixesRoutes_eq_fanInheritedRouteSuffix_of_lookup
        clearanceSource clearancePlacement clearanceWidth
        (retainedFigureNineClearanceIncidenceRoutes source)
        firstClauseIndex firstLiteralIndex first firstLookup
  have secondSuffixEq :
      suffixes.routes secondClauseIndex secondLiteralIndex =
        PlanarOneInThreeNoUnitsFigureNine.fanInheritedRouteSuffix
          outputPlacement clearancePlacement
          second.sourceClause second.generatedClause
          (PositionedPeriodicCNF.clauseExitFanData
            second.sourceClause second.sourceClauseIndex
            (retainedFigureNineClearanceIncidenceRoutes source))
          (second.sourceSlot clearanceWidth)
          (retainedFigureNineClearanceIncidenceRoutes
            source second.sourceClauseIndex second.sourceLiteralIndex) := by
    have completedShape :=
      PlanarOneInThreeNoUnitsFigureNine.completeRouteSuffixes_routes_of_members
        clearanceSource clearancePlacement clearanceWidth
        clearanceDistinct original second.generatedClauseMember
        second.generatedLiteralMember
    rw [second.literalAtom] at completedShape
    rw [completedShape]
    change
      PlanarOneInThreeNoUnitsFigureNine.orderedInheritedRouteSuffixesRoutes
          clearanceSource clearancePlacement clearanceWidth
          (retainedFigureNineClearanceIncidenceRoutes source)
          secondClauseIndex secondLiteralIndex = _
    exact
      PlanarOneInThreeNoUnitsFigureNine.orderedInheritedRouteSuffixesRoutes_eq_fanInheritedRouteSuffix_of_lookup
        clearanceSource clearancePlacement clearanceWidth
        (retainedFigureNineClearanceIncidenceRoutes source)
        secondClauseIndex secondLiteralIndex second secondLookup
  have localsAvoid :=
    retainedOrderedFixedEightFigureNineNormalizedLocalRoutes_relative_avoidEachOther
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty first.generatedClauseMember
      second.generatedClauseMember first.generatedLiteralMember
      second.generatedLiteralMember relativeTranslate
      generatedOccurrencesDifferent
  have firstLocalSecondSuffix :=
    retainedOrderedFixedEightFigureNine_inheritedLocal_strictlyAvoids_translatedInheritedSuffix_of_sourceGaugesNe
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty first second relativeTranslate
      sourceGaugesNe
  have firstSuffixSecondLocal :=
    retainedOrderedFixedEightFigureNine_inheritedSuffix_strictlyAvoids_translatedInheritedLocal_of_sourceGaugesNe
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty first second relativeTranslate
      sourceGaugesNe
  have suffixesAvoid :=
    retainedOrderedFixedEightFigureNine_inheritedSuffixes_relativeAvoidEachOther_of_sourceGaugesNe
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty first second relativeTranslate
      sourceGaugesNe generatedOccurrencesDifferent
  change
    RoutesAvoidEachOther
        (PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
          clearanceSource clearancePlacement
          firstClauseIndex firstLiteralIndex)
        (translatePolyline offset
          (PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
            clearanceSource clearancePlacement
            secondClauseIndex secondLiteralIndex)) ∧
      RoutesStrictlyAvoidEachOther
        (PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
          clearanceSource clearancePlacement
          firstClauseIndex firstLiteralIndex)
        (translatePolyline offset
          (suffixes.routes secondClauseIndex secondLiteralIndex)) ∧
      RoutesStrictlyAvoidEachOther
        (suffixes.routes firstClauseIndex firstLiteralIndex)
        (translatePolyline offset
          (PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
            clearanceSource clearancePlacement
            secondClauseIndex secondLiteralIndex)) ∧
      RoutesAvoidEachOther
        (suffixes.routes firstClauseIndex firstLiteralIndex)
        (translatePolyline offset
          (suffixes.routes secondClauseIndex secondLiteralIndex))
  rw [firstSuffixEq, secondSuffixEq]
  exact
    ⟨by simpa [translatePolyline, clearanceSource,
        clearancePlacement, outputPlacement, offset] using localsAvoid,
      by simpa [clearanceSource, clearancePlacement,
        clearanceWidth, outputPlacement, offset] using
          firstLocalSecondSuffix,
      by simpa [clearanceSource, clearancePlacement,
        clearanceWidth, outputPlacement, offset] using
          firstSuffixSecondLocal,
      by simpa [clearanceSource, clearancePlacement,
        clearanceWidth, outputPlacement, offset] using suffixesAvoid⟩



/-- The equal-source-gauge inherited branch supplies all four geometric
avoidances required by the generic relative splice assembler. -/
theorem
    retainedOrderedFixedEightFigureNine_relativeSplicedRoutePairAvoidances_of_inherited_sourceGaugesEqual
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {firstClauseIndex firstLiteralIndex
      secondClauseIndex secondLiteralIndex : Nat}
    (first :
      PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        firstClauseIndex firstLiteralIndex)
    (second :
      PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        secondClauseIndex secondLiteralIndex)
    (firstLookup :
      PlanarOneInThreeNoUnitsFigureNine.inheritedIncidenceData?
          (retainedFigureNineClearancePositionedFormula source)
          (retainedFigureNineClearancePlacement source)
          firstClauseIndex firstLiteralIndex = some first)
    (secondLookup :
      PlanarOneInThreeNoUnitsFigureNine.inheritedIncidenceData?
          (retainedFigureNineClearancePositionedFormula source)
          (retainedFigureNineClearancePlacement source)
          secondClauseIndex secondLiteralIndex = some second)
    (relativeTranslate : Cell)
    (sourceGaugesEqual :
      PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
          (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source))
          first.sourceClause first.generatedClause =
        Cell.add
          ((PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source)).translation
              relativeTranslate)
          (PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
            (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
              (retainedFigureNineClearancePositionedFormula source)
              (retainedFigureNineClearancePlacement source))
            second.sourceClause second.generatedClause))
    (generatedOccurrencesDifferent :
      ((firstClauseIndex, firstLiteralIndex), (0, 0)) ≠
        ((secondClauseIndex, secondLiteralIndex), relativeTranslate)) :
    PlanarOneInThreeNoUnitsFigureNine.RelativeSplicedRoutePairAvoidances
      (retainedFigureNineClearancePositionedFormula source)
      (retainedFigureNineClearancePlacement source)
      (retainedFigureNineClearancePositionedFormula_widthAtMostThree
        source sourceWidth)
      (retainedFigureNineClearancePositionedFormula_allAtomsNodup
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsOriginalInheritedRouteSuffixes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      firstClauseIndex firstLiteralIndex
      secondClauseIndex secondLiteralIndex relativeTranslate := by
  let clearanceSource :=
    retainedFigureNineClearancePositionedFormula source
  let clearancePlacement :=
    retainedFigureNineClearancePlacement source
  let clearanceWidth :=
    retainedFigureNineClearancePositionedFormula_widthAtMostThree
      source sourceWidth
  let clearanceDistinct :=
    retainedFigureNineClearancePositionedFormula_allAtomsNodup
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let original :=
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsOriginalInheritedRouteSuffixes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let suffixes :=
    PlanarOneInThreeNoUnitsFigureNine.completeRouteSuffixes
      clearanceSource clearancePlacement clearanceWidth
      clearanceDistinct original
  let outputPlacement :=
    PlanarOneInThreeNoUnitsFigureNine.composedPlacement
      clearanceSource clearancePlacement
  let offset := outputPlacement.translation relativeTranslate
  have firstSuffixEq :
      suffixes.routes firstClauseIndex firstLiteralIndex =
        PlanarOneInThreeNoUnitsFigureNine.fanInheritedRouteSuffix
          outputPlacement clearancePlacement
          first.sourceClause first.generatedClause
          (PositionedPeriodicCNF.clauseExitFanData
            first.sourceClause first.sourceClauseIndex
            (retainedFigureNineClearanceIncidenceRoutes source))
          (first.sourceSlot clearanceWidth)
          (retainedFigureNineClearanceIncidenceRoutes
            source first.sourceClauseIndex first.sourceLiteralIndex) := by
    have completedShape :=
      PlanarOneInThreeNoUnitsFigureNine.completeRouteSuffixes_routes_of_members
        clearanceSource clearancePlacement clearanceWidth
        clearanceDistinct original first.generatedClauseMember
        first.generatedLiteralMember
    rw [first.literalAtom] at completedShape
    rw [completedShape]
    change
      PlanarOneInThreeNoUnitsFigureNine.orderedInheritedRouteSuffixesRoutes
          clearanceSource clearancePlacement clearanceWidth
          (retainedFigureNineClearanceIncidenceRoutes source)
          firstClauseIndex firstLiteralIndex = _
    exact
      PlanarOneInThreeNoUnitsFigureNine.orderedInheritedRouteSuffixesRoutes_eq_fanInheritedRouteSuffix_of_lookup
        clearanceSource clearancePlacement clearanceWidth
        (retainedFigureNineClearanceIncidenceRoutes source)
        firstClauseIndex firstLiteralIndex first firstLookup
  have secondSuffixEq :
      suffixes.routes secondClauseIndex secondLiteralIndex =
        PlanarOneInThreeNoUnitsFigureNine.fanInheritedRouteSuffix
          outputPlacement clearancePlacement
          second.sourceClause second.generatedClause
          (PositionedPeriodicCNF.clauseExitFanData
            second.sourceClause second.sourceClauseIndex
            (retainedFigureNineClearanceIncidenceRoutes source))
          (second.sourceSlot clearanceWidth)
          (retainedFigureNineClearanceIncidenceRoutes
            source second.sourceClauseIndex second.sourceLiteralIndex) := by
    have completedShape :=
      PlanarOneInThreeNoUnitsFigureNine.completeRouteSuffixes_routes_of_members
        clearanceSource clearancePlacement clearanceWidth
        clearanceDistinct original second.generatedClauseMember
        second.generatedLiteralMember
    rw [second.literalAtom] at completedShape
    rw [completedShape]
    change
      PlanarOneInThreeNoUnitsFigureNine.orderedInheritedRouteSuffixesRoutes
          clearanceSource clearancePlacement clearanceWidth
          (retainedFigureNineClearanceIncidenceRoutes source)
          secondClauseIndex secondLiteralIndex = _
    exact
      PlanarOneInThreeNoUnitsFigureNine.orderedInheritedRouteSuffixesRoutes_eq_fanInheritedRouteSuffix_of_lookup
        clearanceSource clearancePlacement clearanceWidth
        (retainedFigureNineClearanceIncidenceRoutes source)
        secondClauseIndex secondLiteralIndex second secondLookup
  have localsAvoid :=
    retainedOrderedFixedEightFigureNineNormalizedLocalRoutes_relative_avoidEachOther
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty first.generatedClauseMember
      second.generatedClauseMember first.generatedLiteralMember
      second.generatedLiteralMember relativeTranslate
      generatedOccurrencesDifferent
  have firstLocalSecondSuffix :=
    retainedOrderedFixedEightFigureNine_inheritedLocal_strictlyAvoids_translatedInheritedSuffix_of_sourceGaugesEqual
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty first second relativeTranslate
      sourceGaugesEqual generatedOccurrencesDifferent
  have firstSuffixSecondLocal :=
    retainedOrderedFixedEightFigureNine_inheritedSuffix_strictlyAvoids_translatedInheritedLocal_of_sourceGaugesEqual
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty first second relativeTranslate
      sourceGaugesEqual generatedOccurrencesDifferent
  have suffixesAvoid :=
    retainedOrderedFixedEightFigureNine_inheritedSuffixes_relativeAvoidEachOther_of_sourceGaugesEqual
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty first second relativeTranslate
      sourceGaugesEqual generatedOccurrencesDifferent
  change
    RoutesAvoidEachOther
        (PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
          clearanceSource clearancePlacement
          firstClauseIndex firstLiteralIndex)
        (translatePolyline offset
          (PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
            clearanceSource clearancePlacement
            secondClauseIndex secondLiteralIndex)) ∧
      RoutesStrictlyAvoidEachOther
        (PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
          clearanceSource clearancePlacement
          firstClauseIndex firstLiteralIndex)
        (translatePolyline offset
          (suffixes.routes secondClauseIndex secondLiteralIndex)) ∧
      RoutesStrictlyAvoidEachOther
        (suffixes.routes firstClauseIndex firstLiteralIndex)
        (translatePolyline offset
          (PlanarOneInThreeNoUnitsFigureNine.normalizedLocalRoutes
            clearanceSource clearancePlacement
            secondClauseIndex secondLiteralIndex)) ∧
      RoutesAvoidEachOther
        (suffixes.routes firstClauseIndex firstLiteralIndex)
        (translatePolyline offset
          (suffixes.routes secondClauseIndex secondLiteralIndex))
  rw [firstSuffixEq, secondSuffixEq]
  exact
    ⟨by simpa [translatePolyline, clearanceSource,
        clearancePlacement, outputPlacement, offset] using localsAvoid,
      by simpa [clearanceSource, clearancePlacement,
        clearanceWidth, outputPlacement, offset] using
          firstLocalSecondSuffix,
      by simpa [clearanceSource, clearancePlacement,
        clearanceWidth, outputPlacement, offset] using
          firstSuffixSecondLocal,
      by simpa [clearanceSource, clearancePlacement,
        clearanceWidth, outputPlacement, offset] using suffixesAvoid⟩

/-- Every distinct pair of inherited incidences supplies the four
geometric avoidances required by the generic relative splice assembler. -/
theorem
    retainedOrderedFixedEightFigureNine_relativeSplicedRoutePairAvoidances_of_inherited
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {firstClauseIndex firstLiteralIndex
      secondClauseIndex secondLiteralIndex : Nat}
    (first :
      PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        firstClauseIndex firstLiteralIndex)
    (second :
      PlanarOneInThreeNoUnitsFigureNine.InheritedIncidenceData
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        secondClauseIndex secondLiteralIndex)
    (firstLookup :
      PlanarOneInThreeNoUnitsFigureNine.inheritedIncidenceData?
          (retainedFigureNineClearancePositionedFormula source)
          (retainedFigureNineClearancePlacement source)
          firstClauseIndex firstLiteralIndex = some first)
    (secondLookup :
      PlanarOneInThreeNoUnitsFigureNine.inheritedIncidenceData?
          (retainedFigureNineClearancePositionedFormula source)
          (retainedFigureNineClearancePlacement source)
          secondClauseIndex secondLiteralIndex = some second)
    (relativeTranslate : Cell)
    (generatedOccurrencesDifferent :
      ((firstClauseIndex, firstLiteralIndex), (0, 0)) ≠
        ((secondClauseIndex, secondLiteralIndex), relativeTranslate)) :
    PlanarOneInThreeNoUnitsFigureNine.RelativeSplicedRoutePairAvoidances
      (retainedFigureNineClearancePositionedFormula source)
      (retainedFigureNineClearancePlacement source)
      (retainedFigureNineClearancePositionedFormula_widthAtMostThree
        source sourceWidth)
      (retainedFigureNineClearancePositionedFormula_allAtomsNodup
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsOriginalInheritedRouteSuffixes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      firstClauseIndex firstLiteralIndex
      secondClauseIndex secondLiteralIndex relativeTranslate := by
  by_cases sourceGaugesEqual :
      PlanarOneInThreeNoUnitsFigureNine.normalizedSourceClausePosition
          (PlanarOneInThreeNoUnitsFigureNine.composedPlacement
            (retainedFigureNineClearancePositionedFormula source)
            (retainedFigureNineClearancePlacement source))
          first.sourceClause first.generatedClause =
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
      retainedOrderedFixedEightFigureNine_relativeSplicedRoutePairAvoidances_of_inherited_sourceGaugesEqual
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty first second firstLookup secondLookup
        relativeTranslate sourceGaugesEqual generatedOccurrencesDifferent
  · exact
      retainedOrderedFixedEightFigureNine_relativeSplicedRoutePairAvoidances_of_inherited_sourceGaugesNe
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty first second firstLookup secondLookup
        relativeTranslate sourceGaugesEqual generatedOccurrencesDifferent

/-- Four pointwise avoidance conditions—ordinary local/local and
suffix/suffix separation plus strict separation of the two cross pairs—imply
complete raw relative route separation for the retained ordered family. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRaw_relativeIncidenceRoutesAvoidEachOther_of_avoidances
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (avoidances :
      ∀ first ∈
          (PeriodicCNF.incidencesWithMetadata
            (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
              source).erase).zipIdx,
        ∀ second ∈
            (PeriodicCNF.incidencesWithMetadata
              (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
                source).erase).zipIdx,
          ∀ relativeTranslate,
            (first.2, (0, 0)) ≠
                (second.2, relativeTranslate) →
              PlanarOneInThreeNoUnitsFigureNine.RelativeSplicedRoutePairAvoidances
                (retainedFigureNineClearancePositionedFormula source)
                (retainedFigureNineClearancePlacement source)
                (retainedFigureNineClearancePositionedFormula_widthAtMostThree
                  source sourceWidth)
                (retainedFigureNineClearancePositionedFormula_allAtomsNodup
                  source sourceLocal sourceWidth sourceOccurrences
                  sourceClausesNonempty)
                (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsOriginalInheritedRouteSuffixes
                  source sourceLocal sourceWidth sourceOccurrences
                  sourceClausesNonempty)
                first.1.clauseIndex first.1.literalIndex
                second.1.clauseIndex second.1.literalIndex
                relativeTranslate) :
    PositionedPeriodicCNF.RelativeIncidenceRoutesAvoidEachOther
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty) := by
  simpa [
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes]
    using
      PlanarOneInThreeNoUnitsFigureNine.splicedRoutes_relativeIncidenceRoutesAvoidEachOther_of_avoidances
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        (retainedFigureNineClearancePositionedFormula_widthAtMostThree
          source sourceWidth)
        (retainedFigureNineClearancePositionedFormula_allAtomsNodup
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsOriginalInheritedRouteSuffixes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)
        avoidances

/-- The six generic component conditions, instantiated at every distinct
relative pair of incidences of the retained ordered composed formula, imply
complete raw relative route separation. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRaw_relativeIncidenceRoutesAvoidEachOther_of_components
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (components :
      ∀ first ∈
          (PeriodicCNF.incidencesWithMetadata
            (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
              source).erase).zipIdx,
        ∀ second ∈
            (PeriodicCNF.incidencesWithMetadata
              (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
                source).erase).zipIdx,
          ∀ relativeTranslate,
            (first.2, (0, 0)) ≠
                (second.2, relativeTranslate) →
              PlanarOneInThreeNoUnitsFigureNine.RelativeSplicedRoutePairComponentsSeparated
                (retainedFigureNineClearancePositionedFormula source)
                (retainedFigureNineClearancePlacement source)
                (retainedFigureNineClearancePositionedFormula_widthAtMostThree
                  source sourceWidth)
                (retainedFigureNineClearancePositionedFormula_allAtomsNodup
                  source sourceLocal sourceWidth sourceOccurrences
                  sourceClausesNonempty)
                (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsOriginalInheritedRouteSuffixes
                  source sourceLocal sourceWidth sourceOccurrences
                  sourceClausesNonempty)
                first.1.clauseIndex first.1.literalIndex
                second.1.clauseIndex second.1.literalIndex
                relativeTranslate) :
    PositionedPeriodicCNF.RelativeIncidenceRoutesAvoidEachOther
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty) := by
  simpa [
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement,
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes]
    using
      PlanarOneInThreeNoUnitsFigureNine.splicedRoutes_relativeIncidenceRoutesAvoidEachOther_of_components
        (retainedFigureNineClearancePositionedFormula source)
        (retainedFigureNineClearancePlacement source)
        (retainedFigureNineClearancePositionedFormula_widthAtMostThree
          source sourceWidth)
        (retainedFigureNineClearancePositionedFormula_allAtomsNodup
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsOriginalInheritedRouteSuffixes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)
        components

/-- The same component family is the final missing geometric input for the
normalized ordered drawing's ribbon-ready certificate. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing_isRibbonReady_of_components
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (components :
      ∀ first ∈
          (PeriodicCNF.incidencesWithMetadata
            (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
              source).erase).zipIdx,
        ∀ second ∈
            (PeriodicCNF.incidencesWithMetadata
              (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
                source).erase).zipIdx,
          ∀ relativeTranslate,
            (first.2, (0, 0)) ≠
                (second.2, relativeTranslate) →
              PlanarOneInThreeNoUnitsFigureNine.RelativeSplicedRoutePairComponentsSeparated
                (retainedFigureNineClearancePositionedFormula source)
                (retainedFigureNineClearancePlacement source)
                (retainedFigureNineClearancePositionedFormula_widthAtMostThree
                  source sourceWidth)
                (retainedFigureNineClearancePositionedFormula_allAtomsNodup
                  source sourceLocal sourceWidth sourceOccurrences
                  sourceClausesNonempty)
                (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsOriginalInheritedRouteSuffixes
                  source sourceLocal sourceWidth sourceOccurrences
                  sourceClausesNonempty)
                first.1.clauseIndex first.1.literalIndex
                second.1.clauseIndex second.1.literalIndex
                relativeTranslate) :
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).IsRibbonReady := by
  apply
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceDrawing_isRibbonReady_of_rawRelativeIncidenceRoutesAvoidEachOther
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  exact
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRaw_relativeIncidenceRoutesAvoidEachOther_of_components
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty components

end PeriodicOrthocrossing
end LeanTrominoes
